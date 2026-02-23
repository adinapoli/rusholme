//! Robinson unification over `HType`.
//!
//! Unification is the core algorithmic engine of type inference.  Given two
//! types `a` and `b`, `unify` determines — and records — the substitution
//! that makes them equal, by filling in `MetaVar.ref` fields in place.
//!
//! ## Algorithm (structural, with occurs check)
//!
//! 1. Chase any solved metavars on both sides.
//! 2. If both are the same unsolved `Meta` (same ID): reflexivity — done.
//! 3. If one side is an unsolved `Meta`: occurs check, then bind.
//! 4. If both are `Con`: names must match (same unique ID), then unify args
//!    pairwise.
//! 5. If both are `Fun`: unify arg↔arg, then res↔res.
//! 6. If both are `Rigid`: they must be the same rigid variable (same unique
//!    ID); otherwise `RigidMismatch`.
//! 7. If both are `ForAll`: unify bodies (binders are rigid, so they must
//!    have the same unique ID — the renamer guarantees this for well-scoped
//!    programs).
//! 8. Otherwise: `TypeMismatch`.
//!
//! ## Mutation discipline
//!
//! Unification mutates `MetaVar.ref` fields directly.  There is no explicit
//! substitution map.  This is the "mutable unification cells" approach used
//! by GHC, Lean, and Agda.  The arena that owns all `HType` nodes is
//! threaded through `bind` so that the solution can be allocated there.
//!
//! ## Error context
//!
//! `UnifyError` values carry a `SourceSpan` so that the constraint solver can
//! report the error at the site of the constraint that triggered unification,
//! not deep inside the unifier.
//!
//! ## References
//!
//! - Robinson, "A Machine-Oriented Logic Based on the Resolution Principle",
//!   JACM 1965.
//! - Dunfield & Krishnaswami, "Complete and Easy Bidirectional Typechecking
//!   for Higher-Rank Polymorphism", ICFP 2013.

const std = @import("std");
const htype = @import("htype.zig");
const span_mod = @import("../diagnostics/span.zig");
const cycle_detection = @import("cycle_detection.zig");

pub const HType = htype.HType;
pub const MetaVar = htype.MetaVar;
pub const MetaVarSupply = htype.MetaVarSupply;
pub const Name = htype.Name;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;

// ── Errors ─────────────────────────────────────────────────────────────

/// Errors that unification can produce.
///
/// Each variant carries the `SourceSpan` of the constraint that triggered
/// unification so that the caller can attach source location to diagnostics.
pub const UnifyError = error{
    /// Two incompatible type constructors were unified, e.g. `Int ~ Bool`.
    TypeMismatch,
    /// The occurs check failed: a metavariable appears in its own solution,
    /// which would produce an infinite type, e.g. `?0 ~ [?0]`.
    InfiniteType,
    /// A cycle was detected in the metavariable chain (e.g., ?0 → ?1 → ?0).
    /// This indicates unsound type unification occurred, but we report it
    /// gracefully as a diagnostic rather than panicking.
    InfiniteTypeCycle,
    /// Two distinct rigid type variables were unified, e.g. `a ~ b` where
    /// both are bound by `forall`.
    RigidMismatch,
    /// Argument count mismatch for a type constructor, e.g. `Maybe Int Bool`
    /// vs `Maybe Int`.  This is a compiler-internal invariant violation.
    ArityMismatch,
    /// Arena allocation failed.  Treated as a fatal error by the caller.
    OutOfMemory,
};

// ── Unifier ────────────────────────────────────────────────────────────

/// Unify `a` and `b` in place, filling in metavar `ref` fields as needed.
///
/// Both `a` and `b` are passed as pointers so that metavar bindings written
/// inside `bind` are visible to the caller through the original `HType` node.
/// This is essential: `MetaVar.ref` lives inside the `HType` union field, and
/// only a pointer to that field allows mutation to propagate back.
///
/// `alloc` must be the arena that owns all `HType` nodes in scope — it is
/// used only when binding a metavar to a non-Meta type (to allocate the
/// solution on the arena).
///
/// On success, `a` and `b` are unified: chasing their metavar chains will
/// yield the same ground type.  On failure, no partial writes are guaranteed
/// to be rolled back (unification is not transactional at this level — the
/// constraint solver is responsible for checkpointing if needed).
pub fn unify(alloc: std.mem.Allocator, a: *HType, b: *HType) UnifyError!void {
    // Chase to the root of each side (follows solved MetaVar chains).
    // Use tryChase to propagate cycle detection as an error.
    const lhs = a.tryChase() catch return UnifyError.InfiniteTypeCycle;
    const rhs = b.tryChase() catch return UnifyError.InfiniteTypeCycle;

    // Both are the same unsolved metavar — reflexivity.
    if (lhs == .Meta and rhs == .Meta and lhs.Meta.eql(rhs.Meta))
        return;

    // Both are distinct unsolved metavars — link LHS → RHS using the actual
    // RHS arena node pointer, avoiding a value copy that would sever the
    // mutation chain.  We walk to the tail of `a`'s chain and point it at
    // the tail of `b`'s chain directly.
    if (lhs == .Meta and rhs == .Meta) {
        const a_tail = try tailPtr(a);
        const b_tail = try tailPtr(b);
        a_tail.Meta.ref = b_tail;
        return;
    }

    // LHS is an unsolved metavar — bind it to rhs (a non-Meta ground type).
    if (lhs == .Meta) {
        try bindPtr(alloc, a, rhs);
        return;
    }

    // RHS is an unsolved metavar — bind it to lhs (a non-Meta ground type).
    if (rhs == .Meta) {
        try bindPtr(alloc, b, lhs);
        return;
    }

    // Both are fully resolved (non-Meta after chasing) — structural match.
    switch (lhs) {
        .Meta => unreachable, // handled above
        .Rigid => |ln| {
            switch (rhs) {
                .Rigid => |rn| {
                    if (ln.unique.value != rn.unique.value)
                        return UnifyError.RigidMismatch;
                },
                .Meta => {
                    // Rigid can be unified with a metavariable by solving the meta.
                    // This is the key for bidirectional checking: infer(?a, rigid) solves ?a = rigid.
                    try bindPtr(alloc, b, lhs);
                },
                else => return UnifyError.TypeMismatch,
            }
        },
        .Con => |lc| {
            switch (rhs) {
                .Con => |rc| {
                    if (lc.name.unique.value != rc.name.unique.value)
                        return UnifyError.TypeMismatch;
                    if (lc.args.len != rc.args.len)
                        return UnifyError.ArityMismatch;
                    // Args are slices of const HType; unify pairwise by value
                    // (Con args are not mutated themselves — only metavars
                    // inside them get bound, and those mutations go through
                    // the MetaVar.ref pointer which is already a pointer).
                    for (lc.args, rc.args) |*la, *ra|
                        try unify(alloc, @constCast(la), @constCast(ra));
                },
                .AppTy => |ra| {
                    // Con(c, [arg]) ~ AppTy(?h, ?a)
                    // Symmetric to the case in .AppTy branch
                    if (lc.args.len != 1) return UnifyError.TypeMismatch;

                    // First, unify the arguments: arg ~ ?a
                    const lhs_arg_ptr = @constCast(&lc.args[0]);
                    try unify(alloc, lhs_arg_ptr, @constCast(ra.arg));

                    // Bind the head: Con(c, []) ~ ?h
                    const constructor = HType{ .Con = .{ .name = lc.name, .args = &.{} } };
                    const constructor_ptr = try alloc.create(HType);
                    constructor_ptr.* = constructor;
                    try unify(alloc, constructor_ptr, @constCast(ra.head));
                },
                else => return UnifyError.TypeMismatch,
            }
        },
        .Fun => |lf| {
            switch (rhs) {
                .Fun => |rf| {
                    try unify(alloc, @constCast(lf.arg), @constCast(rf.arg));
                    try unify(alloc, @constCast(lf.res), @constCast(rf.res));
                },
                else => return UnifyError.TypeMismatch,
            }
        },
        .AppTy => |lat| {
            switch (rhs) {
                .AppTy => |rat| {
                    try unify(alloc, @constCast(lat.head), @constCast(rat.head));
                    try unify(alloc, @constCast(lat.arg), @constCast(rat.arg));
                },
                .Con => |rc| {
                    // AppTy(?h, ?a) ~ Con(c, [arg])
                    // This supports generic monad inference: AppTy(?0, ?1) unifies with IO ()
                    // For M1, only single-argument constructors are handled (e.g. IO, Maybe, [])
                    if (rc.args.len != 1) return UnifyError.TypeMismatch;

                    // First, unify the arguments: ?a ~ arg
                    try unify(alloc, @constCast(lat.arg), @constCast(&rc.args[0]));

                    // After argument unification, bind the head to the constructor
                    // ?h ~ Con(c, [])
                    const constructor = HType{ .Con = .{ .name = rc.name, .args = &.{} } };
                    const constructor_ptr = try alloc.create(HType);
                    constructor_ptr.* = constructor;
                    try unify(alloc, @constCast(lat.head), constructor_ptr);
                },
                else => return UnifyError.TypeMismatch,
            }
        },
        .ForAll => |lfa| {
            switch (rhs) {
                .ForAll => |rfa| {
                    // Binders must be alpha-equivalent: the renamer gives
                    // each `forall`-bound variable a globally unique ID, so
                    // syntactic equality of unique IDs implies same variable.
                    if (lfa.binder.unique.value != rfa.binder.unique.value)
                        return UnifyError.TypeMismatch;
                    try unify(alloc, @constCast(lfa.body), @constCast(rfa.body));
                },
                else => return UnifyError.TypeMismatch,
            }
        },
    }
}

/// Walk a MetaVar chain to the last unsolved `Meta` node and return a pointer
/// to it.  `node` must be a `.Meta` (possibly with solved links).
/// Returns `InfiniteTypeCycle` if a cycle is detected in the chain.
fn tailPtr(node: *HType) UnifyError!*HType {
    return cycle_detection.chasePtr(node) catch UnifyError.InfiniteTypeCycle;
}

fn bindPtr(alloc: std.mem.Allocator, node: *HType, ty: HType) UnifyError!void {
    const end = cycle_detection.chasePtr(node) catch return UnifyError.InfiniteTypeCycle;
    return bind(end, end.Meta.id, ty, alloc);
}

/// Perform the occurs check and write the solution into the MetaVar cell at
/// `node` (which must be an unsolved `.Meta` with id `meta_id`).
fn bind(node: *HType, meta_id: u32, ty: HType, alloc: std.mem.Allocator) UnifyError!void {
    // Occurs check: ?id must not appear free in ty.
    if (ty.occursIn(meta_id))
        return UnifyError.InfiniteType;

    // Allocate a stable copy of `ty` on the arena and point the MetaVar at it.
    const solution = try alloc.create(HType);
    solution.* = ty;

    // Write the solution through the pointer to the HType node.
    // `node.*` is `.Meta` with a null ref; we overwrite the ref field.
    node.Meta.ref = solution;
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

/// Helper: a `Name` for tests.
fn testName(base: []const u8, id: u64) Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

/// Helper: nullary `HType.Con` (e.g. `Int`, `Bool`).
fn con0(name: []const u8, id: u64) HType {
    return .{ .Con = .{ .name = testName(name, id), .args = &.{} } };
}

// ── Unify Con ~ Con ────────────────────────────────────────────────────

test "unify: Int ~ Int succeeds" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var int1 = con0("Int", 0);
    var int2 = con0("Int", 0);
    try unify(arena.allocator(), &int1, &int2);
}

test "unify: Int ~ Bool returns TypeMismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var int_ty = con0("Int", 0);
    var bool_ty = con0("Bool", 1);
    try testing.expectError(UnifyError.TypeMismatch, unify(arena.allocator(), &int_ty, &bool_ty));
}

// ── Unify Meta ~ Con ───────────────────────────────────────────────────

test "unify: ?0 ~ Int solves ?0 to Int" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    var meta_ty = HType{ .Meta = mv };
    var int_ty = con0("Int", 0);

    try unify(alloc, &meta_ty, &int_ty);

    const chased = meta_ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

test "unify: Int ~ ?0 solves ?0 to Int (symmetric)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    var meta_ty = HType{ .Meta = mv };
    var int_ty = con0("Int", 0);

    try unify(alloc, &int_ty, &meta_ty);

    const chased = meta_ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

// ── Unify Meta ~ Meta ──────────────────────────────────────────────────

test "unify: ?0 ~ ?0 (same metavar) succeeds without binding" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    var a = HType{ .Meta = mv };
    var b = HType{ .Meta = mv };
    try unify(arena.allocator(), &a, &b);
    // Both still unsolved — reflexivity requires no binding.
    try testing.expect(a.chase() == .Meta);
}

test "unify: ?0 ~ ?1 binds one to the other" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var supply = MetaVarSupply{};
    const mv0 = supply.fresh();
    const mv1 = supply.fresh();
    var a = HType{ .Meta = mv0 };
    var b = HType{ .Meta = mv1 };

    try unify(alloc, &a, &b);

    // ?0 is now bound to ?1 (unsolved). Chasing `a` yields a Meta.
    const chased = a.chase();
    try testing.expect(chased == .Meta);
}

// ── Unify Fun ~ Fun ────────────────────────────────────────────────────

test "unify: ?0 -> ?1 ~ Int -> Bool solves both metavars" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var supply = MetaVarSupply{};
    const mv0 = supply.fresh();
    const mv1 = supply.fresh();
    var arg_ty = HType{ .Meta = mv0 };
    var res_ty = HType{ .Meta = mv1 };
    var fun_meta = HType{ .Fun = .{ .arg = &arg_ty, .res = &res_ty } };

    var int_ty = con0("Int", 0);
    var bool_ty = con0("Bool", 1);
    var fun_con = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };

    try unify(alloc, &fun_meta, &fun_con);

    try testing.expectEqualStrings("Int", arg_ty.chase().Con.name.base);
    try testing.expectEqualStrings("Bool", res_ty.chase().Con.name.base);
}

test "unify: Int -> Bool ~ Bool -> Int returns TypeMismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var int_ty = con0("Int", 0);
    var bool_ty = con0("Bool", 1);
    var f1 = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };
    var f2 = HType{ .Fun = .{ .arg = &bool_ty, .res = &int_ty } };
    try testing.expectError(UnifyError.TypeMismatch, unify(arena.allocator(), &f1, &f2));
}

test "unify: Fun ~ Con returns TypeMismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var int_ty = con0("Int", 0);
    var bool_ty = con0("Bool", 1);
    var fun_ty = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };
    var con_ty = con0("Int", 0);
    try testing.expectError(UnifyError.TypeMismatch, unify(arena.allocator(), &fun_ty, &con_ty));
}

// ── Unify Con with args ────────────────────────────────────────────────

test "unify: Maybe ?0 ~ Maybe Int solves ?0 to Int" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    // args_meta must be `var` so the unifier can mutate the MetaVar.ref
    // inside args_meta[0] in place. We then verify through the array, not
    // through the original `mv` copy (which is a separate local).
    var args_meta = [_]HType{HType{ .Meta = mv }};
    var maybe_meta = HType{ .Con = .{ .name = testName("Maybe", 10), .args = &args_meta } };

    const int_ty = con0("Int", 0);
    const args_con = [_]HType{int_ty};
    var maybe_int = HType{ .Con = .{ .name = testName("Maybe", 10), .args = &args_con } };

    try unify(alloc, &maybe_meta, &maybe_int);

    // The solved metavar lives in args_meta[0], not in the discarded local.
    const chased = args_meta[0].chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

test "unify: Maybe Int ~ Either Int Bool returns TypeMismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    const int_ty = con0("Int", 0);
    const bool_ty = con0("Bool", 1);
    const args1 = [_]HType{int_ty};
    const args2 = [_]HType{ int_ty, bool_ty };
    var maybe = HType{ .Con = .{ .name = testName("Maybe", 10), .args = &args1 } };
    var either = HType{ .Con = .{ .name = testName("Either", 11), .args = &args2 } };
    try testing.expectError(UnifyError.TypeMismatch, unify(arena.allocator(), &maybe, &either));
}

// ── Occurs check ───────────────────────────────────────────────────────

test "unify: ?0 ~ [?0] returns InfiniteType" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    var meta_ty = HType{ .Meta = mv };
    // Represent [?0] as `List ?0`
    const args = [_]HType{meta_ty};
    var list_meta = HType{ .Con = .{ .name = testName("List", 99), .args = &args } };

    try testing.expectError(UnifyError.InfiniteType, unify(alloc, &meta_ty, &list_meta));
}

// ── Rigid ~ Rigid ──────────────────────────────────────────────────────

test "unify: rigid a ~ rigid a (same id) succeeds" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var a1 = HType{ .Rigid = testName("a", 1) };
    var a2 = HType{ .Rigid = testName("a", 1) };
    try unify(arena.allocator(), &a1, &a2);
}

test "unify: rigid a ~ rigid b (different id) returns RigidMismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var a = HType{ .Rigid = testName("a", 1) };
    var b = HType{ .Rigid = testName("b", 2) };
    try testing.expectError(UnifyError.RigidMismatch, unify(arena.allocator(), &a, &b));
}

test "unify: rigid a ~ Int returns TypeMismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var a = HType{ .Rigid = testName("a", 1) };
    var int_ty = con0("Int", 0);
    try testing.expectError(UnifyError.TypeMismatch, unify(arena.allocator(), &a, &int_ty));
}

// ── Arity mismatch ─────────────────────────────────────────────────────

test "unify: Maybe Int ~ Maybe Int Bool returns ArityMismatch" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    const int_ty = con0("Int", 0);
    const bool_ty = con0("Bool", 1);
    const args1 = [_]HType{int_ty};
    const args2 = [_]HType{ int_ty, bool_ty };
    var maybe1 = HType{ .Con = .{ .name = testName("Maybe", 10), .args = &args1 } };
    var maybe2 = HType{ .Con = .{ .name = testName("Maybe", 10), .args = &args2 } };
    try testing.expectError(UnifyError.ArityMismatch, unify(arena.allocator(), &maybe1, &maybe2));
}
