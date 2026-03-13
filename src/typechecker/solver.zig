//! Constraint solver for the bidirectional typechecker.
//!
//! The typechecker emits *Wanted* equality constraints rather than calling
//! the unifier inline.  This separation keeps each stage independently
//! testable and mirrors GHC's constraint pipeline (simplified for M1).
//!
//! ## Pipeline position
//!
//! ```
//! Bidirectional TC  →  [Constraint]  →  Solver  →  solved MetaVar.ref fields
//!                                           ↓
//!                                    DiagnosticCollector (type errors)
//! ```
//!
//! After `solve` returns, all `MetaVar.ref` fields reachable from the
//! program's `HType` nodes are filled in (or a diagnostic has been emitted
//! for each failure).  The elaborator can then call `HType.toCore()` on
//! every node.
//!
//! ## Error handling
//!
//! The solver does **not** fail fast.  It continues after a unification
//! failure so that a single compilation surfaces as many type errors as
//! possible.  Each failure is turned into a structured `Diagnostic` carrying
//! the `SourceSpan` of the constraint that triggered it.
//!
//! ## M1 scope
//!
//! Only equality constraints (`Constraint.Eq`) are needed for M1.  The
//! design is intentionally open for extension:
//!
//! - M2: add `Constraint.Class` for type class constraints; the solver would
//!   look up instances in `TyEnv` and emit dictionary arguments.
//! - Future: stratified solving (OutsideIn-style), constraint simplification.
//!
//! ## References
//!
//! - Vytiniotis, Peyton Jones et al., "OutsideIn(X)", JFP 2011.
//! - Dunfield & Krishnaswami, "Complete and Easy Bidirectional Typechecking
//!   for Higher-Rank Polymorphism", ICFP 2013.

const std = @import("std");
const htype_mod = @import("htype.zig");
const unify_mod = @import("unify.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");
const span_mod = @import("../diagnostics/span.zig");
const type_error_mod = @import("type_error.zig");
const class_env_mod = @import("class_env.zig");

pub const HType = htype_mod.HType;
pub const MetaVar = htype_mod.MetaVar;
pub const MetaVarSupply = htype_mod.MetaVarSupply;
pub const UnifyError = unify_mod.UnifyError;
pub const Diagnostic = diag_mod.Diagnostic;
pub const DiagnosticCollector = diag_mod.DiagnosticCollector;
pub const DiagnosticCode = diag_mod.DiagnosticCode;
pub const DiagnosticPayload = diag_mod.DiagnosticPayload;
pub const Severity = diag_mod.Severity;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;
pub const TypeError = type_error_mod.TypeError;
pub const ClassEnv = class_env_mod.ClassEnv;
pub const ClassConstraint = class_env_mod.ClassConstraint;

// ── Constraint ─────────────────────────────────────────────────────────

/// A constraint emitted by the typechecker for the solver to discharge.
///
/// Two variants:
/// - `Eq`: equality constraint `lhs ~ rhs` (Robinson unification).
/// - `Class`: class constraint `ClassName ty` (instance resolution).
///
/// Both `lhs`/`rhs` (for Eq) and `ty` (for Class) are stored by value;
/// the solver takes pointers to the copies it holds in the constraint
/// slice so that metavar bindings written by the unifier are visible
/// through those pointers.  Callers must ensure that any `HType` nodes
/// referenced transitively are allocated on an arena that outlives the
/// solve call.

/// Payload for equality constraints: `lhs ~ rhs`.
pub const EqConstraint = struct {
    lhs: HType,
    rhs: HType,
    span: SourceSpan,
};

/// Payload for class constraints: `ClassName ty`.
pub const ClassConstraintPayload = struct {
    class_name: class_env_mod.Name,
    ty: HType,
    span: SourceSpan,
    /// Filled by the solver after resolution. Null means unresolved.
    evidence: ?*const DictEvidence = null,
};

pub const Constraint = union(enum) {
    /// Equality constraint: `lhs ~ rhs`.
    Eq: EqConstraint,
    /// Class constraint: `ClassName ty`.
    Class: ClassConstraintPayload,
};

// ── DictEvidence ───────────────────────────────────────────────────────

/// Evidence for how a class constraint was satisfied.
///
/// Produced by the solver during class constraint resolution and consumed
/// by the desugarer to generate dictionary-passing Core code.
pub const DictEvidence = union(enum) {
    /// Satisfied by a concrete instance dictionary value.
    /// E.g., `Eq Int` is satisfied by `dict$Eq$Int`.
    instance: struct {
        class_name: class_env_mod.Name,
        head_ty: HType,
        /// Sub-evidence for instance context constraints.
        /// E.g., `instance Eq a => Eq [a]` needs evidence for `Eq a`.
        context_evidence: []const DictEvidence,
    },
    /// Satisfied by a dictionary parameter of the enclosing function.
    /// E.g., in `elem :: Eq a => ...`, the `Eq a` constraint is a parameter.
    param: struct {
        param_index: u32,
        class_name: class_env_mod.Name,
    },
    /// Satisfied by extracting a superclass dictionary.
    /// E.g., `Eq` from an `Ord` dictionary via a superclass selector.
    superclass: struct {
        class_name: class_env_mod.Name,
        sub_evidence: *const DictEvidence,
        super_index: u32,
    },
};

// ── Solver ─────────────────────────────────────────────────────────────

/// Solve a slice of equality constraints by driving Robinson unification.
///
/// For each constraint `lhs ~ rhs`, calls `unify(&lhs, &rhs)`.  On failure,
/// emits a structured `Diagnostic` into `diags` and continues to the next
/// constraint (no fail-fast — collect all errors).
///
/// `alloc` is the typechecker's arena; it is passed through to `unify` for
/// metavar binding allocation.  It is also used to format diagnostic
/// messages.
///
/// `class_env` is the class environment containing all declared classes and
/// instances.  It is ignored for M1 (equality-only constraints) but will be
/// used in M2 for issue #37 (class constraint resolution).
///
/// Returns `error.OutOfMemory` only if arena allocation fails (a fatal
/// condition distinct from type errors, which are soft failures recorded in
/// `diags`).
pub fn solve(
    constraints: []Constraint,
    alloc: std.mem.Allocator,
    diags: *DiagnosticCollector,
    class_env: ?*const ClassEnv,
) std.mem.Allocator.Error!void {
    for (constraints) |*c| {
        switch (c.*) {
            .Class => |*cc| {
                try solveClassConstraint(cc, alloc, diags, class_env);
            },
            .Eq => |*eq| {
                try solveEqConstraint(eq, alloc, diags);
            },
        }
    }
}

/// Solve a class constraint by looking up instances in the ClassEnv.
fn solveClassConstraint(
    cc: *ClassConstraintPayload,
    alloc: std.mem.Allocator,
    diags: *DiagnosticCollector,
    class_env: ?*const ClassEnv,
) std.mem.Allocator.Error!void {
    const env = class_env orelse return; // No ClassEnv → cannot resolve
    const chased = cc.ty.chase();

    // If the type is a rigid (polymorphic context), the constraint becomes
    // a dictionary parameter — evidence is recorded as `param`. The param
    // index is not known here; it will be assigned by the caller based on
    // the constraint's position in the function's constraint list.
    switch (chased) {
        .Rigid => {
            // Polymorphic: will become a dictionary parameter.
            // The caller (inferModule) assigns param indices.
            return;
        },
        .Meta => {
            // Unsolved meta — ambiguous type. Defer to later or emit diagnostic.
            return;
        },
        else => {},
    }

    // Concrete type: look up matching instances.
    const instances = env.lookupInstances(cc.class_name.unique.value);
    var match_count: usize = 0;
    var matched_instance: ?class_env_mod.InstanceInfo = null;
    for (instances) |inst| {
        // Simple matching: check if the instance head matches the constraint type.
        // For now, we do structural equality on the chased types.
        // A full implementation would use unification-based matching.
        if (htypeMatchesHead(chased, inst.head)) {
            match_count += 1;
            matched_instance = inst;
        }
    }

    if (match_count == 0) {
        const te = TypeError{ .missing_instance = .{
            .class_name = cc.class_name,
            .ty = chased,
        } };
        const msg = try type_error_mod.format(alloc, te);
        try diags.emit(alloc, .{
            .severity = .@"error",
            .code = .type_error,
            .span = cc.span,
            .message = msg,
            .payload = DiagnosticPayload{ .type_error = te },
        });
        return;
    }

    if (match_count > 1) {
        const te = TypeError{ .overlapping_instances = .{
            .class_name = cc.class_name,
            .ty = chased,
        } };
        const msg = try type_error_mod.format(alloc, te);
        try diags.emit(alloc, .{
            .severity = .@"error",
            .code = .type_error,
            .span = cc.span,
            .message = msg,
            .payload = DiagnosticPayload{ .type_error = te },
        });
        return;
    }

    // Exactly one match — record the evidence.
    if (matched_instance) |inst| {
        const ev = try alloc.create(DictEvidence);
        ev.* = .{ .instance = .{
            .class_name = cc.class_name,
            .head_ty = chased,
            .context_evidence = &.{}, // TODO: resolve context constraints recursively
        } };
        cc.evidence = ev;

        // If the instance has context constraints, they should be emitted
        // as new wanted constraints. For now, we defer recursive resolution.
        _ = inst;
    }
}

/// Check if an HType matches an instance head (simple structural match).
///
/// For M1 scope, we match on constructor names. A full implementation
/// would use unification to handle parametric instance heads like `Eq [a]`.
fn htypeMatchesHead(ty: HType, head: HType) bool {
    const chased_ty = ty.chase();
    const chased_head = head.chase();
    return switch (chased_ty) {
        .Con => |tc| switch (chased_head) {
            .Con => |hc| tc.name.unique.value == hc.name.unique.value,
            else => false,
        },
        else => false,
    };
}

/// Solve an equality constraint via Robinson unification.
fn solveEqConstraint(
    c: *EqConstraint,
    alloc: std.mem.Allocator,
    diags: *DiagnosticCollector,
) std.mem.Allocator.Error!void {
    unify_mod.unify(alloc, &c.lhs, &c.rhs) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.TypeMismatch,
        error.RigidMismatch,
        => {
            const te = TypeError{ .mismatch = .{
                .lhs = c.lhs,
                .rhs = c.rhs,
            } };
            const msg = try type_error_mod.format(alloc, te);
            try diags.emit(alloc, .{
                .severity = .@"error",
                .code = .type_error,
                .span = c.span,
                .message = msg,
                .payload = DiagnosticPayload{ .type_error = te },
            });
        },
        error.InfiniteType => {
            // Extract the metavar from the lhs (should be a Meta)
            const meta = if (c.lhs.chase() == .Meta)
                c.lhs.Meta
            else
                blk: {
                    // If lhs isn't a Meta, try rhs
                    if (c.rhs.chase() == .Meta) break :blk c.rhs.Meta;
                    // Fallback: create a placeholder (this shouldn't happen in normal operation)
                    break :blk MetaVar{ .id = 0, .ref = null };
                };
            const te = TypeError{ .infinite_type = .{
                .meta = meta,
                .ty = c.rhs,
            } };
            const msg = try type_error_mod.format(alloc, te);
            try diags.emit(alloc, .{
                .severity = .@"error",
                .code = .type_error,
                .span = c.span,
                .message = msg,
                .payload = DiagnosticPayload{ .type_error = te },
            });
        },
        error.InfiniteTypeCycle => {
            // A cycle was detected in the metavariable chain.
            // Extract the metavar ID for better error reporting.
            const meta_id = if (c.lhs.chase() == .Meta)
                c.lhs.Meta.id
            else
                blk: {
                    if (c.rhs.chase() == .Meta) break :blk c.rhs.Meta.id;
                    break :blk 0;
                };
            const te = TypeError{ .infinite_type_cycle = .{
                .meta_id = meta_id,
            } };
            const msg = try type_error_mod.format(alloc, te);
            try diags.emit(alloc, .{
                .severity = .@"error",
                .code = .type_error,
                .span = c.span,
                .message = msg,
                .payload = DiagnosticPayload{ .type_error = te },
            });
        },
        error.ArityMismatch => {
            // For M1, we don't have detailed arity info from the unifier,
            // so we use a generic payload. The message still provides
            // useful information.
            const unknown_name = @import("../naming/unique.zig").Name{
                .base = "<type>",
                .unique = .{ .value = 0 },
            };
            const te = TypeError{ .arity_mismatch = .{
                .name = unknown_name,
                .expected = 0,
                .got = 0,
            } };
            const msg = "type constructor arity mismatch";
            try diags.emit(alloc, .{
                .severity = .@"error",
                .code = .type_error,
                .span = c.span,
                .message = msg,
                .payload = DiagnosticPayload{ .type_error = te },
            });
        },
    };
}

// ── Diagnostic message formatting ──────────────────────────────────────

/// Format an HType for diagnostic messages.
///
/// Delegates to the canonical `HType.pretty` printer in `htype.zig`, which
/// handles correct parenthesisation (issue #163).
///
/// Note: Most diagnostics now use `type_error.format()` instead, but this
/// is kept for test compatibility.
fn formatHType(alloc: std.mem.Allocator, ty: HType) std.mem.Allocator.Error![]const u8 {
    return ty.pretty(alloc);
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

fn testSpan() SourceSpan {
    return SourceSpan.init(
        SourcePos.init(1, 1, 1),
        SourcePos.init(1, 1, 10),
    );
}

fn testName(base: []const u8, id: u64) htype_mod.Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

fn con0(base: []const u8, id: u64) HType {
    return HType{ .Con = .{ .name = testName(base, id), .args = &.{} } };
}

/// Arena-allocate a nullary Con so its address can be taken for Fun.arg/res.
fn dupCon0(alloc: std.mem.Allocator, base: []const u8, id: u64) !*HType {
    const p = try alloc.create(HType);
    p.* = con0(base, id);
    return p;
}

// ── solve: success cases ───────────────────────────────────────────────

test "solve: empty constraint set produces no diagnostics" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena.allocator());

    const constraints: []Constraint = &.{};
    try solve(constraints, arena.allocator(), &diags, null);
    try testing.expect(!diags.hasErrors());
}

test "solve: single Int ~ Int constraint succeeds" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena.allocator());

    var constraints = [_]Constraint{.{ .Eq = .{
        .lhs = con0("Int", 0),
        .rhs = con0("Int", 0),
        .span = testSpan(),
    } }};
    try solve(&constraints, arena.allocator(), &diags, null);
    try testing.expect(!diags.hasErrors());
}

test "solve: ?0 ~ Int solves metavar" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    var constraints = [_]Constraint{.{ .Eq = .{
        .lhs = HType{ .Meta = mv },
        .rhs = con0("Int", 0),
        .span = testSpan(),
    } }};
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(!diags.hasErrors());

    // The metavar in the constraint should now be solved to Int.
    const chased = constraints[0].Eq.lhs.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

test "solve: multiple independent constraints all solved" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    const mv0 = supply.fresh();
    const mv1 = supply.fresh();
    var constraints = [_]Constraint{
        .{ .Eq = .{ .lhs = HType{ .Meta = mv0 }, .rhs = con0("Int", 0), .span = testSpan() } },
        .{ .Eq = .{ .lhs = HType{ .Meta = mv1 }, .rhs = con0("Bool", 1), .span = testSpan() } },
    };
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(!diags.hasErrors());

    try testing.expectEqualStrings("Int", constraints[0].Eq.lhs.chase().Con.name.base);
    try testing.expectEqualStrings("Bool", constraints[1].Eq.lhs.chase().Con.name.base);
}

// ── solve: failure cases ───────────────────────────────────────────────

test "solve: Int ~ Bool emits TypeMismatch diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var constraints = [_]Constraint{.{ .Eq = .{
        .lhs = con0("Int", 0),
        .rhs = con0("Bool", 1),
        .span = testSpan(),
    } }};
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
    try testing.expectEqual(DiagnosticCode.type_error, diags.diagnostics.items[0].code);
}

test "solve: ?0 ~ [?0] emits InfiniteType diagnostic" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    const meta_ty = HType{ .Meta = mv };
    const args = [_]HType{meta_ty};
    var constraints = [_]Constraint{.{ .Eq = .{
        .lhs = meta_ty,
        .rhs = HType{ .Con = .{ .name = testName("[]", 99), .args = &args } },
        .span = testSpan(),
    } }};
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(diags.hasErrors());
    // Message should mention "occurs check"
    try testing.expect(std.mem.indexOf(u8, diags.diagnostics.items[0].message, "occurs check") != null);
}

test "solve: conflicting constraints both reported" {
    // ?0 ~ Int, then ?0 ~ Bool — the second should fail after ?0 is solved to Int.
    //
    // For the mutation on constraint[0] to be visible when solving constraint[1],
    // both `lhs` fields must share the same MetaVar storage.  We achieve this by
    // allocating the MetaVar's HType on the arena and building each constraint's
    // `lhs` as a `Fun` that references the shared heap cell.  A simpler way is
    // to allocate the shared HType and use `HType{ .Fun = .{ .arg = shared, ... } }`
    // so both constraints hold a pointer to the *same* MetaVar node.
    //
    // Concretely: build `lhs = ?0 -> ()` for both constraints, where the `arg`
    // pointer is the same heap cell.  After the first solve, `shared.Meta.ref`
    // points to `Int`, and the second solve unifies `Int -> () ~ Bool -> ()`,
    // which fails with TypeMismatch.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    // Allocate the shared metavar cell on the arena so both constraints
    // reference the same underlying HType node.
    const shared = try alloc.create(HType);
    shared.* = HType{ .Meta = supply.fresh() };
    var unit_ty = con0("()", 99);

    var constraints = [_]Constraint{
        .{ .Eq = .{ .lhs = HType{ .Fun = .{ .arg = shared, .res = &unit_ty } }, .rhs = HType{ .Fun = .{ .arg = try dupCon0(alloc, "Int", 0), .res = &unit_ty } }, .span = testSpan() } },
        .{ .Eq = .{ .lhs = HType{ .Fun = .{ .arg = shared, .res = &unit_ty } }, .rhs = HType{ .Fun = .{ .arg = try dupCon0(alloc, "Bool", 1), .res = &unit_ty } }, .span = testSpan() } },
    };
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(diags.hasErrors());
    // The second constraint fails (Int vs Bool after ?0 = Int).
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
}

test "solve: diagnostic carries correct source span" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const span = SourceSpan.init(
        SourcePos.init(1, 42, 5),
        SourcePos.init(1, 42, 12),
    );
    var constraints = [_]Constraint{.{ .Eq = .{
        .lhs = con0("Int", 0),
        .rhs = con0("Bool", 1),
        .span = span,
    } }};
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(u32, 42), diags.diagnostics.items[0].span.start.line);
    try testing.expectEqual(@as(u32, 5), diags.diagnostics.items[0].span.start.column);
}

// ── formatHType ────────────────────────────────────────────────────────

test "formatHType: nullary Con" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const s = try formatHType(arena.allocator(), con0("Int", 0));
    try testing.expectEqualStrings("Int", s);
}

test "formatHType: unsolved Meta" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const ty = HType{ .Meta = MetaVar{ .id = 7, .ref = null } };
    const s = try formatHType(arena.allocator(), ty);
    try testing.expectEqualStrings("?7", s);
}

test "formatHType: Fun type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var int_ty = con0("Int", 0);
    var bool_ty = con0("Bool", 1);
    const ty = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };
    const s = try formatHType(alloc, ty);
    try testing.expectEqualStrings("Int -> Bool", s);
}

test "formatHType: list type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const char_ty = con0("Char", 0);
    const args = [_]HType{char_ty};
    const ty = HType{ .Con = .{ .name = testName("[]", 1), .args = &args } };
    const s = try formatHType(alloc, ty);
    try testing.expectEqualStrings("[Char]", s);
}

test "formatHType: solved Meta renders as solution" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var int_ty = con0("Int", 0);
    const ty = HType{ .Meta = MetaVar{ .id = 0, .ref = &int_ty } };
    const s = try formatHType(alloc, ty);
    try testing.expectEqualStrings("Int", s);
}

// ── Payload round-trip tests ────────────────────────────────────────────

test "solver: type mismatch diagnostic carries structured payload" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var constraints = [_]Constraint{.{ .Eq = .{
        .lhs = con0("Int", 0),
        .rhs = con0("Bool", 1),
        .span = testSpan(),
    } }};
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), diags.errorCount());

    const diag = diags.diagnostics.items[0];
    try testing.expect(diag.payload != null);

    switch (diag.payload.?) {
        .type_error => |te| {
            try testing.expect(te == .mismatch);
            const m = te.mismatch;
            try testing.expect(m.lhs == .Con);
            try testing.expectEqualStrings("Int", m.lhs.Con.name.base);
            try testing.expect(m.rhs == .Con);
            try testing.expectEqualStrings("Bool", m.rhs.Con.name.base);
        },
    }
}

test "solver: infinite type diagnostic carries structured payload" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    const meta_ty = HType{ .Meta = mv };
    const args = [_]HType{meta_ty};
    var constraints = [_]Constraint{.{ .Eq = .{
        .lhs = meta_ty,
        .rhs = HType{ .Con = .{ .name = testName("[]", 99), .args = &args } },
        .span = testSpan(),
    } }};
    try solve(&constraints, alloc, &diags, null);
    try testing.expect(diags.hasErrors());

    const diag = diags.diagnostics.items[0];
    try testing.expect(diag.payload != null);

    switch (diag.payload.?) {
        .type_error => |te| {
            try testing.expect(te == .infinite_type);
            const it = te.infinite_type;
            try testing.expectEqual(mv.id, it.meta.id);
            try testing.expect(it.ty == .Con);
        },
    }
}

// ── Class constraint resolution tests ──────────────────────────────────

const Known = @import("../naming/known.zig");

test "solve: class constraint with matching instance resolves to evidence" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // Set up a ClassEnv with class Eq and instance Eq Int.
    var class_env = ClassEnv.init(alloc);
    defer class_env.deinit();

    try class_env.addClass(.{
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{},
    });
    try class_env.addInstance(.{
        .class_name = Known.Class.Eq,
        .head = con0("Int", Known.Type.Int.unique.value),
        .context = &.{},
        .span = testSpan(),
    });

    // Constraint: Eq Int
    var constraints = [_]Constraint{.{ .Class = .{
        .class_name = Known.Class.Eq,
        .ty = con0("Int", Known.Type.Int.unique.value),
        .span = testSpan(),
    } }};

    try solve(&constraints, alloc, &diags, &class_env);
    try testing.expect(!diags.hasErrors());
    // Evidence should be filled in.
    try testing.expect(constraints[0].Class.evidence != null);
    try testing.expect(constraints[0].Class.evidence.?.* == .instance);
}

test "solve: class constraint with no matching instance emits missing_instance" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // Set up ClassEnv with class Eq but NO instances.
    var class_env = ClassEnv.init(alloc);
    defer class_env.deinit();

    try class_env.addClass(.{
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{},
    });

    // Constraint: Eq Int (no instance exists)
    var constraints = [_]Constraint{.{ .Class = .{
        .class_name = Known.Class.Eq,
        .ty = con0("Int", Known.Type.Int.unique.value),
        .span = testSpan(),
    } }};

    try solve(&constraints, alloc, &diags, &class_env);
    try testing.expect(diags.hasErrors());
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
    // Should mention "no instance"
    try testing.expect(std.mem.indexOf(u8, diags.diagnostics.items[0].message, "no instance") != null);
}

test "solve: class constraint with rigid type defers (no error)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var class_env = ClassEnv.init(alloc);
    defer class_env.deinit();

    try class_env.addClass(.{
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{},
    });

    // Constraint: Eq a (rigid — should defer, not error)
    var constraints = [_]Constraint{.{ .Class = .{
        .class_name = Known.Class.Eq,
        .ty = HType{ .Rigid = testName("a", 42) },
        .span = testSpan(),
    } }};

    try solve(&constraints, alloc, &diags, &class_env);
    try testing.expect(!diags.hasErrors());
    // No evidence assigned for rigid — it becomes a dictionary parameter.
    try testing.expect(constraints[0].Class.evidence == null);
}

test "solve: mixed Eq and Class constraints both resolved" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var class_env = ClassEnv.init(alloc);
    defer class_env.deinit();

    try class_env.addClass(.{
        .name = Known.Class.Eq,
        .tyvar = 5000,
        .superclasses = &.{},
        .methods = &.{},
    });
    try class_env.addInstance(.{
        .class_name = Known.Class.Eq,
        .head = con0("Int", Known.Type.Int.unique.value),
        .context = &.{},
        .span = testSpan(),
    });

    var supply = MetaVarSupply{};
    const mv = supply.fresh();

    var constraints = [_]Constraint{
        // Equality: ?0 ~ Int
        .{ .Eq = .{
            .lhs = HType{ .Meta = mv },
            .rhs = con0("Int", Known.Type.Int.unique.value),
            .span = testSpan(),
        } },
        // Class: Eq Int
        .{ .Class = .{
            .class_name = Known.Class.Eq,
            .ty = con0("Int", Known.Type.Int.unique.value),
            .span = testSpan(),
        } },
    };

    try solve(&constraints, alloc, &diags, &class_env);
    try testing.expect(!diags.hasErrors());

    // Equality solved
    try testing.expectEqualStrings("Int", constraints[0].Eq.lhs.chase().Con.name.base);
    // Class constraint has evidence
    try testing.expect(constraints[1].Class.evidence != null);
}
