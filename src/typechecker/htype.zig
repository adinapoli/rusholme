//! HType — the typechecker's internal type representation.
//!
//! During bidirectional type inference the typechecker works with
//! *partially-known* types.  A fresh metavariable `?0` stands for an unknown
//! type that will be filled in by the constraint solver.  `core.ir.CoreType`
//! has no such concept — it is a fully-resolved, immutable type produced only
//! after elaboration.  `HType` bridges the gap.
//!
//! ## Metavariable discipline
//!
//! Metavariables use mutable optional pointers (`?*HType`) rather than
//! threading an explicit substitution map through every recursive call.  This
//! is the standard technique used by GHC, Lean, and Agda.  The invariant is:
//!
//!   * All `HType` values are arena-allocated.  The typechecker owns a single
//!     `ArenaAllocator`; every `HType` node lives there.
//!   * A `MetaVar.ref` pointer either is `null` (unsolved) or points to
//!     another arena-allocated `HType` (the solution).
//!   * Solutions may themselves contain unsolved metavariables (i.e. chains
//!     are allowed); `toCore` follows chains to the end.
//!   * `HType` never escapes the typechecker.  Before the elaborator runs,
//!     every `HType` is converted to `CoreType` via `toCore`.
//!
//! ## References
//!
//! Dunfield & Krishnaswami, "Complete and Easy Bidirectional Typechecking
//! for Higher-Rank Polymorphism", ICFP 2013.
//! https://www.cl.cam.ac.uk/~nk480/bidir.pdf

const std = @import("std");
const naming = @import("../naming/unique.zig");
const core = @import("../core/ir.zig");

pub const Name = naming.Name;
pub const UniqueSupply = naming.UniqueSupply;
pub const CoreType = core.CoreType;

// ── MetaVar ────────────────────────────────────────────────────────────

/// A unification metavariable: a cell that starts unsolved (`ref == null`)
/// and is filled in by the constraint solver.
///
/// The `id` is used for the occurs check and for human-readable display
/// (e.g. `?42`).  Equality between metavars is identity: two `MetaVar`
/// values are the *same* variable iff they have the same `id`.
pub const MetaVar = struct {
    id: u32,

    /// Null means unsolved.  Non-null means the solver has set this
    /// metavar to the pointed-to `HType` (which may itself contain
    /// further unsolved metavars — follow the chain in `HType.chase`).
    ///
    /// This field is mutated by the solver; all other fields are immutable
    /// after construction.
    ref: ?*HType,

    /// Two metavariables are the same iff their ids match.
    pub fn eql(self: MetaVar, other: MetaVar) bool {
        return self.id == other.id;
    }

    /// True iff this metavar has been solved.
    pub fn isSolved(self: MetaVar) bool {
        return self.ref != null;
    }
};

// ── MetaVarSupply ──────────────────────────────────────────────────────

/// A monotonically-increasing counter for fresh metavariable IDs.
///
/// Analogous to `naming.UniqueSupply` but for metavariables.  Intentionally
/// separate so that the two ID spaces never overlap and can be displayed
/// with different sigils (`_42` vs `?42`).
pub const MetaVarSupply = struct {
    next: u32 = 0,

    /// Allocate a fresh, unsolved metavariable.
    pub fn fresh(self: *MetaVarSupply) MetaVar {
        const id = self.next;
        self.next += 1;
        return .{ .id = id, .ref = null };
    }
};

// ── HType ──────────────────────────────────────────────────────────────

/// The typechecker's internal type representation.
///
/// Structurally mirrors `core.ir.CoreType` but adds `Meta` (unification
/// metavariables) and uses `Rigid` instead of `TyVar` to emphasise that
/// rigid variables are *given*, not inferred.
///
/// After the constraint solver runs, every `Meta` that appears in an
/// `HType` reachable from the program must be solved.  `toCore` enforces
/// this by panicking on unsolved metavars — an unsolved metavar at that
/// point is a compiler bug, not a user error.
pub const HType = union(enum) {
    /// Unification metavariable — mutable, filled in by the solver.
    Meta: MetaVar,

    /// Rigid type variable introduced by a `forall` binder or a user-
    /// supplied type signature.  Rigid variables cannot be unified with
    /// arbitrary types (only with themselves).
    Rigid: Name,

    /// Type constructor application: `Maybe Int`, `IO ()`, bare `Int`.
    /// A nullary constructor like `Int` has `args == &.{}`.
    Con: struct { name: Name, args: []const HType },

    /// Function type: `a -> b`.
    Fun: struct { arg: *const HType, res: *const HType },

    /// Polymorphic type: `forall a. a -> a`.
    ForAll: struct { binder: Name, body: *const HType },

    // ── Metavariable utilities ─────────────────────────────────────────

    /// Follow a chain of solved metavariables to the first unsolved one
    /// or non-Meta node.
    ///
    /// Given `?0 → ?1 → Int`, `chase` on `?0` returns the `HType.Con`
    /// for `Int`.  If `self` is not a `Meta`, returns `self` unchanged.
    ///
    /// This is the core operation used by the unifier to avoid repeatedly
    /// traversing long chains.
    pub fn chase(self: HType) HType {
        var current = self;
        while (true) {
            switch (current) {
                .Meta => |mv| {
                    if (mv.ref) |next| {
                        current = next.*;
                    } else {
                        return current; // unsolved — stop
                    }
                },
                else => return current,
            }
        }
    }

    // ── Predicates ─────────────────────────────────────────────────────

    /// True iff the type is monomorphic: contains no `Meta` or `ForAll`.
    ///
    /// A monomorphic type is safe to use as a concrete type without
    /// further generalisation.
    pub fn isMono(self: HType) bool {
        return switch (self) {
            .Meta => false,
            .Rigid => true,
            .Con => |c| blk: {
                for (c.args) |arg| {
                    if (!arg.isMono()) break :blk false;
                }
                break :blk true;
            },
            .Fun => |f| f.arg.isMono() and f.res.isMono(),
            .ForAll => false,
        };
    }

    /// True iff the metavariable `id` appears free in `self`.
    ///
    /// Used by the unifier for the occurs check: before solving `?id := τ`,
    /// verify that `?id` does not appear in `τ`, which would produce an
    /// infinite type (e.g. `?0 ~ [?0]`).
    ///
    /// Follows solved metavar chains via `chase` so that the check is
    /// complete even when the type graph contains aliases.
    pub fn occursIn(self: HType, id: u32) bool {
        const current = self.chase();
        return switch (current) {
            .Meta => |mv| mv.id == id,
            .Rigid => false,
            .Con => |c| blk: {
                for (c.args) |arg| {
                    if (arg.occursIn(id)) break :blk true;
                }
                break :blk false;
            },
            .Fun => |f| f.arg.occursIn(id) or f.res.occursIn(id),
            .ForAll => |fa| fa.body.occursIn(id),
        };
    }

    // ── Conversion ─────────────────────────────────────────────────────

    /// Convert a fully-solved `HType` to `CoreType`.
    ///
    /// Allocates `CoreType` nodes using `alloc` (typically the elaborator's
    /// arena).  Follows all `MetaVar.ref` chains.
    ///
    /// Panics if any metavariable in the type remains unsolved — an unsolved
    /// metavar at elaboration time is a compiler bug (the solver should have
    /// caught all ambiguity as a type error before this point).
    pub fn toCore(self: HType, alloc: std.mem.Allocator) std.mem.Allocator.Error!CoreType {
        const current = self.chase();
        return switch (current) {
            .Meta => |mv| std.debug.panic(
                "HType.toCore: unsolved metavar ?{d} — constraint solver is incomplete",
                .{mv.id},
            ),
            .Rigid => |name| CoreType{ .TyVar = name },
            .Con => |c| {
                const core_args = try alloc.alloc(CoreType, c.args.len);
                for (c.args, 0..) |arg, i| {
                    core_args[i] = try arg.toCore(alloc);
                }
                return CoreType{ .TyCon = .{ .name = c.name, .args = core_args } };
            },
            .Fun => |f| {
                const core_arg = try alloc.create(CoreType);
                core_arg.* = try f.arg.toCore(alloc);
                const core_res = try alloc.create(CoreType);
                core_res.* = try f.res.toCore(alloc);
                return CoreType{ .FunTy = .{ .arg = core_arg, .res = core_res } };
            },
            .ForAll => |fa| {
                const core_body = try alloc.create(CoreType);
                core_body.* = try fa.body.toCore(alloc);
                return CoreType{ .ForAllTy = .{ .binder = fa.binder, .body = core_body } };
            },
        };
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

/// Helper: a `Name` for tests — unique ID is irrelevant, just needs to be
/// distinct from others in the same test.
fn testName(base: []const u8, id: u64) Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

/// Helper: `HType.Con` for a nullary type constructor (e.g. `Int`).
fn con0(name: []const u8, id: u64) HType {
    return .{ .Con = .{ .name = testName(name, id), .args = &.{} } };
}

// ── MetaVarSupply ──────────────────────────────────────────────────────

test "MetaVarSupply.fresh: produces sequential IDs" {
    var supply = MetaVarSupply{};
    const a = supply.fresh();
    const b = supply.fresh();
    const c = supply.fresh();
    try testing.expectEqual(@as(u32, 0), a.id);
    try testing.expectEqual(@as(u32, 1), b.id);
    try testing.expectEqual(@as(u32, 2), c.id);
}

test "MetaVarSupply.fresh: new metavars are unsolved" {
    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    try testing.expect(!mv.isSolved());
    try testing.expect(mv.ref == null);
}

test "MetaVar.eql: same id" {
    const a = MetaVar{ .id = 7, .ref = null };
    const b = MetaVar{ .id = 7, .ref = null };
    try testing.expect(a.eql(b));
}

test "MetaVar.eql: different ids" {
    const a = MetaVar{ .id = 0, .ref = null };
    const b = MetaVar{ .id = 1, .ref = null };
    try testing.expect(!a.eql(b));
}

// ── HType construction ─────────────────────────────────────────────────

test "HType.Meta: construction" {
    var supply = MetaVarSupply{};
    const mv = supply.fresh();
    const ty = HType{ .Meta = mv };
    try testing.expect(ty == .Meta);
    try testing.expectEqual(@as(u32, 0), ty.Meta.id);
}

test "HType.Rigid: construction" {
    const ty = HType{ .Rigid = testName("a", 1) };
    try testing.expect(ty == .Rigid);
    try testing.expectEqualStrings("a", ty.Rigid.base);
}

test "HType.Con: nullary (Int)" {
    const ty = con0("Int", 0);
    try testing.expect(ty == .Con);
    try testing.expectEqualStrings("Int", ty.Con.name.base);
    try testing.expectEqual(@as(usize, 0), ty.Con.args.len);
}

test "HType.Con: unary (Maybe Int)" {
    const int_ty = con0("Int", 0);
    const args = [_]HType{int_ty};
    const ty = HType{ .Con = .{ .name = testName("Maybe", 1), .args = &args } };
    try testing.expectEqual(@as(usize, 1), ty.Con.args.len);
    try testing.expectEqualStrings("Int", ty.Con.args[0].Con.name.base);
}

test "HType.Fun: construction" {
    const int_ty = con0("Int", 0);
    const bool_ty = con0("Bool", 1);
    const ty = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };
    try testing.expect(ty == .Fun);
    try testing.expectEqualStrings("Int", ty.Fun.arg.Con.name.base);
    try testing.expectEqualStrings("Bool", ty.Fun.res.Con.name.base);
}

test "HType.ForAll: construction" {
    const a_name = testName("a", 1);
    const body = HType{ .Rigid = a_name };
    const ty = HType{ .ForAll = .{ .binder = a_name, .body = &body } };
    try testing.expect(ty == .ForAll);
    try testing.expectEqualStrings("a", ty.ForAll.binder.base);
}

// ── HType.chase ────────────────────────────────────────────────────────

test "HType.chase: non-Meta returns self" {
    const ty = con0("Int", 0);
    const chased = ty.chase();
    try testing.expect(chased == .Con);
}

test "HType.chase: unsolved Meta returns self" {
    const mv = MetaVar{ .id = 0, .ref = null };
    const ty = HType{ .Meta = mv };
    const chased = ty.chase();
    try testing.expect(chased == .Meta);
    try testing.expectEqual(@as(u32, 0), chased.Meta.id);
}

test "HType.chase: solved Meta follows one link" {
    // ?0 → Int
    var int_ty = con0("Int", 0);
    const mv = MetaVar{ .id = 0, .ref = &int_ty };
    const ty = HType{ .Meta = mv };
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

test "HType.chase: follows chain of two solved metavars" {
    // ?0 → ?1 → Int
    var int_ty = con0("Int", 0);
    var mv1 = HType{ .Meta = MetaVar{ .id = 1, .ref = &int_ty } };
    const mv0 = MetaVar{ .id = 0, .ref = &mv1 };
    const ty = HType{ .Meta = mv0 };
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

// ── HType.isMono ───────────────────────────────────────────────────────

test "HType.isMono: nullary Con is mono" {
    try testing.expect(con0("Int", 0).isMono());
}

test "HType.isMono: Con with mono args is mono" {
    const int_ty = con0("Int", 0);
    const args = [_]HType{int_ty};
    const ty = HType{ .Con = .{ .name = testName("Maybe", 1), .args = &args } };
    try testing.expect(ty.isMono());
}

test "HType.isMono: Rigid is mono" {
    const ty = HType{ .Rigid = testName("a", 1) };
    try testing.expect(ty.isMono());
}

test "HType.isMono: Fun of two mono types is mono" {
    const int_ty = con0("Int", 0);
    const bool_ty = con0("Bool", 1);
    const ty = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };
    try testing.expect(ty.isMono());
}

test "HType.isMono: unsolved Meta is not mono" {
    const mv = MetaVar{ .id = 0, .ref = null };
    const ty = HType{ .Meta = mv };
    try testing.expect(!ty.isMono());
}

test "HType.isMono: Con containing a Meta is not mono" {
    const mv_ty = HType{ .Meta = MetaVar{ .id = 0, .ref = null } };
    const args = [_]HType{mv_ty};
    const ty = HType{ .Con = .{ .name = testName("Maybe", 1), .args = &args } };
    try testing.expect(!ty.isMono());
}

test "HType.isMono: ForAll is not mono" {
    const a_name = testName("a", 1);
    const body = HType{ .Rigid = a_name };
    const ty = HType{ .ForAll = .{ .binder = a_name, .body = &body } };
    try testing.expect(!ty.isMono());
}

// ── HType.occursIn ─────────────────────────────────────────────────────

test "HType.occursIn: unsolved Meta matches its own id" {
    const ty = HType{ .Meta = MetaVar{ .id = 3, .ref = null } };
    try testing.expect(ty.occursIn(3));
}

test "HType.occursIn: unsolved Meta does not match different id" {
    const ty = HType{ .Meta = MetaVar{ .id = 3, .ref = null } };
    try testing.expect(!ty.occursIn(7));
}

test "HType.occursIn: Rigid never matches" {
    const ty = HType{ .Rigid = testName("a", 1) };
    try testing.expect(!ty.occursIn(0));
}

test "HType.occursIn: Con with matching Meta arg" {
    const mv_ty = HType{ .Meta = MetaVar{ .id = 5, .ref = null } };
    const args = [_]HType{mv_ty};
    const ty = HType{ .Con = .{ .name = testName("Maybe", 1), .args = &args } };
    try testing.expect(ty.occursIn(5));
    try testing.expect(!ty.occursIn(0));
}

test "HType.occursIn: Fun arg contains Meta" {
    const mv_ty = HType{ .Meta = MetaVar{ .id = 2, .ref = null } };
    const bool_ty = con0("Bool", 1);
    const ty = HType{ .Fun = .{ .arg = &mv_ty, .res = &bool_ty } };
    try testing.expect(ty.occursIn(2));
    try testing.expect(!ty.occursIn(99));
}

test "HType.occursIn: Fun res contains Meta" {
    const int_ty = con0("Int", 0);
    const mv_ty = HType{ .Meta = MetaVar{ .id = 9, .ref = null } };
    const ty = HType{ .Fun = .{ .arg = &int_ty, .res = &mv_ty } };
    try testing.expect(ty.occursIn(9));
}

test "HType.occursIn: solved Meta follows chain" {
    // ?0 is solved to Int. Checking if ?1 occurs in ?0 should be false.
    var int_ty = con0("Int", 0);
    var mv_ty = HType{ .Meta = MetaVar{ .id = 0, .ref = &int_ty } };
    try testing.expect(!mv_ty.occursIn(1));
}

// ── HType.toCore ───────────────────────────────────────────────────────

test "HType.toCore: Rigid → TyVar" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const ty = HType{ .Rigid = testName("a", 1) };
    const ct = try ty.toCore(alloc);
    try testing.expect(ct == .TyVar);
    try testing.expectEqualStrings("a", ct.TyVar.base);
}

test "HType.toCore: nullary Con → TyCon" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const ty = con0("Int", 0);
    const ct = try ty.toCore(alloc);
    try testing.expect(ct == .TyCon);
    try testing.expectEqualStrings("Int", ct.TyCon.name.base);
    try testing.expectEqual(@as(usize, 0), ct.TyCon.args.len);
}

test "HType.toCore: Con with arg → TyCon with args" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const int_ty = con0("Int", 0);
    const args = [_]HType{int_ty};
    const ty = HType{ .Con = .{ .name = testName("Maybe", 1), .args = &args } };
    const ct = try ty.toCore(alloc);
    try testing.expect(ct == .TyCon);
    try testing.expectEqualStrings("Maybe", ct.TyCon.name.base);
    try testing.expectEqual(@as(usize, 1), ct.TyCon.args.len);
    try testing.expectEqualStrings("Int", ct.TyCon.args[0].TyCon.name.base);
}

test "HType.toCore: Fun → FunTy" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const int_ty = con0("Int", 0);
    const bool_ty = con0("Bool", 1);
    const ty = HType{ .Fun = .{ .arg = &int_ty, .res = &bool_ty } };
    const ct = try ty.toCore(alloc);
    try testing.expect(ct == .FunTy);
    try testing.expectEqualStrings("Int", ct.FunTy.arg.TyCon.name.base);
    try testing.expectEqualStrings("Bool", ct.FunTy.res.TyCon.name.base);
}

test "HType.toCore: ForAll → ForAllTy" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const a_name = testName("a", 1);
    const body = HType{ .Rigid = a_name };
    const ty = HType{ .ForAll = .{ .binder = a_name, .body = &body } };
    const ct = try ty.toCore(alloc);
    try testing.expect(ct == .ForAllTy);
    try testing.expectEqualStrings("a", ct.ForAllTy.binder.base);
    try testing.expect(ct.ForAllTy.body.* == .TyVar);
}

test "HType.toCore: solved Meta chain → CoreType" {
    // ?0 → ?1 → Int  should produce TyCon{ Int }
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var int_ty = con0("Int", 0);
    var mv1 = HType{ .Meta = MetaVar{ .id = 1, .ref = &int_ty } };
    const mv0 = MetaVar{ .id = 0, .ref = &mv1 };
    const ty = HType{ .Meta = mv0 };

    const ct = try ty.toCore(alloc);
    try testing.expect(ct == .TyCon);
    try testing.expectEqualStrings("Int", ct.TyCon.name.base);
}

test "HType.toCore: nested Fun with solved Meta" {
    // ?0 → Bool, then Int -> ?0 should produce Int -> Bool
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var bool_ty = con0("Bool", 1);
    var mv0_ty = HType{ .Meta = MetaVar{ .id = 0, .ref = &bool_ty } };
    const int_ty = con0("Int", 0);
    const fun_ty = HType{ .Fun = .{ .arg = &int_ty, .res = &mv0_ty } };

    const ct = try fun_ty.toCore(alloc);
    try testing.expect(ct == .FunTy);
    try testing.expectEqualStrings("Int", ct.FunTy.arg.TyCon.name.base);
    try testing.expectEqualStrings("Bool", ct.FunTy.res.TyCon.name.base);
}
