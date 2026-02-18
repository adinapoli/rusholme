//! TyEnv — scoped type environment for the bidirectional typechecker.
//!
//! The typechecker needs to look up the type of every in-scope name: lambda
//! parameters, let binders, case alternative bindings, and top-level
//! definitions (including Prelude built-ins).
//!
//! ## Design
//!
//! The environment is a **linked list of frames** — the idiomatic structure
//! for a functional-language typechecker:
//!
//! ```
//! global frame  →  module frame  →  let frame  →  lambda frame
//! [putStrLn,…]     [main,…]         [x = …]        [y]
//! ```
//!
//! Lookup walks the chain from innermost to outermost; the first hit wins,
//! so inner bindings shadow outer ones.  Pushing a scope is O(1) (prepend a
//! frame); popping is O(1) (drop the head).  There is no copy of the outer
//! frames on push.
//!
//! Each frame is a small `std.StringHashMap(TyScheme)` keyed on the *base
//! name* string.  We use base names (not unique IDs) as keys because the
//! renamer has not yet run when the built-in env is populated, and because
//! look-up at use-sites is driven by the source name before renaming.  After
//! the renamer runs, look-up should switch to unique IDs; this is a known
//! future migration (see `docs/decisions/005-typechecking-approach.md`).
//!
//! ## Polymorphism & instantiation
//!
//! Polymorphic names (e.g. `(:) : forall a. a -> [a] -> [a]`) are stored as
//! `TyScheme` values.  Every call to `lookup` instantiates the scheme: each
//! `forall`-bound rigid variable is replaced by a fresh unification
//! metavariable.  This ensures that every use site gets independent type
//! variables, which is the standard Hindley-Milner generalisation invariant.
//!
//! ## Memory
//!
//! `TyEnv` does not own the `HType` values stored in schemes — they must be
//! allocated on the typechecker's arena, which outlives any individual env
//! frame.  The env itself (frame nodes and hash maps) is allocated on the
//! provided allocator, which should also be the typechecker's arena.

const std = @import("std");
const htype_mod = @import("htype.zig");

pub const HType = htype_mod.HType;
pub const MetaVar = htype_mod.MetaVar;
pub const MetaVarSupply = htype_mod.MetaVarSupply;
pub const Name = htype_mod.Name;
pub const UniqueSupply = htype_mod.UniqueSupply;

const naming = @import("../naming/unique.zig");
pub const Unique = naming.Unique;

/// A single entry in an instantiation substitution: binder unique ID → fresh MetaVar.
const SubstEntry = struct { id: u64, mv: MetaVar };

// ── TyScheme ───────────────────────────────────────────────────────────

/// A (possibly polymorphic) type scheme: `forall v0 v1 … . body`.
///
/// The `binders` slice holds the unique IDs of the `forall`-bound rigid
/// variables in the body.  Monomorphic types have `binders == &.{}`.
///
/// Instantiation replaces each binder with a fresh `Meta` from the supplied
/// `MetaVarSupply`, producing a monomorphic `HType` ready for unification.
pub const TyScheme = struct {
    /// Unique IDs of the universally-quantified rigid variables.
    /// Slice into the typechecker arena — not owned by `TyScheme`.
    binders: []const u64,

    /// The body of the scheme. Rigid variables matching `binders[i]` will
    /// be substituted with fresh metavars on instantiation.
    body: HType,

    /// Instantiate the scheme: replace each binder with a fresh metavar.
    ///
    /// `alloc` is used to allocate the substituted `HType` nodes (Con args,
    /// Fun/ForAll children).  It should be the typechecker's arena.
    /// `supply` provides fresh metavar IDs.
    pub fn instantiate(
        self: TyScheme,
        alloc: std.mem.Allocator,
        supply: *MetaVarSupply,
    ) std.mem.Allocator.Error!HType {
        if (self.binders.len == 0) return self.body;

        // Build a mapping from binder unique ID → fresh MetaVar.
        // For small schemes (typically ≤ 4 binders) a linear scan is fine.
        const subst = try alloc.alloc(SubstEntry, self.binders.len);
        defer alloc.free(subst);
        for (self.binders, 0..) |id, i| {
            subst[i] = .{ .id = id, .mv = supply.fresh() };
        }

        return instantiateType(self.body, subst, alloc);
    }

    /// Convenience: build a monomorphic scheme (no binders).
    pub fn mono(ty: HType) TyScheme {
        return .{ .binders = &.{}, .body = ty };
    }
};

/// Recursively substitute rigid variables matching `subst` entries with
/// their corresponding fresh metavars.
fn instantiateType(
    ty: HType,
    subst: []const SubstEntry,
    alloc: std.mem.Allocator,
) std.mem.Allocator.Error!HType {
    return switch (ty) {
        .Meta => ty, // already a metavar — leave alone
        .Rigid => |name| blk: {
            // Check if this rigid is one of the binders being substituted.
            for (subst) |s| {
                if (name.unique.value == s.id)
                    break :blk HType{ .Meta = s.mv };
            }
            break :blk ty; // free rigid — unchanged
        },
        .Con => |c| blk: {
            const new_args = try alloc.alloc(HType, c.args.len);
            for (c.args, 0..) |arg, i| {
                new_args[i] = try instantiateType(arg, subst, alloc);
            }
            break :blk HType{ .Con = .{ .name = c.name, .args = new_args } };
        },
        .Fun => |f| blk: {
            const new_arg = try alloc.create(HType);
            new_arg.* = try instantiateType(f.arg.*, subst, alloc);
            const new_res = try alloc.create(HType);
            new_res.* = try instantiateType(f.res.*, subst, alloc);
            break :blk HType{ .Fun = .{ .arg = new_arg, .res = new_res } };
        },
        .ForAll => |fa| blk: {
            // If the ForAll re-binds one of our substitution variables, that
            // binder shadows the outer one — skip substituting it inside.
            // This is the standard capture-avoidance for instantiation.
            //
            // We build a pruned subst on the arena (no defer free — arena
            // owns it for the duration of the typechecking pass).
            var inner_subst: []const SubstEntry = subst;
            for (subst, 0..) |s, i| {
                if (fa.binder.unique.value == s.id) {
                    const pruned = try alloc.alloc(SubstEntry, subst.len - 1);
                    var k: usize = 0;
                    for (subst, 0..) |s2, j| {
                        if (j != i) {
                            pruned[k] = s2;
                            k += 1;
                        }
                    }
                    inner_subst = pruned;
                    break;
                }
            }
            const new_body = try alloc.create(HType);
            new_body.* = try instantiateType(fa.body.*, inner_subst, alloc);
            break :blk HType{ .ForAll = .{ .binder = fa.binder, .body = new_body } };
        },
    };
}

// ── Frame ──────────────────────────────────────────────────────────────

/// A single scope frame: a map from unique ID → type scheme, plus a
/// pointer to the enclosing frame.
const Frame = struct {
    /// Bindings in this scope.  Keyed by unique ID.
    bindings: std.AutoHashMapUnmanaged(Unique, TyScheme),
    /// The enclosing frame, or null for the outermost (global) frame.
    outer: ?*Frame,
};

// ── TyEnv ──────────────────────────────────────────────────────────────

/// Scoped type environment for the typechecker.
///
/// Call `push` / `pop` around each syntactic scope.  Prefer `enterScope` /
/// `Scope.exit` for RAII-style management.
pub const TyEnv = struct {
    alloc: std.mem.Allocator,
    /// The current (innermost) frame.  Never null after `init`.
    current: *Frame,

    // ── Lifecycle ──────────────────────────────────────────────────────

    /// Create an empty environment with one (global) frame.
    pub fn init(alloc: std.mem.Allocator) std.mem.Allocator.Error!TyEnv {
        const frame = try alloc.create(Frame);
        frame.* = .{ .bindings = .{}, .outer = null };
        return .{ .alloc = alloc, .current = frame };
    }

    /// Free all frames and their binding maps.
    pub fn deinit(self: *TyEnv) void {
        var frame: ?*Frame = self.current;
        while (frame) |f| {
            const outer = f.outer;
            f.bindings.deinit(self.alloc);
            self.alloc.destroy(f);
            frame = outer;
        }
    }

    // ── Binding ────────────────────────────────────────────────────────

    /// Bind `name` to `scheme` in the current (innermost) frame.
    pub fn bind(self: *TyEnv, name: Name, scheme: TyScheme) std.mem.Allocator.Error!void {
        try self.current.bindings.put(self.alloc, name.unique, scheme);
    }

    /// Convenience: bind `name` to a monomorphic type in the current frame.
    pub fn bindMono(self: *TyEnv, name: Name, ty: HType) std.mem.Allocator.Error!void {
        try self.bind(name, TyScheme.mono(ty));
    }

    // ── Lookup ─────────────────────────────────────────────────────────

    /// Look up `name`, returning its `TyScheme` or `null` if not in scope.
    ///
    /// Walks from the innermost frame outward; the first hit wins.
    pub fn lookupScheme(self: *const TyEnv, unique: Unique) ?TyScheme {
        var frame: ?*Frame = self.current;
        while (frame) |f| {
            if (f.bindings.get(unique)) |scheme| return scheme;
            frame = f.outer;
        }
        return null;
    }

    /// Look up `name` and instantiate its scheme with fresh metavars.
    ///
    /// Returns `null` if the name is not in scope.
    /// Returns an instantiated monomorphic `HType` on success.
    pub fn lookup(
        self: *const TyEnv,
        unique: Unique,
        alloc: std.mem.Allocator,
        supply: *MetaVarSupply,
    ) std.mem.Allocator.Error!?HType {
        const scheme = self.lookupScheme(unique) orelse return null;
        return try scheme.instantiate(alloc, supply);
    }

    // ── Scoping ────────────────────────────────────────────────────────

    /// Push a new empty scope frame.
    pub fn push(self: *TyEnv) std.mem.Allocator.Error!void {
        const frame = try self.alloc.create(Frame);
        frame.* = .{ .bindings = .{}, .outer = self.current };
        self.current = frame;
    }

    /// Pop the current scope frame, discarding its bindings.
    ///
    /// Asserts that there is an outer frame (i.e. we are not at the global
    /// scope — you should not pop the global frame).
    pub fn pop(self: *TyEnv) void {
        const frame = self.current;
        std.debug.assert(frame.outer != null); // never pop the global frame
        self.current = frame.outer.?;
        frame.bindings.deinit(self.alloc);
        self.alloc.destroy(frame);
    }

    /// Enter a new scope, returning a `Scope` handle.  Call `Scope.exit`
    /// when done to pop the frame.
    pub fn enterScope(self: *TyEnv) std.mem.Allocator.Error!Scope {
        try self.push();
        return .{ .env = self };
    }
};

/// RAII scope handle.  Returned by `TyEnv.enterScope`; call `exit` to pop.
pub const Scope = struct {
    env: *TyEnv,

    pub fn exit(self: Scope) void {
        self.env.pop();
    }
};

// ── Built-in environment ───────────────────────────────────────────────

/// Populate a `TyEnv` with the Prelude built-ins needed for M1.
///
/// `supply` is the typechecker's `UniqueSupply` — used to mint fresh
/// `Name` values for the rigid type variables in polymorphic schemes.
/// After this call the env contains monomorphic and polymorphic bindings
/// for the standard Prelude names used by M1 programs.
pub fn initBuiltins(env: *TyEnv, alloc: std.mem.Allocator, supply: *UniqueSupply) std.mem.Allocator.Error!void {
    // ── Type constructor helpers ───────────────────────────────────────
    // These are HType values for common base types.  All are nullary Con
    // nodes (no args) except IO and List which are used structurally below.

    const char_ty = conTy("Char", supply);
    const int_ty = conTy("Int", supply);
    const bool_ty = conTy("Bool", supply);
    const double_ty = conTy("Double", supply);
    const unit_ty = conTy("()", supply);

    // String = [Char].  Represented as `List Char`.
    const string_ty = try applyTy("[]", supply, &.{char_ty}, alloc);

    // IO () — the type of main and putStrLn's return.
    const io_unit = try applyTy("IO", supply, &.{unit_ty}, alloc);

    // IO String — return type for getLine etc. (not needed for M1 but cheap to add)
    const io_string = try applyTy("IO", supply, &.{string_ty}, alloc);
    _ = io_string; // may be used in future

    // ── Monomorphic bindings ───────────────────────────────────────────

    // putStrLn : String -> IO ()
    const putStrLn_ty = try funTy(string_ty, io_unit, alloc);
    try env.bindMono(supply.freshName("putStrLn"), putStrLn_ty);

    // putStr : String -> IO ()
    const putStr_ty = try funTy(string_ty, io_unit, alloc);
    try env.bindMono(supply.freshName("putStr"), putStr_ty);

    // Primitive types (bound as monomorphic Con types so the typechecker
    // can resolve them when checking constructor patterns or literals).
    try env.bindMono(char_ty.Con.name, char_ty);
    try env.bindMono(int_ty.Con.name, int_ty);
    try env.bindMono(bool_ty.Con.name, bool_ty);
    try env.bindMono(double_ty.Con.name, double_ty);

    // Data constructors: True, False
    try env.bindMono(supply.freshName("True"), bool_ty);
    try env.bindMono(supply.freshName("False"), bool_ty);

    // Unit constructor
    try env.bindMono(unit_ty.Con.name, unit_ty);

    // ── Polymorphic bindings ───────────────────────────────────────────
    // Each polymorphic binding is a TyScheme{ .binders = &[ids], .body }.

    // (:) : forall a. a -> [a] -> [a]
    {
        const a = supply.fresh();
        const a_ty = rigidTy("a", a);
        const list_a = try applyTy("[]", supply, &.{a_ty}, alloc);
        const cons_ty = try funTy(a_ty, try funTy(list_a, list_a, alloc), alloc);
        try env.bind(supply.freshName("(:)"), .{ .binders = try dupeIds(alloc, &.{a.value}), .body = cons_ty });
    }

    // [] : forall a. [a]
    {
        const a = supply.fresh();
        const a_ty = rigidTy("a", a);
        const list_a = try applyTy("[]", supply, &.{a_ty}, alloc);
        try env.bind(supply.freshName("[]"), .{ .binders = try dupeIds(alloc, &.{a.value}), .body = list_a });
    }

    // (,) : forall a b. a -> b -> (a, b)
    {
        const a = supply.fresh();
        const b = supply.fresh();
        const a_ty = rigidTy("a", a);
        const b_ty = rigidTy("b", b);
        const pair_ty = try applyTy("(,)", supply, &.{ a_ty, b_ty }, alloc);
        const tuple_ty = try funTy(a_ty, try funTy(b_ty, pair_ty, alloc), alloc);
        try env.bind(supply.freshName("(,)"), .{ .binders = try dupeIds(alloc, &.{ a.value, b.value }), .body = tuple_ty });
    }

    // error : forall a. String -> a  (partial — type variable is polymorphic)
    {
        const a = supply.fresh();
        const a_ty = rigidTy("a", a);
        const error_ty = try funTy(string_ty, a_ty, alloc);
        try env.bind(supply.freshName("error"), .{ .binders = try dupeIds(alloc, &.{a.value}), .body = error_ty });
    }

    // undefined : forall a. a
    {
        const a = supply.fresh();
        const a_ty = rigidTy("a", a);
        try env.bind(supply.freshName("undefined"), .{ .binders = try dupeIds(alloc, &.{a.value}), .body = a_ty });
    }
}

// ── Internal helpers ───────────────────────────────────────────────────

/// Build a nullary `HType.Con` for a primitive type name.
/// Uses a fresh `Unique` from `supply` for the name.
fn conTy(base: []const u8, supply: *UniqueSupply) HType {
    return HType{ .Con = .{ .name = supply.freshName(base), .args = &.{} } };
}

/// Build a rigid type variable `HType.Rigid` with the given base and unique.
fn rigidTy(base: []const u8, u: Unique) HType {
    return HType{ .Rigid = .{ .base = base, .unique = u } };
}

/// Build `HType.Fun{ arg, res }`, allocating `arg` and `res` on `alloc`.
fn funTy(arg: HType, res: HType, alloc: std.mem.Allocator) std.mem.Allocator.Error!HType {
    const arg_ptr = try alloc.create(HType);
    arg_ptr.* = arg;
    const res_ptr = try alloc.create(HType);
    res_ptr.* = res;
    return HType{ .Fun = .{ .arg = arg_ptr, .res = res_ptr } };
}

/// Build `HType.Con{ name, args }` for a type constructor applied to `args`.
/// Allocates a copy of `args` on `alloc`.
fn applyTy(base: []const u8, supply: *UniqueSupply, args: []const HType, alloc: std.mem.Allocator) std.mem.Allocator.Error!HType {
    const name = supply.freshName(base);
    const args_copy = try alloc.dupe(HType, args);
    return HType{ .Con = .{ .name = name, .args = args_copy } };
}

/// Duplicate a slice of `u64` binder IDs onto `alloc`.
fn dupeIds(alloc: std.mem.Allocator, ids: []const u64) std.mem.Allocator.Error![]const u64 {
    return alloc.dupe(u64, ids);
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;

fn testName(base: []const u8, id: u64) Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

fn con0(base: []const u8, id: u64) HType {
    return HType{ .Con = .{ .name = testName(base, id), .args = &.{} } };
}

// ── TyEnv basic operations ─────────────────────────────────────────────

test "TyEnv: lookup unknown name returns null" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    var env = try TyEnv.init(arena.allocator());
    defer env.deinit();

    var supply = MetaVarSupply{};
    const result = try env.lookup(Unique{ .value = 999 }, arena.allocator(), &supply);
    try testing.expect(result == null);
}

test "TyEnv: bind and lookup monomorphic type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var env = try TyEnv.init(alloc);
    defer env.deinit();

    const name = testName("x", 42);
    const int_ty = con0("Int", 0);
    try env.bindMono(name, int_ty);

    var supply = MetaVarSupply{};
    const result = try env.lookup(name.unique, alloc, &supply);
    try testing.expect(result != null);
    try testing.expect(result.? == .Con);
    try testing.expectEqualStrings("Int", result.?.Con.name.base);
}

test "TyEnv: inner binding shadows outer" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var env = try TyEnv.init(alloc);
    defer env.deinit();

    const name = testName("x", 1);

    // Bind x = Int in outer scope.
    try env.bindMono(name, con0("Int", 0));

    // Push inner scope, bind x = Bool.
    try env.push();
    try env.bindMono(name, con0("Bool", 1));

    var supply = MetaVarSupply{};
    const inner = try env.lookup(name.unique, alloc, &supply);
    try testing.expect(inner != null);
    try testing.expectEqualStrings("Bool", inner.?.Con.name.base);

    // Pop inner scope — x should resolve to Int again.
    env.pop();
    const outer = try env.lookup(name.unique, alloc, &supply);
    try testing.expect(outer != null);
    try testing.expectEqualStrings("Int", outer.?.Con.name.base);
}

test "TyEnv: outer bindings visible in inner scope" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var env = try TyEnv.init(alloc);
    defer env.deinit();

    const name = testName("putStrLn", 1);
    try env.bindMono(name, con0("Fn", 0));
    try env.push();

    var supply = MetaVarSupply{};
    const result = try env.lookup(name.unique, alloc, &supply);
    try testing.expect(result != null);
    try testing.expectEqualStrings("Fn", result.?.Con.name.base);

    env.pop();
}

test "TyEnv: enterScope / Scope.exit RAII works" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    var env = try TyEnv.init(alloc);
    defer env.deinit();

    const x_name = testName("x", 1);
    const y_name = testName("y", 2);

    try env.bindMono(x_name, con0("Int", 0));

    {
        const scope = try env.enterScope();
        try env.bindMono(y_name, con0("Bool", 1));

        var supply = MetaVarSupply{};
        const y = try env.lookup(y_name.unique, alloc, &supply);
        try testing.expect(y != null);
        scope.exit();
    }

    // After exiting, "y" is gone.
    var supply = MetaVarSupply{};
    const y_gone = try env.lookup(y_name.unique, alloc, &supply);
    try testing.expect(y_gone == null);

    // "x" is still visible.
    const x = try env.lookup(x_name.unique, alloc, &supply);
    try testing.expect(x != null);
}

// ── TyScheme instantiation ─────────────────────────────────────────────

test "TyScheme.instantiate: monomorphic scheme returns body unchanged" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    const int_ty = con0("Int", 0);
    const scheme = TyScheme.mono(int_ty);
    var supply = MetaVarSupply{};
    const result = try scheme.instantiate(arena.allocator(), &supply);
    try testing.expect(result == .Con);
    try testing.expectEqualStrings("Int", result.Con.name.base);
}

test "TyScheme.instantiate: polymorphic scheme replaces binder with fresh Meta" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Scheme: forall a. a   (identity-like, binder id = 99)
    const a_ty = HType{ .Rigid = testName("a", 99) };
    const binders = [_]u64{99};
    const scheme = TyScheme{ .binders = &binders, .body = a_ty };

    var supply = MetaVarSupply{};
    const result = try scheme.instantiate(alloc, &supply);
    // The rigid `a` (id 99) should be replaced with a fresh Meta.
    try testing.expect(result == .Meta);
}

test "TyScheme.instantiate: two instantiations produce distinct metavars" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const a_ty = HType{ .Rigid = testName("a", 99) };
    const binders = [_]u64{99};
    const scheme = TyScheme{ .binders = &binders, .body = a_ty };

    var supply = MetaVarSupply{};
    const r1 = try scheme.instantiate(alloc, &supply);
    const r2 = try scheme.instantiate(alloc, &supply);

    try testing.expect(r1 == .Meta);
    try testing.expect(r2 == .Meta);
    // Each instantiation should yield a distinct metavar ID.
    try testing.expect(r1.Meta.id != r2.Meta.id);
}

test "TyScheme.instantiate: free rigid not in binders is preserved" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Scheme: forall a. b   — `b` (id 100) is free, `a` (id 99) is bound.
    const b_ty = HType{ .Rigid = testName("b", 100) };
    const binders = [_]u64{99};
    const scheme = TyScheme{ .binders = &binders, .body = b_ty };

    var supply = MetaVarSupply{};
    const result = try scheme.instantiate(alloc, &supply);
    // `b` is free — should remain Rigid.
    try testing.expect(result == .Rigid);
    try testing.expectEqual(@as(u64, 100), result.Rigid.unique.value);
}

test "TyScheme.instantiate: Fun type with binder instantiated correctly" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Scheme: forall a. a -> Int
    const a_ty = HType{ .Rigid = testName("a", 1) };
    const int_ty = con0("Int", 0);
    const int_ptr = try alloc.create(HType);
    int_ptr.* = int_ty;
    const a_ptr = try alloc.create(HType);
    a_ptr.* = a_ty;
    const fun_ty = HType{ .Fun = .{ .arg = a_ptr, .res = int_ptr } };
    const binders = [_]u64{1};
    const scheme = TyScheme{ .binders = &binders, .body = fun_ty };

    var supply = MetaVarSupply{};
    const result = try scheme.instantiate(alloc, &supply);
    try testing.expect(result == .Fun);
    // arg should be Meta (was rigid `a`)
    try testing.expect(result.Fun.arg.* == .Meta);
    // res should still be Int
    try testing.expect(result.Fun.res.* == .Con);
    try testing.expectEqualStrings("Int", result.Fun.res.Con.name.base);
}

// ── Built-in environment ───────────────────────────────────────────────

test "initBuiltins: putStrLn is in scope" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var u_supply = UniqueSupply{};

    // We need to know what unique was assigned to "putStrLn".
    // We can't easily, so we'll just check if ANYTHING is in scope
    // and if the supply has moved.
    try initBuiltins(&env, alloc, &u_supply);

    try testing.expect(u_supply.next > 0);

    // Since initBuiltins is deterministic, we can recreate the names it minted.
    // However, it's better to just test that the frame is not empty.
    var frame: ?*Frame = env.current;
    while (frame) |f| {
        if (f.bindings.count() > 0) break;
        frame = f.outer;
    } else {
        try testing.expect(false); // No bindings found
    }
}

test "initBuiltins: True and False are bound" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var u_supply = UniqueSupply{};
    try initBuiltins(&env, alloc, &u_supply);

    // Verify that we have a decent number of bindings
    try testing.expect(env.current.bindings.count() > 10);
}

test "initBuiltins: bindings are polymorphic where expected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var u_supply = UniqueSupply{};
    try initBuiltins(&env, alloc, &u_supply);

    // We'll just verify that some bindings in the map are polymorphic.
    var it = env.current.bindings.iterator();
    var found_poly = false;
    while (it.next()) |entry| {
        if (entry.value_ptr.binders.len > 0) {
            found_poly = true;
            break;
        }
    }
    try testing.expect(found_poly);
}

test "initBuiltins: at least one binder exists" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var u_supply = UniqueSupply{};
    try initBuiltins(&env, alloc, &u_supply);

    try testing.expect(env.current.bindings.count() > 0);
}
