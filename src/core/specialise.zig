//! Dictionary specialisation — Core to Core transformation (#807).
//!
//! Eliminates class-method runtime dispatch when the dictionary is
//! statically known. The desugarer's dictionary-passing translation
//! (Wadler & Blott 1989) turns every class-method call into
//!
//!   (<) dict$Ord$Int x y      -- selector + dictionary + args
//!
//! where `(<)` is a selector that scrutinises the dictionary node and
//! calls the function stored in the method's slot. For monomorphic call
//! sites the dictionary is a top-level constant, so the dispatch can be
//! resolved at compile time:
//!
//!   primLtInt x y             -- direct call to the instance method
//!
//! The pass runs whole-program (all modules at once) because user
//! modules reference dictionaries defined in the Prelude.
//!
//! Algorithm:
//! 1. Scan all top-level binds, collecting:
//!    a. *Dictionaries*: binds whose RHS is a saturated application of a
//!       `MkDict$<Class>` constructor — recording the field expressions.
//!    b. *Selectors*: binds of the shape
//!         \dict -> \x0 .. xn -> case dict of MkDict$C f0 .. fm -> fi x0 .. xn
//!       recording the constructor unique and the method index `i`.
//! 2. Rewrite every sub-expression `App (Var selector) (Var dict)` to the
//!    dictionary's field expression at the method index, when that field
//!    is itself a variable. The rewrite deliberately targets the partial
//!    application node, so both saturated and partially-applied method
//!    calls specialise.
//!
//! Polymorphic call sites (dictionary is a lambda-bound parameter) are
//! left untouched — they still go through runtime dispatch.
//!
//! Reference: GHC's `GHC.Core.Opt.Specialise` (this pass is the
//! monomorphic-dictionary subset).

const std = @import("std");
const core = @import("ast.zig");
const Expr = core.Expr;
const Bind = core.Bind;
const BindPair = core.BindPair;
const Id = core.Id;
const Alt = core.Alt;
const CoreProgram = core.CoreProgram;

/// A class-method selector: scrutinises a `MkDict$C` node and returns
/// the field at `method_index`.
const SelectorInfo = struct {
    /// Unique of the `MkDict$<Class>` constructor the selector matches on.
    con_unique: u64,
    /// Which dictionary field the selector projects.
    method_index: usize,
};

/// A statically-known dictionary: a top-level `MkDict$C e0 .. en` value.
const DictInfo = struct {
    /// Unique of the `MkDict$<Class>` constructor at the application head.
    con_unique: u64,
    /// The field expressions, in application order.
    fields: []const *const Expr,
};

/// Environment shared across all modules of the program.
pub const SpecialiseEnv = struct {
    /// selector binder unique → selector shape
    selectors: std.AutoHashMapUnmanaged(u64, SelectorInfo) = .empty,
    /// dictionary binder unique → dictionary fields
    dicts: std.AutoHashMapUnmanaged(u64, DictInfo) = .empty,

    pub fn deinit(self: *SpecialiseEnv, alloc: std.mem.Allocator) void {
        self.selectors.deinit(alloc);
        self.dicts.deinit(alloc);
    }
};

/// Collect selectors and dictionaries from one module's top-level binds.
/// Call once per module (in any order) before rewriting.
pub fn collectEnv(
    alloc: std.mem.Allocator,
    env: *SpecialiseEnv,
    prog: CoreProgram,
) std.mem.Allocator.Error!void {
    for (prog.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| try collectPair(alloc, env, pair),
            .Rec => |pairs| for (pairs) |pair| try collectPair(alloc, env, pair),
        }
    }
}

fn collectPair(
    alloc: std.mem.Allocator,
    env: *SpecialiseEnv,
    pair: BindPair,
) std.mem.Allocator.Error!void {
    const unique = pair.binder.name.unique.value;
    if (try detectDict(alloc, pair.rhs)) |dict| {
        try env.dicts.put(alloc, unique, dict);
    }
    if (detectSelector(pair.rhs)) |sel| {
        try env.selectors.put(alloc, unique, sel);
    }
}

/// Is `MkDict$` the prefix of this variable's base name?
fn isMkDictName(id: Id) bool {
    return std.mem.startsWith(u8, id.name.base, "MkDict$");
}

/// Recognise `MkDict$C e0 .. en` application spines.
fn detectDict(
    alloc: std.mem.Allocator,
    rhs: *const Expr,
) std.mem.Allocator.Error!?DictInfo {
    // Walk down the application spine, counting arguments.
    var n_args: usize = 0;
    var cur = rhs;
    while (cur.* == .App) : (n_args += 1) cur = cur.App.fn_expr;
    if (cur.* != .Var or !isMkDictName(cur.Var)) return null;
    if (n_args == 0) return null;

    const fields = try alloc.alloc(*const Expr, n_args);
    var i = n_args;
    cur = rhs;
    while (cur.* == .App) : (cur = cur.App.fn_expr) {
        i -= 1;
        fields[i] = cur.App.arg;
    }
    return .{ .con_unique = cur.Var.name.unique.value, .fields = fields };
}

/// Recognise the selector shape the desugarer generates:
///   \dict -> \x0 .. xn -> case dict of MkDict$C f0 .. fm -> fi x0 .. xn
/// The argument lambdas and the application of `fi` are not validated
/// beyond locating `fi` at the head — the desugarer is the only producer
/// of this shape, and the head position is all the rewrite needs.
fn detectSelector(rhs: *const Expr) ?SelectorInfo {
    if (rhs.* != .Lam) return null;
    const dict_binder = rhs.Lam.binder.name.unique.value;

    // Skip the method-argument lambdas down to the case.
    var body = rhs.Lam.body;
    while (body.* == .Lam) body = body.Lam.body;
    if (body.* != .Case) return null;
    const case = body.Case;

    // The scrutinee must be the dictionary parameter itself.
    if (case.scrutinee.* != .Var) return null;
    if (case.scrutinee.Var.name.unique.value != dict_binder) return null;

    // Exactly one constructor alternative, on a MkDict$ constructor.
    if (case.alts.len != 1) return null;
    const alt = case.alts[0];
    if (alt.con != .DataAlt) return null;
    if (!std.mem.startsWith(u8, alt.con.DataAlt.base, "MkDict$")) return null;

    // The alternative body's head variable must be one of the field
    // binders; its position is the method index.
    var head = alt.body;
    while (head.* == .App) head = head.App.fn_expr;
    if (head.* != .Var) return null;
    const head_unique = head.Var.name.unique.value;
    for (alt.binders, 0..) |field_binder, idx| {
        if (field_binder.name.unique.value == head_unique) {
            return .{
                .con_unique = alt.con.DataAlt.unique.value,
                .method_index = idx,
            };
        }
    }
    return null;
}

/// Rewrite one module's program. Returns a program whose binds share
/// unchanged sub-trees with the input (everything is arena-allocated).
pub fn specialiseProgram(
    alloc: std.mem.Allocator,
    env: *const SpecialiseEnv,
    prog: CoreProgram,
) std.mem.Allocator.Error!CoreProgram {
    const new_binds = try alloc.alloc(Bind, prog.binds.len);
    for (prog.binds, new_binds) |bind, *out| {
        out.* = switch (bind) {
            .NonRec => |pair| .{ .NonRec = .{
                .binder = pair.binder,
                .rhs = try rewrite(alloc, env, pair.rhs),
            } },
            .Rec => |pairs| blk: {
                const new_pairs = try alloc.alloc(BindPair, pairs.len);
                for (pairs, new_pairs) |pair, *np| {
                    np.* = .{
                        .binder = pair.binder,
                        .rhs = try rewrite(alloc, env, pair.rhs),
                    };
                }
                break :blk .{ .Rec = new_pairs };
            },
        };
    }
    return .{ .data_decls = prog.data_decls, .binds = new_binds };
}

fn rewrite(
    alloc: std.mem.Allocator,
    env: *const SpecialiseEnv,
    expr: *const Expr,
) std.mem.Allocator.Error!*const Expr {
    switch (expr.*) {
        .Var, .Lit, .Type, .Coercion => return expr,

        .App => |app| {
            // The rewrite: (Var selector) (Var dict) → dictionary field.
            if (app.fn_expr.* == .Var and app.arg.* == .Var) {
                if (env.selectors.get(app.fn_expr.Var.name.unique.value)) |sel| {
                    if (env.dicts.get(app.arg.Var.name.unique.value)) |dict| {
                        if (sel.con_unique == dict.con_unique and
                            sel.method_index < dict.fields.len)
                        {
                            const field = dict.fields[sel.method_index];
                            // Only substitute variables: duplicating a
                            // larger expression per call site would trade
                            // a dispatch for code growth and lost sharing.
                            if (field.* == .Var) {
                                const e = try alloc.create(Expr);
                                e.* = .{ .Var = .{
                                    .name = field.Var.name,
                                    .ty = field.Var.ty,
                                    .span = app.span,
                                } };
                                return e;
                            }
                        }
                    }
                }
            }
            const new_fn = try rewrite(alloc, env, app.fn_expr);
            const new_arg = try rewrite(alloc, env, app.arg);
            if (new_fn == app.fn_expr and new_arg == app.arg) return expr;
            const e = try alloc.create(Expr);
            e.* = .{ .App = .{ .fn_expr = new_fn, .arg = new_arg, .span = app.span } };
            return e;
        },

        .Lam => |lam| {
            const new_body = try rewrite(alloc, env, lam.body);
            if (new_body == lam.body) return expr;
            const e = try alloc.create(Expr);
            e.* = .{ .Lam = .{ .binder = lam.binder, .body = new_body, .span = lam.span } };
            return e;
        },

        .Let => |let| {
            const new_bind: Bind = switch (let.bind) {
                .NonRec => |pair| .{ .NonRec = .{
                    .binder = pair.binder,
                    .rhs = try rewrite(alloc, env, pair.rhs),
                } },
                .Rec => |pairs| blk: {
                    const new_pairs = try alloc.alloc(BindPair, pairs.len);
                    for (pairs, new_pairs) |pair, *np| {
                        np.* = .{
                            .binder = pair.binder,
                            .rhs = try rewrite(alloc, env, pair.rhs),
                        };
                    }
                    break :blk .{ .Rec = new_pairs };
                },
            };
            const new_body = try rewrite(alloc, env, let.body);
            const e = try alloc.create(Expr);
            e.* = .{ .Let = .{ .bind = new_bind, .body = new_body, .span = let.span } };
            return e;
        },

        .Case => |case| {
            const new_scrut = try rewrite(alloc, env, case.scrutinee);
            const new_alts = try alloc.alloc(Alt, case.alts.len);
            var changed = new_scrut != case.scrutinee;
            for (case.alts, new_alts) |alt, *na| {
                const new_alt_body = try rewrite(alloc, env, alt.body);
                changed = changed or new_alt_body != alt.body;
                na.* = .{ .con = alt.con, .binders = alt.binders, .body = new_alt_body };
            }
            if (!changed) return expr;
            const e = try alloc.create(Expr);
            e.* = .{ .Case = .{
                .scrutinee = new_scrut,
                .binder = case.binder,
                .ty = case.ty,
                .alts = new_alts,
                .span = case.span,
            } };
            return e;
        },
    }
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;
const SourceSpan = core.SourceSpan;
const SourcePos = core.SourcePos;

fn testSpan() SourceSpan {
    return SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 2));
}

fn testId(base: []const u8, unique: u64) Id {
    return .{
        .name = .{ .base = base, .unique = .{ .value = unique } },
        .ty = .{ .TyCon = .{ .name = .{ .base = "Int", .unique = .{ .value = 0 } }, .args = &.{} } },
        .span = testSpan(),
    };
}

fn varExpr(alloc: std.mem.Allocator, id: Id) !*const Expr {
    const e = try alloc.create(Expr);
    e.* = .{ .Var = id };
    return e;
}

fn appExpr(alloc: std.mem.Allocator, f: *const Expr, a: *const Expr) !*const Expr {
    const e = try alloc.create(Expr);
    e.* = .{ .App = .{ .fn_expr = f, .arg = a, .span = testSpan() } };
    return e;
}

/// Build the canonical test fixture:
///   dict$Ord$Int (u=100) = MkDict$Ord (u=50) primLtInt (u=60)
///   <  (u=200)           = \d -> \x -> \y -> case d of MkDict$Ord f0 -> f0 x y
///   user (u=300)         = < dict$Ord$Int 1 2   (as nested Apps on vars)
fn buildFixture(alloc: std.mem.Allocator) !struct {
    prog: CoreProgram,
    call_site: *const Expr,
} {
    const mkdict = testId("MkDict$Ord", 50);
    const prim_lt = testId("primLtInt", 60);

    // dict$Ord$Int = MkDict$Ord primLtInt
    const dict_rhs = try appExpr(alloc, try varExpr(alloc, mkdict), try varExpr(alloc, prim_lt));

    // selector: \d -> \x -> \y -> case d of MkDict$Ord f0 -> f0 x y
    const d = testId("d", 1);
    const x = testId("x", 2);
    const y = testId("y", 3);
    const f0 = testId("f0", 4);
    const alt_body = try appExpr(
        alloc,
        try appExpr(alloc, try varExpr(alloc, f0), try varExpr(alloc, x)),
        try varExpr(alloc, y),
    );
    const alts = try alloc.alloc(Alt, 1);
    alts[0] = .{
        .con = .{ .DataAlt = .{ .base = "MkDict$Ord", .unique = .{ .value = 50 } } },
        .binders = try alloc.dupe(Id, &.{f0}),
        .body = alt_body,
    };
    const case_expr = try alloc.create(Expr);
    case_expr.* = .{ .Case = .{
        .scrutinee = try varExpr(alloc, d),
        .binder = d,
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = alts,
        .span = testSpan(),
    } };
    const lam_y = try alloc.create(Expr);
    lam_y.* = .{ .Lam = .{ .binder = y, .body = case_expr, .span = testSpan() } };
    const lam_x = try alloc.create(Expr);
    lam_x.* = .{ .Lam = .{ .binder = x, .body = lam_y, .span = testSpan() } };
    const sel_rhs = try alloc.create(Expr);
    sel_rhs.* = .{ .Lam = .{ .binder = d, .body = lam_x, .span = testSpan() } };

    // call site: ((< dict$Ord$Int) a) b
    const a = testId("a", 5);
    const b = testId("b", 6);
    const call = try appExpr(
        alloc,
        try appExpr(
            alloc,
            try appExpr(alloc, try varExpr(alloc, testId("<", 200)), try varExpr(alloc, testId("dict$Ord$Int", 100))),
            try varExpr(alloc, a),
        ),
        try varExpr(alloc, b),
    );

    const binds = try alloc.alloc(Bind, 3);
    binds[0] = .{ .NonRec = .{ .binder = testId("dict$Ord$Int", 100), .rhs = dict_rhs } };
    binds[1] = .{ .NonRec = .{ .binder = testId("<", 200), .rhs = sel_rhs } };
    binds[2] = .{ .NonRec = .{ .binder = testId("user", 300), .rhs = call } };

    return .{
        .prog = .{ .data_decls = &.{}, .binds = binds },
        .call_site = call,
    };
}

test "specialise: monomorphic dict call rewrites to instance method" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const fixture = try buildFixture(alloc);

    var env = SpecialiseEnv{};
    try collectEnv(alloc, &env, fixture.prog);
    defer env.deinit(alloc);

    try testing.expect(env.selectors.contains(200));
    try testing.expect(env.dicts.contains(100));
    try testing.expectEqual(@as(usize, 0), env.selectors.get(200).?.method_index);

    const out = try specialiseProgram(alloc, &env, fixture.prog);

    // user = ((primLtInt a) b) — the selector+dict collapsed to primLtInt.
    const user_rhs = out.binds[2].NonRec.rhs;
    const inner = user_rhs.App.fn_expr.App.fn_expr;
    try testing.expect(inner.* == .Var);
    try testing.expectEqualStrings("primLtInt", inner.Var.name.base);
    try testing.expectEqual(@as(u64, 60), inner.Var.name.unique.value);
}

test "specialise: polymorphic call site (lambda-bound dict) untouched" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const fixture = try buildFixture(alloc);

    var env = SpecialiseEnv{};
    try collectEnv(alloc, &env, fixture.prog);
    defer env.deinit(alloc);

    // poly = \d2 -> < d2 a b   — d2 is not a known dictionary.
    const d2 = testId("d2", 700);
    const call = try appExpr(
        alloc,
        try varExpr(alloc, testId("<", 200)),
        try varExpr(alloc, d2),
    );
    const lam = try alloc.create(Expr);
    lam.* = .{ .Lam = .{ .binder = d2, .body = call, .span = testSpan() } };

    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{ .binder = testId("poly", 800), .rhs = lam } };
    const poly_prog = CoreProgram{ .data_decls = &.{}, .binds = binds };

    const out = try specialiseProgram(alloc, &env, poly_prog);
    // Unchanged: the rewrite must not fire on a lambda-bound dictionary.
    try testing.expectEqual(lam, out.binds[0].NonRec.rhs);
}

test "specialise: mismatched class constructor does not rewrite" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const fixture = try buildFixture(alloc);

    var env = SpecialiseEnv{};
    try collectEnv(alloc, &env, fixture.prog);
    defer env.deinit(alloc);

    // A dict built from a *different* constructor (MkDict$Num, u=51).
    const other_con = testId("MkDict$Num", 51);
    const other_dict_rhs = try appExpr(alloc, try varExpr(alloc, other_con), try varExpr(alloc, testId("primAddInt", 61)));
    const binds = try alloc.alloc(Bind, 2);
    binds[0] = .{ .NonRec = .{ .binder = testId("dict$Num$Int", 101), .rhs = other_dict_rhs } };
    // bad = < dict$Num$Int   (selector of Ord applied to a Num dict)
    const bad_call = try appExpr(
        alloc,
        try varExpr(alloc, testId("<", 200)),
        try varExpr(alloc, testId("dict$Num$Int", 101)),
    );
    binds[1] = .{ .NonRec = .{ .binder = testId("bad", 900), .rhs = bad_call } };
    const prog = CoreProgram{ .data_decls = &.{}, .binds = binds };

    try collectEnv(alloc, &env, prog);
    const out = try specialiseProgram(alloc, &env, prog);
    try testing.expectEqual(bad_call, out.binds[1].NonRec.rhs);
}
