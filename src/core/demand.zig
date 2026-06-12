//! Demand (strictness) analysis — Core-level, whole-program (#802).
//!
//! Computes, for every top-level function, which parameters are *strict*:
//! `f` is strict in its i-th parameter when `f a1 .. ⊥ .. an = ⊥` — i.e.
//! evaluating the call to WHNF necessarily forces that argument. Callers
//! can then pass strict arguments eagerly instead of allocating thunks,
//! with no change to semantics (the argument would have been forced
//! anyway, and forcing it earlier cannot turn a terminating program into
//! a diverging one for an argument that is always demanded).
//!
//! Algorithm (Mycroft 1980, the classic abstract-interpretation
//! formulation restricted to flat demand — no higher-order or nested
//! product demands):
//!
//! 1. Every known function starts with the most-strict assumption (all
//!    parameters strict; abstractly `f# = ⊥`).
//! 2. Iterate: recompute each function's strict-parameter mask from its
//!    body under the current assumptions, until no mask changes. The
//!    iteration descends monotonically in the mask lattice and the
//!    fixpoint is the least fixed point of the abstract semantics —
//!    sound for recursive and mutually recursive groups.
//!
//! The core predicate is `demands(e, p)`: does evaluating `e` to WHNF
//! force the variable `p`?
//!
//!   demands(p)                      = true
//!   demands(⊥)                      = true                  (vacuous: ⊥ never reaches WHNF)
//!   demands(prim a1..an)           = ∃i. demands(ai)        (primops are strict)
//!   demands(f a1..an) | saturated  = ∃i. strict(f,i) ∧ demands(ai)
//!   demands(f a1..an) | partial    = false                  (P-node is WHNF)
//!   demands(case s of alts)        = demands(s) ∨ ∀alt. demands(alt)
//!   demands(let x = r in b)        = demands(b) ∨ (b demands x ∧ demands(r))
//!   demands(λ…), demands(lit)      = false
//!
//! Reference: Mycroft, "The theory and practice of transforming
//! call-by-need into call-by-value" (1980); GHC's GHC.Core.Opt.DmdAnal
//! (this pass is the 1-bit subset).

const std = @import("std");
const core = @import("ast.zig");
const known = @import("../naming/known.zig");
// PrimOp name vocabulary. The demand analysis needs to know which
// application heads are primitive operations (strict in all arguments);
// primops appear in Core with renamer-assigned uniques, so the canonical
// name list in grin/primop.zig is the only reliable identification.
const primop = @import("../grin/primop.zig");
const Expr = core.Expr;
const Bind = core.Bind;
const BindPair = core.BindPair;
const CoreProgram = core.CoreProgram;

/// Per-function demand result. Bit i of `strict` = parameter i is
/// strict (always forced when the call is evaluated to WHNF). Bit i of
/// `unbox` = strict AND the parameter's Core type is Int or Char — its
/// runtime representation is a tagged immediate, so a worker/wrapper
/// split (#803) can pass it as a raw machine word. `unbox` is always a
/// subset of `strict`. Functions with more than 64 parameters are not
/// analysed (no such function survives the desugarer in practice).
pub const FnDemand = struct {
    strict: u64 = 0,
    unbox: u64 = 0,
};

/// Demand masks keyed by function binder unique.
pub const StrictnessMap = std.AutoHashMapUnmanaged(u64, FnDemand);

const FnInfo = struct {
    params: []const u64,
    /// Bit i set = parameter i has an immediate-representation type
    /// (Int/Char) and is therefore a worker-unboxing candidate.
    imm_typed: u64,
    body: *const Expr,
};

/// Is this Core type represented as a tagged immediate at runtime?
fn isImmediateType(ty: core.CoreType) bool {
    return switch (ty) {
        .TyCon => |tc| std.mem.eql(u8, tc.name.base, "Int") or
            std.mem.eql(u8, tc.name.base, "Char"),
        else => false,
    };
}

/// Analyse all modules of a program. `programs` is the per-module Core
/// in any order; the analysis is whole-program because user modules call
/// Prelude functions. The returned map is owned by the caller (deinit
/// with the same allocator).
pub fn analyse(
    alloc: std.mem.Allocator,
    programs: []const CoreProgram,
) std.mem.Allocator.Error!StrictnessMap {
    // ── Collect functions: unique → (params, body) ──────────────────
    var fns = std.AutoHashMapUnmanaged(u64, FnInfo){};
    defer {
        var it = fns.valueIterator();
        while (it.next()) |info| alloc.free(info.params);
        fns.deinit(alloc);
    }
    // Alias bindings (`(+) = primAddInt`): alias unique → target unique.
    var aliases = std.AutoHashMapUnmanaged(u64, u64){};
    defer aliases.deinit(alloc);

    for (programs) |prog| {
        for (prog.binds) |bind| {
            switch (bind) {
                .NonRec => |pair| try collectFn(alloc, &fns, &aliases, pair),
                .Rec => |pairs| for (pairs) |pair| try collectFn(alloc, &fns, &aliases, pair),
            }
        }
    }

    // ── Fixpoint ────────────────────────────────────────────────────
    var masks = StrictnessMap{};
    errdefer masks.deinit(alloc);

    // Most-strict start: all parameters strict.
    var fn_it = fns.iterator();
    while (fn_it.next()) |entry| {
        const arity = entry.value_ptr.params.len;
        const mask: u64 = if (arity >= 64) ~@as(u64, 0) else (@as(u64, 1) << @intCast(arity)) - 1;
        try masks.put(alloc, entry.key_ptr.*, .{
            .strict = mask,
            .unbox = mask & entry.value_ptr.imm_typed,
        });
    }

    var changed = true;
    while (changed) {
        changed = false;
        var it = fns.iterator();
        while (it.next()) |entry| {
            const info = entry.value_ptr.*;
            var mask: u64 = 0;
            for (info.params, 0..) |param, i| {
                if (i >= 64) break;
                if (demands(info.body, param, &fns, &aliases, &masks)) {
                    mask |= @as(u64, 1) << @intCast(i);
                }
            }
            const slot = masks.getPtr(entry.key_ptr.*).?;
            if (slot.strict != mask) {
                slot.* = .{ .strict = mask, .unbox = mask & info.imm_typed };
                changed = true;
            }
        }
    }

    // Resolve aliases into the final map so callers can look up either
    // name: strict((+)) = strict(primAddInt).
    var alias_it = aliases.iterator();
    while (alias_it.next()) |entry| {
        var target = entry.value_ptr.*;
        // Follow alias chains (bounded — cycles cannot demand anything).
        var hops: u8 = 0;
        while (aliases.get(target)) |next| : (hops += 1) {
            if (hops > 8) break;
            target = next;
        }
        if (masks.get(target)) |dm| {
            try masks.put(alloc, entry.key_ptr.*, dm);
        } else if (target < known.reserved_range_end) {
            // Alias of a raw primop: strict in everything. No unbox
            // mask — primop calls inline anyway, no worker exists.
            try masks.put(alloc, entry.key_ptr.*, .{ .strict = ~@as(u64, 0) });
        }
    }

    return masks;
}

fn collectFn(
    alloc: std.mem.Allocator,
    fns: *std.AutoHashMapUnmanaged(u64, FnInfo),
    aliases: *std.AutoHashMapUnmanaged(u64, u64),
    pair: BindPair,
) std.mem.Allocator.Error!void {
    const unique = pair.binder.name.unique.value;
    // Simple alias: `f = g`.
    if (pair.rhs.* == .Var) {
        try aliases.put(alloc, unique, pair.rhs.Var.name.unique.value);
        return;
    }
    // Lambda chain: collect parameter uniques and their type shapes.
    var params = std.ArrayListUnmanaged(u64).empty;
    errdefer params.deinit(alloc);
    var imm_typed: u64 = 0;
    var cur = pair.rhs;
    var idx: usize = 0;
    while (cur.* == .Lam) : ({
        cur = cur.Lam.body;
        idx += 1;
    }) {
        try params.append(alloc, cur.Lam.binder.name.unique.value);
        if (idx < 64 and isImmediateType(cur.Lam.binder.ty)) {
            imm_typed |= @as(u64, 1) << @intCast(idx);
        }
    }
    if (params.items.len == 0) {
        params.deinit(alloc);
        return; // CAF — nothing to analyse.
    }
    try collectVarAliases(alloc, cur, aliases);
    try fns.put(alloc, unique, .{
        .params = try params.toOwnedSlice(alloc),
        .imm_typed = imm_typed,
        .body = cur,
    });
}

/// Record `let x = y` variable aliases from a function body. The pattern
/// compiler re-binds parameters under fresh names in every alternative
/// (`let acc' = arg_0 in ...`); without resolving these, demand on the
/// original parameter is invisible. Uniques are globally unique after
/// renaming, so one flat map is safe (no shadowing).
fn collectVarAliases(
    alloc: std.mem.Allocator,
    e: *const Expr,
    aliases: *std.AutoHashMapUnmanaged(u64, u64),
) std.mem.Allocator.Error!void {
    switch (e.*) {
        .Var, .Lit, .Type, .Coercion => {},
        .Lam => |l| try collectVarAliases(alloc, l.body, aliases),
        .App => |a| {
            try collectVarAliases(alloc, a.fn_expr, aliases);
            try collectVarAliases(alloc, a.arg, aliases);
        },
        .Case => |case_expr| {
            try collectVarAliases(alloc, case_expr.scrutinee, aliases);
            for (case_expr.alts) |alt| try collectVarAliases(alloc, alt.body, aliases);
        },
        .Let => |l| {
            switch (l.bind) {
                .NonRec => |pair| {
                    if (pair.rhs.* == .Var) {
                        try aliases.put(alloc, pair.binder.name.unique.value, pair.rhs.Var.name.unique.value);
                    }
                    try collectVarAliases(alloc, pair.rhs, aliases);
                },
                .Rec => |pairs| for (pairs) |pair| try collectVarAliases(alloc, pair.rhs, aliases),
            }
            try collectVarAliases(alloc, l.body, aliases);
        },
    }
}

/// Follow the alias chain to the representative unique.
fn resolveAlias(aliases: *const std.AutoHashMapUnmanaged(u64, u64), unique: u64) u64 {
    var cur = unique;
    var hops: u8 = 0;
    while (aliases.get(cur)) |next| : (hops += 1) {
        if (hops > 8) break;
        cur = next;
    }
    return cur;
}

/// Is `e` certainly bottom — guaranteed to diverge (or abort) when
/// evaluated to WHNF? Recognises applications of `error` / `primError`
/// and any reference to `undefined`. The desugarer emits
/// `error "Non-exhaustive patterns …"` as the fallback alternative of
/// every compiled pattern match, so dead default branches land here.
///
/// A bottoming expression vacuously demands every variable: if one
/// branch of a case is ⊥, that branch can never weaken the strictness
/// meet over the alternatives (`f x = ⊥` is strict in `x` by the
/// definition `f ⊥ = ⊥`). GHC's DmdAnal does the same by giving such
/// branches the bottom demand type.
fn isBottom(e: *const Expr) bool {
    var n_args: usize = 0;
    var cur = e;
    while (cur.* == .App) : (n_args += 1) cur = cur.App.fn_expr;
    if (cur.* != .Var) return false;
    const base = cur.Var.name.base;
    if (std.mem.eql(u8, base, "undefined")) return true;
    return n_args >= 1 and
        (std.mem.eql(u8, base, "error") or std.mem.eql(u8, base, "primError"));
}

/// Does evaluating `e` to WHNF force the variable `p`?
fn demands(
    e: *const Expr,
    p: u64,
    fns: *const std.AutoHashMapUnmanaged(u64, FnInfo),
    aliases: *const std.AutoHashMapUnmanaged(u64, u64),
    masks: *const StrictnessMap,
) bool {
    if (isBottom(e)) return true;
    switch (e.*) {
        .Var => |id| return resolveAlias(aliases, id.name.unique.value) == p,
        .Lit, .Lam, .Type, .Coercion => return false,

        .App => {
            // Walk the application spine.
            var n_args: usize = 0;
            var cur = e;
            while (cur.* == .App) : (n_args += 1) cur = cur.App.fn_expr;
            if (cur.* != .Var) return false;
            var head = cur.Var.name.unique.value;
            // Evaluating the application evaluates the head.
            if (head == p) return true;

            // Resolve aliases to the defining function.
            var hops: u8 = 0;
            while (aliases.get(head)) |next| : (hops += 1) {
                if (hops > 8) break;
                head = next;
            }

            const strict_mask: u64 = blk: {
                if (head < known.reserved_range_end or
                    primop.PrimOp.fromString(cur.Var.name.base) != null)
                {
                    // Compiler primop: strict in all arguments.
                    break :blk ~@as(u64, 0);
                }
                const info = fns.get(head) orelse return false;
                // Unsaturated application builds a closure — WHNF, forces
                // nothing. Oversaturated: the first `arity` args reach the
                // function; be conservative and require exact saturation.
                if (n_args != info.params.len) return false;
                break :blk if (masks.get(head)) |dm| dm.strict else 0;
            };

            // ∃i. strict(f, i) ∧ demands(a_i, p)
            var i = n_args;
            cur = e;
            while (cur.* == .App) : (cur = cur.App.fn_expr) {
                i -= 1;
                if (i < 64 and (strict_mask >> @intCast(i)) & 1 == 1) {
                    if (demands(cur.App.arg, p, fns, aliases, masks)) return true;
                }
            }
            return false;
        },

        .Case => |case_expr| {
            if (demands(case_expr.scrutinee, p, fns, aliases, masks)) return true;
            if (case_expr.alts.len == 0) return false;
            for (case_expr.alts) |alt| {
                if (!demands(alt.body, p, fns, aliases, masks)) return false;
            }
            return true;
        },

        .Let => |let| {
            if (demands(let.body, p, fns, aliases, masks)) return true;
            // If the body demands the bound variable, the RHS is forced.
            switch (let.bind) {
                .NonRec => |pair| {
                    const x = pair.binder.name.unique.value;
                    return demands(let.body, x, fns, aliases, masks) and
                        demands(pair.rhs, p, fns, aliases, masks);
                },
                .Rec => return false, // conservative
            }
        },
    }
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = std.testing;
const SourceSpan = core.SourceSpan;
const SourcePos = core.SourcePos;
const Id = core.Id;

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

fn v(alloc: std.mem.Allocator, id: Id) !*const Expr {
    const e = try alloc.create(Expr);
    e.* = .{ .Var = id };
    return e;
}

fn app(alloc: std.mem.Allocator, f: *const Expr, a: *const Expr) !*const Expr {
    const e = try alloc.create(Expr);
    e.* = .{ .App = .{ .fn_expr = f, .arg = a, .span = testSpan() } };
    return e;
}

fn lam(alloc: std.mem.Allocator, binder: Id, body: *const Expr) !*const Expr {
    const e = try alloc.create(Expr);
    e.* = .{ .Lam = .{ .binder = binder, .body = body, .span = testSpan() } };
    return e;
}

fn lit(alloc: std.mem.Allocator, n: i64) !*const Expr {
    const e = try alloc.create(Expr);
    e.* = .{ .Lit = .{ .val = .{ .Int = n }, .span = testSpan() } };
    return e;
}

test "demand: fib-shaped recursion is strict in its parameter" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // lt (unique 10, builtin range), fib (unique 2000), n (unique 1).
    // fib = \n -> case lt n 2 of { _ -> fib n }
    const n = testId("n", 1);
    const lt = testId("lt_Int", 10);
    const fib = testId("fib", 2000);

    const scrut = try app(alloc, try app(alloc, try v(alloc, lt), try v(alloc, n)), try lit(alloc, 2));
    const alt_body = try app(alloc, try v(alloc, fib), try v(alloc, n));
    const alts = try alloc.alloc(core.Alt, 1);
    alts[0] = .{ .con = .{ .Default = {} }, .binders = &.{}, .body = alt_body };
    const case_e = try alloc.create(Expr);
    case_e.* = .{ .Case = .{
        .scrutinee = scrut,
        .binder = testId("s", 3),
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = alts,
        .span = testSpan(),
    } };

    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{ .binder = fib, .rhs = try lam(alloc, n, case_e) } };
    const progs = [_]CoreProgram{.{ .data_decls = &.{}, .binds = binds }};

    var masks = try analyse(testing.allocator, &progs);
    defer masks.deinit(testing.allocator);

    try testing.expectEqual(@as(u64, 1), masks.get(2000).?.strict);
}

test "demand: accumulator threaded through recursive strict call is strict" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // sumTo = \acc -> \n -> case n of { 0 -> acc; _ -> sumTo (add acc n) (sub n 1) }
    const acc = testId("acc", 1);
    const n = testId("n", 2);
    const add = testId("add_Int", 10);
    const sub = testId("sub_Int", 11);
    const sum_to = testId("sumTo", 2000);

    const rec_call = try app(
        alloc,
        try app(
            alloc,
            try v(alloc, sum_to),
            try app(alloc, try app(alloc, try v(alloc, add), try v(alloc, acc)), try v(alloc, n)),
        ),
        try app(alloc, try app(alloc, try v(alloc, sub), try v(alloc, n)), try lit(alloc, 1)),
    );
    const alts = try alloc.alloc(core.Alt, 2);
    alts[0] = .{ .con = .{ .LitAlt = .{ .Int = 0 } }, .binders = &.{}, .body = try v(alloc, acc) };
    alts[1] = .{ .con = .{ .Default = {} }, .binders = &.{}, .body = rec_call };
    const case_e = try alloc.create(Expr);
    case_e.* = .{ .Case = .{
        .scrutinee = try v(alloc, n),
        .binder = testId("s", 3),
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = alts,
        .span = testSpan(),
    } };

    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{
        .binder = sum_to,
        .rhs = try lam(alloc, acc, try lam(alloc, n, case_e)),
    } };
    const progs = [_]CoreProgram{.{ .data_decls = &.{}, .binds = binds }};

    var masks = try analyse(testing.allocator, &progs);
    defer masks.deinit(testing.allocator);

    // Both acc (bit 0) and n (bit 1) strict.
    try testing.expectEqual(@as(u64, 0b11), masks.get(2000).?.strict);
}

test "demand: dead non-exhaustive error branch does not poison strictness" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // The desugarer compiles `if a < b then q else helper (sub a b) b (add q 1)`
    // into nested cases whose innermost default is `error "Non-exhaustive…"`.
    // helper = \a -> \b -> \q ->
    //   case lt a b of
    //     True  -> q
    //     _     -> case lt a b of
    //       False -> helper (sub a b) b (add q 1)
    //       _     -> error "Non-exhaustive patterns in case"
    const a = testId("a", 1);
    const b = testId("b", 2);
    const q = testId("q", 3);
    const lt = testId("lt_Int", 10);
    const add = testId("add_Int", 11);
    const sub = testId("sub_Int", 12);
    const err = testId("error", 5);
    const helper = testId("helper", 2000);

    const scrut = try app(alloc, try app(alloc, try v(alloc, lt), try v(alloc, a)), try v(alloc, b));
    const rec_call = try app(
        alloc,
        try app(
            alloc,
            try app(
                alloc,
                try v(alloc, helper),
                try app(alloc, try app(alloc, try v(alloc, sub), try v(alloc, a)), try v(alloc, b)),
            ),
            try v(alloc, b),
        ),
        try app(alloc, try app(alloc, try v(alloc, add), try v(alloc, q)), try lit(alloc, 1)),
    );
    const err_str = try alloc.create(Expr);
    err_str.* = .{ .Lit = .{ .val = .{ .String = "Non-exhaustive patterns in case" }, .span = testSpan() } };
    const err_call = try app(alloc, try v(alloc, err), err_str);

    const inner_alts = try alloc.alloc(core.Alt, 2);
    inner_alts[0] = .{ .con = .{ .DataAlt = .{ .base = "False", .unique = .{ .value = 20 } } }, .binders = &.{}, .body = rec_call };
    inner_alts[1] = .{ .con = .{ .Default = {} }, .binders = &.{}, .body = err_call };
    const inner_case = try alloc.create(Expr);
    inner_case.* = .{ .Case = .{
        .scrutinee = scrut,
        .binder = testId("s2", 31),
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = inner_alts,
        .span = testSpan(),
    } };

    const outer_alts = try alloc.alloc(core.Alt, 2);
    outer_alts[0] = .{ .con = .{ .DataAlt = .{ .base = "True", .unique = .{ .value = 21 } } }, .binders = &.{}, .body = try v(alloc, q) };
    outer_alts[1] = .{ .con = .{ .Default = {} }, .binders = &.{}, .body = inner_case };
    const outer_case = try alloc.create(Expr);
    outer_case.* = .{ .Case = .{
        .scrutinee = scrut,
        .binder = testId("s1", 30),
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = outer_alts,
        .span = testSpan(),
    } };

    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{
        .binder = helper,
        .rhs = try lam(alloc, a, try lam(alloc, b, try lam(alloc, q, outer_case))),
    } };
    const progs = [_]CoreProgram{.{ .data_decls = &.{}, .binds = binds }};

    var masks = try analyse(testing.allocator, &progs);
    defer masks.deinit(testing.allocator);

    // All three parameters strict — the dead error branch must not
    // demote the accumulator `q` to lazy.
    try testing.expectEqual(@as(u64, 0b111), masks.get(2000).?.strict);
}

test "demand: argument only used under a lambda is not strict" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // constFn = \x -> \y -> x   — strict in x (returned), lazy in y.
    const x = testId("x", 1);
    const y = testId("y", 2);
    const const_fn = testId("constFn", 2000);

    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{
        .binder = const_fn,
        .rhs = try lam(alloc, x, try lam(alloc, y, try v(alloc, x))),
    } };
    const progs = [_]CoreProgram{.{ .data_decls = &.{}, .binds = binds }};

    var masks = try analyse(testing.allocator, &progs);
    defer masks.deinit(testing.allocator);

    try testing.expectEqual(@as(u64, 0b01), masks.get(2000).?.strict);
}

test "demand: alias bindings inherit the target's strictness" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // primAdd = \a -> \b -> add_Int a b ;  (+) = primAdd
    const a = testId("a", 1);
    const b = testId("b", 2);
    const add = testId("add_Int", 10);
    const prim_add = testId("primAdd", 2000);
    const plus = testId("+", 2001);

    const body = try app(alloc, try app(alloc, try v(alloc, add), try v(alloc, a)), try v(alloc, b));
    const binds = try alloc.alloc(Bind, 2);
    binds[0] = .{ .NonRec = .{ .binder = prim_add, .rhs = try lam(alloc, a, try lam(alloc, b, body)) } };
    binds[1] = .{ .NonRec = .{ .binder = plus, .rhs = try v(alloc, prim_add) } };
    const progs = [_]CoreProgram{.{ .data_decls = &.{}, .binds = binds }};

    var masks = try analyse(testing.allocator, &progs);
    defer masks.deinit(testing.allocator);

    try testing.expectEqual(@as(u64, 0b11), masks.get(2000).?.strict);
    try testing.expectEqual(@as(u64, 0b11), masks.get(2001).?.strict);
}
