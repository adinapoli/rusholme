//! Core-to-Core simplification (post-desugar cleanup).
//!
//! The sequential pattern-match compiler (Augustsson 1985-style, in
//! `desugar.zig`) compiles a multi-equation match into a *chain* of
//! single-alternative cases linked through their default branches:
//!
//! ```
//! case s of (b) { C1 …  -> e1
//!               ; _     -> case s of (b) { C2 … -> e2
//!                                        ; _    -> error "Non-exhaustive…" } }
//! ```
//!
//! Both links scrutinise the same expression and bind the *same* case
//! binder (the desugarer reuses one synthetic `_case_scrut` Id for the
//! whole chain), so the inner case re-evaluates a value that is already
//! in hand. Downstream this costs a second `eval` in GRIN and a second
//! `__rhc_force` call in the emitted code, and it hides the real shape
//! of the dispatch from the LLVM switch lowering.
//!
//! `simplifyProgram` merges such chains into a single multi-alternative
//! case:
//!
//! ```
//! case s of (b) { C1 … -> e1 ; C2 … -> e2 ; _ -> error "Non-exhaustive…" }
//! ```
//!
//! Soundness: the merge fires only when the inner case binds the same
//! binder unique as the outer one. Uniques are globally unique after
//! renaming, so a re-bound unique can only be the desugarer's own chain
//! artifact, which guarantees the scrutinee expressions are identical.
//! Sequential match semantics are preserved by keeping the outer
//! alternatives first and dropping inner alternatives whose constructor
//! is already covered (earlier equations shadow later ones).
//!
//! Reference: Maranget, "Compiling pattern matching to good decision
//! trees" (ML 2008) — the merged form is the first step from
//! backtracking automata towards decision trees.

const std = @import("std");
const core = @import("ast.zig");
const Expr = core.Expr;
const Alt = core.Alt;
const AltCon = core.AltCon;
const Bind = core.Bind;
const BindPair = core.BindPair;
const CoreProgram = core.CoreProgram;

/// Simplify every binding of a module's Core program in place
/// (rebinding RHS pointers; the AST nodes themselves are immutable and
/// arena-allocated, so no frees happen here).
pub fn simplifyProgram(
    alloc: std.mem.Allocator,
    program: CoreProgram,
) std.mem.Allocator.Error!CoreProgram {
    var rw = Rewriter{ .alloc = alloc };
    defer rw.cache.deinit(alloc);

    const new_binds = try alloc.alloc(Bind, program.binds.len);
    for (program.binds, 0..) |bind, i| {
        new_binds[i] = switch (bind) {
            .NonRec => |pair| .{ .NonRec = try rw.rewritePair(pair) },
            .Rec => |pairs| blk: {
                const new_pairs = try alloc.alloc(BindPair, pairs.len);
                for (pairs, 0..) |pair, j| new_pairs[j] = try rw.rewritePair(pair);
                break :blk .{ .Rec = new_pairs };
            },
        };
    }
    return .{ .data_decls = program.data_decls, .binds = new_binds };
}

const Rewriter = struct {
    alloc: std.mem.Allocator,
    /// Memoization keyed by source node pointer. The pattern compiler
    /// produces shared fallback subtrees (a DAG); rewriting each shared
    /// node once keeps the output a DAG of the same size instead of
    /// exploding it into a tree.
    cache: std.AutoHashMapUnmanaged(usize, *const Expr) = .{},

    fn rewritePair(self: *Rewriter, pair: BindPair) std.mem.Allocator.Error!BindPair {
        return .{ .binder = pair.binder, .rhs = try self.rewrite(pair.rhs) };
    }

    fn rewrite(self: *Rewriter, e: *const Expr) std.mem.Allocator.Error!*const Expr {
        if (self.cache.get(@intFromPtr(e))) |hit| return hit;
        const result: *const Expr = switch (e.*) {
            .Var, .Lit, .Type, .Coercion => e,

            .Lam => |l| blk: {
                const body = try self.rewrite(l.body);
                if (body == l.body) break :blk e;
                const n = try self.alloc.create(Expr);
                n.* = .{ .Lam = .{ .binder = l.binder, .body = body, .span = l.span } };
                break :blk n;
            },

            .App => |a| blk: {
                const fn_expr = try self.rewrite(a.fn_expr);
                const arg = try self.rewrite(a.arg);
                if (fn_expr == a.fn_expr and arg == a.arg) break :blk e;
                const n = try self.alloc.create(Expr);
                n.* = .{ .App = .{ .fn_expr = fn_expr, .arg = arg, .span = a.span } };
                break :blk n;
            },

            .Let => |l| blk: {
                const body = try self.rewrite(l.body);
                const bind: Bind = switch (l.bind) {
                    .NonRec => |pair| .{ .NonRec = try self.rewritePair(pair) },
                    .Rec => |pairs| rec: {
                        const new_pairs = try self.alloc.alloc(BindPair, pairs.len);
                        for (pairs, 0..) |pair, j| new_pairs[j] = try self.rewritePair(pair);
                        break :rec .{ .Rec = new_pairs };
                    },
                };
                const n = try self.alloc.create(Expr);
                n.* = .{ .Let = .{ .bind = bind, .body = body, .span = l.span } };
                break :blk n;
            },

            .Case => try self.rewriteCase(e),
        };
        try self.cache.put(self.alloc, @intFromPtr(e), result);
        return result;
    }

    fn rewriteCase(
        self: *Rewriter,
        original: *const Expr,
    ) std.mem.Allocator.Error!*const Expr {
        const c = original.Case;
        const scrut = try self.rewrite(c.scrutinee);

        var alts = std.ArrayListUnmanaged(Alt).empty;
        defer alts.deinit(self.alloc);
        var changed = scrut != c.scrutinee;

        for (c.alts) |alt| {
            const body = try self.rewrite(alt.body);
            changed = changed or body != alt.body;
            try alts.append(self.alloc, .{ .con = alt.con, .binders = alt.binders, .body = body });
        }

        // ── Chain merge ──────────────────────────────────────────────
        // While the trailing default alternative is itself a case that
        // re-binds the same case binder, splice its alternatives in.
        while (alts.items.len > 0) {
            const last = alts.items[alts.items.len - 1];
            if (last.con != .Default) break;
            if (last.body.* != .Case) break;
            const inner = last.body.Case;
            if (inner.binder.name.unique.value != c.binder.name.unique.value) break;

            _ = alts.pop();
            for (inner.alts) |inner_alt| {
                if (coveredBy(alts.items, inner_alt.con)) continue;
                try alts.append(self.alloc, inner_alt);
            }
            changed = true;
        }

        if (!changed) return original;
        const n = try self.alloc.create(Expr);
        n.* = .{ .Case = .{
            .scrutinee = scrut,
            .binder = c.binder,
            .ty = c.ty,
            .alts = try self.alloc.dupe(Alt, alts.items),
            .span = c.span,
        } };
        return n;
    }
};

/// Is `con` already matched by one of `alts`? Sequential semantics:
/// an earlier alternative for the same constructor/literal (or an
/// earlier default) shadows everything after it.
fn coveredBy(alts: []const Alt, con: AltCon) bool {
    for (alts) |alt| {
        switch (alt.con) {
            .Default => return true,
            .DataAlt => |name| if (con == .DataAlt and
                name.unique.value == con.DataAlt.unique.value) return true,
            .LitAlt => |lit| if (con == .LitAlt and litEql(lit, con.LitAlt)) return true,
        }
    }
    return false;
}

fn litEql(a: core.Literal, b: core.Literal) bool {
    return switch (a) {
        .Int => |x| b == .Int and b.Int == x,
        .Float => |x| b == .Float and b.Float == x,
        .Char => |x| b == .Char and b.Char == x,
        .String => |s| b == .String and std.mem.eql(u8, b.String, s),
    };
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
        .ty = .{ .TyVar = .{ .base = "_t", .unique = .{ .value = 0 } } },
        .span = testSpan(),
    };
}

fn mkVar(alloc: std.mem.Allocator, id: Id) !*const Expr {
    const e = try alloc.create(Expr);
    e.* = .{ .Var = id };
    return e;
}

test "simplify: desugared if-chain merges into one case" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // case s of (b) { True -> t ; _ -> case s of (b) { False -> f ; _ -> err } }
    const scrut = try mkVar(alloc, testId("s", 1));
    const binder = testId("_case_scrut", 42);

    const inner_alts = try alloc.alloc(Alt, 2);
    inner_alts[0] = .{
        .con = .{ .DataAlt = .{ .base = "False", .unique = .{ .value = 11 } } },
        .binders = &.{},
        .body = try mkVar(alloc, testId("f", 2)),
    };
    inner_alts[1] = .{
        .con = .{ .Default = {} },
        .binders = &.{},
        .body = try mkVar(alloc, testId("err", 3)),
    };
    const inner = try alloc.create(Expr);
    inner.* = .{ .Case = .{
        .scrutinee = scrut,
        .binder = binder,
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = inner_alts,
        .span = testSpan(),
    } };

    const outer_alts = try alloc.alloc(Alt, 2);
    outer_alts[0] = .{
        .con = .{ .DataAlt = .{ .base = "True", .unique = .{ .value = 10 } } },
        .binders = &.{},
        .body = try mkVar(alloc, testId("t", 4)),
    };
    outer_alts[1] = .{ .con = .{ .Default = {} }, .binders = &.{}, .body = inner };
    const outer = try alloc.create(Expr);
    outer.* = .{ .Case = .{
        .scrutinee = scrut,
        .binder = binder,
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = outer_alts,
        .span = testSpan(),
    } };

    const f_binder = testId("g", 100);
    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{ .binder = f_binder, .rhs = outer } };

    const out = try simplifyProgram(alloc, .{ .data_decls = &.{}, .binds = binds });
    const rhs = out.binds[0].NonRec.rhs;

    try testing.expect(rhs.* == .Case);
    const merged = rhs.Case;
    try testing.expectEqual(@as(usize, 3), merged.alts.len);
    try testing.expectEqualStrings("True", merged.alts[0].con.DataAlt.base);
    try testing.expectEqualStrings("False", merged.alts[1].con.DataAlt.base);
    try testing.expect(merged.alts[2].con == .Default);
}

test "simplify: cases binding different uniques do not merge" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // case s of (b1) { C -> t ; _ -> case s2 of (b2) { D -> f } }
    const inner_alts = try alloc.alloc(Alt, 1);
    inner_alts[0] = .{
        .con = .{ .DataAlt = .{ .base = "D", .unique = .{ .value = 11 } } },
        .binders = &.{},
        .body = try mkVar(alloc, testId("f", 2)),
    };
    const inner = try alloc.create(Expr);
    inner.* = .{ .Case = .{
        .scrutinee = try mkVar(alloc, testId("s2", 5)),
        .binder = testId("b2", 43),
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = inner_alts,
        .span = testSpan(),
    } };

    const outer_alts = try alloc.alloc(Alt, 2);
    outer_alts[0] = .{
        .con = .{ .DataAlt = .{ .base = "C", .unique = .{ .value = 10 } } },
        .binders = &.{},
        .body = try mkVar(alloc, testId("t", 4)),
    };
    outer_alts[1] = .{ .con = .{ .Default = {} }, .binders = &.{}, .body = inner };
    const outer = try alloc.create(Expr);
    outer.* = .{ .Case = .{
        .scrutinee = try mkVar(alloc, testId("s", 1)),
        .binder = testId("b1", 42),
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = outer_alts,
        .span = testSpan(),
    } };

    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{ .binder = testId("g", 100), .rhs = outer } };

    const out = try simplifyProgram(alloc, .{ .data_decls = &.{}, .binds = binds });
    const rhs = out.binds[0].NonRec.rhs;
    try testing.expectEqual(@as(usize, 2), rhs.Case.alts.len);
}

test "simplify: shadowed inner alternative is dropped" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // case s of (b) { C -> t1 ; _ -> case s of (b) { C -> t2 ; D -> f } }
    // Inner C is dead (sequential match); only D is spliced.
    const scrut = try mkVar(alloc, testId("s", 1));
    const binder = testId("b", 42);

    const inner_alts = try alloc.alloc(Alt, 2);
    inner_alts[0] = .{
        .con = .{ .DataAlt = .{ .base = "C", .unique = .{ .value = 10 } } },
        .binders = &.{},
        .body = try mkVar(alloc, testId("t2", 2)),
    };
    inner_alts[1] = .{
        .con = .{ .DataAlt = .{ .base = "D", .unique = .{ .value = 11 } } },
        .binders = &.{},
        .body = try mkVar(alloc, testId("f", 3)),
    };
    const inner = try alloc.create(Expr);
    inner.* = .{ .Case = .{
        .scrutinee = scrut,
        .binder = binder,
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = inner_alts,
        .span = testSpan(),
    } };

    const outer_alts = try alloc.alloc(Alt, 2);
    outer_alts[0] = .{
        .con = .{ .DataAlt = .{ .base = "C", .unique = .{ .value = 10 } } },
        .binders = &.{},
        .body = try mkVar(alloc, testId("t1", 4)),
    };
    outer_alts[1] = .{ .con = .{ .Default = {} }, .binders = &.{}, .body = inner };
    const outer = try alloc.create(Expr);
    outer.* = .{ .Case = .{
        .scrutinee = scrut,
        .binder = binder,
        .ty = .{ .TyVar = .{ .base = "t", .unique = .{ .value = 0 } } },
        .alts = outer_alts,
        .span = testSpan(),
    } };

    const binds = try alloc.alloc(Bind, 1);
    binds[0] = .{ .NonRec = .{ .binder = testId("g", 100), .rhs = outer } };

    const out = try simplifyProgram(alloc, .{ .data_decls = &.{}, .binds = binds });
    const merged = out.binds[0].NonRec.rhs.Case;
    try testing.expectEqual(@as(usize, 2), merged.alts.len);
    try testing.expectEqualStrings("C", merged.alts[0].con.DataAlt.base);
    try testing.expectEqualStrings("t1", merged.alts[0].body.Var.name.base);
    try testing.expectEqualStrings("D", merged.alts[1].con.DataAlt.base);
}
