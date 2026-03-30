//! Declaration dependency analysis for SCC-based type inference.
//!
//! Haskell 2010 §4.5.1 requires all top-level declarations in a module
//! to be mutually recursive — declaration order must not affect type
//! inference. This module computes strongly connected components (SCCs)
//! of the declaration dependency graph, returning groups in topological
//! order so the typechecker can generalise each group before processing
//! dependents.
//!
//! ## Algorithm references
//!
//! - Tarjan, R.E. (1972). "Depth-first search and linear graph algorithms."
//!   *SIAM Journal on Computing*, 1(2), 146–160.

const std = @import("std");
const renamer_mod = @import("../renamer/renamer.zig");
const naming_mod = @import("../naming/unique.zig");
const Name = @import("../core/ast.zig").Name;
const SourceSpan = @import("../core/ast.zig").SourceSpan;

const RExpr = renamer_mod.RExpr;
const RDecl = renamer_mod.RDecl;
const RRhs = renamer_mod.RRhs;
const RMatch = renamer_mod.RMatch;
const RStmt = renamer_mod.RStmt;
const RAlt = renamer_mod.RAlt;
const RGuardedRhs = renamer_mod.RGuardedRhs;
const RGuard = renamer_mod.RGuard;

/// Set of unique variable IDs (used for top-level binder lookup).
const UniqueSet = std.AutoHashMapUnmanaged(u64, void);

// ── Variable reference collection ───────────────────────────────────────

/// Collect all variable references in an expression whose unique IDs
/// appear in `top_level`. Appends matching unique IDs to `refs`.
fn collectExprVarRefs(
    expr: RExpr,
    top_level: *const UniqueSet,
    refs: *std.ArrayListUnmanaged(u64),
    alloc: std.mem.Allocator,
) std.mem.Allocator.Error!void {
    switch (expr) {
        .Var => |v| {
            if (top_level.contains(v.name.unique.value)) {
                try refs.append(alloc, v.name.unique.value);
            }
        },
        .Lit => {},
        .App => |a| {
            try collectExprVarRefs(a.fn_expr.*, top_level, refs, alloc);
            try collectExprVarRefs(a.arg_expr.*, top_level, refs, alloc);
        },
        .InfixApp => |ia| {
            try collectExprVarRefs(ia.left.*, top_level, refs, alloc);
            if (top_level.contains(ia.op.unique.value)) {
                try refs.append(alloc, ia.op.unique.value);
            }
            try collectExprVarRefs(ia.right.*, top_level, refs, alloc);
        },
        .LeftSection => |ls| {
            try collectExprVarRefs(ls.expr.*, top_level, refs, alloc);
            if (top_level.contains(ls.op.unique.value)) {
                try refs.append(alloc, ls.op.unique.value);
            }
        },
        .RightSection => |rs| {
            if (top_level.contains(rs.op.unique.value)) {
                try refs.append(alloc, rs.op.unique.value);
            }
            try collectExprVarRefs(rs.expr.*, top_level, refs, alloc);
        },
        .Lambda => |lam| {
            try collectExprVarRefs(lam.body.*, top_level, refs, alloc);
        },
        .Let => |lt| {
            for (lt.binds) |bind| {
                try collectDeclVarRefs(bind, top_level, refs, alloc);
            }
            try collectExprVarRefs(lt.body.*, top_level, refs, alloc);
        },
        .Case => |c| {
            try collectExprVarRefs(c.scrutinee.*, top_level, refs, alloc);
            for (c.alts) |alt| {
                try collectRhsVarRefs(alt.rhs, top_level, refs, alloc);
            }
        },
        .If => |i| {
            try collectExprVarRefs(i.condition.*, top_level, refs, alloc);
            try collectExprVarRefs(i.then_expr.*, top_level, refs, alloc);
            try collectExprVarRefs(i.else_expr.*, top_level, refs, alloc);
        },
        .Do => |stmts| {
            for (stmts) |stmt| {
                switch (stmt) {
                    .Generator => |g| try collectExprVarRefs(g.expr, top_level, refs, alloc),
                    .Qualifier => |e| try collectExprVarRefs(e, top_level, refs, alloc),
                    .Stmt => |e| try collectExprVarRefs(e, top_level, refs, alloc),
                    .LetStmt => |binds| {
                        for (binds) |bind| {
                            try collectDeclVarRefs(bind, top_level, refs, alloc);
                        }
                    },
                }
            }
        },
        .Tuple => |elems| {
            for (elems) |e| try collectExprVarRefs(e, top_level, refs, alloc);
        },
        .List => |elems| {
            for (elems) |e| try collectExprVarRefs(e, top_level, refs, alloc);
        },
        .EnumFrom => |ef| try collectExprVarRefs(ef.from.*, top_level, refs, alloc),
        .EnumFromThen => |eft| {
            try collectExprVarRefs(eft.from.*, top_level, refs, alloc);
            try collectExprVarRefs(eft.then.*, top_level, refs, alloc);
        },
        .EnumFromTo => |eft| {
            try collectExprVarRefs(eft.from.*, top_level, refs, alloc);
            try collectExprVarRefs(eft.to.*, top_level, refs, alloc);
        },
        .EnumFromThenTo => |eftt| {
            try collectExprVarRefs(eftt.from.*, top_level, refs, alloc);
            try collectExprVarRefs(eftt.then.*, top_level, refs, alloc);
            try collectExprVarRefs(eftt.to.*, top_level, refs, alloc);
        },
        .TypeAnn => |ta| try collectExprVarRefs(ta.expr.*, top_level, refs, alloc),
        .TypeApp => |ta| try collectExprVarRefs(ta.fn_expr.*, top_level, refs, alloc),
        .Negate => |e| try collectExprVarRefs(e.*, top_level, refs, alloc),
        .Paren => |e| try collectExprVarRefs(e.*, top_level, refs, alloc),
        .RecordCon => |rc| {
            for (rc.fields) |f| try collectExprVarRefs(f.expr, top_level, refs, alloc);
        },
        .RecordUpdate => |ru| {
            try collectExprVarRefs(ru.expr.*, top_level, refs, alloc);
            for (ru.fields) |f| try collectExprVarRefs(f.expr, top_level, refs, alloc);
        },
        .Field => |f| try collectExprVarRefs(f.expr.*, top_level, refs, alloc),
    }
}

/// Collect variable references from an RHS (unguarded or guarded).
fn collectRhsVarRefs(
    rhs: RRhs,
    top_level: *const UniqueSet,
    refs: *std.ArrayListUnmanaged(u64),
    alloc: std.mem.Allocator,
) std.mem.Allocator.Error!void {
    switch (rhs) {
        .UnGuarded => |e| try collectExprVarRefs(e, top_level, refs, alloc),
        .Guarded => |guards| {
            for (guards) |g| {
                for (g.guards) |guard| {
                    switch (guard) {
                        .PatGuard => |pg| try collectExprVarRefs(pg.expr, top_level, refs, alloc),
                        .ExprGuard => |e| try collectExprVarRefs(e, top_level, refs, alloc),
                    }
                }
                try collectExprVarRefs(g.rhs, top_level, refs, alloc);
            }
        },
    }
}

/// Collect variable references from a declaration (FunBind or PatBind RHS).
fn collectDeclVarRefs(
    decl: RDecl,
    top_level: *const UniqueSet,
    refs: *std.ArrayListUnmanaged(u64),
    alloc: std.mem.Allocator,
) std.mem.Allocator.Error!void {
    switch (decl) {
        .FunBind => |fb| {
            for (fb.equations) |eq| {
                try collectRhsVarRefs(eq.rhs, top_level, refs, alloc);
            }
        },
        .PatBind => |pb| {
            try collectRhsVarRefs(pb.rhs, top_level, refs, alloc);
        },
        else => {},
    }
}

// ── Public API ──────────────────────────────────────────────────────────

/// A group of mutually recursive (or independent) declarations.
pub const DeclGroup = struct {
    /// Indices into the original `module.declarations` slice.
    decl_indices: []const u32,
    /// True if the group has more than one member, or a single member
    /// that references itself (direct recursion).
    is_recursive: bool,
};

/// Analyse dependencies among top-level value declarations and return
/// groups in dependency order (leaves first).
///
/// Non-value declarations (TypeSig, DataDecl, ClassDecl, InstanceDecl,
/// ForeignPrim) are excluded — they are processed by earlier passes.
pub fn computeDeclGroups(
    declarations: []const RDecl,
    alloc: std.mem.Allocator,
) std.mem.Allocator.Error![]const DeclGroup {
    // Step 1: Collect top-level value binder uniques → vertex index.
    var unique_to_vertex = UniqueSet{};
    defer unique_to_vertex.deinit(alloc);
    var vertex_to_decl = std.ArrayListUnmanaged(u32){};
    defer vertex_to_decl.deinit(alloc);
    var unique_to_idx = std.AutoHashMapUnmanaged(u64, u32){};
    defer unique_to_idx.deinit(alloc);

    for (declarations, 0..) |decl, di| {
        const unique_val: ?u64 = switch (decl) {
            .FunBind => |fb| fb.name.unique.value,
            .PatBind => |pb| switch (pb.pattern) {
                .Var => |v| v.name.unique.value,
                else => null,
            },
            else => null,
        };
        if (unique_val) |uv| {
            const vertex: u32 = @intCast(vertex_to_decl.items.len);
            try unique_to_vertex.put(alloc, uv, {});
            try unique_to_idx.put(alloc, uv, vertex);
            try vertex_to_decl.append(alloc, @intCast(di));
        }
    }

    const n = vertex_to_decl.items.len;
    if (n == 0) return &.{};

    // Step 2: Build adjacency list.
    var edges = try alloc.alloc(std.ArrayListUnmanaged(u32), n);
    for (0..n) |i| edges[i] = .{};
    defer {
        for (edges) |*e| e.deinit(alloc);
        alloc.free(edges);
    }

    for (declarations) |decl| {
        const src_unique: ?u64 = switch (decl) {
            .FunBind => |fb| fb.name.unique.value,
            .PatBind => |pb| switch (pb.pattern) {
                .Var => |v| v.name.unique.value,
                else => null,
            },
            else => null,
        };
        const src_vertex = if (src_unique) |su| unique_to_idx.get(su) else null;
        if (src_vertex == null) continue;

        var refs = std.ArrayListUnmanaged(u64){};
        defer refs.deinit(alloc);
        try collectDeclVarRefs(decl, &unique_to_vertex, &refs, alloc);

        for (refs.items) |ref_unique| {
            const dst_vertex = unique_to_idx.get(ref_unique) orelse continue;
            // Add edge (including self-edges for self-recursion detection).
            var found = false;
            for (edges[src_vertex.?].items) |existing| {
                if (existing == dst_vertex) {
                    found = true;
                    break;
                }
            }
            if (!found) try edges[src_vertex.?].append(alloc, dst_vertex);
        }
    }

    // Step 3: Tarjan's SCC.
    const sccs = try tarjanScc(n, edges, alloc);
    defer {
        for (sccs) |scc| alloc.free(scc);
        alloc.free(sccs);
    }

    // Step 4: Convert SCCs to DeclGroups.
    // Tarjan emits SCCs in reverse topological order (leaves first).
    var groups = std.ArrayListUnmanaged(DeclGroup){};
    for (sccs) |scc| {
        const decl_indices = try alloc.alloc(u32, scc.len);
        var is_recursive = scc.len > 1;
        for (scc, 0..) |vertex, i| {
            decl_indices[i] = vertex_to_decl.items[vertex];
            // Check self-reference for singleton SCCs.
            if (scc.len == 1) {
                for (edges[vertex].items) |dst| {
                    if (dst == vertex) {
                        is_recursive = true;
                        break;
                    }
                }
            }
        }
        try groups.append(alloc, .{
            .decl_indices = decl_indices,
            .is_recursive = is_recursive,
        });
    }
    return groups.toOwnedSlice(alloc);
}

// ── Tarjan's SCC (adapted from src/modules/module_graph.zig) ────────────

const TarjanState = struct {
    alloc: std.mem.Allocator,
    edges: []const std.ArrayListUnmanaged(u32),
    index_counter: u32,
    stack: std.ArrayListUnmanaged(u32),
    on_stack: []bool,
    indices: []i64,
    lowlinks: []u32,
    sccs: std.ArrayListUnmanaged([]u32),
};

fn tarjanScc(
    n: usize,
    edges: []const std.ArrayListUnmanaged(u32),
    alloc: std.mem.Allocator,
) std.mem.Allocator.Error![][]u32 {
    var state = TarjanState{
        .alloc = alloc,
        .edges = edges,
        .index_counter = 0,
        .stack = .{},
        .on_stack = try alloc.alloc(bool, n),
        .indices = try alloc.alloc(i64, n),
        .lowlinks = try alloc.alloc(u32, n),
        .sccs = .{},
    };
    defer {
        state.stack.deinit(alloc);
        alloc.free(state.on_stack);
        alloc.free(state.indices);
        alloc.free(state.lowlinks);
    }
    @memset(state.indices, -1);
    @memset(state.on_stack, false);

    for (0..n) |v| {
        if (state.indices[v] == -1) {
            try tarjanVisit(&state, @intCast(v));
        }
    }
    return state.sccs.toOwnedSlice(alloc);
}

fn tarjanVisit(s: *TarjanState, v: u32) std.mem.Allocator.Error!void {
    s.indices[v] = s.index_counter;
    s.lowlinks[v] = s.index_counter;
    s.index_counter += 1;
    try s.stack.append(s.alloc, v);
    s.on_stack[v] = true;

    for (s.edges[v].items) |w| {
        if (s.indices[w] == -1) {
            try tarjanVisit(s, w);
            s.lowlinks[v] = @min(s.lowlinks[v], s.lowlinks[w]);
        } else if (s.on_stack[w]) {
            s.lowlinks[v] = @min(s.lowlinks[v], @as(u32, @intCast(s.indices[w])));
        }
    }

    if (s.lowlinks[v] == @as(u32, @intCast(s.indices[v]))) {
        var scc = std.ArrayListUnmanaged(u32){};
        while (true) {
            const w = s.stack.pop().?;
            s.on_stack[w] = false;
            try scc.append(s.alloc, w);
            if (w == v) break;
        }
        try s.sccs.append(s.alloc, try scc.toOwnedSlice(s.alloc));
    }
}

// ── Tests ───────────────────────────────────────────────────────────────

const testing = std.testing;
const ast = @import("../frontend/ast.zig");

fn testName(base: []const u8, unique: u64) Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn testSpan() SourceSpan {
    const SourcePos = @import("../core/ast.zig").SourcePos;
    return SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 10));
}

test "computeDeclGroups: independent functions are separate singletons" {
    const lit_expr_1 = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const lit_expr_2 = RExpr{ .Lit = .{ .Int = .{ .value = 2, .span = testSpan() } } };

    const decls = [_]RDecl{
        .{ .FunBind = .{
            .name = testName("f", 1),
            .equations = &.{RMatch{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit_expr_1 }, .span = testSpan() }},
            .span = testSpan(),
        } },
        .{ .FunBind = .{
            .name = testName("g", 2),
            .equations = &.{RMatch{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit_expr_2 }, .span = testSpan() }},
            .span = testSpan(),
        } },
    };

    const groups = try computeDeclGroups(&decls, testing.allocator);
    defer {
        for (groups) |g| testing.allocator.free(g.decl_indices);
        testing.allocator.free(groups);
    }

    try testing.expectEqual(@as(usize, 2), groups.len);
    try testing.expect(!groups[0].is_recursive);
    try testing.expect(!groups[1].is_recursive);
}

test "computeDeclGroups: forward reference creates dependency order" {
    const g_ref = RExpr{ .Var = .{ .name = testName("g", 2), .span = testSpan() } };
    const lit_expr = RExpr{ .Lit = .{ .Int = .{ .value = 42, .span = testSpan() } } };

    const decls = [_]RDecl{
        .{ .FunBind = .{
            .name = testName("f", 1),
            .equations = &.{RMatch{ .patterns = &.{}, .rhs = .{ .UnGuarded = g_ref }, .span = testSpan() }},
            .span = testSpan(),
        } },
        .{ .FunBind = .{
            .name = testName("g", 2),
            .equations = &.{RMatch{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit_expr }, .span = testSpan() }},
            .span = testSpan(),
        } },
    };

    const groups = try computeDeclGroups(&decls, testing.allocator);
    defer {
        for (groups) |g| testing.allocator.free(g.decl_indices);
        testing.allocator.free(groups);
    }

    // g (decl index 1) should come before f (decl index 0) in dependency order.
    try testing.expectEqual(@as(usize, 2), groups.len);
    try testing.expectEqual(@as(u32, 1), groups[0].decl_indices[0]);
    try testing.expectEqual(@as(u32, 0), groups[1].decl_indices[0]);
}

test "computeDeclGroups: mutual recursion forms single group" {
    const g_ref = RExpr{ .Var = .{ .name = testName("g", 2), .span = testSpan() } };
    const f_ref = RExpr{ .Var = .{ .name = testName("f", 1), .span = testSpan() } };

    const decls = [_]RDecl{
        .{ .FunBind = .{
            .name = testName("f", 1),
            .equations = &.{RMatch{ .patterns = &.{}, .rhs = .{ .UnGuarded = g_ref }, .span = testSpan() }},
            .span = testSpan(),
        } },
        .{ .FunBind = .{
            .name = testName("g", 2),
            .equations = &.{RMatch{ .patterns = &.{}, .rhs = .{ .UnGuarded = f_ref }, .span = testSpan() }},
            .span = testSpan(),
        } },
    };

    const groups = try computeDeclGroups(&decls, testing.allocator);
    defer {
        for (groups) |g| testing.allocator.free(g.decl_indices);
        testing.allocator.free(groups);
    }

    try testing.expectEqual(@as(usize, 1), groups.len);
    try testing.expectEqual(@as(usize, 2), groups[0].decl_indices.len);
    try testing.expect(groups[0].is_recursive);
}

test "computeDeclGroups: self-recursive function is marked recursive" {
    const f_ref = RExpr{ .Var = .{ .name = testName("f", 1), .span = testSpan() } };

    const decls = [_]RDecl{
        .{ .FunBind = .{
            .name = testName("f", 1),
            .equations = &.{RMatch{ .patterns = &.{}, .rhs = .{ .UnGuarded = f_ref }, .span = testSpan() }},
            .span = testSpan(),
        } },
    };

    const groups = try computeDeclGroups(&decls, testing.allocator);
    defer {
        for (groups) |g| testing.allocator.free(g.decl_indices);
        testing.allocator.free(groups);
    }

    try testing.expectEqual(@as(usize, 1), groups.len);
    try testing.expect(groups[0].is_recursive);
}
