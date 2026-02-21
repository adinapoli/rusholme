const std = @import("std");
const ast_mod = @import("../core/ast.zig");
const renamer_mod = @import("../renamer/renamer.zig");
const infer_mod = @import("../typechecker/infer.zig");
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");
const Name = ast_mod.Name;
const SourceSpan = ast_mod.SourceSpan;
const SourcePos = ast_mod.SourcePos;
const DiagnosticCollector = @import("../diagnostics/diagnostic.zig").DiagnosticCollector;

pub const DesugarCtx = struct {
    alloc: std.mem.Allocator,
    types: *const infer_mod.ModuleTypes,
    diags: *DiagnosticCollector,
};

// Synthetic span for desugared constructs
fn syntheticSpan() SourceSpan {
    return SourceSpan.init(SourcePos.invalid(), SourcePos.invalid());
}

fn htypeToCore(alloc: std.mem.Allocator, ty: *const htype_mod.HType) !ast_mod.CoreType {
    return ty.toCore(alloc);
}

fn schemeToCore(alloc: std.mem.Allocator, scheme: env_mod.TyScheme) !ast_mod.CoreType {
    // Convert the scheme's body to CoreType.
    var ty = try scheme.body.toCore(alloc);
    // Wrap in ForAllTy for each binder.
    // TyScheme binders are just Unique IDs. We have to synthesize Names for them.
    for (scheme.binders) |b_id| {
        const p_ty = try alloc.create(ast_mod.CoreType);
        p_ty.* = ty;
        ty = ast_mod.CoreType{
            .ForAllTy = .{
                .binder = Name{ .base = "a", .unique = .{ .value = b_id } },
                .body = p_ty,
            },
        };
    }
    return ty;
}

pub fn desugarModule(
    alloc: std.mem.Allocator,
    module: renamer_mod.RenamedModule,
    module_types: *const infer_mod.ModuleTypes,
    diags: *DiagnosticCollector,
) std.mem.Allocator.Error!ast_mod.CoreProgram {
    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = module_types,
        .diags = diags,
    };

    var binds = std.ArrayListUnmanaged(ast_mod.Bind){};
    errdefer binds.deinit(alloc);

    for (module.declarations) |decl| {
        switch (decl) {
            .FunBind => |fb| {
                const scheme = module_types.schemes.get(fb.name.unique) orelse continue;
                const core_ty = try schemeToCore(alloc, scheme);

                const binder_id = ast_mod.Id{
                    .name = fb.name,
                    .ty = core_ty,
                    .span = fb.span,
                };

                // For M1, we assume single equation, single match, or desugar to lambdas/cases.
                // Re-using the logic from infer: typically we have equations.
                // A complete desugarer would build a match compiler here.
                // For now, we simply translate the RHS of the first equation.
                if (fb.equations.len > 0) {
                    const eq = fb.equations[0];
                    var body = try desugarRhs(&ctx, eq.rhs);

                    // Wrap body in lambdas for the parameters
                    var i = eq.patterns.len;
                    while (i > 0) {
                        i -= 1;
                        const pat = eq.patterns[i];
                        switch (pat) {
                            .Var => |v| {
                                const p_body = try alloc.create(ast_mod.Expr);
                                p_body.* = body;

                                const p_ty_ptr = module_types.local_binders.get(v.name.unique) orelse {
                                    std.debug.panic("Missing type for parameter {s}", .{v.name.base});
                                };
                                const p_ty = try htypeToCore(alloc, p_ty_ptr);

                                body = ast_mod.Expr{
                                    .Lam = .{
                                        .binder = ast_mod.Id{ .name = v.name, .ty = p_ty, .span = v.span },
                                        .body = p_body,
                                        .span = syntheticSpan(), // ideally span covering lam
                                    },
                                };
                            },
                            else => {
                                // Match compiler needed for complex patterns in args.
                                std.debug.panic("Pattern matching in function args not fully implemented for Core translation yet", .{});
                            },
                        }
                    }

                    const p_body = try alloc.create(ast_mod.Expr);
                    p_body.* = body;

                    try binds.append(alloc, .{ .NonRec = .{
                        .binder = binder_id,
                        .rhs = p_body,
                    } });
                }
            },
            .PatBind => |pb| {
                switch (pb.pattern) {
                    .Var => |v| {
                        const ty_ptr = module_types.local_binders.get(v.name.unique) orelse {
                            std.debug.panic("Missing type for top-level patbind {s}", .{v.name.base});
                        };
                        const core_ty = try htypeToCore(alloc, ty_ptr);
                        const binder_id = ast_mod.Id{
                            .name = v.name,
                            .ty = core_ty,
                            .span = v.span,
                        };
                        const rhs = try alloc.create(ast_mod.Expr);
                        rhs.* = try desugarRhs(&ctx, pb.rhs);
                        try binds.append(alloc, .{ .NonRec = .{
                            .binder = binder_id,
                            .rhs = rhs,
                        } });
                    },
                    else => std.debug.panic("Complex top-level pattern bindings not implemented in desugarer", .{}),
                }
            },
            else => {},
        }
    }

    return binds.toOwnedSlice(alloc);
}

fn desugarRhs(ctx: *DesugarCtx, rhs: renamer_mod.RRhs) !ast_mod.Expr {
    switch (rhs) {
        .UnGuarded => |expr| return (try desugarExpr(ctx, expr)).*,
        .Guarded => std.debug.panic("Guarded RHS not yet supported in desugarer", .{}),
    }
}

pub fn desugarExpr(ctx: *DesugarCtx, expr: renamer_mod.RExpr) std.mem.Allocator.Error!*ast_mod.Expr {
    const alloc = ctx.alloc;
    const node = try alloc.create(ast_mod.Expr);

    switch (expr) {
        .Var => |v| {
            // It could be a local binder or a top-level scheme.
            if (ctx.types.local_binders.get(v.name.unique)) |ty_ptr| {
                const ty = try htypeToCore(alloc, ty_ptr);
                node.* = .{ .Var = .{ .name = v.name, .ty = ty, .span = v.span } };
            } else if (ctx.types.schemes.get(v.name.unique)) |scheme| {
                const ty = try schemeToCore(alloc, scheme);
                node.* = .{ .Var = .{ .name = v.name, .ty = ty, .span = v.span } };
            } else {
                std.debug.panic("Variable {s} (id {d}) not found in type definitions", .{ v.name.base, v.name.unique.value });
            }
        },
        .Lit => |l| {
            // In a complete compiler, we'd lookup Enum types based on Literal variant.
            node.* = .{ .Lit = .{ .val = desugarLiteral(l), .span = l.getSpan() } };
        },
        .App => |a| {
            node.* = .{
                .App = .{
                    .fn_expr = try desugarExpr(ctx, a.fn_expr.*),
                    .arg = try desugarExpr(ctx, a.arg_expr.*),
                    .span = syntheticSpan(), // Can improve span tracking
                },
            };
        },
        .Lambda => |lam| {
            var body = (try desugarExpr(ctx, lam.body.*)).*;
            var i = lam.params.len;
            while (i > 0) {
                i -= 1;
                const param = lam.params[i];
                const span = lam.param_spans[i];

                const p_body = try alloc.create(ast_mod.Expr);
                p_body.* = body;

                const p_ty_ptr = ctx.types.local_binders.get(param.unique) orelse {
                    std.debug.panic("Missing type for lambda param {s}", .{param.base});
                };
                const p_ty = try htypeToCore(alloc, p_ty_ptr);

                body = ast_mod.Expr{ .Lam = .{
                    .binder = ast_mod.Id{ .name = param, .ty = p_ty, .span = span },
                    .body = p_body,
                    .span = syntheticSpan(),
                } };
            }
            node.* = body;
        },
        .Let => |let_blk| {
            const body = try desugarExpr(ctx, let_blk.body.*);

            // Nested lets: in functional languages, `let x = ...; y = ... in body`
            // desugars to either Rec binds or nested NonRec binds.
            // For M1, we'll assume mutually recursive and build a Rec block for all FunBinds.
            // Real desugarer would dependency-analyse.
            var pairs = std.ArrayListUnmanaged(ast_mod.BindPair){};
            defer pairs.deinit(alloc);

            for (let_blk.binds) |bd| {
                switch (bd) {
                    .FunBind => |fb| {
                        if (fb.equations.len > 0) {
                            const eq = fb.equations[0]; // naive: assume 1 eq, no args
                            const rhs = try alloc.create(ast_mod.Expr);
                            rhs.* = try desugarRhs(ctx, eq.rhs);

                            const ty_ptr = ctx.types.local_binders.get(fb.name.unique) orelse {
                                std.debug.panic("Missing type for let funbind {s}", .{fb.name.base});
                            };
                            const ty = try htypeToCore(alloc, ty_ptr);

                            try pairs.append(alloc, .{
                                .binder = ast_mod.Id{ .name = fb.name, .ty = ty, .span = fb.span },
                                .rhs = rhs,
                            });
                        }
                    },
                    .PatBind => |pb| {
                        if (pb.pattern == .Var) {
                            const v = pb.pattern.Var;
                            const rhs = try alloc.create(ast_mod.Expr);
                            rhs.* = try desugarRhs(ctx, pb.rhs);

                            const ty_ptr = ctx.types.local_binders.get(v.name.unique) orelse {
                                std.debug.panic("Missing type for let patbind {s}", .{v.name.base});
                            };
                            const ty = try htypeToCore(alloc, ty_ptr);

                            try pairs.append(alloc, .{
                                .binder = ast_mod.Id{ .name = v.name, .ty = ty, .span = v.span },
                                .rhs = rhs,
                            });
                        }
                    },
                    else => {},
                }
            }

            node.* = .{ .Let = .{
                .bind = .{ .Rec = try pairs.toOwnedSlice(alloc) },
                .body = body,
                .span = syntheticSpan(),
            } };
        },
        .If => |if_blk| {
            // if c then t else e => case c of True -> t; False -> e
            const cond = try desugarExpr(ctx, if_blk.condition.*);
            const then_e = try desugarExpr(ctx, if_blk.then_expr.*);
            const else_e = try desugarExpr(ctx, if_blk.else_expr.*);

            // Result type of the case
            // Let's conservatively assume the if is well-typed and has the type of `then_e`.
            // Note: we can't easily extract type from CoreExpr without a typeof pass.
            // For M1, we'll try to get it from the environment if possible, or use a dummy.
            // Actually, Core Expr doesn't cache types bottom-up, we'd need to compute it.
            // To simplify, we peek into local_binders? No, then_e could be complex.
            // We use a dummy for now since M1 GRIN codegen won't rely strictly on it.
            const dummy_ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } };

            var alts = try alloc.alloc(ast_mod.Alt, 2);
            // True case
            alts[0] = .{
                .con = .{ .DataAlt = Name{ .base = "True", .unique = .{ .value = 0 } } },
                .binders = &.{},
                .body = then_e,
            };
            // False case
            alts[1] = .{
                .con = .{ .DataAlt = Name{ .base = "False", .unique = .{ .value = 1 } } },
                .binders = &.{},
                .body = else_e,
            };

            const wild_id = ast_mod.Id{
                .name = Name{ .base = "wild", .unique = .{ .value = 99999 } },
                .ty = dummy_ty,
                .span = syntheticSpan(),
            };

            node.* = .{ .Case = .{
                .scrutinee = cond,
                .binder = wild_id,
                .ty = dummy_ty,
                .alts = alts,
                .span = syntheticSpan(),
            } };
        },
        // Fallbacks for unhandled AST nodes
        else => std.debug.panic("desugarExpr: unhandled RExpr variant {}", .{std.meta.activeTag(expr)}),
    }

    return node;
}

fn desugarLiteral(lit: @import("../frontend/ast.zig").Literal) ast_mod.Literal {
    return switch (lit) {
        .Int => |i| .{ .Int = i.value },
        .Float => |f| .{ .Float = f.value },
        .Char => |c| .{ .Char = c.value },
        .String => |s| .{ .String = s.value },
        .Rational => |r| .{ .Int = r.numerator }, // Simple approximation for now
    };
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

fn testName(base: []const u8, id: u64) Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

test "desugarExpr: Var and Lit" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{
        .schemes = .{},
        .local_binders = .{},
    };
    defer types.deinit(alloc);

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = &types,
        .diags = &diags,
    };

    // Add a local binder type mapping
    const int_h_ty = try alloc.create(htype_mod.HType);
    int_h_ty.* = .{ .Con = .{ .name = testName("Int", 0), .args = &.{} } };
    const x_name = testName("x", 42);
    try types.local_binders.put(alloc, x_name.unique, int_h_ty);

    // Test Lit
    const lit_node = renamer_mod.RExpr{
        .Lit = .{ .Int = .{ .value = 123, .span = syntheticSpan() } },
    };
    const c_lit = try desugarExpr(&ctx, lit_node);
    try testing.expect(c_lit.* == .Lit);
    try testing.expectEqual(@as(i64, 123), c_lit.Lit.val.Int);

    // Test Var
    const var_node = renamer_mod.RExpr{
        .Var = .{ .name = x_name, .span = syntheticSpan() },
    };
    const c_var = try desugarExpr(&ctx, var_node);
    try testing.expect(c_var.* == .Var);
    try testing.expectEqualStrings("x", c_var.Var.name.base);
    try testing.expect(c_var.Var.ty == .TyCon);
    try testing.expectEqualStrings("Int", c_var.Var.ty.TyCon.name.base);
}
