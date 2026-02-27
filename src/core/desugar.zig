const std = @import("std");
const ast_mod = @import("../core/ast.zig");
const renamer_mod = @import("../renamer/renamer.zig");
const infer_mod = @import("../typechecker/infer.zig");
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");
const Known = @import("../naming/known.zig");
const naming_mod = @import("../naming/unique.zig");
const Name = ast_mod.Name;
const SourceSpan = ast_mod.SourceSpan;
const SourcePos = ast_mod.SourcePos;
const DiagnosticCollector = @import("../diagnostics/diagnostic.zig").DiagnosticCollector;

pub const DesugarCtx = struct {
    alloc: std.mem.Allocator,
    types: *const infer_mod.ModuleTypes,
    diags: *DiagnosticCollector,
    /// Used to generate fresh unique values for synthetic binders (lambda
    /// parameters created by the pattern-match compiler, constructor field
    /// binders, etc.). Each synthetic binder must get a globally unique ID so
    /// that the GRIN translator can distinguish them in its `var_map`.
    u_supply: *naming_mod.UniqueSupply,
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
    u_supply: *naming_mod.UniqueSupply,
) std.mem.Allocator.Error!ast_mod.CoreProgram {
    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = module_types,
        .diags = diags,
        .u_supply = u_supply,
    };

    var binds = std.ArrayListUnmanaged(ast_mod.Bind){};
    errdefer binds.deinit(alloc);

    var data_decls = std.ArrayListUnmanaged(ast_mod.CoreDataDecl){};
    errdefer data_decls.deinit(alloc);

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

                // Check if this FunBind needs pattern match compilation
                var needs_match_compiler = fb.equations.len > 1;
                if (!needs_match_compiler and fb.equations.len > 0) {
                    for (fb.equations[0].patterns) |pat| {
                        if (pat != .Var) {
                            needs_match_compiler = true;
                            break;
                        }
                    }
                }

                if (needs_match_compiler) {
                    const p_body = try desugarMatch(&ctx, fb.equations, core_ty);
                    try binds.append(alloc, .{ .NonRec = .{
                        .binder = binder_id,
                        .rhs = p_body,
                    } });
                } else if (fb.equations.len > 0) {
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
                            else => unreachable, // Blocked by needs_match_compiler check
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
            .DataDecl => |dd| {
                var tyvars = try alloc.alloc(Name, dd.tyvars.len);
                for (dd.tyvars, 0..) |tv_str, i| {
                    tyvars[i] = Name{ .base = tv_str, .unique = .{ .value = 0 } };
                }

                var cons = try alloc.alloc(ast_mod.Id, dd.constructors.len);
                for (dd.constructors, 0..) |con, i| {
                    const scheme = module_types.schemes.get(con.name.unique) orelse {
                        std.debug.panic("Missing type scheme for data constructor {s}", .{con.name.base});
                    };
                    const core_ty = try schemeToCore(alloc, scheme);
                    cons[i] = ast_mod.Id{
                        .name = con.name,
                        .ty = core_ty,
                        .span = con.span,
                    };
                }

                try data_decls.append(alloc, .{
                    .name = dd.name,
                    .tyvars = tyvars,
                    .constructors = cons,
                    .span = dd.span,
                });
            },
            else => {},
        }
    }

    return ast_mod.CoreProgram{
        .data_decls = try data_decls.toOwnedSlice(alloc),
        .binds = try binds.toOwnedSlice(alloc),
    };
}

fn desugarRhs(ctx: *DesugarCtx, rhs: renamer_mod.RRhs) !ast_mod.Expr {
    switch (rhs) {
        .UnGuarded => |expr| return (try desugarExpr(ctx, expr)).*,
        // tracked in: https://github.com/adinapoli/rusholme/issues/417
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
        .List => |elems| {
            // [e1, e2, ..., en] desugars to (:) e1 ((:) e2 (... ((:) en []) ...))
            const cons_ty = blk: {
                const scheme = ctx.types.schemes.get(Known.Con.Cons.unique) orelse
                    std.debug.panic("Missing type scheme for (:) constructor", .{});
                break :blk try schemeToCore(alloc, scheme);
            };
            const nil_ty = blk: {
                const scheme = ctx.types.schemes.get(Known.Con.Nil.unique) orelse
                    std.debug.panic("Missing type scheme for [] constructor", .{});
                break :blk try schemeToCore(alloc, scheme);
            };

            // Start with Nil: []
            var result = try alloc.create(ast_mod.Expr);
            result.* = .{ .Var = .{ .name = Known.Con.Nil, .ty = nil_ty, .span = syntheticSpan() } };

            // Right-fold: iterate elements from right to left
            var i = elems.len;
            while (i > 0) {
                i -= 1;
                const elem = try desugarExpr(ctx, elems[i]);

                // Build: (:) elem result
                // First apply Cons to the element: ((:) elem)
                const cons_var = try alloc.create(ast_mod.Expr);
                cons_var.* = .{ .Var = .{ .name = Known.Con.Cons, .ty = cons_ty, .span = syntheticSpan() } };

                const app1 = try alloc.create(ast_mod.Expr);
                app1.* = .{ .App = .{ .fn_expr = cons_var, .arg = elem, .span = syntheticSpan() } };

                // Then apply to the tail: ((:) elem) result
                const app2 = try alloc.create(ast_mod.Expr);
                app2.* = .{ .App = .{ .fn_expr = app1, .arg = result, .span = syntheticSpan() } };

                result = app2;
            }

            node.* = result.*;
        },
        .Paren => |inner| {
            // Parenthesised expression — just unwrap.
            const inner_result = try desugarExpr(ctx, inner.*);
            node.* = inner_result.*;
        },

        // ── Not yet implemented ─────────────────────────────────────────
        //
        // Each unsupported case has its own explicit handler below (tracked in
        // https://github.com/adinapoli/rusholme/issues/361). See #309 for ListComp.
        .Case => {
            // RExpr case expressions - desugar to Core case
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_case", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .Do => {
            // Do-notation - desugar to bind chaining
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_do", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .InfixApp => |infix| {
            // Infix operator application: `left op right` desugars to
            // `App(App(op, left), right)` using curried form.
            // tracked in: https://github.com/adinapoli/rusholme/issues/361

            // Special case: `$` (function application operator) is purely
            // syntactic — `f $ x` is identical to `f x`.  Desugar directly
            // to `App(left, right)` without materialising an operator node.
            if (std.mem.eql(u8, infix.op.base, "$")) {
                const left_result = try desugarExpr(ctx, infix.left.*);
                const right_result = try desugarExpr(ctx, infix.right.*);
                const app = try alloc.create(ast_mod.Expr);
                app.* = .{ .App = .{
                    .fn_expr = left_result,
                    .arg = right_result,
                    .span = syntheticSpan(),
                } };
                node.* = app.*;
                return node;
            }

            // General case: look up the operator's Core type.
            const op_ty_ptr = ctx.types.local_binders.get(infix.op.unique);
            const core_op_ty: ast_mod.CoreType = if (op_ty_ptr) |ty| blk: {
                // Guard against unsolved metavariables — if the operator type
                // is still a free meta the solver could not determine it.
                const chased = ty.chase();
                if (chased == .Meta) {
                    // Operator type could not be resolved (constraint solver
                    // incomplete). Use a synthetic TyVar as a placeholder so
                    // downstream passes do not crash.
                    // tracked in: https://github.com/adinapoli/rusholme/issues/407
                    break :blk ast_mod.CoreType{ .TyVar = Name{ .base = infix.op.base, .unique = infix.op.unique } };
                }
                break :blk try htypeToCore(alloc, ty);
            } else if (ctx.types.schemes.get(infix.op.unique)) |scheme|
                try schemeToCore(alloc, scheme)
            else blk: {
                // Operator is not in local_binders or schemes (e.g. a free
                // variable that the renamer could not resolve).  Use a
                // synthetic type rather than panicking — the program is
                // already ill-typed but we produce a best-effort Core IR.
                // tracked in: https://github.com/adinapoli/rusholme/issues/407
                break :blk ast_mod.CoreType{ .TyVar = Name{ .base = infix.op.base, .unique = infix.op.unique } };
            };

            const op_var = try alloc.create(ast_mod.Expr);
            op_var.* = .{ .Var = .{
                .name = Name{ .base = infix.op.base, .unique = infix.op.unique },
                .ty = core_op_ty,
                .span = syntheticSpan(),
            } };

            // Desugar left operand
            const left_result = try desugarExpr(ctx, infix.left.*);

            // Create app: op left
            const app1 = try alloc.create(ast_mod.Expr);
            app1.* = .{ .App = .{
                .fn_expr = op_var,
                .arg = left_result,
                .span = syntheticSpan(),
            } };

            // Desugar right operand
            const right_result = try desugarExpr(ctx, infix.right.*);

            // Create app: (op left) right
            const app2 = try alloc.create(ast_mod.Expr);
            app2.* = .{ .App = .{
                .fn_expr = app1,
                .arg = right_result,
                .span = syntheticSpan(),
            } };

            node.* = app2.*;
        },
        .LeftSection => {
            // Left operator section (e.g., (x +))
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_leftsection", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .RightSection => {
            // Right operator section (e.g., (+ x))
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_rightsection", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .Negate => {
            // Numeric negation
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_negate", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .Tuple => {
            // Tuple expressions
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_tuple", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .EnumFrom, .EnumFromThen, .EnumFromTo, .EnumFromThenTo => {
            // Arithmetic sequences
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_seq", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .TypeAnn => {
            // Type annotations (erased at this stage)
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "unit", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .TypeApp => {
            // Type applications (erased at this stage)
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "unit", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
        .RecordCon, .RecordUpdate, .Field => {
            // Record syntax
            // tracked in: https://github.com/adinapoli/rusholme/issues/361
            node.* = .{ .Var = .{
                .name = Name{ .base = "todo_record", .unique = .{ .value = 0 } },
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = syntheticSpan(),
            } };
        },
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

// ── Pattern Match Compiler (Tier 1) ────────────────────────────────────

/// Extract the argument types from a function's CoreType by peeling off
/// ForAllTy and FunTy layers.
fn getArgTypes(alloc: std.mem.Allocator, ty: ast_mod.CoreType, num_args: usize) ![]const ast_mod.CoreType {
    var types = try alloc.alloc(ast_mod.CoreType, num_args);
    var current = ty;
    // skip foralls
    while (current == .ForAllTy) {
        current = current.ForAllTy.body.*;
    }
    for (0..num_args) |i| {
        if (current != .FunTy) {
            std.debug.panic("Expected FunTy for argument {d}, got {any}", .{ i, current });
        }
        types[i] = current.FunTy.arg.*;
        current = current.FunTy.res.*;
    }
    return types;
}

/// Pattern Match Compiler (Tier 2: nested patterns, as-patterns, tuples, infix cons).
///
/// Translates multi-equation `FunBind`s or single equations with non-Var patterns
/// into a series of `Lam` abstractions over a nested sequential `Case` tree.
///
/// This implements Sestoft's sequential algorithm (SLPJ Ch.5 mixture rule):
/// each equation's patterns are matched left-to-right; each pattern match
/// produces either a `Case` expression (for constructor/literal patterns), a
/// `let` binding (for variable/as patterns), or nothing (for wildcards).  Nested
/// constructor patterns are handled by binding each constructor field to a fresh
/// variable, then recursively matching the sub-pattern against that field.
///
/// Supported pattern kinds:
///   Var, Wild, Lit, Con (including nested), Tuple, InfixCon (:), AsPat
///   Paren — transparent wrapper, unwrapped before dispatch
///
/// Tracked limitations (separate issues):
///   Guards          — tracked in: https://github.com/adinapoli/rusholme/issues/417
///   List patterns   — tracked in: https://github.com/adinapoli/rusholme/issues/418
///   Decision trees  — tracked in: https://github.com/adinapoli/rusholme/issues/378
fn desugarMatch(
    ctx: *DesugarCtx,
    equations: []const renamer_mod.RMatch,
    core_ty: ast_mod.CoreType,
) !*ast_mod.Expr {
    const num_args = equations[0].patterns.len;
    if (num_args == 0) {
        // Nullary function -- just desugar the first equation's RHS.
        const rhs_expr = try ctx.alloc.create(ast_mod.Expr);
        rhs_expr.* = try desugarRhs(ctx, equations[0].rhs);
        return rhs_expr;
    }

    const arg_tys = try getArgTypes(ctx.alloc, core_ty, num_args);

    // Create fresh lambda binders: `arg_0, arg_1, ...`
    // Each binder gets a fresh unique so that the GRIN translator's var_map
    // can distinguish parameters that share the same base name (e.g. when the
    // pattern-match compiler generates multiple `arg_N` parameters).
    var binders = try ctx.alloc.alloc(ast_mod.Id, num_args);
    for (0..num_args) |i| {
        const arg_name = try std.fmt.allocPrint(ctx.alloc, "arg_{d}", .{i});
        binders[i] = .{
            .name = .{ .base = arg_name, .unique = ctx.u_supply.fresh() },
            .ty = arg_tys[i],
            .span = syntheticSpan(),
        };
    }

    // Process equations from top to bottom.
    // We build the body inside-out: start with the last fallback (a non-exhaustive
    // error literal), then layer on the equations from bottom to top.
    var current_body = try ctx.alloc.create(ast_mod.Expr);
    current_body.* = .{
        .Lit = .{
            .val = .{ .String = "Non-exhaustive patterns in function" },
            .span = syntheticSpan(),
        },
    };

    var eq_idx: usize = equations.len;
    while (eq_idx > 0) {
        eq_idx -= 1;
        const eq = equations[eq_idx];

        // The base RHS for this equation.
        var eq_body = try ctx.alloc.create(ast_mod.Expr);
        eq_body.* = try desugarRhs(ctx, eq.rhs);

        // Build sequential matches for each argument, from right to left.
        var arg_idx: usize = num_args;
        while (arg_idx > 0) {
            arg_idx -= 1;
            // Unwrap Paren layers — `(Pat)` is semantically identical to `Pat`.
            var pat = eq.patterns[arg_idx];
            while (pat == .Paren) pat = pat.Paren.*;

            const scrut_expr = try ctx.alloc.create(ast_mod.Expr);
            scrut_expr.* = .{ .Var = binders[arg_idx] };

            eq_body = try applyPat(
                ctx,
                scrut_expr,
                binders[arg_idx],
                arg_tys[arg_idx],
                pat,
                eq_body,
                current_body,
                arg_idx,
                0,
            );
        }
        current_body = eq_body;
    }

    // Wrap the assembled body in lambdas for each parameter.
    const final_expr = current_body;
    var lam_idx: usize = num_args;
    while (lam_idx > 0) {
        lam_idx -= 1;
        const p_body = try ctx.alloc.create(ast_mod.Expr);
        p_body.* = final_expr.*;
        final_expr.* = .{ .Lam = .{
            .binder = binders[lam_idx],
            .body = p_body,
            .span = syntheticSpan(),
        } };
    }

    return final_expr;
}

/// Apply a single pattern to a scrutinee, wrapping `success` in the appropriate
/// Core construct, falling through to `failure` on mismatch.
///
/// `scrut_id` is the Id used as the case binder (the scrutinee variable).
/// `depth` and `arg_idx` are used only for fresh-binder name generation.
fn applyPat(
    ctx: *DesugarCtx,
    scrut_expr: *ast_mod.Expr,
    scrut_id: ast_mod.Id,
    scrut_ty: ast_mod.CoreType,
    pat: renamer_mod.RPat,
    success: *ast_mod.Expr,
    failure: *ast_mod.Expr,
    arg_idx: usize,
    depth: usize,
) !*ast_mod.Expr {
    // Unwrap parentheses transparently.
    if (pat == .Paren) {
        return applyPat(ctx, scrut_expr, scrut_id, scrut_ty, pat.Paren.*, success, failure, arg_idx, depth);
    }

    return switch (pat) {
        // ── Variable pattern ───────────────────────────────────────────────
        // Always succeeds; bind the scrutinee to the variable name.
        .Var => |v| blk: {
            const inner = success;
            const result = try ctx.alloc.create(ast_mod.Expr);
            const var_id = ast_mod.Id{ .name = v.name, .ty = scrut_ty, .span = v.span };
            result.* = .{ .Let = .{
                .bind = .{ .NonRec = .{ .binder = var_id, .rhs = scrut_expr } },
                .body = inner,
                .span = syntheticSpan(),
            } };
            break :blk result;
        },

        // ── Wildcard pattern ──────────────────────────────────────────────
        // Always succeeds; no binding needed.
        .Wild => success,

        // ── Literal pattern ───────────────────────────────────────────────
        .Lit => |l| blk: {
            const alt = ast_mod.Alt{
                .con = .{ .LitAlt = desugarLiteral(l) },
                .binders = &.{},
                .body = success,
            };
            const default_alt = ast_mod.Alt{
                .con = .Default,
                .binders = &.{},
                .body = failure,
            };
            const result = try ctx.alloc.create(ast_mod.Expr);
            result.* = .{ .Case = .{
                .scrutinee = scrut_expr,
                .binder = scrut_id,
                .ty = scrut_ty,
                .alts = try ctx.alloc.dupe(ast_mod.Alt, &.{ alt, default_alt }),
                .span = syntheticSpan(),
            } };
            break :blk result;
        },

        // ── Constructor pattern ───────────────────────────────────────────
        //
        // For each constructor argument:
        //   • If it is a Var: use the variable name directly as the field binder.
        //   • If it is a Wild: mint a fresh `_field_` binder.
        //   • Otherwise (nested pattern): mint a fresh `field_` binder, then
        //     wrap `success` in an inner applyPat for the sub-pattern.
        //
        // This implements the constructor rule from SLPJ Ch.5.
        .Con => |c| blk: {
            var inner_success = success;

            // Allocate binders for all constructor arguments.
            var con_binders = try ctx.alloc.alloc(ast_mod.Id, c.args.len);

            // Process args in *reverse* order so that nested inner cases
            // wrap the body correctly (innermost last, outermost first).
            var field_i: usize = c.args.len;
            while (field_i > 0) {
                field_i -= 1;
                var sub_pat = c.args[field_i];
                while (sub_pat == .Paren) sub_pat = sub_pat.Paren.*;

                const field_binder = try freshFieldBinder(ctx.alloc, ctx.u_supply, arg_idx, depth, field_i);

                // The binder always captures the field value, regardless of whether
                // the sub-pattern matches.
                con_binders[field_i] = field_binder;

                switch (sub_pat) {
                    // Variable: rename the binder to the variable name directly.
                    .Var => |v| {
                        // Get the type from local_binders if available; fall back to a dummy.
                        const p_ty: ast_mod.CoreType = if (ctx.types.local_binders.get(v.name.unique)) |ty_ptr|
                            try htypeToCore(ctx.alloc, ty_ptr)
                        else
                            dummyCoreType();
                        con_binders[field_i] = .{
                            .name = v.name,
                            .ty = p_ty,
                            .span = v.span,
                        };
                    },
                    // Wildcard: leave the fresh dummy binder.
                    .Wild => {},
                    // Nested pattern: keep the fresh binder, then recursively match.
                    else => {
                        // The fresh binder's type is unknown without full type propagation.
                        // We look up from local_binders; if not found use a dummy.
                        const field_scrut = try ctx.alloc.create(ast_mod.Expr);
                        field_scrut.* = .{ .Var = field_binder };
                        inner_success = try applyPat(
                            ctx,
                            field_scrut,
                            field_binder,
                            field_binder.ty,
                            sub_pat,
                            inner_success,
                            failure,
                            arg_idx,
                            depth + 1,
                        );
                    },
                }
            }

            const alt = ast_mod.Alt{
                .con = .{ .DataAlt = c.name },
                .binders = con_binders,
                .body = inner_success,
            };
            const default_alt = ast_mod.Alt{
                .con = .Default,
                .binders = &.{},
                .body = failure,
            };
            const result = try ctx.alloc.create(ast_mod.Expr);
            result.* = .{ .Case = .{
                .scrutinee = scrut_expr,
                .binder = scrut_id,
                .ty = scrut_ty,
                .alts = try ctx.alloc.dupe(ast_mod.Alt, &.{ alt, default_alt }),
                .span = syntheticSpan(),
            } };
            break :blk result;
        },

        // ── As-pattern (@) ────────────────────────────────────────────────
        //
        // `xs@pat` binds the scrutinee to `xs` and also matches `pat`.
        // Desugar as: let xs = scrut in applyPat(scrut, pat, success, failure)
        .AsPat => |as_| blk: {
            const inner = try applyPat(ctx, scrut_expr, scrut_id, scrut_ty, as_.pat.*, success, failure, arg_idx, depth);
            const result = try ctx.alloc.create(ast_mod.Expr);
            const var_id = ast_mod.Id{ .name = as_.name, .ty = scrut_ty, .span = as_.span };
            result.* = .{ .Let = .{
                .bind = .{ .NonRec = .{ .binder = var_id, .rhs = scrut_expr } },
                .body = inner,
                .span = syntheticSpan(),
            } };
            break :blk result;
        },

        // ── Tuple pattern ─────────────────────────────────────────────────
        //
        // `(a, b)` matches a tuple constructor `(,)` with two fields.
        // We treat it identically to a constructor pattern.
        .Tuple => |elems| blk: {
            var inner_success = success;
            var con_binders = try ctx.alloc.alloc(ast_mod.Id, elems.len);

            var field_i: usize = elems.len;
            while (field_i > 0) {
                field_i -= 1;
                var sub_pat = elems[field_i];
                while (sub_pat == .Paren) sub_pat = sub_pat.Paren.*;

                const field_binder = try freshFieldBinder(ctx.alloc, ctx.u_supply, arg_idx, depth, field_i);
                con_binders[field_i] = field_binder;

                switch (sub_pat) {
                    .Var => |v| {
                        const p_ty: ast_mod.CoreType = if (ctx.types.local_binders.get(v.name.unique)) |ty_ptr|
                            try htypeToCore(ctx.alloc, ty_ptr)
                        else
                            dummyCoreType();
                        con_binders[field_i] = .{ .name = v.name, .ty = p_ty, .span = v.span };
                    },
                    .Wild => {},
                    else => {
                        const field_scrut = try ctx.alloc.create(ast_mod.Expr);
                        field_scrut.* = .{ .Var = field_binder };
                        inner_success = try applyPat(
                            ctx,
                            field_scrut,
                            field_binder,
                            field_binder.ty,
                            sub_pat,
                            inner_success,
                            failure,
                            arg_idx,
                            depth + 1,
                        );
                    },
                }
            }

            // Build the tuple constructor name: "(,)" for 2-tuples, "(,,)" for 3, etc.
            const tuple_con_name = try buildTupleConName(ctx.alloc, elems.len);
            const alt = ast_mod.Alt{
                .con = .{ .DataAlt = .{ .base = tuple_con_name, .unique = .{ .value = 0 } } },
                .binders = con_binders,
                .body = inner_success,
            };
            const default_alt = ast_mod.Alt{ .con = .Default, .binders = &.{}, .body = failure };
            const result = try ctx.alloc.create(ast_mod.Expr);
            result.* = .{ .Case = .{
                .scrutinee = scrut_expr,
                .binder = scrut_id,
                .ty = scrut_ty,
                .alts = try ctx.alloc.dupe(ast_mod.Alt, &.{ alt, default_alt }),
                .span = syntheticSpan(),
            } };
            break :blk result;
        },

        // ── Infix constructor pattern ──────────────────────────────────────
        //
        // `x:xs` — treated as `Con (:) [x, xs]`.
        .InfixCon => |inf| blk: {
            const synthetic_con = renamer_mod.RPat{ .Con = .{
                .name = inf.con,
                .con_span = inf.con_span,
                .args = try ctx.alloc.dupe(renamer_mod.RPat, &.{ inf.left.*, inf.right.* }),
            } };
            break :blk try applyPat(ctx, scrut_expr, scrut_id, scrut_ty, synthetic_con, success, failure, arg_idx, depth);
        },

        // ── Negated literal ───────────────────────────────────────────────
        //
        // `-n` is the same as matching on the literal `-n`.
        .Negate => |inner_pat| blk: {
            // `Negate` wraps a literal pattern.  We synthesize a negative literal.
            switch (inner_pat.*) {
                .Lit => |l| {
                    const neg_lit: ast_mod.Literal = switch (l) {
                        .Int => |i| .{ .Int = -i.value },
                        .Float => |f| .{ .Float = -f.value },
                        else => {
                            std.debug.panic("Negate pattern applied to non-numeric literal: {}", .{l});
                        },
                    };
                    const alt = ast_mod.Alt{
                        .con = .{ .LitAlt = neg_lit },
                        .binders = &.{},
                        .body = success,
                    };
                    const default_alt = ast_mod.Alt{ .con = .Default, .binders = &.{}, .body = failure };
                    const result = try ctx.alloc.create(ast_mod.Expr);
                    result.* = .{ .Case = .{
                        .scrutinee = scrut_expr,
                        .binder = scrut_id,
                        .ty = scrut_ty,
                        .alts = try ctx.alloc.dupe(ast_mod.Alt, &.{ alt, default_alt }),
                        .span = syntheticSpan(),
                    } };
                    break :blk result;
                },
                else => {
                    std.debug.panic("Negate pattern applied to non-literal sub-pattern: {}", .{inner_pat.*});
                },
            }
        },

        // ── Paren (transparent) ───────────────────────────────────────────
        // Already unwrapped at the call sites; handle here for completeness.
        .Paren => |inner| try applyPat(ctx, scrut_expr, scrut_id, scrut_ty, inner.*, success, failure, arg_idx, depth),

        // ── Not yet implemented ───────────────────────────────────────────
        //
        // IMPORTANT: Each unsupported case MUST have a tracking issue.
        .List => {
            // tracked in: https://github.com/adinapoli/rusholme/issues/418
            std.debug.panic("List patterns not yet supported in match compiler: {}", .{pat});
        },
        .RecPat => {
            // Record pattern desugaring requires the record type to be fully
            // in scope; tracked as part of the record support work.
            // tracked in: https://github.com/adinapoli/rusholme/issues/418
            std.debug.panic("Record patterns not yet supported in match compiler: {}", .{pat});
        },
    };
}

/// Allocate a fresh `Id` for a constructor field binder.
/// Create a fresh binder for a constructor field in a pattern match.
///
/// Each binder gets a fresh unique from `u_supply` so that the downstream
/// passes can distinguish field binders that share a base name pattern.
fn freshFieldBinder(
    alloc: std.mem.Allocator,
    u_supply: *naming_mod.UniqueSupply,
    arg_idx: usize,
    depth: usize,
    field_i: usize,
) !ast_mod.Id {
    const name = try std.fmt.allocPrint(alloc, "_field_{d}_{d}_{d}", .{ arg_idx, depth, field_i });
    return .{
        .name = .{ .base = name, .unique = u_supply.fresh() },
        .ty = dummyCoreType(),
        .span = syntheticSpan(),
    };
}

/// A placeholder CoreType used for fresh binders whose precise type we do not
/// track through the pattern match compiler (no full type propagation yet).
fn dummyCoreType() ast_mod.CoreType {
    return .{ .TyVar = .{ .base = "_t", .unique = .{ .value = 0 } } };
}

/// Build the tuple constructor name for a tuple of `arity` elements.
///   arity=2 → "(,)"
///   arity=3 → "(,,)"
fn buildTupleConName(alloc: std.mem.Allocator, arity: usize) ![]const u8 {
    if (arity < 2) return error.OutOfMemory; // degenerate — shouldn't occur
    var buf = try alloc.alloc(u8, arity + 1); // '(' + (arity-1) commas + ')'
    buf[0] = '(';
    for (1..arity) |i| buf[i] = ',';
    buf[arity] = ')';
    return buf;
}

// ── Literal conversions ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "desugarMatch: Tier 1 literal and wildcard" {
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

    var u_supply = naming_mod.UniqueSupply{};
    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = &types,
        .diags = &diags,
        .u_supply = &u_supply,
    };

    // f 0 = "zero"
    // f _ = "many"
    // Type: Int -> String
    const int_ty_name = renamer_mod.Name{ .base = "Int", .unique = .{ .value = 1 } };
    const str_ty_name = renamer_mod.Name{ .base = "String", .unique = .{ .value = 2 } };
    const int_ty = ast_mod.CoreType{ .TyCon = .{ .name = int_ty_name, .args = &.{} } };
    const str_ty = ast_mod.CoreType{ .TyCon = .{ .name = str_ty_name, .args = &.{} } };

    const arg_ty_ptr = try alloc.create(ast_mod.CoreType);
    arg_ty_ptr.* = int_ty;
    const res_ty_ptr = try alloc.create(ast_mod.CoreType);
    res_ty_ptr.* = str_ty;

    const fun_ty = ast_mod.CoreType{ .FunTy = .{ .arg = arg_ty_ptr, .res = res_ty_ptr } };

    // Fake LHS patterns:
    const pat1 = renamer_mod.RPat{ .Lit = .{ .Int = .{ .value = 0, .span = syntheticSpan() } } };
    const pat2 = renamer_mod.RPat{ .Wild = syntheticSpan() };

    // Fake RHS expressions:
    const rhs1 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .String = .{ .value = "zero", .span = syntheticSpan() } } } };
    const rhs2 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .String = .{ .value = "many", .span = syntheticSpan() } } } };

    // Equations
    const eq1 = renamer_mod.RMatch{
        .patterns = try alloc.dupe(renamer_mod.RPat, &.{pat1}),
        .rhs = rhs1,
        .span = syntheticSpan(),
    };
    const eq2 = renamer_mod.RMatch{
        .patterns = try alloc.dupe(renamer_mod.RPat, &.{pat2}),
        .rhs = rhs2,
        .span = syntheticSpan(),
    };

    const expr = try desugarMatch(&ctx, &.{ eq1, eq2 }, fun_ty);

    // It should be a Lam (Case ... -> "zero" ; _ -> "many")
    try testing.expect(expr.* == .Lam);
    try testing.expectEqualStrings("arg_0", expr.Lam.binder.name.base);

    const body = expr.Lam.body.*;
    try testing.expect(body == .Case);
    try testing.expectEqual(@as(usize, 2), body.Case.alts.len);

    const alt1 = body.Case.alts[0];
    try testing.expect(alt1.con == .LitAlt);
    try testing.expectEqual(@as(i64, 0), alt1.con.LitAlt.Int);

    const alt2 = body.Case.alts[1];
    try testing.expect(alt2.con == .Default);
    // The default body should be the eq2 translation (which has wildcard so just the string)
    // Wait, wildcard doesn't emit case, just passes eq_body
    try testing.expect(alt2.body.* == .Lit);
    try testing.expectEqualStrings("many", alt2.body.Lit.val.String);
}

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

    var u_supply = naming_mod.UniqueSupply{};
    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = &types,
        .diags = &diags,
        .u_supply = &u_supply,
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

test "desugarExpr: List desugars to Cons/Nil chain" {
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

    // Build (:) scheme: forall a. a -> [a] -> [a]
    {
        const a_id: u64 = 10000;
        const a_name = Name{ .base = "a", .unique = .{ .value = a_id } };
        const a_rigid = htype_mod.HType{ .Rigid = a_name };
        const list_a_args = try alloc.dupe(htype_mod.HType, &.{a_rigid});
        const list_a = htype_mod.HType{ .Con = .{ .name = Known.Type.List, .args = list_a_args } };

        const a_ptr = try alloc.create(htype_mod.HType);
        a_ptr.* = a_rigid;
        const list_a_ptr = try alloc.create(htype_mod.HType);
        list_a_ptr.* = list_a;
        const list_a_ptr2 = try alloc.create(htype_mod.HType);
        list_a_ptr2.* = list_a;

        // [a] -> [a]
        const inner_fun_ptr = try alloc.create(htype_mod.HType);
        inner_fun_ptr.* = .{ .Fun = .{ .arg = list_a_ptr, .res = list_a_ptr2 } };
        // a -> [a] -> [a]
        const cons_body = htype_mod.HType{ .Fun = .{ .arg = a_ptr, .res = inner_fun_ptr } };

        const binders = try alloc.dupe(u64, &.{a_id});
        try types.schemes.put(alloc, Known.Con.Cons.unique, .{ .binders = binders, .constraints = &.{}, .body = cons_body });
    }

    // Build [] scheme: forall a. [a]
    {
        const a_id: u64 = 10001;
        const a_name = Name{ .base = "a", .unique = .{ .value = a_id } };
        const a_rigid = htype_mod.HType{ .Rigid = a_name };
        const list_a_args = try alloc.dupe(htype_mod.HType, &.{a_rigid});
        const nil_body = htype_mod.HType{ .Con = .{ .name = Known.Type.List, .args = list_a_args } };

        const binders = try alloc.dupe(u64, &.{a_id});
        try types.schemes.put(alloc, Known.Con.Nil.unique, .{ .binders = binders, .constraints = &.{}, .body = nil_body });
    }

    var u_supply = naming_mod.UniqueSupply{};
    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = &types,
        .diags = &diags,
        .u_supply = &u_supply,
    };

    // Test empty list: [] desugars to Var(Nil)
    {
        const empty_list = renamer_mod.RExpr{ .List = &.{} };
        const result = try desugarExpr(&ctx, empty_list);
        try testing.expect(result.* == .Var);
        try testing.expectEqualStrings("[]", result.Var.name.base);
        try testing.expectEqual(@as(u64, 207), result.Var.name.unique.value);
    }

    // Test [1, 2]: desugars to (:) 1 ((:) 2 [])
    {
        const elems = try alloc.dupe(renamer_mod.RExpr, &.{
            .{ .Lit = .{ .Int = .{ .value = 1, .span = syntheticSpan() } } },
            .{ .Lit = .{ .Int = .{ .value = 2, .span = syntheticSpan() } } },
        });
        const list_expr = renamer_mod.RExpr{ .List = elems };
        const result = try desugarExpr(&ctx, list_expr);

        // Outermost: App(App(Cons, 1), ...)
        try testing.expect(result.* == .App);
        const outer_app = result.App;

        // outer_app.fn_expr = App(Cons, 1)
        try testing.expect(outer_app.fn_expr.* == .App);
        const cons_app1 = outer_app.fn_expr.App;
        try testing.expect(cons_app1.fn_expr.* == .Var);
        try testing.expectEqualStrings("(:)", cons_app1.fn_expr.Var.name.base);
        try testing.expect(cons_app1.arg.* == .Lit);
        try testing.expectEqual(@as(i64, 1), cons_app1.arg.Lit.val.Int);

        // outer_app.arg = App(App(Cons, 2), Nil)
        try testing.expect(outer_app.arg.* == .App);
        const inner_app = outer_app.arg.App;

        // inner_app.fn_expr = App(Cons, 2)
        try testing.expect(inner_app.fn_expr.* == .App);
        const cons_app2 = inner_app.fn_expr.App;
        try testing.expect(cons_app2.fn_expr.* == .Var);
        try testing.expectEqualStrings("(:)", cons_app2.fn_expr.Var.name.base);
        try testing.expect(cons_app2.arg.* == .Lit);
        try testing.expectEqual(@as(i64, 2), cons_app2.arg.Lit.val.Int);

        // inner_app.arg = Nil
        try testing.expect(inner_app.arg.* == .Var);
        try testing.expectEqualStrings("[]", inner_app.arg.Var.name.base);
    }
}

test "desugarExpr: Paren unwraps inner expression" {
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

    // Add a local binder for x
    const int_h_ty = try alloc.create(htype_mod.HType);
    int_h_ty.* = .{ .Con = .{ .name = testName("Int", 0), .args = &.{} } };
    const x_name = testName("x", 42);
    try types.local_binders.put(alloc, x_name.unique, int_h_ty);

    var u_supply = naming_mod.UniqueSupply{};
    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = &types,
        .diags = &diags,
        .u_supply = &u_supply,
    };

    const inner = try alloc.create(renamer_mod.RExpr);
    inner.* = .{ .Var = .{ .name = x_name, .span = syntheticSpan() } };

    const paren_expr = renamer_mod.RExpr{ .Paren = inner };
    const result = try desugarExpr(&ctx, paren_expr);

    try testing.expect(result.* == .Var);
    try testing.expectEqualStrings("x", result.Var.name.base);
}

// ── Tier 2 pattern match tests ──────────────────────────────────────────────

/// Helper: build a DesugarCtx backed by an ArenaAllocator for pattern tests.
fn makeCtx(alloc: std.mem.Allocator, types: *infer_mod.ModuleTypes, diags: *DiagnosticCollector, u_supply: *naming_mod.UniqueSupply) DesugarCtx {
    return .{ .alloc = alloc, .types = types, .diags = diags, .u_supply = u_supply };
}

/// Helper: build a simple `Con_name -> T` function type for single-arg functions.
fn singleArgFunTy(alloc: std.mem.Allocator, arg_ty: ast_mod.CoreType, res_ty: ast_mod.CoreType) !ast_mod.CoreType {
    const arg_ptr = try alloc.create(ast_mod.CoreType);
    arg_ptr.* = arg_ty;
    const res_ptr = try alloc.create(ast_mod.CoreType);
    res_ptr.* = res_ty;
    return .{ .FunTy = .{ .arg = arg_ptr, .res = res_ptr } };
}

test "desugarMatch: Tier 2 constructor pattern with Var sub-pattern" {
    // f (Just x) = x
    // f Nothing  = 0
    // Type: Maybe Int -> Int  (simplified: TyCon "Maybe" -> TyCon "Int")
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{} };
    defer types.deinit(alloc);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var u_supply = naming_mod.UniqueSupply{};
    var ctx = makeCtx(alloc, &types, &diags, &u_supply);

    const maybe_ty_name = testName("Maybe", 10);
    const int_ty_name = testName("Int", 1);
    const maybe_ty = ast_mod.CoreType{ .TyCon = .{ .name = maybe_ty_name, .args = &.{} } };
    const int_ty = ast_mod.CoreType{ .TyCon = .{ .name = int_ty_name, .args = &.{} } };
    const fun_ty = try singleArgFunTy(alloc, maybe_ty, int_ty);

    // Patterns
    const x_name = testName("x", 99);
    const x_pat = renamer_mod.RPat{ .Var = .{ .name = x_name, .span = syntheticSpan() } };
    const just_pat = renamer_mod.RPat{ .Con = .{
        .name = testName("Just", 50),
        .con_span = syntheticSpan(),
        .args = try alloc.dupe(renamer_mod.RPat, &.{x_pat}),
    } };
    const nothing_pat = renamer_mod.RPat{ .Con = .{
        .name = testName("Nothing", 51),
        .con_span = syntheticSpan(),
        .args = &.{},
    } };

    const rhs1 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 42, .span = syntheticSpan() } } } };
    const rhs2 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 0, .span = syntheticSpan() } } } };

    const eq1 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{just_pat}), .rhs = rhs1, .span = syntheticSpan() };
    const eq2 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{nothing_pat}), .rhs = rhs2, .span = syntheticSpan() };

    const expr = try desugarMatch(&ctx, &.{ eq1, eq2 }, fun_ty);

    // \arg_0 -> case arg_0 { Just x -> 42 ; _ -> case arg_0 { Nothing -> 0 ; _ -> <fallback> } }
    try testing.expect(expr.* == .Lam);
    const body = expr.Lam.body.*;
    try testing.expect(body == .Case);
    try testing.expectEqual(@as(usize, 2), body.Case.alts.len);

    // First alt: Just x -> 42
    const just_alt = body.Case.alts[0];
    try testing.expect(just_alt.con == .DataAlt);
    try testing.expectEqualStrings("Just", just_alt.con.DataAlt.base);
    // The Just constructor has 1 binder; because sub-pat is Var the binder name = "x".
    try testing.expectEqual(@as(usize, 1), just_alt.binders.len);
    try testing.expectEqualStrings("x", just_alt.binders[0].name.base);

    // Default branch leads to the Nothing case
    const default_alt = body.Case.alts[1];
    try testing.expect(default_alt.con == .Default);
    try testing.expect(default_alt.body.* == .Case);
    const nothing_case = default_alt.body.*;
    try testing.expectEqual(@as(usize, 2), nothing_case.Case.alts.len);
    try testing.expect(nothing_case.Case.alts[0].con == .DataAlt);
    try testing.expectEqualStrings("Nothing", nothing_case.Case.alts[0].con.DataAlt.base);
}

test "desugarMatch: Tier 2 as-pattern" {
    // f xs@(Just _) = 1
    // f Nothing     = 0
    // Type: Maybe Int -> Int  (RHS uses Lit to avoid Var type-lookup overhead)
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{} };
    defer types.deinit(alloc);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var u_supply = naming_mod.UniqueSupply{};
    var ctx = makeCtx(alloc, &types, &diags, &u_supply);

    const maybe_ty_name = testName("Maybe", 10);
    const int_ty_name = testName("Int", 1);
    const maybe_ty = ast_mod.CoreType{ .TyCon = .{ .name = maybe_ty_name, .args = &.{} } };
    const int_ty = ast_mod.CoreType{ .TyCon = .{ .name = int_ty_name, .args = &.{} } };
    const fun_ty = try singleArgFunTy(alloc, maybe_ty, int_ty);

    // xs@(Just _)
    const wild_ptr = try alloc.create(renamer_mod.RPat);
    wild_ptr.* = .{ .Wild = syntheticSpan() };
    const just_con_ptr = try alloc.create(renamer_mod.RPat);
    just_con_ptr.* = .{ .Con = .{
        .name = testName("Just", 50),
        .con_span = syntheticSpan(),
        .args = try alloc.dupe(renamer_mod.RPat, &.{wild_ptr.*}),
    } };
    const as_pat = renamer_mod.RPat{ .AsPat = .{
        .name = testName("xs", 77),
        .pat = just_con_ptr,
        .span = syntheticSpan(),
    } };
    const nothing_pat = renamer_mod.RPat{ .Con = .{
        .name = testName("Nothing", 51),
        .con_span = syntheticSpan(),
        .args = &.{},
    } };

    const rhs1 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 1, .span = syntheticSpan() } } } };
    const rhs2 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 0, .span = syntheticSpan() } } } };

    const eq1 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{as_pat}), .rhs = rhs1, .span = syntheticSpan() };
    const eq2 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{nothing_pat}), .rhs = rhs2, .span = syntheticSpan() };

    const expr = try desugarMatch(&ctx, &.{ eq1, eq2 }, fun_ty);

    // \arg_0 -> let xs = arg_0 in case arg_0 { Just _ -> 1 ; _ -> ... }
    try testing.expect(expr.* == .Lam);

    // The as-pattern wraps the inner match in a let-binding first.
    const body = expr.Lam.body.*;
    try testing.expect(body == .Let);
    try testing.expect(body.Let.bind == .NonRec);
    try testing.expectEqualStrings("xs", body.Let.bind.NonRec.binder.name.base);

    // Inside the let: a Case on arg_0 with Just -> 1 ; _ -> ...
    const inner = body.Let.body.*;
    try testing.expect(inner == .Case);
    try testing.expectEqual(@as(usize, 2), inner.Case.alts.len);
    try testing.expect(inner.Case.alts[0].con == .DataAlt);
    try testing.expectEqualStrings("Just", inner.Case.alts[0].con.DataAlt.base);
}

test "desugarMatch: Tier 2 tuple pattern" {
    // f (a, _) = 99   -- RHS uses Lit to avoid Var type-lookup overhead
    // Type: (Int, Int) -> Int
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{} };
    defer types.deinit(alloc);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var u_supply = naming_mod.UniqueSupply{};
    var ctx = makeCtx(alloc, &types, &diags, &u_supply);

    const int_ty_name = testName("Int", 1);
    const int_ty = ast_mod.CoreType{ .TyCon = .{ .name = int_ty_name, .args = &.{} } };
    const tuple_ty_name = testName("(,)", 20);
    const tuple_ty = ast_mod.CoreType{ .TyCon = .{ .name = tuple_ty_name, .args = &.{} } };
    const fun_ty = try singleArgFunTy(alloc, tuple_ty, int_ty);

    // (a, _)
    const a_name = testName("a", 88);
    const a_pat = renamer_mod.RPat{ .Var = .{ .name = a_name, .span = syntheticSpan() } };
    const wild_pat = renamer_mod.RPat{ .Wild = syntheticSpan() };
    const tuple_pat = renamer_mod.RPat{ .Tuple = try alloc.dupe(renamer_mod.RPat, &.{ a_pat, wild_pat }) };

    const rhs1 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 99, .span = syntheticSpan() } } } };
    const eq1 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{tuple_pat}), .rhs = rhs1, .span = syntheticSpan() };

    const expr = try desugarMatch(&ctx, &.{eq1}, fun_ty);

    // \arg_0 -> case arg_0 { (,) a _ -> 99 ; _ -> <fallback> }
    try testing.expect(expr.* == .Lam);
    const body = expr.Lam.body.*;
    try testing.expect(body == .Case);
    try testing.expectEqual(@as(usize, 2), body.Case.alts.len);

    const tuple_alt = body.Case.alts[0];
    try testing.expect(tuple_alt.con == .DataAlt);
    try testing.expectEqualStrings("(,)", tuple_alt.con.DataAlt.base);
    // 2 binders: first = "a" (from Var), second = fresh wildcard binder
    try testing.expectEqual(@as(usize, 2), tuple_alt.binders.len);
    try testing.expectEqualStrings("a", tuple_alt.binders[0].name.base);
}
