//! Core to GRIN Translation.
//!
//! Transforms Core IR (System F_C) to GRIN IR (imperative monadic language).
//! This is issue #314: Core to GRIN translation for simple expressions.
//!
//! Translation strategy (see docs/decisions/042-core-to-grin-translation.md):
//! - Top-level bindings → GRIN Defs
//! - Literals → Expr.Return with Val.Lit
//! - Constructor application → Expr.Store with Val.ConstTagNode (C-tagged)
//! - Let bindings (NonRec) → Expr.Store (F-tagged thunk) + Expr.Bind
//! - Let bindings (Rec) → store placeholders + backpatch via Expr.Update
//! - Case expressions → fetch + eval + Expr.Case
//! - Fully-applied function calls → Expr.App
//! - Type/Coercion erasure — dropped
//!
//! This is a simple translation without partial application handling (#317)
//! or eval/apply generation (#315).

const std = @import("std");
const core = @import("../core/ast.zig");
const grin = @import("ast.zig");

const CoreExpr = core.Expr;
const CoreBind = core.Bind;
const CoreBindPair = core.BindPair;
const CoreLiteral = core.Literal;
const CoreProgram = core.CoreProgram;
const CoreType = core.CoreType;
const CoreId = core.Id;
const CoreAlt = core.Alt;
const CoreAltCon = core.AltCon;

// Type aliases for union payloads that are referenced in parameter types
const CoreLet = struct { bind: core.Bind, body: *const core.Expr, span: core.SourceSpan };
const CoreCase = struct { scrutinee: *const core.Expr, binder: core.Id, ty: core.CoreType, alts: []const core.Alt, span: core.SourceSpan };

const GrinExpr = grin.Expr;
const GrinVal = grin.Val;
const GrinTag = grin.Tag;
const GrinTagType = grin.TagType;
const GrinLiteral = grin.Literal;
const GrinProgram = grin.Program;
const GrinDef = grin.Def;
const GrinCPat = grin.CPat;
const GrinAlt = grin.Alt;
const GrinName = grin.Name;

// ── Translation Context ─────────────────────────────────────────────────

/// Context for the Core to GRIN translation.
const TranslateCtx = struct {
    alloc: std.mem.Allocator,
    // Maps Core binders to their GRIN variable names.
    var_map: std.AutoHashMapUnmanaged(u64, GrinName),
    // Counter for generating fresh GRIN variable names.
    name_counter: u64 = 0,

    pub fn init(alloc: std.mem.Allocator) TranslateCtx {
        return .{
            .alloc = alloc,
            .var_map = .{},
        };
    }

    pub fn deinit(self: *TranslateCtx) void {
        self.var_map.deinit(self.alloc);
    }

    /// Generate a fresh GRIN variable name.
    fn freshName(self: *TranslateCtx, base: []const u8) !GrinName {
        const name = GrinName{
            .base = base,
            .unique = .{ .value = self.name_counter },
        };
        self.name_counter += 1;
        return name;
    }

    /// Map a Core binder to a GRIN variable name.
    fn mapBinder(self: *TranslateCtx, core_id: *const CoreId) !GrinName {
        const unique_id = core_id.name.unique.value;
        if (self.var_map.get(unique_id)) |name| {
            return name;
        }
        // Not mapped yet, create a fresh variable with the same base name.
        const fresh = try self.freshName(core_id.name.base);
        try self.var_map.put(self.alloc, unique_id, fresh);
        return fresh;
    }

    /// Get or create a GRIN variable name for a Core ID.
    fn getCoreVar(self: *TranslateCtx, core_name: grin.Name) !GrinName {
        const unique_id = core_name.unique.value;
        if (self.var_map.get(unique_id)) |name| {
            return name;
        }
        const fresh = try self.freshName(core_name.base);
        try self.var_map.put(self.alloc, unique_id, fresh);
        return fresh;
    }
};

// ── Translation Functions ───────────────────────────────────────────────

/// Translate a Core program to a GRIN program.
pub fn translateProgram(alloc: std.mem.Allocator, core_prog: CoreProgram) !GrinProgram {
    var ctx = TranslateCtx.init(alloc);
    defer ctx.deinit();

    var defs = std.ArrayListUnmanaged(GrinDef){};
    defer defs.deinit(alloc);

    // Process each top-level binding into a GRIN Def.
    for (core_prog.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                const grinning = try translateDef(&ctx, pair);
                try defs.append(alloc, grinning);
            },
            .Rec => |pairs| {
                // Handle mutually recursive bindings.
                // First, create placeholder variables for all binders.
                var placeholders = try alloc.alloc(GrinName, pairs.len);
                defer alloc.free(placeholders);
                for (pairs, 0..) |pair, i| {
                    placeholders[i] = try ctx.mapBinder(&pair.binder);
                }

                // Then translate each RHS.
                for (pairs) |pair| {
                    const grinning = try translateDef(&ctx, pair);
                    try defs.append(alloc, grinning);
                }
            },
        }
    }

    const defs_slice = try defs.toOwnedSlice(alloc);
    return GrinProgram{ .defs = defs_slice };
}

/// Translate a single Core binding to a GRIN definition.
fn translateDef(ctx: *TranslateCtx, pair: CoreBindPair) !GrinDef {
    const name = try ctx.mapBinder(&pair.binder);
    var params = std.ArrayListUnmanaged(GrinName){};
    defer params.deinit(ctx.alloc);

    // Collect all lambda parameters from the binding chain.
    var body_expr: *const CoreExpr = pair.rhs;
    while (true) {
        switch (body_expr.*) {
            .Lam => |lam| {
                const param_name = try ctx.mapBinder(&lam.binder);
                try params.append(ctx.alloc, param_name);
                body_expr = lam.body;
            },
            else => break,
        }
    }

    // Translate the body.
    const body = try translateExpr(ctx, body_expr);

    const params_slice = try params.toOwnedSlice(ctx.alloc);
    return GrinDef{
        .name = name,
        .params = params_slice,
        .body = body,
    };
}

/// Translate a Core expression to a GRIN expression.
fn translateExpr(ctx: *TranslateCtx, expr: *const CoreExpr) !*GrinExpr {
    const new_expr = try ctx.alloc.create(GrinExpr);

    switch (expr.*) {
        .Var => |v| {
            // Variable reference becomes a variable value.
            const grin_name = try ctx.getCoreVar(v.name);
            new_expr.* = .{ .Return = .{ .Var = grin_name } };
        },
        .Lit => |l| {
            // Literal becomes a return with literal value.
            const grin_lit = translateLiteral(l.val);
            new_expr.* = .{ .Return = .{ .Lit = grin_lit } };
        },
        .App => {
            // Function application.
            // For now, assume we can collect the function name and all arguments.
            // Partial application handling is deferred to #317.
            const result = try translateApp(ctx, expr);
            new_expr.* = result.*;
        },
        .Lam => {
            // Lambda should have been collected by translateDef.
            // As a fallback, translate the body directly.
            std.debug.panic("Unexpected lambda in translateExpr (should be collected by translateDef)", .{});
        },
        .Let => {
            // Pass the expression pointer and extract Let data inside
            const let_data: *const CoreLet = @ptrCast(expr);
            const result = try translateLet(ctx, let_data);
            new_expr.* = result.*;
        },
        .Case => {
            // Pass the expression pointer and extract Case data inside
            const case_data: *const CoreCase = @ptrCast(expr);
            const result = try translateCase(ctx, case_data);
            new_expr.* = result.*;
        },
        .Type => {
            // Type erasure: type applications have no runtime representation.
            // This should not happen in valid Core (it's a function arg).
            // Just return unit as a placeholder.
            new_expr.* = .{ .Return = .{ .Unit = {} } };
        },
        .Coercion => {
            // Coercion erasure: all coercions are Refl (identity).
            new_expr.* = .{ .Return = .{ .Unit = {} } };
        },
    }

    return new_expr;
}

/// Translate a function application.
fn translateApp(ctx: *TranslateCtx, app_expr: *const CoreExpr) anyerror!*GrinExpr {
    // Verify this is an App expression
    switch (app_expr.*) {
        .App => {},
        else => std.debug.panic("translateApp called with non-App expression", .{}),
    }

    // Collect the function and all arguments from the application chain.
    // Core App is left-associative: f x y = ((f x) y)
    // We walk left collecting arguments, then reverse them.
    var args = std.ArrayListUnmanaged(*const CoreExpr){};
    defer args.deinit(ctx.alloc);

    var current: *const CoreExpr = app_expr;
    while (true) {
        switch (current.*) {
            .App => |a| {
                try args.append(ctx.alloc, a.arg);
                current = a.fn_expr;
            },
            else => {
                // Reached the function head
                break;
            },
        }
    }

    // `current` is now the function expression (should be a Var)
    const fn_expr = current;

    // Translate the function name.
    const translated_fn = try translateExpr(ctx, fn_expr);

    // Reverse the arguments (we collected them right-to-left)
    std.mem.reverse(*const CoreExpr, args.items);

    // Translate all arguments.
    var grin_args = try ctx.alloc.alloc(GrinVal, args.items.len);
    for (args.items, 0..) |arg, i| {
        const arg_result = try translateExpr(ctx, arg);
        // The expression should return a value.
        switch (arg_result.*) {
            .Return => |v| {
                grin_args[i] = v;
            },
            else => {
                // Complex argument expression - need to bind and use.
                // For MVP, we'll just create a variable.
                const fresh_var = try ctx.freshName("arg");
                grin_args[i] = .{ .Var = fresh_var };
            },
        }
    }

    // Create an App expression.
    // Need to get the function name from the translated function.
    const fn_name = blk: {
        switch (translated_fn.*) {
            .Return => |v| {
                switch (v) {
                    .Var => |name| break :blk name,
                    else => {
                        std.debug.panic("Function expression is not a variable", .{});
                    },
                }
            },
            else => {
                std.debug.panic("Function expression is not a simple return", .{});
            },
        }
    };

    const grubin_app = try ctx.alloc.create(GrinExpr);
    grubin_app.* = .{ .App = .{
        .name = fn_name,
        .args = grin_args,
    }};

    return grubin_app;
}

/// Translate a let binding.
fn translateLet(ctx: *TranslateCtx, let_expr: *const CoreLet) anyerror!*GrinExpr {
    switch (let_expr.bind) {
        .NonRec => |pair| {
            // Non-recursive let: Lazy evaluation means we store a thunk.
            // let x = rhs in body
            // becomes: store (F<func> [<args>]) >>= \x -> body

            // Translate RHS into a thunk.
            // For MVP, we'll just translate and store it directly.
            // A full implementation would analyze strictness.
            const rhs_expr = try translateExpr(ctx, pair.rhs);

            // Store the thunk - we need to wrap in an F-tag for lazy evaluation,
            // but for MVP we'll store the value directly.
            const store_expr: *GrinExpr = blk: {
                const e = try ctx.alloc.create(GrinExpr);
                e.* = switch (rhs_expr.*) {
                    .Return => |v| .{ .Store = v },
                    else => {
                        // Complex RHS - need to evaluate and store.
                        // For MVP, store a unit placeholder.
                        e.* = .{ .Return = .{ .Unit = {} } };
                        break :blk e;
                    },
                };
                break :blk e;
            };

            // Bind the stored value to a variable.
            const fresh_ptr = try ctx.freshName("p");

            // Translate the body.
            const body_expr = try translateExpr(ctx, let_expr.body);

            // Create the bind expression: store X >>= \p -> body
            const bind_expr = try ctx.alloc.create(GrinExpr);
            bind_expr.* = .{ .Bind = .{
                .lhs = store_expr,
                .pat = .{ .Var = fresh_ptr },
                .rhs = body_expr,
            }};

            return bind_expr;
        },
        .Rec => |pairs| {
            // Recursive let: Allocate placeholders, update with real values.
            // let rec { a = f b; b = g a } in body
            // becomes: store placeholders with dummy values, update with real thunks.

            const placeholders = try ctx.alloc.alloc(GrinName, pairs.len);
            defer ctx.alloc.free(placeholders);

            // Create placeholder stores for each binder.
            for (placeholders) |*p| {
                p.* = try ctx.freshName("p");

                // Create a unit value as placeholder.
                const store_expr = try ctx.alloc.create(GrinExpr);
                store_expr.* = .{ .Store = .{ .Unit = {} } };

                // Bind to a fresh pointer variable.
                // Create the RHS expression (unit return) first.
                const rhs_expr = try ctx.alloc.create(GrinExpr);
                rhs_expr.* = .{ .Return = .{ .Unit = {} } };

                const bind_expr = try ctx.alloc.create(GrinExpr);
                bind_expr.* = .{ .Bind = .{
                    .lhs = store_expr,
                    .pat = .{ .Var = p.* },
                    .rhs = rhs_expr,
                }};
            }

            // For MVP, just translate the body.
            // A full implementation would update placeholders with actual values.
            const body_expr = try translateExpr(ctx, let_expr.body);
            return body_expr;
        },
    }
}

/// Translate a case expression.
fn translateCase(ctx: *TranslateCtx, case_expr: *const CoreCase) anyerror!*GrinExpr {
    // case scrutinee of { alts }
    // becomes: fetch scrutinee >>= \val -> case val of { alts }
    // Note: eval call would be inserted by #315 (eval/apply generation)
    // For now, we just fetch and case directly.

    const scrutinee_val = try translateScrutinee(ctx, case_expr.scrutinee);

    // Translate the case binder.
    // Translate case alternatives.
    var alts = try ctx.alloc.alloc(GrinAlt, case_expr.alts.len);
    for (case_expr.alts, 0..) |alt, i| {
        alts[i] = try translateAlt(ctx, alt);
    }

    // Create the case expression.
    const case_grin = try ctx.alloc.create(GrinExpr);
    case_grin.* = .{ .Case = .{
        .scrutinee = scrutinee_val,
        .alts = alts,
    }};

    return case_grin;
}

/// Translate a case scrutinee to a value.
fn translateScrutinee(ctx: *TranslateCtx, scrutinee: *const CoreExpr) !GrinVal {
    // Simple case: variable or literal.
    // For MVP, handle Var and Lit only.
    switch (scrutinee.*) {
        .Var => |v| {
            const grin_name = try ctx.getCoreVar(v.name);
            return .{ .Var = grin_name };
        },
        .Lit => |l| {
            return .{ .Lit = translateLiteral(l.val) };
        },
        else => {
            // Complex scrutinee expression.
            // For MVP, use a placeholder variable.
            const fresh = try ctx.freshName("scrut");
            return .{ .Var = fresh };
        },
    }
}

/// Translate a case alternative.
fn translateAlt(ctx: *TranslateCtx, alt: CoreAlt) !GrinAlt {
    // Translate the pattern.
    const pat = try translatePattern(ctx, alt.con, alt.binders);

    // Translate the body.
    const body = try translateExpr(ctx, alt.body);

    return GrinAlt{
        .pat = pat,
        .body = body,
    };
}

/// Translate a pattern.
fn translatePattern(ctx: *TranslateCtx, con: CoreAltCon, binders: []const CoreId) !GrinCPat {
    switch (con) {
        .DataAlt => |name| {
            // Constructor pattern: bind field names.
            var field_names = try ctx.alloc.alloc(GrinName, binders.len);
            for (binders, 0..) |binder, i| {
                field_names[i] = try ctx.mapBinder(&binder);
            }

            const tag = GrinTag{
                .tag_type = .Con,
                .name = name,
            };

            return .{ .NodePat = .{
                .tag = tag,
                .fields = field_names,
            }};
        },
        .LitAlt => |lit| {
            // Literal pattern.
            const grin_lit = translateLiteral(lit);
            return .{ .LitPat = grin_lit };
        },
        .Default => {
            // Default/wildcard pattern.
            return .{ .DefaultPat = {} };
        },
    }
}

/// Translate a Core literal to a GRIN literal.
fn translateLiteral(lit: CoreLiteral) GrinLiteral {
    return switch (lit) {
        .Int => |i| .{ .Int = i },
        .Float => |f| .{ .Float = f },
        .Char => |c| .{ .Char = c },
        .String => |s| .{ .String = s },
    };
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "translateProgram: simple identity function" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a simple Core program: id = \x -> x
    const x_id = core.Id{
        .name = grin.Name{ .base = "x", .unique = .{ .value = 1 } },
        .ty = undefined,
        .span = undefined,
    };

    const x_var = try alloc.create(CoreExpr);
    x_var.* = .{ .Var = x_id };

    const lambda = try alloc.create(CoreExpr);
    lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = x_var,
        .span = undefined,
    }};

    const id_binder = core.Id{
        .name = grin.Name{ .base = "id", .unique = .{ .value = 10 } },
        .ty = undefined,
        .span = undefined,
    };

    const bind_pair = CoreBindPair{
        .binder = id_binder,
        .rhs = lambda,
    };

    const core_prog = CoreProgram{
        .data_decls = &.{},
        .binds = &.{.{ .NonRec = bind_pair }},
    };

    const grin_prog = try translateProgram(alloc, core_prog);

    // Should have one definition with one parameter.
    try testing.expectEqual(@as(usize, 1), grin_prog.defs.len);
    try testing.expectEqual(@as(usize, 1), grin_prog.defs[0].params.len);
}

test "translateLiteral: all variants" {
    const lit_int = translateLiteral(.{ .Int = 42 });
    try testing.expectEqual(@as(i64, 42), lit_int.Int);

    const lit_float = translateLiteral(.{ .Float = 3.14 });
    try testing.expectEqual(@as(f64, 3.14), lit_float.Float);

    const lit_char = translateLiteral(.{ .Char = 'x' });
    try testing.expectEqual(@as(u21, 'x'), lit_char.Char);

    const lit_str = translateLiteral(.{ .String = "hello" });
    try testing.expectEqualStrings("hello", lit_str.String);
}

test "TranslateCtx: freshName generation" {
    var ctx = TranslateCtx.init(testing.allocator);
    defer ctx.deinit();

    const n1 = try ctx.freshName("x");
    const n2 = try ctx.freshName("x");

    try testing.expect(!n1.eql(n2));
    try testing.expect(n1.unique.value < n2.unique.value);
}

test "TranslateCtx: binder mapping" {
    var ctx = TranslateCtx.init(testing.allocator);
    defer ctx.deinit();

    const core_name = grin.Name{ .base = "foo", .unique = .{ .value = 42 } };
    const core_id = core.Id{
        .name = core_name,
        .ty = undefined,
        .span = undefined,
    };

    const mapped1 = try ctx.mapBinder(&core_id);
    const mapped2 = try ctx.mapBinder(&core_id);

    // Should return the same name for the same binder.
    try testing.expect(mapped1.eql(mapped2));
}

test "translateProgram: literal value" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a Core program: main = 42
    const lit_expr = try alloc.create(CoreExpr);
    lit_expr.* = .{ .Lit = .{ .val = .{ .Int = 42 }, .span = undefined } };

    const main_binder = core.Id{
        .name = grin.Name{ .base = "main", .unique = .{ .value = 0 } },
        .ty = undefined,
        .span = undefined,
    };

    const bind_pair = CoreBindPair{
        .binder = main_binder,
        .rhs = lit_expr,
    };

    const core_prog = CoreProgram{
        .data_decls = &.{},
        .binds = &.{.{ .NonRec = bind_pair }},
    };

    const grin_prog = try translateProgram(alloc, core_prog);

    try testing.expectEqual(@as(usize, 1), grin_prog.defs.len);

    // The body should be a Return expression with the literal.
    const body = grin_prog.defs[0].body;
    switch (body.*) {
        .Return => |v| {
            try testing.expectEqual(@as(i64, 42), v.Lit.Int);
        },
        else => try testing.expect(false),
    }
}
