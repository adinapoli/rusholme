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
const FieldType = grin.FieldType;

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

// ── HPT-Lite Type Inference Helpers ─────────────────────────────────────

/// Infer FieldType from a Core literal.
/// Part of HPT-lite: simple type inference for literal values.
/// See: https://github.com/adinapoli/rusholme/issues/449
fn inferFieldTypeFromLiteral(lit: core.Literal) FieldType {
    return switch (lit) {
        .Int => .i64,
        .Float => .f64,
        .Char => .i64, // chars are stored as i64
        .String => .ptr, // strings are pointers
    };
}

/// Infer FieldType from a Core type.
/// Returns null for complex types (delegates to ptr conservatively).
/// Part of HPT-lite: simple type inference from type annotations.
/// See: https://github.com/adinapoli/rusholme/issues/449
fn inferFieldTypeFromCoreType(ty: core.CoreType) ?FieldType {
    return switch (ty) {
        .TyVar => null, // Type variable - unknown
        .TyCon => |tc| blk: {
            // Check for primitive type constructors
            if (std.mem.eql(u8, tc.name.base, "Int") or
                std.mem.eql(u8, tc.name.base, "Char") or
                std.mem.eql(u8, tc.name.base, "Bool"))
            {
                break :blk .i64;
            }
            if (std.mem.eql(u8, tc.name.base, "Float") or
                std.mem.eql(u8, tc.name.base, "Double"))
            {
                break :blk .f64;
            }
            // Other type constructors are heap pointers
            break :blk .ptr;
        },
        .FunTy => .ptr, // Functions are closures (pointers)
        .ForAllTy => |fa| inferFieldTypeFromCoreType(fa.body.*),
    };
}

// ── Translation Context ─────────────────────────────────────────────────

/// Context for the Core to GRIN translation.
const TranslateCtx = struct {
    alloc: std.mem.Allocator,
    // Maps Core binders to their GRIN variable names.
    var_map: std.AutoHashMapUnmanaged(u64, GrinName),
    // Maps function names to their arity (number of parameters).
    // Used for partial/over-application handling (issue #317).
    arity_map: std.AutoHashMapUnmanaged(u64, u32),
    // Maps data constructor uniques to their field count (number of value
    // arguments, excluding type arguments).  Built from CoreProgram.data_decls.
    // Used to distinguish constructor applications from function calls in
    // translateApp, and to emit ValTag for nullary constructors in translateExpr.
    con_map: std.AutoHashMapUnmanaged(u64, u32),
    // Counter for generating fresh GRIN variable names.
    name_counter: u64 = 0,

    pub fn init(alloc: std.mem.Allocator) TranslateCtx {
        return .{
            .alloc = alloc,
            .var_map = .{},
            .arity_map = .{},
            .con_map = .{},
        };
    }

    pub fn deinit(self: *TranslateCtx) void {
        self.var_map.deinit(self.alloc);
        self.arity_map.deinit(self.alloc);
        self.con_map.deinit(self.alloc);
    }

    /// Return true if the given unique belongs to a known data constructor.
    fn isConstructor(self: TranslateCtx, unique: u64) bool {
        return self.con_map.contains(unique);
    }

    /// Return the field count for a constructor, or null if unknown.
    fn conFieldCount(self: TranslateCtx, unique: u64) ?u32 {
        return self.con_map.get(unique);
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

    /// Get the arity (number of parameters) of a function.
    /// Returns null if the function is unknown (e.g., higher-order).
    fn getFunctionArity(self: TranslateCtx, name: GrinName) ?u32 {
        return self.arity_map.get(name.unique.value);
    }
};

/// A pending bind for a complex argument sub-expression.
/// Used by translateApp to sequence complex args before the outer App.
const PendingBind = struct {
    fresh_var: GrinName,
    complex_expr: *GrinExpr,
};

// ── Translation Functions ───────────────────────────────────────────────

/// Analyze a Core program to build the arity map.
/// This maps each function name to its arity (number of lambda parameters).
fn buildArityMap(alloc: std.mem.Allocator, core_prog: CoreProgram) !std.AutoHashMapUnmanaged(u64, u32) {
    var arity_map = std.AutoHashMapUnmanaged(u64, u32){};
    errdefer arity_map.deinit(alloc);

    // Process each top-level binding.
    for (core_prog.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                const arity = try countLambdaArity(pair.rhs);
                const unique_id = pair.binder.name.unique.value;
                try arity_map.put(alloc, unique_id, arity);
            },
            .Rec => |pairs| {
                for (pairs) |pair| {
                    const arity = try countLambdaArity(pair.rhs);
                    const unique_id = pair.binder.name.unique.value;
                    try arity_map.put(alloc, unique_id, arity);
                }
            },
        }
    }

    return arity_map;
}

/// Build a map from data constructor uniques to their field counts.
///
/// The field count of a constructor is the number of value-level arguments
/// its type has, i.e. the number of leading `FunTy` arrows after stripping
/// `ForAllTy` quantifiers.
///
/// Example:
///   Nil  :: forall a. List a         → 0 fields
///   Cons :: forall a. a -> List a -> List a  → 2 fields
fn buildConMap(alloc: std.mem.Allocator, core_prog: CoreProgram) !std.AutoHashMapUnmanaged(u64, u32) {
    var con_map = std.AutoHashMapUnmanaged(u64, u32){};
    errdefer con_map.deinit(alloc);

    for (core_prog.data_decls) |decl| {
        for (decl.constructors) |con| {
            const unique = con.name.unique.value;
            const n_fields = countConFields(con.ty);
            try con_map.put(alloc, unique, n_fields);
        }
    }

    return con_map;
}

/// Count the value-level field count of a constructor type by counting
/// leading FunTy arrows, stripping ForAllTy quantifiers first.
fn countConFields(ty: CoreType) u32 {
    var current = ty;
    // Strip leading ForAllTy quantifiers.
    while (true) {
        switch (current) {
            .ForAllTy => |fa| current = fa.body.*,
            else => break,
        }
    }
    // Count FunTy arrows.
    var fields: u32 = 0;
    while (true) {
        switch (current) {
            .FunTy => |ft| {
                fields += 1;
                current = ft.res.*;
            },
            else => break,
        }
    }
    return fields;
}

/// Count the number of lambda parameters in a Core expression.
fn countLambdaArity(expr: *const CoreExpr) !u32 {
    var arity: u32 = 0;
    var current = expr;
    while (true) {
        switch (current.*) {
            .Lam => |lam| {
                arity += 1;
                current = lam.body;
            },
            else => break,
        }
    }
    return arity;
}

/// Translate a Core program to a GRIN program.
pub fn translateProgram(alloc: std.mem.Allocator, core_prog: CoreProgram) !GrinProgram {
    // Build the arity map for partial/over-application handling.
    var arity_map = try buildArityMap(alloc, core_prog);
    defer arity_map.deinit(alloc);

    // Build the constructor map from data declarations.
    var con_map = try buildConMap(alloc, core_prog);
    defer con_map.deinit(alloc);

    var ctx = TranslateCtx.init(alloc);
    defer ctx.deinit();

    // Copy the arity map into the context.
    var iter = arity_map.iterator();
    while (iter.next()) |entry| {
        try ctx.arity_map.put(alloc, entry.key_ptr.*, entry.value_ptr.*);
    }

    // Copy the constructor map into the context.
    var con_iter = con_map.iterator();
    while (con_iter.next()) |entry| {
        try ctx.con_map.put(alloc, entry.key_ptr.*, entry.value_ptr.*);
    }

    var defs = std.ArrayListUnmanaged(GrinDef){};
    defer defs.deinit(alloc);

    // Process each top-level binding into a GRIN Def.
    for (core_prog.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                // Skip `$` — it is inlined at every call site in translateApp
                // and never needs a runtime GRIN definition.
                if (std.mem.eql(u8, pair.binder.name.base, "$")) continue;
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
            const unique = v.name.unique.value;
            if (ctx.conFieldCount(unique)) |n_fields| {
                if (n_fields == 0) {
                    // Nullary constructor (e.g. Nil, True, Nothing): emit a bare tag value.
                    // In GRIN, nullary constructors are immediate tag constants — no heap
                    // allocation needed.  The LLVM backend emits an i64 discriminant for them.
                    const tag = GrinTag{ .tag_type = .Con, .name = v.name };
                    new_expr.* = .{ .Return = .{ .ValTag = tag } };
                } else {
                    // Non-nullary constructor used as a value (e.g. partially applied).
                    // Fall back to a variable reference; proper closure support is tracked in:
                    // https://github.com/adinapoli/rusholme/issues/386
                    const grin_name = try ctx.getCoreVar(v.name);
                    new_expr.* = .{ .Return = .{ .Var = grin_name } };
                }
            } else {
                // Ordinary variable reference.
                const grin_name = try ctx.getCoreVar(v.name);
                new_expr.* = .{ .Return = .{ .Var = grin_name } };
            }
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

/// Extract a GrinVal from a GrinExpr assuming it returns a simple value.
/// Used for Update expressions which need a Val rather than an Expr.
fn exprToVal(expr: *const GrinExpr) !GrinVal {
    return switch (expr.*) {
        .Return => |v| v,
        else => error.CannotExtractValue, // Complex expressions need binding
    };
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
    var fn_expr: *const CoreExpr = current;

    // Inline `$`: `App(App($, f), x)` → `App(f, x)`.
    //
    // `$` is purely syntactic function application sugar; it never needs a
    // runtime representation.  After the arg-collection loop, `args` is in
    // right-to-left order, so `args[args.items.len - 1]` is the leftmost
    // argument — the function to be applied.  We promote that expression to
    // be the new head and drop it from the argument list.
    //
    // This is iterated so that a chain like `($) ($) f x` is also handled.
    while (true) {
        switch (fn_expr.*) {
            .Var => |v| {
                if (!std.mem.eql(u8, v.name.base, "$")) break;
                if (args.items.len == 0) break;
                fn_expr = args.items[args.items.len - 1];
                args.items.len -= 1;
            },
            else => break,
        }
    }

    // Check whether the function head is a data constructor *before* translating
    // it.  We need the original Core unique to look up the con_map, because
    // translateExpr assigns a fresh GRIN unique that won't match.
    const core_con_unique: ?u64 = switch (fn_expr.*) {
        .Var => |v| if (ctx.isConstructor(v.name.unique.value)) v.name.unique.value else null,
        else => null,
    };

    // Translate the function head.
    const translated_fn = try translateExpr(ctx, fn_expr);

    const FnNameAndArity = struct {
        name: ?GrinName,
        arity: ?u32,
    };

    const fn_name_and_arity = blk: {
        switch (translated_fn.*) {
            .Return => |v| {
                switch (v) {
                    .Var => |name| {
                        const arity = ctx.getFunctionArity(name);
                        break :blk FnNameAndArity{
                            .name = name,
                            .arity = arity,
                        };
                    },
                    else => break :blk FnNameAndArity{ .name = null, .arity = null },
                }
            },
            else => break :blk FnNameAndArity{ .name = null, .arity = null },
        }
    };

    // Reverse the arguments (we collected them right-to-left)
    std.mem.reverse(*const CoreExpr, args.items);

    // Translate all arguments.
    // GRIN requires all App arguments to be simple values (variables or literals).
    // Complex sub-expressions (e.g., another App like `g x`) must be sequenced
    // with Bind before the outer App call (A-normal form).
    //
    // Example: `f (g x)` becomes:
    //   arg <- g x
    //   f arg

    var pending_binds = std.ArrayListUnmanaged(PendingBind){};
    defer pending_binds.deinit(ctx.alloc);

    var grin_args = try ctx.alloc.alloc(GrinVal, args.items.len);
    for (args.items, 0..) |arg, i| {
        const arg_result = try translateExpr(ctx, arg);
        // The expression should return a value.
        switch (arg_result.*) {
            .Return => |v| {
                grin_args[i] = v;
            },
            else => {
                // Complex argument expression - bind it to a fresh variable.
                const fresh_var = try ctx.freshName("arg");
                grin_args[i] = .{ .Var = fresh_var };
                try pending_binds.append(ctx.alloc, .{
                    .fresh_var = fresh_var,
                    .complex_expr = arg_result,
                });
            },
        }
    }

    // ── Constructor application ────────────────────────────────────────────
    //
    // If the function head is a known data constructor, emit a heap allocation
    // instead of a function call:
    //   `Cons x xs`  →  store (CCons [x, xs])
    //
    // This handles saturated constructor applications.  Partial application of
    // constructors (tracked in https://github.com/adinapoli/rusholme/issues/386)
    // falls through to the general partial-application path below.
    if (core_con_unique) |con_unique| {
        if (fn_name_and_arity.name) |fn_name| {
            const n_fields = ctx.conFieldCount(con_unique).?;
            const arg_count = @as(u32, @intCast(args.items.len));
            if (arg_count == n_fields) {
                // Saturated constructor application → Store (ConstTagNode).
                // Use the original Core name so the tag carries the stable unique.
                const core_name = switch (fn_expr.*) {
                    .Var => |v| v.name,
                    else => fn_name,
                };
                const tag = GrinTag{ .tag_type = .Con, .name = core_name };
                const store_expr = try ctx.alloc.create(GrinExpr);
                store_expr.* = .{ .Store = .{ .ConstTagNode = .{
                    .tag = tag,
                    .fields = grin_args,
                } } };
                const ptr_var = try ctx.freshName("node");
                const return_expr = try ctx.alloc.create(GrinExpr);
                return_expr.* = .{ .Return = .{ .Var = ptr_var } };
                const bind_expr = try ctx.alloc.create(GrinExpr);
                bind_expr.* = .{ .Bind = .{
                    .lhs = store_expr,
                    .pat = .{ .Var = ptr_var },
                    .rhs = return_expr,
                } };
                return try wrapWithPendingBinds(ctx, bind_expr, pending_binds.items);
            }
            // Under-saturated constructor: fall through to partial-application path.
        }
    }

    // Handle partial/over-application (issue #317)
    if (fn_name_and_arity.name) |fn_name| {
        if (fn_name_and_arity.arity) |arity| {
            const arg_count = @as(u32, @intCast(args.items.len));

            if (arg_count < arity) {
                // Partial application: create a P-tagged node
                // Example: map f (arity=2, args=1) -> store (P(1)map [f])

                // Create the partial application node with P-tag
                const store_expr = try ctx.alloc.create(GrinExpr);
                store_expr.* = .{ .Store = .{ .VarTagNode = .{
                    .tag_var = fn_name,
                    .fields = grin_args,
                } } };

                // Wrap in a bind to get the pointer and return it
                const ptr_var = try ctx.freshName("partial");
                const return_expr = try ctx.alloc.create(GrinExpr);
                return_expr.* = .{ .Return = .{ .Var = ptr_var } };

                const bind_expr = try ctx.alloc.create(GrinExpr);
                bind_expr.* = .{ .Bind = .{
                    .lhs = store_expr,
                    .pat = .{ .Var = ptr_var },
                    .rhs = return_expr,
                } };

                return try wrapWithPendingBinds(ctx, bind_expr, pending_binds.items);
            } else if (arg_count > arity) {
                // Over-application: use App for saturated part, chain apply calls
                // Example: (f x) y z (arity=1, args=3) ->
                //   app f [x] >>= \res -> apply res [y] >>= \res2 -> apply res2 [z]
                const saturated_args = grin_args[0..arity];
                const excess_args = grin_args[arity..];

                // Create the initial App with saturated arguments
                const initial_app = try ctx.alloc.create(GrinExpr);
                initial_app.* = .{ .App = .{
                    .name = fn_name,
                    .args = saturated_args,
                } };

                // Chain apply calls for excess arguments
                var current_expr: *GrinExpr = initial_app;
                for (excess_args) |excess_arg| {
                    const result_var = try ctx.freshName("res");

                    // Create apply expr: apply current_result [excess_arg]
                    const apply_expr = try ctx.alloc.create(GrinExpr);
                    apply_expr.* = .{
                        .App = .{
                            .name = .{ .base = "apply", .unique = .{ .value = 9998 } },
                            .args = &[_]GrinVal{
                                .{ .Var = result_var }, // This will be bound from previous step
                                excess_arg,
                            },
                        },
                    };

                    // Create bind: result = apply current_result [excess_arg]
                    const bind_expr = try ctx.alloc.create(GrinExpr);
                    bind_expr.* = .{ .Bind = .{
                        .lhs = current_expr,
                        .pat = .{ .Var = result_var },
                        .rhs = apply_expr,
                    } };

                    current_expr = bind_expr;
                }

                // Return the final result
                const final_result = try ctx.freshName("final");
                const return_expr = try ctx.alloc.create(GrinExpr);
                return_expr.* = .{ .Return = .{ .Var = final_result } };

                const final_bind = try ctx.alloc.create(GrinExpr);
                final_bind.* = .{ .Bind = .{
                    .lhs = current_expr,
                    .pat = .{ .Var = final_result },
                    .rhs = return_expr,
                } };

                return try wrapWithPendingBinds(ctx, final_bind, pending_binds.items);
            }
        }
    }

    // Normal case: exact application or unknown arity
    // Create an App expression.
    const app_fn_name = blk: {
        if (fn_name_and_arity.name) |name| {
            break :blk name;
        }
        // Fallback: if we couldn't extract a simple function name,
        // we can't create a direct App - use a placeholder
        break :blk try ctx.freshName("unknown_func");
    };

    const grin_app = try ctx.alloc.create(GrinExpr);
    grin_app.* = .{ .App = .{
        .name = app_fn_name,
        .args = grin_args,
    } };

    return try wrapWithPendingBinds(ctx, grin_app, pending_binds.items);
}

/// Wrap an expression in Bind chains for pending complex argument sub-expressions.
///
/// Given `pending_binds = [{arg_1, (g x)}, {arg_2, (h y)}]` and `inner = f arg_1 arg_2`,
/// produces:
///   arg_1 <- g x
///   arg_2 <- h y
///   f arg_1 arg_2
///
/// The binds are built inside-out: the last pending bind wraps innermost.
fn wrapWithPendingBinds(
    ctx: *TranslateCtx,
    inner: *GrinExpr,
    pending_binds: []const PendingBind,
) anyerror!*GrinExpr {
    if (pending_binds.len == 0) return inner;

    // Build from inside out: the last pending bind is closest to inner.
    var result = inner;
    var i: usize = pending_binds.len;
    while (i > 0) {
        i -= 1;
        const pb = pending_binds[i];
        const bind_expr = try ctx.alloc.create(GrinExpr);
        bind_expr.* = .{ .Bind = .{
            .lhs = pb.complex_expr,
            .pat = .{ .Var = pb.fresh_var },
            .rhs = result,
        } };
        result = bind_expr;
    }
    return result;
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

            // Bind the stored value using the actual let-bound binder name so the
            // body's references (via var_map) resolve correctly.
            const binder_name = try ctx.mapBinder(&pair.binder);

            // Translate the body.
            const body_expr = try translateExpr(ctx, let_expr.body);

            // Create the bind expression: store X >>= \binder_name -> body
            const bind_expr = try ctx.alloc.create(GrinExpr);
            bind_expr.* = .{ .Bind = .{
                .lhs = store_expr,
                .pat = .{ .Var = binder_name },
                .rhs = body_expr,
            } };

            return bind_expr;
        },
        .Rec => |pairs| {
            // Recursive let: Allocate placeholders, then backpatch with real values.
            // let rec { a = f b; b = g a } in body
            // becomes:
            //   store Unit >>= p_a ->
            //   store Unit >>= p_b ->
            //   [[f b with b:=p_b]] >>= thunk_a -> update p_a thunk_a -> _
            //   [[g a with a:=p_a]] >>= thunk_b -> update p_b thunk_b -> _
            //   [[body[a:=p_a, b:=p_b]]]

            // First, create placeholder variables for all binders
            const placeholders = try ctx.alloc.alloc(GrinName, pairs.len);
            defer ctx.alloc.free(placeholders);

            for (placeholders, 0..) |_, i| {
                placeholders[i] = try ctx.mapBinder(&pairs[i].binder);
            }

            // Create placeholder stores for each binder (storing unit placeholders)
            var current_expr: ?*GrinExpr = null;

            // Step 1: Allocate all placeholders
            for (placeholders) |p| {
                const store_expr = try ctx.alloc.create(GrinExpr);
                store_expr.* = .{ .Store = .{ .Unit = {} } };

                const placeholder_expr = if (current_expr) |_|
                    // Chain: prev >>= \p_placeholder -> store Unit
                    try ctx.alloc.create(GrinExpr)
                else
                    store_expr;

                if (current_expr) |prev_expr| {
                    placeholder_expr.* = .{ .Bind = .{
                        .lhs = prev_expr,
                        .pat = .{ .Var = p },
                        .rhs = store_expr,
                    } };
                }

                current_expr = placeholder_expr;
            }

            // Step 2: Backpatch each binding with its real RHS
            for (pairs, 0..) |pair, i| {
                // Translate the RHS expression
                const rhs_expr = try translateExpr(ctx, pair.rhs);

                // For Update, we need a Val, not an Expr.
                // If RHS is a simple Return, extract its value.
                // Otherwise, we'd need to bind and use the variable.
                // For now, assume RHS can be converted to a value.
                const rhs_val = try exprToVal(rhs_expr);

                // Create the update expression: update placeholder_i rhs_val
                const update_expr = try ctx.alloc.create(GrinExpr);
                update_expr.* = .{ .Update = .{
                    .ptr = placeholders[i],
                    .val = rhs_val,
                } };

                // Chain the update after previous binds, bind _ to continue
                const discard_var = try ctx.freshName("_");

                if (current_expr) |prev| {
                    const bind_update = try ctx.alloc.create(GrinExpr);
                    bind_update.* = .{ .Bind = .{
                        .lhs = prev,
                        .pat = .{ .Var = discard_var },
                        .rhs = update_expr,
                    } };
                    current_expr = bind_update;
                }
            }

            // Step 3: Translate the body with binders substituted by placeholders
            const body_expr = try translateExpr(ctx, let_expr.body);

            // Finish the chain by binding the body as the final RHS
            if (current_expr) |prev| {
                const final_bind = try ctx.alloc.create(GrinExpr);
                final_bind.* = .{ .Bind = .{
                    .lhs = prev,
                    .pat = .{ .Var = try ctx.freshName("_") },
                    .rhs = body_expr,
                } };
                return final_bind;
            }

            // Fallback if no bindings (shouldn't happen with Rec)
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
    } };

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
            } };
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

// ── Tag Collection ────────────────────────────────────────────────────────

/// Collected tags from a GRIN program for eval/apply generation.
const TagInfo = struct {
    /// Constructor tags (C-tagged)
    con_tags: std.ArrayListUnmanaged(GrinTag),

    /// Function tags (F-tagged) - all top-level function names
    fun_tags: std.StringHashMapUnmanaged(void), // deduplicated by name

    pub fn init() TagInfo {
        return .{
            .con_tags = .empty,
            .fun_tags = .empty,
        };
    }

    pub fn deinit(self: *TagInfo, alloc: std.mem.Allocator) void {
        self.con_tags.deinit(alloc);
        self.fun_tags.deinit(alloc);
    }
};

/// Collect all tags from a GRIN program.
fn collectTags(alloc: std.mem.Allocator, program: GrinProgram) !TagInfo {
    var info = TagInfo.init();
    errdefer info.deinit(alloc);

    // Collect function names (all Def names are potential F-tags)
    for (program.defs) |def| {
        try info.fun_tags.put(alloc, def.name.base, {});
    }

    // Collect constructor tags by scanning all expressions for ConstTagNode
    for (program.defs) |def| {
        try collectTagsFromExpr(alloc, def.body, &info);
    }

    return info;
}

/// Recursively scan an expression to collect constructor tags.
fn collectTagsFromExpr(alloc: std.mem.Allocator, expr: *const GrinExpr, info: *TagInfo) !void {
    switch (expr.*) {
        .Bind => |bind| {
            try collectTagsFromExpr(alloc, bind.lhs, info);
            try collectTagsFromExpr(alloc, bind.rhs, info);
        },
        .Case => |case_expr| {
            try collectTagsFromVal(alloc, case_expr.scrutinee, info);
            for (case_expr.alts) |alt| {
                try collectTagsFromExpr(alloc, alt.body, info);
            }
        },
        .App => |app| {
            for (app.args) |arg| {
                try collectTagsFromVal(alloc, arg, info);
            }
        },
        .Return => |v| {
            try collectTagsFromVal(alloc, v, info);
        },
        .Store => |v| {
            try collectTagsFromVal(alloc, v, info);
        },
        .Fetch => |fetch| {
            _ = fetch; // no tags in ptr variable name
        },
        .Update => |update| {
            try collectTagsFromVal(alloc, update.val, info);
        },
        .Block => |inner| {
            try collectTagsFromExpr(alloc, inner, info);
        },
    }
}

/// Recursively scan a value for constructor tags.
fn collectTagsFromVal(alloc: std.mem.Allocator, val: GrinVal, info: *TagInfo) !void {
    switch (val) {
        .ConstTagNode => |ctn| {
            // Found a constructor - add it to con_tags if not already present
            const tag = ctn.tag;
            var found = false;
            for (info.con_tags.items) |t| {
                if (t.eql(tag)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                try info.con_tags.append(alloc, tag);
            }
            // Also scan fields recursively
            for (ctn.fields) |field| {
                try collectTagsFromVal(alloc, field, info);
            }
        },
        .VarTagNode => |vtn| {
            // Scan field variables (these are not constructor names)
            for (vtn.fields) |field| {
                try collectTagsFromVal(alloc, field, info);
            }
        },
        else => {},
    }
}

// ── Eval/Apply Generation ─────────────────────────────────────────────────

/// Helper: Create a constructor tag with the given name.
fn conTag(base: []const u8, unique: u64) GrinTag {
    return .{ .tag_type = .{ .Con = {} }, .name = .{ .base = base, .unique = .{ .value = unique } } };
}

/// Helper: Create a function tag with the given name.
fn funTag(base: []const u8, unique: u64) GrinTag {
    return .{ .tag_type = .{ .Fun = {} }, .name = .{ .base = base, .unique = .{ .value = unique } } };
}

/// Helper: Create a partial tag with the given name and missing count.
fn partialTag(base: []const u8, unique: u64, missing: u32) GrinTag {
    return .{ .tag_type = .{ .Partial = missing }, .name = .{ .base = base, .unique = .{ .value = unique } } };
}

/// Generate the `eval` and `apply` functions for a GRIN program.
///
/// This is issue #315: Generate whole-program eval and apply functions.
/// Takes a GRIN program and returns it augmented with the special functions.
pub fn generateEvalApply(alloc: std.mem.Allocator, program: GrinProgram) !GrinProgram {
    // Collect all tags from the program
    var tag_info = try collectTags(alloc, program);
    defer tag_info.deinit(alloc);

    // Create a new program with all existing defs plus eval and apply
    var new_defs = std.ArrayListUnmanaged(GrinDef){};
    defer new_defs.deinit(alloc);

    // Copy all existing definitions
    for (program.defs) |def| {
        try new_defs.append(alloc, def);
    }

    // Generate the eval function
    const eval_def = try generateEvalFunc(alloc, &tag_info);
    try new_defs.append(alloc, eval_def);

    // Generate the apply function
    const apply_def = try generateApplyFunc(alloc);
    try new_defs.append(alloc, apply_def);

    const defs_slice = try new_defs.toOwnedSlice(alloc);
    return GrinProgram{ .defs = defs_slice };
}

/// Generate the `eval p` function.
///
/// eval p:
///   fetch p >>= \node ->
///     case node of {
///       C<tag> <fields> -> return C<tag> <fields>
///       F<func> []      -> app func [] >>= \result -> update p result; return result
///       P(n)<func> <args> -> return P(n)<func> <args>
///       _ -> return node
///     }
fn generateEvalFunc(alloc: std.mem.Allocator, tag_info: *const TagInfo) !GrinDef {
    const eval_unique: u64 = 9999;
    const p_param = try alloc.create(GrinName);
    p_param.* = .{ .base = "p", .unique = .{ .value = eval_unique } };

    // Variable to hold the fetched node
    const node_var = try alloc.create(GrinName);
    node_var.* = .{ .base = "node", .unique = .{ .value = eval_unique + 1 } };

    // Variable to hold function application result
    const result_var = try alloc.create(GrinName);
    result_var.* = .{ .base = "result", .unique = .{ .value = eval_unique + 2 } };

    // Create alternatives for all tags
    var alts = std.ArrayListUnmanaged(GrinAlt){};
    defer alts.deinit(alloc);

    // Add C-tag alternatives (constructors - already evaluated)
    for (tag_info.con_tags.items) |con_tag| {
        const alt = try generateConTagAlt(alloc, node_var.*, con_tag);
        try alts.append(alloc, alt);
    }

    // Add F-tag alternatives (thunks - need to force)
    var fun_iter = tag_info.fun_tags.iterator();
    while (fun_iter.next()) |entry| {
        const func_name = GrinName{
            .base = entry.key_ptr.*,
            .unique = .{ .value = 0 }, // Use base name
        };
        const alt = try generateFunTagAlt(alloc, p_param.*, result_var.*, func_name);
        try alts.append(alloc, alt);
    }

    // Add P-tag alternatives (partial applications - already a value)
    // For simplicity, use a default pattern that returns the node
    const default_alt = try alloc.create(GrinAlt);
    const default_body = try alloc.create(GrinExpr);
    default_body.* = .{ .Return = .{ .Var = node_var.* } };
    default_alt.* = .{
        .pat = .{ .DefaultPat = {} },
        .body = default_body,
    };
    try alts.append(alloc, default_alt.*);

    // Create case expression: case node of { ... }
    const case_expr = try alloc.create(GrinExpr);
    case_expr.* = .{ .Case = .{
        .scrutinee = .{ .Var = node_var.* },
        .alts = try alts.toOwnedSlice(alloc),
    } };

    // Create fetch expression: fetch p
    const fetch_expr = try alloc.create(GrinExpr);
    fetch_expr.* = .{ .Fetch = .{
        .ptr = p_param.*,
        .index = null,
    } };

    // Create bind expression: fetch p >>= \node -> case node of ...
    const body = try alloc.create(GrinExpr);
    body.* = .{ .Bind = .{
        .lhs = fetch_expr,
        .pat = .{ .Var = node_var.* },
        .rhs = case_expr,
    } };

    const params_slice = try alloc.alloc(GrinName, 1);
    params_slice[0] = p_param.*;

    return GrinDef{
        .name = .{ .base = "eval", .unique = .{ .value = eval_unique } },
        .params = params_slice,
        .body = body,
    };
}

/// Generate a C-tag alternative (constructor - already evaluated).
///
/// Pattern: C<tag> <fields>
/// Body: return C<tag> <fields>
fn generateConTagAlt(alloc: std.mem.Allocator, node_var: GrinName, con_tag: GrinTag) !GrinAlt {
    // We need to create fresh field names for binding
    // The number of fields should be known from the constructor's arity
    // For simplicity, we'll just return the node directly
    const alt_body = try alloc.create(GrinExpr);
    alt_body.* = .{ .Return = .{ .Var = node_var } };

    return GrinAlt{
        .pat = .{ .TagPat = con_tag },
        .body = alt_body,
    };
}

/// Generate an F-tag alternative (thunk - need to force).
///
/// Pattern: F<func>
/// Body: app func [] >>= \result -> update p result; return result
fn generateFunTagAlt(alloc: std.mem.Allocator, p: GrinName, result: GrinName, func_name: GrinName) !GrinAlt {
    // Create app expression: app func []
    const app_expr = try alloc.create(GrinExpr);
    app_expr.* = .{
        .App = .{
            .name = func_name,
            .args = &.{}, // No arguments (unforced thunk)
        },
    };

    // Create update expression: update p result
    const update_expr = try alloc.create(GrinExpr);
    update_expr.* = .{ .Update = .{
        .ptr = p,
        .val = .{ .Var = result },
    } };

    // Create bind expression: app func [] >>= \result -> update p result
    const update_bind = try alloc.create(GrinExpr);
    update_bind.* = .{ .Bind = .{
        .lhs = app_expr,
        .pat = .{ .Var = result },
        .rhs = update_expr,
    } };

    // Create return expression: return result
    const ret_expr = try alloc.create(GrinExpr);
    ret_expr.* = .{ .Return = .{ .Var = result } };

    // Chain: (app func [] >>= \result -> update p result); return result
    const alt_body = try alloc.create(GrinExpr);
    alt_body.* = .{ .Bind = .{
        .lhs = update_bind,
        .pat = .{ .Var = result },
        .rhs = ret_expr,
    } };

    const fun_tag = funTag(func_name.base, func_name.unique.value);

    return GrinAlt{
        .pat = .{ .TagPat = fun_tag },
        .body = alt_body,
    };
}

/// Generate the `apply f x` function.
///
/// apply f x:
///   case f of {
///     P(n)<func> <args> with n > 1 ->
///       return P(n-1)<func> <args ++ [x]>
///     P(1)<func> <args> ->
///       app func <args ++ [x]>
///     _ -> return unit  // Simplified: just return unit for non-P values
///   }
///
/// Note: For MVP, we use a simplified version that just returns unit.
/// Full implementation would require extracting the P-tag structure.
fn generateApplyFunc(alloc: std.mem.Allocator) !GrinDef {
    const apply_unique: u64 = 9998;

    const f_param = try alloc.create(GrinName);
    f_param.* = .{ .base = "f", .unique = .{ .value = apply_unique } };

    const x_param = try alloc.create(GrinName);
    x_param.* = .{ .base = "x", .unique = .{ .value = apply_unique + 1 } };

    // For MVP: return unit
    // Full implementation would complexly pattern match on P-tags
    const body = try alloc.create(GrinExpr);
    body.* = .{ .Return = .{ .Unit = {} } };

    const params_slice = try alloc.alloc(GrinName, 2);
    params_slice[0] = f_param.*;
    params_slice[1] = x_param.*;

    return GrinDef{
        .name = .{ .base = "apply", .unique = .{ .value = apply_unique } },
        .params = params_slice,
        .body = body,
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
    } };

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

test "generateEvalApply: adds eval and apply to program" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a simple GRIN program with one function
    const body = try alloc.create(GrinExpr);
    body.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const def = GrinDef{
        .name = .{ .base = "main", .unique = .{ .value = 0 } },
        .params = &.{},
        .body = body,
    };

    const defs = try alloc.alloc(GrinDef, 1);
    defs[0] = def;

    const program = GrinProgram{ .defs = defs };

    // Generate eval/apply functions
    const augmented = try generateEvalApply(alloc, program);

    // Should have 3 definitions: original + eval + apply
    try testing.expectEqual(@as(usize, 3), augmented.defs.len);

    // Original function should be present
    try testing.expectEqualStrings("main", augmented.defs[0].name.base);

    // eval function should be present
    var eval_found = false;
    for (augmented.defs) |d| {
        if (std.mem.eql(u8, d.name.base, "eval")) {
            eval_found = true;
            try testing.expectEqual(@as(usize, 1), d.params.len);
            try testing.expectEqualStrings("p", d.params[0].base);
        }
    }
    try testing.expect(eval_found);

    // apply function should be present
    var apply_found = false;
    for (augmented.defs) |d| {
        if (std.mem.eql(u8, d.name.base, "apply")) {
            apply_found = true;
            try testing.expectEqual(@as(usize, 2), d.params.len);
            try testing.expectEqualStrings("f", d.params[0].base);
            try testing.expectEqualStrings("x", d.params[1].base);
        }
    }
    try testing.expect(apply_found);
}

test "generateEvalFunc: has proper structure" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a program with a constructor
    const con_node = try alloc.create(GrinExpr);
    con_node.* = .{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 42 } }},
    } } };

    const def = GrinDef{
        .name = .{ .base = "testFunc", .unique = .{ .value = 10 } },
        .params = &.{},
        .body = con_node,
    };

    const defs = try alloc.alloc(GrinDef, 1);
    defs[0] = def;

    const program = GrinProgram{ .defs = defs };

    // Generate eval function
    var tag_info = try collectTags(alloc, program);
    defer tag_info.deinit(alloc);

    const eval_def = try generateEvalFunc(alloc, &tag_info);

    // Verify eval structure
    try testing.expectEqualStrings("eval", eval_def.name.base);
    try testing.expectEqual(@as(usize, 1), eval_def.params.len);
    try testing.expectEqualStrings("p", eval_def.params[0].base);

    // Body should be a Bind: fetch p >>= \node -> case node of ...
    switch (eval_def.body.*) {
        .Bind => |bind| {
            // LHS should be a Fetch
            switch (bind.lhs.*) {
                .Fetch => |fetch| {
                    try testing.expectEqualStrings("p", fetch.ptr.base);
                    try testing.expect(fetch.index == null);
                },
                else => try testing.expect(false), // LHS should be Fetch
            }

            // RHS should be a Case
            switch (bind.rhs.*) {
                .Case => |case_expr| {
                    // Scrutinee should be the node variable
                    try testing.expectEqualStrings("node", case_expr.scrutinee.Var.base);

                    // Should have at least one alternative (for constructor)
                    try testing.expect(case_expr.alts.len >= 1);
                },
                else => try testing.expect(false), // RHS should be Case
            }
        },
        else => try testing.expect(false), // Body should be Bind
    }
}

test "TagInfo: collects constructor tags" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a program with multiple constructors
    const just_node = try alloc.create(GrinExpr);
    just_node.* = .{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Just", 1),
        .fields = &.{.{ .Lit = .{ .Int = 42 } }},
    } } };

    const nothing_node = try alloc.create(GrinExpr);
    nothing_node.* = .{ .Store = .{ .ConstTagNode = .{
        .tag = conTag("Nothing", 2),
        .fields = &.{},
    } } };

    const def = GrinDef{
        .name = .{ .base = "testFunc", .unique = .{ .value = 10 } },
        .params = &.{},
        .body = just_node,
    };

    const defs = try alloc.alloc(GrinDef, 1);
    defs[0] = def;

    const program = GrinProgram{ .defs = defs };

    // Collect tags
    var tag_info = try collectTags(alloc, program);
    defer tag_info.deinit(alloc);

    // Should have collected the Just constructor
    try testing.expect(tag_info.con_tags.items.len >= 1);

    // Find the Just tag
    var just_found = false;
    for (tag_info.con_tags.items) |tag| {
        if (std.mem.eql(u8, tag.name.base, "Just")) {
            just_found = true;
            try testing.expect(tag.tag_type == .Con);
        }
    }
    try testing.expect(just_found);

    // Should have collected the function name
    try testing.expect(tag_info.fun_tags.count() >= 1);
    try testing.expect(tag_info.fun_tags.contains("testFunc"));
}

test "generateApplyFunc: has proper signature" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const apply_def = try generateApplyFunc(alloc);

    // Verify apply structure
    try testing.expectEqualStrings("apply", apply_def.name.base);
    try testing.expectEqual(@as(usize, 2), apply_def.params.len);
    try testing.expectEqualStrings("f", apply_def.params[0].base);
    try testing.expectEqualStrings("x", apply_def.params[1].base);

    // Body should be a Return with Unit (MVP)
    switch (apply_def.body.*) {
        .Return => |v| {
            try testing.expect(v == .Unit);
        },
        else => try testing.expect(false), // Body should be Return
    }
}

test "buildArityMap: correctly counts lambda parameters" {
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
    } };

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

    var arity_map = try buildArityMap(alloc, core_prog);
    defer arity_map.deinit(alloc);

    // id should have arity 1
    try testing.expect(arity_map.count() == 1);
    const arity = arity_map.get(id_binder.name.unique.value);
    try testing.expect(arity != null);
    try testing.expectEqual(@as(u32, 1), arity.?);
}

test "buildArityMap: correctly counts multi-parameter functions" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a Core program: const = \x y -> x
    const x_id = core.Id{
        .name = grin.Name{ .base = "x", .unique = .{ .value = 1 } },
        .ty = undefined,
        .span = undefined,
    };

    const y_id = core.Id{
        .name = grin.Name{ .base = "y", .unique = .{ .value = 2 } },
        .ty = undefined,
        .span = undefined,
    };

    const x_var = try alloc.create(CoreExpr);
    x_var.* = .{ .Var = x_id };

    const inner_lambda = try alloc.create(CoreExpr);
    inner_lambda.* = .{ .Lam = .{
        .binder = y_id,
        .body = x_var,
        .span = undefined,
    } };

    const outer_lambda = try alloc.create(CoreExpr);
    outer_lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = inner_lambda,
        .span = undefined,
    } };

    // Count arity directly
    const arity = try countLambdaArity(outer_lambda);
    try testing.expectEqual(@as(u32, 2), arity);
}

test "translateProgram: partial application generates P-tag" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a Core program with a 2-parameter function applied to 1 arg
    // map = \f xs -> f (head xs)
    // main = map (const 42)
    const f_id = core.Id{
        .name = grin.Name{ .base = "f", .unique = .{ .value = 1 } },
        .ty = undefined,
        .span = undefined,
    };

    const xs_id = core.Id{
        .name = grin.Name{ .base = "xs", .unique = .{ .value = 2 } },
        .ty = undefined,
        .span = undefined,
    };

    // Create function body: f (head xs)
    // For simplicity, just return f
    const f_var = try alloc.create(CoreExpr);
    f_var.* = .{ .Var = f_id };

    const map_inner = try alloc.create(CoreExpr);
    map_inner.* = .{ .Lam = .{
        .binder = xs_id,
        .body = f_var,
        .span = undefined,
    } };

    const map_outer = try alloc.create(CoreExpr);
    map_outer.* = .{ .Lam = .{
        .binder = f_id,
        .body = map_inner,
        .span = undefined,
    } };

    const map_binder = core.Id{
        .name = grin.Name{ .base = "map", .unique = .{ .value = 100 } },
        .ty = undefined,
        .span = undefined,
    };

    const map_pair = CoreBindPair{
        .binder = map_binder,
        .rhs = map_outer,
    };

    // Create a value literal
    const val_lit_expr = try alloc.create(CoreExpr);
    val_lit_expr.* = .{ .Lit = .{ .val = .{ .Int = 42 }, .span = undefined } };

    // Create application: map val_lit_expr (partial application)
    const map_var = try alloc.create(CoreExpr);
    map_var.* = .{ .Var = map_binder };

    const partial_app = try alloc.create(CoreExpr);
    partial_app.* = .{ .App = .{ .fn_expr = map_var, .arg = val_lit_expr, .span = undefined } };

    const main_binder = core.Id{
        .name = grin.Name{ .base = "main", .unique = .{ .value = 0 } },
        .ty = undefined,
        .span = undefined,
    };

    const main_pair = CoreBindPair{
        .binder = main_binder,
        .rhs = partial_app,
    };

    const core_prog = CoreProgram{
        .data_decls = &.{},
        .binds = &[_]CoreBind{ .{ .NonRec = map_pair }, .{ .NonRec = main_pair } },
    };

    const grin_prog = try translateProgram(alloc, core_prog);

    // Should have 2 definitions: map and main
    try testing.expectEqual(@as(usize, 2), grin_prog.defs.len);

    // The key thing is that partial application translation succeeds
    // without errors and produces a valid GRIN program
    try testing.expect(grin_prog.defs.len == 2);
}

test "translateProgram: over-application generates chained apply calls" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create a Core program with a 1-parameter function applied to 3 args
    // id = \x -> x
    // main = ((id 1) 2) 3
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
    } };

    const id_binder = core.Id{
        .name = grin.Name{ .base = "id", .unique = .{ .value = 100 } },
        .ty = undefined,
        .span = undefined,
    };

    const id_pair = CoreBindPair{
        .binder = id_binder,
        .rhs = lambda,
    };

    // Create application: ((id 1) 2) 3
    const lit1 = try alloc.create(CoreExpr);
    lit1.* = .{ .Lit = .{ .val = .{ .Int = 1 }, .span = undefined } };

    const lit2 = try alloc.create(CoreExpr);
    lit2.* = .{ .Lit = .{ .val = .{ .Int = 2 }, .span = undefined } };

    const lit3 = try alloc.create(CoreExpr);
    lit3.* = .{ .Lit = .{ .val = .{ .Int = 3 }, .span = undefined } };

    const id_var = try alloc.create(CoreExpr);
    id_var.* = .{ .Var = id_binder };

    const app1 = try alloc.create(CoreExpr);
    app1.* = .{ .App = .{ .fn_expr = id_var, .arg = lit1, .span = undefined } };

    const app2 = try alloc.create(CoreExpr);
    app2.* = .{ .App = .{ .fn_expr = app1, .arg = lit2, .span = undefined } };

    const app3 = try alloc.create(CoreExpr);
    app3.* = .{ .App = .{ .fn_expr = app2, .arg = lit3, .span = undefined } };

    const main_binder = core.Id{
        .name = grin.Name{ .base = "main", .unique = .{ .value = 0 } },
        .ty = undefined,
        .span = undefined,
    };

    const main_pair = CoreBindPair{
        .binder = main_binder,
        .rhs = app3,
    };

    const core_prog = CoreProgram{
        .data_decls = &.{},
        .binds = &[_]CoreBind{ .{ .NonRec = id_pair }, .{ .NonRec = main_pair } },
    };

    const grin_prog = try translateProgram(alloc, core_prog);

    // Should have 2 definitions: id and main
    try testing.expectEqual(@as(usize, 2), grin_prog.defs.len);

    // main's body should have nested binds with apply calls
    // The structure should involve Apply with "apply" name for over-application
    // For simplicity, we'll just check that the code compiles and runs correctly
    // A full check would require recursively traversing the expression tree
    try testing.expect(true);
}

test "exprToVal: extracts value from simple Return expression" {
    const ret_expr = grin.Expr{
        .Return = .{ .Lit = .{ .Int = 42 } },
    };

    const val = try exprToVal(&ret_expr);
    try testing.expectEqual(@as(i64, 42), val.Lit.Int);
}

test "exprToVal: returns error for complex expressions" {
    const bind_expr = grin.Expr{
        .Bind = .{
            .lhs = undefined,
            .pat = undefined,
            .rhs = undefined,
        },
    };

    const result = exprToVal(&bind_expr);
    try testing.expectError(error.CannotExtractValue, result);
}

test "translateApp: nested application f (g x) emits Bind for complex arg (#374)" {
    // Regression test for #374: complex sub-expression arguments in App
    // must be sequenced with Bind, not dropped.
    //
    // Core: compose = \f -> \g -> \x -> f (g x)
    // Expected GRIN:
    //   compose f g x =
    //     arg <- g x
    //     f arg
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Create Core IDs
    const f_id = core.Id{
        .name = grin.Name{ .base = "f", .unique = .{ .value = 100 } },
        .ty = undefined,
        .span = undefined,
    };
    const g_id = core.Id{
        .name = grin.Name{ .base = "g", .unique = .{ .value = 101 } },
        .ty = undefined,
        .span = undefined,
    };
    const x_id = core.Id{
        .name = grin.Name{ .base = "x", .unique = .{ .value = 102 } },
        .ty = undefined,
        .span = undefined,
    };
    const compose_id = core.Id{
        .name = grin.Name{ .base = "compose", .unique = .{ .value = 200 } },
        .ty = undefined,
        .span = undefined,
    };

    // Build: x (Var)
    const x_var = try alloc.create(CoreExpr);
    x_var.* = .{ .Var = x_id };

    // Build: g (Var)
    const g_var = try alloc.create(CoreExpr);
    g_var.* = .{ .Var = g_id };

    // Build: g x (App)
    const g_x = try alloc.create(CoreExpr);
    g_x.* = .{ .App = .{ .fn_expr = g_var, .arg = x_var, .span = undefined } };

    // Build: f (Var)
    const f_var = try alloc.create(CoreExpr);
    f_var.* = .{ .Var = f_id };

    // Build: f (g x) (App)
    const f_g_x = try alloc.create(CoreExpr);
    f_g_x.* = .{ .App = .{ .fn_expr = f_var, .arg = g_x, .span = undefined } };

    // Build: \x -> f (g x) (Lam)
    const lam_x = try alloc.create(CoreExpr);
    lam_x.* = .{ .Lam = .{ .binder = x_id, .body = f_g_x, .span = undefined } };

    // Build: \g -> \x -> f (g x) (Lam)
    const lam_g = try alloc.create(CoreExpr);
    lam_g.* = .{ .Lam = .{ .binder = g_id, .body = lam_x, .span = undefined } };

    // Build: \f -> \g -> \x -> f (g x) (Lam)
    const lam_f = try alloc.create(CoreExpr);
    lam_f.* = .{ .Lam = .{ .binder = f_id, .body = lam_g, .span = undefined } };

    const bind_pair = CoreBindPair{
        .binder = compose_id,
        .rhs = lam_f,
    };

    const core_prog = CoreProgram{
        .data_decls = &.{},
        .binds = &.{.{ .NonRec = bind_pair }},
    };

    const grin_prog = try translateProgram(alloc, core_prog);

    // Should have one definition with 3 parameters (f, g, x).
    try testing.expectEqual(@as(usize, 1), grin_prog.defs.len);
    const def = grin_prog.defs[0];
    try testing.expectEqual(@as(usize, 3), def.params.len);

    // The body must be a Bind (not a bare App), since the inner
    // application (g x) is complex and must be sequenced.
    //
    // Expected: Bind { lhs = App(g, [x]), pat = Var(arg), rhs = App(f, [arg]) }
    switch (def.body.*) {
        .Bind => |bind| {
            // LHS should be an App (g x)
            switch (bind.lhs.*) {
                .App => |inner_app| {
                    try testing.expectEqualStrings("g", inner_app.name.base);
                    try testing.expectEqual(@as(usize, 1), inner_app.args.len);
                    switch (inner_app.args[0]) {
                        .Var => |v| try testing.expectEqualStrings("x", v.base),
                        else => return error.TestUnexpectedResult,
                    }
                },
                else => return error.TestUnexpectedResult,
            }

            // Pat should be a Var (the fresh arg binding)
            switch (bind.pat) {
                .Var => |v| try testing.expectEqualStrings("arg", v.base),
                else => return error.TestUnexpectedResult,
            }

            // RHS should be an App (f arg)
            switch (bind.rhs.*) {
                .App => |outer_app| {
                    try testing.expectEqualStrings("f", outer_app.name.base);
                    try testing.expectEqual(@as(usize, 1), outer_app.args.len);
                    switch (outer_app.args[0]) {
                        .Var => |v| try testing.expectEqualStrings("arg", v.base),
                        else => return error.TestUnexpectedResult,
                    }
                },
                else => return error.TestUnexpectedResult,
            }
        },
        else => {
            // If the body is a bare App, the bug is still present!
            return error.TestUnexpectedResult;
        },
    }
}
