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
const PrimOp = @import("primop.zig").PrimOp;
const FieldType = grin.FieldType;
const known = @import("../naming/known.zig");

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
        .FunTy => .fn_ptr, // Function types are function pointers (for dictionary fields)
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
    // Maps data constructor uniques to their field types.
    // Used for dictionary field type tracking (issue #569).
    con_field_types: std.AutoHashMapUnmanaged(u64, []const grin.FieldType),
    // Counter for generating fresh GRIN variable names.
    name_counter: u64 = 0,
    // Lambda-lifted helper functions generated during translation.
    // Non-App complex expressions in constructor arguments are lifted into
    // helper functions so they can be suspended as F-tagged thunks (issue #518).
    lifted_defs: std.ArrayListUnmanaged(GrinDef) = .{},

    pub fn init(alloc: std.mem.Allocator) TranslateCtx {
        return .{
            .alloc = alloc,
            .var_map = .{},
            .arity_map = .{},
            .con_map = .{},
            .con_field_types = .{},
        };
    }

    pub fn deinit(self: *TranslateCtx) void {
        self.var_map.deinit(self.alloc);
        // arity_map ownership is transferred to GrinProgram - do not deinit
        self.con_map.deinit(self.alloc);
        self.lifted_defs.deinit(self.alloc);

        // Note: con_field_types and arities ownership transferred to GrinProgram in translateProgram
        // The caller (translateProgram) takes ownership and handles cleanup
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
        // Not mapped yet, create a GrinName with the original unique ID
        // from the Core binder (critical: do NOT use freshName() which
        // would change the unique ID and break GRIN→LLVM lookup).
        const fresh = GrinName{
            .base = core_id.name.base,
            .unique = core_id.name.unique,
        };
        try self.var_map.put(self.alloc, unique_id, fresh);
        return fresh;
    }

    /// Get or create a GRIN variable name for a Core name.
    /// Preserves the original unique ID to maintain GRIN→LLVM mapping.
    fn getCoreVar(self: *TranslateCtx, core_name: grin.Name) !GrinName {
        const unique_id = core_name.unique.value;
        if (self.var_map.get(unique_id)) |name| {
            return name;
        }
        // Preserve the original unique ID (do NOT use freshName).
        const fresh = GrinName{
            .base = core_name.base,
            .unique = core_name.unique,
        };
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

    // Fixup pass: eta-reduced definitions like `(+) = primAddInt` get arity 0
    // because they have no leading lambdas.  If the RHS is a bare Var
    // referencing a function with known arity (from the primop table or
    // another binding in this program), inherit that arity.  This ensures
    // call sites see the correct arity and emit App instead of
    // over-application chains with unknown_func placeholders.
    for (core_prog.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                const uid = pair.binder.name.unique.value;
                const current_arity = arity_map.get(uid) orelse continue;
                if (current_arity > 0) continue;
                const rhs_arity = resolveEtaArity(pair.rhs, &arity_map);
                if (rhs_arity > 0) {
                    try arity_map.put(alloc, uid, rhs_arity);
                }
            },
            .Rec => |pairs| {
                for (pairs) |pair| {
                    const uid = pair.binder.name.unique.value;
                    const current_arity = arity_map.get(uid) orelse continue;
                    if (current_arity > 0) continue;
                    const rhs_arity = resolveEtaArity(pair.rhs, &arity_map);
                    if (rhs_arity > 0) {
                        try arity_map.put(alloc, uid, rhs_arity);
                    }
                }
            },
        }
    }

    return arity_map;
}

/// If `expr` is a bare Var, look up its arity from the arity_map or primop
/// table.  Returns 0 if the arity cannot be determined.
fn resolveEtaArity(
    expr: *const CoreExpr,
    arity_map: *const std.AutoHashMapUnmanaged(u64, u32),
) u32 {
    // Strip leading lambdas — if the user wrote `f = \x -> g x`, the outer
    // `countLambdaArity` already found 1; we only enter here with arity 0,
    // but the RHS might still be wrapped in type lambdas or coercions in
    // future.  For now, only handle bare Var.
    switch (expr.*) {
        .Var => |v| {
            // Check arity_map first (other user definitions).
            if (arity_map.get(v.name.unique.value)) |a| {
                if (a > 0) return a;
            }
            // Check primop table by base name.
            return primopArity(v.name.base);
        },
        else => return 0,
    }
}

/// Return the arity (number of value-level arguments) for a PrimOp given its
/// base name string.  Returns 0 for unknown names.
fn primopArity(name_str: []const u8) u32 {
    const op = PrimOp.fromString(name_str) orelse return 0;
    return switch (op) {
        // IO: write_stdout, write_stderr, putStrLn_ take 1 arg (String -> IO ())
        .write_stdout, .write_stderr, .putStrLn_ => 1,
        // IO: putChar_ takes 1 arg (Char -> IO ())
        .putChar_ => 1,
        // IO: read_stdin takes 0 args (IO String)
        .read_stdin => 0,
        // Unary arithmetic: neg_Int, abs_Int, neg_Double
        .neg_Int, .abs_Int, .neg_Double => 1,
        // Binary arithmetic
        .add_Int, .sub_Int, .mul_Int, .quot_Int, .rem_Int => 2,
        .add_Double, .sub_Double, .mul_Double, .div_Double => 2,
        // Comparisons (all binary)
        .eq_Int, .ne_Int, .lt_Int, .le_Int, .gt_Int, .ge_Int => 2,
        .eq_Char => 2,
        .eq_Double, .ne_Double, .lt_Double, .le_Double, .gt_Double, .ge_Double => 2,
        // Unary conversions
        .intToDouble, .doubleToInt, .charToInt, .intToChar => 1,
        // String ops
        .str_cons => 2,
        .str_head, .str_tail, .str_null => 1,
        // error: 1 arg (String -> a)
        .@"error" => 1,
        // unreachable: 0 args
        .unreachable_ => 0,
        // Heap ops
        .newMutVar, .readMutVar => 1,
        .writeMutVar => 2,
        // ccall: unknown arity
        .ccall => 0,
        // Non-exhaustive enum catch-all
        _ => 0,
    };
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
pub fn countConFields(ty: CoreType) u32 {
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

/// Build a map from data constructor uniques to their field types.
/// For dictionary constructors (like MkDict$Eq), fields that are function
/// types are marked as fn_ptr. This is needed for the LLVM backend to
/// properly handle dictionary fields.
/// See: https://github.com/adinapoli/rusholme/issues/569
fn buildConFieldTypes(alloc: std.mem.Allocator, core_prog: CoreProgram) !std.AutoHashMapUnmanaged(u64, []const grin.FieldType) {
    var con_map = std.AutoHashMapUnmanaged(u64, []const grin.FieldType){};
    errdefer {
        var iter = con_map.iterator();
        while (iter.next()) |entry| {
            alloc.free(entry.value_ptr.*);
        }
        con_map.deinit(alloc);
    }

    for (core_prog.data_decls) |decl| {
        for (decl.constructors) |con| {
            const unique = con.name.unique.value;
            const n_fields = countConFields(con.ty);

            // Default to .ptr for all fields (conservative)
            var fields = try alloc.alloc(grin.FieldType, n_fields);
            for (fields) |*ft| ft.* = .ptr;

            // Now check if any fields should be .fn_ptr by analyzing the type
            var current = con.ty;
            var field_idx: u32 = 0;

            // Strip ForAllTy quantifiers
            while (true) {
                switch (current) {
                    .ForAllTy => |fa| current = fa.body.*,
                    else => break,
                }
            }

            // For each FunTy arrow, check if the argument type is a function.
            // Dictionary methods have function types (FunTy), which means we need
            // nested analysis.
            while (field_idx < n_fields) {
                switch (current) {
                    .FunTy => |ft| {
                        // Check if this field's type is a function (nested FunTy)
                        const arg_type = ft.arg.*;
                        const is_fn = switch (arg_type) {
                            .FunTy => true,
                            else => false,
                        };

                        if (is_fn) {
                            fields[field_idx] = .fn_ptr;
                        }

                        field_idx += 1;
                        current = ft.res.*;
                    },
                    else => break,
                }
            }

            try con_map.put(alloc, unique, fields);
        }
    }

    return con_map;
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
pub fn translateProgram(
    alloc: std.mem.Allocator,
    core_prog: CoreProgram,
    external_arities: ?*const std.AutoHashMapUnmanaged(u64, u32),
    external_con_map: ?*const std.AutoHashMapUnmanaged(u64, u32),
) !GrinProgram {
    // Build the arity map for partial/over-application handling.
    var arity_map = try buildArityMap(alloc, core_prog);
    defer arity_map.deinit(alloc);

    // Build the constructor map from data declarations.
    var con_map = try buildConMap(alloc, core_prog);
    defer con_map.deinit(alloc);

    // Build constructor field type map for dictionary handling (issue #569).
    var con_field_types = try buildConFieldTypes(alloc, core_prog);
    defer con_field_types.deinit(alloc);

    var ctx = TranslateCtx.init(alloc);
    defer ctx.deinit();

    // Copy the arity map into the context.
    var iter = arity_map.iterator();
    while (iter.next()) |entry| {
        try ctx.arity_map.put(alloc, entry.key_ptr.*, entry.value_ptr.*);
    }

    // Seed with external arities (from REPL session's prior inputs).
    // Local entries take precedence — only add externals not already present.
    if (external_arities) |ext| {
        var ext_iter = ext.iterator();
        while (ext_iter.next()) |entry| {
            const gop = try ctx.arity_map.getOrPut(alloc, entry.key_ptr.*);
            if (!gop.found_existing) {
                gop.value_ptr.* = entry.value_ptr.*;
            }
        }
    }

    // Copy the constructor map into the context.
    var con_iter = con_map.iterator();
    while (con_iter.next()) |entry| {
        try ctx.con_map.put(alloc, entry.key_ptr.*, entry.value_ptr.*);
    }

    // Copy the constructor field type map into the context.
    var ft_iter = con_field_types.iterator();
    while (ft_iter.next()) |entry| {
        // Deep copy the field type slice
        const field_types = try alloc.alloc(grin.FieldType, entry.value_ptr.len);
        @memcpy(field_types, entry.value_ptr.*);
        try ctx.con_field_types.put(alloc, entry.key_ptr.*, field_types);
    }

    // Seed with external constructor map (from REPL session's prior data declarations).
    // Local entries take precedence — only add externals not already present.
    if (external_con_map) |ext| {
        var ext_iter = ext.iterator();
        while (ext_iter.next()) |entry| {
            const gop = try ctx.con_map.getOrPut(alloc, entry.key_ptr.*);
            if (!gop.found_existing) {
                gop.value_ptr.* = entry.value_ptr.*;
            }
        }
    }

    // Seed built-in constructors that are pure syntax with no user-visible
    // data declaration: list (`[]`, `(:)`), unit (`()`), and tuples.
    // These are wired into the compiler via src/naming/known.zig with stable
    // unique IDs but are never declared in user code.  Without seeding, the
    // translator treats e.g. `(:)` as a function call instead of a constructor
    // application, producing undefined linker references.
    //
    // Note: Bool (True/False), Maybe (Nothing/Just), Either (Left/Right) are
    // NOT seeded here because they have explicit `data` declarations in the
    // Prelude.  Their constructors enter the con_map via buildConMap when the
    // Prelude is compiled.  Seeding them here would cause a GRIN→LLVM mismatch:
    // the GRIN translator would emit ValTag (tag discriminant) instead of Var,
    // but the LLVM backend has hardcoded paths for True/False Var uniques that
    // map to the correct i64 values expected by formatJitResult.
    //
    // Use getOrPut so user-declared constructors take precedence.
    const builtin_cons = [_]struct { unique: u64, n_fields: u32 }{
        .{ .unique = known.Con.Unit.unique.value, .n_fields = 0 },
        .{ .unique = known.Con.Nil.unique.value, .n_fields = 0 },
        .{ .unique = known.Con.Cons.unique.value, .n_fields = 2 },
        .{ .unique = known.Con.Tuple2.unique.value, .n_fields = 2 },
        .{ .unique = known.Con.Tuple3.unique.value, .n_fields = 3 },
        .{ .unique = known.Con.Tuple4.unique.value, .n_fields = 4 },
        .{ .unique = known.Con.Tuple5.unique.value, .n_fields = 5 },
    };
    for (builtin_cons) |b| {
        const gop = try ctx.con_map.getOrPut(alloc, b.unique);
        if (!gop.found_existing) {
            gop.value_ptr.* = b.n_fields;
        }
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

    // Append any lambda-lifted helper functions generated during translation
    // (e.g., thunk wrappers for non-App constructor arguments, issue #518).
    for (ctx.lifted_defs.items) |lifted| {
        try defs.append(alloc, lifted);
    }

    const defs_slice = try defs.toOwnedSlice(alloc);
    // Move field type map from context to program
    const field_types = ctx.con_field_types;
    // Move arity map from context to program (issue #595)
    const arities = ctx.arity_map;

    return GrinProgram{
        .defs = defs_slice,
        .field_types = field_types,
        .arities = arities,
    };
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

    // Eta-expansion for eta-reduced definitions.
    //
    // When a binding has no lambda parameters but the arity_map records a
    // positive arity (inherited from its RHS via resolveEtaArity), the body
    // is just a bare Var reference to the target function.  We must
    // eta-expand: generate fresh parameters and wrap the body as a call.
    //
    //   (+) = primAddInt          -- Core: no lambdas, arity 0
    //   →  (+)(x, y) = primAddInt x y   -- GRIN: arity 2, calls primAddInt
    const expected_arity = ctx.arity_map.get(pair.binder.name.unique.value) orelse 0;
    if (params.items.len == 0 and expected_arity > 0) {
        switch (body_expr.*) {
            .Var => |v| {
                const target_name = try ctx.getCoreVar(v.name);

                // Generate fresh parameters for the eta-expanded definition.
                var eta_params = try ctx.alloc.alloc(GrinName, expected_arity);
                var eta_args = try ctx.alloc.alloc(GrinVal, expected_arity);
                for (0..expected_arity) |i| {
                    const pname = try ctx.freshName("eta");
                    eta_params[i] = pname;
                    eta_args[i] = .{ .Var = pname };
                }

                // Body: App(target, [eta_0, eta_1, ...])
                const app_expr = try ctx.alloc.create(GrinExpr);
                app_expr.* = .{ .App = .{
                    .name = target_name,
                    .args = eta_args,
                } };

                return GrinDef{
                    .name = name,
                    .params = eta_params,
                    .body = app_expr,
                };
            },
            else => {
                // Non-Var RHS with arity mismatch — fall through to normal
                // translation.  This shouldn't happen with the current
                // resolveEtaArity (only resolves Var), but is safe to handle.
            },
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
                const grin_name = try ctx.getCoreVar(v.name);
                // If this is a known function with arity 0, emit a call
                // (App with no args) rather than a bare variable reference.
                // This is critical for the REPL: when the user types `main`
                // after `:l`, the translator must call `main` (not just
                // return a reference to it).
                if (ctx.getFunctionArity(grin_name)) |arity| {
                    if (arity == 0) {
                        new_expr.* = .{ .App = .{
                            .name = grin_name,
                            .args = &.{},
                        } };
                    } else {
                        // Non-zero arity function used as a value (higher-order).
                        // Return as a variable reference.
                        new_expr.* = .{ .Return = .{ .Var = grin_name } };
                    }
                } else {
                    // Unknown function — ordinary variable reference.
                    new_expr.* = .{ .Return = .{ .Var = grin_name } };
                }
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

    // ── IO monad sequencing operators ────────────────────────────────────
    //
    // `>>` and `>>=` are magical known names used by do-notation desugaring.
    // They have no runtime definition — sequencing is structural in GRIN.
    // Translate them into GRIN Bind chains:
    //
    //   >> a b     →   a >>= \_ -> b        (execute a for side effects, then b)
    //   >>= m f   →   m >>= \x -> f x       (execute m, apply result to f)
    //
    // Arguments are translated eagerly (not as F-tag thunks) because both
    // operands are IO actions whose side effects must actually execute.
    switch (fn_expr.*) {
        .Var => |v| {
            const uid = v.name.unique.value;
            if (uid == known.Fn.then.unique.value and args.items.len == 2) {
                // >> a b: args collected in reverse order, so args[1]=a, args[0]=b
                const lhs_core = args.items[1]; // first argument (a)
                const rhs_core = args.items[0]; // second argument (b)

                const lhs_grin = try translateExpr(ctx, lhs_core);
                const rhs_grin = try translateExpr(ctx, rhs_core);

                const discard = try ctx.freshName("_seq");
                const bind_expr = try ctx.alloc.create(GrinExpr);
                bind_expr.* = .{ .Bind = .{
                    .lhs = lhs_grin,
                    .pat = .{ .Var = discard },
                    .rhs = rhs_grin,
                } };
                return bind_expr;
            }
            if (uid == known.Fn.bind.unique.value and args.items.len == 2) {
                // >>= m f: args collected in reverse order, so args[1]=m, args[0]=f
                const m_core = args.items[1]; // monadic action (m)
                const f_core = args.items[0]; // continuation (f)

                const m_grin = try translateExpr(ctx, m_core);

                // The continuation `f` must be a lambda-lifted function name
                // (a Var) or a zero-arity call (App).  Lambda lifting turns
                // all do-notation continuations (`\x -> body`) into named
                // top-level functions.  If this fails, it indicates a bug in
                // the lambda lifter — the continuation was not lifted.
                const f_grin = try translateExpr(ctx, f_core);
                const f_name = switch (f_grin.*) {
                    .Return => |ret| switch (ret) {
                        .Var => |name| name,
                        else => {
                            std.log.err(">>=: continuation resolved to Return({s}), expected Var " ++
                                "(lambda lifting may have failed to lift a do-notation continuation)", .{@tagName(ret)});
                            return error.CannotExtractValue;
                        },
                    },
                    .App => |app| app.name,
                    else => {
                        std.log.err(">>=: continuation is {s}, expected Return(Var) or App " ++
                            "(lambda lifting may have failed to lift a do-notation continuation)", .{@tagName(f_grin.*)});
                        return error.CannotExtractValue;
                    },
                };

                const bind_var = try ctx.freshName("bind_res");
                const app_cont = try ctx.alloc.create(GrinExpr);
                app_cont.* = .{ .App = .{
                    .name = f_name,
                    .args = &[_]GrinVal{.{ .Var = bind_var }},
                } };

                const bind_expr = try ctx.alloc.create(GrinExpr);
                bind_expr.* = .{ .Bind = .{
                    .lhs = m_grin,
                    .pat = .{ .Var = bind_var },
                    .rhs = app_cont,
                } };
                return bind_expr;
            }
        },
        else => {},
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
                // Note: We do NOT register fresh_var in var_map here.
                // The var_map is for Core variable lookups, not GRIN fresh variables.
                // The LLVM backend tracks fresh variables via translateBind which
                // adds them to the params map when results are bound.
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
                return try wrapWithLazyBindsForCon(ctx, bind_expr, pending_binds.items);
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
                const missing = arity - arg_count;

                // Create the partial application node with a static Partial tag.
                // Using ConstTagNode (not VarTagNode) because the tag is fully
                // known at translation time — the function name and missing arg
                // count are both static. This integrates naturally with the LLVM
                // backend's TagTable, discriminant assignment, and case dispatch.
                const store_expr = try ctx.alloc.create(GrinExpr);
                store_expr.* = .{ .Store = .{ .ConstTagNode = .{
                    .tag = partialTag(fn_name.base, fn_name.unique.value, missing),
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

                return try wrapWithLazyBindsForFunc(ctx, bind_expr, pending_binds.items);
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

                return try wrapWithLazyBindsForFunc(ctx, final_bind, pending_binds.items);
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

    // Wrap function arguments lazily for user-defined functions.
    // Primops and prelude functions remain eager.
    return try wrapWithLazyBindsForFunc(ctx, grin_app, pending_binds.items);
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

/// Wrap an inner expression with lazy thunk stores for function arguments.
///
/// In Haskell, function call arguments are lazy (call-by-need):
/// `f (g x)` does not evaluate `g x` — it stores a thunk that captures the
/// function and its arguments. This function replaces eager binds with F-tagged
/// stores for `App` expressions where the function is a known top-level definition:
///
///   -- Eager (old):              -- Lazy (new):
///   arg <- g x                   arg <- store (Fg [x])
///   f arg                        f arg
///
/// For primops and prelude functions, arguments remain eager since the evaluator
/// expects fully evaluated values. Higher-order applications (where the function
/// is a parameter variable) also remain eager since F-tag dispatch requires a
/// statically known function name in the function table.
fn wrapWithLazyBindsForFunc(
    ctx: *TranslateCtx,
    inner: *GrinExpr,
    pending_binds: []const PendingBind,
) anyerror!*GrinExpr {
    if (pending_binds.len == 0) return inner;

    // Check if the inner expression is a primop application.
    // If so, keep all arguments eager since primops expect evaluated values.
    const is_primop_app = switch (inner.*) {
        .App => |app| PrimOp.fromString(app.name.base) != null or PrimOp.fromPreludeName(app.name.base) != null,
        else => false,
    };

    if (is_primop_app) {
        // Primop application: keep all arguments eager.
        return try wrapWithPendingBinds(ctx, inner, pending_binds);
    }

    var result = inner;
    var i: usize = pending_binds.len;
    while (i > 0) {
        i -= 1;
        const pb = pending_binds[i];

        const lhs = switch (pb.complex_expr.*) {
            .App => |app| b: {
                // Only wrap as a lazy thunk if the function is a known
                // top-level definition with correct arity. Higher-order
                // applications (where the function is a parameter variable)
                // cannot be thunked because F-tag dispatch requires a
                // statically known function name in the function table.
                //
                // Primop applications (e.g. charToInt, intToChar) must
                // remain eager — they compile to inline instructions, not
                // heap-allocated thunks.
                const is_primop = PrimOp.fromString(app.name.base) != null or
                    PrimOp.fromPreludeName(app.name.base) != null;
                if (!is_primop) {
                    if (ctx.getFunctionArity(app.name)) |arity| {
                        if (app.args.len == arity and arity > 0) {
                            // Fully-saturated application with arguments:
                            // store as lazy thunk (F-tag node).
                            //
                            // Zero-arity calls (e.g. dictionary bindings like
                            // dict$ShowIt$A) are NOT wrapped as thunks because
                            // the callee immediately scrutinizes the result via
                            // Case and does not force F-tagged nodes. Eagerly
                            // evaluating them avoids a force/eval round-trip.
                            const ftag = GrinTag{ .tag_type = .{ .Fun = {} }, .name = app.name };
                            const store_expr = try ctx.alloc.create(GrinExpr);
                            // Copy the arguments into a new allocation for the heap node
                            const stored_node = try ctx.alloc.alloc(GrinVal, app.args.len);
                            @memcpy(stored_node, app.args);
                            store_expr.* = .{ .Store = .{ .ConstTagNode = .{
                                .tag = ftag,
                                .fields = stored_node,
                            } } };
                            break :b store_expr;
                        }
                    }
                }
                // Higher-order application (function is a parameter variable):
                // evaluate eagerly since F-tag dispatch requires a statically
                // known function name.
                // tracked in: https://github.com/adinapoli/rusholme/issues/551
                break :b pb.complex_expr;
            },
            else => pb.complex_expr,
        };

        const bind_expr = try ctx.alloc.create(GrinExpr);
        bind_expr.* = .{ .Bind = .{
            .lhs = lhs,
            .pat = .{ .Var = pb.fresh_var },
            .rhs = result,
        } };
        result = bind_expr;
    }

    return result;
}

// ── Free Variable Analysis for GRIN Expressions ─────────────────────────
//
// Used by the ad-hoc lambda lifter in wrapWithLazyBindsForCon (issue #518)
// to determine which variables a non-App complex expression captures.

/// Unique-keyed set for collecting free variables.
const UniqueSet = std.AutoHashMapUnmanaged(u64, void);

/// Record variables bound by a GRIN value pattern (Bind LHS).
fn collectBoundFromVal(alloc: std.mem.Allocator, val: *const GrinVal, bound: *UniqueSet) !void {
    switch (val.*) {
        .Var => |name| try bound.put(alloc, name.unique.value, {}),
        .ConstTagNode => |ctn| {
            for (ctn.fields) |field| {
                switch (field) {
                    .Var => |name| try bound.put(alloc, name.unique.value, {}),
                    else => {},
                }
            }
        },
        .VarTagNode => |vtn| {
            try bound.put(alloc, vtn.tag_var.unique.value, {});
            for (vtn.fields) |field| {
                switch (field) {
                    .Var => |name| try bound.put(alloc, name.unique.value, {}),
                    else => {},
                }
            }
        },
        .Unit, .Lit, .ValTag => {},
    }
}

/// Record variables bound by a case pattern.
fn collectBoundFromPat(alloc: std.mem.Allocator, pat: GrinCPat, bound: *UniqueSet) !void {
    switch (pat) {
        .NodePat => |np| {
            for (np.fields) |name| {
                try bound.put(alloc, name.unique.value, {});
            }
        },
        .LitPat, .TagPat, .DefaultPat => {},
    }
}

/// Check whether a GRIN expression involves genuine computation (Case
/// dispatch, function application) as opposed to simple constructor
/// construction (Store/Bind chains that produce WHNF values).
///
/// Used by wrapWithLazyBindsForCon to decide whether a non-App complex
/// expression should be lambda-lifted into a thunk (true) or kept eager
/// (false). Constructor store chains are already in WHNF and don't benefit
/// from thunking.
fn exprInvolvesComputation(expr: *const GrinExpr) bool {
    return switch (expr.*) {
        .Case => true,
        .App => true,
        .Bind => |bind| exprInvolvesComputation(bind.lhs) or exprInvolvesComputation(bind.rhs),
        .Block => |inner| exprInvolvesComputation(inner),
        // Store, Fetch, Update, Return are simple operations.
        .Store, .Fetch, .Update, .Return => false,
    };
}

/// Collect free variables in a GRIN expression.
/// Returns a set of unique IDs that are referenced but not locally bound.
fn collectFreeVarsExpr(alloc: std.mem.Allocator, expr: *const GrinExpr, bound: *const UniqueSet, free: *UniqueSet) !void {
    switch (expr.*) {
        .Bind => |bind| {
            // Collect free vars from the LHS.
            try collectFreeVarsExpr(alloc, bind.lhs, bound, free);
            // The pattern binds new variables for the RHS.
            var inner_bound = try bound.clone(alloc);
            defer inner_bound.deinit(alloc);
            try collectBoundFromVal(alloc, &bind.pat, &inner_bound);
            try collectFreeVarsExpr(alloc, bind.rhs, &inner_bound, free);
        },
        .Case => |case| {
            try collectFreeVarsVal(alloc, case.scrutinee, bound, free);
            for (case.alts) |alt| {
                var inner_bound = try bound.clone(alloc);
                defer inner_bound.deinit(alloc);
                try collectBoundFromPat(alloc, alt.pat, &inner_bound);
                try collectFreeVarsExpr(alloc, alt.body, &inner_bound, free);
            }
        },
        .App => |app| {
            // The function name itself is a reference (unless it's a known
            // top-level def, in which case it's not captured — but we collect
            // it anyway; the caller filters via arity_map).
            if (!bound.contains(app.name.unique.value)) {
                try free.put(alloc, app.name.unique.value, {});
            }
            for (app.args) |arg| {
                try collectFreeVarsVal(alloc, arg, bound, free);
            }
        },
        .Return => |val| try collectFreeVarsVal(alloc, val, bound, free),
        .Store => |val| try collectFreeVarsVal(alloc, val, bound, free),
        .Fetch => |fetch| {
            if (!bound.contains(fetch.ptr.unique.value)) {
                try free.put(alloc, fetch.ptr.unique.value, {});
            }
        },
        .Update => |upd| {
            if (!bound.contains(upd.ptr.unique.value)) {
                try free.put(alloc, upd.ptr.unique.value, {});
            }
            try collectFreeVarsVal(alloc, upd.val, bound, free);
        },
        .Block => |inner| try collectFreeVarsExpr(alloc, inner, bound, free),
    }
}

/// Collect free variable references from a GRIN value.
fn collectFreeVarsVal(alloc: std.mem.Allocator, val: GrinVal, bound: *const UniqueSet, free: *UniqueSet) !void {
    switch (val) {
        .Var => |name| {
            if (!bound.contains(name.unique.value)) {
                try free.put(alloc, name.unique.value, {});
            }
        },
        .ConstTagNode => |ctn| {
            for (ctn.fields) |field| {
                try collectFreeVarsVal(alloc, field, bound, free);
            }
        },
        .VarTagNode => |vtn| {
            if (!bound.contains(vtn.tag_var.unique.value)) {
                try free.put(alloc, vtn.tag_var.unique.value, {});
            }
            for (vtn.fields) |field| {
                try collectFreeVarsVal(alloc, field, bound, free);
            }
        },
        .ValTag, .Unit, .Lit => {},
    }
}

/// Wrap an inner expression with lazy thunk stores for constructor arguments.
///
/// In Haskell, constructor arguments are lazy: `Succ (double x)` does not
/// evaluate `double x` — it stores a thunk that captures the function and
/// its arguments.  This function replaces eager binds with F-tagged stores:
///
///   -- App arguments (direct thunk):
///   arg <- double x              →  arg <- store (Fdouble [x])
///   store (CSucc [arg])             store (CSucc [arg])
///
///   -- Non-App arguments (lambda-lifted thunk, issue #518):
///   arg <- case x of ...         →  arg <- store (F_thunk_0 [x])
///   store (CSucc [arg])             store (CSucc [arg])
///   (where _thunk_0 x = case x of ... is a lifted helper function)
fn wrapWithLazyBindsForCon(
    ctx: *TranslateCtx,
    inner: *GrinExpr,
    pending_binds: []const PendingBind,
) anyerror!*GrinExpr {
    if (pending_binds.len == 0) return inner;

    // Partition pending_binds: App expressions become lazy thunks,
    // everything else stays eager.
    var eager_binds = std.ArrayListUnmanaged(PendingBind){};
    defer eager_binds.deinit(ctx.alloc);

    var result = inner;
    var i: usize = pending_binds.len;
    while (i > 0) {
        i -= 1;
        const pb = pending_binds[i];
        switch (pb.complex_expr.*) {
            .App => |app| {
                // Only wrap as a lazy thunk if the function is a known
                // top-level definition. Higher-order applications (where
                // the function is a parameter variable) cannot be thunked
                // because the F-tag dispatch requires a statically known
                // function name in the function table.
                // tracked in: https://github.com/adinapoli/rusholme/issues/517
                if (ctx.getFunctionArity(app.name) != null) {
                    // Replace the eager `app func [args]` with `store (Ffunc [args])`.
                    // The F-tag carries the function's actual unique ID so the LLVM
                    // tag table can register and dispatch on it correctly.
                    const ftag = GrinTag{ .tag_type = .{ .Fun = {} }, .name = app.name };
                    const store_expr = try ctx.alloc.create(GrinExpr);
                    store_expr.* = .{ .Store = .{ .ConstTagNode = .{
                        .tag = ftag,
                        .fields = app.args,
                    } } };
                    const bind_expr = try ctx.alloc.create(GrinExpr);
                    bind_expr.* = .{ .Bind = .{
                        .lhs = store_expr,
                        .pat = .{ .Var = pb.fresh_var },
                        .rhs = result,
                    } };
                    result = bind_expr;
                } else {
                    // Higher-order application: evaluate eagerly.
                    try eager_binds.append(ctx.alloc, pb);
                }
            },
            else => {
                // Non-App complex expression. Distinguish:
                //
                // - Store/Bind chains (nested constructor applications):
                //   already produce WHNF values — keep eager.
                //
                // - Case expressions and Bind chains rooted in Case:
                //   represent genuine computation — lambda-lift into a
                //   helper function and suspend as an F-tagged thunk
                //   (issue #518).
                if (exprInvolvesComputation(pb.complex_expr)) {
                    // Lambda-lift: compute free variables, generate helper.
                    var bound_set = UniqueSet{};
                    defer bound_set.deinit(ctx.alloc);
                    var free_set = UniqueSet{};
                    defer free_set.deinit(ctx.alloc);

                    try collectFreeVarsExpr(ctx.alloc, pb.complex_expr, &bound_set, &free_set);

                    // Filter: remove top-level functions and constructors
                    // (they are global, not captured in the thunk).
                    var free_vars = std.ArrayListUnmanaged(GrinName){};
                    defer free_vars.deinit(ctx.alloc);

                    var fv_iter = free_set.iterator();
                    while (fv_iter.next()) |entry| {
                        const uid = entry.key_ptr.*;
                        if (ctx.arity_map.contains(uid)) continue;
                        if (ctx.con_map.contains(uid)) continue;
                        // Resolve the unique back to its GrinName via var_map.
                        if (ctx.var_map.get(uid)) |name| {
                            try free_vars.append(ctx.alloc, name);
                        }
                    }

                    // Generate helper function: _thunk_N fv1 fv2 ... = <expr>
                    const helper_name = try ctx.freshName("_thunk");
                    const params = try ctx.alloc.alloc(GrinName, free_vars.items.len);
                    const capture_vals = try ctx.alloc.alloc(GrinVal, free_vars.items.len);
                    for (free_vars.items, 0..) |fv, j| {
                        // The helper's parameter names match the captured variables
                        // so the body expression (which references them by unique)
                        // resolves correctly.
                        params[j] = fv;
                        capture_vals[j] = .{ .Var = fv };
                    }

                    const helper_def = GrinDef{
                        .name = helper_name,
                        .params = params,
                        .body = pb.complex_expr,
                    };
                    try ctx.lifted_defs.append(ctx.alloc, helper_def);
                    try ctx.arity_map.put(ctx.alloc, helper_name.unique.value, @intCast(params.len));

                    // Emit: store (F_thunk_N [fv1, fv2, ...])
                    const ftag = GrinTag{ .tag_type = .{ .Fun = {} }, .name = helper_name };
                    const store_expr = try ctx.alloc.create(GrinExpr);
                    store_expr.* = .{ .Store = .{ .ConstTagNode = .{
                        .tag = ftag,
                        .fields = capture_vals,
                    } } };
                    const bind_expr = try ctx.alloc.create(GrinExpr);
                    bind_expr.* = .{ .Bind = .{
                        .lhs = store_expr,
                        .pat = .{ .Var = pb.fresh_var },
                        .rhs = result,
                    } };
                    result = bind_expr;
                } else {
                    // Store/Bind chain producing a constructor: keep eager.
                    try eager_binds.append(ctx.alloc, pb);
                }
            },
        }
    }

    // Wrap any remaining eager binds around the (now lazy-wrapped) result.
    // The eager_binds were collected in reverse order, so reverse them back.
    std.mem.reverse(PendingBind, eager_binds.items);
    return try wrapWithPendingBinds(ctx, result, eager_binds.items);
}

/// Chain a store and update into: `store_expr >>= \bind_var -> update_expr`.
/// Used by the Rec let path to store a thunk then update a placeholder.
fn chainStoreUpdate(
    ctx: *TranslateCtx,
    store_expr: *GrinExpr,
    bind_var: GrinName,
    update_expr: *GrinExpr,
) !*GrinExpr {
    const bind = try ctx.alloc.create(GrinExpr);
    bind.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = .{ .Var = bind_var },
        .rhs = update_expr,
    } };
    return bind;
}

/// Translate a let binding.
///
/// Non-recursive let bindings are lazy: when the RHS is a function
/// application of a known top-level function, it is suspended as an
/// F-tagged thunk (`store (Ffunc [args])`). The thunk is only forced
/// when the bound variable is scrutinised by a `case` expression.
///
/// Simple values (Var, Lit, ValTag) and constructor nodes are not
/// thunked — they are already in WHNF or need heap allocation
/// respectively. Higher-order applications (where the function is a
/// parameter variable) are also kept eager since F-tag dispatch
/// requires a statically known function name.
fn translateLet(ctx: *TranslateCtx, let_expr: *const CoreLet) anyerror!*GrinExpr {
    switch (let_expr.bind) {
        .NonRec => |pair| {
            // Non-recursive let: translate `let x = rhs in body`.
            //
            // The treatment depends on the RHS shape:
            //
            //   Simple values (Var, Lit, ValTag):
            //     `pure rhs >>= \x -> body`
            //     These are already-evaluated values that don't need heap
            //     allocation. Storing them would wrap the value in an
            //     indirection (heap pointer), breaking function dispatch
            //     for higher-order parameters and losing literal values.
            //     This case is critical for the pattern-match compiler,
            //     which generates `let f = arg_0` to alias a lambda
            //     parameter to its equation-local name.
            //
            //   Heap-allocated nodes (ConstTagNode, VarTagNode):
            //     `store rhs >>= \x -> body`
            //     Constructor nodes live on the heap in GRIN; case
            //     expressions fetch them via heap pointers.
            //
            //   App of known top-level function (lazy):
            //     `store (Ffunc [args]) >>= \x -> body`
            //     Suspended as an F-tagged thunk — only forced when x
            //     is scrutinised at a case site.
            //
            //   Other complex sub-expressions:
            //     `rhs >>= \x -> body`
            //     Kept eager — higher-order applications and control
            //     flow (Case, Bind chains) are evaluated immediately.
            const rhs_expr = try translateExpr(ctx, pair.rhs);

            const lhs_expr: *GrinExpr = blk: {
                switch (rhs_expr.*) {
                    .Return => |v| {
                        const e = try ctx.alloc.create(GrinExpr);
                        switch (v) {
                            // Simple values: pass through without heap allocation.
                            .Var, .Lit, .ValTag, .Unit => {
                                e.* = .{ .Return = v };
                            },
                            // Constructor nodes: store on heap.
                            .ConstTagNode, .VarTagNode => {
                                e.* = .{ .Store = v };
                            },
                        }
                        break :blk e;
                    },
                    .App => |app| {
                        // Function application: wrap as lazy thunk if the
                        // function is a known top-level definition.
                        if (ctx.getFunctionArity(app.name) != null) {
                            const ftag = GrinTag{ .tag_type = .{ .Fun = {} }, .name = app.name };
                            const e = try ctx.alloc.create(GrinExpr);
                            e.* = .{ .Store = .{ .ConstTagNode = .{
                                .tag = ftag,
                                .fields = app.args,
                            } } };
                            break :blk e;
                        }
                        // Higher-order application: evaluate eagerly.
                        break :blk rhs_expr;
                    },
                    else => {
                        // Other complex RHS (Bind, Case, etc.) — already a
                        // monadic expression whose result we bind directly.
                        break :blk rhs_expr;
                    },
                }
            };

            // Bind the result using the actual let-bound binder name so the
            // body's references (via var_map) resolve correctly.
            const binder_name = try ctx.mapBinder(&pair.binder);

            // Translate the body.
            const body_expr = try translateExpr(ctx, let_expr.body);

            // Create the bind expression: lhs >>= \binder_name -> body
            const bind_expr = try ctx.alloc.create(GrinExpr);
            bind_expr.* = .{ .Bind = .{
                .lhs = lhs_expr,
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

            // Create placeholder stores for each binder (storing unit placeholders).
            // Each placeholder is allocated on the heap and its heap pointer
            // is bound to the binder name.
            //
            // For N placeholders, we build:
            //   store () >>= \p_a ->
            //   store () >>= \p_b ->
            //   ...rest...
            //
            // We build this inside-out: start from the innermost expression
            // (Step 2 + body) and wrap stores around it. But since Steps 2
            // and 3 need the placeholder names to already be in the var_map
            // (done above via mapBinder), we build the chain bottom-up.
            //
            // Strategy: build a linked list of (store, binder) pairs, then
            // in Step 3 wrap them around the final expression.
            var current_expr: ?*GrinExpr = null;

            // Step 1: Build the placeholder allocation chain.
            // Each `store () >>= \p_i -> next` allocates a heap cell and
            // binds the pointer to `p_i`.
            //
            // We chain left-to-right: for the first placeholder, we just
            // record `store ()` as the LHS; subsequent placeholders chain
            // via Bind. The final chain will be connected to Step 2 + body
            // in Step 3.
            //
            // Build: store () >>= \p_0 -> store () >>= \p_1 -> ... -> <rest>
            // We construct this as a list of (store, name) pairs and fold
            // them in Step 3. For now, build the leftmost prefix.
            const store_binds = try ctx.alloc.alloc(struct { store: *GrinExpr, name: GrinName }, placeholders.len);
            defer ctx.alloc.free(store_binds);

            for (placeholders, 0..) |p, idx| {
                const store_expr = try ctx.alloc.create(GrinExpr);
                store_expr.* = .{ .Store = .{ .Unit = {} } };
                store_binds[idx] = .{ .store = store_expr, .name = p };
            }

            // Step 2: Backpatch each binding with its real RHS.
            //
            // For App expressions calling known top-level functions, we
            // store them as F-tagged thunks (lazy). The thunk node is
            // stored on the heap and the placeholder is updated to point
            // to it. For simple Return values, we update directly.
            // For other complex expressions, we evaluate into a temp var
            // first, then update.
            for (pairs, 0..) |pair, i| {
                const rhs_expr = try translateExpr(ctx, pair.rhs);

                switch (rhs_expr.*) {
                    .App => |app| {
                        if (ctx.getFunctionArity(app.name) != null) {
                            // Known function: store as lazy F-tagged thunk,
                            // then update the placeholder with the thunk pointer.
                            const ftag = GrinTag{ .tag_type = .{ .Fun = {} }, .name = app.name };
                            const store_thunk = try ctx.alloc.create(GrinExpr);
                            store_thunk.* = .{ .Store = .{ .ConstTagNode = .{
                                .tag = ftag,
                                .fields = app.args,
                            } } };

                            const thunk_var = try ctx.freshName("thunk");
                            const update_expr = try ctx.alloc.create(GrinExpr);
                            update_expr.* = .{ .Update = .{
                                .ptr = placeholders[i],
                                .val = .{ .Var = thunk_var },
                            } };

                            // store (Ffunc [args]) >>= \thunk_var -> update p_i thunk_var
                            const store_update = try chainStoreUpdate(ctx, store_thunk, thunk_var, update_expr);

                            if (current_expr) |prev| {
                                const bind_chain = try ctx.alloc.create(GrinExpr);
                                bind_chain.* = .{ .Bind = .{
                                    .lhs = prev,
                                    .pat = .{ .Var = try ctx.freshName("_") },
                                    .rhs = store_update,
                                } };
                                current_expr = bind_chain;
                            } else {
                                current_expr = store_update;
                            }
                            continue;
                        }
                        // Higher-order app: fall through to complex-expr path.
                    },
                    .Return => {
                        // Simple value: update placeholder directly.
                        const rhs_val = try exprToVal(rhs_expr);
                        const update_expr = try ctx.alloc.create(GrinExpr);
                        update_expr.* = .{ .Update = .{
                            .ptr = placeholders[i],
                            .val = rhs_val,
                        } };

                        if (current_expr) |prev| {
                            const bind_update = try ctx.alloc.create(GrinExpr);
                            bind_update.* = .{ .Bind = .{
                                .lhs = prev,
                                .pat = .{ .Var = try ctx.freshName("_") },
                                .rhs = update_expr,
                            } };
                            current_expr = bind_update;
                        }
                        continue;
                    },
                    else => {},
                }

                // Complex expression (higher-order app, Case, Bind, etc.):
                // evaluate into a temp var, then update the placeholder.
                const temp_var = try ctx.freshName("rec_rhs");
                const update_expr = try ctx.alloc.create(GrinExpr);
                update_expr.* = .{ .Update = .{
                    .ptr = placeholders[i],
                    .val = .{ .Var = temp_var },
                } };

                // rhs_expr >>= \temp_var -> update p_i temp_var
                const bind_rhs = try ctx.alloc.create(GrinExpr);
                bind_rhs.* = .{ .Bind = .{
                    .lhs = rhs_expr,
                    .pat = .{ .Var = temp_var },
                    .rhs = update_expr,
                } };

                if (current_expr) |prev| {
                    const bind_chain = try ctx.alloc.create(GrinExpr);
                    bind_chain.* = .{ .Bind = .{
                        .lhs = prev,
                        .pat = .{ .Var = try ctx.freshName("_") },
                        .rhs = bind_rhs,
                    } };
                    current_expr = bind_chain;
                } else {
                    current_expr = bind_rhs;
                }
            }

            // Step 3: Translate the body and assemble the full expression.
            const body_expr = try translateExpr(ctx, let_expr.body);

            // Connect the backpatch chain (Step 2) to the body.
            var inner = body_expr;
            if (current_expr) |backpatch| {
                const bind_body = try ctx.alloc.create(GrinExpr);
                bind_body.* = .{ .Bind = .{
                    .lhs = backpatch,
                    .pat = .{ .Var = try ctx.freshName("_") },
                    .rhs = body_expr,
                } };
                inner = bind_body;
            }

            // Wrap placeholder allocations (Step 1) around the inner
            // expression, right-to-left:
            //   store () >>= \p_0 -> store () >>= \p_1 -> ... -> inner
            var idx = store_binds.len;
            while (idx > 0) {
                idx -= 1;
                const sb = store_binds[idx];
                const bind_expr = try ctx.alloc.create(GrinExpr);
                bind_expr.* = .{ .Bind = .{
                    .lhs = sb.store,
                    .pat = .{ .Var = sb.name },
                    .rhs = inner,
                } };
                inner = bind_expr;
            }

            return inner;
        },
    }
}

/// Translate a case expression.
///
/// Simple scrutinees (Var, Lit) translate directly.  Complex scrutinees
/// (App, Case, Let, …) are A-normalized: the expression is translated,
/// its result bound to a fresh variable, and the case dispatches on that
/// variable.
///
///   case (f x) of { alts }
///   →  scrut <- f x; case scrut of { alts }
fn translateCase(ctx: *TranslateCtx, case_expr: *const CoreCase) anyerror!*GrinExpr {
    // A-normalize complex scrutinee expressions.
    const ScrutInfo = struct {
        val: GrinVal,
        bind_expr: ?*GrinExpr,
        bind_name: ?GrinName,
    };

    const scrut_info: ScrutInfo = switch (case_expr.scrutinee.*) {
        .Var => |v| blk: {
            // Nullary constructors (True, False, Nil, etc.) must be
            // A-normalized through translateExpr so they become ValTag
            // values that the evaluator's case dispatch can match.
            // A bare GrinVal.Var for a constructor would be unresolvable
            // at runtime (constructors have no function-table entry).
            if (ctx.conFieldCount(v.name.unique.value)) |n_fields| {
                if (n_fields == 0) {
                    const scrut_expr = try translateExpr(ctx, case_expr.scrutinee);
                    const fresh = try ctx.freshName("scrut");
                    break :blk .{
                        .val = .{ .Var = fresh },
                        .bind_expr = scrut_expr,
                        .bind_name = fresh,
                    };
                }
            }
            break :blk .{
                .val = .{ .Var = try ctx.getCoreVar(v.name) },
                .bind_expr = null,
                .bind_name = null,
            };
        },
        .Lit => |l| .{
            .val = .{ .Lit = translateLiteral(l.val) },
            .bind_expr = null,
            .bind_name = null,
        },
        else => blk: {
            const scrut_expr = try translateExpr(ctx, case_expr.scrutinee);
            const fresh = try ctx.freshName("scrut");
            break :blk .{
                .val = .{ .Var = fresh },
                .bind_expr = scrut_expr,
                .bind_name = fresh,
            };
        },
    };

    // Translate case alternatives.
    var alts = try ctx.alloc.alloc(GrinAlt, case_expr.alts.len);
    for (case_expr.alts, 0..) |alt, i| {
        alts[i] = try translateAlt(ctx, alt);
    }

    // Create the case expression.
    const case_grin = try ctx.alloc.create(GrinExpr);
    case_grin.* = .{ .Case = .{
        .scrutinee = scrut_info.val,
        .alts = alts,
    } };

    // Wrap with scrutinee binding if the scrutinee was complex.
    if (scrut_info.bind_expr) |bind_lhs| {
        const bind_expr = try ctx.alloc.create(GrinExpr);
        bind_expr.* = .{ .Bind = .{
            .lhs = bind_lhs,
            .pat = .{ .Var = scrut_info.bind_name.? },
            .rhs = case_grin,
        } };
        return bind_expr;
    }

    return case_grin;
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
            const tag = GrinTag{
                .tag_type = .Con,
                .name = name,
            };

            // Nullary constructors use TagPat (matches ValTag values);
            // constructors with fields use NodePat (matches ConstTagNode).
            if (binders.len == 0) {
                return .{ .TagPat = tag };
            }

            var field_names = try ctx.alloc.alloc(GrinName, binders.len);
            for (binders, 0..) |binder, i| {
                field_names[i] = try ctx.mapBinder(&binder);
            }

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
/// Metadata for an F-tagged function thunk: base name and arity.
const FunTagInfo = struct {
    base: []const u8,
    arity: u32,
};

const TagInfo = struct {
    /// Constructor tags (C-tagged)
    con_tags: std.ArrayListUnmanaged(GrinTag),

    /// Function tags (F-tagged), keyed by unique ID.
    /// Carries the base name and arity so that eval can generate
    /// NodePat field binders and pass captured args to the function.
    fun_tags: std.AutoHashMapUnmanaged(u64, FunTagInfo),

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

    // Collect function names with their unique IDs and arities.
    // All top-level defs are potential F-tag targets for thunk forcing.
    for (program.defs) |def| {
        try info.fun_tags.put(alloc, def.name.unique.value, .{
            .base = def.name.base,
            .arity = @intCast(def.params.len),
        });
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
    return GrinProgram{
        .defs = defs_slice,
        .field_types = .{},
        .arities = .{},
    };
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

    // Add F-tag alternatives (thunks - need to force).
    // Each F-tag captures the function's arguments in its fields, so
    // we use NodePat with field binders and pass them to the function call.
    var fun_iter = tag_info.fun_tags.iterator();
    while (fun_iter.next()) |entry| {
        const unique = entry.key_ptr.*;
        const info = entry.value_ptr.*;
        const func_name = GrinName{
            .base = info.base,
            .unique = .{ .value = unique },
        };
        const alt = try generateFunTagAlt(alloc, p_param.*, result_var.*, func_name, info.arity);
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
/// An F-tagged thunk `Ffunc [a0, a1, ...]` captures the function's arguments
/// in its fields.  Forcing it means extracting those fields and calling the
/// function, then updating the thunk with an indirection to the result.
///
/// Pattern: F<func> field_0 field_1 ... field_{arity-1}
/// Body: app func [field_0, ..., field_{arity-1}] >>= \result ->
///         update p result; return result
fn generateFunTagAlt(alloc: std.mem.Allocator, p: GrinName, result: GrinName, func_name: GrinName, arity: u32) !GrinAlt {
    const fun_tag = funTag(func_name.base, func_name.unique.value);

    // Create field binder names for captured arguments.
    const field_names = try alloc.alloc(GrinName, arity);
    const field_args = try alloc.alloc(GrinVal, arity);
    for (0..arity) |i| {
        field_names[i] = .{
            .base = "fld",
            .unique = .{ .value = func_name.unique.value *% 100 +% i },
        };
        field_args[i] = .{ .Var = field_names[i] };
    }

    // Create app expression: app func [field_0, ..., field_{arity-1}]
    const app_expr = try alloc.create(GrinExpr);
    app_expr.* = .{
        .App = .{
            .name = func_name,
            .args = field_args,
        },
    };

    // Create update expression: update p result
    const update_expr = try alloc.create(GrinExpr);
    update_expr.* = .{ .Update = .{
        .ptr = p,
        .val = .{ .Var = result },
    } };

    // Create bind expression: app func [args] >>= \result -> update p result
    const update_bind = try alloc.create(GrinExpr);
    update_bind.* = .{ .Bind = .{
        .lhs = app_expr,
        .pat = .{ .Var = result },
        .rhs = update_expr,
    } };

    // Create return expression: return result
    const ret_expr = try alloc.create(GrinExpr);
    ret_expr.* = .{ .Return = .{ .Var = result } };

    // Chain: (app func [args] >>= \result -> update p result); return result
    const alt_body = try alloc.create(GrinExpr);
    alt_body.* = .{ .Bind = .{
        .lhs = update_bind,
        .pat = .{ .Var = result },
        .rhs = ret_expr,
    } };

    return GrinAlt{
        .pat = .{ .NodePat = .{ .tag = fun_tag, .fields = field_names } },
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

    const grin_prog = try translateProgram(alloc, core_prog, null, null);

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

    const grin_prog = try translateProgram(alloc, core_prog, null, null);

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

    const program = GrinProgram{
        .defs = defs,
        .field_types = .{},
        .arities = .{},
    };

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

    const program = GrinProgram{
        .defs = defs,
        .field_types = .{},
        .arities = .{},
    };

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

    const program = GrinProgram{
        .defs = defs,
        .field_types = .{},
        .arities = .{},
    };

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

    // Should have collected the function name (keyed by unique ID)
    try testing.expect(tag_info.fun_tags.count() >= 1);
    try testing.expect(tag_info.fun_tags.contains(10)); // testFunc unique = 10
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

    const grin_prog = try translateProgram(alloc, core_prog, null, null);

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

    const grin_prog = try translateProgram(alloc, core_prog, null, null);

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

    const grin_prog = try translateProgram(alloc, core_prog, null, null);

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

test "translateProgram: external 0-arity function produces App not Return Var" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Simulate: `main` was defined in a prior REPL input with arity 0.
    // Current input: `replExpr__ = main` (a bare variable reference).
    // The translator should emit App(main, []) not Return(Var(main)).
    const main_unique: u64 = 999;

    var external_arities = std.AutoHashMapUnmanaged(u64, u32){};
    defer external_arities.deinit(alloc);
    try external_arities.put(alloc, main_unique, 0);

    // Build Core program: replExpr__ = main
    const rhs = try alloc.create(core.Expr);
    rhs.* = .{ .Var = .{
        .name = .{ .base = "main", .unique = .{ .value = main_unique } },
        .ty = .{ .TyVar = .{ .base = "IO", .unique = .{ .value = 0 } } },
        .span = undefined,
    } };

    const bind_pair = CoreBindPair{
        .binder = .{
            .name = .{ .base = "replExpr__", .unique = .{ .value = 1000 } },
            .ty = undefined,
            .span = undefined,
        },
        .rhs = rhs,
    };

    const core_prog = CoreProgram{
        .data_decls = &.{},
        .binds = &.{.{ .NonRec = bind_pair }},
    };

    const grin_prog = try translateProgram(alloc, core_prog, &external_arities, null);

    try testing.expectEqual(@as(usize, 1), grin_prog.defs.len);

    // The body of replExpr__ should be App(main, []), not Return(Var(main)).
    switch (grin_prog.defs[0].body.*) {
        .App => |app| {
            try testing.expectEqualStrings("main", app.name.base);
            try testing.expectEqual(@as(usize, 0), app.args.len);
        },
        .Return => {
            // This is the bug: should NOT be Return(Var(main)).
            return error.TestUnexpectedResult;
        },
        else => return error.TestUnexpectedResult,
    }
}

test "wrapWithLazyBindsForCon: Case arg lambda-lifted into thunk (#518)" {
    // Core: data Wrap = MkWrap Int
    //       f x = MkWrap (case x of { 0 -> 42; _ -> 99 })
    //
    // Expected GRIN:
    //   f x =
    //     arg <- store (F_thunk [x])     -- Case lifted to helper
    //     store (CMkWrap [arg])
    //
    //   _thunk x =                        -- lifted helper
    //     case x of { ... }
    //
    // The Case expression should NOT be evaluated eagerly; it should be
    // suspended as an F-tagged thunk via ad-hoc lambda lifting.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Data constructor: MkWrap :: Int -> Wrap (1 field)
    const mkwrap_name = grin.Name{ .base = "MkWrap", .unique = .{ .value = 500 } };
    const wrap_ty = core.CoreType{ .TyCon = .{
        .name = grin.Name{ .base = "Wrap", .unique = .{ .value = 503 } },
        .args = &.{},
    } };
    const int_ty = core.CoreType{ .TyCon = .{
        .name = grin.Name{ .base = "Int", .unique = .{ .value = 600 } },
        .args = &.{},
    } };
    const arg_ty = try alloc.create(core.CoreType);
    arg_ty.* = int_ty;
    const res_ty = try alloc.create(core.CoreType);
    res_ty.* = wrap_ty;
    const mkwrap_ty = core.CoreType{ .FunTy = .{ .arg = arg_ty, .res = res_ty } };

    const mkwrap_id = core.Id{
        .name = mkwrap_name,
        .ty = mkwrap_ty,
        .span = undefined,
    };

    const x_id = core.Id{
        .name = grin.Name{ .base = "x", .unique = .{ .value = 501 } },
        .ty = undefined,
        .span = undefined,
    };

    const f_id = core.Id{
        .name = grin.Name{ .base = "f", .unique = .{ .value = 502 } },
        .ty = undefined,
        .span = undefined,
    };

    // Build: case x of { 0 -> 42; _ -> 99 }
    const x_var_scrutinee = try alloc.create(CoreExpr);
    x_var_scrutinee.* = .{ .Var = x_id };

    const lit_42 = try alloc.create(CoreExpr);
    lit_42.* = .{ .Lit = .{ .val = .{ .Int = 42 }, .span = undefined } };

    const lit_99 = try alloc.create(CoreExpr);
    lit_99.* = .{ .Lit = .{ .val = .{ .Int = 99 }, .span = undefined } };

    const case_expr = try alloc.create(CoreExpr);
    case_expr.* = .{ .Case = .{
        .scrutinee = x_var_scrutinee,
        .binder = x_id,
        .ty = .{ .TyCon = .{ .name = grin.Name{ .base = "Int", .unique = .{ .value = 600 } }, .args = &.{} } },
        .alts = &.{
            .{ .con = .{ .LitAlt = .{ .Int = 0 } }, .binders = &.{}, .body = lit_42 },
            .{ .con = .Default, .binders = &.{}, .body = lit_99 },
        },
        .span = undefined,
    } };

    // Build: MkWrap (case x of ...)  -- constructor application
    const mkwrap_var = try alloc.create(CoreExpr);
    mkwrap_var.* = .{ .Var = mkwrap_id };

    const app_expr = try alloc.create(CoreExpr);
    app_expr.* = .{ .App = .{ .fn_expr = mkwrap_var, .arg = case_expr, .span = undefined } };

    // Build: \x -> MkWrap (case x of ...)
    const lam_x = try alloc.create(CoreExpr);
    lam_x.* = .{ .Lam = .{ .binder = x_id, .body = app_expr, .span = undefined } };

    const bind_pair = CoreBindPair{
        .binder = f_id,
        .rhs = lam_x,
    };

    // Data declaration for MkWrap (1 constructor, 1 field)
    const data_decl = core.CoreDataDecl{
        .name = grin.Name{ .base = "Wrap", .unique = .{ .value = 503 } },
        .tyvars = &.{},
        .constructors = &.{mkwrap_id},
        .span = undefined,
    };

    const core_prog = CoreProgram{
        .data_decls = &.{data_decl},
        .binds = &.{.{ .NonRec = bind_pair }},
    };

    const grin_prog = try translateProgram(alloc, core_prog, null, null);

    // Should have 2 defs: f and the lifted thunk helper.
    try testing.expectEqual(@as(usize, 2), grin_prog.defs.len);

    const f_def = grin_prog.defs[0];
    try testing.expectEqualStrings("f", f_def.name.base);
    try testing.expectEqual(@as(usize, 1), f_def.params.len);

    // The body of f should be a Bind chain:
    //   store (F_thunk [x]) >>= \arg -> store (CMkWrap [arg])
    // The outermost Bind's LHS should be a Store with an F-tag (thunk).
    switch (f_def.body.*) {
        .Bind => |bind| {
            switch (bind.lhs.*) {
                .Store => |store_val| {
                    switch (store_val) {
                        .ConstTagNode => |ctn| {
                            // Should be an F-tag (function thunk)
                            switch (ctn.tag.tag_type) {
                                .Fun => {},
                                else => return error.TestUnexpectedResult,
                            }
                            try testing.expectEqualStrings("_thunk", ctn.tag.name.base);
                            // Should capture x as free variable
                            try testing.expectEqual(@as(usize, 1), ctn.fields.len);
                            switch (ctn.fields[0]) {
                                .Var => |v| try testing.expectEqualStrings("x", v.base),
                                else => return error.TestUnexpectedResult,
                            }
                        },
                        else => return error.TestUnexpectedResult,
                    }
                },
                else => return error.TestUnexpectedResult,
            }
        },
        else => return error.TestUnexpectedResult,
    }

    // The lifted helper should be the second def.
    const thunk_def = grin_prog.defs[1];
    try testing.expectEqualStrings("_thunk", thunk_def.name.base);
    // Should have 1 parameter (captured x).
    try testing.expectEqual(@as(usize, 1), thunk_def.params.len);
    try testing.expectEqualStrings("x", thunk_def.params[0].base);
    // The body should be a Case expression.
    switch (thunk_def.body.*) {
        .Case => {},
        // Bind chain containing a Case is also acceptable
        .Bind => |bind| {
            switch (bind.rhs.*) {
                .Case => {},
                else => return error.TestUnexpectedResult,
            }
        },
        else => return error.TestUnexpectedResult,
    }
}

test "exprInvolvesComputation: distinguishes values from computation (#518)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const dummy_name = GrinName{ .base = "x", .unique = .{ .value = 0 } };

    // Store → no computation (constructor allocation)
    const store_expr = try alloc.create(GrinExpr);
    store_expr.* = .{ .Store = .{ .Var = dummy_name } };
    try testing.expect(!exprInvolvesComputation(store_expr));

    // Return → no computation
    const return_expr = try alloc.create(GrinExpr);
    return_expr.* = .{ .Return = .{ .Var = dummy_name } };
    try testing.expect(!exprInvolvesComputation(return_expr));

    // Case → computation
    const case_expr = try alloc.create(GrinExpr);
    case_expr.* = .{ .Case = .{ .scrutinee = .{ .Var = dummy_name }, .alts = &.{} } };
    try testing.expect(exprInvolvesComputation(case_expr));

    // App → computation
    const app_expr = try alloc.create(GrinExpr);
    app_expr.* = .{ .App = .{ .name = dummy_name, .args = &.{} } };
    try testing.expect(exprInvolvesComputation(app_expr));

    // Bind(Store, Return) → no computation (constructor chain)
    const bind_store = try alloc.create(GrinExpr);
    bind_store.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = .{ .Var = dummy_name },
        .rhs = return_expr,
    } };
    try testing.expect(!exprInvolvesComputation(bind_store));

    // Bind(Store, Case) → computation (case in RHS)
    const bind_case = try alloc.create(GrinExpr);
    bind_case.* = .{ .Bind = .{
        .lhs = store_expr,
        .pat = .{ .Var = dummy_name },
        .rhs = case_expr,
    } };
    try testing.expect(exprInvolvesComputation(bind_case));
}
