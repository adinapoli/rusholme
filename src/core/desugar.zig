const std = @import("std");
const ast_mod = @import("../core/ast.zig");
const renamer_mod = @import("../renamer/renamer.zig");
const infer_mod = @import("../typechecker/infer.zig");
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");
const Known = @import("../naming/known.zig");
const naming_mod = @import("../naming/unique.zig");
const primop_mod = @import("../grin/primop.zig");
const class_env_mod = @import("../typechecker/class_env.zig");
const solver_mod = @import("../typechecker/solver.zig");
const Name = ast_mod.Name;
const SourceSpan = ast_mod.SourceSpan;
const SourcePos = ast_mod.SourcePos;
const diag_mod = @import("../diagnostics/diagnostic.zig");
const DiagnosticCollector = diag_mod.DiagnosticCollector;

pub const DesugarCtx = struct {
    alloc: std.mem.Allocator,
    types: *infer_mod.ModuleTypes,
    diags: *DiagnosticCollector,
    /// Used to generate fresh unique values for synthetic binders (lambda
    /// parameters created by the pattern-match compiler, constructor field
    /// binders, etc.). Each synthetic binder must get a globally unique ID so
    /// that the GRIN translator can distinguish them in its `var_map`.
    u_supply: *naming_mod.UniqueSupply,

    /// Maps `(class_unique, head_type_base_name)` → dictionary `Name`.
    /// Populated by `desugarInstanceDecl`, queried by `buildDictExpr`
    /// when translating `DictEvidence.instance` to a Core variable reference.
    dict_names: DictNameMap = .empty,

    /// Evidence map built from solved constraints. Keyed by
    /// `(var_unique, class_name_unique)` → list of `DictEvidence` pointers.
    /// Multiple constraints for the same variable can arise from multiple
    /// class constraints (e.g., `(Eq a, Ord a) =>`).
    evidence_map: EvidenceMap = .empty,

    /// Maps class unique → dictionary parameter Name for the current
    /// function.  Populated by `wrapWithDictLambdas`, consumed by
    /// `buildDictExpr` (.param case) to reference the correct binder.
    dict_param_names: std.AutoHashMapUnmanaged(u64, Name) = .{},

    /// The `True` constructor name, extracted from the renamed module's
    /// `data Bool` declaration. Used by guard desugaring to build
    /// `case cond of { True -> rhs ; _ -> fallback }`.
    /// Falls back to `Known.Con.True` if no `data Bool` is in scope.
    true_name: Name = Known.Con.True,

    pub const DictNameKey = struct {
        class_unique: u64,
        head_name: []const u8,
    };

    pub const DictNameMap = std.ArrayHashMapUnmanaged(
        DictNameKey,
        Name,
        struct {
            pub fn hash(_: @This(), key: DictNameKey) u32 {
                var h = std.hash.Wyhash.init(0);
                h.update(std.mem.asBytes(&key.class_unique));
                h.update(key.head_name);
                return @truncate(h.final());
            }
            pub fn eql(_: @This(), a: DictNameKey, b: DictNameKey, _: usize) bool {
                return a.class_unique == b.class_unique and std.mem.eql(u8, a.head_name, b.head_name);
            }
        },
        true,
    );

    /// Key for the evidence map: identifies a constraint by the use-site
    /// variable and the class.
    pub const EvidenceKey = struct {
        var_unique: u64,
        span_start_line: u32,
        span_start_col: u32,
        class_unique: u64,
    };

    pub const EvidenceMap = std.ArrayHashMapUnmanaged(
        EvidenceKey,
        *const solver_mod.DictEvidence,
        struct {
            pub fn hash(_: @This(), key: EvidenceKey) u32 {
                var h = std.hash.Wyhash.init(0);
                h.update(std.mem.asBytes(&key.var_unique));
                h.update(std.mem.asBytes(&key.span_start_line));
                h.update(std.mem.asBytes(&key.span_start_col));
                h.update(std.mem.asBytes(&key.class_unique));
                return @truncate(h.final());
            }
            pub fn eql(_: @This(), a: EvidenceKey, b: EvidenceKey, _: usize) bool {
                return a.var_unique == b.var_unique and
                    a.span_start_line == b.span_start_line and
                    a.span_start_col == b.span_start_col and
                    a.class_unique == b.class_unique;
            }
        },
        true,
    );
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

/// Result of desugaring a module.
pub const DesugarResult = struct {
    /// The desugared Core program.
    program: ast_mod.CoreProgram,
    /// Dictionary name map accumulated during desugaring.
    /// Maps (class_unique, head_type_name) → dictionary Name.
    /// The REPL session persists this across inputs so that
    /// dictionary evidence resolution can find dictionaries
    /// declared in prior inputs (#578).
    dict_names: DesugarCtx.DictNameMap,
};

pub fn desugarModule(
    alloc: std.mem.Allocator,
    module: renamer_mod.RenamedModule,
    module_types: *infer_mod.ModuleTypes,
    diags: *DiagnosticCollector,
    u_supply: *naming_mod.UniqueSupply,
    external_dict_names: ?*const DesugarCtx.DictNameMap,
) std.mem.Allocator.Error!DesugarResult {
    var ctx = DesugarCtx{
        .alloc = alloc,
        .types = module_types,
        .diags = diags,
        .u_supply = u_supply,
    };

    // Extract the True constructor name from the renamed module's
    // data declarations. Guard desugaring needs this to build
    // `case cond of { True -> rhs ; _ -> fallback }`.
    // The renamer may have assigned a fresh unique to True when
    // processing `data Bool = False | True` from the Prelude.
    for (module.declarations) |decl| {
        switch (decl) {
            .DataDecl => |dd| {
                if (std.mem.eql(u8, dd.name.base, "Bool")) {
                    for (dd.constructors) |con| {
                        if (std.mem.eql(u8, con.name.base, "True")) {
                            ctx.true_name = con.name;
                            break;
                        }
                    }
                    break;
                }
            },
            else => {},
        }
    }

    // Seed with dictionary names from prior REPL inputs so that
    // evidence resolution can find dictionaries declared earlier.
    if (external_dict_names) |ext| {
        for (ext.keys(), ext.values()) |key, val| {
            try ctx.dict_names.put(alloc, key, val);
        }
    }

    // Build evidence map from solved constraints so the expression desugarer
    // can look up dictionary evidence for each variable use site.
    try buildEvidenceMap(&ctx);

    var binds = std.ArrayListUnmanaged(ast_mod.Bind){};
    errdefer binds.deinit(alloc);

    var data_decls = std.ArrayListUnmanaged(ast_mod.CoreDataDecl){};
    errdefer data_decls.deinit(alloc);

    // Pass 1: Process class and instance declarations first.
    // This populates ctx.dict_names so that dictionary evidence resolution
    // in Pass 2 can find the correct dictionary names.
    for (module.declarations) |decl| {
        switch (decl) {
            .ClassDecl => |cd| {
                try desugarClassDecl(&ctx, cd, &data_decls, &binds);
            },
            .InstanceDecl => |id_decl| {
                try desugarInstanceDecl(&ctx, id_decl, &binds);
            },
            else => {},
        }
    }

    // Pass 2: Process all other declarations (FunBind, PatBind, DataDecl, etc.).
    for (module.declarations) |decl| {
        switch (decl) {
            .ClassDecl => {}, // Handled in Pass 1
            .InstanceDecl => {}, // Handled in Pass 1
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

                // Pre-populate dict_param_names so that buildDictExpr (.param
                // case) can reference the correct binder unique when desugaring
                // the body.  wrapWithDictLambdas will then reuse these names
                // instead of generating fresh ones.
                ctx.dict_param_names.clearRetainingCapacity();
                for (scheme.constraints) |constraint| {
                    const dpn = Name{
                        .base = try std.fmt.allocPrint(alloc, "dict${s}", .{constraint.class_name.base}),
                        .unique = ctx.u_supply.fresh(),
                    };
                    try ctx.dict_param_names.put(alloc, constraint.class_name.unique.value, dpn);
                }

                if (needs_match_compiler) {
                    const p_body = try desugarMatch(&ctx, fb.equations, core_ty);
                    // Wrap with dictionary lambdas if the function is constrained.
                    const wrapped_body = try wrapWithDictLambdas(&ctx, scheme, p_body, fb.span);
                    try binds.append(alloc, .{ .NonRec = .{
                        .binder = binder_id,
                        .rhs = wrapped_body,
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

                    // Wrap with dictionary lambdas if the function is constrained.
                    const body_ptr = try alloc.create(ast_mod.Expr);
                    body_ptr.* = body;
                    const wrapped = try wrapWithDictLambdas(&ctx, scheme, body_ptr, fb.span);

                    try binds.append(alloc, .{ .NonRec = .{
                        .binder = binder_id,
                        .rhs = wrapped,
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
            .ForeignPrim => |fp| {
                // Validate the PrimOp name at compile time.
                // Accept both raw PrimOp enum names (e.g. "add_Int") and
                // Prelude-level names (e.g. "putStrLn" → putStrLn_).
                const is_known = primop_mod.PrimOp.fromString(fp.primop_name) != null or
                    primop_mod.PrimOp.fromPreludeName(fp.primop_name) != null;
                if (!is_known) {
                    const msg = try std.fmt.allocPrint(
                        alloc,
                        "unknown primitive operation: `{s}`",
                        .{fp.primop_name},
                    );
                    try diags.emit(alloc, .{
                        .severity = .@"error",
                        .code = .unknown_primop,
                        .span = fp.span,
                        .message = msg,
                    });
                    continue;
                }

                const scheme = module_types.schemes.get(fp.name.unique) orelse continue;
                const core_ty = try schemeToCore(alloc, scheme);

                // Count the function arity from the type (number of top-level arrows).
                const arity = countFunctionArity(core_ty);

                // Resolve the user-facing name to the canonical PrimOp enum
                // name.  This normalises aliases: e.g.
                //   foreign import prim "putStrLn" ...  → "putStrLn_"
                //   foreign import prim "putStr"  ...  → "write_stdout"
                // so the LLVM backend's PrimOpMapping only needs to match
                // canonical names.  Raw enum names (e.g. "add_Int") pass
                // through unchanged via fromString.
                const canonical_base = if (primop_mod.PrimOp.fromString(fp.primop_name)) |_|
                    fp.primop_name
                else if (primop_mod.PrimOp.fromPreludeName(fp.primop_name)) |op|
                    op.name()
                else
                    fp.primop_name; // validated above — shouldn't reach here

                const primop_name = Name{
                    .base = canonical_base,
                    .unique = ctx.u_supply.fresh(),
                };

                // Build the lambda wrapper: \x1 -> \x2 -> ... -> primop x1 x2 ...
                const bind = try buildPrimOpWrapper(
                    alloc,
                    &ctx,
                    fp.name,
                    primop_name,
                    core_ty,
                    arity,
                    fp.span,
                );
                try binds.append(alloc, bind);
            },
            .TypeSig => {},
        }
    }

    return DesugarResult{
        .program = ast_mod.CoreProgram{
            .data_decls = try data_decls.toOwnedSlice(alloc),
            .binds = try binds.toOwnedSlice(alloc),
        },
        .dict_names = ctx.dict_names,
    };
}

// ── Type class desugaring ──────────────────────────────────────────────
//
// Dictionary-passing translation (Wadler & Blott 1989).
//
// For each class declaration, we generate:
//   1. A dictionary data type:  data Dict$Eq a = MkDict$Eq (method types...)
//   2. Selector functions:      (==) = \dict -> case dict of MkDict$Eq f0 f1 -> f0
//
// For each instance declaration, we generate:
//   1. A dictionary value:      dict$Eq$Int = MkDict$Eq primEqInt ...

/// Desugar a class declaration into a dictionary data type and method selectors.
fn desugarClassDecl(
    ctx: *DesugarCtx,
    cd: renamer_mod.RClassDecl,
    data_decls: *std.ArrayListUnmanaged(ast_mod.CoreDataDecl),
    binds: *std.ArrayListUnmanaged(ast_mod.Bind),
) std.mem.Allocator.Error!void {
    const alloc = ctx.alloc;
    const class_env = &ctx.types.class_env;

    // Look up the class info populated during type inference (Pass 0b).
    const class_info = class_env.lookupClass(cd.name.unique.value) orelse return;

    // ── 1. Dictionary data type ───────────────────────────────────────
    //
    // data Dict$Eq a = MkDict$Eq (method_type_1) (method_type_2) ...

    const dict_tycon_name = Name{
        .base = try std.fmt.allocPrint(alloc, "Dict${s}", .{cd.name.base}),
        .unique = ctx.u_supply.fresh(),
    };
    const dict_con_name = Name{
        .base = try std.fmt.allocPrint(alloc, "MkDict${s}", .{cd.name.base}),
        .unique = ctx.u_supply.fresh(),
    };

    // Build the constructor type: method_1_ty -> method_2_ty -> ... -> Dict$Class a
    // We use a placeholder CoreType for the dictionary type itself.
    const tyvar_name = Name{ .base = cd.tyvar.base, .unique = cd.tyvar.unique };
    const dict_result_ty = ast_mod.CoreType{
        .TyCon = .{
            .name = dict_tycon_name,
            .args = try alloc.dupe(ast_mod.CoreType, &.{ast_mod.CoreType{ .TyVar = tyvar_name }}),
        },
    };

    // Build constructor type: field1 -> field2 -> ... -> Dict$Class a
    var con_ty: ast_mod.CoreType = dict_result_ty;
    {
        var i = class_info.methods.len;
        while (i > 0) {
            i -= 1;
            const method_htype = class_info.methods[i].ty;
            const method_core_ty = try method_htype.toCore(alloc);
            const p_arg = try alloc.create(ast_mod.CoreType);
            p_arg.* = method_core_ty;
            const p_res = try alloc.create(ast_mod.CoreType);
            p_res.* = con_ty;
            con_ty = ast_mod.CoreType{ .FunTy = .{ .arg = p_arg, .res = p_res } };
        }
    }

    // Wrap in forall for the class tyvar.
    const fa_body = try alloc.create(ast_mod.CoreType);
    fa_body.* = con_ty;
    con_ty = ast_mod.CoreType{ .ForAllTy = .{ .binder = tyvar_name, .body = fa_body } };

    const con_id = ast_mod.Id{
        .name = dict_con_name,
        .ty = con_ty,
        .span = cd.span,
    };

    try data_decls.append(alloc, .{
        .name = dict_tycon_name,
        .tyvars = try alloc.dupe(Name, &.{tyvar_name}),
        .constructors = try alloc.dupe(ast_mod.Id, &.{con_id}),
        .span = cd.span,
    });

    // ── 2. Method selector functions ──────────────────────────────────
    //
    // For each method at index `i`:
    //   method_i = \dict -> case dict of { MkDict$Class f0 f1 ... -> fi }
    //
    // The selector uses the ORIGINAL method Name so downstream references
    // (from user code) resolve correctly.

    for (class_info.methods, 0..) |method, method_idx| {
        // Build field binders for the case alternative
        var field_binders = try alloc.alloc(ast_mod.Id, class_info.methods.len);
        for (class_info.methods, 0..) |m, j| {
            const field_name = Name{
                .base = try std.fmt.allocPrint(alloc, "f{d}", .{j}),
                .unique = ctx.u_supply.fresh(),
            };
            field_binders[j] = ast_mod.Id{
                .name = field_name,
                .ty = try m.ty.toCore(alloc),
                .span = cd.span,
            };
        }

        // Eta-expand the selector to the full method arity.
        //
        // Without eta-expansion, `showIt = \dict -> case dict of { ... -> f0 }`
        // has arity 1 (just the dict param). But `showIt dict MkA` passes 2
        // arguments, triggering the over-application path which emits a call
        // to `apply` — a function that is not yet defined in the runtime.
        //
        // With eta-expansion: `showIt = \dict x0 -> case dict of { ... -> f0 x0 }`
        // has arity 2, matching the call site and avoiding over-application.
        // This is how GHC generates dictionary selectors.

        // Count the method's own arity from its type (number of Fun arrows).
        const method_arity = countFunArity(method.ty);

        // Create fresh binders for the eta-expanded parameters.
        var eta_binders = try alloc.alloc(ast_mod.Id, method_arity);
        {
            var remaining_ty = method.ty;
            for (0..method_arity) |ei| {
                const chased = remaining_ty.chase();
                const arg_core_ty = switch (chased) {
                    .Fun => |f| try f.arg.toCore(alloc),
                    else => ast_mod.CoreType{ .TyCon = .{ .name = Known.Type.Unit, .args = &.{} } },
                };
                eta_binders[ei] = ast_mod.Id{
                    .name = Name{
                        .base = try std.fmt.allocPrint(alloc, "x{d}", .{ei}),
                        .unique = ctx.u_supply.fresh(),
                    },
                    .ty = arg_core_ty,
                    .span = cd.span,
                };
                remaining_ty = switch (chased) {
                    .Fun => |f| f.res.*,
                    else => remaining_ty,
                };
            }
        }

        // Build the case body: apply the extracted field to eta params.
        // `f_i x0 x1 ...`
        var case_body: *const ast_mod.Expr = blk: {
            const v = try alloc.create(ast_mod.Expr);
            v.* = ast_mod.Expr{ .Var = field_binders[method_idx] };
            break :blk v;
        };
        for (eta_binders) |eb| {
            const arg_expr = try alloc.create(ast_mod.Expr);
            arg_expr.* = ast_mod.Expr{ .Var = eb };
            const app_expr = try alloc.create(ast_mod.Expr);
            app_expr.* = ast_mod.Expr{
                .App = .{ .fn_expr = case_body, .arg = arg_expr, .span = cd.span },
            };
            case_body = app_expr;
        }

        // The case alternative: MkDict$Class f0 f1 ... -> f_i x0 x1 ...
        const alt = ast_mod.Alt{
            .con = .{ .DataAlt = dict_con_name },
            .binders = field_binders,
            .body = case_body,
        };

        // The dict parameter binder
        const dict_param_name = Name{
            .base = "dict",
            .unique = ctx.u_supply.fresh(),
        };

        // Dict type for the parameter (use a placeholder — not critical for GRIN)
        const dict_param_ty = ast_mod.CoreType{
            .TyCon = .{ .name = dict_tycon_name, .args = &.{} },
        };
        const dict_param_id = ast_mod.Id{
            .name = dict_param_name,
            .ty = dict_param_ty,
            .span = cd.span,
        };

        // Scrutinee: the dict parameter variable
        const scrutinee = try alloc.create(ast_mod.Expr);
        scrutinee.* = ast_mod.Expr{ .Var = dict_param_id };

        // Result type is the return type after all eta params are applied.
        const result_core_ty = blk: {
            var ty = method.ty;
            for (0..method_arity) |_| {
                const chased = ty.chase();
                ty = switch (chased) {
                    .Fun => |f| f.res.*,
                    else => break,
                };
            }
            break :blk try ty.toCore(alloc);
        };

        // Case expression
        const case_expr = try alloc.create(ast_mod.Expr);
        case_expr.* = ast_mod.Expr{
            .Case = .{
                .scrutinee = scrutinee,
                .binder = dict_param_id,
                .ty = result_core_ty,
                .alts = try alloc.dupe(ast_mod.Alt, &.{alt}),
                .span = cd.span,
            },
        };

        // Build the lambda chain: \dict -> \x0 -> \x1 -> ... -> case ...
        // Start from the innermost (case expr) and wrap with eta params
        // from right to left, then add the dict param outermost.
        var body_expr: *const ast_mod.Expr = case_expr;
        {
            var i = method_arity;
            while (i > 0) {
                i -= 1;
                const lam = try alloc.create(ast_mod.Expr);
                lam.* = ast_mod.Expr{
                    .Lam = .{
                        .binder = eta_binders[i],
                        .body = body_expr,
                        .span = cd.span,
                    },
                };
                body_expr = lam;
            }
        }

        // Outermost lambda: \dict -> ...
        const lam_expr = try alloc.create(ast_mod.Expr);
        lam_expr.* = ast_mod.Expr{
            .Lam = .{
                .binder = dict_param_id,
                .body = body_expr,
                .span = cd.span,
            },
        };

        // The selector binding uses the original method name.
        const selector_ty = if (ctx.types.schemes.get(method.name.unique)) |method_scheme|
            try schemeToCore(alloc, method_scheme)
        else
            try method.ty.toCore(alloc);

        const selector_id = ast_mod.Id{
            .name = method.name,
            .ty = selector_ty,
            .span = cd.span,
        };

        try binds.append(alloc, .{ .NonRec = .{
            .binder = selector_id,
            .rhs = lam_expr,
        } });
    }

    // ── 3. Default method bindings ────────────────────────────────────
    //
    // For each method with `has_default == true` and a non-null default_impl,
    // generate:
    //   default$ClassName$methodName = \dict -> \x1 -> ... -> body
    //
    // where `body` is the compiled default implementation. The dict parameter
    // allows the instance desugarer to reference this binding and pass the
    // instance dictionary when a method is not explicitly provided.

    for (cd.methods) |method| {
        const default_impl = method.default_impl orelse continue;
        if (default_impl.len == 0) continue;

        const default_name = Name{
            .base = try std.fmt.allocPrint(alloc, "default${s}${s}", .{ cd.name.base, method.name.base }),
            .unique = ctx.u_supply.fresh(),
        };

        // Compile the default method body using the pattern match compiler.
        // The default body is a slice of RMatch equations (same as FunBind).
        const method_htype = class_info.methods[0].ty; // Placeholder — use method's own type
        var method_core_ty: ast_mod.CoreType = undefined;

        // Find the correct method info by name.
        for (class_info.methods) |mi| {
            if (mi.name.unique.value == method.name.unique.value) {
                method_core_ty = try mi.ty.toCore(alloc);
                break;
            }
        } else {
            method_core_ty = try method_htype.toCore(alloc);
        }

        const body_expr = try desugarMatch(ctx, default_impl, method_core_ty);

        // Wrap with a dictionary lambda: \dict -> body
        const dict_param_name = Name{
            .base = "dict",
            .unique = ctx.u_supply.fresh(),
        };
        const dict_param_ty = ast_mod.CoreType{
            .TyCon = .{ .name = dict_tycon_name, .args = &.{} },
        };
        const dict_param_id = ast_mod.Id{
            .name = dict_param_name,
            .ty = dict_param_ty,
            .span = cd.span,
        };

        const lam_default = try alloc.create(ast_mod.Expr);
        lam_default.* = ast_mod.Expr{
            .Lam = .{
                .binder = dict_param_id,
                .body = body_expr,
                .span = cd.span,
            },
        };

        const default_id = ast_mod.Id{
            .name = default_name,
            .ty = method_core_ty,
            .span = cd.span,
        };

        try binds.append(alloc, .{ .NonRec = .{
            .binder = default_id,
            .rhs = lam_default,
        } });
    }

    // Store the dictionary constructor name in ClassEnv so that instance
    // declarations can reuse it (issue #569).
    ctx.types.class_env.setDictConName(cd.name.unique.value, dict_con_name);
}

/// Desugar an instance declaration into a dictionary value binding.
fn desugarInstanceDecl(
    ctx: *DesugarCtx,
    id_decl: renamer_mod.RInstanceDecl,
    binds: *std.ArrayListUnmanaged(ast_mod.Bind),
) std.mem.Allocator.Error!void {
    const alloc = ctx.alloc;
    const class_env = &ctx.types.class_env;

    // Look up the class to know method order.
    const class_info = class_env.lookupClass(id_decl.class_name.unique.value) orelse return;

    // Reuse the dictionary constructor name from the class declaration.
    // This ensures all instances use the same constructor unique (issue #569).
    const dict_con_name = class_info.dict_con_name;

    // Build an instance dictionary name.  Convention: dict$<ClassName>$<HeadType>.
    const head_name = try instanceHeadName(alloc, id_decl.instance_type);
    const dict_name = Name{
        .base = try std.fmt.allocPrint(alloc, "dict${s}${s}", .{ id_decl.class_name.base, head_name }),
        .unique = ctx.u_supply.fresh(),
    };

    // Register in the dict_names map so call-site evidence resolution can
    // find the dictionary name for this (class, head_type) pair.
    try ctx.dict_names.put(alloc, .{
        .class_unique = id_decl.class_name.unique.value,
        .head_name = head_name,
    }, dict_name);

    // If the instance has context constraints (e.g. `Show a => Show [a]`),
    // pre-populate dict_param_names so that evidence resolution inside method
    // bodies can reference the enclosing dictionary parameters.  These names
    // are reused when wrapping the dictionary expression with lambdas below.
    var context_param_names = try alloc.alloc(Name, id_decl.context.len);
    if (id_decl.context.len > 0) {
        ctx.dict_param_names.clearRetainingCapacity();
        for (id_decl.context, 0..) |assertion, ci| {
            const dpn = Name{
                .base = try std.fmt.allocPrint(alloc, "dict${s}", .{assertion.class_name.base}),
                .unique = ctx.u_supply.fresh(),
            };
            context_param_names[ci] = dpn;
            try ctx.dict_param_names.put(alloc, assertion.class_name.unique.value, dpn);
        }
    }

    // Build the dictionary value: MkDict$Class method1_impl method2_impl ...
    // For each method in class declaration order, find the binding in the instance.
    // If not found and the class has a default, use a placeholder.
    var method_exprs = try alloc.alloc(*const ast_mod.Expr, class_info.methods.len);
    for (class_info.methods, 0..) |method, i| {
        // Look for this method in the instance bindings
        var found_binding: ?renamer_mod.RInstanceBinding = null;
        for (id_decl.bindings) |binding| {
            if (binding.name.unique.value == method.name.unique.value) {
                found_binding = binding;
                break;
            }
        }

        if (found_binding) |binding| {
            // Desugar the instance method body.
            if (binding.equations.len == 1 and binding.equations[0].patterns.len == 0) {
                // Simple case: no patterns, just an RHS
                const body = try alloc.create(ast_mod.Expr);
                body.* = try desugarRhs(ctx, binding.equations[0].rhs);
                method_exprs[i] = body;
            } else {
                // Use the pattern match compiler for multi-equation / pattern methods
                const method_scheme = ctx.types.schemes.get(method.name.unique) orelse continue;
                const method_core_ty = try schemeToCore(alloc, method_scheme);
                method_exprs[i] = try desugarMatch(ctx, binding.equations, method_core_ty);
            }
        } else if (method.has_default) {
            // Apply the compiled default method to the instance dictionary.
            // E.g., for `(/=)` with no instance binding:
            //   default$Eq$/= dict$Eq$Int
            // The default method was compiled in desugarClassDecl (section 3).
            const default_fn = try alloc.create(ast_mod.Expr);
            default_fn.* = ast_mod.Expr{
                .Var = ast_mod.Id{
                    .name = Name{
                        .base = try std.fmt.allocPrint(alloc, "default${s}${s}", .{ id_decl.class_name.base, method.name.base }),
                        .unique = ctx.u_supply.fresh(),
                    },
                    .ty = try method.ty.toCore(alloc),
                    .span = id_decl.span,
                },
            };
            // Apply the default function to the instance dictionary.
            const dict_ref = try alloc.create(ast_mod.Expr);
            dict_ref.* = ast_mod.Expr{
                .Var = ast_mod.Id{
                    .name = dict_name,
                    .ty = ast_mod.CoreType{ .TyCon = .{ .name = dict_con_name, .args = &.{} } },
                    .span = id_decl.span,
                },
            };
            const app = try alloc.create(ast_mod.Expr);
            app.* = ast_mod.Expr{
                .App = .{
                    .fn_expr = default_fn,
                    .arg = dict_ref,
                    .span = id_decl.span,
                },
            };
            method_exprs[i] = app;
        } else {
            // Missing method with no default — emit diagnostic.
            const msg = try std.fmt.allocPrint(
                alloc,
                "missing method `{s}` in instance `{s} {s}`",
                .{ method.name.base, id_decl.class_name.base, head_name },
            );
            try ctx.diags.emit(alloc, .{
                .severity = .@"error",
                .code = .type_error,
                .span = id_decl.span,
                .message = msg,
            });
            // Use error expression as placeholder
            const err_expr = try alloc.create(ast_mod.Expr);
            err_expr.* = ast_mod.Expr{
                .Var = ast_mod.Id{
                    .name = Known.Fn.@"error",
                    .ty = try method.ty.toCore(alloc),
                    .span = id_decl.span,
                },
            };
            method_exprs[i] = err_expr;
        }
    }

    // Build: MkDict$Class method1 method2 ...
    // This is a chain of App nodes: ((MkDict$Class m1) m2) ...
    const con_ty = ast_mod.CoreType{ .TyCon = .{ .name = dict_con_name, .args = &.{} } };
    var dict_expr: *const ast_mod.Expr = blk: {
        const p = try alloc.create(ast_mod.Expr);
        p.* = ast_mod.Expr{
            .Var = ast_mod.Id{
                .name = dict_con_name,
                .ty = con_ty,
                .span = id_decl.span,
            },
        };
        break :blk p;
    };

    for (method_exprs) |method_expr| {
        const app = try alloc.create(ast_mod.Expr);
        app.* = ast_mod.Expr{
            .App = .{
                .fn_expr = dict_expr,
                .arg = method_expr,
                .span = id_decl.span,
            },
        };
        dict_expr = app;
    }

    // If the instance has context constraints, wrap the dictionary expression
    // with lambdas for each constraint.  E.g. for `instance Show a => Show [a]`:
    //   dict$Show$List = \dict$Show -> MkDict$Show (\xs -> showListWith dict$Show xs)
    // This makes the dictionary a function that accepts the sub-dictionaries.
    if (id_decl.context.len > 0) {
        var i = id_decl.context.len;
        while (i > 0) {
            i -= 1;
            const dict_param_ty = ast_mod.CoreType{ .TyCon = .{
                .name = Name{
                    .base = try std.fmt.allocPrint(alloc, "Dict${s}", .{id_decl.context[i].class_name.base}),
                    .unique = .{ .value = 0 },
                },
                .args = &.{},
            } };
            const wrapped = try alloc.create(ast_mod.Expr);
            wrapped.* = .{ .Lam = .{
                .binder = .{
                    .name = context_param_names[i],
                    .ty = dict_param_ty,
                    .span = id_decl.span,
                },
                .body = dict_expr,
                .span = id_decl.span,
            } };
            dict_expr = wrapped;
        }
    }

    // The dictionary binding type (placeholder — not critical for GRIN translation).
    const dict_ty = ast_mod.CoreType{ .TyCon = .{ .name = dict_con_name, .args = &.{} } };
    const dict_id = ast_mod.Id{
        .name = dict_name,
        .ty = dict_ty,
        .span = id_decl.span,
    };

    try binds.append(alloc, .{ .NonRec = .{
        .binder = dict_id,
        .rhs = dict_expr,
    } });
}

/// Extract a string name from an instance head type for dictionary naming.
/// E.g., `Int` → "Int", `[a]` → "List", `(a, b)` → "Tuple2".
fn instanceHeadName(alloc: std.mem.Allocator, ty: @import("../frontend/ast.zig").Type) std.mem.Allocator.Error![]const u8 {
    return switch (ty) {
        .Con => |qname| try alloc.dupe(u8, qname.name),
        .App => |parts| if (parts.len > 0) instanceHeadName(alloc, parts[0].*) else try alloc.dupe(u8, "Unknown"),
        .List => try alloc.dupe(u8, "List"),
        .Tuple => try alloc.dupe(u8, "Tuple"),
        .Paren => |inner| instanceHeadName(alloc, inner.*),
        .Var => |name| try alloc.dupe(u8, name),
        .Fun, .Forall, .IParam => try alloc.dupe(u8, "Unknown"),
    };
}

// ── Dictionary-passing helpers ─────────────────────────────────────────

/// Build the evidence map from solved constraints in `ModuleTypes`.
///
/// Iterates over `wanted_constraints` and for each `Class` constraint that
/// has both a `var_unique` and resolved `evidence`, inserts an entry keyed
/// by `(var_unique, span_start, class_unique)`.
fn buildEvidenceMap(ctx: *DesugarCtx) std.mem.Allocator.Error!void {
    for (ctx.types.wanted_constraints.items) |c| {
        switch (c) {
            .Class => |cc| {
                const ev = cc.evidence orelse continue;
                const vu = cc.var_unique orelse continue;
                const key = DesugarCtx.EvidenceKey{
                    .var_unique = vu.value,
                    .span_start_line = cc.span.start.line,
                    .span_start_col = cc.span.start.column,
                    .class_unique = cc.class_name.unique.value,
                };
                try ctx.evidence_map.put(ctx.alloc, key, ev);
            },
            .Eq => {},
        }
    }
}

/// Wrap a function body with dictionary lambda parameters for each class
/// constraint in the function's type scheme.
///
/// For `f :: Eq a => a -> Bool`, this transforms `\x -> body` into
/// `\dict$Eq -> \x -> body`, where `dict$Eq` is a fresh binder for the
/// Eq dictionary parameter.
fn wrapWithDictLambdas(
    ctx: *DesugarCtx,
    scheme: env_mod.TyScheme,
    body: *const ast_mod.Expr,
    span: SourceSpan,
) std.mem.Allocator.Error!*const ast_mod.Expr {
    if (scheme.constraints.len == 0) return body;

    const alloc = ctx.alloc;
    var current: *const ast_mod.Expr = body;

    // Wrap in reverse order so the first constraint is the outermost lambda.
    var i = scheme.constraints.len;
    while (i > 0) {
        i -= 1;
        const constraint = scheme.constraints[i];

        // Reuse the pre-populated name if available (set before body desugaring),
        // otherwise generate a fresh one.
        const dict_param_name = ctx.dict_param_names.get(constraint.class_name.unique.value) orelse Name{
            .base = try std.fmt.allocPrint(alloc, "dict${s}", .{constraint.class_name.base}),
            .unique = ctx.u_supply.fresh(),
        };

        // The dictionary parameter type is a placeholder.
        // A full implementation would compute the proper dictionary type.
        const dict_ty = ast_mod.CoreType{ .TyCon = .{
            .name = Name{
                .base = try std.fmt.allocPrint(alloc, "Dict${s}", .{constraint.class_name.base}),
                .unique = .{ .value = 0 },
            },
            .args = &.{},
        } };

        const wrapped = try alloc.create(ast_mod.Expr);
        wrapped.* = .{ .Lam = .{
            .binder = .{ .name = dict_param_name, .ty = dict_ty, .span = span },
            .body = current,
            .span = span,
        } };
        current = wrapped;
    }

    return current;
}

/// Convert a `DictEvidence` to a Core expression.
///
/// - `instance`: looks up the dictionary name from `ctx.dict_names` and
///   returns a `Var` reference.
/// - `param`: returns a `Var` referencing the enclosing function's
///   dictionary parameter (identified by class name).
/// - `superclass`: not yet implemented (tracked by #558).
fn buildDictExpr(
    ctx: *DesugarCtx,
    evidence: *const solver_mod.DictEvidence,
    span: SourceSpan,
) std.mem.Allocator.Error!*const ast_mod.Expr {
    const alloc = ctx.alloc;
    switch (evidence.*) {
        .instance => |inst| {
            // Look up the dictionary name by (class, head_type_name).
            const head_name = htypeHeadName(inst.head_ty);
            const dict_name = lookupDictName(&ctx.dict_names, inst.class_name.unique.value, head_name);

            if (dict_name) |dn| {
                var node = try alloc.create(ast_mod.Expr);
                const dict_ty = ast_mod.CoreType{ .TyCon = .{
                    .name = Name{
                        .base = try std.fmt.allocPrint(alloc, "Dict${s}", .{inst.class_name.base}),
                        .unique = .{ .value = 0 },
                    },
                    .args = &.{},
                } };
                node.* = .{ .Var = .{ .name = dn, .ty = dict_ty, .span = span } };

                // Apply context evidence as arguments for constrained instances.
                // E.g. for `Show [Int]` resolved via `instance Show a => Show [a]`,
                // the context_evidence contains [Show Int], so we generate:
                //   dict$Show$List dict$Show$Int
                for (inst.context_evidence) |ctx_ev| {
                    const sub_dict = try buildDictExpr(ctx, &ctx_ev, span);
                    const app = try alloc.create(ast_mod.Expr);
                    app.* = .{ .App = .{
                        .fn_expr = node,
                        .arg = sub_dict,
                        .span = span,
                    } };
                    node = app;
                }

                return node;
            } else {
                // Dictionary not found — emit a placeholder.
                // This can happen if the instance was not in scope.
                const node = try alloc.create(ast_mod.Expr);
                const name = Name{
                    .base = try std.fmt.allocPrint(alloc, "dict${s}${s}", .{ inst.class_name.base, head_name }),
                    .unique = ctx.u_supply.fresh(),
                };
                node.* = .{ .Var = .{
                    .name = name,
                    .ty = ast_mod.CoreType{ .TyCon = .{
                        .name = Name{ .base = "Dict", .unique = .{ .value = 0 } },
                        .args = &.{},
                    } },
                    .span = span,
                } };
                return node;
            }
        },
        .param => |p| {
            // Reference the dictionary parameter of the enclosing function.
            // Look up the actual unique from dict_param_names, which was
            // populated by wrapWithDictLambdas when the enclosing function's
            // dictionary lambda was created.
            const node = try alloc.create(ast_mod.Expr);
            const dict_param_name = if (ctx.dict_param_names.get(p.class_name.unique.value)) |name|
                name
            else
                Name{
                    .base = try std.fmt.allocPrint(alloc, "dict${s}", .{p.class_name.base}),
                    .unique = .{ .value = 0 },
                };
            node.* = .{ .Var = .{
                .name = dict_param_name,
                .ty = ast_mod.CoreType{ .TyCon = .{
                    .name = Name{
                        .base = try std.fmt.allocPrint(alloc, "Dict${s}", .{p.class_name.base}),
                        .unique = .{ .value = 0 },
                    },
                    .args = &.{},
                } },
                .span = span,
            } };
            return node;
        },
        .superclass => {
            // tracked in: https://github.com/adinapoli/rusholme/issues/558
            // For now, emit a placeholder that will fail at a later stage.
            const node = try alloc.create(ast_mod.Expr);
            node.* = .{ .Var = .{
                .name = Name{ .base = "superclass_dict_placeholder", .unique = ctx.u_supply.fresh() },
                .ty = ast_mod.CoreType{ .TyCon = .{
                    .name = Name{ .base = "Dict", .unique = .{ .value = 0 } },
                    .args = &.{},
                } },
                .span = span,
            } };
            return node;
        },
    }
}

/// Linear scan lookup for dictionary names.
///
/// Works around an issue where `ArrayHashMap.get()` fails to find
/// entries that were seeded from an external map (likely a hash
/// function inconsistency when keys are copied between maps).
fn lookupDictName(map: *const DesugarCtx.DictNameMap, class_unique: u64, head_name: []const u8) ?Name {
    for (map.keys(), map.values()) |k, v| {
        if (k.class_unique == class_unique and std.mem.eql(u8, k.head_name, head_name)) {
            return v;
        }
    }
    return null;
}

/// Extract a base name from an HType for dictionary name lookup.
/// Maps concrete types to their base name string (e.g. `Con(Int)` → "Int").
fn htypeHeadName(ty: htype_mod.HType) []const u8 {
    const chased = ty.chase();
    return switch (chased) {
        .Con => |c| if (std.mem.eql(u8, c.name.base, "[]")) "List" else c.name.base,
        .Rigid => |r| r.base,
        .AppTy => |a| htypeHeadName(a.head.*),
        .Meta => "Meta",
        .Fun => "Fun",
        .ForAll => "ForAll",
    };
}

/// Look up all solved evidence entries for a given variable use site.
///
/// Returns the evidence entries keyed by `(var_unique, span)` that match
/// the given variable and span. Used by `desugarExpr` to find which
/// dictionary arguments to insert at a method call site.
fn findEvidenceForVar(
    ctx: *const DesugarCtx,
    var_unique: u64,
    span: SourceSpan,
    scheme: env_mod.TyScheme,
) std.mem.Allocator.Error![]const *const solver_mod.DictEvidence {
    if (scheme.constraints.len == 0) return &.{};

    var result = std.ArrayListUnmanaged(*const solver_mod.DictEvidence){};
    for (scheme.constraints) |constraint| {
        const key = DesugarCtx.EvidenceKey{
            .var_unique = var_unique,
            .span_start_line = span.start.line,
            .span_start_col = span.start.column,
            .class_unique = constraint.class_name.unique.value,
        };
        if (ctx.evidence_map.get(key)) |ev| {
            try result.append(ctx.alloc, ev);
        }
    }
    return try result.toOwnedSlice(ctx.alloc);
}

// ── Foreign import prim helpers ────────────────────────────────────────

/// Count the number of top-level function arrows in a Core type.
/// `Int -> Int -> Bool` has arity 2.
/// `forall a. a -> a` has arity 1 (skips ForAllTy).
/// Count the number of `Fun` arrows in an HType.
///
/// For `a -> b -> c` this returns 2. Used to determine how many
/// extra parameters a class method selector needs for eta-expansion.
fn countFunArity(ty: htype_mod.HType) u32 {
    var count: u32 = 0;
    var current = ty;
    while (true) {
        const chased = current.chase();
        switch (chased) {
            .Fun => |f| {
                count += 1;
                current = f.res.*;
            },
            .ForAll => |fa| {
                current = fa.body.*;
            },
            else => break,
        }
    }
    return count;
}

fn countFunctionArity(ty: ast_mod.CoreType) u32 {
    var count: u32 = 0;
    var current = ty;
    while (true) {
        switch (current) {
            .FunTy => |f| {
                count += 1;
                current = f.res.*;
            },
            .ForAllTy => |fa| {
                current = fa.body.*;
            },
            else => break,
        }
    }
    return count;
}

/// Build a Core lambda wrapper for a foreign import prim declaration.
///
/// For `foreign import prim "add_Int" primAddInt :: Int -> Int -> Int`,
/// generates:
///
///   primAddInt = \x0 -> \x1 -> add_Int x0 x1
///
/// The inner `add_Int` uses the stable PrimOp Name from the registry,
/// which the GRIN translator and LLVM backend already know how to handle.
fn buildPrimOpWrapper(
    alloc: std.mem.Allocator,
    ctx: *DesugarCtx,
    binding_name: Name,
    primop_name: Name,
    core_ty: ast_mod.CoreType,
    arity: u32,
    span: SourceSpan,
) !ast_mod.Bind {
    // Collect parameter types by walking the FunTy chain.
    var param_types = std.ArrayListUnmanaged(ast_mod.CoreType){};
    defer param_types.deinit(alloc);
    var result_ty = core_ty;
    // Skip ForAllTy wrappers.
    while (result_ty == .ForAllTy) {
        result_ty = result_ty.ForAllTy.body.*;
    }
    for (0..arity) |_| {
        switch (result_ty) {
            .FunTy => |f| {
                try param_types.append(alloc, f.arg.*);
                result_ty = f.res.*;
            },
            else => break,
        }
    }

    // Generate fresh parameter names and Ids.
    var param_ids = try alloc.alloc(ast_mod.Id, arity);
    for (0..arity) |i| {
        const param_name = ctx.u_supply.freshName("x");
        const param_ty = if (i < param_types.items.len)
            param_types.items[i]
        else
            ast_mod.CoreType{ .TyCon = .{
                .name = Name{ .base = "Any", .unique = .{ .value = 0 } },
                .args = &.{},
            } };
        param_ids[i] = ast_mod.Id{
            .name = param_name,
            .ty = param_ty,
            .span = span,
        };
    }

    // Build the innermost expression: primop_name x0 x1 ... xN
    // Core uses curried application: App(App(primop, x0), x1)
    var primop_id = ast_mod.Id{
        .name = primop_name,
        .ty = core_ty,
        .span = span,
    };
    var body_ptr = try alloc.create(ast_mod.Expr);
    body_ptr.* = .{ .Var = primop_id };

    for (param_ids) |param| {
        const arg_ptr = try alloc.create(ast_mod.Expr);
        arg_ptr.* = .{ .Var = param };

        const new_body = try alloc.create(ast_mod.Expr);
        new_body.* = .{ .App = .{
            .fn_expr = body_ptr,
            .arg = arg_ptr,
            .span = span,
        } };
        body_ptr = new_body;

        // Update primop_id type for the next application (strip one FunTy).
        switch (primop_id.ty) {
            .FunTy => |f| primop_id.ty = f.res.*,
            else => {},
        }
    }

    // Wrap in lambdas: \x0 -> \x1 -> ... -> body
    // Build from inside out (last parameter first).
    var i: usize = arity;
    while (i > 0) {
        i -= 1;
        const lam_body = body_ptr;
        body_ptr = try alloc.create(ast_mod.Expr);
        body_ptr.* = .{ .Lam = .{
            .binder = param_ids[i],
            .body = lam_body,
            .span = span,
        } };
    }

    const binder_id = ast_mod.Id{
        .name = binding_name,
        .ty = core_ty,
        .span = span,
    };

    return .{ .NonRec = .{
        .binder = binder_id,
        .rhs = body_ptr,
    } };
}

fn desugarRhs(ctx: *DesugarCtx, rhs: renamer_mod.RRhs) !ast_mod.Expr {
    switch (rhs) {
        .UnGuarded => |expr| return (try desugarExpr(ctx, expr)).*,
        .Guarded => |grhs_list| return desugarGuardedRhs(ctx, grhs_list),
    }
}

/// Desugar a sequence of guarded RHS alternatives into nested Core `if/case`
/// expressions.
///
/// Each `RGuardedRhs` has a list of guards and an RHS expression.  Guards are
/// desugared left-to-right as conjunctive conditions:
///
///   | g1, g2 = rhs   →   if g1 then (if g2 then rhs else <next>) else <next>
///
/// The final fallback is the non-exhaustive error literal (same as in
/// `desugarMatch`).  The special name `otherwise` (and the literal `True`) are
/// recognised as always-true guards and short-circuit to the RHS directly.
///
/// Only `ExprGuard` is implemented here.  `PatGuard` (pattern guards,
/// `pat <- expr`) is a GHC extension not in Haskell 2010 and is not
/// yet supported.
fn desugarGuardedRhs(
    ctx: *DesugarCtx,
    grhs_list: []const renamer_mod.RGuardedRhs,
) !ast_mod.Expr {
    const alloc = ctx.alloc;

    // Start with the non-exhaustive fallback.
    var fallback = try alloc.create(ast_mod.Expr);
    fallback.* = .{
        .Lit = .{
            .val = .{ .String = "Non-exhaustive patterns in function" },
            .span = syntheticSpan(),
        },
    };

    // Build from the last guarded RHS back to the first so that each
    // alternative wraps around the previous fallback.
    var idx: usize = grhs_list.len;
    while (idx > 0) {
        idx -= 1;
        const grhs = grhs_list[idx];

        var rhs_expr = try desugarExpr(ctx, grhs.rhs);

        // Apply guards from right to left (innermost guard wraps rhs_expr,
        // outer guards wrap that result with the same fallback).
        var g_idx: usize = grhs.guards.len;
        while (g_idx > 0) {
            g_idx -= 1;
            const guard = grhs.guards[g_idx];
            switch (guard) {
                .ExprGuard => |cond_expr| {
                    // `otherwise` and `True` are always-true sentinels — emit
                    // the RHS directly without a conditional wrapper.
                    const is_trivially_true = switch (cond_expr) {
                        .Var => |v| std.mem.eql(u8, v.name.base, "otherwise") or
                            std.mem.eql(u8, v.name.base, "True"),
                        else => false,
                    };
                    if (is_trivially_true) continue;

                    // General boolean guard: desugar to
                    //   case <cond> of { True -> rhs ; _ -> fallback }
                    const cond = try desugarExpr(ctx, cond_expr);

                    const dummy_ty = ast_mod.CoreType{
                        .TyVar = Name{ .base = "_t", .unique = .{ .value = 0 } },
                    };
                    const wild_id = ast_mod.Id{
                        .name = Name{ .base = "wild", .unique = ctx.u_supply.fresh() },
                        .ty = dummy_ty,
                        .span = syntheticSpan(),
                    };

                    var alts = try alloc.alloc(ast_mod.Alt, 2);
                    alts[0] = .{
                        .con = .{ .DataAlt = ctx.true_name },
                        .binders = &.{},
                        .body = rhs_expr,
                    };
                    alts[1] = .{
                        .con = .Default,
                        .binders = &.{},
                        .body = fallback,
                    };

                    const new_rhs = try alloc.create(ast_mod.Expr);
                    new_rhs.* = .{ .Case = .{
                        .scrutinee = cond,
                        .binder = wild_id,
                        .ty = dummy_ty,
                        .alts = alts,
                        .span = syntheticSpan(),
                    } };
                    rhs_expr = new_rhs;
                },
                .PatGuard => {
                    // Pattern guards are a GHC extension, not in Haskell 2010.
                    // Emit the RHS unconditionally so compilation does not panic;
                    // a proper implementation is left for a future issue.
                    // tracked in: https://github.com/adinapoli/rusholme/issues/417
                    break;
                },
            }
        }

        // This guarded RHS result becomes the new fallback for the previous one.
        fallback = rhs_expr;
    }

    return fallback.*;
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

                // If this variable has class constraints, look up the solved
                // evidence and wrap the variable in App nodes with dictionary
                // arguments.
                const evidences = try findEvidenceForVar(ctx, v.name.unique.value, v.span, scheme);
                if (evidences.len > 0) {
                    var current: *const ast_mod.Expr = node;
                    for (evidences) |ev| {
                        const dict_arg = try buildDictExpr(ctx, ev, v.span);
                        const app_node = try alloc.create(ast_mod.Expr);
                        app_node.* = .{ .App = .{
                            .fn_expr = current,
                            .arg = dict_arg,
                            .span = v.span,
                        } };
                        current = app_node;
                    }
                    return @constCast(current);
                }
            } else {
                std.debug.panic("Variable {s} (id {d}) not found in type definitions", .{ v.name.base, v.name.unique.value });
            }

            // Even for variables found in local_binders, check if there's a
            // polymorphic scheme with constraints.  This handles recursive
            // calls to constrained functions: `showListTail` is in
            // local_binders (mono binding from Pass 1) but also has a scheme
            // with `Show a =>` constraints.  Without this, the dictionary
            // argument is omitted from the recursive call.
            if (ctx.types.schemes.get(v.name.unique)) |scheme| {
                if (scheme.constraints.len > 0) {
                    const evidences = try findEvidenceForVar(ctx, v.name.unique.value, v.span, scheme);
                    if (evidences.len > 0) {
                        var current: *const ast_mod.Expr = node;
                        for (evidences) |ev| {
                            const dict_arg = try buildDictExpr(ctx, ev, v.span);
                            const app_node = try alloc.create(ast_mod.Expr);
                            app_node.* = .{ .App = .{
                                .fn_expr = current,
                                .arg = dict_arg,
                                .span = v.span,
                            } };
                            current = app_node;
                        }
                        return @constCast(current);
                    }
                }
            }
        },
        .Lit => |l| {
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
                            const ty_ptr = ctx.types.local_binders.get(fb.name.unique) orelse {
                                std.debug.panic("Missing type for let funbind {s}", .{fb.name.base});
                            };
                            const ty = try htypeToCore(alloc, ty_ptr);

                            // Check if this let-bound function needs the match compiler
                            // (multiple equations or non-Var patterns).
                            var needs_match_compiler = fb.equations.len > 1;
                            if (!needs_match_compiler) {
                                for (fb.equations[0].patterns) |pat| {
                                    if (pat != .Var) {
                                        needs_match_compiler = true;
                                        break;
                                    }
                                }
                            }

                            const rhs = try alloc.create(ast_mod.Expr);
                            if (needs_match_compiler) {
                                rhs.* = (try desugarMatch(ctx, fb.equations, ty)).*;
                            } else {
                                const eq = fb.equations[0];
                                var body_expr = try desugarRhs(ctx, eq.rhs);

                                // Wrap body in lambdas for parameters (right-to-left).
                                var i = eq.patterns.len;
                                while (i > 0) {
                                    i -= 1;
                                    const pat = eq.patterns[i];
                                    switch (pat) {
                                        .Var => |v| {
                                            const p_body = try alloc.create(ast_mod.Expr);
                                            p_body.* = body_expr;

                                            const p_ty_ptr = ctx.types.local_binders.get(v.name.unique) orelse {
                                                std.debug.panic("Missing type for let param {s}", .{v.name.base});
                                            };
                                            const p_ty = try htypeToCore(alloc, p_ty_ptr);

                                            body_expr = ast_mod.Expr{
                                                .Lam = .{
                                                    .binder = ast_mod.Id{ .name = v.name, .ty = p_ty, .span = v.span },
                                                    .body = p_body,
                                                    .span = syntheticSpan(),
                                                },
                                            };
                                        },
                                        else => unreachable, // guarded by needs_match_compiler check
                                    }
                                }
                                rhs.* = body_expr;
                            }

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

            // Use NonRec for single bindings (avoids unnecessary heap
            // indirection in the Rec store/update path). A full dependency
            // analysis (#566) would allow nested NonRec for multiple
            // independent bindings; for now, multiple bindings still
            // default to Rec for safety.
            const owned_pairs = try pairs.toOwnedSlice(alloc);
            const bind: ast_mod.Bind = if (owned_pairs.len == 1)
                .{ .NonRec = .{
                    .binder = owned_pairs[0].binder,
                    .rhs = owned_pairs[0].rhs,
                } }
            else
                .{ .Rec = owned_pairs };

            node.* = .{ .Let = .{
                .bind = bind,
                .body = body,
                .span = syntheticSpan(),
            } };
        },
        .If => {
            // The renamer desugars if-then-else into Case on True/False,
            // so the desugarer should never encounter .If nodes.
            unreachable;
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
        .Case => |c| {
            // Desugar case expressions using the same pattern-match
            // compiler infrastructure as function equations (applyPat).
            //
            //   case scrut of { p1 -> rhs1; p2 -> rhs2; ... }
            //
            // becomes nested Core Case expressions, built bottom-to-top:
            // the last alternative's failure falls through to a
            // non-exhaustive error, each earlier alternative wraps the
            // accumulated body as its failure branch.

            const scrut_core = try desugarExpr(ctx, c.scrutinee.*);

            // Synthetic binder for the scrutinee value.
            const scrut_id = ast_mod.Id{
                .name = .{ .base = "_case_scrut", .unique = ctx.u_supply.fresh() },
                .ty = dummyCoreType(),
                .span = syntheticSpan(),
            };

            // Start with a non-exhaustive error as the fallback.
            var current_body = try alloc.create(ast_mod.Expr);
            current_body.* = .{
                .Lit = .{
                    .val = .{ .String = "Non-exhaustive patterns in case" },
                    .span = syntheticSpan(),
                },
            };

            // Process alternatives bottom-to-top.
            var alt_idx: usize = c.alts.len;
            while (alt_idx > 0) {
                alt_idx -= 1;
                const alt = c.alts[alt_idx];

                const rhs_body = try alloc.create(ast_mod.Expr);
                rhs_body.* = try desugarRhs(ctx, alt.rhs);

                current_body = try applyPat(
                    ctx,
                    scrut_core,
                    scrut_id,
                    dummyCoreType(),
                    alt.pattern,
                    rhs_body,
                    current_body,
                    0,
                    0,
                );
            }

            node.* = current_body.*;
        },
        .Do => {
            // Do-notation desugaring (issue #464)
            //
            // Desugars do-notation statements into bind chaining:
            //   do { x <- m; body }   →   m >>= (\x -> body)
            //   do { m; body }        →   m >> body
            //   do { let x = v; body} →   let x = v in body
            //
            // Build from right to left: the rightmost statement is the innermost body.
            const dummy_ty = ast_mod.CoreType{ .TyVar = Name{ .base = "_t", .unique = .{ .value = 0 } } };

            // Start with the last statement as the initial body
            var body: *ast_mod.Expr = undefined;
            var last_idx = expr.Do.len;

            // First, find the rightmost qualifier or stmt to start
            while (last_idx > 0) {
                last_idx -= 1;
                const stmt = expr.Do[last_idx];
                if (stmt == .Qualifier or stmt == .Stmt) {
                    const expr_ptr = if (stmt == .Qualifier) stmt.Qualifier else stmt.Stmt;
                    body = try desugarExpr(ctx, expr_ptr);
                    break;
                } else if (stmt == .Generator) {
                    // x <- m - need a dummy body for now, will be wrapped below
                    const dummy_body = try alloc.create(ast_mod.Expr);
                    dummy_body.* = .{ .Var = .{
                        .name = Name{ .base = "unit", .unique = Known.Con.Unit.unique },
                        .ty = dummy_ty,
                        .span = syntheticSpan(),
                    } };
                    body = dummy_body;
                    break;
                } else if (stmt == .LetStmt) {
                    // let statements define bindings, use unit as body
                    const dummy_body = try alloc.create(ast_mod.Expr);
                    dummy_body.* = .{ .Var = .{
                        .name = Name{ .base = "unit", .unique = Known.Con.Unit.unique },
                        .ty = dummy_ty,
                        .span = syntheticSpan(),
                    } };
                    body = dummy_body;
                    break;
                }
            }

            if (last_idx == 0 and expr.Do.len > 0) {
                // Didn't find a starting point, handle first statement
                const first_stmt = expr.Do[0];
                if (first_stmt == .Qualifier) {
                    body = try desugarExpr(ctx, first_stmt.Qualifier);
                } else if (first_stmt == .Stmt) {
                    body = try desugarExpr(ctx, first_stmt.Stmt);
                } else {
                    const dummy_body = try alloc.create(ast_mod.Expr);
                    dummy_body.* = .{ .Var = .{
                        .name = Name{ .base = "unit", .unique = Known.Con.Unit.unique },
                        .ty = dummy_ty,
                        .span = syntheticSpan(),
                    } };
                    body = dummy_body;
                }
            }

            // Process remaining statements from right to left
            while (last_idx > 0) {
                last_idx -= 1;
                const stmt = expr.Do[last_idx];

                switch (stmt) {
                    .Generator => |g| {
                        // x <- m  =>  m >>= (\x -> body)
                        const m_expr = try desugarExpr(ctx, g.expr);
                        const pat = g.pat;

                        // Build lambda: \x -> body
                        // For variable patterns: simple lambda
                        const binder_id = if (pat == .Var) blk: {
                            const v = pat.Var;
                            const ty_ptr = ctx.types.local_binders.get(v.name.unique);
                            const v_ty = if (ty_ptr) |p| try htypeToCore(alloc, p) else dummy_ty;
                            break :blk ast_mod.Id{ .name = v.name, .ty = v_ty, .span = v.span };
                        } else blk: {
                            // Complex pattern: use a fresh variable
                            const fresh_name = Name{
                                .base = "do_pat",
                                .unique = ctx.u_supply.fresh(),
                            };
                            break :blk ast_mod.Id{ .name = fresh_name, .ty = dummy_ty, .span = syntheticSpan() };
                        };

                        const p_body = try alloc.create(ast_mod.Expr);
                        p_body.* = body.*;

                        const lambda = try alloc.create(ast_mod.Expr);
                        lambda.* = .{ .Lam = .{
                            .binder = binder_id,
                            .body = p_body,
                            .span = syntheticSpan(),
                        } };

                        // Build (>>=) application: ((>>=) m) lambda
                        const bind_var = try alloc.create(ast_mod.Expr);
                        bind_var.* = .{ .Var = .{
                            .name = Known.Fn.bind,
                            .ty = dummy_ty,
                            .span = syntheticSpan(),
                        } };

                        const app1 = try alloc.create(ast_mod.Expr);
                        app1.* = .{ .App = .{
                            .fn_expr = bind_var,
                            .arg = m_expr,
                            .span = syntheticSpan(),
                        } };

                        const app2 = try alloc.create(ast_mod.Expr);
                        app2.* = .{ .App = .{
                            .fn_expr = app1,
                            .arg = lambda,
                            .span = syntheticSpan(),
                        } };

                        body = app2;
                    },
                    .Qualifier => |q| {
                        // m  =>  m >> body
                        const m_expr = try desugarExpr(ctx, q);

                        // Build (>>) application: ((>>) m) body
                        const then_var = try alloc.create(ast_mod.Expr);
                        then_var.* = .{ .Var = .{
                            .name = Known.Fn.then,
                            .ty = dummy_ty,
                            .span = syntheticSpan(),
                        } };

                        const app1 = try alloc.create(ast_mod.Expr);
                        app1.* = .{ .App = .{
                            .fn_expr = then_var,
                            .arg = m_expr,
                            .span = syntheticSpan(),
                        } };

                        const app2 = try alloc.create(ast_mod.Expr);
                        app2.* = .{ .App = .{
                            .fn_expr = app1,
                            .arg = body,
                            .span = syntheticSpan(),
                        } };

                        body = app2;
                    },
                    .Stmt => |s| {
                        // Same as qualifier - treat as m >> body
                        const m_expr = try desugarExpr(ctx, s);

                        const then_var = try alloc.create(ast_mod.Expr);
                        then_var.* = .{ .Var = .{
                            .name = Known.Fn.then,
                            .ty = dummy_ty,
                            .span = syntheticSpan(),
                        } };

                        const app1 = try alloc.create(ast_mod.Expr);
                        app1.* = .{ .App = .{
                            .fn_expr = then_var,
                            .arg = m_expr,
                            .span = syntheticSpan(),
                        } };

                        const app2 = try alloc.create(ast_mod.Expr);
                        app2.* = .{ .App = .{
                            .fn_expr = app1,
                            .arg = body,
                            .span = syntheticSpan(),
                        } };

                        body = app2;
                    },
                    .LetStmt => {
                        // let x = v; rest  =>  let x = v in body
                        // For now, we skip let statements in the reverse loop
                        // and assume they're at the beginning or already handled
                        continue;
                    },
                }
            }

            node.* = body.*;
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

            // If the operator has class constraints, look up the solved
            // evidence and wrap it in App nodes with dictionary arguments.
            var op_with_dicts: *const ast_mod.Expr = op_var;
            if (ctx.types.schemes.get(infix.op.unique)) |scheme| {
                const evidences = try findEvidenceForVar(ctx, infix.op.unique.value, infix.op_span, scheme);
                if (evidences.len > 0) {
                    // Build an App chain: (==) dict1 dict2 ...
                    for (evidences) |ev| {
                        const dict_arg = try buildDictExpr(ctx, ev, infix.op_span);
                        const dict_app = try alloc.create(ast_mod.Expr);
                        dict_app.* = .{ .App = .{
                            .fn_expr = op_with_dicts,
                            .arg = dict_arg,
                            .span = infix.op_span,
                        } };
                        op_with_dicts = dict_app;
                    }
                }
            }

            // Desugar left operand
            const left_result = try desugarExpr(ctx, infix.left.*);

            // Create app: (op dict...) left
            const app1 = try alloc.create(ast_mod.Expr);
            app1.* = .{ .App = .{
                .fn_expr = op_with_dicts,
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
        .EnumFrom => |enum_from| {
            // [n..] → enumFrom n
            const fn_var = try alloc.create(ast_mod.Expr);
            fn_var.* = .{ .Var = .{
                .name = enum_from.fn_name,
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = enum_from.span,
            } };
            const from_arg = try desugarExpr(ctx, enum_from.from.*);
            node.* = .{ .App = .{
                .fn_expr = fn_var,
                .arg = from_arg,
                .span = enum_from.span,
            } };
        },
        .EnumFromTo => |enum_from_to| {
            // [n..m] → enumFromTo n m
            const fn_var = try alloc.create(ast_mod.Expr);
            fn_var.* = .{ .Var = .{
                .name = enum_from_to.fn_name,
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = enum_from_to.span,
            } };
            const from_arg = try desugarExpr(ctx, enum_from_to.from.*);
            const to_arg = try desugarExpr(ctx, enum_from_to.to.*);
            const partial = try alloc.create(ast_mod.Expr);
            partial.* = .{ .App = .{
                .fn_expr = fn_var,
                .arg = from_arg,
                .span = enum_from_to.span,
            } };
            node.* = .{ .App = .{
                .fn_expr = partial,
                .arg = to_arg,
                .span = enum_from_to.span,
            } };
        },
        .EnumFromThen => |enum_from_then| {
            // [n,n2..] → enumFromThen n n2
            const fn_var = try alloc.create(ast_mod.Expr);
            fn_var.* = .{ .Var = .{
                .name = enum_from_then.fn_name,
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = enum_from_then.span,
            } };
            const from_arg = try desugarExpr(ctx, enum_from_then.from.*);
            const then_arg = try desugarExpr(ctx, enum_from_then.then.*);
            const partial = try alloc.create(ast_mod.Expr);
            partial.* = .{ .App = .{
                .fn_expr = fn_var,
                .arg = from_arg,
                .span = enum_from_then.span,
            } };
            node.* = .{ .App = .{
                .fn_expr = partial,
                .arg = then_arg,
                .span = enum_from_then.span,
            } };
        },
        .EnumFromThenTo => |enum_from_then_to| {
            // [n,n2..m] → enumFromThenTo n n2 m
            const fn_var = try alloc.create(ast_mod.Expr);
            fn_var.* = .{ .Var = .{
                .name = enum_from_then_to.fn_name,
                .ty = ast_mod.CoreType{ .TyVar = Name{ .base = "t", .unique = .{ .value = 0 } } },
                .span = enum_from_then_to.span,
            } };
            const from_arg = try desugarExpr(ctx, enum_from_then_to.from.*);
            const then_arg = try desugarExpr(ctx, enum_from_then_to.then.*);
            const to_arg = try desugarExpr(ctx, enum_from_then_to.to.*);
            const partial1 = try alloc.create(ast_mod.Expr);
            partial1.* = .{ .App = .{
                .fn_expr = fn_var,
                .arg = from_arg,
                .span = enum_from_then_to.span,
            } };
            const partial2 = try alloc.create(ast_mod.Expr);
            partial2.* = .{ .App = .{
                .fn_expr = partial1,
                .arg = then_arg,
                .span = enum_from_then_to.span,
            } };
            node.* = .{ .App = .{
                .fn_expr = partial2,
                .arg = to_arg,
                .span = enum_from_then_to.span,
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

    // Pre-register pattern variables in `local_binders` so that `desugarRhs`
    // can resolve them.  This is necessary for instance method bindings whose
    // bodies are not type-checked by `inferPat` (the typechecker skips
    // InstanceDecl bodies).  For top-level FunBinds this is a harmless no-op
    // because `inferPat` already populated `local_binders`.
    try registerPatBinders(ctx, equations, arg_tys);

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

        // ── List pattern ──────────────────────────────────────────────────
        //
        // `[]`       → Con(Nil, [])
        // `[p1,..,pn]` → InfixCon(p1, :, InfixCon(p2, :, ... Con(Nil, []) ...))
        //
        // We synthesise the equivalent `RPat` and recurse via `applyPat`.
        .List => |elems| blk: {
            // Build from the right: start with the Nil pattern.
            var right_pat = try ctx.alloc.create(renamer_mod.RPat);
            right_pat.* = renamer_mod.RPat{ .Con = .{
                .name = Known.Con.Nil,
                .con_span = syntheticSpan(),
                .args = &.{},
            } };

            // Wrap each element from the right: InfixCon(elem, :, right_pat)
            var i: usize = elems.len;
            while (i > 0) {
                i -= 1;
                const elem_ptr = try ctx.alloc.create(renamer_mod.RPat);
                elem_ptr.* = elems[i];

                const new_right = try ctx.alloc.create(renamer_mod.RPat);
                new_right.* = renamer_mod.RPat{ .InfixCon = .{
                    .left = elem_ptr,
                    .con = Known.Con.Cons,
                    .con_span = syntheticSpan(),
                    .right = right_pat,
                } };
                right_pat = new_right;
            }

            break :blk try applyPat(ctx, scrut_expr, scrut_id, scrut_ty, right_pat.*, success, failure, arg_idx, depth);
        },

        // ── Not yet implemented ───────────────────────────────────────────
        //
        // IMPORTANT: Each unsupported case MUST have a tracking issue.
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

/// Convert a CoreType back to HType so it can be stored in `local_binders`.
///
/// This is the inverse of `HType.toCore`.  Used by `registerPatBinders` to
/// populate `local_binders` for instance method pattern variables that were
/// never processed by the typechecker's `inferPat`.
fn coreTypeToHType(alloc: std.mem.Allocator, ty: ast_mod.CoreType) std.mem.Allocator.Error!*htype_mod.HType {
    const node = try alloc.create(htype_mod.HType);
    node.* = switch (ty) {
        .TyVar => |n| htype_mod.HType{ .Rigid = n },
        .TyCon => |tc| blk: {
            const args = try alloc.alloc(htype_mod.HType, tc.args.len);
            for (tc.args, 0..) |arg, i| {
                args[i] = (try coreTypeToHType(alloc, arg)).*;
            }
            break :blk htype_mod.HType{ .Con = .{ .name = tc.name, .args = args } };
        },
        .FunTy => |f| blk: {
            const arg_p = try coreTypeToHType(alloc, f.arg.*);
            const res_p = try coreTypeToHType(alloc, f.res.*);
            break :blk htype_mod.HType{ .Fun = .{ .arg = arg_p, .res = res_p } };
        },
        .ForAllTy => |fa| blk: {
            const body_p = try coreTypeToHType(alloc, fa.body.*);
            break :blk htype_mod.HType{ .ForAll = .{ .binder = fa.binder, .body = body_p } };
        },
    };
    return node;
}

/// Register pattern variables in `local_binders` so that `desugarExpr` can
/// find their types during RHS desugaring.
///
/// When instance methods have pattern-matching bindings (e.g. `show n = ...`),
/// the typechecker skips their bodies, so pattern variables are never added to
/// `local_binders` via `inferPat`.  This function fills that gap by walking
/// each equation's patterns and registering `.Var` patterns with the
/// corresponding argument type derived from the method's declared type.
fn registerPatBinders(
    ctx: *DesugarCtx,
    equations: []const renamer_mod.RMatch,
    arg_tys: []const ast_mod.CoreType,
) std.mem.Allocator.Error!void {
    for (equations) |eq| {
        for (eq.patterns, 0..) |pat, i| {
            if (i >= arg_tys.len) break;
            try registerPatBindersRec(ctx, pat, arg_tys[i]);
        }
    }
}

/// Recursively walk a pattern and register any variable binders in `local_binders`.
///
/// For top-level argument patterns, `ty` is the argument type from the method
/// signature.  For sub-patterns inside constructors, we pass a dummy type since
/// decomposing the constructor's field types is not available here; the
/// desugarer's `applyPat` will later assign the correct type in the Core AST
/// via the Case binder.
fn registerPatBindersRec(
    ctx: *DesugarCtx,
    pat: renamer_mod.RPat,
    ty: ast_mod.CoreType,
) std.mem.Allocator.Error!void {
    const dummy = dummyCoreType();
    switch (pat) {
        .Var => |v| {
            // Only register if not already present (the typechecker may have
            // populated it for top-level FunBinds).
            if (!ctx.types.local_binders.contains(v.name.unique)) {
                const hty = try coreTypeToHType(ctx.alloc, ty);
                try ctx.types.local_binders.put(ctx.alloc, v.name.unique, hty);
            }
        },
        .Paren => |inner| try registerPatBindersRec(ctx, inner.*, ty),
        .AsPat => |as_| {
            if (!ctx.types.local_binders.contains(as_.name.unique)) {
                const hty = try coreTypeToHType(ctx.alloc, ty);
                try ctx.types.local_binders.put(ctx.alloc, as_.name.unique, hty);
            }
            try registerPatBindersRec(ctx, as_.pat.*, ty);
        },
        .Con => |c| {
            for (c.args) |sub| try registerPatBindersRec(ctx, sub, dummy);
        },
        .InfixCon => |ic| {
            try registerPatBindersRec(ctx, ic.left.*, dummy);
            try registerPatBindersRec(ctx, ic.right.*, dummy);
        },
        .Tuple => |elems| {
            for (elems) |sub| try registerPatBindersRec(ctx, sub, dummy);
        },
        .List => |elems| {
            for (elems) |sub| try registerPatBindersRec(ctx, sub, dummy);
        },
        .Negate => |inner| try registerPatBindersRec(ctx, inner.*, ty),
        .RecPat => |rp| {
            for (rp.fields) |f| {
                if (f.pat) |sub| try registerPatBindersRec(ctx, sub.*, dummy);
            }
        },
        .Lit, .Wild => {},
    }
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
        .class_env = infer_mod.ClassEnv.init(alloc),
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
        .class_env = infer_mod.ClassEnv.init(alloc),
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
        .class_env = infer_mod.ClassEnv.init(alloc),
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
        .class_env = infer_mod.ClassEnv.init(alloc),
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

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{}, .class_env = infer_mod.ClassEnv.init(alloc) };
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

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{}, .class_env = infer_mod.ClassEnv.init(alloc) };
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

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{}, .class_env = infer_mod.ClassEnv.init(alloc) };
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

// ── List pattern tests (#418) ────────────────────────────────────────────────

test "desugarMatch: empty list pattern []" {
    // f [] = 0
    // f _  = 1
    // Type: [Int] -> Int
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{}, .class_env = infer_mod.ClassEnv.init(alloc) };
    defer types.deinit(alloc);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var u_supply = naming_mod.UniqueSupply{};
    var ctx = makeCtx(alloc, &types, &diags, &u_supply);

    const list_ty_name = testName("[]", 110);
    const int_ty_name = testName("Int", 1);
    const list_ty = ast_mod.CoreType{ .TyCon = .{ .name = list_ty_name, .args = &.{} } };
    const int_ty = ast_mod.CoreType{ .TyCon = .{ .name = int_ty_name, .args = &.{} } };
    const fun_ty = try singleArgFunTy(alloc, list_ty, int_ty);

    // [] pattern (empty list)
    const nil_pat = renamer_mod.RPat{ .List = &.{} };
    const wild_pat = renamer_mod.RPat{ .Wild = syntheticSpan() };

    const rhs0 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 0, .span = syntheticSpan() } } } };
    const rhs1 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 1, .span = syntheticSpan() } } } };

    const eq1 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{nil_pat}), .rhs = rhs0, .span = syntheticSpan() };
    const eq2 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{wild_pat}), .rhs = rhs1, .span = syntheticSpan() };

    const expr = try desugarMatch(&ctx, &.{ eq1, eq2 }, fun_ty);

    // \arg_0 -> case arg_0 { [] -> 0 ; _ -> 1 }
    // The empty list pattern desugars to Con(Nil,[]) which is a DataAlt on "[]".
    try testing.expect(expr.* == .Lam);
    const body = expr.Lam.body.*;
    try testing.expect(body == .Case);
    try testing.expectEqual(@as(usize, 2), body.Case.alts.len);

    const nil_alt = body.Case.alts[0];
    try testing.expect(nil_alt.con == .DataAlt);
    try testing.expectEqualStrings("[]", nil_alt.con.DataAlt.base);
    try testing.expectEqual(@as(usize, 0), nil_alt.binders.len);
    try testing.expect(nil_alt.body.* == .Lit);
    try testing.expectEqual(@as(i64, 0), nil_alt.body.Lit.val.Int);
}

test "desugarMatch: non-empty list pattern [x, y]" {
    // f [x, y] = x
    // f _      = 0
    // Type: [Int] -> Int
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{}, .class_env = infer_mod.ClassEnv.init(alloc) };
    defer types.deinit(alloc);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var u_supply = naming_mod.UniqueSupply{};
    var ctx = makeCtx(alloc, &types, &diags, &u_supply);

    const list_ty_name = testName("[]", 110);
    const int_ty_name = testName("Int", 1);
    const list_ty = ast_mod.CoreType{ .TyCon = .{ .name = list_ty_name, .args = &.{} } };
    const int_ty = ast_mod.CoreType{ .TyCon = .{ .name = int_ty_name, .args = &.{} } };
    const fun_ty = try singleArgFunTy(alloc, list_ty, int_ty);

    const x_name = testName("x", 91);
    const y_name = testName("y", 92);
    const x_pat = renamer_mod.RPat{ .Var = .{ .name = x_name, .span = syntheticSpan() } };
    const y_pat = renamer_mod.RPat{ .Var = .{ .name = y_name, .span = syntheticSpan() } };

    // [x, y] pattern
    const list_pat = renamer_mod.RPat{ .List = try alloc.dupe(renamer_mod.RPat, &.{ x_pat, y_pat }) };
    const wild_pat = renamer_mod.RPat{ .Wild = syntheticSpan() };

    const rhs1 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 42, .span = syntheticSpan() } } } };
    const rhs2 = renamer_mod.RRhs{ .UnGuarded = .{ .Lit = .{ .Int = .{ .value = 0, .span = syntheticSpan() } } } };

    const eq1 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{list_pat}), .rhs = rhs1, .span = syntheticSpan() };
    const eq2 = renamer_mod.RMatch{ .patterns = try alloc.dupe(renamer_mod.RPat, &.{wild_pat}), .rhs = rhs2, .span = syntheticSpan() };

    const expr = try desugarMatch(&ctx, &.{ eq1, eq2 }, fun_ty);

    // \arg_0 -> case arg_0 { (:) x ys -> case ys { (:) y [] -> 42 ; _ -> ... } ; _ -> 0 }
    // The outermost case must be a DataAlt on "(:)".
    try testing.expect(expr.* == .Lam);
    const body = expr.Lam.body.*;
    try testing.expect(body == .Case);

    const cons_alt = body.Case.alts[0];
    try testing.expect(cons_alt.con == .DataAlt);
    try testing.expectEqualStrings("(:)", cons_alt.con.DataAlt.base);
    // (:) binder 0 = x (Var sub-pattern), binder 1 = fresh tail binder
    try testing.expectEqual(@as(usize, 2), cons_alt.binders.len);
    try testing.expectEqualStrings("x", cons_alt.binders[0].name.base);
}

// ── Guard tests (#417) ───────────────────────────────────────────────────────

test "desugarRhs: simple boolean guard" {
    // | x > 0 = "pos"   (represented as ExprGuard with a Var placeholder)
    // | otherwise = "non-pos"
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{}, .class_env = infer_mod.ClassEnv.init(alloc) };
    defer types.deinit(alloc);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var u_supply = naming_mod.UniqueSupply{};
    var ctx = makeCtx(alloc, &types, &diags, &u_supply);

    // Use a Var "cond_var" as the guard expression (stands in for any boolean expr).
    // We need a type for it in the type environment.
    const bool_h_ty = try alloc.create(htype_mod.HType);
    bool_h_ty.* = .{ .Con = .{ .name = testName("Bool", 104), .args = &.{} } };
    const cond_name = testName("cond_var", 200);
    try types.local_binders.put(alloc, cond_name.unique, bool_h_ty);

    // Guard 1: ExprGuard(Var "cond_var") -> "pos"
    // Guard 2: ExprGuard(Var "otherwise") -> "non-pos"
    const cond_expr = renamer_mod.RExpr{ .Var = .{ .name = cond_name, .span = syntheticSpan() } };
    const otherwise_expr = renamer_mod.RExpr{ .Var = .{ .name = Known.Fn.otherwise, .span = syntheticSpan() } };

    // We need `otherwise` in the type env too.
    const bool_h_ty2 = try alloc.create(htype_mod.HType);
    bool_h_ty2.* = .{ .Con = .{ .name = testName("Bool", 104), .args = &.{} } };
    try types.local_binders.put(alloc, Known.Fn.otherwise.unique, bool_h_ty2);

    const grhs1 = renamer_mod.RGuardedRhs{
        .guards = try alloc.dupe(renamer_mod.RGuard, &.{.{ .ExprGuard = cond_expr }}),
        .rhs = .{ .Lit = .{ .String = .{ .value = "pos", .span = syntheticSpan() } } },
    };
    const grhs2 = renamer_mod.RGuardedRhs{
        .guards = try alloc.dupe(renamer_mod.RGuard, &.{.{ .ExprGuard = otherwise_expr }}),
        .rhs = .{ .Lit = .{ .String = .{ .value = "non-pos", .span = syntheticSpan() } } },
    };

    const rhs = renamer_mod.RRhs{ .Guarded = try alloc.dupe(renamer_mod.RGuardedRhs, &.{ grhs1, grhs2 }) };
    const result = try desugarRhs(&ctx, rhs);

    // Expected: case cond_var of { True -> "pos" ; _ -> "non-pos" }
    // (the `otherwise` guard is trivially true so grhs2 becomes the fallback directly)
    try testing.expect(result == .Case);
    try testing.expectEqual(@as(usize, 2), result.Case.alts.len);
    try testing.expect(result.Case.alts[0].con == .DataAlt);
    try testing.expectEqualStrings("True", result.Case.alts[0].con.DataAlt.base);
    try testing.expect(result.Case.alts[0].body.* == .Lit);
    try testing.expectEqualStrings("pos", result.Case.alts[0].body.Lit.val.String);
    // Default branch is the `otherwise` case body: "non-pos"
    try testing.expect(result.Case.alts[1].con == .Default);
    try testing.expect(result.Case.alts[1].body.* == .Lit);
    try testing.expectEqualStrings("non-pos", result.Case.alts[1].body.Lit.val.String);
}

test "desugarRhs: otherwise-only guard is transparent" {
    // | otherwise = 42
    // The `otherwise` sentinel should pass through directly without wrapping in a Case.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var types = infer_mod.ModuleTypes{ .schemes = .{}, .local_binders = .{}, .class_env = infer_mod.ClassEnv.init(alloc) };
    defer types.deinit(alloc);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var u_supply = naming_mod.UniqueSupply{};
    var ctx = makeCtx(alloc, &types, &diags, &u_supply);

    const otherwise_expr = renamer_mod.RExpr{ .Var = .{ .name = Known.Fn.otherwise, .span = syntheticSpan() } };
    const bool_h_ty = try alloc.create(htype_mod.HType);
    bool_h_ty.* = .{ .Con = .{ .name = testName("Bool", 104), .args = &.{} } };
    try types.local_binders.put(alloc, Known.Fn.otherwise.unique, bool_h_ty);

    const grhs = renamer_mod.RGuardedRhs{
        .guards = try alloc.dupe(renamer_mod.RGuard, &.{.{ .ExprGuard = otherwise_expr }}),
        .rhs = .{ .Lit = .{ .Int = .{ .value = 42, .span = syntheticSpan() } } },
    };

    const rhs = renamer_mod.RRhs{ .Guarded = try alloc.dupe(renamer_mod.RGuardedRhs, &.{grhs}) };
    const result = try desugarRhs(&ctx, rhs);

    // `otherwise` is trivially true: no Case wrapper, just the Lit directly.
    try testing.expect(result == .Lit);
    try testing.expectEqual(@as(i64, 42), result.Lit.val.Int);
}
