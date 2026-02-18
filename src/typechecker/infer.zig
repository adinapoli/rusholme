//! Algorithm W — Hindley-Milner type inference over the renamed AST.
//!
//! This module implements the classic Algorithm W (Damas & Milner 1982) over
//! the `RExpr` language produced by the renamer.  It operates in two modes:
//!
//! - **Synthesis** (`infer`): given an expression, compute its type.
//! - **Checking** (`check`): given an expression and an expected type, verify
//!   they agree (by synthesising and then unifying).
//!
//! ## Pointer discipline
//!
//! Every `HType` node produced by `infer` is arena-allocated and returned as
//! `*HType`.  This is essential for correctness: the unifier writes solutions
//! into `MetaVar.ref` fields in place, and those writes must be visible
//! through every alias of the node.  Returning `HType` by value would create
//! independent copies of the `Meta` struct — subsequent `ref` writes by the
//! solver would be invisible to callers holding the original value.
//!
//! The pattern throughout is therefore:
//!
//! ```zig
//! const ty: *HType = try infer(ctx, expr);
//! // Later, after constraints are solved:
//! const chased = ty.chase();  // follows ref chains; sees the solution
//! ```
//!
//! ## Algorithm outline (per expression)
//!
//! | Expression   | Rule |
//! |---|---|
//! | Variable     | Instantiate its scheme from the env |
//! | Literal      | Return the fixed literal type |
//! | Application  | Infer `f :: a -> b`, check `arg :: a`, yield `b` |
//! | Lambda       | Bind params as fresh metas, infer body |
//! | Let          | Infer binding, *generalise*, extend env, infer body |
//! | If           | Check cond :: Bool, unify branches |
//! | Case         | Infer scrutinee, check each alternative |
//! | Do           | Thread `IO a` through statement sequence |
//! | Tuple        | Infer each element, return `(a, b, …)` |
//! | List         | Infer elements, unify to common type `[a]` |
//! | InfixApp     | Desugar to application, same as App |
//! | TypeAnn      | Parse annotation, check expr against it |
//!
//! ## Generalisation (let-polymorphism)
//!
//! After inferring the type of a `let`-bound RHS, we *generalise*: collect
//! all unsolved metavariables in the inferred type that do not appear in the
//! current environment, and close over them with `forall`.  The binders of
//! the resulting `TyScheme` are recorded as rigid variables for downstream
//! instantiation.
//!
//! ## Error recovery
//!
//! Type errors are emitted into the caller-supplied `DiagnosticCollector`
//! and inference continues with a fresh metavar in place of the ill-typed
//! sub-expression.  This ensures that a single compilation surfaces as many
//! errors as possible.
//!
//! ## M1 scope / known limitations
//!
//! - Type-class constraints (issue #37) are not resolved here; they remain
//!   as unsolved metavariables.  Built-in numeric operations assume `Int`.
//! - `do`-notation assumes `IO` monad — no monad inference.
//! - Operator sections desugar to lambdas (synthetic metavars).
//! - Type annotations in source (`expr :: Type`) are parsed but the AST
//!   `Type` is not yet converted to `HType` — tracked as follow-up issue.
//! - Multi-equation function bindings unify each equation against a shared
//!   arena node so generalisation sees the fully-solved type.
//!
//! ## References
//!
//! - Damas & Milner, "Principal type-schemes for functional programs", POPL 1982.
//! - Peyton Jones (ed.), "Haskell 98 Language Report", chapter 4.
//! - Vytiniotis, Peyton Jones et al., "OutsideIn(X)", JFP 2011.

const std = @import("std");
const htype_mod = @import("htype.zig");
const env_mod = @import("env.zig");
const unify_mod = @import("unify.zig");
const solver_mod = @import("solver.zig");
const renamer_mod = @import("../renamer/renamer.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");
const span_mod = @import("../diagnostics/span.zig");
const known_mod = @import("../naming/known.zig");
const naming_mod = @import("../naming/unique.zig");

pub const HType = htype_mod.HType;
pub const MetaVar = htype_mod.MetaVar;
pub const MetaVarSupply = htype_mod.MetaVarSupply;
pub const TyScheme = env_mod.TyScheme;
pub const TyEnv = env_mod.TyEnv;
pub const Constraint = solver_mod.Constraint;
pub const DiagnosticCollector = diag_mod.DiagnosticCollector;
pub const DiagnosticCode = diag_mod.DiagnosticCode;
pub const Severity = diag_mod.Severity;
pub const SourceSpan = span_mod.SourceSpan;
pub const SourcePos = span_mod.SourcePos;
pub const RExpr = renamer_mod.RExpr;
pub const RDecl = renamer_mod.RDecl;
pub const RPat = renamer_mod.RPat;
pub const RAlt = renamer_mod.RAlt;
pub const RStmt = renamer_mod.RStmt;
pub const RRhs = renamer_mod.RRhs;
pub const RMatch = renamer_mod.RMatch;
pub const RenamedModule = renamer_mod.RenamedModule;
pub const Name = naming_mod.Name;
pub const UniqueSupply = naming_mod.UniqueSupply;
const Known = known_mod;

// ── InferCtx ───────────────────────────────────────────────────────────

/// Threading context for inference — bundles all the mutable state that
/// needs to be passed through every recursive call.
pub const InferCtx = struct {
    alloc: std.mem.Allocator,
    env: *TyEnv,
    mv_supply: *MetaVarSupply,
    u_supply: *UniqueSupply,
    diags: *DiagnosticCollector,

    pub fn init(
        alloc: std.mem.Allocator,
        env: *TyEnv,
        mv_supply: *MetaVarSupply,
        u_supply: *UniqueSupply,
        diags: *DiagnosticCollector,
    ) InferCtx {
        return .{
            .alloc = alloc,
            .env = env,
            .mv_supply = mv_supply,
            .u_supply = u_supply,
            .diags = diags,
        };
    }

    // ── Helpers ────────────────────────────────────────────────────────

    /// Allocate a fresh unsolved metavar on the arena and return a pointer.
    ///
    /// Callers must hold onto the `*HType` pointer — NOT a value copy — so
    /// that solver mutations to `Meta.ref` are visible through the pointer.
    pub fn freshMeta(self: *InferCtx) std.mem.Allocator.Error!*HType {
        const mv = self.mv_supply.fresh();
        const node = try self.alloc.create(HType);
        node.* = HType{ .Meta = mv };
        return node;
    }

    /// Allocate a fresh rigid `Name` for generalisation.
    pub fn freshRigid(self: *InferCtx, base: []const u8) Name {
        return self.u_supply.freshName(base);
    }

    /// Copy `ty` onto the arena, returning a stable `*HType` pointer.
    pub fn alloc_ty(self: *InferCtx, ty: HType) std.mem.Allocator.Error!*HType {
        const node = try self.alloc.create(HType);
        node.* = ty;
        return node;
    }

    /// Immediately unify two arena-allocated nodes.
    ///
    /// Errors are emitted as diagnostics; only `OutOfMemory` propagates.
    pub fn unifyNow(
        self: *InferCtx,
        lhs: *HType,
        rhs: *HType,
        span: SourceSpan,
    ) std.mem.Allocator.Error!void {
        unify_mod.unify(self.alloc, lhs, rhs) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InfiniteType => {
                const lhs_str = try fmtHType(self.alloc, lhs.*);
                const rhs_str = try fmtHType(self.alloc, rhs.*);
                const msg = try std.fmt.allocPrint(
                    self.alloc,
                    "infinite type: `{s}` ~ `{s}` (occurs check failed)",
                    .{ lhs_str, rhs_str },
                );
                try self.diags.emit(self.alloc, .{
                    .severity = .@"error",
                    .code = .type_error,
                    .span = span,
                    .message = msg,
                });
            },
            else => {
                const lhs_str = try fmtHType(self.alloc, lhs.*);
                const rhs_str = try fmtHType(self.alloc, rhs.*);
                const msg = try std.fmt.allocPrint(
                    self.alloc,
                    "cannot unify `{s}` with `{s}`",
                    .{ lhs_str, rhs_str },
                );
                try self.diags.emit(self.alloc, .{
                    .severity = .@"error",
                    .code = .type_error,
                    .span = span,
                    .message = msg,
                });
            },
        };
    }

    /// Emit a type-error diagnostic and return a fresh meta for recovery.
    pub fn recoverWithFreshMeta(
        self: *InferCtx,
        msg: []const u8,
        span: SourceSpan,
    ) std.mem.Allocator.Error!*HType {
        try self.diags.emit(self.alloc, .{
            .severity = .@"error",
            .code = .type_error,
            .span = span,
            .message = msg,
        });
        return self.freshMeta();
    }
};

// ── HType formatting (minimal, for diagnostics) ─────────────────────────

fn fmtHType(alloc: std.mem.Allocator, ty: HType) std.mem.Allocator.Error![]const u8 {
    const chased = ty.chase();
    return switch (chased) {
        .Meta => |mv| std.fmt.allocPrint(alloc, "?{d}", .{mv.id}),
        .Rigid => |name| std.fmt.allocPrint(alloc, "{s}", .{name.base}),
        .Con => |c| blk: {
            if (c.args.len == 0) break :blk std.fmt.allocPrint(alloc, "{s}", .{c.name.base});
            if (std.mem.eql(u8, c.name.base, "[]") and c.args.len == 1) {
                const inner = try fmtHType(alloc, c.args[0]);
                break :blk std.fmt.allocPrint(alloc, "[{s}]", .{inner});
            }
            var buf: std.ArrayListUnmanaged(u8) = .empty;
            try buf.appendSlice(alloc, c.name.base);
            for (c.args) |arg| {
                try buf.append(alloc, ' ');
                try buf.appendSlice(alloc, try fmtHType(alloc, arg));
            }
            break :blk buf.toOwnedSlice(alloc);
        },
        .Fun => |f| blk: {
            const a = try fmtHType(alloc, f.arg.*);
            const b = try fmtHType(alloc, f.res.*);
            break :blk std.fmt.allocPrint(alloc, "{s} -> {s}", .{ a, b });
        },
        .ForAll => |fa| blk: {
            const body = try fmtHType(alloc, fa.body.*);
            break :blk std.fmt.allocPrint(alloc, "forall {s}. {s}", .{ fa.binder.base, body });
        },
    };
}

// ── Free-metavar collection ─────────────────────────────────────────────

fn collectFreeMetas(
    ty: HType,
    out: *std.AutoHashMapUnmanaged(u32, void),
    alloc: std.mem.Allocator,
) std.mem.Allocator.Error!void {
    const current = ty.chase();
    switch (current) {
        .Meta => |mv| try out.put(alloc, mv.id, {}),
        .Rigid => {},
        .Con => |c| for (c.args) |arg| try collectFreeMetas(arg, out, alloc),
        .Fun => |f| {
            try collectFreeMetas(f.arg.*, out, alloc);
            try collectFreeMetas(f.res.*, out, alloc);
        },
        .ForAll => |fa| try collectFreeMetas(fa.body.*, out, alloc),
    }
}

// ── Generalisation ─────────────────────────────────────────────────────

/// Generalise the type at `ty_node` over its free metavariables.
///
/// A metavar is generalised only if it does not appear in `env_metas` —
/// the set of metavariables that are free in the ambient type environment
/// at the point of the binding (the "active type variables" condition of
/// Damas & Milner 1982, §3).
///
/// Callers must snapshot the env free metas *before* adding the current
/// binder's mono pre-binding to the env (so the binder's own unsolved
/// meta is not included in `env_metas`).  See `inferLetDecl`.
///
/// After calling this, every generalisable free metavar in `ty_node.*`
/// will have been solved to a fresh rigid variable, and `ty_node.*`
/// (after chasing) will contain only rigids for those variables.
///
/// Returns a `TyScheme` whose `body` is the chased `ty_node.*` and whose
/// `binders` list the unique IDs of the newly-introduced rigid variables.
pub fn generalisePtr(
    ctx: *InferCtx,
    ty_node: *HType,
    env_metas: *const std.AutoHashMapUnmanaged(u32, void),
) std.mem.Allocator.Error!TyScheme {
    var ty_metas = std.AutoHashMapUnmanaged(u32, void){};
    defer ty_metas.deinit(ctx.alloc);
    try collectFreeMetas(ty_node.*, &ty_metas, ctx.alloc);

    var binder_ids = std.ArrayListUnmanaged(u64){};

    var it = ty_metas.keyIterator();
    while (it.next()) |meta_id_ptr| {
        const meta_id = meta_id_ptr.*;
        if (env_metas.contains(meta_id)) continue;

        const rigid_name = ctx.u_supply.freshName("a");
        const rigid_ty = try ctx.alloc.create(HType);
        rigid_ty.* = HType{ .Rigid = rigid_name };

        solveMetaInTree(ty_node, meta_id, rigid_ty);
        try binder_ids.append(ctx.alloc, rigid_name.unique.value);
    }

    const binders = try binder_ids.toOwnedSlice(ctx.alloc);
    // Chase ty_node to the root so that the scheme body does not contain an
    // intermediate Meta that instantiateType would leave unresolved.
    return TyScheme{ .binders = binders, .body = ty_node.chase() };
}

/// Mutate every unsolved meta with `id == target_id` in the tree rooted
/// at `node` to point to `rigid`.
fn solveMetaInTree(node: *HType, target_id: u32, rigid: *HType) void {
    switch (node.*) {
        .Meta => |*mv| {
            if (mv.ref) |next| {
                solveMetaInTree(next, target_id, rigid);
            } else if (mv.id == target_id) {
                mv.ref = rigid;
            }
        },
        .Rigid => {},
        .Con => |c| for (c.args) |arg| solveMetaInTree(@constCast(&arg), target_id, rigid),
        .Fun => |f| {
            solveMetaInTree(@constCast(f.arg), target_id, rigid);
            solveMetaInTree(@constCast(f.res), target_id, rigid);
        },
        .ForAll => |fa| solveMetaInTree(@constCast(fa.body), target_id, rigid),
    }
}

// ── Type signature handling ────────────────────────────────────────────

/// Mapping from type variable names (e.g., "a", "b") to their allocated `*HType` nodes.
/// Used when converting `ast.Type` with bound type variables.
const TypeVarMap = std.StringHashMapUnmanaged(*HType);

/// Convert an `ast.Type` annotation to an arena-allocated `*HType`.
///
/// Handles type variables via the provided map: if a variable is already in the map,
/// returns the existing node; otherwise allocates a fresh meta and adds it to the map.
/// This allows type signatures like `a -> a` to correctly represent the type as
/// using the same type variable in multiple positions.
///
/// Intentionally minimal for M1 — handles the common cases.
/// Known shortcoming: App, Paren, Forall, and n-ary Tuple not yet handled.
/// See #177.
fn astTypeToHTypeWithScope(
    ast_ty: @import("../frontend/ast.zig").Type,
    ctx: *InferCtx,
    scope: *TypeVarMap,
) std.mem.Allocator.Error!*HType {
    return switch (ast_ty) {
        .Var => |name| blk: {
            if (scope.get(name)) |existing| {
                break :blk existing;
            }
            const meta = try ctx.freshMeta();
            try scope.put(ctx.alloc, name, meta);
            break :blk meta;
        },
        .Con => |qname| blk: {
            if (knownTypeByName(qname.name)) |ty| break :blk ctx.alloc_ty(ty);
            break :blk ctx.freshMeta();
        },
        .Fun => |parts| blk: {
            if (parts.len < 2) break :blk ctx.freshMeta();
            var result = try astTypeToHTypeWithScope(parts[parts.len - 1].*, ctx, scope);
            var i = parts.len - 1;
            while (i > 0) {
                i -= 1;
                const arg_p = try astTypeToHTypeWithScope(parts[i].*, ctx, scope);
                const res_p = try ctx.alloc.create(HType);
                res_p.* = result.*;
                const node = try ctx.alloc.create(HType);
                node.* = HType{ .Fun = .{ .arg = arg_p, .res = res_p } };
                result = node;
            }
            break :blk result;
        },
        .App => ctx.freshMeta(), // simplified for M1
        .List => |inner| blk: {
            const inner_p = try astTypeToHTypeWithScope(inner.*, ctx, scope);
            const args = try ctx.alloc.dupe(HType, &.{inner_p.*});
            break :blk ctx.alloc_ty(HType{ .Con = .{ .name = Known.Type.List, .args = args } });
        },
        .Tuple => |parts| blk: {
            if (parts.len == 2) {
                const a = try astTypeToHTypeWithScope(parts[0].*, ctx, scope);
                const b = try astTypeToHTypeWithScope(parts[1].*, ctx, scope);
                const args = try ctx.alloc.dupe(HType, &.{ a.*, b.* });
                break :blk ctx.alloc_ty(HType{ .Con = .{ .name = Known.Con.Tuple2, .args = args } });
            }
            break :blk ctx.freshMeta();
        },
        .Paren => |inner| astTypeToHTypeWithScope(inner.*, ctx, scope),
        .Forall => |fa| astTypeToHTypeWithScope(fa.type.*, ctx, scope), // Ignore binders, let scope handle it
        .IParam => ctx.freshMeta(),
    };
}

/// Simple wrapper for callers that don't need type variable scope sharing.
fn astTypeToHType(
    ast_ty: @import("../frontend/ast.zig").Type,
    ctx: *InferCtx,
) std.mem.Allocator.Error!*HType {
    var scope = TypeVarMap{};
    defer scope.deinit(ctx.alloc);
    return astTypeToHTypeWithScope(ast_ty, ctx, &scope);
}

/// Type signature entry: maps a Name to its declared `*HType`.
const TypeSigEntry = struct {
    name: Name,
    ty: *HType,
    loc: SourceSpan, // For error reporting
};

fn knownTypeByName(name: []const u8) ?HType {
    if (std.mem.eql(u8, name, "Int")) return HType{ .Con = .{ .name = Known.Type.Int, .args = &.{} } };
    if (std.mem.eql(u8, name, "Integer")) return HType{ .Con = .{ .name = Known.Type.Integer, .args = &.{} } };
    if (std.mem.eql(u8, name, "Double")) return HType{ .Con = .{ .name = Known.Type.Double, .args = &.{} } };
    if (std.mem.eql(u8, name, "Float")) return HType{ .Con = .{ .name = Known.Type.Float, .args = &.{} } };
    if (std.mem.eql(u8, name, "Bool")) return HType{ .Con = .{ .name = Known.Type.Bool, .args = &.{} } };
    if (std.mem.eql(u8, name, "Char")) return HType{ .Con = .{ .name = Known.Type.Char, .args = &.{} } };
    if (std.mem.eql(u8, name, "String")) return HType{ .Con = .{
        .name = Known.Type.List,
        .args = &.{HType{ .Con = .{ .name = Known.Type.Char, .args = &.{} } }},
    } };
    if (std.mem.eql(u8, name, "IO")) return HType{ .Con = .{ .name = Known.Type.IO, .args = &.{} } };
    if (std.mem.eql(u8, name, "Maybe")) return HType{ .Con = .{ .name = Known.Type.Maybe, .args = &.{} } };
    if (std.mem.eql(u8, name, "Either")) return HType{ .Con = .{ .name = Known.Type.Either, .args = &.{} } };
    return null;
}

// ── Literal typing ─────────────────────────────────────────────────────

/// Return the monomorphic type of an AST literal.
fn inferLit(lit: @import("../frontend/ast.zig").Literal, ctx: *InferCtx) std.mem.Allocator.Error!*HType {
    const ty: HType = switch (lit) {
        .Int => intTy(),
        .Float => doubleTy(),
        .Char => charTy(),
        .String => stringTy(),
        .Rational => doubleTy(),
    };
    return ctx.alloc_ty(ty);
}

// ── Pattern inference ──────────────────────────────────────────────────

/// Infer the type introduced by a pattern, binding new names into the env.
/// Returns a pointer to the arena-allocated type the pattern matches against.
pub fn inferPat(ctx: *InferCtx, pat: RPat) std.mem.Allocator.Error!*HType {
    return switch (pat) {
        .Var => |v| blk: {
            const ty = try ctx.freshMeta();
            try ctx.env.bindMono(v.name, ty.*);
            break :blk ty;
        },
        .Lit => |l| inferLit(l, ctx),
        .Wild => ctx.freshMeta(),
        .AsPat => |ap| blk: {
            const inner_ty = try inferPat(ctx, ap.pat.*);
            try ctx.env.bindMono(ap.name, inner_ty.*);
            break :blk inner_ty;
        },
        .Con => |c| blk: {
            const scheme = ctx.env.lookupScheme(c.name.unique) orelse {
                const msg = try std.fmt.allocPrint(
                    ctx.alloc,
                    "unknown constructor `{s}`",
                    .{c.name.base},
                );
                break :blk try ctx.recoverWithFreshMeta(msg, c.con_span);
            };
            var inst_ty = try ctx.alloc_ty(try scheme.instantiate(ctx.alloc, ctx.mv_supply));

            for (c.args) |arg_pat| {
                const arg_ty = try inferPat(ctx, arg_pat);
                const fun_arg = try ctx.freshMeta();
                const fun_res = try ctx.freshMeta();
                const fun_node = try ctx.alloc_ty(HType{ .Fun = .{ .arg = fun_arg, .res = fun_res } });
                try ctx.unifyNow(inst_ty, fun_node, c.con_span);
                try ctx.unifyNow(arg_ty, fun_arg, c.con_span);
                inst_ty = fun_res;
            }
            break :blk inst_ty;
        },
        .Tuple => |pats| blk: {
            var elem_tys = std.ArrayListUnmanaged(HType){};
            for (pats) |p| {
                const pt = try inferPat(ctx, p);
                try elem_tys.append(ctx.alloc, pt.*);
            }
            const args = try elem_tys.toOwnedSlice(ctx.alloc);
            break :blk ctx.alloc_ty(HType{ .Con = .{ .name = Known.Con.Tuple2, .args = args } });
        },
        .List => |pats| blk: {
            const elem_ty = try ctx.freshMeta();
            for (pats) |p| {
                const pt = try inferPat(ctx, p);
                try ctx.unifyNow(pt, elem_ty, syntheticSpan());
            }
            const args = try ctx.alloc.dupe(HType, &.{elem_ty.*});
            break :blk ctx.alloc_ty(HType{ .Con = .{ .name = Known.Type.List, .args = args } });
        },
        .InfixCon => |ic| blk: {
            const left_ty = try inferPat(ctx, ic.left.*);
            const right_ty = try inferPat(ctx, ic.right.*);
            const elem_ty = try ctx.freshMeta();
            const list_args = try ctx.alloc.dupe(HType, &.{elem_ty.*});
            const list_ty = try ctx.alloc_ty(HType{ .Con = .{ .name = Known.Type.List, .args = list_args } });
            try ctx.unifyNow(left_ty, elem_ty, ic.con_span);
            try ctx.unifyNow(right_ty, list_ty, ic.con_span);
            break :blk list_ty;
        },
        .Negate => |inner| blk: {
            const inner_ty = try inferPat(ctx, inner.*);
            const int_node = try ctx.alloc_ty(intTy());
            try ctx.unifyNow(inner_ty, int_node, syntheticSpan());
            break :blk int_node;
        },
        .Paren => |inner| inferPat(ctx, inner.*),
    };
}

// ── Expression inference ───────────────────────────────────────────────

/// Synthesise the type of `expr`, returning an arena-allocated `*HType`.
///
/// All solver mutations to `MetaVar.ref` are visible through the returned
/// pointer because both the returned node and the nodes inside constraints
/// are the *same* arena-allocated objects.
pub fn infer(ctx: *InferCtx, expr: RExpr) std.mem.Allocator.Error!*HType {
    return switch (expr) {

        // ── Var ────────────────────────────────────────────────────────
        //
        // Look up the name in the env and instantiate its scheme.
        .Var => |v| blk: {
            const ty = try ctx.env.lookup(v.name.unique, ctx.alloc, ctx.mv_supply);
            if (ty) |t| break :blk ctx.alloc_ty(t);
            const msg = try std.fmt.allocPrint(
                ctx.alloc,
                "unbound variable `{s}` in typechecker (renamer bug?)",
                .{v.name.base},
            );
            break :blk try ctx.recoverWithFreshMeta(msg, v.span);
        },

        // ── Lit ───────────────────────────────────────────────────────
        .Lit => |l| inferLit(l, ctx),

        // ── App ───────────────────────────────────────────────────────
        //
        // Γ ⊢ f : τ₁ → τ₂    Γ ⊢ arg : τ₁
        // ─────────────────────────────────
        //       Γ ⊢ f arg : τ₂
        .App => |a| blk: {
            const fn_ty = try infer(ctx, a.fn_expr.*);
            const arg_ty = try infer(ctx, a.arg_expr.*);
            const res_ty = try ctx.freshMeta();
            const expected_fn = try ctx.alloc_ty(HType{ .Fun = .{ .arg = arg_ty, .res = res_ty } });
            try ctx.unifyNow(fn_ty, expected_fn, syntheticSpan());
            break :blk res_ty;
        },

        // ── Lambda ───────────────────────────────────────────────────
        //
        // Γ, x₁:τ₁, …, xₙ:τₙ ⊢ body : τ
        // ─────────────────────────────────
        //   Γ ⊢ \x₁…xₙ -> body : τ₁ → … → τₙ → τ
        .Lambda => |lam| blk: {
            try ctx.env.push();
            defer ctx.env.pop();

            var param_tys = std.ArrayListUnmanaged(*HType){};
            for (lam.params) |param| {
                const ty = try ctx.freshMeta();
                try ctx.env.bindMono(param, ty.*);
                try param_tys.append(ctx.alloc, ty);
            }

            const body_ty = try infer(ctx, lam.body.*);

            // Build function type right-to-left.
            var result: *HType = body_ty;
            var i = param_tys.items.len;
            while (i > 0) {
                i -= 1;
                result = try ctx.alloc_ty(HType{ .Fun = .{
                    .arg = param_tys.items[i],
                    .res = result,
                } });
            }
            break :blk result;
        },

        // ── Let ──────────────────────────────────────────────────────
        //
        // Let-polymorphism (the key HM rule):
        //   Γ ⊢ rhs : τ    σ = gen(Γ, τ)    Γ, x:σ ⊢ body : τ'
        //   ────────────────────────────────────────────────────
        //               Γ ⊢ let x = rhs in body : τ'
        .Let => |let| blk: {
            try ctx.env.push();
            defer ctx.env.pop();
            // TODO(#175): Collect TypeSig declarations first and check signatures.
            // For now, pass null for sig since we don't support checking signatures in this context yet.
            for (let.binds) |decl| try inferLetDecl(ctx, decl, null);
            break :blk try infer(ctx, let.body.*);
        },

        // ── If ────────────────────────────────────────────────────────
        //
        // Γ ⊢ cond : Bool    Γ ⊢ t : τ    Γ ⊢ e : τ
        // ────────────────────────────────────────────
        //          Γ ⊢ if cond then t else e : τ
        .If => |i| blk: {
            const cond_ty = try infer(ctx, i.condition.*);
            const then_ty = try infer(ctx, i.then_expr.*);
            const else_ty = try infer(ctx, i.else_expr.*);
            const bool_node = try ctx.alloc_ty(boolTy());
            try ctx.unifyNow(cond_ty, bool_node, syntheticSpan());
            try ctx.unifyNow(then_ty, else_ty, syntheticSpan());
            break :blk then_ty;
        },

        // ── Case ──────────────────────────────────────────────────────
        //
        // Γ ⊢ scrut : τ_s
        // ∀ alt: Γ, pat_bindings ⊢ pat : τ_s,  Γ ⊢ rhs : τ_r
        // ──────────────────────────────────────────────────────
        //            Γ ⊢ case scrut of alts : τ_r
        .Case => |c| blk: {
            const scrut_ty = try infer(ctx, c.scrutinee.*);
            const result_ty = try ctx.freshMeta();
            for (c.alts) |alt| {
                try ctx.env.push();
                defer ctx.env.pop();
                const pat_ty = try inferPat(ctx, alt.pattern);
                try ctx.unifyNow(scrut_ty, pat_ty, alt.span);
                const rhs_ty = try inferRhs(ctx, alt.rhs);
                try ctx.unifyNow(rhs_ty, result_ty, alt.span);
            }
            break :blk result_ty;
        },

        // ── Do ────────────────────────────────────────────────────────
        //
        // M1: do-notation is hard-coded to IO.  See #176 for generic Monad.
        .Do => |stmts| blk: {
            if (stmts.len == 0) break :blk try ctx.freshMeta();
            try ctx.env.push();
            defer ctx.env.pop();
            var last_inner: *HType = try ctx.freshMeta();
            for (stmts) |stmt| last_inner = try inferStmt(ctx, stmt);
            break :blk last_inner;
        },

        // ── Tuple ─────────────────────────────────────────────────────
        .Tuple => |elems| blk: {
            var elem_tys = std.ArrayListUnmanaged(HType){};
            for (elems) |e| {
                const et = try infer(ctx, e);
                try elem_tys.append(ctx.alloc, et.*);
            }
            const args = try elem_tys.toOwnedSlice(ctx.alloc);
            if (args.len == 2) {
                break :blk ctx.alloc_ty(HType{ .Con = .{ .name = Known.Con.Tuple2, .args = args } });
            }
            break :blk ctx.freshMeta();
        },

        // ── List ──────────────────────────────────────────────────────
        //
        // Γ ⊢ e₁ : τ, …, Γ ⊢ eₙ : τ
        // ────────────────────────────
        //     Γ ⊢ [e₁, …, eₙ] : [τ]
        .List => |elems| blk: {
            const elem_ty = try ctx.freshMeta();
            for (elems) |e| {
                const et = try infer(ctx, e);
                try ctx.unifyNow(et, elem_ty, syntheticSpan());
            }
            const args = try ctx.alloc.dupe(HType, &.{elem_ty.*});
            break :blk ctx.alloc_ty(HType{ .Con = .{ .name = Known.Type.List, .args = args } });
        },

        // ── InfixApp ─────────────────────────────────────────────────
        //
        // `l op r`  ≡  `(op l) r`
        .InfixApp => |ia| blk: {
            const op_scheme = ctx.env.lookupScheme(ia.op.unique);
            const op_ty = if (op_scheme) |s|
                try ctx.alloc_ty(try s.instantiate(ctx.alloc, ctx.mv_supply))
            else blk2: {
                const msg = try std.fmt.allocPrint(ctx.alloc, "unknown operator `{s}`", .{ia.op.base});
                break :blk2 try ctx.recoverWithFreshMeta(msg, ia.op_span);
            };

            const left_ty = try infer(ctx, ia.left.*);
            const right_ty = try infer(ctx, ia.right.*);
            const res_ty = try ctx.freshMeta();

            // op_ty must be: left_ty -> right_ty -> res_ty
            const inner = try ctx.alloc_ty(HType{ .Fun = .{ .arg = right_ty, .res = res_ty } });
            const expected = try ctx.alloc_ty(HType{ .Fun = .{ .arg = left_ty, .res = inner } });
            try ctx.unifyNow(op_ty, expected, ia.op_span);
            break :blk res_ty;
        },

        // ── Sections ─────────────────────────────────────────────────
        .LeftSection => |ls| blk: {
            const op_scheme = ctx.env.lookupScheme(ls.op.unique);
            const op_ty = if (op_scheme) |s|
                try ctx.alloc_ty(try s.instantiate(ctx.alloc, ctx.mv_supply))
            else
                try ctx.freshMeta();

            const expr_ty = try infer(ctx, ls.expr.*);
            const right_ty = try ctx.freshMeta();
            const res_ty = try ctx.freshMeta();

            const inner = try ctx.alloc_ty(HType{ .Fun = .{ .arg = right_ty, .res = res_ty } });
            const expected = try ctx.alloc_ty(HType{ .Fun = .{ .arg = expr_ty, .res = inner } });
            try ctx.unifyNow(op_ty, expected, ls.op_span);
            break :blk ctx.alloc_ty(HType{ .Fun = .{ .arg = right_ty, .res = res_ty } });
        },

        .RightSection => |rs| blk: {
            const op_scheme = ctx.env.lookupScheme(rs.op.unique);
            const op_ty = if (op_scheme) |s|
                try ctx.alloc_ty(try s.instantiate(ctx.alloc, ctx.mv_supply))
            else
                try ctx.freshMeta();

            const expr_ty = try infer(ctx, rs.expr.*);
            const left_ty = try ctx.freshMeta();
            const res_ty = try ctx.freshMeta();

            const inner = try ctx.alloc_ty(HType{ .Fun = .{ .arg = expr_ty, .res = res_ty } });
            const expected = try ctx.alloc_ty(HType{ .Fun = .{ .arg = left_ty, .res = inner } });
            try ctx.unifyNow(op_ty, expected, rs.op_span);
            break :blk ctx.alloc_ty(HType{ .Fun = .{ .arg = left_ty, .res = res_ty } });
        },

        // ── TypeAnn ───────────────────────────────────────────────────
        //
        // Γ ⊢ e : τ'    τ' ~ τ_ann
        // ─────────────────────────
        //   Γ ⊢ (e :: τ_ann) : τ_ann
        .TypeAnn => |ta| blk: {
            const ann_ty = try astTypeToHType(ta.type, ctx);
            const expr_ty = try infer(ctx, ta.expr.*);
            try ctx.unifyNow(expr_ty, ann_ty, syntheticSpan());
            break :blk ann_ty;
        },

        // ── Negate ────────────────────────────────────────────────────
        .Negate => |inner| blk: {
            const inner_ty = try infer(ctx, inner.*);
            const int_node = try ctx.alloc_ty(intTy());
            try ctx.unifyNow(inner_ty, int_node, syntheticSpan());
            break :blk int_node;
        },

        // ── Paren ─────────────────────────────────────────────────────
        .Paren => |inner| infer(ctx, inner.*),
    };
}

// ── Check mode ─────────────────────────────────────────────────────────

/// Check that `expr` has type `expected`.
pub fn check(
    ctx: *InferCtx,
    expr: RExpr,
    expected: *HType,
    span: SourceSpan,
) std.mem.Allocator.Error!void {
    const actual = try infer(ctx, expr);
    try ctx.unifyNow(actual, expected, span);
}

// ── RHS inference ──────────────────────────────────────────────────────

fn inferRhs(ctx: *InferCtx, rhs: RRhs) std.mem.Allocator.Error!*HType {
    return switch (rhs) {
        .UnGuarded => |e| infer(ctx, e),
        .Guarded => |guards| blk: {
            const result_ty = try ctx.freshMeta();
            for (guards) |g| {
                for (g.guards) |guard| {
                    switch (guard) {
                        .ExprGuard => |ge| {
                            const gt = try infer(ctx, ge);
                            const bool_node = try ctx.alloc_ty(boolTy());
                            try ctx.unifyNow(gt, bool_node, syntheticSpan());
                        },
                    }
                }
                const rhs_ty = try infer(ctx, g.rhs);
                try ctx.unifyNow(rhs_ty, result_ty, syntheticSpan());
            }
            break :blk result_ty;
        },
    };
}

// ── Statement inference (do-notation) ──────────────────────────────────

/// Infer the inner type of a do-statement (the `a` in `IO a`).
fn inferStmt(ctx: *InferCtx, stmt: RStmt) std.mem.Allocator.Error!*HType {
    return switch (stmt) {
        .Generator => |g| blk: {
            const action_ty = try infer(ctx, g.expr);
            const pat_ty = try inferPat(ctx, g.pat);
            const io_pat = try ioTy(pat_ty.*, ctx.alloc);
            const io_node = try ctx.alloc_ty(io_pat);
            try ctx.unifyNow(action_ty, io_node, syntheticSpan());
            break :blk pat_ty;
        },
        .Qualifier => |e| blk: {
            const ty = try infer(ctx, e);
            const inner = try ctx.freshMeta();
            const io_inner = try ctx.alloc_ty(try ioTy(inner.*, ctx.alloc));
            try ctx.unifyNow(ty, io_inner, syntheticSpan());
            break :blk inner;
        },
        .Stmt => |e| blk: {
            const ty = try infer(ctx, e);
            const inner = try ctx.freshMeta();
            const io_inner = try ctx.alloc_ty(try ioTy(inner.*, ctx.alloc));
            try ctx.unifyNow(ty, io_inner, syntheticSpan());
            break :blk inner;
        },
        .LetStmt => |decls| blk: {
            // TODO(#175): Collect TypeSig declarations first and check signatures.
            // For now, pass null for sig since we don't support checking signatures in this context yet.
            for (decls) |decl| try inferLetDecl(ctx, decl, null);
            break :blk ctx.freshMeta();
        },
    };
}

// ── Let-declaration inference ───────────────────────────────────────────

/// Infer the type of a let-bound declaration and extend the env.
///
/// Allocates a fresh meta node for the binder, infers each equation (or the
/// RHS), unifies through the node, flushes, then generalises.
///
/// If a type signature (`TypeSig`) is provided, the inferred type is unified
/// against the signature to ensure they match.
///
/// TODO(#175): Type signatures should be collected in a separate pass before
/// any inference, so that mutually recursive bindings with signatures can be
/// handled correctly. The current implementation checks signatures after
/// inference, which works for single-binding cases but not for mutual recursion.
fn inferLetDecl(
    ctx: *InferCtx,
    decl: RDecl,
    sig: ?*const TypeSigEntry,
) std.mem.Allocator.Error!void {
    switch (decl) {
        .FunBind => |fb| {
            // Snapshot env free metas *before* adding the mono pre-binding.
            // This excludes the binder's own unsolved meta from the active
            // set, so it is not spuriously protected from generalisation.
            var env_metas = std.AutoHashMapUnmanaged(u32, void){};
            defer env_metas.deinit(ctx.alloc);
            try ctx.env.collectFreeMetas(&env_metas, ctx.alloc);

            // Pre-allocate a meta node for the function (enables recursion).
            const fun_node = try ctx.freshMeta();
            try ctx.env.bindMono(fb.name, fun_node.*);

            // Infer each equation and unify *through* fun_node.
            for (fb.equations) |eq| {
                const eq_ty = try inferMatch(ctx, eq);
                try ctx.unifyNow(fun_node, eq_ty, fb.span);
            }

            // If there's a type signature, check the inferred type against it.
            if (sig) |s| {
                try ctx.unifyNow(fun_node, s.ty, fb.span);
            }

            // Generalise using the pre-snapshot env metas and rebind.
            const scheme = try generalisePtr(ctx, fun_node, &env_metas);
            try ctx.env.bind(fb.name, scheme);
        },
        .PatBind => |pb| {
            const rhs_ty = try inferRhs(ctx, pb.rhs);
            const pat_ty = try inferPat(ctx, pb.pattern);
            try ctx.unifyNow(rhs_ty, pat_ty, pb.span);
        },
        .TypeSig => {
            // Type signatures are collected separately and not processed here.
        },
    }
}

// ── Match inference ─────────────────────────────────────────────────────

/// Infer the type of a single match equation `p₁ … pₙ = rhs`.
///
/// Returns `τ₁ → … → τₙ → τ_rhs`.
fn inferMatch(ctx: *InferCtx, match: RMatch) std.mem.Allocator.Error!*HType {
    try ctx.env.push();
    defer ctx.env.pop();

    var param_tys = std.ArrayListUnmanaged(*HType){};
    for (match.patterns) |pat| {
        try param_tys.append(ctx.alloc, try inferPat(ctx, pat));
    }

    const rhs_ty = try inferRhs(ctx, match.rhs);

    // Build τ₁ → … → τₙ → τ_rhs
    var result: *HType = rhs_ty;
    var i = param_tys.items.len;
    while (i > 0) {
        i -= 1;
        result = try ctx.alloc_ty(HType{ .Fun = .{
            .arg = param_tys.items[i],
            .res = result,
        } });
    }
    return result;
}

// ── Module inference ────────────────────────────────────────────────────

/// Type-check an entire renamed module.
///
/// Returns a `ModuleTypes` mapping each top-level name's unique to its
/// `TyScheme`.  Errors are collected in `ctx.diags`.
pub fn inferModule(ctx: *InferCtx, module: RenamedModule) std.mem.Allocator.Error!ModuleTypes {
    // Pass 0: Collect type signatures and convert them to HType.
    var sigs = std.AutoHashMapUnmanaged(naming_mod.Unique, TypeSigEntry){};
    defer sigs.deinit(ctx.alloc);

    for (module.declarations) |decl| {
        if (decl != .TypeSig) continue;
        const ts = decl.TypeSig;

        var scope = TypeVarMap{};
        defer scope.deinit(ctx.alloc);

        // Convert AST type to HType with shared type variables
        const ty = try astTypeToHTypeWithScope(ts.type, ctx, &scope);

        // Bind for all names in the signature (Haskell allows multiple names per signature)
        for (ts.names) |name| {
            try sigs.put(ctx.alloc, name.unique, .{
                .name = name,
                .ty = ty,
                .loc = ts.span,
            });
        }
    }

    // Snapshot env free metas before any top-level binders are added.
    // All top-level bindings are mutually recursive peers, so they share
    // this one snapshot for the active-variables check during generalisation.
    var env_metas = std.AutoHashMapUnmanaged(u32, void){};
    defer env_metas.deinit(ctx.alloc);
    try ctx.env.collectFreeMetas(&env_metas, ctx.alloc);

    // Pass 1: allocate fresh meta nodes for all top-level binders.
    var top_metas = std.AutoHashMapUnmanaged(naming_mod.Unique, *HType){};
    for (module.declarations) |decl| {
        switch (decl) {
            .FunBind => |fb| {
                const node = try ctx.freshMeta();
                try ctx.env.bindMono(fb.name, node.*);
                try top_metas.put(ctx.alloc, fb.name.unique, node);
            },
            .PatBind => |pb| try assignPatMetas(ctx, pb.pattern, &top_metas),
            .TypeSig => {},
        }
    }

    // Pass 2: infer each declaration body, unify through the node, generalise.
    for (module.declarations) |decl| {
        switch (decl) {
            .FunBind => |fb| {
                const fun_node = top_metas.get(fb.name.unique) orelse continue;
                const sig_entry = sigs.get(fb.name.unique);

                for (fb.equations) |eq| {
                    const eq_ty = try inferMatch(ctx, eq);

                    if (sig_entry) |s| {
                        // If there's a signature, unify the inferred type against it.
                        try ctx.unifyNow(eq_ty, s.ty, fb.span);
                    } else {
                        // Otherwise, unify against the fresh meta node.
                        try ctx.unifyNow(fun_node, eq_ty, fb.span);
                    }
                }

                if (sig_entry) |_| {
                    // For bindings with signatures, create a scheme from the signature type.
                    // The signature is the authority, not the inferred type.
                    // We need to generalise the signature type (which contains fresh metas).
                    const scheme = try generalisePtr(ctx, sig_entry.?.ty, &env_metas);
                    try ctx.env.bind(fb.name, scheme);
                } else {
                    // For bindings without signatures, generalise the inferred type.
                    const scheme = try generalisePtr(ctx, fun_node, &env_metas);
                    try ctx.env.bind(fb.name, scheme);
                }
            },
            .PatBind => |pb| {
                const rhs_ty = try inferRhs(ctx, pb.rhs);
                const pat_ty = try inferPat(ctx, pb.pattern);
                try ctx.unifyNow(rhs_ty, pat_ty, pb.span);
            },
            .TypeSig => {},
        }
    }

    // Build result.
    var result = ModuleTypes{ .schemes = .{} };
    var it = top_metas.iterator();
    while (it.next()) |entry| {
        const scheme = ctx.env.lookupScheme(entry.key_ptr.*) orelse
            TyScheme.mono(entry.value_ptr.*.*);
        try result.schemes.put(ctx.alloc, entry.key_ptr.*, scheme);
    }
    return result;
}

fn assignPatMetas(
    ctx: *InferCtx,
    pat: RPat,
    out: *std.AutoHashMapUnmanaged(naming_mod.Unique, *HType),
) std.mem.Allocator.Error!void {
    switch (pat) {
        .Var => |v| {
            const node = try ctx.freshMeta();
            try ctx.env.bindMono(v.name, node.*);
            try out.put(ctx.alloc, v.name.unique, node);
        },
        .AsPat => |ap| {
            const node = try ctx.freshMeta();
            try ctx.env.bindMono(ap.name, node.*);
            try out.put(ctx.alloc, ap.name.unique, node);
            try assignPatMetas(ctx, ap.pat.*, out);
        },
        .Tuple => |pats| for (pats) |p| try assignPatMetas(ctx, p, out),
        .List => |pats| for (pats) |p| try assignPatMetas(ctx, p, out),
        .Con => |c| for (c.args) |a| try assignPatMetas(ctx, a, out),
        .InfixCon => |ic| {
            try assignPatMetas(ctx, ic.left.*, out);
            try assignPatMetas(ctx, ic.right.*, out);
        },
        .Paren => |inner| try assignPatMetas(ctx, inner.*, out),
        .Negate => |inner| try assignPatMetas(ctx, inner.*, out),
        .Lit, .Wild => {},
    }
}

// ── ModuleTypes ─────────────────────────────────────────────────────────

/// The result of type-checking a module.
pub const ModuleTypes = struct {
    schemes: std.AutoHashMapUnmanaged(naming_mod.Unique, TyScheme),

    pub fn deinit(self: *ModuleTypes, alloc: std.mem.Allocator) void {
        self.schemes.deinit(alloc);
    }

    pub fn get(self: *const ModuleTypes, unique: naming_mod.Unique) ?TyScheme {
        return self.schemes.get(unique);
    }
};

// ── Type helpers ────────────────────────────────────────────────────────

fn intTy() HType {
    return HType{ .Con = .{ .name = Known.Type.Int, .args = &.{} } };
}

fn boolTy() HType {
    return HType{ .Con = .{ .name = Known.Type.Bool, .args = &.{} } };
}

fn charTy() HType {
    return HType{ .Con = .{ .name = Known.Type.Char, .args = &.{} } };
}

fn doubleTy() HType {
    return HType{ .Con = .{ .name = Known.Type.Double, .args = &.{} } };
}

fn stringTy() HType {
    return HType{ .Con = .{
        .name = Known.Type.List,
        .args = &.{HType{ .Con = .{ .name = Known.Type.Char, .args = &.{} } }},
    } };
}

fn ioTy(inner: HType, alloc: std.mem.Allocator) std.mem.Allocator.Error!HType {
    const args = try alloc.dupe(HType, &.{inner});
    return HType{ .Con = .{ .name = Known.Type.IO, .args = args } };
}

/// Synthetic span for constraints generated during desugaring.
/// Uses `SourcePos.invalid()` which bypasses line/column assertions.
fn syntheticSpan() SourceSpan {
    return SourceSpan.init(SourcePos.invalid(), SourcePos.invalid());
}

// ── Tests ───────────────────────────────────────────────────────────────

const testing = std.testing;

fn makeCtx(
    arena: *std.heap.ArenaAllocator,
    env: *TyEnv,
    mv_supply: *MetaVarSupply,
    u_supply: *UniqueSupply,
    diags: *DiagnosticCollector,
) InferCtx {
    return InferCtx.init(arena.allocator(), env, mv_supply, u_supply, diags);
}

fn testSpan() SourceSpan {
    return SourceSpan.init(SourcePos.init(1, 1, 1), SourcePos.init(1, 1, 10));
}

fn testName(base: []const u8, id: u64) Name {
    return .{ .base = base, .unique = .{ .value = id } };
}

// ── Literal inference ─────────────────────────────────────────────────

test "infer: integer literal has type Int" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const expr = RExpr{ .Lit = .{ .Int = .{ .value = 42, .span = testSpan() } } };
    const ty = try infer(&ctx, expr);
    try testing.expect(ty.* == .Con);
    try testing.expectEqualStrings("Int", ty.Con.name.base);
    try testing.expect(!diags.hasErrors());
}

test "infer: character literal has type Char" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const expr = RExpr{ .Lit = .{ .Char = .{ .value = 'x', .span = testSpan() } } };
    const ty = try infer(&ctx, expr);
    try testing.expect(ty.* == .Con);
    try testing.expectEqualStrings("Char", ty.Con.name.base);
    try testing.expect(!diags.hasErrors());
}

test "infer: string literal has type [Char]" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const expr = RExpr{ .Lit = .{ .String = .{ .value = "hello", .span = testSpan() } } };
    const ty = try infer(&ctx, expr);
    try testing.expect(ty.* == .Con);
    try testing.expectEqualStrings("[]", ty.Con.name.base);
    try testing.expectEqual(@as(usize, 1), ty.Con.args.len);
    try testing.expectEqualStrings("Char", ty.Con.args[0].Con.name.base);
    try testing.expect(!diags.hasErrors());
}

test "infer: float literal has type Double" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const expr = RExpr{ .Lit = .{ .Float = .{ .value = 3.14, .span = testSpan() } } };
    const ty = try infer(&ctx, expr);
    try testing.expect(ty.* == .Con);
    try testing.expectEqualStrings("Double", ty.Con.name.base);
}

// ── Variable inference ────────────────────────────────────────────────

test "infer: variable resolves from env" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const x_name = testName("x", 2000);
    try env.bindMono(x_name, intTy());

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const expr = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const ty = try infer(&ctx, expr);
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
    try testing.expect(!diags.hasErrors());
}

test "infer: unbound variable emits error and returns fresh meta" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const missing = testName("notDefined", 9999);
    const expr = RExpr{ .Var = .{ .name = missing, .span = testSpan() } };
    const ty = try infer(&ctx, expr);
    try testing.expect(ty.* == .Meta);
    try testing.expect(diags.hasErrors());
}

// ── Lambda inference ───────────────────────────────────────────────────

test "infer: lambda \\x -> x has type ?a -> ?a (identity)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const x_name = testName("x", 2001);
    const body = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const lam = RExpr{ .Lambda = .{
        .params = &.{x_name},
        .param_spans = &.{testSpan()},
        .body = &body,
    } };

    const ty = try infer(&ctx, lam);

    try testing.expect(!diags.hasErrors());
    try testing.expect(ty.* == .Fun);
    // Both arg and result should chase to the same meta (the param's meta).
    const arg_chased = ty.Fun.arg.chase();
    const res_chased = ty.Fun.res.chase();
    try testing.expect(arg_chased == .Meta);
    try testing.expect(res_chased == .Meta);
    try testing.expectEqual(arg_chased.Meta.id, res_chased.Meta.id);
}

test "infer: lambda \\x -> 42 has type ?a -> Int" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const x_name = testName("x", 2002);
    const body = RExpr{ .Lit = .{ .Int = .{ .value = 42, .span = testSpan() } } };
    const lam = RExpr{ .Lambda = .{
        .params = &.{x_name},
        .param_spans = &.{testSpan()},
        .body = &body,
    } };

    const ty = try infer(&ctx, lam);

    try testing.expect(!diags.hasErrors());
    try testing.expect(ty.* == .Fun);
    try testing.expect(ty.Fun.arg.chase() == .Meta); // arg is a free ?a
    const res = ty.Fun.res.chase();
    try testing.expect(res == .Con);
    try testing.expectEqualStrings("Int", res.Con.name.base);
}

// ── Application inference ──────────────────────────────────────────────

test "infer: application f x where f :: Int -> Bool, x :: Int gives Bool" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // f :: Int -> Bool
    const f_name = testName("f", 3000);
    const int_p = try alloc.create(HType);
    int_p.* = intTy();
    const bool_p = try alloc.create(HType);
    bool_p.* = boolTy();
    try env.bindMono(f_name, HType{ .Fun = .{ .arg = int_p, .res = bool_p } });

    // x :: Int
    const x_name = testName("x", 3001);
    try env.bindMono(x_name, intTy());

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const fn_expr = RExpr{ .Var = .{ .name = f_name, .span = testSpan() } };
    const arg_expr = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const app = RExpr{ .App = .{ .fn_expr = &fn_expr, .arg_expr = &arg_expr } };

    const ty = try infer(&ctx, app);

    try testing.expect(!diags.hasErrors());
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Bool", chased.Con.name.base);
}

test "infer: application type mismatch emits error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // f :: Int -> Bool
    const f_name = testName("f", 4000);
    const int_p = try alloc.create(HType);
    int_p.* = intTy();
    const bool_p = try alloc.create(HType);
    bool_p.* = boolTy();
    try env.bindMono(f_name, HType{ .Fun = .{ .arg = int_p, .res = bool_p } });

    // x :: Bool (wrong type for f)
    const x_name = testName("x", 4001);
    try env.bindMono(x_name, boolTy());

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const fn_expr = RExpr{ .Var = .{ .name = f_name, .span = testSpan() } };
    const arg_expr = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const app = RExpr{ .App = .{ .fn_expr = &fn_expr, .arg_expr = &arg_expr } };

    _ = try infer(&ctx, app);

    try testing.expect(diags.hasErrors());
}

// ── Let-polymorphism ──────────────────────────────────────────────────

test "infer: let id = \\x -> x in (id 1, id True) — let-polymorphism" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    // id = \x -> x
    const x_name = testName("x", 5001);
    const id_name = testName("id", 5000);
    const body = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const id_lam = RExpr{ .Lambda = .{
        .params = &.{x_name},
        .param_spans = &.{testSpan()},
        .body = &body,
    } };
    const id_decl = RDecl{ .FunBind = .{
        .name = id_name,
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = id_lam }, .span = testSpan() }},
        .span = testSpan(),
    } };

    // id 1
    const id_ref1 = RExpr{ .Var = .{ .name = id_name, .span = testSpan() } };
    const one = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const app1 = RExpr{ .App = .{ .fn_expr = &id_ref1, .arg_expr = &one } };

    // id True
    const id_ref2 = RExpr{ .Var = .{ .name = id_name, .span = testSpan() } };
    const true_expr = RExpr{ .Var = .{ .name = Known.Con.True, .span = testSpan() } };
    const app2 = RExpr{ .App = .{ .fn_expr = &id_ref2, .arg_expr = &true_expr } };

    // (id 1, id True)
    const tuple = RExpr{ .Tuple = &.{ app1, app2 } };

    // let id = \x -> x in (id 1, id True)
    const let_expr = RExpr{ .Let = .{ .binds = &.{id_decl}, .body = &tuple } };

    const ty = try infer(&ctx, let_expr);

    try testing.expect(!diags.hasErrors());
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqual(@as(usize, 2), chased.Con.args.len);
    const fst = chased.Con.args[0].chase();
    const snd = chased.Con.args[1].chase();
    try testing.expect(fst == .Con);
    try testing.expectEqualStrings("Int", fst.Con.name.base);
    try testing.expect(snd == .Con);
    try testing.expectEqualStrings("Bool", snd.Con.name.base);
}

// ── Over-generalisation regression (#174) ─────────────────────────────
//
// Direct unit test of `generalisePtr`: a meta that is free in the ambient
// env must NOT be generalised.
//
// Scenario: `?outer` is free in the env (simulating an outer lambda param).
// We ask generalisePtr to generalise `?inner -> ?outer`.  Only `?inner`
// should become a rigid binder; `?outer` must remain monomorphic.
test "generalisePtr: meta free in env is not generalised" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    // Simulate an outer lambda parameter `x` bound as a mono type in env.
    const x_name = testName("x", 9000);
    const outer_meta = try ctx.freshMeta(); // ?outer — the "ambient" meta
    try ctx.env.bindMono(x_name, outer_meta.*);

    // The type to generalise: ?inner -> ?outer  (simulating \y -> x)
    const inner_meta = try ctx.freshMeta(); // ?inner — local to the let-rhs
    const ty_node = try ctx.alloc_ty(HType{ .Fun = .{
        .arg = inner_meta,
        .res = outer_meta,
    } });

    // Snapshot env metas before adding any pre-binding (as inferLetDecl does).
    var env_metas = std.AutoHashMapUnmanaged(u32, void){};
    defer env_metas.deinit(alloc);
    try ctx.env.collectFreeMetas(&env_metas, alloc);

    // env_metas must contain ?outer (it is free in the env via x's binding).
    try testing.expect(env_metas.contains(outer_meta.Meta.id));
    // env_metas must NOT contain ?inner (it is purely local).
    try testing.expect(!env_metas.contains(inner_meta.Meta.id));

    const scheme = try generalisePtr(&ctx, ty_node, &env_metas);

    // Only ?inner should have been generalised — exactly one binder.
    try testing.expectEqual(@as(usize, 1), scheme.binders.len);

    // The body should be: rigid_a -> ?outer (where ?outer stays unsolved).
    const body = scheme.body.chase();
    try testing.expect(body == .Fun);
    try testing.expect(body.Fun.arg.*.chase() == .Rigid); // ?inner → rigid
    try testing.expect(body.Fun.res.*.chase() == .Meta);  // ?outer stays meta
}

test "infer: genuine let-polymorphism still works in nested scopes" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    // let id = \x -> x in
    //   let const_ = \a -> \b -> a in
    //     (id 1, const_ True 42)
    //
    // Both id and const_ are genuinely polymorphic — their metas are fully
    // local and must still be generalised correctly even with the fix.
    const id_name = testName("id", 9100);
    const const_name = testName("const_", 9101);
    const xa = testName("xa", 9102);
    const a_name = testName("a", 9103);
    const b_name = testName("b", 9104);

    // \xa -> xa
    const xa_ref = RExpr{ .Var = .{ .name = xa, .span = testSpan() } };
    const id_lam = RExpr{ .Lambda = .{
        .params = &.{xa},
        .param_spans = &.{testSpan()},
        .body = &xa_ref,
    } };
    const id_decl = RDecl{ .FunBind = .{
        .name = id_name,
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = id_lam }, .span = testSpan() }},
        .span = testSpan(),
    } };

    // \a -> \b -> a
    const a_ref = RExpr{ .Var = .{ .name = a_name, .span = testSpan() } };
    const inner_lam = RExpr{ .Lambda = .{
        .params = &.{b_name},
        .param_spans = &.{testSpan()},
        .body = &a_ref,
    } };
    const const_lam = RExpr{ .Lambda = .{
        .params = &.{a_name},
        .param_spans = &.{testSpan()},
        .body = &inner_lam,
    } };
    const const_decl = RDecl{ .FunBind = .{
        .name = const_name,
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = const_lam }, .span = testSpan() }},
        .span = testSpan(),
    } };

    // id 1
    const id_ref = RExpr{ .Var = .{ .name = id_name, .span = testSpan() } };
    const one = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const id_app = RExpr{ .App = .{ .fn_expr = &id_ref, .arg_expr = &one } };

    // const_ True 42
    const const_ref = RExpr{ .Var = .{ .name = const_name, .span = testSpan() } };
    const true_expr = RExpr{ .Var = .{ .name = Known.Con.True, .span = testSpan() } };
    const forty_two = RExpr{ .Lit = .{ .Int = .{ .value = 42, .span = testSpan() } } };
    const const_app1 = RExpr{ .App = .{ .fn_expr = &const_ref, .arg_expr = &true_expr } };
    const const_app2 = RExpr{ .App = .{ .fn_expr = &const_app1, .arg_expr = &forty_two } };

    // (id 1, const_ True 42)
    const tuple = RExpr{ .Tuple = &.{ id_app, const_app2 } };

    // let const_ = ... in (...)
    const inner_let = RExpr{ .Let = .{ .binds = &.{const_decl}, .body = &tuple } };
    // let id = ... in let const_ = ... in ...
    const outer_let = RExpr{ .Let = .{ .binds = &.{id_decl}, .body = &inner_let } };

    const ty = try infer(&ctx, outer_let);
    try testing.expect(!diags.hasErrors());

    // Result should be (Int, Bool)
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqual(@as(usize, 2), chased.Con.args.len);
    try testing.expectEqualStrings("Int", chased.Con.args[0].chase().Con.name.base);
    try testing.expectEqualStrings("Bool", chased.Con.args[1].chase().Con.name.base);
}

// ── Occurs check ──────────────────────────────────────────────────────

test "infer: occurs check rejected — f = \\x -> x x" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const x_name = testName("x", 6000);
    const x_ref1 = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const x_ref2 = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const self_app = RExpr{ .App = .{ .fn_expr = &x_ref1, .arg_expr = &x_ref2 } };
    const lam = RExpr{ .Lambda = .{
        .params = &.{x_name},
        .param_spans = &.{testSpan()},
        .body = &self_app,
    } };

    _ = try infer(&ctx, lam);

    try testing.expect(diags.hasErrors());
    const msg = diags.diagnostics.items[0].message;
    try testing.expect(std.mem.indexOf(u8, msg, "occurs check") != null);
}

// ── If expression ─────────────────────────────────────────────────────

test "infer: if True then 1 else 2 has type Int" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const true_expr = RExpr{ .Var = .{ .name = Known.Con.True, .span = testSpan() } };
    const one = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const two = RExpr{ .Lit = .{ .Int = .{ .value = 2, .span = testSpan() } } };
    const if_expr = RExpr{ .If = .{
        .condition = &true_expr,
        .then_expr = &one,
        .else_expr = &two,
    } };

    const ty = try infer(&ctx, if_expr);

    try testing.expect(!diags.hasErrors());
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("Int", chased.Con.name.base);
}

test "infer: if branches of different types emits error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const true_expr = RExpr{ .Var = .{ .name = Known.Con.True, .span = testSpan() } };
    const one = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const ch = RExpr{ .Lit = .{ .Char = .{ .value = 'a', .span = testSpan() } } };
    const if_expr = RExpr{ .If = .{
        .condition = &true_expr,
        .then_expr = &one,
        .else_expr = &ch,
    } };

    _ = try infer(&ctx, if_expr);

    try testing.expect(diags.hasErrors());
}

// ── List inference ────────────────────────────────────────────────────

test "infer: [1, 2, 3] has type [Int]" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const one = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const two = RExpr{ .Lit = .{ .Int = .{ .value = 2, .span = testSpan() } } };
    const three = RExpr{ .Lit = .{ .Int = .{ .value = 3, .span = testSpan() } } };
    const list_expr = RExpr{ .List = &.{ one, two, three } };

    const ty = try infer(&ctx, list_expr);

    try testing.expect(!diags.hasErrors());
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqualStrings("[]", chased.Con.name.base);
    try testing.expectEqual(@as(usize, 1), chased.Con.args.len);
    const elem = chased.Con.args[0].chase();
    try testing.expect(elem == .Con);
    try testing.expectEqualStrings("Int", elem.Con.name.base);
}

test "infer: heterogeneous list emits error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const one = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const ch = RExpr{ .Lit = .{ .Char = .{ .value = 'a', .span = testSpan() } } };
    const list_expr = RExpr{ .List = &.{ one, ch } };

    _ = try infer(&ctx, list_expr);

    try testing.expect(diags.hasErrors());
}

// ── Tuple inference ───────────────────────────────────────────────────

test "infer: (1, True) has type (Int, Bool)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const one = RExpr{ .Lit = .{ .Int = .{ .value = 1, .span = testSpan() } } };
    const true_e = RExpr{ .Var = .{ .name = Known.Con.True, .span = testSpan() } };
    const tuple = RExpr{ .Tuple = &.{ one, true_e } };

    const ty = try infer(&ctx, tuple);

    try testing.expect(!diags.hasErrors());
    const chased = ty.chase();
    try testing.expect(chased == .Con);
    try testing.expectEqual(@as(usize, 2), chased.Con.args.len);
    const fst = chased.Con.args[0].chase();
    const snd = chased.Con.args[1].chase();
    try testing.expectEqualStrings("Int", fst.Con.name.base);
    try testing.expectEqualStrings("Bool", snd.Con.name.base);
}

// ── Module-level inference ────────────────────────────────────────────

test "inferModule: main = putStrLn \"Hello\"" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const main_name = testName("main", 7000);
    const str_lit = RExpr{ .Lit = .{ .String = .{ .value = "Hello", .span = testSpan() } } };
    const psl = RExpr{ .Var = .{ .name = Known.Fn.putStrLn, .span = testSpan() } };
    const app = RExpr{ .App = .{ .fn_expr = &psl, .arg_expr = &str_lit } };

    const module = RenamedModule{
        .module_name = "Main",
        .declarations = &.{RDecl{ .FunBind = .{
            .name = main_name,
            .equations = &.{.{
                .patterns = &.{},
                .rhs = .{ .UnGuarded = app },
                .span = testSpan(),
            }},
            .span = testSpan(),
        } }},
        .span = testSpan(),
    };

    var module_types = try inferModule(&ctx, module);
    defer module_types.deinit(alloc);

    try testing.expect(!diags.hasErrors());

    const scheme = module_types.get(main_name.unique);
    try testing.expect(scheme != null);
    // main :: IO ()
    const ty = scheme.?.body.chase();
    try testing.expect(ty == .Con);
    try testing.expectEqualStrings("IO", ty.Con.name.base);
    try testing.expectEqual(@as(usize, 1), ty.Con.args.len);
    const inner = ty.Con.args[0].chase();
    try testing.expect(inner == .Con);
    try testing.expectEqualStrings("()", inner.Con.name.base);
}

test "inferModule: two independent definitions" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    const f_name = testName("f", 8000);
    const g_name = testName("g", 8001);
    const lit_int = RExpr{ .Lit = .{ .Int = .{ .value = 42, .span = testSpan() } } };
    const lit_char = RExpr{ .Lit = .{ .Char = .{ .value = 'a', .span = testSpan() } } };

    const module = RenamedModule{
        .module_name = "Test",
        .declarations = &.{
            RDecl{ .FunBind = .{
                .name = f_name,
                .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit_int }, .span = testSpan() }},
                .span = testSpan(),
            } },
            RDecl{ .FunBind = .{
                .name = g_name,
                .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lit_char }, .span = testSpan() }},
                .span = testSpan(),
            } },
        },
        .span = testSpan(),
    };

    var module_types = try inferModule(&ctx, module);
    defer module_types.deinit(alloc);

    try testing.expect(!diags.hasErrors());

    const f_ty = module_types.get(f_name.unique).?.body.chase();
    const g_ty = module_types.get(g_name.unique).?.body.chase();
    try testing.expectEqualStrings("Int", f_ty.Con.name.base);
    try testing.expectEqualStrings("Char", g_ty.Con.name.base);
}

// ── Type Signature Tests (issue #175) ─────────────────────────────────

test "inferModule: signature matches inferred type" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    // f :: Int -> Int
    // f x = x
    const f_name = testName("f", 9000);
    const x_name = testName("x", 9001);

    const AstType = @import("../frontend/ast.zig").Type;

    // Construct AST type: Int -> Int
    const int_ptr = try alloc.create(AstType);
    int_ptr.* = AstType{ .Con = .{ .name = "Int", .span = testSpan() } };

    const fun_args = try alloc.alloc(*const AstType, 2);
    fun_args[0] = int_ptr;
    fun_args[1] = int_ptr;

    const fun_type = AstType{ .Fun = fun_args };

    // Create the signature declaration
    const sig = RDecl{ .TypeSig = .{
        .names = &.{f_name},
        .type = fun_type,
        .span = testSpan(),
    } };

    // Create the FunBind: f x = x (represented as f = \\x -> x for simplicity)
    const body = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const lam = RExpr{ .Lambda = .{
        .params = &.{x_name},
        .param_spans = &.{testSpan()},
        .body = &body,
    } };
    const funbind = RDecl{ .FunBind = .{
        .name = f_name,
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lam }, .span = testSpan() }},
        .span = testSpan(),
    } };

    const module = RenamedModule{
        .module_name = "SigTest",
        .declarations = &.{ sig, funbind },
        .span = testSpan(),
    };

    var module_types = try inferModule(&ctx, module);
    defer module_types.deinit(alloc);

    // Should have no errors (signature matches)
    try testing.expect(!diags.hasErrors());

    // Check that the binding has the correct type
    const scheme = module_types.get(f_name.unique).?;
    const ty = scheme.body.chase();
    try testing.expect(ty == .Fun);
    const arg = ty.Fun.arg.chase();
    try testing.expect(arg == .Con);
    try testing.expectEqualStrings("Int", arg.Con.name.base);
}

test "inferModule: signature mismatch produces error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    // f :: Int
    // f = True
    // This should produce a type error: Int vs Bool
    const f_name = testName("f", 9100);

    const AstType = @import("../frontend/ast.zig").Type;

    // Construct AST type: Int
    const int_type = AstType{ .Con = .{ .name = "Int", .span = testSpan() } };

    const sig = RDecl{ .TypeSig = .{
        .names = &.{f_name},
        .type = int_type,
        .span = testSpan(),
    } };

    const true_lit = RExpr{ .Var = .{ .name = Known.Con.True, .span = testSpan() } };
    const funbind = RDecl{ .FunBind = .{
        .name = f_name,
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = true_lit }, .span = testSpan() }},
        .span = testSpan(),
    } };

    const module = RenamedModule{
        .module_name = "SigMismatch",
        .declarations = &.{ sig, funbind },
        .span = testSpan(),
    };

    var module_types = try inferModule(&ctx, module);
    defer module_types.deinit(alloc);

    try testing.expect(diags.hasErrors());
}

test "inferModule: type variables in signature are scoped correctly" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = try TyEnv.init(alloc);
    defer env.deinit();
    var mv = MetaVarSupply{};
    var us = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    try env_mod.initBuiltins(&env, alloc, &us);

    var ctx = makeCtx(&arena, &env, &mv, &us, &diags);

    // f :: a -> a
    // f x = x
    const f_name = testName("f", 9200);
    const x_name = testName("x", 9201);

    const AstType = @import("../frontend/ast.zig").Type;

    // Construct AST type: a -> a
    const a_var_p1 = try alloc.create(AstType);
    a_var_p1.* = AstType{ .Var = "a" };

    const a_var_p2 = try alloc.create(AstType);
    a_var_p2.* = AstType{ .Var = "a" };

    const fun_args = try alloc.alloc(*const AstType, 2);
    fun_args[0] = a_var_p1;
    fun_args[1] = a_var_p2;

    const fun_type = AstType{ .Fun = fun_args };

    const sig = RDecl{ .TypeSig = .{
        .names = &.{f_name},
        .type = fun_type,
        .span = testSpan(),
    } };

    const body = RExpr{ .Var = .{ .name = x_name, .span = testSpan() } };
    const lam = RExpr{ .Lambda = .{
        .params = &.{x_name},
        .param_spans = &.{testSpan()},
        .body = &body,
    } };
    const funbind = RDecl{ .FunBind = .{
        .name = f_name,
        .equations = &.{.{ .patterns = &.{}, .rhs = .{ .UnGuarded = lam }, .span = testSpan() }},
        .span = testSpan(),
    } };

    const module = RenamedModule{
        .module_name = "PolySig",
        .declarations = &.{ sig, funbind },
        .span = testSpan(),
    };

    var module_types = try inferModule(&ctx, module);
    defer module_types.deinit(alloc);

    try testing.expect(!diags.hasErrors());

    const scheme = module_types.get(f_name.unique).?;
    try testing.expectEqual(@as(usize, 1), scheme.binders.len);
}
