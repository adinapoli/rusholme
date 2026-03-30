//! Lambda Lifting - Core to Core transformation.
//!
//! Transforms nested lambda expressions into top-level function definitions.
//! This is a prerequisite for Core → GRIN translation (#313).
//!
//! Algorithm (Johnsson 1985):
//! 1. Traverse the program to find all lambda expressions.
//! 2. For each lambda, compute its free variables.
//! 3. Lift nested lambdas to top-level Bind entries.
//! 4. Add free variables as extra parameters to lifted functions.
//! 5. Rewrite lambda literals to function calls passing free variables.
//!
//! Example:
//! ```
//! Core before:
//!   f = \x -> (\y -> x + y) 5
//!
//! Core after:
//!   f = \x -> lifted_y_x x 5
//!   lifted_y_x x y = x + y
//! ```
//!
//! Reference:
//! - Johnsson, T. (1985). "Lambda Lifting: Transforming Programs to Recursive
//!   Equations".
//! - GHC's implementation: compiler/GHC/Core/Lift.hs

const std = @import("std");
const core = @import("ast.zig");
const Name = core.Name;
const Unique = core.Unique;
const Expr = core.Expr;
const Bind = core.Bind;
const BindPair = core.BindPair;
const Id = core.Id;
const CoreType = core.CoreType;
const CoreLiteral = core.Literal;
const SourceSpan = core.SourceSpan;

// ── Lambda Information ─────────────────────────────────────────────────────

/// Information about a lambda expression found during collection.
const LambdaInfo = struct {
    /// Unique ID for tracking this lambda during collection.
    id: u64,
    /// Pointer to the original lambda expression (for identification).
    expr: *const Expr,
    /// Body of the lambda (needed for reconstruction during lifting).
    body: *const Expr,
    /// Free variables of this lambda (by unique ID).
    free_vars: []const u64,
    /// Parameters of the lambda (before lifting).
    params: []const Id,
    /// Type of the lambda (for generating lifted function types).
    ty: CoreType,
    /// Whether this lambda must be lifted to a top-level binding.
    /// False only for leading Lam chains of top-level Bind entries,
    /// which translateDef peels as function parameters.
    needs_lifting: bool,
    /// Generated name for the lifted function.
    lifted_name: Name,
};

// Explicit error set for mutually recursive functions
const LifterError = std.mem.Allocator.Error;

/// A set of variable unique IDs, using a hash set.
const VarSet = struct {
    set: std.AutoHashMapUnmanaged(u64, void),
    const Allocator = std.mem.Allocator;

    fn init(alloc: Allocator) VarSet {
        _ = alloc;
        return .{ .set = .{} };
    }

    fn deinit(self: *VarSet, alloc: Allocator) void {
        self.set.deinit(alloc);
    }

    fn add(self: *VarSet, alloc: Allocator, id: u64) !void {
        try self.set.put(alloc, id, {});
    }

    fn contains(self: *const VarSet, id: u64) bool {
        return self.set.contains(id);
    }

    fn merge(self: *VarSet, alloc: Allocator, other: *const VarSet) !void {
        var it = other.set.iterator();
        while (it.next()) |entry| {
            try self.set.put(alloc, entry.key_ptr.*, {});
        }
    }

    fn toSlice(self: *VarSet, alloc: Allocator) ![]u64 {
        const result = try alloc.alloc(u64, self.set.count());
        var i: usize = 0;
        var it = self.set.iterator();
        while (it.next()) |entry| {
            result[i] = entry.key_ptr.*;
            i += 1;
        }
        return result;
    }

    fn clone(self: *const VarSet, alloc: Allocator) !VarSet {
        var result = VarSet.init(alloc);
        try result.merge(alloc, self);
        return result;
    }
};

/// Set of expression pointers identifying leading parameter lambdas.
const LeadingLamSet = std.AutoHashMapUnmanaged(usize, void);

// ── Lambda Lifter Context ─────────────────────────────────────────────────

/// Context for the lambda lifting transformation.
pub const LambdaLifter = struct {
    alloc: std.mem.Allocator,
    /// Counter for generating unique lambda IDs.
    lambda_counter: u64 = 0,
    /// Counter for generating unique IDs for lifted function names.
    lifted_id_counter: u64 = 0,
    /// Map from lambda ID to LambdaInfo.
    lambdas: std.AutoHashMapUnmanaged(u64, LambdaInfo),
    /// Map from expression pointer to lambda ID (for identifying lambdas during rewrite).
    expr_to_lambda: std.AutoHashMapUnmanaged(usize, u64),
    /// Variables visible at top-level scope (program binders + external imports).
    /// Populated in Phase 1 of lambdaLift; read-only during Phase 2 traversal.
    top_level_vars: VarSet,
    /// Memoization cache for rewriteExpr, keyed by source expression pointer.
    /// Preserves pointer sharing from the desugarer: the sequential
    /// pattern-match algorithm produces shared fallback nodes (a DAG), and
    /// without this cache rewriteExpr would clone each shared subtree at
    /// every occurrence, causing exponential blowup in AST size.
    rewrite_cache: std.AutoHashMapUnmanaged(usize, *Expr) = .{},

    pub fn init(alloc: std.mem.Allocator) LambdaLifter {
        return .{
            .alloc = alloc,
            .lambdas = .{},
            .expr_to_lambda = .{},
            .top_level_vars = VarSet.init(alloc),
        };
    }

    pub fn deinit(self: *LambdaLifter) void {
        // Free allocated arrays in LambdaInfo first, before deinit the hashmap
        var it = self.lambdas.iterator();
        while (it.next()) |entry| {
            const info = &entry.value_ptr.*;
            self.alloc.free(info.free_vars);
        }

        self.lambdas.deinit(self.alloc);
        self.expr_to_lambda.deinit(self.alloc);
        self.top_level_vars.deinit(self.alloc);
        self.rewrite_cache.deinit(self.alloc);
    }

    /// Walk the leading Lam chain of an expression and record the pointer
    /// addresses of those Lam nodes. These are "parameter lambdas" that
    /// translateDef will peel as function parameters — they must NOT be lifted.
    fn collectLeadingLamPtrs(expr: *const Expr, out: *LeadingLamSet, alloc: std.mem.Allocator) !void {
        var current = expr;
        while (true) {
            switch (current.*) {
                .Lam => |l| {
                    try out.put(alloc, @intFromPtr(current), {});
                    current = l.body;
                },
                else => break,
            }
        }
    }

    /// Register a lambda expression and return its unique ID.
    fn registerLambda(self: *LambdaLifter, expr: *const Expr) !u64 {
        const lambda_id = self.lambda_counter + 1;
        self.lambda_counter = lambda_id;

        // Store mapping from expr pointer to lambda ID
        const expr_ptr = @intFromPtr(expr);
        try self.expr_to_lambda.put(self.alloc, expr_ptr, lambda_id);

        return lambda_id;
    }

    /// Complete lambda registration after free variable computation.
    fn completeLambda(self: *LambdaLifter, lambda_id: u64, free_vars: []const u64, params: []const Id, body: *const Expr, ty: CoreType, needs_lifting: bool) !void {
        const lifted_name = Name{
            .base = "lifted",
            .unique = Unique{ .value = self.lifted_id_counter },
        };
        self.lifted_id_counter += 1;

        const info = LambdaInfo{
            .id = lambda_id,
            .expr = body,
            .body = body,
            .free_vars = free_vars,
            .params = params,
            .ty = ty,
            .needs_lifting = needs_lifting,
            .lifted_name = lifted_name,
        };
        try self.lambdas.put(self.alloc, lambda_id, info);
    }

    /// Collect all lambdas in an expression and compute their free variables.
    /// Returns a fresh VarSet containing the free variables of the expression.
    ///
    /// `scope` is an immutable snapshot of variables currently in scope.
    /// It is passed by value (shallow copy) and never mutated — when the
    /// scope must be extended (let binders, case binders, lambda params),
    /// a deep clone is created via `scope.clone()`.
    ///
    /// For expression lambdas (needs_lifting), the scope resets to
    /// `self.top_level_vars ∪ {param}` — enclosing lambda parameters
    /// become free variables that are passed as extra arguments.
    /// The "contribution" propagated to the caller is filtered by the
    /// caller's scope, preventing variables already in scope from leaking
    /// upward.  This is the fix for #659.
    ///
    /// `leading_lams` contains the pointer addresses of Lam nodes that form
    /// leading parameter chains on top-level binding RHS. Lambdas in this set
    /// are NOT lifted (translateDef peels them).
    fn collectFreeVarsOf(
        self: *LambdaLifter,
        expr: *const Expr,
        scope: VarSet,
        leading_lams: *const LeadingLamSet,
    ) !VarSet {
        var fvs = VarSet.init(self.alloc);
        errdefer fvs.deinit(self.alloc);

        switch (expr.*) {
            .Var => |v| {
                // Data constructors are globally available and must never be
                // captured as free variables.  In Haskell, constructor names
                // start with an uppercase letter or ':'.
                if (!isDataCon(v.name.base) and !scope.contains(v.name.unique.value)) {
                    try fvs.add(self.alloc, v.name.unique.value);
                }
            },
            .Lit => {},
            .App => |a| {
                var fn_fvs = try self.collectFreeVarsOf(a.fn_expr, scope, leading_lams);
                defer fn_fvs.deinit(self.alloc);
                var arg_fvs = try self.collectFreeVarsOf(a.arg, scope, leading_lams);
                defer arg_fvs.deinit(self.alloc);
                try fvs.merge(self.alloc, &fn_fvs);
                try fvs.merge(self.alloc, &arg_fvs);
            },
            .Lam => |l| {
                const is_leading = leading_lams.contains(@intFromPtr(expr));
                const needs_lifting = !is_leading;

                const lambda_id = try self.registerLambda(expr);
                const param_id = l.binder.name.unique.value;

                if (needs_lifting) {
                    // Expression lambda: will be lifted to top level.
                    //
                    // Scope resets to top-level vars + own parameter.
                    // Enclosing lambda parameters are NOT in scope for the
                    // lifted function — they become free variables passed as
                    // extra arguments at the call site.
                    var inner_scope = try self.top_level_vars.clone(self.alloc);
                    defer inner_scope.deinit(self.alloc);
                    try inner_scope.add(self.alloc, param_id);

                    var inner_fvs = try self.collectFreeVarsOf(l.body, inner_scope, leading_lams);
                    defer inner_fvs.deinit(self.alloc);

                    // Complete lambda registration with free variables.
                    const fvs_slice = try inner_fvs.toSlice(self.alloc);
                    // Heap-allocate the params slice so it outlives this scope.
                    // Using a temporary `&.{l.binder}` would create a dangling
                    // reference — all lifted lambdas would share the same
                    // (overwritten) stack slot.
                    const param_slice = try self.alloc.alloc(Id, 1);
                    param_slice[0] = l.binder;
                    try self.completeLambda(lambda_id, fvs_slice, param_slice, l.body, l.binder.ty, needs_lifting);

                    // Compute function type with free vars added as parameters.
                    var lifted_ty = l.binder.ty;
                    for (fvs_slice) |_| {
                        const p_ty = try self.alloc.create(CoreType);
                        p_ty.* = intType(); // tracked in: follow-up issue for placeholder types
                        const param_ty = try self.alloc.create(CoreType);
                        param_ty.* = lifted_ty;
                        lifted_ty = CoreType{ .FunTy = .{ .arg = p_ty, .res = param_ty } };
                    }

                    // Update the lambda's type.
                    if (self.lambdas.getPtr(lambda_id)) |info_ptr| {
                        info_ptr.ty = lifted_ty;
                    }

                    // Propagate: only free vars NOT already in the caller's
                    // scope.  This is the key fix for #659 — without the
                    // filter, an enclosing lambda's own parameter leaks
                    // upward as a spurious free variable.
                    for (fvs_slice) |fv_id| {
                        if (!scope.contains(fv_id)) {
                            try fvs.add(self.alloc, fv_id);
                        }
                    }
                } else {
                    // Parameter lambda: part of the leading chain on a
                    // top-level binding RHS. Keep in place — translateDef
                    // will peel it as a function parameter.
                    //
                    // Scope handling: clone scope and add the parameter so
                    // that the body sees it as in-scope (not free).
                    var extended_scope = try scope.clone(self.alloc);
                    defer extended_scope.deinit(self.alloc);
                    try extended_scope.add(self.alloc, param_id);

                    var body_fvs = try self.collectFreeVarsOf(l.body, extended_scope, leading_lams);
                    defer body_fvs.deinit(self.alloc);

                    // Complete lambda registration (not lifted, but still tracked).
                    const fvs_slice = try body_fvs.toSlice(self.alloc);
                    try self.completeLambda(lambda_id, fvs_slice, &.{l.binder}, l.body, l.binder.ty, needs_lifting);

                    // Leading lambdas contribute their body's free vars to the parent.
                    try fvs.merge(self.alloc, &body_fvs);
                }
            },
            .Let => |l| {
                switch (l.bind) {
                    .NonRec => |pair| {
                        // RHS is evaluated in the current scope (the binder
                        // is not yet visible to its own definition).
                        var rhs_fvs = try self.collectFreeVarsOf(pair.rhs, scope, leading_lams);
                        defer rhs_fvs.deinit(self.alloc);
                        try fvs.merge(self.alloc, &rhs_fvs);

                        // Body sees the binder in scope.
                        var body_scope = try scope.clone(self.alloc);
                        defer body_scope.deinit(self.alloc);
                        try body_scope.add(self.alloc, pair.binder.name.unique.value);

                        var body_fvs = try self.collectFreeVarsOf(l.body, body_scope, leading_lams);
                        defer body_fvs.deinit(self.alloc);
                        try fvs.merge(self.alloc, &body_fvs);
                    },
                    .Rec => |pairs| {
                        // All binders are in scope for every RHS and the body.
                        var rec_scope = try scope.clone(self.alloc);
                        defer rec_scope.deinit(self.alloc);
                        for (pairs) |pair| {
                            try rec_scope.add(self.alloc, pair.binder.name.unique.value);
                        }

                        for (pairs) |pair| {
                            var rhs_fvs = try self.collectFreeVarsOf(pair.rhs, rec_scope, leading_lams);
                            defer rhs_fvs.deinit(self.alloc);
                            try fvs.merge(self.alloc, &rhs_fvs);
                        }

                        var body_fvs = try self.collectFreeVarsOf(l.body, rec_scope, leading_lams);
                        defer body_fvs.deinit(self.alloc);
                        try fvs.merge(self.alloc, &body_fvs);
                    },
                }
            },
            .Case => |c| {
                // Scrutinee is evaluated in the current scope.
                var scrut_fvs = try self.collectFreeVarsOf(c.scrutinee, scope, leading_lams);
                defer scrut_fvs.deinit(self.alloc);
                try fvs.merge(self.alloc, &scrut_fvs);

                // Case binder is in scope for all alternatives.
                var case_scope = try scope.clone(self.alloc);
                defer case_scope.deinit(self.alloc);
                try case_scope.add(self.alloc, c.binder.name.unique.value);

                for (c.alts) |alt| {
                    // Each alt adds its pattern binders to scope.
                    var alt_scope = try case_scope.clone(self.alloc);
                    defer alt_scope.deinit(self.alloc);
                    for (alt.binders) |binder| {
                        try alt_scope.add(self.alloc, binder.name.unique.value);
                    }

                    var alt_fvs = try self.collectFreeVarsOf(alt.body, alt_scope, leading_lams);
                    defer alt_fvs.deinit(self.alloc);
                    try fvs.merge(self.alloc, &alt_fvs);
                }
            },
            .Type => {},
            .Coercion => {},
        }

        return fvs;
    }

    /// Rewrite an expression, replacing lifted lambdas with function calls.
    fn rewriteExpr(self: *LambdaLifter, expr: *const Expr, current_binders: []const u64) LifterError!*Expr {
        // Memoize: if we've already rewritten this exact expression, reuse
        // the result.  This preserves pointer sharing from the desugarer's
        // sequential pattern-match algorithm (shared fallback nodes).
        const expr_key = @intFromPtr(expr);
        if (self.rewrite_cache.get(expr_key)) |cached| return cached;

        const new_expr = try self.alloc.create(Expr);

        switch (expr.*) {
            .Var => |v| {
                new_expr.* = .{ .Var = v };
            },
            .Lit => |l| {
                new_expr.* = .{ .Lit = l };
            },
            .App => |a| {
                const new_fn = try self.rewriteExpr(a.fn_expr, current_binders);
                const new_arg = try self.rewriteExpr(a.arg, current_binders);
                new_expr.* = .{ .App = .{
                    .fn_expr = new_fn,
                    .arg = new_arg,
                    .span = a.span,
                } };
            },
            .Lam => |l| {
                // Check if this lambda was registered and needs lifting.
                const expr_ptr = @intFromPtr(expr);
                if (self.expr_to_lambda.get(expr_ptr)) |lambda_id| {
                    if (self.lambdas.getPtr(lambda_id)) |info| {
                        if (info.needs_lifting) {
                            // This lambda was lifted. Replace with a call to
                            // the lifted function, passing free variables as
                            // extra arguments.
                            const lifted_id = Id{
                                .name = info.lifted_name,
                                .ty = info.ty,
                                .span = l.span,
                            };

                            // Start with the lifted function name
                            var current: *Expr = try self.alloc.create(Expr);
                            current.* = .{ .Var = lifted_id };

                            // Wrap in App nodes for each free variable
                            for (info.free_vars) |fv_id| {
                                const fv_var = try self.alloc.create(Expr);
                                fv_var.* = .{ .Var = .{
                                    .name = .{ .base = "fv", .unique = .{ .value = fv_id } },
                                    .ty = intType(), // tracked in: follow-up issue for placeholder types
                                    .span = l.span,
                                } };

                                const app = try self.alloc.create(Expr);
                                app.* = .{ .App = .{
                                    .fn_expr = current,
                                    .arg = fv_var,
                                    .span = l.span,
                                } };
                                current = app;
                            }

                            new_expr.* = current.*;
                        } else {
                            // Parameter lambda — keep as-is, just rewrite body.
                            const new_body = try self.rewriteExpr(l.body, current_binders);
                            new_expr.* = .{ .Lam = .{
                                .binder = l.binder,
                                .body = new_body,
                                .span = l.span,
                            } };
                        }
                    } else {
                        // Lambda info not found, keep as is
                        const new_body = try self.rewriteExpr(l.body, current_binders);
                        new_expr.* = .{ .Lam = .{
                            .binder = l.binder,
                            .body = new_body,
                            .span = l.span,
                        } };
                    }
                } else {
                    // Lambda not registered, rewrite body
                    const new_body = try self.rewriteExpr(l.body, current_binders);
                    new_expr.* = .{ .Lam = .{
                        .binder = l.binder,
                        .body = new_body,
                        .span = l.span,
                    } };
                }
            },
            .Let => |l| {
                const new_bind = try self.rewriteBind(l.bind, current_binders);
                // For the body, we need to add the let-binders to the available binders
                const new_binders = try self.expandBinders(current_binders, l.bind);
                defer self.alloc.free(new_binders);
                const new_body = try self.rewriteExpr(l.body, new_binders);
                new_expr.* = .{ .Let = .{
                    .bind = new_bind,
                    .body = new_body,
                    .span = l.span,
                } };
            },
            .Case => |c| {
                const new_scrutinee = try self.rewriteExpr(c.scrutinee, current_binders);
                const new_alts = try self.alloc.alloc(core.Alt, c.alts.len);
                for (c.alts, 0..) |alt, i| {
                    // Add alt binders to available binders for the alt body
                    var alt_binders = try self.alloc.alloc(u64, current_binders.len + alt.binders.len);
                    @memcpy(alt_binders[0..current_binders.len], current_binders);
                    for (alt.binders, 0..) |binder, j| {
                        alt_binders[current_binders.len + j] = binder.name.unique.value;
                    }
                    const alt_body = try self.rewriteExpr(alt.body, alt_binders);
                    self.alloc.free(alt_binders);
                    new_alts[i] = .{
                        .con = alt.con,
                        .binders = alt.binders,
                        .body = alt_body,
                    };
                }
                new_expr.* = .{ .Case = .{
                    .scrutinee = new_scrutinee,
                    .binder = c.binder,
                    .ty = c.ty,
                    .alts = new_alts,
                    .span = c.span,
                } };
            },
            .Type => |t| {
                new_expr.* = .{ .Type = t };
            },
            .Coercion => {
                new_expr.* = .{ .Coercion = .Refl };
            },
        }

        self.rewrite_cache.put(self.alloc, expr_key, new_expr) catch return error.OutOfMemory;
        return new_expr;
    }

    /// Expand the current binders list with binders from a Let binding.
    fn expandBinders(self: *LambdaLifter, current: []const u64, bind: Bind) ![]u64 {
        switch (bind) {
            .NonRec => |pair| {
                const result = try self.alloc.alloc(u64, current.len + 1);
                @memcpy(result[0..current.len], current);
                result[current.len] = pair.binder.name.unique.value;
                return result;
            },
            .Rec => |pairs| {
                const result = try self.alloc.alloc(u64, current.len + pairs.len);
                @memcpy(result[0..current.len], current);
                for (pairs, 0..) |pair, i| {
                    result[current.len + i] = pair.binder.name.unique.value;
                }
                return result;
            },
        }
    }

    /// Rewrite a binding.
    fn rewriteBind(self: *LambdaLifter, bind: Bind, current_binders: []const u64) LifterError!Bind {
        switch (bind) {
            .NonRec => |pair| {
                const new_rhs = try self.rewriteExpr(pair.rhs, current_binders);
                return .{ .NonRec = .{
                    .binder = pair.binder,
                    .rhs = new_rhs,
                } };
            },
            .Rec => |pairs| {
                const expanded = try self.expandBinders(current_binders, .{ .Rec = pairs });
                defer self.alloc.free(expanded);
                const new_pairs = try self.alloc.alloc(BindPair, pairs.len);
                for (pairs, 0..) |pair, i| {
                    const new_rhs = try self.rewriteExpr(pair.rhs, expanded);
                    new_pairs[i] = .{
                        .binder = pair.binder,
                        .rhs = new_rhs,
                    };
                }
                return .{ .Rec = new_pairs };
            },
        }
    }
};

// ── Public API ─────────────────────────────────────────────────────────────

/// Lambda-lift a Core program.
///
/// Returns a new program with all nested lambdas lifted to top-level
/// function definitions.
///
/// `external_scope` provides unique IDs of names defined outside this
/// module (e.g. Prelude/imported functions) that should be considered
/// globally in-scope when computing free variables.  Without this,
/// references to imported functions inside nested lambdas would be
/// mis-classified as free variables and incorrectly captured.
pub fn lambdaLift(alloc: std.mem.Allocator, program: core.CoreProgram, external_scope: ?[]const u64) !core.CoreProgram {
    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();

    // Phase 1: Build top-level scope (program binders + externals).
    // Include externally-visible names (Prelude, imports) so that the
    // free-variable analysis does not capture them as closures.
    if (external_scope) |ext| {
        for (ext) |id| {
            try lifter.top_level_vars.add(alloc, id);
        }
    }

    for (program.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                try lifter.top_level_vars.add(alloc, pair.binder.name.unique.value);
            },
            .Rec => |pairs| {
                for (pairs) |pair| {
                    try lifter.top_level_vars.add(alloc, pair.binder.name.unique.value);
                }
            },
        }
    }

    // Phase 2: Collect all lambdas and their free variables.
    // For each binding, compute the leading Lam set (parameter lambdas that
    // translateDef will peel) before traversing.
    var leading_lams = LeadingLamSet{};
    defer leading_lams.deinit(alloc);

    for (program.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                leading_lams.clearRetainingCapacity();
                try LambdaLifter.collectLeadingLamPtrs(pair.rhs, &leading_lams, alloc);
                var result_fvs = try lifter.collectFreeVarsOf(pair.rhs, lifter.top_level_vars, &leading_lams);
                result_fvs.deinit(alloc);
            },
            .Rec => |pairs| {
                for (pairs) |pair| {
                    leading_lams.clearRetainingCapacity();
                    try LambdaLifter.collectLeadingLamPtrs(pair.rhs, &leading_lams, alloc);
                    var result_fvs = try lifter.collectFreeVarsOf(pair.rhs, lifter.top_level_vars, &leading_lams);
                    result_fvs.deinit(alloc);
                }
            },
        }
    }

    // Derive top-level slice for Phase 4 (rewriteBind needs []const u64).
    const top_level_slice = try lifter.top_level_vars.toSlice(alloc);

    // Phase 3: Generate lifted function bindings.
    var lifted_binds = std.ArrayListUnmanaged(Bind){};
    defer lifted_binds.deinit(alloc);

    var it = lifter.lambdas.iterator();
    while (it.next()) |entry| {
        const info = &entry.value_ptr.*;

        if (!info.needs_lifting) {
            continue;
        }

        // Create a binding for the lifted function.
        // The function parameters are the free vars (extra params) plus the
        // original lambda params.

        // Build the lifted function body as a Lam chain:
        //   \fv1 -> \fv2 -> ... \fvN -> \p1 -> ... \pM -> body
        var current_body = info.body;

        // Wrap original parameters (innermost)
        var k = info.params.len;
        while (k > 0) {
            k -= 1;
            const lam_expr = try alloc.create(Expr);
            lam_expr.* = .{ .Lam = .{
                .binder = info.params[k],
                .body = current_body,
                .span = info.params[0].span,
            } };
            current_body = lam_expr;
        }

        // Wrap free variable parameters (outermost).
        //
        // Iterate in REVERSE so that free_vars[0] ends up as the outermost
        // lambda (first parameter), matching Phase 4 which applies free_vars[0]
        // first.  Forward iteration produces LIFO wrapping, making free_vars[0]
        // the innermost param — the opposite of what Phase 4 expects.
        var fv_i = info.free_vars.len;
        while (fv_i > 0) {
            fv_i -= 1;
            const fv = info.free_vars[fv_i];
            const fv_binder = Id{
                .name = .{ .base = "fv", .unique = .{ .value = fv } },
                .ty = intType(), // tracked in: follow-up issue for placeholder types
                .span = info.params[0].span,
            };

            const lam_expr = try alloc.create(Expr);
            lam_expr.* = .{ .Lam = .{
                .binder = fv_binder,
                .body = current_body,
                .span = info.params[0].span,
            } };
            current_body = lam_expr;
        }

        // Create the new binding
        try lifted_binds.append(alloc, .{ .NonRec = .{
            .binder = Id{
                .name = info.lifted_name,
                .ty = info.ty,
                .span = info.params[0].span,
            },
            .rhs = current_body,
        } });
    }

    // Phase 4: Rewrite the original bindings.
    var new_binds = std.ArrayListUnmanaged(Bind){};
    defer new_binds.deinit(alloc);

    for (program.binds) |bind| {
        const new_bind = try lifter.rewriteBind(bind, top_level_slice);
        try new_binds.append(alloc, new_bind);
    }

    // Phase 5: Combine lifted bindings with original bindings.
    const all_binds_len = new_binds.items.len + lifted_binds.items.len;
    const all_binds = try alloc.alloc(Bind, all_binds_len);

    var idx: usize = 0;
    for (lifted_binds.items) |b| {
        all_binds[idx] = b;
        idx += 1;
    }
    for (new_binds.items) |b| {
        all_binds[idx] = b;
        idx += 1;
    }

    return core.CoreProgram{
        .data_decls = program.data_decls,
        .binds = all_binds,
    };
}

// ── Helper Functions ─────────────────────────────────────────────────────

/// Return true if `name` is a Haskell data constructor.
///
/// Data constructors are globally available and must never be captured as
/// free variables during lambda lifting.  In Haskell:
///   - Named constructors start with uppercase: `True`, `Just`, `MkDict$Show`
///   - Operator constructors start with `:`: `(:)` in source, `(:)` in Core
///   - Special syntax constructors: `[]`, `()`, `(,)`, `(,,)`, etc.
fn isDataCon(name: []const u8) bool {
    if (name.len == 0) return false;
    if (std.ascii.isUpper(name[0])) return true;
    if (name[0] == ':') return true;
    // Parenthesized operator constructors: (:), (,), (,,), ...
    // and special constructors: (), []
    if (name.len >= 2 and name[0] == '(' and (name[1] == ':' or name[1] == ',' or name[1] == ')'))
        return true;
    if (std.mem.eql(u8, name, "[]")) return true;
    return false;
}

fn intType() CoreType {
    return .{ .TyCon = .{
        .name = .{ .base = "Int", .unique = .{ .value = 0 } },
        .args = &.{},
    } };
}

// ── Tests ─────────────────────────────────────────────────────────────────

const testing = std.testing;

fn testName(base: []const u8, unique: u64) Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn intTypeForTest() CoreType {
    return .{ .TyCon = .{ .name = testName("Int", 0), .args = &.{} } };
}

fn testId(base: []const u8, unique: u64) Id {
    return .{
        .name = testName(base, unique),
        .ty = intTypeForTest(),
        .span = SourceSpan.init(
            core.SourcePos.init(1, 1, 1),
            core.SourcePos.init(1, 1, 10),
        ),
    };
}

fn testSpan() SourceSpan {
    return SourceSpan.init(
        core.SourcePos.init(1, 1, 1),
        core.SourcePos.init(1, 1, 10),
    );
}

/// Check whether an expression tree contains any Lam nodes in
/// non-leading position (i.e., not as the outermost chain on a
/// binding RHS). Used by tests to verify lifting completeness.
fn containsExprLambda(expr: *const Expr) bool {
    switch (expr.*) {
        .Var, .Lit, .Type, .Coercion => return false,
        .App => |a| return containsExprLambda(a.fn_expr) or containsExprLambda(a.arg),
        .Lam => return true, // any Lam inside an expression is an expression lambda
        .Let => |l| {
            const in_bind = switch (l.bind) {
                .NonRec => |pair| containsExprLambdaInRhs(pair.rhs),
                .Rec => |pairs| blk: {
                    for (pairs) |pair| {
                        if (containsExprLambdaInRhs(pair.rhs)) break :blk true;
                    }
                    break :blk false;
                },
            };
            return in_bind or containsExprLambda(l.body);
        },
        .Case => |c| {
            if (containsExprLambda(c.scrutinee)) return true;
            for (c.alts) |alt| {
                if (containsExprLambda(alt.body)) return true;
            }
            return false;
        },
    }
}

/// Check a binding RHS for expression lambdas: skip the leading Lam chain,
/// then check the body.
fn containsExprLambdaInRhs(expr: *const Expr) bool {
    var current = expr;
    while (true) {
        switch (current.*) {
            .Lam => |l| current = l.body,
            else => break,
        }
    }
    return containsExprLambda(current);
}

test "lambdaLift: identity function with no nested lambda" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // f = \x -> x
    const x_id = testId("x", 1);
    const x_var = try alloc.create(Expr);
    x_var.* = .{ .Var = x_id };

    const lambda_body = try alloc.create(Expr);
    lambda_body.* = .{ .Lam = .{
        .binder = x_id,
        .body = x_var,
        .span = testSpan(),
    } };

    const f_bind = Bind{ .NonRec = .{
        .binder = testId("f", 10),
        .rhs = lambda_body,
    } };

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{f_bind},
    };

    const lifted = try lambdaLift(alloc, program, null);

    // No nested lambda → exactly 1 binding, unchanged.
    try testing.expectEqual(@as(usize, 1), lifted.binds.len);
}

test "lambdaLift: nested lambda is lifted" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // f = \x -> (\y -> x) 5
    // The inner lambda \y -> x should be lifted.

    const x_id = testId("x", 1);
    const y_id = testId("y", 2);
    const five_lit = try alloc.create(Expr);
    five_lit.* = .{ .Lit = .{ .val = .{ .Int = 5 }, .span = testSpan() } };

    const x_var = try alloc.create(Expr);
    x_var.* = .{ .Var = x_id };

    // Inner lambda: \y -> x
    const inner_lambda = try alloc.create(Expr);
    inner_lambda.* = .{ .Lam = .{
        .binder = y_id,
        .body = x_var,
        .span = testSpan(),
    } };

    // Apply inner lambda to 5: (\y -> x) 5
    const inner_app = try alloc.create(Expr);
    inner_app.* = .{ .App = .{
        .fn_expr = inner_lambda,
        .arg = five_lit,
        .span = testSpan(),
    } };

    // Outer lambda: \x -> (\y -> x) 5
    const outer_lambda = try alloc.create(Expr);
    outer_lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = inner_app,
        .span = testSpan(),
    } };

    const f_bind = Bind{ .NonRec = .{
        .binder = testId("f", 10),
        .rhs = outer_lambda,
    } };

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{f_bind},
    };

    const lifted = try lambdaLift(alloc, program, null);

    // Should have 2 bindings: the lifted inner lambda + the rewritten f.
    try testing.expectEqual(@as(usize, 2), lifted.binds.len);

    // The original binding (f) should have no expression-position lambdas.
    // It appears second (lifted bindings come first).
    const f_binding = lifted.binds[1];
    switch (f_binding) {
        .NonRec => |pair| {
            try testing.expect(!containsExprLambdaInRhs(pair.rhs));
        },
        .Rec => unreachable,
    }
}

test "lambdaLift: nested lambda free vars include enclosing lambda params" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // f = \x -> (\y -> x) 5
    // The lifted function for \y -> x should have x as a free variable.

    const x_id = testId("x", 1);
    const y_id = testId("y", 2);
    const five_lit = try alloc.create(Expr);
    five_lit.* = .{ .Lit = .{ .val = .{ .Int = 5 }, .span = testSpan() } };

    const x_var = try alloc.create(Expr);
    x_var.* = .{ .Var = x_id };

    const inner_lambda = try alloc.create(Expr);
    inner_lambda.* = .{ .Lam = .{
        .binder = y_id,
        .body = x_var,
        .span = testSpan(),
    } };

    const inner_app = try alloc.create(Expr);
    inner_app.* = .{ .App = .{
        .fn_expr = inner_lambda,
        .arg = five_lit,
        .span = testSpan(),
    } };

    const outer_lambda = try alloc.create(Expr);
    outer_lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = inner_app,
        .span = testSpan(),
    } };

    const f_bind = Bind{ .NonRec = .{
        .binder = testId("f", 10),
        .rhs = outer_lambda,
    } };

    // Use a separate lifter to inspect the lambda info directly.
    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();

    try lifter.top_level_vars.add(alloc, f_bind.NonRec.binder.name.unique.value);

    var leading_lams = LeadingLamSet{};
    defer leading_lams.deinit(alloc);
    try LambdaLifter.collectLeadingLamPtrs(f_bind.NonRec.rhs, &leading_lams, alloc);

    var result_fvs = try lifter.collectFreeVarsOf(f_bind.NonRec.rhs, lifter.top_level_vars, &leading_lams);
    result_fvs.deinit(alloc);

    // Find the lifted lambda (the one with needs_lifting = true).
    var found_lifted = false;
    var lifted_it = lifter.lambdas.iterator();
    while (lifted_it.next()) |entry| {
        const info = &entry.value_ptr.*;
        if (info.needs_lifting) {
            found_lifted = true;
            // The inner lambda \y -> x has x (unique=1) as a free variable.
            try testing.expectEqual(@as(usize, 1), info.free_vars.len);
            try testing.expectEqual(@as(u64, 1), info.free_vars[0]);
        }
    }
    try testing.expect(found_lifted);
}

test "lambdaLift: multi-param leading chain not lifted" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // f = \x -> \y -> x
    // Both lambdas are leading — neither should be lifted.

    const x_id = testId("x", 1);
    const y_id = testId("y", 2);

    const x_var = try alloc.create(Expr);
    x_var.* = .{ .Var = x_id };

    const inner_lambda = try alloc.create(Expr);
    inner_lambda.* = .{ .Lam = .{
        .binder = y_id,
        .body = x_var,
        .span = testSpan(),
    } };

    const outer_lambda = try alloc.create(Expr);
    outer_lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = inner_lambda,
        .span = testSpan(),
    } };

    const f_bind = Bind{ .NonRec = .{
        .binder = testId("f", 10),
        .rhs = outer_lambda,
    } };

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{f_bind},
    };

    const lifted = try lambdaLift(alloc, program, null);

    // No expression lambdas → exactly 1 binding.
    try testing.expectEqual(@as(usize, 1), lifted.binds.len);
}

test "lambdaLift: anonymous lambda in app position (#501)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // it = (\x -> 1) 2
    // The lambda is NOT a leading lambda (it's inside an App).
    // It should be lifted.

    const x_id = testId("x", 1);
    const one_lit = try alloc.create(Expr);
    one_lit.* = .{ .Lit = .{ .val = .{ .Int = 1 }, .span = testSpan() } };

    const two_lit = try alloc.create(Expr);
    two_lit.* = .{ .Lit = .{ .val = .{ .Int = 2 }, .span = testSpan() } };

    // Lambda: \x -> 1
    const lambda = try alloc.create(Expr);
    lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = one_lit,
        .span = testSpan(),
    } };

    // App: (\x -> 1) 2
    const app = try alloc.create(Expr);
    app.* = .{ .App = .{
        .fn_expr = lambda,
        .arg = two_lit,
        .span = testSpan(),
    } };

    const it_bind = Bind{ .NonRec = .{
        .binder = testId("it", 10),
        .rhs = app,
    } };

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{it_bind},
    };

    const lifted = try lambdaLift(alloc, program, null);

    // Should have 2 bindings: the lifted lambda + the rewritten `it`.
    try testing.expectEqual(@as(usize, 2), lifted.binds.len);

    // The original binding (it) should have no expression-position lambdas.
    const it_binding = lifted.binds[1];
    switch (it_binding) {
        .NonRec => |pair| {
            try testing.expect(!containsExprLambdaInRhs(pair.rhs));
        },
        .Rec => unreachable,
    }
}

test "VarSet: basic operations" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var set = VarSet.init(alloc);
    defer set.deinit(alloc);

    try set.add(alloc, 1);
    try set.add(alloc, 2);
    try set.add(alloc, 3);

    try testing.expect(set.contains(1));
    try testing.expect(set.contains(2));
    try testing.expect(!set.contains(99));

    const slice = try set.toSlice(alloc);
    try testing.expectEqual(@as(usize, 3), slice.len);
}

test "VarSet: clone" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var set1 = VarSet.init(alloc);
    defer set1.deinit(alloc);

    try set1.add(alloc, 1);
    try set1.add(alloc, 2);

    var set2 = try set1.clone(alloc);
    defer set2.deinit(alloc);

    try testing.expect(set2.contains(1));
    try testing.expect(set2.contains(2));
    try testing.expect(!set2.contains(3));

    // Sets are independent
    try set2.add(alloc, 3);
    try testing.expect(!set1.contains(3));
}

test "lambdaLift: two-arg expression lambda does not propagate own param as free var (#659)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // g = (\x -> (\y -> x)) 5
    //
    // Both \x and \y are expression lambdas (inside App, not leading).
    // \y -> x should capture x as free var.
    // \x should have ZERO free vars — x is its own parameter.
    // Bug #659: the old code propagated x to \x's free vars.

    const x_id = testId("x", 1);
    const y_id = testId("y", 2);
    const five_lit = try alloc.create(Expr);
    five_lit.* = .{ .Lit = .{ .val = .{ .Int = 5 }, .span = testSpan() } };

    const x_var = try alloc.create(Expr);
    x_var.* = .{ .Var = x_id };

    // Inner lambda: \y -> x
    const inner_lambda = try alloc.create(Expr);
    inner_lambda.* = .{ .Lam = .{
        .binder = y_id,
        .body = x_var,
        .span = testSpan(),
    } };

    // Outer lambda: \x -> (\y -> x)
    const outer_lambda = try alloc.create(Expr);
    outer_lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = inner_lambda,
        .span = testSpan(),
    } };

    // Application: (\x -> (\y -> x)) 5
    // Makes \x an expression lambda (not leading — it's inside App).
    const app = try alloc.create(Expr);
    app.* = .{ .App = .{
        .fn_expr = outer_lambda,
        .arg = five_lit,
        .span = testSpan(),
    } };

    const g_bind = Bind{ .NonRec = .{
        .binder = testId("g", 10),
        .rhs = app,
    } };

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{g_bind},
    };

    const lifted = try lambdaLift(alloc, program, null);

    // Should have 3 bindings: lifted \y, lifted \x, rewritten g.
    try testing.expectEqual(@as(usize, 3), lifted.binds.len);

    // Also verify via direct lifter inspection.
    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();
    try lifter.top_level_vars.add(alloc, g_bind.NonRec.binder.name.unique.value);

    var leading_lams = LeadingLamSet{};
    defer leading_lams.deinit(alloc);
    // No leading lams — RHS is an App, not a Lam chain.

    var result_fvs = try lifter.collectFreeVarsOf(g_bind.NonRec.rhs, lifter.top_level_vars, &leading_lams);
    result_fvs.deinit(alloc);

    // Check each lifted lambda.
    var lifted_it = lifter.lambdas.iterator();
    while (lifted_it.next()) |entry| {
        const info = &entry.value_ptr.*;
        if (!info.needs_lifting) continue;

        if (info.params.len == 1 and info.params[0].name.unique.value == y_id.name.unique.value) {
            // \y -> x: should have x (unique=1) as free var.
            try testing.expectEqual(@as(usize, 1), info.free_vars.len);
            try testing.expectEqual(@as(u64, 1), info.free_vars[0]);
        } else if (info.params.len == 1 and info.params[0].name.unique.value == x_id.name.unique.value) {
            // \x -> (\y -> x): x is own param, so ZERO free vars.
            // This is the core assertion for #659.
            try testing.expectEqual(@as(usize, 0), info.free_vars.len);
        }
    }
}

test "LambdaLifter: initialization" {
    const alloc = testing.allocator;

    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();

    try testing.expectEqual(@as(u64, 0), lifter.lambda_counter);
    try testing.expectEqual(@as(usize, 0), lifter.lambdas.count());
    try testing.expectEqual(@as(usize, 0), lifter.top_level_vars.set.count());
}
