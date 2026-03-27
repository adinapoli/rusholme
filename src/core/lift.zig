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

// ── Expression Stack Frame ───────────────────────────────────────────────

/// Represents a scope level with binders and their IDs.
const Frame = struct {
    /// Variables bound in this frame.
    vars: []const u64,
    /// Lambda IDs defined in this frame.
    lambdas: []const u64,
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
    /// Stack of frames representing nested scopes.
    frames: std.ArrayListUnmanaged(Frame),
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
            .frames = .{},
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
        self.frames.deinit(self.alloc);
        self.rewrite_cache.deinit(self.alloc);
    }

    /// Push a new scope frame.
    fn pushFrame(self: *LambdaLifter, vars: []const u64) !void {
        try self.frames.append(self.alloc, .{
            .vars = vars,
            .lambdas = &.{},
        });
    }

    /// Pop the current scope frame.
    fn popFrame(self: *LambdaLifter) void {
        _ = self.frames.pop();
    }

    /// Check if a variable is in scope (not free) in the current context.
    fn inScope(self: *LambdaLifter, id: u64) bool {
        // Iterate frames from top to bottom
        var i = self.frames.items.len;
        while (i > 0) {
            i -= 1;
            const frame = self.frames.items[i];
            for (frame.vars) |var_id| {
                if (var_id == id) return true;
            }
        }
        return false;
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
    /// Returns the set of free variables in the entire expression.
    ///
    /// `leading_lams` contains the pointer addresses of Lam nodes that form
    /// leading parameter chains on top-level binding RHS. Lambdas in this set
    /// are NOT lifted (translateDef peels them).
    fn collectLambdas(
        self: *LambdaLifter,
        expr: *const Expr,
        leading_lams: *const LeadingLamSet,
        current_frame: *Frame,
        free_vars: *VarSet,
        ty: CoreType,
    ) !VarSet {
        switch (expr.*) {
            .Var => |v| {
                // Data constructors are globally available and must never be
                // captured as free variables.  In Haskell, constructor names
                // start with an uppercase letter or ':'.
                if (!isDataCon(v.name.base) and !self.inScope(v.name.unique.value)) {
                    try free_vars.add(self.alloc, v.name.unique.value);
                }
            },
            .Lit => {},
            .App => |a| {
                var fn_free = try self.collectLambdas(a.fn_expr, leading_lams, current_frame, free_vars, ty);
                defer fn_free.deinit(self.alloc);
                var arg_free = try self.collectLambdas(a.arg, leading_lams, current_frame, free_vars, ty);
                defer arg_free.deinit(self.alloc);
                try free_vars.merge(self.alloc, &fn_free);
                try free_vars.merge(self.alloc, &arg_free);
            },
            .Lam => |l| {
                const is_leading = leading_lams.contains(@intFromPtr(expr));
                const needs_lifting = !is_leading;

                const lambda_id = try self.registerLambda(expr);

                const param_id = l.binder.name.unique.value;

                if (needs_lifting) {
                    // Expression lambda: will be lifted to top level.
                    //
                    // For free-variable computation, only the top-level frame
                    // (index 0) and this lambda's own parameter should be
                    // visible. Enclosing lambda parameters are NOT in scope
                    // for the lifted function — they become free variables
                    // that are passed as extra arguments at the call site.
                    //
                    // We use a temporary frame list so that `append` inside
                    // the recursive call cannot invalidate the saved frames.
                    const saved_frames = self.frames;
                    self.frames = .{};
                    try self.frames.append(self.alloc, saved_frames.items[0]); // top-level frame

                    var new_frame_vars = try self.alloc.alloc(u64, 1);
                    new_frame_vars[0] = param_id;

                    var new_frame = Frame{
                        .vars = new_frame_vars,
                        .lambdas = &.{},
                    };
                    try self.frames.append(self.alloc, new_frame);

                    // Collect free variables in the lambda body.
                    var body_free_vars = VarSet.init(self.alloc);
                    defer body_free_vars.deinit(self.alloc);
                    _ = try self.collectLambdas(l.body, leading_lams, &new_frame, &body_free_vars, ty);

                    // Discard temporary frame list and restore the saved one.
                    self.alloc.free(new_frame_vars);
                    self.frames.deinit(self.alloc);
                    self.frames = saved_frames;

                    // Complete lambda registration with free variables.
                    const free_vars_slice = try body_free_vars.toSlice(self.alloc);
                    // Heap-allocate the params slice so it outlives this scope.
                    // Using a temporary `&.{l.binder}` would create a dangling
                    // reference — all lifted lambdas would share the same
                    // (overwritten) stack slot.
                    const param_slice = try self.alloc.alloc(Id, 1);
                    param_slice[0] = l.binder;
                    try self.completeLambda(lambda_id, free_vars_slice, param_slice, l.body, l.binder.ty, needs_lifting);

                    // Compute function type with free vars added as parameters.
                    var lifted_ty = l.binder.ty;
                    for (free_vars_slice) |_| {
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

                    // Propagate free variables of the lifted lambda to the
                    // enclosing scope so that the caller knows these variables
                    // are needed.
                    for (free_vars_slice) |fv_id| {
                        try free_vars.add(self.alloc, fv_id);
                    }
                } else {
                    // Parameter lambda: part of the leading chain on a
                    // top-level binding RHS. Keep in place — translateDef
                    // will peel it as a function parameter.
                    //
                    // Scope handling: add the parameter to the current frame
                    // so that the body sees it as in-scope (not free).
                    var new_frame_vars = try self.alloc.alloc(u64, current_frame.vars.len + 1);
                    @memcpy(new_frame_vars[0..current_frame.vars.len], current_frame.vars);
                    new_frame_vars[current_frame.vars.len] = param_id;

                    var new_frame = Frame{
                        .vars = new_frame_vars,
                        .lambdas = &.{},
                    };
                    try self.frames.append(self.alloc, new_frame);

                    // Collect free variables in the lambda body.
                    var body_free_vars = VarSet.init(self.alloc);
                    defer body_free_vars.deinit(self.alloc);
                    _ = try self.collectLambdas(l.body, leading_lams, &new_frame, &body_free_vars, ty);

                    // Pop the frame.
                    _ = self.frames.pop();
                    self.alloc.free(new_frame_vars);

                    // Complete lambda registration (not lifted, but still tracked).
                    const free_vars_slice = try body_free_vars.toSlice(self.alloc);
                    try self.completeLambda(lambda_id, free_vars_slice, &.{l.binder}, l.body, l.binder.ty, needs_lifting);
                }
            },
            .Let => |l| {
                switch (l.bind) {
                    .NonRec => |pair| {
                        // Create new frame with binder.
                        var new_frame_vars = try self.alloc.alloc(u64, current_frame.vars.len + 1);
                        @memcpy(new_frame_vars[0..current_frame.vars.len], current_frame.vars);
                        new_frame_vars[current_frame.vars.len] = pair.binder.name.unique.value;

                        var new_frame = Frame{
                            .vars = new_frame_vars,
                            .lambdas = &.{},
                        };
                        try self.frames.append(self.alloc, new_frame);

                        // Collect free vars in RHS.
                        var rhs_free = try self.collectLambdas(pair.rhs, leading_lams, &new_frame, free_vars, ty);
                        defer rhs_free.deinit(self.alloc);

                        // Collect free vars in body.
                        var body_free = try self.collectLambdas(l.body, leading_lams, &new_frame, free_vars, ty);
                        defer body_free.deinit(self.alloc);

                        try free_vars.merge(self.alloc, &rhs_free);
                        try free_vars.merge(self.alloc, &body_free);

                        // Pop frame.
                        _ = self.frames.pop();
                        self.alloc.free(new_frame_vars);
                    },
                    .Rec => |pairs| {
                        // Create new frame with all binders.
                        const old_len = current_frame.vars.len;
                        var new_frame_vars = try self.alloc.alloc(u64, old_len + pairs.len);
                        @memcpy(new_frame_vars[0..old_len], current_frame.vars);
                        for (pairs, 0..) |pair, i| {
                            new_frame_vars[old_len + i] = pair.binder.name.unique.value;
                        }

                        var new_frame = Frame{
                            .vars = new_frame_vars,
                            .lambdas = &.{},
                        };
                        try self.frames.append(self.alloc, new_frame);

                        var all_rhs_free = VarSet.init(self.alloc);
                        defer all_rhs_free.deinit(self.alloc);

                        // Collect free vars in all RHS.
                        for (pairs) |pair| {
                            var rhs_free = try self.collectLambdas(pair.rhs, leading_lams, &new_frame, free_vars, ty);
                            defer rhs_free.deinit(self.alloc);
                            try all_rhs_free.merge(self.alloc, &rhs_free);
                        }

                        // Collect free vars in body.
                        var body_free = try self.collectLambdas(l.body, leading_lams, &new_frame, free_vars, ty);
                        defer body_free.deinit(self.alloc);

                        try free_vars.merge(self.alloc, &all_rhs_free);
                        try free_vars.merge(self.alloc, &body_free);

                        // Pop frame.
                        _ = self.frames.pop();
                        self.alloc.free(new_frame_vars);
                    },
                }
            },
            .Case => |c| {
                // Collect free vars in scrutinee.
                var scrut_free = try self.collectLambdas(c.scrutinee, leading_lams, current_frame, free_vars, ty);
                defer scrut_free.deinit(self.alloc);
                try free_vars.merge(self.alloc, &scrut_free);

                // Create new frame with case binder.
                var new_frame_vars = try self.alloc.alloc(u64, current_frame.vars.len + 1);
                @memcpy(new_frame_vars[0..current_frame.vars.len], current_frame.vars);
                new_frame_vars[current_frame.vars.len] = c.binder.name.unique.value;

                var new_frame = Frame{
                    .vars = new_frame_vars,
                    .lambdas = &.{},
                };
                try self.frames.append(self.alloc, new_frame);

                var all_alt_free = VarSet.init(self.alloc);
                defer all_alt_free.deinit(self.alloc);

                for (c.alts) |alt| {
                    // Create frame with alt binders.
                    var alt_frame_vars = try self.alloc.alloc(u64, new_frame.vars.len + alt.binders.len);
                    @memcpy(alt_frame_vars[0..new_frame.vars.len], new_frame.vars);
                    for (alt.binders, 0..) |binder, i| {
                        alt_frame_vars[new_frame.vars.len + i] = binder.name.unique.value;
                    }

                    var alt_frame = Frame{
                        .vars = alt_frame_vars,
                        .lambdas = &.{},
                    };
                    try self.frames.append(self.alloc, alt_frame);

                    var alt_free = try self.collectLambdas(alt.body, leading_lams, &alt_frame, free_vars, ty);
                    defer alt_free.deinit(self.alloc);
                    try all_alt_free.merge(self.alloc, &alt_free);

                    // Pop alt frame.
                    _ = self.frames.pop();
                    self.alloc.free(alt_frame_vars);
                }

                try free_vars.merge(self.alloc, &all_alt_free);

                // Pop case frame.
                _ = self.frames.pop();
                self.alloc.free(new_frame_vars);
            },
            .Type => {},
            .Coercion => {},
        }

        return free_vars.clone(self.alloc) catch free_vars.*;
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

    // Phase 1: Create initial frame with top-level binders + externals.
    var top_level_vars = std.ArrayListUnmanaged(u64){};
    defer top_level_vars.deinit(alloc);

    // Include externally-visible names (Prelude, imports) so that the
    // free-variable analysis does not capture them as closures.
    if (external_scope) |ext| {
        try top_level_vars.appendSlice(alloc, ext);
    }

    for (program.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                try top_level_vars.append(alloc, pair.binder.name.unique.value);
            },
            .Rec => |pairs| {
                for (pairs) |pair| {
                    try top_level_vars.append(alloc, pair.binder.name.unique.value);
                }
            },
        }
    }

    const top_level_slice = try top_level_vars.toOwnedSlice(alloc);
    try lifter.pushFrame(top_level_slice);

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
                var free_vars = VarSet.init(alloc);
                defer free_vars.deinit(alloc);
                _ = try lifter.collectLambdas(pair.rhs, &leading_lams, &lifter.frames.items[0], &free_vars, intType());
            },
            .Rec => |pairs| {
                var free_vars = VarSet.init(alloc);
                defer free_vars.deinit(alloc);
                for (pairs) |pair| {
                    leading_lams.clearRetainingCapacity();
                    try LambdaLifter.collectLeadingLamPtrs(pair.rhs, &leading_lams, alloc);
                    _ = try lifter.collectLambdas(pair.rhs, &leading_lams, &lifter.frames.items[0], &free_vars, intType());
                }
            },
        }
    }

    // Pop the top-level frame.
    lifter.popFrame();

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

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{},
    };
    _ = program;

    // Use a separate lifter to inspect the lambda info directly.
    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();

    try lifter.pushFrame(&.{f_bind.NonRec.binder.name.unique.value});

    var leading_lams = LeadingLamSet{};
    defer leading_lams.deinit(alloc);
    try LambdaLifter.collectLeadingLamPtrs(f_bind.NonRec.rhs, &leading_lams, alloc);

    var free_vars = VarSet.init(alloc);
    defer free_vars.deinit(alloc);
    _ = try lifter.collectLambdas(f_bind.NonRec.rhs, &leading_lams, &lifter.frames.items[0], &free_vars, intType());

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

test "LambdaLifter: initialization" {
    const alloc = testing.allocator;

    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();

    try testing.expectEqual(@as(u64, 0), lifter.lambda_counter);
    try testing.expectEqual(@as(usize, 0), lifter.lambdas.count());
}

test "LambdaLifter: frame management" {
    const alloc = testing.allocator;

    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();

    const vars = [_]u64{ 1, 2, 3 };
    try lifter.pushFrame(&vars);

    try testing.expect(lifter.inScope(1));
    try testing.expect(lifter.inScope(2));
    try testing.expect(lifter.inScope(3));
    try testing.expect(!lifter.inScope(99));

    lifter.popFrame();

    try testing.expect(!lifter.inScope(1));
}
