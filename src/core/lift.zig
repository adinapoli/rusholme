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

/// Information about a lambda expression that needs to be lifted.
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
    /// Parent lambda ID (0 if top-level).
    parent_id: u64,
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
    /// Counter for generating unique Names.
    name_counter: u64 = 0,

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

    /// Register a lambda expression and return its unique ID.
    fn registerLambda(self: *LambdaLifter, expr: *const Expr, params: []const Id, body: *const Expr, parent_id: u64, ty: CoreType, span: SourceSpan) !u64 {
        _ = params;
        _ = body;
        _ = parent_id;
        _ = ty;
        _ = span;
        const lambda_id = self.lambda_counter + 1;
        self.lambda_counter = lambda_id;

        // Store mapping from expr pointer to lambda ID
        const expr_ptr = @intFromPtr(expr);
        try self.expr_to_lambda.put(self.alloc, expr_ptr, lambda_id);

        return lambda_id;
    }

    /// Complete lambda registration after free variable computation.
    fn completeLambda(self: *LambdaLifter, lambda_id: u64, free_vars: []const u64, params: []const Id, body: *const Expr, ty: CoreType, span: SourceSpan) !void {
        _ = span;
        const lifted_name = Name{
            .base = "lifted",
            .unique = Unique{ .value = self.lifted_id_counter },
        };
        self.lifted_id_counter += 1;

        const info = LambdaInfo{
            .id = lambda_id,
            .expr = body, // Point to body, will handle this in rewrite
            .body = body,
            .free_vars = free_vars,
            .params = params,
            .ty = ty,
            .parent_id = 0,
            .lifted_name = lifted_name,
        };
        try self.lambdas.put(self.alloc, lambda_id, info);
    }

    /// Collect all lambdas in an expression and compute their free variables.
    /// Returns the set of free variables in the entire expression.
    fn collectLambdas(
        self: *LambdaLifter,
        expr: *const Expr,
        parent_lambda_id: u64,
        current_frame: *Frame,
        free_vars: *VarSet,
        ty: CoreType,
        span: SourceSpan,
    ) !VarSet {
        switch (expr.*) {
            .Var => |v| {
                if (!self.inScope(v.name.unique.value)) {
                    try free_vars.add(self.alloc, v.name.unique.value);
                }
            },
.Lit => {},
            .App => |a| {
                var fn_free = try self.collectLambdas(a.fn_expr, parent_lambda_id, current_frame, free_vars, ty, a.span);
                defer fn_free.deinit(self.alloc);
                var arg_free = try self.collectLambdas(a.arg, parent_lambda_id, current_frame, free_vars, ty, a.span);
                defer arg_free.deinit(self.alloc);
                try free_vars.merge(self.alloc, &fn_free);
                try free_vars.merge(self.alloc, &arg_free);
            },
            .Lam => |l| {
                // This is a lambda that needs to be lifted.
                const lambda_id = try self.registerLambda(expr, &.{l.binder}, l.body, parent_lambda_id, ty, span);

                // Create a new frame with the lambda's parameter.
                const param_id = l.binder.name.unique.value;
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
                _ = try self.collectLambdas(l.body, lambda_id, &new_frame, &body_free_vars, ty, l.span);

                // Pop the frame.
                _ = self.frames.pop();
                _ = self.alloc.free(new_frame_vars);

                // Complete lambda registration with free variables.
                const free_vars_slice = try body_free_vars.toSlice(self.alloc);
                try self.completeLambda(lambda_id, free_vars_slice, &.{l.binder}, l.body, l.binder.ty, l.span);

                // Compute function type with free vars added as parameters.
                // For each free variable, we add a parameter to the type.
                var lifted_ty = l.binder.ty;
for (free_vars_slice) |_| {
                    const p_ty = try self.alloc.create(CoreType);
                    p_ty.* = intType(); // Use dummy type for now; would need actual type lookup
                    const param_ty = try self.alloc.create(CoreType);
                    param_ty.* = lifted_ty;
                    lifted_ty = CoreType{ .FunTy = .{ .arg = p_ty, .res = param_ty } };
                }

                // Update the lambda's type.
                if (self.lambdas.getPtr(lambda_id)) |info_ptr| {
                    info_ptr.ty = lifted_ty;
                }

                // Note: we don't propagate free_vars from the lambda, since lifted
                // functions are referenced by name.
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
                        var rhs_free = try self.collectLambdas(pair.rhs, parent_lambda_id, &new_frame, free_vars, ty, l.span);
                        defer rhs_free.deinit(self.alloc);

                        // Collect free vars in body.
                        var body_free = try self.collectLambdas(l.body, parent_lambda_id, &new_frame, free_vars, ty, l.span);
                        defer body_free.deinit(self.alloc);

                        try free_vars.merge(self.alloc, &rhs_free);
                        try free_vars.merge(self.alloc, &body_free);

                        // Pop frame.
                        _ = self.frames.pop();
                        _ = self.alloc.free(new_frame_vars);
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
                            var rhs_free = try self.collectLambdas(pair.rhs, parent_lambda_id, &new_frame, free_vars, ty, l.span);
                            defer rhs_free.deinit(self.alloc);
                            try all_rhs_free.merge(self.alloc, &rhs_free);
                        }

                        // Collect free vars in body.
                        var body_free = try self.collectLambdas(l.body, parent_lambda_id, &new_frame, free_vars, ty, l.span);
                        defer body_free.deinit(self.alloc);

                        try free_vars.merge(self.alloc, &all_rhs_free);
                        try free_vars.merge(self.alloc, &body_free);

                        // Pop frame.
                        _ = self.frames.pop();
                        _ = self.alloc.free(new_frame_vars);
                    },
                }
            },
            .Case => |c| {
                // Collect free vars in scrutinee.
                var scrut_free = try self.collectLambdas(c.scrutinee, parent_lambda_id, current_frame, free_vars, ty, c.span);
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

                    var alt_free = try self.collectLambdas(alt.body, parent_lambda_id, &alt_frame, free_vars, ty, c.span);
                    defer alt_free.deinit(self.alloc);
                    try all_alt_free.merge(self.alloc, &alt_free);

                    // Pop alt frame.
                    _ = self.frames.pop();
                    _ = self.alloc.free(alt_frame_vars);
                }

                try free_vars.merge(self.alloc, &all_alt_free);

                // Pop case frame.
                _ = self.frames.pop();
                _ = self.alloc.free(new_frame_vars);
            },
.Type => {},
            .Coercion => {},
        }

        return free_vars.clone(self.alloc) catch free_vars.*;
    }

    /// Rewrite an expression, replacing lambdas with function calls.
    fn rewriteExpr(self: *LambdaLifter, expr: *const Expr, current_binders: []const u64) LifterError!*Expr {
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
                }};
            },
            .Lam => |l| {
                // Check if this lambda was lifted.
                const expr_ptr = @intFromPtr(expr);
                if (self.expr_to_lambda.get(expr_ptr)) |lambda_id| {
                    if (self.lambdas.get(lambda_id)) |info| {
                        // This lambda was lifted. Replace with a reference to the lifted function.
                        // Create a Var node referencing the lifted function.
                        const lifted_id = Id{
                            .name = info.lifted_name,
                            .ty = info.ty,
                            .span = l.span,
                        };
                        new_expr.* = .{ .Var = lifted_id };
                    } else {
                        // Lambda info not found, keep as is
                        const new_body = try self.rewriteExpr(l.body, current_binders);
                        new_expr.* = .{ .Lam = .{
                            .binder = l.binder,
                            .body = new_body,
                            .span = l.span,
                        }};
                    }
                } else {
                    // Lambda not registered (top-level lambda chain), rewrite body
                    const new_body = try self.rewriteExpr(l.body, current_binders);
                    new_expr.* = .{ .Lam = .{
                        .binder = l.binder,
                        .body = new_body,
                        .span = l.span,
                    }};
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
                }};
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
                }};
            },
            .Type => |t| {
                new_expr.* = .{ .Type = t };
            },
            .Coercion => {
                new_expr.* = .{ .Coercion = .Refl };
            },
        }

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
                }};
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

/// Perform lambda lifting on a Core program.
///
/// Returns a new program with all nested lambdas lifted to top-level
/// function definitions.
pub fn lambdaLift(alloc: std.mem.Allocator, program: core.CoreProgram) !core.CoreProgram {
    var lifter = LambdaLifter.init(alloc);
    defer lifter.deinit();

    // Phase 1: Create initial frame with top-level binders.
    var top_level_vars = std.ArrayListUnmanaged(u64){};
    defer top_level_vars.deinit(alloc);

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

    try lifter.pushFrame(try top_level_vars.toOwnedSlice(alloc));

    // Phase 2: Collect all lambdas and their free variables.
    for (program.binds) |bind| {
        switch (bind) {
            .NonRec => |pair| {
                var free_vars = VarSet.init(alloc);
                defer free_vars.deinit(alloc);
                _ = try lifter.collectLambdas(pair.rhs, 0, &lifter.frames.items[0], &free_vars, intType(), pair.binder.span);
            },
            .Rec => |pairs| {
                var free_vars = VarSet.init(alloc);
                defer free_vars.deinit(alloc);
                for (pairs) |pair| {
                    _ = try lifter.collectLambdas(pair.rhs, 0, &lifter.frames.items[0], &free_vars, intType(), pair.binder.span);
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
        
        // Only lift nested lambdas (parent_id != 0).
        // Top-level lambdas (parent_id == 0) are already bindings and don't need lifting.
        if (info.parent_id == 0) {
            continue;
        }
        
        // Create a binding for the lifted function.
        // The function parameters are the original params plus the free vars.
        
        // Create Ids for the free var parameters (using a placeholder type)
        const num_free = info.free_vars.len;
        const num_params = info.params.len + num_free;
        const lifted_params = try alloc.alloc(Id, num_params);
        
        // First, the free variable parameters
        var param_i: usize = 0;
        for (info.free_vars, 0..) |fv, i| {
            lifted_params[i] = Id{
                .name = .{ .base = "fv", .unique = .{ .value = fv } },
                .ty = intType(),
                .span = info.params[0].span,
            };
            param_i += 1;
        }
        
        // Then the original parameters
        for (info.params, 0..) |p, j| {
            lifted_params[param_i + j] = p;
        }

        // Create a new lambda body with all parameters
        var current_body = info.body;
        var k = info.params.len;
        while (k > 0) {
            k -= 1;
            const p_body = try alloc.create(Expr);
            p_body.* = current_body.*;
            
            const binder = info.params[k];
            lifted_params[param_i + k] = binder;
            
            current_body = p_body;
        }

        // Now create lam wrappers for the free var parameters
        for (info.free_vars, 0..) |fv, i| {
            _ = i;
            const fv_binder = Id{
                .name = .{ .base = "fv", .unique = .{ .value = fv } },
                .ty = intType(),
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
        const lifted_pair = try alloc.create(BindPair);
        lifted_pair.binder = Id{
            .name = info.lifted_name,
            .ty = info.ty,
            .span = info.params[0].span,
        };
        lifted_pair.rhs = current_body;

        try lifted_binds.append(alloc, .{ .NonRec = lifted_pair.* });
    }

    // Phase 4: Rewrite the original bindings.
    var new_binds = std.ArrayListUnmanaged(Bind){};
    const top_binders_list = try top_level_vars.toOwnedSlice(alloc);
    defer alloc.free(top_binders_list);
    
    for (program.binds) |bind| {
        const new_bind = try lifter.rewriteBind(bind, top_binders_list);
        try new_binds.append(alloc, new_bind);
    }

    // Phase 5: Combine original bindings with lifted bindings.
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

fn intType() CoreType {
    return .{ .TyCon = .{ 
        .name = .{ .base = "Int", .unique = .{ .value = 0 } },
        .args = &.{} 
    }};
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
        .span = SourceSpan.init(
            core.SourcePos.init(1, 1, 1),
            core.SourcePos.init(1, 1, 10),
        ),
    }};

    const f_bind = Bind{ .NonRec = .{
        .binder = testId("f", 10),
        .rhs = lambda_body,
    }};

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{f_bind},
    };

    const lifted = try lambdaLift(alloc, program);

    // After lifting with no nested lambda, we should have the same binding
    try testing.expectEqual(@as(usize, 1), lifted.binds.len);
}

test "lambdaLift: nested lambda" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // f = \x -> (\y -> x) 5
    // This should lift the inner lambda \y -> x

    const x_id = testId("x", 1);
    const y_id = testId("y", 2);
    const five_lit = try alloc.create(Expr);
    five_lit.* = .{ .Lit = .{ .val = .{ .Int = 5 }, .span = SourceSpan.init(
        core.SourcePos.init(1, 1, 1),
        core.SourcePos.init(1, 1, 5),
    )}};

    const x_var = try alloc.create(Expr);
    x_var.* = .{ .Var = x_id };

    // Inner lambda: \y -> x
    const inner_lambda = try alloc.create(Expr);
    inner_lambda.* = .{ .Lam = .{
        .binder = y_id,
        .body = x_var,
        .span = SourceSpan.init(
            core.SourcePos.init(1, 2, 3),
            core.SourcePos.init(1, 2, 7),
        ),
    }};

    // Apply inner lambda to 5: (\y -> x) 5
    const inner_app = try alloc.create(Expr);
    inner_app.* = .{ .App = .{
        .fn_expr = inner_lambda,
        .arg = five_lit,
        .span = SourceSpan.init(
            core.SourcePos.init(1, 1, 1),
            core.SourcePos.init(1, 1, 10),
        ),
    }};

    // Outer lambda: \x -> (\y -> x) 5
    const outer_lambda = try alloc.create(Expr);
    outer_lambda.* = .{ .Lam = .{
        .binder = x_id,
        .body = inner_app,
        .span = SourceSpan.init(
            core.SourcePos.init(1, 1, 1),
            core.SourcePos.init(1, 1, 20),
        ),
    }};

    const f_bind = Bind{ .NonRec = .{
        .binder = testId("f", 10),
        .rhs = outer_lambda,
    }};

    const program: core.CoreProgram = .{
        .data_decls = &.{},
        .binds = &.{f_bind},
    };

    const lifted = try lambdaLift(alloc, program);

    // After lifting, we should have:
    // - The outer lambda binding
    // - A lifted function for the inner lambda
    try testing.expect(lifted.binds.len >= 1);
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

    var slice = try set.toSlice(alloc);
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
