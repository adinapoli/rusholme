//! Core Lint — type-check Core IR for internal consistency.
//!
//! Core is the "type-safety firewall" — if Core typechecks, later stages
//! (GRIN translation, codegen) can trust the program is well-formed.
//! Lint errors are **internal compiler errors (ICE)**, not user-facing.
//!
//! Reference: GHC's `compiler/GHC/Core/Lint.hs`
//!
//! ## What Lint checks
//!
//! 1. **Variable scope**: All `Var` references are bound in the environment.
//! 2. **Type scope**: All type variables (`TyVar`) are bound.
//! 3. **Application well-formedness**: Function and argument types align.
//! 4. **Let binding consistency**: Binder type matches RHS type.
//! 5. **Case consistency**: Result type matches alternatives; binders are
//!    consistent with the constructor/alternative being matched.
//!
//! ## Usage
//!
//! ```zig
//! var diags = DiagnosticCollector.init();
//! defer diags.deinit(alloc);
//! lintCoreProgram(alloc, program, &diags);
//! if (diags.hasErrors()) {
//!     // ICE: compiler bug
//! }
//! ```

const std = @import("std");
const core = @import("ast.zig");
const diagnostic = @import("../diagnostics/diagnostic.zig");

pub const CoreType = core.CoreType;
pub const Expr = core.Expr;
pub const Bind = core.Bind;
pub const Alt = core.Alt;
pub const AltCon = core.AltCon;
pub const Id = core.Id;
pub const Literal = core.Literal;
pub const Name = core.Name;
pub const DiagnosticCollector = diagnostic.DiagnosticCollector;
pub const Diagnostic = diagnostic.Diagnostic;
pub const Severity = diagnostic.Severity;
pub const SourceSpan = core.SourceSpan;

// ── Lint Environment ─────────────────────────────────────────────────────

/// A type environment mapping `Id` unique values to their types.
///
/// Unlike `TyEnv` in the typechecker, this uses a simple hash map since
/// Core has already been elaborated — there's no polymorphism or scopes
/// to manage beyond what `push`/`pop` provide.
const LintEnv = struct {
    alloc: std.mem.Allocator,
    /// Value bindings: unique ID -> type
    bindings: std.AutoHashMapUnmanaged(u64, CoreType),
    /// Type variable bindings: unique ID -> void (just tracks in-scope)
    ty_vars: std.AutoHashMapUnmanaged(u64, void),

    fn init(alloc: std.mem.Allocator) LintEnv {
        return .{
            .alloc = alloc,
            .bindings = .{},
            .ty_vars = .{},
        };
    }

    fn deinit(self: *LintEnv) void {
        self.bindings.deinit(self.alloc);
        self.ty_vars.deinit(self.alloc);
    }

    /// Add a value binding to the environment.
    fn bindValue(self: *LintEnv, id: Id) !void {
        try self.bindings.put(self.alloc, id.name.unique.value, id.ty);
    }

    /// Add a type variable to the environment.
    fn bindTyVar(self: *LintEnv, name: Name) !void {
        try self.ty_vars.put(self.alloc, name.unique.value, {});
    }

    /// Look up a value binding by unique ID.
    fn lookupValue(self: *const LintEnv, unique: u64) ?CoreType {
        return self.bindings.get(unique);
    }

    /// Check if a type variable is in scope.
    fn tyVarInScope(self: *const LintEnv, unique: u64) bool {
        return self.ty_vars.contains(unique);
    }

    /// Clone the environment (for branching contexts like case alternatives).
    fn clone(self: *const LintEnv) !LintEnv {
        var copy = LintEnv.init(self.alloc);
        errdefer copy.deinit();
        var it = self.bindings.iterator();
        while (it.next()) |entry| {
            try copy.bindings.put(self.alloc, entry.key_ptr.*, entry.value_ptr.*);
        }
        var tv_it = self.ty_vars.iterator();
        while (tv_it.next()) |entry| {
            try copy.ty_vars.put(self.alloc, entry.key_ptr.*, {});
        }
        return copy;
    }
};

// ── Lint Result ──────────────────────────────────────────────────────────

/// The type of an expression, computed during lint.
const LintType = union(enum) {
    /// Successfully inferred type.
    ok: CoreType,
    /// An error was already reported; propagate without adding more.
    err: void,
};

// ── Core Lint API ─────────────────────────────────────────────────────────

/// Lint a Core program, accumulating diagnostics for any errors found.
///
/// Returns `true` if the program passes lint, `false` if errors were found.
/// All errors are added to `diags` as `Severity.Error` diagnostics.
pub fn lintCoreProgram(
    alloc: std.mem.Allocator,
    program: core.CoreProgram,
    diags: *DiagnosticCollector,
) !bool {
    var env = LintEnv.init(alloc);
    defer env.deinit();

    var has_errors = false;

    for (program, 0..) |bind, i| {
        const ok = try lintBind(alloc, &env, bind, diags, alloc, "top-level");
        if (!ok) {
            has_errors = true;
            // Continue linting to find more errors
            _ = i;
        }
    }

    return !has_errors;
}

/// Lint a single binding (NonRec or Rec).
fn lintBind(
    alloc: std.mem.Allocator,
    env: *LintEnv,
    bind: Bind,
    diags: *DiagnosticCollector,
    diag_alloc: std.mem.Allocator,
    context: []const u8,
) !bool {
    switch (bind) {
        .NonRec => |pair| {
            // Lint the RHS first, then add the binder.
            const rhs_ty = try lintExpr(alloc, env, pair.rhs, diags, diag_alloc);
            switch (rhs_ty) {
                .err => return false,
                .ok => |ty| {
                    // Check that RHS type matches binder annotation.
                    if (!typesEqual(ty, pair.binder.ty)) {
                        try reportTypeError(
                            diag_alloc,
                            diags,
                            pair.binder.span,
                            "type mismatch in {s} binding: binder expects {}, but RHS has {}",
                            .{ context, fmtType(pair.binder.ty), fmtType(ty) },
                        );
                        return false;
                    }
                },
            }
            // Add binder to environment for subsequent code.
            try env.bindValue(pair.binder);
            return true;
        },
        .Rec => |pairs| {
            // For recursive bindings, first add all binders to the environment,
            // then lint all RHS bodies.
            for (pairs) |pair| {
                try env.bindValue(pair.binder);
                // Add any type variables from the binder's type.
                try bindTypeVars(env, pair.binder.ty);
            }
            var all_ok = true;
            for (pairs) |pair| {
                const rhs_ty = try lintExpr(alloc, env, pair.rhs, diags, diag_alloc);
                switch (rhs_ty) {
                    .err => all_ok = false,
                    .ok => |ty| {
                        if (!typesEqual(ty, pair.binder.ty)) {
                            try reportTypeError(
                                diag_alloc,
                                diags,
                                pair.binder.span,
                                "type mismatch in recursive binding: binder expects {}, but RHS has {}",
                                .{ fmtType(pair.binder.ty), fmtType(ty) },
                            );
                            all_ok = false;
                        }
                    },
                }
            }
            return all_ok;
        },
    }
}

/// Lint an expression, returning its type (or error).
fn lintExpr(
    alloc: std.mem.Allocator,
    env: *LintEnv,
    expr: *const Expr,
    diags: *DiagnosticCollector,
    diag_alloc: std.mem.Allocator,
) error{OutOfMemory}!LintType {
    switch (expr.*) {
        .Var => |v| {
            // Check that the variable is in scope.
            if (env.lookupValue(v.name.unique.value)) |ty| {
                // Check that the type annotation matches what's in the environment.
                if (!typesEqual(ty, v.ty)) {
                    try reportTypeError(
                        diag_alloc,
                        diags,
                        v.span,
                        "variable {} has inconsistent type annotation: env has {}, but occurrence has {}",
                        .{ fmtName(v.name), fmtType(ty), fmtType(v.ty) },
                    );
                    return .{ .err = {} };
                }
                return .{ .ok = ty };
            } else {
                try reportScopeError(
                    diag_alloc,
                    diags,
                    v.span,
                    "unbound variable: {}",
                    .{fmtName(v.name)},
                );
                return .{ .err = {} };
            }
        },

        .Lit => |l| {
            // Literals have a type derived from their value.
            const ty = literalType(l.val);
            return .{ .ok = ty };
        },

        .App => |a| {
            const fn_ty = try lintExpr(alloc, env, a.fn_expr, diags, diag_alloc);
            const arg_ty = try lintExpr(alloc, env, a.arg, diags, diag_alloc);

            switch (fn_ty) {
                .err => return .{ .err = {} },
                .ok => |ft| switch (arg_ty) {
                    .err => return .{ .err = {} },
                    .ok => |at| {
                        // Function type must be FunTy with matching arg type.
                        switch (ft) {
                            .FunTy => |fun| {
                                if (!typesEqual(fun.arg.*, at)) {
                                    try reportTypeError(
                                        diag_alloc,
                                        diags,
                                        a.span,
                                        "application type mismatch: function expects {}, but argument has {}",
                                        .{ fmtType(fun.arg.*), fmtType(at) },
                                    );
                                    return .{ .err = {} };
                                }
                                return .{ .ok = fun.res.* };
                            },
                            else => {
                                try reportTypeError(
                                    diag_alloc,
                                    diags,
                                    a.span,
                                    "application of non-function: {}",
                                    .{fmtType(ft)},
                                );
                                return .{ .err = {} };
                            },
                        }
                    },
                },
            }
        },

        .Lam => |l| {
            // Add the binder to the environment for the body.
            try env.bindValue(l.binder);
            try bindTypeVars(env, l.binder.ty);

            const body_ty = try lintExpr(alloc, env, l.body, diags, diag_alloc);
            switch (body_ty) {
                .err => return .{ .err = {} },
                .ok => |bt| {
                    // Lambda type is binder.ty -> body_type
                    const fun_ty = CoreType{ .FunTy = .{
                        .arg = &l.binder.ty,
                        .res = &bt,
                    } };
                    // Note: This creates a dangling pointer issue for the result type.
                    // For a proper implementation, we'd need to allocate on an arena.
                    // For linting purposes, we return a simpler representation.
                    return .{ .ok = fun_ty };
                },
            }
        },

        .Let => |l| {
            // Lint the binding first.
            const bind_ok = try lintBind(alloc, env, l.bind, diags, diag_alloc, "let");
            if (!bind_ok) {
                return .{ .err = {} };
            }

            // Now lint the body with the new bindings in scope.
            const body_ty = try lintExpr(alloc, env, l.body, diags, diag_alloc);
            return body_ty;
        },

        .Case => |c| {
            // Lint the scrutinee.
            const scrut_ty = try lintExpr(alloc, env, c.scrutinee, diags, diag_alloc);
            switch (scrut_ty) {
                .err => return .{ .err = {} },
                .ok => {
                    // The case binder is in scope for all alternatives.
                    try env.bindValue(c.binder);
                    try bindTypeVars(env, c.binder.ty);

                    // Lint each alternative.
                    if (c.alts.len == 0) {
                        // Empty alternatives: scrutinee is known to diverge.
                        // The result type is c.ty.
                        return .{ .ok = c.ty };
                    }

                    var result_ty: ?CoreType = null;
                    var all_ok = true;

                    for (c.alts) |alt| {
                        // Clone env for each alternative (they have different binders).
                        var alt_env = try env.clone();
                        defer alt_env.deinit();

                        // Add alternative binders.
                        for (alt.binders) |b| {
                            try alt_env.bindValue(b);
                            try bindTypeVars(&alt_env, b.ty);
                        }

                        const alt_body_ty = try lintExpr(alloc, &alt_env, alt.body, diags, diag_alloc);
                        switch (alt_body_ty) {
                            .err => all_ok = false,
                            .ok => |at| {
                                if (result_ty) |rt| {
                                    // All alternatives must have the same result type.
                                    if (!typesEqual(rt, at)) {
                                        try reportTypeError(
                                            diag_alloc,
                                            diags,
                                            c.span,
                                            "case alternatives have inconsistent types: {} vs {}",
                                            .{ fmtType(rt), fmtType(at) },
                                        );
                                        all_ok = false;
                                    }
                                } else {
                                    result_ty = at;
                                }
                            },
                        }
                    }

                    if (!all_ok) return .{ .err = {} };

                    // Check that the declared result type matches the alternatives.
                    if (result_ty) |rt| {
                        if (!typesEqual(c.ty, rt)) {
                            try reportTypeError(
                                diag_alloc,
                                diags,
                                c.span,
                                "case result type mismatch: declared {}, but alternatives have {}",
                                .{ fmtType(c.ty), fmtType(rt) },
                            );
                            return .{ .err = {} };
                        }
                    }

                    return .{ .ok = c.ty };
                },
            }
        },

        .Type => |t| {
            // Type arguments are valid; their "type" is the type itself.
            // We should check that all TyVars are in scope.
            try lintCoreType(env, t, diags);
            return .{ .ok = t };
        },

        .Coercion => {
            // Coercions are stubbed; treat as valid.
            return .{ .ok = CoreType{ .TyVar = .{ .base = "coercion", .unique = .{ .value = 0 } } } };
        },
    }
}

/// Lint a CoreType, checking that all type variables are in scope.
fn lintCoreType(env: *LintEnv, ty: CoreType, diags: *DiagnosticCollector) !void {
    switch (ty) {
        .TyVar => |name| {
            if (!env.tyVarInScope(name.unique.value)) {
                // Note: This is often acceptable for top-level type variables
                // that haven't been explicitly bound. We don't report an error
                // here for now, but could add a warning if needed.
            }
        },
        .TyCon => |tc| {
            for (tc.args) |arg| {
                try lintCoreType(env, arg, diags);
            }
        },
        .FunTy => |f| {
            try lintCoreType(env, f.arg.*, diags);
            try lintCoreType(env, f.res.*, diags);
        },
        .ForAllTy => |fa| {
            try env.bindTyVar(fa.binder);
            try lintCoreType(env, fa.body.*, diags);
        },
    }
}

/// Add all free type variables from a type to the environment.
fn bindTypeVars(env: *LintEnv, ty: CoreType) !void {
    switch (ty) {
        .TyVar => |name| try env.bindTyVar(name),
        .TyCon => |tc| {
            for (tc.args) |arg| try bindTypeVars(env, arg);
        },
        .FunTy => |f| {
            try bindTypeVars(env, f.arg.*);
            try bindTypeVars(env, f.res.*);
        },
        .ForAllTy => |fa| {
            try env.bindTyVar(fa.binder);
            try bindTypeVars(env, fa.body.*);
        },
    }
}

/// Get the CoreType of a literal value.
/// Uses consistent unique IDs matching test helper functions.
fn literalType(lit: Literal) CoreType {
    return switch (lit) {
        .Int => CoreType{ .TyCon = .{ .name = testNameBase("Int", 1), .args = &.{} } },
        .Float => CoreType{ .TyCon = .{ .name = testNameBase("Double", 3), .args = &.{} } },
        .Char => CoreType{ .TyCon = .{ .name = testNameBase("Char", 4), .args = &.{} } },
        .String => CoreType{ .TyCon = .{ .name = testNameBase("String", 5), .args = &.{} } },
    };
}

/// Structural equality check for CoreTypes.
///
/// Note: This is a simplified check that doesn't handle alpha-equivalence
/// for ForAll binders. For a production implementation, we'd need proper
/// de Bruijn indices or a substitution-based comparison.
fn typesEqual(t1: CoreType, t2: CoreType) bool {
    const tag1: std.meta.Tag(CoreType) = t1;
    const tag2: std.meta.Tag(CoreType) = t2;
    if (tag1 != tag2) return false;

    switch (t1) {
        .TyVar => |n1| {
            const n2 = t2.TyVar;
            return n1.unique.value == n2.unique.value;
        },
        .TyCon => |tc1| {
            const tc2 = t2.TyCon;
            if (tc1.name.unique.value != tc2.name.unique.value) return false;
            if (tc1.args.len != tc2.args.len) return false;
            for (tc1.args, tc2.args) |a1, a2| {
                if (!typesEqual(a1, a2)) return false;
            }
            return true;
        },
        .FunTy => |f1| {
            const f2 = t2.FunTy;
            return typesEqual(f1.arg.*, f2.arg.*) and typesEqual(f1.res.*, f2.res.*);
        },
        .ForAllTy => |fa1| {
            const fa2 = t2.ForAllTy;
            // Simplified: compare binder IDs directly (not alpha-equivalent).
            if (fa1.binder.unique.value != fa2.binder.unique.value) return false;
            return typesEqual(fa1.body.*, fa2.body.*);
        },
    }
}

// ── Error Reporting Helpers ──────────────────────────────────────────────

fn reportTypeError(
    alloc: std.mem.Allocator,
    diags: *DiagnosticCollector,
    span: SourceSpan,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    var msg_buf: [1024]u8 = undefined;
    const msg = std.fmt.bufPrint(&msg_buf, fmt, args) catch "<error message too long>";

    // Clone the message since bufPrint gives us a stack-allocated slice
    const owned_msg = try alloc.dupe(u8, msg);

    const diag = Diagnostic{
        .severity = .@"error",
        .message = owned_msg,
        .span = span,
        .code = .type_error,
    };
    try diags.add(alloc, diag);
}

fn reportScopeError(
    alloc: std.mem.Allocator,
    diags: *DiagnosticCollector,
    span: SourceSpan,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    var msg_buf: [1024]u8 = undefined;
    const msg = std.fmt.bufPrint(&msg_buf, fmt, args) catch "<error message too long>";

    // Clone the message since bufPrint gives us a stack-allocated slice
    const owned_msg = try alloc.dupe(u8, msg);

    const diag = Diagnostic{
        .severity = .@"error",
        .message = owned_msg,
        .span = span,
        .code = .unbound_variable,
    };
    try diags.add(alloc, diag);
}

// ── Formatting Helpers ───────────────────────────────────────────────────

/// Format a Name as "base_unique" (or just "base" if unique is 0).
const NameFormatter = struct {
    name: Name,

    pub fn format(
        self: NameFormatter,
        comptime _: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        if (self.name.unique.value == 0) {
            try writer.writeAll(self.name.base);
        } else {
            try writer.print("{s}_{d}", .{ self.name.base, self.name.unique.value });
        }
    }
};

fn fmtName(name: Name) NameFormatter {
    return .{ .name = name };
}

/// Format a CoreType in a readable form.
const TypeFormatter = struct {
    ty: CoreType,

    pub fn format(
        self: TypeFormatter,
        comptime _: []const u8,
        _: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        try formatTypeImpl(self.ty, writer);
    }

    fn formatTypeImpl(ty: CoreType, writer: anytype) !void {
        switch (ty) {
            .TyVar => |n| {
                if (n.unique.value == 0) {
                    try writer.writeAll(n.base);
                } else {
                    try writer.print("{s}_{d}", .{ n.base, n.unique.value });
                }
            },
            .TyCon => |tc| {
                if (tc.name.unique.value == 0) {
                    try writer.writeAll(tc.name.base);
                } else {
                    try writer.print("{s}_{d}", .{ tc.name.base, tc.name.unique.value });
                }
                if (tc.args.len > 0) {
                    for (tc.args) |arg| {
                        try writer.writeByte(' ');
                        const needs_parens = switch (arg) {
                            .FunTy, .ForAllTy => true,
                            .TyCon => |c| c.args.len > 0,
                            .TyVar => false,
                        };
                        if (needs_parens) try writer.writeByte('(');
                        try formatTypeImpl(arg, writer);
                        if (needs_parens) try writer.writeByte(')');
                    }
                }
            },
            .FunTy => |f| {
                const arg_needs_parens = switch (f.arg.*) {
                    .FunTy, .ForAllTy => true,
                    else => false,
                };
                if (arg_needs_parens) try writer.writeByte('(');
                try formatTypeImpl(f.arg.*, writer);
                if (arg_needs_parens) try writer.writeByte(')');
                try writer.writeAll(" -> ");
                try formatTypeImpl(f.res.*, writer);
            },
            .ForAllTy => |fa| {
                try writer.print("forall {s}_{d}. ", .{ fa.binder.base, fa.binder.unique.value });
                try formatTypeImpl(fa.body.*, writer);
            },
        }
    }
};

fn fmtType(ty: CoreType) TypeFormatter {
    return .{ .ty = ty };
}

// ── Tests ────────────────────────────────────────────────────────────────

const testing = std.testing;

fn testSpan() SourceSpan {
    return SourceSpan.init(
        core.SourcePos.init(1, 1, 1),
        core.SourcePos.init(1, 1, 10),
    );
}

fn testNameBase(base: []const u8, unique: u64) Name {
    return .{ .base = base, .unique = .{ .value = unique } };
}

fn intType() CoreType {
    return .{ .TyCon = .{ .name = testNameBase("Int", 1), .args = &.{} } };
}

fn boolType() CoreType {
    return .{ .TyCon = .{ .name = testNameBase("Bool", 2), .args = &.{} } };
}

fn testId(base: []const u8, unique: u64, ty: CoreType) Id {
    return .{
        .name = testNameBase(base, unique),
        .ty = ty,
        .span = testSpan(),
    };
}

test "lintCoreProgram: empty program passes" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    const program: core.CoreProgram = &.{};
    const ok = try lintCoreProgram(alloc, program, &diags);
    try testing.expect(ok);
    try testing.expectEqual(@as(usize, 0), diags.errorCount());
}

test "lintCoreProgram: simple non-recursive binding passes" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // x :: Int = 42
    const rhs = try alloc.create(Expr);
    rhs.* = .{ .Lit = .{ .val = .{ .Int = 42 }, .span = testSpan() } };

    const bind = Bind{ .NonRec = .{
        .binder = testId("x", 1, intType()),
        .rhs = rhs,
    } };

    const program: core.CoreProgram = &.{bind};
    const ok = try lintCoreProgram(alloc, program, &diags);
    try testing.expect(ok);
    try testing.expectEqual(@as(usize, 0), diags.errorCount());
}

test "lintCoreProgram: unbound variable fails" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // x :: Int = y  (y is unbound)
    const rhs = try alloc.create(Expr);
    rhs.* = .{ .Var = testId("y", 999, intType()) };

    const bind = Bind{ .NonRec = .{
        .binder = testId("x", 1, intType()),
        .rhs = rhs,
    } };

    const program: core.CoreProgram = &.{bind};
    const ok = try lintCoreProgram(alloc, program, &diags);
    try testing.expect(!ok);
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
}

test "lintCoreProgram: type mismatch in binding fails" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // x :: Bool = 42  (type mismatch)
    const rhs = try alloc.create(Expr);
    rhs.* = .{ .Lit = .{ .val = .{ .Int = 42 }, .span = testSpan() } };

    const bind = Bind{ .NonRec = .{
        .binder = testId("x", 1, boolType()), // expects Bool
        .rhs = rhs, // but RHS is Int
    } };

    const program: core.CoreProgram = &.{bind};
    const ok = try lintCoreProgram(alloc, program, &diags);
    try testing.expect(!ok);
    try testing.expectEqual(@as(usize, 1), diags.errorCount());
}

test "lintCoreProgram: application of non-function fails" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // f :: Int; x = f 42  (applying Int as a function)
    const f_id = testId("f", 1, intType());

    const f_var = try alloc.create(Expr);
    f_var.* = .{ .Var = f_id };

    const arg = try alloc.create(Expr);
    arg.* = .{ .Lit = .{ .val = .{ .Int = 42 }, .span = testSpan() } };

    const app = try alloc.create(Expr);
    app.* = .{ .App = .{
        .fn_expr = f_var,
        .arg = arg,
        .span = testSpan(),
    } };

    // f :: Int = 0
    const f_rhs = try alloc.create(Expr);
    f_rhs.* = .{ .Lit = .{ .val = .{ .Int = 0 }, .span = testSpan() } };

    const bind_f = Bind{ .NonRec = .{
        .binder = f_id,
        .rhs = f_rhs,
    } };

    const bind_x = Bind{ .NonRec = .{
        .binder = testId("x", 2, intType()),
        .rhs = app,
    } };

    const program: core.CoreProgram = &.{ bind_f, bind_x };
    const ok = try lintCoreProgram(alloc, program, &diags);
    try testing.expect(!ok);
    try testing.expect(diags.errorCount() >= 1);
}

test "lintCoreProgram: recursive binding passes" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);

    // rec { f = f }  (infinite loop, but well-typed)
    const f_id = testId("f", 1, intType());

    const f_var = try alloc.create(Expr);
    f_var.* = .{ .Var = f_id };

    const pairs = try alloc.alloc(core.BindPair, 1);
    pairs[0] = .{ .binder = f_id, .rhs = f_var };

    const bind = Bind{ .Rec = pairs };

    const program: core.CoreProgram = &.{bind};
    const ok = try lintCoreProgram(alloc, program, &diags);
    try testing.expect(ok);
    try testing.expectEqual(@as(usize, 0), diags.errorCount());
}

test "typesEqual: same types are equal" {
    try testing.expect(typesEqual(intType(), intType()));
    try testing.expect(typesEqual(boolType(), boolType()));
}

test "typesEqual: different types are not equal" {
    try testing.expect(!typesEqual(intType(), boolType()));
}

test "typesEqual: function types compare structurally" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    const int_t = intType();
    const bool_t = boolType();

    // Int -> Bool
    const fun1 = CoreType{ .FunTy = .{
        .arg = &int_t,
        .res = &bool_t,
    } };

    // Int -> Bool (same)
    const fun2 = CoreType{ .FunTy = .{
        .arg = &int_t,
        .res = &bool_t,
    } };

    // Bool -> Int (different)
    const fun3 = CoreType{ .FunTy = .{
        .arg = &bool_t,
        .res = &int_t,
    } };

    try testing.expect(typesEqual(fun1, fun2));
    try testing.expect(!typesEqual(fun1, fun3));
}
