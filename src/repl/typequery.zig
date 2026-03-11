//! Type query for REPL `:type <expr>` command.
//!
//! This module provides the ability to type-check an expression without
//! modifying session state or evaluating the expression. Used for the
//! REPL's `:type` command to display inferred types.
//!
//! The `typeOf()` function:
//! - Does NOT modify session state (transactional typechecking)
//! - Does NOT evaluate the expression (no execution side effects)
//! - Does NOT perform IO (pure type inference)
//!
//! See docs/superpowers/plans/0005-repl-type-command.md for the full plan.

const std = @import("std");
const Allocator = std.mem.Allocator;

const Session = @import("session.zig").Session;
const pipeline = @import("pipeline.zig").Pipeline;
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");
const DiagnosticCollector = @import("../diagnostics/diagnostic.zig").DiagnosticCollector;

pub const TypeQueryResult = struct {
    /// The inferred type scheme (polymorphic or monomorphic).
    /// Note: The HType body is arena-allocated from the session's allocator.
    /// The result is valid only for the lifetime of the session arena.
    scheme: env_mod.TyScheme,
    /// Formatted display string: "<expr> :: <type>"
    /// Allocated by the caller's allocator; caller must free.
    display: []const u8,
    /// Diagnostics from type-checking (empty on success).
    /// These are owned by session.last_diagnostics and persist across queries.
    diags: []const @import("../diagnostics/diagnostic.zig").Diagnostic,
};

/// Type-check an expression and return its inferred type.
/// Does NOT modify session state, does NOT evaluate, does NOT execute IO.
pub fn typeOf(
    alloc: std.mem.Allocator,
    session: *Session,
    expr: []const u8,
) !TypeQueryResult {
    _ = alloc;

    // 1. Push transactional scope frames BEFORE compilation
    session.rename_env.scope.push() catch return error.OutOfMemory;
    session.ty_env.push() catch {
        session.rename_env.scope.pop();
        return error.OutOfMemory;
    };

    // 2. Compile the expression through the pipeline
    var diags = DiagnosticCollector.init();
    defer diags.deinit(session.allocator);

    const compile = session.pipeline.compileInput(
        expr,
        &session.u_supply,
        &session.rename_env,
        &session.ty_env,
        &session.mv_supply,
        &diags,
        &session.accumulated_arities,
        &session.accumulated_con_map,
    ) catch |err| {
        // Rollback: pop the scope frames to discard partial bindings
        session.ty_env.pop();
        session.rename_env.scope.pop();
        return err;
    };

    // 3. Transactional rollback: pop scope frames to restore state
    // This ensures read-only semantics — the compilation is performed
    // but all bindings are discarded after type lookup.
    session.ty_env.pop();
    session.rename_env.scope.pop();

    // 4. Look up the type via the synthesized name
    // Expressions are wrapped as `replExpr__ = <expr>` during compilation,
    // so the first def in the program should be the expression binding.
    if (compile.program.defs.len == 0) {
        return error.CompilationFailed;
    }
    const def = compile.program.defs[0];
    const scheme = session.ty_env.lookupScheme(def.name.unique) orelse {
        return error.CompilationFailed;
    };

    // 5. Format the display: "<expr> :: <type>"
    const type_str = try htype_mod.prettyScheme(scheme, session.allocator);
    defer session.allocator.free(type_str);
    const display = try std.fmt.allocPrint(session.allocator, "{s} :: {s}", .{ expr, type_str });

    return TypeQueryResult{
        .scheme = scheme,
        .display = display,
        .diags = &.{},
    };
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "typequery: simple literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const result = try typeOf(alloc, &session, "42");
    defer alloc.free(result.display);

    try testing.expectEqualStrings("42 :: Int", result.display);
}
