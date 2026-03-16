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
const diag_mod = @import("../diagnostics/diagnostic.zig");
const DiagnosticCollector = diag_mod.DiagnosticCollector;
const Diagnostic = diag_mod.Diagnostic;
const Note = diag_mod.Note;

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
    alloc: std.mem.Allocator,  // Reserved for future use (currently uses session.allocator)
    session: *Session,
    expr: []const u8,
) !TypeQueryResult {
    _ = alloc;

    // Clear previous diagnostics - free their message allocations first
    for (session.last_diagnostics.items) |diag| {
        session.allocator.free(diag.message);
        if (diag.notes.len > 0) {
            session.allocator.free(diag.notes);
        }
    }
    session.last_diagnostics.clearRetainingCapacity();

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
        &session.accumulated_class_env,
        &session.accumulated_dict_names,
    ) catch |err| {
        // Capture compilation context for diagnostic rendering.
        session.last_source = session.pipeline.last_source;
        session.last_input = expr;
        session.last_input_kind = session.pipeline.last_input_kind;

        // Save diagnostics to session before returning error so callers can render them.
        // Note: we need to dupe the message allocation since diags will be deinitialized.
        for (diags.diagnostics.items) |diag| {
            session.last_diagnostics.append(session.allocator, .{
                .severity = diag.severity,
                .code = diag.code,
                .span = diag.span,
                .message = session.allocator.dupe(u8, diag.message) catch {
                    // Rollback and return error if we can't save diagnostics
                    session.ty_env.pop();
                    session.rename_env.scope.pop();
                    return err;
                },
                .notes = if (diag.notes.len > 0)
                    session.allocator.dupe(Note, diag.notes) catch &.{}
                else
                    &.{},
            }) catch {};
        }

        // Rollback: pop the scope frames to discard partial bindings
        session.ty_env.pop();
        session.rename_env.scope.pop();
        return err;
    };

    // 3. Look up the type via the synthesized name FIRST
    // Expressions are wrapped as `replExpr__ = <expr>` during compilation,
    // so the first def in the program should be the expression binding.
    // IMPORTANT: Lookup must happen BEFORE rollback.
    if (compile.program.defs.len == 0) {
        // Rollback before returning
        session.ty_env.pop();
        session.rename_env.scope.pop();
        return error.CompilationFailed;
    }
    const def = compile.program.defs[0];
    const scheme = session.ty_env.lookupScheme(def.name.unique) orelse {
        // Rollback before returning
        session.ty_env.pop();
        session.rename_env.scope.pop();
        return error.CompilationFailed;
    };

    // 4. Transactional rollback: pop scope frames to restore state
    // This ensures read-only semantics — the compilation is performed
    // but all bindings are discarded after type lookup.
    session.ty_env.pop();
    session.rename_env.scope.pop();

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

test "typequery: session state unchanged after query" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // Define something first
    _ = try session.processInput("id x = x");

    const arities_before = session.accumulated_arities.count();
    const con_map_before = session.accumulated_con_map.count();

    // Query a type - should not modify accumulated state
    _ = try typeOf(alloc, &session, "42");

    // Session state should not be modified
    try testing.expectEqual(arities_before, session.accumulated_arities.count());
    try testing.expectEqual(con_map_before, session.accumulated_con_map.count());
}

test "typequery: polymorphic constructor type (#508)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // Define a polymorphic data type
    _ = try session.processInput("data List a = Nil | Cons a (List a)");

    // Query the type of Nil - should show "forall a. List a", not "forall a. List ?N"
    const nil_result = try typeOf(alloc, &session, "Nil");
    defer alloc.free(nil_result.display);
    try testing.expectEqualStrings("Nil :: forall a. List a", nil_result.display);

    // Query the type of Cons - should show proper polymorphic type
    const cons_result = try typeOf(alloc, &session, "Cons");
    defer alloc.free(cons_result.display);
    try testing.expectEqualStrings("Cons :: forall a. a -> List a -> List a", cons_result.display);
}

test "typequery: type error diagnostics captured (#514)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // Define two different types
    _ = try session.processInput("data A = MkA");
    _ = try session.processInput("data B = MkB");

    // Try to type an expression with a type error:
    // \f -> (f MkA, f MkB) should fail because f can't accept both A and B
    const result = typeOf(alloc, &session, "\\f -> (f MkA, f MkB)");
    try testing.expectError(error.CompilationFailed, result);

    // The key fix: diagnostics should be captured in session.last_diagnostics
    // so the caller can render them instead of showing a generic error message
    try testing.expect(session.last_diagnostics.items.len > 0);
}

test "typequery: class method shows constraint (#582)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // Define a type class with a method
    _ = try session.processInput("class ShowIt a where\n  showIt :: a -> String");

    // Verify the type scheme is stored correctly in TyEnv by looking
    // up the scheme directly, rather than going through typeOf() which
    // compiles the expression fully (including desugaring + lambda
    // lifting) and crashes due to circular dictionary expressions.
    // tracked in: https://github.com/adinapoli/rusholme/issues/569
    const name = session.rename_env.scope.lookup("showIt") orelse
        return error.TestUnexpectedResult;
    const scheme = session.ty_env.lookupScheme(name.unique) orelse
        return error.TestUnexpectedResult;
    const type_str = try htype_mod.prettyScheme(scheme, alloc);
    defer alloc.free(type_str);
    try testing.expectEqualStrings("forall a. ShowIt a => a -> [Char]", type_str);
}
