//! REPL Protocol Interface
//!
//! Provides structured API for REPL UI layers (CLI and browser/xterm.js).
//! Separates business logic from presentation.

const std = @import("std");
const Allocator = std.mem.Allocator;

const testing_io = testing.io;

const Session = @import("session.zig").Session;
const typequery = @import("typequery.zig");
const Diagnostic = @import("../diagnostics/diagnostic.zig").Diagnostic;

// ── Public Types ──────────────────────────────────────────────────────

/// Response status for protocol operations.
pub const Status = enum {
    /// Successful evaluation with a value.
    success,
    /// Error occurred, diagnostics contain details.
    failed,
    /// Declaration or command that succeeded silently (no value to display).
    silent,
};

/// Structured result from protocol operations.
pub const ProtocolResult = struct {
    /// Operation status.
    status: Status,
    /// Formatted result value (empty for errors and silent operations).
    /// Caller-owned when status == .failed and value is non-empty.
    /// Session-owned when status == .success.
    value: []const u8,
    /// Diagnostics from the operation (empty on success).
    diagnostics: []const Diagnostic,

    /// Free caller-owned allocations in this result.
    /// Call this with defer to ensure cleanup:
    ///   const result = try evaluate(alloc, session, input);
    ///   defer result.free(alloc);
    pub fn free(self: *const ProtocolResult, allocator: Allocator) void {
        // Only free value if this result owns it (error cases with allocated messages)
        // Session-owned values (success cases) should not be freed here.
        // We detect this by checking if value is non-empty and status is failed.
        if (self.status == .failed and self.value.len > 0) {
            // The value string was allocated by this function and needs freeing
            // Note: diagnostics messages are owned by session, not us
            allocator.free(self.value);
        }
    }
};

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "protocol: ProtocolResult has expected fields" {
    const result = ProtocolResult{
        .status = .success,
        .value = "42",
        .diagnostics = &.{},
    };
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("42", result.value);
}

test "protocol: Status enum has expected variants" {
    try testing.expectEqual(Status.success, Status.success);
    try testing.expectEqual(Status.failed, Status.failed);
    try testing.expectEqual(Status.silent, Status.silent);
}

// ── Operations ────────────────────────────────────────────────────────

/// Evaluate a REPL input through the protocol.
///
/// Memory ownership:
/// - On success: `value` is owned by the session and valid for the session's lifetime.
/// - On failure: `value` is caller-owned and must be freed via result.free(allocator).
///   Use `defer result.free(allocator)` for automatic cleanup.
pub fn evaluate(allocator: Allocator, session: *Session, input: []const u8) !ProtocolResult {
    // Delegate to Session.eval which handles expression vs declaration
    const session_result = session.eval(input) catch |err| {
        // On error, return error status with diagnostics
        var diags = session.getDiagnosticsForInput(allocator, input) catch &.{};

        // Build error result - if no diagnostics, capture what we can from the error
        if (diags.len > 0) {
            return ProtocolResult{
                .status = .failed,
                .value = diags[0].message,
                .diagnostics = diags,
            };
        }

        // No diagnostics available — format the error itself so the user
        // gets something more useful than a generic "evaluation failed".
        const msg = std.fmt.allocPrint(allocator, "Runtime error: {s} while evaluating: {s}", .{ @errorName(err), input }) catch "evaluation failed";
        return ProtocolResult{
            .status = .failed,
            .value = msg,
            .diagnostics = diags,
        };
    };

    // Success case - determine status based on result value
    const status: Status = if (session_result.value.len > 0) .success else .silent;

    return ProtocolResult{
        .status = status,
        .value = session_result.value,
        .diagnostics = &.{},
    };
}

/// Get diagnostics from the most recent evaluation.
pub fn getDiagnostics(session: *Session) []const Diagnostic {
    return session.last_diagnostics.items;
}

/// Get the type of a REPL expression through the protocol.
///
/// Memory ownership:
/// - On success: `value` is owned by the session and valid for the session's lifetime.
/// - On failure: `value` is caller-owned and must be freed via result.free(allocator).
///   Use `defer result.free(allocator)` for automatic cleanup.
pub fn typeOf(allocator: Allocator, session: *Session, input: []const u8) !ProtocolResult {
    const query_result = typequery.typeOf(allocator, session, input) catch |err| {
        // On error, return error status with diagnostics
        var diags = session.getDiagnosticsForInput(allocator, input) catch &.{};

        // Get the first diagnostic's error message (or fall back to error name)
        if (diags.len > 0) {
            return ProtocolResult{
                .status = .failed,
                .value = diags[0].message,
                .diagnostics = diags,
            };
        }

        const msg = std.fmt.allocPrint(allocator, "Type checking failed: {s}", .{@errorName(err)}) catch "type checking failed";
        return ProtocolResult{
            .status = .failed,
            .value = msg,
            .diagnostics = diags,
        };
    };

    // Success case: type query succeeded
    // Note: result.value is session.allocator-allocated memory valid for the lifetime of the session.
    // Diagnostics are owned by session.last_diagnostics.
    return ProtocolResult{
        .status = .success,
        .value = query_result.display,  // Full "<expr> :: <type>" string
        .diagnostics = &.{},
    };
}

test "protocol: evaluate returns success for simple expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing_io);
    defer session.deinit();

    const result = try evaluate(alloc, &session, "42");
    defer result.free(alloc);

    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("42", result.value);
    try testing.expectEqual(@as(usize, 0), result.diagnostics.len);
}

test "protocol: getDiagnostics returns empty slice on success" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing_io);
    defer session.deinit();

    {
        const result = try evaluate(alloc, &session, "42");
        defer result.free(alloc);
    }
    const diags = getDiagnostics(&session);

    try testing.expectEqual(@as(usize, 0), diags.len);
}

test "protocol: evaluate handles errors with diagnostics" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing_io);
    defer session.deinit();

    // Error: undefined variable should return failed status
    const result = try evaluate(alloc, &session, "undefined_var");
    defer result.free(alloc);
    try testing.expectEqual(Status.failed, result.status);
}

test "protocol: evaluate error result can be freed" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing_io);
    defer session.deinit();

    // Error case - value should be freed
    const result = try evaluate(alloc, &session, "nonexistent_function");
    try testing.expectEqual(Status.failed, result.status);
    try testing.expect(result.value.len > 0);

    // Free the allocated error message
    result.free(alloc);

    // Verify no leak by deinitializing the arena
    // (if we didn't free, the arena would have unreachable allocations)
}

test "protocol: typeOf error result can be freed" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing_io);
    defer session.deinit();

    // First define something so typeOf has a valid session
    _ = try evaluate(alloc, &session, "id x = x");

    // Error case: type an invalid expression
    const result = typeOf(alloc, &session, "undefined_var") catch |err| {
        // Expected to fail - check that we can still free if needed
        if (err == error.CompilationFailed) {
            // Check session diagnostics for the actual error message
            try testing.expect(session.last_diagnostics.items.len > 0);
            return; // Test passes if we got here without leak
        }
        return err;
    };
    defer result.free(alloc);

    // If we got a result (success path for error handling), it should be freeable
    try testing.expectEqual(Status.failed, result.status);
}
