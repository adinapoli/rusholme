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
    value: []const u8,
    /// Diagnostics from the operation (empty on success).
    diagnostics: []const Diagnostic,
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
/// - On failure: `value` is arena-allocated from the session's allocator and cleaned
///   up when the session is deinitialized. Callers using arena allocation need not free.
pub fn evaluate(allocator: Allocator, session: *Session, input: []const u8) !ProtocolResult {
    _ = allocator; // Session allocator is used for all allocations

    // Delegate to Session.eval which handles expression vs declaration
    const session_result = session.eval(input) catch |err| {
        // On error, return error status with diagnostics
        var diags = session.getDiagnosticsForInput(session.allocator, input) catch &.{};

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
        // Use session allocator so cleanup happens at session deinit.
        const msg = std.fmt.allocPrint(session.allocator, "Runtime error: {s} while evaluating: {s}", .{ @errorName(err), input }) catch "evaluation failed";
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
/// - On failure: `value` is arena-allocated from the session's allocator and cleaned
///   up when the session is deinitialized. Callers using arena allocation need not free.
pub fn typeOf(allocator: Allocator, session: *Session, input: []const u8) !ProtocolResult {
    _ = allocator; // Session allocator is used for all allocations

    const query_result = typequery.typeOf(session.allocator, session, input) catch |err| {
        // On error, return error status with diagnostics
        var diags = session.getDiagnosticsForInput(session.allocator, input) catch &.{};

        // Get the first diagnostic's error message (or fall back to error name)
        if (diags.len > 0) {
            return ProtocolResult{
                .status = .failed,
                .value = diags[0].message,
                .diagnostics = diags,
            };
        }

        // Use session allocator so cleanup happens at session deinit.
        const msg = std.fmt.allocPrint(session.allocator, "Type checking failed: {s}", .{@errorName(err)}) catch "type checking failed";
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

    _ = try evaluate(alloc, &session, "42");
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
    try testing.expectEqual(Status.failed, result.status);
}
