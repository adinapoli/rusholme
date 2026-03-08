//! REPL Protocol Interface
//!
//! Provides structured API for REPL UI layers (CLI and browser/xterm.js).
//! Separates business logic from presentation.

const std = @import("std");
const Allocator = std.mem.Allocator;

const testing_io = testing.io;

const Session = @import("session.zig").Session;
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
pub fn evaluate(allocator: Allocator, session: *Session, input: []const u8) !ProtocolResult {
    // Delegate to Session.eval which handles expression vs declaration
    const session_result = session.eval(input) catch |err| {
        // Debug: print error name for investigation
        std.debug.print("ERROR in evaluate({s}): {}\n", .{ input, err });

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

        // If no diagnostics available, return generic error
        return ProtocolResult{
            .status = .failed,
            .value = "evaluation failed",
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
