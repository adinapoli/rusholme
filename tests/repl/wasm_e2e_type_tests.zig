//! WASM REPL Server End-to-End Tests for Type Queries
//!
//! Tests the `type` JSON-RPC method which returns the type of an expression.
//! These tests verify that the REPL can:
//! - Return types for literals
//! - Return errors for unbound names
//! - Return types for session-defined functions
//!
//! These tests share the same infrastructure as `wasm_e2e_tests.zig` but focus
//! specifically on the type query functionality.

const std = @import("std");
const testing = std.testing;

// Helpers from wasm_e2e_tests.zig
const runServer = @import("wasm_e2e_tests.zig").runServer;
const extractResult = @import("wasm_e2e_tests.zig").extractResult;
const hasError = @import("wasm_e2e_tests.zig").hasError;
const splitLines = @import("wasm_e2e_tests.zig").splitLines;

// ── Tests ─────────────────────────────────────────────────────────────────

test "type e2e: jsonrpc type request for literal" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"type","params":["42"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    const r = try extractResult(testing.allocator, lines[1]);
    defer if (r) |s| testing.allocator.free(s);

    try testing.expect(std.mem.indexOf(u8, r.?, "42") != null);
    try testing.expect(std.mem.indexOf(u8, r.?, "::") != null);
}

test "type e2e: jsonrpc type request returns diagnostics on error" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"type","params":["undefinedVar"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    // Should contain error response
    try testing.expect(std.mem.indexOf(u8, result.stdout, "\"error\"") != null);
}

test "type e2e: session-defined function type" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["id x = x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"type","params":["id"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    const r = try extractResult(testing.allocator, lines[2]);
    defer if (r) |s| testing.allocator.free(s);

    try testing.expect(std.mem.indexOf(u8, r.?, "forall") != null);
    try testing.expect(std.mem.indexOf(u8, r.?, "a -> a") != null or std.mem.indexOf(u8, r.?, "forall a. a -> a") != null);
}
