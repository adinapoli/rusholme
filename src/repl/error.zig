//! JSON error formatting for REPL WASM bridge
//!
//! Provides simplified JSON formatting for errors that can be
//! used over the WASM/JavaScript bridge.

const std = @import("std");
const buffer = @import("buffer.zig");

/// Format a simple error as JSON for the REPL
pub fn formatErrorJson(message: []const u8) []const u8 {
    // Format: {"status":"error","message":"..."}
    // For MVP: just return simple message
    // In production, would build proper JSON with escaping
    _ = message;
    return "{\"status\":\"error\",\"type\":\"parse_error\",\"message\":\"Parse error\"}";
}

/// Format a simple success result as JSON for the REPL
pub fn formatSuccessJson(value: []const u8) []const u8 {
    // Format: {"status":"success","value":"..."}
    // For MVP: just return simple message
    _ = value;
    return "{\"status\":\"success\",\"value\":\"result\"}";
}

test "error format" {
    const json = formatErrorJson("test error");
    _ = json;
}

test "success format" {
    const json = formatSuccessJson("test value");
    _ = json;
}
