//! JSON-RPC 2.0 Protocol Module
//!
//! Provides parsing and serialization for JSON-RPC 2.0 requests and responses,
//! implementing the spec from https://www.jsonrpc.org/specification

const std = @import("std");

pub const ParseError = error{
    InvalidRequest,
};

pub const Request = struct {
    jsonrpc: []const u8 = "2.0",
    id: u32,
    method: []const u8,
    allocator: std.mem.Allocator,

    /// Free all memory allocated for this request.
    pub fn deinit(self: *Request) void {
        self.allocator.free(self.method);
    }
};

pub const Response = struct {
    jsonrpc: []const u8 = "2.0",
    id: u32,
    result: ?std.json.Value = null,
    @"error": ?ErrorResponse = null,
};

pub const ErrorResponse = struct {
    code: i32,
    message: []const u8,
    data: ?[]const u8 = null,
};

/// Parse a JSON-RPC request string into a Request struct.
/// Returns ParseError.InvalidRequest if the request is malformed.
/// Caller must call request.deinit() to free allocated memory.
pub fn parseRequest(allocator: std.mem.Allocator, input: []const u8) ParseError!Request {
    const parsed = std.json.parseFromSlice(std.json.Value, allocator, input, .{}) catch {
        // Convert any parse error to InvalidRequest
        return ParseError.InvalidRequest;
    };
    defer parsed.deinit();

    const root = parsed.value;

    // Extract object if value is an object
    const obj = switch (root) {
        .object => |o| o,
        else => return ParseError.InvalidRequest,
    };

    const id_value = obj.get("id") orelse return ParseError.InvalidRequest;
    const id = switch (id_value) {
        .integer => |i| i,
        else => return ParseError.InvalidRequest,
    };

    const method_value = obj.get("method") orelse return ParseError.InvalidRequest;
    const method_slice = switch (method_value) {
        .string => |s| s,
        else => return ParseError.InvalidRequest,
    };

    // Copy the method string to the caller's allocator
    const method = allocator.dupe(u8, method_slice) catch return ParseError.InvalidRequest;

    return .{
        .id = @intCast(id),
        .method = method,
        .allocator = allocator,
    };
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "jsonrpc: parse simple request" {
    const allocator = std.testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"test\"}";
    var result = try parseRequest(allocator, input);
    defer result.deinit();
    try testing.expectEqual(@as(u32, 1), result.id);
    try testing.expectEqualStrings("test", result.method);
}

test "jsonrpc: parse request with params" {
    const allocator = std.testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"evaluate\",\"params\":[\"1 + 1\"]}";
    var result = try parseRequest(allocator, input);
    defer result.deinit();
    try testing.expectEqual(@as(u32, 42), result.id);
    try testing.expectEqualStrings("evaluate", result.method);
}

test "jsonrpc: parse invalid request returns error" {
    const allocator = std.testing.allocator;
    // Missing 'id' field
    const input = "{\"jsonrpc\":\"2.0\",\"method\":\"test\"}";
    const result = parseRequest(allocator, input);
    try testing.expectError(ParseError.InvalidRequest, result);
}

test "jsonrpc: parse invalid json returns error" {
    const allocator = std.testing.allocator;
    const input = "not valid json";
    const result = parseRequest(allocator, input);
    try testing.expectError(ParseError.InvalidRequest, result);
}
