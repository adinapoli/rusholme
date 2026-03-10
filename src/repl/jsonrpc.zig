//! JSON-RPC 2.0 Protocol Module
//!
//! Provides parsing and serialization for JSON-RPC 2.0 requests and responses,
//! implementing the spec from https://www.jsonrpc.org/specification

const std = @import("std");

pub const ParseError = error{
    InvalidRequest,
    OutOfMemory,
};

pub const Request = struct {
    jsonrpc: []const u8 = "2.0",
    id: u32,
    method: []const u8,
    params: ?std.json.Value = null,
    allocator: std.mem.Allocator,

    /// Free all memory allocated for this request.
    pub fn deinit(self: *Request) void {
        self.allocator.free(self.method);
        // params is borrowed from the parsed JSON tree and does not need deinit
    }
};

pub const Response = struct {
    jsonrpc: []const u8 = "2.0",
    id: u32,
    result: ?std.json.Value = null,
    @"error": ?ErrorResponse = null,
    allocator: std.mem.Allocator,

    /// Free all memory allocated for this response.
    /// Must be called before the response goes out of scope.
    pub fn deinit(self: *Response) void {
        if (self.result) |*r| {
            r.deinit(self.allocator);
        }
    }
};

pub const ErrorResponse = struct {
    code: i32,
    /// Borrowed slice of the original JSON response.
    /// Points into the input string used to create the Response;
    /// does not need to be freed.
    message: []const u8,
    /// Additional error details. This is a borrowed slice pointing into
    /// the original JSON response, or null if not present.
    /// Does not need to be freed.
    data: ?[]const u8 = null,
};

/// Parse a JSON-RPC request string into a Request struct.
/// Returns ParseError.InvalidRequest if the request is malformed.
/// Returns ParseError.OutOfMemory on allocation failure.
/// Caller must call request.deinit() to free allocated memory.
pub fn parseRequest(allocator: std.mem.Allocator, input: []const u8) ParseError!Request {
    const parsed = std.json.parseFromSlice(std.json.Value, allocator, input, .{}) catch |err| {
        // Propagate OutOfMemory, convert other errors to InvalidRequest
        switch (err) {
            error.OutOfMemory => return ParseError.OutOfMemory,
            else => return ParseError.InvalidRequest,
        }
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
    const method = allocator.dupe(u8, method_slice) catch return ParseError.OutOfMemory;

    // Extract optionally-present params field
    const params = obj.get("params");

    return .{
        .id = @intCast(id),
        .method = method,
        .allocator = allocator,
        .params = params,
    };
}

/// Format a JSON-RPC response as a JSON string.
/// The returned string is allocated with the provided allocator and must be freed by the caller.
pub fn formatResponse(allocator: std.mem.Allocator, response: Response) ![]const u8 {
    const ResponseJson = struct {
        jsonrpc: []const u8,
        id: u32,
        result: ?std.json.Value = null,
        @"error": ?ErrorResponse = null,
    };

    const response_json = ResponseJson{
        .jsonrpc = "2.0",
        .id = response.id,
        .result = response.result,
        .@"error" = response.@"error",
    };

    var out = std.Io.Writer.Allocating.init(allocator);
    var write_stream: std.json.Stringify = .{
        .writer = &out.writer,
        .options = .{},
    };

    try write_stream.write(response_json);
    return out.written();
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

test "jsonrpc: format success response" {
    const allocator = std.testing.allocator;
    const response = Response{ .id = 1, .result = std.json.Value.null, .allocator = allocator };
    const output = try formatResponse(allocator, response);
    defer allocator.free(output);
    try testing.expect(std.mem.indexOf(u8, output, "\"jsonrpc\":\"2.0\"") != null);
}
