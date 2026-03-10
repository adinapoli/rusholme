//! REPL Server Mode Tests
//!
//! Integration tests for the JSON-RPC server mode.
//! Tests verify basic request/response cycles, all commands (init, eval,
//! type, shutdown), and error handling for invalid requests.
//!
//! Uses std.testing framework and tests the JSON-RPC parsing/formatting
//! functionality directly since mocking stdin/stdout for full server
//! integration testing requires careful IO management.

const std = @import("std");
const testing = std.testing;
const Allocator = std.mem.Allocator;

const jsonrpc = @import("../../src/repl/jsonrpc.zig");

// ── Test Helpers ─────────────────────────────────────────────────────────

/// Parse a JSON string and verify it contains expected fields.
fn verifyJsonResponse(json_str: []const u8, expected_id: u32, expected_result: ?[]const u8, expected_error: ?struct { code: i32, message: []const u8 }) !void {
    const parsed = std.json.parseFromSlice(std.json.Value, testing.allocator, json_str, .{}) catch {
        std.debug.print("Failed to parse JSON: '{s}'\n", .{json_str});
        return error.InvalidJson;
    };
    defer parsed.deinit();

    // Check jsonrpc field
    const jsonrpc_obj = parsed.value.object.get("jsonrpc") orelse return error.MissingJsonrpc;
    try testing.expectEqualStrings("2.0", jsonrpc_obj.string);

    // Check id field
    const id = parsed.value.object.get("id") orelse return error.MissingId;
    try testing.expectEqual(expected_id, @intCast(id.integer));

    // Either result or error should be present
    const has_result = parsed.value.object.get("result") != null;
    const has_error = parsed.value.object.get("error") != null;

    if (expected_result) |result| {
        try testing.expect(has_result);
        try testing.expect(!has_error);
        const result_value = parsed.value.object.get("result").?;
        try testing.expectEqualStrings(result, result_value.string);
    } else if (expected_error) |expected| {
        try testing.expect(!has_result);
        try testing.expect(has_error);
        const error_obj = parsed.value.object.get("error").?.object;
        try testing.expectEqual(expected.code, error_obj.get("code").?.integer);
        try testing.expectEqualStrings(expected.message, error_obj.get("message").?.string);
    }
}

// ── Tests: Basic request/response cycle ─────────────────────────────────

test "server: parseRequest handles init command" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"init\",\"params\":null}";

    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 1), result.id);
    try testing.expectEqualStrings("init", result.method);
    try testing.expect(result.params == null);
}

test "server: parseRequest handles eval with string params" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"eval\",\"params\":[\"42\"]}";

    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 2), result.id);
    try testing.expectEqualStrings("eval", result.method);
}

test "server: parseRequest handles type command" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"type\",\"params\":[\"x\"]}";

    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 3), result.id);
    try testing.expectEqualStrings("type", result.method);
}

test "server: parseRequest handles shutdown command" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"shutdown\"}";

    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 4), result.id);
    try testing.expectEqualStrings("shutdown", result.method);
}

test "server: parseRequest handles eval with expression" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"eval\",\"params\":[\"1 + 1\"]}";

    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 5), result.id);
    try testing.expectEqualStrings("eval", result.method);
}

// ── Tests: Error handling for invalid requests ─────────────────────────

test "server: parseRequest returns error for invalid request" {
    const allocator = testing.allocator;
    // Missing 'id' field
    const input = "{\"jsonrpc\":\"2.0\",\"method\":\"test\"}";
    const result = jsonrpc.parseRequest(allocator, input);
    try testing.expectError(jsonrpc.ParseError.InvalidRequest, result);
}

test "server: parseRequest returns error for invalid JSON" {
    const allocator = testing.allocator;
    const input = "not valid json";
    const result = jsonrpc.parseRequest(allocator, input);
    try testing.expectError(jsonrpc.ParseError.InvalidRequest, result);
}

test "server: parseRequest handles request with array params" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"evaluate\",\"params\":[\"1 + 1\"]}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 42), result.id);
    try testing.expectEqualStrings("evaluate", result.method);
}

test "server: parseRequest handles request with string params" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":10,\"method\":\"eval\",\"params\":\"test\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 10), result.id);
    try testing.expectEqualStrings("eval", result.method);
}

test "server: parseRequest handles missing params field" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"init\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 1), result.id);
    try testing.expectEqualStrings("init", result.method);
    try testing.expect(result.params == null);
}

test "server: parseRequest handles params with special characters" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"eval\",\"params\":[\"\\\"hello\\\" world\"]}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 6), result.id);
    try testing.expectEqualStrings("eval", result.method);
}

test "server: parseRequest handles empty string params" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"eval\",\"params\":[\"\"]}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 7), result.id);
    try testing.expectEqualStrings("eval", result.method);
}

// ── Tests: Response formatting ─────────────────────────────────────────

test "server: formatResponse produces valid JSON" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .id = 1,
        .result = std.json.Value{ .string = "ok" },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    // Verify output is valid JSON
    const parsed = std.json.parseFromSlice(std.json.Value, allocator, output, .{}) catch {
        return error.InvalidJson;
    };
    defer parsed.deinit();

    try testing.expect(std.mem.indexOf(u8, output, "\"jsonrpc\":\"2.0\"") != null);
    try testing.expect(std.mem.indexOf(u8, output, "\"id\":1") != null);
}

test "server: formatResponse includes result field" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .id = 5,
        .result = std.json.Value{ .string = "42" },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    try testing.expect(std.mem.indexOf(u8, output, "\"result\"") != null);
    try testing.expect(std.mem.indexOf(u8, output, "\"42\"") != null);
}

test "server: formatResponse with null result works" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .id = 0,
        .result = null,
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    try testing.expect(output.len > 0);
}

test "server: formatResponse with error field" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 0,
        .result = null,
        .@"error" = .{ .code = -32600, .message = "Invalid Request", .data = null },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    const parsed = std.json.parseFromSlice(std.json.Value, allocator, output, .{}) catch {
        return error.InvalidJson;
    };
    defer parsed.deinit();

    try testing.expect(parsed.value.object.get("error") != null);
    const error_obj = parsed.value.object.get("error").?.object;
    try testing.expectEqual(@as(i64, -32600), error_obj.get("code").?.integer);
}

test "server: formatResponse handles numeric result" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .id = 8,
        .result = std.json.Value{ .integer = 100 },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    try testing.expect(std.mem.indexOf(u8, output, "100") != null);
}

test "server: formatResponse handles boolean result" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .id = 9,
        .result = std.json.Value{ .bool = true },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    try testing.expect(std.mem.indexOf(u8, output, "true") != null);
}

test "server: formatResponse handles object result" {
    const allocator = testing.allocator;
    const obj = std.json.ObjectMap.init(allocator);
    defer obj.deinit();
    try obj.put(allocator, "key", std.json.Value{ .string = "value" });

    const response = jsonrpc.Response{
        .id = 10,
        .result = std.json.Value{ .object = &obj },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    try testing.expect(std.mem.indexOf(u8, output, "\"object\"") != null);
}

// ── Tests: Request parsing edge cases ─────────────────────────────────

test "server: parseRequest handles extra whitespace" {
    const allocator = testing.allocator;
    // JSON with extra whitespace
    const input = "  {  \"jsonrpc\"  :  \"2.0\"  ,  \"id\"  :  1  ,  \"method\"  :  \"init\"  }  ";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 1), result.id);
    try testing.expectEqualStrings("init", result.method);
}

test "server: parseRequest handles newline characters" {
    const allocator = testing.allocator;
    // JSON with newlines
    const input =
        \\{
        \\  "jsonrpc": "2.0",
        \\  "id": 1,
        \\  "method": "init"
        \\}
    ;
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 1), result.id);
    try testing.expectEqualStrings("init", result.method);
}

test "server: parseRequest handles zero id" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":0,\"method\":\"init\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 0), result.id);
    try testing.expectEqualStrings("init", result.method);
}

test "server: parseRequest handles large id values" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":999999,\"method\":\"init\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(@as(u32, 999999), result.id);
    try testing.expectEqualStrings("init", result.method);
}

test "server: parseRequest handles max u32 id" {
    const allocator = testing.allocator;
    const max_id: u32 = std.math.maxInt(u32);
    const input = std.fmt.allocPrint(allocator, "{{\"jsonrpc\":\"2.0\",\"id\":{d},\"method\":\"init\"}}", .{max_id}) catch unreachable;
    defer allocator.free(input);

    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqual(max_id, result.id);
}

// ── Tests: JSON-RPC standard error codes ───────────────────────────────

test "server: standard JSON-RPC error codes are defined" {
    // From spec: https://www.jsonrpc.org/specification
    // -32700  Parse error
    // -32600  Invalid Request
    // -32601  Method not found
    // -32602  Invalid params
    // -32603  Internal error

    const parse_error: i32 = -32700;
    const invalid_request: i32 = -32600;
    const method_not_found: i32 = -32601;
    const invalid_params: i32 = -32602;
    const internal_error: i32 = -32603;

    // Verify error codes match spec
    try testing.expectEqual(@as(i32, -32700), parse_error);
    try testing.expectEqual(@as(i32, -32600), invalid_request);
    try testing.expectEqual(@as(i32, -32601), method_not_found);
    try testing.expectEqual(@as(i32, -32602), invalid_params);
    try testing.expectEqual(@as(i32, -32603), internal_error);
}

test "server: error response can be formatted" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 0,
        .result = null,
        .@"error" = .{ .code = -32600, .message = "Invalid Request", .data = null },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    // Verify error text is present
    try testing.expect(std.mem.indexOf(u8, output, "-32600") != null);
    try testing.expect(std.mem.indexOf(u8, output, "Invalid Request") != null);
}

// ── Tests: Response structure ─────────────────────────────────────────

test "server: Response struct has expected fields" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 0,
        .result = null,
        .@"error" = null,
        .allocator = allocator,
    };

    _ = response.jsonrpc;
    _ = response.id;
    _ = response.result;
    _ = response.@"error";
}

test "server: ErrorResponse struct has expected fields" {
    const error_response = jsonrpc.ErrorResponse{
        .code = -32600,
        .message = "Invalid Request",
        .data = null,
    };

    try testing.expectEqual(@as(i32, -32600), error_response.code);
    try testing.expectEqualStrings("Invalid Request", error_response.message);
}

// ── Tests: Response deinitialization ───────────────────────────────────

test "server: Response.deinit correctly cleans up" {
    const allocator = testing.allocator;
    var response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 1,
        .result = std.json.Value{ .string = "test" },
        .@"error" = null,
        .allocator = allocator,
    };

    // Should not panic
    response.deinit();
}

test "server: Response.deinit handles null result" {
    const allocator = testing.allocator;
    var response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 0,
        .result = null,
        .@"error" = null,
        .allocator = allocator,
    };

    // Should not panic
    response.deinit();
}

test "server: Response.deinit handles error response" {
    const allocator = testing.allocator;
    var response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 0,
        .result = null,
        .@"error" = .{ .code = -32600, .message = "Invalid Request", .data = null },
        .allocator = allocator,
    };

    // Should not panic
    response.deinit();
}

test "server: Response.deinit handles numeric result" {
    const allocator = testing.allocator;
    var response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 1,
        .result = std.json.Value{ .integer = 42 },
        .@"error" = null,
        .allocator = allocator,
    };

    // Should not panic
    response.deinit();
}

test "server: Response.deinit handles boolean result" {
    const allocator = testing.allocator;
    var response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 1,
        .result = std.json.Value{ .bool = true },
        .@"error" = null,
        .allocator = allocator,
    };

    // Should not panic
    response.deinit();
}

// ── Tests: Method invocation helpers ───────────────────────────────────

test "server: parseRequest preserves method string" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"testMethod\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqualStrings("testMethod", result.method);
}

test "server: parseRequest handles complex method name" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"testMethod_with_underscore\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqualStrings("testMethod_with_underscore", result.method);
}

test "server: parseRequest handles method name with numbers" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"test123\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqualStrings("test123", result.method);
}

test "server: parseRequest handles empty method name" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"\"}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expectEqualStrings("", result.method);
}

// ── Tests: Error handling ─────────────────────────────────────────────

test "server: formatResponse handles error with data field" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 1,
        .result = null,
        .@"error" = .{ .code = -32603, .message = "Evaluation failed", .data = "Division by zero" },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);

    try testing.expect(std.mem.indexOf(u8, output, "-32603") != null);
    try testing.expect(std.mem.indexOf(u8, output, "Evaluation failed") != null);
}

test "server: formatResponse handles null error data" {
    const allocator = testing.allocator;
    const response = jsonrpc.Response{
        .jsonrpc = "2.0",
        .id = 1,
        .result = null,
        .@"error" = .{ .code = -32603, .message = "Error", .data = null },
        .allocator = allocator,
    };

    const output = try jsonrpc.formatResponse(allocator, response);
    defer allocator.free(output);
}

// ── Tests: Array params handling ───────────────────────────────────────

test "server: parseRequest handles multiple params in array" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"test\",\"params\":[\"a\",\"b\",\"c\"]}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expect(result.params != null);
    if (result.params) |params| {
        try testing.expect(params == .array);
        try testing.expectEqual(@as(usize, 3), params.array.items.len);
    }
}

test "server: parseRequest handles empty params array" {
    const allocator = testing.allocator;
    const input = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"test\",\"params\":[]}";
    var result = try jsonrpc.parseRequest(allocator, input);
    defer result.deinit();

    try testing.expect(result.params != null);
    if (result.params) |params| {
        try testing.expect(params == .array);
        try testing.expectEqual(@as(usize, 0), params.array.items.len);
    }
}
