//! WASM REPL Server End-to-End Tests
//!
//! Spawns `wasmtime run repl-server.wasm` as a subprocess and
//! exercises the JSON-RPC 2.0 protocol over stdin/stdout.
//!
//! Each test writes a complete JSON-RPC script (newline-delimited
//! requests) to stdin, closes the pipe (causing EOF → graceful
//! shutdown), then asserts against the collected stdout lines.
//!
//! These tests verify the same WASM binary that the browser uses
//! (same pipeline, same GRIN evaluator) but through the headless
//! command-mode server, making failures reproducible without a
//! browser.

const std = @import("std");
const testing = std.testing;
const process = std.process;
const Io = std.Io;
const File = Io.File;

// ── Helpers ───────────────────────────────────────────────────────────────

/// Result of running the WASM server with piped input.
const ServerResult = struct {
    stdout: []u8,
    stderr: []u8,
    term: process.Child.Term,

    fn deinit(self: ServerResult, allocator: std.mem.Allocator) void {
        allocator.free(self.stdout);
        allocator.free(self.stderr);
    }
};

/// Spawn `wasmtime run repl-server.wasm`, feed it `input` on stdin,
/// and return collected stdout and stderr after the process exits.
fn runServer(allocator: std.mem.Allocator, input: []const u8) !ServerResult {
    const io = testing.io;
    const argv = [_][]const u8{ "wasmtime", "run", "zig-out/bin/repl-server.wasm" };

    var child = try process.spawn(io, .{
        .argv = &argv,
        .stdin = .pipe,
        .stdout = .pipe,
        .stderr = .pipe,
    });
    errdefer child.kill(io);

    const stdin_file = child.stdin.?;
    stdin_file.writeStreamingAll(io, input) catch {};
    stdin_file.close(io);
    child.stdin = null;

    var multi_reader_buffer: File.MultiReader.Buffer(2) = undefined;
    var multi_reader: File.MultiReader = undefined;
    multi_reader.init(allocator, io, multi_reader_buffer.toStreams(), &.{ child.stdout.?, child.stderr.? });
    defer multi_reader.deinit();

    while (true) {
        multi_reader.fill(64, .none) catch |err| switch (err) {
            error.EndOfStream => break,
            else => |e| return e,
        };
    }

    try multi_reader.checkAnyError();

    const term = try child.wait(io);

    const stdout_slice = try multi_reader.toOwnedSlice(0);
    errdefer allocator.free(stdout_slice);

    const stderr_slice = try multi_reader.toOwnedSlice(1);

    return .{
        .stdout = stdout_slice,
        .stderr = stderr_slice,
        .term = term,
    };
}

/// Parse one JSON-RPC response line and return the "result" string value.
/// Returns null if the response has no result or result is not a string.
fn extractResult(allocator: std.mem.Allocator, line: []const u8) !?[]const u8 {
    const parsed = std.json.parseFromSlice(std.json.Value, allocator, line, .{}) catch return null;
    defer parsed.deinit();

    const obj = switch (parsed.value) {
        .object => |o| o,
        else => return null,
    };

    const result_val = obj.get("result") orelse return null;
    return switch (result_val) {
        .string => |s| try allocator.dupe(u8, s),
        else => null,
    };
}

/// Parse one JSON-RPC response line and return whether it has an error.
fn hasError(allocator: std.mem.Allocator, line: []const u8) !bool {
    const parsed = std.json.parseFromSlice(std.json.Value, allocator, line, .{}) catch return false;
    defer parsed.deinit();

    const obj = switch (parsed.value) {
        .object => |o| o,
        else => return false,
    };

    return obj.get("error") != null;
}

/// Split stdout into non-empty lines.
fn splitLines(allocator: std.mem.Allocator, text: []const u8) ![][]const u8 {
    var lines: std.ArrayListUnmanaged([]const u8) = .{};
    var iter = std.mem.splitScalar(u8, text, '\n');
    while (iter.next()) |line| {
        if (line.len > 0) {
            try lines.append(allocator, line);
        }
    }
    return try lines.toOwnedSlice(allocator);
}

/// Assert that `haystack` contains `needle`. On failure, prints both
/// for easier debugging.
fn expectContains(haystack: []const u8, needle: []const u8) !void {
    if (std.mem.indexOf(u8, haystack, needle) == null) {
        std.debug.print(
            "Expected output to contain: '{s}'\nActual output ({d} bytes): '{s}'\n",
            .{ needle, haystack.len, haystack },
        );
        return error.TestExpectedContains;
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────

test "wasm e2e: init returns ok" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 1);
    const r = try extractResult(testing.allocator, lines[0]);
    defer if (r) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("ok", r.?);
}

test "wasm e2e: eval integer literal" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["42"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 2);
    const r = try extractResult(testing.allocator, lines[1]);
    defer if (r) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("42", r.?);
}

// NOTE: Boolean literals (True/False) and string literals are not yet
// supported by the GRIN tree-walking evaluator used in WASM mode. They
// work in the native REPL (which uses LLVM JIT) but fail here because
// the GRIN evaluator cannot evaluate bare constructor applications.
// tracked in: https://github.com/adinapoli/rusholme/issues/494

test "wasm e2e: define function then apply" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["f x = x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["f 42"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 3);

    // Declaration returns empty string (silent).
    const r_decl = try extractResult(testing.allocator, lines[1]);
    defer if (r_decl) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("", r_decl.?);

    // Application of f to 42 returns "42".
    const r_eval = try extractResult(testing.allocator, lines[2]);
    defer if (r_eval) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("42", r_eval.?);
}

test "wasm e2e: define multiple functions then use" {
    // Simulates a :load scenario: multiple declarations followed by use.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["id x = x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["const x y = x"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["id 99"]}
        \\{"jsonrpc":"2.0","id":5,"method":"eval","params":["const 1 2"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 5);

    // id 99 => "99"
    const r4 = try extractResult(testing.allocator, lines[3]);
    defer if (r4) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("99", r4.?);

    // const 1 2 => "1"
    const r5 = try extractResult(testing.allocator, lines[4]);
    defer if (r5) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("1", r5.?);
}

test "wasm e2e: multiline declaration via eval" {
    // Send a multi-line declaration body as a single eval (simulates :load
    // sending the entire file body).
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["id x = x\nconst x y = x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["id 7"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["const 3 4"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 4);

    // id 7 => "7"
    const r3 = try extractResult(testing.allocator, lines[2]);
    defer if (r3) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("7", r3.?);

    // const 3 4 => "3"
    const r4 = try extractResult(testing.allocator, lines[3]);
    defer if (r4) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("3", r4.?);
}

test "wasm e2e: method not found returns error" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"bogus"}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 2);
    try testing.expect(try hasError(testing.allocator, lines[1]));
}

test "wasm e2e: parse error returns error" {
    const input = "not json at all\n";
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 1);
    try testing.expect(try hasError(testing.allocator, lines[0]));
}

test "wasm e2e: graceful shutdown on stdin close" {
    // Empty input — server should exit cleanly when stdin closes.
    const result = try runServer(testing.allocator, "");
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "wasm e2e: unbound variable returns error" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["undefined_xyz"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 2);
    try testing.expect(try hasError(testing.allocator, lines[1]));
}
