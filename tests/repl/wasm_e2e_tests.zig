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

// Import type query tests
const _ = @import("wasm_e2e_type_tests.zig");

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

/// Spawn `wasmtime run --invoke repl_server_run repl.wasm`, feed it
/// `input` on stdin, and return collected stdout/stderr after exit.
fn runServer(allocator: std.mem.Allocator, input: []const u8) !ServerResult {
    const io = testing.io;
    const argv = [_][]const u8{ "wasmtime", "run", "--invoke", "repl_server_run", "zig-out/bin/repl.wasm" };

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

// NOTE: Built-in constructors (True/False) require a Prelude that provides
// `data Bool = True | False` etc. User-defined constructors work because
// their data declarations flow through the pipeline and populate the
// GRIN translator's constructor map across REPL interactions.
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

// ── User-defined ADT tests ────────────────────────────────────────────

test "wasm e2e: user-defined nullary constructors" {
    // Define a data type and evaluate its constructors directly.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["data Color = Red | Green | Blue"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["Red"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["Green"]}
        \\{"jsonrpc":"2.0","id":5,"method":"eval","params":["Blue"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 5);

    // Data declaration is silent.
    const r_decl = try extractResult(testing.allocator, lines[1]);
    defer if (r_decl) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("", r_decl.?);

    // Bare constructors evaluate to their tag name.
    const r_red = try extractResult(testing.allocator, lines[2]);
    defer if (r_red) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("Red", r_red.?);

    const r_green = try extractResult(testing.allocator, lines[3]);
    defer if (r_green) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("Green", r_green.?);

    const r_blue = try extractResult(testing.allocator, lines[4]);
    defer if (r_blue) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("Blue", r_blue.?);
}

test "wasm e2e: pass user-defined constructor through function" {
    // Constructors should survive being passed through functions.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["data Color = Red | Green | Blue"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["id x = x"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["id Red"]}
        \\{"jsonrpc":"2.0","id":5,"method":"eval","params":["id Green"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 5);

    const r4 = try extractResult(testing.allocator, lines[3]);
    defer if (r4) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("Red", r4.?);

    const r5 = try extractResult(testing.allocator, lines[4]);
    defer if (r5) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("Green", r5.?);
}

test "wasm e2e: multiline data type and function in one eval" {
    // A data type and function defined together in a single multi-line eval.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["data Dir = North | South\ngo x = x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["go North"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 3);

    const r = try extractResult(testing.allocator, lines[2]);
    defer if (r) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("North", r.?);
}

// ── Case expressions ──────────────────────────────────────────────────

test "wasm e2e: case expression on nullary constructors" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["data Color = Red | Green | Blue"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["showColor c = case c of { Red -> 1 ; Green -> 2 ; Blue -> 3 }"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["showColor Red"]}
        \\{"jsonrpc":"2.0","id":5,"method":"eval","params":["showColor Blue"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 5);

    const r4 = try extractResult(testing.allocator, lines[3]);
    defer if (r4) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("1", r4.?);

    const r5 = try extractResult(testing.allocator, lines[4]);
    defer if (r5) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("3", r5.?);
}

test "wasm e2e: case expression on constructor with fields" {
    // Constructors with fields are stored on the heap; case matching
    // must auto-fetch through the heap pointer.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["data List a = Nil | Cons a (List a)"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["head_it xs = case xs of { Cons y ys -> y }"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["head_it (Cons 42 Nil)"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 4);

    const r4 = try extractResult(testing.allocator, lines[3]);
    defer if (r4) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("42", r4.?);
}

// ── Higher-order functions ────────────────────────────────────────────

test "wasm e2e: higher-order function application" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["apply f x = f x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["identity x = x"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["apply identity 42"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 4);

    const r4 = try extractResult(testing.allocator, lines[3]);
    defer if (r4) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("42", r4.?);
}

test "wasm e2e: recursive higher-order function (map)" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["data List a = Nil | Cons a (List a)"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["identity x = x"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["map_it f xs = case xs of { Nil -> Nil ; Cons y ys -> Cons (f y) (map_it f ys) }"]}
        \\{"jsonrpc":"2.0","id":5,"method":"eval","params":["head_it xs = case xs of { Cons y ys -> y }"]}
        \\{"jsonrpc":"2.0","id":6,"method":"eval","params":["head_it (map_it identity (Cons 99 Nil))"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 6);

    const r6 = try extractResult(testing.allocator, lines[5]);
    defer if (r6) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("99", r6.?);
}

// ── IO and do-notation ────────────────────────────────────────────────

test "wasm e2e: putStrLn produces output" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["putStrLn \"Hello\""]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    // putStrLn writes to stdout before the JSON-RPC response.
    try expectContains(result.stdout, "Hello\n");
}

test "wasm e2e: do-notation with multiple putStrLn" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["do { putStrLn \"Hello\" ; putStrLn \"World\" }"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    try expectContains(result.stdout, "Hello\n");
    try expectContains(result.stdout, "World\n");
}

test "wasm e2e: dollar operator with putStrLn" {
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["($) f x = f x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["identity x = x"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["putStrLn $ identity \"Hello\""]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    try expectContains(result.stdout, "Hello\n");
}

// ── Full hello.hs integration ─────────────────────────────────────────

test "wasm e2e: hello.hs feature set" {
    // Exercises all features from the hello.hs target program:
    // ($), identity, data List, map_it, head_it, do-notation, putStrLn.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["($) f x = f x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["identity x = x"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["data List a = Nil | Cons a (List a)"]}
        \\{"jsonrpc":"2.0","id":5,"method":"eval","params":["map_it f xs = case xs of { Nil -> Nil ; Cons y ys -> Cons (f y) (map_it f ys) }"]}
        \\{"jsonrpc":"2.0","id":6,"method":"eval","params":["head_it xs = case xs of { Cons y ys -> y }"]}
        \\{"jsonrpc":"2.0","id":7,"method":"eval","params":["head_it (Cons 42 Nil)"]}
        \\{"jsonrpc":"2.0","id":8,"method":"eval","params":["head_it (map_it identity (Cons 99 Nil))"]}
        \\{"jsonrpc":"2.0","id":9,"method":"eval","params":["do { putStrLn $ identity \"Hello\" ; putStrLn \"World\" }"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    // Find the JSON-RPC responses for ids 7, 8 (value assertions).
    // Note: putStrLn output lines are interleaved with JSON-RPC responses.
    // We search by content rather than relying on fixed line indices.
    var found_42 = false;
    var found_99 = false;
    for (lines) |line| {
        const r = try extractResult(testing.allocator, line);
        defer if (r) |s| testing.allocator.free(s);
        if (r) |val| {
            if (std.mem.eql(u8, val, "42")) found_42 = true;
            if (std.mem.eql(u8, val, "99")) found_99 = true;
        }
    }
    try testing.expect(found_42);
    try testing.expect(found_99);

    // Verify IO output.
    try expectContains(result.stdout, "Hello\n");
    try expectContains(result.stdout, "World\n");
}

test "wasm e2e: multi-equation functions with higher-order arguments" {
    // Regression test: multi-equation function definitions (desugared via
    // the pattern-match compiler) must correctly pass through higher-order
    // function arguments. The desugarer generates `let f = arg_0` bindings
    // to alias lambda parameters to their equation-local names; these must
    // be translated as value aliases (pure), not heap stores.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["identity x = x"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["data List a = Nil | Cons a (List a)"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["map_it _ Nil = Nil\nmap_it f (Cons x xs) = Cons (f x) (map_it f xs)"]}
        \\{"jsonrpc":"2.0","id":5,"method":"eval","params":["head_it (Cons x _) = x"]}
        \\{"jsonrpc":"2.0","id":6,"method":"eval","params":["head_it (map_it identity (Cons 99 Nil))"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    var found_99 = false;
    for (lines) |line| {
        const r = try extractResult(testing.allocator, line);
        defer if (r) |s| testing.allocator.free(s);
        if (r) |val| {
            if (std.mem.eql(u8, val, "99")) found_99 = true;
        }
    }
    try testing.expect(found_99);
}

test "wasm e2e: multi-equation variable pattern preserves literal values" {
    // Regression test: `let n = arg_0` in desugared multi-equation functions
    // must pass through literal values correctly. Previously, all let-bound
    // values were heap-stored, causing literals to appear as `_hptr`.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["f 0 = 42\nf n = n"]}
        \\{"jsonrpc":"2.0","id":3,"method":"eval","params":["f 5"]}
        \\{"jsonrpc":"2.0","id":4,"method":"eval","params":["f 0"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    var found_5 = false;
    var found_42 = false;
    for (lines) |line| {
        const r = try extractResult(testing.allocator, line);
        defer if (r) |s| testing.allocator.free(s);
        if (r) |val| {
            if (std.mem.eql(u8, val, "5")) found_5 = true;
            if (std.mem.eql(u8, val, "42")) found_42 = true;
        }
    }
    try testing.expect(found_5);
    try testing.expect(found_42);
}

// ── Anonymous lambda (issue #501) ────────────────────────────────────────

test "wasm e2e: anonymous lambda in app position (#501)" {
    // Regression test: expression-position lambdas must be lifted and
    // evaluated correctly. Previously panicked with "Unexpected lambda in
    // translateExpr" or produced no output.
    const input =
        \\{"jsonrpc":"2.0","id":1,"method":"init"}
        \\{"jsonrpc":"2.0","id":2,"method":"eval","params":["(\\x -> 1) 2"]}
        \\
    ;
    const result = try runServer(testing.allocator, input);
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);

    const lines = try splitLines(testing.allocator, result.stdout);
    defer testing.allocator.free(lines);

    try testing.expect(lines.len >= 2);

    // The lambda (\x -> 1) ignores its argument and returns 1.
    const r = try extractResult(testing.allocator, lines[1]);
    defer if (r) |s| testing.allocator.free(s);
    try testing.expectEqualStrings("1", r.?);
}
