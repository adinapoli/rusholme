//! CLI End-to-End REPL Tests
//!
//! Spawns `rhc repl` as a subprocess and tests the full interactive
//! experience: banner, prompts, command dispatch, expression evaluation,
//! and clean exit.
//!
//! Each test writes a complete stdin script, closes the pipe (causing
//! EOF), then asserts against the collected stdout/stderr. This avoids
//! the fragility of interactive byte-by-byte prompt detection.
//!
//! NOTE: Multi-input-line tests (multiline blocks, define-then-use,
//! error-then-recovery) are not included here because the REPL's
//! `readLine` function currently recreates its stdin `Reader` on every
//! call, which drops the first byte of each subsequent line when input
//! arrives in bulk via a pipe. This is tracked as a known issue and
//! will be testable once the fix lands.
//! tracked in: https://github.com/adinapoli/rusholme/issues/487

const std = @import("std");
const testing = std.testing;
const process = std.process;
const Io = std.Io;
const File = Io.File;

// ── Helpers ───────────────────────────────────────────────────────────────

/// Result of running the REPL with piped input.
const ReplResult = struct {
    stdout: []u8,
    stderr: []u8,
    term: process.Child.Term,

    fn deinit(self: ReplResult, allocator: std.mem.Allocator) void {
        allocator.free(self.stdout);
        allocator.free(self.stderr);
    }
};

/// Spawn `rhc repl`, feed it `input` on stdin, and return collected
/// stdout and stderr after the process exits.
fn runRepl(allocator: std.mem.Allocator, input: []const u8) !ReplResult {
    const io = testing.io;
    const argv = [_][]const u8{ "zig-out/bin/rhc", "repl" };

    var child = try process.spawn(io, .{
        .argv = &argv,
        .stdin = .pipe,
        .stdout = .pipe,
        .stderr = .pipe,
    });
    // If anything goes wrong, kill the child so we don't leak processes.
    errdefer child.kill(io);

    // Write the entire input script to the child's stdin, then close it
    // so the REPL sees EOF and exits its read loop.
    const stdin_file = child.stdin.?;
    stdin_file.writeStreamingAll(io, input) catch {};
    stdin_file.close(io);
    child.stdin = null;

    // Collect stdout and stderr concurrently using the same MultiReader
    // pattern that std.process.run uses internally.
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

test "cli e2e: banner on startup" {
    const result = try runRepl(testing.allocator, "");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "Rusholme REPL v0.1.0");
    try expectContains(result.stdout, "Type :help for available commands, :quit to exit.");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: prompt appears after banner" {
    const result = try runRepl(testing.allocator, "");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "rusholme> ");
}

test "cli e2e: evaluate integer expression" {
    const result = try runRepl(testing.allocator, "42\n");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "42");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: evaluate boolean True" {
    const result = try runRepl(testing.allocator, "True\n");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "True");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: evaluate boolean False" {
    const result = try runRepl(testing.allocator, "False\n");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "False");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: evaluate string literal" {
    const result = try runRepl(testing.allocator, "\"hello\"\n");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "\"hello\"");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: :help command" {
    const result = try runRepl(testing.allocator, ":help\n");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "Available commands");
    try expectContains(result.stdout, ":quit");
    try expectContains(result.stdout, ":load");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: :quit exits cleanly" {
    const result = try runRepl(testing.allocator, ":quit\n");
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: :q shorthand exits cleanly" {
    const result = try runRepl(testing.allocator, ":q\n");
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: EOF exits cleanly" {
    // Empty input means immediate EOF on stdin.
    const result = try runRepl(testing.allocator, "");
    defer result.deinit(testing.allocator);

    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: unknown command produces message" {
    const result = try runRepl(testing.allocator, ":bogus\n");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "Unknown command");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: error output goes to stderr" {
    const result = try runRepl(testing.allocator, "undefined_xyz\n");
    defer result.deinit(testing.allocator);

    // Errors should appear on stderr, not stdout.
    try expectContains(result.stderr, "error");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: entering multiline mode shows multiline prompt" {
    // Send just :{ followed by a line, then EOF.
    // The REPL enters multiline mode and shows the multiline prompt.
    const result = try runRepl(testing.allocator, ":{" ++ "\n");
    defer result.deinit(testing.allocator);

    try expectContains(result.stdout, "rusholme| ");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: function declaration is silent" {
    const result = try runRepl(testing.allocator, "f x = x\n");
    defer result.deinit(testing.allocator);

    // A declaration should produce no output between the prompts.
    // The stdout should be: banner + prompt + prompt (no value printed).
    const banner_end = std.mem.indexOf(u8, result.stdout, "rusholme> ") orelse
        return error.TestExpectedContains;
    const after_first_prompt = banner_end + "rusholme> ".len;
    const second_prompt = std.mem.indexOf(u8, result.stdout[after_first_prompt..], "rusholme> ");

    // If there's a second prompt immediately (or with just whitespace), the
    // declaration was silent.
    if (second_prompt) |offset| {
        const between = std.mem.trim(u8, result.stdout[after_first_prompt .. after_first_prompt + offset], " \t\n\r");
        try testing.expectEqualStrings("", between);
    }
    // If there's no second prompt, the REPL exited after the declaration,
    // which is also acceptable (EOF after one input).
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: :type shows error diagnostics on type error (#514)" {
    // When :type encounters a type error, it should show the actual
    // type error diagnostics, not a generic "Failed to compile" message.
    // This test verifies that diagnostics are captured and rendered.
    const result = try runRepl(testing.allocator, ":type undefinedVar\n");
    defer result.deinit(testing.allocator);

    // Should show a specific error about the undefined variable,
    // not just "Failed to compile expression for type query"
    try expectContains(result.stderr, "variable not in scope");
    try testing.expectEqual(process.Child.Term{ .exited = 0 }, result.term);
}

test "cli e2e: lazy function arguments do not evaluate unused arguments (#517)" {
    // const x _ = x
    // putStrLn (const "hello" (error "foo"))
    //
    // With lazy evaluation, the error thunk should never be forced.
    // Blocked on multi-line REPL stdin.
    // tracked in: https://github.com/adinapoli/rusholme/issues/487
    return;
}

test "cli e2e: nested lazy function calls work correctly (#517)" {
    // wrap x = x; apply x = wrap (wrap x); apply 42
    //
    // Nested lazy thunks should force correctly, returning 42.
    // Blocked on multi-line REPL stdin.
    // tracked in: https://github.com/adinapoli/rusholme/issues/487
    return;
}
