//! REPL TDD Tests
//!
//! Test-driven development for REPL behavior.
//! Tests are written first, then implementation is fixed to make them pass.

const std = @import("std");
const testing = std.testing;
const rusholme = @import("rusholme");

// Use proper module imports via rusholme
const Session = rusholme.repl.session.Session;
const protocol = rusholme.repl.protocol;
const Status = protocol.Status;
const evaluate = protocol.evaluate;

// For test purposes, we need to provide an io parameter even though
// we don't use it. Use undefined as a placeholder since tests don't
// perform actual I/O operations.
const testing_io: std.Io = undefined;

// ── Test: literal expressions ─────────────────────────────────────────────

test "repl: evaluate integer literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "42") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("42", result.value);
}

test "repl: evaluate string literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "\"hello\"") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("\"hello\"", result.value);
}

test "repl: evaluate boolean literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "True") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("True", result.value);
}

// ── Test: simple declarations ────────────────────────────────────────────

test "repl: define function silently" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    // Declaration should succeed silently
    try testing.expectEqual(Status.silent, result.status);
    try testing.expectEqualStrings("", result.value);
}

test "repl: define then use function" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define id
    const decl_result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use id
    const use_result = evaluate(alloc, &session, "id 42") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, use_result.status);
    try testing.expectEqualStrings("42", use_result.value);
}

// ── Test: IO expressions ─────────────────────────────────────────────────

test "repl: putStrLn \"hello\" returns unit" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Execute putStrLn "hello"
    const result = evaluate(alloc, &session, "putStrLn \"hello\"") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };

    // Should succeed
    try testing.expectEqual(Status.success, result.status);

    // Result value should be unit (empty string for display)
    try testing.expectEqualStrings("", result.value);
}

// ── Integration tests for let-defined functions with IO ───────────────

test "repl: define function then use with putStrLn" {
    // This tests the issue reported: putStrLn (f "hello") where f was defined earlier
    // Previously caused ModuleAddFailed error due to premature context disposal
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define a simple function
    const decl_result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use it with putStrLn
    const use_result = evaluate(alloc, &session, "putStrLn (id \"hello\")") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, use_result.status);
    try testing.expectEqualStrings("", use_result.value);
}

test "repl: multiple function definitions" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define multiple functions
    const decl1 = evaluate(alloc, &session, "f x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl1.status);

    const decl2 = evaluate(alloc, &session, "g y = y") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl2.status);

    // Use both
    const use = evaluate(alloc, &session, "f (g 42)") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.success, use.status);
    try testing.expectEqualStrings("42", use.value);
}

test "repl: function call after declaration accumulates correctly" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("Failed to init session: {}", .{err});
    };
    defer session.deinit();

    // Define identity function
    const decl_result = evaluate(alloc, &session, "id x = x") catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    try testing.expectEqual(Status.silent, decl_result.status);

    // Use it multiple times - each should work without failing
    for ([_]u8{0}**3) |_| {
        const use_result = evaluate(alloc, &session, "id 99") catch |err| {
            std.debug.panic("evaluate failed: {}", .{err});
        };
        try testing.expectEqual(Status.success, use_result.status);
        try testing.expectEqualStrings("99", use_result.value);
    }
}

// ── Test: function composition ───────────────────────────────────────────

test "repl: function composition" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Define increment and double functions
    _ = try evaluate(alloc, &session, "inc x = x + 1");
    _ = try evaluate(alloc, &session, "double x = x * 2");

    // Compose them
    const result = try evaluate(alloc, &session, "double (inc 5)");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("12", result.value);
}

// ── Test: lambda expressions ─────────────────────────────────────────────────

test "repl: lambda expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Use a lambda inline
    const result = try evaluate(alloc, &session, "(\\x -> x) 42");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("42", result.value);
}

test "repl: lambda with complex expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Lambda with arithmetic
    const result = try evaluate(alloc, &session, "(\\x -> x + 10) 5");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("15", result.value);
}

// ── Test: multi-argument functions ───────────────────────────────────────

test "repl: multi-argument function" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Define a binary function
    _ = try evaluate(alloc, &session, "add x y = x + y");

    // Apply it
    const result = try evaluate(alloc, &session, "add 3 4");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("7", result.value);
}

test "repl: multi-argument function with previous bindings" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Define functions and then use them together
    _ = try evaluate(alloc, &session, "square x = x * x");
    _ = try evaluate(alloc, &session, "sumSquares x y = square x + square y");

    const result = try evaluate(alloc, &session, "sumSquares 3 4");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("25", result.value);
}

// ── Test: conditional expressions ────────────────────────────────────────

test "repl: if-then-else true branch" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "if True then 1 else 0");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("1", result.value);
}

test "repl: if-then-else false branch" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "if False then 1 else 0");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("0", result.value);
}

// ── Test: chained function applications ───────────────────────────────────

test "repl: chained function application" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Define a function and apply it multiple times
    _ = try evaluate(alloc, &session, "succ x = x + 1");

    const r1 = try evaluate(alloc, &session, "succ 1");
    try testing.expectEqualStrings("2", r1.value);

    const r2 = try evaluate(alloc, &session, "succ (succ 1)");
    try testing.expectEqualStrings("3", r2.value);

    const r3 = try evaluate(alloc, &session, "succ (succ (succ 1))");
    try testing.expectEqualStrings("4", r3.value);
}

// ── Test: arithmetic operations ─────────────────────────────────────────

test "repl: arithmetic add" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "2 + 3");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("5", result.value);
}

test "repl: arithmetic subtract" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "5 - 2");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("3", result.value);
}

test "repl: arithmetic multiply" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "3 * 4");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("12", result.value);
}

test "repl: arithmetic divide" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "10 / 2");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("5", result.value);
}

test "repl: arithmetic with parentheses" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "(2 + 3) * 4");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("20", result.value);
}

// ── Test: comparison operations ─────────────────────────────────────────

test "repl: equals comparison true" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "5 == 5");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("True", result.value);
}

test "repl: equals comparison false" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "5 == 3");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("False", result.value);
}

// ── Test: error handling for undefined variables ───────────────────────

test "repl: undefined variable causes error" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "undefinedVar");
    try testing.expectEqual(Status.failed, result.status);
    try testing.expect(result.diagnostics.len > 0);
}

// ── Test: session isolation between sessions ────────────────────────────

test "repl: two sessions are independent" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Session 1
    var session1 = try Session.init(alloc, testing_io);
    defer session1.deinit();

    _ = try evaluate(alloc, &session1, "f x = x");
    const r1 = try evaluate(alloc, &session1, "f 42");
    try testing.expectEqualStrings("42", r1.value);

    // Session 2 should be independent
    var session2 = try Session.init(alloc, testing_io);
    defer session2.deinit();

    const r2 = evaluate(alloc, &session2, "f 99");
    try testing.expect(Status.failed == r2.status or Status.silent == r2.status);
    // Either failed (undefined) or succeeded (if f was a builtin in the init env)
}

// ── Test: data declarations ─────────────────────────────────────────────

test "repl: data declaration then use" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Define a simple data type
    _ = try evaluate(alloc, &session, "data Pair = Pair Int Int");

    // Use one of its constructors
    const result = try evaluate(alloc, &session, "Pair 1 2");
    try testing.expectEqual(Status.success, result.status);
    try testing.expect(result.value.len > 0);
}

test "repl: multiple data declarations" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Define multiple data types
    _ = try evaluate(alloc, &session, "data Maybe = Just Int | Nothing");
    _ = try evaluate(alloc, &session, "data Either = Left Bool | Right Int");

    // Use constructors from both
    const r1 = try evaluate(alloc, &session, "Just 42");
    try testing.expectEqual(Status.success, r1.status);

    const r2 = try evaluate(alloc, &session, "Right 99");
    try testing.expectEqual(Status.success, r2.status);
}

// ── Test: arithmetic with defined functions ─────────────────────────────

test "repl: arithmetic with defined function" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // Define a function and use in arithmetic
    _ = try evaluate(alloc, &session, "f x = x * 2");

    const result = try evaluate(alloc, &session, "f 5 + 1");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("11", result.value);
}

// ── Test: nesting function calls ───────────────────────────────────────

test "repl: nested function calls" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    _ = try evaluate(alloc, &session, "f x = x + 1");

    const result = try evaluate(alloc, &session, "f (f (f 0))");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("3", result.value);
}

// ── Test: negative numbers ─────────────────────────────────────────────

test "repl: negative number literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "-5");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("-5", result.value);
}

test "repl: arithmetic with negative numbers" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const r1 = try evaluate(alloc, &session, "-5 + 10");
    try testing.expectEqualStrings("5", r1.value);

    const r2 = try evaluate(alloc, &session, "5 + -3");
    try testing.expectEqualStrings("2", r2.value);
}

// ── Test: boolean literal variants ──────────────────────────────────────

test "repl: lowercase true literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "true");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("True", result.value);
}

test "repl: lowercase false literal" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "false");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("False", result.value);
}

// ── Test: string operations ────────────────────────────────────────────

test "repl: string literal with special characters" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "\"hello world\"");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("\"hello world\"", result.value);
}

// ── Test: function with boolean argument ────────────────────────────────

test "repl: function with boolean argument" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    _ = try evaluate(alloc, &session, "not b = if b then False else True");

    const result = try evaluate(alloc, &session, "not True");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("False", result.value);
}

// ── Test: complex arithmetic expressions ────────────────────────────────

test "repl: complex nested arithmetic" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = try evaluate(alloc, &session, "(1 + 2) * (3 + 4) - 5");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("19", result.value);
}

// ── Test: empty input handling ──────────────────────────────────────────

test "repl: error on empty input" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    const result = evaluate(alloc, &session, "");
    // Empty input should fail
    try testing.expect(Status.failed == result.status or Status.silent == result.status);
}

// ── Test: error messages persist ────────────────────────────────────────

test "repl: errors persist across evaluations" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    // First, a valid evaluation
    _ = try evaluate(alloc, &session, "42");

    // Then an error
    const err = try evaluate(alloc, &session, "undefined_var");
    try testing.expectEqual(Status.failed, err.status);
    try testing.expect(err.diagnostics.len > 0);

    // Another valid evaluation should work
    const valid = try evaluate(alloc, &session, "99");
    try testing.expectEqual(Status.success, valid.status);
}

// ── Test: pattern matching with data constructors ─────────────────────────

test "repl: use constructor from data decl" {
    var arena = std.heap.AreaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    _ = try evaluate(alloc, &session, "data Opt = Some Int | None");

    const result = try evaluate(alloc, &session, "Some 10");
    try testing.expectEqual(Status.success, result.status);
}

// ── Test: multiple uses of same function in session ────────────────────

test "repl: same function used multiple ways" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    _ = try evaluate(alloc, &session, "add x y = x + y");

    const r1 = try evaluate(alloc, &session, "add 1 2");
    try testing.expectEqualStrings("3", r1.value);

    const r2 = try evaluate(alloc, &session, "add (add 1 2) 3");
    try testing.expectEqualStrings("6", r2.value);

    const r3 = try evaluate(alloc, &session, "add 1 (add 2 3)");
    try testing.expectEqualStrings("6", r3.value);
}

// ── Test: expression with multiple levels ───────────────────────────────

test "repl: deeply nested function calls" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = Session.init(alloc, testing_io) catch |err| {
        std.debug.panic("evaluate failed: {}", .{err});
    };
    defer session.deinit();

    _ = try evaluate(alloc, &session, "add x y = x + y");

    const result = try evaluate(alloc, &session, "add (add (add 1 2) 3) 4");
    try testing.expectEqual(Status.success, result.status);
    try testing.expectEqualStrings("10", result.value);
}
