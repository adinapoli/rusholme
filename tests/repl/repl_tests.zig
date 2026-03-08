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

const testing_io = testing.io;

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
