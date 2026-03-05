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
