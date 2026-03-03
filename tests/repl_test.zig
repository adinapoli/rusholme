//! REPL integration tests
//!
//! Tests for REPL buffer management and evaluator functionality.

const std = @import("std");
const buffer = @import("../../src/repl/buffer.zig");
const eval = @import("../../src/repl/eval.zig");
const evaluator = @import("../../src/repl/evaluator.zig");

test "repl buffer copying" {
    const input = "test expression";
    const input_buf = buffer.getInputBuffer();

    // Copy test string to input buffer
    for (input, 0..) |c, i| {
        input_buf[i] = c;
    }

    // Verify we can read it back
    try std.testing.expectEqualStrings(input, input_buf[0..input.len]);
}

test "multi-line delimiter stripping" {
    const multiline = ":{\nlet x = 5\n:\}";
    const stripped = eval.stripMultilineDelimiters(multiline);
    const expected = "let x = 5\n";

    try std.testing.expectEqualStrings(expected, stripped);
}

test "evaluator returns non-zero length" {
    const input = "test";
    const result_len = evaluator.evaluate(input);

    // Should produce a response with some length
    try std.testing.expect(result_len > 0);
}

test "evaluator identifier detection" {
    const inputs = [_][]const u8{
        "x",
        "foo_bar",
        "MY_VAR",
    };

    for (inputs) |input| {
        const result_len = evaluator.evaluate(input);
        try std.testing.expect(result_len > 0);
    }
}

test "evaluator number detection" {
    const inputs = [_][]const u8{
        "42",
        "123",
    };

    for (inputs) |input| {
        const result_len = evaluator.evaluate(input);
        try std.testing.expect(result_len > 0);
    }
}
