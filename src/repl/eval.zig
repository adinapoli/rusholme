//! REPL Evaluation Loop
//!
//! Handles parsing, compilation, and evaluation of REPL input.

const std = @import("std");
const buffer = @import("buffer.zig");

/// Strip multiline block delimiters from GHCi-style :{ ... :} blocks
pub fn stripMultilineDelimiters(input: []const u8) []const u8 {
    // Remove leading ":{\n"
    // Remove trailing "\n:}"
    // Return inner content
    if (input.len < 4) return input;
    
    var start: usize = 0;
    var end: usize = input.len;
    
    // Check for ":{"
    if (input[0] == ':' and input[1] == '{') {
        // Skip past newline if present
        start = if (input[2] == '\n') 3 else 2;
    }
    
    // Check for ":}"
    if (input.len >= 2 and input[input.len - 2] == ':' and input[input.len - 1] == '}') {
        end = input.len - 3; // Account for preceding newline if present
        if (end > 0 and input[end - 1] == '\n') {
            end -= 1;
        }
    }
    
    return input[start..end];
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "strip multiline delimiters" {
    const input = ":{\nx\n:}";
    const stripped = stripMultilineDelimiters(input);
    try testing.expectEqualStrings("x", stripped);
}

test "multiline without delimiters" {
    const input = "simple\nline";
    const stripped = stripMultilineDelimiters(input);
    try testing.expectEqualStrings(input, stripped);
}

test "multiline delimiters without newline" {
    const input = ":{x:}";
    const stripped = stripMultilineDelimiters(input);
    try testing.expectEqualStrings("x", stripped);
}

test "multiline delimiters with content" {
    const input = ":{\nidentity x = x\nx\n:}";
    const stripped = stripMultilineDelimiters(input);
    try testing.expectEqualStrings("identity x = x\nx", stripped);
}
