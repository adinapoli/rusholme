//! WebAssembly bridge exports
//!
//! Exports functions that JavaScript can call to interact with the REPL.
//! This is the WASM entry point; the real pipeline integration will be
//! built in src/repl/session.zig (see docs/decisions/0006-repl-architecture.md).

const std = @import("std");

pub const buffer = @import("buffer.zig");
pub const eval = @import("eval.zig");

var initialized = false;

pub fn main() void {
    // No-op main for WASM entry point requirement
}

/// Initialize the REPL
pub export fn repl_init() void {
    if (!initialized) {
        initialized = true;
    }
}

/// Get the input buffer pointer for JavaScript to write into
pub export fn repl_get_input_buffer() [*]u8 {
    return buffer.getInputBuffer();
}

/// Get the output buffer pointer for JavaScript to read from
pub export fn repl_get_output_buffer() [*]u8 {
    return buffer.getOutputBuffer();
}

/// Evaluate a Haskell expression
///
/// Parameters:
///   length - the length of the expression in the input buffer
/// Returns:
///   length - length of JSON result written to output buffer (starts at offset 0)
pub export fn repl_evaluate(length: usize) usize {
    const input = buffer.getInputBuffer()[0..length];
    const output = buffer.getOutputBuffer()[0..16384];

    // Strip multi-line delimiters if present
    const expr = eval.stripMultilineDelimiters(input);

    // Placeholder: echo input back as a message indicating the real
    // pipeline is not yet wired. This will be replaced by the pipeline
    // orchestrator (see docs/decisions/0006-repl-architecture.md).
    const template = "{{\"status\":\"success\",\"value\":\"[REPL not yet connected to pipeline] {s}\"}}";
    const len = (std.fmt.bufPrint(output, template, .{expr}) catch return 0).len;
    return len;
}
