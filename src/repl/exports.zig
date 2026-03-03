//! WebAssembly bridge exports
//!
//! Exports functions that JavaScript can call to interact with the REPL.

const std = @import("std");

pub const state = @import("state.zig");
pub const buffer = @import("buffer.zig");
pub const eval = @import("eval.zig");
pub const evaluator = @import("evaluator.zig");

// Module-level state for REPL
var state_instance: state.ReplState = undefined;
var initialized = false;

pub fn main() void {
    // No-op main for WASM entry point requirement
}

/// Initialize the REPL
pub export fn repl_init() void {
    if (!initialized) {
        state_instance = state.ReplState.init(std.heap.page_allocator);
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

    // Use evaluator module for actual evaluation
    return evaluator.evaluate(input);
}
