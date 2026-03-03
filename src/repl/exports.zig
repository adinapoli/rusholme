//! WebAssembly bridge exports
//!
//! Exports functions that JavaScript can call to interact with the REPL.

const std = @import("std");

pub const state = @import("state.zig");
pub const buffer = @import("buffer.zig");

// Module-level state for REPL
var state_instance: state.ReplState = undefined;
var success_callback: *const fn ([]const u8) void = undefined;
var error_callback: *const fn ([]const u8) void = undefined;

/// Initialize the REPL with success and error callbacks
pub export fn repl_init(
    success_cb: *const fn ([]const u8) void,
    error_cb: *const fn ([]const u8) void
) void {
    state_instance = state.ReplState.init(std.heap.page_allocator) catch unreachable;
    success_callback = success_cb;
    error_callback = error_cb;
}

/// Get the input buffer pointer for JavaScript to write into
pub export fn repl_get_input_buffer() [*]u8 {
    return buffer.getInputBuffer();
}

/// Get the output buffer pointer for JavaScript to read from
pub export fn repl_get_output_buffer() [*]u8 {
    return buffer.getOutputBuffer();
}

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "exports function" {
    const success_cb = fn ([]const u8) void;
    const error_cb = fn ([]const u8) void;
    var success_called = false;
    var error_called = false;
    
    const success_wrapper = fn ([]const u8) void {
        success_called = true;
    };
    
    const error_wrapper = fn ([]const u8) void {
        error_called = true;
    };
    
    repl_init(success_wrapper, error_wrapper);
}
