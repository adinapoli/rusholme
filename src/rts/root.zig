//! Root module for LLVM-based runtime (issue #56).
//!
//! This module re-exports all runtime submodules and forces compilation
//! of all exported RTS functions. Zig only compiles what's referenced,
//! so we must explicitly reference the export functions to ensure they
//! are included in the static library.

const std = @import("std");
const builtin = @import("builtin");

pub const heap = @import("heap.zig");
pub const io_module = @import("io.zig");
pub const eval = @import("eval.zig");
pub const node = @import("node.zig");

// Only export entry for WASM targets
pub const entry = if (builtin.target.os.tag == .wasi) @import("entry.zig") else struct {};

// Force compilation of all exported RTS functions by taking their addresses.
// This ensures they are included in the static library even though nothing
// in the Zig code calls them (they're called from LLVM-generated code).
comptime {
    _ = &node.rts_alloc;
    _ = &node.rts_store_field;
    _ = &node.rts_load_field;
    _ = &node.rts_store;
    _ = &io_module.rts_putStrLn;
    _ = &io_module.rts_putStr;
    _ = &io_module.rts_error;
    _ = &heap.init;
    _ = &heap.deinit;
    _ = &heap.allocator;
    
    // For WASM targets, also force compilation of the _start entry point
    // to allow automatic execution when the module is instantiated
    if (builtin.target.os.tag == .wasi) {
        _ = &entry._start;
    }
}
