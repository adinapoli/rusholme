//! WASM REPL entry point.
//!
//! This file exists at the `src/` level so that the REPL pipeline
//! modules can resolve their `../frontend/`, `../grin/`, etc. relative
//! imports. It re-exports everything from `repl/exports.zig`.
//!
//! The `pub export` functions in exports.zig are visible to the linker
//! as long as that module is referenced. The `comptime` block forces
//! the reference.

const exports = @import("repl/exports.zig");

comptime {
    // Force the linker to see the `pub export` symbols.
    _ = &exports.repl_init;
    _ = &exports.repl_get_input_buffer;
    _ = &exports.repl_get_output_buffer;
    _ = &exports.repl_evaluate;
    _ = &exports.repl_server_run;
    _ = &exports.repl_process_jsonrpc;
}

pub fn main() void {}
