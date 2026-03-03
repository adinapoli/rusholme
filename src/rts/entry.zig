//! Entry point for LLVM-based runtime (issue #56).
//!
//! This module defines the program entry point that the OS calls.
//! It initializes the runtime and calls the Haskell `main` function.

const std = @import("std");
const heap = @import("heap.zig");
const node = @import("node.zig");

// ── External Haskell main function ────────────────────────────────────────

/// External Haskell main function.
/// This will be provided by the LLVM-generated code.
extern fn main() i32;

// ── Entry Point (WASM-only) ─────────────────────────────────────────────────

// For WASM/WASI targets, _start gets called when the module is instantiated.
// For native targets, the system provides _start from crt1.o.
//
// NOTE: This function is only included for WASM builds (via the root.zig
// conditional import).

pub export fn _start() noreturn {
    heap.init();
    const result = main();
    std.process.exit(@intCast(result));
}
