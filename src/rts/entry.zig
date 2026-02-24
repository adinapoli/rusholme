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
extern fn haskell_main() i32;

// ── Entry Point ───────────────────────────────────────────────────────────

/// Program entry point.
/// Initializes the runtime and calls the Haskell `main` function.
export fn _start() callconv(.C) noreturn {
    // Initialize heap
    heap.init();
    // Call the Haskell main function
    const result = haskell_main();
    // Exit with the result
    std.posix.exit(@intCast(result));
}
