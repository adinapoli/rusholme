//! Runtime test runner for issue #56 tests.
//!
//! This module runs tests for the LLVM-based runtime (src/rts/).
//! These tests require C headers/libc and should be run via `nix develop`.

const std = @import("std");

// Import from the rusholme runtime module (defined in build.zig)
const runtime = @import("runtime");

// Get submodules from runtime
const heap = runtime.heap;
const io = runtime.io_module;
const eval = runtime.eval;
const node = runtime.node;

test {
    // The runtime modules have inline test blocks
    // Using refAllDecls ensures those tests are discovered
    std.testing.refAllDecls(heap);
    std.testing.refAllDecls(io);
    std.testing.refAllDecls(eval);
    std.testing.refAllDecls(node);
}
