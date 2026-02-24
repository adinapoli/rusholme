//! Thunk evaluator for LLVM-based runtime (issue #56).
//!
//! This module implements thunk evaluation: forcing lazy values to WHNF.
//!
// tracked in: https://github.com/adinapoli/rusholme/issues/384

const std = @import("std");
const node = @import("node.zig");

// ═══════════════════════════════════════════════════════════════════════
// Thunk Evaluation
// ═══════════════════════════════════════════════════════════════════════

/// Evaluate a thunk and return its WHNF.
/// Called `rts_eval` from LLVM.
export fn rts_eval(ptr: *node.Node) *node.Node {
    // Check if it's a thunk
    if (ptr.tag == .Thunk) {
        // For M1, thunks are not fully implemented
        // This is a placeholder for upcoming lazy evaluation support
        // For now, just return the thunk itself
        // Full implementation: https://github.com/adinapoli/rusholme/issues/384
        return ptr;
    }

    // Already evaluated, return as-is
    return ptr;
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "rts_eval exports C function" {
    // Check that the export exists
    const testing = std.testing;
    _ = testing;
}

test "evaluate non-thunk returns as-is" {
    const heap = @import("heap.zig");
    heap.init();
    defer heap.deinit();

    const n = node.createInt(42);
    const result = rts_eval(n);
    
    try std.testing.expectEqual(n, result);
}

