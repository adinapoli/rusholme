//! Thunk evaluator for LLVM-based runtime (issue #56).
//!
//! This module implements thunk evaluation: forcing lazy values to WHNF.

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
        return ptr;
    }

    // Already evaluated, return as-is
    return ptr;
}
