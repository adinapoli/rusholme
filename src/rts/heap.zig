//! Heap allocator for LLVM-based runtime (issue #56).
//!
//! This module provides the heap management for the runtime system.
//! For M1, we use ArenaAllocator (no GC - memory grows until program exits).

const std = @import("std");

// ═══════════════════════════════════════════════════════════════════════
// Global Arena Allocator
// ═══════════════════════════════════════════════════════════════════════

/// Global heap state.
/// Using threadlocal static variables for proper initialization.
const State = struct {
    var gpa: std.heap.ArenaAllocator = undefined;
    var initialized: bool = false;

    fn get() *std.heap.ArenaAllocator {
        if (!initialized) {
            gpa = std.heap.ArenaAllocator.init(std.heap.page_allocator);
            initialized = true;
        }
        return &gpa;
    }
};

/// Initialize the heap allocator.
pub fn init() void {
    _ = State.get();
}

/// Cleanup the heap allocator.
pub fn deinit() void {
    if (State.initialized) {
        State.gpa.deinit();
        State.initialized = false;
    }
}

/// Get the heap allocator.
pub fn allocator() std.mem.Allocator {
    return State.get().allocator();
}

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "init/deinit heap" {
    init();
    defer deinit();

    // Should be able to get allocator
    _ = allocator();
}

