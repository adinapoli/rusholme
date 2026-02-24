//! Root module for LLVM-based runtime (issue #56).
//!
//! This module re-exports all runtime submodules.

pub const heap = @import("heap.zig");
pub const io_module = @import("io.zig");
pub const eval = @import("eval.zig");
pub const node = @import("node.zig");
pub const entry = @import("entry.zig");
