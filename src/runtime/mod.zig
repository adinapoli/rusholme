//! Runtime System (RTS) for Rusholme.
//!
//! The RTS provides the execution environment for compiled Haskell programs.
//! It implements:
//!
//! - **PrimOp execution**: The primitive operations that high-level code calls
//! - **Memory management**: Heap allocation and garbage collection
//! - **IO subsystem**: Interaction with the outside world
//! - **FFI bridge**: Calling foreign (C) functions
//!
//! ## Architecture
//!
//! The RTS is organized into modules:
//!
//! - `value`: Runtime value representation (heap objects, literals, etc.)
//! - `io`: IO primitives (writeStdout, readStdin, etc.)
//! - `arith`: Arithmetic primitives (add, sub, mul, etc.)
//!
//! Reference: docs/decisions/0001-primops-and-rts-architecture.md

const std = @import("std");

pub const value = @import("value.zig");
pub const io = @import("io.zig");
pub const arith = @import("arith.zig");

// Re-export commonly used types
pub const Value = value.Value;
pub const EvalError = value.EvalError;
pub const Heap = value.Heap;

// ── Tests ────────────────────────────────────────────────────────────────

test {
    const testing = std.testing;
    testing.refAllDecls(@This());
}
