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
//! - : Runtime value representation (heap objects, literals, etc.)
//! - : IO primitives (writeStdout, readStdin, etc.)
//! - : Arithmetic primitives (add, sub, mul, etc.)
//! - : GRIN evaluator with PrimOp dispatch
//!
//! ## Known Shortcomings (Being Tracked)
//!
//! The initial runtime implementation (issue #56) serves as a minimal skeleton.
//! Many features are placeholders with follow-up issues:
//!
//! - **Thunk evaluation**: https://github.com/adinapoli/rusholme/issues/384
//! - **Heap node field storage**: https://github.com/adinapoli/rusholme/issues/385
//! - **Closure support**: https://github.com/adinapoli/rusholme/issues/386
//!
//! Reference: docs/decisions/0001-primops-and-rts-architecture.md

const std = @import("std");

pub const value = @import("value.zig");
pub const io = @import("io.zig");
pub const arith = @import("arith.zig");
pub const eval = @import("eval.zig");
pub const string = @import("string.zig");

// Re-export commonly used types
pub const Value = value.Value;
pub const EvalError = value.EvalError;
pub const Heap = value.Heap;
pub const EvalContext = eval.EvalContext;
pub const evalPrimOp = eval.evalPrimOp;

// ── Tests ────────────────────────────────────────────────────────────────

test {
    const testing = std.testing;
    testing.refAllDecls(@This());
}
