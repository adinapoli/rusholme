//! Backend module - code generation and execution targets.
//!
//! This is the top-level aggregator for all backend-related code.
//! It includes both the core backend infrastructure (from PR #57) and
//! the multi-backend trait interface (from PR #335).
//!
//! Usage:
//!   // Core LLVM codegen (from main)
//!   const llvm = rusholme.backend.llvm;
//!   const grin_to_llvm = rusholme.backend.grin_to_llvm;
//!   const linker = rusholme.backend.linker;
//!
//!   // Multi-backend trait interface (from #335)
//!   const_backend_mod = rusholme.backend.backend_mod;
//!   const native = rusholme.backend.native;
//!   const graalvm = rusholme.backend.graalvm;

// ═══════════════════════════════════════════════════════════════════════
// Core Backend Infrastructure (from PR #57)
// ═══════════════════════════════════════════════════════════════════════

/// LLVM C API bindings for code generation.
pub const llvm = @import("backend/llvm.zig");

/// GRIN-to-LLVM IR Translator.
pub const grin_to_llvm = @import("backend/grin_to_llvm.zig");

/// Native linker for object code → executable.
pub const linker = @import("backend/linker.zig");

/// LLVM codegen skeleton (issue #54).
pub const codegen = @import("backend/codegen.zig");

// ═══════════════════════════════════════════════════════════════════════
// Multi-Backend Trait Interface (from PR #335)
// ═══════════════════════════════════════════════════════════════════════

/// Backend trait for multi-target code generation.
///
/// Defines the abstraction layer for pluggable backends
/// (native, GraalVM, WebAssembly, C, etc.).
pub const backend_mod = @import("backend/backend_trait.zig");

/// Native LLVM backend implementation.
pub const native = @import("backend/native.zig");

/// GraalVM/Sulong backend implementation.
pub const graalvm = @import("backend/graalvm.zig");

// ═══════════════════════════════════════════════════════════════════════
// Test discovery
// ═══════════════════════════════════════════════════════════════════════

test {
    @import("std").testing.refAllDecls(@This());
    @import("std").testing.refAllDecls(llvm);
    @import("std").testing.refAllDecls(grin_to_llvm);
    @import("std").testing.refAllDecls(linker);
    @import("std").testing.refAllDecls(backend_mod);
    @import("std").testing.refAllDecls(native);
    @import("std").testing.refAllDecls(graalvm);
}
