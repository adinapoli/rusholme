//! Backend trait for multi-target code generation.
//!
//! This module defines the abstraction layer for different backends
//! (native, GraalVM, WebAssembly, C, etc.). Each backend implements
//! the Backend vtable with emit/link/run operations.
//!
//! See `docs/sulong-architecture.md` for full design details.

const std = @import("std");

const grin = @import("../grin/ast.zig");

// ═══════════════════════════════════════════════════════════════════════
// Backend Kind
// ═══════════════════════════════════════════════════════════════════════

/// Supported backend targets.
pub const BackendKind = enum {
    /// Native executable via LLVM (default, current implementation).
    native,

    /// GraalVM/Sulong interpreter (LLVM bitcode).
    graalvm,

    /// WebAssembly (future, issues #77-#79).
    wasm,

    /// C source output (for debugging).
    c,
};

/// Display name for each backend kind.
pub fn backendName(kind: BackendKind) []const u8 {
    return switch (kind) {
        .native => "native",
        .graalvm => "graalvm",
        .wasm => "wasm",
        .c => "c",
    };
}

/// Parse backend name string to enum.
pub fn parseBackendKind(name: []const u8) ?BackendKind {
    if (std.mem.eql(u8, name, "native")) return .native;
    if (std.mem.eql(u8, name, "graalvm")) return .graalvm;
    if (std.mem.eql(u8, name, "wasm")) return .wasm;
    if (std.mem.eql(u8, name, "c")) return .c;
    return null;
}

// ═══════════════════════════════════════════════════════════════════════
// Backend Contexts
// ═══════════════════════════════════════════════════════════════════════

/// Context for backend emission operations.
pub const EmitContext = struct {
    /// The GRIN program to emit.
    grin_program: *const grin.Program,

    /// Output path for the emitted file.
    output_path: []const u8,

    /// Allocator for temporary allocations.
    allocator: std.mem.Allocator,
};

/// Context for backend linking operations.
pub const LinkContext = struct {
    /// List of emitted files to link together.
    emitted_files: []const []const u8,

    /// User-specified output filename (without extension).
    /// If null, derive from source file.
    output_name: ?[]const u8,

    /// System libraries to link against.
    system_libs: []const []const u8,

    /// Allocator for temporary allocations.
    allocator: std.mem.Allocator,
};

/// Context for backend run/execution operations.
pub const RuntimeContext = struct {
    /// Path to the executable/bitcode to run.
    executable_path: []const u8,

    /// Command-line arguments to pass.
    args: []const []const u8,

    /// Standard io handle.
    io: std.Io,
};

// ═══════════════════════════════════════════════════════════════════════
// Emission Result
// ═══════════════════════════════════════════════════════════════════════

/// Result of backend emission.
pub const EmissionResult = union(enum) {
    /// Object file (.o) with format specified.
    object_file: ObjectFile,

    /// LLVM bitcode (.bc).
    bitcode: []const u8,

    /// WebAssembly binary (.wasm).
    wasm_binary: []const u8,

    /// C source (.c).
    c_source: []const u8,
};

/// Object file format.
pub const ObjectFile = struct {
    /// Path to the generated object file.
    path: []const u8,

    /// Format of the object file.
    format: ObjectFormat,
};

pub const ObjectFormat = enum {
    /// Native object file (.o, COFF, etc.).
    object,

    /// LLVM bitcode (.bc).
    bitcode,

    /// WebAssembly module (.wasm).
    wasm,

    /// C source (.c).
    c_source,
};

// ═══════════════════════════════════════════════════════════════════════
// Backend VTable
// ═══════════════════════════════════════════════════════════════════════

/// Virtual table of backend operations.
///
/// Each backend implements this vtable to provide its own emit/link/run
/// behavior. The `run` function pointer is optional (null for compile-only
/// backends like C).
pub const VTable = struct {
    /// Emit backend-specific output from a GRIN program.
    ///
    /// Arguments:
    ///   - backend: pointer to the backing backend struct (for downcasting)
    ///   - context: emission configuration and GRIN program
    ///
    /// Returns emission result or error.
    emit: *const fn (backend: *const anyopaque, context: *const EmitContext) anyerror!EmissionResult,

    /// Link emitted units into final output.
    ///
    /// Arguments:
    ///   - backend: pointer to the backing backend struct
    ///   - context: linking configuration (files, output, libraries)
    link: *const fn (backend: *const anyopaque, context: *const LinkContext) anyerror!void,

    /// Execute/run the program (optional - null for compile-only backends).
    ///
    /// Arguments:
    ///   - backend: pointer to the backing backend struct
    ///   - context: runtime configuration (executable, args)
    ///
    /// Only present for backends that support execution.
    run: ?*const fn (backend: *const anyopaque, context: *const RuntimeContext) anyerror!void = null,
};

// ═══════════════════════════════════════════════════════════════════════
// Backend Trait
// ═══════════════════════════════════════════════════════════════════════

/// Backend trait - abstract interface for code generation targets.
///
/// Usage pattern:
///
/// ```zig
/// const native_backend = backend.NativeBackend{ ... };
/// const b = backend.Backend{
///     .kind = .native,
///     .name = "native",
///     .vtable = .{
///         .emit = native_backend.emit,
///         .link = native_backend.link,
///         .run = native_backend.run,
///     },
/// };
/// ```
///
/// Each backend struct (NativeBackend, GraalVMBackend, etc.) should:
/// 1. Embed Backend as its first field (or in a known position)
/// 2. Implement the vtable functions with @ptrCast to the concrete type
pub const Backend = struct {
    /// Kind of backend (native, graalvm, wasm, c).
    kind: BackendKind,

    /// Human-readable name.
    name: []const u8,

    /// Virtual table of operations.
    vtable: VTable,
};

// ═══════════════════════════════════════════════════════════════════════
// Error Types
// ═══════════════════════════════════════════════════════════════════════

/// Errors that can occur during backend operations.
pub const Error = error{
    /// Generic emission failure.
    EmissionFailed,

    /// Generic linking failure.
    LinkFailed,

    /// Generic execution failure.
    ExecutionFailed,

    /// System I/O error.
    IoError,

    /// Out of memory.
    OutOfMemory,

    /// Unsupported operation for this backend.
    UnsupportedOperation,
};

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "backendName" {
    try std.testing.expectEqualStrings("native", backendName(.native));
    try std.testing.expectEqualStrings("graalvm", backendName(.graalvm));
    try std.testing.expectEqualStrings("wasm", backendName(.wasm));
    try std.testing.expectEqualStrings("c", backendName(.c));
}

test "parseBackendKind" {
    try std.testing.expect(parseBackendKind("native").? == .native);
    try std.testing.expect(parseBackendKind("graalvm").? == .graalvm);
    try std.testing.expect(parseBackendKind("wasm").? == .wasm);
    try std.testing.expect(parseBackendKind("c").? == .c);
    try std.testing.expect(parseBackendKind("unknown") == null);
}

test "BackendKind enum values" {
    try std.testing.expectEqual(@intFromEnum(BackendKind.native), 0);
    try std.testing.expectEqual(@intFromEnum(BackendKind.graalvm), 1);
    try std.testing.expectEqual(@intFromEnum(BackendKind.wasm), 2);
    try std.testing.expectEqual(@intFromEnum(BackendKind.c), 3);
}

test "ObjectFormat enum values" {
    try std.testing.expectEqual(@intFromEnum(ObjectFormat.object), 0);
    try std.testing.expectEqual(@intFromEnum(ObjectFormat.bitcode), 1);
    try std.testing.expectEqual(@intFromEnum(ObjectFormat.wasm), 2);
    try std.testing.expectEqual(@intFromEnum(ObjectFormat.c_source), 3);
}
