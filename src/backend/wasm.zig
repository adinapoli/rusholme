//! WebAssembly backend stub.
//!
//! Future implementation will compile GRIN programs to WebAssembly binary
//! format (.wasm) for execution in browsers and WASI runtimes.
//!
//! See issues #77–#79 for the planned deliverables.
//!
// tracked in: https://github.com/adinapoli/rusholme/issues/77

const std = @import("std");

const backend_mod = @import("backend_interface.zig");

/// Emit WebAssembly binary (stub – not yet implemented).
// tracked in: https://github.com/adinapoli/rusholme/issues/77
const emit = struct {
    fn emit(
        backend: *const anyopaque,
        context: *const backend_mod.EmitContext,
    ) !backend_mod.EmissionResult {
        _ = backend;
        _ = context;
        return error.UnsupportedOperation;
    }
};

/// Link WebAssembly modules (stub – not yet implemented).
// tracked in: https://github.com/adinapoli/rusholme/issues/77
const link_link = struct {
    fn link(
        backend: *const anyopaque,
        context: *const backend_mod.LinkContext,
    ) !void {
        _ = backend;
        _ = context;
        return error.UnsupportedOperation;
    }
};

/// Run a WebAssembly binary via a WASI runtime (stub – not yet implemented).
// tracked in: https://github.com/adinapoli/rusholme/issues/77
const link_run = struct {
    fn run(
        backend: *const anyopaque,
        context: *const backend_mod.RuntimeContext,
    ) !void {
        _ = backend;
        _ = context;
        return error.UnsupportedOperation;
    }
};

pub const WasmBackend = struct {
    /// Allocator for runtime allocations.
    allocator: std.mem.Allocator,

    /// Backend struct implementing the vtable operations.
    pub const inner = backend_mod.Backend{
        .kind = .wasm,
        .name = "wasm",
        .vtable = .{
            .emit = emit.emit,
            .link = link_link.link,
            .run = link_run.run,
        },
    };

    /// Create a WasmBackend instance.
    pub fn init(allocator: std.mem.Allocator) WasmBackend {
        return .{ .allocator = allocator };
    }

    /// Get the Backend interface reference.
    pub fn asBackend(self: *const WasmBackend) *const backend_mod.Backend {
        _ = self;
        return &inner;
    }
};

test "WasmBackend: create and get backend reference" {
    const allocator = std.testing.allocator;
    const wasm = WasmBackend.init(allocator);
    _ = wasm;
    try std.testing.expectEqual(backend_mod.BackendKind.wasm, WasmBackend.inner.kind);
}
