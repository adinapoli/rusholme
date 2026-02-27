//! C source backend stub.
//!
//! Future implementation will emit C source code from GRIN programs,
//! primarily useful for debugging and portability to platforms without
//! LLVM support.

const std = @import("std");

const backend_mod = @import("backend_interface.zig");

/// Emit C source code (stub – not yet implemented).
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

/// Compile and link C source via a system C compiler (stub – not yet implemented).
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

pub const CBackend = struct {
    /// Allocator for runtime allocations.
    allocator: std.mem.Allocator,

    /// Backend struct implementing the vtable operations.
    /// No `run` vtable entry: the C backend is compile-only.
    pub const inner = backend_mod.Backend{
        .kind = .c,
        .name = "c",
        .vtable = .{
            .emit = emit.emit,
            .link = link_link.link,
            .run = null,
        },
    };

    /// Create a CBackend instance.
    pub fn init(allocator: std.mem.Allocator) CBackend {
        return .{ .allocator = allocator };
    }

    /// Get the Backend interface reference.
    pub fn asBackend(self: *const CBackend) *const backend_mod.Backend {
        _ = self;
        return &inner;
    }
};

test "CBackend: create and get backend reference" {
    const allocator = std.testing.allocator;
    const c_backend = CBackend.init(allocator);
    _ = c_backend;
    try std.testing.expectEqual(backend_mod.BackendKind.c, CBackend.inner.kind);
}
