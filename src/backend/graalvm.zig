//! GraalVM/Sulong backend - interprets LLVM bitcode via GraalVM.
//!
//! This backend compiles the Zig runtime to LLVM bitcode and links it
//! with Haskell LLVM IR for execution via GraalVM's lli launcher.

const std = @import("std");

const backend_mod = @import("backend_interface.zig");
const grin = @import("../grin/ast.zig");

/// Zig build-lib command flags for emitting LLVM bitcode.
const ZIG_BITCODE_FLAGS = &[_][]const u8{
    "-femit-llvm-bc",
    "-fno-emit-bin",
    "-O",
    "ReleaseFast",
    "-ofmt=bc",
};

/// Build Zig runtime system as LLVM bitcode for GraalVM.
///
/// This invokes zig build-lib with the appropriate flags to produce
/// a .bc file instead of a native object.
pub fn buildRuntimeBitcode(allocator: std.mem.Allocator, output_path: []const u8) !void {
    var argv_slice = try std.ArrayList([]const u8).initCapacity(allocator, 12);
    defer argv_slice.deinit(allocator);

    // Build the zig command: zig build-lib src/rts/root.zig [flags] -M output
    try argv_slice.append(allocator, "zig");
    try argv_slice.append(allocator, "build-lib");
    try argv_slice.append(allocator, "src/rts/root.zig");

    // Add bitcode emission flags
    for (ZIG_BITCODE_FLAGS) |flag| {
        try argv_slice.append(allocator, flag);
    }

    try argv_slice.append(allocator, "--dep");
    try argv_slice.append(allocator, "rusholme-rts");
    try argv_slice.append(allocator, "-M");
    try argv_slice.append(allocator, output_path);

    var result = try std.process.run(allocator, undefined, .{
        .argv = argv_slice.items,
    });
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    if (@intFromEnum(result.term) != 0) {
        std.log.err("zig build-lib failed:\n{s}", .{result.stderr});
        return error.RTSBuildFailed;
    }
}

/// Link Haskell and Zig bitcode using llvm-link.
pub fn linkBitcode(allocator: std.mem.Allocator, haskell_bc: []const u8, zig_bc: []const u8, output_path: []const u8) !void {
    var argv_slice = try std.ArrayList([]const u8).initCapacity(allocator, 6);
    defer argv_slice.deinit(allocator);

    try argv_slice.append(allocator, "llvm-link");
    try argv_slice.append(allocator, haskell_bc);
    try argv_slice.append(allocator, zig_bc);
    try argv_slice.append(allocator, "-o");
    try argv_slice.append(allocator, output_path);

    var result = try std.process.run(allocator, undefined, .{
        .argv = argv_slice.items,
    });
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    if (@intFromEnum(result.term) != 0) {
        std.log.err("llvm-link failed:\n{s}", .{result.stderr});
        return error.BitcodeLinkFailed;
    }
}

/// Emit LLVM bitcode for execution via Sulong.
const emit = struct {
    fn emit(
        backend: *const anyopaque,
        context: *const backend_mod.EmitContext,
    ) !backend_mod.EmissionResult {
        const self_graalvm: *const GraalVMBackend = @ptrCast(@alignCast(backend));

        // For M1 scope: emit haskell_llvm_to_bc
        // This would call grin_to_llvm.zig translator and then convert to bitcode

        // Placeholder: return the expected bitcode path
        // Real implementation would:
        // 1. Translate GRIN to LLVM IR
        // 2. Use llc -filetype=obj to emit bitcode
        // 3. Build runtime bitcode via zig build-lib
        // 4. Return path to combined bitcode or just the Haskell bitcode

        _ = self_graalvm.allocator;
        _ = context.grin_program;

        return .{ .bitcode = context.output_path };
    }
};

/// Link bitcode files together.
const link_link = struct {
    fn link(
        backend: *const anyopaque,
        context: *const backend_mod.LinkContext,
    ) !void {
        const self_graalvm: *const GraalVMBackend = @ptrCast(@alignCast(backend));

        // Expected context: 2 files - [haskell_program.bc, runtime.bc]
        if (context.emitted_files.len < 2) {
            std.log.err("GraalVM link expected at least 2 files, got {d}", .{context.emitted_files.len});
            return error.InvalidInput;
        }

        const haskell_bc = context.emitted_files[0];
        const runtime_bc = context.emitted_files[1];
        const output_name = context.output_name orelse "graalvm_app.bc";

        // Build runtime bitcode if not already built
        // (In real implementation, check if runtime_bc exists)
        try buildRuntimeBitcode(self_graalvm.allocator, runtime_bc);

        // Link them together
        try linkBitcode(self_graalvm.allocator, haskell_bc, runtime_bc, output_name);

        std.log.info("Linked {s} and {s} into {s}", .{ haskell_bc, runtime_bc, output_name });
    }
};

/// Run bitcode via GraalVM's lli.
const link_run = struct {
    fn run(
        backend: *const anyopaque,
        context: *const backend_mod.RuntimeContext,
    ) !void {
        _ = backend;

        // Invoke lli to execute the bitcode
        // Check GraalVM is available on PATH
        var which_result = try std.process.run(std.heap.page_allocator, undefined, .{
            .argv = &.{ "which", "lli" },
        });
        defer std.heap.page_allocator.free(which_result.stdout);
        defer std.heap.page_allocator.free(which_result.stderr);

        if (@intFromEnum(which_result.term) != 0) {
            return error.GraalVMNotFound;
        }

        // For real execution, would run: lli <executable_path> [args...]
        std.log.info("Would execute: lli {s}", .{context.executable_path});
    }
};

pub const GraalVMBackend = struct {
    /// Allocator for runtime allocations.
    allocator: std.mem.Allocator,

    /// Backend struct implementing the vtable operations.
    pub const inner = backend_mod.Backend{
        .kind = .graalvm,
        .name = "graalvm",
        .vtable = .{
            .emit = emit.emit,
            .link = link_link.link,
            .run = link_run.run,
        },
    };

    /// Create a GraalVMBackend instance.
    pub fn init(allocator: std.mem.Allocator) GraalVMBackend {
        return .{ .allocator = allocator };
    }

    /// Get the Backend trait reference.
    pub fn asBackend(self: *const GraalVMBackend) *const backend_mod.Backend {
        return &self.inner;
    }
};

test "GraalVMBackend: create and get backend reference" {
    const allocator = std.testing.allocator;
    const graalvm = GraalVMBackend.init(allocator);
    _ = graalvm; // Use value
    try std.testing.expectEqual(backend_mod.BackendKind.graalvm, GraalVMBackend.inner.kind);
}
