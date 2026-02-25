//! Native backend - generates native executables via LLVM.
//!
//! This backend compiles GRIN programs to LLVM IR, then emits native
//! object code and links with the Zig runtime system.

const std = @import("std");

const backend_mod = @import("backend_interface.zig");
const grin = @import("../grin/ast.zig");
const grin_to_llvm = @import("grin_to_llvm.zig");
const llvm = @import("llvm.zig");

/// Emit LLVM IR from GRIN program.
const emit = struct {
    fn emit(
        backend: *const anyopaque,
        context: *const backend_mod.EmitContext,
    ) !backend_mod.EmissionResult {
        const self_native: *const NativeBackend = @ptrCast(backend);

        // Translate GRIN to LLVM using existing translator
        var translator = grin_to_llvm.GrinTranslator.init(self_native.allocator);
        defer translator.deinit();

        const llvm_module = try translator.translateProgramToModule(context.grin_program.*);

        // Emit object file using LLVM target machine
        const machine = llvm.createNativeTargetMachine() catch |err| {
            std.log.err("Failed to create target machine: {}", .{err});
            return error.TargetMachineFailed;
        };
        defer llvm.disposeTargetMachine(machine);

        llvm.setModuleDataLayout(llvm_module, machine);
        llvm.setModuleTriple(llvm_module);

        // Emit object file
        const obj_path = context.output_path;
        llvm.emitObjectFile(machine, llvm_module, obj_path) catch |err| {
            std.log.err("Failed to emit object file: {}", .{err});
            return error.EmissionFailed;
        };

        return .{ .object_file = .{
            .path = obj_path,
            .format = .object,
        } };
    }
};

/// Link object files into executable.
const link_link = struct {
    fn link(
        backend: *const anyopaque,
        context: *const backend_mod.LinkContext,
    ) !void {
        _ = backend;
        // Simple linking via zig build-exe
        // System libraries + runtime linking would go here
        // For now, this is a placeholder
        std.log.info("Linking {d} files to {s}", .{ context.emitted_files.len, context.output_name orelse "a.out" });
    }
};

/// Run executable (for the `run` command).
const link_run = struct {
    fn run(
        backend: *const anyopaque,
        context: *const backend_mod.RuntimeContext,
    ) !void {
        _ = backend;
        _ = context;
        // Would execute the program via std.process.Child.exec
        return error.NotImplemented;
    }
};

pub const NativeBackend = struct {
    /// Allocator for runtime allocations.
    allocator: std.mem.Allocator,

    /// Backend struct implementing the vtable operations.
    pub const inner = backend_mod.Backend{
        .kind = .native,
        .name = "native",
        .vtable = .{
            .emit = emit.emit,
            .link = link_link.link,
            .run = link_run.run,
        },
    };

    /// Create a NativeBackend instance.
    pub fn init(allocator: std.mem.Allocator) NativeBackend {
        return .{ .allocator = allocator };
    }

    /// Get the Backend trait reference.
    pub fn asBackend(self: *const NativeBackend) *const backend_mod.Backend {
        return &self.inner;
    }
};

test "NativeBackend: create and get backend reference" {
    const allocator = std.testing.allocator;
    const native = NativeBackend.init(allocator);
    _ = native; // Use value
    try std.testing.expectEqual(backend_mod.BackendKind.native, NativeBackend.inner.kind);
}
