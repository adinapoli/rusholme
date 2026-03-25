//! WebAssembly backend for code generation.
//!
//! Compiles GRIN programs to WebAssembly binary format (.wasm) for
//! execution in browsers and WASI runtimes.
//!
//! See issues #77, #471, #472 for implementation details.
//!
// tracked in: https://github.com/adinapoli/rusholme/issues/77

const std = @import("std");

const backend_mod = @import("backend_interface.zig");
const grin = @import("../grin/ast.zig");
const grin_to_llvm = @import("grin_to_llvm.zig");
const llvm = @import("llvm.zig");

// ═══════════════════════════════════════════════════════════════════════
// Emit
// ═══════════════════════════════════════════════════════════════════════

/// Emit WebAssembly binary from GRIN program.
// tracked in: https://github.com/adinapoli/rusholme/issues/77
const emit = struct {
    fn emit(
        backend: *const anyopaque,
        context: *const backend_mod.EmitContext,
    ) !backend_mod.EmissionResult {
        const self_wasm: *const WasmBackend = @ptrCast(@alignCast(backend));

        // Translate GRIN to LLVM using existing translator
        var registry = grin_to_llvm.TagRegistry.init();
        defer registry.deinit(self_wasm.allocator);
        var translator = grin_to_llvm.GrinTranslator.init(self_wasm.allocator, &registry);
        defer translator.deinit();

        const llvm_module = try translator.translateProgramToModule(context.grin_program.*);

        // Create target machine for WebAssembly (wasm32-wasi)
        const machine = llvm.createWasmTargetMachine() catch |err| {
            std.log.err("Failed to create WebAssembly target machine: {}", .{err});
            return error.TargetMachineFailed;
        };
        defer llvm.disposeTargetMachine(machine);

        // Set module target triple and data layout for WASM
        llvm.setModuleTargetTriple(llvm_module, "wasm32-wasi");
        llvm.setModuleDataLayout(llvm_module, machine);

        // Emit WebAssembly binary
        const wasm_path = context.output_path;
        llvm.emitObjectFile(machine, llvm_module, wasm_path) catch |err| {
            std.log.err("Failed to emit WebAssembly binary: {}", .{err});
            return error.EmissionFailed;
        };

        return .{ .wasm_binary = wasm_path };
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Link
// ═══════════════════════════════════════════════════════════════════════

/// Link WebAssembly modules together.
// tracked in: https://github.com/adinapoli/rusholme/issues/77
const link_link = struct {
    fn link(
        backend: *const anyopaque,
        context: *const backend_mod.LinkContext,
    ) !void {
        _ = backend;
        const allocator = context.allocator;

        // For WASM, linking is typically done at the LLVM level via llvm.linkModules
        // Here we just log the operation for now - actual linking would happen
        // by merging multiple .bc files before emission or using wasm-merge
        std.log.info("Linking {d} WebAssembly modules for output: {s}", .{
            context.emitted_files.len,
            context.output_name orelse "output.wasm",
        });

        // TODO: Implement proper WASM module linking (issue #472)
        // Options include:
        // 1. Use llvm.linkModules to merge bitcode before emission
        // 2. Use wasm-tools/wasm-merge to combine .wasm files
        // 3. Handle system_libs that need to be compiled to WASM (WASI libc)
        _ = allocator;
        _ = context.emitted_files;
        _ = context.system_libs;
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Run
// ═══════════════════════════════════════════════════════════════════════

/// Run a WebAssembly binary via a WASI runtime (not yet implemented).
// tracked in: https://github.com/adinapoli/rusholme/issues/471
const link_run = struct {
    fn run(
        backend: *const anyopaque,
        context: *const backend_mod.RuntimeContext,
    ) !void {
        _ = backend;
        _ = context;
        // WASM runtime execution requires full integration with WASI-compliant runtimes
        // TODO: Issue #471 covers runtime execution
        return error.NotImplemented;
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Backend
// ═══════════════════════════════════════════════════════════════════════

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
