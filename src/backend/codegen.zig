//! LLVM Codegen Skeleton for issue #54.
//!
//! This module provides the infrastructure for generating LLVM IR from GRIN programs.
//! It focuses on the skeleton: modules, functions, external declarations, and string literals.
//!
//! This is issue #54: LLVM codegen skeleton implementation.

const std = @import("std");
const llvm_module = @import("llvm.zig");

// ═══════════════════════════════════════════════════════════════════════
// Codegen Context
// ═══════════════════════════════════════════════════════════════════════

/// Context for LLVM code generation.
///
/// Holds all the LLVM objects needed for code generation:
/// - LLVM context (memory management)
/// - Module (the IR being built)
/// - Builder (instruction generation)
pub const CodegenContext = struct {
    ctx: llvm_module.Context,
    module: llvm_module.Module,
    builder: llvm_module.Builder,

    /// Initialize a new codegen context.
    pub fn init() CodegenContext {
        llvm_module.initialize();
        const ctx = llvm_module.c.LLVMContextCreate();
        const module = llvm_module.c.LLVMModuleCreateWithName("haskell");
        const builder = llvm_module.c.LLVMCreateBuilder();
        return .{
            .ctx = ctx,
            .module = module,
            .builder = builder,
        };
    }

    /// Deinitialize the codegen context.
    pub fn deinit(self: CodegenContext) void {
        llvm_module.c.LLVMDisposeBuilder(self.builder);
        llvm_module.c.LLVMContextDispose(self.ctx);
    }

    /// Write the generated LLVM IR to a file.
    pub fn writeFile(self: CodegenContext, filename: []const u8) !void {
        try llvm_module.writeModuleToFile(self.module, filename);
    }

    /// Get the LLVM module as a string.
    pub fn toString(self: CodegenContext, allocator: std.mem.Allocator) ![]u8 {
        return llvm_module.printModuleToString(self.module, allocator);
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Function Generation Helpers
// ═══════════════════════════════════════════════════════════════════════

/// Add a function definition to the module.
///
/// Parameters:
///   - ctx: Codegen context
///   - name: Function name (e.g., "main")
///   - return_type: Return type (use llvm_module.voidType() for void)
///   - param_types: Array of parameter types
///
/// Returns the LLVM function value.
pub fn addFunction(
    ctx: *CodegenContext,
    name: []const u8,
    return_type: llvm_module.Type,
    param_types: []const llvm_module.Type,
) llvm_module.Value {
    const fn_type = llvm_module.c.LLVMFunctionType(return_type, @ptrCast(param_types.ptr), @intCast(param_types.len), 0);
    return llvm_module.c.LLVMAddFunction(ctx.module, name, fn_type);
}

/// Add an external function declaration (no body).
///
/// Use this for declaring libc functions like `puts`, `puts` that won't
/// be implemented by our code.
///
/// Parameters:
///   - ctx: Codegen context
///   - name: External function name
///   - return_type: Return type
///   - param_types: Array of parameter types
pub fn addExternalFunction(
    ctx: *CodegenContext,
    name: []const u8,
    return_type: llvm_module.Type,
    param_types: []const llvm_module.Type,
) llvm_module.Value {
    return llvm_module.addExternalDeclaration(ctx.module, name, return_type, param_types);
}

// ═══════════════════════════════════════════════════════════════════════
// Helper Functions
// ═══════════════════════════════════════════════════════════════════════

/// Create a global string constant.
///
/// This creates a global string variable in the module and returns a pointer
/// to it. Useful for string literals like "Hello World!".
///
/// Example:
///   const hello_str = createGlobalString(ctx, "Hello World!\n", "hello_str");
pub fn createGlobalString(ctx: *CodegenContext, string: []const u8, name: []const u8) llvm_module.Value {
    return llvm_module.buildGlobalString(ctx.module, ctx.builder, string, name);
}

/// Get or create the LLVM i64 type.
pub fn i64Type() llvm_module.Type {
    return llvm_module.c.LLVMInt64Type();
}

/// Get or create the LLVM i32 type.
pub fn i32Type() llvm_module.Type {
    return llvm_module.c.LLVMInt32Type();
}

/// Get or create the LLVM i8 type.
pub fn i8Type() llvm_module.Type {
    return llvm_module.c.LLVMInt8Type();
}

/// Get or create the LLVM void type.
pub fn voidType() llvm_module.Type {
    return llvm_module.c.LLVMVoidType();
}

/// Get or create the pointer type for the given element type.
pub fn pointerType(element_type: llvm_module.Type) llvm_module.Type {
    return llvm_module.c.LLVMPointerType(element_type, 0);
}

/// Create a constant integer value.
pub fn constInt(value: i64) llvm_module.Value {
    return llvm_module.c.LLVMConstInt(llvm_module.c.LLVMInt32Type(), @bitCast(@as(u32, @intCast(value))), 1);
}

/// Create a constant null pointer.
pub fn constNull(type_: llvm_module.Type) llvm_module.Value {
    return llvm_module.c.LLVMConstNull(type_);
}
