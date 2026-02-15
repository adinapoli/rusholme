//! LLVM C API bindings for code generation.
//!
//! This module provides Zig bindings to the LLVM-C API using Zig's
//! @cImport to directly import LLVM headers.

const std = @import("std");

// Import LLVM-C API headers
const llvm_c = @cImport({
    @cInclude("llvm-c/Core.h");
    @cInclude("llvm-c/Target.h");
    @cInclude("llvm-c/TargetMachine.h");
    @cInclude("llvm-c/IRReader.h");
    @cInclude("llvm-c/Linker.h");
});

pub const c = llvm_c;

/// Context is an execution context for LLVM operations.
/// It owns and manages the memory of all LLVM objects created from it.
pub const Context = *c.LLVMContext;

/// Module represents a single translation unit in LLVM IR.
pub const Module = *c.LLVMModule;

/// Builder provides a uniform interface for generating instructions.
pub const Builder = *c.LLVMBuilder;

/// Value represents a value in LLVM IR (constants, instructions, etc.).
pub const Value = *c.LLVMValue;

/// Type represents the type of an LLVM value.
pub const Type = *c.LLVMType;

/// BasicBlock represents a basic block of instructions.
pub const BasicBlock = *c.LLVMBasicBlock;

/// ExecutionEngine provides JIT compilation and execution capabilities.
pub const ExecutionEngine = *c.LLVMExecutionEngine;

/// PassManager manages optimization passes.
pub const PassManager = *c.LLVMPassManager;

/// Target represents a target architecture.
pub const Target = *c.LLVMTarget;

/// TargetMachine represents a specific target configuration.
pub const TargetMachine = *c.LLVMTargetMachine;

/// Initialize LLVM.
/// Must be called before using any LLVM functions.
pub fn initialize() void {
    llvm_c.LLVMInitializeAllTargetInfos();
    llvm_c.LLVMInitializeAllTargets();
    llvm_c.LLVMInitializeAllTargetMCs();
    llvm_c.LLVMInitializeAllAsmParsers();
    llvm_c.LLVMInitializeAllAsmPrinters();
}

/// Create a new LLVM context.
pub fn createContext() Context {
    return llvm_c.LLVMContextCreate();
}

/// Dispose of a context and all its objects.
pub fn disposeContext(context: Context) void {
    llvm_c.LLVMContextDispose(context);
}

/// Create a new module with the given name.
pub fn createModule(name: []const u8, context: Context) Module {
    const name_c = tryToNullTerminated(name);
    defer std.heap.raw_c_allocator.free(name_c);
    return llvm_c.LLVMModuleCreateWithNameInContext(name_c, context);
}

/// Create a new IR builder.
pub fn createBuilder(context: Context) Builder {
    return llvm_c.LLVMCreateBuilderInContext(context);
}

/// Dispose of a builder.
pub fn disposeBuilder(builder: Builder) void {
    llvm_c.LLVMDisposeBuilder(builder);
}

/// Create an entry point basic block for a function.
pub fn appendBasicBlock(function: Value, name: []const u8) BasicBlock {
    const name_c = tryToNullTerminated(name);
    defer std.heap.raw_c_allocator.free(name_c);
    return llvm_c.LLVMAppendBasicBlock(function, name_c);
}

/// Position the builder at the end of the specified block.
pub fn positionBuilderAtEnd(builder: Builder, block: BasicBlock) void {
    llvm_c.LLVMPositionBuilderAtEnd(builder, block);
}

/// Create a function type.
/// params: array of parameter types (or null for varargs)
/// is_varargs: true if the function takes variable arguments
pub fn functionType(return_type: Type, params: []const Type, is_varargs: bool) Type {
    return llvm_c.LLVMFunctionType(return_type, @ptrCast(params.ptr), @intCast(params.len), @intFromBool(is_varargs));
}

/// Add a function to a module.
pub fn addFunction(module: Module, name: []const u8, function_type: Type) Value {
    const name_c = tryToNullTerminated(name);
    defer std.heap.raw_c_allocator.free(name_c);
    return llvm_c.LLVMAddFunction(module, name_c, function_type);
}

/// Get the name of a value.
pub fn getValueName(value: Value) []const u8 {
    const length = llvm_c.LLVMGetValueName2(value, null, 0);
    if (length == 0) return &.{};
    const name = std.heap.raw_c_allocator.allocSentinel(u8, length, 0) catch return &.{};
    llvm_c.LLVMGetValueName2(value, name.ptr, length);
    return name;
}

/// Set the name of a value.
pub fn setValueName(value: Value, name: []const u8) void {
    llvm_c.LLVMSetValueName2(value, name.ptr, name.len);
}

/// Create an i32 constant.
pub fn constInt32(value: i32) Value {
    return llvm_c.LLVMConstInt(llvm_c.LLVMInt32Type(), @bitCast(@as(u32, @intCast(value))), 1);
}

/// Create a void constant (unit type).
pub fn constVoid() Value {
    return llvm_c.LLVMGetUndef(llvm_c.LLVMVoidType());
}

/// Print LLVM IR to stdout.
pub fn dumpModule(module: Module) void {
    llvm_c.LLVMDumpModule(module);
}

/// Write a module to a string.
pub fn printModuleToString(module: Module, allocator: std.mem.Allocator) ![]u8 {
    const str = llvm_c.LLVMPrintModuleToString(module);
    defer llvm_c.LLVMDisposeMessage(str);
    return allocator.dupeZ(u8, std.mem.span(str));
}

/// Create a return instruction.
pub fn buildRet(builder: Builder, value: Value) Value {
    return llvm_c.LLVMBuildRet(builder, value);
}

/// Create a void return instruction.
pub fn buildRetVoid(builder: Builder) Value {
    return llvm_c.LLVMBuildRetVoid(builder);
}

/// Create an add instruction.
pub fn buildAdd(builder: Builder, lhs: Value, rhs: Value, name: []const u8) Value {
    const name_c = tryToNullTerminated(name);
    defer std.heap.raw_c_allocator.free(name_c);
    return llvm_c.LLVMBuildAdd(builder, lhs, rhs, name_c);
}

/// Create a call instruction.
pub fn buildCall(builder: Builder, function: Value, args: []const Value, name: []const u8) Value {
    const name_c = tryToNullTerminated(name);
    defer std.heap.raw_c_allocator.free(name_c);
    return llvm_c.LLVMBuildCall2(builder, llvm_c.LLVMGetFunctionType(function), function, @ptrCast(args.ptr), @intCast(args.len), name_c);
}

/// Convert a slice to a null-terminated string.
fn tryToNullTerminated(s: []const u8) [:0]const u8 {
    const result = std.heap.raw_c_allocator.allocSentinel(u8, s.len, 0) catch @panic("OOM");
    @memcpy(result, s);
    return @ptrCast(result);
}
