//! Tests for LLVM codegen skeleton (issue #54).
//!
//! This module tests the LLVM code generation skeleton infrastructure.

const std = @import("std");
const llvm = @import("llvm.zig");
const codegen = @import("codegen.zig");

test "codegen skeleton: create context and module" {
    var ctx = codegen.CodegenContext.init();
    defer ctx.deinit();

    // Verify the context was created
    try std.testing.expect(ctx.ctx != null);
    try std.testing.expect(ctx.module != null);
    try std.testing.expect(ctx.builder != null);
}

test "codegen skeleton: add empty function" {
    var ctx = codegen.CodegenContext.init();
    defer ctx.deinit();

    const void_ty = codegen.voidType();
    const main_fn = codegen.addFunction(&ctx, "main", void_ty, &.{});

    try std.testing.expect(main_fn != null);

    // Verify it has an entry block
    const entry = llvm.c.LLVMAppendBasicBlock(main_fn, "entry");
    try std.testing.expect(entry != null);

    // Verify we can retrieve the function
    const retrieved = llvm.c.LLVMGetNamedFunction(ctx.module, "main");
    try std.testing.expect(retrieved == main_fn);
}

test "codegen skeleton: add external declaration" {
    var ctx = codegen.CodegenContext.init();
    defer ctx.deinit();

    const void_ty = codegen.voidType();
    const ptr_ty = codegen.pointerType(codegen.i8Type());

    const puts_fn = codegen.addExternalFunction(&ctx, "puts", void_ty, &.{ptr_ty});

    try std.testing.expect(puts_fn != null);

    // Verify it's external (no body)
    const first_block = llvm.c.LLVMGetFirstBasicBlock(puts_fn);
    try std.testing.expect(first_block == null);
}

test "codegen skeleton: global string literal" {
    var ctx = codegen.CodegenContext.init();
    defer ctx.deinit();

    const hello_str = codegen.createGlobalString(&ctx, "Hello World!\n", "hello");

    try std.testing.expect(hello_str != null);
}

test "codegen skeleton: simple call to puts" {
    var ctx = codegen.CodegenContext.init();
    defer ctx.deinit();

    // Set up external puts
    const void_ty = codegen.voidType();
    const ptr_ty = codegen.pointerType(codegen.i8Type());
    const puts_fn = codegen.addExternalFunction(&ctx, "puts", void_ty, &.{ptr_ty});

    // Create main function
    const main_fn = codegen.addFunction(&ctx, "main", void_ty, &.{});
    const entry = llvm.appendBasicBlock(main_fn, "entry");
    llvm.positionBuilderAtEnd(ctx.builder, entry);

    // Add call to puts
    const hello_str = codegen.createGlobalString(&ctx, "Hello", "hello");
    _ = llvm.buildCall(ctx.builder, puts_fn, &.{hello_str}, "");

    // Add return
    _ = llvm.buildRetVoid(ctx.builder);
}

test "codegen skeleton: write module to string" {
    var ctx = codegen.CodegenContext.init();
    defer ctx.deinit();

    const allocator = std.testing.allocator;
    const ir = try ctx.toString(allocator);
    defer allocator.free(ir);

    // Should contain module declaration
    try std.testing.expect(std.mem.indexOf(u8, ir, "define") != null);
}

test "codegen skeleton: hello world program" {
    var ctx = codegen.CodegenContext.init();
    defer ctx.deinit();

    const allocator = std.testing.allocator;

    // Declare external puts function
    const void_ty = codegen.voidType();
    const ptr_ty = codegen.pointerType(codegen.i8Type());
    const puts_fn = codegen.addExternalFunction(&ctx, "puts", void_ty, &.{ptr_ty});

    // Create main function with correct signature for main returning i32
    const i32_ty = codegen.i32Type();
    const main_fn = codegen.addFunction(&ctx, "main", i32_ty, &.{});
    const entry = llvm.appendBasicBlock(main_fn, "entry");
    llvm.positionBuilderAtEnd(ctx.builder, entry);

    // Add call to puts with global string
    const hello_str = codegen.createGlobalString(&ctx, "Hello World!\n", "hello");
    _ = llvm.buildCall(ctx.builder, puts_fn, &.{hello_str}, "");

    // Return 0
    const zero = codegen.constInt(0);
    _ = llvm.buildRet(ctx.builder, zero);

    // Write to string and verify
    const ir = try ctx.toString(allocator);
    defer allocator.free(ir);

    // Verify the IR contains our function
    try std.testing.expect(std.mem.indexOf(u8, ir, "define i32 @main") != null);
    try std.testing.expect(std.mem.indexOf(u8, ir, "Hello World") != null);
    try std.testing.expect(std.mem.indexOf(u8, ir, "puts") != null);
}
