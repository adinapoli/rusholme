//! GRIN-to-LLVM IR Translator.
//!
//! Translates GRIN IR programs to LLVM IR using the LLVM-C API.
//! This is issue #55: LLVM codegen for GRIN expressions.
//!
//! ## Scope (M1)
//!
//! This module implements the minimum translation needed for the M1 Hello
//! World milestone: `main = putStrLn "Hello World!"`. The GRIN program
//! is a sequence of `App` and `Store` expressions.
//!
//! Supported GRIN constructs:
//!   - `App` of known Prelude/PrimOp functions (via PrimOpMapping)
//!   - `Return` with Unit only (M1 scope)
//!   - `Bind`, `Case`, `Store`, `Fetch`, `Update`, `Block` (placeholders)

const std = @import("std");

const grin = @import("../grin/ast.zig");

const llvm = @import("llvm.zig");
const c = llvm.c;

// ═══════════════════════════════════════════════════════════════════════
// PrimOp-to-libc Mapping
// ═══════════════════════════════════════════════════════════════════════

/// Centralized mapping from GRIN Prelude/PrimOp function base names to
/// their libc equivalents.
///
/// Importantly, this mapping must NOT hold live LLVM type refs — those
/// are runtime objects that cannot survive as return values from a
/// function (they'd be dangling pointers to stack-local temporaries).
/// Instead, the mapping describes the signature abstractly, and the
/// translator builds the actual LLVM types at the call site.
const PrimOpMapping = struct {
    fn lookupLibcMapping(name: grin.Name) ?LibcFunction {
        if (std.mem.eql(u8, name.base, "putStrLn")) {
            return .{
                .name = "puts",
                .return_kind = .i32,
                .param_kinds = &.{.ptr},
                .arg_strategy = .string_to_global_ptr,
            };
        }
        return null;
    }
};

/// Abstract description of a parameter or return type,
/// independent of any LLVM context.
const ParamKind = enum {
    i32,
    ptr,
};

/// Describes how GRIN arguments map to LLVM call arguments.
const ArgStrategy = enum {
    string_to_global_ptr,
};

/// A libc function descriptor — holds *descriptions* of types,
/// not LLVM type refs (see `PrimOpMapping` doc comment).
const LibcFunction = struct {
    name: [*:0]const u8,
    return_kind: ParamKind,
    param_kinds: []const ParamKind,
    arg_strategy: ArgStrategy,

    /// Build the actual LLVM return type. Must be called while the
    /// LLVM context is live.
    fn llvmReturnType(self: LibcFunction) llvm.Type {
        return switch (self.return_kind) {
            .i32 => llvm.i32Type(),
            .ptr => c.LLVMPointerTypeInContext(c.LLVMGetGlobalContext(), 0),
        };
    }

    /// Build the LLVM function type. Caller must ensure `buf` is large
    /// enough to hold `self.param_kinds.len` elements.
    fn llvmFunctionType(self: LibcFunction, buf: []llvm.Type) llvm.Type {
        for (self.param_kinds, 0..) |kind, i| {
            buf[i] = switch (kind) {
                .i32 => llvm.i32Type(),
                .ptr => c.LLVMPointerTypeInContext(c.LLVMGetGlobalContext(), 0),
            };
        }
        const ret = self.llvmReturnType();
        return c.LLVMFunctionType(ret, @ptrCast(buf.ptr), @intCast(self.param_kinds.len), 0);
    }
};

// ═══════════════════════════════════════════════════════════════════════
// GRIN-to-LLVM Translator
// ═══════════════════════════════════════════════════════════════════════

pub const TranslationError = error{
    UnsupportedGrinVal,
    UnknownFunction,
    OutOfMemory,
};

pub const GrinTranslator = struct {
    ctx: llvm.Context,
    module: llvm.Module,
    builder: llvm.Builder,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) GrinTranslator {
        llvm.initialize();
        const ctx = llvm.createContext();
        return .{
            .ctx = ctx,
            .module = llvm.createModule("haskell", ctx),
            .builder = llvm.createBuilder(ctx),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *GrinTranslator) void {
        llvm.disposeBuilder(self.builder);
        // Disposing the context also disposes modules created within it.
        llvm.disposeContext(self.ctx);
    }

    /// Translate the entire GRIN program into the LLVM module.
    /// Returns the underlying LLVM Module for direct use (e.g. object emission).
    /// The module is owned by this translator's context — do not dispose it
    /// separately; it is freed when the translator is deinited.
    pub fn translateProgramToModule(self: *GrinTranslator, program: grin.Program) TranslationError!llvm.Module {
        for (program.defs) |def| {
            try self.translateDef(def);
        }
        return self.module;
    }

    /// Translate the GRIN program and return the LLVM IR as a string.
    /// Convenience wrapper around `translateProgramToModule` for text output.
    pub fn translateProgram(self: *GrinTranslator, program: grin.Program) TranslationError![]u8 {
        _ = try self.translateProgramToModule(program);
        return llvm.printModuleToString(self.module, self.allocator) catch
            return error.OutOfMemory;
    }

    fn translateDef(self: *GrinTranslator, def: grin.Def) TranslationError!void {
        // For M1, `main` returns i32 (C convention); other defs return void.
        const is_main = std.mem.eql(u8, def.name.base, "main");
        const ret_type = if (is_main) llvm.i32Type() else llvm.voidType();

        const fn_type = llvm.functionType(ret_type, &.{}, false);
        const func = llvm.addFunction(self.module, def.name.base, fn_type);
        const entry_bb = llvm.appendBasicBlock(func, "entry");
        llvm.positionBuilderAtEnd(self.builder, entry_bb);

        try self.translateExpr(def.body);

        // Emit the terminator.
        if (is_main) {
            _ = llvm.buildRet(self.builder, c.LLVMConstInt(llvm.i32Type(), 0, 0));
        } else {
            _ = llvm.buildRetVoid(self.builder);
        }
    }

    fn translateExpr(self: *GrinTranslator, expr: *const grin.Expr) TranslationError!void {
        switch (expr.*) {
            .App => |app| try self.translateApp(app.name, app.args),
            // ── Not yet implemented ─────────────────────────────────────
            // tracked in: https://github.com/adinapoli/rusholme/issues/55
            .Return, .Bind, .Case, .Store, .Fetch, .Update, .Block => {},
        }
    }

    fn translateApp(self: *GrinTranslator, name: grin.Name, args: []const grin.Val) TranslationError!void {
        if (PrimOpMapping.lookupLibcMapping(name)) |libc_fn| {
            // Build the LLVM function type on the stack from the
            // abstract descriptor (avoids dangling-pointer issues).
            var param_buf: [8]llvm.Type = undefined;
            const fn_type = libc_fn.llvmFunctionType(&param_buf);

            // Get or declare the external function.
            const func = c.LLVMGetNamedFunction(self.module, libc_fn.name) orelse
                llvm.addFunction(self.module, std.mem.span(libc_fn.name), fn_type);

            if (args.len > 0) {
                var llvm_arg = try self.translateValToLlvm(args[0]);
                _ = c.LLVMBuildCall2(
                    self.builder,
                    fn_type,
                    func,
                    @ptrCast(&llvm_arg),
                    1,
                    "",
                );
            }
        } else {
            return error.UnknownFunction;
        }
    }

    fn translateValToLlvm(self: *GrinTranslator, val: grin.Val) TranslationError!llvm.Value {
        return switch (val) {
            .Lit => |lit| switch (lit) {
                .String => |s| blk: {
                    const s_z = self.allocator.dupeZ(u8, s) catch return error.OutOfMemory;
                    defer self.allocator.free(s_z);
                    break :blk c.LLVMBuildGlobalStringPtr(self.builder, s_z.ptr, ".str") orelse
                        return error.OutOfMemory;
                },
                .Int => |i| c.LLVMConstInt(llvm.i64Type(), @bitCast(@as(i64, i)), 1),
                .Float => |f| c.LLVMConstReal(c.LLVMDoubleType(), f),
                .Bool => |b| c.LLVMConstInt(c.LLVMInt1Type(), @intFromBool(b), 0),
                .Char => |ch| c.LLVMConstInt(llvm.i32Type(), ch, 0),
            },
            .Unit => c.LLVMGetUndef(llvm.i32Type()),
            else => return error.UnsupportedGrinVal,
        };
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "PrimOpMapping: putStrLn maps to puts" {
    const result = PrimOpMapping.lookupLibcMapping(.{
        .base = "putStrLn",
        .unique = .{ .value = 42 },
    });
    try std.testing.expect(result != null);
    try std.testing.expectEqualStrings("puts", std.mem.span(result.?.name));
}

test "PrimOpMapping: unknown function returns null" {
    const result = PrimOpMapping.lookupLibcMapping(.{
        .base = "myFunction",
        .unique = .{ .value = 0 },
    });
    try std.testing.expect(result == null);
}
