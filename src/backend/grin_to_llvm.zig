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
/// their LLVM equivalents.
const PrimOpMapping = struct {
    fn lookup(name: grin.Name) ?PrimOpResult {
        // Libc function mappings
        if (std.mem.eql(u8, name.base, "putStrLn")) {
            return .{
                .libcall = .{
                    .name = "puts",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "print")) {
            return .{
                .libcall = .{
                    .name = "printf",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "putStr")) {
            return .{
                .libcall = .{
                    .name = "fputs",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr, .ptr}, // string, FILE* (stdout)
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }

        // Arithmetic PrimOp mappings
        if (std.mem.eql(u8, name.base, "add_Int")) return .{ .instruction = .{ .add = {} } };
        if (std.mem.eql(u8, name.base, "sub_Int")) return .{ .instruction = .{ .sub = {} } };
        if (std.mem.eql(u8, name.base, "mul_Int")) return .{ .instruction = .{ .mul = {} } };
        if (std.mem.eql(u8, name.base, "div#")) return .{ .instruction = .{ .sdiv = {} } };
        if (std.mem.eql(u8, name.base, "mod#")) return .{ .instruction = .{ .srem = {} } };
        if (std.mem.eql(u8, name.base, "quot#")) return .{ .instruction = .{ .sdiv = {} } };
        if (std.mem.eql(u8, name.base, "rem#")) return .{ .instruction = .{ .srem = {} } };

        // Comparison PrimOp mappings
        if (std.mem.eql(u8, name.base, "eq_Int")) return .{ .instruction = .{ .eq = {} } };
        if (std.mem.eql(u8, name.base, "ne_Int")) return .{ .instruction = .{ .ne = {} } };
        if (std.mem.eql(u8, name.base, "lt_Int")) return .{ .instruction = .{ .slt = {} } };
        if (std.mem.eql(u8, name.base, "le_Int")) return .{ .instruction = .{ .sle = {} } };
        if (std.mem.eql(u8, name.base, "gt_Int")) return .{ .instruction = .{ .sgt = {} } };
        if (std.mem.eql(u8, name.base, "ge_Int")) return .{ .instruction = .{ .sge = {} } };

        return null;
    }
};

/// Abstract description of a parameter or return type,
/// independent of any LLVM context.
const ParamKind = enum {
    i32,
    i64,
    ptr,
};

/// Describes how GRIN arguments map to LLVM call arguments.
const ArgStrategy = enum {
    string_to_global_ptr,
    value_passthrough,
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
            .i64 => llvm.i64Type(),
            .ptr => c.LLVMPointerTypeInContext(c.LLVMGetGlobalContext(), 0),
        };
    }

    /// Build the LLVM function type. Caller must ensure `buf` is large
    /// enough to hold `self.param_kinds.len` elements.
    fn llvmFunctionType(self: LibcFunction, buf: []llvm.Type) llvm.Type {
        for (self.param_kinds, 0..) |kind, i| {
            buf[i] = switch (kind) {
                .i32 => llvm.i32Type(),
                .i64 => llvm.i64Type(),
                .ptr => c.LLVMPointerTypeInContext(c.LLVMGetGlobalContext(), 0),
            };
        }
        const ret = self.llvmReturnType();
        return c.LLVMFunctionType(ret, @ptrCast(buf.ptr), @intCast(self.param_kinds.len), 0);
    }
};

/// LLVM instruction-based PrimOp (not a libc call)
const LLVMInstruction = union(enum) {
    /// Binary arithmetic instructions
    add: void,
    sub: void,
    mul: void,
    sdiv: void,
    srem: void,
    /// Comparison instructions (icmp)
    eq: void,
    ne: void,
    slt: void,
    sle: void,
    sgt: void,
    sge: void,
};

/// A translated PrimOp result
const PrimOpResult = union(enum) {
    libcall: LibcFunction,
    instruction: LLVMInstruction,
};

// ═══════════════════════════════════════════════════════════════════════
// GRIN-to-LLVM Translator
// ═══════════════════════════════════════════════════════════════════════

pub const TranslationError = error{
    UnsupportedGrinVal,
    UnknownFunction,
    OutOfMemory,
    UnimplementedPattern,
};

pub const GrinTranslator = struct {
    ctx: llvm.Context,
    module: llvm.Module,
    builder: llvm.Builder,
    allocator: std.mem.Allocator,
    params: std.StringHashMap(llvm.Value),

    pub fn init(allocator: std.mem.Allocator) GrinTranslator {
        llvm.initialize();
        const ctx = llvm.createContext();
        return .{
            .ctx = ctx,
            .module = llvm.createModule("haskell", ctx),
            .builder = llvm.createBuilder(ctx),
            .allocator = allocator,
            .params = std.StringHashMap(llvm.Value).init(allocator),
        };
    }

    pub fn deinit(self: *GrinTranslator) void {
        self.params.deinit();
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
        // For M1, use base name only (assumes unique names for small test programs)
        const is_main = std.mem.eql(u8, def.name.base, "main");
        const ret_type = if (is_main) llvm.i32Type() else llvm.voidType();

        // Create parameter types (all i32 for M1 scope)
        var param_types: [8]llvm.Type = undefined;
        for (def.params[0..@min(def.params.len, 8)], 0..) |_, i| {
            param_types[i] = llvm.i32Type();
        }

        const fn_type = llvm.functionType(ret_type, param_types[0..def.params.len], false);
        const func = llvm.addFunction(self.module, def.name.base, fn_type);
        const entry_bb = llvm.appendBasicBlock(func, "entry");

        // Debug: verify function was created
        // _ = c.LLVMGetNamedFunction(self.module, fn_name) orelse @panic("Function declaration failed!");
        // std.debug.print("Declared LLVM function: {s}\n", .{fn_name});
        llvm.positionBuilderAtEnd(self.builder, entry_bb);

        // Clear previous function's parameter mapping and set up current one
        self.params.deinit();
        self.params = std.StringHashMap(llvm.Value).init(self.allocator);

        // Store each parameter as a named value in the params map
        for (def.params, 0..) |param_name, i| {
            // Get the LLVM parameter value at this index
            const param_val = c.LLVMGetParam(func, @intCast(i));
            if (param_val == null) return error.OutOfMemory;

            // Store the base name as the key (param_name.base is a slice)
            try self.params.put(param_name.base, param_val);
        }

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
            .Bind => |b| try self.translateBind(b.lhs, b.pat, b.rhs),
            .Case => |case_| try self.translateCase(case_.scrutinee, case_.alts),
            .Store => |val| try self.translateStore(val),
            .Fetch => |f| try self.translateFetch(f.ptr, f.index),
            .Update => |u| try self.translateUpdate(u.ptr, u.val),
            .Return => |r| try self.translateReturn(r),
            .Block => |e| try self.translateExpr(e),
        }
    }

    fn translateBind(
        self: *GrinTranslator,
        lhs: *const grin.Expr,
        pat: grin.Val,
        rhs: *const grin.Expr,
    ) TranslationError!void {
        // TODO: For full M1, we need to handle complex patterns (ConstTagNode, etc.)
        // For now, only handle simple variable bindings (Var pattern) and discard (Unit)
        // tracked in: https://github.com/adinapoli/rusholme/issues/390

        const pat_name = switch (pat) {
            .Var => |v| v,
            .Unit => {
                // Discard the value, just evaluate RHS with no binding
                try self.translateExpr(lhs);
                try self.translateExpr(rhs);
                return;
            },
            else => return error.UnimplementedPattern,
        };

        // Evaluate LHS - for M1, only App produces side effects we care about
        // For Store/Fetch etc., we'll need to capture their return values
        try self.translateExpr(lhs);

        // For now, in M1 scope, we don't have a good way to capture LHS results
        // since most expressions (App, Store) don't return usable LLVM values yet
        // TODO: Proper SSA variable binding requires refactoring translateExpr
        // tracked in: https://github.com/adinapoli/rusholme/issues/390

        // Store binding (will resolve this later when we have proper value emission)
        _ = pat_name;

        // Evaluate RHS
        try self.translateExpr(rhs);
    }

    fn translateApp(self: *GrinTranslator, name: grin.Name, args: []const grin.Val) TranslationError!void {
        // Handle `pure` as a special built-in: pure x = x (identity, wraps in monadic context)
        // For LLVM codegen, this is essentially a no-op - we just translate the value
        // and the result is the translated value (which gets returned via the Return in the function body)
        if (std.mem.eql(u8, name.base, "pure")) {
            // For M1, no-op - the value will be handled by the surrounding Return
            return;
        }

        // Lookup the PrimOp mapping
        if (PrimOpMapping.lookup(name)) |result| {
            switch (result) {
                .libcall => |libc_fn| {
                    try self.emitLibcCall(libc_fn, args);
                },
                .instruction => |instr| {
                    try self.emitInstruction(instr, args);
                },
            }
        }

        // For M1, we don't support arbitrary user-defined function calls.
        // The test case uses pure and PrimOps only, which should be handled above.
    }

    fn emitLibcCall(self: *GrinTranslator, libc_fn: LibcFunction, args: []const grin.Val) TranslationError!void {
        // Build the LLVM function type on the stack from the
        // abstract descriptor (avoids dangling-pointer issues).
        var param_buf: [8]llvm.Type = undefined;
        const fn_type = libc_fn.llvmFunctionType(&param_buf);

        // Get or declare the external function.
        const func = c.LLVMGetNamedFunction(self.module, libc_fn.name) orelse
            llvm.addFunction(self.module, std.mem.span(libc_fn.name), fn_type);

        // Translate all arguments
        var llvm_args: [8]llvm.Value = undefined;
        for (args[0..@min(args.len, 8)], 0..) |val, i| {
            llvm_args[i] = try self.translateValToLlvm(val);
        }

        // Special case for putStr: need to pass stdout FILE* as second argument
        var actual_args = llvm_args[0..args.len];
        if (std.mem.eql(u8, std.mem.span(libc_fn.name), "fputs") and args.len == 2) {
            // For M1, we don't have a good way to get stdout. Use stderr for now.
            // tracked in: https://github.com/adinapoli/rusholme/issues/391
            _ = llvm_args[1]; // placeholder for FILE*
        }

        _ = c.LLVMBuildCall2(
            self.builder,
            fn_type,
            func,
            @ptrCast(actual_args.ptr),
            @intCast(args.len),
            "",
        );
    }

    fn emitInstruction(self: *GrinTranslator, instr: LLVMInstruction, args: []const grin.Val) TranslationError!void {
        // For M1, instructions need at least 2 arguments, ignore the rest
        if (args.len < 2) {
            return error.UnsupportedGrinVal;
        }

        const lhs = try self.translateValToLlvm(args[0]);
        const rhs = try self.translateValToLlvm(args[1]);

        const result = switch (instr) {
            .add => c.LLVMBuildAdd(self.builder, lhs, rhs, "add"),
            .sub => c.LLVMBuildSub(self.builder, lhs, rhs, "sub"),
            .mul => c.LLVMBuildMul(self.builder, lhs, rhs, "mul"),
            .sdiv => c.LLVMBuildSDiv(self.builder, lhs, rhs, "sdiv"),
            .srem => c.LLVMBuildSRem(self.builder, lhs, rhs, "rem"),
            .eq => c.LLVMBuildICmp(self.builder, @as(c_uint, @bitCast(c.LLVMIntEQ)), lhs, rhs, "eq"),
            .ne => c.LLVMBuildICmp(self.builder, @as(c_uint, @bitCast(c.LLVMIntNE)), lhs, rhs, "ne"),
            .slt => c.LLVMBuildICmp(self.builder, @as(c_uint, @bitCast(c.LLVMIntSLT)), lhs, rhs, "slt"),
            .sle => c.LLVMBuildICmp(self.builder, @as(c_uint, @bitCast(c.LLVMIntSLE)), lhs, rhs, "sle"),
            .sgt => c.LLVMBuildICmp(self.builder, @as(c_uint, @bitCast(c.LLVMIntSGT)), lhs, rhs, "sgt"),
            .sge => c.LLVMBuildICmp(self.builder, @as(c_uint, @bitCast(c.LLVMIntSGE)), lhs, rhs, "sge"),
        };

        _ = result;
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

    fn translateCase(
        self: *GrinTranslator,
        scrutinee: grin.Val,
        alts: []const grin.Alt,
    ) TranslationError!void {
        // TODO: For M1, we need to implement the actual pattern matching and branching logic:
        // 1. Translate scrutinee to LLVM value
        // 2. For node patterns: create LLVM switch on tag value
        // 3. For literal patterns: compare and branch
        // 4. For default: unconditional branch to default block
        //
        // For now, structural placeholder - each alternative's body would be generated
        // in its own basic block joined by an incoming edge from the switch.
        // tracked in: https://github.com/adinapoli/rusholme/issues/390
        _ = self;
        _ = scrutinee;
        _ = alts;
    }

    fn translateStore(self: *GrinTranslator, val: grin.Val) TranslationError!void {
        // TODO: For M1, Store should:
        // 1. Call RTS allocation function to get heap pointer
        // 2. Write tag value to first word
        // 3. Write each field to subsequent words
        // 4. Return pointer to stored node
        //
        // This requires RTS integration which is a separate milestone.
        // For now, structural placeholder.
        // tracked in: https://github.com/adinapoli/rusholme/issues/390
        _ = self;
        _ = val;
    }

    fn translateFetch(
        self: *GrinTranslator,
        ptr: grin.Name,
        index: ?u32,
    ) TranslationError!void {
        // TODO: For M1, Fetch should:
        // 1. Load the heap pointer from variable
        // 2. Read tag or field value from memory
        // 3. Return the loaded GRIN value
        //
        // This requires proper SSA variable tracking for `ptr`.
        // tracked in: https://github.com/adinapoli/rusholme/issues/390
        _ = self;
        _ = ptr;
        _ = index;
    }

    fn translateUpdate(
        self: *GrinTranslator,
        ptr: grin.Name,
        val: grin.Val,
    ) TranslationError!void {
        // TODO: For M1, Update should:
        // 1. Load the heap pointer from variable
        // 2. Overwrite the node at that location with new value
        //
        // This requires proper SSA variable tracking for `ptr` and
        // value translation for `val`.
        // tracked in: https://github.com/adinapoli/rusholme/issues/390
        _ = self;
        _ = ptr;
        _ = val;
    }

    fn translateReturn(self: *GrinTranslator, val: grin.Val) TranslationError!void {
        // Return a value from the function.
        // For now, return i32 (M1 scope) - later this should use the
        // proper return type from function signature.
        const llvm_val = try self.translateValToLlvm(val);
        _ = llvm.buildRet(self.builder, llvm_val);
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Tests
// ═══════════════════════════════════════════════════════════════════════

test "PrimOpMapping: putStrLn maps to puts" {
    const result = PrimOpMapping.lookup(.{
        .base = "putStrLn",
        .unique = .{ .value = 42 },
    });
    try std.testing.expect(result != null);
    try std.testing.expectEqualStrings("puts", std.mem.span(result.?.libcall.name));
}

test "PrimOpMapping: unknown function returns null" {
    const result = PrimOpMapping.lookup(.{
        .base = "myFunction",
        .unique = .{ .value = 0 },
    });
    try std.testing.expect(result == null);
}
