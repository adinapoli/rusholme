//! GRIN-to-LLVM IR Translator.
//!
//! Translates GRIN IR programs to LLVM IR using the LLVM-C API.
//! This is issue #55: LLVM codegen for GRIN expressions.
//!
//! ## Heap node layout
//!
//! Every constructor node is represented as a heap-allocated struct:
//!
//!   { i64 tag, ptr field0, ptr field1, … }
//!
//! The `tag` is an integer discriminant assigned by `TagTable` — each
//! unique constructor gets a stable `i64` value (0, 1, 2, …) in the
//! order they are first encountered in the program.  All field values
//! are opaque `ptr` (i8*) — the M1 backend boxes everything.
//!
//! Nullary constructors (no fields) can appear as `Val.Var` references.
//! When the tag table recognises a name as a nullary constructor, we emit
//! an unboxed `i64` constant instead of dereferencing a heap pointer.
//!
//! ## Supported GRIN constructs (M1 scope)
//!
//!   - App  — PrimOps (puts, arithmetic) and user-defined calls
//!   - Bind — variable binding (Var pattern) and unit discard
//!   - Case — switch on tag discriminant with per-alt basic blocks (#390)
//!   - Store — malloc + write tag + fields to heap (#390)
//!   - Return — emit `ret`
//!   - Block — transparent scoping
//!
//! Fetch and Update remain stubs (tracked in #390).

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
// Tag Table
// ═══════════════════════════════════════════════════════════════════════

/// Maps every constructor `Tag` in the GRIN program to a stable `i64`
/// discriminant (0, 1, 2, …) and records the number of fields each
/// constructor carries.
///
/// Built once before translation starts by scanning all `ConstTagNode`
/// values in the program.  The unique value of the tag's name is used as
/// the map key so that identity is name-based, not string-based.
const TagTable = struct {
    /// Discriminant assigned to each constructor, keyed by name unique.
    discriminants: std.AutoHashMapUnmanaged(u64, i64),
    /// Number of fields for each constructor, keyed by name unique.
    field_counts: std.AutoHashMapUnmanaged(u64, u32),
    /// Next discriminant to assign.
    next: i64,

    fn init() TagTable {
        return .{
            .discriminants = .{},
            .field_counts = .{},
            .next = 0,
        };
    }

    fn deinit(self: *TagTable, alloc: std.mem.Allocator) void {
        self.discriminants.deinit(alloc);
        self.field_counts.deinit(alloc);
    }

    /// Register a constructor tag with the given field count.
    /// If already registered, this is a no-op (idempotent).
    fn register(self: *TagTable, alloc: std.mem.Allocator, tag: grin.Tag, n_fields: u32) !void {
        const key = tag.name.unique.value;
        if (self.discriminants.contains(key)) return;
        try self.discriminants.put(alloc, key, self.next);
        try self.field_counts.put(alloc, key, n_fields);
        self.next += 1;
    }

    /// Return the discriminant for a constructor, or null if unknown.
    fn discriminant(self: *const TagTable, tag: grin.Tag) ?i64 {
        return self.discriminants.get(tag.name.unique.value);
    }

    /// Return the field count for a constructor, or null if unknown.
    fn fieldCount(self: *const TagTable, tag: grin.Tag) ?u32 {
        return self.field_counts.get(tag.name.unique.value);
    }

    /// Return true if the named variable is a known nullary constructor.
    /// We match by base name since the GRIN Val.Var just carries a Name.
    fn isNullaryByName(self: *const TagTable, name: grin.Name) bool {
        const fc = self.field_counts.get(name.unique.value) orelse return false;
        return fc == 0;
    }

    /// Return the discriminant for a variable if it is a known nullary
    /// constructor, otherwise null.
    fn discriminantByName(self: *const TagTable, name: grin.Name) ?i64 {
        if (!self.isNullaryByName(name)) return null;
        return self.discriminants.get(name.unique.value);
    }
};

/// Scan the entire GRIN program and populate the tag table.
fn buildTagTable(alloc: std.mem.Allocator, program: grin.Program) !TagTable {
    var table = TagTable.init();
    errdefer table.deinit(alloc);
    for (program.defs) |def| {
        try scanExprForTags(alloc, def.body, &table);
    }
    return table;
}

fn scanExprForTags(alloc: std.mem.Allocator, expr: *const grin.Expr, table: *TagTable) !void {
    switch (expr.*) {
        .Return => |v| try scanValForTags(alloc, v, table),
        .Store => |v| try scanValForTags(alloc, v, table),
        .App => |a| for (a.args) |arg| try scanValForTags(alloc, arg, table),
        .Bind => |b| {
            try scanExprForTags(alloc, b.lhs, table);
            try scanValForTags(alloc, b.pat, table);
            try scanExprForTags(alloc, b.rhs, table);
        },
        .Case => |k| {
            try scanValForTags(alloc, k.scrutinee, table);
            for (k.alts) |alt| {
                // Register the pattern tag too.
                switch (alt.pat) {
                    .NodePat => |np| try table.register(alloc, np.tag, @intCast(np.fields.len)),
                    .TagPat => |t| try table.register(alloc, t, 0),
                    else => {},
                }
                try scanExprForTags(alloc, alt.body, table);
            }
        },
        .Update => |u| try scanValForTags(alloc, u.val, table),
        .Fetch => {},
        .Block => |inner| try scanExprForTags(alloc, inner, table),
    }
}

fn scanValForTags(alloc: std.mem.Allocator, val: grin.Val, table: *TagTable) !void {
    switch (val) {
        .ConstTagNode => |ctn| {
            try table.register(alloc, ctn.tag, @intCast(ctn.fields.len));
            for (ctn.fields) |f| try scanValForTags(alloc, f, table);
        },
        .ValTag => |t| try table.register(alloc, t, 0),
        .VarTagNode => |vtn| for (vtn.fields) |f| try scanValForTags(alloc, f, table),
        else => {},
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Heap node helpers
// ═══════════════════════════════════════════════════════════════════════

/// Return the LLVM opaque pointer type used for all heap pointers.
fn ptrType() llvm.Type {
    return c.LLVMPointerTypeInContext(c.LLVMGetGlobalContext(), 0);
}

/// Return the LLVM struct type for a node with `n_fields` payload fields:
///   { i64 tag, ptr field0, …, ptr fieldN-1 }
fn nodeStructType(n_fields: u32) llvm.Type {
    var members: [9]llvm.Type = undefined; // 1 tag + up to 8 fields
    members[0] = llvm.i64Type();
    for (1..n_fields + 1) |i| members[i] = ptrType();
    return c.LLVMStructType(@ptrCast(&members), n_fields + 1, 0);
}

/// Declare `malloc` in the module if not already declared.
fn declareMalloc(module: llvm.Module) llvm.Value {
    const name = "malloc";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    const param_ty = llvm.i64Type();
    var params = [_]llvm.Type{param_ty};
    const fn_ty = c.LLVMFunctionType(ptrType(), &params, 1, 0);
    return c.LLVMAddFunction(module, name, fn_ty);
}

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
    /// Maps GRIN variable unique IDs to their current LLVM SSA values.
    /// Keyed by `Name.unique.value` so that variables with the same base name
    /// but different uniques (e.g. `arg_20`, `arg_21`) are kept distinct.
    params: std.AutoHashMap(u64, llvm.Value),
    /// Constructor tag discriminants, built before translation.
    tag_table: TagTable,
    /// The LLVM function currently being translated (needed for
    /// `LLVMAppendBasicBlock` calls inside Case translation).
    current_func: llvm.Value,

    pub fn init(allocator: std.mem.Allocator) GrinTranslator {
        llvm.initialize();
        const ctx = llvm.createContext();
        return .{
            .ctx = ctx,
            .module = llvm.createModule("haskell", ctx),
            .builder = llvm.createBuilder(ctx),
            .allocator = allocator,
            .params = std.AutoHashMap(u64, llvm.Value).init(allocator),
            .tag_table = TagTable.init(),
            .current_func = null,
        };
    }

    pub fn deinit(self: *GrinTranslator) void {
        self.params.deinit();
        self.tag_table.deinit(self.allocator);
        llvm.disposeBuilder(self.builder);
        // Disposing the context also disposes modules created within it.
        llvm.disposeContext(self.ctx);
    }

    /// Translate the entire GRIN program into the LLVM module.
    /// Returns the underlying LLVM Module for direct use (e.g. object emission).
    /// The module is owned by this translator's context — do not dispose it
    /// separately; it is freed when the translator is deinited.
    pub fn translateProgramToModule(self: *GrinTranslator, program: grin.Program) TranslationError!llvm.Module {
        // Build the tag table once before any translation.
        self.tag_table = buildTagTable(self.allocator, program) catch return error.OutOfMemory;
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
        // For M1, `main` follows the C ABI (i32 return, no params).
        // All other user-defined functions use an opaque `ptr` representation
        // for parameters and return values — GRIN has no type information at
        // this stage and all heap values are pointers.
        const is_main = std.mem.eql(u8, def.name.base, "main");
        const has_params = def.params.len > 0;
        const value_type = if (is_main) llvm.i32Type() else ptrType();
        const ret_type = if (is_main) llvm.i32Type() else if (has_params) value_type else llvm.voidType();

        // Parameter types: i32 for main (no params), ptr for all others.
        var param_types: [8]llvm.Type = undefined;
        for (def.params[0..@min(def.params.len, 8)], 0..) |_, i| {
            param_types[i] = value_type;
        }

        const fn_type = llvm.functionType(ret_type, param_types[0..def.params.len], false);
        const func = llvm.addFunction(self.module, def.name.base, fn_type);
        self.current_func = func;
        const entry_bb = llvm.appendBasicBlock(func, "entry");
        llvm.positionBuilderAtEnd(self.builder, entry_bb);

        // Clear previous function's parameter mapping and set up current one.
        self.params.deinit();
        self.params = std.AutoHashMap(u64, llvm.Value).init(self.allocator);

        // Store each parameter as a named value in the params map.
        for (def.params, 0..) |param_name, i| {
            const param_val = c.LLVMGetParam(func, @intCast(i));
            if (param_val == null) return error.OutOfMemory;
            try self.params.put(param_name.unique.value, param_val);
        }

        try self.translateExpr(def.body);

        // Emit the terminator based on return type — only if the current
        // block does not already have one (a Return expr may have emitted it).
        const current_bb = c.LLVMGetInsertBlock(self.builder);
        if (current_bb != null and c.LLVMGetBasicBlockTerminator(current_bb) == null) {
            if (is_main) {
                _ = llvm.buildRet(self.builder, c.LLVMConstInt(llvm.i32Type(), 0, 0));
            } else if (has_params) {
                _ = llvm.buildRet(self.builder, c.LLVMConstPointerNull(value_type));
            } else {
                _ = llvm.buildRetVoid(self.builder);
            }
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
        switch (pat) {
            .Unit => {
                // Discard the value — evaluate LHS for side effects only.
                try self.translateExpr(lhs);
                try self.translateExpr(rhs);
            },
            .Var => |v| {
                // Bind the LHS result to a named variable.
                const result = try self.translateExprToValue(lhs, v.base);
                if (result) |val| {
                    try self.params.put(v.unique.value, val);
                }
                try self.translateExpr(rhs);
            },
            .ConstTagNode => |ctn| {
                // Destructure: the LHS produced a heap pointer to a node
                // matching this tag. Extract each field and bind the field
                // names into params so the RHS can reference them.
                const ptr_val = try self.translateExprToValue(lhs, "node") orelse
                    return error.UnsupportedGrinVal;
                const n_fields: u32 = @intCast(ctn.fields.len);
                const struct_ty = nodeStructType(n_fields);
                for (ctn.fields, 0..) |field_val, fi| {
                    if (field_val != .Var) continue;
                    const field_var = field_val.Var;
                    // GEP: index 0 = tag, index fi+1 = field fi.
                    var indices = [_]llvm.Value{
                        c.LLVMConstInt(llvm.i32Type(), 0, 0),
                        c.LLVMConstInt(llvm.i32Type(), @intCast(fi + 1), 0),
                    };
                    const gep = c.LLVMBuildGEP2(
                        self.builder,
                        struct_ty,
                        ptr_val,
                        &indices,
                        2,
                        nullTerminate(field_var.base).ptr,
                    );
                    const loaded = c.LLVMBuildLoad2(self.builder, ptrType(), gep, nullTerminate(field_var.base).ptr);
                    try self.params.put(field_var.unique.value, loaded);
                }
                try self.translateExpr(rhs);
            },
            else => return error.UnimplementedPattern,
        }
    }

    /// Translate an expression and return the resulting LLVM value.
    /// Returns null for expressions that produce no SSA value (void calls).
    ///
    /// For `Bind(lhs, pat, rhs)` — which arises from left-associative ANF chains —
    /// we evaluate the inner bind sequence imperatively (each step binding its
    /// result into `params`) and then return the value of the final `rhs`.
    fn translateExprToValue(
        self: *GrinTranslator,
        expr: *const grin.Expr,
        result_name: []const u8,
    ) TranslationError!?llvm.Value {
        return switch (expr.*) {
            .App => |app| self.translateAppToValue(app.name, app.args, result_name),
            .Return => |v| @as(?llvm.Value, try self.translateValToLlvm(v)),
            .Store => |v| self.translateStoreToValue(v, result_name),
            .Bind => |b| {
                // Evaluate the lhs, bind result to pat, then return the value of rhs.
                // This handles left-leaning ANF bind chains produced by wrapWithPendingBinds.
                const inner_name: []const u8 = switch (b.pat) {
                    .Var => |v| v.base,
                    else => result_name,
                };
                const inner_result = try self.translateExprToValue(b.lhs, inner_name);
                switch (b.pat) {
                    .Var => |v| {
                        if (inner_result) |val| try self.params.put(v.unique.value, val);
                    },
                    .Unit => {},
                    .ConstTagNode => |ctn| {
                        if (inner_result) |ptr_val| {
                            const n_fields: u32 = @intCast(ctn.fields.len);
                            const struct_ty = nodeStructType(n_fields);
                            for (ctn.fields, 0..) |field_val, fi| {
                                if (field_val != .Var) continue;
                                const fv = field_val.Var;
                                var indices = [_]llvm.Value{
                                    c.LLVMConstInt(llvm.i32Type(), 0, 0),
                                    c.LLVMConstInt(llvm.i32Type(), @intCast(fi + 1), 0),
                                };
                                const gep = c.LLVMBuildGEP2(self.builder, struct_ty, ptr_val, &indices, 2, nullTerminate(fv.base).ptr);
                                const loaded = c.LLVMBuildLoad2(self.builder, ptrType(), gep, nullTerminate(fv.base).ptr);
                                try self.params.put(fv.unique.value, loaded);
                            }
                        }
                    },
                    else => return error.UnimplementedPattern,
                }
                return self.translateExprToValue(b.rhs, result_name);
            },
            else => {
                try self.translateExpr(expr);
                return null;
            },
        };
    }

    /// Like translateApp but returns the LLVM call instruction value so the
    /// caller can bind it to a GRIN variable (identified by `result_name`).
    /// Returns null for void-result calls (primops that return nothing useful).
    fn translateAppToValue(
        self: *GrinTranslator,
        name: grin.Name,
        args: []const grin.Val,
        result_name: []const u8,
    ) TranslationError!?llvm.Value {
        if (std.mem.eql(u8, name.base, "pure")) {
            // `pure` is a no-op in M1 — the argument is the value.
            if (args.len > 0) {
                return try self.translateValToLlvm(args[0]);
            }
            return null;
        }

        if (PrimOpMapping.lookup(name)) |result| {
            switch (result) {
                .libcall => |libc_fn| try self.emitLibcCall(libc_fn, args),
                .instruction => |instr| try self.emitInstruction(instr, args),
            }
            return null;
        }

        // User-defined function call.
        var llvm_args: [8]llvm.Value = undefined;
        const arg_count = @min(args.len, 8);
        for (args[0..arg_count], 0..) |val, i| {
            llvm_args[i] = try self.translateValToLlvm(val);
        }

        // Build a ptr-returning function type for indirect/forward calls.
        var param_types: [8]llvm.Type = undefined;
        for (0..arg_count) |i| param_types[i] = ptrType();
        const fn_type = llvm.functionType(ptrType(), param_types[0..arg_count], false);

        // Resolve the callee:
        //   1. Local variable holding a function pointer (higher-order call) — use
        //      an indirect call via the pointer stored in `params`.
        //   2. Named LLVM function (direct call to a known def).
        //   3. Forward-declare and call (for functions not yet translated).
        const func: llvm.Value = blk: {
            if (self.params.get(name.unique.value)) |fn_ptr| break :blk fn_ptr;
            var fn_name_buf: [128]u8 = undefined;
            std.debug.assert(name.base.len < fn_name_buf.len);
            @memcpy(fn_name_buf[0..name.base.len], name.base);
            fn_name_buf[name.base.len] = 0;
            const fn_name_z = fn_name_buf[0..name.base.len :0];
            if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |existing| break :blk existing;
            break :blk llvm.addFunction(self.module, name.base, fn_type);
        };

        var name_buf: [64]u8 = undefined;
        const res_z: [*:0]const u8 = if (result_name.len < name_buf.len - 1) blk: {
            @memcpy(name_buf[0..result_name.len], result_name);
            name_buf[result_name.len] = 0;
            break :blk name_buf[0..result_name.len :0];
        } else "";

        return c.LLVMBuildCall2(
            self.builder,
            fn_type,
            func,
            @ptrCast(&llvm_args),
            @intCast(arg_count),
            res_z,
        );
    }

    fn translateApp(self: *GrinTranslator, name: grin.Name, args: []const grin.Val) TranslationError!void {
        if (std.mem.eql(u8, name.base, "pure")) return;

        if (PrimOpMapping.lookup(name)) |result| {
            switch (result) {
                .libcall => |libc_fn| try self.emitLibcCall(libc_fn, args),
                .instruction => |instr| try self.emitInstruction(instr, args),
            }
            return;
        }

        // User-defined function call (result discarded).
        var llvm_args: [8]llvm.Value = undefined;
        const arg_count = @min(args.len, 8);
        for (args[0..arg_count], 0..) |val, i| {
            llvm_args[i] = try self.translateValToLlvm(val);
        }

        var param_types: [8]llvm.Type = undefined;
        for (0..arg_count) |i| param_types[i] = ptrType();
        const fn_type = llvm.functionType(ptrType(), param_types[0..arg_count], false);

        const func: llvm.Value = blk: {
            if (self.params.get(name.unique.value)) |fn_ptr| break :blk fn_ptr;
            var fn_name_buf: [128]u8 = undefined;
            std.debug.assert(name.base.len < fn_name_buf.len);
            @memcpy(fn_name_buf[0..name.base.len], name.base);
            fn_name_buf[name.base.len] = 0;
            const fn_name_z = fn_name_buf[0..name.base.len :0];
            if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |existing| break :blk existing;
            break :blk llvm.addFunction(self.module, name.base, fn_type);
        };
        _ = c.LLVMBuildCall2(
            self.builder,
            fn_type,
            func,
            @ptrCast(&llvm_args),
            @intCast(arg_count),
            "",
        );
    }

    fn emitLibcCall(self: *GrinTranslator, libc_fn: LibcFunction, args: []const grin.Val) TranslationError!void {
        var param_buf: [8]llvm.Type = undefined;
        const fn_type = libc_fn.llvmFunctionType(&param_buf);

        const func = c.LLVMGetNamedFunction(self.module, libc_fn.name) orelse
            llvm.addFunction(self.module, std.mem.span(libc_fn.name), fn_type);

        var llvm_args: [8]llvm.Value = undefined;
        for (args[0..@min(args.len, 8)], 0..) |val, i| {
            llvm_args[i] = try self.translateValToLlvm(val);
        }

        const actual_args = llvm_args[0..args.len];
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
        if (args.len < 2) return error.UnsupportedGrinVal;

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
            .Var => |name| blk: {
                // 1. Check params (function parameters and let-bound variables),
                //    keyed by unique ID to distinguish variables with the same base.
                if (self.params.get(name.unique.value)) |v| break :blk v;
                // 2. Nullary constructor: emit its tag discriminant as an i64.
                //    Tracked in: https://github.com/adinapoli/rusholme/issues/410
                if (self.tag_table.discriminantByName(name)) |disc| {
                    break :blk c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                }
                // 3. Top-level function reference: look up the LLVM function by
                //    name and return its pointer (for higher-order use).
                //    This handles passing named functions as arguments, e.g.:
                //      map_it identity xs  =>  identity is a global function ptr.
                var fn_name_buf: [128]u8 = undefined;
                if (name.base.len < fn_name_buf.len) {
                    @memcpy(fn_name_buf[0..name.base.len], name.base);
                    fn_name_buf[name.base.len] = 0;
                    const fn_name_z = fn_name_buf[0..name.base.len :0];
                    if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |fn_val| {
                        break :blk fn_val;
                    }
                }
                std.debug.print("UnsupportedGrinVal: Var {s}_{d} not found in params, tag table, or module\n", .{ name.base, name.unique.value });
                return error.UnsupportedGrinVal;
            },
            .ConstTagNode => |ctn| blk: {
                // Allocate a heap node and return the pointer.
                break :blk try self.translateStoreToValue(.{ .ConstTagNode = ctn }, "node") orelse
                    return error.UnsupportedGrinVal;
            },
            .VarTagNode => {
                // Variable-tag nodes appear in eval/apply stubs — not yet lowerable.
                // tracked in: https://github.com/adinapoli/rusholme/issues/410
                std.debug.print("UnsupportedGrinVal: VarTagNode not yet supported\n", .{});
                return error.UnsupportedGrinVal;
            },
            .ValTag => |t| blk: {
                // Bare tag value — emit its discriminant as i64.
                const disc = self.tag_table.discriminant(t) orelse {
                    std.debug.print("UnsupportedGrinVal: ValTag {s} not in tag table\n", .{t.name.base});
                    return error.UnsupportedGrinVal;
                };
                break :blk c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
            },
        };
    }

    /// Allocate a heap node for a `Val` and return the pointer.
    /// This is the value-returning variant of `translateStore`.
    fn translateStoreToValue(self: *GrinTranslator, val: grin.Val, result_name: []const u8) TranslationError!?llvm.Value {
        switch (val) {
            .ConstTagNode => |ctn| {
                const tag = ctn.tag;
                const n_fields: u32 = @intCast(ctn.fields.len);
                const disc = self.tag_table.discriminant(tag) orelse return error.UnsupportedGrinVal;
                const struct_ty = nodeStructType(n_fields);

                // sizeof(struct_ty) via LLVMSizeOf gives an i64 constant.
                const size_val = c.LLVMSizeOf(struct_ty);
                const malloc_fn = declareMalloc(self.module);
                var malloc_args = [_]llvm.Value{size_val};
                const node_ptr = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(malloc_fn),
                    malloc_fn,
                    &malloc_args,
                    1,
                    nullTerminate(result_name).ptr,
                );

                // Store the tag discriminant at field index 0.
                var tag_idx = [_]llvm.Value{
                    c.LLVMConstInt(llvm.i32Type(), 0, 0),
                    c.LLVMConstInt(llvm.i32Type(), 0, 0),
                };
                const tag_gep = c.LLVMBuildGEP2(self.builder, struct_ty, node_ptr, &tag_idx, 2, "tag_ptr");
                _ = c.LLVMBuildStore(
                    self.builder,
                    c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0),
                    tag_gep,
                );

                // Store each field at index fi+1, cast to ptr if needed.
                for (ctn.fields, 0..) |field, fi| {
                    var raw_val = try self.translateValToLlvm(field);
                    // Fields are stored as opaque ptr; box integers by alloca+store.
                    const field_ty = c.LLVMTypeOf(raw_val);
                    const kind = c.LLVMGetTypeKind(field_ty);
                    const is_ptr = kind == c.LLVMPointerTypeKind;
                    if (!is_ptr) {
                        // Box the scalar: alloca + store, use the pointer.
                        const slot = c.LLVMBuildAlloca(self.builder, field_ty, "box");
                        _ = c.LLVMBuildStore(self.builder, raw_val, slot);
                        raw_val = slot;
                    }
                    var field_idx = [_]llvm.Value{
                        c.LLVMConstInt(llvm.i32Type(), 0, 0),
                        c.LLVMConstInt(llvm.i32Type(), @intCast(fi + 1), 0),
                    };
                    const field_gep = c.LLVMBuildGEP2(self.builder, struct_ty, node_ptr, &field_idx, 2, "field_ptr");
                    _ = c.LLVMBuildStore(self.builder, raw_val, field_gep);
                }

                return node_ptr;
            },
            .Unit => return @as(?llvm.Value, c.LLVMGetUndef(llvm.i32Type())),
            .Var => |name| return @as(?llvm.Value, try self.translateValToLlvm(.{ .Var = name })),
            else => return @as(?llvm.Value, try self.translateValToLlvm(val)),
        }
    }

    fn translateStore(self: *GrinTranslator, val: grin.Val) TranslationError!void {
        _ = try self.translateStoreToValue(val, "stored");
    }

    /// Translate a Case expression into an LLVM switch + per-alt basic blocks.
    ///
    /// The scrutinee is expected to be either:
    ///   a) A heap pointer to a `{ i64 tag, … }` node  (for NodePat / TagPat),
    ///   b) An i64 tag value directly                   (for nullary constructors).
    ///
    /// We load the i64 tag word then emit `LLVMBuildSwitch`.  Each alternative
    /// gets its own basic block; a shared `merge` block is appended after all
    /// alts and becomes the new insertion point.
    fn translateCase(
        self: *GrinTranslator,
        scrutinee: grin.Val,
        alts: []const grin.Alt,
    ) TranslationError!void {
        if (alts.len == 0) return;

        // ── 1. Obtain the tag integer ──────────────────────────────────────
        const scrut_llvm = try self.translateValToLlvm(scrutinee);
        const scrut_ty = c.LLVMTypeOf(scrut_llvm);
        const scrut_kind = c.LLVMGetTypeKind(scrut_ty);
        const is_ptr = scrut_kind == c.LLVMPointerTypeKind;

        const tag_val: llvm.Value = if (is_ptr) blk: {
            // Load the first field (i64 tag) from the heap node.
            // We use a synthetic struct type with 1 field for GEP purposes;
            // the actual node may have more fields but GEP only cares about
            // the type used for offset calculation.
            const base_struct = nodeStructType(0); // {i64} — enough for tag GEP
            var idx = [_]llvm.Value{
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
            };
            const tag_gep = c.LLVMBuildGEP2(self.builder, base_struct, scrut_llvm, &idx, 2, "tag_gep");
            break :blk c.LLVMBuildLoad2(self.builder, llvm.i64Type(), tag_gep, "tag");
        } else scrut_llvm; // Already an i64 discriminant (nullary constructor).

        // ── 2. Build basic blocks ──────────────────────────────────────────
        const merge_bb = c.LLVMAppendBasicBlock(self.current_func, "case.merge");

        // Identify default alt (if any) and non-default alts.
        var default_bb: llvm.BasicBlock = null;
        var default_alt: ?*const grin.Alt = null;

        var alt_bbs = self.allocator.alloc(llvm.BasicBlock, alts.len) catch return error.OutOfMemory;
        defer self.allocator.free(alt_bbs);

        for (alts, 0..) |*alt, i| {
            switch (alt.pat) {
                .DefaultPat => {
                    default_bb = c.LLVMAppendBasicBlock(self.current_func, "case.default");
                    alt_bbs[i] = default_bb;
                    default_alt = alt;
                },
                else => {
                    var name_buf: [32]u8 = undefined;
                    const bb_name = std.fmt.bufPrintZ(&name_buf, "case.alt{d}", .{i}) catch "case.alt";
                    alt_bbs[i] = c.LLVMAppendBasicBlock(self.current_func, bb_name.ptr);
                },
            }
        }

        // If no default alt was found, use the merge block as the default
        // (non-exhaustive match — UB at runtime, acceptable for M1).
        if (default_bb == null) default_bb = merge_bb;

        // ── 3. Emit the switch instruction ────────────────────────────────
        // Count non-default cases for the switch.
        var n_cases: u32 = 0;
        for (alts) |alt| {
            if (alt.pat != .DefaultPat) n_cases += 1;
        }
        const switch_inst = c.LLVMBuildSwitch(self.builder, tag_val, default_bb, n_cases);

        for (alts, 0..) |alt, i| {
            switch (alt.pat) {
                .DefaultPat => {}, // already set as default above
                .NodePat => |np| {
                    const disc = self.tag_table.discriminant(np.tag) orelse return error.UnsupportedGrinVal;
                    const case_val = c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                    c.LLVMAddCase(switch_inst, case_val, alt_bbs[i]);
                },
                .TagPat => |t| {
                    const disc = self.tag_table.discriminant(t) orelse return error.UnsupportedGrinVal;
                    const case_val = c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                    c.LLVMAddCase(switch_inst, case_val, alt_bbs[i]);
                },
                .LitPat => |lit| {
                    const case_val: llvm.Value = switch (lit) {
                        .Int => |int_val| c.LLVMConstInt(llvm.i64Type(), @bitCast(int_val), 1),
                        .Bool => |b| c.LLVMConstInt(llvm.i64Type(), @intFromBool(b), 0),
                        .Char => |ch| c.LLVMConstInt(llvm.i64Type(), ch, 0),
                        else => return error.UnsupportedGrinVal,
                    };
                    c.LLVMAddCase(switch_inst, case_val, alt_bbs[i]);
                },
            }
        }

        // ── 4. Emit each alternative body ────────────────────────────────
        for (alts, 0..) |alt, i| {
            llvm.positionBuilderAtEnd(self.builder, alt_bbs[i]);

            // For NodePat alts: GEP-load each field into params.
            if (alt.pat == .NodePat and is_ptr) {
                const np = alt.pat.NodePat;
                const n_fields: u32 = @intCast(np.fields.len);
                // Use a struct type sized for this specific constructor.
                const struct_ty = nodeStructType(n_fields);
                for (np.fields, 0..) |field_name, fi| {
                    var idx = [_]llvm.Value{
                        c.LLVMConstInt(llvm.i32Type(), 0, 0),
                        c.LLVMConstInt(llvm.i32Type(), @intCast(fi + 1), 0),
                    };
                    const gep = c.LLVMBuildGEP2(
                        self.builder,
                        struct_ty,
                        scrut_llvm,
                        &idx,
                        2,
                        nullTerminate(field_name.base).ptr,
                    );
                    const loaded = c.LLVMBuildLoad2(
                        self.builder,
                        ptrType(),
                        gep,
                        nullTerminate(field_name.base).ptr,
                    );
                    try self.params.put(field_name.unique.value, loaded);
                }
            }

            try self.translateExpr(alt.body);

            // Branch to merge if the alt didn't produce a terminator.
            const cur_bb = c.LLVMGetInsertBlock(self.builder);
            if (cur_bb != null and c.LLVMGetBasicBlockTerminator(cur_bb) == null) {
                _ = c.LLVMBuildBr(self.builder, merge_bb);
            }
        }

        // ── 5. Continue from merge block ──────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, merge_bb);
    }

    fn translateFetch(
        self: *GrinTranslator,
        ptr: grin.Name,
        index: ?u32,
    ) TranslationError!void {
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
        // tracked in: https://github.com/adinapoli/rusholme/issues/390
        _ = self;
        _ = ptr;
        _ = val;
    }

    fn translateReturn(self: *GrinTranslator, val: grin.Val) TranslationError!void {
        const llvm_val = try self.translateValToLlvm(val);
        _ = llvm.buildRet(self.builder, llvm_val);
    }
};

// ═══════════════════════════════════════════════════════════════════════
// Utilities
// ═══════════════════════════════════════════════════════════════════════

/// Return a stack-allocated null-terminated version of `s`.
/// Only safe for names short enough to fit in 128 bytes.
fn nullTerminate(s: []const u8) [:0]const u8 {
    const Buf = struct {
        var buf: [128]u8 = undefined;
    };
    const len = @min(s.len, Buf.buf.len - 1);
    @memcpy(Buf.buf[0..len], s[0..len]);
    Buf.buf[len] = 0;
    return Buf.buf[0..len :0];
}

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

test "TagTable: register and discriminant" {
    const alloc = std.testing.allocator;
    var table = TagTable.init();
    defer table.deinit(alloc);

    const nil_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Nil", .unique = .{ .value = 1 } } };
    const cons_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Cons", .unique = .{ .value = 2 } } };

    try table.register(alloc, nil_tag, 0);
    try table.register(alloc, cons_tag, 2);

    try std.testing.expectEqual(@as(?i64, 0), table.discriminant(nil_tag));
    try std.testing.expectEqual(@as(?i64, 1), table.discriminant(cons_tag));
    try std.testing.expectEqual(@as(?u32, 0), table.fieldCount(nil_tag));
    try std.testing.expectEqual(@as(?u32, 2), table.fieldCount(cons_tag));
}

test "TagTable: isNullaryByName" {
    const alloc = std.testing.allocator;
    var table = TagTable.init();
    defer table.deinit(alloc);

    const nil_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Nil", .unique = .{ .value = 5 } } };
    const cons_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Cons", .unique = .{ .value = 6 } } };

    try table.register(alloc, nil_tag, 0);
    try table.register(alloc, cons_tag, 2);

    const nil_name = grin.Name{ .base = "Nil", .unique = .{ .value = 5 } };
    const cons_name = grin.Name{ .base = "Cons", .unique = .{ .value = 6 } };
    try std.testing.expect(table.isNullaryByName(nil_name));
    try std.testing.expect(!table.isNullaryByName(cons_name));
}

test "TagTable: idempotent re-registration" {
    const alloc = std.testing.allocator;
    var table = TagTable.init();
    defer table.deinit(alloc);

    const tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Just", .unique = .{ .value = 10 } } };
    try table.register(alloc, tag, 1);
    try table.register(alloc, tag, 1); // second call must not change discriminant

    try std.testing.expectEqual(@as(?i64, 0), table.discriminant(tag));
}
