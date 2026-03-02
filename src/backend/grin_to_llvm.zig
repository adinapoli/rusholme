//! GRIN-to-LLVM IR Translator.
//!
//! Translates GRIN IR programs to LLVM IR using the LLVM-C API.
//! This is issue #55: LLVM codegen for GRIN expressions.
//!
//! ## Heap node layout (unified with Zig RTS — #422)
//!
//! Every constructor node is allocated via `rts_alloc(tag, n_fields)` and
//! uses the Zig RTS `Node` layout:
//!
//!   ┌─────────────┬──────────────┬────────────┬────────────────────────┐
//!   │  tag (u64)  │ n_fields(u32)│  _pad(u32) │ field[0] … field[N-1] │
//!   └─────────────┴──────────────┴────────────┴────────────────────────┘
//!
//! The header is 16 bytes; each field slot is 8 bytes (u64).  Field values
//! are stored as raw u64 — either a pointer cast to uintptr (for *Node
//! children) or an integer bit-pattern (for scalars such as Int/Char).
//!
//! Allocation and field I/O go through three RTS helpers:
//!   - `rts_alloc(tag: u64, n_fields: u32) -> *Node`
//!   - `rts_store_field(node: *Node, index: u32, value: u64)`
//!   - `rts_load_field(node: *const Node, index: u32) -> u64`
//!
//! The `tag` discriminant is assigned by `TagTable` — each unique
//! constructor gets a stable `i64` value (0, 1, 2, …).
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
//!   - Store — rts_alloc + rts_store_field (#422)
//!   - Return — emit `ret`
//!   - Block — transparent scoping
//!
//! Fetch and Update remain stubs (tracked in #390).

const std = @import("std");

const grin = @import("../grin/ast.zig");
const FieldType = grin.FieldType;

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
/// discriminant (0, 1, 2, …), records the number of fields, and tracks
/// the FieldType of each field for HPT-lite.
///
/// Built once before translation starts by scanning all `ConstTagNode`
/// values in the program.  The unique value of the tag's name is used as
/// the map key so that identity is name-based, not string-based.
///
/// See: https://github.com/adinapoli/rusholme/issues/449
const TagTable = struct {
    /// Discriminant assigned to each constructor, keyed by name unique.
    discriminants: std.AutoHashMapUnmanaged(u64, i64),
    /// Number of fields for each constructor, keyed by name unique.
    field_counts: std.AutoHashMapUnmanaged(u64, u32),
    /// Field types per constructor, keyed by name unique.
    /// Each slice contains FieldType for each field position.
    /// This is HPT-lite: a simplified type tracking that will be
    /// extended when implementing full HPT (M2.4).
    field_types: std.AutoHashMapUnmanaged(u64, []const FieldType),
    /// Next discriminant to assign.
    next: i64,

    fn init() TagTable {
        return .{
            .discriminants = .{},
            .field_counts = .{},
            .field_types = .{},
            .next = 0,
        };
    }

    fn deinit(self: *TagTable, alloc: std.mem.Allocator) void {
        self.discriminants.deinit(alloc);
        self.field_counts.deinit(alloc);
        // Free each field_types slice
        var iter = self.field_types.iterator();
        while (iter.next()) |entry| {
            alloc.free(entry.value_ptr.*);
        }
        self.field_types.deinit(alloc);
    }

    /// Register a constructor tag with the given field count.
    /// If already registered, this is a no-op (idempotent).
    fn register(self: *TagTable, alloc: std.mem.Allocator, tag: grin.Tag, n_fields: u32) !void {
        const key = tag.name.unique.value;
        if (self.discriminants.contains(key)) return;
        try self.discriminants.put(alloc, key, self.next);
        try self.field_counts.put(alloc, key, n_fields);
        // Default: all fields are ptr (conservative for HPT-lite)
        const types = try alloc.alloc(FieldType, n_fields);
        for (types) |*t| t.* = .ptr;
        try self.field_types.put(alloc, key, types);
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

    /// Return field types for a constructor, or null if unknown.
    fn fieldTypes(self: *const TagTable, tag: grin.Tag) ?[]const FieldType {
        return self.field_types.get(tag.name.unique.value);
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

/// Return the LLVM struct type for the unified node header:
///   { i64 tag, i32 n_fields, i32 _pad }   (16 bytes)
///
/// Used only for GEP into the tag word when loading the discriminant
/// in Case expressions.  Field I/O uses the rts_load_field / rts_store_field
/// RTS helpers instead of direct GEP.
fn nodeHeaderType() llvm.Type {
    var members = [_]llvm.Type{
        llvm.i64Type(), // tag
        llvm.i32Type(), // n_fields
        llvm.i32Type(), // _pad
    };
    return c.LLVMStructType(@ptrCast(&members), 3, 0);
}

/// Declare `rts_alloc(tag: i64, n_fields: i32) -> ptr` in the module if needed.
fn declareRtsAlloc(module: llvm.Module) llvm.Value {
    const name = "rts_alloc";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    var params = [_]llvm.Type{ llvm.i64Type(), llvm.i32Type() };
    const fn_ty = c.LLVMFunctionType(ptrType(), &params, 2, 0);
    return c.LLVMAddFunction(module, name, fn_ty);
}

/// Declare `rts_store_field(node: ptr, index: i32, value: i64) -> void`.
fn declareRtsStoreField(module: llvm.Module) llvm.Value {
    const name = "rts_store_field";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    var params = [_]llvm.Type{ ptrType(), llvm.i32Type(), llvm.i64Type() };
    const fn_ty = c.LLVMFunctionType(llvm.voidType(), &params, 3, 0);
    return c.LLVMAddFunction(module, name, fn_ty);
}

/// Declare `rts_load_field(node: ptr, index: i32) -> i64`.
fn declareRtsLoadField(module: llvm.Module) llvm.Value {
    const name = "rts_load_field";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    var params = [_]llvm.Type{ ptrType(), llvm.i32Type() };
    const fn_ty = c.LLVMFunctionType(llvm.i64Type(), &params, 2, 0);
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

// ═══════════════════════════════════════════════════════════════════════
// HPT-Lite Type Environment
// ═══════════════════════════════════════════════════════════════════════

/// HPT-Lite: Lightweight type propagation environment for LLVM codegen.
///
/// This is a simplified version of full Heap Points-to Analysis.
/// It tracks the FieldType of each GRIN variable so the LLVM backend
/// can emit correctly-typed IR (ptr vs i64 vs f64).
///
/// See: https://github.com/adinapoli/rusholme/issues/449
/// TODO: Replace with full HPT when implementing M2.4.
const TypeEnv = struct {
    /// Maps variable unique IDs to their FieldType.
    var_types: std.AutoHashMapUnmanaged(u64, FieldType),
    /// Reference to the tag table for constructor field types.
    tag_table: *const TagTable,

    fn init() TypeEnv {
        return .{
            .var_types = .{},
            .tag_table = undefined,
        };
    }

    fn deinit(self: *TypeEnv, alloc: std.mem.Allocator) void {
        self.var_types.deinit(alloc);
    }

    fn setTagTable(self: *TypeEnv, table: *const TagTable) void {
        self.tag_table = table;
    }

    fn setVarType(self: *TypeEnv, alloc: std.mem.Allocator, name: grin.Name, ft: FieldType) !void {
        try self.var_types.put(alloc, name.unique.value, ft);
    }

    fn getVarType(self: *const TypeEnv, name: grin.Name) ?FieldType {
        return self.var_types.get(name.unique.value);
    }

    /// Get the type of a GRIN value for LLVM codegen.
    /// Falls back to .ptr (conservative) if type is unknown.
    fn getValType(self: *const TypeEnv, val: grin.Val) FieldType {
        return switch (val) {
            .Lit => |lit| switch (lit) {
                .Int => .i64,
                .Float => .f64,
                .Char => .i64,
                .String => .ptr,
                .Bool => .i64,
            },
            .Unit => .i64, // Unit is unboxed
            .Var => |name| self.getVarType(name) orelse .ptr,
            .ConstTagNode => .ptr, // Allocated node is always a pointer
            .ValTag => .i64, // Bare tags are i64 discriminants
            .VarTagNode => .ptr, // Variable-tag nodes are pointers
        };
    }

    /// Get the type of a field at the given index for a constructor.
    fn getFieldTagType(self: *const TypeEnv, tag: grin.Tag, index: u32) FieldType {
        const types = self.tag_table.fieldTypes(tag) orelse return .ptr;
        if (index >= types.len) return .ptr;
        return types[index];
    }
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
    /// HPT-lite type environment for type-correct LLVM codegen.
    /// See: https://github.com/adinapoli/rusholme/issues/449
    type_env: TypeEnv,
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
            .type_env = TypeEnv.init(),
            .current_func = null,
        };
    }

    pub fn deinit(self: *GrinTranslator) void {
        self.params.deinit();
        self.tag_table.deinit(self.allocator);
        self.type_env.deinit(self.allocator);
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
        // Link TypeEnv to the tag table for field type lookups.
        self.type_env.setTagTable(&self.tag_table);
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

    // ── Multi-module translation ──────────────────────────────────────────

    /// Pre-compute the global tag table from the union of all modules' GRIN
    /// programs.
    ///
    /// Call this ONCE before calling `translateModuleGrin` for each module in
    /// a multi-module build.  The tag table must cover all constructors from
    /// all modules because module B may pattern-match on constructors from
    /// module A.
    ///
    /// Any previously held tag table is released.
    pub fn prepareGlobalTagTable(self: *GrinTranslator, all_prog: grin.Program) TranslationError!void {
        self.tag_table.deinit(self.allocator);
        self.tag_table = buildTagTable(self.allocator, all_prog) catch return error.OutOfMemory;
        // TypeEnv pointer is refreshed inside translateModuleGrin before each
        // module translation (needed because the tag_table field was reassigned).
    }

    /// Translate a single module's GRIN program into a fresh LLVM module.
    ///
    /// The returned module is owned by this translator's context and will be
    /// freed when `deinit` is called.  The caller may write it to a bitcode
    /// file via `llvm.writeBitcodeToFile` and/or merge it into a link-time
    /// module via `llvm.linkModules`.
    ///
    /// `prepareGlobalTagTable` must be called before the first call to this
    /// function so that the tag table covers all constructors.
    ///
    /// Cross-module function calls are handled lazily: if a called function is
    /// not defined in `prog.defs`, the existing `LLVMGetNamedFunction` +
    /// `LLVMAddFunction` fallback in `translateApp` creates an external `declare`
    /// that `llvm.linkModules` resolves at link time.
    pub fn translateModuleGrin(
        self: *GrinTranslator,
        module_name: []const u8,
        prog: grin.Program,
    ) TranslationError!llvm.Module {
        // Refresh the TypeEnv pointer in case prepareGlobalTagTable rebuilt the
        // tag table (which moves it in memory when the old table is deinited and
        // a new one is allocated).
        self.type_env.setTagTable(&self.tag_table);

        const mod = llvm.createModule(module_name, self.ctx);

        // Temporarily point self.module at the new per-module LLVM module so
        // that translateDef emits all functions into it.  Restored afterwards.
        const saved_module = self.module;
        self.module = mod;
        for (prog.defs) |def| {
            try self.translateDef(def);
        }
        self.module = saved_module;

        return mod;
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

        // Translate the body and capture its value if needed.
        // For non-main functions with parameters, we need to return the body's value.
        // See: https://github.com/adinapuli/rusholme/issues/449
        if (!is_main and has_params) {
            const body_val = try self.translateExprToValue(def.body, "result");
            const current_bb = c.LLVMGetInsertBlock(self.builder);
            if (current_bb != null and c.LLVMGetBasicBlockTerminator(current_bb) == null) {
                if (body_val) |val| {
                    _ = llvm.buildRet(self.builder, val);
                } else {
                    _ = llvm.buildRet(self.builder, c.LLVMConstPointerNull(value_type));
                }
            }
        } else {
            try self.translateExpr(def.body);
            // Emit the terminator based on return type — only if the current
            // block does not already have one (a Return expr may have emitted it).
            const current_bb = c.LLVMGetInsertBlock(self.builder);
            if (current_bb != null and c.LLVMGetBasicBlockTerminator(current_bb) == null) {
                if (is_main) {
                    _ = llvm.buildRet(self.builder, c.LLVMConstInt(llvm.i32Type(), 0, 0));
                } else {
                    _ = llvm.buildRetVoid(self.builder);
                }
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
                // matching this tag. Load each field via rts_load_field and
                // bind the names into params so the RHS can reference them.
                const ptr_val = try self.translateExprToValue(lhs, "node") orelse
                    return error.UnsupportedGrinVal;
                const rts_load_fn = declareRtsLoadField(self.module);
                for (ctn.fields, 0..) |field_val, fi| {
                    if (field_val != .Var) continue;
                    const field_var = field_val.Var;
                    var load_args = [_]llvm.Value{
                        ptr_val,
                        c.LLVMConstInt(llvm.i32Type(), fi, 0),
                    };
                    const loaded = c.LLVMBuildCall2(
                        self.builder,
                        llvm.getFunctionType(rts_load_fn),
                        rts_load_fn,
                        &load_args,
                        2,
                        nullTerminate(field_var.base).ptr,
                    );
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
                            const rts_load_fn = declareRtsLoadField(self.module);
                            for (ctn.fields, 0..) |field_val, fi| {
                                if (field_val != .Var) continue;
                                const fv = field_val.Var;
                                var load_args = [_]llvm.Value{
                                    ptr_val,
                                    c.LLVMConstInt(llvm.i32Type(), fi, 0),
                                };
                                const loaded = c.LLVMBuildCall2(
                                    self.builder,
                                    llvm.getFunctionType(rts_load_fn),
                                    rts_load_fn,
                                    &load_args,
                                    2,
                                    nullTerminate(fv.base).ptr,
                                );
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

                // Allocate a node via rts_alloc(tag, n_fields).
                const rts_alloc_fn = declareRtsAlloc(self.module);
                var alloc_args = [_]llvm.Value{
                    c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0),
                    c.LLVMConstInt(llvm.i32Type(), n_fields, 0),
                };
                const node_ptr = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(rts_alloc_fn),
                    rts_alloc_fn,
                    &alloc_args,
                    2,
                    nullTerminate(result_name).ptr,
                );

                // Write each field via rts_store_field(node, index, value_as_u64).
                // Pointer values are cast to i64 via ptrtoint; integer values are
                // already i64.  No boxing via alloca is needed — the RTS field
                // slots are plain u64.
                //
                // For nullary constructors (ValTag), we need to box them first
                // since fields must be pointers to heap nodes.
                // See: https://github.com/adinapuli/rusholme/issues/449
                const rts_store_fn = declareRtsStoreField(self.module);
                for (ctn.fields, 0..) |field, fi| {
                    // Check if field is a nullary constructor that needs boxing
                    const raw_val: llvm.Value = if (field == .ValTag) blk: {
                        // Box the nullary constructor: allocate a node with tag but 0 fields
                        const field_tag = field.ValTag;
                        const field_disc = self.tag_table.discriminant(field_tag) orelse return error.UnsupportedGrinVal;
                        const field_alloc_fn = declareRtsAlloc(self.module);
                        var field_alloc_args = [_]llvm.Value{
                            c.LLVMConstInt(llvm.i64Type(), @bitCast(field_disc), 0),
                            c.LLVMConstInt(llvm.i32Type(), 0, 0), // n_fields = 0
                        };
                        break :blk c.LLVMBuildCall2(
                            self.builder,
                            llvm.getFunctionType(field_alloc_fn),
                            field_alloc_fn,
                            &field_alloc_args,
                            2,
                            "boxed_field",
                        );
                    } else try self.translateValToLlvm(field);
                    
                    const field_ty = c.LLVMTypeOf(raw_val);
                    const kind = c.LLVMGetTypeKind(field_ty);
                    const is_ptr = kind == c.LLVMPointerTypeKind;
                    // Convert to i64: ptrtoint for pointers, keep as-is for integers.
                    const as_u64: llvm.Value = if (is_ptr)
                        c.LLVMBuildPtrToInt(self.builder, raw_val, llvm.i64Type(), "field_u64")
                    else
                        raw_val;
                    var store_args = [_]llvm.Value{
                        node_ptr,
                        c.LLVMConstInt(llvm.i32Type(), fi, 0),
                        as_u64,
                    };
                    _ = c.LLVMBuildCall2(
                        self.builder,
                        llvm.getFunctionType(rts_store_fn),
                        rts_store_fn,
                        &store_args,
                        3,
                        "",
                    );
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
            // Load the i64 tag from the unified node header { i64 tag, i32 n_fields, i32 _pad }.
            // GEP [0, 0] reaches the `tag` field at byte offset 0.
            const header_ty = nodeHeaderType();
            var idx = [_]llvm.Value{
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
            };
            const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, scrut_llvm, &idx, 2, "tag_gep");
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

            // For NodePat alts: load each field via rts_load_field(node, index).
            // Use TypeEnv to determine the correct LLVM type for each field.
            // HPT-lite: This ensures type consistency for LLVM codegen.
            // See: https://github.com/adinapoli/rusholme/issues/449
            if (alt.pat == .NodePat and is_ptr) {
                const np = alt.pat.NodePat;
                const rts_load_fn = declareRtsLoadField(self.module);
                for (np.fields, 0..) |field_name, fi| {
                    var load_args = [_]llvm.Value{
                        scrut_llvm,
                        c.LLVMConstInt(llvm.i32Type(), fi, 0),
                    };
                    const loaded_i64 = c.LLVMBuildCall2(
                        self.builder,
                        llvm.getFunctionType(rts_load_fn),
                        rts_load_fn,
                        &load_args,
                        2,
                        nullTerminate(field_name.base).ptr,
                    );

                    // Get the expected field type from TypeEnv/TagTable.
                    const field_type = self.type_env.getFieldTagType(np.tag, @intCast(fi));

                    // Convert the loaded i64 to the appropriate type.
                    const final_val: llvm.Value = switch (field_type) {
                        .i64 => loaded_i64,
                        .f64 => c.LLVMBuildBitCast(self.builder, loaded_i64, c.LLVMDoubleType(), "as_f64"),
                        .ptr => c.LLVMBuildIntToPtr(self.builder, loaded_i64, ptrType(), "as_ptr"),
                    };

                    try self.params.put(field_name.unique.value, final_val);

                    // Record the type in TypeEnv for downstream use.
                    try self.type_env.setVarType(self.allocator, field_name, field_type);
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

        // Type correction: if the function returns ptr but we have an i64,
        // we need to box the value. This happens for nullary constructors
        // returned from non-main functions.
        // See: https://github.com/adinapuli/rusholme/issues/449
        const val_ty = c.LLVMTypeOf(llvm_val);
        const val_kind = c.LLVMGetTypeKind(val_ty);
        const is_int = val_kind == c.LLVMIntegerTypeKind;

        // Only convert if we have an integer and the current function is a
        // non-main function (which return ptr). Main returns i32 so no conversion.
        if (is_int and self.current_func != null) {
            // Get the function name to check if it's main
            const func_name = c.LLVMGetValueName(self.current_func);
            if (func_name != null) {
                const name_slice = std.mem.span(func_name);
                if (!std.mem.eql(u8, name_slice, "main")) {
                    // Non-main functions return ptr.
                    // For nullary constructors (ValTag), we need to allocate
                    // a heap node with just the tag and no fields.
                    if (val == .ValTag) {
                        // Allocate a node with tag but 0 fields
                        const rts_alloc_fn = declareRtsAlloc(self.module);
                        var alloc_args = [_]llvm.Value{
                            llvm_val, // tag discriminant as i64
                            c.LLVMConstInt(llvm.i32Type(), 0, 0), // n_fields = 0
                        };
                        const node_ptr = c.LLVMBuildCall2(
                            self.builder,
                            llvm.getFunctionType(rts_alloc_fn),
                            rts_alloc_fn,
                            &alloc_args,
                            2,
                            "boxed_tag",
                        );
                        _ = llvm.buildRet(self.builder, node_ptr);
                        return;
                    } else {
                        // For other i64 values, use inttoptr
                        const converted = c.LLVMBuildIntToPtr(self.builder, llvm_val, ptrType(), "ret_as_ptr");
                        _ = llvm.buildRet(self.builder, converted);
                        return;
                    }
                }
            }
        }

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

test "Store emits rts_alloc and rts_store_field instead of malloc" {
    // Build a minimal GRIN program:
    //   main = store (CJust []) ; return ()
    // and verify that the LLVM IR contains calls to rts_alloc / rts_store_field
    // but does NOT contain calls to malloc (i.e. the old layout is gone).
    const alloc = std.testing.allocator;

    const just_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Just", .unique = .{ .value = 1 } } };
    const unit_val = grin.Val{ .Unit = {} };

    // Store (CJust [unit]) ; Return unit
    var store_expr = grin.Expr{ .Store = .{ .ConstTagNode = .{ .tag = just_tag, .fields = &.{unit_val} } } };
    var ret_expr = grin.Expr{ .Return = unit_val };
    var bind_expr = grin.Expr{ .Bind = .{
        .lhs = &store_expr,
        .pat = unit_val,
        .rhs = &ret_expr,
    } };

    const main_def = grin.Def{
        .name = .{ .base = "main", .unique = .{ .value = 0 } },
        .params = &.{},
        .body = &bind_expr,
    };
    const program = grin.Program{ .defs = &.{main_def} };

    var translator = GrinTranslator.init(alloc);
    defer translator.deinit();

    // translateProgram → printModuleToString → dupeZ allocates len+1 bytes
    // (string + null terminator).  Free as [:0]u8 so the GPA size accounting
    // matches the allocation size.
    const ir_raw = try translator.translateProgram(program);
    const ir: [:0]u8 = ir_raw.ptr[0..ir_raw.len :0];
    defer alloc.free(ir);

    // Must call rts_alloc and rts_store_field.
    try std.testing.expect(std.mem.indexOf(u8, ir, "rts_alloc") != null);
    try std.testing.expect(std.mem.indexOf(u8, ir, "rts_store_field") != null);
    // Must NOT call malloc (the old layout is removed).
    try std.testing.expect(std.mem.indexOf(u8, ir, "@malloc") == null);
}
