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
const rts_node = @import("../rts/node.zig");

const llvm = @import("llvm.zig");
const c = llvm.c;

// Known Prelude constants with stable unique IDs
// These are used when variables reference Prelude literals like True, False, etc.
const known = struct {
    pub const true_val = 200; // True
    pub const false_val = 201; // False
    pub const nothing_val = 202; // Nothing
    pub const just_val = 203; // Just
    pub const left_val = 204; // Left
    pub const right_val = 205; // Right
    pub const unit_val = 206; // ()
    pub const nil_val = 207; // []
    pub const cons_val = 208; // (:)
};

// ═══════════════════════════════════════════════════════════════════════
// PrimOp-to-libc Mapping
// ═══════════════════════════════════════════════════════════════════════

/// Centralized mapping from GRIN Prelude/PrimOp function base names to
/// their LLVM equivalents.
const PrimOpMapping = struct {
    fn lookup(name: grin.Name) ?PrimOpResult {
        // RTS IO function mappings.
        //
        // These call into the compiled Rusholme RTS (`src/rts/io.zig`) rather
        // than libc directly.  `rts_putStrLn` / `rts_putStr` are implemented
        // with `std.io`, so the same source compiles to `write()` for native
        // targets and `wasi_snapshot_preview1::fd_write` for wasm32-wasi —
        // no backend-specific adaptations required.
        if (std.mem.eql(u8, name.base, "putStrLn")) {
            return .{
                .libcall = .{
                    .name = "rts_putStrLn",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "putStr")) {
            return .{
                .libcall = .{
                    .name = "rts_putStr",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "print")) {
            return .{
                .libcall = .{
                    // tracked in: https://github.com/adinapoli/rusholme/issues/479
                    // `print` requires Show desugaring; for now, pass the raw
                    // string representation through rts_putStrLn as a fallback.
                    .name = "rts_putStrLn",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "error")) {
            return .{
                .libcall = .{
                    .name = "rts_error",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
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

        // Monad operations for IO (do-notation desugaring, issue #464)
        // In M1, >> and >>= are no-ops that return unit. The actual sequencing
        // is handled by the GRIN bind structure which evaluates actions in order.
        if (std.mem.eql(u8, name.base, ">>")) return .{ .instruction = .{ .seq = {} } };
        if (std.mem.eql(u8, name.base, ">>=")) return .{ .instruction = .{ .seq = {} } };

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
    /// Monadic sequencing (>>) and bind (>>=)
    /// These are no-ops in M1 - the GRIN bind structure handles sequencing
    seq: void,
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
    /// Set of unique IDs that are F-tags (function thunks).
    /// Used by the inline eval loop to distinguish thunks from constructors.
    fun_tags: std.AutoHashMapUnmanaged(u64, void),
    /// Maps F-tag unique IDs to their GRIN names for LLVM function lookup.
    fun_tag_names: std.AutoHashMapUnmanaged(u64, grin.Name),
    /// Next discriminant to assign.
    next: i64,

    fn init() TagTable {
        return .{
            .discriminants = .{},
            .field_counts = .{},
            .field_types = .{},
            .fun_tags = .{},
            .fun_tag_names = .{},
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
        self.fun_tags.deinit(alloc);
        self.fun_tag_names.deinit(alloc);
    }

    /// Register a tag with the given field count.
    /// If already registered, this is a no-op (idempotent).
    /// F-tags (Fun) are also recorded in the fun_tags set for eval dispatch.
    fn register(self: *TagTable, alloc: std.mem.Allocator, tag: grin.Tag, n_fields: u32) !void {
        const key = tag.name.unique.value;
        if (self.discriminants.contains(key)) return;
        try self.discriminants.put(alloc, key, self.next);
        try self.field_counts.put(alloc, key, n_fields);
        // Default: all fields are ptr (conservative for HPT-lite)
        const types = try alloc.alloc(FieldType, n_fields);
        for (types) |*t| t.* = .ptr;
        try self.field_types.put(alloc, key, types);
        // Track F-tags for the inline eval loop in translateCase.
        if (tag.tag_type == .Fun) {
            try self.fun_tags.put(alloc, key, {});
            try self.fun_tag_names.put(alloc, key, tag.name);
        }
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
    /// Buffer for formatting GRIN names as null-terminated C strings.
    /// Used by formatName() to create "base_unique" style names.
    name_buf: [256]u8 align(16) = undefined,
    /// When set, the translator treats a function whose base name matches
    /// this string the same way it treats "main" — using i64 return type
    /// and emitting the name without a unique suffix. This allows the REPL
    /// JIT engine to use per-evaluation entry point names (e.g.
    /// "repl_expr_0", "repl_expr_1") instead of always colliding on "main".
    repl_entry_point: ?[]const u8 = null,

    /// Extra GRIN defs to scan for tag registration but NOT translate.
    /// Used by the REPL JIT to propagate F-tags from prior declaration
    /// sessions so that the inline eval loop in `forceValueToWhnf` can
    /// handle thunks created by previously-compiled functions.
    extra_tag_defs: []const grin.Def = &.{},

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

    /// Returns true if `base` is an entry-point name — either the standard
    /// "main" or the REPL-specific entry point set via `repl_entry_point`.
    fn isEntryPoint(self: *const GrinTranslator, base: []const u8) bool {
        if (std.mem.eql(u8, base, "main")) return true;
        if (self.repl_entry_point) |ep| return std.mem.eql(u8, base, ep);
        return false;
    }

    /// Like `isEntryPoint`, but checks the LLVM function name string
    /// (a null-terminated C string obtained from `LLVMGetValueName`).
    fn isEntryPointFunc(self: *const GrinTranslator, func_name: []const u8) bool {
        return self.isEntryPoint(func_name);
    }

    /// Allocate a Unit heap node and return its address as an i64.
    ///
    /// Used by entry-point functions that need to return a
    /// distinguishable "no value" result (as opposed to integer 0,
    /// which is boolean False).
    fn buildUnitNode(self: *GrinTranslator) llvm.Value {
        const rts_alloc_fn = declareRtsAlloc(self.module);
        const unit_tag = @intFromEnum(rts_node.Tag.Unit);
        const unit_disc = c.LLVMConstInt(llvm.i64Type(), unit_tag, 0);
        var alloc_args = [_]llvm.Value{
            unit_disc,
            c.LLVMConstInt(llvm.i32Type(), 0, 0), // n_fields = 0
        };
        const node_ptr = c.LLVMBuildCall2(
            self.builder,
            llvm.getFunctionType(rts_alloc_fn),
            rts_alloc_fn,
            &alloc_args,
            2,
            "unit",
        );
        return c.LLVMBuildPtrToInt(self.builder, node_ptr, llvm.i64Type(), "unit_i64");
    }

    /// Translate the entire GRIN program into the LLVM module.
    /// Returns the underlying LLVM Module for direct use (e.g. object emission).
    /// The module is owned by this translator's context — do not dispose it
    /// separately; it is freed when the translator is deinited.
    pub fn translateProgramToModule(self: *GrinTranslator, program: grin.Program) TranslationError!llvm.Module {
        // Build the tag table once before any translation.
        self.tag_table = buildTagTable(self.allocator, program) catch return error.OutOfMemory;
        // Also scan extra defs (from prior REPL sessions) for tag
        // registration. These defs are NOT translated — they were
        // already compiled in a previous JIT session — but their tags
        // must be known so that forceValueToWhnf can handle thunks
        // created by those functions.
        for (self.extra_tag_defs) |def| {
            scanExprForTags(self.allocator, def.body, &self.tag_table) catch return error.OutOfMemory;
        }
        // Link TypeEnv to the tag table for field type lookups.
        self.type_env.setTagTable(&self.tag_table);

        // Emit __rhc_force(ptr) → ptr once the tag table is complete.
        // User-defined function Returns call this to force thunks to WHNF.
        // Only emitted for whole-program (non-REPL) compilation — the REPL
        // uses inline forceValueToWhnf at the entry-point return instead.
        if (self.tag_table.fun_tags.count() > 0 and self.repl_entry_point == null) {
            try self.emitForceFunction();
        }

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
        // Entry-point functions ("main" or REPL entry points like "repl_expr_0")
        // use a specific return type: native `main` returns i32 (C ABI),
        // REPL entry points return i64 (raw value or heap pointer).
        // All other user-defined functions use an opaque `ptr` representation
        // for parameters and return values — GRIN has no type information at
        // this stage and all heap values are pointers.
        const is_entry = self.isEntryPoint(def.name.base);
        const is_repl_entry = if (self.repl_entry_point) |ep| std.mem.eql(u8, def.name.base, ep) else false;
        const has_params = def.params.len > 0;
        const value_type = if (is_entry) (if (is_repl_entry) llvm.i64Type() else llvm.i32Type()) else ptrType();
        const ret_type = if (is_entry) value_type else if (has_params) value_type else llvm.voidType();

        // Parameter types: i32 for main (no params), ptr for all others.
        var param_types: [8]llvm.Type = undefined;
        for (def.params[0..@min(def.params.len, 8)], 0..) |_, i| {
            param_types[i] = value_type;
        }

        const fn_type = llvm.functionType(ret_type, param_types[0..def.params.len], false);
        const fn_name_z = self.formatName(def.name);
        // Check if function was already forward-declared; if so, reuse it.
        // This prevents LLVM from adding .1 suffix due to name collision.
        const func = c.LLVMGetNamedFunction(self.module, fn_name_z) orelse
            llvm.addFunction(self.module, fn_name_z, fn_type);
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

        // Translate the body and capture its value for return.
        //
        // Functions with parameters and REPL entry points both need
        // to capture the body's value and return it. The difference:
        //   - Parameterized functions return `ptr`
        //   - REPL entry points return `i64` (raw value or heap pointer)
        //   - Native `main` falls through to the void/unit path below
        //
        // See: https://github.com/adinapuli/rusholme/issues/449
        if ((!is_entry and has_params) or is_repl_entry) {
            const body_val = try self.translateExprToValue(def.body, "result");
            const current_bb = c.LLVMGetInsertBlock(self.builder);
            if (current_bb != null and c.LLVMGetBasicBlockTerminator(current_bb) == null) {
                if (body_val) |val| {
                    if (is_repl_entry) {
                        // REPL entry points return i64. The body value
                        // may be a ptr (from function calls) or an i64
                        // (from literal returns). Cast if needed.
                        // Compare by type kind rather than type identity
                        // because ptrType() uses the global context while
                        // the value lives in the translator's context.
                        const val_kind = c.LLVMGetTypeKind(c.LLVMTypeOf(val));
                        if (val_kind == c.LLVMPointerTypeKind) {
                            // IO primops return a null pointer placeholder
                            // (see translateAppToValue). Treat as Unit.
                            if (c.LLVMIsAConstantPointerNull(val) != null) {
                                _ = llvm.buildRet(self.builder, self.buildUnitNode());
                            } else {
                                // Force any F-tagged thunks to WHNF before
                                // returning. The user expects REPL results
                                // in normal form, not unevaluated thunks.
                                const forced = if (self.tag_table.fun_tags.count() > 0)
                                    try self.forceValueToWhnf(val)
                                else
                                    val;
                                const as_i64 = c.LLVMBuildPtrToInt(self.builder, forced, llvm.i64Type(), "ret_i64");
                                _ = llvm.buildRet(self.builder, as_i64);
                            }
                        } else {
                            _ = llvm.buildRet(self.builder, val);
                        }
                    } else {
                        // Non-REPL function: force thunks before returning.
                        const val_kind2 = c.LLVMGetTypeKind(c.LLVMTypeOf(val));
                        const forced = if (val_kind2 == c.LLVMPointerTypeKind)
                            self.callForceIfNeeded(val)
                        else
                            val;
                        _ = llvm.buildRet(self.builder, forced);
                    }
                } else {
                    if (is_repl_entry) {
                        // Body returned no value (e.g. IO action) —
                        // return a Unit heap node so the REPL displays
                        // nothing rather than a random integer.
                        _ = llvm.buildRet(self.builder, self.buildUnitNode());
                    } else {
                        _ = llvm.buildRet(self.builder, c.LLVMConstPointerNull(value_type));
                    }
                }
            }
        } else {
            try self.translateExpr(def.body);
            // Emit the terminator based on return type — only if the current
            // block does not already have one (a Return expr may have emitted it).
            const current_bb = c.LLVMGetInsertBlock(self.builder);
            if (current_bb != null and c.LLVMGetBasicBlockTerminator(current_bb) == null) {
                if (is_repl_entry) {
                    // REPL entry point: return a Unit heap node so
                    // formatJitResult can distinguish unit from boolean False.
                    _ = llvm.buildRet(self.builder, self.buildUnitNode());
                } else if (is_entry) {
                    // Native main: return 0 (success exit code, C ABI).
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
            .Fetch => |f| {
                // In the unified heap layout, fetch is a pass-through: the
                // pointer IS the node.  Return the pointer value so that
                // `fetch p >>= \node -> ...` binds `node` to `p`'s value.
                return @as(?llvm.Value, try self.translateValToLlvm(.{ .Var = f.ptr }));
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
            // Return a null pointer for PrimOps so that bindings still work.
            // The value itself isn't used for IO actions, but the variable
            // needs to be registered in params so it can be referenced in
            // subsequent expressions (e.g., passed to >> for sequencing).
            return c.LLVMConstPointerNull(ptrType());
        }

        // User-defined function call.
        var llvm_args: [8]llvm.Value = undefined;
        const arg_count = @min(args.len, 8);
        for (args[0..arg_count], 0..) |val, i| {
            llvm_args[i] = try self.translateValToLlvm(val);
        }

        // Detect calls to `main` from the REPL entry point.
        // `main` was compiled with an i32 return type (C ABI exit code),
        // but the generic user-function call path assumes ptr return type.
        // Calling main for its side effects (IO) and discarding its result
        // avoids the type mismatch. The REPL entry-point return logic
        // handles null body_val by returning a Unit heap node.
        //
        // Note: `main` typically lives in a separate JIT dylib (loaded via
        // `:l` / addDeclarations), so LLVMGetNamedFunction may not find it
        // in the current module. We forward-declare it with the correct
        // signature so the ORC linker resolves it at execution time.
        if (std.mem.eql(u8, name.base, "main") and self.repl_entry_point != null) {
            const fn_name_z = self.formatName(name);
            const main_fn_type = llvm.functionType(llvm.i32Type(), &.{}, false);
            const func = c.LLVMGetNamedFunction(self.module, fn_name_z) orelse
                llvm.addFunction(self.module, fn_name_z, main_fn_type);
            _ = c.LLVMBuildCall2(
                self.builder,
                main_fn_type,
                func,
                @ptrCast(&llvm_args),
                @intCast(arg_count),
                "",
            );
            return null;
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
            const fn_name_z = self.formatName(name);
            if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |existing| break :blk existing;
            break :blk llvm.addFunction(self.module, fn_name_z, fn_type);
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
            const fn_name_z = self.formatName(name);
            if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |existing| break :blk existing;
            break :blk llvm.addFunction(self.module, fn_name_z, fn_type);
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
        // seq is a no-op that doesn't need arguments
        if (instr == .seq) {
            // Monadic sequencing - nothing to do, the bind structure handles it
            return;
        }

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
            .seq => unreachable, // handled above
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
                // 2. Check if variable is a known Prelude constant (True, False, None, etc.)
                //    These have stable unique IDs and should be emitted as literals.
                switch (name.unique.value) {
                    known.true_val, known.false_val => break :blk c.LLVMConstInt(llvm.i64Type(), @bitCast(@as(i64, if (name.unique.value == known.true_val) 1 else 0)), 1),
                    known.unit_val => break :blk self.buildUnitNode(),
                    else => {},
                }

                // 2b. If not a known literal, check tag discriminant for nullary constructors.
                //    Tracked in: https://github.com/adinapoli/rusholme/issues/410
                if (self.tag_table.discriminantByName(name)) |disc| {
                    break :blk c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                }
                // 3. Top-level function reference: look up the LLVM function by
                //    full name (base + unique suffix) and return its pointer (for
                //    higher-order use).
                //    This handles passing named functions as arguments, e.g.:
                //      map_it identity xs  =>  identity becomes a global function ptr.
                const fn_name_z = self.formatName(name);
                if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |fn_val| {
                    break :blk fn_val;
                }
                // Cross-module function reference: forward-declare as
                // external so the ORC linker can resolve it from a
                // previously-loaded module. This mirrors the pattern
                // used by translateApp for unknown function calls.
                const ext_fn_type = llvm.functionType(ptrType(), &.{}, false);
                break :blk llvm.addFunction(self.module, fn_name_z, ext_fn_type);
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

        // ── 1. Obtain scrutinee and check if it's a heap pointer ───────────
        const scrut_llvm = try self.translateValToLlvm(scrutinee);
        const scrut_ty = c.LLVMTypeOf(scrut_llvm);
        const scrut_kind = c.LLVMGetTypeKind(scrut_ty);
        const is_ptr = scrut_kind == c.LLVMPointerTypeKind;

        // ── 1b. Inline eval loop (laziness) ────────────────────────────────
        //
        // If the scrutinee is a heap pointer, it may be an unevaluated thunk
        // (F-tag) or an indirection (Ind).  We insert a loop that forces
        // thunks and follows indirections until the value is in WHNF.
        //
        //   eval.entry:
        //     %scrut_phi = phi [original, entry] [forced, eval.ind] [result, eval.ftag.*]
        //     tag = load %scrut_phi.tag
        //     switch tag: F-tags → force, Ind → follow, default → case.dispatch

        // The "current scrutinee" used by the rest of the function.
        // For non-pointer scrutinees, no eval loop is needed.
        var cur_scrut: llvm.Value = scrut_llvm;
        var cur_tag: llvm.Value = undefined;

        if (is_ptr and self.tag_table.fun_tags.count() > 0) {
            const entry_bb = c.LLVMGetInsertBlock(self.builder);

            // Create the eval loop header and dispatch target.
            const eval_bb = c.LLVMAppendBasicBlock(self.current_func, "eval.entry");
            const dispatch_bb = c.LLVMAppendBasicBlock(self.current_func, "case.dispatch");

            // Branch from current block to eval loop.
            _ = c.LLVMBuildBr(self.builder, eval_bb);

            // ── eval.entry: phi + tag load + switch ──────────────────────
            llvm.positionBuilderAtEnd(self.builder, eval_bb);
            const phi = c.LLVMBuildPhi(self.builder, ptrType(), "scrut.eval");

            const header_ty = nodeHeaderType();
            var tag_idx = [_]llvm.Value{
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
            };
            const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "eval.tag_gep");
            const tag_val = c.LLVMBuildLoad2(self.builder, llvm.i64Type(), tag_gep, "eval.tag");

            // Count F-tags + 1 for Ind.
            const n_eval_cases = @as(u32, @intCast(self.tag_table.fun_tags.count())) + 1;
            const eval_switch = c.LLVMBuildSwitch(self.builder, tag_val, dispatch_bb, n_eval_cases);

            // ── Ind case: follow indirection ─────────────────────────────
            const ind_bb = c.LLVMAppendBasicBlock(self.current_func, "eval.ind");
            const ind_disc = c.LLVMConstInt(llvm.i64Type(), 0x101, 0); // Tag.Ind
            c.LLVMAddCase(eval_switch, ind_disc, ind_bb);

            llvm.positionBuilderAtEnd(self.builder, ind_bb);
            const rts_load_fn = declareRtsLoadField(self.module);
            var ind_load_args = [_]llvm.Value{
                phi,
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
            };
            const ind_target_i64 = c.LLVMBuildCall2(
                self.builder,
                llvm.getFunctionType(rts_load_fn),
                rts_load_fn,
                &ind_load_args,
                2,
                "ind.target",
            );
            const ind_target = c.LLVMBuildIntToPtr(self.builder, ind_target_i64, ptrType(), "ind.ptr");
            _ = c.LLVMBuildBr(self.builder, eval_bb);

            // ── F-tag cases: force thunk ─────────────────────────────────
            // Collect all incoming phi values: entry_bb→scrut_llvm, ind_bb→ind_target, plus each ftag_bb→result.
            var phi_incoming_vals = std.ArrayListUnmanaged(llvm.Value){};
            defer phi_incoming_vals.deinit(self.allocator);
            var phi_incoming_bbs = std.ArrayListUnmanaged(llvm.BasicBlock){};
            defer phi_incoming_bbs.deinit(self.allocator);

            // First two: entry and ind.
            phi_incoming_vals.append(self.allocator, scrut_llvm) catch return error.OutOfMemory;
            phi_incoming_bbs.append(self.allocator, entry_bb) catch return error.OutOfMemory;
            phi_incoming_vals.append(self.allocator, ind_target) catch return error.OutOfMemory;
            phi_incoming_bbs.append(self.allocator, ind_bb) catch return error.OutOfMemory;

            var ftag_iter = self.tag_table.fun_tags.iterator();
            while (ftag_iter.next()) |ftag_entry| {
                const ftag_unique = ftag_entry.key_ptr.*;
                const ftag_disc = self.tag_table.discriminants.get(ftag_unique) orelse continue;
                const ftag_name = self.tag_table.fun_tag_names.get(ftag_unique) orelse continue;
                const ftag_n_fields = self.tag_table.field_counts.get(ftag_unique) orelse 0;

                const ftag_bb = c.LLVMAppendBasicBlock(self.current_func, "eval.ftag");
                c.LLVMAddCase(eval_switch, c.LLVMConstInt(llvm.i64Type(), @bitCast(ftag_disc), 0), ftag_bb);

                llvm.positionBuilderAtEnd(self.builder, ftag_bb);

                // Load captured arguments from the thunk node's fields.
                var call_args: [8]llvm.Value = undefined;
                const n_args = @min(ftag_n_fields, 8);
                for (0..n_args) |fi| {
                    var fld_load_args = [_]llvm.Value{
                        phi,
                        c.LLVMConstInt(llvm.i32Type(), @intCast(fi), 0),
                    };
                    const loaded_i64 = c.LLVMBuildCall2(
                        self.builder,
                        llvm.getFunctionType(rts_load_fn),
                        rts_load_fn,
                        &fld_load_args,
                        2,
                        "ftag.arg",
                    );
                    // Thunk fields are pointers (heap nodes).
                    call_args[fi] = c.LLVMBuildIntToPtr(self.builder, loaded_i64, ptrType(), "ftag.ptr");
                }

                // Call the function.
                const fn_name_z = self.formatName(ftag_name);
                var param_types: [8]llvm.Type = undefined;
                for (0..n_args) |pi| param_types[pi] = ptrType();
                const fn_type = llvm.functionType(ptrType(), param_types[0..n_args], false);
                const func = c.LLVMGetNamedFunction(self.module, fn_name_z) orelse
                    llvm.addFunction(self.module, fn_name_z, fn_type);
                const result = c.LLVMBuildCall2(
                    self.builder,
                    fn_type,
                    func,
                    @ptrCast(&call_args),
                    @intCast(n_args),
                    "ftag.result",
                );

                // Update the thunk with an indirection: tag = Ind, field[0] = result.
                const upd_tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "ftag.upd.tag");
                _ = c.LLVMBuildStore(self.builder, c.LLVMConstInt(llvm.i64Type(), 0x101, 0), upd_tag_gep);
                const rts_store_fn = declareRtsStoreField(self.module);
                const result_u64 = c.LLVMBuildPtrToInt(self.builder, result, llvm.i64Type(), "ftag.upd.u64");
                var upd_store_args = [_]llvm.Value{
                    phi,
                    c.LLVMConstInt(llvm.i32Type(), 0, 0),
                    result_u64,
                };
                _ = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(rts_store_fn),
                    rts_store_fn,
                    &upd_store_args,
                    3,
                    "",
                );

                // Loop back to re-eval the result.
                _ = c.LLVMBuildBr(self.builder, eval_bb);

                phi_incoming_vals.append(self.allocator, result) catch return error.OutOfMemory;
                phi_incoming_bbs.append(self.allocator, ftag_bb) catch return error.OutOfMemory;
            }

            // Wire up the phi node.
            c.LLVMAddIncoming(
                phi,
                @ptrCast(phi_incoming_vals.items.ptr),
                @ptrCast(phi_incoming_bbs.items.ptr),
                @intCast(phi_incoming_vals.items.len),
            );

            // Continue from dispatch block with the resolved scrutinee.
            llvm.positionBuilderAtEnd(self.builder, dispatch_bb);
            cur_scrut = phi;
            cur_tag = tag_val;
        } else if (is_ptr) {
            // No F-tags in program — just load the tag directly (no eval loop).
            const header_ty = nodeHeaderType();
            var idx = [_]llvm.Value{
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
            };
            const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, scrut_llvm, &idx, 2, "tag_gep");
            cur_tag = c.LLVMBuildLoad2(self.builder, llvm.i64Type(), tag_gep, "tag");
        } else {
            cur_tag = scrut_llvm; // Already an i64 discriminant (nullary constructor).
        }

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
        const switch_inst = c.LLVMBuildSwitch(self.builder, cur_tag, default_bb, n_cases);

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
                        cur_scrut,
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
        // `update p v` overwrites the node at `p` with an indirection to `v`.
        // After update, the node's tag becomes Ind (0x101) and field[0] holds
        // a pointer to `v`.  Subsequent eval calls will follow the indirection.
        const p_val = try self.translateValToLlvm(.{ .Var = ptr });
        const v_val = try self.translateValToLlvm(val);

        // 1. Write the Ind tag (0x101) into the node's tag field.
        const header_ty = nodeHeaderType();
        var idx = [_]llvm.Value{
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, p_val, &idx, 2, "upd.tag_gep");
        _ = c.LLVMBuildStore(self.builder, c.LLVMConstInt(llvm.i64Type(), 0x101, 0), tag_gep);

        // 2. Write `v` into field[0] via rts_store_field(p, 0, ptrtoint(v)).
        const rts_store_fn = declareRtsStoreField(self.module);
        const v_kind = c.LLVMGetTypeKind(c.LLVMTypeOf(v_val));
        const v_as_u64: llvm.Value = if (v_kind == c.LLVMPointerTypeKind)
            c.LLVMBuildPtrToInt(self.builder, v_val, llvm.i64Type(), "upd.v_u64")
        else
            v_val;
        var store_args = [_]llvm.Value{
            p_val,
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
            v_as_u64,
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

    fn translateReturn(self: *GrinTranslator, val: grin.Val) TranslationError!void {
        const llvm_val = try self.translateValToLlvm(val);

        // Type correction: if the function returns ptr but we have an i64,
        // we need to box the value. This happens for nullary constructors
        // returned from non-main functions.
        // See: https://github.com/adinapuli/rusholme/issues/449
        const val_ty = c.LLVMTypeOf(llvm_val);
        const val_kind = c.LLVMGetTypeKind(val_ty);
        const is_int = val_kind == c.LLVMIntegerTypeKind;
        const is_ptr = val_kind == c.LLVMPointerTypeKind;

        if (self.current_func != null) {
            const func_name = c.LLVMGetValueName(self.current_func);
            if (func_name != null) {
                const name_slice = std.mem.span(func_name);
                const is_repl_ep = if (self.repl_entry_point) |ep| std.mem.eql(u8, name_slice, ep) else false;
                const is_native_main = std.mem.eql(u8, name_slice, "main");

                if (is_repl_ep) {
                    // REPL entry points return i64 (raw value or heap pointer).
                    if (is_ptr) {
                        // Force any F-tagged thunks to WHNF before returning.
                        // The user expects REPL results in normal form.
                        const forced = if (self.tag_table.fun_tags.count() > 0)
                            try self.forceValueToWhnf(llvm_val)
                        else
                            llvm_val;
                        const converted = c.LLVMBuildPtrToInt(self.builder, forced, llvm.i64Type(), "ptr_to_i64");
                        _ = llvm.buildRet(self.builder, converted);
                        return;
                    } else if (is_int) {
                        const val_width = c.LLVMGetIntTypeWidth(val_ty);
                        if (val_width == 32) {
                            const converted = c.LLVMBuildZExt(self.builder, llvm_val, llvm.i64Type(), "i32_to_i64");
                            _ = llvm.buildRet(self.builder, converted);
                            return;
                        }
                        _ = llvm.buildRet(self.builder, llvm_val);
                        return;
                    }
                } else if (!is_native_main) {
                    // Non-main, non-REPL functions return ptr.
                    // Force any F-tagged thunks to WHNF before returning
                    // so that callers always receive evaluated values.
                    if (is_ptr) {
                        const forced = self.callForceIfNeeded(llvm_val);
                        _ = llvm.buildRet(self.builder, forced);
                        return;
                    }
                    // Main returns i32 so no conversion needed — it falls
                    // through to the default buildRet below.
                    if (is_int) {
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
                // Native main: fall through to default buildRet (returns i32 as-is).
            }
        }

        _ = llvm.buildRet(self.builder, llvm_val);
    }

    /// Format a GRIN Name as a null-terminated C string using the translator's buffer.
    ///
    /// Special cases:
    ///   - Entry-point names ("main" or the REPL entry point): use the base
    ///     name without a unique suffix so the linker/JIT can find them.
    ///   - Everything else: use "base_unique" including unique 0.
    fn formatName(self: *GrinTranslator, name: grin.Name) [:0]const u8 {
        // Entry-point names are emitted verbatim (no _unique suffix).
        if (self.isEntryPoint(name.base)) {
            const len = @min(name.base.len, self.name_buf.len - 1);
            @memcpy(self.name_buf[0..len], name.base[0..len]);
            self.name_buf[len] = 0;
            return self.name_buf[0..len :0];
        }

        // For all other names, always include the unique suffix.
        // This is critical for the linker to correctly resolve references.
        // The unique ID is what distinguishes variables with the same base name.
        const written = std.fmt.bufPrint(&self.name_buf, "{s}_{d}", .{ name.base, name.unique.value }) catch "";
        self.name_buf[written.len] = 0;
        return self.name_buf[0..written.len :0];
    }

    // ── Standalone __rhc_force function ──────────────────────────────────
    //
    // The whole-program compiler emits a single `__rhc_force(ptr) → ptr`
    // function that forces a heap pointer to WHNF.  User-defined function
    // Returns call it instead of inlining the eval loop at every return
    // site, keeping code size under control.
    //
    // The REPL path continues to use the inline `forceValueToWhnf` because
    // it needs cross-session tag accumulation via `extra_tag_defs`.

    /// Emit the `__rhc_force` function into the current module.
    ///
    /// Must be called after the tag table is fully populated (i.e. after
    /// `buildTagTable` and any `scanExprForTags` calls).  The function
    /// contains the same eval loop as `forceValueToWhnf` but as a real
    /// callable function rather than inlined IR.
    fn emitForceFunction(self: *GrinTranslator) TranslationError!void {
        const ptr_ty = ptrType();
        const i64_ty = llvm.i64Type();
        const header_ty = nodeHeaderType();
        const rts_load_fn = declareRtsLoadField(self.module);
        const rts_store_fn = declareRtsStoreField(self.module);

        // fn __rhc_force(ptr) -> ptr
        var param_types = [_]llvm.Type{ptr_ty};
        const fn_type = llvm.functionType(ptr_ty, &param_types, false);
        const func = llvm.addFunction(self.module, "__rhc_force", fn_type);

        // Save and restore builder/function state so translateDef is not
        // affected by our temporary positioning.
        const saved_func = self.current_func;
        const saved_bb = c.LLVMGetInsertBlock(self.builder);
        defer {
            self.current_func = saved_func;
            if (saved_bb != null) llvm.positionBuilderAtEnd(self.builder, saved_bb);
        }
        self.current_func = func;

        const param = c.LLVMGetParam(func, 0);
        const entry_bb = llvm.appendBasicBlock(func, "entry");
        const eval_bb = c.LLVMAppendBasicBlock(func, "eval");
        const check_bb = c.LLVMAppendBasicBlock(func, "check");
        const done_bb = c.LLVMAppendBasicBlock(func, "done");

        // ── entry: branch to eval loop ─────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, entry_bb);
        _ = c.LLVMBuildBr(self.builder, eval_bb);

        // ── eval: phi + heap-pointer guard ─────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, eval_bb);
        const phi = c.LLVMBuildPhi(self.builder, ptr_ty, "cur");

        // Runtime guard: only dereference if the pointer looks like a
        // valid heap node (aligned to 8 bytes AND above page zero).
        // Raw integers stored via inttoptr (e.g. 42) fail this check.
        const ptr_as_int = c.LLVMBuildPtrToInt(self.builder, phi, i64_ty, "ptr_int");
        const align_bits = c.LLVMBuildAnd(self.builder, ptr_as_int, c.LLVMConstInt(i64_ty, 7, 0), "align");
        const is_aligned = c.LLVMBuildICmp(self.builder, c.LLVMIntEQ, align_bits, c.LLVMConstInt(i64_ty, 0, 0), "aligned");
        const is_above_min = c.LLVMBuildICmp(self.builder, c.LLVMIntUGT, ptr_as_int, c.LLVMConstInt(i64_ty, 4096, 0), "above_min");
        const is_heap_ptr = c.LLVMBuildAnd(self.builder, is_aligned, is_above_min, "is_heap");
        _ = c.LLVMBuildCondBr(self.builder, is_heap_ptr, check_bb, done_bb);

        // ── check: tag load + switch ───────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, check_bb);
        var tag_idx = [_]llvm.Value{
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "tag_gep");
        const tag_val = c.LLVMBuildLoad2(self.builder, i64_ty, tag_gep, "tag");

        const n_cases = @as(u32, @intCast(self.tag_table.fun_tags.count())) + 1;
        const sw = c.LLVMBuildSwitch(self.builder, tag_val, done_bb, n_cases);

        // ── Ind case: follow indirection ───────────────────────────────
        const ind_bb = c.LLVMAppendBasicBlock(func, "ind");
        c.LLVMAddCase(sw, c.LLVMConstInt(i64_ty, 0x101, 0), ind_bb);

        llvm.positionBuilderAtEnd(self.builder, ind_bb);
        var ind_load_args = [_]llvm.Value{
            phi,
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const ind_target_i64 = c.LLVMBuildCall2(
            self.builder,
            llvm.getFunctionType(rts_load_fn),
            rts_load_fn,
            &ind_load_args,
            2,
            "ind_target",
        );
        const ind_target = c.LLVMBuildIntToPtr(self.builder, ind_target_i64, ptr_ty, "ind_ptr");
        _ = c.LLVMBuildBr(self.builder, eval_bb);

        // ── Phi incoming values ────────────────────────────────────────
        var phi_vals = std.ArrayListUnmanaged(llvm.Value){};
        defer phi_vals.deinit(self.allocator);
        var phi_bbs = std.ArrayListUnmanaged(llvm.BasicBlock){};
        defer phi_bbs.deinit(self.allocator);

        phi_vals.append(self.allocator, param) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, entry_bb) catch return error.OutOfMemory;
        phi_vals.append(self.allocator, ind_target) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, ind_bb) catch return error.OutOfMemory;

        // ── F-tag cases: force thunk ───────────────────────────────────
        var ftag_iter = self.tag_table.fun_tags.iterator();
        while (ftag_iter.next()) |ftag_entry| {
            const ftag_unique = ftag_entry.key_ptr.*;
            const ftag_disc = self.tag_table.discriminants.get(ftag_unique) orelse continue;
            const ftag_name = self.tag_table.fun_tag_names.get(ftag_unique) orelse continue;
            const ftag_n_fields = self.tag_table.field_counts.get(ftag_unique) orelse 0;

            const ftag_bb = c.LLVMAppendBasicBlock(func, "ftag");
            c.LLVMAddCase(sw, c.LLVMConstInt(i64_ty, @bitCast(ftag_disc), 0), ftag_bb);

            llvm.positionBuilderAtEnd(self.builder, ftag_bb);

            // Load captured arguments from thunk fields.
            var call_args: [8]llvm.Value = undefined;
            const n_args = @min(ftag_n_fields, 8);
            for (0..n_args) |fi| {
                var fld_args = [_]llvm.Value{
                    phi,
                    c.LLVMConstInt(llvm.i32Type(), @intCast(fi), 0),
                };
                const loaded = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(rts_load_fn),
                    rts_load_fn,
                    &fld_args,
                    2,
                    "arg",
                );
                call_args[fi] = c.LLVMBuildIntToPtr(self.builder, loaded, ptr_ty, "arg_ptr");
            }

            // Call the thunk's function.
            const fn_name_z = self.formatName(ftag_name);
            var fn_param_types: [8]llvm.Type = undefined;
            for (0..n_args) |pi| fn_param_types[pi] = ptr_ty;
            const callee_type = llvm.functionType(ptr_ty, fn_param_types[0..n_args], false);
            const callee = c.LLVMGetNamedFunction(self.module, fn_name_z) orelse
                llvm.addFunction(self.module, fn_name_z, callee_type);
            const result = c.LLVMBuildCall2(
                self.builder,
                callee_type,
                callee,
                @ptrCast(&call_args),
                @intCast(n_args),
                "result",
            );

            // Memoize: overwrite thunk with Ind → result.
            const upd_tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "upd_tag");
            _ = c.LLVMBuildStore(self.builder, c.LLVMConstInt(i64_ty, 0x101, 0), upd_tag_gep);
            const result_u64 = c.LLVMBuildPtrToInt(self.builder, result, i64_ty, "upd_u64");
            var upd_args = [_]llvm.Value{
                phi,
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
                result_u64,
            };
            _ = c.LLVMBuildCall2(
                self.builder,
                llvm.getFunctionType(rts_store_fn),
                rts_store_fn,
                &upd_args,
                3,
                "",
            );

            _ = c.LLVMBuildBr(self.builder, eval_bb);

            phi_vals.append(self.allocator, result) catch return error.OutOfMemory;
            phi_bbs.append(self.allocator, ftag_bb) catch return error.OutOfMemory;
        }

        // Wire up phi.
        c.LLVMAddIncoming(
            phi,
            @ptrCast(phi_vals.items.ptr),
            @ptrCast(phi_bbs.items.ptr),
            @intCast(phi_vals.items.len),
        );

        // ── done: return WHNF value ────────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, done_bb);
        _ = llvm.buildRet(self.builder, phi);
    }

    /// Emit a call to `__rhc_force` if the module contains F-tags.
    /// Returns the forced pointer value, or the original value unchanged
    /// if no F-tags exist (i.e. `__rhc_force` was never emitted).
    fn callForceIfNeeded(self: *GrinTranslator, val: llvm.Value) llvm.Value {
        if (self.tag_table.fun_tags.count() == 0) return val;
        const force_fn = c.LLVMGetNamedFunction(self.module, "__rhc_force") orelse return val;
        var args = [_]llvm.Value{val};
        return c.LLVMBuildCall2(
            self.builder,
            llvm.getFunctionType(force_fn),
            force_fn,
            &args,
            1,
            "forced",
        );
    }

    /// Force a heap pointer to WHNF by following indirections and forcing
    /// F-tagged thunks. Emits an inline eval loop at the current builder
    /// position (which must be in a valid basic block without a terminator).
    ///
    /// The generated IR mirrors the case-scrutinee eval loop from
    /// `translateCase`: a phi-based loop that switches on the heap node
    /// tag, follows `Ind` pointers, and calls known F-tag functions.
    ///
    /// Returns the forced pointer value; the builder is left positioned
    /// in the `force.done` block.
    fn forceValueToWhnf(self: *GrinTranslator, llvm_val: llvm.Value) TranslationError!llvm.Value {
        const header_ty = nodeHeaderType();
        const rts_load_fn = declareRtsLoadField(self.module);
        const rts_store_fn = declareRtsStoreField(self.module);
        const ptr_ty = ptrType();
        const i64_ty = llvm.i64Type();

        const entry_bb = c.LLVMGetInsertBlock(self.builder);
        const eval_bb = c.LLVMAppendBasicBlock(self.current_func, "force.eval");
        const check_bb = c.LLVMAppendBasicBlock(self.current_func, "force.check");
        const done_bb = c.LLVMAppendBasicBlock(self.current_func, "force.done");

        _ = c.LLVMBuildBr(self.builder, eval_bb);

        // ── eval loop header: phi + heap-pointer guard ─────────────────
        llvm.positionBuilderAtEnd(self.builder, eval_bb);
        const phi = c.LLVMBuildPhi(self.builder, ptr_ty, "force.phi");

        // Runtime guard: only dereference if the pointer looks like a
        // valid heap node (aligned to 8 bytes AND above page zero).
        // Raw integers stored via inttoptr (e.g. 42) fail this check
        // and go straight to done_bb.
        const ptr_as_int = c.LLVMBuildPtrToInt(self.builder, phi, i64_ty, "force.ptr_int");
        const align_mask = c.LLVMConstInt(i64_ty, 7, 0);
        const align_bits = c.LLVMBuildAnd(self.builder, ptr_as_int, align_mask, "force.align");
        const is_aligned = c.LLVMBuildICmp(self.builder, c.LLVMIntEQ, align_bits, c.LLVMConstInt(i64_ty, 0, 0), "force.is_aligned");
        const min_addr = c.LLVMConstInt(i64_ty, 4096, 0);
        const is_above_min = c.LLVMBuildICmp(self.builder, c.LLVMIntUGT, ptr_as_int, min_addr, "force.above_min");
        const is_heap_ptr = c.LLVMBuildAnd(self.builder, is_aligned, is_above_min, "force.is_heap");
        _ = c.LLVMBuildCondBr(self.builder, is_heap_ptr, check_bb, done_bb);

        // ── check block: tag load + switch ─────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, check_bb);

        var tag_idx = [_]llvm.Value{
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "force.tag_gep");
        const tag_val = c.LLVMBuildLoad2(self.builder, i64_ty, tag_gep, "force.tag");

        const n_cases = @as(u32, @intCast(self.tag_table.fun_tags.count())) + 1; // F-tags + Ind
        const sw = c.LLVMBuildSwitch(self.builder, tag_val, done_bb, n_cases);

        // ── Ind case: follow indirection ───────────────────────────────
        const ind_bb = c.LLVMAppendBasicBlock(self.current_func, "force.ind");
        c.LLVMAddCase(sw, c.LLVMConstInt(llvm.i64Type(), 0x101, 0), ind_bb);

        llvm.positionBuilderAtEnd(self.builder, ind_bb);
        var ind_load_args = [_]llvm.Value{
            phi,
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const ind_target_i64 = c.LLVMBuildCall2(
            self.builder,
            llvm.getFunctionType(rts_load_fn),
            rts_load_fn,
            &ind_load_args,
            2,
            "force.ind_target",
        );
        const ind_target = c.LLVMBuildIntToPtr(self.builder, ind_target_i64, ptr_ty, "force.ind_ptr");
        _ = c.LLVMBuildBr(self.builder, eval_bb);

        // ── Collect phi incoming values ────────────────────────────────
        var phi_vals = std.ArrayListUnmanaged(llvm.Value){};
        defer phi_vals.deinit(self.allocator);
        var phi_bbs = std.ArrayListUnmanaged(llvm.BasicBlock){};
        defer phi_bbs.deinit(self.allocator);

        phi_vals.append(self.allocator, llvm_val) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, entry_bb) catch return error.OutOfMemory;
        phi_vals.append(self.allocator, ind_target) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, ind_bb) catch return error.OutOfMemory;

        // ── F-tag cases: force thunk ───────────────────────────────────
        var ftag_iter = self.tag_table.fun_tags.iterator();
        while (ftag_iter.next()) |ftag_entry| {
            const ftag_unique = ftag_entry.key_ptr.*;
            const ftag_disc = self.tag_table.discriminants.get(ftag_unique) orelse continue;
            const ftag_name = self.tag_table.fun_tag_names.get(ftag_unique) orelse continue;
            const ftag_n_fields = self.tag_table.field_counts.get(ftag_unique) orelse 0;

            const ftag_bb = c.LLVMAppendBasicBlock(self.current_func, "force.ftag");
            c.LLVMAddCase(sw, c.LLVMConstInt(llvm.i64Type(), @bitCast(ftag_disc), 0), ftag_bb);

            llvm.positionBuilderAtEnd(self.builder, ftag_bb);

            // Load captured arguments from thunk fields.
            var call_args: [8]llvm.Value = undefined;
            const n_args = @min(ftag_n_fields, 8);
            for (0..n_args) |fi| {
                var fld_args = [_]llvm.Value{
                    phi,
                    c.LLVMConstInt(llvm.i32Type(), @intCast(fi), 0),
                };
                const loaded = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(rts_load_fn),
                    rts_load_fn,
                    &fld_args,
                    2,
                    "force.arg",
                );
                call_args[fi] = c.LLVMBuildIntToPtr(self.builder, loaded, ptr_ty, "force.ptr");
            }

            // Call the thunk's function.
            const fn_name_z = self.formatName(ftag_name);
            var param_types: [8]llvm.Type = undefined;
            for (0..n_args) |pi| param_types[pi] = ptr_ty;
            const fn_type = llvm.functionType(ptr_ty, param_types[0..n_args], false);
            const func = c.LLVMGetNamedFunction(self.module, fn_name_z) orelse
                llvm.addFunction(self.module, fn_name_z, fn_type);
            const result = c.LLVMBuildCall2(
                self.builder,
                fn_type,
                func,
                @ptrCast(&call_args),
                @intCast(n_args),
                "force.result",
            );

            // Memoize: overwrite thunk with Ind → result.
            const upd_tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "force.upd.tag");
            _ = c.LLVMBuildStore(self.builder, c.LLVMConstInt(llvm.i64Type(), 0x101, 0), upd_tag_gep);
            const result_u64 = c.LLVMBuildPtrToInt(self.builder, result, llvm.i64Type(), "force.upd.u64");
            var upd_args = [_]llvm.Value{
                phi,
                c.LLVMConstInt(llvm.i32Type(), 0, 0),
                result_u64,
            };
            _ = c.LLVMBuildCall2(
                self.builder,
                llvm.getFunctionType(rts_store_fn),
                rts_store_fn,
                &upd_args,
                3,
                "",
            );

            // Loop back to re-evaluate (result may itself be a thunk).
            _ = c.LLVMBuildBr(self.builder, eval_bb);

            phi_vals.append(self.allocator, result) catch return error.OutOfMemory;
            phi_bbs.append(self.allocator, ftag_bb) catch return error.OutOfMemory;
        }

        // Wire up phi with all incoming edges (single call, no duplicates).
        c.LLVMAddIncoming(
            phi,
            @ptrCast(phi_vals.items.ptr),
            @ptrCast(phi_bbs.items.ptr),
            @intCast(phi_vals.items.len),
        );

        // ── done: value is in WHNF ────────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, done_bb);
        return phi;
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

test "PrimOpMapping: putStrLn maps to rts_putStrLn" {
    const result = PrimOpMapping.lookup(.{
        .base = "putStrLn",
        .unique = .{ .value = 42 },
    });
    try std.testing.expect(result != null);
    try std.testing.expectEqualStrings("rts_putStrLn", std.mem.span(result.?.libcall.name));
}

test "PrimOpMapping: error maps to rts_error" {
    const result = PrimOpMapping.lookup(.{
        .base = "error",
        .unique = .{ .value = 5 },
    });
    try std.testing.expect(result != null);
    try std.testing.expectEqualStrings("rts_error", std.mem.span(result.?.libcall.name));
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
