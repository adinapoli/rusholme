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
//!   ┌─────────────┬──────────────┬─────────────────┬────────────────────────┐
//!   │  tag (u64)  │ n_fields(u32)│  gc_flags (u32) │ field[0] … field[N-1] │
//!   └─────────────┴──────────────┴─────────────────┴────────────────────────┘
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
const core_demand = @import("../core/demand.zig");
const rts_node = @import("../rts/node.zig");

const llvm = @import("llvm.zig");
const c = llvm.c;

const tag_registry_mod = @import("tag_registry.zig");
pub const TagRegistry = tag_registry_mod.TagRegistry;
pub const KnownTags = tag_registry_mod.KnownTags;
const FieldType = tag_registry_mod.FieldType;

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
    const naming_known = @import("../naming/known.zig");

    /// True if the Name is a compiler built-in (reserved unique range).
    fn isBuiltin(n: grin.Name) bool {
        return n.unique.value < naming_known.reserved_range_end;
    }

    fn lookup(name: grin.Name) ?PrimOpResult {
        // RTS IO function mappings.
        //
        // These call into the compiled Rusholme RTS (`src/rts/io.zig`) rather
        // than libc directly.  `rts_putStrLn` / `rts_putStr` are implemented
        // with `std.io`, so the same source compiles to `write()` for native
        // targets and `wasi_snapshot_preview1::fd_write` for wasm32-wasi —
        // no backend-specific adaptations required.
        //
        // Canonical names ("putStrLn_", "write_stdout", "putChar_") come
        // from desugar normalisation of `foreign import prim` aliases.
        // Prim-prefixed names ("primPutStrLn", etc.) come from the
        // Prelude's internal foreign imports.
        //
        // Unprefixed names ("putStrLn", "putStr", "putChar") are matched
        // ONLY for compiler built-in names (unique < 1000).  When the
        // Prelude is loaded, it defines Haskell-level putStr/putStrLn
        // that drive lazy evaluation via pattern matching on the list
        // spine (#612).  Those have unique >= 1000 and must NOT be
        // short-circuited to the RTS.

        // ── putStrLn ────────────────────────────────────────────
        if (std.mem.eql(u8, name.base, "primPutStrLn") or std.mem.eql(u8, name.base, "putStrLn_") or
            (std.mem.eql(u8, name.base, "putStrLn") and isBuiltin(name)))
        {
            return .{
                .libcall = .{
                    .name = "rts_putStrLn",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        // ── putStr / write_stdout ───────────────────────────────
        if (std.mem.eql(u8, name.base, "primPutStr") or std.mem.eql(u8, name.base, "write_stdout") or
            (std.mem.eql(u8, name.base, "putStr") and isBuiltin(name)) or
            (std.mem.eql(u8, name.base, "print") and isBuiltin(name)))
        {
            return .{
                .libcall = .{
                    .name = "rts_putStr",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        // ── putChar ─────────────────────────────────────────────
        if (std.mem.eql(u8, name.base, "primPutChar") or std.mem.eql(u8, name.base, "putChar_") or
            (std.mem.eql(u8, name.base, "putChar") and isBuiltin(name)))
        {
            return .{
                .libcall = .{
                    .name = "rts_putChar",
                    .return_kind = .i32,
                    .param_kinds = &.{.i64},
                    .arg_strategy = .value_passthrough,
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

        // ── Direct RTS symbols via `foreign import ccall` (#536) ─────
        //
        // The desugarer passes ccall symbol names through unchanged, so
        // they arrive here as the literal RTS symbol. This set must stay
        // in sync with `PrimOp.isSupportedCCallSymbol` (src/grin/primop.zig),
        // which gates what the desugarer accepts.
        if (std.mem.eql(u8, name.base, "rts_putStrLn")) {
            return .{
                .libcall = .{
                    .name = "rts_putStrLn",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "rts_putStr")) {
            return .{
                .libcall = .{
                    .name = "rts_putStr",
                    .return_kind = .i32,
                    .param_kinds = &.{.ptr},
                    .arg_strategy = .string_to_global_ptr,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "rts_putChar")) {
            return .{
                .libcall = .{
                    .name = "rts_putChar",
                    .return_kind = .i32,
                    .param_kinds = &.{.i64},
                    .arg_strategy = .value_passthrough,
                },
            };
        }
        if (std.mem.eql(u8, name.base, "rts_error")) {
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
        if (std.mem.eql(u8, name.base, "neg_Int")) return .{ .instruction = .{ .neg = {} } };
        if (std.mem.eql(u8, name.base, "abs_Int")) return .{ .instruction = .{ .abs = {} } };
        if (std.mem.eql(u8, name.base, "quot_Int")) return .{ .instruction = .{ .sdiv = {} } };
        if (std.mem.eql(u8, name.base, "rem_Int")) return .{ .instruction = .{ .srem = {} } };
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

        // Character ↔ Int conversions — identity at the LLVM level since
        // both Char and Int are represented as i64.
        if (std.mem.eql(u8, name.base, "intToChar")) return .{ .instruction = .{ .identity = {} } };
        if (std.mem.eql(u8, name.base, "charToInt")) return .{ .instruction = .{ .identity = {} } };

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
    /// Unary arithmetic instructions
    neg: void,
    abs: void,
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
    /// Identity passthrough (intToChar, charToInt) — both types are i64
    /// at the LLVM level, so no conversion is needed.
    identity: void,
};

/// A translated PrimOp result
const PrimOpResult = union(enum) {
    libcall: LibcFunction,
    instruction: LLVMInstruction,
};

// ═══════════════════════════════════════════════════════════════════════
// Heap node helpers
// ═══════════════════════════════════════════════════════════════════════

/// Return the LLVM opaque pointer type used for all heap pointers.
fn ptrType() llvm.Type {
    return c.LLVMPointerTypeInContext(c.LLVMGetGlobalContext(), 0);
}

// ── Integer tagging ────────────────────────────────────────────────────
//
// Raw Haskell integers (Int, Char) flowing as ptr-typed SSA values are
// encoded with bit 0 set: `(n << 1) | 1`.  Heap pointers are 8-byte
// aligned and always have bit 0 = 0.  This lets `__rhc_force` and
// inline eval guards distinguish the two with a single bit test,
// eliminating the unreliable address-range heuristic that mis-identified
// large aligned integers (e.g. factorial(7) = 5040) as heap pointers.
//
// Encoding: tagInt(builder, i64_val) -> ptr   (sets bit 0)
// Decoding: untagInt(builder, ptr_val) -> i64 (clears bit 0, arithmetic shift right)

fn tagInt(builder: llvm.Builder, val: llvm.Value) llvm.Value {
    const i64_ty = llvm.i64Type();
    const shifted = c.LLVMBuildShl(builder, val, c.LLVMConstInt(i64_ty, 1, 0), "tag_shl");
    const tagged = c.LLVMBuildOr(builder, shifted, c.LLVMConstInt(i64_ty, 1, 0), "tag_or");
    return c.LLVMBuildIntToPtr(builder, tagged, ptrType(), "tagged_int");
}

/// Encode a nullary constructor as a tagged immediate: `(disc << 1) | 1`,
/// same encoding as integers. Case dispatch untags ptr-typed scrutinees
/// with bit 0 set and switches on the result, so a nullary constructor
/// never needs a heap node — its discriminant *is* the value. Only valid
/// for `.Con` tags: F-tags need a heap slot for the Ind update (#605),
/// and P-tags carry an arity header the apply machinery inspects.
fn tagImmediateCon(builder: llvm.Builder, disc_val: llvm.Value) llvm.Value {
    return tagInt(builder, disc_val);
}

fn untagInt(builder: llvm.Builder, val: llvm.Value) llvm.Value {
    const i64_ty = llvm.i64Type();
    const as_int = if (c.LLVMGetTypeKind(c.LLVMTypeOf(val)) == c.LLVMPointerTypeKind)
        c.LLVMBuildPtrToInt(builder, val, i64_ty, "untag_p2i")
    else
        val;
    return c.LLVMBuildAShr(builder, as_int, c.LLVMConstInt(i64_ty, 1, 0), "untagged");
}

/// Return the LLVM struct type for the unified node header:
///   { i64 tag, i32 n_fields, i32 gc_flags }   (16 bytes)
///
/// Used only for GEP into the tag word when loading the discriminant
/// in Case expressions.  Field I/O uses the rts_load_field / rts_store_field
/// RTS helpers instead of direct GEP. The third word stores Immix
/// collector metadata (see `src/rts/node.zig::Node.gc_flags`) and is
/// never read by generated code.
fn nodeHeaderType() llvm.Type {
    var members = [_]llvm.Type{
        llvm.i64Type(), // tag
        llvm.i32Type(), // n_fields
        llvm.i32Type(), // gc_flags
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

// ── Inline alloc fast path (issue #798) ──────────────────────────────────
//
// Constants mirroring `src/rts/immix.zig`. Kept in sync with the RTS
// side; bump both together if either changes.
const IMMIX_BLOCK_SIZE: u64 = 32 * 1024;
const IMMIX_LINE_SIZE: u64 = 128;
const IMMIX_LINE_LOG2: u64 = 7; // log2(IMMIX_LINE_SIZE)
// Maximum node size that can take the inline fast path. Multi-line
// allocations would require marking more than one line byte; defer
// those to the slow path (the RTS handles them correctly).
const INLINE_ALLOC_MAX_SIZE: u64 = IMMIX_LINE_SIZE;
// Maximum number of payload fields the inline fast path zero-inits.
// Larger allocations defer to the slow path to keep the inline IR
// small. The vast majority of Haskell heap nodes are well below this.
const INLINE_ALLOC_MAX_FIELDS: u32 = 8;

/// Declare `extern usize @rts_immix_cursor`. Updated by both the RTS
/// and by generated code's inline fast path.
fn declareImmixCursor(module: llvm.Module) llvm.Value {
    const name = "rts_immix_cursor";
    if (c.LLVMGetNamedGlobal(module, name)) |existing| return existing;
    const g = c.LLVMAddGlobal(module, llvm.i64Type(), name);
    c.LLVMSetLinkage(g, c.LLVMExternalLinkage);
    return g;
}

/// Declare `extern usize @rts_immix_limit`. Read-only from generated
/// code's perspective; written by the RTS when it advances to a new
/// hole or block.
fn declareImmixLimit(module: llvm.Module) llvm.Value {
    const name = "rts_immix_limit";
    if (c.LLVMGetNamedGlobal(module, name)) |existing| return existing;
    const g = c.LLVMAddGlobal(module, llvm.i64Type(), name);
    c.LLVMSetLinkage(g, c.LLVMExternalLinkage);
    return g;
}

/// Declare `rts_set_backend(value: i32) -> void`. The RTS reads this
/// once on the first allocation to choose between `ArenaGc` and
/// `ImmixGc`; subsequent calls with the same value are no-ops. See
/// `src/rts/heap.zig`.
fn declareRtsSetBackend(module: llvm.Module) llvm.Value {
    const name = "rts_set_backend";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    var params = [_]llvm.Type{llvm.i32Type()};
    const fn_ty = c.LLVMFunctionType(llvm.voidType(), &params, 1, 0);
    return c.LLVMAddFunction(module, name, fn_ty);
}

/// Get-or-define the module-private `rts_store_field(ptr, i32, i64)`.
/// Field access is a fixed-offset store (`fields(n)[i] = v` in
/// src/rts/node.zig); defining it as an always-inline body in every
/// module lets LLVM fold the call away — out-of-line RTS calls for
/// every field write were a dominant cost on alloc-heavy benches.
fn declareRtsStoreField(module: llvm.Module) llvm.Value {
    const name = "rts_store_field";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    var params = [_]llvm.Type{ ptrType(), llvm.i32Type(), llvm.i64Type() };
    const fn_ty = c.LLVMFunctionType(llvm.voidType(), &params, 3, 0);
    const func = c.LLVMAddFunction(module, name, fn_ty);
    defineFieldAccessorBody(module, func, .store);
    return func;
}

/// Get-or-define the module-private `rts_load_field(ptr, i32) -> i64`.
fn declareRtsLoadField(module: llvm.Module) llvm.Value {
    const name = "rts_load_field";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    var params = [_]llvm.Type{ ptrType(), llvm.i32Type() };
    const fn_ty = c.LLVMFunctionType(llvm.i64Type(), &params, 2, 0);
    const func = c.LLVMAddFunction(module, name, fn_ty);
    defineFieldAccessorBody(module, func, .load);
    return func;
}

/// Emit the body for an inline field accessor. The function is given
/// internal linkage and the `alwaysinline` attribute so the symbol never
/// clashes with the real RTS export (which remains for Zig-side callers)
/// and the call disappears during optimisation.
fn defineFieldAccessorBody(module: llvm.Module, func: llvm.Value, kind: enum { load, store }) void {
    c.LLVMSetLinkage(func, c.LLVMInternalLinkage);
    const ctx = c.LLVMGetModuleContext(module);
    const kind_id = c.LLVMGetEnumAttributeKindForName("alwaysinline", "alwaysinline".len);
    const attr = c.LLVMCreateEnumAttribute(ctx, kind_id, 0);
    const fn_index: c_uint = @bitCast(@as(c_int, c.LLVMAttributeFunctionIndex));
    c.LLVMAddAttributeAtIndex(func, fn_index, attr);

    const builder = c.LLVMCreateBuilderInContext(ctx);
    defer c.LLVMDisposeBuilder(builder);
    const entry = llvm.appendBasicBlock(func, "entry");
    llvm.positionBuilderAtEnd(builder, entry);

    const node_ptr = c.LLVMGetParam(func, 0);
    const index = c.LLVMGetParam(func, 1);
    const idx64 = c.LLVMBuildZExt(builder, index, llvm.i64Type(), "idx");
    // fields base = node + 16 bytes (2 i64 header slots), slot i at +8*i.
    const hdr = c.LLVMConstInt(llvm.i64Type(), 2, 0);
    var base_idx = [_]llvm.Value{hdr};
    const base = c.LLVMBuildGEP2(builder, llvm.i64Type(), node_ptr, &base_idx, 1, "fields.base");
    var slot_idx = [_]llvm.Value{idx64};
    const slot = c.LLVMBuildGEP2(builder, llvm.i64Type(), base, &slot_idx, 1, "field.slot");

    switch (kind) {
        .load => {
            const v = c.LLVMBuildLoad2(builder, llvm.i64Type(), slot, "field.val");
            _ = c.LLVMBuildRet(builder, v);
        },
        .store => {
            const v = c.LLVMGetParam(func, 2);
            _ = c.LLVMBuildStore(builder, v, slot);
            _ = c.LLVMBuildRetVoid(builder);
        },
    }
}

/// Capacity (in slots) of the shadow-stack buffer exposed by the RTS.
/// Must match `SHADOW_CAP` in `src/rts/heap.zig` — keep these two
/// in sync if either changes.
const SHADOW_CAP: u64 = 1 << 20;

/// Declare `extern [SHADOW_CAP x i64] @rts_shadow_buffer` in the
/// module. The global is defined in `src/rts/heap.zig` and linked in
/// from the RTS static library; here we just declare it so generated
/// code can address it directly without going through a C call.
/// Issue #788.
fn declareRtsShadowBuffer(module: llvm.Module) llvm.Value {
    const name = "rts_shadow_buffer";
    if (c.LLVMGetNamedGlobal(module, name)) |existing| return existing;
    const arr_ty = c.LLVMArrayType(llvm.i64Type(), @intCast(SHADOW_CAP));
    const g = c.LLVMAddGlobal(module, arr_ty, name);
    c.LLVMSetLinkage(g, c.LLVMExternalLinkage);
    return g;
}

/// Declare `extern i32 @rts_shadow_top` in the module. Companion to
/// `rts_shadow_buffer`; tracks the next free slot.
fn declareRtsShadowTop(module: llvm.Module) llvm.Value {
    const name = "rts_shadow_top";
    if (c.LLVMGetNamedGlobal(module, name)) |existing| return existing;
    const g = c.LLVMAddGlobal(module, llvm.i32Type(), name);
    c.LLVMSetLinkage(g, c.LLVMExternalLinkage);
    return g;
}

/// Declare `rts_set_pointer_mask(tag: i64, mask: i64) -> void`.
/// Called once per user-defined constructor at program start to
/// register the constructor's pointer-mask with the collector (#779).
fn declareRtsSetPointerMask(module: llvm.Module) llvm.Value {
    const name = "rts_set_pointer_mask";
    if (c.LLVMGetNamedFunction(module, name)) |existing| return existing;
    var params = [_]llvm.Type{ llvm.i64Type(), llvm.i64Type() };
    const fn_ty = c.LLVMFunctionType(llvm.voidType(), &params, 2, 0);
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
    /// Reference to the tag registry for constructor field types.
    registry: *const TagRegistry,

    fn init() TypeEnv {
        return .{
            .var_types = .{},
            .registry = undefined,
        };
    }

    fn deinit(self: *TypeEnv, alloc: std.mem.Allocator) void {
        self.var_types.deinit(alloc);
    }

    fn setRegistry(self: *TypeEnv, reg: *const TagRegistry) void {
        self.registry = reg;
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
        const types = self.registry.fieldTypes(tag) orelse return .ptr;
        if (index >= types.len) return .ptr;
        return types[index];
    }
};

/// Selects which RTS heap backend the generated `main` initialises
/// before user code runs. Mirrors `RtsBackend` in `src/rts/heap.zig`
/// — keep the numeric values in sync (they cross the C ABI).
pub const RtsBackend = enum(u32) {
    arena = 0,
    immix = 1,

    pub fn parse(s: []const u8) ?RtsBackend {
        if (std.mem.eql(u8, s, "arena")) return .arena;
        if (std.mem.eql(u8, s, "immix")) return .immix;
        return null;
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
    /// GRIN variable uniques whose bound value is statically known to be
    /// in WHNF (primop results, freshly-stored constructor nodes, tagged
    /// immediates). Case sites consult this to elide the `__rhc_force`
    /// pre-force call (#800). Cleared at the start of each translateDef.
    whnf_vars: std.AutoHashMap(u64, void),
    /// Strict-parameter masks from the Core demand analysis (#802),
    /// keyed by function unique. Strict parameters are forced once at
    /// function entry and tracked as WHNF, eliding every per-use force
    /// in the body. Null when no analysis ran (REPL, debug commands).
    strict_params: ?*const core_demand.StrictnessMap = null,
    /// Per-function cache for translated GRIN Case expressions.  The
    /// sequential pattern-match desugarer creates shared fallback nodes
    /// (a DAG) that would be re-translated exponentially without caching.
    /// Keyed by the GRIN expression pointer (as usize); value is the LLVM
    /// basic block where the translated case's dispatch logic starts.
    /// Cleared at the start of each `translateDef` call.
    case_entry_cache: std.AutoHashMap(usize, llvm.BasicBlock),
    /// Persistent tag registry — owned externally (JIT engine or caller).
    registry: *TagRegistry,
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

    /// Function arity map for correct forward declarations (issue #595).
    /// Maps function unique IDs to their parameter counts.
    arity_map: ?*const std.AutoHashMapUnmanaged(u64, u32) = null,

    /// RTS backend selected by `rhc build --rts=…`. When non-`.arena`
    /// the translator emits a `call void @rts_set_backend(i32 N)` at
    /// the very start of `main`'s entry block, before any other
    /// instruction. `.arena` matches the default lazy-init behaviour
    /// in `src/rts/heap.zig` and is therefore a no-op for codegen.
    /// See issue #776.
    rts_backend: RtsBackend = .arena,

    /// When set, the translator emits precise GC root tracking (issue
    /// #780): a `rts_shadow_save` call at function entry, a
    /// `rts_shadow_push` call at every `*Node` SSA definition, and a
    /// `rts_shadow_restore` call before every return. The flag is
    /// armed only inside the body of a GRIN-translated function whose
    /// active backend has a tracing collector — i.e. `rts_backend !=
    /// .arena`. Helper functions emitted directly into the module
    /// (`__rhc_force`, `__rhc_apply`, the unit-node builder) disarm it
    /// for the duration of their own emission and re-arm it on exit.
    shadow_emit_enabled: bool = false,

    /// The `i32` SSA value returned by `rts_shadow_save` at the entry
    /// of the function currently being translated. `null` outside of a
    /// shadow-stack-tracked function (or before entry has emitted the
    /// save). Each return in the current function calls
    /// `rts_shadow_restore` with this exact value.
    shadow_saved_top: ?llvm.Value = null,

    pub fn init(allocator: std.mem.Allocator, registry: *TagRegistry) GrinTranslator {
        llvm.initialize();
        const ctx = llvm.createContext();
        return .{
            .ctx = ctx,
            .module = llvm.createModule("haskell", ctx),
            .builder = llvm.createBuilder(ctx),
            .allocator = allocator,
            .params = std.AutoHashMap(u64, llvm.Value).init(allocator),
            .whnf_vars = std.AutoHashMap(u64, void).init(allocator),
            .case_entry_cache = std.AutoHashMap(usize, llvm.BasicBlock).init(allocator),
            .registry = registry,
            .type_env = TypeEnv.init(),
            .current_func = null,
        };
    }

    pub fn deinit(self: *GrinTranslator) void {
        self.params.deinit();
        self.whnf_vars.deinit();
        self.case_entry_cache.deinit();
        // registry is not owned — do not deinit it.
        self.type_env.deinit(self.allocator);
        llvm.disposeBuilder(self.builder);
        // Disposing the context also disposes modules created within it.
        llvm.disposeContext(self.ctx);
    }

    /// Extract the tag discriminants for well-known constructors
    /// (True, False, [], (:), etc.) from the current tag table.
    /// Used by the JIT engine to format results correctly.
    pub fn getKnownTagDiscriminants(self: *const GrinTranslator) KnownTags {
        return self.registry.getKnownDiscriminants();
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

    /// Allocate a 0-field Unit heap node and return its address as an i64.
    ///
    /// Used by entry-point functions that need to return a
    /// distinguishable "no value" result (as opposed to integer 0,
    /// which is boolean False).
    /// Emit `rts_set_backend(value)` at the current builder position.
    /// Generated as the first instruction of native `main` whenever
    /// the user picks a non-default backend (see #776).
    fn emitSetRtsBackendCall(self: *GrinTranslator, value: u32) void {
        const fn_val = declareRtsSetBackend(self.module);
        var args = [_]llvm.Value{c.LLVMConstInt(llvm.i32Type(), value, 0)};
        _ = c.LLVMBuildCall2(
            self.builder,
            llvm.getFunctionType(fn_val),
            fn_val,
            &args,
            1,
            "",
        );
    }

    /// Emit one `rts_set_pointer_mask(tag, mask)` call per
    /// constructor the registry knows about (issue #779). Run at the
    /// very start of `main`'s entry block, before any user code can
    /// allocate, so the collector sees the precise per-tag layout
    /// from the first allocation onwards. No-op under `--rts=arena`
    /// (no collector). Tags whose mask the registry does not know
    /// stay at `UNKNOWN_MASK` and the collector falls back to a
    /// conservative scan for them.
    fn emitPointerMaskInit(self: *GrinTranslator) void {
        if (self.rts_backend == .arena) return;
        const set_mask_fn = declareRtsSetPointerMask(self.module);
        const i64_ty = llvm.i64Type();
        var iter = self.registry.field_types.iterator();
        while (iter.next()) |entry| {
            const tag_key = entry.key_ptr.*;
            const types = entry.value_ptr.*;
            const disc = self.registry.discriminants.get(tag_key) orelse continue;
            // Compute the pointer-mask: bit i = 1 ⇔ field i is a
            // `*Node`. Function pointers (`fn_ptr`) and scalars are
            // not heap roots and stay 0 in the mask.
            var mask: u64 = 0;
            for (types, 0..) |ft, i| {
                if (i >= 64) break;
                if (ft == .ptr) {
                    mask |= @as(u64, 1) << @intCast(i);
                }
            }
            var args = [_]llvm.Value{
                c.LLVMConstInt(i64_ty, @bitCast(disc), 0),
                c.LLVMConstInt(i64_ty, mask, 0),
            };
            _ = c.LLVMBuildCall2(
                self.builder,
                llvm.getFunctionType(set_mask_fn),
                set_mask_fn,
                &args,
                2,
                "",
            );
        }
    }

    /// Emit `%saved = call i32 @rts_shadow_save()` at the current
    /// builder position and arm the precise-root emission state for the
    /// rest of the current function. Called once at function entry when
    /// the selected backend uses a tracing collector (#780). Must be
    /// paired with a `rts_shadow_restore` before every return in the
    /// same function — `buildRetWithShadowRestore` handles that.
    fn enableShadowStackForCurrentFunction(self: *GrinTranslator) void {
        if (self.rts_backend == .arena) return;
        // Inline `rts_shadow_save()`: a single load of the top counter.
        // The save/restore pair brackets every GRIN function; emitting
        // them as calls cost ~2 calls per function invocation (and 2 per
        // *inlined wrapper* after LLVM inlining) — the dominant Immix
        // overhead on call-heavy benches.
        const top_var = declareRtsShadowTop(self.module);
        const saved = c.LLVMBuildLoad2(self.builder, llvm.i32Type(), top_var, "shadow.saved");
        self.shadow_saved_top = saved;
        self.shadow_emit_enabled = true;
    }

    /// Disarm precise-root emission and forget the saved-top SSA value.
    /// Called when leaving a GRIN-translated function so subsequent
    /// helper emissions do not pick up stale shadow-stack state.
    fn disableShadowStackForCurrentFunction(self: *GrinTranslator) void {
        self.shadow_emit_enabled = false;
        self.shadow_saved_top = null;
    }

    /// Emit `call void @rts_shadow_push(ptrtoint(value to i64))` at the
    /// current builder position. No-op when precise root emission is
    /// disabled (arena backend, or inside one of the helper functions
    /// like `__rhc_force` that does not participate). Also no-op for
    /// non-pointer-typed values — the shadow stack only tracks `*Node`.
    /// Emit the equivalent of `rts_shadow_push(ptrtoint(value, i64))`
    /// inline at the current builder position (issue #788). The push
    /// itself is five LLVM instructions — load top, GEP, store value,
    /// add, store new top — and is fully visible to the optimiser:
    /// SROA / GVN / LICM can hoist redundant loads of `@rts_shadow_top`
    /// across nearby pushes, and the per-push call-ABI overhead of
    /// going through `@rts_shadow_push` is eliminated.
    ///
    /// The cap check (`top < SHADOW_CAP`) is **not** emitted inline —
    /// the static cap is 1M slots (8 MB) and any program that hits it
    /// already has a runaway-recursion bug. Direct C-ABI callers
    /// (tests, embedders) still go through the exported
    /// `rts_shadow_push` which enforces the cap.
    fn rootPtr(self: *GrinTranslator, value: llvm.Value) void {
        if (!self.shadow_emit_enabled) return;
        const ty = c.LLVMTypeOf(value);
        if (c.LLVMGetTypeKind(ty) != c.LLVMPointerTypeKind) return;

        const i32_ty = llvm.i32Type();
        const i64_ty = llvm.i64Type();
        const buf_ty = c.LLVMArrayType(i64_ty, @intCast(SHADOW_CAP));
        const buf = declareRtsShadowBuffer(self.module);
        const top_var = declareRtsShadowTop(self.module);

        const top = c.LLVMBuildLoad2(self.builder, i32_ty, top_var, "shadow.top");
        var indices = [_]llvm.Value{
            c.LLVMConstInt(i32_ty, 0, 0),
            top,
        };
        const slot = c.LLVMBuildGEP2(self.builder, buf_ty, buf, &indices, 2, "shadow.slot");
        const as_u64 = c.LLVMBuildPtrToInt(self.builder, value, i64_ty, "shadow.val");
        _ = c.LLVMBuildStore(self.builder, as_u64, slot);
        const new_top = c.LLVMBuildAdd(self.builder, top, c.LLVMConstInt(i32_ty, 1, 0), "shadow.new_top");
        _ = c.LLVMBuildStore(self.builder, new_top, top_var);
    }

    /// Bind `value` to GRIN unique id `uid` in `self.params` and emit a
    /// shadow-stack push if precise root tracking is active. Replaces
    /// the bare `self.params.put(uid, value)` pattern at every site
    /// where a GRIN-named SSA is introduced.
    /// Whether a GRIN expression's result is statically a *tagged
    /// immediate* (never a heap pointer): primop instruction results,
    /// Int/Char literals, nullary constructors. Such values need no
    /// shadow-stack root — the collector skips bit-0 values anyway.
    /// Strictly stronger than exprYieldsWhnf (a fresh Con store is WHNF
    /// but lives on the heap and must be rooted).
    fn exprYieldsImmediate(self: *const GrinTranslator, expr: *const grin.Expr) bool {
        return switch (expr.*) {
            .Return => |v| switch (v) {
                .ValTag => true,
                .Lit => |lit| lit == .Int or lit == .Char or lit == .Bool,
                else => false,
            },
            .App => |app| if (PrimOpMapping.lookup(app.name)) |m| m == .instruction else false,
            .Block => |inner| self.exprYieldsImmediate(inner),
            .Bind => |b| self.exprYieldsImmediate(b.rhs),
            else => false,
        };
    }

    fn bindAndRoot(self: *GrinTranslator, uid: u64, value: llvm.Value) !void {
        try self.params.put(uid, value);
        self.rootPtr(value);
    }

    /// Emit a `rts_shadow_restore` call if precise root tracking is
    /// active, then build the return instruction. Use this in place of
    /// `llvm.buildRet` for every return in a GRIN-translated function
    /// so the shadow stack is unwound on every exit path.
    fn buildRetWithShadowRestore(self: *GrinTranslator, value: llvm.Value) void {
        self.emitShadowRestoreIfActive();
        _ = llvm.buildRet(self.builder, value);
    }

    /// Variant of `buildRetWithShadowRestore` for `ret void`.
    fn buildRetVoidWithShadowRestore(self: *GrinTranslator) void {
        self.emitShadowRestoreIfActive();
        _ = llvm.buildRetVoid(self.builder);
    }

    /// Emit the `rts_shadow_restore` call if shadow-stack tracking is
    /// active for the current function. Safe to call multiple times per
    /// return path (each call shrinks the stack to the saved height —
    /// a second call is a no-op on the buffer).
    fn emitShadowRestoreIfActive(self: *GrinTranslator) void {
        if (!self.shadow_emit_enabled) return;
        const saved = self.shadow_saved_top orelse return;
        // Inline `rts_shadow_restore(saved)`: a single store of the top
        // counter. Slots above `top` are never read by the collector
        // (it scans `rts_shadow_buffer[0..top]`), so no zeroing is
        // needed — popping is just lowering the counter.
        const top_var = declareRtsShadowTop(self.module);
        _ = c.LLVMBuildStore(self.builder, saved, top_var);
    }

    fn buildUnitNode(self: *GrinTranslator) llvm.Value {
        const unit_tag: i64 = @intFromEnum(rts_node.Tag.Unit);
        return self.emitAllocConst(unit_tag, 0, "unit");
    }

    /// Allocate a `Node` with the given tag and field count. Under
    /// `--rts=immix` this emits the inline bump path (#798): load the
    /// cursor, branch on whether the padded size fits before the
    /// limit, take the slow path through `rts_alloc` on overflow,
    /// otherwise commit the header (tag + n_fields + zero gc_flags),
    /// mark the line used, and bump the cursor. Under any other
    /// backend it falls back to the plain `rts_alloc` C call.
    ///
    /// `n_fields` is a compile-time constant — every call site already
    /// has it as a Zig value, and the fast path needs it constant to
    /// fold the padded size + per-field zero stores. `tag` is an LLVM
    /// `i64` value, which may be a constant or a runtime select (e.g.
    /// the boolean-boxing path emits the tag via `LLVMBuildSelect`).
    /// The header write is just `store i64 %tag` — works for both.
    ///
    /// Two convenience constructors are provided below for the common
    /// constant-tag and unit-tag cases.
    fn emitAlloc(self: *GrinTranslator, tag_val: llvm.Value, n_fields: u32, result_name: []const u8) llvm.Value {
        const i32_ty = llvm.i32Type();
        const nf_val = c.LLVMConstInt(i32_ty, n_fields, 0);

        // Slow-path-only conditions: arena backend (no inline cursor
        // exists), or the allocation does not fit the inline shape
        // (line-spanning sizes, very wide nodes).
        const padded_size: u64 = 16 + @as(u64, n_fields) * 8;
        // Both backends bump through the shared cursor/limit globals;
        // the arena fast path just skips the Immix line-mark stores.
        // REPL (ORC JIT) modules cannot resolve the cursor globals
        // against the bitcode-loaded RTS, so they keep the call path.
        const inline_eligible =
            self.repl_entry_point == null and
            padded_size <= INLINE_ALLOC_MAX_SIZE and
            n_fields <= INLINE_ALLOC_MAX_FIELDS;
        if (!inline_eligible) {
            return self.emitAllocSlow(tag_val, nf_val, result_name);
        }
        return self.emitAllocInline(n_fields, tag_val, nf_val, padded_size, result_name);
    }

    /// Convenience wrapper for the (overwhelmingly common) case where
    /// the tag is a Zig-side compile-time constant.
    fn emitAllocConst(self: *GrinTranslator, tag: i64, n_fields: u32, result_name: []const u8) llvm.Value {
        const tag_val = c.LLVMConstInt(llvm.i64Type(), @bitCast(tag), 0);
        return self.emitAlloc(tag_val, n_fields, result_name);
    }

    /// Slow-path allocation: plain `rts_alloc` C call. Same shape the
    /// backend used before #798.
    fn emitAllocSlow(self: *GrinTranslator, tag_val: llvm.Value, nf_val: llvm.Value, result_name: []const u8) llvm.Value {
        const rts_alloc_fn = declareRtsAlloc(self.module);
        var args = [_]llvm.Value{ tag_val, nf_val };
        return c.LLVMBuildCall2(
            self.builder,
            llvm.getFunctionType(rts_alloc_fn),
            rts_alloc_fn,
            &args,
            2,
            nullTerminate(result_name).ptr,
        );
    }

    /// Inline fast path. Emits a three-block diamond at the current
    /// builder position:
    ///
    ///   entry:  load cursor; add padded size; load limit; cmp.
    ///   fast:   commit header + line mark + cursor update.
    ///   slow:   delegate to rts_alloc.
    ///   done:   phi the resulting node pointer.
    ///
    /// After the call the builder is positioned at the `done` block.
    fn emitAllocInline(
        self: *GrinTranslator,
        n_fields: u32,
        tag_val: llvm.Value,
        nf_val: llvm.Value,
        padded_size: u64,
        result_name: []const u8,
    ) llvm.Value {
        const i8_ty = llvm.i8Type();
        const i32_ty = llvm.i32Type();
        const i64_ty = llvm.i64Type();
        const ptr_ty = ptrType();

        const cursor_g = declareImmixCursor(self.module);
        const limit_g = declareImmixLimit(self.module);

        // ── entry: probe cursor + limit ───────────────────────────────
        const top = c.LLVMBuildLoad2(self.builder, i64_ty, cursor_g, "alloc.top");
        const size_const = c.LLVMConstInt(i64_ty, padded_size, 0);
        const end_v = c.LLVMBuildAdd(self.builder, top, size_const, "alloc.end");
        const limit_v = c.LLVMBuildLoad2(self.builder, i64_ty, limit_g, "alloc.limit");
        const fits = c.LLVMBuildICmp(self.builder, c.LLVMIntULE, end_v, limit_v, "alloc.fits");

        const cur_func = self.current_func;
        const fast_bb = c.LLVMAppendBasicBlock(cur_func, "alloc.fast");
        const slow_bb = c.LLVMAppendBasicBlock(cur_func, "alloc.slow");
        const done_bb = c.LLVMAppendBasicBlock(cur_func, "alloc.done");
        _ = c.LLVMBuildCondBr(self.builder, fits, fast_bb, slow_bb);

        // ── fast: commit ─────────────────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, fast_bb);
        const p_fast = c.LLVMBuildIntToPtr(self.builder, top, ptr_ty, "alloc.p_fast");
        // tag at offset 0 (i64)
        _ = c.LLVMBuildStore(self.builder, tag_val, p_fast);
        // n_fields (i32) + gc_flags (i32) at offset 8 — pack into one
        // i64 store: low 32 = n_fields, high 32 = 0 (gc_flags).
        const header_pair: u64 = @as(u64, n_fields);
        const header_pair_val = c.LLVMConstInt(i64_ty, header_pair, 0);
        const hdr_addr = c.LLVMBuildAdd(self.builder, top, c.LLVMConstInt(i64_ty, 8, 0), "alloc.hdr_addr");
        const hdr_ptr = c.LLVMBuildIntToPtr(self.builder, hdr_addr, ptr_ty, "alloc.hdr_ptr");
        _ = c.LLVMBuildStore(self.builder, header_pair_val, hdr_ptr);
        // Zero the field slots (offset 16 ..= 16+8*(n_fields-1)). Skip
        // the suppressor here — callers immediately overwrite fields
        // for ConstTagNode allocations, but partial-application call
        // sites rely on zero-initialised tail slots. Cheaper than a
        // memset for the n_fields ≤ INLINE_ALLOC_MAX_FIELDS case.
        var fi: u32 = 0;
        while (fi < n_fields) : (fi += 1) {
            const off: u64 = 16 + @as(u64, fi) * 8;
            const slot_addr = c.LLVMBuildAdd(self.builder, top, c.LLVMConstInt(i64_ty, off, 0), "alloc.slot_addr");
            const slot_ptr = c.LLVMBuildIntToPtr(self.builder, slot_addr, ptr_ty, "alloc.slot_ptr");
            _ = c.LLVMBuildStore(self.builder, c.LLVMConstInt(i64_ty, 0, 0), slot_ptr);
        }
        // Mark every line the allocation spans as used (Immix only:
        // arena chunks have no block headers, and the line-mark store
        // would scribble over unrelated memory). Since
        // `padded_size <= LINE_SIZE` (#798 ceiling) the allocation
        // covers at most two lines — mark both unconditionally; a
        // duplicate store on the same byte is harmless. `line_marks`
        // sits at offset 0 of `BlockHeader`, so the byte address for
        // line `i` is `block_base + i`.
        if (self.rts_backend == .immix) {
            const block_mask = c.LLVMConstInt(i64_ty, ~@as(u64, IMMIX_BLOCK_SIZE - 1), 0);
            const block_base = c.LLVMBuildAnd(self.builder, top, block_mask, "alloc.block_base");
            const offset_first = c.LLVMBuildSub(self.builder, top, block_base, "alloc.off_first");
            const line_first = c.LLVMBuildLShr(self.builder, offset_first, c.LLVMConstInt(i64_ty, IMMIX_LINE_LOG2, 0), "alloc.line_first");
            const lm_first_addr = c.LLVMBuildAdd(self.builder, block_base, line_first, "alloc.lm_first_addr");
            const lm_first_ptr = c.LLVMBuildIntToPtr(self.builder, lm_first_addr, ptr_ty, "alloc.lm_first_ptr");
            _ = c.LLVMBuildStore(self.builder, c.LLVMConstInt(i8_ty, 1, 0), lm_first_ptr);
            // Second line (only different from the first when the alloc
            // straddles a boundary). Compute via `(end - 1) >> 7`.
            const end_inclusive = c.LLVMBuildAdd(self.builder, top, c.LLVMConstInt(i64_ty, padded_size - 1, 0), "alloc.end_inclusive");
            const offset_last = c.LLVMBuildSub(self.builder, end_inclusive, block_base, "alloc.off_last");
            const line_last = c.LLVMBuildLShr(self.builder, offset_last, c.LLVMConstInt(i64_ty, IMMIX_LINE_LOG2, 0), "alloc.line_last");
            const lm_last_addr = c.LLVMBuildAdd(self.builder, block_base, line_last, "alloc.lm_last_addr");
            const lm_last_ptr = c.LLVMBuildIntToPtr(self.builder, lm_last_addr, ptr_ty, "alloc.lm_last_ptr");
            _ = c.LLVMBuildStore(self.builder, c.LLVMConstInt(i8_ty, 1, 0), lm_last_ptr);
        }
        // Publish the new cursor.
        _ = c.LLVMBuildStore(self.builder, end_v, cursor_g);
        _ = c.LLVMBuildBr(self.builder, done_bb);

        // ── slow: defer to rts_alloc ────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, slow_bb);
        // Re-locate nf_val in this BB — it's already an SSA constant,
        // LLVM tolerates cross-block constant references.
        _ = i32_ty;
        const p_slow = self.emitAllocSlow(tag_val, nf_val, "alloc.p_slow");
        _ = c.LLVMBuildBr(self.builder, done_bb);

        // ── done: phi ───────────────────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, done_bb);
        const phi = c.LLVMBuildPhi(self.builder, ptr_ty, nullTerminate(result_name).ptr);
        var inc_vals = [_]llvm.Value{ p_fast, p_slow };
        var inc_bbs = [_]llvm.BasicBlock{ fast_bb, slow_bb };
        c.LLVMAddIncoming(phi, &inc_vals, &inc_bbs, 2);
        return phi;
    }

    /// Translate the entire GRIN program into the LLVM module.
    /// Returns the underlying LLVM Module for direct use (e.g. object emission).
    /// The module is owned by this translator's context — do not dispose it
    /// separately; it is freed when the translator is deinited.
    pub fn translateProgramToModule(self: *GrinTranslator, program: grin.Program) TranslationError!llvm.Module {
        // Register tags from the current program into the shared registry.
        // The registry is append-only: prior discriminants are preserved.
        self.registry.registerDefsAndBodies(self.allocator, program.defs) catch return error.OutOfMemory;

        // Merge constructor field types from the GRIN program's field_types map.
        self.registry.registerFieldTypes(self.allocator, program.field_types) catch return error.OutOfMemory;

        // Link TypeEnv to the registry for field type lookups.
        self.type_env.setRegistry(self.registry);
        // Link arity map for correct forward declarations (issue #595).
        self.arity_map = &program.arities;

        // Emit __rhc_force(ptr) → ptr once the registry is complete.
        // In whole-program mode, emit it here.  In REPL mode, the JIT
        // engine manages a shared external __rhc_force via
        // `emitForceModuleIr` / `emitSharedForceModule` — expression
        // modules must NOT define it to avoid duplicate-symbol errors.
        // P-tags also require __rhc_force: case sites rely on it to call
        // saturated partial applications (P(0) nodes) in scrutinees.
        if (self.registry.fun_tags.count() > 0 or self.registry.partial_tags.count() > 0) {
            if (self.repl_entry_point == null) {
                // Whole-program mode: emit the force function here.
                try self.emitForceFunction();
            } else {
                // REPL mode: declare __rhc_force as external; the shared
                // force module (emitted by JitEngine) provides the definition.
                const ptr_ty = ptrType();
                var param_types = [_]llvm.Type{ptr_ty};
                const fn_type = c.LLVMFunctionType(ptr_ty, &param_types, 1, 0);
                _ = llvm.addFunction(self.module, "__rhc_force", fn_type);
            }
        }

        // Emit __rhc_apply(ptr, ptr) → ptr for partial application dispatch.
        // Same REPL-mode pattern as __rhc_force: expression modules must NOT
        // define __rhc_apply to avoid duplicate-symbol errors in ORC JIT.
        // The shared force/apply module (emitForceModule) provides the definition.
        if (self.registry.partial_tags.count() > 0) {
            if (self.repl_entry_point == null) {
                // Whole-program mode: emit the apply function here.
                try self.emitApplyFunction();
            } else {
                // REPL mode: declare __rhc_apply as external; the shared
                // force/apply module (emitted by JitEngine) provides the definition.
                const ptr_ty = ptrType();
                var apply_params = [_]llvm.Type{ ptr_ty, ptr_ty };
                const apply_fn_type = c.LLVMFunctionType(ptr_ty, &apply_params, 2, 0);
                _ = llvm.addFunction(self.module, "__rhc_apply", apply_fn_type);
            }
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
        // Refresh the TypeEnv pointer to the registry.
        self.type_env.setRegistry(self.registry);
        // Link arity map for correct forward declarations (issue #595).
        self.arity_map = &prog.arities;

        const mod = llvm.createModule(module_name, self.ctx);

        // Temporarily point self.module at the new per-module LLVM module so
        // that translateDef emits all functions into it.  Restored afterwards.
        const saved_module = self.module;
        self.module = mod;

        // Per-def modules do NOT emit __rhc_force.  They declare it as
        // external and ORC JIT resolves calls to the shared force module
        // emitted by `emitForceModuleIr`.  This ensures per-def code can
        // force thunks with F-tags introduced by later REPL expressions
        // that the per-def tag table didn't know about at compile time.
        if (self.registry.fun_tags.count() > 0 or self.registry.partial_tags.count() > 0) {
            // Declare __rhc_force as an external function so that
            // callForceIfNeeded can find it via LLVMGetNamedFunction.
            const ptr_ty = ptrType();
            var param_types = [_]llvm.Type{ptr_ty};
            const fn_type = c.LLVMFunctionType(ptr_ty, &param_types, 1, 0);
            _ = llvm.addFunction(mod, "__rhc_force", fn_type);
        }

        // Declare __rhc_apply as external so that per-def modules that route
        // single-argument indirect calls through it can resolve the symbol.
        // The definition lives in the shared force/apply module emitted by
        // `emitForceModule`.  Mirrors the __rhc_force pattern above.
        if (self.registry.partial_tags.count() > 0) {
            const ptr_ty = ptrType();
            var apply_params = [_]llvm.Type{ ptr_ty, ptr_ty };
            const apply_fn_type = c.LLVMFunctionType(ptr_ty, &apply_params, 2, 0);
            _ = llvm.addFunction(mod, "__rhc_apply", apply_fn_type);
        }

        for (prog.defs) |def| {
            try self.translateDef(def);
        }
        self.module = saved_module;

        return mod;
    }

    /// Emit a standalone LLVM module containing only `__rhc_force` with
    /// **external** linkage.  Used by both the native backend (per-module
    /// compilation) and the REPL JIT engine to provide a single shared
    /// force function that all other modules can call.
    ///
    /// Per-module code declares `__rhc_force` as external; the linker
    /// (native) or ORC JIT (REPL) resolves calls to this shared copy.
    ///
    /// Returns the LLVM module.  Caller must not dispose it if it will be
    /// linked via `LLVMLinkModules2` (which disposes source modules).
    pub fn emitForceModule(self: *GrinTranslator) TranslationError!llvm.Module {
        const mod = llvm.createModule("rhc_force", self.ctx);
        const saved_module = self.module;
        self.module = mod;
        defer self.module = saved_module;

        if (self.registry.fun_tags.count() > 0 or self.registry.partial_tags.count() > 0) {
            try self.emitForceFunction();
        }

        // Emit __rhc_apply alongside __rhc_force so that per-def modules that
        // declare it as external can resolve it through the same shared module.
        // This is safe for all paths: per-module AOT (translateModuleGrin +
        // emitForceModule) and REPL (per-def + shared force module). The
        // whole-program AOT path (translateProgramToModule) does NOT call
        // emitForceModule, so there is no duplicate definition risk.
        if (self.registry.partial_tags.count() > 0) {
            try self.emitApplyFunction();
        }

        return mod;
    }

    /// Like `emitForceModule` but returns LLVM IR text instead of the
    /// module object.  Used by the REPL JIT engine which parses IR text
    /// via `LLVMParseIRInContext`.
    pub fn emitForceModuleIr(self: *GrinTranslator) TranslationError![]u8 {
        const mod = try self.emitForceModule();
        return llvm.printModuleToString(mod, self.allocator) catch
            return error.OutOfMemory;
    }

    /// The unbox mask for a worker/wrapper split (#803) of the named
    /// function, or 0 when no worker applies. Conditions kept in sync
    /// between the def site (translateDef) and call sites
    /// (translateAppToValue): demand analysis ran, the function has
    /// 1..8 parameters, and at least one strict parameter has an
    /// immediate-representation type (Int/Char).
    fn workerUnboxMask(self: *const GrinTranslator, fn_unique: u64, arity: usize) u64 {
        if (arity == 0 or arity > 8) return 0;
        const sp = self.strict_params orelse return 0;
        const dm = sp.get(fn_unique) orelse return 0;
        const arity_bits: u64 = (@as(u64, 1) << @intCast(arity)) - 1;
        return dm.unbox & arity_bits;
    }

    /// Symbol name of the unboxed worker for `name`: `"w$" ++ base_unique`.
    /// Written into `buf`; the caller owns the storage.
    fn workerSymbol(self: *GrinTranslator, name: grin.Name, buf: []u8) [:0]const u8 {
        const inner = self.formatName(name);
        const written = std.fmt.bufPrintZ(buf, "w${s}", .{inner}) catch return "w$overflow";
        return written;
    }

    /// LLVM function type of a worker: raw i64 at unboxed positions,
    /// ptr elsewhere; always returns ptr.
    fn workerFnType(unbox_mask: u64, arity: usize) llvm.Type {
        var param_types: [8]llvm.Type = undefined;
        for (0..arity) |i| {
            const unboxed = (unbox_mask >> @as(u6, @intCast(i))) & 1 == 1;
            param_types[i] = if (unboxed) llvm.i64Type() else ptrType();
        }
        return llvm.functionType(ptrType(), param_types[0..arity], false);
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
        const value_type = if (is_entry) (if (is_repl_entry) llvm.i64Type() else llvm.i32Type()) else ptrType();
        // All non-entry functions return ptr — including zero-arity CAFs
        // (e.g. dictionary bindings like `dict$Show$Int`).  These are
        // constant applicative forms that compute and return a heap node.
        //
        // Previously, batch mode used `void` for zero-arity functions, but
        // this caused an LLVM type mismatch when cross-module dictionary
        // passing called `dict$Show$Int()` and expected a `ptr` return.
        // Using `ptr` uniformly matches the REPL convention and is correct
        // because every GRIN function produces a value (#618).
        const ret_type = if (is_entry) value_type else ptrType();

        // Parameter types: i32 for main (no params), ptr for all others.
        var param_types: [8]llvm.Type = undefined;
        for (def.params[0..@min(def.params.len, 8)], 0..) |_, i| {
            param_types[i] = value_type;
        }

        const fn_type = llvm.functionType(ret_type, param_types[0..def.params.len], false);
        const fn_name_z = self.formatName(def.name);
        // Check if function was already forward-declared; if so, reuse it.
        // This prevents LLVM from adding .1 suffix due to name collision.
        const existing_fn = c.LLVMGetNamedFunction(self.module, fn_name_z);
        const func = existing_fn orelse
            llvm.addFunction(self.module, fn_name_z, fn_type);

        // ── Worker/wrapper split (#803) ───────────────────────────────
        // When the demand analysis proved some Int/Char parameters
        // strict, the function body is emitted into a worker `w$f` that
        // takes those parameters as raw i64 machine words. The original
        // symbol becomes a thin wrapper (force + untag + call worker) so
        // every boxed entry path — thunk forcing, partial application,
        // higher-order use — keeps working unchanged. Saturated direct
        // calls go straight to the worker (translateAppToValue).
        const unbox_mask = if (is_entry) 0 else self.workerUnboxMask(def.name.unique.value, def.params.len);
        const body_func = if (unbox_mask == 0) func else blk: {
            var wsym_buf: [300]u8 = undefined;
            const wsym = self.workerSymbol(def.name, &wsym_buf);
            const w_type = workerFnType(unbox_mask, def.params.len);
            const worker = c.LLVMGetNamedFunction(self.module, wsym.ptr) orelse
                llvm.addFunction(self.module, wsym, w_type);

            // Wrapper body: force + untag the unboxed positions, call
            // the worker, return its result. Allocates nothing itself,
            // and the worker roots its own pointer parameters, so no
            // shadow-stack bracketing is needed here.
            self.current_func = func;
            const wrap_entry = llvm.appendBasicBlock(func, "entry");
            llvm.positionBuilderAtEnd(self.builder, wrap_entry);
            var call_args: [8]llvm.Value = undefined;
            for (0..def.params.len) |i| {
                const p = c.LLVMGetParam(func, @intCast(i));
                if ((unbox_mask >> @as(u6, @intCast(i))) & 1 == 1) {
                    const forced = self.callForceIfNeeded(p);
                    call_args[i] = untagInt(self.builder, forced);
                } else {
                    call_args[i] = p;
                }
            }
            const r = c.LLVMBuildCall2(
                self.builder,
                w_type,
                worker,
                @ptrCast(&call_args),
                @intCast(def.params.len),
                "worker.result",
            );
            _ = llvm.buildRet(self.builder, r);
            break :blk worker;
        };

        self.current_func = body_func;
        const entry_bb = llvm.appendBasicBlock(body_func, "entry");
        llvm.positionBuilderAtEnd(self.builder, entry_bb);

        // For native `main`, if the user selected a non-default RTS
        // backend (#776), emit `call void @rts_set_backend(i32 N)` as
        // the very first instruction so the heap picks up the
        // selection before any allocation. Arena is the default, so
        // codegen omits the call (it matches lazy init).
        if (is_entry and !is_repl_entry and self.rts_backend != .arena) {
            self.emitSetRtsBackendCall(@intFromEnum(self.rts_backend));
            // Register every constructor's pointer-mask with the
            // collector (#779) before any allocation can fire.
            self.emitPointerMaskInit();
        }

        // Precise GC root tracking (#780): snapshot the shadow-stack
        // height so every return in this function can restore it.
        // Emits nothing under `--rts=arena`.
        self.enableShadowStackForCurrentFunction();
        defer self.disableShadowStackForCurrentFunction();

        // Clear previous function's parameter mapping and set up current one.
        self.params.deinit();
        self.params = std.AutoHashMap(u64, llvm.Value).init(self.allocator);
        self.whnf_vars.clearRetainingCapacity();

        // Clear the per-function case expression cache.  The cache prevents
        // exponential re-translation of shared GRIN expressions produced by the
        // sequential pattern-match compiler.
        self.case_entry_cache.clearRetainingCapacity();

        // Store each parameter as a named value in the params map. For
        // pointer-typed params, also push them onto the shadow stack so
        // the collector sees them as live across this function's body.
        //
        // Strict parameters (#802) are forced once here and tracked as
        // WHNF: the demand analysis proved every execution path forces
        // them, so a single entry force replaces every per-use force in
        // the body (a worker/wrapper-lite that keeps the boxed ABI).
        const entry_strict_mask: u64 = blk: {
            const sp = self.strict_params orelse break :blk 0;
            break :blk if (sp.get(def.name.unique.value)) |dm| dm.strict else 0;
        };
        for (def.params, 0..) |param_name, i| {
            var param_val = c.LLVMGetParam(body_func, @intCast(i));
            if (param_val == null) return error.OutOfMemory;
            if (i < 64 and (entry_strict_mask >> @intCast(i)) & 1 == 1 and
                c.LLVMGetTypeKind(c.LLVMTypeOf(param_val)) == c.LLVMPointerTypeKind)
            {
                param_val = self.callForceIfNeeded(param_val);
            }
            if (i < 64 and (entry_strict_mask >> @intCast(i)) & 1 == 1) {
                // Strict parameter: forced above (ptr) or a raw machine
                // word (worker i64) — either way WHNF from here on.
                self.whnf_vars.put(param_name.unique.value, {}) catch return error.OutOfMemory;
            }
            try self.bindAndRoot(param_name.unique.value, param_val);
        }

        // Translate the body and capture its value for return.
        //
        // Functions with parameters and REPL entry points both need
        // to capture the body's value and return it. The difference:
        //   - Parameterized functions return `ptr`
        //   - REPL entry points return `i64` (raw value or heap pointer)
        //   - Native `main` falls through to the void/unit path below
        //
        // All non-entry functions (including zero-arity CAFs like dictionary
        // bindings) compute and return a ptr value.  Zero-arity CAFs are
        // constant applicative forms that construct heap nodes and return
        // them.  This applies uniformly in both batch and REPL modes (#618).
        //
        // See: https://github.com/adinapoli/rusholme/issues/449
        if (!is_entry or is_repl_entry) {
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
                                const unit_ptr = self.buildUnitNode();
                                self.buildRetWithShadowRestore(c.LLVMBuildPtrToInt(self.builder, unit_ptr, llvm.i64Type(), "unit_i64"));
                            } else {
                                // Force any F-tagged thunks to WHNF before
                                // returning. The user expects REPL results
                                // in normal form, not unevaluated thunks.
                                const forced = if (self.registry.fun_tags.count() > 0)
                                    try self.forceValueToWhnf(val)
                                else
                                    val;
                                const as_i64 = c.LLVMBuildPtrToInt(self.builder, forced, llvm.i64Type(), "ret_i64");
                                self.buildRetWithShadowRestore(as_i64);
                            }
                        } else {
                            // Non-pointer body value (raw i64 from a literal
                            // return or arithmetic).  Tag the integer so that
                            // `formatJitResult` can distinguish integer 0 from
                            // the Unit heap-node pointer.
                            // See: https://github.com/adinapoli/rusholme/issues/621
                            const val_kind_inner = c.LLVMGetTypeKind(c.LLVMTypeOf(val));
                            if (val_kind_inner == c.LLVMIntegerTypeKind) {
                                const val_width_inner = c.LLVMGetIntTypeWidth(c.LLVMTypeOf(val));
                                const val_to_tag = if (val_width_inner == 32) blk: {
                                    break :blk c.LLVMBuildZExt(self.builder, val, llvm.i64Type(), "i32_to_i64_body");
                                } else val;
                                const tagged = tagInt(self.builder, val_to_tag);
                                const as_i64 = c.LLVMBuildPtrToInt(self.builder, tagged, llvm.i64Type(), "tagged_i64_body");
                                self.buildRetWithShadowRestore(as_i64);
                            } else {
                                self.buildRetWithShadowRestore(val);
                            }
                        }
                    } else {
                        // Non-REPL function: ensure return value matches function signature.
                        // Primop instructions return i64, but user functions return ptr.
                        // Cast i64→ptr to match the declared return type.
                        // The return-site force upholds the "call results
                        // are WHNF" convention; skip it when the body's
                        // value is statically WHNF already.
                        const val_kind2 = c.LLVMGetTypeKind(c.LLVMTypeOf(val));
                        const coerced = if (val_kind2 == c.LLVMPointerTypeKind)
                            (if (self.exprYieldsWhnf(def.body)) val else self.callForceIfNeeded(val))
                        else if (val_kind2 == c.LLVMIntegerTypeKind)
                            tagInt(self.builder, val)
                        else
                            val;
                        self.buildRetWithShadowRestore(coerced);
                    }
                } else {
                    if (is_repl_entry) {
                        // Body returned no value (e.g. IO action) —
                        // return a Unit heap node so the REPL displays
                        // nothing rather than a random integer.
                        const unit_ptr2 = self.buildUnitNode();
                        self.buildRetWithShadowRestore(c.LLVMBuildPtrToInt(self.builder, unit_ptr2, llvm.i64Type(), "unit_i64"));
                    } else {
                        self.buildRetWithShadowRestore(c.LLVMConstPointerNull(value_type));
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
                    const unit_ptr3 = self.buildUnitNode();
                    self.buildRetWithShadowRestore(c.LLVMBuildPtrToInt(self.builder, unit_ptr3, llvm.i64Type(), "unit_i64"));
                } else if (is_entry) {
                    // Native main: return 0 (success exit code, C ABI).
                    self.buildRetWithShadowRestore(c.LLVMConstInt(llvm.i32Type(), 0, 0));
                } else {
                    self.buildRetVoidWithShadowRestore();
                }
            }
        }
    }

    fn translateExpr(self: *GrinTranslator, expr: *const grin.Expr) TranslationError!void {
        switch (expr.*) {
            .App => |app| try self.translateApp(app.name, app.args),
            .Bind => |b| try self.translateBind(b.lhs, b.pat, b.rhs),
            .Case => |case_| {
                // The sequential pattern-match desugarer creates shared
                // fallback nodes (a DAG).  Without caching, each shared
                // node is re-translated at every occurrence, causing
                // exponential blowup in basic blocks and compile time.
                //
                // Cache by GRIN expression pointer: if we've already
                // translated this exact Case node, branch to its entry
                // block instead of re-emitting the dispatch logic.
                const expr_key = @intFromPtr(expr);
                if (self.case_entry_cache.get(expr_key)) |cached_entry| {
                    _ = c.LLVMBuildBr(self.builder, cached_entry);
                    return;
                }
                // First encounter: create an entry block, cache it, then
                // translate the case normally.
                const case_entry = c.LLVMAppendBasicBlock(self.current_func, "case.shared");
                _ = c.LLVMBuildBr(self.builder, case_entry);
                llvm.positionBuilderAtEnd(self.builder, case_entry);
                self.case_entry_cache.put(expr_key, case_entry) catch return error.OutOfMemory;
                try self.translateCase(case_.scrutinee, case_.alts);
            },
            .Store => |val| try self.translateStore(val),
            .Fetch => |f| try self.translateFetch(f.ptr, f.index),
            .Update => |u| try self.translateUpdate(u.ptr, u.val),
            .Return => |r| try self.translateReturn(r),
            .Block => |e| try self.translateExpr(e),
        }
    }

    /// Whether a GRIN value is statically known to be in WHNF when it
    /// reaches an SSA binding: literals and tagged immediates trivially;
    /// constructor nodes by construction; variables if already tracked.
    fn valYieldsWhnf(self: *const GrinTranslator, val: grin.Val) bool {
        return switch (val) {
            .Lit, .ValTag => true,
            .ConstTagNode => |ctn| ctn.tag.tag_type == .Con,
            .Var => |v| self.whnf_vars.contains(v.unique.value),
            else => false,
        };
    }

    /// Whether a GRIN expression's result is statically known to be in
    /// WHNF. Conservative: anything unrecognised is assumed forceable.
    ///
    /// Primop instruction results are tagged immediates; a `Store` of a
    /// constructor node is WHNF (F/P-tag stores are thunks/closures and
    /// are not). Direct function calls are WHNF by calling convention:
    /// every non-main GRIN function forces its return value at the return
    /// site (see translateReturn) — and that force is itself only elided
    /// when the returned value is already statically WHNF, so the
    /// convention is preserved inductively.
    fn exprYieldsWhnf(self: *const GrinTranslator, expr: *const grin.Expr) bool {
        return switch (expr.*) {
            .Return => |v| self.valYieldsWhnf(v),
            .Store => |v| switch (v) {
                .ConstTagNode => |ctn| ctn.tag.tag_type == .Con,
                else => false,
            },
            .App => |app| blk: {
                // `pure` passes its argument through unevaluated.
                if (std.mem.eql(u8, app.name.base, "pure"))
                    break :blk app.args.len > 0 and self.valYieldsWhnf(app.args[0]);
                if (PrimOpMapping.lookup(app.name)) |m|
                    break :blk m == .instruction;
                // Direct call (or apply): result forced at the callee's
                // return site per the calling convention above.
                break :blk true;
            },
            .Block => |inner| self.exprYieldsWhnf(inner),
            // A bind chain yields its continuation's value. By the time
            // this runs at a return site, codegen has already walked the
            // chain and recorded WHNF-ness of every bound variable.
            .Bind => |b| self.exprYieldsWhnf(b.rhs),
            else => false,
        };
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
                // General case: evaluate LHS and bind result to variable.
                // If the LHS contains a Case expression (directly or nested in a Bind),
                // translateExprToValue will handle it correctly via the .Case branch
                // which calls translateCaseToValue to generate phi nodes.
                const result = try self.translateExprToValue(lhs, v.base);
                if (result) |val| {
                    if (self.exprYieldsImmediate(lhs)) {
                        // Tagged immediate — no heap pointer, no root.
                        try self.params.put(v.unique.value, val);
                    } else {
                        try self.bindAndRoot(v.unique.value, val);
                    }
                    if (self.exprYieldsWhnf(lhs)) {
                        self.whnf_vars.put(v.unique.value, {}) catch return error.OutOfMemory;
                    }
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
                    try self.bindAndRoot(field_var.unique.value, loaded);
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
                        if (inner_result) |val| {
                            if (self.exprYieldsImmediate(b.lhs)) {
                                // Tagged immediate — no heap pointer, no root.
                                try self.params.put(v.unique.value, val);
                            } else {
                                try self.bindAndRoot(v.unique.value, val);
                            }
                            if (self.exprYieldsWhnf(b.lhs)) {
                                self.whnf_vars.put(v.unique.value, {}) catch return error.OutOfMemory;
                            }
                        }
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
                                try self.bindAndRoot(fv.unique.value, loaded);
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
            .Case => |case_expr| {
                // Case expression in value-producing context (e.g., nested in a bind RHS).
                //
                // Shared GRIN Case nodes (from the desugarer's DAG) may appear
                // multiple times in alt bodies.  If we've already translated this
                // exact Case node, branch to its cached entry block instead of
                // re-translating.  The cached code terminates with ret/br so
                // control never returns — we emit a dead placeholder block for
                // the caller to continue emitting without LLVM errors.
                const expr_key = @intFromPtr(expr);
                if (self.case_entry_cache.get(expr_key)) |cached_entry| {
                    _ = c.LLVMBuildBr(self.builder, cached_entry);
                    const dead_bb = c.LLVMAppendBasicBlock(self.current_func, "dead.cached");
                    llvm.positionBuilderAtEnd(self.builder, dead_bb);
                    return @as(?llvm.Value, c.LLVMConstPointerNull(ptrType()));
                }
                // First encounter: create an entry block and cache it before
                // translating, so that subsequent encounters of this shared
                // Case node can branch here directly.
                const case_entry = c.LLVMAppendBasicBlock(self.current_func, "caseval.shared");
                _ = c.LLVMBuildBr(self.builder, case_entry);
                llvm.positionBuilderAtEnd(self.builder, case_entry);
                self.case_entry_cache.put(expr_key, case_entry) catch return error.OutOfMemory;
                return try self.translateCaseToValue(case_expr.scrutinee, case_expr.alts, result_name);
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

        // Intercept calls to the GRIN-level `apply` stub (unique 9998)
        // and route them to the LLVM-level __rhc_apply instead.
        if (std.mem.eql(u8, name.base, "apply") and name.unique.value == 9998) {
            if (args.len >= 2) {
                const f_val = try self.translateValToLlvm(args[0]);
                const x_val = try self.translateValToLlvm(args[1]);
                const apply_fn = c.LLVMGetNamedFunction(self.module, "__rhc_apply") orelse blk: {
                    var apply_params = [_]llvm.Type{ ptrType(), ptrType() };
                    const apply_type = llvm.functionType(ptrType(), &apply_params, false);
                    break :blk llvm.addFunction(self.module, "__rhc_apply", apply_type);
                };
                var apply_args = [_]llvm.Value{ f_val, x_val };
                return c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(apply_fn),
                    apply_fn,
                    &apply_args,
                    2,
                    "apply_result",
                );
            }
            return null;
        }

        if (PrimOpMapping.lookup(name)) |mapping| {
            switch (mapping) {
                .libcall => |libc_fn| {
                    try self.emitLibcCall(libc_fn, args);
                    return c.LLVMConstPointerNull(ptrType());
                },
                .instruction => |instr| {
                    const raw = try self.emitInstruction(instr, args);
                    if (raw) |val| {
                        if (isComparisonOp(instr)) {
                            // Comparison: wrap i1 result as a Bool heap node
                            return try self.wrapComparisonAsBool(val);
                        }
                        // Arithmetic/identity: the raw result is i64 or ptr.
                        // Normalise to ptr so case-alternative phi nodes
                        // don't mis-box the value as a heap-node tag via
                        // rts_alloc (which would corrupt the raw Int/Char).
                        if (c.LLVMGetTypeKind(c.LLVMTypeOf(val)) == c.LLVMIntegerTypeKind) {
                            return tagInt(self.builder, val);
                        }
                        return val;
                    }
                    return c.LLVMConstPointerNull(ptrType());
                },
            }
        }

        // User-defined function call.
        var llvm_args: [8]llvm.Value = undefined;
        const arg_count = @min(args.len, 8);
        for (args[0..arg_count], 0..) |val, i| {
            llvm_args[i] = try self.translateValToLlvm(val);
        }

        // ── Worker fast path (#803) ──────────────────────────────────
        // Saturated direct call to a function with unboxable strict
        // parameters: call the `w$` worker, passing raw i64 at unboxed
        // positions. Boxed pointer arguments are forced (elided when
        // statically WHNF) and untagged; raw i64 arguments (literals)
        // pass through. Higher-order and unsaturated uses fall through
        // to the wrapper, which preserves the boxed ABI.
        if (self.params.get(name.unique.value) == null and !self.isEntryPoint(name.base)) {
            const saturated = if (self.arity_map) |am|
                (if (am.get(name.unique.value)) |arity| arity == args.len else false)
            else
                false;
            if (saturated) {
                const unbox_mask = self.workerUnboxMask(name.unique.value, args.len);
                if (unbox_mask != 0) {
                    var wsym_buf: [300]u8 = undefined;
                    const wsym = self.workerSymbol(name, &wsym_buf);
                    const w_type = workerFnType(unbox_mask, args.len);
                    const worker = c.LLVMGetNamedFunction(self.module, wsym.ptr) orelse
                        llvm.addFunction(self.module, wsym, w_type);
                    var w_args: [8]llvm.Value = undefined;
                    for (0..arg_count) |i| {
                        const raw = llvm_args[i];
                        const is_ptr_arg = c.LLVMGetTypeKind(c.LLVMTypeOf(raw)) == c.LLVMPointerTypeKind;
                        if ((unbox_mask >> @as(u6, @intCast(i))) & 1 == 1) {
                            w_args[i] = if (is_ptr_arg)
                                untagInt(self.builder, self.forceOperandIfNeeded(raw, args[i]))
                            else
                                raw; // already a raw machine word (literal)
                        } else {
                            // Mirror the regular coercion: raw integers
                            // become tagged immediates for ptr params.
                            w_args[i] = if (is_ptr_arg) raw else tagInt(self.builder, raw);
                        }
                    }
                    return c.LLVMBuildCall2(
                        self.builder,
                        w_type,
                        worker,
                        @ptrCast(&w_args),
                        @intCast(arg_count),
                        nullTerminate(result_name).ptr,
                    );
                }
            }
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

        // Coerce i64 arguments to ptr: integer literals (e.g., #1, #2) are
        // translated to i64 by translateValToLlvm, but GRIN functions use
        // opaque ptr for all parameters.
        for (0..arg_count) |i| {
            if (@intFromPtr(llvm_args[i]) == 0) {
                return null;
            }
            const arg_ty = c.LLVMTypeOf(llvm_args[i]);
            const arg_kind = c.LLVMGetTypeKind(arg_ty);
            if (arg_kind == c.LLVMIntegerTypeKind) {
                if (args[i] == .ValTag) {
                    // Nullary constructors (e.g. MkA, True, False) are
                    // translated as i64 discriminants but the callee
                    // expects a heap-allocated node it can pattern-match
                    // on. Box via the inline-alloc fast path.
                    llvm_args[i] = self.emitAlloc(llvm_args[i], 0, "boxed_tag");
                } else {
                    // Plain integer literal — tag and pass through.
                    llvm_args[i] = tagInt(self.builder, llvm_args[i]);
                }
            }
        }

        // Resolve the callee:
        //   1. Local variable holding a function pointer (higher-order call) — use
        //      an indirect call via the pointer stored in `params`.
        //   2. Named LLVM function (direct call to a known def).
        //   3. Forward-declare and call (for functions not yet translated).
        var callee_from_params = false;
        const func: llvm.Value = blk: {
            if (self.params.get(name.unique.value)) |fn_ptr| {
                callee_from_params = true;
                break :blk fn_ptr;
            }
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

        // For single-argument calls through case/param-bound variables (e.g.
        // method selectors extracting `fn` from a dictionary), route through
        // __rhc_apply when Partial application nodes exist.  Dictionary fields
        // for constrained instances (e.g. Show [a]) store P-tagged heap nodes,
        // not direct function pointers; __rhc_apply dispatches correctly for
        // both.
        // tracked in: https://github.com/adinapoli/rusholme/issues/629
        if (callee_from_params and arg_count == 1 and
            self.registry.partial_tags.count() > 0)
        {
            const apply_fn = c.LLVMGetNamedFunction(self.module, "__rhc_apply") orelse blk: {
                var ap = [_]llvm.Type{ ptrType(), ptrType() };
                const at = llvm.functionType(ptrType(), &ap, false);
                break :blk llvm.addFunction(self.module, "__rhc_apply", at);
            };
            var apply_args = [_]llvm.Value{ func, llvm_args[0] };
            return c.LLVMBuildCall2(
                self.builder,
                llvm.getFunctionType(apply_fn),
                apply_fn,
                &apply_args,
                2,
                res_z,
            );
        }

        // Multi-argument calls through param-bound variables (#386): the
        // value is either a P-tagged node (constructor/function partial
        // application — must chain __rhc_apply per argument) or a raw
        // function pointer (monomorphic dictionary field — must be called
        // directly at full arity).  Statically indistinguishable, so emit
        // an inline tag dispatch.
        if (callee_from_params and arg_count >= 2 and
            self.registry.partial_tags.count() > 0)
        {
            return try self.emitParamApplyDispatch(func, llvm_args[0..arg_count], fn_type, res_z);
        }

        return c.LLVMBuildCall2(
            self.builder,
            fn_type,
            func,
            @ptrCast(&llvm_args),
            @intCast(arg_count),
            res_z,
        );
    }

    /// Emit an inline runtime dispatch for a multi-argument call through a
    /// param-bound function value (#386):
    ///
    /// ```
    ///   tag = load i64, f
    ///   switch tag [each P-tag discriminant] → bb_apply, else → bb_direct
    /// bb_apply:                 ; P-node: chain one __rhc_apply per arg
    ///   r = __rhc_apply(f, x1) ; r = __rhc_apply(r, x2) ; …
    /// bb_direct:                ; raw function pointer: full-arity call
    ///   d = call f(x1, …, xn)
    /// merge:
    ///   phi [r, bb_apply], [d, bb_direct]
    /// ```
    ///
    /// Loading the first word of a raw function pointer reads code bytes —
    /// readable on every supported target — and cannot collide with a P-tag
    /// discriminant assigned by the TagTable only to heap nodes... except by
    /// astronomical coincidence; the same assumption underpins __rhc_apply's
    /// own default branch.
    fn emitParamApplyDispatch(
        self: *GrinTranslator,
        func: llvm.Value,
        args: []const llvm.Value,
        fn_type: llvm.Type,
        res_z: [*:0]const u8,
    ) TranslationError!llvm.Value {
        const i64_ty = llvm.i64Type();
        const i32_ty = llvm.i32Type();
        const header_ty = nodeHeaderType();
        const cur_func = self.current_func orelse return error.UnsupportedGrinVal;

        const apply_fn = c.LLVMGetNamedFunction(self.module, "__rhc_apply") orelse blk: {
            var ap = [_]llvm.Type{ ptrType(), ptrType() };
            const at = llvm.functionType(ptrType(), &ap, false);
            break :blk llvm.addFunction(self.module, "__rhc_apply", at);
        };

        const bb_apply = llvm.appendBasicBlock(cur_func, "pap_apply");
        const bb_direct = llvm.appendBasicBlock(cur_func, "pap_direct");
        const bb_merge = llvm.appendBasicBlock(cur_func, "pap_merge");

        // entry: load the tag word and switch on P-tag discriminants.
        var tag_idx = [_]llvm.Value{
            c.LLVMConstInt(i32_ty, 0, 0),
            c.LLVMConstInt(i32_ty, 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, func, &tag_idx, 2, "pap_tag_gep");
        const tag_val = c.LLVMBuildLoad2(self.builder, i64_ty, tag_gep, "pap_tag");
        const sw = c.LLVMBuildSwitch(self.builder, tag_val, bb_direct, @intCast(self.registry.partial_tags.count()));
        var ptag_iter = self.registry.partial_tags.iterator();
        while (ptag_iter.next()) |entry| {
            const disc = self.registry.discriminants.get(entry.key_ptr.*) orelse continue;
            c.LLVMAddCase(sw, c.LLVMConstInt(i64_ty, @bitCast(disc), 0), bb_apply);
        }

        // bb_apply: chain __rhc_apply per argument.
        llvm.positionBuilderAtEnd(self.builder, bb_apply);
        var chained: llvm.Value = func;
        for (args) |arg| {
            var apply_args = [_]llvm.Value{ chained, arg };
            chained = c.LLVMBuildCall2(
                self.builder,
                llvm.getFunctionType(apply_fn),
                apply_fn,
                &apply_args,
                2,
                "ap_chain",
            );
        }
        _ = c.LLVMBuildBr(self.builder, bb_merge);
        const bb_apply_end = c.LLVMGetInsertBlock(self.builder);

        // bb_direct: full-arity call through the raw function pointer.
        llvm.positionBuilderAtEnd(self.builder, bb_direct);
        var direct_args: [8]llvm.Value = undefined;
        @memcpy(direct_args[0..args.len], args);
        const direct = c.LLVMBuildCall2(
            self.builder,
            fn_type,
            func,
            @ptrCast(&direct_args),
            @intCast(args.len),
            "pap_direct_call",
        );
        _ = c.LLVMBuildBr(self.builder, bb_merge);
        const bb_direct_end = c.LLVMGetInsertBlock(self.builder);

        // merge: phi over both results.
        llvm.positionBuilderAtEnd(self.builder, bb_merge);
        const phi = c.LLVMBuildPhi(self.builder, ptrType(), res_z);
        var incoming_vals = [_]llvm.Value{ chained, direct };
        var incoming_bbs = [_]llvm.BasicBlock{ bb_apply_end, bb_direct_end };
        c.LLVMAddIncoming(phi, &incoming_vals, &incoming_bbs, 2);
        return phi;
    }

    fn translateApp(self: *GrinTranslator, name: grin.Name, args: []const grin.Val) TranslationError!void {
        if (std.mem.eql(u8, name.base, "pure")) return;

        // Intercept calls to the GRIN-level `apply` stub (unique 9998).
        if (std.mem.eql(u8, name.base, "apply") and name.unique.value == 9998) {
            if (args.len >= 2) {
                const f_val = try self.translateValToLlvm(args[0]);
                const x_val = try self.translateValToLlvm(args[1]);
                const apply_fn = c.LLVMGetNamedFunction(self.module, "__rhc_apply") orelse blk: {
                    var apply_params = [_]llvm.Type{ ptrType(), ptrType() };
                    const apply_type = llvm.functionType(ptrType(), &apply_params, false);
                    break :blk llvm.addFunction(self.module, "__rhc_apply", apply_type);
                };
                var apply_args = [_]llvm.Value{ f_val, x_val };
                _ = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(apply_fn),
                    apply_fn,
                    &apply_args,
                    2,
                    "",
                );
            }
            return;
        }

        if (PrimOpMapping.lookup(name)) |mapping| {
            switch (mapping) {
                .libcall => |libc_fn| try self.emitLibcCall(libc_fn, args),
                .instruction => |instr| {
                    _ = try self.emitInstruction(instr, args);
                },
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

        // Coerce i64 arguments to ptr (same logic as translateAppToValue).
        for (0..arg_count) |i| {
            if (@intFromPtr(llvm_args[i]) == 0) return;
            const arg_ty = c.LLVMTypeOf(llvm_args[i]);
            const arg_kind = c.LLVMGetTypeKind(arg_ty);
            if (arg_kind == c.LLVMIntegerTypeKind) {
                if (args[i] == .ValTag) {
                    llvm_args[i] = self.emitAlloc(llvm_args[i], 0, "boxed_tag");
                } else {
                    llvm_args[i] = tagInt(self.builder, llvm_args[i]);
                }
            }
        }

        var callee_from_params_app = false;
        const func: llvm.Value = blk: {
            if (self.params.get(name.unique.value)) |fn_ptr| {
                callee_from_params_app = true;
                break :blk fn_ptr;
            }
            const fn_name_z = self.formatName(name);
            if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |existing| break :blk existing;
            break :blk llvm.addFunction(self.module, fn_name_z, fn_type);
        };

        // Route single-arg params-based calls through __rhc_apply when P-tags exist.
        // tracked in: https://github.com/adinapoli/rusholme/issues/629
        if (callee_from_params_app and arg_count == 1 and
            self.registry.partial_tags.count() > 0)
        {
            const apply_fn = c.LLVMGetNamedFunction(self.module, "__rhc_apply") orelse blk: {
                var ap = [_]llvm.Type{ ptrType(), ptrType() };
                const at = llvm.functionType(ptrType(), &ap, false);
                break :blk llvm.addFunction(self.module, "__rhc_apply", at);
            };
            var apply_args = [_]llvm.Value{ func, llvm_args[0] };
            _ = c.LLVMBuildCall2(
                self.builder,
                llvm.getFunctionType(apply_fn),
                apply_fn,
                &apply_args,
                2,
                "",
            );
            return;
        }

        // Multi-argument calls through param-bound variables (#386): emit
        // the P-node vs raw-function-pointer dispatch (result discarded).
        if (callee_from_params_app and arg_count >= 2 and
            self.registry.partial_tags.count() > 0)
        {
            _ = try self.emitParamApplyDispatch(func, llvm_args[0..arg_count], fn_type, "");
            return;
        }

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
            llvm_args[i] = switch (libc_fn.arg_strategy) {
                // For primops that expect C strings: string literals are passed
                // directly as global string pointers (avoiding a round-trip through
                // [Char] lists). Variables are assumed to be [Char] lists (the
                // Haskell representation of String) and are converted via the RTS.
                .string_to_global_ptr => switch (val) {
                    .Lit => |lit| switch (lit) {
                        .String => |s| try self.translateStringLitToPtr(s),
                        else => try self.translateValToLlvm(val),
                    },
                    else => self.emitCharlistToCstring(try self.translateValToLlvm(val)),
                },
                .value_passthrough => blk: {
                    const raw = try self.translateValToLlvm(val);
                    // If the argument is a heap pointer it might be an
                    // unevaluated thunk (F-tag node). Force it to WHNF
                    // before passing to the RTS function, then untag the
                    // tagged integer so the callee receives a plain value.
                    if (c.LLVMGetTypeKind(c.LLVMTypeOf(raw)) == c.LLVMPointerTypeKind) {
                        const forced = self.callForceIfNeeded(raw);
                        break :blk untagInt(self.builder, forced);
                    }
                    break :blk raw;
                },
            };
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

    /// Emit a call to rts_charlist_to_cstring to convert a [Char] heap list
    /// to a null-terminated C string pointer.
    fn emitCharlistToCstring(self: *GrinTranslator, list_val: llvm.Value) llvm.Value {
        // Declare rts_charlist_to_cstring if not already declared
        const conv_fn = blk: {
            const existing = c.LLVMGetNamedFunction(self.module, "rts_charlist_to_cstring");
            if (existing) |f| break :blk f;
            // Signature: ptr rts_charlist_to_cstring(ptr list, i64 cons_disc, i64 nil_disc)
            var param_types = [_]llvm.Type{ ptrType(), llvm.i64Type(), llvm.i64Type() };
            const ft = c.LLVMFunctionType(ptrType(), &param_types, 3, 0);
            break :blk llvm.addFunction(self.module, "rts_charlist_to_cstring", ft);
        };

        // Look up the (:) and [] discriminants from the tag table
        const cons_disc: i64 = self.registry.findByName("(:)") orelse 0;
        const nil_disc: i64 = self.registry.findByName("[]") orelse 0;

        // Ensure list_val is a pointer (it may be an i64 if from PtrToInt)
        const list_ptr = if (c.LLVMGetTypeKind(c.LLVMTypeOf(list_val)) == c.LLVMIntegerTypeKind)
            c.LLVMBuildIntToPtr(self.builder, list_val, ptrType(), "list_ptr")
        else
            list_val;

        var call_args = [_]llvm.Value{
            list_ptr,
            c.LLVMConstInt(llvm.i64Type(), @bitCast(cons_disc), 0),
            c.LLVMConstInt(llvm.i64Type(), @bitCast(nil_disc), 0),
        };
        return c.LLVMBuildCall2(
            self.builder,
            c.LLVMGlobalGetValueType(conv_fn),
            conv_fn,
            &call_args,
            3,
            "cstr",
        );
    }

    /// Emit a call to rts_cstring_to_charlist to convert a C string pointer
    /// to a [Char] heap list (Cons/Nil linked list).
    ///
    /// Called when a string literal value needs to be represented as a [Char]
    /// list at runtime (e.g., when passed to a user-defined function that
    /// pattern-matches on list constructors).
    fn emitCstringToCharlist(self: *GrinTranslator, str_val: llvm.Value) llvm.Value {
        const conv_fn = blk: {
            const existing = c.LLVMGetNamedFunction(self.module, "rts_cstring_to_charlist");
            if (existing) |f| break :blk f;
            // Signature: ptr rts_cstring_to_charlist(ptr str, i64 cons_disc, i64 nil_disc)
            var param_types = [_]llvm.Type{ ptrType(), llvm.i64Type(), llvm.i64Type() };
            const ft = c.LLVMFunctionType(ptrType(), &param_types, 3, 0);
            break :blk llvm.addFunction(self.module, "rts_cstring_to_charlist", ft);
        };

        const cons_disc: i64 = self.registry.findByName("(:)") orelse 0;
        const nil_disc: i64 = self.registry.findByName("[]") orelse 0;

        var call_args = [_]llvm.Value{
            str_val,
            c.LLVMConstInt(llvm.i64Type(), @bitCast(cons_disc), 0),
            c.LLVMConstInt(llvm.i64Type(), @bitCast(nil_disc), 0),
        };
        return c.LLVMBuildCall2(
            self.builder,
            c.LLVMGlobalGetValueType(conv_fn),
            conv_fn,
            &call_args,
            3,
            "charlist",
        );
    }

    /// Emit an LLVM instruction for a GRIN primop application.
    /// Returns the raw LLVM value (i64 for arithmetic, i1 for comparisons)
    /// so the caller can decide how to use it.
    fn emitInstruction(self: *GrinTranslator, instr: LLVMInstruction, args: []const grin.Val) TranslationError!?llvm.Value {
        // seq is a no-op that doesn't need arguments
        if (instr == .seq) {
            // Monadic sequencing - nothing to do, the bind structure handles it
            return null;
        }

        // Identity passthrough (intToChar, charToInt) — both are i64 at
        // the value level, but we return ptr so that case-alternative phi
        // normalisation does not box the result as a heap node (which would
        // treat the raw value as a tag discriminant).
        // Force pointer args in case they are unevaluated thunks (e.g. a
        // Char extracted from a lazy list produced by `show`).
        if (instr == .identity) {
            if (args.len < 1) return error.UnsupportedGrinVal;
            const operand_raw = try self.translateValToLlvm(args[0]);
            if (c.LLVMGetTypeKind(c.LLVMTypeOf(operand_raw)) == c.LLVMPointerTypeKind) {
                // Already a pointer — force thunks and return as-is.
                return self.forceOperandIfNeeded(operand_raw, args[0]);
            }
            // Raw i64 — tag as ptr to avoid mis-boxing downstream.
            return tagInt(self.builder, operand_raw);
        }

        // Unary instructions (neg_Int, abs_Int)
        if (instr == .neg or instr == .abs) {
            if (args.len < 1) return error.UnsupportedGrinVal;
            const operand_raw = try self.translateValToLlvm(args[0]);
            // Force the operand if it's a pointer — it may be an unevaluated
            // thunk (e.g. F:div).  Without forcing, ptrtoint would give the
            // heap address instead of the Haskell integer value.
            const operand_forced = if (c.LLVMGetTypeKind(c.LLVMTypeOf(operand_raw)) == c.LLVMPointerTypeKind)
                self.forceOperandIfNeeded(operand_raw, args[0])
            else
                operand_raw;
            const operand = if (c.LLVMGetTypeKind(c.LLVMTypeOf(operand_forced)) == c.LLVMPointerTypeKind)
                untagInt(self.builder, operand_forced)
            else
                operand_forced;
            // Return ptr (via inttoptr) — same rationale as binary arithmetic.
            const raw_unary = switch (instr) {
                .neg => c.LLVMBuildNeg(self.builder, operand, "neg"),
                .abs => blk: {
                    // abs(x) = x >= 0 ? x : -x
                    const zero = c.LLVMConstInt(llvm.i64Type(), 0, 0);
                    const is_neg = c.LLVMBuildICmp(
                        self.builder,
                        @as(c_uint, @bitCast(c.LLVMIntSLT)),
                        operand,
                        zero,
                        "is_neg",
                    );
                    const negated = c.LLVMBuildNeg(self.builder, operand, "negated");
                    break :blk c.LLVMBuildSelect(self.builder, is_neg, negated, operand, "abs");
                },
                else => unreachable,
            };
            return tagInt(self.builder, raw_unary);
        }

        if (args.len < 2) return error.UnsupportedGrinVal;

        const lhs_raw = try self.translateValToLlvm(args[0]);
        const rhs_raw = try self.translateValToLlvm(args[1]);

        // Force operands if they are pointers — they may be unevaluated
        // thunks (e.g. F:div).  Without forcing, ptrtoint would give the
        // heap address instead of the Haskell integer value.
        const lhs_forced = if (c.LLVMGetTypeKind(c.LLVMTypeOf(lhs_raw)) == c.LLVMPointerTypeKind)
            self.forceOperandIfNeeded(lhs_raw, args[0])
        else
            lhs_raw;
        const rhs_forced = if (c.LLVMGetTypeKind(c.LLVMTypeOf(rhs_raw)) == c.LLVMPointerTypeKind)
            self.forceOperandIfNeeded(rhs_raw, args[1])
        else
            rhs_raw;

        // Coerce operands to i64: function parameters are ptr-typed in GRIN,
        // but arithmetic/comparison primops operate on integer values.
        const lhs = if (c.LLVMGetTypeKind(c.LLVMTypeOf(lhs_forced)) == c.LLVMPointerTypeKind)
            untagInt(self.builder, lhs_forced)
        else
            lhs_forced;
        const rhs = if (c.LLVMGetTypeKind(c.LLVMTypeOf(rhs_forced)) == c.LLVMPointerTypeKind)
            untagInt(self.builder, rhs_forced)
        else
            rhs_forced;

        // Arithmetic ops return ptr (via inttoptr) so that downstream
        // case-alternative phi normalisation never sees raw i64 from a
        // primop — only from true constructor discriminants.  Without
        // this, the phi path would call rts_alloc(raw_value, 0) and
        // treat the integer as a tag, corrupting the result.
        // Comparisons still return i1 (caller wraps as Bool heap node).
        const raw_result = switch (instr) {
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
            .neg, .abs => unreachable, // handled above
            .seq => unreachable, // handled above
            .identity => unreachable, // handled above
        };
        if (isComparisonOp(instr)) return raw_result; // i1 — caller wraps
        return tagInt(self.builder, raw_result);
    }

    /// Check whether a primop instruction is a comparison (returns i1/Bool).
    fn isComparisonOp(instr: LLVMInstruction) bool {
        return switch (instr) {
            .eq, .ne, .slt, .sle, .sgt, .sge => true,
            else => false,
        };
    }

    /// Wrap an i1 comparison result in a Bool constructor heap node.
    /// Produces: select i1 %cmp, i64 <true_disc>, i64 <false_disc> → rts_alloc(tag, 0)
    fn wrapComparisonAsBool(self: *GrinTranslator, cmp_i1: llvm.Value) TranslationError!llvm.Value {
        // Look up True/False discriminants by their exact tag (unique + type).
        // This works for NoImplicitPrelude modules where Bool uses the
        // built-in Known.Con uniques (200/201).  For Prelude-imported
        // modules, the caller's case alternatives also use these uniques
        // because the renamer resolves True/False to whatever is in scope
        // (which is the built-in for modules that don't re-declare Bool,
        // or the Prelude's re-declared version which gets the same
        // discriminant since it's the same constructor).
        const true_name = grin.Name{ .base = "True", .unique = .{ .value = known.true_val } };
        const false_name = grin.Name{ .base = "False", .unique = .{ .value = known.false_val } };
        const true_tag = grin.Tag{ .tag_type = .Con, .name = true_name };
        const false_tag = grin.Tag{ .tag_type = .Con, .name = false_name };
        // Try exact unique match first, then fall back to name-based lookup
        // for contexts where the Prelude assigned fresh uniques to Bool.
        const true_disc: i64 = self.registry.discriminant(true_tag) orelse
            self.registry.findByName("True") orelse 2;
        const false_disc: i64 = self.registry.discriminant(false_tag) orelse
            self.registry.findByName("False") orelse 3;

        const true_i64 = c.LLVMConstInt(llvm.i64Type(), @bitCast(true_disc), 0);
        const false_i64 = c.LLVMConstInt(llvm.i64Type(), @bitCast(false_disc), 0);
        const tag = c.LLVMBuildSelect(self.builder, cmp_i1, true_i64, false_i64, "bool_tag");

        // Bool is nullary — encode as a tagged immediate, no allocation.
        return tagImmediateCon(self.builder, tag);
    }

    /// Translate a GRIN string literal to an LLVM global string pointer.
    /// Used by emitLibcCall for primops that expect C strings.
    fn translateStringLitToPtr(self: *GrinTranslator, s: []const u8) TranslationError!llvm.Value {
        const s_z = self.allocator.dupeZ(u8, s) catch return error.OutOfMemory;
        defer self.allocator.free(s_z);
        return c.LLVMBuildGlobalStringPtr(self.builder, s_z.ptr, ".str") orelse
            return error.OutOfMemory;
    }

    fn translateValToLlvm(self: *GrinTranslator, val: grin.Val) TranslationError!llvm.Value {
        return switch (val) {
            .Lit => |lit| switch (lit) {
                .String => |s| blk: {
                    // Convert string literal to [Char] heap list at runtime.
                    // This ensures strings are always represented as proper Haskell
                    // lists, making pattern matching (e.g., in ++) work correctly.
                    // Primop boundaries use translateStringLitToPtr for C string access.
                    const str_ptr = try self.translateStringLitToPtr(s);
                    break :blk self.emitCstringToCharlist(str_ptr);
                },
                .Int => |i| c.LLVMConstInt(llvm.i64Type(), @bitCast(@as(i64, i)), 1),
                .Float => |f| c.LLVMConstReal(c.LLVMDoubleType(), f),
                .Bool => |b| c.LLVMConstInt(c.LLVMInt1Type(), @intFromBool(b), 0),
                .Char => |ch| c.LLVMConstInt(llvm.i64Type(), ch, 0),
            },
            .Unit => c.LLVMGetUndef(llvm.i32Type()),
            .Var => |name| blk: {
                // 1. Check params (function parameters and let-bound variables),
                //    keyed by unique ID to distinguish variables with the same base.
                if (self.params.get(name.unique.value)) |v| break :blk v;
                // 2. Nullary constructor: emit its tag discriminant as an i64.
                //    Tracked in: https://github.com/adinapoli/rusholme/issues/410
                // 2. Check if variable is a known Prelude constant.
                //    Unit is special: always returns a heap node so the REPL can
                //    distinguish "no value" from integer 0.
                if (name.unique.value == known.unit_val) {
                    break :blk self.buildUnitNode();
                }

                // 2b. If not a known literal, check tag discriminant for nullary constructors.
                //    Allocate a heap node so that the REPL and case analysis can
                //    distinguish constructors from integer literals by type (ptr vs i64).
                //    Tracked in: https://github.com/adinapoli/rusholme/issues/410
                if (self.registry.discriminantByName(name)) |disc| {
                    const alloc_fn = declareRtsAlloc(self.module);
                    var alloc_args2 = [_]llvm.Value{
                        c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0),
                        c.LLVMConstInt(llvm.i32Type(), 0, 0),
                    };
                    break :blk c.LLVMBuildCall2(
                        self.builder,
                        llvm.getFunctionType(alloc_fn),
                        alloc_fn,
                        &alloc_args2,
                        2,
                        "nullary_node",
                    );
                }
                // 3. Top-level function reference: look up the LLVM function by
                //    full name (base + unique suffix) and return its pointer (for
                //    higher-order use).
                //    This handles passing named functions as arguments, e.g.:
                //      map_it identity xs  =>  identity becomes a global function ptr.
                const fn_name_z = self.formatName(name);

                // Look up arity to decide whether this is a CAF (arity 0)
                // or a higher-order function reference.
                const arity = if (self.arity_map) |map| map.get(name.unique.value) orelse 0 else 0;

                const fn_val = if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |fv|
                    fv
                else blk2: {
                    // Cross-module function reference: forward-declare as
                    // external so the ORC linker can resolve it from a
                    // previously-loaded module. This mirrors the pattern
                    // used by translateApp for unknown function calls.
                    var param_types: [8]llvm.Type = undefined;
                    for (0..arity) |i| param_types[i] = ptrType();
                    const ext_fn_type = llvm.functionType(ptrType(), param_types[0..arity], false);
                    break :blk2 llvm.addFunction(self.module, fn_name_z, ext_fn_type);
                };

                // Zero-arity CAFs (e.g. dictionary bindings like
                // dict$Show$Int) must be CALLED to produce their value,
                // every time they are referenced.
                // Higher-arity functions are returned as function pointers
                // for higher-order use (e.g. `map f xs`).
                if (arity == 0) {
                    var caf_param_types: [0]llvm.Type = undefined;
                    const caf_fn_type = llvm.functionType(ptrType(), &caf_param_types, false);
                    break :blk c.LLVMBuildCall2(
                        self.builder,
                        caf_fn_type,
                        fn_val,
                        null,
                        0,
                        "caf_val",
                    );
                }
                break :blk fn_val;
            },
            .ConstTagNode => |ctn| blk: {
                // Allocate a heap node and return the pointer.
                break :blk try self.translateStoreToValue(.{ .ConstTagNode = ctn }, "node") orelse
                    return error.UnsupportedGrinVal;
            },
            .VarTagNode => {
                // VarTagNode with truly dynamic tags (e.g., generic eval/apply).
                // Not needed for partial applications — those use ConstTagNode
                // with Partial tags (issue #583).
                // tracked in: https://github.com/adinapoli/rusholme/issues/410
                return error.UnsupportedGrinVal;
            },
            .ValTag => |t| blk: {
                const disc = self.registry.discriminant(t) orelse return error.UnsupportedGrinVal;
                const disc_val = c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                // Nullary constructors are tagged immediates — no heap node.
                // F-tags still need a heap slot for the Ind update (#605).
                if (t.tag_type == .Con) {
                    break :blk tagImmediateCon(self.builder, disc_val);
                }
                const alloc_fn = declareRtsAlloc(self.module);
                var alloc_args2 = [_]llvm.Value{
                    disc_val,
                    c.LLVMConstInt(llvm.i32Type(), 0, 0),
                };
                break :blk c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(alloc_fn),
                    alloc_fn,
                    &alloc_args2,
                    2,
                    "valtag_node",
                );
            },
        };
    }

    /// Allocate a heap node for a `Val` and return the pointer.
    /// This is the value-returning variant of `translateStore`.
    fn translateStoreToValue(self: *GrinTranslator, val: grin.Val, result_name: []const u8) TranslationError!?llvm.Value {
        switch (val) {
            .ConstTagNode => |ctn| {
                const tag = ctn.tag;
                var n_fields: u32 = @intCast(ctn.fields.len);
                const disc = self.registry.discriminant(tag) orelse return error.UnsupportedGrinVal;

                // Ensure F-tag thunks always have ≥1 field so the eval loop can
                // write an indirection update (tag=Ind, field[0]=result) after
                // forcing. Without this, 0-field thunks violate call-by-need
                // semantics because they get re-evaluated on every access.
                //
                // This invariant is also relied upon by:
                //   - translateCase: unconditional Ind update (line ~2053)
                //   - translateCaseToValue: unconditional Ind update (line ~2411)
                //   - emitInlineEval (__rhc_force): unconditional Ind update
                //   - translateUpdate: unconditional field[0] write
                // Unit-tested by `rts/node.zig` test
                // "0-field F-tag thunk: padded slot supports Ind update".
                // See: https://github.com/adinapoli/rusholme/issues/605
                // and: https://github.com/adinapoli/rusholme/issues/711
                if (tag.tag_type == .Fun and n_fields == 0) {
                    n_fields = 1;
                }

                // Nullary constructors need no heap node at all — they are
                // tagged immediates (see tagImmediateCon).
                if (tag.tag_type == .Con and n_fields == 0) {
                    const disc_val = c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                    return tagImmediateCon(self.builder, disc_val);
                }

                // Allocate a node via the inline-alloc fast path (#798),
                // falling back to `rts_alloc` for oversized / dynamic
                // shapes.
                const node_ptr = self.emitAllocConst(disc, n_fields, result_name);

                // Write each field via rts_store_field(node, index, value_as_u64).
                // Pointer values are cast to i64 via ptrtoint; integer values are
                // already i64.  No boxing via alloca is needed — the RTS field
                // slots are plain u64.
                //
                // Nullary constructors (ValTag) are already heap-allocated nodes
                // from translateValToLlvm, so they flow through the pointer path.
                const rts_store_fn = declareRtsStoreField(self.module);
                for (ctn.fields, 0..) |field, fi| {
                    const raw_val: llvm.Value = try self.translateValToLlvm(field);

                    const field_ty = c.LLVMTypeOf(raw_val);
                    const kind = c.LLVMGetTypeKind(field_ty);
                    const is_ptr = kind == c.LLVMPointerTypeKind;
                    // Convert to u64 for storage.  Pointers are stored via
                    // ptrtoint.  Raw integers are tagged ((n<<1)|1) so that
                    // when loaded back (inttoptr), __rhc_force can distinguish
                    // them from heap pointers by bit 0.
                    const as_u64: llvm.Value = if (is_ptr)
                        c.LLVMBuildPtrToInt(self.builder, raw_val, llvm.i64Type(), "field_u64")
                    else blk: {
                        const tagged = tagInt(self.builder, raw_val);
                        break :blk c.LLVMBuildPtrToInt(self.builder, tagged, llvm.i64Type(), "field_tagged");
                    };
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
            .Unit => {
                // Allocate a 1-field Unit heap cell that the GRIN `Rec`-let
                // lowering will subsequently mutate via `update` (i.e.
                // `rts_store_field(p, 0, …)`).  A 0-field cell would trip
                // the `index < n_fields` assertion in `rts_store_field`
                // (see src/rts/node.zig:~272).
                //
                // This is the placeholder allocation in the multi-binding
                // `Rec` backpatch chain; the single-binding `NonRec` path
                // never reaches this arm because the desugarer dodges it
                // via the NonRec workaround.
                // See: https://github.com/adinapoli/rusholme/issues/747
                const unit_tag: i64 = @intFromEnum(rts_node.Tag.Unit);
                const unit_ptr = self.emitAllocConst(unit_tag, 1, result_name);
                return @as(?llvm.Value, unit_ptr);
            },
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
    /// Emit the tag dispatch for a WHNF scrutinee: a low-bit guard routes
    /// tagged immediates (raw Ints/Chars and nullary constructors) straight
    /// to the case dispatch with their untagged payload as the "tag", while
    /// heap nodes go through a header tag load.
    ///
    /// The scrutinee must already be in WHNF — pre-forced via `__rhc_force`,
    /// which follows indirections, forces F-tag thunks, and calls saturated
    /// partial applications. This replaces the per-case-site inline eval
    /// loop, which duplicated the entire F/P-tag switch table at every case
    /// expression (a major code-size and branch-prediction cost).
    ///
    /// Returns the i64 tag value to switch on. The builder is left in the
    /// dispatch block.
    fn emitWhnfTagDispatch(self: *GrinTranslator, scrut: llvm.Value) llvm.Value {
        const i64_ty = llvm.i64Type();
        const guard_bb = c.LLVMGetInsertBlock(self.builder);
        const tagload_bb = c.LLVMAppendBasicBlock(self.current_func, "case.tagload");
        const dispatch_bb = c.LLVMAppendBasicBlock(self.current_func, "case.dispatch");

        const raw = c.LLVMBuildPtrToInt(self.builder, scrut, i64_ty, "scrut.int");
        const untagged = c.LLVMBuildAShr(self.builder, raw, c.LLVMConstInt(i64_ty, 1, 0), "scrut.untagged");
        const low_bit = c.LLVMBuildAnd(self.builder, raw, c.LLVMConstInt(i64_ty, 1, 0), "scrut.low_bit");
        const is_heap = c.LLVMBuildICmp(self.builder, c.LLVMIntEQ, low_bit, c.LLVMConstInt(i64_ty, 0, 0), "scrut.is_heap");
        const is_nonnull = c.LLVMBuildICmp(self.builder, c.LLVMIntNE, raw, c.LLVMConstInt(i64_ty, 0, 0), "scrut.nonnull");
        const is_valid = c.LLVMBuildAnd(self.builder, is_heap, is_nonnull, "scrut.valid_heap");
        _ = c.LLVMBuildCondBr(self.builder, is_valid, tagload_bb, dispatch_bb);

        llvm.positionBuilderAtEnd(self.builder, tagload_bb);
        const header_ty = nodeHeaderType();
        var tag_idx = [_]llvm.Value{
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, scrut, &tag_idx, 2, "scrut.tag_gep");
        const tag_val = c.LLVMBuildLoad2(self.builder, i64_ty, tag_gep, "scrut.tag");
        _ = c.LLVMBuildBr(self.builder, dispatch_bb);

        llvm.positionBuilderAtEnd(self.builder, dispatch_bb);
        const tag_phi = c.LLVMBuildPhi(self.builder, i64_ty, "dispatch.tag");
        var phi_vals = [_]llvm.Value{ untagged, tag_val };
        var phi_bbs = [_]llvm.BasicBlock{ guard_bb, tagload_bb };
        c.LLVMAddIncoming(tag_phi, @ptrCast(&phi_vals), @ptrCast(&phi_bbs), 2);
        return tag_phi;
    }

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

        // ── 1b. Pre-force via __rhc_force ────────────────────────────────
        //
        // In REPL mode, per-def modules' inline eval loops only know about
        // F-tags that existed at Prelude compile time.  Expressions can
        // introduce new F-tags (e.g., `< 5 10` becomes an F-tagged thunk).
        // To handle this, pre-force the scrutinee via the shared external
        // `__rhc_force` which is re-emitted whenever new F-tags appear.
        //
        // After pre-forcing, the inline eval loop below is still needed for
        // non-REPL (whole-program) compilation where `__rhc_force` may not
        // exist, and for indirection following.
        // Elide the force entirely when the scrutinee is statically WHNF
        // (primop result, fresh constructor node, tagged immediate) — #800.
        const scrut_is_whnf = self.valYieldsWhnf(scrutinee);
        const pre_forced = if (is_ptr and !scrut_is_whnf)
            self.callForceIfNeeded(scrut_llvm)
        else
            scrut_llvm;

        // ── 1c. Tag dispatch ───────────────────────────────────────────────
        //
        // `pre_forced` is in WHNF: `__rhc_force` follows indirections,
        // forces F-tag thunks, and calls saturated partial applications.
        // All that remains is routing tagged immediates vs heap nodes to
        // the alternatives switch (emitWhnfTagDispatch). The former
        // per-case-site inline eval loop is gone — see #800.

        // The "current scrutinee" used by the rest of the function.
        const cur_scrut: llvm.Value = pre_forced;
        var cur_tag: llvm.Value = undefined;

        if (is_ptr) {
            cur_tag = self.emitWhnfTagDispatch(pre_forced);
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
                    const disc = self.registry.discriminant(np.tag) orelse return error.UnsupportedGrinVal;
                    const case_val = c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                    c.LLVMAddCase(switch_inst, case_val, alt_bbs[i]);
                },
                .TagPat => |t| {
                    const disc = self.registry.discriminant(t) orelse return error.UnsupportedGrinVal;
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
                        .fn_ptr => c.LLVMBuildIntToPtr(self.builder, loaded_i64, ptrType(), "as_fn_ptr"),
                    };

                    try self.bindAndRoot(field_name.unique.value, final_val);

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

    /// Translate a case expression in value-producing mode (for bind contexts).
    /// Returns an LLVM value (typically a phi node) representing the case result.
    /// Each alternative produces a value and branches to the merge block instead
    /// of returning directly.
    fn translateCaseToValue(
        self: *GrinTranslator,
        scrutinee: grin.Val,
        alts: []const grin.Alt,
        result_name: []const u8,
    ) TranslationError!?llvm.Value {
        if (alts.len == 0) return null;

        // ── 1. Obtain scrutinee and force to WHNF (same as translateCase) ──
        const scrut_llvm = try self.translateValToLlvm(scrutinee);
        if (@intFromPtr(scrut_llvm) == 0) return null;
        const scrut_ty = c.LLVMTypeOf(scrut_llvm);
        const scrut_kind = c.LLVMGetTypeKind(scrut_ty);
        const is_ptr = scrut_kind == c.LLVMPointerTypeKind;

        // ── 1b. Pre-force via __rhc_force ────────────────────────────────
        // Same as translateCase: in REPL mode, per-def modules' inline eval
        // loops only know about F-tags from Prelude compile time. Pre-force
        // via the shared external __rhc_force which knows all F-tags.
        // Elide the force entirely when the scrutinee is statically WHNF
        // (primop result, fresh constructor node, tagged immediate) — #800.
        const scrut_is_whnf = self.valYieldsWhnf(scrutinee);
        const pre_forced = if (is_ptr and !scrut_is_whnf)
            self.callForceIfNeeded(scrut_llvm)
        else
            scrut_llvm;

        // ── 1c. Tag dispatch (same as translateCase) ───────────────────────
        // `pre_forced` is WHNF; route immediates vs heap nodes (#800).
        const cur_scrut: llvm.Value = pre_forced;
        var cur_tag: llvm.Value = undefined;

        if (is_ptr) {
            cur_tag = self.emitWhnfTagDispatch(pre_forced);
        } else {
            cur_tag = scrut_llvm;
        }

        // ── 2. Build basic blocks ──────────────────────────────────────────
        const merge_bb = c.LLVMAppendBasicBlock(self.current_func, "case.merge");
        const unreachable_bb = c.LLVMAppendBasicBlock(self.current_func, "case.unreachable");

        var default_bb: llvm.BasicBlock = null;
        var alt_bbs = self.allocator.alloc(llvm.BasicBlock, alts.len) catch return error.OutOfMemory;
        defer self.allocator.free(alt_bbs);

        for (alts, 0..) |*alt, i| {
            switch (alt.pat) {
                .DefaultPat => {
                    default_bb = c.LLVMAppendBasicBlock(self.current_func, "case.default");
                    alt_bbs[i] = default_bb;
                },
                else => {
                    var name_buf: [32]u8 = undefined;
                    const bb_name = std.fmt.bufPrintZ(&name_buf, "case.alt{d}", .{i}) catch "case.alt";
                    alt_bbs[i] = c.LLVMAppendBasicBlock(self.current_func, bb_name.ptr);
                },
            }
        }

        // Non-exhaustive match — default case is unreachable in well-typed programs
        if (default_bb == null) default_bb = unreachable_bb;

        // ── 3. Emit switch ──────────────────────────────────────────────────
        var n_cases: u32 = 0;
        for (alts) |alt| {
            if (alt.pat != .DefaultPat) n_cases += 1;
        }
        const switch_inst = c.LLVMBuildSwitch(self.builder, cur_tag, default_bb, n_cases);

        for (alts, 0..) |alt, i| {
            switch (alt.pat) {
                .DefaultPat => {},
                .NodePat => |np| {
                    const disc = self.registry.discriminant(np.tag) orelse return error.UnsupportedGrinVal;
                    const case_val = c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
                    c.LLVMAddCase(switch_inst, case_val, alt_bbs[i]);
                },
                .TagPat => |t| {
                    const disc = self.registry.discriminant(t) orelse return error.UnsupportedGrinVal;
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

        // ── 4. Emit alternatives and collect values for phi ────────────────
        var phi_values = std.ArrayListUnmanaged(llvm.Value).empty;
        defer phi_values.deinit(self.allocator);
        var phi_blocks = std.ArrayListUnmanaged(llvm.BasicBlock).empty;
        defer phi_blocks.deinit(self.allocator);

        for (alts, 0..) |alt, i| {
            llvm.positionBuilderAtEnd(self.builder, alt_bbs[i]);

            // Handle NodePat field binding (same as translateCase)
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

                    const field_type = self.type_env.getFieldTagType(np.tag, @intCast(fi));
                    const final_val: llvm.Value = switch (field_type) {
                        .i64 => loaded_i64,
                        .f64 => c.LLVMBuildBitCast(self.builder, loaded_i64, c.LLVMDoubleType(), "as_f64"),
                        .ptr => c.LLVMBuildIntToPtr(self.builder, loaded_i64, ptrType(), "as_ptr"),
                        .fn_ptr => c.LLVMBuildIntToPtr(self.builder, loaded_i64, ptrType(), "as_fn_ptr"),
                    };

                    try self.bindAndRoot(field_name.unique.value, final_val);
                    try self.type_env.setVarType(self.allocator, field_name, field_type);
                }
            }

            // Translate the alternative body as a value (not with ret)
            const alt_value = try self.translateExprToValue(alt.body, result_name);

            // Every alternative must produce a value in bind context
            if (alt_value) |val| {
                // Normalize value type: box i64 nullary constructors into heap nodes
                // so all phi incoming values have the same type (ptr).
                // This handles cases where different alternatives return nullary
                // constructors (i64 discriminants) vs heap-allocated nodes (ptr).
                const val_ty = c.LLVMTypeOf(val);
                const val_kind = c.LLVMGetTypeKind(val_ty);
                const is_i64 = val_kind == c.LLVMIntegerTypeKind and c.LLVMGetIntTypeWidth(val_ty) == 64;
                const normalized_val: llvm.Value = if (is_i64)
                    tagInt(self.builder, val)
                else
                    val;

                try phi_values.append(self.allocator, normalized_val);
                const cur_bb = c.LLVMGetInsertBlock(self.builder);
                try phi_blocks.append(self.allocator, cur_bb);
                _ = c.LLVMBuildBr(self.builder, merge_bb);
            } else {
                // Alternative didn't produce a value - this shouldn't happen in bind context
                return error.UnsupportedGrinVal;
            }
        }

        // ── 5. Create phi node in merge block ──────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, merge_bb);

        if (phi_values.items.len == 0) return null;

        // All values have been normalized to ptr type, so phi is always ptr
        const phi = c.LLVMBuildPhi(self.builder, ptrType(), nullTerminate(result_name).ptr);

        c.LLVMAddIncoming(
            phi,
            @ptrCast(phi_values.items.ptr),
            @ptrCast(phi_blocks.items.ptr),
            @intCast(phi_values.items.len),
        );

        // ── 6. Emit unreachable in default block (for non-exhaustive matches) ──
        llvm.positionBuilderAtEnd(self.builder, unreachable_bb);
        _ = c.LLVMBuildUnreachable(self.builder);

        // Reposition at merge for continuation
        llvm.positionBuilderAtEnd(self.builder, merge_bb);

        return phi;
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
        else blk: {
            const tagged = tagInt(self.builder, v_val);
            break :blk c.LLVMBuildPtrToInt(self.builder, tagged, llvm.i64Type(), "upd.v_tagged");
        };
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
                        const forced = if (self.registry.fun_tags.count() > 0)
                            try self.forceValueToWhnf(llvm_val)
                        else
                            llvm_val;
                        const converted = c.LLVMBuildPtrToInt(self.builder, forced, llvm.i64Type(), "ptr_to_i64");
                        self.buildRetWithShadowRestore(converted);
                        return;
                    } else if (is_int) {
                        const val_width = c.LLVMGetIntTypeWidth(val_ty);
                        if (val_width == 32) {
                            const widened = c.LLVMBuildZExt(self.builder, llvm_val, llvm.i64Type(), "i32_to_i64");
                            const tagged = tagInt(self.builder, widened);
                            const as_i64 = c.LLVMBuildPtrToInt(self.builder, tagged, llvm.i64Type(), "tagged_i64");
                            self.buildRetWithShadowRestore(as_i64);
                            return;
                        }
                        // Tag the integer so that `formatJitResult` can
                        // distinguish integer 0 from Unit (a heap pointer
                        // with tag rts_node.Tag.Unit).  Without this, both
                        // `0` and `()` produce a raw 0 at the i64 boundary,
                        // causing `0` to be suppressed in the REPL output.
                        // tagInt encodes the value as `(val << 1) | 1`.
                        // See: https://github.com/adinapoli/rusholme/issues/621
                        const tagged = tagInt(self.builder, llvm_val);
                        const as_i64 = c.LLVMBuildPtrToInt(self.builder, tagged, llvm.i64Type(), "tagged_i64");
                        self.buildRetWithShadowRestore(as_i64);
                        return;
                    }
                } else if (!is_native_main) {
                    // Non-main, non-REPL functions return ptr.
                    // Force any F-tagged thunks to WHNF before returning
                    // so that callers always receive evaluated values.
                    // (This return-site force is the convention that makes
                    // every direct call result WHNF — see exprYieldsWhnf.)
                    // Skip it when the value is statically WHNF already.
                    if (is_ptr) {
                        const forced = if (self.valYieldsWhnf(val))
                            llvm_val
                        else
                            self.callForceIfNeeded(llvm_val);
                        self.buildRetWithShadowRestore(forced);
                        return;
                    }
                    // Main returns i32 so no conversion needed — it falls
                    // through to the default buildRet below.
                    if (is_int) {
                        // Integer values (e.g. primop results) need inttoptr
                        // to match the ptr return type of non-entry functions.
                        const converted = tagInt(self.builder, llvm_val);
                        self.buildRetWithShadowRestore(converted);
                        return;
                    }
                }
                // Native main: fall through to default buildRet (returns i32 as-is).
            }
        }

        self.buildRetWithShadowRestore(llvm_val);
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
        const low_bit = c.LLVMBuildAnd(self.builder, ptr_as_int, c.LLVMConstInt(i64_ty, 1, 0), "low_bit");
        const is_heap_ptr = c.LLVMBuildICmp(self.builder, c.LLVMIntEQ, low_bit, c.LLVMConstInt(i64_ty, 0, 0), "is_heap");
        const is_nonnull = c.LLVMBuildICmp(self.builder, c.LLVMIntNE, ptr_as_int, c.LLVMConstInt(i64_ty, 0, 0), "nonnull");
        const is_valid_heap = c.LLVMBuildAnd(self.builder, is_heap_ptr, is_nonnull, "valid_heap");
        _ = c.LLVMBuildCondBr(self.builder, is_valid_heap, check_bb, done_bb);

        // ── check: tag load + switch ───────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, check_bb);
        var tag_idx = [_]llvm.Value{
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "tag_gep");
        const tag_val = c.LLVMBuildLoad2(self.builder, i64_ty, tag_gep, "tag");

        const n_cases = @as(u32, @intCast(self.registry.fun_tags.count() + self.registry.partial_tags.count())) + 1;
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
        var phi_vals = std.ArrayListUnmanaged(llvm.Value).empty;
        defer phi_vals.deinit(self.allocator);
        var phi_bbs = std.ArrayListUnmanaged(llvm.BasicBlock).empty;
        defer phi_bbs.deinit(self.allocator);

        phi_vals.append(self.allocator, param) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, entry_bb) catch return error.OutOfMemory;
        phi_vals.append(self.allocator, ind_target) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, ind_bb) catch return error.OutOfMemory;

        // ── F-tag cases: force thunk ───────────────────────────────────
        var ftag_iter = self.registry.fun_tags.iterator();
        while (ftag_iter.next()) |ftag_entry| {
            const ftag_unique = ftag_entry.key_ptr.*;
            const ftag_disc = self.registry.discriminants.get(ftag_unique) orelse continue;
            const ftag_name = self.registry.fun_tag_names.get(ftag_unique) orelse continue;
            const ftag_n_fields = self.registry.field_counts.get(ftag_unique) orelse 0;

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

        // ── P-tag cases: call saturated partial applications ───────────
        // Mirrors the P-tag arm the per-case-site inline eval loops used
        // to emit (now that case sites rely solely on __rhc_force, the
        // P(0) forcing must live here). A P(0) node stores all the
        // function's arguments; load them and call directly.
        //
        // Only saturated (missing == 0) closures are callable. An
        // under-saturated partial application is already WHNF — it falls
        // through the switch default to `done` and is returned as-is.
        var ptag_iter = self.registry.partial_tags.iterator();
        while (ptag_iter.next()) |ptag_entry| {
            const ptag_unique = ptag_entry.key_ptr.*;
            const ptag_disc = self.registry.discriminants.get(ptag_unique) orelse continue;
            const ptag_info = self.registry.partial_tag_info.get(ptag_unique) orelse continue;
            if (ptag_info.missing != 0) continue;

            const ptag_bb = c.LLVMAppendBasicBlock(func, "ptag");
            c.LLVMAddCase(sw, c.LLVMConstInt(i64_ty, @bitCast(ptag_disc), 0), ptag_bb);

            llvm.positionBuilderAtEnd(self.builder, ptag_bb);

            const fn_name_z = self.formatName(ptag_info.name);
            const n_fields = ptag_info.n_fields;
            var call_args: [8]llvm.Value = undefined;
            const n_args = @min(n_fields, 8);
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
                    "pap_arg",
                );
                call_args[fi] = c.LLVMBuildIntToPtr(self.builder, loaded, ptr_ty, "pap_ptr");
            }

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
                "pap_result",
            );

            _ = c.LLVMBuildBr(self.builder, eval_bb);

            phi_vals.append(self.allocator, result) catch return error.OutOfMemory;
            phi_bbs.append(self.allocator, ptag_bb) catch return error.OutOfMemory;
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
        self.buildRetWithShadowRestore(phi);
    }

    /// Emit a call to `__rhc_force` if the module contains F-tags.
    /// Returns the forced pointer value, or the original value unchanged
    /// if no F-tags exist (i.e. `__rhc_force` was never emitted).
    /// Force a translated operand unless its GRIN value is statically
    /// WHNF (strict-forced parameter, primop result, immediate).
    fn forceOperandIfNeeded(self: *GrinTranslator, raw: llvm.Value, val: grin.Val) llvm.Value {
        if (self.valYieldsWhnf(val)) return raw;
        return self.callForceIfNeeded(raw);
    }

    fn callForceIfNeeded(self: *GrinTranslator, val: llvm.Value) llvm.Value {
        if (self.registry.fun_tags.count() == 0 and self.registry.partial_tags.count() == 0) return val;
        if (c.LLVMGetNamedFunction(self.module, "__rhc_force") == null) return val;
        const guard = self.getOrDefineForceFastGuard();
        var args = [_]llvm.Value{val};
        return c.LLVMBuildCall2(
            self.builder,
            llvm.getFunctionType(guard),
            guard,
            &args,
            1,
            "forced",
        );
    }

    /// Get-or-define the module-internal `__rhc_force_fast(ptr) -> ptr`:
    /// an always-inline guard that returns tagged immediates (and null)
    /// without a call, and defers heap pointers to the full `__rhc_force`.
    /// After LLVM inlining, forcing a value that is statically a tagged
    /// immediate folds away entirely, and runtime forces of immediates
    /// cost two bit tests instead of a function call.
    fn getOrDefineForceFastGuard(self: *GrinTranslator) llvm.Value {
        const name = "__rhc_force_fast";
        if (c.LLVMGetNamedFunction(self.module, name)) |existing| return existing;

        const ptr_ty = ptrType();
        const i64_ty = llvm.i64Type();
        var param_types = [_]llvm.Type{ptr_ty};
        const fn_ty = llvm.functionType(ptr_ty, &param_types, false);
        const func = llvm.addFunction(self.module, name, fn_ty);
        c.LLVMSetLinkage(func, c.LLVMInternalLinkage);
        const ctx = c.LLVMGetModuleContext(self.module);
        const kind_id = c.LLVMGetEnumAttributeKindForName("alwaysinline", "alwaysinline".len);
        const attr = c.LLVMCreateEnumAttribute(ctx, kind_id, 0);
        const fn_index: c_uint = @bitCast(@as(c_int, c.LLVMAttributeFunctionIndex));
        c.LLVMAddAttributeAtIndex(func, fn_index, attr);

        const saved_bb = c.LLVMGetInsertBlock(self.builder);
        defer if (saved_bb != null) llvm.positionBuilderAtEnd(self.builder, saved_bb);

        const entry_bb = llvm.appendBasicBlock(func, "entry");
        const slow_bb = c.LLVMAppendBasicBlock(func, "slow");
        const done_bb = c.LLVMAppendBasicBlock(func, "done");
        llvm.positionBuilderAtEnd(self.builder, entry_bb);
        const param = c.LLVMGetParam(func, 0);
        const raw = c.LLVMBuildPtrToInt(self.builder, param, i64_ty, "raw");
        const low = c.LLVMBuildAnd(self.builder, raw, c.LLVMConstInt(i64_ty, 1, 0), "low");
        const is_imm = c.LLVMBuildICmp(self.builder, c.LLVMIntNE, low, c.LLVMConstInt(i64_ty, 0, 0), "is_imm");
        const is_null = c.LLVMBuildICmp(self.builder, c.LLVMIntEQ, raw, c.LLVMConstInt(i64_ty, 0, 0), "is_null");
        const skip = c.LLVMBuildOr(self.builder, is_imm, is_null, "skip");
        _ = c.LLVMBuildCondBr(self.builder, skip, done_bb, slow_bb);

        llvm.positionBuilderAtEnd(self.builder, slow_bb);
        const heavy = c.LLVMGetNamedFunction(self.module, "__rhc_force").?;
        var slow_args = [_]llvm.Value{param};
        const forced = c.LLVMBuildCall2(self.builder, llvm.getFunctionType(heavy), heavy, &slow_args, 1, "forced.slow");
        _ = c.LLVMBuildRet(self.builder, forced);

        llvm.positionBuilderAtEnd(self.builder, done_bb);
        _ = c.LLVMBuildRet(self.builder, param);

        return func;
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
        const low_bit = c.LLVMBuildAnd(self.builder, ptr_as_int, c.LLVMConstInt(i64_ty, 1, 0), "force.low_bit");
        const is_heap = c.LLVMBuildICmp(self.builder, c.LLVMIntEQ, low_bit, c.LLVMConstInt(i64_ty, 0, 0), "force.is_heap");
        const is_nonnull = c.LLVMBuildICmp(self.builder, c.LLVMIntNE, ptr_as_int, c.LLVMConstInt(i64_ty, 0, 0), "force.nonnull");
        const is_valid_heap = c.LLVMBuildAnd(self.builder, is_heap, is_nonnull, "force.valid_heap");
        _ = c.LLVMBuildCondBr(self.builder, is_valid_heap, check_bb, done_bb);

        // ── check block: tag load + switch ─────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, check_bb);

        var tag_idx = [_]llvm.Value{
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
            c.LLVMConstInt(llvm.i32Type(), 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, phi, &tag_idx, 2, "force.tag_gep");
        const tag_val = c.LLVMBuildLoad2(self.builder, i64_ty, tag_gep, "force.tag");

        const n_cases = @as(u32, @intCast(self.registry.fun_tags.count())) + 1; // F-tags + Ind
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
        var phi_vals = std.ArrayListUnmanaged(llvm.Value).empty;
        defer phi_vals.deinit(self.allocator);
        var phi_bbs = std.ArrayListUnmanaged(llvm.BasicBlock).empty;
        defer phi_bbs.deinit(self.allocator);

        phi_vals.append(self.allocator, llvm_val) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, entry_bb) catch return error.OutOfMemory;
        phi_vals.append(self.allocator, ind_target) catch return error.OutOfMemory;
        phi_bbs.append(self.allocator, ind_bb) catch return error.OutOfMemory;

        // ── F-tag cases: force thunk ───────────────────────────────────
        var ftag_iter = self.registry.fun_tags.iterator();
        while (ftag_iter.next()) |ftag_entry| {
            const ftag_unique = ftag_entry.key_ptr.*;
            const ftag_disc = self.registry.discriminants.get(ftag_unique) orelse continue;
            const ftag_name = self.registry.fun_tag_names.get(ftag_unique) orelse continue;
            const ftag_n_fields = self.registry.field_counts.get(ftag_unique) orelse 0;

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

    // ── Apply function for partial applications ───────────────────────

    /// Emit `__rhc_apply(f_ptr, x_ptr) -> ptr` as a standalone LLVM
    /// function.  Dispatches on the tag of `f_ptr`:
    ///
    ///   P(n)func [a0..a_{k-1}]  with n > 1  →  allocate P(n-1)func [a0..a_{k-1}, x]
    ///   P(1)func [a0..a_{k-1}]               →  call func(a0..a_{k-1}, x)
    ///   anything else                        →  return f_ptr (no-op)
    fn emitApplyFunction(self: *GrinTranslator) TranslationError!void {
        const ptr_ty = ptrType();
        const i64_ty = llvm.i64Type();
        const i32_ty = llvm.i32Type();
        const header_ty = nodeHeaderType();
        const rts_load_fn = declareRtsLoadField(self.module);
        const rts_store_fn = declareRtsStoreField(self.module);
        const rts_alloc_fn = declareRtsAlloc(self.module);

        // fn __rhc_apply(ptr, ptr) -> ptr
        var param_types = [_]llvm.Type{ ptr_ty, ptr_ty };
        const fn_type = llvm.functionType(ptr_ty, &param_types, false);
        const func = llvm.addFunction(self.module, "__rhc_apply", fn_type);

        // Save and restore builder/function state.
        const saved_func = self.current_func;
        const saved_bb = c.LLVMGetInsertBlock(self.builder);
        defer {
            self.current_func = saved_func;
            if (saved_bb != null) llvm.positionBuilderAtEnd(self.builder, saved_bb);
        }
        self.current_func = func;

        const f_param = c.LLVMGetParam(func, 0);
        const x_param = c.LLVMGetParam(func, 1);
        const entry_bb = llvm.appendBasicBlock(func, "entry");
        const default_bb = c.LLVMAppendBasicBlock(func, "default");

        // ── entry: load tag and switch ─────────────────────────────────
        llvm.positionBuilderAtEnd(self.builder, entry_bb);
        var tag_idx = [_]llvm.Value{
            c.LLVMConstInt(i32_ty, 0, 0),
            c.LLVMConstInt(i32_ty, 0, 0),
        };
        const tag_gep = c.LLVMBuildGEP2(self.builder, header_ty, f_param, &tag_idx, 2, "tag_gep");
        const tag_val = c.LLVMBuildLoad2(self.builder, i64_ty, tag_gep, "tag");

        const n_cases: u32 = @intCast(self.registry.partial_tags.count());
        const sw = c.LLVMBuildSwitch(self.builder, tag_val, default_bb, n_cases);

        // ── default: not a partial application — call f_ptr as a direct
        // single-argument function pointer.  Dictionary fields for monomorphic
        // instances (e.g. Show Int) store plain LLVM function pointers; calling
        // them directly here handles the case where __rhc_apply is invoked on a
        // non-P-tagged value (e.g. a method extracted from a MkDict$Show node).
        llvm.positionBuilderAtEnd(self.builder, default_bb);
        var default_args = [_]llvm.Value{x_param};
        var default_param_types = [_]llvm.Type{ptr_ty};
        const default_fn_type = llvm.functionType(ptr_ty, &default_param_types, false);
        const default_result = c.LLVMBuildCall2(
            self.builder,
            default_fn_type,
            f_param,
            &default_args,
            1,
            "direct_call",
        );
        self.buildRetWithShadowRestore(default_result);

        // ── P-tag cases ────────────────────────────────────────────────
        var ptag_iter = self.registry.partial_tags.iterator();
        while (ptag_iter.next()) |ptag_entry| {
            const ptag_key = ptag_entry.key_ptr.*;
            const ptag_disc = self.registry.discriminants.get(ptag_key) orelse continue;
            const ptag_info = self.registry.partial_tag_info.get(ptag_key) orelse continue;

            const ptag_bb = c.LLVMAppendBasicBlock(func, "ptag");
            c.LLVMAddCase(sw, c.LLVMConstInt(i64_ty, @bitCast(ptag_disc), 0), ptag_bb);

            llvm.positionBuilderAtEnd(self.builder, ptag_bb);

            if (ptag_info.missing > 1) {
                // ── Still unsaturated: build P(n-1)func [old_fields..., x] ──
                const new_tag = grin.Tag{
                    .tag_type = .{ .Partial = ptag_info.missing - 1 },
                    .name = ptag_info.name,
                };
                const new_disc = self.registry.discriminant(new_tag) orelse
                    return error.UnsupportedGrinVal;
                const new_n_fields: u32 = ptag_info.n_fields + 1;

                var alloc_args = [_]llvm.Value{
                    c.LLVMConstInt(i64_ty, @bitCast(new_disc), 0),
                    c.LLVMConstInt(i32_ty, new_n_fields, 0),
                };
                const new_node = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(rts_alloc_fn),
                    rts_alloc_fn,
                    &alloc_args,
                    2,
                    "new_pap",
                );

                // Copy captured fields from the old node.
                for (0..ptag_info.n_fields) |fi| {
                    var load_args = [_]llvm.Value{
                        f_param,
                        c.LLVMConstInt(i32_ty, @intCast(fi), 0),
                    };
                    const loaded = c.LLVMBuildCall2(
                        self.builder,
                        llvm.getFunctionType(rts_load_fn),
                        rts_load_fn,
                        &load_args,
                        2,
                        "cap_arg",
                    );
                    var store_args = [_]llvm.Value{
                        new_node,
                        c.LLVMConstInt(i32_ty, @intCast(fi), 0),
                        loaded,
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

                // Store the new argument as the last field.
                const x_as_u64 = c.LLVMBuildPtrToInt(self.builder, x_param, i64_ty, "x_u64");
                var x_store_args = [_]llvm.Value{
                    new_node,
                    c.LLVMConstInt(i32_ty, ptag_info.n_fields, 0),
                    x_as_u64,
                };
                _ = c.LLVMBuildCall2(
                    self.builder,
                    llvm.getFunctionType(rts_store_fn),
                    rts_store_fn,
                    &x_store_args,
                    3,
                    "",
                );

                self.buildRetWithShadowRestore(new_node);
            } else {
                // ── Saturated (missing == 1): call func(captured_args..., x) ──
                const total_args = ptag_info.n_fields + 1; // captured + x

                // Load captured arguments.
                var call_args: [8]llvm.Value = undefined;
                const n_cap = @min(ptag_info.n_fields, 7); // leave room for x
                for (0..n_cap) |fi| {
                    var load_args = [_]llvm.Value{
                        f_param,
                        c.LLVMConstInt(i32_ty, @intCast(fi), 0),
                    };
                    const loaded = c.LLVMBuildCall2(
                        self.builder,
                        llvm.getFunctionType(rts_load_fn),
                        rts_load_fn,
                        &load_args,
                        2,
                        "sat_arg",
                    );
                    call_args[fi] = c.LLVMBuildIntToPtr(self.builder, loaded, ptr_ty, "sat_ptr");
                }
                call_args[n_cap] = x_param; // the new argument

                // Call the function.
                const fn_name_z = self.formatName(ptag_info.name);
                const n_call_args: u32 = @intCast(@min(total_args, 8));
                var fn_param_types: [8]llvm.Type = undefined;
                for (0..n_call_args) |pi| fn_param_types[pi] = ptr_ty;
                const callee_type = llvm.functionType(ptr_ty, fn_param_types[0..n_call_args], false);
                const callee = c.LLVMGetNamedFunction(self.module, fn_name_z) orelse
                    llvm.addFunction(self.module, fn_name_z, callee_type);
                const result = c.LLVMBuildCall2(
                    self.builder,
                    callee_type,
                    callee,
                    @ptrCast(&call_args),
                    n_call_args,
                    "sat_result",
                );
                self.buildRetWithShadowRestore(result);
            }
        }
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

test "PrimOpMapping: primPutStrLn maps to rts_putStrLn" {
    const result = PrimOpMapping.lookup(.{
        .base = "primPutStrLn",
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

test "PrimOpMapping: ccall rts_ symbols map directly (#536)" {
    // ccall names pass through desugar unchanged, so the mapping must
    // match the literal RTS symbol regardless of unique.
    const cases = [_]struct { sym: []const u8, param: ParamKind }{
        .{ .sym = "rts_putStrLn", .param = .ptr },
        .{ .sym = "rts_putStr", .param = .ptr },
        .{ .sym = "rts_putChar", .param = .i64 },
        .{ .sym = "rts_error", .param = .ptr },
    };
    for (cases) |case| {
        const result = PrimOpMapping.lookup(.{
            .base = case.sym,
            .unique = .{ .value = 4242 },
        });
        try std.testing.expect(result != null);
        try std.testing.expectEqualStrings(case.sym, std.mem.span(result.?.libcall.name));
        try std.testing.expectEqual(case.param, result.?.libcall.param_kinds[0]);
    }
}

test "PrimOpMapping: unknown function returns null" {
    const result = PrimOpMapping.lookup(.{
        .base = "myFunction",
        .unique = .{ .value = 0 },
    });
    try std.testing.expect(result == null);
}

test "PrimOpMapping: built-in putStrLn (unique < 1000) maps to rts_putStrLn" {
    const result = PrimOpMapping.lookup(.{
        .base = "putStrLn",
        .unique = .{ .value = 0 }, // Known.Fn.putStrLn
    });
    try std.testing.expect(result != null);
    try std.testing.expectEqualStrings("rts_putStrLn", std.mem.span(result.?.libcall.name));
}

test "PrimOpMapping: Prelude putStrLn (unique >= 1000) is NOT a primop" {
    const result = PrimOpMapping.lookup(.{
        .base = "putStrLn",
        .unique = .{ .value = 1033 }, // Prelude-renamed
    });
    try std.testing.expect(result == null);
}

test "PrimOpMapping: canonical putStrLn_ always maps regardless of unique" {
    const result = PrimOpMapping.lookup(.{
        .base = "putStrLn_",
        .unique = .{ .value = 9999 },
    });
    try std.testing.expect(result != null);
    try std.testing.expectEqualStrings("rts_putStrLn", std.mem.span(result.?.libcall.name));
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
    const program = grin.Program{
        .defs = &.{main_def},
        .field_types = .{},
        .arities = .{},
    };

    var registry = tag_registry_mod.TagRegistry.init();
    defer registry.deinit(alloc);
    var translator = GrinTranslator.init(alloc, &registry);
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

test "Partial application store emits rts_alloc with TagTable discriminant" {
    // Build a GRIN program with a partial application:
    //   double = store (P(1)add [42]) ; return ()
    // and verify the LLVM IR uses rts_alloc (not a magic constant).
    const alloc = std.testing.allocator;

    const add_name = grin.Name{ .base = "add", .unique = .{ .value = 10 } };
    const p1_tag = grin.Tag{ .tag_type = .{ .Partial = 1 }, .name = add_name };
    const lit_val = grin.Val{ .Lit = .{ .Int = 42 } };
    const unit_val = grin.Val{ .Unit = {} };

    var store_expr = grin.Expr{ .Store = .{
        .ConstTagNode = .{ .tag = p1_tag, .fields = &.{lit_val} },
    } };
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
    const program = grin.Program{
        .defs = &.{main_def},
        .field_types = .{},
        .arities = .{},
    };

    var registry = tag_registry_mod.TagRegistry.init();
    defer registry.deinit(alloc);
    var translator = GrinTranslator.init(alloc, &registry);
    defer translator.deinit();

    const ir_raw = try translator.translateProgram(program);
    const ir: [:0]u8 = ir_raw.ptr[0..ir_raw.len :0];
    defer alloc.free(ir);

    // Must call rts_alloc (P-tag node allocation).
    try std.testing.expect(std.mem.indexOf(u8, ir, "rts_alloc") != null);
    // Must NOT contain the old magic P-tag constant (0x500...).
    try std.testing.expect(std.mem.indexOf(u8, ir, "5629499534213120") == null); // 0x500 << 48
}

test "Partial application emits __rhc_apply when P-tags exist" {
    // Build a GRIN program with a P-tag to verify __rhc_apply is emitted.
    const alloc = std.testing.allocator;

    const add_name = grin.Name{ .base = "add", .unique = .{ .value = 10 } };
    const p1_tag = grin.Tag{ .tag_type = .{ .Partial = 1 }, .name = add_name };
    const lit_val = grin.Val{ .Lit = .{ .Int = 42 } };
    const unit_val = grin.Val{ .Unit = {} };

    var store_expr = grin.Expr{ .Store = .{
        .ConstTagNode = .{ .tag = p1_tag, .fields = &.{lit_val} },
    } };
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
    const program = grin.Program{
        .defs = &.{main_def},
        .field_types = .{},
        .arities = .{},
    };

    var registry = tag_registry_mod.TagRegistry.init();
    defer registry.deinit(alloc);
    var translator = GrinTranslator.init(alloc, &registry);
    defer translator.deinit();

    const ir_raw = try translator.translateProgram(program);
    const ir: [:0]u8 = ir_raw.ptr[0..ir_raw.len :0];
    defer alloc.free(ir);

    // __rhc_apply should be emitted since P-tags exist.
    try std.testing.expect(std.mem.indexOf(u8, ir, "__rhc_apply") != null);
}
