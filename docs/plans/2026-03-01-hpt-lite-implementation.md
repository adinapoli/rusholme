# HPT-Lite Type Propagation Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Implement lightweight type propagation ("HPT-lite") to fix LLVM codegen type mismatches causing runtime segfaults.

**Architecture:** Extend TagTable with field type information during Core→GRIN translation, then add a TypeEnv pass that propagates types through GRIN variables. The LLVM backend queries TypeEnv to emit correct IR types.

**Tech Stack:** Zig, existing GRIN AST, LLVM-C API

---

## Task 1: Add FieldType Enum to GRIN AST

**Files:**
- Modify: `src/grin/ast.zig:68-75` (after `SimpleType` enum)

**Step 1: Write the failing test**

Add to `src/grin/ast.zig` after the existing tests:

```zig
test "FieldType: all variants" {
    try testing.expectEqual(@as(usize, 3), @as(usize, @typeInfo(FieldType).@"enum".fields.len));
    try testing.expectEqualStrings("i64", @tagName(FieldType.i64));
    try testing.expectEqualStrings("f64", @tagName(FieldType.f64));
    try testing.expectEqualStrings("ptr", @tagName(FieldType.ptr));
}
```

**Step 2: Run test to verify it fails**

Run: `zig build test -- --test-filter "FieldType: all variants"`
Expected: FAIL with "FieldType not found"

**Step 3: Write minimal implementation**

Add to `src/grin/ast.zig` after `SimpleType` enum (around line 68):

```zig
// ── Field types for HPT-lite ───────────────────────────────────────────

/// Field types tracked by HPT-lite for LLVM codegen.
/// This is a simplified type system that will be extended when
/// implementing full Heap Points-to Analysis (M2.4).
///
/// See: https://github.com/adinapoli/rusholme/issues/449
/// Reference: Podlovics, Hruska & Pénzes, "Compiling Lazy Functional
/// Programs to LLVM IR", 2020, Section 4.2.
pub const FieldType = enum {
    /// Integer or character (64-bit).
    i64,
    /// Floating-point (64-bit).
    f64,
    /// Heap pointer (to another node).
    ptr,
};
```

**Step 4: Run test to verify it passes**

Run: `zig build test -- --test-filter "FieldType: all variants"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/grin/ast.zig
git commit -m "#449: Add FieldType enum for HPT-lite type tracking"
```

---

## Task 2: Extend TagTable with Field Types

**Files:**
- Modify: `src/backend/grin_to_llvm.zig:79-112` (TagTable struct)

**Step 1: Write the failing test**

Add to `src/backend/grin_to_llvm.zig` tests section:

```zig
test "TagTable: field_types storage" {
    const alloc = std.testing.allocator;
    var table = TagTable.init();
    defer table.deinit(alloc);

    const just_tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Just", .unique = .{ .value = 1 } } };
    const field_types = [_]FieldType{ .i64 };
    try table.registerWithTypes(alloc, just_tag, 1, &field_types);

    const retrieved = table.fieldTypes(just_tag).?;
    try std.testing.expectEqual(@as(usize, 1), retrieved.len);
    try std.testing.expectEqual(FieldType.i64, retrieved[0]);
}
```

**Step 2: Run test to verify it fails**

Run: `zig build test -- --test-filter "TagTable: field_types storage"`
Expected: FAIL with "registerWithTypes not found"

**Step 3: Write minimal implementation**

Modify `TagTable` in `src/backend/grin_to_llvm.zig`:

```zig
/// Maps every constructor `Tag` in the GRIN program to a stable `i64`
/// discriminant (0, 1, 2, …), records the number of fields, and tracks
/// the FieldType of each field for HPT-lite.
///
/// See: https://github.com/adinapoli/rusholme/issues/449
const TagTable = struct {
    discriminants: std.AutoHashMapUnmanaged(u64, i64),
    field_counts: std.AutoHashMapUnmanaged(u64, u32),
    /// Field types per constructor, keyed by name unique.
    /// Each slice contains FieldType for each field position.
    /// This is HPT-lite: a simplified type tracking that will be
    /// extended when implementing full HPT (M2.4).
    field_types: std.AutoHashMapUnmanaged(u64, []const FieldType),
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

    /// Register with explicit field types (called from Core→GRIN translation).
    fn registerWithTypes(
        self: *TagTable,
        alloc: std.mem.Allocator,
        tag: grin.Tag,
        n_fields: u32,
        types: []const FieldType,
    ) !void {
        const key = tag.name.unique.value;
        if (self.discriminants.contains(key)) return;
        try self.discriminants.put(alloc, key, self.next);
        try self.field_counts.put(alloc, key, n_fields);
        const types_copy = try alloc.dupe(FieldType, types);
        try self.field_types.put(alloc, key, types_copy);
        self.next += 1;
    }

    fn discriminant(self: *const TagTable, tag: grin.Tag) ?i64 {
        return self.discriminants.get(tag.name.unique.value);
    }

    fn fieldCount(self: *const TagTable, tag: grin.Tag) ?u32 {
        return self.field_counts.get(tag.name.unique.value);
    }

    /// Return field types for a constructor, or null if unknown.
    fn fieldTypes(self: *const TagTable, tag: grin.Tag) ?[]const FieldType {
        return self.field_types.get(tag.name.unique.value);
    }

    fn isNullaryByName(self: *const TagTable, name: grin.Name) bool {
        const fc = self.field_counts.get(name.unique.value) orelse return false;
        return fc == 0;
    }

    fn discriminantByName(self: *const TagTable, name: grin.Name) ?i64 {
        if (!self.isNullaryByName(name)) return null;
        return self.discriminants.get(name.unique.value);
    }
};
```

Also add the import at the top of the file:

```zig
const grin = @import("../grin/ast.zig");
// Add after grin import:
const FieldType = grin.FieldType;
```

**Step 4: Run test to verify it passes**

Run: `zig build test -- --test-filter "TagTable: field_types storage"`
Expected: PASS

**Step 5: Run all tests to ensure nothing is broken**

Run: `zig build test --summary all`
Expected: All tests pass

**Step 6: Commit**

```bash
git add src/backend/grin_to_llvm.zig
git commit -m "#449: Extend TagTable with field_types for HPT-lite"
```

---

## Task 3: Add Type Inference Helper in Core→GRIN Translation

**Files:**
- Modify: `src/grin/translate.zig` (add type inference function)

**Step 1: Write the failing test**

Add to `src/grin/translate.zig` tests:

```zig
test "inferFieldType: Int literal" {
    const core_lit = core.Literal{ .Int = 42 };
    const ft = inferFieldTypeFromLiteral(core_lit);
    try testing.expectEqual(FieldType.i64, ft);
}

test "inferFieldType: Float literal" {
    const core_lit = core.Literal{ .Float = 3.14 };
    const ft = inferFieldTypeFromLiteral(core_lit);
    try testing.expectEqual(FieldType.f64, ft);
}
```

**Step 2: Run test to verify it fails**

Run: `zig build test -- --test-filter "inferFieldType"`
Expected: FAIL with "inferFieldTypeFromLiteral not found"

**Step 3: Write minimal implementation**

Add to `src/grin/translate.zig` after the imports:

```zig
// Import FieldType from GRIN AST
const FieldType = grin.FieldType;

/// Infer FieldType from a Core literal.
/// Part of HPT-lite: simple type inference for literal values.
/// See: https://github.com/adinapoli/rusholme/issues/449
fn inferFieldTypeFromLiteral(lit: core.Literal) FieldType {
    return switch (lit) {
        .Int => .i64,
        .Float => .f64,
        .Char => .i64, // chars are stored as i64
        .String => .ptr, // strings are pointers
    };
}

/// Infer FieldType from a Core type.
/// Returns null for complex types (delegates to ptr conservatively).
/// Part of HPT-lite: simple type inference from type annotations.
/// See: https://github.com/adinapoli/rusholme/issues/449
fn inferFieldTypeFromCoreType(ty: core.CoreType) ?FieldType {
    return switch (ty) {
        .TyVar => null, // Type variable - unknown
        .TyCon => |tc| blk: {
            // Check for primitive type constructors
            if (std.mem.eql(u8, tc.name.base, "Int") or
                std.mem.eql(u8, tc.name.base, "Char") or
                std.mem.eql(u8, tc.name.base, "Bool"))
            {
                break :blk .i64;
            }
            if (std.mem.eql(u8, tc.name.base, "Float") or
                std.mem.eql(u8, tc.name.base, "Double"))
            {
                break :blk .f64;
            }
            // Other type constructors are heap pointers
            break :blk .ptr;
        },
        .FunTy => .ptr, // Functions are closures (pointers)
        .ForAllTy => |fa| inferFieldTypeFromCoreType(fa.body.*),
    };
}
```

**Step 4: Run test to verify it passes**

Run: `zig build test -- --test-filter "inferFieldType"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/grin/translate.zig
git commit -m "#449: Add FieldType inference helpers for HPT-lite"
```

---

## Task 4: Build Extended TagTable During Core→GRIN Translation

**Files:**
- Modify: `src/grin/translate.zig` (buildTagTableWithTypes function)
- Create: `src/grin/tag_table.zig`

**Step 1: Create new tag_table.zig with tests**

Create `src/grin/tag_table.zig`:

```zig
//! Extended TagTable with field type information for HPT-lite.
//!
//! This module provides a TagTable that includes field type information
//! derived from Core AST type annotations. It is built during Core→GRIN
//! translation and used by the LLVM backend for type-correct codegen.
//!
//! See: https://github.com/adinapoli/rusholme/issues/449

const std = @import("std");
const grin = @import("ast.zig");
const core = @import("../core/ast.zig");

pub const FieldType = grin.FieldType;

/// Extended tag information including discriminant and field types.
pub const ExtendedTagInfo = struct {
    discriminant: i64,
    field_types: []const FieldType,
};

/// Tag table with field type information for HPT-lite.
pub const ExtendedTagTable = struct {
    /// Maps tag unique to ExtendedTagInfo.
    tags: std.AutoHashMapUnmanaged(u64, ExtendedTagInfo),
    /// Next discriminant to assign.
    next: i64,

    pub fn init() ExtendedTagTable {
        return .{
            .tags = .{},
            .next = 0,
        };
    }

    pub fn deinit(self: *ExtendedTagTable, alloc: std.mem.Allocator) void {
        var iter = self.tags.iterator();
        while (iter.next()) |entry| {
            alloc.free(entry.value_ptr.field_types);
        }
        self.tags.deinit(alloc);
    }

    /// Register a constructor with inferred field types.
    pub fn register(
        self: *ExtendedTagTable,
        alloc: std.mem.Allocator,
        tag: grin.Tag,
        field_types: []const FieldType,
    ) !void {
        const key = tag.name.unique.value;
        if (self.tags.contains(key)) return;

        const types_copy = try alloc.dupe(FieldType, field_types);
        try self.tags.put(alloc, key, .{
            .discriminant = self.next,
            .field_types = types_copy,
        });
        self.next += 1;
    }

    pub fn getTagInfo(self: *const ExtendedTagTable, tag: grin.Tag) ?ExtendedTagInfo {
        const info = self.tags.get(tag.name.unique.value);
        return info;
    }

    pub fn discriminant(self: *const ExtendedTagTable, tag: grin.Tag) ?i64 {
        const info = self.getTagInfo(tag) orelse return null;
        return info.discriminant;
    }

    pub fn fieldTypes(self: *const ExtendedTagTable, tag: grin.Tag) ?[]const FieldType {
        const info = self.getTagInfo(tag) orelse return null;
        return info.field_types;
    }
};

// Tests
const testing = std.testing;

test "ExtendedTagTable: register and retrieve" {
    const alloc = testing.allocator;
    var table = ExtendedTagTable.init();
    defer table.deinit(alloc);

    const tag = grin.Tag{ .tag_type = .Con, .name = .{ .base = "Just", .unique = .{ .value = 1 } } };
    const field_types = [_]FieldType{.i64};
    try table.register(alloc, tag, &field_types);

    const info = table.getTagInfo(tag).?;
    try testing.expectEqual(@as(i64, 0), info.discriminant);
    try testing.expectEqual(@as(usize, 1), info.field_types.len);
    try testing.expectEqual(FieldType.i64, info.field_types[0]);
}
```

**Step 2: Run test to verify it passes**

Run: `zig build test -- --test-filter "ExtendedTagTable"`
Expected: PASS

**Step 3: Commit**

```bash
git add src/grin/tag_table.zig
git commit -m "#449: Add ExtendedTagTable with field types for HPT-lite"
```

---

## Task 5: Integrate TypeEnv into LLVM Backend

**Files:**
- Modify: `src/backend/grin_to_llvm.zig` (add TypeEnv to GrinTranslator)

**Step 1: Write the failing test**

Add to `src/backend/grin_to_llvm.zig` tests:

```zig
test "TypeEnv: variable type lookup" {
    const alloc = std.testing.allocator;
    var env = TypeEnv.init(alloc);
    defer env.deinit();

    const var_name = grin.Name{ .base = "x", .unique = .{ .value = 1 } };
    try env.setVarType(var_name, .i64);

    try std.testing.expectEqual(FieldType.i64, env.getVarType(var_name).?);
}
```

**Step 2: Run test to verify it fails**

Run: `zig build test -- --test-filter "TypeEnv: variable type lookup"`
Expected: FAIL with "TypeEnv not found"

**Step 3: Write minimal implementation**

Add `TypeEnv` struct to `src/backend/grin_to_llvm.zig` before `GrinTranslator`:

```zig
// ═══════════════════════════════════════════════════════════════════════
// HPT-Lite Type Environment
// ═══════════════════════════════════════════════════════════════════════

/// HPT-Lite: Lightweight type propagation environment for LLVM codegen.
///
/// This is a simplified version of full Heap Points-to Analysis.
/// It tracks the FieldType of each GRIN variable so the LLVM backend
/// can emit correctly-typed IR (ptr vs i64 vs f64).
///
/// See: https://github.com/adinapuli/rusholme/issues/449
/// TODO: Replace with full HPT when implementing M2.4.
const TypeEnv = struct {
    /// Maps variable unique IDs to their FieldType.
    var_types: std.AutoHashMapUnmanaged(u64, FieldType),
    /// Reference to the tag table for constructor field types.
    tag_table: *const TagTable,

    fn init(alloc: std.mem.Allocator) TypeEnv {
        _ = alloc;
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
            .ConstTagNode => |ctn| blk: {
                // If this is being returned/stored as a value, it's a pointer
                // to the allocated node.
                _ = ctn;
                break :blk .ptr;
            },
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
```

**Step 4: Add TypeEnv to GrinTranslator**

Modify `GrinTranslator` struct:

```zig
pub const GrinTranslator = struct {
    ctx: llvm.Context,
    module: llvm.Module,
    builder: llvm.Builder,
    allocator: std.mem.Allocator,
    params: std.AutoHashMap(u64, llvm.Value),
    tag_table: TagTable,
    /// HPT-lite type environment for type-correct LLVM codegen.
    /// See: https://github.com/adinapoli/rusholme/issues/449
    type_env: TypeEnv,
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
            .type_env = TypeEnv.init(allocator),
            .current_func = null,
        };
    }

    pub fn deinit(self: *GrinTranslator) void {
        self.params.deinit();
        self.tag_table.deinit(self.allocator);
        self.type_env.deinit(self.allocator);
        llvm.disposeBuilder(self.builder);
        llvm.disposeContext(self.ctx);
    }
    // ... rest unchanged
};
```

**Step 5: Run test to verify it passes**

Run: `zig build test -- --test-filter "TypeEnv: variable type lookup"`
Expected: PASS

**Step 6: Run all tests**

Run: `zig build test --summary all`
Expected: All tests pass

**Step 7: Commit**

```bash
git add src/backend/grin_to_llvm.zig
git commit -m "#449: Add TypeEnv for HPT-lite type propagation"
```

---

## Task 6: Use TypeEnv in translateValToLlvm

**Files:**
- Modify: `src/backend/grin_to_llvm.zig:translateValToLlvm`

**Step 1: Identify the test case**

The existing test `Store emits rts_alloc and rts_store_field` should continue to pass.

**Step 2: Modify translateValToLlvm to use TypeEnv**

The key change is in how we handle values. Currently, the function returns whatever type it computes. We need to ensure type consistency based on TypeEnv.

No new test needed - existing tests should continue to pass.

**Step 3: Update translateValToLlvm**

Modify the `.Var` case in `translateValToLlvm`:

```zig
.Var => |name| blk: {
    // 1. Check params (function parameters and let-bound variables)
    if (self.params.get(name.unique.value)) |v| {
        // Type check: if the variable is supposed to be a pointer but we
        // have an i64, or vice versa, insert the appropriate conversion.
        const expected_type = self.type_env.getVarType(name) orelse .ptr;
        const val_type = c.LLVMTypeOf(v);
        const kind = c.LLVMGetTypeKind(val_type);
        const is_ptr = kind == c.LLVMPointerTypeKind;
        
        if (expected_type == .ptr and !is_ptr) {
            // Need to convert i64 to ptr
            break :blk c.LLVMBuildIntToPtr(self.builder, v, ptrType(), "to_ptr");
        } else if (expected_type != .ptr and is_ptr) {
            // Need to convert ptr to i64
            break :blk c.LLVMBuildPtrToInt(self.builder, v, llvm.i64Type(), "to_i64");
        }
        break :blk v;
    }
    // 2. Nullary constructor: emit its tag discriminant as an i64.
    if (self.tag_table.discriminantByName(name)) |disc| {
        break :blk c.LLVMConstInt(llvm.i64Type(), @bitCast(disc), 0);
    }
    // 3. Top-level function reference
    var fn_name_buf: [128]u8 = undefined;
    if (name.base.len < fn_name_buf.len) {
        @memcpy(fn_name_buf[0..name.base.len], name.base);
        fn_name_buf[name.base.len] = 0;
        const fn_name_z = fn_name_buf[0..name.base.len :0];
        if (c.LLVMGetNamedFunction(self.module, fn_name_z)) |fn_val| {
            break :blk fn_val;
        }
    }
    std.debug.print("UnsupportedGrinVal: Var {s}_{d} not found\n", .{ name.base, name.unique.value });
    return error.UnsupportedGrinVal;
},
```

**Step 4: Run all tests**

Run: `zig build test --summary all`
Expected: All tests pass

**Step 5: Commit**

```bash
git add src/backend/grin_to_llvm.zig
git commit -m "#449: Use TypeEnv in translateValToLlvm for type consistency"
```

---

## Task 7: Use TypeEnv in translateCase for Field Loading

**Files:**
- Modify: `src/backend/grin_to_llvm.zig:translateCase`

**Step 1: Update field loading in translateCase**

Modify the NodePat handling in `translateCase` to use correct types:

```zig
// For NodePat alts: load each field via rts_load_field(node, index).
// Use TypeEnv to determine the correct LLVM type for each field.
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
        
        // Get the expected field type from TypeEnv/TagTable
        const field_type = self.type_env.getFieldTagType(np.tag, @intCast(fi));
        
        // Convert the loaded i64 to the appropriate type
        const final_val: llvm.Value = switch (field_type) {
            .i64 => loaded_i64,
            .f64 => c.LLVMBuildBitCast(self.builder, loaded_i64, c.LLVMDoubleType(), "as_f64"),
            .ptr => c.LLVMBuildIntToPtr(self.builder, loaded_i64, ptrType(), "as_ptr"),
        };
        
        try self.params.put(field_name.unique.value, final_val);
        
        // Also record the type in TypeEnv for downstream use
        try self.type_env.setVarType(self.allocator, field_name, field_type);
    }
}
```

**Step 2: Run all tests**

Run: `zig build test --summary all`
Expected: All tests pass

**Step 3: Commit**

```bash
git add src/backend/grin_to_llvm.zig
git commit -m "#449: Use TypeEnv in translateCase for type-correct field loading"
```

---

## Task 8: Add E2E Test - Simple Arithmetic

**Files:**
- Create: `tests/e2e/ghc_009_arithmetic2.hs`
- Create: `tests/e2e/ghc_009_arithmetic2.stdout`
- Create: `tests/e2e/ghc_009_arithmetic2.properties` (if needed)

**Step 1: Create test file**

`tests/e2e/ghc_009_arithmetic2.hs`:

```haskell
main :: IO ()
main = putStrLn (show (1 + 2))
```

`tests/e2e/ghc_009_arithmetic2.stdout`:

```
3
```

**Step 2: Run the e2e test**

Run: `zig build test --summary all`
Expected: New test passes (or identify what needs fixing)

**Step 3: Commit**

```bash
git add tests/e2e/ghc_009_arithmetic2.*
git commit -m "#449: Add e2e test for simple arithmetic"
```

---

## Task 9: Add E2E Test - ADT with Single Constructor

**Files:**
- Create: `tests/e2e/ghc_010_single_con.hs`
- Create: `tests/e2e/ghc_010_single_con.stdout`

**Step 1: Create test file**

`tests/e2e/ghc_010_single_con.hs`:

```haskell
data Point = Point Int Int

main :: IO ()
main = case Point 3 4 of
    Point x y -> putStrLn (show (x + y))
```

`tests/e2e/ghc_010_single_con.stdout`:

```
7
```

**Step 2: Run the e2e test**

Run: `zig build test --summary all`

**Step 3: Commit**

```bash
git add tests/e2e/ghc_010_single_con.*
git commit -m "#449: Add e2e test for ADT with single constructor"
```

---

## Task 10: Add E2E Test - Higher-Order Functions

**Files:**
- Create: `tests/e2e/ghc_011_hof.hs`
- Create: `tests/e2e/ghc_011_hof.stdout`

**Step 1: Create test file**

`tests/e2e/ghc_011_hof.hs`:

```haskell
data List a = Nil | Cons a (List a)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr f z Nil = z
foldr f z (Cons x xs) = f x (foldr f z xs)

sumList :: List Int -> Int
sumList = foldr (+) 0

main :: IO ()
main = putStrLn (show (sumList (Cons 1 (Cons 2 (Cons 3 Nil)))))
```

`tests/e2e/ghc_011_hof.stdout`:

```
6
```

**Step 2: Run the e2e test**

This is the critical test that was failing before the fix.

Run: `zig build test --summary all`

**Step 3: Commit**

```bash
git add tests/e2e/ghc_011_hof.*
git commit -m "#449: Add e2e test for higher-order functions (the failing case)"
```

---

## Task 11: Final Verification and Cleanup

**Step 1: Run all tests**

Run: `zig build test --summary all`
Expected: All tests pass

**Step 2: Verify the specific failing case**

Create a manual test:

```bash
# Create test file
cat > /tmp/hof_test.hs << 'EOF'
data List a = Nil | Cons a (List a)

foldr :: (a -> b -> b) -> b -> List a -> b
foldr f z Nil = z
foldr f z (Cons x xs) = f x (foldr f z xs)

main :: IO ()
main = putStrLn (show (foldr (+) 0 (Cons 1 (Cons 2 Nil))))
EOF

# Build and run
zig build
./zig-out/bin/rusholme build /tmp/hof_test.hs -o /tmp/hof_test
/tmp/hof_test
```

Expected output: `3`

**Step 3: Push changes**

```bash
git push origin llm-agent/issue-449
```

**Step 4: Create PR**

```bash
gh pr create \
  --title "#449: Implement HPT-lite type propagation for LLVM codegen" \
  --body "Closes #449

## Summary
Implemented HPT-lite (lightweight Heap Points-to Analysis) to fix type
mismatches in LLVM codegen that caused runtime segfaults with ADTs and
higher-order functions.

## Changes
- Added FieldType enum (i64, f64, ptr) to GRIN AST
- Extended TagTable with field type information
- Added TypeEnv for type propagation through GRIN variables
- Updated LLVM backend to use TypeEnv for type-correct IR emission
- Added e2e tests for arithmetic, ADTs, and HOFs

## Testing
All existing tests pass. New e2e tests verify the fix works for the
previously-failing case (programs with ADTs and HOFs).

## References
- Issue: https://github.com/adinapoli/rusholme/issues/449
- Design: docs/plans/2026-03-01-hpt-lite-type-propagation.md
- GRIN Paper: Podlovics, Hruska & Pénzes, 2020, Section 4.2" \
  --base main \
  --head llm-agent/issue-449 \
  --reviewer adinapoli
```
