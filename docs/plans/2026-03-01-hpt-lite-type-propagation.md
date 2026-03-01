# HPT-Lite Type Propagation for GRIN→LLVM

**Issue:** #449  
**Date:** 2026-03-01  
**Status:** Approved

## Problem

The LLVM backend generates type-incorrect IR when compiling programs with ADTs and higher-order functions. Example:

```llvm
define i64 @main() {
  ; ...
  %result = call ptr @some_function()  ; returns ptr
  ret i64 %result                       ; but function declared to return i64
}
```

This causes runtime segmentation faults because LLVM's type system is violated.

## Root Cause

GRIN is untyped — the `Val` type carries no type information. When translating GRIN to LLVM, the backend must guess types, leading to mismatches between function signatures and actual return values.

The GRIN paper (Podlovics, Hruska, Penzes 2020) explicitly addresses this:

> "The main challenge of compiling GRIN to LLVM has to do with the discrepancy between the respective type systems: GRIN is untyped, while LLVM has static typing."

## Solution: HPT-Lite

Implement a lightweight type propagation pass ("HPT-lite") that tracks type information through the GRIN AST. This is explicitly a stepping stone toward full Heap Points-to Analysis.

### Design Principle

This is **not** full HPT. Full HPT (planned for M2.4) tracks:
- Which heap locations each variable can point to
- Points-to sets for optimization
- Strictness analysis

HPT-lite tracks only:
- The type of each variable (i64, f64, or ptr)
- Field types for each constructor tag

### Components

#### 1. FieldType Enum

```zig
/// Field types tracked by HPT-lite.
/// This will be extended when implementing full HPT (M2.4).
pub const FieldType = enum {
    i64,  // integers, chars
    f64,  // doubles
    ptr,  // heap pointers (other nodes)
};
```

#### 2. Extended TagTable

Extend `TagTable` to record field types per constructor:

```zig
pub const TagInfo = struct {
    discriminant: u32,
    field_types: []const FieldType,  // NEW: types of each field
};
```

During Core→GRIN translation, populate `field_types` based on the Core AST type information.

#### 3. TypeEnv (HPT-Lite Pass)

A new pass that propagates types through GRIN variables:

```zig
/// HPT-Lite: Lightweight type propagation for LLVM codegen.
/// This is a simplified version of full Heap Points-to Analysis.
/// See: https://github.com/adinapoli/rusholme/issues/449
/// TODO: Replace with full HPT when implementing M2.4.
pub const TypeEnv = struct {
    var_types: std.HashMap(Name, FieldType),  // variable -> type
    tag_table: *const TagTable,               // constructor field types
};
```

#### 4. LLVM Backend Integration

The backend queries `TypeEnv` when emitting code:

```zig
fn translateValToLlvm(self: *Self, val: Val) !LlvmValue {
    const field_type = self.type_env.getType(val);
    return switch (field_type) {
        .i64 => // emit i64 operations
        .f64 => // emit f64 operations  
        .ptr => // emit pointer operations
    };
}
```

### Data Flow

```
Core AST (typed)
    ↓ Core→GRIN translation
GRIN AST + TagTable (with field_types)
    ↓ HPT-Lite pass
GRIN AST + TypeEnv
    ↓ LLVM codegen
Correctly-typed LLVM IR
```

### Implementation Steps

1. Add `FieldType` enum to GRIN AST module
2. Extend `TagTable` with `field_types` field
3. Modify Core→GRIN translation to populate field types
4. Implement `TypeEnv` pass for type propagation
5. Integrate `TypeEnv` into LLVM backend
6. Add e2e tests for increasingly complex programs

### Testing Strategy

Add e2e tests with increasingly complex programs:

1. `hello.hs` - Simple main returning unit (already works)
2. `arith.hs` - Integer arithmetic
3. `single_con.hs` - ADT with single constructor
4. `multi_con.hs` - ADT with multiple constructors
5. `hof.hs` - Higher-order functions (the failing case)

Each test should:
- Compile to LLVM IR
- Execute successfully
- Produce correct output

### Relation to Full HPT

Full HPT (M2.4) will extend this infrastructure:

| HPT-Lite (Now) | Full HPT (M2.4) |
|----------------|-----------------|
| Single type per variable | Set of possible types |
| No points-to tracking | Points-to sets |
| Type-only analysis | Optimization-friendly |

The `FieldType` enum and `TypeEnv` structure are designed to be extended, not replaced.

### References

- GRIN Paper: Podlovics, Hruska, Penzes. "Compiling Lazy Functional Programs to LLVM IR". 2020.
- Issue: https://github.com/adinapoli/rusholme/issues/449
