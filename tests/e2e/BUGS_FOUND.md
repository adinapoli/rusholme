# Rusholme Bugs Exposed by e2e Test Development

This document tracks bugs found while developing e2e tests for issue #64.

## Bug #001: GRIN→LLVM Codegen Function Name Mismatch

**Description:** When a function is defined in GRIN, the LLVM backend generates a different function name (e.g., `showMyBool.1` instead of `showMyBool`), causing undefined reference errors at link time.

**Affected files:**
- `tests/e2e/e2e_002_bool.hs`
- `tests/e2e/e2e_005_nested_datatypes.hs`

**Example:**
```haskell
-- GRIN output:
main = showMyBool_2 CMyTrue ...

-- LLVM output:
declare ptr @showMyBool(ptr)
define ptr @showMyBool.1(ptr %0) { ... }
```

**Impact:** Any test that defines a function with multiple pattern matches will fail at link time.

**Workaround (for now):** Only use inlined expressions or single-line functions without pattern matching.

---

## Bug #002: Do Notation - UnsupportedGrinVal

**Description:** When desugaring `do` notation, Rusholme generates `todo_do_1` symbols that GRIN→LLVM cannot resolve.

**Example:**
```haskell
main = do
  putStrLn "first"
  putStrLn "second"
```

Generates GRIN:
```
main = pure todo_do_1
```

But LLVM codegen fails with: `UnsupportedGrinVal: Var todo_do_1 not found in params, tag table, or module`

**Affected files:**
- `tests/e2e/e2e_003_multi_putStrLn.hs`

**Impact:** Any code using `do` notation (including most multi-statement programs) fails compilation.

---

## Bug #003: Reserved Constructor Names Conflict

**Description:** Constructor names like `True` and `False` conflict with reserved names in Rusholme's parser/renamer.

**Affected files:**
- `tests/e2e/e2e_002_bool.hs` (original, fixed by renaming to `MyTrue`/`MyFalse`)

**Workaround:** Avoid reserved constructor names.

---

## Known Limitations (Not Bugs)

### Typechecker limitations with Polymorphism
The typechecker struggles with polymorphic function definitions. This is expected given the current state of the implementation.

### Nested Where Clauses
Variable scoping in nested `where` clauses is not fully implemented yet.

---

## Summary

At this time, the e2e test infrastructure can reliably test:
1. `putStrLn` with string literals
2. Module parsing and compilation

But cannot yet test:
1. Custom data types with functions (Bug #001)
2. Do notation/multi-statement programs (Bug #002)
3. Complex pattern matching

These bugs should be filed as GitHub issues and tracked separately from issue #462 (Prelude work).
