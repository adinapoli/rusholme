# Plan: Issue #184 — Bidirectional Signature Checking for Rank-N Polymorphism

## Context

The typechecker currently converts type signatures to `HType` by replacing all type variables (including `forall`-bound ones) with **fresh metavariables**. The inferred body type is unified against this signature, and then `generalisePtr` converts the surviving metas into rigids for the final `TyScheme`. This works for rank-1 but fails for rank-N because:

- Metavariables can be unified with anything — they don't enforce that a type variable is **universally quantified** (rigid/skolem).
- For rank-2 types like `(forall s. ST s a) -> a`, the inner `forall s` gets instantiated to a meta, destroying the higher-rank structure.

Additionally, the existing `Forall` handler in `astTypeToHTypeWithScope` has a bug: it creates rigid binder names but does **not** insert them into the scope before recursing into the body, so the body's type variables resolve to metas instead of the intended rigids.

**Reference:** Dunfield & Krishnaswami, "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism", ICFP 2013.

## Changes

All changes are in **`src/typechecker/infer.zig`** (no other files need modification).

### 1. Fix `Forall` handler in `astTypeToHTypeWithScope` (~line 479)

**Bug:** The handler recurses into the body *before* creating the rigid binders, so type variables in the body resolve to metas (or existing scope entries) rather than the binders.

**Fix:** Create fresh rigid names, insert them into the scope, *then* recurse into the body, then wrap in `ForAll` nodes.

```
Current:  recurse body → create rigids → wrap ForAll
Fixed:    create rigids → insert into scope → recurse body → wrap ForAll
```

### 2. Add `SkolemiseResult` struct and `skolemiseSignature` function

```zig
const SkolemiseResult = struct {
    ty: *HType,
    skolem_ids: []const u64,
};
```

`skolemiseSignature(ast_ty, ctx)` handles two cases:
- **Explicit `forall`:** Creates fresh rigids for each binder, inserts them into a scope, converts the body with that scope. Returns the body type and the rigid unique IDs.
- **No explicit `forall`:** Collects free type variable names from the AST type (implicit `forall`), creates fresh rigids for each, converts with those in scope.

Nested `forall`s inside the body are handled by the (now-fixed) `Forall` handler in `astTypeToHTypeWithScope` — they produce `HType.ForAll` nodes (preserving rank-2+ structure), not top-level skolems.

### 3. Add `collectFreeTypeVars` helper

Recursively walks an AST `Type` and collects free type variable names (the `Var` cases). Skips variables bound by nested `Forall`. This handles the implicit `forall` case (`f :: a -> a` = `f :: forall a. a -> a`).

### 4. Add `skolem_ids` field to `TypeSigEntry`

```zig
const TypeSigEntry = struct {
    name: Name,
    ty: *HType,
    loc: SourceSpan,
    skolem_ids: []const u64,  // NEW
};
```

### 5. Modify signature collection (3 locations)

Change from `astTypeToHTypeWithScope` to `skolemiseSignature` in:
- `inferModule` Pass 0 (~line 1444)
- `collectLetSigs` (~line 1308)

### 6. Modify scheme construction when signature is present (3 locations)

When a signature is present, **skip `generalisePtr`** and build `TyScheme` directly from `skolem_ids`:

```zig
const scheme = TyScheme{
    .binders = s.skolem_ids,
    .constraints = &.{},
    .body = s.ty.*,
};
```

Apply in:
- `inferModule` Pass 2 (~line 1540)
- `Let` handler Pass 2 (~line 690)
- `inferLetDecl` (~line 1370)

### 7. Unit tests

| Test | Verifies |
|------|----------|
| `skolemiseSignature: explicit forall a. a -> a` | 1 skolem, body is `Rigid -> Rigid` (same rigid) |
| `skolemiseSignature: implicit forall (a -> a)` | Same result as explicit |
| `skolemiseSignature: no type vars (Int -> Int)` | 0 skolems, body is `Con -> Con` |
| `skolemiseSignature: multiple vars (a -> b -> a)` | 2 skolems, body correctly structured |
| `signature mismatch: f :: a -> b; f x = x` | Error: distinct skolems `a` and `b` can't unify |
| `rank-1 signature: f :: a -> a; f x = x` | Passes, scheme has 1 binder |
| `monomorphic sig: f :: Int -> Int; f x = x` | Passes, 0 binders |
| `const sig: const :: a -> b -> a; const x y = x` | Passes, 2 binders |
| Regressions: existing let-polymorphism, module inference tests pass | No breakage |

## Files to modify

- `src/typechecker/infer.zig` — all changes and new tests

## Verification

```bash
zig build test --summary all
```

All existing tests must pass. New tests exercise the skolemisation path.
