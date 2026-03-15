# Type Unification Fix for PR #575

## Problem

When checking polymorphic functions like `(++) :: [a] -> [a] -> [a]` against their pattern-matching equations, pattern variables create independent fresh metavariables (`?163`, `?172`) instead of sharing the same type variable `a` from the signature:

```
error[E002]: cannot unify `[a] -> [?163] -> [a]` with `[a] -> [a] -> [a]` (rigid type variable mismatch)
```

This causes 12 e2e test failures in PR #575.

## Root Cause

The path for type inference is separated:

1. **Signature handling** (`skolemiseSignature()`): Converts signatures to rigid types, storing them in a `rigid_map` keyed by type variable name
2. **Pattern inference** (`inferPat()`): Unconditionally creates fresh metas for pattern variables, never checking if a signature has constraints

These two worlds don't communicate, so equation patterns get independent metas.

## Solution

Pass signature context (the `rigid_map`) into pattern inference so pattern variables can check for pre-defined rigid types before creating fresh metas.

## Design

### API Changes

Add optional signature context parameter to functions that lead to pattern inference:

| Function | Current Signature | New Signature |
|----------|------------------|---------------|
| `inferPat` | `(ctx, pat)` | `(ctx, sig_vars, pat)` |
| `inferMatch` | `(ctx, match)` | `(ctx, sig_vars, match)` |

### Pattern Variable Lookup Logic

When inferring a `.Var` pattern:

1. Check if `sig_vars` parameter is not null
2. If not null, check if pattern variable's name exists in the `sig_vars` map
3. If found, use the rigid HType pointer from the signature's scope
4. If not found or `sig_vars` is null, fall back to fresh meta (backward compatible)

```zig
.Var => |v| blk: {
    var ty: *HType = undefined;
    
    if (sig_vars) |scope| {
        if (scope.get(v.name.base)) |rigid_ty| {
            ty = rigid_ty;  // Type from signature
        } else {
            ty = try ctx.freshMeta();  // Fresh meta (backward compatible)
        }
    } else {
        ty = try ctx.freshMeta();  // Fresh meta (backward compatible)
    }
    
    try ctx.env.bindMono(v.name, ty.*);
    try ctx.local_binders.put(ctx.alloc, v.name.unique, ty);
    break :blk ty;
},
```

### Call Site Updates

Primary update is the `.FunBind` equation checking loop:

```zig
for (fb.equations) |eq| {
    if (sig_entry) |s| {
        // Pass signature context for pattern inference
        const sig_vars = &s.rigid_map;
        const eq_ty = try inferMatch(ctx, sig_vars, eq);
        try ctx.unifyNow(eq_ty, s.ty, fb.span);
        try ctx.unifyNow(fun_node, s.ty, fb.span);
    } else {
        // No signature context
        const eq_ty = try inferMatch(ctx, null, eq);
        try ctx.unifyNow(fun_node, eq_ty, fb.span);
    }
}
```

All other call sites pass `null` for backward compatibility.

### Error Handling

No new error cases. This fix only changes the source of types for pattern variables without introducing new failure modes.

### Testing

**Unit tests:**
- Test `inferPat` with `sig_vars` uses rigid types
- Test `inferPat` without `sig_vars` creates fresh meta

**E2E tests:**
- 12 currently failing tests with rigid mismatch error should pass after fix
- No xfail annotations to remove (xfails are for pre-existing bugs)

**Verification:**
```bash
zig build test --summary all
# Expected: 888/888 tests pass (all 12 currently-failing e2e tests now pass)
```

## Implementation Checklist

- [ ] Add `sig_vars` parameter to `inferPat()` signature
- [ ] Add `sig_vars` parameter to `inferMatch()` signature
- [ ] Modify `inferPat`'s `.Var` case to check `sig_vars` first
- [ ] Update `.FunBind` equation checking loop to pass `sig_entry.rigid_map`
- [ ] Update all other call sites to pass `null`
- [ ] Add unit tests for `inferPat` with `sig_vars` paths
- [ ] Verify all 888 tests pass

## Files Modified

- `src/typechecker/infer.zig` (~30 lines in 3 functions)

## Complexity

- **Low risk:** Only changes pattern variable type sourcing, no unification logic changes
- **Backward compatible:** Null-safe fallback to existing behavior
- **Testable:** Explicit unit tests can verify both paths
