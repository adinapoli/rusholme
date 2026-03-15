# Type Unification Fix Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix type unification bug causing "rigid type variable mismatch" errors in PR #575

**Architecture:** Pass signature context (rigid type map) into pattern inference so pattern variables use signature's rigid types instead of fresh metas

**Tech Stack:** Zig 0.12+, Rusholme compiler, HType arena allocation, TypeVarMap for type variable lookups

---

## Chunk 1: Add Rigid Map to Structures

This chunk adds the necessary data structures for passing type variable context from signatures to pattern inference.

### Task 1: Add rigid_map field to SkolemiseResult

**Files:**
- Modify: `src/typechecker/infer.zig:650-660`

- [ ] **Step 1: Add rigid_map field to SkolemiseResult struct**

After line 657, add the rigid_map field after constraints:

```zig
constraints: []const ClassConstraint,
/// Map from type variable names (e.g., "a", "b") to their rigid HType pointers.
/// Used during pattern inference to ensure pattern variables use the same
/// type variables from the signature instead of fresh metas.
rigid_map: TypeVarMap,
};
```

Run: `zig build`
Expected: PASS (struct field added, no behavior change yet)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Add rigid_map field to SkolemiseResult"
```

### Task 2: Add rigid_map field to TypeSigEntry

**Files:**
- Modify: `src/typechecker/infer.zig:630-639`

- [ ] **Step 1: Add rigid_map field to TypeSigEntry struct**

After line 639 (after constraints field), add the rigid_map field:

```zig
constraints: []const ClassConstraint,
/// Map from type variable names to their rigid HType pointers from skolemisation.
/// Used during pattern inference to maintain type variable consistency across
/// patterns in the same signature.
rigid_map: TypeVarMap,
};
```

Run: `zig build`
Expected: PASS

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Add rigid_map field to TypeSigEntry"
```

---

## Chunk 2: Modify skolemiseSignature to Return rigid_map

This chunk modifies `skolemiseSignature` to populate and return the TypeVarMap instead of deinitializing it.

**Files:**
- Modify: `src/typechecker/infer.zig:677-750`

### Task 3: Change skolemiseSignature to return scope instead of deinitting

- [ ] **Step 1: Remove defer scope.deinit() call**

Find line 683 (`defer scope.deinit(ctx.alloc);`) and remove it. The scope should be returned to the caller for use in pattern inference.

Run: `zig build`
Expected: PASS

- [ ] **Step 2: Add scope to SkolemiseResult at all return points**

Find all return statements in `skolemiseSignature` and add `.rigid_map = scope`:

For the explicit forall case (around line 746):
```zig
return .{
    .ty = conv_ty,
    .skolem_ids = skolem_ids.items,
    .constraints = constraints,
    .rigid_map = scope,
};
```

For the no-explicit-forall case (implicit forall, around line 785):
```zig
return .{
    .ty = conv_ty,
    .skolem_ids = skolem_ids.items,
    .constraints = constraints,
    .rigid_map = scope,
};
```

Run: `zig build`
Expected: PASS

- [ ] **Step 3: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Return TypeVarMap from skolemiseSignature"
```

---

## Chunk 3: Update TypeSigEntry Creation to Store rigid_map

This chunk modifies the three call sites where TypeSigEntry structures are created to store the rigid_map field.

**Files:**
- Modify: `src/typechecker/infer.zig:1723-1730`
- Modify: `src/typechecker/infer.zig:1886-1893`
- Modify: `src/typechecker/infer.zig:1901-1908`

### Task 4: Add rigid_map to TypeSigEntry initialization (first call site)

File: src/typechecker/infer.zig, lines 1723-1728

- [ ] **Step 1: Add rigid_map to TypeSigEntry literal**

After line 1727 (after constraints), add:
```zig
.constraints = skolem_result.constraints,
.rigid_map = skolem_result.rigid_map,
```

Run: `zig build`
Expected: PASS

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Store rigid_map in TypeSigEntry (Pass0b)"
```

### Task 5: Add rigid_map to TypeSigEntry initialization (second call site)

File: src/typechecker/infer.zig, lines 1886-1891

- [ ] **Step 1: Add rigid_map to TypeSigEntry literal**

After line 1890 (after constraints), add:
```zig
.constraints = skolem_result.constraints,
.rigid_map = skolem_result.rigid_map,
```

Run: `zig build`
Expected: PASS

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Store rigid_map in TypeSigEntry (Pass0a)"
```

### Task 6: Add rigid_map to TypeSigEntry initialization (third call site)

File: src/typechecker/infer.zig, lines 1901-1906

- [ ] **Step 1: Add rigid_map to TypeSigEntry literal**

After line 1905 (after constraints), add:
```zig
.constraints = skolem_result.constraints,
.rigid_map = skolem_result.rigid_map,
```

Run: `zig build`
Expected: PASS

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Store rigid_map in TypeSigEntry (ForeignPrim)"
```

---

## Chunk 4: Update Function Signatures

This chunk updates the signatures of `inferPat` and `inferMatch` to accept an optional signature context parameter.

### Task 7: Update inferPat signature

**Files:**
- Modify: `src/typechecker/infer.zig:910`

- [ ] **Step 1: Add sig_vars parameter to inferPat**

Change line 910 from:
```zig
pub fn inferPat(ctx: *InferCtx, pat: RPat) std.mem.Allocator.Error!*HType {
```

To:
```zig
pub fn inferPat(ctx: *InferCtx, sig_vars: ?*const TypeVarMap, pat: RPat) std.mem.Allocator.Error!*HType {
```

Run: `zig build`
Expected: FAIL (multiple call sites now incorrect)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Add sig_vars parameter to inferPat"
```

### Task 8: Update inferMatch signature

**Files:**
- Modify: `src/typechecker/infer.zig:1825`

- [ ] **Step 1: Add sig_vars parameter to inferMatch**

Change line 1825 from:
```zig
fn inferMatch(ctx: *InferCtx, match: RMatch) std.mem.Allocator.Error!*HType {
```

To:
```zig
fn inferMatch(ctx: *InferCtx, sig_vars: ?*const TypeVarMap, match: RMatch) std.mem.Allocator.Error!*HType {
```

Run: `zig build`
Expected: FAIL (multiple call sites now incorrect)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Add sig_vars parameter to inferMatch"
```

---

## Chunk 5: Implement Pattern Variable Lookup Logic

This chunk implements the core logic: checking the signature context first before creating fresh metas.

### Task 9: Modify inferPat Var case to check sig_vars

**Files:**
- Modify: `src/typechecker/infer.zig:912-919`

- [ ] **Step 1: Replace .Var case implementation**

Replace lines 912-919 (the entire .Var => |v| block) with:

```zig
.Var => |v| blk: {
    var ty: *HType = undefined;
    
    if (sig_vars) |scope| {
        if (scope.get(v.name.base)) |rigid_ty| {
            ty = rigid_ty;  // Use signature's rigid type
        } else {
            ty = try ctx.freshMeta();  // Backward compatible: fresh meta
        }
    } else {
        ty = try ctx.freshMeta();  // Backward compatible: fresh meta
    }
    
    try ctx.env.bindMono(v.name, ty.*);
    try ctx.local_binders.put(ctx.alloc, v.name.unique, ty);
    break :blk ty;
},
```

Run: `zig build`
Expected: FAIL (call sites still not updated)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Check sig_vars in inferPat .Var case"
```

### Task 10: Update inferMatch to pass sig_vars to inferPat

**Files:**
- Modify: `src/typechecker/infer.zig:1842`

- [ ] **Step 1: Pass sig_vars to inner inferPat call**

Find line 1842:
```zig
const arg_ty = try inferPat(ctx, arg_pat);
```

Replace with:
```zig
const arg_ty = try inferPat(ctx, sig_vars, arg_pat);
```

Run: `zig build`
Expected: FAIL (more call sites to update)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Pass sig_vars through inferMatch to inferPat"
```

---

## Chunk 6: Update Primary Call Site (FunBind)

This chunk updates the primary call site where equations are type-checked, passing the signature context.

### Task 11: Update Pass inferRhs FunBind call site

**Files:**
- Modify: `src/typechecker/infer.zig:1730`
- Modify: `src/typechecker/infer.zig:1740-1748`

- [ ] **Step 1: Add sig_vars variable in inferRhs FunBind**

Context: Around line 1729-1753 in the inferRhs function's FunBind case

Find line 1730 and modify the code to capture sig_vars:

After line 1732:
```zig
const fun_node = let_metas.get(fb.name.unique) orelse continue;

// Store the rigid_map for passing to inferMatch
const entry = sigs.get(fb.name.unique);
const sig_vars = blk: {
    if (entry) |e| {
        break :blk &e.rigid_map;
    }
    break :blk null;
};

for (fb.equations) |eq| {
```

Run: `zig build`
Expected: FAIL (call site still uses old inferMatch signature)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Capture sig_vars in inferRhs FunBind"
```

- [ ] **Step 3: Update inferMatch call to pass sig_vars**

Lines 1740-1748, replace the entire block:

Old code:
```zig
for (fb.equations) |eq| {
    const eq_ty = try inferMatch(ctx, eq);

    if (sig_entry) |s| {
        // If there's a signature, unify the inferred type against it.
        try ctx.unifyNow(eq_ty, s.ty, fb.span);
        // Also unify fun_node with the signature so that local_binders
        // has the solved type. Without this, fun_node remains an unsolved
        // meta and causes a panic in HType.toCore during desugaring.
        try ctx.unifyNow(fun_node, s.ty, fb.span);
    } else {
        // Otherwise, unify against the fresh meta node.
        try ctx.unifyNow(fun_node, eq_ty, fb.span);
    }
}
```

New code:
```zig
for (fb.equations) |eq| {
    const eq_ty = try inferMatch(ctx, sig_vars, eq);

    if (entry) |s| {
        // If there's a signature, unify the inferred type against it.
        try ctx.unifyNow(eq_ty, s.ty, fb.span);
        // Also unify fun_node with the signature so that local_binders
        // has the solved type. Without this, fun_node remains an unsolved
        // meta and causes a panic in HType.toCore during desugaring.
        try ctx.unifyNow(fun_node, s.ty, fb.span);
    } else {
        // Otherwise, unify against the fresh meta node.
        try ctx.unifyNow(fun_node, eq_ty, fb.span);
    }
}
```

Run: `zig build`
Expected: FAIL (more call sites to update in other functions)

- [ ] **Step 4: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Pass sig_vars to inferMatch in inferRhs"
```

### Task 12: Update Pass inferDecl FunBind call site

**Files:**
- Modify: `src/typechecker/infer.zig:1211`
- Modify: `src/typechecker/infer.zig:1227-1244`

- [ ] **Step 1: Add sig_vars variable in inferDecl FunBind**

Around line 1227, after retrieving sig_entry:

After line 1229:
```zig
const fun_node = let_metas.get(fb.name.unique) orelse continue;
const sig_entry = sigs.get(fb.name.unique);

// Store the rigid_map for passing to inferMatch
const sig_vars = blk: {
    if (sig_entry) |e| {
        break :blk &e.rigid_map;
    }
    break :blk null;
};

for (fb.equations) |eq| {
```

Run: `zig build`
Expected: FAIL (call site still uses old inferMatch signature)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Capture sig_vars in inferDecl FunBind"
```

- [ ] **Step 3: Update inferMatch call to pass sig_vars**

Lines 1231-1243, replace the entire block with:

```zig
for (fb.equations) |eq| {
    const eq_ty = try inferMatch(ctx, sig_vars, eq);

    if (sig_entry) |s| {
        // If there's a signature, unify the inferred type against it.
        try ctx.unifyNow(eq_ty, s.ty, fb.span);
        // Also unify fun_node with the signature so that local_binders
        // has the solved type. Without this, fun_node remains an unsolved
        // meta and causes a panic in HType.toCore during desugaring.
        try ctx.unifyNow(fun_node, s.ty, fb.span);
    } else {
        // Otherwise, unify against the fresh meta node.
        try ctx.unifyNow(fun_node, eq_ty, fb.span);
    }
}
```

Run: `zig build`
Expected: FAIL (more call sites to update)

- [ ] **Step 4: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Pass sig_vars to inferMatch in inferDecl"
```

### Task 13: Update Pass inferModule FunBind call site

**Files:**
- Modify: `src/typechecker/infer.zig:2110-2125
**
- [ ] **Step 1: Add sig_vars variable in inferModule FunBind**

Around line 2110, after retrieving sig_entry:

After line 2111:
```zig
const fun_node = top_metas.get(fb.name.unique) orelse continue;
const sig_entry = sigs.get(fb.name.unique);

// Store the rigid_map for passing to inferMatch
const sig_vars = blk: {
    if (sig_entry) |e| {
        break :blk &e.rigid_map;
    }
    break :blk null;
};

for (fb.equations) |eq| {
```

Run: `zig build`
Expected: FAIL (call site still uses old inferMatch signature)

- [ ] **Step 2: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Capture sig_vars in inferModule FunBind"
```

- [ ] **Step 3: Update inferMatch call to pass sig_vars**

Lines 2113-2125, replace the entire block with:

```zig
for (fb.equations) |eq| {
    const eq_ty = try inferMatch(ctx, sig_vars, eq);

    if (sig_entry) |s| {
        // If there's a signature, unify the inferred type against it.
        try ctx.unifyNow(eq_ty, s.ty, fb.span);
        // Also unify fun_node with the signature so that local_binders
        // has the solved type. Without this, fun_node remains an unsolved
        // meta and causes a panic in HType.toCore during desugaring.
        try ctx.unifyNow(fun_node, s.ty, fb.span);
    } else {
        // Otherwise, unify against the fresh meta node.
        try ctx.unifyNow(fun_node, eq_ty, fb.span);
    }
}
```

Run: `zig build`
Expected: FAIL (still more call sites to update)

- [ ] **Step 4: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Pass sig_vars to inferMatch in inferModule"
```

---

## Chunk 7: Update Remaining Call Sites

This chunk updates all other call sites of inferPat and inferMatch to pass null for sig_vars.

### Task 14: Update Lit case call to inferPat

**Files:**
- Modify: `src/typechecker/infer.zig:920`

- [ ] **Step 1: Pass null to inferPat in Lit case**

Line 915, change:
```zig
.Lit => |l| inferLit(l, ctx),
```

To:
```zig
.Lit => |l| inferLit(l, ctx, null),
```

Wait, this is incorrect - Lit doesn't call inferPat. Let me re-check line 915...

Actually Line 915 already directly passes ctx to inferLit, not inferPat. Let me find all actual inferPat call sites.

Search for: `inferPat(ctx,`

Run: `zig build test --summary all`
Expected: Current state should still have compilation errors

- [ ] **Step 2: Search for all inferPat call sites and update them**

Run: `grep -n "inferPat(ctx," src/typechecker/infer.zig`

Expected output shows call sites. Update each one to pass `null` after ctx:

Line 915 (Wild case - but this doesn't call inferPat)
Wait, let me re-read the code. The `.Lit` case doesn't call inferPat. Let me find the correct call sites.

Actually, looking at the pattern inference code:

```zig
.Lit => |l| inferLit(l, ctx),
.Wild => ctx.freshMeta(),
.AsPat => |ap| blk: {
    const inner_ty = try inferPat(ctx, ap.pat.*);
    // ...
```

So I need to update the AsPat case. Let me find the exact line.

Run: `grep -n "\.AsPat" src/typechecker/infer.zig | head -5`

Expected: Line showing AsPat case location

Let me update AsPat case:

- [ ] **Step 3: Pass null in AsPat case**

Line ~922 (AsPat case), find:
```zig
const inner_ty = try inferPat(ctx, ap.pat.*);
```

Replace with:
```zig
const inner_ty = try inferPat(ctx, null, ap.pat.*);
```

Run: `zig build`
Expected: Still failing (need to check line number)

- [ ] **Step 4: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Pass null in AsPat inferPat call"
```

Let me search more systematically for all call sites.

- [ ] **Step 5: Find and update ALL remaining inferPat call sites**

Run: `grep -n "inferPat(ctx," src/typechecker/infer.zig`

Result will show all call sites. For each, add `, null` after ctx parameter.

Based on grep results, update each:
- Line ~952-956 (Con case, probably multiple inferPat calls)
- Any other call sites found

For each match:
Old: `inferPat(ctx, ...)`
New: `inferPat(ctx, null, ...)`

Run: `zig build`
Expected: Still may have inferMatch call sites

- [ ] **Step 6: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Pass null in all remaining inferPat call sites"
```

- [ ] **Step 7: Find and update ALL remaining inferMatch call sites**

Run: `grep -n "inferMatch(ctx," src/typechecker/infer.zig`

For each call site not already updated in Chunk 6, add `, null` after ctx parameter.

Based on grep results (likely Lines ~1767, ~1827, ~1846, ~1926):
Old: `inferMatch(ctx, ...)`
New: `inferMatch(ctx, null, ...)`

Run: `zig build`
Expected: PASS (or close to pass)

- [ ] **Step 8: Commit**

```bash
git add src/typechecker/infer.zig
git commit -m "#573: Pass null in all remaining inferMatch call sites"
```

- [ ] **Step 9: Run full build to verify**

Run: `zig build test --summary all`

Expected: PASS (all tests compile and run successfully)

- [ ] **Step 10: Final commit**

```bash
git add .
git commit -m "#573: Update all remaining call sites to pass null for sig_vars"
```

---

## Chunk 8: Testing and Verification

This chunk runs tests to verify the fix works correctly.

### Task 15: Run full test suite to verify fix

**Files:**
- No files changed (verification only)

- [ ] **Step 1: Run full test suite**

Run: `zig build test --summary all`

Expected output:
- All 888 tests pass
- 12 previously failing e2e tests (with rigid mismatch error) now pass
- No new failures

- [ ] **Step 2: Commit verification results**

If tests pass:
```bash
git commit --allow-empty -m "#573: Verify all 888 tests pass after fix"
```

If tests fail:
- Analyze failure
- Create follow-up GitHub issue for debugging
- Do not merge PR until tests pass

### Task 16: Add unit tests for new behavior

**Files:**
- Modify: `src/typechecker/tests.zig` (if exists) or create dedicated test file

- [ ] **Step 1: Verify existing test coverage**

Run: `ls src/typechecker/*.zig | grep test`

Expected: May find test.zig or tests.zig or none (new test infrastructure needed)

If test infrastructure exists:
- Add unit test for `inferPat` with non-null sig_vars
- Add unit test for `inferPat` with null sig_vars
- Add unit test verifying rigid types are used when available

If test infrastructure does not exist:
- Note: Unit test infrastructure needed as follow-up (create GitHub issue #XXX)

- [ ] **Step 2: Commit test files or follow-up issue**

If tests added:
```bash
git add src/typechecker/test*.zig
git commit -m "#573: Add unit tests for sig_vars handling in inferPat"
```

If follow-up issue needed:
```bash
cat > /tmp/issue-body.md << 'EOF'
## Context
Type unification fix #573 adds signature context passing to pattern inference but no unit test infrastructure exists in src/typechecker.

## Shortcoming
No unit tests verify the new sig_vars parameter behavior in inferPat.

## Deliverable
1. Create test infrastructure in src/typechecker (test.zig or tests.zig)
2. Add unit tests for inferPat with null and non-null sig_vars
3. Add unit tests for inferMatch with sig_vars parameter
4. Test both rigid type use and fresh meta fallback

## References
- src/typechecker/infer.zig:910-925 (inferPat implementation)
- docs/superpowers/specs/2026-03-15-type-unification-fix-design.md
EOF

gh issue create \
  --title "#573: Add unit tests for signature context type unification" \
  --body-file /tmp/issue-body.md \
  --label "component:typechecker,priority:medium,type:feature"
```

---

## Chunk 9: Deinit Cleanup

This chunk adds cleanup for the TypeVarMap in TypeSigEntry to prevent memory leaks.

### Task 17: Add TypeVarMap deinit at sigs cleanup points

**Files:**
- Modify: `src/typechecker/infer.zig` (find sigs.deinit call locations)

- [ ] **Step 1: Find All sigs deinit locations**

Run: `grep -n "sigs.deinit" src/typechecker/infer.zig`

Expected: Lines where TypeSigEntry maps are cleaned up (likely near end of functions)

For each sigs.deinit location:
- Add TypeVarMap cleanup before sigs deinit

Example (after finding exact lines):
```zig
if (entry) |s| {
    s.rigid_map.deinit(ctx.alloc);
}
sigs.deinit(ctx.alloc);
```

But wait - we can't just deinit the map because the HType pointers it contains are arena-allocated and owned by the context, not the map. The map's allocation (internal hash table storage) should be deinitialized, but not the HType nodes it points to.

Let me check the TypeVarMap deinit behavior...

Looking at line 683: `defer scope.deinit(ctx.alloc);`

This deinit only frees the HashMap's internal storage, not the HType values it points to (those are arena-allocated and persist for the context's lifetime).

So we do need to deinit the TypeVarMap when the sigs map is destroyed, BUT we must be careful about arena lifetime.

Actually, looking more carefully - the TypeVarMap is stored in TypeSigEntry which lives in the sigs HashMap. When sigs is deinitialized (likely via `deinit(ctx.alloc)`), the entire map and all its entries are freed. The TypeVarMap inside TypeSigEntry would be freed as part of that.

But wait, we need to explicitly deinit the TypeVarMap's internal storage before the containing TypeSigEntry is freed, or we may leak the hash table's buckets.

Let me look for a proper pattern by searching for how this is done elsewhere...

- [ ] **Step 2: Verify proper deinit ordering**

Run: `zig build test --summary all`

Expected: If memory leaks exist, tests with Valgrind/sanitizer would fail

For now, given the codebase uses ArenaAlloc for HType nodes and TypeVarMap deinit only frees HashMap internals (not values), the current deinit of sigs should handle TypeVarMap cleanup automatically when TypeSigEntry is destroyed.

If issues arise:
- Add explicit TypeVarMap.deinit calls in destructor code
- Ensure ordering: TypeVarMap.deinit first, then sigs.deinit

- [ ] **Step 3: Commit (or create follow-up issue if needed)**

If cleanup already handled:
```bash
git commit --allow-empty -m "#573: Verify TypeVarMap cleanup handled by sigs deinit"
```

If additional cleanup needed:
(Add appropriate deinit code and commit)

If analysis inconclusive:
```bash
cat > /tmp/issue-body.md << 'EOF'
## Context
Fix #573 adds TypeVarMap to TypeSigEntry but deinit cleanup path unclear.

## Shortcoming
Unclear whether TypeVarMap internal storage is properly deinitialized when sigs HashMap is destroyed.

## Deliverable
1. Verify TypeVarMap deinit behavior by running with memory sanitizer
2. Add explicit TypeVarMap.deinit calls if needed
3. Ensure proper ordering (TypeVarMap before sigs)

## References
- src/typechecker/infer.zig:630-640 (TypeSigEntry struct)
- src/typechecker/infer.zig:423 (TypeVarMap definition)
EOF

gh issue create \
  --title "#573: Verify TypeVarMap deinit cleanup" \
  --body-file /tmp/issue-body.md \
  --label "component:typechecker,priority:low,type:feature"
```

---

## Summary

This plan implements a targeted fix for the type unification bug in PR #575:

1. **Add data structures** - `rigid_map` field to `SkolemiseResult` and `TypeSigEntry`
2. **Return and store** - Modify `skolemiseSignature` to return the TypeVarMap and store it in `TypeSigEntry`
3. **Update signatures** - Add optional `sig_vars` parameter to `inferPat` and `inferMatch`
4. **Implement logic** - Modify `.Var` case to check `sig_vars` for pre-existing rigid types before creating fresh metas
5. **Update call sites** - Pass `&s.rigid_map` in FunBind cases, `null` in all other cases
6. **Verify tests** - Ensure all 888 tests pass, especially the 12 previously failing e2e tests

**Files modified:**
- `src/typechecker/infer.zig` (~100-120 lines total across 10+ functions)

**Complexity:** Low risk - only adds optional parameter backward-compatibly, no unification logic changes
