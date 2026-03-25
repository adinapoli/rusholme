# TagRegistry Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the rebuilt-per-compilation TagTable with a persistent, append-only TagRegistry to structurally prevent discriminant drift.

**Architecture:** Extract TagRegistry into its own file. GrinTranslator takes `*TagRegistry` (not owned). JitEngine owns a persistent TagRegistry. Batch compiler creates a local one.

**Tech Stack:** Zig, LLVM ORC JIT

**Spec:** `docs/superpowers/specs/2026-03-25-tag-registry-design.md`

---

### Task 1: Create `tag_registry.zig` — extract TagRegistry

**Files:**
- Create: `src/backend/tag_registry.zig`
- Modify: `src/backend/grin_to_llvm.zig` (remove TagTable, import TagRegistry)

- [ ] **Step 1: Create tag_registry.zig with TagRegistry struct**

Move from `grin_to_llvm.zig` lines 293-576 (TagTable → TagRegistry):
- All fields (discriminants, field_counts, field_types, fun_tags, fun_tag_names, partial_tags, partial_tag_info, con_name_to_disc, next)
- `PartialTagInfo` struct
- `first_discriminant` constant
- `init()`, `deinit()`, `clone()`
- `tagKey()`, `register()`, `discriminant()`, `fieldCount()`, `fieldTypes()`
- `isNullaryByName()`, `discriminantByName()`, `findByName()`
- `ensureListConstructors()`, `registerIntermediatePartialTags()`

Move from `grin_to_llvm.zig`:
- `scanExprForTags` (lines 613-639)
- `scanValForTags` (lines 641-660+)
- `buildTagTable` (lines 579-611) → rename to `buildRegistry`

Add new methods:
- `registerDefsAndBodies(alloc, defs)` — scan bodies + F-tag pre-register + ensureListConstructors + registerIntermediatePartialTags
- `registerFieldTypes(alloc, field_types_map)` — merge program field types
- `getKnownDiscriminants() KnownTags` — extract True/False/Nil/Cons/etc. discriminants

Import dependencies: `grin/ast.zig` for Def/Tag/Expr/Name types, `naming/known.zig` for well-known unique IDs.

- [ ] **Step 2: Update grin_to_llvm.zig to import TagRegistry**

Replace `TagTable` references with `tag_registry.TagRegistry`. Remove the old struct and helpers. Add `const tag_registry = @import("tag_registry.zig");` and `pub const TagRegistry = tag_registry.TagRegistry;` re-export.

- [ ] **Step 3: Build and fix compilation errors**

Run: `nix develop --command zig build 2>&1 | head -30`

- [ ] **Step 4: Commit**

```
git add src/backend/tag_registry.zig src/backend/grin_to_llvm.zig
git commit -m "#636: Extract TagRegistry from TagTable into tag_registry.zig"
```

---

### Task 2: Update GrinTranslator to use `*TagRegistry`

**Files:**
- Modify: `src/backend/grin_to_llvm.zig`

- [ ] **Step 1: Change GrinTranslator fields and init**

- `tag_table: TagTable` → `registry: *TagRegistry`
- Remove `extra_tag_defs` field
- `init(allocator, registry: *TagRegistry)` — store the pointer
- `deinit()` — remove `self.tag_table.deinit()` (not owned)
- `getKnownTagDiscriminants` → delegate to `self.registry.getKnownDiscriminants()`

- [ ] **Step 2: Update translateProgramToModule**

Remove Phase 1-4 scanning (the pre-seeded check and all extra_tag_defs loops). Keep:
- field_types merge → `self.registry.registerFieldTypes(alloc, program.field_types)`
- TypeEnv link → `self.type_env.setRegistry(self.registry)`
- arity_map link
- Partial tag pre-registration → `self.registry.registerIntermediatePartialTags()` (belt-and-suspenders)
- Force/apply emission
- Def translation loop

- [ ] **Step 3: Remove prepareGlobalTagTable**

Delete the entire method. Callers will use `registry.registerDefsAndBodies()`.

- [ ] **Step 4: Update translateModuleGrin**

Replace `self.tag_table` with `self.registry` throughout. The `TypeEnv.setTagTable` → `setRegistry`.

- [ ] **Step 5: Update emitForceModule and emitForceModuleIr**

Replace `self.tag_table` with `self.registry`.

- [ ] **Step 6: Update all remaining self.tag_table references**

Global find-replace `self.tag_table` → `self.registry` in translateDef, translateCase, translateApp, emitCstringToCharlist, and all other methods in GrinTranslator.

- [ ] **Step 7: Update TypeEnv**

`tag_table: *const TagTable` → `registry: *const TagRegistry`
`setTagTable` → `setRegistry`
`fieldTypeForTag` updated to use registry.

- [ ] **Step 8: Build and fix**

- [ ] **Step 9: Commit**

```
git commit -m "#636: Update GrinTranslator to take *TagRegistry, remove tag scanning"
```

---

### Task 3: Update JitEngine

**Files:**
- Modify: `src/repl/jit_engine.zig`

- [ ] **Step 1: Replace fields**

- `base_tag_table: TagTable` → `registry: TagRegistry` (owned)
- Remove `accumulated_grin_defs`
- Update `deinit()`: `self.registry.deinit(alloc)`, remove accumulated_grin_defs.deinit

- [ ] **Step 2: Update addDeclarations**

- Remove `accumulated_grin_defs.append` loop
- Replace pre-seed/clone logic with: `self.registry.registerDefsAndBodies(alloc, program.defs)`
- `self.registry.registerFieldTypes(alloc, program.field_types)`
- `self.known_tags = self.registry.getKnownDiscriminants()`
- Create translator: `GrinTranslator.init(self.allocator, &self.registry)`
- Remove `translator.extra_tag_defs = ...`
- Remove `translator.prepareGlobalTagTable(...)` call
- Remove post-compilation `base_tag_table.clone()` save

- [ ] **Step 3: Update execute**

- Remove pre-seed/clone logic
- `self.registry.registerDefsAndBodies(alloc, program.defs)`
- `self.registry.registerFieldTypes(alloc, program.field_types)`
- Create translator: `GrinTranslator.init(self.allocator, &self.registry)`
- Remove `translator.extra_tag_defs = ...`
- `self.known_tags = self.registry.getKnownDiscriminants()`
- Force re-emit check: compare against `self.registry.fun_tags` directly

- [ ] **Step 4: Update emitSharedForceModule**

Pass translator that already holds `*TagRegistry`. The force module reads from the registry directly.

- [ ] **Step 5: Build and fix**

- [ ] **Step 6: Commit**

```
git commit -m "#636: Update JitEngine to use persistent TagRegistry"
```

---

### Task 4: Update batch compiler call sites

**Files:**
- Modify: `src/main.zig` (4 sites), `src/backend/native.zig`, `src/backend/wasm.zig`

- [ ] **Step 1: Update cmdLl (main.zig ~line 712)**

```zig
var registry = TagRegistry.init();
defer registry.deinit(arena_alloc);
registry.registerDefsAndBodies(arena_alloc, grin_prog.defs);
registry.registerFieldTypes(arena_alloc, grin_prog.field_types);
var translator = GrinTranslator.init(arena_alloc, &registry);
```

- [ ] **Step 2: Update emitNative (main.zig ~line 970)**

Same pattern. Replace `prepareGlobalTagTable` + `translateModuleGrin` with registry pre-registration + translate.

- [ ] **Step 3: Update emitJit (main.zig ~line 1121)**

Same pattern.

- [ ] **Step 4: Update emitWasm (main.zig ~line 1276)**

Same pattern.

- [ ] **Step 5: Update native.zig (line 22)**

Same pattern with local registry.

- [ ] **Step 6: Update wasm.zig (line 31)**

Same pattern with local registry.

- [ ] **Step 7: Build and fix**

- [ ] **Step 8: Commit**

```
git commit -m "#636: Update batch compiler call sites to use TagRegistry"
```

---

### Task 5: Move tests and verify

**Files:**
- Modify: `src/backend/tag_registry.zig` (add tests)
- Modify: `src/backend/grin_to_llvm.zig` (update translator tests)

- [ ] **Step 1: Move TagTable tests to tag_registry.zig**

Move test blocks from grin_to_llvm.zig:
- "TagTable: register and discriminant"
- "TagTable: isNullaryByName"
- "TagTable: idempotent re-registration"
- "TagTable: composite keying..."
- "TagTable: P(1) and P(2)..."
- "TagTable: registerIntermediatePartialTags..."

Rename "TagTable" → "TagRegistry" in test names.

- [ ] **Step 2: Update GrinTranslator tests**

Tests at lines ~3797, ~3941, ~3986 create `GrinTranslator.init(alloc)`.
Change to: create local `TagRegistry`, call `registerDefsAndBodies`, pass `&registry` to `GrinTranslator.init(alloc, &registry)`.

- [ ] **Step 3: Run full test suite**

Run: `nix develop --command zig build test --summary all`
Expected: All tests pass.

- [ ] **Step 4: Commit**

```
git commit -m "#636: Move TagTable tests to tag_registry.zig, update translator tests"
```

---

### Task 6: Clean up dead code

- [ ] **Step 1: Remove TagTable struct** (should already be gone after Task 1-2)
- [ ] **Step 2: Remove clone() from TagTable** (moved to TagRegistry)
- [ ] **Step 3: Remove any remaining extra_tag_defs references**
- [ ] **Step 4: Final build + test**
- [ ] **Step 5: Commit**

```
git commit -m "#636: Remove dead TagTable code"
```
