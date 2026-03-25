# #636: TagRegistry — Persistent Discriminant Registry

## Problem

`TagTable` conflates two roles: (1) a persistent registry that assigns
discriminants to tags, and (2) a transient compilation context that provides
field types and tag sets for a specific translation pass. Because
`GrinTranslator` owns and rebuilds the tag table from scratch for each
compilation, discriminants can shift when `extra_tag_defs` grows — causing
segfaults (#631, #637). The current workaround (`base_tag_table` clone +
pre-seed) is correct but opt-in: a new caller can forget to pre-seed and
reintroduce the bug.

## Key Invariant

**Once a tag receives a discriminant, it never changes.** Enforced
structurally by an append-only registry — not by caller discipline.

**Field type refinement caveat:** `field_types` can be refined by later
compilations (ptr → i64, etc.). This is safe for code compiled *after*
the refinement but not retroactively for already-JIT'd code. In the
REPL this is fine since each expression is freshly compiled; the batch
compiler compiles everything in one pass. Document this constraint in
the registry's `register` doc comment.

## Design

### New struct: `TagRegistry`

File: `src/backend/tag_registry.zig`

Owns all discriminant assignments and tag metadata. Created once per
session (REPL) or once per compilation (batch). Never rebuilt.

```
TagRegistry
  discriminants    : AutoHashMap(u64, i64)     — tagKey → discriminant
  field_counts     : AutoHashMap(u64, u32)     — tagKey → field count
  field_types      : AutoHashMap(u64, []FieldType) — tagKey → per-field types
  fun_tags         : AutoHashMap(u64, void)    — set of F-tag keys
  fun_tag_names    : AutoHashMap(u64, grin.Name) — F-tag key → GRIN name
  partial_tags     : AutoHashMap(u64, void)    — set of P-tag keys
  partial_tag_info : AutoHashMap(u64, PartialTagInfo)
  con_name_to_disc : StringHashMap(i64)        — base name → discriminant
  next             : i64                       — next discriminant to assign
```

**Public API:**

| Method | Purpose |
|--------|---------|
| `init() TagRegistry` | Empty registry, `next = 0x1000` |
| `deinit(alloc)` | Free all owned memory |
| `register(alloc, tag, n_fields)` | Assign discriminant if new; no-op if exists. Public for tests and programmatic registration. |
| `registerDefsAndBodies(alloc, defs)` | Scan bodies + pre-register F-tags + ensure list ctors + intermediate P-tags. Idempotent. Primary entry point. |
| `registerFieldTypes(alloc, field_types_map)` | Merge program-specific field types into the registry. Consolidates the duplicate merge logic from `buildTagTable` and `translateProgramToModule`. |
| `discriminant(tag) ?i64` | Look up by tag key |
| `findByName(base) ?i64` | Look up C-tag by constructor base name |
| `fieldCount(tag) ?u32` | Field count by tag key |
| `fieldTypes(tag) ?[]FieldType` | Field types by tag key |
| `isNullaryByName(name) bool` | Check if constructor is nullary |
| `discriminantByName(name) ?i64` | Look up discriminant by constructor name |
| `getKnownDiscriminants() KnownTags` | Extract well-known constructor discriminants (True, False, [], (:), etc.) for result formatting |
| `tagKey(tag) u64` | Composite key (static, pub) |

`register()` is append-only for discriminants: once assigned, a tag's
discriminant never changes.

`registerDefsAndBodies` replaces the 4-phase scan logic. It:
1. Scans each def's body via `scanExprForTags`
2. Pre-registers each def with `params.len > 0` as an F-tag
3. Calls `ensureListConstructors`
4. Calls `registerIntermediatePartialTags` until stable

Callers call it once per batch of new defs. Idempotent — safe to call
with overlapping def sets.

`registerFieldTypes` replaces the field_types merge blocks that
currently exist in both `buildTagTable` (lines 588-608) and
`translateProgramToModule` (lines 978-991). One method, one place.

### Internal helpers (moved from `grin_to_llvm.zig`)

- `scanExprForTags(alloc, expr, registry)` — recursive body scanner
- `scanValForTags(alloc, val, registry)` — value scanner
- `buildRegistry(alloc, program)` — convenience that creates a registry, calls `registerDefsAndBodies` + `registerFieldTypes`, returns it. Used by batch path.
- `ensureListConstructors` — ensures `[]` and `(:)` are registered
- `registerIntermediatePartialTags` — creates P(n-1) chains

### Changes to `GrinTranslator`

File: `src/backend/grin_to_llvm.zig`

```
GrinTranslator
  registry: *TagRegistry   ← shared reference, not owned
  ...everything else unchanged...
```

- `init(allocator, registry: *TagRegistry)` — always requires a registry
- `deinit()` — no longer frees tag table (not owned)
- `tag_table` field removed; all `self.tag_table.X` → `self.registry.X`
- `extra_tag_defs` field removed — the registry already holds all tags
- `translateProgramToModule` — removes Phase 1-4 scanning; only translates defs, emits force/apply declarations, links TypeEnv. Callers must pre-populate the registry.
- `translateProgram` — thin wrapper around `translateProgramToModule` + `printModuleToString`. Same pre-population requirement as `translateProgramToModule`. Callers (batch `cmdLl` and tests) must call `registry.registerDefsAndBodies` first.
- `prepareGlobalTagTable` — removed entirely (callers use `registry.registerDefsAndBodies`)
- `clone()` on TagTable — removed (no longer needed)
- `getKnownTagDiscriminants` — moves to `TagRegistry.getKnownDiscriminants`. `JitEngine` can call it directly on the registry without a translator.
- `TypeEnv.tag_table` → `TypeEnv.registry: *const TagRegistry`
- Field types merge in `translateProgramToModule` preamble → calls `registry.registerFieldTypes(alloc, program.field_types)`

### Changes to `JitEngine`

File: `src/repl/jit_engine.zig`

```
JitEngine
  registry: TagRegistry          ← owned, persistent, append-only
  accumulated_grin_defs: ...     ← REMOVED
  base_tag_table: ...            ← REMOVED
```

**Why `accumulated_grin_defs` can be removed:** it was only consumed by
(a) the tag scanning phases in `translateProgramToModule` (via
`extra_tag_defs`), and (b) force module emission (via
`translator.tag_table.fun_tags`). Both now read directly from the
persistent registry, making the separate def accumulation redundant.

- `init()` — creates `registry = TagRegistry.init()`
- `deinit()` — calls `self.registry.deinit(alloc)`
- `addDeclarations(program)`:
  1. `self.registry.registerDefsAndBodies(alloc, program.defs)`
  2. `self.registry.registerFieldTypes(alloc, program.field_types)`
  3. `self.known_tags = self.registry.getKnownDiscriminants()`
  4. Create translator with `&self.registry`
  5. Emit shared force module, translate and add per-def modules
- `execute(program)`:
  1. `self.registry.registerDefsAndBodies(alloc, program.defs)`
  2. `self.registry.registerFieldTypes(alloc, program.field_types)`
  3. `self.known_tags = self.registry.getKnownDiscriminants()`
  4. Create translator with `&self.registry`
  5. Translate, check force re-emit, JIT, execute
- `emitSharedForceModule` — uses `self.registry` directly (via translator that holds `*TagRegistry`)
- `force_ftag_uniques` — compared against `self.registry.fun_tags`

### Changes to batch compiler

Files: `src/main.zig`, `src/backend/native.zig`, `src/backend/wasm.zig`

Each call site creates a local registry:

```zig
var registry = TagRegistry.init();
defer registry.deinit(alloc);
registry.registerDefsAndBodies(alloc, all_grin.defs);
registry.registerFieldTypes(alloc, all_grin.field_types);

var translator = GrinTranslator.init(alloc, &registry);
defer translator.deinit();
```

4 call sites in `main.zig`:
- `cmdLl` — currently uses `translateProgram` (no explicit `prepareGlobalTagTable`). After refactor: create registry, register, then call `translateProgram`.
- `compileNative` — currently uses `prepareGlobalTagTable` + `translateModuleGrin`. After refactor: create registry, register, then translate.
- `compileJitModule` — same pattern as `compileNative`.
- `compileWasm` — same pattern.

1 in `native.zig`, 1 in `wasm.zig` — same pattern.

### Test updates

- `TagTable` unit tests in `grin_to_llvm.zig` → `TagRegistry` unit tests in `tag_registry.zig`
- `GrinTranslator` tests (3 in `grin_to_llvm.zig`) create a local `TagRegistry`, call `registerDefsAndBodies`, pass `&registry` to translator
- `translateProgram` callers in tests must pre-register before calling
- REPL regression test from #637 continues to pass unchanged

## Call-site inventory

| File | Call sites | Change |
|------|-----------|--------|
| `grin_to_llvm.zig` | `GrinTranslator.init` (3 tests) | Create local registry, pass `&registry` |
| `jit_engine.zig` | `GrinTranslator.init` (2: addDecl, execute) | Pass `&self.registry` |
| `main.zig` | `GrinTranslator.init` (4: cmdLl, compileNative, compileJitModule, compileWasm) | Create local registry, pass `&registry` |
| `native.zig` | `GrinTranslator.init` (1) | Create local registry, pass `&registry` |
| `wasm.zig` | `GrinTranslator.init` (1) | Create local registry, pass `&registry` |

## Migration order

1. Create `src/backend/tag_registry.zig` — extract `TagRegistry` struct with all fields, `register()`, lookup methods, `registerDefsAndBodies`, `registerFieldTypes`, `getKnownDiscriminants`, `scanExprForTags`, `scanValForTags`, `buildRegistry`
2. Update `GrinTranslator`:
   a. Change `init` to accept `*TagRegistry` instead of owning `TagTable`
   b. Replace all `self.tag_table.X` references with `self.registry.X`
   c. Remove tag scanning from `translateProgramToModule` (Phases 1-4)
   d. Remove `prepareGlobalTagTable`
3. Update `TypeEnv` — `tag_table: *const TagTable` → `registry: *const TagRegistry`
4. Update `JitEngine` — replace `base_tag_table` + `accumulated_grin_defs` + `extra_tag_defs` with owned `TagRegistry`
5. Update batch compiler call sites (main.zig, native.zig, wasm.zig)
6. Move tests to `tag_registry.zig`, update translator tests, verify all pass
7. Remove dead code (`TagTable`, `clone`, `extra_tag_defs` field)
