# Per-Module LLVM Bitcode Artifacts — Design (Issue #436)

Date: 2026-03-01

## Problem

`cmdBuild` currently produces a single temp `.o` file and immediately deletes it
after linking.  For multi-module compilation we need durable, per-module backend
artifacts so that future recompilation avoidance (#371) can skip unchanged modules.

## Decision

Use **LLVM bitcode (`.bc`)** as the per-module durable artifact, mirroring the
per-module `.rhi` interface files already produced by `CompileEnv`.

## Architecture

### Build artifact layout

```
Foo.hs  →  compile  →  Foo.rhi   (typechecker interface, #366)
                    →  Foo.bc    (LLVM bitcode for the linker)
```

### Multi-module link flow

```
Foo.bc  ─┐
Bar.bc  ─┤─► LLVMLinkModules2 (in-process LLVM linker)
Baz.bc  ─┘         │
                    ▼
              linked.bc  ─► LLVMTargetMachineEmitToFile ─► program.o
                                                               │
                                                 cc + rts.a ──► program
```

We use **LLVM's in-process linker** (`LLVMLinkModules2` from `llvm-c/Linker.h`,
already included in `llvm.zig`) rather than spawning an external `llvm-link`
process.  Benefits: no external tool dependency, same link-time optimisation
semantics, uses an API already available in the codebase.

### Per-module GRIN→LLVM translation

**Challenge:** the global `TagTable` must be built from ALL modules' constructors
(since module B may pattern-match on a constructor from module A).  TypeEnv
similarly requires the full tag table.

**Solution:**
1. Lambda-lift and GRIN-translate each module's `CoreProgram` separately.
2. Merge all GRIN programs into one **for tag table construction only**.
3. Call `GrinTranslator.prepareGlobalTagTable(merged_prog)` — stores the global
   TagTable in the translator.
4. For each module: call `GrinTranslator.translateModuleGrin(module_name, prog)`.
   This temporarily swaps `self.module` so all `translateDef` calls land in the
   per-module LLVM module.  Cross-module function calls become `declare` stubs
   (via the existing `LLVMGetNamedFunction` + `LLVMAddFunction` lazy pattern).
5. Write each LLVM module to `<module_name>.bc` via `LLVMWriteBitcodeToFile`.
6. Merge all LLVM modules in-process, emit `.o`, link.

### Changes required

| File | Change |
|------|--------|
| `src/backend/llvm.zig` | Add `writeBitcodeToFile`, add `linkModules` |
| `src/backend/grin_to_llvm.zig` | Add `prepareGlobalTagTable`, `translateModuleGrin` |
| `src/modules/compile_env.zig` | Return `module_order` from `CompileResult` |
| `src/main.zig` — `cmdBuild` | Per-module lambda-lift → GRIN → LLVM → BC flow |
| `BUILDING.md` | Document `.rhi` + `.bc` artifact model |

## Known limitations (follow-up issues)

- The TypeEnv `var_types` accumulates cross-module variable type annotations.
  Since each variable has a globally unique `unique.value`, this is harmless but
  wastes memory.  Clearing per-module would reduce peak usage.
- Per-module `.bc` files are written to the current working directory.  A proper
  build cache path (under `_build/` or alongside the source file) is deferred to
  the recompilation avoidance issue (#371).
