# Design: Language Extension Set and Module Parse Cache

**Date**: 2026-02-28
**Status**: Approved
**Addresses**: Three anti-patterns identified in PR #441 review

---

## Context

PR #441 (implicit Prelude import) introduced `hasNoImplicitPrelude`, a function
that scans raw source bytes to detect `{-# LANGUAGE NoImplicitPrelude #-}`. The
review identified this as symptomatic of a broader architectural gap: there is no
single, authoritative, parsed representation of a module's enabled language
extensions that all compilation phases can query.

Three concrete anti-patterns were found:

1. **`hasNoImplicitPrelude`** (`compile_env.zig`) — raw byte scan on every call,
   no caching, workaround for a lexer bug.
2. **`parseImportNames`** (`compile_env.zig`) — full lex/layout/parse of every
   module just to extract import names for the dependency graph, immediately
   followed by `compileSingle` parsing the same source again.
3. **`parseImportHeaders`** (`module_graph.zig`) — same full-parse-for-imports
   pattern in the file-based discovery path.

The root cause of (1) is a one-line bug in `Lexer.skipWhitespaceAndComments`
that causes `{-# ... #-}` to be consumed as a block comment before `nextToken`
can emit `pragma_open`. The root cause of (2) is the absence of a module parse
cache in `CompileEnv`.

---

## Goals

- **Make impossible states unrepresentable**: once a `Module` exists, its enabled
  extensions are known and queryable. There is no other way to ask.
- **O(1) extension queries** via `std.EnumSet(LanguageExtension)` (a compile-time
  bitmask — strictly better than the O(log n) lower bound).
- **Single parse per module** in `compileProgram`: build the dependency graph and
  run the compilation pipeline from the same `ast_mod.Module` value.
- **Delete dead workarounds**: `hasNoImplicitPrelude` and `parseImportNames`
  are gone entirely.

---

## Design

### 1. AST (`src/frontend/ast.zig`)

Add a `LanguageExtension` enum listing every extension Rusholme understands.
Unknown extensions encountered in source emit a `warning` diagnostic (with span)
rather than being silently ignored.

```zig
pub const LanguageExtension = enum {
    NoImplicitPrelude,
    TypeApplications,
    OverloadedStrings,
    ScopedTypeVariables,
    // ... add new variants as new issues require them
};
```

Extend `Module` with an inline bitmask field:

```zig
pub const Module = struct {
    module_name:         []const u8,
    exports:             ?[]const ExportSpec,
    imports:             []const ImportDecl,
    declarations:        []const Decl,
    language_extensions: std.EnumSet(LanguageExtension),  // NEW
    span:                SourceSpan,
};
```

`std.EnumSet` is backed by a comptime-sized integer — no heap allocation, embeds
inline in `Module`. Adding a new variant to `LanguageExtension` automatically
widens the backing integer; no call-site changes are needed.

**Query pattern** throughout the pipeline:
```zig
if (module.language_extensions.contains(.NoImplicitPrelude)) { ... }
```

### 2. Lexer fix (`src/frontend/lexer.zig`)

`skipWhitespaceAndComments` enters block-comment mode when it sees `{-`, without
checking whether the next character is `#`. Fix: peek one character further; if
it is `#`, break out of the skip loop and let `nextToken` handle the pragma.

```zig
// Before entering block-comment mode:
if (self.peekAt(2) == '#') break; // pragma — let nextToken emit pragma_open
```

The `pragma_open` / `pragma_close` / `kw_LANGUAGE` tokens already exist in the
lexer and are correct; they were simply unreachable. This one-line fix makes them
live.

### 3. Parser (`src/frontend/parser.zig`)

`parseModule` gains a pragma-collection phase before the module header:

```
parseLangPragmas → parseModuleHeader → parseImports → parseDecls
```

**`parseLangPragmas`** (private helper):
- Loops while `peek() == .pragma_open`
- Per pragma: consume `pragma_open`, expect `kw_LANGUAGE`, parse
  comma-separated `conid` tokens, consume `pragma_close`
- For each extension name: look up in a comptime `std.StaticStringMap(LanguageExtension)`;
  if found → `set.insert(ext)`; if not found → emit `warning` diagnostic with the
  name's `SourceSpan`
- Returns the accumulated `std.EnumSet(LanguageExtension)`

The accumulated set is stored on the returned `Module`. By the time any phase
downstream of the parser holds a `Module`, `language_extensions` is complete and
authoritative.

### 4. `CompileEnv` parse cache (`src/modules/compile_env.zig`)

Add to `CompileEnv`:
```zig
parsed_modules: std.StringHashMapUnmanaged(ast_mod.Module),
```

Keys are duped module-name strings owned by the map. Values are `ast_mod.Module`
values whose arena-allocated internals live in `CompileEnv`'s allocator.

**`compileProgram` — three clean phases**:

```
Phase 1 — Parse every SourceModule once; store in parsed_modules cache.
Phase 2 — Build ModuleGraph from cached module.imports (no re-parse).
Phase 3 — Topo sort; drive compileSingle(cached_module) in order.
```

`parseImportNames` is deleted. The graph is built by reading `module.imports`
from the cache — the same `ImportDecl` slice, zero redundant lexing.

**`compileSingle` signature**:
```zig
pub fn compileSingle(
    self: *CompileEnv,
    module_name: []const u8,
    source: []const u8,
    file_id: span_mod.FileId,
    parsed: ?ast_mod.Module,   // NEW: pass cached parse or null for fresh parse
) std.mem.Allocator.Error!?*ModIface
```

When `parsed` is non-null, the lex/layout/parse step is skipped. Standalone
callers (tests, future REPL) pass `null`.

**`hasNoImplicitPrelude` deleted**. Its call site becomes:
```zig
module.language_extensions.contains(.NoImplicitPrelude)
```

### 5. `module_graph.zig` — left as-is with a follow-up issue

`parseImportHeaders` serves the file-based module discovery path, which is
distinct from `compileProgram`'s in-memory flow. Its results are not immediately
reused by the compilation pipeline. It is left unchanged for now; a follow-up
issue tracks unifying it with the `CompileEnv` cache.

---

## What is NOT in scope

- Recompilation avoidance (tracked in #371)
- Making `parseImportHeaders` use the cache (follow-up issue filed during PR prep)
- Changes to the renamer or typechecker — they receive `Module` unchanged

---

## Testing

- Unit tests for `parseLangPragmas`: known extension, unknown extension (expect
  warning diagnostic), multiple pragmas, pragma before `module` keyword.
- `EnumSet` query tests: `contains`, `setUnion`, empty set.
- Integration test: module with `{-# LANGUAGE NoImplicitPrelude #-}` compiles
  without injecting Prelude; module without it does inject.
- Regression: all 741 existing tests continue to pass.
