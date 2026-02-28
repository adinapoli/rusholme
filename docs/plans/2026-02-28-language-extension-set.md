# Language Extension Set Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace three redundant raw-scan / double-parse anti-patterns with a single `std.EnumSet(LanguageExtension)` field on `ast_mod.Module`, computed once per parse, queryable in O(1) by all downstream pipeline stages.

**Architecture:** Fix a one-line lexer bug so `{-# LANGUAGE … #-}` emits real pragma tokens; teach the parser to collect those tokens into a `std.EnumSet(LanguageExtension)` stored on `Module`; cache parsed modules in `CompileEnv` so the dependency-graph builder and the compiler never parse the same source twice; delete `hasNoImplicitPrelude` and `parseImportNames` entirely.

**Tech Stack:** Zig 0.14, `std.EnumSet`, `std.StaticStringMap`, `nix develop --command zig build test --summary all`

---

## Task 0: File the GitHub issue and create the feature branch

**Files:** none

**Step 1: Write the issue body to a temp file**

```bash
cat > /tmp/issue-body.md << 'EOF'
## Context

PR #441 introduced `hasNoImplicitPrelude`, which scans raw source bytes on every
call to detect `{-# LANGUAGE NoImplicitPrelude #-}`. Code review identified this
as symptomatic of three architectural anti-patterns:

1. **`hasNoImplicitPrelude`** (`compile_env.zig`) — raw byte scan, no caching,
   workaround for a bug in `Lexer.skipWhitespaceAndComments`.
2. **`parseImportNames`** (`compile_env.zig`) — full lex/layout/parse of every
   module to extract import names for the dependency graph, immediately before
   `compileSingle` parses the same source again.
3. **`parseImportHeaders`** (`module_graph.zig`) — same full-parse-for-imports
   pattern in the file-based discovery path.

The root cause of (1): `skipWhitespaceAndComments` consumes `{-#` as a block
comment, making the already-correct `pragma_open` token emission in `nextToken`
unreachable.

## Deliverables

- Fix `Lexer.skipWhitespaceAndComments` — do not consume `{-#` as a block comment
- Add `LanguageExtension` enum to `ast.zig`
- Add `Module.language_extensions: std.EnumSet(LanguageExtension)` to `ast.zig`
- Add `Parser.parseLangPragmas` — collects LANGUAGE pragmas into the `EnumSet`;
  emits a `warning` diagnostic (with span) for unrecognised extension names
- Add `CompileEnv.parsed_modules` cache; parse each module once in `compileProgram`
- Update `compileSingle` to accept a pre-parsed `?ast_mod.Module`
- Delete `hasNoImplicitPrelude` and `parseImportNames`
- All existing tests continue to pass; add targeted unit tests for each new piece

## References

- `src/frontend/lexer.zig` — `skipWhitespaceAndComments` (line 534), pragma tokens (line 427–461)
- `src/frontend/ast.zig` — `Module` struct (line 72)
- `src/frontend/parser.zig` — `parseModule` (line 537)
- `src/modules/compile_env.zig` — `CompileEnv`, `compileSingle`, `compileProgram`, `parseImportNames`
- `docs/plans/2026-02-28-language-extension-set-design.md` — approved design doc
EOF

gh issue create \
  --title "ast+parser: introduce LanguageExtension EnumSet and module parse cache" \
  --body-file /tmp/issue-body.md \
  --label "component:frontend,component:modules,priority:high,type:feature"
```

**Step 2: Note the issue number, create feature branch**

```bash
# Replace NNN with the issue number printed by the previous command
git checkout main
git pull
git checkout -b llm-agent/issue-NNN
```

---

## Task 1: Add `LanguageExtension` enum and extend `Module` in `ast.zig`

**Files:**
- Modify: `src/frontend/ast.zig:72-78`

**Step 1: Write the failing test (in `ast.zig` at the bottom)**

Add this `test` block at the end of `src/frontend/ast.zig`:

```zig
const testing = @import("std").testing;

test "LanguageExtension EnumSet: empty set contains nothing" {
    const set = std.EnumSet(LanguageExtension).initEmpty();
    try testing.expect(!set.contains(.NoImplicitPrelude));
    try testing.expect(!set.contains(.TypeApplications));
}

test "LanguageExtension EnumSet: insert and query" {
    var set = std.EnumSet(LanguageExtension).initEmpty();
    set.insert(.NoImplicitPrelude);
    try testing.expect(set.contains(.NoImplicitPrelude));
    try testing.expect(!set.contains(.TypeApplications));
}

test "LanguageExtension EnumSet: union" {
    var a = std.EnumSet(LanguageExtension).initEmpty();
    a.insert(.NoImplicitPrelude);
    var b = std.EnumSet(LanguageExtension).initEmpty();
    b.insert(.TypeApplications);
    a.setUnion(b);
    try testing.expect(a.contains(.NoImplicitPrelude));
    try testing.expect(a.contains(.TypeApplications));
}
```

**Step 2: Run tests to verify they fail**

```bash
nix develop --command zig build test --summary all 2>&1 | grep -E "FAIL|error|LanguageExtension"
```

Expected: compile error — `LanguageExtension` not declared.

**Step 3: Add `LanguageExtension` enum and update `Module`**

In `src/frontend/ast.zig`, add before `pub const Module`:

```zig
/// GHC/Haskell LANGUAGE extensions that Rusholme recognises.
///
/// Extensions encountered in source but not listed here cause the parser to
/// emit a `warning` diagnostic with the unrecognised name's `SourceSpan`.
/// Add new variants here as new issues require support for additional extensions.
pub const LanguageExtension = enum {
    NoImplicitPrelude,
    OverloadedStrings,
    ScopedTypeVariables,
    TypeApplications,
    // Add new variants here; std.EnumSet widens automatically.
};
```

Update `Module` to add the new field with a default (so existing struct literals
that omit it still compile):

```zig
pub const Module = struct {
    module_name:         []const u8,
    exports:             ?[]const ExportSpec,
    imports:             []const ImportDecl,
    declarations:        []const Decl,
    /// Extensions declared via `{-# LANGUAGE … #-}` pragmas in this module.
    /// Populated by the parser; authoritative for all downstream phases.
    /// Query with: `module.language_extensions.contains(.SomeExtension)`.
    language_extensions: std.EnumSet(LanguageExtension) = std.EnumSet(LanguageExtension).initEmpty(),
    span:                SourceSpan,
};
```

**Step 4: Run tests to verify they pass**

```bash
nix develop --command zig build test --summary all 2>&1 | tail -5
```

Expected: all tests pass (the three new ones included).

**Step 5: Commit**

```bash
git add src/frontend/ast.zig
git commit -m "#NNN: Add LanguageExtension enum and EnumSet field to Module"
```

---

## Task 2: Fix `Lexer.skipWhitespaceAndComments` to not eat `{-#`

**Files:**
- Modify: `src/frontend/lexer.zig:558-576`

**Step 1: Write the failing test (in `lexer.zig` at the bottom)**

Add this test block at the end of `src/frontend/lexer.zig`:

```zig
test "lexer: {-# ... #-} emits pragma_open, not consumed as block comment" {
    var lexer = Lexer.init(testing.allocator, "{-# LANGUAGE NoImplicitPrelude #-}", 0);
    const tok = lexer.nextToken();
    try testing.expectEqual(TokenTag.pragma_open, std.meta.activeTag(tok.token));
}

test "lexer: {- ... -} is still a block comment" {
    var lexer = Lexer.init(testing.allocator, "{- this is a comment -} foo", 0);
    const tok = lexer.nextToken();
    // The comment is skipped; first real token is `foo` (a varid)
    try testing.expectEqual(TokenTag.varid, std.meta.activeTag(tok.token));
}
```

**Step 2: Run tests to verify first test fails**

```bash
nix develop --command zig build test -- --test-filter "lexer: {-#" 2>&1
```

Expected: FAIL — `pragma_open` not emitted; block comment consumed instead.

**Step 3: Fix `skipWhitespaceAndComments`**

In `src/frontend/lexer.zig`, in the `skipWhitespaceAndComments` function, find
the block that handles `{` followed by `-` (around line 558). Add a pragma check
before entering block-comment mode:

```zig
'{' => {
    if (self.peekNext() == '-') {
        // Peek one further: {-# is a pragma open, not a block comment.
        // Let nextToken handle it.
        const after_dash = if (self.pos + 2 < self.source.len)
            self.source[self.pos + 2]
        else
            @as(u8, 0);
        if (after_dash == '#') break;

        // Block comment {- ... -}. Nested.
        _ = self.advance(); // {
        _ = self.advance(); // -
        var depth: usize = 1;
        // ... (rest unchanged)
    } else {
        break;
    }
},
```

**Step 4: Run all tests**

```bash
nix develop --command zig build test --summary all 2>&1 | tail -5
```

Expected: all tests pass.

**Step 5: Commit**

```bash
git add src/frontend/lexer.zig
git commit -m "#NNN: Fix skipWhitespaceAndComments to not consume {-# as block comment"
```

---

## Task 3: Add `Parser.parseLangPragmas` and wire it into `parseModule`

**Files:**
- Modify: `src/frontend/parser.zig:537-597`

**Step 1: Write the failing tests (in `parser.zig` at the bottom)**

```zig
test "parseLangPragmas: known extension populates EnumSet" {
    // Use a helper that drives a fresh parser on a source string.
    const source =
        \\{-# LANGUAGE NoImplicitPrelude #-}
        \\module Foo where
        \\
    ;
    const module = try parseModuleFromSource(testing.allocator, source);
    try testing.expect(module.language_extensions.contains(.NoImplicitPrelude));
    try testing.expect(!module.language_extensions.contains(.TypeApplications));
}

test "parseLangPragmas: multiple extensions in one pragma" {
    const source =
        \\{-# LANGUAGE NoImplicitPrelude, TypeApplications #-}
        \\module Foo where
        \\
    ;
    const module = try parseModuleFromSource(testing.allocator, source);
    try testing.expect(module.language_extensions.contains(.NoImplicitPrelude));
    try testing.expect(module.language_extensions.contains(.TypeApplications));
}

test "parseLangPragmas: multiple pragmas accumulate" {
    const source =
        \\{-# LANGUAGE NoImplicitPrelude #-}
        \\{-# LANGUAGE TypeApplications #-}
        \\module Foo where
        \\
    ;
    const module = try parseModuleFromSource(testing.allocator, source);
    try testing.expect(module.language_extensions.contains(.NoImplicitPrelude));
    try testing.expect(module.language_extensions.contains(.TypeApplications));
}

test "parseLangPragmas: unknown extension emits warning, does not error" {
    var diag_bag = DiagnosticBag.init();
    defer diag_bag.deinit(testing.allocator);
    var diags = DiagnosticCollector.init();

    const source =
        \\{-# LANGUAGE UnknownExtensionXYZ #-}
        \\module Foo where
        \\
    ;
    const module = try parseModuleFromSource2(testing.allocator, source, &diags);
    // Module still parses successfully
    try testing.expectEqualStrings("Foo", module.module_name);
    // A warning was emitted for the unknown extension
    try testing.expect(diags.hasWarnings());
    try testing.expect(!diags.hasErrors());
}

test "parseLangPragmas: no pragmas yields empty EnumSet" {
    const source =
        \\module Foo where
        \\
    ;
    const module = try parseModuleFromSource(testing.allocator, source);
    try testing.expect(module.language_extensions.eql(
        std.EnumSet(ast_mod.LanguageExtension).initEmpty(),
    ));
}
```

(Use or add a `parseModuleFromSource` private test helper that drives
`Lexer → LayoutProcessor → Parser.parseModule` with a fresh `DiagnosticCollector`.)

**Step 2: Run to verify failure**

```bash
nix develop --command zig build test -- --test-filter "parseLangPragmas" 2>&1
```

Expected: compile errors — `parseLangPragmas` not defined.

**Step 3: Implement `parseLangPragmas`**

Add this private method to `Parser` in `src/frontend/parser.zig`, before `parseModule`:

```zig
/// Collect consecutive `{-# LANGUAGE … #-}` pragmas at the top of the source.
///
/// Each recognised extension is inserted into the returned `EnumSet`.
/// Unrecognised extension names emit a `warning` diagnostic with the name's
/// `SourceSpan` and are otherwise ignored — the module still parses.
///
/// Stops as soon as the next token is not `pragma_open`.
fn parseLangPragmas(
    self: *Parser,
) ParseError!std.EnumSet(ast_mod.LanguageExtension) {
    const ext_map = std.StaticStringMap(ast_mod.LanguageExtension).initComptime(.{
        .{ "NoImplicitPrelude", .NoImplicitPrelude },
        .{ "OverloadedStrings",  .OverloadedStrings  },
        .{ "ScopedTypeVariables", .ScopedTypeVariables },
        .{ "TypeApplications",   .TypeApplications   },
    });

    var set = std.EnumSet(ast_mod.LanguageExtension).initEmpty();

    while (try self.check(.pragma_open)) {
        _ = try self.advance(); // consume {-#
        _ = try self.expect(.kw_LANGUAGE);

        // Parse comma-separated extension names until pragma_close.
        while (true) {
            if (try self.check(.pragma_close)) break;

            const name_tok = try self.expect(.conid);
            const name = name_tok.token.conid;
            const span = name_tok.span;

            if (ext_map.get(name)) |ext| {
                set.insert(ext);
            } else {
                self.diagnostics.addWarning(.{
                    .span = span,
                    .message = try std.fmt.allocPrint(
                        self.allocator,
                        "unknown LANGUAGE extension '{s}'; ignored",
                        .{name},
                    ),
                });
            }

            if (try self.match(.comma) == null) break;
        }

        _ = try self.expect(.pragma_close);
    }

    return set;
}
```

**Step 4: Call `parseLangPragmas` from `parseModule`**

In `parseModule` (line 537), prepend the pragma collection phase:

```zig
pub fn parseModule(self: *Parser) ParseError!ast_mod.Module {
    const start = try self.currentSpan();

    // ── Language pragmas (before module header) ───────────────────────
    const language_extensions = try self.parseLangPragmas();

    var module_name: []const u8 = "Main";
    // ... (rest unchanged) ...

    return ast_mod.Module{
        .module_name        = module_name,
        .exports            = exports,
        .imports            = try imports.toOwnedSlice(self.allocator),
        .declarations       = merged_decls,
        .language_extensions = language_extensions,   // NEW
        .span               = self.spanFrom(start),
    };
}
```

**Step 5: Check that `DiagnosticCollector` has a `hasWarnings()` method**

```bash
grep -n "hasWarnings\|addWarning\|Warning\|warning" src/diagnostics/diagnostic.zig | head -20
```

If `hasWarnings` or `addWarning` don't exist, add them to
`src/diagnostics/diagnostic.zig` using the same pattern as `hasErrors`/`addError`.
If the `Diagnostic` severity model already supports warnings (look for a `severity`
field or `Severity` enum), use that — don't invent a new mechanism.

**Step 6: Run all tests**

```bash
nix develop --command zig build test --summary all 2>&1 | tail -5
```

Expected: all tests pass.

**Step 7: Commit**

```bash
git add src/frontend/parser.zig src/diagnostics/diagnostic.zig
git commit -m "#NNN: Add parseLangPragmas; populate Module.language_extensions"
```

---

## Task 4: Add `parsed_modules` cache to `CompileEnv`

**Files:**
- Modify: `src/modules/compile_env.zig:69-116`

**Step 1: Write the failing test**

Add this test at the bottom of `compile_env.zig`:

```zig
test "CompileEnv: compileSingle with pre-parsed module skips re-parse" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    const source =
        \\module Cached where
        \\answer :: Int
        \\answer = 42
        \\
    ;

    // Parse once manually.
    var lexer = lexer_mod.Lexer.init(alloc, source, 1);
    var layout = layout_mod.LayoutProcessor.init(alloc, &lexer);
    layout.setDiagnostics(&env.diags);
    var parser = try parser_mod.Parser.init(alloc, &layout, &env.diags);
    const parsed = try parser.parseModule();

    // Compile using the pre-parsed module.
    const result = try env.compileSingle("Cached", source, 1, parsed);
    try testing.expect(result != null);
    try testing.expect(!env.diags.hasErrors());
}
```

**Step 2: Run to verify failure**

```bash
nix develop --command zig build test -- --test-filter "pre-parsed module" 2>&1
```

Expected: compile error — `compileSingle` does not accept a fourth argument.

**Step 3: Add `parsed_modules` field to `CompileEnv` and update lifecycle**

In `CompileEnv`, add the new field with documentation:

```zig
/// Map: module name → parsed AST module.
///
/// Populated during Phase 1 of `compileProgram` so that the dependency-graph
/// builder and `compileSingle` share a single parse result per module.
/// Keys are owned by `alloc` (duped on insert). Values are arena-allocated.
parsed_modules: std.StringHashMapUnmanaged(ast_mod.Module) = .{},
```

Update `init` to initialise it:
```zig
.parsed_modules = .{},
```

Update `deinit` to clean up:
```zig
self.parsed_modules.deinit(self.alloc);
```

**Step 4: Update `compileSingle` signature**

Change the signature to accept an optional pre-parsed module:

```zig
pub fn compileSingle(
    self: *CompileEnv,
    module_name: []const u8,
    source: []const u8,
    file_id: u32,
    parsed: ?ast_mod.Module,
) std.mem.Allocator.Error!?CoreProgram {
    // ── Parse (skip if caller provides pre-parsed module) ────────────
    const module = blk: {
        if (parsed) |p| break :blk p;

        var lexer = lexer_mod.Lexer.init(self.alloc, source, file_id);
        var layout = layout_mod.LayoutProcessor.init(self.alloc, &lexer);
        layout.setDiagnostics(&self.diags);

        var parser = parser_mod.Parser.init(self.alloc, &layout, &self.diags) catch return null;
        const m = parser.parseModule() catch return null;
        break :blk m;
    };
    if (self.diags.hasErrors()) return null;

    // ... rest of function unchanged, but use `module` (not `parsed_module`) ...
}
```

Also update the implicit-Prelude check (removing `hasNoImplicitPrelude`):

```zig
// Replace:
//   const module = if (hasNoImplicitPrelude(source) or mentionsPrelude(parsed_module.imports))
// With:
const final_module = if (module.language_extensions.contains(.NoImplicitPrelude) or
    mentionsPrelude(module.imports))
    module
else
    try injectImplicitPrelude(self.alloc, module);
```

Then use `final_module` for all downstream stages (rename, typecheck, desugar,
build interface).

**Step 5: Fix all call sites of `compileSingle` to pass `null`**

Search for all callers:
```bash
grep -rn "compileSingle" src/ tests/ 2>/dev/null
```

For every call that currently passes three arguments, add `null` as the fourth:
```zig
// Before:
_ = try env.compileSingle(m.module_name, m.source, m.file_id);
// After:
_ = try env.compileSingle(m.module_name, m.source, m.file_id, null);
```

**Step 6: Run all tests**

```bash
nix develop --command zig build test --summary all 2>&1 | tail -5
```

Expected: all tests pass.

**Step 7: Commit**

```bash
git add src/modules/compile_env.zig
git commit -m "#NNN: Add parsed_modules cache to CompileEnv; update compileSingle signature"
```

---

## Task 5: Rewrite `compileProgram` to parse once and use the cache

**Files:**
- Modify: `src/modules/compile_env.zig:362-411`

**Step 1: Write the integration test**

Add this test at the bottom of `compile_env.zig`:

```zig
test "compileProgram: multi-module compilation builds correct graph without double-parse" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    // Two modules: Bar depends on Foo.
    const modules = [_]SourceModule{
        .{ .module_name = "Foo", .source = "module Foo where\nfooVal :: Int\nfooVal = 1\n", .file_id = 1 },
        .{ .module_name = "Bar", .source = "module Bar where\nimport Foo\nbarVal :: Int\nbarVal = fooVal\n", .file_id = 2 },
    };

    const result = try compileProgram(alloc, &modules);
    try testing.expect(!result.env.diags.hasErrors());
}
```

**Step 2: Run to see current behaviour (should pass, verifying baseline)**

```bash
nix develop --command zig build test -- --test-filter "multi-module compilation" 2>&1
```

**Step 3: Rewrite `compileProgram`**

Replace the body of `compileProgram` with the three-phase approach:

```zig
pub fn compileProgram(
    alloc: std.mem.Allocator,
    modules: []const SourceModule,
) std.mem.Allocator.Error!struct { env: CompileEnv, result: CompileResult } {
    var env = CompileEnv.init(alloc);

    // ── Phase 1: Parse every module once; populate cache ─────────────
    for (modules) |m| {
        var lexer = lexer_mod.Lexer.init(alloc, m.source, m.file_id);
        var layout = layout_mod.LayoutProcessor.init(alloc, &lexer);
        layout.setDiagnostics(&env.diags);

        var parser = parser_mod.Parser.init(alloc, &layout, &env.diags) catch continue;
        const parsed = parser.parseModule() catch continue;

        const owned_name = try alloc.dupe(u8, m.module_name);
        try env.parsed_modules.put(alloc, owned_name, parsed);
    }

    // ── Phase 2: Build module graph from cached imports ───────────────
    var graph = ModuleGraph.init(alloc);
    defer graph.deinit();

    for (modules) |m| {
        _ = try graph.addModule(m.module_name);
        if (env.parsed_modules.get(m.module_name)) |parsed| {
            for (parsed.imports) |imp| {
                try graph.addEdge(m.module_name, imp.module_name);
            }
        }
    }

    // ── Topological sort ──────────────────────────────────────────────
    const topo = try module_graph.topoSort(&graph, alloc, &env.diags);
    defer alloc.free(topo.order);

    if (!topo.is_complete) {
        return .{
            .env = env,
            .result = .{ .core = .{ .data_decls = &.{}, .binds = &.{} }, .had_errors = true },
        };
    }

    // ── Phase 3: Compile in topological order using cached parses ─────
    var src_map: std.StringHashMapUnmanaged(SourceModule) = .{};
    defer src_map.deinit(alloc);
    for (modules) |m| try src_map.put(alloc, m.module_name, m);

    for (topo.order) |mod_name| {
        const m = src_map.get(mod_name) orelse continue;
        const cached = env.parsed_modules.get(mod_name);
        _ = try env.compileSingle(m.module_name, m.source, m.file_id, cached);
    }

    const had_errors = env.diags.hasErrors();
    const merged = try env.mergePrograms(alloc, topo.order);

    return .{
        .env = env,
        .result = .{ .core = merged, .had_errors = had_errors },
    };
}
```

**Step 4: Delete `parseImportNames`**

Remove the entire `parseImportNames` function from `compile_env.zig` (it is now
unreachable and has no callers).

**Step 5: Run all tests**

```bash
nix develop --command zig build test --summary all 2>&1 | tail -5
```

Expected: all tests pass.

**Step 6: Commit**

```bash
git add src/modules/compile_env.zig
git commit -m "#NNN: Rewrite compileProgram to parse once; delete parseImportNames"
```

---

## Task 6: Delete `hasNoImplicitPrelude` and clean up `compile_env.zig`

**Files:**
- Modify: `src/modules/compile_env.zig`

**Step 1: Delete `hasNoImplicitPrelude`**

Remove the entire `hasNoImplicitPrelude` function and its associated tests
(`hasNoImplicitPrelude: false when no pragma`, etc.) from `compile_env.zig`.

At this point the call site in `compileSingle` (Task 4, Step 4) should already
use `module.language_extensions.contains(.NoImplicitPrelude)`.

**Step 2: Verify no remaining callers**

```bash
grep -rn "hasNoImplicitPrelude" src/ tests/ 2>/dev/null
```

Expected: no output.

**Step 3: Run all tests**

```bash
nix develop --command zig build test --summary all 2>&1 | tail -5
```

Expected: all tests pass.

**Step 4: Commit**

```bash
git add src/modules/compile_env.zig
git commit -m "#NNN: Delete hasNoImplicitPrelude; use module.language_extensions"
```

---

## Task 7: File follow-up issue for `parseImportHeaders` in `module_graph.zig`

**Files:** none (GitHub only)

`parseImportHeaders` in `src/modules/module_graph.zig` follows the same
full-parse-for-imports pattern but serves the file-based module discovery path.
It is out of scope here because its results are not immediately reused by the
compilation pipeline. File a tracking issue so it isn't forgotten.

**Step 1: File the issue**

```bash
cat > /tmp/followup-body.md << 'EOF'
## Context

Issue #NNN introduced a `CompileEnv.parsed_modules` cache that eliminates the
double-parse in `compileProgram`. However, `parseImportHeaders` in
`src/modules/module_graph.zig` (used by `discoverModules`) still performs a full
parse just to extract import names, and its results are not shared with the
`CompileEnv` cache.

## Shortcoming

`discoverModules` parses each `.hs` file once to discover dependencies, then
`compileProgram` parses the same files again (Phase 1 of the new cache-populating
loop). The two parse passes are not unified.

## Deliverable

Refactor `discoverModules` to return `ast_mod.Module` values (not just file
paths), and plumb those into `compileProgram`'s Phase 1 cache so files reachable
via discovery are parsed exactly once across both phases.

## References

- `src/modules/module_graph.zig` — `parseImportHeaders`, `discoverModules`
- `src/modules/compile_env.zig` — `compileProgram` Phase 1
EOF

gh issue create \
  --title "modules: unify parseImportHeaders with CompileEnv parse cache" \
  --body-file /tmp/followup-body.md \
  --label "component:modules,priority:medium,type:feature"
```

**Step 2: Add a tracking comment in `module_graph.zig`**

In `parseImportHeaders`, add a comment referencing the new issue number:

```zig
/// Parse only the import declarations from a `.hs` file, returning the list
/// of imported module names.  Does a full parse of the module header but
/// stops after imports (does not parse declarations).
///
/// Returns an empty slice on read or parse error (discovery is best-effort).
///
/// NOTE: This performs a full parse that is currently not shared with the
/// `CompileEnv.parsed_modules` cache. A follow-up issue tracks unifying these
/// two parse passes:
/// tracked in: https://github.com/adinapoli/rusholme/issues/FOLLOWUP_NNN
fn parseImportHeaders(alloc: std.mem.Allocator, file_path: []const u8) ...
```

**Step 3: Commit**

```bash
git add src/modules/module_graph.zig
git commit -m "#NNN: Add tracking comment for parseImportHeaders follow-up"
```

---

## Task 8: Final verification, PR, and roadmap update

**Step 1: Run the full test suite**

```bash
nix develop --command zig build test --summary all 2>&1 | tail -10
```

Expected: all tests pass (741+).

**Step 2: Write PR body**

```bash
cat > /tmp/pr-body.md << 'EOF'
Closes #NNN

## Summary

Introduces `LanguageExtension` / `std.EnumSet(LanguageExtension)` as the single
authoritative source of enabled extensions for a parsed module, eliminating three
raw-scan / double-parse anti-patterns identified in the PR #441 review.

## Deliverables

- [x] `LanguageExtension` enum in `ast.zig`; `Module.language_extensions` field
- [x] Fix `Lexer.skipWhitespaceAndComments` — `{-#` no longer consumed as block comment
- [x] `Parser.parseLangPragmas` — collects LANGUAGE pragmas; warns on unknown extensions
- [x] `CompileEnv.parsed_modules` cache — each module parsed exactly once
- [x] `compileSingle` accepts `?ast_mod.Module` — callers can supply a cached parse
- [x] `compileProgram` refactored into three clean phases (parse → graph → compile)
- [x] `hasNoImplicitPrelude` deleted; replaced by `module.language_extensions.contains(.NoImplicitPrelude)`
- [x] `parseImportNames` deleted
- [x] Follow-up issue filed for `parseImportHeaders` unification

## Testing

```
nix develop --command zig build test --summary all
# All tests pass
```
EOF

gh pr create \
  --title "#NNN: ast+parser: introduce LanguageExtension EnumSet and module parse cache" \
  --body-file /tmp/pr-body.md \
  --base main \
  --head llm-agent/issue-NNN \
  --reviewer adinapoli
```

**Step 3: Update ROADMAP**

On the `project-planning` branch, add the new issue under the appropriate epic
with status `:yellow_circle:`, then push.

```bash
git checkout project-planning
git rebase main
# Edit ROADMAP.md — add the issue entry
git add ROADMAP.md
git commit -m "#NNN: Update roadmap status to in-review"
git push origin project-planning
git checkout llm-agent/issue-NNN
```
