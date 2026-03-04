# REPL Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Build a backend-agnostic REPL that compiles Haskell through the full Rusholme pipeline and executes it — via LLVM ORC JIT on native, via the GRIN tree-walking evaluator on WASM.

**Architecture:** The REPL is a session that accumulates compiler state (type env, rename env, unique supply) across inputs. Each input is classified as an expression, declaration, or command, then compiled through the full pipeline (lexer -> parser -> renamer -> typechecker -> desugarer -> lambda lifter -> GRIN translator). The execution engine is a pluggable backend: LLVM JIT for native, GRIN evaluator for WASM. See `docs/decisions/0006-repl-architecture.md`.

**Tech Stack:** Zig 0.16, LLVM 19 (ORC JIT via LLVM-C), browser_wasi_shim (WASM), xterm.js (browser terminal).

---

## Phase 1: Pipeline Orchestrator (backend-agnostic)

The core of the REPL: take a string of Haskell, run it through the pipeline, produce GRIN IR. No execution yet — just proving we can compile REPL inputs incrementally.

### Task 1: Create the pipeline orchestrator module

**Files:**
- Create: `src/repl/pipeline.zig`
- Test: inline `test` blocks in `src/repl/pipeline.zig`

**Step 1: Write the failing test**

Write a test that creates a `Pipeline`, feeds it a simple expression string `"42"`, and expects to get a GRIN `Program` back.

```zig
const std = @import("std");
const testing = std.testing;
const Pipeline = @import("pipeline.zig").Pipeline;

test "pipeline: compile simple literal expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var pipeline = try Pipeline.init(alloc, testing.io);
    defer pipeline.deinit();

    const result = try pipeline.compileInput("42");
    // Should produce a GRIN program with at least one definition
    try testing.expect(result.program.defs.len > 0);
}
```

**Step 2: Run test to verify it fails**

Run: `nix develop --command zig build test --summary all -- --test-filter "pipeline: compile simple literal"`
Expected: Compilation error — `Pipeline` not defined.

**Step 3: Write minimal implementation**

Create `src/repl/pipeline.zig` with a `Pipeline` struct that:
1. Wraps the compiler state: `UniqueSupply`, `DiagnosticCollector`, `ArenaAllocator`
2. Has `compileInput(source: []const u8) !CompileResult` that:
   - Wraps the source as a module: `module ReplInput where\nmain = <source>`
   - Runs: Lexer -> LayoutProcessor -> Parser -> Renamer -> Typechecker -> Desugarer -> Lambda Lifter -> GRIN Translator
   - Returns the GRIN `Program`
3. Follow the exact pipeline invocation pattern from `src/main.zig:cmdGrin` (lines 445-543)

The `CompileResult` struct holds:
```zig
pub const CompileResult = struct {
    program: grin_ast.Program,
    kind: enum { expression, declaration },
};
```

Reference files:
- `src/main.zig:445-543` — the `cmdGrin` function shows the exact pipeline invocation
- `src/root.zig` — module re-exports for all pipeline stages
- `src/diagnostics/diagnostic.zig` — `DiagnosticCollector`

**Step 4: Run test to verify it passes**

Run: `nix develop --command zig build test --summary all -- --test-filter "pipeline: compile simple literal"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/repl/pipeline.zig
git commit -m "repl: add pipeline orchestrator with basic expression compilation"
```

---

### Task 2: Add declaration compilation to the pipeline

**Files:**
- Modify: `src/repl/pipeline.zig`

**Step 1: Write the failing test**

```zig
test "pipeline: compile data declaration" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var pipeline = try Pipeline.init(alloc, testing.io);
    defer pipeline.deinit();

    const result = try pipeline.compileInput("data Color = Red | Green | Blue");
    try testing.expect(result.kind == .declaration);
    try testing.expect(result.program.defs.len > 0);
}
```

**Step 2: Run test to verify it fails**

Expected: FAIL — the pipeline currently wraps everything as `main = <expr>`, which won't parse a `data` declaration.

**Step 3: Implement input classification**

Add input classification to `Pipeline.compileInput`:
1. Try to parse as a module body (top-level declarations): wrap as `module ReplInput where\n<source>`
2. If that fails (parse error), try to parse as an expression: wrap as `module ReplInput where\nreplExpr__ = <source>`
3. Set `result.kind` accordingly

This is the "try declaration first, fall back to expression" strategy from the design doc.

**Step 4: Run test to verify it passes**

Run: `nix develop --command zig build test --summary all -- --test-filter "pipeline: compile data"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/repl/pipeline.zig
git commit -m "repl: add declaration vs expression classification in pipeline"
```

---

### Task 3: Add session state accumulation

**Files:**
- Create: `src/repl/session.zig`
- Test: inline `test` blocks in `src/repl/session.zig`

**Step 1: Write the failing test**

```zig
test "session: define then use across inputs" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // First input: define a function
    const r1 = try session.processInput("double x = x + x");
    try testing.expect(r1.kind == .declaration);

    // Second input: use the function — should compile successfully
    // because `double` is in the session's environment
    const r2 = try session.processInput("double 21");
    try testing.expect(r2.kind == .expression);
}
```

**Step 2: Run test to verify it fails**

Expected: Compilation error — `Session` not defined.

**Step 3: Write minimal implementation**

Create `src/repl/session.zig` with a `Session` struct that:
1. Owns persistent state: `UniqueSupply`, `RenameEnv`, `TyEnv`, `MetaVarSupply`
2. Has `processInput(source: []const u8) !ProcessResult` that:
   - Creates a fresh `Pipeline` for this input, seeded with the session's accumulated state
   - Compiles the input
   - On success: commits new bindings/types back to the session state
   - On failure: discards everything, returns the diagnostics
3. The `ProcessResult` includes the GRIN program (for the execution engine to use) and diagnostics

Key challenge: the typechecker's `TyEnv`, renamer's `RenameEnv`, and `UniqueSupply` must persist across inputs. Study how `cmdGrin` in `src/main.zig` initializes these, and make them fields of `Session` instead of locals.

Reference files:
- `src/main.zig:445-543` — how state objects are created
- `src/typechecker/env.zig` — `TyEnv.init`, `initBuiltins`
- `src/renamer/renamer.zig` — `RenameEnv.init`
- `src/naming/unique.zig` — `UniqueSupply`

**Step 4: Run test to verify it passes**

Run: `nix develop --command zig build test --summary all -- --test-filter "session: define then use"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/repl/session.zig
git commit -m "repl: add session with state accumulation across inputs"
```

---

### Task 4: Add transactional error handling

**Files:**
- Modify: `src/repl/session.zig`

**Step 1: Write the failing test**

```zig
test "session: failed input does not corrupt state" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // Define a valid function
    _ = try session.processInput("f x = x");

    // Submit invalid input — should fail but not corrupt state
    const bad = session.processInput("let = = =");
    try testing.expect(bad == error.CompilationFailed or
        (if (bad) |r| r.diagnostics.len > 0 else false));

    // Original function should still work
    const r = try session.processInput("f 42");
    try testing.expect(r.kind == .expression);
}
```

**Step 2: Run test to verify it fails**

Expected: FAIL — currently a bad input might partially mutate session state.

**Step 3: Implement transactional rollback**

The session should:
1. Clone/snapshot the mutable state before each input (or use arena-per-input that can be discarded)
2. On pipeline failure: discard the input's arena, leave session state unchanged
3. On success: merge the input's results into session state

The cleanest approach: each input gets its own `ArenaAllocator`. Declarations that succeed have their results copied into the session's long-lived arena. Failed inputs just discard the per-input arena.

**Step 4: Run test to verify it passes**

Run: `nix develop --command zig build test --summary all -- --test-filter "session: failed input"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/repl/session.zig
git commit -m "repl: add transactional error handling — failed inputs don't corrupt state"
```

---

## Phase 2: WASM Execution Engine (GRIN evaluator)

Wire the GRIN tree-walking evaluator as the execution backend for the WASM REPL. This is the simpler engine and lets us test the full loop before tackling LLVM JIT.

### Task 5: Create the execution engine abstraction

**Files:**
- Create: `src/repl/engine.zig`
- Test: inline `test` blocks

**Step 1: Write the failing test**

```zig
test "grin engine: evaluate literal expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var engine = try GrinEngine.init(alloc, testing.io);
    defer engine.deinit();

    // Build a trivial GRIN program: main = return 42
    const main_body = try alloc.create(grin_ast.Expr);
    main_body.* = .{ .Return = .{ .Lit = .{ .Int = 42 } } };

    const main_def = grin_ast.Def{
        .name = .{ .base = "main", .unique = .{ .value = 0 } },
        .params = &.{},
        .body = main_body,
    };
    const defs = try alloc.alloc(grin_ast.Def, 1);
    defs[0] = main_def;
    const program = grin_ast.Program{ .defs = defs };

    try engine.addProgram(&program);
    const result = try engine.executeMain();

    try testing.expectEqualStrings("42", result.value);
}
```

**Step 2: Run test to verify it fails**

Expected: Compilation error — `GrinEngine` not defined.

**Step 3: Write minimal implementation**

Create `src/repl/engine.zig` with:
- `GrinEngine` struct wrapping `GrinEvaluator` from `src/grin/evaluator.zig`
- `addProgram(program)` — populates the evaluator's function table
- `executeMain() !ExecResult` — looks up `main`, evaluates it, formats the result as a string
- `ExecResult` struct: `{ value: []const u8, stdout: []const u8 }`

The `GrinEngine` reuses the existing `GrinEvaluator.init()` and `.eval()` API. The value formatting converts GRIN `Val` to a human-readable string (integers, booleans, constructors, etc.).

Reference files:
- `src/grin/evaluator.zig:379` — `GrinEvaluator.init`
- `src/grin/evaluator.zig:506` — `GrinEvaluator.eval`
- `src/integration_test.zig` — pattern for building and evaluating GRIN programs

**Step 4: Run test to verify it passes**

Run: `nix develop --command zig build test --summary all -- --test-filter "grin engine: evaluate literal"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/repl/engine.zig
git commit -m "repl: add GRIN execution engine with value formatting"
```

---

### Task 6: Wire session to GRIN engine for end-to-end evaluation

**Files:**
- Modify: `src/repl/session.zig`
- Modify: `src/repl/engine.zig`

**Step 1: Write the failing test**

```zig
test "session: end-to-end evaluate expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, .{ .engine = .grin }, testing.io);
    defer session.deinit();

    const result = try session.eval("2 + 3");
    try testing.expectEqualStrings("5", result.value);
}
```

**Step 2: Run test to verify it fails**

Expected: FAIL — `session.eval` doesn't exist yet.

**Step 3: Implement session.eval**

Add `eval(source: []const u8) !EvalResult` to `Session`:
1. Call `processInput(source)` to compile through the pipeline
2. If it's an expression: pass the GRIN program to `engine.addProgram()` then `engine.executeMain()`
3. If it's a declaration: just add to session state, return a "defined" message
4. Return the `ExecResult`

**Step 4: Run test to verify it passes**

Run: `nix develop --command zig build test --summary all -- --test-filter "session: end-to-end evaluate"`
Expected: PASS

**Step 5: Add more end-to-end tests**

```zig
test "session: define and call function" {
    // ...
    _ = try session.eval("double x = x + x");
    const result = try session.eval("double 21");
    try testing.expectEqualStrings("42", result.value);
}

test "session: data type and pattern match" {
    // ...
    _ = try session.eval("data Color = Red | Green | Blue");
    const result = try session.eval("Red");
    // Expect constructor representation
    try testing.expect(result.value.len > 0);
}
```

**Step 6: Commit**

```bash
git add src/repl/session.zig src/repl/engine.zig
git commit -m "repl: wire session to GRIN engine for end-to-end evaluation"
```

---

## Phase 3: WASM Browser Integration

### Task 7: Update build.zig for wasm32-wasi REPL with pipeline

**Files:**
- Modify: `build.zig`

**Step 1: Update the REPL WASM target**

The current target is `wasm32-freestanding`. Change to `wasm32-wasi` and add the `rusholme` module as a dependency (excluding the LLVM backend).

The key challenge: the `rusholme` module (`src/root.zig`) imports `backend.zig` which imports `llvm.zig` which uses `@cImport` for LLVM-C headers. This won't compile for `wasm32-wasi`. We need either:

a. A separate root module for the REPL that imports everything except `backend`, or
b. Conditional compilation in `src/root.zig` to skip the backend on WASM targets

Option (a) is cleaner — create `src/repl/root.zig` that re-exports the pipeline modules without the LLVM backend.

**Step 2: Create REPL-specific root module**

Create `src/repl/root.zig` that imports:
- `diagnostics`, `frontend`, `naming`, `renamer`, `tc`, `core`, `grin`, `runtime`
- Does NOT import `backend`

**Step 3: Update build.zig**

```zig
const repl_mod = b.addModule("rusholme_repl", .{
    .root_source_file = b.path("src/repl/root.zig"),
    .target = b.resolveTargetQuery(.{
        .cpu_arch = .wasm32,
        .os_tag = .wasi,
    }),
    .optimize = .ReleaseSmall,
});

const repl_wasm = b.addExecutable(.{
    .name = "repl",
    .root_module = b.createModule(.{
        .root_source_file = b.path("src/repl/exports.zig"),
        .target = b.resolveTargetQuery(.{
            .cpu_arch = .wasm32,
            .os_tag = .wasi,
        }),
        .optimize = .ReleaseSmall,
        .imports = &.{.{ .name = "rusholme", .module = repl_mod }},
    }),
});
repl_wasm.rdynamic = true;
```

**Step 4: Build and verify**

Run: `nix develop --command zig build`
Expected: Successful build producing `zig-out/bin/repl.wasm` with all exports.

**Step 5: Commit**

```bash
git add build.zig src/repl/root.zig
git commit -m "repl: switch WASM target to wasm32-wasi with pipeline modules"
```

---

### Task 8: Wire exports.zig to the real session

**Files:**
- Modify: `src/repl/exports.zig`

**Step 1: Update exports.zig**

Replace the placeholder with real session integration:

```zig
const rusholme = @import("rusholme");
const Session = @import("session.zig").Session;
const buffer = @import("buffer.zig");
const eval = @import("eval.zig");

var session: ?Session = null;

pub export fn repl_init() void {
    if (session == null) {
        session = Session.init(
            std.heap.page_allocator,
            .{ .engine = .grin },
            std.io.getStdIo(),
        ) catch return;
    }
}

pub export fn repl_evaluate(length: usize) usize {
    const input = buffer.getInputBuffer()[0..length];
    const expr = eval.stripMultilineDelimiters(input);
    const output = buffer.getOutputBuffer()[0..16384];

    if (session) |*s| {
        const result = s.eval(expr) catch |err| {
            // Format error as JSON
            return formatError(output, err, s);
        };
        return formatSuccess(output, result);
    }
    return formatError(output, error.NotInitialized, null);
}
```

**Step 2: Build and verify**

Run: `nix develop --command zig build`
Expected: Build succeeds.

**Step 3: Test locally**

Run: `cd website && npm run build && npx serve .`
Open browser, type `42` in the REPL, expect to see `42`.

**Step 4: Commit**

```bash
git add src/repl/exports.zig
git commit -m "repl: wire WASM exports to real pipeline session"
```

---

### Task 9: Add browser_wasi_shim for IO routing

**Files:**
- Modify: `website/package.json`
- Modify: `website/repl/bridge.js`
- Modify: `website/repl/index.html`

**Step 1: Add browser_wasi_shim dependency**

Add `@aspect-build/wasi-shim` (or `@bjorn3/browser_wasi_shim`) to `website/package.json`.

**Step 2: Update bridge.js**

Replace the current `WebAssembly.instantiate(module, { env: {} })` with WASI-aware instantiation:

```javascript
import { WASI, ConsoleStdout, File, OpenFile } from "@aspect-build/wasi-shim";

const stdout = ConsoleStdout.lineBuffered(msg => terminal.writeLine(msg));
const wasi = new WASI([], [], [
    new OpenFile(new File([])),  // stdin
    stdout,                      // stdout
    stdout,                      // stderr
]);

const { instance } = await WebAssembly.instantiateStreaming(
    fetch('repl.wasm'),
    wasi.getImportObject()
);
wasi.initialize(instance);
```

**Step 3: Test in browser**

Type `putStrLn "Hello"` in the REPL. Expect "Hello" to appear in the terminal via the WASI stdout shim.

**Step 4: Commit**

```bash
git add website/
git commit -m "repl: add browser_wasi_shim for IO routing to xterm.js terminal"
```

---

## Phase 4: Native LLVM JIT Engine

### Task 10: Create LLVM JIT execution engine

**Files:**
- Create: `src/repl/jit_engine.zig`
- Test: inline `test` blocks

**Step 1: Write the failing test**

```zig
test "jit engine: evaluate literal via LLVM JIT" {
    // Build a GRIN program for "main = return 42"
    // Translate to LLVM IR via grin_to_llvm
    // Feed to JIT engine
    // Execute main, expect "42"
}
```

**Step 2: Implement JIT engine**

Create `src/repl/jit_engine.zig` wrapping LLVM ORC LLJIT:

```zig
pub const JitEngine = struct {
    jit: llvm.OrcLLJITRef,
    context: llvm.OrcThreadSafeContextRef,
    allocator: Allocator,

    pub fn init(allocator: Allocator) !JitEngine { ... }
    pub fn deinit(self: *JitEngine) void { ... }

    /// Add a GRIN program: translate to LLVM IR, feed to JIT
    pub fn addProgram(self: *JitEngine, program: *const grin.Program) !void { ... }

    /// Look up and call the main symbol
    pub fn executeMain(self: *JitEngine) !ExecResult { ... }

    /// Register RTS symbols so JIT'd code can call rts_alloc, rts_putStrLn, etc.
    fn registerRtsSymbols(self: *JitEngine) !void { ... }
};
```

Key LLVM-C APIs to wrap:
- `LLVMOrcCreateLLJIT` / `LLVMOrcDisposeLLJIT`
- `LLVMOrcLLJITAddLLVMIRModule`
- `LLVMOrcLLJITLookup`
- `LLVMOrcCreateNewThreadSafeContext` / `LLVMOrcCreateNewThreadSafeModule`
- `LLVMOrcDefineMaterializedAbsoluteSymbols` (for RTS symbol registration)

Reference files:
- `src/backend/llvm.zig` — existing LLVM-C bindings
- `src/backend/grin_to_llvm.zig` — GRIN to LLVM IR translator
- LLVM-C headers: `llvm-c/LLJIT.h`, `llvm-c/Orc.h`

**Step 3: Register RTS symbols**

The JIT needs to resolve calls to `rts_alloc`, `rts_putStrLn`, `rts_store_field`, etc. Register these using `LLVMOrcDefineMaterializedAbsoluteSymbols` pointing to the in-process addresses of the RTS functions (which are linked into `rhc`).

**Step 4: Run tests**

Run: `nix develop --command zig build test --summary all -- --test-filter "jit engine"`
Expected: PASS

**Step 5: Commit**

```bash
git add src/repl/jit_engine.zig
git commit -m "repl: add LLVM ORC JIT execution engine"
```

---

### Task 11: Add the `rhc repl` CLI command

**Files:**
- Modify: `src/main.zig`
- Create: `src/repl/cli.zig`

**Step 1: Add command parsing**

Add `repl` as a subcommand in `src/main.zig`'s argument parser. When invoked, it creates a `Session` with the JIT engine and enters the read-eval-print loop.

**Step 2: Implement the CLI REPL loop**

Create `src/repl/cli.zig`:

```zig
pub fn run(allocator: Allocator, io: std.Io) !void {
    var session = try Session.init(allocator, .{ .engine = .jit }, io);
    defer session.deinit();

    // Print banner
    // Read line (using stdin for now; linenoise later per #75)
    // Process input
    // Print result or diagnostics
    // Loop until :quit
}
```

**Step 3: Test manually**

Run: `nix develop --command zig-out/bin/rhc repl`
Type: `2 + 3`
Expect: `5`

**Step 4: Commit**

```bash
git add src/main.zig src/repl/cli.zig
git commit -m "repl: add rhc repl CLI command with LLVM JIT backend"
```

---

## Phase 5: Polish and Integration

### Task 12: Add REPL command handling (:quit, :type)

**Files:**
- Create: `src/repl/commands.zig`
- Modify: `src/repl/session.zig`

Implement `:quit` (exit the REPL) and `:type <expr>` (show the inferred type without evaluating). The command parser checks for a leading `:` and dispatches to the command handler.

---

### Task 13: Run full test suite and verify nothing is broken

**Step 1:** Run `nix develop --command zig build test --summary all`
**Step 2:** Run `nix develop --command zig build`
**Step 3:** Verify WASM binary has all exports
**Step 4:** Verify `npm run build && npm run serve` works locally

---

### Task 14: Update ROADMAP.md and open PR

Update issue #75 status in the roadmap, push the branch, open a PR for review.

---

## Dependency Graph

```
Task 1 (pipeline orchestrator)
  └─> Task 2 (declaration classification)
       └─> Task 3 (session state accumulation)
            └─> Task 4 (transactional errors)
                 ├─> Task 5 (GRIN engine abstraction)
                 │    └─> Task 6 (wire session to engine)
                 │         └─> Task 7 (build.zig wasm32-wasi)
                 │              └─> Task 8 (wire exports.zig)
                 │                   └─> Task 9 (browser_wasi_shim)
                 └─> Task 10 (LLVM JIT engine)
                      └─> Task 11 (rhc repl CLI)
                           └─> Task 12 (commands)
                                └─> Task 13 (full test suite)
                                     └─> Task 14 (PR)
```

Tasks 5-9 (WASM path) and Tasks 10-11 (native path) can be worked in parallel after Task 4.
