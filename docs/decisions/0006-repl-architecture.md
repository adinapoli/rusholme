# Decision 0006: REPL Architecture

## Context

Rusholme needs an interactive REPL (issue #15, #75) for both native CLI use
(`rhc repl`) and browser deployment (WASM). A previous attempt (#482) delivered
a browser-facing WASM stub that echoed input without invoking the compiler
pipeline. This document defines the architecture for a real REPL that compiles
and executes Haskell through the full Rusholme pipeline.

## Design Principles

1. **The REPL is backend-agnostic.** The pipeline orchestrator, session state,
   and input handling are the same regardless of target. Only the execution
   engine (the "run this compiled unit" step) is backend-specific.

2. **WASM is not special.** The browser REPL is the native REPL cross-compiled
   to a different target. We do not design around browser constraints; we design
   a correct REPL and then compile it for the browser.

3. **Each backend implements PrimOps in terms of its target.** On native,
   `putStrLn` calls `fd_write`. In the browser, it flows through WASI
   `fd_write` to a JavaScript shim that writes to the terminal. The PrimOp
   dispatch layer is unchanged.

---

## Overall Architecture

```
+-----------------------------------------------------------+
|                      REPL Session                         |
|                                                           |
|  +----------------+    +-----------------------------+    |
|  | Input Handler  |--->| Pipeline Orchestrator       |    |
|  | (read line,    |    |                             |    |
|  |  :commands)    |    | Lexer -> Layout -> Parser   |    |
|  +----------------+    | -> Renamer -> Typechecker   |    |
|                        | -> Desugarer -> Lambda Lift |    |
|                        | -> GRIN Translator          |    |
|                        +-----------+-----------------+    |
|                                    |                      |
|                     +--------------+--------------+       |
|                     |                             |       |
|                     v                             v       |
|            +----------------+          +--------------+   |
|            | Native Engine  |          | WASM Engine  |   |
|            | GRIN -> LLVM   |          | GRIN tree-   |   |
|            | -> ORC JIT     |          | walking eval |   |
|            +----------------+          +--------------+   |
|                     |                             |       |
|  +----------------+ |                             |       |
|  | Session State  |<+-----------------------------+       |
|  | - bindings     |                                       |
|  | - types        |                                       |
|  | - GRIN defs    |                                       |
|  +----------------+                                       |
+-----------------------------------------------------------+
```

The pipeline is identical on all backends. Only the execution engine changes.

---

## Session State

Each REPL session accumulates state across inputs:

```zig
pub const ReplSession = struct {
    allocator: Allocator,

    // Compiler state (persists across inputs)
    unique_supply: UniqueSupply,
    rename_env: RenameEnv,
    type_env: TyEnv,
    meta_var_supply: MetaVarSupply,

    // Execution state (persists across inputs)
    engine: ExecutionEngine,  // backend-specific

    // Diagnostics (reset per input)
    diagnostics: DiagnosticCollector,
};
```

The session state is the compiler's "global environment" that normally comes
from a single source file, but in REPL mode grows incrementally. Each input
is compiled using this shared state, producing a small compilation unit that
the execution engine processes. The engine accumulates compiled units over
time so that definitions from earlier inputs are available to later ones.

---

## Input Classification

A REPL input is one of three kinds:

### Expressions

`2 + 3`, `map f [1,2,3]`, `not True`

Wrapped in a temporary module for compilation:

```haskell
-- User types:
2 + 3

-- REPL wraps as:
module ReplExpr where
main = putStrLn (show (2 + 3))
```

Compiled, executed, output captured and displayed.

### Declarations

`data Color = Red | Green | Blue`, `let f x = x + 1`

Compiled and added to the session. No execution; the bindings, types, and
compiled symbols become available to subsequent inputs.

### Commands

`:type <expr>`, `:quit`, `:load <file>`

Handled by the input handler directly, not the compiler pipeline.

### Classification strategy

Attempt to parse as a declaration first. If that fails, try as an expression.
This matches GHCi's approach.

### Multi-line input

The existing `:{` / `:}` delimiter handling (in `src/repl/eval.zig`) allows
multi-line blocks.

---

## Execution Engine

The execution engine is the only backend-specific component. It abstracts
"compile this and give me a callable thing."

```zig
pub const ExecutionEngine = union(enum) {
    native: NativeJIT,
    wasm: WasmEngine,

    /// Add a compiled unit to the engine. Symbols become
    /// available for subsequent lookups and future modules.
    pub fn addModule(self: *ExecutionEngine, ...) !void;

    /// Look up and execute the main symbol.
    /// Returns captured stdout as the result.
    pub fn executeMain(self: *ExecutionEngine) ![]const u8;
};
```

### Native: LLVM ORC JIT

The native engine wraps LLVM's ORC LLJIT (available via LLVM-C in LLVM 19):

- **Pipeline endpoint**: GRIN -> LLVM IR (using the existing `grin_to_llvm`
  translator).
- **addModule**: Calls `LLVMOrcLLJITAddLLVMIRModule`. The LLVM module is added
  to a JIT dylib; symbols accumulate across REPL inputs.
- **executeMain**: Calls `LLVMOrcLLJITLookup("main")`, casts the result to a
  function pointer, and calls it.
- **RTS linkage**: RTS symbols (`rts_alloc`, `rts_putStrLn`, etc.) are
  registered with the JIT via `LLVMOrcDefineMaterializedAbsoluteSymbols`,
  pointing to the in-process RTS library that is already linked into `rhc`.

Key LLVM-C APIs used:

| Operation | API |
|-----------|-----|
| Create JIT | `LLVMOrcCreateLLJIT` |
| Add IR module | `LLVMOrcLLJITAddLLVMIRModule` |
| Look up symbol | `LLVMOrcLLJITLookup` |
| Register RTS symbols | `LLVMOrcDefineMaterializedAbsoluteSymbols` |
| Dispose | `LLVMOrcDisposeLLJIT` |

### WASM: GRIN Tree-Walking Evaluator

The WASM engine uses the existing GRIN evaluator (`src/grin/evaluator.zig`):

- **Pipeline endpoint**: GRIN (one stage before LLVM IR).
- **addModule**: Adds GRIN definitions to the evaluator's `FunctionTable` and
  the session's `Environment`.
- **executeMain**: Calls `GrinEvaluator.eval()` on the main expression.
- **RTS linkage**: PrimOps dispatch through the evaluator's `evalPrimOp` bridge
  to the runtime module. IO PrimOps use Zig's `std.Io`, which on `wasm32-wasi`
  emits WASI `fd_write` calls routed by the browser shim to the terminal.

---

## Architectural Tension: Evaluation Level

The native backend compiles all the way to machine code (LLVM JIT), while the
WASM backend interprets at the GRIN level. This is a deliberate trade-off:

**Why not LLVM JIT in the browser?** The LLVM-C API is a native C library that
cannot be compiled to WebAssembly. Embedding LLVM in a browser WASM module
would produce an impractically large binary (tens of MB) and is not supported
by the LLVM project.

**Why not compile-to-WASM-and-instantiate?** Each expression would need to be
compiled from LLVM IR to `.wasm` bytes (requiring `llc` and `wasm-ld` in the
browser) and then instantiated via `WebAssembly.instantiate()`. This has the
same problem: LLVM's codegen cannot run inside WASM.

**Consequences of the split:**

- The WASM REPL will be slower for compute-heavy expressions (tree-walking
  interpretation vs JIT'd machine code).
- Some bugs might manifest differently between backends (JIT codegen vs
  tree-walking evaluation exercise different code paths).
- This is acceptable because: (a) the browser REPL is for demo and learning,
  not benchmarking; (b) the GRIN evaluator implements the same semantic model;
  and (c) the architecture naturally resolves if WebAssembly gains JIT
  capabilities or if a lightweight codegen becomes embeddable.

**Mitigation:** Both backends run the same pipeline through GRIN. The only
divergence is the last step (JIT vs interpret). Both use the same PrimOp
dispatch. End-to-end tests that run on both backends will catch semantic
divergence early.

---

## WASM Browser Integration

### Build target

`wasm32-wasi`. Zig's `std.Io` works natively on this target, emitting WASI
`fd_write` / `fd_read` calls.

### WASI polyfill

[browser_wasi_shim](https://github.com/bjorn3/browser_wasi_shim) provides
`wasi_snapshot_preview1` in the browser. Actively maintained (25 releases,
latest June 2025, 243 commits, 20 contributors).

Stdout redirection to xterm.js:

```javascript
import { WASI, ConsoleStdout, File, OpenFile } from "@aspect-build/wasi-shim";

const stdout = ConsoleStdout.lineBuffered(
    msg => terminal.writeLine(msg)
);

const wasi = new WASI([], [], [
    new OpenFile(new File([])),  // stdin
    stdout,                      // stdout
    stdout,                      // stderr
]);

const { instance } = await WebAssembly.instantiateStreaming(
    fetch("repl.wasm"),
    { wasi_snapshot_preview1: wasi.wapiMemory }
);
```

### WASM module contents

The REPL WASM module contains:
- The full Rusholme pipeline (lexer through GRIN translator) — pure Zig, no
  LLVM dependency
- The GRIN tree-walking evaluator
- The runtime PrimOp dispatch (IO routed through WASI)
- The REPL session state manager
- The WASM export bridge (`repl_init`, `repl_evaluate`, buffer management)

It does **not** contain:
- LLVM-C bindings or the LLVM JIT
- The `grin_to_llvm` translator
- The native linker/codegen

This is enforced at the build level: the WASM REPL target imports a subset of
the `rusholme` module that excludes `backend.*`.

### JavaScript bridge

The existing bridge architecture (shared input/output buffers, JSON responses)
is retained from #482 but repurposed to carry real results:

```json
{"status": "success", "value": "5"}
{"status": "success", "value": "Color: Red"}
{"status": "error", "stage": "typecheck", "message": "...", "span": {...}}
{"status": "declaration", "name": "Color", "kind": "data"}
```

For complete protocol documentation including server mode, see
[docs/proxy/repl_protocol.md](../proxy/repl_protocol.md), which provides:

- Full server mode specification (JSON-RPC 2.0 over stdin/stdout)
- Command reference with request/response examples
- WASM export documentation
- Error handling patterns
- Usage examples for native, WASM, and browser clients

---

## Error Handling

Errors never crash the REPL. A bad input produces a diagnostic, then the
session continues with unchanged state.

The pipeline is transactional:

1. Snapshot the session state.
2. Run the pipeline on the new input.
3. If any stage produces errors:
   - Render diagnostics to the terminal (via the `DiagnosticCollector`).
   - Discard all intermediate results.
   - Restore the snapshot.
4. If all stages succeed:
   - Commit the new bindings, types, and compiled symbols to session state.
   - Execute and print the result (for expressions).

The `DiagnosticCollector` already supports this model. Diagnostics are rendered
using the existing terminal renderer (native) or serialized to JSON (WASM).

---

## Scope

### In scope

- Backend-agnostic REPL session (`src/repl/session.zig`)
- Native execution engine (LLVM ORC JIT via LLVM-C)
- WASM execution engine (GRIN tree-walking evaluator)
- Input handling: expressions, declarations, commands (`:quit`, `:type`)
- Multi-line input via `:{` / `:}`
- Browser integration: `wasm32-wasi`, `browser_wasi_shim`, xterm.js, JS bridge
- CLI mode: `rhc repl` command with line editing (linenoise via C interop)
- Transactional error handling with structured diagnostics

### Deferred (tracked by issues)

- Auto-completion (issue #76)
- `:load <file>` command (needs module system work)
- Thunk evaluation / lazy semantics (issue #384)
- Closure support (issue #386)
- Persistent REPL history
- Optimizing WASM recompilation (caching compiled GRIN modules)

---

## References

- Issue #15: Epic: REPL / interactive mode
- Issue #75: Implement basic REPL loop
- Issue #76: Implement REPL auto-completion and multi-line input
- Issue #482: REPL WASM (predecessor, scaffold only)
- LLVM ORC JIT C API: `llvm-c/LLJIT.h`, `llvm-c/Orc.h` (LLVM 19)
- browser_wasi_shim: https://github.com/bjorn3/browser_wasi_shim
- Decision 0001: PrimOps and RTS Architecture
- DESIGN.md: Backend Strategy, GRIN Details
