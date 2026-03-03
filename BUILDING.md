# Building Rusholme

Rusholme uses the [Nix](https://nixos.org/) package manager to provide a
reproducible development environment containing the exact versions of Zig and
LLVM the project requires.

## Prerequisites

| Tool | Notes |
|------|-------|
| **Nix** (≥ 2.4) | Install from <https://nixos.org/download>. Flakes must be enabled. |

> [!NOTE]
> On most systems you can enable flakes by adding the following to
> `~/.config/nix/nix.conf`:
>
> ```
> experimental-features = nix-command flakes
> ```

## Entering the Dev Shell

```bash
nix develop          # opens a shell with Zig + LLVM + tooling on PATH
```

Alternatively, prefix any command with `nix develop --command`:

```bash
nix develop --command zig build
```

The shell prints the toolchain versions on entry:

```
🍛 Rusholme dev environment loaded
   Zig:  0.16.0-dev.2611+f996d2866
   LLVM: 19.1.7
```

## Build

```bash
zig build                         # compile the `rhc` executable
zig build test --summary all      # run all tests (unit + golden + parser + runtime)
```

### Running the Compiler

```bash
zig build run -- parse  FILE.hs   # pretty-print the AST
zig build run -- core   FILE.hs   # show desugared Core IR
zig build run -- grin   FILE.hs   # show GRIN IR
zig build run -- ll     FILE.hs   # emit LLVM IR
zig build run -- build  FILE.hs   # compile to native executable
```

## WASM REPL (Browser-based Demo)

Rusholme includes a browser-based REPL built with WebAssembly for live Haskell
evaluation demos.

### Building the REPL

```bash
nix develop --command zig build    # builds repl.wasm
```

The REPL binary is produced at `zig-out/bin/repl.wasm`. The website files are
located in `website/repl/`:

```
website/repl/
├── index.html      # HTML shell with xterm.js terminal
├── terminal.js     # xterm.js setup
├── input-handler.js  # Enter key handling
├── bridge.js       # WASM→JavaScript bridge
└── repl.wasm       # Compiled WebAssembly module
```

### Running the REPL

To test locally, serve the `website/repl/` directory with an HTTP server:

```bash
python -m http.server 8000 --directory website/repl
# Then open http://localhost:8000 in a browser
```

The REPL terminal supports:
- **Expression typing** - Type expressions and press Enter to evaluate
- **Multi-line blocks** - Surround with `:{` and `:}` for multi-line definitions
- **Ctrl+C** - Clear the current line

### MVP Limitiations

The current MVP echoes input with type information (identifier, literal, or
expression). Full Haskell compilation, type-checking, and evaluation will be
added in future iterations by integrating the Rusholme parser, typechecker,
Core desugaring, GRIN translation, and LLVM backend.

## Why `llvm-config` Matters

Rusholme's LLVM backend (`src/backend/llvm.zig`) uses Zig's `@cImport` to
pull in LLVM-C headers (`llvm-c/Core.h`, etc.). The challenge under Nix is
threefold:

1. **No pkg-config file.** Nixpkgs does not ship a `.pc` file for LLVM, so
   `pkg-config --cflags llvm` does not work.
2. **Split store paths.** Nix separates LLVM into `-dev` (headers) and `-lib`
   (shared objects) outputs living under different Nix store paths.
3. **`@cImport` ignores `NIX_CFLAGS_COMPILE`.** Zig's translate-C subprocess
   does not inherit the shell-level C flags that Nix sets, so headers are
   invisible without explicit include paths.

The solution in `build.zig` is a `configureLlvm` helper that shells out to
`llvm-config --includedir` and `llvm-config --libdir` at build-graph
construction time, then passes the discovered paths to the Zig module via
`addSystemIncludePath` / `addLibraryPath` / `linkSystemLibrary`.

## Build Artifacts

`rhc build` produces per-module backend artifacts alongside the `.rhi` interface
files that the typechecker uses for cross-module type information:

```
Foo.hs  →  compile  →  Foo.rhi    (typechecker interface — module types and exports)
                    →  Foo.bc     (LLVM bitcode — durable backend artifact)
```

The `.bc` files are **kept after linking** and can be inspected or re-used:

```bash
# Inspect the bitcode for a module
llvm-dis Foo.bc -o Foo.ll    # convert to human-readable LLVM IR
opt -O2 Foo.bc -o Foo.opt.bc  # run LLVM optimisation passes
```

### Multi-module link flow

When compiling multiple Haskell source files, `rhc build` translates each module
to a separate LLVM module, writes its bitcode, then links the LLVM modules
in-process before emitting the final object file:

```
Foo.bc  ─┐
Bar.bc  ─┤─► LLVMLinkModules2 ─► linked module ─► emitObjectFile ─► cc + rts.a ─► exe
Baz.bc  ─┘
```

The RTS (`librts.a`) is compiled separately and linked in at the final `cc` step,
unchanged from the single-module flow.

## Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| `error: C import failed … 'llvm-c/Core.h' not found` | Not inside the Nix devShell | Run `nix develop` first, or prefix with `nix develop --command` |
| `Failed to run 'llvm-config --includedir'` | LLVM not on PATH | Same as above |
| `error: struct 'heap' has no member named 'raw_c_allocator'` | Zig version mismatch; `raw_c_allocator` was removed in 0.16 | Use `std.heap.c_allocator` instead |
