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

## Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| `error: C import failed … 'llvm-c/Core.h' not found` | Not inside the Nix devShell | Run `nix develop` first, or prefix with `nix develop --command` |
| `Failed to run 'llvm-config --includedir'` | LLVM not on PATH | Same as above |
| `error: struct 'heap' has no member named 'raw_c_allocator'` | Zig version mismatch; `raw_c_allocator` was removed in 0.16 | Use `std.heap.c_allocator` instead |
