# Contributing to Rusholme

Thank you for your interest in contributing to Rusholme!

## Development Setup

Rusholme uses [Nix](https://nixos.org/) with flakes for reproducible development.

```bash
# Enter the development environment
nix develop

# Or if Zig is already installed on your system:
zig build
```

## Running Tests

Zig's built-in test framework is used for unit tests across all modules.

```bash
# Run all tests
zig build test

# Run tests with verbose output
zig build test --summary all

# Run a specific test
zig build test -- --test-filter "test name"

# Run tests for the library module only
zig build test-lib
```

### Test Conventions

#### Location

- Unit tests live alongside the code they test in the same `.zig` file
- Each module's `test` blocks are discovered automatically via `refAllDecls()`

#### Naming

- Test names should be descriptive: `test "SourceSpan.merge combines spans correctly"`
- Use `--test-filter` to run specific tests by pattern match

#### Running Tests

**Important:** Always use `zig build test` rather than `zig build` alone!

Zig uses lazy compilation — `zig build` only compiles code reachable from `main.zig`.
Since `main.zig` doesn't yet use all library modules, `zig build` alone won't catch
compilation errors in library code.

**Before committing:**

```bash
# ALWAYS run this to verify correctness
zig build test --summary all
```

The `--summary all` flag is critical — it prints the number of tests discovered
and their pass/fail status, confirming tests are actually running.

#### Test Discovery

The `src/root.zig` file ensures all submodule tests are discovered:

```zig
test {
    const testing = @import("std").testing;
    testing.refAllDecls(@This());
    testing.refAllDecls(diagnostics);
    testing.refAllDecls(frontend);
    testing.refAllDecls(core);
    testing.refAllDecls(grin);
    testing.refAllDecls(backend);
}
```

This pattern forces the test runner to discover tests across all submodules.

## Memory Safety: Zero-Leak Policy

Rusholme enforces a **zero-leak policy**. Every heap allocation must be paired
with a deallocation. No PR may be merged if it introduces a memory leak.

See [docs/decisions/002-zero-leak-strategy.md](docs/decisions/002-zero-leak-strategy.md)
for the full rationale.

### Rules

1. **All tests MUST use `std.testing.allocator`** (or `ArenaAllocator` wrapping
   it). This allocator automatically fails the test if any allocation is not
   freed.

2. **`main.zig` uses `GeneralPurposeAllocator`** with a `.deinit() == .ok`
   assertion. This catches leaks during development runs.

3. **Every allocation needs a corresponding `defer`**:
   ```zig
   const data = try allocator.alloc(u8, size);
   defer allocator.free(data);
   ```

4. **Use `errdefer` for error path cleanup**:
   ```zig
   const foo = try allocator.create(Foo);
   errdefer allocator.destroy(foo);

   const bar = try initBar(allocator); // if this fails, foo is freed
   ```

5. **Use `ArenaAllocator` for batch temporary allocations**:
   ```zig
   var arena = std.heap.ArenaAllocator.init(parent_allocator);
   defer arena.deinit(); // frees everything at once
   const allocator = arena.allocator();
   ```

6. **Pass allocators explicitly** — never use global allocators. All functions
   that allocate take `allocator: std.mem.Allocator` as a parameter.

### What the tooling catches

| Layer | Tool | Catches |
|-------|------|---------|
| Unit tests | `std.testing.allocator` | Zig-side leaks per test |
| Debug builds | GPA with `.deinit()` check | Zig-side leaks in full runs |
| C interop | Valgrind (future, see #109) | LLVM C API leaks |

## Coding Standards

- **Read before writing.** Always read existing code before modifying.
- **Follow existing conventions.** Match the style of surrounding code.
- **No dead code.** Don't leave commented-out code or unused imports.
- **Source spans everywhere.** Every AST/IR node must carry a `SourceSpan`.
- **Errors are structured, not strings.** Use the `Diagnostic` infrastructure.
- **Write tests.** Every new feature needs unit tests.
- **Zero leaks.** Every test uses `std.testing.allocator`. Every allocation has a `defer` free.

## Project Structure

```
src/
  main.zig              -- CLI entry point
  root.zig              -- Library root, exports all public APIs
  diagnostics/          -- Structured error diagnostics
  frontend/             -- Lexer, parser, AST
  core/                 -- Core IR (System F_C)
  grin/                 -- GRIN IR
  backend/              -- LLVM code generation
  runtime/              -- Zig runtime for compiled programs
```

## Issue Workflow

1. Pick an issue from [ROADMAP.md](ROADMAP.md) with all dependencies done
2. Create a feature branch: `git checkout -b feat/issue-<NUMBER>`
3. Work on the issue (follow CLAUDE.md for instructions)
4. Run tests: `zig build test --summary all`
5. Commit and push: `git push origin feat/issue-<NUMBER>`
6. Open a PR for review

See [CLAUDE.md](CLAUDE.md) for complete workflow instructions.

## License

Not yet decided. For now, consider this code available for reading and learning.
