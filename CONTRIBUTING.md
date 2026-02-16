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

## Coding Standards

- **Read before writing.** Always read existing code before modifying.
- **Follow existing conventions.** Match the style of surrounding code.
- **No dead code.** Don't leave commented-out code or unused imports.
- **Source spans everywhere.** Every AST/IR node must carry a `SourceSpan`.
- **Errors are structured, not strings.** Use the `Diagnostic` infrastructure.
- **Write tests.** Every new feature needs unit tests.

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
