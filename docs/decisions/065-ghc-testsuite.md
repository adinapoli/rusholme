# Decision 065: Research and Import GHC Testsuite Programs

## Context

Rusholme needs real-world Haskell programs to validate its parser (and later,
its full pipeline). GHC's testsuite is the canonical source of Haskell test
programs covering the full language surface.

## GHC Testsuite Structure

The GHC testsuite lives at
<https://gitlab.haskell.org/ghc/ghc/-/tree/master/testsuite>.

### Directory layout

| Directory | Purpose |
|---|---|
| `tests/typecheck/should_compile/` | Type-checking programs that must compile |
| `tests/typecheck/should_run/` | Type-checking programs that must run correctly |
| `tests/codeGen/should_run/` | Code generation programs with expected output |
| `tests/simplCore/` | Core-to-Core simplification tests |
| `tests/parser/should_compile/` | Parser tests that must compile |
| `tests/parser/should_fail/` | Parser tests that must fail |
| `tests/ghci/` | GHCi-specific tests |
| `tests/programs/` | Complete programs exercising multiple features |

Each test directory contains `.hs` source files alongside a `*.T` driver file
(Python) that specifies how to run the test, expected output, and any flags.
Expected stdout/stderr go in `.stdout` and `.stderr` files.

### Licensing

GHC is licensed under **BSD-3-Clause**. The testsuite files carry the same
licence. We can freely import and redistribute them provided we retain the
copyright notice. The GHC licence file is at
<https://gitlab.haskell.org/ghc/ghc/-/blob/master/LICENSE>.

**Conclusion:** We can reuse GHC test programs without licensing concerns.

## Selection Criteria

For Rusholme's current stage (parser + lexer complete, no type checker or code
generation yet), we selected programs that:

1. **Use only Haskell 2010 features** — no GHC extensions (unless tagged skip).
2. **Are short** — under 20 lines, to keep golden tests readable.
3. **Cover distinct language features** — one feature per test where possible.
4. **Are self-contained** — no external module dependencies beyond Prelude.

## Imported Tests

### Golden tests (`tests/golden/`) — parse-only

These test that the parser accepts valid Haskell 2010 syntax. They do not
require a runtime.

| File | Feature exercised | Status |
|---|---|---|
| `ghc_001_qualified_import.hs` | Qualified imports | Active |
| `ghc_002_fixity.hs` | Fixity declarations, operator constructors | Active |
| `ghc_003_layout.hs` | Layout rule with `do`/`where` | Active |
| `ghc_004_empty_decls.hs` | Explicit braces, empty declarations | Active |
| `ghc_005_simple_function.hs` | Function definitions, type signatures | Active |
| `ghc_006_adt.hs` | Algebraic data types | Active |
| `ghc_007_pattern_matching.hs` | Pattern matching | Active |
| `ghc_008_typeclass.hs` | Type class and instance declarations | Active |
| `ghc_009_deriving.hs` | Deriving clauses | Active |
| `ghc_010_gadt.hs` | GADT-style declarations | **Skip** (GHC extension) |
| `ghc_011_record.hs` | Record syntax | **Skip** (not yet implemented) |
| `ghc_012_type_operator.hs` | Type operators in data declarations | **Skip** (not yet implemented) |
| `ghc_013_newtype.hs` | Newtype declarations | Active |
| `ghc_014_type_synonym.hs` | Type synonyms | Active |
| `ghc_015_tuples.hs` | Tuple types and expressions | **Skip** (not yet implemented) |

### End-to-end tests (`tests/e2e/`) — parse + expected output

These will eventually test the full pipeline (parse → compile → run). For now
they are all tagged **skip** because the runtime does not exist yet. Each `.hs`
file has a corresponding `.stdout` with expected output.

| File | Feature exercised | Status |
|---|---|---|
| `ghc_001_negative_literal.hs` | Negative literals | Skip |
| `ghc_002_nested_where.hs` | Nested `where` clauses | Skip |
| `ghc_003_sk_combinators.hs` | Higher-order functions (S/K combinators) | Skip |
| `ghc_004_length.hs` | List literals, `length` | Skip |
| `ghc_005_arithmetic.hs` | Integer arithmetic | Skip |
| `ghc_006_infinite_list.hs` | Infinite lists, `take` | Skip |
| `ghc_007_tree.hs` | ADTs, recursion, `max` | Skip |
| `ghc_008_list_comprehension.hs` | List comprehensions | Skip |

### Sources

The programs are inspired by tests in the following GHC testsuite directories:

- `testsuite/tests/typecheck/should_compile/` — imports, fixity, layout
- `testsuite/tests/codeGen/should_run/` — arithmetic, combinators, trees
- `testsuite/tests/programs/` — complete runnable programs

Some tests were simplified or adapted to remove GHC-specific extensions while
preserving the language feature being exercised.

## Test Infrastructure

### Golden test runner (`tests/golden_test_runner.zig`)

A Zig test module that:

1. Iterates over all `.hs` files in `tests/golden/`.
2. For each file, checks for a `.properties` sidecar containing `skip:`.
3. If not skipped, lexes → layouts → parses the file and asserts success.
4. Reports pass/fail counts.

The runner is integrated into `build.zig` and runs as part of `zig build test`.

### Properties files

A simple key-value format for per-test configuration:

```
skip: reason for skipping
```

Lines starting with `#` are comments. This keeps test metadata out of the
Haskell source files.

## Recommendation

1. **Keep using the `.properties` sidecar approach** for skip/xfail metadata.
   It is simple, language-agnostic, and does not pollute the Haskell sources.

2. **Add more golden tests** as parser features are implemented (records,
   tuple types, type operators). When a feature lands, un-skip the
   corresponding test.

3. **Activate e2e tests incrementally** as the runtime pipeline is built out.
   Each e2e test already has its expected `.stdout`; a future e2e runner just
   needs to compile-and-run then diff the output.

4. **Respect GHC's BSD-3-Clause licence** by keeping attribution in this
   document and not stripping copyright headers from any imported files.
