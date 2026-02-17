# Rusholme Roadmap

> Auto-generated from GitHub issues. Each issue links to its tracker.
> **Starting points** (zero dependencies): #1✓, #2✓, #17✓, #22✓, #24✓, #27✓, #53✓, #85✓, #58, #62⚡, #66, #68, #107

**Recent Progress (2026-02-16):**
- ✓ #85: Lexer support for numeric literals (Dec, Hex, Oct, Bin, Float)
- ✓ #86: Lexer support for string and character literals (Escapes, Gaps, Mnemonics)
- ✓ #25: Lexer support for Identifiers, Keywords and Operators
- ✓ #26: Implement full Haskell 2010 layout rule

**Recent Progress (2026-02-15):**
- ✓ #1: GitHub Actions CI upgraded to Nix 2.18
- ✓ #17: SourceSpan and SourcePos types implemented
- ✓ #18: Diagnostic ADT implemented (structured error data)
- ✓ #22: Parser technique researched (hand-written recursive descent chosen)
- ✓ #23: Haskell lexer token types defined (full Haskell 2010 set)
- ✓ #24: Unicode character classification implemented
- ✓ #27: Full Haskell AST types defined
- ✓ #53: LLVM C API bindings created

---

## M0: Project Infrastructure

### CI & Project Layout

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#1](https://github.com/adinapoli/rusholme/issues/1) | Set up GitHub Actions CI via Nix flake | — | :green_circle: |
| [#2](https://github.com/adinapoli/rusholme/issues/2) | Establish modular project layout (src/ split by pipeline stage) | — | :green_circle: |

### Epic [#3](https://github.com/adinapoli/rusholme/issues/3): Structured Error Diagnostics

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#17](https://github.com/adinapoli/rusholme/issues/17) | Define SourceSpan and SourcePos types | — | :green_circle: |
| [#18](https://github.com/adinapoli/rusholme/issues/18) | Define Diagnostic ADT (errors as structured data, not strings) | [#17](https://github.com/adinapoli/rusholme/issues/17) | :green_circle: |
| [#19](https://github.com/adinapoli/rusholme/issues/19) | Implement DiagnosticCollector for accumulating errors across modules | [#18](https://github.com/adinapoli/rusholme/issues/18) | :green_circle: |
| [#20](https://github.com/adinapoli/rusholme/issues/20) | Implement terminal diagnostic renderer with source snippets | [#18](https://github.com/adinapoli/rusholme/issues/18) | :green_circle: |
| [#21](https://github.com/adinapoli/rusholme/issues/21) | Implement JSON diagnostic renderer | [#18](https://github.com/adinapoli/rusholme/issues/18) | :green_circle: |
| [#89](https://github.com/adinapoli/rusholme/issues/89) | Terminal Renderer: Source Code Snippets with Context | [#20](https://github.com/adinapoli/rusholme/issues/20) | :green_circle: |
| [#80](https://github.com/adinapoli/rusholme/issues/80) | #18: Define Diagnostic ADT (errors as structured data, not strings) | — | :green_circle: |
| [#81](https://github.com/adinapoli/rusholme/issues/81) | ci: Upgrade install-nix-action v23 → v31 | — | :green_circle: |
| [#83](https://github.com/adinapoli/rusholme/issues/83) | docs: add status badges to README | — | :green_circle: |

### Epic [#11](https://github.com/adinapoli/rusholme/issues/11): Testing Infrastructure

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#62](https://github.com/adinapoli/rusholme/issues/62) | Set up Zig test harness and project test structure | — | :green_circle: |
| [#63](https://github.com/adinapoli/rusholme/issues/63) | Implement golden/snapshot test runner | [#62](https://github.com/adinapoli/rusholme/issues/62) | :white_circle: |
| [#64](https://github.com/adinapoli/rusholme/issues/64) | Implement end-to-end test runner (compile + run + check stdout) | [#63](https://github.com/adinapoli/rusholme/issues/63) | :white_circle: |
| [#65](https://github.com/adinapoli/rusholme/issues/65) | Research and import simple test programs from GHC's testsuite | [#63](https://github.com/adinapoli/rusholme/issues/63) | :white_circle: |

### Epic [#106](https://github.com/adinapoli/rusholme/issues/106): Zero-Leak Compiler

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#107](https://github.com/adinapoli/rusholme/issues/107) | Research: Zero-leak enforcement strategy (GPA vs Valgrind vs hybrid) | — | :white_circle: |
| [#108](https://github.com/adinapoli/rusholme/issues/108) | Enforce std.testing.allocator in all tests and add GPA to main.zig | [#107](https://github.com/adinapoli/rusholme/issues/107) | :white_circle: |
| [#109](https://github.com/adinapoli/rusholme/issues/109) | Add Valgrind CI step for C interop leak detection | [#107](https://github.com/adinapoli/rusholme/issues/107) | :white_circle: |
| [#110](https://github.com/adinapoli/rusholme/issues/110) | Document zero-leak policy in CONTRIBUTING.md and DESIGN.md | [#107](https://github.com/adinapoli/rusholme/issues/107) | :white_circle: |

---

## M1: Hello World

> **Goal:** `main = putStrLn "Hello"` compiles and runs end-to-end.

### Epic [#4](https://github.com/adinapoli/rusholme/issues/4): Haskell Parser

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#22](https://github.com/adinapoli/rusholme/issues/22) | Research: Parser technique decision (tree-sitter vs Alex/Happy vs hand-written) | — | :green_circle: |
| [#23](https://github.com/adinapoli/rusholme/issues/23) | Define lexer token types for Haskell | [#22](https://github.com/adinapoli/rusholme/issues/22) | :green_circle: |
| [#24](https://github.com/adinapoli/rusholme/issues/24) | Implement Unicode character classification | — | :green_circle: |
| [#85](https://github.com/adinapoli/rusholme/issues/85) | Lexer: Numeric Literals | [#23](https://github.com/adinapoli/rusholme/issues/23), [#24](https://github.com/adinapoli/rusholme/issues/24) | :green_circle: |
| [#86](https://github.com/adinapoli/rusholme/issues/86) | Lexer: String and Character Literals | [#85](https://github.com/adinapoli/rusholme/issues/85) | :green_circle: |
| [#25](https://github.com/adinapoli/rusholme/issues/25) | Lexer: Identifiers, Keywords and Operators | [#85](https://github.com/adinapoli/rusholme/issues/85), [#86](https://github.com/adinapoli/rusholme/issues/86) | :green_circle: |
| [#26](https://github.com/adinapoli/rusholme/issues/26) | Implement full Haskell 2010 layout rule | [#25](https://github.com/adinapoli/rusholme/issues/25) | :green_circle: |
| [#27](https://github.com/adinapoli/rusholme/issues/27) | Define Haskell AST types (module, declarations, expressions, patterns, types) | [#17](https://github.com/adinapoli/rusholme/issues/17) | :green_circle: |
| [#28](https://github.com/adinapoli/rusholme/issues/28) | Implement AST pretty-printer for debugging and golden tests | [#27](https://github.com/adinapoli/rusholme/issues/27) | :green_circle: |
| [#87](https://github.com/adinapoli/rusholme/issues/87) | Parser: Infrastructure, Combinators and Error Recovery | [#26](https://github.com/adinapoli/rusholme/issues/26), [#19](https://github.com/adinapoli/rusholme/issues/19) | :green_circle: |
| [#29](https://github.com/adinapoli/rusholme/issues/29) | Implement parser: module header, imports, and top-level declarations | [#26](https://github.com/adinapoli/rusholme/issues/26), [#27](https://github.com/adinapoli/rusholme/issues/27) | :green_circle: |
| [#88](https://github.com/adinapoli/rusholme/issues/88) | Parser: Expression Precedence (Fixity-aware) | [#87](https://github.com/adinapoli/rusholme/issues/87), [#27](https://github.com/adinapoli/rusholme/issues/27) | :white_circle: |
| [#30](https://github.com/adinapoli/rusholme/issues/30) | Implement parser: expressions | [#29](https://github.com/adinapoli/rusholme/issues/29), [#88](https://github.com/adinapoli/rusholme/issues/88) | :white_circle: |
| [#31](https://github.com/adinapoli/rusholme/issues/31) | Implement parser: patterns | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#32](https://github.com/adinapoli/rusholme/issues/32) | Implement parser: type expressions | [#29](https://github.com/adinapoli/rusholme/issues/29) | :white_circle: |
| [#33](https://github.com/adinapoli/rusholme/issues/33) | Implement parser: class and instance declarations, deriving | [#29](https://github.com/adinapoli/rusholme/issues/29), [#32](https://github.com/adinapoli/rusholme/issues/32) | :white_circle: |
| [#82](https://github.com/adinapoli/rusholme/issues/82) | #23: Define lexer token types for Haskell | — | :green_circle: |

### Research: Cross-cutting Decisions

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#68](https://github.com/adinapoli/rusholme/issues/68) | Research: Name uniqueness strategy (De Bruijn vs Unique supply vs hybrid) | — | :green_circle: |
| [#69](https://github.com/adinapoli/rusholme/issues/69) | Implement chosen name uniqueness mechanism | [#68](https://github.com/adinapoli/rusholme/issues/68) | :green_circle: |
| [#66](https://github.com/adinapoli/rusholme/issues/66) | Research: Calling convention (eval/apply vs push/enter vs CPS) | — | :green_circle: |
| [#67](https://github.com/adinapoli/rusholme/issues/67) | Implement chosen calling convention in runtime and codegen | [#66](https://github.com/adinapoli/rusholme/issues/66), [#54](https://github.com/adinapoli/rusholme/issues/54) | :white_circle: |

### Epic [#5](https://github.com/adinapoli/rusholme/issues/5): Core IR (System F_C)

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#34](https://github.com/adinapoli/rusholme/issues/34) | Define Core IR types (System F_C expressions, binders, types) | [#69](https://github.com/adinapoli/rusholme/issues/69) | :white_circle: |
| [#35](https://github.com/adinapoli/rusholme/issues/35) | Implement Core IR pretty-printer | [#34](https://github.com/adinapoli/rusholme/issues/34) | :white_circle: |
| [#36](https://github.com/adinapoli/rusholme/issues/36) | Implement Hindley-Milner type inference engine | [#34](https://github.com/adinapoli/rusholme/issues/34), [#18](https://github.com/adinapoli/rusholme/issues/18) | :white_circle: |
| [#37](https://github.com/adinapoli/rusholme/issues/37) | Implement type class resolution and dictionary passing | [#36](https://github.com/adinapoli/rusholme/issues/36) | :white_circle: |
| [#38](https://github.com/adinapoli/rusholme/issues/38) | Implement desugarer (AST to Core translation) | [#36](https://github.com/adinapoli/rusholme/issues/36), [#27](https://github.com/adinapoli/rusholme/issues/27) | :white_circle: |
| [#39](https://github.com/adinapoli/rusholme/issues/39) | Implement Core lint (type-check Core IR for internal consistency) | [#34](https://github.com/adinapoli/rusholme/issues/34) | :white_circle: |

### Epic [#6](https://github.com/adinapoli/rusholme/issues/6): GRIN IR and Core→GRIN Translation

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#40](https://github.com/adinapoli/rusholme/issues/40) | Define GRIN IR types (Modern GRIN dialect) | [#69](https://github.com/adinapoli/rusholme/issues/69) | :white_circle: |
| [#41](https://github.com/adinapoli/rusholme/issues/41) | Implement GRIN IR pretty-printer | [#40](https://github.com/adinapoli/rusholme/issues/40) | :white_circle: |
| [#42](https://github.com/adinapoli/rusholme/issues/42) | Research: Core to GRIN translation strategy | [#34](https://github.com/adinapoli/rusholme/issues/34), [#40](https://github.com/adinapoli/rusholme/issues/40) | :white_circle: |
| [#43](https://github.com/adinapoli/rusholme/issues/43) | Implement Core to GRIN translation | [#42](https://github.com/adinapoli/rusholme/issues/42) | :white_circle: |

### Epic [#8](https://github.com/adinapoli/rusholme/issues/8): Tree-Walking Interpreter

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#50](https://github.com/adinapoli/rusholme/issues/50) | Implement GRIN tree-walking evaluator (core eval loop) | [#40](https://github.com/adinapoli/rusholme/issues/40) | :white_circle: |
| [#51](https://github.com/adinapoli/rusholme/issues/51) | Implement basic IO primitives for the interpreter (putStrLn, getLine) | [#50](https://github.com/adinapoli/rusholme/issues/50) | :white_circle: |
| [#52](https://github.com/adinapoli/rusholme/issues/52) | Implement arithmetic and comparison primitives for the interpreter | [#50](https://github.com/adinapoli/rusholme/issues/50) | :white_circle: |

### Epic [#9](https://github.com/adinapoli/rusholme/issues/9): LLVM Backend and Zig Runtime

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#53](https://github.com/adinapoli/rusholme/issues/53) | Set up LLVM C API bindings in Zig | — | :large_blue_circle: |
| [#54](https://github.com/adinapoli/rusholme/issues/54) | Implement LLVM codegen skeleton (module, function defs, entry point) | [#53](https://github.com/adinapoli/rusholme/issues/53), [#40](https://github.com/adinapoli/rusholme/issues/40) | :white_circle: |
| [#55](https://github.com/adinapoli/rusholme/issues/55) | Implement LLVM codegen for GRIN expressions (store/fetch/update/case/app) | [#54](https://github.com/adinapoli/rusholme/issues/54) | :white_circle: |
| [#56](https://github.com/adinapoli/rusholme/issues/56) | Implement Zig runtime (heap allocator, thunk evaluator, entry point) | [#53](https://github.com/adinapoli/rusholme/issues/53) | :white_circle: |
| [#57](https://github.com/adinapoli/rusholme/issues/57) | Implement end-to-end: LLVM compile + link with Zig runtime + produce executable | [#55](https://github.com/adinapoli/rusholme/issues/55), [#56](https://github.com/adinapoli/rusholme/issues/56) | :white_circle: |

---

## M2: Basic Programs

> **Goal:** ADTs, pattern matching, type classes, modules, minimal Prelude.

### Epic [#10](https://github.com/adinapoli/rusholme/issues/10): Minimal Prelude

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#58](https://github.com/adinapoli/rusholme/issues/58) | Research: Survey existing minimal Preludes from teaching compilers | — | :white_circle: |
| [#59](https://github.com/adinapoli/rusholme/issues/59) | Implement Prelude basic types (Bool, Int, Char, Maybe, Either, IO, lists, tuples) | [#58](https://github.com/adinapoli/rusholme/issues/58), [#38](https://github.com/adinapoli/rusholme/issues/38) | :white_circle: |
| [#60](https://github.com/adinapoli/rusholme/issues/60) | Implement Prelude type classes (Eq, Ord, Show, Read, Num, Monad) | [#59](https://github.com/adinapoli/rusholme/issues/59), [#37](https://github.com/adinapoli/rusholme/issues/37) | :white_circle: |
| [#61](https://github.com/adinapoli/rusholme/issues/61) | Implement Prelude core functions (id, const, map, filter, foldr, foldl, etc.) | [#60](https://github.com/adinapoli/rusholme/issues/60) | :white_circle: |

### Epic [#14](https://github.com/adinapoli/rusholme/issues/14): Memory Management (Arena → Immix GC)

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#70](https://github.com/adinapoli/rusholme/issues/70) | Define runtime allocator interface for GC-swappable heap | [#56](https://github.com/adinapoli/rusholme/issues/56) | :white_circle: |
| [#71](https://github.com/adinapoli/rusholme/issues/71) | Implement Immix block and line allocator | [#70](https://github.com/adinapoli/rusholme/issues/70) | :white_circle: |
| [#72](https://github.com/adinapoli/rusholme/issues/72) | Implement Immix mark-and-sweep collection | [#71](https://github.com/adinapoli/rusholme/issues/71) | :white_circle: |
| [#73](https://github.com/adinapoli/rusholme/issues/73) | Implement Immix opportunistic defragmentation | [#72](https://github.com/adinapoli/rusholme/issues/72) | :white_circle: |
| [#74](https://github.com/adinapoli/rusholme/issues/74) | Research: ASAP-style static deallocation via GRIN analysis | [#44](https://github.com/adinapoli/rusholme/issues/44) | :white_circle: |

---

## M3: GRIN Optimisations

> **Goal:** Dead code elimination, unboxing, heap-to-stack, heap points-to analysis.

### Epic [#7](https://github.com/adinapoli/rusholme/issues/7): GRIN Optimisation Passes

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#44](https://github.com/adinapoli/rusholme/issues/44) | Implement heap points-to analysis for GRIN | [#40](https://github.com/adinapoli/rusholme/issues/40) | :white_circle: |
| [#45](https://github.com/adinapoli/rusholme/issues/45) | Implement GRIN dead code elimination | [#44](https://github.com/adinapoli/rusholme/issues/44) | :white_circle: |
| [#46](https://github.com/adinapoli/rusholme/issues/46) | Implement evaluated case elimination | [#44](https://github.com/adinapoli/rusholme/issues/44) | :white_circle: |
| [#47](https://github.com/adinapoli/rusholme/issues/47) | Implement sparse case optimisation | [#44](https://github.com/adinapoli/rusholme/issues/44) | :white_circle: |
| [#48](https://github.com/adinapoli/rusholme/issues/48) | Implement unboxing optimisation | [#44](https://github.com/adinapoli/rusholme/issues/44) | :white_circle: |
| [#49](https://github.com/adinapoli/rusholme/issues/49) | Implement heap-to-stack conversion | [#44](https://github.com/adinapoli/rusholme/issues/44) | :white_circle: |

---

## M4: Multi-backend + Polish

> **Goal:** Wasm output, REPL, improved diagnostics.

### Epic [#15](https://github.com/adinapoli/rusholme/issues/15): REPL / Interactive Mode

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#75](https://github.com/adinapoli/rusholme/issues/75) | Implement basic REPL loop (read-eval-print with interpreter) | [#50](https://github.com/adinapoli/rusholme/issues/50), [#51](https://github.com/adinapoli/rusholme/issues/51) | :white_circle: |
| [#76](https://github.com/adinapoli/rusholme/issues/76) | Implement REPL auto-completion and multi-line input | [#75](https://github.com/adinapoli/rusholme/issues/75) | :white_circle: |

### Epic [#16](https://github.com/adinapoli/rusholme/issues/16): WebAssembly Output

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#77](https://github.com/adinapoli/rusholme/issues/77) | Configure LLVM backend to emit WebAssembly | [#57](https://github.com/adinapoli/rusholme/issues/57) | :white_circle: |
| [#78](https://github.com/adinapoli/rusholme/issues/78) | Port Zig runtime to WebAssembly (WASI) | [#77](https://github.com/adinapoli/rusholme/issues/77), [#56](https://github.com/adinapoli/rusholme/issues/56) | :white_circle: |
| [#79](https://github.com/adinapoli/rusholme/issues/79) | Run compiled Haskell in the browser via Wasm | [#78](https://github.com/adinapoli/rusholme/issues/78) | :white_circle: |

---

## Dependency Graph (Critical Path)

The longest dependency chain to M1 (`main = putStrLn "Hello"`):

```
#68 naming research
 └─► #69 unique supply
      ├─► #34 Core IR types ──► #36 HM inference ──► #38 desugarer
      └─► #40 GRIN IR types ──► #42 Core→GRIN research ──► #43 Core→GRIN impl
                               ├─► #50 GRIN evaluator ──► #51 IO primitives  ✓ interpreter path
                               └─► #54 LLVM codegen ──► #55 GRIN exprs ─┐
                                                                         ├─► #57 link & run  ✓ compiler path
                                                        #53✓ LLVM bindings ──► #56 Zig runtime ─┘

#17✓ SourceSpan ──► #18 diagnostics ──► #36 (also needs diagnostics)

#22✓ parser research ──► #23 tokens ─┐
#24✓ unicode ────────────────────────┼─► #25 lexer ──► #26 layout ──► #29 parser ──► #30/#31/#32/#33
#17✓ SourceSpan ─────────────────────┘
```

**Legend:** :white_circle: Not started | :large_blue_circle: In progress | :green_circle: Done
