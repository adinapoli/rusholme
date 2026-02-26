# Rusholme Roadmap

> Auto-generated from GitHub issues. Each issue links to its tracker.
> **Starting points** (zero dependencies): #1✓, #2✓, #17✓, #22✓, #24✓, #27✓, #53✓, #85✓, #58, #62⚡, #66, #68, #107✓

**Architecture Decisions:**
- **#0001**: PrimOps and RTS Architecture — defines the contract between compiler and runtime via ~15-30 primitive operations. See `docs/decisions/0001-primops-and-rts-architecture.md`.

**Recent Progress (2026-02-25):**
- ✓ #55: Implement LLVM codegen for GRIN expressions (M1 scope: App with PrimOpMapping, BUILDING.md)
- ✓ #321: End-to-end integration test: main = putStrLn "Hello" through GRIN evaluator

**Recent Progress (2026-02-26):**
- ◷ #407: Multiple equations not accepted (renamer Prelude shadowing + desugar InfixApp crash) — PR #408 open

**Recent Progress (2026-02-24):**
- ✓ #361: Implement remaining RExpr variants in desugarer
- ✓ #359: sc017_string_char_literals.hs doesn't pass the core desugaring
- ✓ #347: Implement proper backpatching for recursive let bindings in GRIN translator
- ✓ #351: Custom ADT type unification failures
- ✓ #350: Multi-equation function definitions treated as duplicates
- ✓ #349: Desugarer panics on unsolved metavariables in HType.toCore
- ✓ #317: Handle partial and over-application in Core→GRIN translation
- ✓ #315: Generate whole-program eval and apply functions for GRIN
- ✓ #320: Implement GRIN evaluator for App and Case expressions
- ✓ #319: Implement GRIN evaluator for simple expressions
- ✓ #318: Implement GRIN evaluator state: heap, environment, and function table
- ✓ #316: Add validation for duplicate record field names in data types
- ✓ #304: Fix unifier to handle rigid type (skolem) unification
- ✓ #139: Implement parser: field selectors

**Recent Progress (2026-02-23):**
- ✓ #314: Implement Core to GRIN translation for simple expressions
- ✓ #313: Implement lambda lifting pass on Core IR
- ✓ #330: Define PrimOps and implement GRIN evaluator dispatch

**Recent Progress (2026-02-22):**
- ✓ #184: typechecker: bidirectional signature checking for rank-N polymorphism
- ✓ #41: Implement GRIN IR pretty-printer
- ✓ #35: Implement Core IR pretty-printer
- ✓ #38: Implement desugarer / elaborator (typed AST → Core IR)
- ✓ #42: Research: Core to GRIN translation strategy
- ✓ #39: Implement Core lint (type-check Core IR for internal consistency)
- ✓ #277: Research: Thunk representation for Rusholme's runtime

**Recent Progress (2026-02-21):**
- ✓ #310: Core-checking sc004_record_syntax.hs doesn't recognise record functions
- ✓ #307: Core-checking sc004_record_syntax trigger renamer bug
- ✓ #302: core check doesn't work for sc004 (record syntax)
- ✓ #298: calling `core` on sc003_data_types.hs emits 0 bindings
- ✓ #288: Research: Evaluate zig-graph for dependency and analysis graphs
- ✓ #248: Improve diagnostics for typechecker cycle detection panics
- ✓ #246: Audit usages of `while(true)`
- ✓ #236: typechecker errors lack source file name and spans - shows '<unknown>:0:0-0'
- ✓ #183: typechecker: let-binding type signatures are ignored
- ✓ #216: ast: add LetQualifier variant to Qualifier for list comprehension let-bindings
- ✓ #218: Parser: backtick left sections with compound LHS
- ✓ #207: parser: layout rule too permissive — bad indentation accepted instead of rejected
- ✓ #250: Make `vtt-parser` program parse (VTT file added as test case)
- ✓ #263: typechecker: mutually recursive let-bindings with type signatures

**Recent Progress (2026-02-20):**
- ✓ #205: parser: record syntax in newtype declarations
- ✓ #256: lexer+parser: quasi-quotation syntax ([name| ... |])
- ✓ #255: lexer: LANGUAGE pragma support ({-# LANGUAGE #-})
- ✓ #254: lexer: string literal keyword parsing (resolved by quasiquotation fix)
- ✓ #252: parser: TypeApplications extension (e @Type)

**Recent Progress (2026-02-19):**
- ✓ #198: parser: operator function definitions and type signatures ((|>) x y = ...)
- ✓ #202: parser: fix operator sections with consym operators ((p ++) fails)
- ✓ #203: parser: fix where-clause after do-block (layout rule closes do context incorrectly)
- ✓ #193: lexer+parser: backtick infix operator syntax (`f`)
- ✓ #195: parser: superclass context in class declarations (class (Eq a) => ...)
- ✓ #204: parser: default method implementations in class declarations
- ✓ #136: parser: list comprehensions [e | x <- xs]

**Recent Progress (2026-02-18):**
- ✓ #196: parser: as-patterns (x@pat) in case alternatives and function args
- ✓ #194: parser: let-without-in as a do-statement binding
- ✓ #201: parser: negative float literal parsing (-3.14)
- ✓ #192: parser: arithmetic sequences ([e..], [e,e..], [e..e], [e,e..e])
- ✓ #65: Expanded parser test coverage to GHC-style should_compile / should_fail suite (62 new tests, 433 total); filed issues #192–#207 for discovered parser gaps
- ✓ #36: Implement Hindley-Milner type inference engine (Algorithm W) with let-polymorphism
- ✓ #174: Fix over-generalisation in generalisePtr (active-variables condition, Damas & Milner §3)
- ✓ #160: Migrate TyEnv lookup to Unique IDs
- ✓ #161: Wire built-ins to stable Unique IDs

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
| [#225](https://github.com/adinapoli/rusholme/issues/225) | infra: track libxev for future parallel compilation and LSP async I/O | — | :white_circle: |
| [#290](https://github.com/adinapoli/rusholme/issues/290) | Research: Evaluate toposort library for dependency ordering | — | :white_circle: |
| [#288](https://github.com/adinapoli/rusholme/issues/288) | Research: Evaluate zig-graph for dependency and analysis graphs | — | :green_circle: |

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
| [#65](https://github.com/adinapoli/rusholme/issues/65) | Research and import simple test programs from GHC's testsuite | [#63](https://github.com/adinapoli/rusholme/issues/63) | :green_circle: |

### Epic [#106](https://github.com/adinapoli/rusholme/issues/106): Zero-Leak Compiler

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#107](https://github.com/adinapoli/rusholme/issues/107) | Research: Zero-leak enforcement strategy (GPA vs Valgrind vs hybrid) | — | :green_circle: |
| [#108](https://github.com/adinapoli/rusholme/issues/108) | Enforce std.testing.allocator in all tests and add GPA to main.zig | [#107](https://github.com/adinapoli/rusholme/issues/107) | :green_circle: |
| [#109](https://github.com/adinapoli/rusholme/issues/109) | Add Valgrind CI step for C interop leak detection | [#107](https://github.com/adinapoli/rusholme/issues/107) | :white_circle: |
| [#110](https://github.com/adinapoli/rusholme/issues/110) | Document zero-leak policy in CONTRIBUTING.md and DESIGN.md | [#107](https://github.com/adinapoli/rusholme/issues/107) | :green_circle: |
| [#246](https://github.com/adinapoli/rusholme/issues/246) | infra: Audit usages of `while(true)` for potential improvements | — | :green_circle: |

---

## M1: Hello World

> **Goal:** `main = putStrLn "Hello"` compiles and runs end-to-end.

### Epic [#4](https://github.com/adinapoli/rusholme/issues/4): Haskell Parser

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#22](https://github.com/adinapoli/rusholme/issues/22) | Research: Parser technique decision (tree-sitter vs Alex/Happy vs hand-written) | — | :green_circle: |
| [#23](https://github.com/adinapoli/rusholme/issues/23) | Define lexer token types for Haskell | [#22](https://github.com/adinapoli/rusholme/issues/22) | :green_circle: |
| [#24](https://github.com/adinapoli/rusholme/issues/24) | Implement Unicode character classification | — | :green_circle: |
| [#224](https://github.com/adinapoli/rusholme/issues/224) | lexer: evaluate and adopt uucode for Unicode character classification | [#24](https://github.com/adinapoli/rusholme/issues/24) | :white_circle: |
| [#85](https://github.com/adinapoli/rusholme/issues/85) | Lexer: Numeric Literals | [#23](https://github.com/adinapoli/rusholme/issues/23), [#24](https://github.com/adinapoli/rusholme/issues/24) | :green_circle: |
| [#86](https://github.com/adinapoli/rusholme/issues/86) | Lexer: String and Character Literals | [#85](https://github.com/adinapoli/rusholme/issues/85) | :green_circle: |
| [#25](https://github.com/adinapoli/rusholme/issues/25) | Lexer: Identifiers, Keywords and Operators | [#85](https://github.com/adinapoli/rusholme/issues/85), [#86](https://github.com/adinapoli/rusholme/issues/86) | :green_circle: |
| [#26](https://github.com/adinapoli/rusholme/issues/26) | Implement full Haskell 2010 layout rule | [#25](https://github.com/adinapoli/rusholme/issues/25) | :green_circle: |
| [#27](https://github.com/adinapoli/rusholme/issues/27) | Define Haskell AST types (module, declarations, expressions, patterns, types) | [#17](https://github.com/adinapoli/rusholme/issues/17) | :green_circle: |
| [#28](https://github.com/adinapoli/rusholme/issues/28) | Implement AST pretty-printer for debugging and golden tests | [#27](https://github.com/adinapoli/rusholme/issues/27) | :green_circle: |
| [#87](https://github.com/adinapoli/rusholme/issues/87) | Parser: Infrastructure, Combinators and Error Recovery | [#26](https://github.com/adinapoli/rusholme/issues/26), [#19](https://github.com/adinapoli/rusholme/issues/19) | :green_circle: |
| [#29](https://github.com/adinapoli/rusholme/issues/29) | Implement parser: module header, imports, and top-level declarations | [#26](https://github.com/adinapoli/rusholme/issues/26), [#27](https://github.com/adinapoli/rusholme/issues/27) | :green_circle: |
| [#88](https://github.com/adinapoli/rusholme/issues/88) | Parser: Expression Precedence (Fixity-aware) | [#87](https://github.com/adinapoli/rusholme/issues/87), [#27](https://github.com/adinapoli/rusholme/issues/27) | :green_circle: |
| [#30](https://github.com/adinapoli/rusholme/issues/30) | Implement parser: expressions | [#29](https://github.com/adinapoli/rusholme/issues/29), [#88](https://github.com/adinapoli/rusholme/issues/88) | :green_circle: |
| [#31](https://github.com/adinapoli/rusholme/issues/31) | Implement parser: patterns | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#32](https://github.com/adinapoli/rusholme/issues/32) | Implement parser: type expressions | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#33](https://github.com/adinapoli/rusholme/issues/33) | Implement parser: class and instance declarations, deriving | [#29](https://github.com/adinapoli/rusholme/issues/29), [#32](https://github.com/adinapoli/rusholme/issues/32) | :green_circle: |
| [#82](https://github.com/adinapoli/rusholme/issues/82) | #23: Define lexer token types for Haskell | — | :green_circle: |
| [#133](https://github.com/adinapoli/rusholme/issues/133) | Implement parser: list literals | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#134](https://github.com/adinapoli/rusholme/issues/134) | Implement parser: tuple types and expressions | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#135](https://github.com/adinapoli/rusholme/issues/135) | Implement parser: record syntax | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#136](https://github.com/adinapoli/rusholme/issues/136) | Implement parser: list comprehensions | [#29](https://github.com/adinapoli/rusholme/issues/29), [#133](https://github.com/adinapoli/rusholme/issues/133) | :green_circle: |
| [#216](https://github.com/adinapoli/rusholme/issues/216) | ast: add LetQualifier variant to Qualifier for list comprehension let-bindings | [#136](https://github.com/adinapoli/rusholme/issues/136) | :green_circle: |
| [#137](https://github.com/adinapoli/rusholme/issues/137) | Implement parser: type operators | [#29](https://github.com/adinapoli/rusholme/issues/29), [#32](https://github.com/adinapoli/rusholme/issues/32) | :green_circle: |
| [#138](https://github.com/adinapoli/rusholme/issues/138) | Implement parser: bang patterns | [#29](https://github.com/adinapoli/rusholme/issues/29), [#31](https://github.com/adinapoli/rusholme/issues/31) | :green_circle: |
| [#139](https://github.com/adinapoli/rusholme/issues/139) | Implement parser: field selectors | [#29](https://github.com/adinapoli/rusholme/issues/29), [#135](https://github.com/adinapoli/rusholme/issues/135) | :green_circle: |
| [#140](https://github.com/adinapoli/rusholme/issues/140) | Implement parser: overloaded literals | [#29](https://github.com/adinapoli/rusholme/issues/29), [#32](https://github.com/adinapoli/rusholme/issues/32) | :white_circle: |
| [#192](https://github.com/adinapoli/rusholme/issues/192) | parser: implement arithmetic sequences ([e..], [e,e..], [e..e], [e,e..e]) | [#29](https://github.com/adinapoli/rusholme/issues/29), [#133](https://github.com/adinapoli/rusholme/issues/133) | :green_circle: |
| [#193](https://github.com/adinapoli/rusholme/issues/193) | lexer+parser: implement backtick infix operator syntax (`f`) | [#25](https://github.com/adinapoli/rusholme/issues/25), [#30](https://github.com/adinapoli/rusholme/issues/30) | :green_circle: |
| [#218](https://github.com/adinapoli/rusholme/issues/218) | Parser: backtick left sections require atomic LHS | [#193](https://github.com/adinapoli/rusholme/issues/193) | :green_circle: |
| [#194](https://github.com/adinapoli/rusholme/issues/194) | parser: implement let-without-in as a do-statement binding | [#30](https://github.com/adinapoli/rusholme/issues/30) | :green_circle: |
| [#195](https://github.com/adinapoli/rusholme/issues/195) | parser: implement superclass context in class declarations (class (Eq a) => ...) | [#33](https://github.com/adinapoli/rusholme/issues/33) | :green_circle: |
| [#196](https://github.com/adinapoli/rusholme/issues/196) | parser: implement as-patterns (x@pat) in case alternatives and function args | [#31](https://github.com/adinapoli/rusholme/issues/31) | :green_circle: |
| [#197](https://github.com/adinapoli/rusholme/issues/197) | parser: implement functional dependencies in class declarations (\| a -> b) | [#33](https://github.com/adinapoli/rusholme/issues/33) | :green_circle: |
| [#198](https://github.com/adinapoli/rusholme/issues/198) | parser: implement operator function definitions and type signatures ((\|>) x y = ...) | [#29](https://github.com/adinapoli/rusholme/issues/29), [#30](https://github.com/adinapoli/rusholme/issues/30) | :green_circle: |
| [#199](https://github.com/adinapoli/rusholme/issues/199) | parser: implement constrained and existential GADT constructors (forall / Class a =>) | [#29](https://github.com/adinapoli/rusholme/issues/29), [#32](https://github.com/adinapoli/rusholme/issues/32) | :green_circle: |
| [#200](https://github.com/adinapoli/rusholme/issues/200) | parser: implement multi-condition guards (\| g1, g2 = e) and pattern guards | [#30](https://github.com/adinapoli/rusholme/issues/30) | :green_circle: |
| [#201](https://github.com/adinapoli/rusholme/issues/201) | parser: fix negative float literal parsing (-3.14 fails with 'expected expression') | [#30](https://github.com/adinapoli/rusholme/issues/30) | :green_circle: |
| [#202](https://github.com/adinapoli/rusholme/issues/202) | parser: fix operator sections with consym operators ((p ++) fails) | [#30](https://github.com/adinapoli/rusholme/issues/30) | :green_circle: |
| [#203](https://github.com/adinapoli/rusholme/issues/203) | parser: fix where-clause after do-block (layout rule closes do context incorrectly) | [#26](https://github.com/adinapoli/rusholme/issues/26), [#30](https://github.com/adinapoli/rusholme/issues/30) | :green_circle: |
| [#204](https://github.com/adinapoli/rusholme/issues/204) | parser: implement default method implementations in class declarations | [#33](https://github.com/adinapoli/rusholme/issues/33) | :green_circle: |
| [#220](https://github.com/adinapoli/rusholme/issues/220) | ast/parser: class default methods only store first equation | [#204](https://github.com/adinapoli/rusholme/issues/204) | :green_circle: |
| [#205](https://github.com/adinapoli/rusholme/issues/205) | parser: implement record syntax in newtype declarations (depends on #135) | [#135](https://github.com/adinapoli/rusholme/issues/135) | :green_circle: |
| [#206](https://github.com/adinapoli/rusholme/issues/206) | parser: implement infix type constructors in data declaration heads (data a :+: b = ...) | [#29](https://github.com/adinapoli/rusholme/issues/29), [#137](https://github.com/adinapoli/rusholme/issues/137) | :green_circle: |
| [#207](https://github.com/adinapoli/rusholme/issues/207) | parser: layout rule too permissive — bad indentation accepted instead of rejected | [#26](https://github.com/adinapoli/rusholme/issues/26) | :green_circle: |
| [#230](https://github.com/adinapoli/rusholme/issues/230) | parser: fix guarded case alternatives (\| guard -> expr uses wrong arrow) | [#202](https://github.com/adinapoli/rusholme/issues/202) | :green_circle: |
| [#212](https://github.com/adinapoli/rusholme/issues/212) | lexer+ast: replace i64 integer literals with arbitrary-precision representation | [#85](https://github.com/adinapoli/rusholme/issues/85), [#27](https://github.com/adinapoli/rusholme/issues/27) | :white_circle: |
| [#232](https://github.com/adinapoli/rusholme/issues/232) | pattern guards: AST and parser incomplete for pat <- expr in guards | [#200](https://github.com/adinapoli/rusholme/issues/200) | :green_circle: |
| [#252](https://github.com/adinapoli/rusholme/issues/252) | parser: Support TypeApplications extension in expressions (e @Type) | [#30](https://github.com/adinapoli/rusholme/issues/30), [#32](https://github.com/adinapoli/rusholme/issues/32) | :green_circle: |
| [#250](https://github.com/adinapoli/rusholme/issues/250) | parser: support wildcard patterns in do notation bindings (completed via #252; VTT parser blocked by #254) | [#30](https://github.com/adinapoli/rusholme/issues/30), [#31](https://github.com/adinapoli/rusholme/issues/31), [#254](https://github.com/adinapoli/rusholme/issues/254) | :green_circle: |
| [#254](https://github.com/adinapoli/rusholme/issues/254) | lexer: string literal parsing fails when string contains keyword 'of' (resolved by quasiquotation fix) | [#86](https://github.com/adinapoli/rusholme/issues/86) | :green_circle: |
| [#255](https://github.com/adinapoli/rusholme/issues/255) | parser: support LANGUAGE pragmas ({-# LANGUAGE ... #-}) | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#256](https://github.com/adinapoli/rusholme/issues/256) | parser: support quasi-quotation syntax ([name\| ... \|]) | [#29](https://github.com/adinapoli/rusholme/issues/29) | :green_circle: |
| [#316](https://github.com/adinapoli/rusholme/issues/316) | Add validation for duplicate record field names in data types | [#135](https://github.com/adinapoli/rusholme/issues/135) | :white_circle: |

### CLI

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#142](https://github.com/adinapoli/rusholme/issues/142) | Implement rhc CLI with parse subcommand | [#28](https://github.com/adinapoli/rusholme/issues/28), [#33](https://github.com/adinapoli/rusholme/issues/33), [#20](https://github.com/adinapoli/rusholme/issues/20) | :green_circle: |
| [#144](https://github.com/adinapoli/rusholme/issues/144) | Syntax highlighting for pretty-printed AST output | [#142](https://github.com/adinapoli/rusholme/issues/142) | :white_circle: |
| [#145](https://github.com/adinapoli/rusholme/issues/145) | Shell completion (bash/zsh/fish) for rhc CLI | [#142](https://github.com/adinapoli/rusholme/issues/142) | :white_circle: |

### Research: Cross-cutting Decisions

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#68](https://github.com/adinapoli/rusholme/issues/68) | Research: Name uniqueness strategy (De Bruijn vs Unique supply vs hybrid) | — | :green_circle: |
| [#69](https://github.com/adinapoli/rusholme/issues/69) | Implement chosen name uniqueness mechanism | [#68](https://github.com/adinapoli/rusholme/issues/68) | :green_circle: |
| [#66](https://github.com/adinapoli/rusholme/issues/66) | Research: Calling convention (eval/apply vs push/enter vs CPS) | — | :green_circle: |
| [#67](https://github.com/adinapoli/rusholme/issues/67) | Implement chosen calling convention in runtime and codegen | [#66](https://github.com/adinapoli/rusholme/issues/66), [#54](https://github.com/adinapoli/rusholme/issues/54) | :white_circle: |
| [#277](https://github.com/adinapoli/rusholme/issues/277) | Research: Thunk representation for Rusholme's runtime | [#66](https://github.com/adinapoli/rusholme/issues/66) | :green_circle: |

### Epic [#154](https://github.com/adinapoli/rusholme/issues/154): Typechecker, Renamer & Desugarer (AST → Core)

> Architecture decision: **bidirectional typechecking + constraint-based elaboration**.
> See `docs/decisions/005-typechecking-approach.md`.

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#148](https://github.com/adinapoli/rusholme/issues/148) | Research: Typechecking approach (bidirectional TC + constraint elaboration) | — | :green_circle: |
| [#149](https://github.com/adinapoli/rusholme/issues/149) | Implement Renamer: resolve AST names to unique Names and check scope | [#27](https://github.com/adinapoli/rusholme/issues/27), [#69](https://github.com/adinapoli/rusholme/issues/69) | :green_circle: |
| [#150](https://github.com/adinapoli/rusholme/issues/150) | Define HType: internal typechecker type with unification metavariables | [#34](https://github.com/adinapoli/rusholme/issues/34) | :green_circle: |
| [#151](https://github.com/adinapoli/rusholme/issues/151) | Implement Robinson unification with occurs check over HType | [#150](https://github.com/adinapoli/rusholme/issues/150) | :green_circle: |
| [#152](https://github.com/adinapoli/rusholme/issues/152) | Implement TyEnv: scoped type environment for the typechecker | [#150](https://github.com/adinapoli/rusholme/issues/150) | :green_circle: |
| [#153](https://github.com/adinapoli/rusholme/issues/153) | Implement Constraint Solver: equality constraints and substitution | [#151](https://github.com/adinapoli/rusholme/issues/151) | :green_circle: |
| [#160](https://github.com/adinapoli/rusholme/issues/160) | TyEnv: migrate lookup key from base name string to unique ID after renamer | [#149](https://github.com/adinapoli/rusholme/issues/149), [#152](https://github.com/adinapoli/rusholme/issues/152) | :green_circle: |
| [#161](https://github.com/adinapoli/rusholme/issues/161) | TyEnv: wire initBuiltins into renamer known-key table for stable Name values | [#149](https://github.com/adinapoli/rusholme/issues/149), [#160](https://github.com/adinapoli/rusholme/issues/160) | :green_circle: |
| [#163](https://github.com/adinapoli/rusholme/issues/163) | Proper HType pretty-printer for diagnostic messages | [#153](https://github.com/adinapoli/rusholme/issues/153) | :green_circle: |
| [#165](https://github.com/adinapoli/rusholme/issues/165) | Structured TypeError payload in Diagnostic (replace stringly-typed messages) | [#153](https://github.com/adinapoli/rusholme/issues/153), [#163](https://github.com/adinapoli/rusholme/issues/163) | :green_circle: |
| [#166](https://github.com/adinapoli/rusholme/issues/166) | Add SourceSpan to ast.Pattern.Var to eliminate synthetic spans in renamer | [#149](https://github.com/adinapoli/rusholme/issues/149) | :green_circle: |
| [#167](https://github.com/adinapoli/rusholme/issues/167) | Stable Unique values for built-in names across compilation units | [#149](https://github.com/adinapoli/rusholme/issues/149), [#161](https://github.com/adinapoli/rusholme/issues/161) | :green_circle: |
| [#36](https://github.com/adinapoli/rusholme/issues/36) | Implement bidirectional typechecker (synth + check modes) | [#149](https://github.com/adinapoli/rusholme/issues/149), [#150](https://github.com/adinapoli/rusholme/issues/150), [#152](https://github.com/adinapoli/rusholme/issues/152) | :green_circle: |
| [#174](https://github.com/adinapoli/rusholme/issues/174) | typechecker: generalisePtr passes empty env_types, risking over-generalisation | [#36](https://github.com/adinapoli/rusholme/issues/36) | :green_circle: |
| [#175](https://github.com/adinapoli/rusholme/issues/175) | typechecker: type signatures are ignored during inference | [#36](https://github.com/adinapoli/rusholme/issues/36) | :green_circle: |
| [#176](https://github.com/adinapoli/rusholme/issues/176) | typechecker: do-notation inference is hard-coded to IO, not generic Monad | [#36](https://github.com/adinapoli/rusholme/issues/36), [#37](https://github.com/adinapoli/rusholme/issues/37) | :green_circle: |
| [#183](https://github.com/adinapoli/rusholme/issues/183) | typechecker: let-binding type signatures are ignored | [#175](https://github.com/adinapoli/rusholme/issues/175) | :green_circle: |
| [#263](https://github.com/adinapoli/rusholme/issues/263) | typechecker: mutually recursive let-bindings with type signatures not fully supported | [#183](https://github.com/adinapoli/rusholme/issues/183) | :green_circle: |
| [#184](https://github.com/adinapoli/rusholme/issues/184) | typechecker: bidirectional signature checking for rank-N polymorphism | [#175](https://github.com/adinapoli/rusholme/issues/175) | :green_circle: |
| [#236](https://github.com/adinapoli/rusholme/issues/236) | typechecker: errors lack source file name and spans - shows '<unknown>:0:0-0' | [#184](https://github.com/adinapoli/rusholme/issues/184) | :green_circle: |
| [#248](https://github.com/adinapoli/rusholme/issues/248) | typechecker: Improve diagnostics for cycle detection panics | [#184](https://github.com/adinapoli/rusholme/issues/184) | :green_circle: |
| [#177](https://github.com/adinapoli/rusholme/issues/177) | typechecker: astTypeToHType incomplete — App, Paren, Forall, n-tuples not handled | [#36](https://github.com/adinapoli/rusholme/issues/36) | :green_circle: |
| [#304](https://github.com/adinapoli/rusholme/issues/304) | Unifier: fix rigid type (skolem) unification | [#36](https://github.com/adinapoli/rusholme/issues/36) | :white_circle: |
| [#37](https://github.com/adinapoli/rusholme/issues/37) | Implement type class resolution and dictionary passing | [#36](https://github.com/adinapoli/rusholme/issues/36), [#153](https://github.com/adinapoli/rusholme/issues/153) | :green_circle: |
| [#38](https://github.com/adinapoli/rusholme/issues/38) | Implement desugarer / elaborator (typed AST → Core IR) | [#36](https://github.com/adinapoli/rusholme/issues/36), [#153](https://github.com/adinapoli/rusholme/issues/153) | :green_circle: |

### Epic [#5](https://github.com/adinapoli/rusholme/issues/5): Core IR (System F_C)

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#34](https://github.com/adinapoli/rusholme/issues/34) | Define Core IR types (System F_C expressions, binders, types) | [#69](https://github.com/adinapoli/rusholme/issues/69) | :green_circle: |
| [#35](https://github.com/adinapoli/rusholme/issues/35) | Implement Core IR pretty-printer | [#34](https://github.com/adinapoli/rusholme/issues/34) | :green_circle: |
| [#39](https://github.com/adinapoli/rusholme/issues/39) | Implement Core lint (type-check Core IR for internal consistency) | [#34](https://github.com/adinapoli/rusholme/issues/34) | :green_circle: |
| [#298](https://github.com/adinapoli/rusholme/issues/298) | core: fix binding emission for sc003_data_types.hs (0 bindings emitted) | [#38](https://github.com/adinapoli/rusholme/issues/38) | :green_circle: |
| [#302](https://github.com/adinapoli/rusholme/issues/302) | core: fix lint for sc004 (record syntax validation) | [#39](https://github.com/adinapoli/rusholme/issues/39) | :green_circle: |
| [#307](https://github.com/adinapoli/rusholme/issues/307) | core: fix sc004_record_syntax renamer bug (triggered by record functions) | [#302](https://github.com/adinapoli/rusholme/issues/302) | :green_circle: |
| [#310](https://github.com/adinapoli/rusholme/issues/310) | core: fix record function recognition in sc004_record_syntax.hs | [#307](https://github.com/adinapoli/rusholme/issues/307) | :green_circle: |
| [#349](https://github.com/adinapoli/rusholme/issues/349) | core: desugarer panics on unsolved metavariables in HType.toCore | [#38](https://github.com/adinapoli/rusholme/issues/38) | :green_circle: |
| [#350](https://github.com/adinapoli/rusholme/issues/350) | core: multi-equation function definitions treated as duplicates | [#38](https://github.com/adinapoli/rusholme/issues/38) | :green_circle: |
| [#351](https://github.com/adinapoli/rusholme/issues/351) | core: custom ADT type unification failures | [#38](https://github.com/adinapoli/rusholme/issues/38) | :green_circle: |
| [#359](https://github.com/adinapoli/rusholme/issues/359) | core: sc017_string_char_literals.hs doesn't pass the core desugaring | [#38](https://github.com/adinapoli/rusholme/issues/38) | :green_circle: |
| [#361](https://github.com/adinapoli/rusholme/issues/361) | Implement remaining RExpr variants in desugarer | [#359](https://github.com/adinapoli/rusholme/issues/359) | :green_circle: |
| [#407](https://github.com/adinapoli/rusholme/issues/407) | Multiple equations not accepted (renamer Prelude shadowing + desugar InfixApp crash) | [#38](https://github.com/adinapoli/rusholme/issues/38) | :yellow_circle: |

### Epic [#6](https://github.com/adinapoli/rusholme/issues/6): GRIN IR and Core→GRIN Translation

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#40](https://github.com/adinapoli/rusholme/issues/40) | Define GRIN IR types (Modern GRIN dialect) | [#69](https://github.com/adinapoli/rusholme/issues/69) | :green_circle: |
| [#41](https://github.com/adinapoli/rusholme/issues/41) | Implement GRIN IR pretty-printer | [#40](https://github.com/adinapoli/rusholme/issues/40) | :green_circle: |
| [#42](https://github.com/adinapoli/rusholme/issues/42) | Research: Core to GRIN translation strategy | [#34](https://github.com/adinapoli/rusholme/issues/34), [#40](https://github.com/adinapoli/rusholme/issues/40) | :green_circle: |
| [#313](https://github.com/adinapoli/rusholme/issues/313) | Implement lambda lifting pass on Core IR | [#42](https://github.com/adinapoli/rusholme/issues/42) | :green_circle: |
| [#314](https://github.com/adinapoli/rusholme/issues/314) | Implement Core to GRIN translation for simple expressions | [#313](https://github.com/adinapoli/rusholme/issues/313), [#41](https://github.com/adinapoli/rusholme/issues/41), [#42](https://github.com/adinapoli/rusholme/issues/42) | :green_circle: |
| [#315](https://github.com/adinapoli/rusholme/issues/315) | Generate whole-program eval and apply functions for GRIN | [#314](https://github.com/adinapoli/rusholme/issues/314) | :green_circle: |
| [#317](https://github.com/adinapoli/rusholme/issues/317) | Handle partial application and over-application in Core→GRIN | [#314](https://github.com/adinapoli/rusholme/issues/314), [#315](https://github.com/adinapoli/rusholme/issues/315) | :green_circle: |
| [#347](https://github.com/adinapoli/rusholme/issues/347) | Implement proper backpatching for recursive let bindings in GRIN translator | [#314](https://github.com/adinapoli/rusholme/issues/314) | :green_circle: |

### Epic: PrimOps and Runtime System (Decision #0001)

> Architecture: ~15-30 PrimOps form the contract between compiler and RTS.
> Prelude functions are implemented in Haskell, calling down to PrimOps.
> See `docs/decisions/0001-primops-and-rts-architecture.md`.

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#330](https://github.com/adinapoli/rusholme/issues/330) | Define PrimOps and implement GRIN evaluator dispatch | [#40](https://github.com/adinapoli/rusholme/issues/40) | :green_circle: |
| [#325](https://github.com/adinapoli/rusholme/issues/325) | Implement token-passing IO for lazy semantics | [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#326](https://github.com/adinapoli/rusholme/issues/326) | Implement exception handling in the RTS | [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#327](https://github.com/adinapoli/rusholme/issues/327) | Integrate GC with PrimOp allocations | [#330](https://github.com/adinapoli/rusholme/issues/330), [#70](https://github.com/adinapoli/rusholme/issues/70) | :white_circle: |
| [#328](https://github.com/adinapoli/rusholme/issues/328) | Add runtime stack traces for PrimOp failures | [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#329](https://github.com/adinapoli/rusholme/issues/329) | Support concurrent/parallel IO in the RTS | [#326](https://github.com/adinapoli/rusholme/issues/326) | :white_circle: |
| [#341](https://github.com/adinapoli/rusholme/issues/341) | Add PrimOp type signatures to typechecker | [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#342](https://github.com/adinapoli/rusholme/issues/342) | Shrink known.zig to PrimOp names only | [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#343](https://github.com/adinapoli/rusholme/issues/343) | Implement heap operation PrimOps (MutVar) | [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#344](https://github.com/adinapoli/rusholme/issues/344) | Implement FFI bridge (ccall PrimOp) | [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |

### Epic [#8](https://github.com/adinapoli/rusholme/issues/8): Tree-Walking Interpreter

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#318](https://github.com/adinapoli/rusholme/issues/318) | Implement GRIN evaluator state: heap, environment, and function table | [#40](https://github.com/adinapoli/rusholme/issues/40) | :green_circle: |
| [#319](https://github.com/adinapoli/rusholme/issues/319) | Implement GRIN evaluator for simple expressions (Return, Store, Fetch, Update, Bind) | [#318](https://github.com/adinapoli/rusholme/issues/318) | :green_circle: |
| [#320](https://github.com/adinapoli/rusholme/issues/320) | Implement GRIN evaluator for App and Case expressions | [#319](https://github.com/adinapoli/rusholme/issues/319) | :green_circle: |
| [#51](https://github.com/adinapoli/rusholme/issues/51) | Implement basic IO primitives for the interpreter (putStrLn, getLine) | [#320](https://github.com/adinapoli/rusholme/issues/320), [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#52](https://github.com/adinapoli/rusholme/issues/52) | Implement arithmetic and comparison primitives for the interpreter | [#320](https://github.com/adinapoli/rusholme/issues/320), [#330](https://github.com/adinapoli/rusholme/issues/330) | :white_circle: |
| [#321](https://github.com/adinapoli/rusholme/issues/321) | End-to-end integration test: main = putStrLn "Hello" through GRIN evaluator | [#320](https://github.com/adinapoli/rusholme/issues/320), [#315](https://github.com/adinapoli/rusholme/issues/315), [#314](https://github.com/adinapoli/rusholme/issues/314), [#51](https://github.com/adinapoli/rusholme/issues/51) | :green_circle: |

### Epic [#9](https://github.com/adinapoli/rusholme/issues/9): LLVM Backend and Zig Runtime

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#53](https://github.com/adinapoli/rusholme/issues/53) | Set up LLVM C API bindings in Zig | — | :green_circle: |
| [#54](https://github.com/adinapoli/rusholme/issues/54) | Implement LLVM codegen skeleton (module, function defs, entry point) | [#53](https://github.com/adinapoli/rusholme/issues/53), [#40](https://github.com/adinapoli/rusholme/issues/40) | :green_circle: |
| [#55](https://github.com/adinapoli/rusholme/issues/55) | Implement LLVM codegen for GRIN expressions (store/fetch/update/case/app) | [#54](https://github.com/adinapoli/rusholme/issues/54) | :green_circle: |
| [#56](https://github.com/adinapoli/rusholme/issues/56) | Implement Zig runtime (heap allocator, thunk evaluator, entry point) | [#53](https://github.com/adinapoli/rusholme/issues/53) | :green_circle: |
| [#57](https://github.com/adinapoli/rusholme/issues/57) | Implement end-to-end: LLVM compile + link with Zig runtime + produce executable | [#55](https://github.com/adinapoli/rusholme/issues/55), [#56](https://github.com/adinapoli/rusholme/issues/56) | :green_circle: |
| [#384](https://github.com/adinapoli/rusholme/issues/384) | Implement actual thunk evaluation in runtime | [#56](https://github.com/adinapoli/rusholme/issues/56) | :white_circle: |
| [#385](https://github.com/adinapoli/rusholme/issues/385) | Implement proper heap node field storage for GRIN values | [#56](https://github.com/adinapoli/rusholme/issues/56) | :white_circle: |
| [#386](https://github.com/adinapoli/rusholme/issues/386) | Implement runtime closure support | [#56](https://github.com/adinapoli/rusholme/issues/56) | :white_circle: |
| [#390](https://github.com/adinapoli/rusholme/issues/390) | LLVM codegen: translate remaining GRIN expression types (Bind, Case, Store, Fetch, Update, Return) | [#55](https://github.com/adinapoli/rusholme/issues/55) | :yellow_circle: |
| [#391](https://github.com/adinapoli/rusholme/issues/391) | LLVM codegen: expand PrimOpMapping and support multi-arg calls | [#55](https://github.com/adinapoli/rusholme/issues/55) | :yellow_circle: |
| [#392](https://github.com/adinapoli/rusholme/issues/392) | LLVM codegen: translate function parameters in GRIN defs | [#55](https://github.com/adinapoli/rusholme/issues/55) | :yellow_circle: |
| [#410](https://github.com/adinapoli/rusholme/issues/410) | backend: nullary constructors not handled in GRIN→LLVM codegen (Val.Var lookup fails) | [#55](https://github.com/adinapoli/rusholme/issues/55) | :white_circle: |

---

## M2: Basic Programs

> **Goal:** ADTs, pattern matching, type classes, modules, minimal Prelude.

### Epic [#365](https://github.com/adinapoli/rusholme/issues/365): Module System & Multi-Module Compilation

| # | Issue | Deps | Status |
|---|-------|------|--------|
| [#366](https://github.com/adinapoli/rusholme/issues/366) | Define module interface representation (ModIface) with `.rhi` serialisation | [#38](https://github.com/adinapoli/rusholme/issues/38) | :white_circle: |
| [#367](https://github.com/adinapoli/rusholme/issues/367) | Implement module graph and topological compilation order | [#29](https://github.com/adinapoli/rusholme/issues/29) | :white_circle: |
| [#368](https://github.com/adinapoli/rusholme/issues/368) | Implement compilation session (CompileEnv) | [#366](https://github.com/adinapoli/rusholme/issues/366), [#367](https://github.com/adinapoli/rusholme/issues/367) | :white_circle: |
| [#369](https://github.com/adinapoli/rusholme/issues/369) | Implement implicit Prelude import | [#368](https://github.com/adinapoli/rusholme/issues/368) | :white_circle: |
| [#371](https://github.com/adinapoli/rusholme/issues/371) | Implement recompilation avoidance via `.rhi` fingerprinting | [#366](https://github.com/adinapoli/rusholme/issues/366), [#368](https://github.com/adinapoli/rusholme/issues/368) | :white_circle: |
| [#370](https://github.com/adinapoli/rusholme/issues/370) | Bootstrap Prelude from Haskell source | [#368](https://github.com/adinapoli/rusholme/issues/368), [#58](https://github.com/adinapoli/rusholme/issues/58), [#59](https://github.com/adinapoli/rusholme/issues/59) | :white_circle: |

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
      └─► #40 GRIN IR types ──► #41 pretty-printer ─┐
                               │                     │
                               ├─► #42 Core→GRIN research ──► #313 lambda lifting ──► #314 Core→GRIN simple
                               │                                                       ├─► #315 eval/apply gen ──► #317 partial app
                               │                                                       │
                               ├─► #330 PrimOps definition (Decision #0001)
                               │         │
                               │         └─► Provides primitive operations for RTS
                               │
                               ├─► #318 evaluator state ──► #319 simple eval ──► #320 App/Case eval
                               │                                                  ├─► #51 IO prims (via #330)
                               │                                                  └─► #52 arith prims (via #330)
                               │
                               │   #314 + #315 + #320 + #51 ──► #321 end-to-end integration  ✓ interpreter path
                               │
                               └─► #54 LLVM codegen ──► #55 GRIN exprs ─┐
                                                                         ├─► #57 link & run  ✓ compiler path
                                                        #53✓ LLVM bindings ──► #56 Zig runtime ─┘

#17✓ SourceSpan ──► #18 diagnostics ──► #36 (also needs diagnostics)

#22✓ parser research ──► #23 tokens ─┐
#24✓ unicode ────────────────────────┼─► #25 lexer ──► #26 layout ──► #29 parser ──► #30/#31/#32/#33
#17✓ SourceSpan ─────────────────────┘
```

**Legend:** :white_circle: Not started | :large_blue_circle: In progress | :green_circle: Done
