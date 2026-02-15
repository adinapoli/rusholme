# Open Questions

> **Instructions**: answer inline after each question (e.g. `→ your answer`).
> When all questions are answered, we'll fold the decisions into `DESIGN.md`
> and delete this file.

---

## 1. Language Subset — What Haskell Do We Support?

**1.1** Which type system features? Hindley-Milner only, or parts of System F
(explicit `forall`, rank-2 types)? Type classes? Multi-param type classes?

→

**1.2** Which data types? `data`, `newtype`, `type` aliases? GADTs? Deriving?
Which classes can be derived?

→

**1.3** Pattern matching — do we support full Haskell patterns (nested, guards,
`where`, `case`)? View patterns? Pattern synonyms?

→

**1.4** Modules — do we support Haskell's module system? Import/export lists?
Qualified imports? Or a simplified single-file model at first?

→

**1.5** Syntactic sugar — `do`-notation? List comprehensions? `where` clauses?
`if/then/else`? How much desugaring do we commit to?

→

**1.6** FFI — any foreign function interface at all, or purely self-contained?

→

**1.7** Prelude — do we ship a minimal Prelude? What's in it? (`id`, `map`,
`foldr`, basic IO, `Show`/`Eq`?)

→

**1.8** String representation — `[Char]` (faithful but slow) or `Text`-like
(practical but diverges from Haskell 2010)?

→

---

## 2. Frontend — Lexing & Parsing

**2.1** Parser technique — hand-written recursive descent? PEG? Parser
combinators in Zig? Use a grammar/parser generator (tree-sitter, ANTLR, etc.)?

→

**2.2** Layout rule — Haskell's indentation-sensitive parsing is notoriously
tricky. Do we implement the full layout rule from the Report, or a simplified
version?

→

**2.3** Error recovery — how good do parse errors need to be? GHC-quality
suggestions, or "line X: parse error" is fine for now?

→

**2.4** Source locations — do we track spans (for error messages) from the
start, or bolt them on later?

→

**2.5** Unicode — full Unicode support in identifiers/operators (per Haskell
2010), or ASCII-only for v1?

→

---

## 3. Core IR

**3.1** How close to GHC Core? GHC's Core is System F_C (with coercions). Do we
want coercions, or stick with simple System F?

→

**3.2** Core-to-Core optimisations — which ones do we implement first? Inlining?
Beta reduction? Case-of-case? Let-floating? Or defer all optimisation to GRIN?

→

**3.3** Naming / uniqueness — how do we generate unique names? De Bruijn
indices? Unique supply? This affects every IR.

→

---

## 4. GRIN

**4.1** GRIN dialect — do we follow Boquist's original GRIN or the "Modern GRIN"
from Hruska et al.? There are differences in the node representation.

→

**4.2** Core→GRIN translation — this is non-trivial. Do we have a plan for how
thunks, partial applications, and constructors map to GRIN nodes?

→

**4.3** GRIN optimisation passes — which do we implement first? Evaluated case
elimination? Sparse case elimination? Dead variable/code elimination?

→

**4.4** Heap points-to analysis — GRIN's whole-program optimisations depend on
abstract interpretation. How deep do we go in v1?

→

---

## 5. Backends

**5.1** Which backend first? C is simplest (just emit C code and call `cc`),
LLVM is most powerful, JS is most fun. Which one do we boot with?

→

**5.2** Runtime system — even a trivial runtime needs: entry point, thunk
evaluation, heap allocation, basic I/O. Do we write this in Zig, in C, or in
the target language?

→

**5.3** Calling convention — how do compiled Haskell functions get called? CPS?
Eval/apply? Push/enter?

→

---

## 6. Testing Strategy

**6.1** Unit testing — Zig has built-in `test` blocks. Do we unit-test each
pipeline stage independently (lexer, parser, typechecker, Core, GRIN, codegen)?

→

**6.2** Golden/snapshot tests — compile Haskell snippets and compare output
against expected results? What format?

→

**6.3** End-to-end tests — compile + run a Haskell program and check stdout?
When is the earliest we can do this?

→

**6.4** Test suite source — do we write our own test programs, or borrow from an
existing suite (e.g. GHC testsuite, nofib)?

→

**6.5** CI — GitHub Actions for Zig? Which Zig version do we pin?

→

---

## 7. Bootstrapping & First Milestone

**7.1** What's "Milestone 1"? What's the smallest Haskell program we want to
compile and run? `main = putStrLn "Hello"`? Or something even simpler (just
evaluate `1 + 2` and print the result)?

→

**7.2** Interpreted mode first? Should we build a tree-walking interpreter for
Core/GRIN before tackling codegen, to validate the frontend?

→

**7.3** REPL — desirable for interactive development, but adds complexity
(incremental compilation, IO handling). Include in scope or defer?

→

---

## 8. Project Structure

**8.1** Zig project layout — one big `src/` or split into packages/modules per
pipeline stage?

→

**8.2** Error handling — Zig error unions? A custom diagnostic type? How do we
propagate and report errors across stages?

→

**8.3** Logging / debug output — how do we dump intermediate representations
for debugging? Zig's `std.log`? Pretty-printers per IR?

→
