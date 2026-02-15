# Open Questions

> **Instructions**: answer inline after each question (e.g. `→ your answer`).
> When all questions are answered, we'll fold the decisions into `DESIGN.md`
> and delete this file.

---

## 1. Language Subset — What Haskell Do We Support?

**1.1** Which type system features? Hindley-Milner only, or parts of System F
(explicit `forall`, rank-2 types)? Type classes? Multi-param type classes?

→ For now, I would say let's start with basic ADT (Algebra Data types) and
typeclasses, provided we can make this extensible such that it can accept a
broader set of language constructs. It would be nice, but non essential, if
we could support also `forall` as a keyword, at least for types (not kinds).

**1.2** Which data types? `data`, `newtype`, `type` aliases? GADTs? Deriving?
Which classes can be derived?

→ Yes, probably all the data types, including GADTs, deriving included as that
is essential for not locking ourselves to only very little programs in terms
of successful compilation. Let's start with the `stock` classes in GHC-deriving
terms, so `Show, Eq, Read, Ord` would be a nice start.

**1.3** Pattern matching — do we support full Haskell patterns (nested, guards,
`where`, `case`)? View patterns? Pattern synonyms?

→ Absolutely, yes. To make this VERY clear: eventually we want to support ALL
the grammar that modern GHCs support, but but now I'm happy to cut a few corners
for speeding up the prototype.

**1.4** Modules — do we support Haskell's module system? Import/export lists?
Qualified imports? Or a simplified single-file model at first?

→ Absolutely, importing modules is key in order to build very small examples,
or really do something useful at all.

**1.5** Syntactic sugar — `do`-notation? List comprehensions? `where` clauses?
`if/then/else`? How much desugaring do we commit to?

→ We can live for now without list comprehensions, the rest is important.

**1.6** FFI — any foreign function interface at all, or purely self-contained?

→ For now no FFI support. Eventually, absolutely.

**1.7** Prelude — do we ship a minimal Prelude? What's in it? (`id`, `map`,
`foldr`, basic IO, `Show`/`Eq`?)

→ Good question. Unfortunately GHC doesn't have relocatable `base` at the moment
so we cannot simply "import" the `base` library into the ecosystem. Yes, perhaps
a small `Prelude` is actually necessary to do anything meaningful here. Hopefully
we can leverage something on the internet for that: I remember at least a few
teaching projects over the years popping up on Reddit that shipped with trimmed
down versions of Prelude, so maybe we can do a bit of research and it's just copy
and paste.

**1.8** String representation — `[Char]` (faithful but slow) or `Text`-like
(practical but diverges from Haskell 2010)?

→ Very good question. I would design the system, if possible, such that by
default we use the faithful representation with `[Char]` but maybe we have a flag
in the compiler to turn on the `Text`-like representation. But I haven't thought too
much about this yet. I understand and feel the tension between offering a 100% backward
compatible compiler and offering "fringe" features which are unique to the compiler.
I need to ponder better.

---

## 2. Frontend — Lexing & Parsing

**2.1** Parser technique — hand-written recursive descent? PEG? Parser
combinators in Zig? Use a grammar/parser generator (tree-sitter, ANTLR, etc.)?

→ Good question. I would rely on an industry-standard, and I'm genuinely unsure
what Zig offers out of the box. Haskell uses Alex as a lexer, and maybe we can cheat
here, maybe there is a way to use the grammar straight from the GHC repo? We will
have to explore.

**2.2** Layout rule — Haskell's indentation-sensitive parsing is notoriously
tricky. Do we implement the full layout rule from the Report, or a simplified
version?

→ Eventually the full layout rule from the report. If we can reuse as much as
possible the GHC grammar files, we should be in business.

**2.3** Error recovery — how good do parse errors need to be? GHC-quality
suggestions, or "line X: parse error" is fine for now?

→ Funnily enough, I worked on GHC to implement what's called the new "diagnostics"
for GHC. They relied for a long time on stringly typed errors which I helped turning
into a proper AST which could render in a plethora of ways. Having very good errors
is paramount for me. GHC has two main flaws: it doesn't report all the errors for all
the modules (for example when building via Cabal) but it stops as soon as it finds an
error, which is annoying if you have to fix more than one thing, and things like LSP
(Language Server Protocol) clients cannot benefit from all the diagnostics. The second
flaw in GHC error handling is that sometimes you get a parse error and it turns into
a confusing error about something else. That's probably not entirely GHC's fault but
more a result of the confusing/tricky layout rule. Again, it's important to build this
in a scalable way on the get go: it's acceptable to get crappy errors for now provided
we have the _infrastructure_ to improve the errors to be top-class.

**2.4** Source locations — do we track spans (for error messages) from the
start, or bolt them on later?

→ Let's start with the right foot from the get-go. Let's track source locations properly.

**2.5** Unicode — full Unicode support in identifiers/operators (per Haskell
2010), or ASCII-only for v1?

→ Full unicode support.

---

## 3. Core IR

**3.1** How close to GHC Core? GHC's Core is System F_C (with coercions). Do we
want coercions, or stick with simple System F?

→ Let's go with full GHC Core, because how could it would be if we could intercept
the Core output from GHC and "bolt it on" to the rest of the Rusholme pipeline, one day?

**3.2** Core-to-Core optimisations — which ones do we implement first? Inlining?
Beta reduction? Case-of-case? Let-floating? Or defer all optimisation to GRIN?

→ Let's defer all the optimisations to GRIN, that's the coolest part of the project
and we should leverage that. First, it would make the pipeline faster because we
don't have to do core2core, and then we would really see how much GRIN optimise and
what brings to the table.

**3.3** Naming / uniqueness — how do we generate unique names? De Bruijn
indices? Unique supply? This affects every IR.

→ I don't have a strong opinion. We will have to do a bit of research here, and I will
trust your judgement.

---

## 4. GRIN

**4.1** GRIN dialect — do we follow Boquist's original GRIN or the "Modern GRIN"
from Hruska et al.? There are differences in the node representation.

→ I would be leaning in following the "Modern GRIN" just because typically the result
of newer research tends to be more innovative. But I haven't read the papers, so I can't
judge.

**4.2** Core→GRIN translation — this is non-trivial. Do we have a plan for how
thunks, partial applications, and constructors map to GRIN nodes?

→ We don't have a plan and we will have to figure this out. We don't have to decide
now, but we need to have _clear interfaces_ in the code to express that.

**4.3** GRIN optimisation passes — which do we implement first? Evaluated case
elimination? Sparse case elimination? Dead variable/code elimination?

→ I would say dead code elimination, but again I haven't read the papers. I would
say let's implement what would bring the most benefit in terms of speed.

**4.4** Heap points-to analysis — GRIN's whole-program optimisations depend on
abstract interpretation. How deep do we go in v1?

→ I haven't thought about that unfortunately.

---

## 5. Backends

**5.1** Which backend first? C is simplest (just emit C code and call `cc`),
LLVM is most powerful, JS is most fun. Which one do we boot with?

→ If LLVM can generate C, it looks like it would serve us well to go with
LLVM first, because even if trickier, it would tap into a plethora of nice things later.

**5.2** Runtime system — even a trivial runtime needs: entry point, thunk
evaluation, heap allocation, basic I/O. Do we write this in Zig, in C, or in
the target language?

→ It would be nice to write everything in Zig. Excellent point indeed.

**5.3** Calling convention — how do compiled Haskell functions get called? CPS?
Eval/apply? Push/enter?

→ I will need to understand this better, I don't have an answer for you, we will
need to do a bit of research and figure this out together.

---

## 6. Testing Strategy

**6.1** Unit testing — Zig has built-in `test` blocks. Do we unit-test each
pipeline stage independently (lexer, parser, typechecker, Core, GRIN, codegen)?

→ Yes, i think so. and then we have integration tests that checks that we can
compile a given program, run it, and it can emit the expected result.

**6.2** Golden/snapshot tests — compile Haskell snippets and compare output
against expected results? What format?

→ Yes, that's exactly what I was saying as part of 6.1.

**6.3** End-to-end tests — compile + run a Haskell program and check stdout?
When is the earliest we can do this?

→ Yes, I think this falls into 6.1 and 6.2. GHC has a lot of these tests,
perhaps we can take inspirations, they must have very simple programs in the
testuite we can import.

**6.4** Test suite source — do we write our own test programs, or borrow from an
existing suite (e.g. GHC testsuite, nofib)?

→ I gave you the answer in 6.3; whenever possible, I think borrowing reusable
parts from GHC would be a good idea.

**6.5** CI — GitHub Actions for Zig? Which Zig version do we pin?

→ Indeed, let's setup Github Actions as soon as possible, possibly using
the Nix flake we just built.

---

## 7. Bootstrapping & First Milestone

**7.1** What's "Milestone 1"? What's the smallest Haskell program we want to
compile and run? `main = putStrLn "Hello"`? Or something even simpler (just
evaluate `1 + 2` and print the result)?

→ The classic `main = putStrLn "Hello"` would indeed be a cool result for Milestone 1,
possibly, if we manage to go with the LLVM approach, a way to build an ELF binary and
a webassembly output to run in the browser.

**7.2** Interpreted mode first? Should we build a tree-walking interpreter for
Core/GRIN before tackling codegen, to validate the frontend?

→ Absolutely.

**7.3** REPL — desirable for interactive development, but adds complexity
(incremental compilation, IO handling). Include in scope or defer?

→ It should go in tandem with the development. I think that GHCI is nice, it
has some great features (like auto completion, for example) and it's an
integral part of the GHC/Haskell workflow. It also has its own quirks, like
the fact that the bytecode it emits is somewhat different from what we emit
for normal GHC code. If Rusholme had a way to interpret the code in a more
uniform way, it would be great, but I haven't thought too much about this.

**7.4** (Bonus point added by me) What about the flags that GHC supports?

→ For now let's not worry about them. We will have to think a bit about
this. Probably we don't want to support all the flags, that's unavoidable.
Certaint flags _heavily_ depends on GHC and its runtime system (for example
the ones on the worker-wrapper transformation) so it wouldn't make sense to
have them implemented in Rusholme. The same could apply for language extensions
and pragma. the mantra is that **Rusholme should eventually compile every Haskell
program in existence that GHC can also compile, but the runtime behaviour might
be different depending on what we decide to implement, and how.** Please keep
this mantra pinned in your memory while we work.

---

## 8. Project Structure

**8.1** Zig project layout — one big `src/` or split into packages/modules per
pipeline stage?

→ I am no Zig expert, you are, so probably splitting this into packages is a good
idea, provided Zig has a decent support for that. Modularity like Parnas & el and
information hiding are core principles of programming.

**8.2** Error handling — Zig error unions? A custom diagnostic type? How do we
propagate and report errors across stages?

→ I haven't thought about this, perhaps you can advice?

**8.3** Logging / debug output — how do we dump intermediate representations
for debugging? Zig's `std.log`? Pretty-printers per IR?

→ Yes, I would say `std.log` but also files and pretty-printing per IR would be nice.
Again, Zig has an incredibly strong support for binding to C libraries, so we can
cheat whenever we can and just reuse strong, industrial-ready C libraries that offers
capabilities we need. Definitely also pin this in your memory.

**8.4** Mega recap, which are the project's mantras?

→ 1. We should eventually parse and accept everything that GHC parses and accept,
even if we end up implementing things differently; 2. We should leverage strong,
battle tested C libraries to accomplish hard tasks every time we see the chance,
given that Zig has such a delightful support for C libraries and via nix sourcing
them in a stable development environment would be a breeze.
