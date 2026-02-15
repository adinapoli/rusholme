# Decision 001: Parser Technique for Rusholme

**Status:** Draft
**Date:** 2026-02-15
**Issue:** #22

## Context

Rusholme needs to parse a subset of Haskell 2010, with the goal of growing to match GHC's implementation over time. The parser must handle the full layout rule (indentation-based syntax) and produce good error messages.

## Options Evaluated

### 1. Tree-sitter-haskell

**Pros:**
- Community-maintained, actively developed
- C ABI available for Zig interop
- Good incremental parsing support (useful for future editor integration/LSP)
- Handles layout rule

**Cons:**
- Parse tree format is tree-sitter specific (would need translation to our AST)
- Error recovery is not as sophisticated as GHC's
- Limited control over error message formatting
- Harder to extend for Haskell-specific extensions

**Zig Integration:** Possible via C FFI, but requires linking libtree-sitter and the tree-sitter-haskell grammar.

### 2. Reuse GHC's Alex/Happy Grammar

**Pros:**
- Most complete Haskell parser available
- Excellent error recovery and messages (production-proven)
- Literally parses "everything GHC parses" (Mantra #1)

**Cons:**
- Alex (lexer) and Happy (parser) are Haskell tools; their output is Haskell
- Porting .x (Alex) and .y (Happy) grammar files to Zig is significant work
- These are code generators, not pure descriptions - the generated code is part of the solution
- Would need to implement equivalent of Alex's lexer framework and Happy's LALR parser in Zig

**Zig Integration:** Very poor - requires complete rewrite of the code generation logic.

### 3. Hand-written Recursive Descent

**Pros:**
- Full control over error messages and diagnostics
- Native Zig - no external dependencies or FFI overhead
- Easy to iterate and extend
- Can produce clean, idiomatic Zig code
- Good support for predictive parsing (LALR(1) subset needed for Haskell)
- Easier to integrate with source location tracking throughout

**Cons:**
- Most upfront work
- Need to implement everything from scratch
- Risk of implementing an incomplete grammar

**Zig Integration:** Perfect - native Zig code.

### 4. Parser Combinators in Zig

**Pros:**
- Declarative grammar definition
- Good for rapid prototyping
- Native Zig

**Cons:**
- Poor error messages by default
- Performance can be worse than hand-written
- Debugging can be difficult
- Layout rule handling is non-trivial

**Zig Integration:** Good, but not recommended for production compiler.

## Recommendation: Hand-written Recursive Descent

### Rationale

Given Mantra #1 ("Parse everything GHC parses"), the most pragmatic long-term approach is **hand-written recursive descent with explicit left-factoring and error handling**.

**Key reasons:**

1. **Error Quality:** Zig's error unions and custom diagnostic types allow for GHC-quality error messages. Tree-sitter's error recovery is good for editors but not as detailed as we need for a compiler.

2. **Mantra Compliance:** Starting from GHC's grammar and translating it to recursive descent ensures we parse what GHC parses. The structure of GHC's parser.y is well-documented and can serve as a reference implementation.

3. **Zig-Native:** No FFI overhead, no external dependencies, full control over memory management. This aligns with the goal of learning Zig through this project.

4. **Layout Rule:** The Haskell layout rule can be implemented cleanly as a separate module that feeds lookahead to the parser, similar to GHC's approach.

5. **Extensibility:** Adding new language features or extensions is straightforward with hand-written code.

### Implementation Plan

1. **Study GHC's parser structure**:
   - Read `compiler/GHC/Parser.y` for the grammar structure
   - Read `compiler/GHC/Parser/Lexer.x` for token definitions
   - Understand the interaction between lexer, layout rule, and parser

2. **Token types** (#23): Define a comprehensive `Token` enum in `src/frontend/lexer.zig`

3. **Lexer** (#25): Implement the core lexer using Zig's std.mem for efficient string scanning

4. **Layout rule** (#26): Implement as a separate module that:
   - Tracks indentation context stack
   - Inserts implicit braces/semicolons based on indentation changes
   - Provides lookahead with layout awareness

5. **Parser structure**:
   - Use recursive descent with explicit precedence parsing for expressions
   - Left-factor ambiguous constructs (Haskell's grammar is mostly LALR(1))
   - Implement predictive parsing with proper error recovery

### Concerns Addressed

**Concern:** "Too much work to hand-write."

**Response:** While there is more upfront work, the alternatives introduce more complexity:
- Tree-sitter requires maintaining mappings between its parse tree and our AST
- Porting Alex/Happy requires implementing the code generators themselves

Hand-written recursive descent is the most maintainable long-term solution because:
- The code is self-documenting (no separate grammar file to learn)
- Errors are easier to debug (just Zig code)
- No build-time dependencies (no external tools to run)

**Concern:** "Error recovery is hard."

**Response:** Common recursive descent error recovery techniques:
- Synchronized recovery (skip to known synchronization points)
- One-token lookahead with insert- or delete-based recovery
- Contextual error messages based on current parsing context

These are well-documented in compiler literature and can be implemented incrementally.

## References

- [GHC Parser](https://gitlab.haskell.org/ghc/ghc/-/blob/master/compiler/GHC/Parser.y)
- [GHC Lexer](https://gitlab.haskell.org/ghc/ghc/-/blob/master/compiler/GHC/Parser/Lexer.x)
- [Haskell 2010 Report](https://www.haskell.org/onlinereport/haskell2010/)
- [Crafting Interpreters](https://craftinginterpreters.com/) by Robert Nystrom (recursive descent reference)
- [Modern Compiler Implementation in C](https://www.sciencedirect.com/book/9781558603202/) by Andrew W. Appel

## Decision

**Choose:** Hand-written recursive descent parser

**Implementation:** Start with GHC's grammar as reference, translate to Zig idioms incrementally.

**Next Step:** Begin with #23 (Define lexer token types) and #24 (Unicode character classification), then #25 (Core lexer).
