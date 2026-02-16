# Decision 004: Name Uniqueness Strategy (De Bruijn vs Unique Supply)

**Status:** Accepted
**Date:** 2026-02-16
**Issue:** #68

## Context

Rusholme will perform transformations from the original Haskell AST → Core → GRIN → LLVM.
During these transformations, variable names lose their original identifiers and need to be
tracked uniquely to avoid name capture bugs. The choice of representation affects both
correctness and debuggability across all IR levels.

## Options Evaluated

### 1. De Bruijn Indices

Variables are represented as natural numbers indicating their position in the binding stack.
`λx λy x` becomes `λ λ 2` (the second outer binder).

**Pros:**
- Variable capture is impossible by construction
- Alpha-equivalence is structural equality
- No string comparison needed
- No allocation overhead for names

**Cons:**
- Impossible to read/debug — "variable 2" tells you nothing about the original name
- Makes error messages, pretty-printing, and debugging painful
- Requires bookkeeping when moving terms (maintaining the De Bruijn counter)
- Not suitable for IRs that need human-readable output (Core, GRIN)

**Suitability:** Good for the implementation of Core→GRIN translation internals,
but terrible for the IR nodes themselves.

### 2. Unique Supply (GHC's Approach)

Every binder gets a globally unique integer. Names are represented as `(original_name,
unique)` pairs where `unique` is the "uniqueness identifier." For example: `map_42`,
`filter_89`.

**Pros:**
- Retains original names for debugging and pretty-printing
- Simple uniqueness check: just compare the unique integer
- Easy to generate fresh names (increment a counter)
- Works well across multiple IRs (AST, Core, GRIN)
- Well-proven in production (GHC uses it)

**Cons:**
- Requires maintaining a global unique supply (counter)
- Slightly larger representation than De Bruijn

**Suitability:** Excellent for all IRs in Rusholme. Proven production approach.

### 3. Locally Nameless

Bound variables use De Bruijn indices, free variables use names. For example:
`λ λ 2` for bound variables but `f` remains `f` when free.

**Pros:**
- Captures simplicity of De Bruijn for bound variables
- Preserves readability for free variables
- Good for formal verification

**Cons:**
- Complex to implement correctly
- Requires "opening" and "closing" operations when moving terms
- More complex than pure unique supply
- Not widely used in compilers (more a formal methods technique)

**Suitability:** Good for formal verification but overkill for a toy compiler.

### 4. Hybrid: Names for AST, De Bruijn for Core internals

Use readable names for the AST (to match source code), and De Bruijn indices for the
internal transformations in Core→GRIN.

**Pros:**
- Best of both worlds: readable AST, compact Core

**Cons:**
- Two different name representations to manage
- Translation between representations is complexity
- Debugging still hard for Core/GRIN if they use De Bruijn

**Suitability:** Moderate, but adds translation layer complexity.

## Recommendation: GHC-Style Unique Supply

### Rationale

For a teaching/learning compiler like Rusholme, readability and debuggability are
paramount. The goal is to learn how to implement a compiler, not to squeeze out the
last 5% of performance.

**Key reasons for unique supply (Option 2):**

1. **Debuggability:** When reading Core or GRIN output, `map_42` tells you what the
   variable is. De Bruijn would just say "variable 3" — opaque and frustrating.

2. **Proven in Production:** GHC has used unique supply for decades. It's battle-
   tested and well-understood.

3. **Cross-IR Consistency:** A single name representation `(String, Unique)` works
   across AST, Core, and GRIN with no translation between systems.

4. **Implementation Simplicity:** Just maintain a global integer counter. When you
   need a unique name, increment the counter and append it to the original name.

5. **Error Quality:** When reporting errors to users, you can say "undefined variable
   `map`" not "undefined variable 3."

### Performance Consideration

The performance overhead of unique supply is negligible for a toy compiler:

- Integer comparison (O(1)) in place of string comparison (O(n))
- Counter increment is a single `add` instruction
- Memory overhead is small (one extra `u64` per binder)

The correctness and debuggability benefits far outweigh this trivial overhead.

## Implementation

**Representation:**

```zig
const Name = struct {
    base: []const u8,    // Original identifier
    unique: u64,         // Uniqueness counter
};
```

**Unique Supply:**

```zig
const UniqueSupply = struct {
    next: u64 = 0,

    /// Allocate a fresh unique number
    pub fn fresh(self: *UniqueSupply) u64 {
        const u = self.next;
        self.next += 1;
        return u;
    }

    /// Create a fresh name from a base
    pub fn freshName(self: *UniqueSupply, allocator: std.mem.Allocator, base: []const u8) !Name {
        const u = self.fresh();
        // In production: concat base + "_" + itoa(u)
        // For toy: just track (base, u) pair
        return .{ .base = base, .unique = u };
    }
};
```

**Pretty-Printing:** When printing Core/GRIN, display `base_unique` for readability,
e.g. `map_42`, `foldl_87`.

## Decision

**Choose:** GHC-style unique supply

**Implementation:**
- Each binder gets a `(base_name, unique)` pair
- Global UniqueSupply maintains counter
- Pretty-print with `base_unique` format
- Use across AST, Core, and GRIN

**Next Step:**
- Implement UniqueSupply module (#69)
- Integrate into Core IR types (#34)

## References

- GHC's `Unique` module: https://gitlab.haskell.org/ghc/ghc/-/blob/master/compiler/GHC/Types/Unique.hs
- GHC's `OccName` and `Name` types for name representation
- 'The Locally Nameless Representation', Charguéraud 2012 (for comparison)
