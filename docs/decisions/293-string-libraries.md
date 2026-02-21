# Decision 293: String Library Evaluation

**Status:** Accepted
**Date:** 2026-02-21
**Issue:** #293

## Context

Rusholme currently uses `[]const u8` for string handling throughout the compiler.
As the codebase grows, we need to evaluate whether adopting a dedicated string
library would provide benefits for:

1. **Source code manipulation** — slicing, concatenation for diagnostics
2. **Identifier/interning table management** — efficient name storage
3. **Pretty-printing output formatting** — building complex formatted output

This document evaluates two candidate libraries against our requirements.

## Current State

### String Usage Patterns

The codebase uses strings in several key areas:

| Area | Pattern | Ownership |
|------|---------|-----------|
| AST identifiers | `[]const u8` fields | Borrowed from arena |
| Lexer tokens | `[]const u8` in union | Allocated via `dupe()` |
| Scope maps | `StringHashMap` keys | Borrowed from AST |
| Diagnostic messages | `allocPrint` formatted | Caller-owned |
| Pretty-printing | `ArrayList(u8)` buffer | Transferred to caller |

### Pain Points Identified

1. **No interning** — same identifier string allocated multiple times
2. **Ownership ambiguity** — `Name.base` is borrowed but lifetime tracking is manual
3. **Allocation-heavy diagnostics** — each error makes 1-3 `allocPrint` calls
4. **Scope map key lifetime** — `StringHashMap` requires key strings to outlive entries

### Unicode Handling

Current implementation in `src/frontend/unicode.zig`:
- ASCII-only for `isUniSmall`, `isUniLarge`, `isUniLetter`, `isUniSymbol`, `isUniDigit`
- Full Unicode whitespace support (`isUniWhite`)
- Explicit TODO: "consider using a C library like ICU or unicode-utils"

## Libraries Evaluated

### 1. zig-string (JakubSzark/zig-string)

**Repository:** https://github.com/JakubSzark/zig-string

A UTF-8 compatible string library providing mutable string operations.

#### Features

| Category | Functions |
|----------|-----------|
| Memory | `allocate`, `capacity`, `deinit`, `truncate`, `toOwned` |
| Mutation | `concat`, `insert`, `pop`, `remove`, `removeRange`, `repeat`, `reverse` |
| Query | `charAt`, `find`, `rfind`, `len`, `isEmpty`, `startsWith`, `endsWith` |
| Transform | `toLowercase`, `toUppercase`, `toCapitalized`, `trim`, `replace` |
| Splitting | `split`, `splitAll`, `splitToString`, `splitAllToStrings`, `lines` |
| Utility | `clone`, `cmp`, `iterator`, `substr`, `str`, `writer` |

#### Characteristics

- **Ownership:** Always owned — requires `deinit()` to free
- **Allocator:** Constructor takes allocator, stored internally
- **UTF-8:** Claimed support, but character operations are ASCII-only for case conversion
- **Zig version:** Not explicitly stated; appears to track recent Zig
- **Maintenance:** Active (recent commits, CI badge present)

### 2. zigstr (dude_the_builder/zigstr)

**Repository:** https://codeberg.org/dude_the_builder/zigstr (formerly GitHub)

A comprehensive UTF-8 string type with full Unicode support.

#### Features

| Category | Functions |
|----------|-----------|
| Memory | `fromConstBytes`, `fromOwnedBytes`, `copy`, `toOwnedSlice`, `reset` |
| Code Points | `codePointIter`, `codePointLen`, `codePointAt`, `codePoints`, `fromCodePoints` |
| Graphemes | `graphemeIter`, `graphemeLen`, `graphemeAt`, `graphemes` |
| Query | `indexOf`, `lastIndexOf`, `contains`, `count`, `byteAt`, `eql` |
| Transform | `toLower`, `toUpper`, `trim`, `trimLeft`, `trimRight`, `reverse`, `replace` |
| Tokenization | `tokenIter`, `tokenize`, `splitIter`, `split`, `lineIter`, `lines` |
| Mutation | `concat`, `concatAll`, `append`, `appendAll`, `insert`, `remove`, `repeat` |
| Parsing | `parseInt`, `parseFloat`, `parseBool`, `parseTruthy` |
| Utility | `isEmpty`, `isBlank`, `dropLeft`, `dropRight`, `chomp`, `substr` |

#### Characteristics

- **Ownership:** Flexible — `fromConstBytes` (borrowed) or `fromOwnedBytes` (owned)
- **Allocator:** Separated `Data` struct for shared string data
- **UTF-8:** Full Unicode support including grapheme clusters
- **Zig version:** Explicitly targets Zig 0.13 stable
- **Maintenance:** **Looking for new maintainer** (warning in README)

### Comparison Matrix

| Criterion | zig-string | zigstr | `[]const u8` + std |
|-----------|------------|--------|-------------------|
| UTF-8 correctness | Partial | Full | Manual (std.unicode) |
| Grapheme clusters | No | Yes | No |
| Flexible ownership | No (owned only) | Yes | Yes (by convention) |
| Arena-friendly | No | Yes (const bytes) | Yes |
| Unicode case conversion | ASCII only | Full | ASCII only |
| Active maintenance | Yes | **Needs maintainer** | N/A |
| Zig 0.13 support | Likely | Explicit | N/A |
| Zero-cost borrow | No | Yes | Yes |
| Learning curve | Low | Medium | None |

## Analysis

### Against zig-string

**Deal-breaker:** The library requires all strings to be owned. This conflicts
with Rusholme's architecture where most strings are borrowed from arenas:

```zig
// Current pattern (borrowed from arena)
const name = Name{ .base = identifier_string, .unique = supply.fresh() };
// identifier_string lives in arena, no per-name allocation

// With zig-string (would require allocation)
var name_str = try String.init(allocator);
try name_str.setStr(identifier_string);
defer name_str.deinit(); // Per-name allocation overhead!
```

For a compiler that processes thousands of identifiers, this overhead is unacceptable.

### Against zigstr

**Concern:** The project explicitly states it needs a new maintainer. Adopting a
library in maintenance limbo risks:
- No bug fixes for future Zig versions
- No security updates
- Potential abandonment

**Advantage:** The flexible ownership model (borrowed or owned) aligns with
Rusholme's patterns, and grapheme cluster support is genuine Unicode support.

### Current Approach Viability

The `[]const u8` + `std.mem` + `std.unicode` approach is:

| Aspect | Assessment |
|--------|------------|
| Memory efficiency | Excellent — borrows, no overhead |
| Arena compatibility | Perfect — borrowed slices work naturally |
| UTF-8 handling | Adequate with `std.unicode` helpers |
| Developer ergonomics | Good — idiomatic Zig |
| Allocation pressure | Low — only when explicit copies needed |

## Recommendation

**Continue with `[]const u8` + standard library utilities.** Do not adopt either
evaluated library at this time.

### Rationale

1. **Architecture mismatch for zig-string:** The owned-only model adds allocation
   overhead to every identifier, defeating the arena-based memory strategy.

2. **Maintenance risk for zigstr:** Adopting a library seeking a new maintainer
   creates long-term risk. When the author steps away, we inherit maintenance
   burden or face migration.

3. **Current approach is sufficient:** Rusholme's string needs are primarily:
   - Borrowed slices for identifiers (handled perfectly by `[]const u8`)
   - Occasional formatted output (handled by `std.fmt`)
   - Limited Unicode classification (handled adequately by `std.unicode`)

4. **Unicode gaps are narrow:** The main gap is full Unicode case conversion and
   grapheme cluster handling. For a Haskell compiler, these are rarely needed:
   - Haskell identifiers are ASCII by convention
   - String literals are passthrough (no semantic analysis)
   - Diagnostics are in English (ASCII)

5. **Future option:** If full Unicode becomes necessary (e.g., for internationalized
   error messages), consider:
   - Contributing to zigstr if it finds a maintainer
   - Using ziglyph (#283) for character classification only
   - C interop with ICU for comprehensive Unicode

### Actions

- [x] Evaluate zig-string API and ownership model
- [x] Evaluate zigstr API and ownership model  
- [x] Analyze Rusholme's string usage patterns
- [x] Document recommendation

### Follow-up

If string handling becomes a bottleneck, revisit after:
1. zigstr finds a new maintainer, OR
2. A new Zig-native string library emerges with flexible ownership

## References

- zig-string: https://github.com/JakubSzark/zig-string
- zigstr: https://codeberg.org/dude_the_builder/zigstr
- Current implementation: `src/frontend/unicode.zig`
- String usage: `src/naming/unique.zig`, `src/frontend/ast.zig`
