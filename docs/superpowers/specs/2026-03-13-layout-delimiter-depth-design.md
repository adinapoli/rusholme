# Layout Processor: Fix Virtual Token Injection in Parenthesized Contexts

## Context

Issue #543: The layout processor injects virtual semicolons (v_semi) and virtual close braces (v_close_brace) when it encounters blank lines or indentation changes, even inside parentheses (e.g., export lists).

Per Haskell 2010 Report Section 2.7, layout rules should NOT apply inside explicit delimiter pairs like parentheses or brackets.

## Minimal Reproduction

```haskell
module Foo
  ( bar
  , baz

  , quux
  ) where
```

The blank line between `baz` and `quux` triggers virtual token injection, breaking the parse.

## Design

### Data Structure

Add a simple depth counter to `LayoutProcessor`:

```zig
// Track parenthesis/bracket depth to suppress layout inside explicit delimiters.
// Per Haskell 2010 §2.7, layout rules don't apply inside parentheses/brackets.
paren_depth: usize,
```

Initialize to 0 in `init()`.

### Token Handling

1. **Track depth** - At the start of `nextToken()`, before any layout processing:
   - If token is `open_paren` or `open_bracket`: increment `paren_depth`
   - If token is `close_paren` or `close_bracket`: decrement `paren_depth` (ensure it doesn't go negative)

2. **Suppress virtual tokens** - In step 7 (context handling for cases 5 & 6), add condition:
   ```zig
   if (self.paren_depth > 0) {
       // Layout rules don't apply inside explicit delimiters
       continue;
   }
   ```
   This ensures virtual tokens are not injected when inside parentheses/brackets.

### Edge Cases

- Ensure `paren_depth` never goes negative (mismatched parens are a parse error, not our concern)
- Handle nested parentheses correctly (e.g., `(foo (bar))`)
- Track both parentheses `()` and brackets `[]` — brackets can appear in export lists and list literals

## Implementation Steps

1. Add `paren_depth: usize` field to LayoutProcessor struct
2. Initialize to 0 in `init()`
3. Add depth tracking in `nextToken()` before layout processing
4. Add depth check in step 7 (context handling)
5. Add test cases:
   - Export list with blank lines
   - Parenthesized expressions with blank lines
   - Function type signatures with newlines

## Testing

- Existing layout tests must continue to pass
- New test: export list with blank lines (the bug reproduction)
- New test: parenthesized expression with different indentation inside

## References

- Haskell 2010 Report, Section 2.7 (Layout)
- src/frontend/layout.zig