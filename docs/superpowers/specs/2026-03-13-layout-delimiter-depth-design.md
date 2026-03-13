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

### Why a Delimiter Stack (Not Simple Counter)

A delimiter stack is the production-grade choice because:
1. **Extends naturally** - Can handle quasi-quotation `[name| ... |]`, Template Haskell `[| ... |]` in future
2. **Detects mismatches** - Can track unmatched delimiters for better error reporting
3. **Aligns with existing pattern** - The codebase already uses a stack for `{`/`}` explicit contexts
4. **Avoids bolt-on fixes** - Each new delimiter type just pushes/pops, no refactoring needed

### Data Structure

Add a delimiter stack to `LayoutProcessor`:

```zig
// Stack to track explicit delimiter depth (parentheses, brackets, etc.).
// Per Haskell 2010 §2.7, layout rules don't apply inside explicit delimiters.
// This is a stack (not just a counter) to allow future extension to quasi-quotes,
// Template Haskell, and other delimiter types.
delimiter_stack: std.ArrayListUnmanaged(Token),
```

Initialize as empty in `init()`.

### Token Handling

1. **Track delimiters** - At the start of `nextToken()`, before any layout processing:
   - If token is `open_paren` or `open_bracket`: push the token onto the stack
   - If token is `close_paren` or `close_bracket`: pop from the stack (if matches)

2. **Suppress virtual tokens** - In step 7 (context handling for cases 5 & 6), add condition:
   ```zig
   if (self.delimiter_stack.items.len > 0) {
       // Layout rules don't apply inside explicit delimiters
       // Return token normally - no virtual tokens injected
       return tok;
   }
   ```
   This ensures virtual tokens are not injected when inside any explicit delimiter pair.

### Future Extension Points

The delimiter stack design supports future additions:
- **Quasi-quotation**: `[name| expr |]` - push on `|`, pop on `|`
- **Template Haskell**: `[| expr |]`, `[e| expr |]`, `[d| decl |]`
- **View patterns**: (not yet implemented in Haskell 2010)

Each new delimiter type just needs push/pop logic - no refactoring of the core fix.

### Edge Cases

- Handle nested parentheses correctly (e.g., `(foo (bar))`)
- Track both parentheses `()` and brackets `[]` — brackets can appear in export lists and list literals
- Mismatched close delimiter: pop anyway (parser will report the error)

## Implementation Steps

1. Add `delimiter_stack` field to LayoutProcessor struct (ArrayListUnmanaged(Token))
2. Initialize as empty in `init()`
3. Add delimiter tracking in `nextToken()` before layout processing
4. Add stack length check in step 7 (context handling)
5. Add test cases:
   - Export list with blank lines
   - Parenthesized expressions with blank lines
   - Nested parentheses with blank lines

## Testing

- Existing layout tests must continue to pass
- New test: export list with blank lines (the bug reproduction)
- New test: parenthesized expression with different indentation inside
- New test: nested parentheses

## References

- Haskell 2010 Report, Section 2.7 (Layout)
- src/frontend/layout.zig