# Layout Delimiter Stack Fix Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix issue #543 - prevent layout processor from injecting virtual tokens inside parenthesized/bracketed contexts

**Architecture:** Use a delimiter stack to track open/close delimiters. When stack is non-empty, skip virtual token injection per Haskell 2010 §2.7. Stack design supports future extension to quasi-quotes, TH, etc.

**Tech Stack:** Zig, existing layout.zig

---

## Task 1: Add delimiter_stack field to LayoutProcessor

**Files:**
- Modify: `src/frontend/layout.zig:50-70` (LayoutProcessor struct definition)

- [ ] **Step 1: Add delimiter_stack field**

In the `LayoutProcessor` struct, add a new field after `inside_pragma`:

```zig
// Stack to track explicit delimiter depth (parentheses, brackets, etc.).
// Per Haskell 2010 §2.7, layout rules don't apply inside explicit delimiters.
// This is a stack (not just a counter) to allow future extension to quasi-quotes,
// Template Haskell, and other delimiter types.
delimiter_stack: std.ArrayListUnmanaged(Token),
```

- [ ] **Step 2: Initialize delimiter_stack in init()**

In the `init` function, add `.delimiter_stack = .empty,` to the returned struct.

- [ ] **Step 3: Add deinit cleanup for delimiter_stack**

In the `deinit` function, add cleanup:
```zig
self.delimiter_stack.deinit(self.allocator);
```

- [ ] **Step 4: Commit**

```bash
git add src/frontend/layout.zig
git commit -m "#543: Add delimiter_stack to LayoutProcessor"
```

---

## Task 2: Track delimiters on open/close tokens

**Files:**
- Modify: `src/frontend/layout.zig:110-130` (nextToken function)

- [ ] **Step 1: Add delimiter tracking before layout processing**

At the start of `nextToken()`, after handling the pending queue and before any layout logic, add:

```zig
// Track explicit delimiters to suppress layout inside them.
// Per Haskell 2010 §2.7, layout rules don't apply inside explicit delimiter pairs.
switch (tok.token) {
    .open_paren, .open_bracket => try self.delimiter_stack.append(self.allocator, tok.token),
    .close_paren, .close_bracket => {
        // Pop regardless of match - parser will handle mismatches
        if (self.delimiter_stack.items.len > 0) {
            _ = self.delimiter_stack.pop();
        }
    },
    else => {},
}
```

This should go after the EOF check and pragma handling, but before the module-level layout check.

- [ ] **Step 2: Commit**

```bash
git add src/frontend/layout.zig
git commit -m "#543: Track delimiters in layout processor"
```

---

## Task 3: Suppress virtual tokens when inside delimiters

**Files:**
- Modify: `src/frontend/layout.zig:200-230` (step 7 context handling)

- [ ] **Step 1: Add stack check in context handling**

In step 7 (existing layout context handling), wrap the column comparison logic with a delimiter check:

Find the `while (self.peekContext()) |ctx| {` loop and add this at the start:

```zig
// Skip layout processing when inside explicit delimiters.
// Per Haskell 2010 §2.7, layout rules don't apply inside parentheses/brackets.
// Stack-based design allows future extension to quasi-quotes, TH, etc.
if (self.delimiter_stack.items.len > 0) {
    // Just clear the just_opened flag if needed
    if (self.peekContext()) |ctx| {
        if (tok.span.start.column > ctx.column or ctx.kind == .explicit) {
            self.context_just_opened = false;
        }
    }
    // Return token normally - no virtual tokens injected
    return tok;
}
```

- [ ] **Step 2: Commit**

```bash
git add src/frontend/layout.zig
git commit -m "#543: Suppress virtual tokens inside explicit delimiters"
```

---

## Task 4: Add test cases

**Files:**
- Modify: `src/frontend/layout.zig` (add tests at end of file)

- [ ] **Step 1: Add test for export list with blank lines**

Add this test after the existing tests:

```zig
test "Layout: export list with blank lines" {
    // Regression test for #543 - blank lines inside parentheses should not
    // trigger virtual token injection
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator,
        \\module Foo
        \\  ( bar
        \\  , baz
        \\
        \\  , quux
        \\  ) where
    , 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace); // Module
    try expectToken(&layout, Token{ .varid = "Foo" });
    try expectToken(&layout, .kw_module);
    try expectToken(&layout, .open_paren); // (
    try expectToken(&layout, Token{ .varid = "bar" });
    try expectToken(&layout, .comma);
    try expectToken(&layout, Token{ .varid = "baz" });
    try expectToken(&layout, .comma);
    try expectToken(&layout, Token{ .varid = "quux" });
    try expectToken(&layout, .close_paren); // )
    try expectToken(&layout, .kw_where);
    try expectToken(&layout, .v_open_brace);
    try expectToken(&layout, .v_close_brace); // empty where
    try expectToken(&layout, .v_close_brace); // module
    try expectToken(&layout, .eof);
}
```

- [ ] **Step 2: Add test for parenthesized expression**

```zig
test "Layout: parenthesized expression with different indentation" {
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator,
        \\main = (foo
        \\  bar)
    , 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace);
    try expectToken(&layout, Token{ .varid = "main" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, .open_paren);
    try expectToken(&layout, Token{ .varid = "foo" });
    try expectToken(&layout, Token{ .varid = "bar" });
    try expectToken(&layout, .close_paren);
    try expectToken(&layout, .v_close_brace);
    try expectToken(&layout, .eof);
}
```

- [ ] **Step 3: Add test for nested parentheses**

```zig
test "Layout: nested parentheses with blank lines" {
    const allocator = std.testing.allocator;
    var lexer = Lexer.init(allocator,
        \\main = ((foo
        \\  bar)
        \\    baz)
    , 0);
    var layout = LayoutProcessor.init(allocator, &lexer);
    defer layout.deinit();

    try expectToken(&layout, .v_open_brace);
    try expectToken(&layout, Token{ .varid = "main" });
    try expectToken(&layout, .equals);
    try expectToken(&layout, .open_paren);
    try expectToken(&layout, .open_paren);
    try expectToken(&layout, Token{ .varid = "foo" });
    try expectToken(&layout, Token{ .varid = "bar" });
    try expectToken(&layout, .close_paren);
    try expectToken(&layout, Token{ .varid = "baz" });
    try expectToken(&layout, .close_paren);
    try expectToken(&layout, .v_close_brace);
    try expectToken(&layout, .eof);
}
```

- [ ] **Step 4: Run tests**

```bash
zig build test --summary all
```

Expected: All layout tests pass

- [ ] **Step 5: Commit**

```bash
git add src/frontend/layout.zig
git commit -m "#543: Add tests for layout inside explicit delimiters"
```

---

## Task 5: Run full test suite and verify

**Files:**
- Run: `zig build test --summary all`

- [ ] **Step 1: Run full test suite**

```bash
zig build test --summary all
```

Expected: All tests pass

- [ ] **Step 2: Verify with actual parsing**

Test parsing a file with export list blank lines:

```bash
echo 'module Foo
  ( bar
  , baz

  , quux
  ) where' > /tmp/test_export.hs
zig build run -- parse /tmp/test_export.hs
```

Expected: Parses successfully without errors

- [ ] **Step 3: Final commit**

```bash
git add -A
git commit -m "#543: Fix layout processor to not inject virtual tokens inside explicit delimiters"
```

---

## Summary

This fix adds a delimiter stack to the layout processor. When the stack is non-empty, virtual token injection is suppressed, per Haskell 2010 §2.7 which states that layout rules don't apply inside explicit delimiter pairs.

The stack-based design allows future extension to handle:
- Quasi-quotation `[name| ... |]`
- Template Haskell `[| ... |]`, `[e| ... |]`, `[d| ... |]`
- Other delimiter types without refactoring

Changes:
1. Added `delimiter_stack` field (ArrayListUnmanaged(Token))
2. Track open/close parens and brackets on the stack
3. Skip virtual token injection when stack is non-empty
4. Added regression tests for the specific bug case and nested delimiters