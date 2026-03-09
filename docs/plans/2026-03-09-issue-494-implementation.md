# Issue #494: Browser REPL UnboundVariable Fix — Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Fix the browser REPL so that definitions loaded via `:load` (or typed interactively) are reliably available in subsequent evaluations, and runtime errors display useful context instead of bare error names.

**Architecture:** The Zig REPL logic is correct — the fix targets three layers: (1) cache-busting for `repl.wasm` in the browser, (2) better error context in `protocol.zig`, (3) regression tests already written for the WASM code path. No changes to the GRIN evaluator, pipeline, or session accumulation.

**Tech Stack:** Zig 0.16, JavaScript (xterm.js), WASM

---

### Task 1: Add cache-busting to WASM fetch

**Files:**
- Modify: `website/template.html` (the `replBridge.init` function, around the `fetch('repl.wasm')` call)

**Step 1: Make the change**

In `website/template.html`, inside `replBridge.init`, change:

```javascript
const response = await fetch('repl.wasm');
```

to:

```javascript
const response = await fetch('repl.wasm?v=' + Date.now());
```

This appends a unique timestamp query parameter so the browser never serves a cached stale binary.

**Step 2: Verify the template is valid**

Run: `grep -n "fetch.*repl.wasm" website/template.html`
Expected: one match showing the new `?v=` pattern.

**Step 3: Commit**

```bash
git add website/template.html
git commit -m "#494: Add cache-busting to repl.wasm fetch"
```

---

### Task 2: Improve runtime error context in protocol layer

**Files:**
- Modify: `src/repl/protocol.zig` (the `evaluate` function error path)

**Step 1: Make the change**

In `src/repl/protocol.zig`, the error path currently formats a bare `@errorName(err)`. Change it to include the input that caused the error:

Current code:
```zig
const msg = std.fmt.allocPrint(allocator, "{s}", .{@errorName(err)}) catch "evaluation failed";
```

New code:
```zig
const msg = std.fmt.allocPrint(allocator, "Runtime error: {s} while evaluating: {s}", .{ @errorName(err), input }) catch "evaluation failed";
```

**Step 2: Run tests**

Run: `zig build test --summary all`
Expected: all tests pass. The test `"protocol: evaluate handles errors with diagnostics"` should still pass since it checks `Status.failed` not the exact message text.

**Step 3: Commit**

```bash
git add src/repl/protocol.zig
git commit -m "#494: Include input context in runtime error messages"
```

---

### Task 3: Verify regression tests pass

The two issue-specific regression tests were already written in the investigation phase. They live in `tests/repl/repl_tests.zig`:

- `test "repl: GrinEngine — load then evaluate main (WASM :load path, issue #494)"`
- `test "repl: load file body then evaluate main (issue #494)"`

**Step 1: Run tests**

Run: `zig build test --summary all`
Expected: all tests pass, including the two new issue #494 tests.

**Step 2: Commit the test file**

```bash
git add tests/repl/repl_tests.zig
git commit -m "#494: Add regression tests for :load then evaluate flow"
```

---

### Task 4: Improve :load feedback in browser REPL

**Files:**
- Modify: `website/template.html` (the `fileInput` change event handler)

**Step 1: Make the change**

In `website/template.html`, the `:load` handler currently calls `replBridge.evaluate(body)` silently without showing the user whether the loaded definitions were accepted. Wrap the evaluate call to show status:

Current code (inside `reader.onload`):
```javascript
reader.onload = () => {
    term.writeln('Loaded: ' + file.name);
    const body = stripModuleHeader(reader.result);
    replBridge.evaluate(body);
};
```

New code:
```javascript
reader.onload = () => {
    const body = stripModuleHeader(reader.result);
    term.writeln('Loading: ' + file.name + ' (' + body.split('\n').length + ' lines)');
    replBridge.evaluate(body);
};
```

This shows the line count so the user can verify the file was read correctly, and uses "Loading:" since the evaluate call follows immediately.

**Step 2: Verify**

Run: `grep -n "Loading:" website/template.html`
Expected: one match.

**Step 3: Commit**

```bash
git add website/template.html
git commit -m "#494: Show line count when loading files in browser REPL"
```

---

### Task 5: Final verification and PR

**Step 1: Run full test suite**

Run: `zig build test --summary all`
Expected: all tests pass.

**Step 2: Push and open PR**

```bash
git push origin llm-agent/issue-494
```

Then open PR with:
```bash
gh pr create \
  --title "#494: Fix browser REPL UnboundVariable after :load" \
  --body-file /tmp/pr-body.md \
  --base main \
  --head llm-agent/issue-494 \
  --reviewer adinapoli
```

**Step 3: Update ROADMAP.md**

Change issue #494 status from :white_circle: to :yellow_circle:.
