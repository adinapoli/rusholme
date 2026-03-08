# REPL Improvements Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add multiline editing, `:load` command, fix stale repl.wasm, and comprehensive e2e tests to the Rusholme REPL.

**Architecture:** The REPL has a CLI layer (`cli.zig`) for native and a JS layer (`template.html`) for the browser, both backed by the same protocol/session engine. Changes are additive — new state tracking in CLI, new commands, new JS input handling, and two tiers of new tests.

**Tech Stack:** Zig (CLI, protocol, session), JavaScript/xterm.js (browser REPL), `std.process.Child` (CLI e2e tests)

---

## Task 1: Add `InputMode` enum and multiline accumulation to CLI

**Files:**
- Modify: `src/repl/cli.zig`

**Step 1: Add the `InputMode` enum and multiline state**

At the top of `cli.zig`, after the imports, add:

```zig
const InputMode = enum {
    normal,
    multiline,
};
```

**Step 2: Refactor `run()` to use `InputMode` and an `ArrayList` buffer**

Replace the main loop in `run()`. The key changes:
- Add `mode: InputMode = .normal` and `multiline_buf: std.ArrayList(u8)` before the loop.
- The prompt changes based on mode: `"rusholme> "` for `.normal`, `"rusholme| "` for `.multiline`.
- In `.normal` mode, when a line starts with `:`, check if the trimmed content after `:` is `{`. If so, switch to `.multiline` and `continue`.
- Otherwise, dispatch to `handleCommand` as before.
- In `.multiline` mode:
  - If the trimmed line is `:}`, take the accumulated buffer contents, call `evaluate()`, reset `multiline_buf` and mode back to `.normal`.
  - If the line is `:quit` or `:q`, cancel the block: clear `multiline_buf`, switch to `.normal`, and break.
  - Otherwise, append the line (plus `\n`) to `multiline_buf`.
- On Ctrl+D (EOF) during `.multiline`, cancel the block and exit.

**Step 3: Update `handleCommand` to recognise `:{` and `:}` contextually**

The `:{` detection happens in the main loop *before* calling `handleCommand`, so `handleCommand` doesn't need to know about it. But remove the case where `:{` would fall through to "Unknown command" — this is handled by checking `cmd` starts with `{` in the main loop before dispatching to `handleCommand`.

**Step 4: Update the help text**

Add multiline to `printHelp`:
```
  :{              Begin multi-line input block
  :}              End multi-line input block and evaluate
```

**Step 5: Run existing tests**

```bash
zig build test --summary all
```

Expected: all existing tests pass (no regression).

**Step 6: Commit**

```bash
git add src/repl/cli.zig
git commit -m "#485: Add multiline :{ ... :} support to CLI REPL"
```

---

## Task 2: Add multiline support to browser JS

**Files:**
- Modify: `website/template.html`

**Step 1: Add multiline state variables**

In the IIFE that sets up the terminal, after `let currentLine = '';`, add:

```javascript
let inputMode = 'normal'; // 'normal' | 'multiline'
let multilineBuffer = [];
```

**Step 2: Update the Enter key handler**

Replace the Enter key block (`code === 13`) with logic that:
- In `normal` mode: if `currentLine.trim() === ':{'`, switch `inputMode` to `'multiline'`, clear `currentLine`, write the `| ` prompt.
- In `normal` mode (otherwise): evaluate as before.
- In `multiline` mode: if `currentLine.trim() === ':}'`, join `multilineBuffer` with `\n`, wrap in `:{...\n...\n:}`, call `replBridge.evaluate()` with the wrapped string, reset `multilineBuffer`, switch to `'normal'`, write `> ` prompt.
- In `multiline` mode (otherwise): push `currentLine` to `multilineBuffer`, write `| ` prompt.

**Step 3: Update Ctrl+D handler**

Add a handler for character code 4 (Ctrl+D). If in `multiline` mode, cancel the block: clear `multilineBuffer`, switch to `'normal'`, print `^D` and write the `> ` prompt.

**Step 4: Manual verification**

Build and serve:
```bash
cd website && bash dev.sh
```

Open browser, test `:{`, type a declaration, `:}`, then use the declaration.

**Step 5: Commit**

```bash
git add website/template.html
git commit -m "#485: Add multiline :{ ... :} support to browser REPL"
```

---

## Task 3: Add `website/dev.sh` convenience script

**Files:**
- Create: `website/dev.sh`

**Step 1: Create the script**

```bash
#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
echo "Building Rusholme (zig build)..."
zig build
echo "Building website..."
cd website
node build.js
echo "Serving website on http://localhost:3000"
npx serve .
```

**Step 2: Make it executable**

```bash
chmod +x website/dev.sh
```

**Step 3: Verify it works**

```bash
cd website && bash dev.sh
```

Expected: Zig builds, `repl.wasm` is copied, website is served.

**Step 4: Commit**

```bash
git add website/dev.sh
git commit -m "#485: Add website/dev.sh to rebuild repl.wasm and serve"
```

---

## Task 4: Add `:load` command to CLI

**Files:**
- Modify: `src/repl/cli.zig`

**Step 1: Extend `handleCommand` to recognise `:load` and `:l`**

`handleCommand` currently returns `bool`. It needs access to the session and allocator for `:load`. Refactor its signature:

```zig
fn handleCommand(
    io: Io,
    line: []const u8,
    allocator: Allocator,
    session: *Session,
) bool
```

Update the call site in `run()` accordingly.

**Step 2: Implement the `:load` handler**

Inside `handleCommand`, add a branch:

```zig
if (std.mem.startsWith(u8, cmd, "load ") or std.mem.startsWith(u8, cmd, "l ")) {
    const path = std.mem.trim(u8, cmd[if (cmd[0] == 'l' and cmd[1] == ' ') 2 else 5..], " \t");
    loadFile(io, path, allocator, session);
    return true;
}
```

Implement `loadFile`:
- Open with `std.fs.cwd().openFile(path, .{})`.
- Read with `file.readToEndAlloc(allocator, 1024 * 1024)` (1MB limit).
- Call `evaluate(allocator, session, contents)`.
- On `.success` or `.silent`: print `"Loaded: <path>\n"`.
- On `.failed`: render diagnostics (same pattern as the main loop).
- On file open error: print `"Cannot open file: <path>\n"`.

**Step 3: Update help text**

Add to `printHelp`:
```
  :load <file>, :l  Load a Haskell file into the session
```

**Step 4: Run existing tests**

```bash
zig build test --summary all
```

Expected: all pass.

**Step 5: Commit**

```bash
git add src/repl/cli.zig
git commit -m "#485: Add :load/:l command to CLI REPL"
```

---

## Task 5: Add `:load` to browser REPL via file picker

**Files:**
- Modify: `website/template.html`

**Step 1: Add a hidden file input element**

Before the IIFE, or inside it, create:

```javascript
const fileInput = document.createElement('input');
fileInput.type = 'file';
fileInput.accept = '.hs';
fileInput.style.display = 'none';
document.body.appendChild(fileInput);
```

**Step 2: Handle `:load` command in the Enter key handler**

In normal mode, before calling `replBridge.evaluate()`, check if `currentLine.trim()` starts with `:load` or `:l `:

```javascript
if (currentLine.trim() === ':load' || currentLine.trim() === ':l') {
    fileInput.click();
    currentLine = '';
    return;
}
```

**Step 3: Wire up the file input change handler**

```javascript
fileInput.addEventListener('change', (event) => {
    const file = event.target.files[0];
    if (!file) return;
    const reader = new FileReader();
    reader.onload = () => {
        const contents = reader.result;
        replBridge.evaluate(contents);
        // The evaluate() call already writes the prompt
    };
    reader.readAsText(file);
    fileInput.value = ''; // allow re-selecting same file
});
```

**Step 4: Update the help/welcome text**

Add `:load` to the welcome message or the section describing commands.

**Step 5: Manual verification**

Build and serve, try `:load` in the browser terminal, pick a `.hs` file.

**Step 6: Commit**

```bash
git add website/template.html
git commit -m "#485: Add :load file picker to browser REPL"
```

---

## Task 6: Add protocol-level e2e tests

**Files:**
- Modify: `tests/repl/repl_tests.zig`

**Step 1: Write the new test cases**

Add the following tests to `tests/repl/repl_tests.zig`, following the existing pattern (arena allocator, `Session.init`, `evaluate`, assert on status/value):

1. **`"repl: multiline block via joined content"`** — Evaluate `"f x = x\ng y = f y"` as a single input (simulating what the CLI would send after joining a `:{ ... :}` block). Then evaluate `"g 42"`, expect `"42"`.

2. **`"repl: error recovery — bad then good"`** — Evaluate `"not_defined_xyz"`, expect `.failed`. Then evaluate `"42"`, expect `.success` with `"42"`.

3. **`"repl: redefinition of function"`** — Define `"f x = 1"`, use `"f 0"` expect `"1"`. Redefine `"f x = 2"`, use `"f 0"` expect `"2"`.

4. **`"repl: chained declarations"`** — Define `"double x = x + x"`, define `"quadruple x = double (double x)"`, evaluate `"quadruple 3"` expect `"12"`.

5. **`"repl: empty input returns nothing"`** — Evaluate `""`. Protocol should handle gracefully (either `.silent` or no crash).

6. **`"repl: whitespace-only input"`** — Evaluate `"   "`. Same as above.

**Step 2: Run to verify they fail or pass as expected**

```bash
zig build test --summary all
```

Some may pass immediately (e.g. error recovery, empty input). Some may fail (e.g. redefinition — depends on session semantics). Adjust expectations to match actual session behaviour.

**Step 3: Commit**

```bash
git add tests/repl/repl_tests.zig
git commit -m "#485: Add comprehensive protocol-level REPL tests"
```

---

## Task 7: Create CLI e2e test infrastructure and tests

**Files:**
- Create: `tests/repl/cli_e2e_tests.zig`
- Modify: `build.zig`

**Step 1: Add build step in `build.zig`**

After the existing `repl_tests` block (around line 382), add:

```zig
// CLI end-to-end REPL tests — spawn rhc repl as subprocess
const cli_e2e_module = b.createModule(.{
    .root_source_file = b.path("tests/repl/cli_e2e_tests.zig"),
    .target = target,
});
const cli_e2e_tests = b.addTest(.{
    .name = "cli-e2e-tests",
    .root_module = cli_e2e_module,
});
// CLI e2e tests need the rhc binary built first
cli_e2e_tests.step.dependOn(b.getInstallStep());
const run_cli_e2e_tests = std.Build.Step.Run.create(b, "run test cli-e2e-tests");
run_cli_e2e_tests.addArtifactArg(cli_e2e_tests);
run_cli_e2e_tests.expectExitCode(0);
```

And add it to the test step:
```zig
test_step.dependOn(&run_cli_e2e_tests.step);
```

**Step 2: Create `tests/repl/cli_e2e_tests.zig` with test helpers**

The file needs:

1. A `ReplProcess` struct that wraps `std.process.Child`:
   - `spawn()` — starts `zig-out/bin/rhc repl` with piped stdin/stdout.
   - `sendLine(line: []const u8)` — writes `line ++ "\n"` to stdin pipe.
   - `readUntilPrompt()` — reads stdout until it sees `"rusholme> "` or `"rusholme| "`, returns everything before the prompt. Uses a timeout (e.g. 5 seconds) to avoid hanging.
   - `close()` — closes stdin, waits for process to exit.

2. Helper: `expectOutputContains(output: []const u8, needle: []const u8)` — asserts substring match.

**Step 3: Write the CLI e2e tests**

Each test creates a `ReplProcess`, interacts with it, and asserts on output:

1. **`"cli e2e: evaluate expression"`**
   - Spawn, skip banner (readUntilPrompt), sendLine("42"), readUntilPrompt, expect output contains "42", close.

2. **`"cli e2e: :help command"`**
   - Spawn, skip banner, sendLine(":help"), readUntilPrompt, expect output contains "Available commands".

3. **`"cli e2e: :quit exits cleanly"`**
   - Spawn, skip banner, sendLine(":quit"), wait for exit, expect exit code 0.

4. **`"cli e2e: multiline block"`**
   - Spawn, skip banner, sendLine(":{"), readUntilPrompt (expect `rusholme| `), sendLine("f x = x"), readUntilPrompt, sendLine(":}"), readUntilPrompt (back to `rusholme> `), sendLine("f 99"), readUntilPrompt, expect output contains "99".

5. **`"cli e2e: :load file"`**
   - Create a temp `.hs` file with `double x = x + x`, spawn, skip banner, sendLine(":load /tmp/rusholme_test_load.hs"), readUntilPrompt (expect "Loaded:"), sendLine("double 5"), readUntilPrompt, expect "10", close, delete temp file.

6. **`"cli e2e: error then recovery"`**
   - Spawn, skip banner, sendLine("undefined_xyz"), readUntilPrompt (expect "Error"), sendLine("42"), readUntilPrompt, expect "42".

7. **`"cli e2e: EOF exits cleanly"`**
   - Spawn, skip banner, close stdin, wait for exit, expect exit code 0.

**Step 4: Run the CLI e2e tests**

```bash
zig build test --summary all
```

Expected: all pass (assuming Tasks 1 and 4 are complete).

**Step 5: Commit**

```bash
git add tests/repl/cli_e2e_tests.zig build.zig
git commit -m "#485: Add CLI end-to-end REPL tests"
```

---

## Task 8: Final verification and cleanup

**Files:**
- All modified files

**Step 1: Run the full test suite**

```bash
zig build test --summary all
```

Expected: all tests pass, zero failures.

**Step 2: Build and test the website**

```bash
cd website && bash dev.sh
```

Verify in browser:
- REPL loads and evaluates expressions.
- Multiline `:{` / `:}` works.
- `:load` opens file picker and loads a file.

**Step 3: Check for memory leaks**

The protocol-level tests use `testing.allocator` which detects leaks. If all pass, no leaks.

**Step 4: Final commit (if any cleanup needed)**

```bash
git add -A
git commit -m "#485: Final cleanup for REPL improvements"
```
