# REPL Line Editor Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the hand-rolled byte-by-byte `readLine` in `src/repl/cli.zig` with a `LineEditor` struct backed by the replxx C library, providing tab-completion, inline hints, live syntax highlighting, and persistent history at `~/.rhc/repl_history`.

**Architecture:** A new `src/repl/line_editor.zig` module wraps the replxx C API (via `@cImport("replxx.h")`) behind a clean `LineEditor` struct. Three C callbacks delegate immediately to pure Zig helpers (`completionsFor`, `hintsFor`, `highlightLine`) that are independently testable. `cli.zig` owns a `LineEditor` and calls `readLine` — no knowledge of replxx leaks out.

**Tech Stack:** Zig 0.16-dev, replxx 0.0.4 (C API), nixpkgs, `@cImport`.

---

## File Map

| File | Action | Responsibility |
|---|---|---|
| `flake.nix` | Modify | Add `pkgs.replxx` to buildInputs; export `REPLXX_PREFIX` |
| `build.zig` | Modify | Add `configureReplxx` function; call it on `mod` |
| `src/renamer/renamer.zig` | Modify | Add `Scope.collectNames` for completion candidates |
| `src/repl/line_editor.zig` | Create | `LineEditor` struct, callbacks, pure helpers, unit tests |
| `src/repl/cli.zig` | Modify | Use `LineEditor`; remove `readLine`; add `historyFilePath` |

---

### Task 1: Nix + build integration

**Files:**
- Modify: `flake.nix`
- Modify: `build.zig`

- [ ] **Step 1.1: Add replxx to flake.nix**

  In `flake.nix`, find the `default` devShell `buildInputs` list and add `pkgs.replxx`. Also add `export REPLXX_PREFIX="${pkgs.replxx}"` to the `shellHook`:

  ```nix
  default = pkgs.mkShell {
    name = "rusholme";

    buildInputs = zigToolchain ++ (with pkgs; [
      git
      pre-commit
      wasmtime
      graalvmPackages.graalvm-ce
      replxx                          # <-- add this line
    ]) ++ pkgs.lib.optionals (!isDarwin) [
      pkgs.valgrind
    ];

    shellHook = ''
      echo "🍛 Rusholme dev environment loaded"
      echo "   Zig:      $(zig version)"
      echo "   LLVM:     $(llvm-config --version)"
      echo "   Wasmtime: $(wasmtime --version 2>&1 | head -n1 || echo 'not found')"
      echo "   lli:      $(lli --version 2>&1 | head -n1 || echo 'not found')"
      echo ""
      export REPLXX_PREFIX="${pkgs.replxx}"   # <-- add this line
    '';
  };
  ```

- [ ] **Step 1.2: Add `configureReplxx` to build.zig**

  Add this function immediately after `configureLlvm` (around line 44 in `build.zig`):

  ```zig
  /// Configure replxx headers and library on a module.
  ///
  /// replxx ships no pkg-config file. Discover the include and library
  /// paths from the REPLXX_PREFIX environment variable, which is set by
  /// the Nix devShell shellHook (see flake.nix).
  ///
  /// Without REPLXX_PREFIX the paths are omitted; the linker will still
  /// find libreplxx.so if it is on the default library search path.
  fn configureReplxx(b: *std.Build, mod: *std.Build.Module) void {
      if (std.process.getEnvVarOwned(b.allocator, "REPLXX_PREFIX") catch null) |prefix| {
          defer b.allocator.free(prefix);
          mod.addSystemIncludePath(.{ .cwd_relative = b.pathJoin(&.{ prefix, "include" }) });
          mod.addLibraryPath(.{ .cwd_relative = b.pathJoin(&.{ prefix, "lib" }) });
      }
      mod.linkSystemLibrary("replxx", .{});
      mod.linkLibCpp();
  }
  ```

- [ ] **Step 1.3: Call `configureReplxx` for the rusholme module**

  Immediately after the `configureLlvm(b, mod)` call (around line 90), add:

  ```zig
  configureLlvm(b, mod);
  configureReplxx(b, mod);  // <-- add this line
  ```

- [ ] **Step 1.4: Verify build compiles**

  ```bash
  zig build 2>&1 | head -20
  ```

  Expected: builds without errors. (No replxx usage yet — just confirming the
  linker flags are wired in.)

- [ ] **Step 1.5: Commit**

  ```bash
  git add flake.nix build.zig
  git commit -m "#76: Wire replxx into Nix devshell and build.zig"
  ```

---

### Task 2: Add `Scope.collectNames` to the renamer

**Files:**
- Modify: `src/renamer/renamer.zig` (around line 144, after `inCurrentScope`)

- [ ] **Step 2.1: Write the failing test**

  Add at the bottom of `src/renamer/renamer.zig`:

  ```zig
  test "Scope.collectNames returns all bound names across frames" {
      var scope = try Scope.init(std.testing.allocator);
      defer scope.deinit();

      try scope.bind("foo", .{ .base = "foo", .unique = 1 });
      try scope.bind("bar", .{ .base = "bar", .unique = 2 });

      try scope.push();
      try scope.bind("baz", .{ .base = "baz", .unique = 3 });

      var names: std.ArrayListUnmanaged([]const u8) = .empty;
      defer names.deinit(std.testing.allocator);
      try scope.collectNames(std.testing.allocator, &names);

      try std.testing.expect(names.items.len == 3);
  }
  ```

- [ ] **Step 2.2: Run the test to confirm it fails**

  ```bash
  zig build test -- --test-filter "Scope.collectNames"
  ```

  Expected: compilation error — `collectNames` does not exist yet.

- [ ] **Step 2.3: Implement `Scope.collectNames`**

  Add the following method to the `Scope` struct, after the `inCurrentScope`
  method (around line 148):

  ```zig
  /// Collect all source names bound in any scope frame into `results`.
  ///
  /// Walks from the innermost frame outward. Inner-frame names shadow
  /// outer ones at runtime, but for completion all names are included.
  /// The returned slices are owned by the scope's hash maps and are
  /// valid as long as the scope (and its frames) live.
  pub fn collectNames(
      self: *const Scope,
      alloc: std.mem.Allocator,
      results: *std.ArrayListUnmanaged([]const u8),
  ) !void {
      var frame: ?*Frame = self.current;
      while (frame) |f| {
          var it = f.bindings.keyIterator();
          while (it.next()) |key| {
              try results.append(alloc, key.*);
          }
          frame = f.parent;
      }
  }
  ```

  Note: `frame` is declared `var` because we reassign it in the loop; the
  loop body only reads `f` (const), so Zig is satisfied.

- [ ] **Step 2.4: Run the test to confirm it passes**

  ```bash
  zig build test -- --test-filter "Scope.collectNames"
  ```

  Expected: PASS.

- [ ] **Step 2.5: Commit**

  ```bash
  git add src/renamer/renamer.zig
  git commit -m "#76: Add Scope.collectNames for REPL tab completion"
  ```

---

### Task 3: Create `src/repl/line_editor.zig`

**Files:**
- Create: `src/repl/line_editor.zig`

This is the heart of the feature. We implement the module in sub-steps:
pure helpers first (testable), then the LineEditor struct.

- [ ] **Step 3.1: Write failing tests for pure helpers**

  Create `src/repl/line_editor.zig` with just the tests and the necessary
  imports/constants (no implementations yet):

  ```zig
  //! REPL Line Editor
  //!
  //! Wraps the replxx C library to provide feature-rich line editing
  //! for the native `rhc repl` command:
  //!   - Tab completion (REPL commands, in-scope names, filesystem paths)
  //!   - Inline hints (ghost text for the first matching candidate)
  //!   - Live syntax highlighting of the input line
  //!   - Persistent history saved to ~/.rhc/repl_history
  //!
  //! Native-only: imported exclusively by cli.zig, never compiled into
  //! the WASM build target.

  const std = @import("std");
  const Allocator = std.mem.Allocator;
  const Session = @import("session.zig").Session;

  const c = @cImport({
      @cInclude("replxx.h");
  });

  // ── Constants ─────────────────────────────────────────────────────────

  const max_history_entries: c_int = 1000;

  const repl_commands = [_][]const u8{
      ":quit", ":q",   ":type", ":t",
      ":load", ":l",   ":help", ":h",
      ":?",    ":{",   ":}",
  };

  const haskell_keywords = [_][]const u8{
      "let",      "in",       "where",    "data",
      "case",     "of",       "if",       "then",
      "else",     "do",       "type",     "newtype",
      "class",    "instance", "module",   "import",
      "deriving",
  };

  // Forward declarations (implementations follow below)
  fn currentToken(line: []const u8) []const u8;
  fn isFileCompletionContext(line: []const u8) bool;
  fn commandCompletions(alloc: Allocator, prefix: []const u8, out: *std.ArrayListUnmanaged(Completion)) !void;
  fn isKeyword(word: []const u8) bool;
  fn isOperatorChar(ch: u8) bool;

  const Completion = struct {
      text: [:0]u8,
      color: c.ReplxxColor,
  };

  // ── Tests ─────────────────────────────────────────────────────────────

  test "currentToken: bare identifier extracts last token" {
      try std.testing.expectEqualStrings("fo", currentToken("let fo"));
      try std.testing.expectEqualStrings("x", currentToken("x"));
      try std.testing.expectEqualStrings("", currentToken(""));
  }

  test "currentToken: colon command returns whole line" {
      try std.testing.expectEqualStrings(":t", currentToken(":t"));
      try std.testing.expectEqualStrings(":quit", currentToken(":quit"));
  }

  test "currentToken: command argument extracts path prefix" {
      try std.testing.expectEqualStrings("Foo", currentToken(":load Foo"));
      try std.testing.expectEqualStrings("src/", currentToken(":l src/"));
  }

  test "commandCompletions: prefix ':t' matches ':type' and ':t'" {
      var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
      defer arena.deinit();
      var out: std.ArrayListUnmanaged(Completion) = .empty;
      try commandCompletions(arena.allocator(), ":t", &out);
      try std.testing.expect(out.items.len == 2);
  }

  test "commandCompletions: full prefix ':quit' matches only ':quit'" {
      var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
      defer arena.deinit();
      var out: std.ArrayListUnmanaged(Completion) = .empty;
      try commandCompletions(arena.allocator(), ":quit", &out);
      try std.testing.expect(out.items.len == 1);
      try std.testing.expectEqualStrings(":quit", out.items[0].text);
  }

  test "highlightLine: keyword 'let' is blue" {
      const input = "let x = 42";
      var colors: [input.len]c.ReplxxColor = undefined;
      highlightLine(input, &colors);
      try std.testing.expectEqual(c.REPLXX_COLOR_BLUE, colors[0]);
      try std.testing.expectEqual(c.REPLXX_COLOR_BLUE, colors[1]);
      try std.testing.expectEqual(c.REPLXX_COLOR_BLUE, colors[2]);
  }

  test "highlightLine: number literal is yellow" {
      const input = "42";
      var colors: [input.len]c.ReplxxColor = undefined;
      highlightLine(input, &colors);
      try std.testing.expectEqual(c.REPLXX_COLOR_YELLOW, colors[0]);
      try std.testing.expectEqual(c.REPLXX_COLOR_YELLOW, colors[1]);
  }

  test "highlightLine: constructor is bright green" {
      const input = "Just";
      var colors: [input.len]c.ReplxxColor = undefined;
      highlightLine(input, &colors);
      try std.testing.expectEqual(c.REPLXX_COLOR_BRIGHTGREEN, colors[0]);
  }

  test "highlightLine: repl command is cyan" {
      const input = ":type";
      var colors: [input.len]c.ReplxxColor = undefined;
      highlightLine(input, &colors);
      try std.testing.expectEqual(c.REPLXX_COLOR_CYAN, colors[0]);
  }

  test "highlightLine: operator '->' is magenta" {
      const input = "->";
      var colors: [input.len]c.ReplxxColor = undefined;
      highlightLine(input, &colors);
      try std.testing.expectEqual(c.REPLXX_COLOR_MAGENTA, colors[0]);
      try std.testing.expectEqual(c.REPLXX_COLOR_MAGENTA, colors[1]);
  }

  test "highlightLine: string literal is yellow" {
      const input = "\"hello\"";
      var colors: [input.len]c.ReplxxColor = undefined;
      highlightLine(input, &colors);
      for (colors) |col| {
          try std.testing.expectEqual(c.REPLXX_COLOR_YELLOW, col);
      }
  }
  ```

- [ ] **Step 3.2: Run tests to confirm they fail**

  ```bash
  zig build test -- --test-filter "currentToken"
  ```

  Expected: compile error — functions not yet implemented.

- [ ] **Step 3.3: Implement pure helper functions**

  Append the following implementations to `src/repl/line_editor.zig` (after the tests):

  ```zig
  // ── Pure helpers ──────────────────────────────────────────────────────

  /// Extract the token being completed from the current input line.
  ///
  /// - If the line starts with ':', and has no space yet, returns the
  ///   whole ':...' prefix (command completion).
  /// - If the line is ':cmd <arg>', returns the argument portion after
  ///   the last space (file/path completion for :load).
  /// - Otherwise, returns the last word after any word-break character.
  fn currentToken(line: []const u8) []const u8 {
      if (line.len == 0) return line;

      if (line[0] == ':') {
          const sp = std.mem.indexOfScalar(u8, line, ' ') orelse return line;
          // After the command, complete the argument.
          const rest = line[sp + 1 ..];
          const last_sp = std.mem.lastIndexOfScalar(u8, rest, ' ') orelse return rest;
          return rest[last_sp + 1 ..];
      }

      // Walk backward to find the last word-break character.
      var i = line.len;
      while (i > 0) {
          i -= 1;
          switch (line[i]) {
              ' ', '\t', '(', ')', ',', '[', ']', '.' => return line[i + 1 ..],
              else => {},
          }
      }
      return line;
  }

  fn isFileCompletionContext(line: []const u8) bool {
      return std.mem.startsWith(u8, line, ":load ") or
          std.mem.startsWith(u8, line, ":l ");
  }

  /// Build completions for REPL commands matching `prefix`.
  fn commandCompletions(
      alloc: Allocator,
      prefix: []const u8,
      out: *std.ArrayListUnmanaged(Completion),
  ) !void {
      for (repl_commands) |cmd| {
          if (std.mem.startsWith(u8, cmd, prefix)) {
              const text = try alloc.dupeZ(u8, cmd);
              try out.append(alloc, .{ .text = text, .color = c.REPLXX_COLOR_CYAN });
          }
      }
  }

  /// Build completions for filesystem paths matching `prefix`.
  fn fileCompletions(
      alloc: Allocator,
      prefix: []const u8,
      out: *std.ArrayListUnmanaged(Completion),
  ) !void {
      const dir_end = if (std.mem.lastIndexOfScalar(u8, prefix, '/')) |i| i + 1 else 0;
      const dir_part = if (dir_end > 0) prefix[0..dir_end] else ".";
      const file_part = prefix[dir_end..];

      var dir = std.fs.cwd().openDir(dir_part, .{ .iterate = true }) catch return;
      defer dir.close();

      var it = dir.iterate();
      while (it.next() catch null) |entry| {
          if (!std.mem.startsWith(u8, entry.name, file_part)) continue;
          const text: [:0]u8 = if (dir_end > 0)
              try std.fmt.allocPrintZ(alloc, "{s}{s}", .{ prefix[0..dir_end], entry.name })
          else
              try alloc.dupeZ(u8, entry.name);
          try out.append(alloc, .{ .text = text, .color = c.REPLXX_COLOR_WHITE });
      }
  }

  /// Build completions for in-scope identifiers matching `prefix`.
  fn nameCompletions(
      session: *Session,
      alloc: Allocator,
      prefix: []const u8,
      out: *std.ArrayListUnmanaged(Completion),
  ) !void {
      var names: std.ArrayListUnmanaged([]const u8) = .empty;
      defer names.deinit(alloc);
      try session.rename_env.scope.collectNames(alloc, &names);

      for (names.items) |name| {
          if (!std.mem.startsWith(u8, name, prefix)) continue;
          const text = try alloc.dupeZ(u8, name);
          const color: c.ReplxxColor = if (name.len > 0 and std.ascii.isUpper(name[0]))
              c.REPLXX_COLOR_BRIGHTGREEN
          else
              c.REPLXX_COLOR_WHITE;
          try out.append(alloc, .{ .text = text, .color = color });
      }
  }

  /// Dispatch completion candidates based on input context.
  pub fn completionsFor(
      session: *Session,
      alloc: Allocator,
      prefix: []const u8,
      line: []const u8,
      out: *std.ArrayListUnmanaged(Completion),
  ) !void {
      if (line.len > 0 and line[0] == ':') {
          if (isFileCompletionContext(line)) {
              try fileCompletions(alloc, prefix, out);
          } else {
              try commandCompletions(alloc, prefix, out);
          }
      } else {
          try nameCompletions(session, alloc, prefix, out);
      }
  }

  /// Return the hint suffix (ghost text) for the current input, or null.
  /// The returned slice is allocated from `alloc` and null-terminated.
  pub fn hintsFor(
      session: *Session,
      alloc: Allocator,
      prefix: []const u8,
      line: []const u8,
  ) ?[:0]u8 {
      if (prefix.len == 0) return null;

      if (line.len > 0 and line[0] == ':' and !isFileCompletionContext(line)) {
          for (repl_commands) |cmd| {
              if (std.mem.startsWith(u8, cmd, prefix) and cmd.len > prefix.len) {
                  return alloc.dupeZ(u8, cmd[prefix.len..]) catch null;
              }
          }
          return null;
      }

      var names: std.ArrayListUnmanaged([]const u8) = .empty;
      defer names.deinit(alloc);
      session.rename_env.scope.collectNames(alloc, &names) catch return null;

      for (names.items) |name| {
          if (std.mem.startsWith(u8, name, prefix) and name.len > prefix.len) {
              return alloc.dupeZ(u8, name[prefix.len..]) catch null;
          }
      }
      return null;
  }

  /// Colorize `input` by writing a `ReplxxColor` per character into `colors`.
  ///
  /// Uses token-level recognition (no parser):
  ///   `:command`   → cyan
  ///   keywords     → blue
  ///   Constructors → bright green
  ///   numbers      → yellow
  ///   strings      → yellow
  ///   operators    → magenta
  ///   other        → default
  pub fn highlightLine(input: []const u8, colors: []c.ReplxxColor) void {
      @memset(colors, c.REPLXX_COLOR_DEFAULT);
      if (input.len == 0) return;
      const n = @min(input.len, colors.len);

      var i: usize = 0;

      // REPL command: starts with ':'
      if (n > 0 and input[0] == ':') {
          while (i < n and input[i] != ' ') : (i += 1) {
              colors[i] = c.REPLXX_COLOR_CYAN;
          }
      }

      while (i < n) {
          const ch = input[i];

          if (ch == ' ' or ch == '\t') {
              i += 1;
              continue;
          }

          // String literal "..."
          if (ch == '"') {
              const start = i;
              i += 1;
              while (i < n and input[i] != '"') {
                  if (input[i] == '\\') i += 1;
                  if (i < n) i += 1;
              }
              if (i < n) i += 1; // closing '"'
              @memset(colors[start..i], c.REPLXX_COLOR_YELLOW);
              continue;
          }

          // Number literal
          if (std.ascii.isDigit(ch)) {
              const start = i;
              while (i < n and (std.ascii.isDigit(input[i]) or input[i] == '.')) {
                  i += 1;
              }
              @memset(colors[start..i], c.REPLXX_COLOR_YELLOW);
              continue;
          }

          // Identifier or keyword
          if (std.ascii.isAlphabetic(ch) or ch == '_') {
              const start = i;
              while (i < n) : (i += 1) {
                  const c2 = input[i];
                  if (!std.ascii.isAlphanumeric(c2) and c2 != '_' and c2 != '\'') break;
              }
              const word = input[start..i];
              const color: c.ReplxxColor = if (std.ascii.isUpper(word[0]))
                  c.REPLXX_COLOR_BRIGHTGREEN
              else if (isKeyword(word))
                  c.REPLXX_COLOR_BLUE
              else
                  c.REPLXX_COLOR_DEFAULT;
              @memset(colors[start..i], color);
              continue;
          }

          // Operator characters
          if (isOperatorChar(ch)) {
              const start = i;
              while (i < n and isOperatorChar(input[i])) {
                  i += 1;
              }
              @memset(colors[start..i], c.REPLXX_COLOR_MAGENTA);
              continue;
          }

          i += 1;
      }
  }

  fn isKeyword(word: []const u8) bool {
      for (haskell_keywords) |kw| {
          if (std.mem.eql(u8, word, kw)) return true;
      }
      return false;
  }

  fn isOperatorChar(ch: u8) bool {
      return switch (ch) {
          '+', '-', '*', '/', '=', '<', '>', '!', '@', '#',
          '$', '%', '^', '&', '|', '~', '?', '\\', ':',
          => true,
          else => false,
      };
  }
  ```

- [ ] **Step 3.4: Run the helper tests**

  ```bash
  zig build test -- --test-filter "currentToken"
  zig build test -- --test-filter "commandCompletions"
  zig build test -- --test-filter "highlightLine"
  ```

  Expected: all PASS.

- [ ] **Step 3.5: Add `CallbackCtx` and the C callbacks**

  Append to `src/repl/line_editor.zig`:

  ```zig
  // ── Callback context ──────────────────────────────────────────────────

  /// Passed to all replxx callbacks via the `userData` void pointer.
  const CallbackCtx = struct {
      session: *Session,
      allocator: Allocator,
  };

  // ── C callbacks ───────────────────────────────────────────────────────

  fn completionCallback(
      input: [*:0]const u8,
      completions: *c.replxx_completions,
      context_len: *c_int,
      user_data: ?*anyopaque,
  ) callconv(.C) void {
      const ctx: *CallbackCtx = @ptrCast(@alignCast(user_data orelse return));
      var arena = std.heap.ArenaAllocator.init(ctx.allocator);
      defer arena.deinit();
      const alloc = arena.allocator();

      const line = std.mem.sliceTo(input, 0);
      const prefix = currentToken(line);
      context_len.* = @intCast(prefix.len);

      var candidates: std.ArrayListUnmanaged(Completion) = .empty;
      completionsFor(ctx.session, alloc, prefix, line, &candidates) catch return;

      for (candidates.items) |cand| {
          c.replxx_add_color_completion(completions, @ptrCast(cand.text.ptr), cand.color);
      }
  }

  fn hintCallback(
      input: [*:0]const u8,
      hints: *c.replxx_hints,
      context_len: *c_int,
      color: *c.ReplxxColor,
      user_data: ?*anyopaque,
  ) callconv(.C) void {
      const ctx: *CallbackCtx = @ptrCast(@alignCast(user_data orelse return));
      var arena = std.heap.ArenaAllocator.init(ctx.allocator);
      defer arena.deinit();
      const alloc = arena.allocator();

      const line = std.mem.sliceTo(input, 0);
      const prefix = currentToken(line);
      context_len.* = @intCast(prefix.len);
      color.* = c.REPLXX_COLOR_GRAY;

      const hint = hintsFor(ctx.session, alloc, prefix, line) orelse return;
      c.replxx_add_hint(hints, @ptrCast(hint.ptr));
  }

  fn highlightCallback(
      input: [*:0]const u8,
      colors: [*]c.ReplxxColor,
      size: c_int,
      user_data: ?*anyopaque,
  ) callconv(.C) void {
      _ = user_data;
      const line = std.mem.sliceTo(input, 0);
      const n: usize = @intCast(size);
      highlightLine(line, colors[0..n]);
  }
  ```

- [ ] **Step 3.6: Add the `LineEditor` struct**

  Append to `src/repl/line_editor.zig`:

  ```zig
  // ── LineEditor ────────────────────────────────────────────────────────

  pub const LineEditor = struct {
      rx: *c.Replxx,
      allocator: Allocator,
      ctx: *CallbackCtx,
      history_path: [:0]u8,

      /// Initialise a line editor.
      ///
      /// Registers completion, hint, and highlighting callbacks.
      /// Loads history from `history_path` if the file exists.
      pub fn init(
          allocator: Allocator,
          session: *Session,
          history_path: []const u8,
      ) !LineEditor {
          const rx = c.replxx_init() orelse return error.ReplxxInitFailed;
          errdefer c.replxx_end(rx);

          const ctx = try allocator.create(CallbackCtx);
          errdefer allocator.destroy(ctx);
          ctx.* = .{ .session = session, .allocator = allocator };

          c.replxx_set_max_history_size(rx, max_history_entries);
          c.replxx_set_unique_history(rx, 1);

          c.replxx_set_completion_callback(rx, completionCallback, ctx);
          c.replxx_set_hint_callback(rx, hintCallback, ctx);
          c.replxx_set_highlighter_callback(rx, highlightCallback, ctx);

          const path_z = try allocator.dupeZ(u8, history_path);
          errdefer allocator.free(path_z);

          // Ignore load errors — file may not exist on first run.
          _ = c.replxx_history_load(rx, path_z);

          return .{
              .rx = rx,
              .allocator = allocator,
              .ctx = ctx,
              .history_path = path_z,
          };
      }

      /// Save history to disk and free resources.
      pub fn deinit(self: *LineEditor) void {
          _ = c.replxx_history_save(self.rx, self.history_path);
          c.replxx_end(self.rx);
          self.allocator.free(self.history_path);
          self.allocator.destroy(self.ctx);
      }

      /// Read the next line from the terminal with full line editing.
      ///
      /// Returns the line as a slice (valid until the next call to `readLine`).
      /// Returns `null` on EOF (Ctrl+D) or read error.
      /// Non-empty lines are automatically added to history.
      pub fn readLine(self: *LineEditor, prompt: []const u8) !?[]const u8 {
          const prompt_z = try self.allocator.dupeZ(u8, prompt);
          defer self.allocator.free(prompt_z);

          const result = c.replxx_input(self.rx, prompt_z);
          if (result == null) return null;

          const line = std.mem.sliceTo(result, 0);
          if (line.len > 0) {
              c.replxx_history_add(self.rx, result);
          }
          return line;
      }
  };
  ```

- [ ] **Step 3.7: Run full test suite to confirm no regressions**

  ```bash
  zig build test --summary all 2>&1 | tail -20
  ```

  Expected: all tests pass (the new helper tests plus all pre-existing tests).

- [ ] **Step 3.8: Commit**

  ```bash
  git add src/repl/line_editor.zig
  git commit -m "#76: Add LineEditor wrapping replxx with completion/hints/highlighting"
  ```

---

### Task 4: Integrate `LineEditor` into `cli.zig`

**Files:**
- Modify: `src/repl/cli.zig`

- [ ] **Step 4.1: Add imports and `historyFilePath`**

  At the top of `src/repl/cli.zig`, add the import after the existing imports:

  ```zig
  const LineEditor = @import("line_editor.zig").LineEditor;
  ```

  Then add the `historyFilePath` helper function (before `run`, around line 55):

  ```zig
  /// Return the absolute path to the REPL history file: ~/.rhc/repl_history.
  ///
  /// Creates ~/.rhc/ if it does not exist.
  /// The caller owns the returned slice (allocated with `allocator`).
  fn historyFilePath(allocator: Allocator) ![]const u8 {
      const home = std.posix.getenv("HOME") orelse return error.NoHomeDir;
      const dir_path = try std.fs.path.join(allocator, &.{ home, ".rhc" });
      defer allocator.free(dir_path);

      std.fs.makeDirAbsolute(dir_path) catch |err| switch (err) {
          error.PathAlreadyExists => {},
          else => return err,
      };

      return std.fs.path.join(allocator, &.{ home, ".rhc", "repl_history" });
  }
  ```

- [ ] **Step 4.2: Replace the `run()` loop body**

  The current `run()` function (line 55–167):
  - Has `var line_buf: [4096]u8 = undefined;`
  - Calls `try writeStdout(io, prompt)` before reading
  - Calls `readLine(io, &line_buf) catch { ... break; }`

  Replace the section from `try printBanner(io);` through the end of `run()`
  with the following:

  ```zig
  try printBanner(io);

  const history_path = historyFilePath(allocator) catch |err| blk: {
      // Non-fatal: fall back to no persistence if home dir is inaccessible.
      var buf: [128]u8 = undefined;
      const msg = std.fmt.bufPrint(&buf, "Warning: history unavailable: {}\n", .{err}) catch "";
      writeStderr(io, msg) catch {};
      break :blk "";
  };
  defer if (history_path.len > 0) allocator.free(history_path);

  var editor = LineEditor.init(allocator, &session, history_path) catch |err| {
      var buf: [128]u8 = undefined;
      const msg = std.fmt.bufPrint(&buf, "Warning: line editor unavailable: {}\n", .{err}) catch "";
      writeStderr(io, msg) catch {};
      // Fall back to the simple loop below.
      try runSimple(alloc, io, &session);
      return;
  };
  defer editor.deinit();

  var mode: InputMode = .normal;
  var multiline_buf: std.ArrayListUnmanaged(u8) = .empty;
  defer multiline_buf.deinit(allocator);

  while (true) {
      const prompt = switch (mode) {
          .normal => "rusholme> ",
          .multiline => "rusholme| ",
      };

      const line = (try editor.readLine(prompt)) orelse {
          if (mode == .multiline) {
              multiline_buf.clearRetainingCapacity();
              mode = .normal;
          }
          try writeStdout(io, "\n");
          break;
      };

      if (line.len == 0) continue;

      // ── Multiline mode handling ───────────────────────────────
      if (mode == .multiline) {
          const trimmed = std.mem.trim(u8, line, " \t\r");

          if (std.mem.eql(u8, trimmed, ":}")) {
              const input = multiline_buf.items;
              defer multiline_buf.clearRetainingCapacity();
              mode = .normal;

              if (input.len == 0) continue;

              const result = evaluate(alloc, &session, input) catch |err| {
                  try printError(io, err);
                  continue;
              };
              if (result.status == .success) {
                  try writeStdout(io, result.value);
                  try writeStdout(io, "\n");
              } else if (result.status == .failed) {
                  renderDiagnostics(io, alloc, &session, result.diagnostics);
              }
              continue;
          }

          if (std.mem.eql(u8, trimmed, ":quit") or std.mem.eql(u8, trimmed, ":q")) {
              multiline_buf.clearRetainingCapacity();
              mode = .normal;
              break;
          }

          try multiline_buf.appendSlice(allocator, line);
          try multiline_buf.append(allocator, '\n');
          continue;
      }

      // ── Normal mode ───────────────────────────────────────────
      if (line[0] == ':') {
          const cmd = std.mem.trim(u8, line[1..], " \t\r");
          if (std.mem.eql(u8, cmd, "{")) {
              mode = .multiline;
              continue;
          }
          const should_continue = handleCommand(io, line, alloc, &session);
          if (!should_continue) break;
          continue;
      }

      const result = evaluate(alloc, &session, line) catch |err| {
          try printError(io, err);
          continue;
      };
      if (result.status == .success) {
          try writeStdout(io, result.value);
          try writeStdout(io, "\n");
      } else if (result.status == .failed) {
          renderDiagnostics(io, alloc, &session, result.diagnostics);
      }
  }
  ```

- [ ] **Step 4.3: Add `runSimple` fallback and remove `readLine`**

  The old `readLine` function (lines 174–193) can now be repurposed as `runSimple`
  for the case where `LineEditor.init` fails (e.g. non-TTY environment). Add this
  private function after `run()`:

  ```zig
  /// Fallback loop used when the line editor cannot be initialised.
  /// Uses basic byte-by-byte reading with no history or completion.
  fn runSimple(alloc: Allocator, io: Io, session: *Session) !void {
      var line_buf: [4096]u8 = undefined;
      var mode: InputMode = .normal;
      var multiline_buf: std.ArrayListUnmanaged(u8) = .empty;
      defer multiline_buf.deinit(alloc);

      while (true) {
          const prompt = switch (mode) {
              .normal => "rusholme> ",
              .multiline => "rusholme| ",
          };
          try writeStdout(io, prompt);

          const line = readLineRaw(io, &line_buf) catch {
              if (mode == .multiline) {
                  multiline_buf.clearRetainingCapacity();
                  mode = .normal;
              }
              try writeStdout(io, "\n");
              break;
          };

          if (line.len == 0) continue;

          if (mode == .multiline) {
              const trimmed = std.mem.trim(u8, line, " \t\r");
              if (std.mem.eql(u8, trimmed, ":}")) {
                  const input = multiline_buf.items;
                  defer multiline_buf.clearRetainingCapacity();
                  mode = .normal;
                  if (input.len == 0) continue;
                  const result = evaluate(alloc, session, input) catch |err| {
                      try printError(io, err);
                      continue;
                  };
                  if (result.status == .success) {
                      try writeStdout(io, result.value);
                      try writeStdout(io, "\n");
                  } else if (result.status == .failed) {
                      renderDiagnostics(io, alloc, session, result.diagnostics);
                  }
                  continue;
              }
              if (std.mem.eql(u8, trimmed, ":quit") or std.mem.eql(u8, trimmed, ":q")) {
                  multiline_buf.clearRetainingCapacity();
                  mode = .normal;
                  break;
              }
              try multiline_buf.appendSlice(alloc, line);
              try multiline_buf.append(alloc, '\n');
              continue;
          }

          if (line[0] == ':') {
              const cmd = std.mem.trim(u8, line[1..], " \t\r");
              if (std.mem.eql(u8, cmd, "{")) {
                  mode = .multiline;
                  continue;
              }
              const should_continue = handleCommand(io, line, alloc, session);
              if (!should_continue) break;
              continue;
          }

          const result = evaluate(alloc, session, line) catch |err| {
              try printError(io, err);
              continue;
          };
          if (result.status == .success) {
              try writeStdout(io, result.value);
              try writeStdout(io, "\n");
          } else if (result.status == .failed) {
              renderDiagnostics(io, alloc, session, result.diagnostics);
          }
      }
  }
  ```

  Rename the old `readLine` to `readLineRaw` (it is only used by `runSimple` now):

  ```zig
  /// Read a line from stdin into the provided buffer (raw, no editing).
  fn readLineRaw(io: Io, buf: []u8) ![]const u8 {
      // ... keep the existing implementation unchanged, just renamed ...
  }
  ```

- [ ] **Step 4.4: Build and confirm it compiles**

  ```bash
  zig build 2>&1 | head -30
  ```

  Expected: builds without errors or warnings.

- [ ] **Step 4.5: Run the full test suite**

  ```bash
  zig build test --summary all 2>&1 | tail -30
  ```

  Expected: all tests pass.

- [ ] **Step 4.6: Commit**

  ```bash
  git add src/repl/cli.zig
  git commit -m "#76: Integrate LineEditor into cli.zig; add runSimple fallback"
  ```

---

### Task 5: Manual smoke test and PR

**Files:**
- None (verification only)

- [ ] **Step 5.1: Build and run the REPL**

  ```bash
  zig build && ./zig-out/bin/rhc repl
  ```

  Verify the following manually:

  1. Prompt `rusholme> ` appears.
  2. Typing `:t` then Tab cycles through `:type` and `:t` completions (cyan).
  3. Typing `:t` shows ghost hint `"ype"` in gray.
  4. Typing `J` shows `Just`, `Nothing`, etc. (bright green — constructors).
  5. Typing `put` shows completions like `putStrLn`, `putStr` (white).
  6. Typing `let ` shows keyword `let` in blue, cursor after space.
  7. Typing `:load ` then Tab shows filesystem entries.
  8. Up/Down arrow navigates history within the session.
  9. Exiting with `:quit` or Ctrl+D saves `~/.rhc/repl_history`.
  10. Reopening the REPL shows previous commands in history (Up arrow).

- [ ] **Step 5.2: Push branch and open PR**

  ```bash
  git push origin llm-agent/issue-76-repl-line-editor
  ```

  Then open the PR:

  ```bash
  cat > /tmp/pr-body.md << 'EOF'
  Closes #76

  ## Summary
  - Adds `src/repl/line_editor.zig`: `LineEditor` struct wrapping the replxx C API
  - Tab completion: REPL commands (cyan), in-scope identifiers (green/white), filesystem paths for `:load`
  - Inline hints: gray ghost-text suffix for first matching candidate
  - Live syntax highlighting: keywords (blue), constructors (bright green), numbers/strings (yellow), operators (magenta), REPL commands (cyan)
  - Persistent history at `~/.rhc/repl_history` (max 1000 entries, dedup enabled)
  - `runSimple` fallback for non-TTY environments
  - Unit tests for `currentToken`, `commandCompletions`, `highlightLine`
  - Adds `Scope.collectNames` in `renamer.zig` for completion candidate enumeration

  ## Deliverables
  - [x] Tab-completion for REPL commands
  - [x] Tab-completion for identifiers in scope
  - [x] Tab-completion for filesystem paths (`:load`)
  - [x] Inline hints
  - [x] Syntax highlighting
  - [x] Persistent history at `~/.rhc/`
  - [x] Unit tests for pure helpers

  ## Testing
  See manual smoke test checklist in Task 5.1 above.
  Run `zig build test --summary all` for the automated tests.
  EOF

  gh pr create \
    --title "#76: REPL line editor with replxx (completion, hints, highlighting, history)" \
    --body-file /tmp/pr-body.md \
    --base main \
    --head llm-agent/issue-76-repl-line-editor \
    --reviewer adinapoli
  ```

- [ ] **Step 5.3: Update ROADMAP.md to in-review**

  On `llm-agent/issue-76-repl-line-editor`, find issue #76 in `ROADMAP.md` and change its
  status from `:white_circle:` to `:yellow_circle:`. Commit:

  ```bash
  git add ROADMAP.md
  git commit -m "#76: Update roadmap status to in-review"
  git push origin llm-agent/issue-76-repl-line-editor
  ```

---

## Self-Review

**Spec coverage:**
- Tab completion (commands, names, files) → Tasks 3 + 4 ✓
- Inline hints → Task 3 ✓
- Syntax highlighting → Task 3 ✓
- History at `~/.rhc/repl_history` → Tasks 3 + 4 ✓
- `~/.rhc/` directory creation → Task 4 `historyFilePath` ✓
- Unit tests for pure helpers → Task 3 ✓
- `build.zig` + `flake.nix` changes → Task 1 ✓
- `Scope.collectNames` → Task 2 ✓

**Placeholder scan:** None found.

**Type consistency:**
- `LineEditor.readLine` returns `!?[]const u8` → used in Task 4 with `(try editor.readLine(...)) orelse` ✓
- `Completion.text: [:0]u8` → passed via `@ptrCast(cand.text.ptr)` to `[*c]const u8` ✓
- `CallbackCtx` defined before callbacks that use it ✓
- `collectNames` defined in Task 2, used in `nameCompletions` and `hintsFor` in Task 3 ✓
