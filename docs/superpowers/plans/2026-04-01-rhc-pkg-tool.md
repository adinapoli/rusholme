# `rhc pkg` Tool Implementation Plan (#651)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement `rhc pkg` as a subcommand of `rhc` with five operations: `list`, `describe`, `install`, `unregister`, `check`.

**Architecture:** A new `src/packages/pkg_cmd.zig` module holds all subcommand implementations, each accepting a `*store.Store` so tests can inject a tmpDir-backed store. The `store.zig` module gains an `unregister` method and exports `computeKey` publicly. `main.zig` dispatches `rhc pkg ...` by creating the default store and routing to the correct subcommand function.

**Tech Stack:** Zig 0.16 dev, `std.Io`, `std.testing.tmpDir`, `src/packages/store.zig`, `src/packages/descriptor.zig`.

---

## File Map

| File | Action | Purpose |
|------|--------|---------|
| `src/packages/store.zig` | Modify | Add `PackageNotFound` error, `unregister` method, make `computeKey` `pub` |
| `src/packages/pkg_cmd.zig` | **Create** | All `rhc pkg` subcommand implementations |
| `src/root.zig` | Modify | Expose `pkg_cmd` in `packages` namespace and `refAllDecls` |
| `src/main.zig` | Modify | Dispatch `pkg` command, update `printUsage` |
| `tests/pkg_cmd_test.zig` | **Create** | Integration tests for all subcommands |
| `build.zig` | Modify | Register `pkg-cmd-tests` suite |

---

## Reference: Key APIs

```zig
// File deletion (Zig 0.16):
try std.Io.Dir.deleteFile(.cwd(), io, absolute_path);

// File writer pattern (match main.zig style):
var buf: [4096]u8 = undefined;
var fw: File.Writer = .init(.stdout(), io, &buf);
const out = &fw.interface;
try out.print("...\n", .{...});
try out.flush();

// Store functions used in this plan:
store.init(alloc, io, ?path) !Store          // null = default path
store.register(io, key, content, desc) !void
store.unregister(io, name, version) !void    // added in Task 1
store.lookup(io, name, version) !?Entry
store.list(io) ![]const Entry
store.computeKey(alloc, name, ver, content) ![]u8  // made pub in Task 2
descriptor.parse(alloc, source) !PackageDescriptor
```

---

## Task 1: Add `PackageNotFound` error and `unregister` to Store

**Files:**
- Modify: `src/packages/store.zig`

- [ ] **Step 1: Write the two failing tests** — append these at the bottom of `src/packages/store.zig` (above the final closing brace if any, or at the end of the file):

```zig
test "Store.unregister removes conf file" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var s = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer s.deinit();

    const content = "name = \"pkg-a\"\nversion = \"1.0.0\"\n";
    const desc = try descriptor.parse(std.testing.allocator, content);
    defer desc.deinit(std.testing.allocator);
    const key = try computeKey(std.testing.allocator, desc.name, desc.version, content);
    defer std.testing.allocator.free(key);
    try s.register(std.testing.io, key, content, desc);

    const before = try s.list(std.testing.io);
    try std.testing.expectEqual(@as(usize, 1), before.len);
    for (before) |e| e.deinit(std.testing.allocator);
    std.testing.allocator.free(before);

    try s.unregister(std.testing.io, "pkg-a", "1.0.0");

    const after = try s.list(std.testing.io);
    defer { for (after) |e| e.deinit(std.testing.allocator); std.testing.allocator.free(after); }
    try std.testing.expectEqual(@as(usize, 0), after.len);
}

test "Store.unregister returns PackageNotFound for unknown package" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var s = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer s.deinit();

    try std.testing.expectError(
        error.PackageNotFound,
        s.unregister(std.testing.io, "ghost", "0.0.1"),
    );
}
```

- [ ] **Step 2: Run and confirm both tests FAIL**

```bash
zig build test -- --test-filter "Store.unregister"
```

Expected: compile error — `error.PackageNotFound` does not exist yet and `unregister` is undefined.

- [ ] **Step 3: Add `PackageNotFound` to the `Error` union in `src/packages/store.zig`**

Find the `pub const Error = error{` block (around line 212) and add one entry:

```zig
pub const Error = error{
    /// Attempted to register a package that already exists.
    DuplicatePackage,
    /// A .conf file exists but is malformed.
    InvalidConf,
    /// The requested package was not found in the store.
    PackageNotFound,
    // ... rest unchanged
```

- [ ] **Step 4: Add `unregister` to the `Store` struct** — insert after the `list` function (before the closing `};` of the struct):

```zig
/// Remove a package's registry entry from `package.conf.d/`.
///
/// Deletes the `.conf` file for the package named `name` at version `version`.
/// Does NOT delete the compiled artifact directory — artifacts survive
/// unregistration and must be cleaned up separately.
///
/// Returns `error.PackageNotFound` if no matching entry exists.
pub fn unregister(
    self: *Store,
    io: std.Io,
    name: []const u8,
    version: []const u8,
) Error!void {
    const entries = try self.list(io);
    defer {
        for (entries) |e| e.deinit(self.allocator);
        self.allocator.free(entries);
    }

    for (entries) |entry| {
        if (std.mem.eql(u8, entry.name, name) and
            std.mem.eql(u8, entry.version, version))
        {
            const conf_path = try computeConfPath(self, entry.key);
            defer self.allocator.free(conf_path);
            try std.Io.Dir.deleteFile(.cwd(), io, conf_path);
            return;
        }
    }

    return error.PackageNotFound;
}
```

- [ ] **Step 5: Run tests and confirm both PASS**

```bash
zig build test -- --test-filter "Store.unregister"
```

Expected:
```
All 2 tests passed.
```

- [ ] **Step 6: Commit**

```bash
git add src/packages/store.zig
git commit -m "#651: Add Store.unregister and PackageNotFound error"
```

---

## Task 2: Make `computeKey` public

**Files:**
- Modify: `src/packages/store.zig`

- [ ] **Step 1: Change the access modifier** — find line `fn computeKey(` (around line 297) and change it to `pub fn computeKey(`:

```zig
pub fn computeKey(alloc: std.mem.Allocator, name: []const u8, version: []const u8, descriptor_content: []const u8) std.mem.Allocator.Error![]const u8 {
```

- [ ] **Step 2: Verify nothing is broken**

```bash
zig build test --summary all
```

Expected: all existing tests still pass (count unchanged).

- [ ] **Step 3: Commit**

```bash
git add src/packages/store.zig
git commit -m "#651: Export computeKey as pub for use by pkg_cmd"
```

---

## Task 3: Create `src/packages/pkg_cmd.zig` with `cmdPkgList`

**Files:**
- Create: `src/packages/pkg_cmd.zig`

- [ ] **Step 1: Write the failing test for `cmdPkgList`** — create `src/packages/pkg_cmd.zig` with this content:

```zig
//! Subcommand implementations for `rhc pkg`.
//!
//! Each public function accepts a `*store.Store` so callers (including tests)
//! can supply their own store instead of relying on the default path.
//!
//! Issue: #651

const std = @import("std");
const Io = std.Io;
const File = Io.File;
const store = @import("store.zig");
const descriptor = @import("descriptor.zig");

// ── cmdPkgList ────────────────────────────────────────────────────────────────

/// Print one `<name>-<version>` line per installed package to stdout.
pub fn cmdPkgList(alloc: std.mem.Allocator, io: Io, s: *store.Store) !void {
    _ = alloc;
    _ = io;
    _ = s;
    return error.NotImplemented;
}

// ── Tests ─────────────────────────────────────────────────────────────────────

fn makeTestStore(alloc: std.mem.Allocator, tmp: *std.testing.TmpDir) !store.Store {
    const path_z = try std.Io.Dir.realPathFileAlloc(tmp.dir, std.testing.io, ".", alloc);
    defer alloc.free(path_z);
    const path = try alloc.dupe(u8, path_z);
    defer alloc.free(path);
    return store.init(alloc, std.testing.io, path);
}

fn registerTestPkg(
    alloc: std.mem.Allocator,
    s: *store.Store,
    name: []const u8,
    version: []const u8,
) !void {
    const content = try std.fmt.allocPrint(
        alloc,
        "name = \"{s}\"\nversion = \"{s}\"\n",
        .{ name, version },
    );
    defer alloc.free(content);
    const desc = try descriptor.parse(alloc, content);
    defer desc.deinit(alloc);
    const key = try store.computeKey(alloc, name, version, content);
    defer alloc.free(key);
    try s.register(std.testing.io, key, content, desc);
}

test "cmdPkgList lists installed packages" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "alpha", "1.0.0");
    try registerTestPkg(std.testing.allocator, &s, "beta", "2.3.0");

    // cmdPkgList must complete without error (output goes to std.testing.io)
    try cmdPkgList(std.testing.allocator, std.testing.io, &s);

    // Verify both packages remain registered after listing (non-destructive)
    const entries = try s.list(std.testing.io);
    defer { for (entries) |e| e.deinit(std.testing.allocator); std.testing.allocator.free(entries); }
    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

test "cmdPkgList succeeds on empty store" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try cmdPkgList(std.testing.allocator, std.testing.io, &s);
}
```

- [ ] **Step 2: Run and confirm tests FAIL**

```bash
zig build test -- --test-filter "cmdPkgList"
```

Expected: error — `error.NotImplemented` (or compile error for missing `error.NotImplemented`). Add `const NotImplementedError = error{NotImplemented};` temporarily if needed, or just verify the test fails for the right reason.

- [ ] **Step 3: Implement `cmdPkgList`**

Replace the stub body:

```zig
pub fn cmdPkgList(alloc: std.mem.Allocator, io: Io, s: *store.Store) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    const out = &fw.interface;

    for (entries) |entry| {
        try out.print("{s}-{s}\n", .{ entry.name, entry.version });
    }
    try out.flush();
}
```

- [ ] **Step 4: Run and confirm tests PASS**

```bash
zig build test -- --test-filter "cmdPkgList"
```

Expected: `All 2 tests passed.`

- [ ] **Step 5: Commit**

```bash
git add src/packages/pkg_cmd.zig
git commit -m "#651: Add cmdPkgList"
```

---

## Task 4: Add `cmdPkgDescribe`

**Files:**
- Modify: `src/packages/pkg_cmd.zig`

Output format (one block per matching package):
```
name: alpha
version: 1.0.0
id: <64-char-sha256>-alpha-1.0.0
install-path: /path/to/alpha-1.0.0
exposed-modules: Mod.A Mod.B
depends: dep-0.1.0
```

- [ ] **Step 1: Add the stub and its failing test** — append to `src/packages/pkg_cmd.zig`:

```zig
// ── cmdPkgDescribe ────────────────────────────────────────────────────────────

/// Print metadata for all installed packages whose name equals `name`.
/// Prints nothing and exits cleanly if no packages match.
pub fn cmdPkgDescribe(alloc: std.mem.Allocator, io: Io, s: *store.Store, name: []const u8) !void {
    _ = alloc;
    _ = io;
    _ = s;
    _ = name;
    return error.NotImplemented;
}

test "cmdPkgDescribe succeeds for known package" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "mypkg", "1.0.0");

    // Must complete without error; output content is not asserted in unit tests.
    try cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "mypkg");
}

test "cmdPkgDescribe succeeds for unknown package (no output)" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    // No error even when no package matches — just silent.
    try cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "ghost");
}
```

- [ ] **Step 2: Run and confirm tests FAIL**

```bash
zig build test -- --test-filter "cmdPkgDescribe"
```

- [ ] **Step 3: Implement `cmdPkgDescribe`**

Replace the stub:

```zig
pub fn cmdPkgDescribe(alloc: std.mem.Allocator, io: Io, s: *store.Store, name: []const u8) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    const out = &fw.interface;

    var first = true;
    for (entries) |entry| {
        if (!std.mem.eql(u8, entry.name, name)) continue;

        if (!first) try out.writeAll("\n");
        first = false;

        try out.print("name: {s}\n", .{entry.name});
        try out.print("version: {s}\n", .{entry.version});
        try out.print("id: {s}\n", .{entry.key});
        try out.print("install-path: {s}\n", .{entry.install_path});

        try out.writeAll("exposed-modules:");
        for (entry.exposed_modules) |m| try out.print(" {s}", .{m});
        try out.writeAll("\n");

        try out.writeAll("depends:");
        for (entry.depends) |d| try out.print(" {s}", .{d});
        try out.writeAll("\n");
    }
    try out.flush();
}
```

- [ ] **Step 4: Run and confirm tests PASS**

```bash
zig build test -- --test-filter "cmdPkgDescribe"
```

- [ ] **Step 5: Commit**

```bash
git add src/packages/pkg_cmd.zig
git commit -m "#651: Add cmdPkgDescribe"
```

---

## Task 5: Add `cmdPkgInstall`

**Files:**
- Modify: `src/packages/pkg_cmd.zig`

Reads a `.rhc-pkg` file from `pkg_path`, parses it, computes the key, and calls `store.register`.

- [ ] **Step 1: Add the stub and failing test** — append to `src/packages/pkg_cmd.zig`:

```zig
// ── cmdPkgInstall ─────────────────────────────────────────────────────────────

/// Install a package from a `.rhc-pkg` descriptor file at `pkg_path`.
/// Prints `<name>-<version> installed` on success.
/// Returns `store.Error.DuplicatePackage` if the package is already registered.
pub fn cmdPkgInstall(alloc: std.mem.Allocator, io: Io, s: *store.Store, pkg_path: []const u8) !void {
    _ = alloc;
    _ = io;
    _ = s;
    _ = pkg_path;
    return error.NotImplemented;
}

test "cmdPkgInstall registers package from descriptor file" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    // Write a .rhc-pkg file into the tmp dir
    const desc_content = "name = \"install-test\"\nversion = \"0.5.0\"\nexposed-modules = [\"Install.Test\"]\ndepends = []\n";
    const path_z = try std.Io.Dir.realPathFileAlloc(tmp.dir, std.testing.io, ".", std.testing.allocator);
    defer std.testing.allocator.free(path_z);
    const pkg_file_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/install-test.rhc-pkg", .{path_z});
    defer std.testing.allocator.free(pkg_file_path);

    // Create the descriptor file
    const file = try std.Io.Dir.createFile(.cwd(), std.testing.io, pkg_file_path, .{});
    var wbuf: [512]u8 = undefined;
    var fw: File.Writer = .init(file, std.testing.io, &wbuf);
    try fw.interface.writeAll(desc_content);
    try fw.interface.flush();
    file.close(std.testing.io);

    try cmdPkgInstall(std.testing.allocator, std.testing.io, &s, pkg_file_path);

    // Package must now appear in the store
    const entry = try s.lookup(std.testing.io, "install-test", "0.5.0");
    try std.testing.expect(entry != null);
    if (entry) |e| e.deinit(std.testing.allocator);
}
```

- [ ] **Step 2: Run and confirm test FAILS**

```bash
zig build test -- --test-filter "cmdPkgInstall"
```

- [ ] **Step 3: Implement `cmdPkgInstall`**

Replace the stub:

```zig
pub fn cmdPkgInstall(alloc: std.mem.Allocator, io: Io, s: *store.Store, pkg_path: []const u8) !void {
    const content = try std.Io.Dir.cwd().readFileAlloc(io, pkg_path, alloc, .unlimited);
    defer alloc.free(content);

    const desc = try descriptor.parse(alloc, content);
    defer desc.deinit(alloc);

    const key = try store.computeKey(alloc, desc.name, desc.version, content);
    defer alloc.free(key);

    try s.register(io, key, content, desc);

    var buf: [256]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    const out = &fw.interface;
    try out.print("{s}-{s} installed\n", .{ desc.name, desc.version });
    try out.flush();
}
```

- [ ] **Step 4: Run and confirm test PASSES**

```bash
zig build test -- --test-filter "cmdPkgInstall"
```

- [ ] **Step 5: Commit**

```bash
git add src/packages/pkg_cmd.zig
git commit -m "#651: Add cmdPkgInstall"
```

---

## Task 6: Add `cmdPkgUnregister`

**Files:**
- Modify: `src/packages/pkg_cmd.zig`

Accepts a `name_version` string of the form `<name>-<version>` (e.g., `base-0.1.0`). Scans the store to find the matching entry.

- [ ] **Step 1: Add the stub and failing tests** — append to `src/packages/pkg_cmd.zig`:

```zig
// ── cmdPkgUnregister ──────────────────────────────────────────────────────────

/// Unregister a package identified by `name_version` (e.g. `"base-0.1.0"`).
/// The argument must match `<name>-<version>` for some registered package.
/// Prints `<name>-<version> unregistered` on success.
/// Returns `store.Error.PackageNotFound` if no matching package exists.
pub fn cmdPkgUnregister(alloc: std.mem.Allocator, io: Io, s: *store.Store, name_version: []const u8) !void {
    _ = alloc;
    _ = io;
    _ = s;
    _ = name_version;
    return error.NotImplemented;
}

test "cmdPkgUnregister removes the package" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "mypkg", "1.0.0");

    try cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "mypkg-1.0.0");

    const entries = try s.list(std.testing.io);
    defer { for (entries) |e| e.deinit(std.testing.allocator); std.testing.allocator.free(entries); }
    try std.testing.expectEqual(@as(usize, 0), entries.len);
}

test "cmdPkgUnregister returns PackageNotFound for unknown name_version" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try std.testing.expectError(
        error.PackageNotFound,
        cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "ghost-9.9.9"),
    );
}
```

- [ ] **Step 2: Run and confirm tests FAIL**

```bash
zig build test -- --test-filter "cmdPkgUnregister"
```

- [ ] **Step 3: Implement `cmdPkgUnregister`**

The argument format is `<name>-<version>`. Match by scanning `s.list()` for an entry where `name ++ "-" ++ version == name_version`.

Replace the stub:

```zig
pub fn cmdPkgUnregister(alloc: std.mem.Allocator, io: Io, s: *store.Store, name_version: []const u8) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

    for (entries) |entry| {
        const full = try std.fmt.allocPrint(alloc, "{s}-{s}", .{ entry.name, entry.version });
        defer alloc.free(full);

        if (std.mem.eql(u8, full, name_version)) {
            try s.unregister(io, entry.name, entry.version);

            var buf: [256]u8 = undefined;
            var fw: File.Writer = .init(.stdout(), io, &buf);
            const out = &fw.interface;
            try out.print("{s} unregistered\n", .{name_version});
            try out.flush();
            return;
        }
    }

    return error.PackageNotFound;
}
```

- [ ] **Step 4: Run and confirm tests PASS**

```bash
zig build test -- --test-filter "cmdPkgUnregister"
```

- [ ] **Step 5: Commit**

```bash
git add src/packages/pkg_cmd.zig
git commit -m "#651: Add cmdPkgUnregister"
```

---

## Task 7: Add `cmdPkgCheck`

**Files:**
- Modify: `src/packages/pkg_cmd.zig`

For each installed package, checks that every exposed module has a corresponding `.rhi` file at `<install_path>/<Module/Path>.rhi` (dots in module names become path separators). Prints `OK` or `MISSING <rhi-path>` per package.

- [ ] **Step 1: Add the stub and failing tests** — append to `src/packages/pkg_cmd.zig`:

```zig
// ── cmdPkgCheck ───────────────────────────────────────────────────────────────

/// Verify that every exposed module in every installed package has a
/// corresponding `.rhi` file.  Prints one line per package:
///   `  <name>-<version>: OK`
///   `  <name>-<version>: MISSING <module/path>.rhi`
///
/// Returns `error.CheckFailed` if any `.rhi` file is absent.
pub const CheckError = error{CheckFailed};

pub fn cmdPkgCheck(alloc: std.mem.Allocator, io: Io, s: *store.Store) !void {
    _ = alloc;
    _ = io;
    _ = s;
    return error.NotImplemented;
}

test "cmdPkgCheck reports OK when no exposed modules" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    // A package with no exposed modules always passes check.
    try registerTestPkg(std.testing.allocator, &s, "noop", "1.0.0");
    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s);
}

test "cmdPkgCheck returns CheckFailed when rhi is missing" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    // Register a package that exposes a module.
    const content = "name = \"has-module\"\nversion = \"1.0.0\"\nexposed-modules = [\"Has.Module\"]\ndepends = []\n";
    const desc = try descriptor.parse(std.testing.allocator, content);
    defer desc.deinit(std.testing.allocator);
    const key = try store.computeKey(std.testing.allocator, desc.name, desc.version, content);
    defer std.testing.allocator.free(key);
    try s.register(std.testing.io, key, content, desc);

    // The .rhi file does NOT exist → check must fail.
    try std.testing.expectError(
        error.CheckFailed,
        cmdPkgCheck(std.testing.allocator, std.testing.io, &s),
    );
}

test "cmdPkgCheck succeeds when rhi exists" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    const content = "name = \"with-rhi\"\nversion = \"1.0.0\"\nexposed-modules = [\"With.Rhi\"]\ndepends = []\n";
    const desc = try descriptor.parse(std.testing.allocator, content);
    defer desc.deinit(std.testing.allocator);
    const key = try store.computeKey(std.testing.allocator, desc.name, desc.version, content);
    defer std.testing.allocator.free(key);
    try s.register(std.testing.io, key, content, desc);

    // Look up the install_path and create the expected .rhi file.
    const entry = (try s.lookup(std.testing.io, "with-rhi", "1.0.0")) orelse return error.TestExpectFailed;
    defer entry.deinit(std.testing.allocator);

    // Create the rhi subdirectory and file: <install_path>/With/Rhi.rhi
    const subdir_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/With", .{entry.install_path});
    defer std.testing.allocator.free(subdir_path);
    try std.Io.Dir.cwd().createDirPath(std.testing.io, subdir_path);

    const rhi_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/With/Rhi.rhi", .{entry.install_path});
    defer std.testing.allocator.free(rhi_path);
    const rhi_file = try std.Io.Dir.createFile(.cwd(), std.testing.io, rhi_path, .{});
    rhi_file.close(std.testing.io);

    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s);
}
```

- [ ] **Step 2: Run and confirm tests FAIL**

```bash
zig build test -- --test-filter "cmdPkgCheck"
```

- [ ] **Step 3: Implement `cmdPkgCheck`**

Module name to path conversion: replace each `.` with `/` and append `.rhi`.
Example: `"Has.Module"` → `"Has/Module.rhi"`.

Replace the stub:

```zig
pub fn cmdPkgCheck(alloc: std.mem.Allocator, io: Io, s: *store.Store) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

    var buf: [4096]u8 = undefined;
    var fw: File.Writer = .init(.stdout(), io, &buf);
    const out = &fw.interface;

    var any_missing = false;

    for (entries) |entry| {
        var pkg_ok = true;

        for (entry.exposed_modules) |mod_name| {
            // Convert "Foo.Bar.Baz" → "Foo/Bar/Baz.rhi"
            const rel = try alloc.dupe(u8, mod_name);
            defer alloc.free(rel);
            std.mem.replaceScalar(u8, rel, '.', '/');

            const rhi_path = try std.fmt.allocPrint(alloc, "{s}/{s}.rhi", .{ entry.install_path, rel });
            defer alloc.free(rhi_path);

            const exists = blk: {
                std.Io.Dir.access(.cwd(), io, rhi_path, .{}) catch |err| {
                    if (err == error.FileNotFound) break :blk false;
                    return err;
                };
                break :blk true;
            };

            if (!exists) {
                try out.print("  {s}-{s}: MISSING {s}.rhi\n", .{
                    entry.name, entry.version, rel,
                });
                pkg_ok = false;
                any_missing = true;
            }
        }

        if (pkg_ok) {
            try out.print("  {s}-{s}: OK\n", .{ entry.name, entry.version });
        }
    }
    try out.flush();

    if (any_missing) return error.CheckFailed;
}
```

**Note:** The `MISSING` print above has a formatting bug. Replace with:

```zig
try out.print("  {s}-{s}: MISSING {s}.rhi\n", .{ entry.name, entry.version, rel });
```

Remove the incorrect line and use this one instead.

- [ ] **Step 4: Run and confirm tests PASS**

```bash
zig build test -- --test-filter "cmdPkgCheck"
```

Expected: `All 3 tests passed.`

- [ ] **Step 5: Commit**

```bash
git add src/packages/pkg_cmd.zig
git commit -m "#651: Add cmdPkgCheck"
```

---

## Task 8: Add `cmdPkg` dispatcher, wire into `main.zig`, update `printUsage`

**Files:**
- Modify: `src/packages/pkg_cmd.zig`
- Modify: `src/main.zig`

The dispatcher `cmdPkg` is the entry point called from `main.zig`. It creates the default store and routes to the right subcommand. It also handles top-level errors by printing a message and calling `std.process.exit(1)`.

- [ ] **Step 1: Add `cmdPkg` to `src/packages/pkg_cmd.zig`** — append before the `// ── Tests` section:

```zig
// ── cmdPkg ────────────────────────────────────────────────────────────────────

/// Top-level dispatcher for `rhc pkg <subcommand>`.
///
/// `args` is the slice of argv after `"pkg"` (i.e. `["list"]`, `["describe", "base"]`, etc.).
pub fn cmdPkg(alloc: std.mem.Allocator, io: Io, args: []const []const u8) !void {
    if (args.len == 0) {
        try writePkgUsage(io);
        std.process.exit(1);
    }

    const subcommand = args[0];
    const sub_args = args[1..];

    var s = store.init(alloc, io, null) catch |err| {
        var ebuf: [512]u8 = undefined;
        var efw: File.Writer = .init(.stderr(), io, &ebuf);
        const err_out = &efw.interface;
        try err_out.print("rhc pkg: cannot open store: {}\n", .{err});
        try err_out.flush();
        std.process.exit(1);
    };
    defer s.deinit();

    if (std.mem.eql(u8, subcommand, "list")) {
        try cmdPkgList(alloc, io, &s);
        return;
    }

    if (std.mem.eql(u8, subcommand, "describe")) {
        if (sub_args.len == 0) {
            try writeStderr(io, "rhc pkg describe: missing package name\n");
            try writeStderr(io, "Usage: rhc pkg describe <name>\n");
            std.process.exit(1);
        }
        try cmdPkgDescribe(alloc, io, &s, sub_args[0]);
        return;
    }

    if (std.mem.eql(u8, subcommand, "install")) {
        if (sub_args.len == 0) {
            try writeStderr(io, "rhc pkg install: missing path to .rhc-pkg file\n");
            try writeStderr(io, "Usage: rhc pkg install <path-to-.rhc-pkg>\n");
            std.process.exit(1);
        }
        cmdPkgInstall(alloc, io, &s, sub_args[0]) catch |err| {
            var ebuf: [512]u8 = undefined;
            var efw: File.Writer = .init(.stderr(), io, &ebuf);
            const e = &efw.interface;
            switch (err) {
                error.DuplicatePackage => try e.print("rhc pkg install: package already registered\n", .{}),
                else => try e.print("rhc pkg install: {}\n", .{err}),
            }
            try e.flush();
            std.process.exit(1);
        };
        return;
    }

    if (std.mem.eql(u8, subcommand, "unregister")) {
        if (sub_args.len == 0) {
            try writeStderr(io, "rhc pkg unregister: missing package id\n");
            try writeStderr(io, "Usage: rhc pkg unregister <name>-<version>\n");
            std.process.exit(1);
        }
        cmdPkgUnregister(alloc, io, &s, sub_args[0]) catch |err| {
            var ebuf: [512]u8 = undefined;
            var efw: File.Writer = .init(.stderr(), io, &ebuf);
            const e = &efw.interface;
            switch (err) {
                error.PackageNotFound => try e.print("rhc pkg unregister: package not found: {s}\n", .{sub_args[0]}),
                else => try e.print("rhc pkg unregister: {}\n", .{err}),
            }
            try e.flush();
            std.process.exit(1);
        };
        return;
    }

    if (std.mem.eql(u8, subcommand, "check")) {
        cmdPkgCheck(alloc, io, &s) catch |err| {
            switch (err) {
                error.CheckFailed => std.process.exit(1),
                else => return err,
            }
        };
        return;
    }

    var ebuf: [512]u8 = undefined;
    var efw: File.Writer = .init(.stderr(), io, &ebuf);
    const e = &efw.interface;
    try e.print("rhc pkg: unknown subcommand '{s}'\n", .{subcommand});
    try e.flush();
    try writePkgUsage(io);
    std.process.exit(1);
}

fn writePkgUsage(io: Io) !void {
    var buf: [1024]u8 = undefined;
    var fw: File.Writer = .init(.stderr(), io, &buf);
    const out = &fw.interface;
    try out.writeAll(
        \\Usage: rhc pkg <subcommand> [args]
        \\
        \\Subcommands:
        \\  list                          List all installed packages
        \\  describe <name>               Show descriptor for installed package(s)
        \\  install <path-to-.rhc-pkg>    Install a package from a descriptor file
        \\  unregister <name>-<version>   Remove a package from the registry
        \\  check                         Verify all registered .rhi files are present
        \\
    );
    try out.flush();
}

fn writeStderr(io: Io, msg: []const u8) !void {
    var buf: [512]u8 = undefined;
    var fw: File.Writer = .init(.stderr(), io, &buf);
    const out = &fw.interface;
    try out.writeAll(msg);
    try out.flush();
}
```

- [ ] **Step 2: Wire into `src/main.zig`**

Find the `// Unknown command.` block (around line 235) and insert before it:

```zig
    if (std.mem.eql(u8, command, "pkg")) {
        const cmd_args = user_args[1..];
        const pkg_cmd = @import("packages/pkg_cmd.zig");
        try pkg_cmd.cmdPkg(allocator, io, cmd_args);
        return;
    }
```

- [ ] **Step 3: Update `printUsage` in `src/main.zig`**

Find the line `\\  rhc repl [--server]   Interactive REPL` and add after `\\  rhc --version`:

```zig
    \\  rhc pkg <subcommand>           Manage the package store
    \\                         Subcommands: list, describe, install, unregister, check
    \\                         Run 'rhc pkg' for subcommand help
```

The full `printUsage` block after editing should look like:

```zig
    try stdout.writeAll(
        \\rhc — Rusholme Haskell Compiler
        \\
        \\Usage:
        \\  rhc parse <file.hs>    Parse a Haskell file and pretty-print the AST
        \\  rhc check <file.hs>    Parse, rename, and typecheck; print inferred types
        \\  rhc core <file.hs>     Parse, typecheck, and desugar; print Core IR
        \\  rhc grin <file.hs>     Full pipeline; print GRIN IR
        \\  rhc ll <file.hs>       Full pipeline; emit LLVM IR
        \\  rhc build [--backend <kind>] [-o <out>] <file.hs>
        \\                         Full pipeline; compile to an executable
        \\                         Backends: native (default), jit, wasm, c
        \\  rhc repl [--server]    Interactive REPL (read-eval-print loop)
        \\                         Use --server for JSON-RPC protocol mode
        \\  rhc pkg <subcommand>   Manage the package store
        \\                         Subcommands: list, describe, install, unregister, check
        \\                         Run 'rhc pkg' for subcommand help
        \\  rhc --help             Show this help message
        \\  rhc --version          Show version information
        \\
    );
```

- [ ] **Step 4: Build to confirm it compiles**

```bash
zig build 2>&1 | head -20
```

Expected: no errors.

- [ ] **Step 5: Run all tests**

```bash
zig build test --summary all 2>&1 | tail -5
```

Expected: all previously passing tests still pass.

- [ ] **Step 6: Commit**

```bash
git add src/packages/pkg_cmd.zig src/main.zig
git commit -m "#651: Add cmdPkg dispatcher, wire into main.zig, update printUsage"
```

---

## Task 9: Expose in `root.zig`, create `tests/pkg_cmd_test.zig`, register in `build.zig`, full suite

**Files:**
- Modify: `src/root.zig`
- Create: `tests/pkg_cmd_test.zig`
- Modify: `build.zig`

- [ ] **Step 1: Expose `pkg_cmd` in `src/root.zig`**

Find the `pub const packages = struct {` block and add one line:

```zig
pub const packages = struct {
    pub const descriptor = @import("packages/descriptor.zig");
    pub const store = @import("packages/store.zig");
    pub const pkg_cmd = @import("packages/pkg_cmd.zig");
```

Also verify that `testing.refAllDecls(packages)` in the test block at the bottom of `root.zig` will now pull in `pkg_cmd` tests — no change needed since `refAllDecls` recurses.

- [ ] **Step 2: Create `tests/pkg_cmd_test.zig`**

```zig
//! Integration tests for `rhc pkg` subcommands.
//!
//! These tests exercise the public pkg_cmd API end-to-end using a real
//! tmpDir-backed package store. They mirror the unit tests in pkg_cmd.zig
//! but use the rusholme module import path and are registered as a
//! separate test suite in build.zig.
//!
//! Issue: #651

const std = @import("std");
const rusholme = @import("rusholme");
const pkg_cmd = rusholme.packages.pkg_cmd;
const store_mod = rusholme.packages.store;
const descriptor = rusholme.packages.descriptor;

fn makeTestStore(alloc: std.mem.Allocator, tmp: *std.testing.TmpDir) !store_mod.Store {
    const path_z = try std.Io.Dir.realPathFileAlloc(tmp.dir, std.testing.io, ".", alloc);
    defer alloc.free(path_z);
    const path = try alloc.dupe(u8, path_z);
    defer alloc.free(path);
    return store_mod.init(alloc, std.testing.io, path);
}

fn registerPkg(
    alloc: std.mem.Allocator,
    s: *store_mod.Store,
    name: []const u8,
    version: []const u8,
) !void {
    const content = try std.fmt.allocPrint(
        alloc,
        "name = \"{s}\"\nversion = \"{s}\"\n",
        .{ name, version },
    );
    defer alloc.free(content);
    const desc = try descriptor.parse(alloc, content);
    defer desc.deinit(alloc);
    const key = try store_mod.computeKey(alloc, name, version, content);
    defer alloc.free(key);
    try s.register(std.testing.io, key, content, desc);
}

test "rhc pkg list: empty store produces no output" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();
    try pkg_cmd.cmdPkgList(std.testing.allocator, std.testing.io, &s);
}

test "rhc pkg list: lists all registered packages" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();
    try registerPkg(std.testing.allocator, &s, "pkg-x", "1.0.0");
    try registerPkg(std.testing.allocator, &s, "pkg-y", "2.0.0");
    try pkg_cmd.cmdPkgList(std.testing.allocator, std.testing.io, &s);
    const entries = try s.list(std.testing.io);
    defer { for (entries) |e| e.deinit(std.testing.allocator); std.testing.allocator.free(entries); }
    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

test "rhc pkg describe: known package runs without error" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();
    try registerPkg(std.testing.allocator, &s, "described", "3.0.0");
    try pkg_cmd.cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "described");
}

test "rhc pkg describe: unknown name is silent" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();
    try pkg_cmd.cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "nobody");
}

test "rhc pkg unregister: removes registered package" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();
    try registerPkg(std.testing.allocator, &s, "remove-me", "1.0.0");
    try pkg_cmd.cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "remove-me-1.0.0");
    const entries = try s.list(std.testing.io);
    defer { for (entries) |e| e.deinit(std.testing.allocator); std.testing.allocator.free(entries); }
    try std.testing.expectEqual(@as(usize, 0), entries.len);
}

test "rhc pkg unregister: returns PackageNotFound for unknown pkg" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();
    try std.testing.expectError(
        error.PackageNotFound,
        pkg_cmd.cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "nobody-0.0.0"),
    );
}

test "rhc pkg check: empty store passes" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();
    try pkg_cmd.cmdPkgCheck(std.testing.allocator, std.testing.io, &s);
}

test "rhc pkg check: fails when rhi is missing" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    const content = "name = \"needs-rhi\"\nversion = \"1.0.0\"\nexposed-modules = [\"Needs.Rhi\"]\ndepends = []\n";
    const desc = try descriptor.parse(std.testing.allocator, content);
    defer desc.deinit(std.testing.allocator);
    const key = try store_mod.computeKey(std.testing.allocator, desc.name, desc.version, content);
    defer std.testing.allocator.free(key);
    try s.register(std.testing.io, key, content, desc);

    try std.testing.expectError(error.CheckFailed, pkg_cmd.cmdPkgCheck(std.testing.allocator, std.testing.io, &s));
}
```

- [ ] **Step 3: Register `pkg-cmd-tests` in `build.zig`**

Find the `const diag_tests = b.addTest(...)` block (around line 550) and insert after it, before `const test_step = ...`:

```zig
    const pkg_cmd_test_module = b.createModule(.{
        .root_source_file = b.path("tests/pkg_cmd_test.zig"),
        .target = target,
        .imports = &.{.{ .name = "rusholme", .module = mod }},
    });
    const pkg_cmd_tests = b.addTest(.{
        .name = "pkg-cmd-tests",
        .root_module = pkg_cmd_test_module,
    });
    const run_pkg_cmd_tests = b.addRunArtifact(pkg_cmd_tests);
```

Then add to the `test_step` dependencies block:

```zig
    test_step.dependOn(&run_pkg_cmd_tests.step);
```

- [ ] **Step 4: Run the full test suite**

```bash
zig build test --summary all 2>&1 | tail -5
```

Expected:
```
Build Summary: N/N steps succeeded; M/M tests passed
```

where M > previous test count.

- [ ] **Step 5: Commit**

```bash
git add src/root.zig tests/pkg_cmd_test.zig build.zig
git commit -m "#651: Add pkg-cmd-tests suite; expose pkg_cmd in root.zig"
```

---

## Task 10: Open PR, update ROADMAP

- [ ] **Step 1: Push the branch**

```bash
git push origin llm-agent/issue-651
```

- [ ] **Step 2: Open PR**

```bash
cat > /tmp/pr-651.md << 'EOF'
Closes #651

## Summary
Implements the `rhc pkg` tool as a subcommand of `rhc`, mirroring `ghc-pkg`.

## Deliverables
- [x] `rhc pkg list` — prints `<name>-<version>` for each installed package
- [x] `rhc pkg describe <name>` — prints metadata for all versions of a package
- [x] `rhc pkg install <path>` — reads a `.rhc-pkg` file and registers it in the store
- [x] `rhc pkg unregister <name>-<version>` — removes a package's registry entry
- [x] `rhc pkg check` — verifies all exposed modules have `.rhi` files present
- [x] Integration tests in `tests/pkg_cmd_test.zig` registered as `pkg-cmd-tests`
- [x] `store.unregister` + `PackageNotFound` error added to `store.zig`
- [x] `computeKey` made public for use by install command
- [x] `printUsage` updated with `rhc pkg` entry

## Testing
```
zig build test --summary all
```
All tests pass. Run `zig build && zig-out/bin/rhc pkg` to see the subcommand help.
EOF

gh pr create \
  --title "#651: Implement rhc-pkg tool (list/describe/install/unregister/check)" \
  --body-file /tmp/pr-651.md \
  --base main \
  --head llm-agent/issue-651 \
  --reviewer adinapoli
```

- [ ] **Step 3: Update ROADMAP on `project-planning` branch**

```bash
git checkout project-planning
git rebase main
# In ROADMAP.md, change #651 from :white_circle: to :yellow_circle:
git add ROADMAP.md
git commit -m "#651: Update roadmap status to in-review"
git push origin project-planning
```
