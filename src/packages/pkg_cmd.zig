//! Subcommand implementations for `rhc pkg`.
//!
//! Each public function accepts a `*store.Store` so callers (including tests)
//! can supply their own store instead of relying on the default path.
//!
//! ## Subcommands
//!
//! - `cmdPkgList`       — print one `<name>-<version>` line per installed package
//! - `cmdPkgDescribe`   — print metadata for all packages matching `name`
//! - `cmdPkgInstall`    — register a package from a `.rhc-pkg` descriptor file
//! - `cmdPkgUnregister` — remove a package from the registry
//! - `cmdPkgCheck`      — verify every exposed module has a `.rhi` file
//! - `cmdPkg`           — top-level dispatcher called from `main.zig`
//!
//! Issue: #651

const std = @import("std");
const Io = std.Io;
const File = Io.File;
const store = @import("store.zig");
const descriptor = @import("descriptor.zig");

// ── Error types ───────────────────────────────────────────────────────────────

/// Returned by `cmdPkgCheck` when one or more `.rhi` files are absent.
pub const CheckError = error{CheckFailed};

// ── cmdPkgList ────────────────────────────────────────────────────────────────

/// Print one `<name>-<version>` line per installed package to stdout.
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

// ── cmdPkgDescribe ────────────────────────────────────────────────────────────

/// Print metadata for all installed packages whose name equals `name`.
/// Prints nothing and exits cleanly if no packages match.
///
/// Output format (one block per matching package):
///
/// ```
/// name: <name>
/// version: <version>
/// id: <key>
/// install-path: <path>
/// exposed-modules: <mod1> <mod2> ...
/// depends: <dep1> <dep2> ...
/// ```
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

// ── cmdPkgInstall ─────────────────────────────────────────────────────────────

/// Install a package from a `.rhc-pkg` descriptor file at `pkg_path`.
/// Prints `<name>-<version> installed` on success.
/// Returns `store.Error.DuplicatePackage` if the package is already registered.
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

// ── cmdPkgUnregister ──────────────────────────────────────────────────────────

/// Unregister a package identified by `name_version` (e.g. `"base-0.1.0"`).
///
/// The argument must match `<name>-<version>` for some registered package
/// (i.e. `entry.name ++ "-" ++ entry.version == name_version`).
/// Prints `<name_version> unregistered` on success.
/// Returns `store.Error.PackageNotFound` if no matching package exists.
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

// ── cmdPkgCheck ───────────────────────────────────────────────────────────────

/// Verify that every exposed module in every installed package has a
/// corresponding `.rhi` file at `<install_path>/<Module/Path>.rhi`.
///
/// Module name to path conversion: dots become slashes.
/// Example: `"Data.Maybe"` → `"Data/Maybe.rhi"`.
///
/// Prints one line per package:
///   `  <name>-<version>: OK`
///   `  <name>-<version>: MISSING <Module/Path>.rhi`
///
/// Returns `CheckError.CheckFailed` if any `.rhi` file is absent.
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
            // Convert "Foo.Bar.Baz" → "Foo/Bar/Baz"
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

    if (any_missing) return CheckError.CheckFailed;
}

// ── cmdPkg ────────────────────────────────────────────────────────────────────

/// Top-level dispatcher for `rhc pkg <subcommand>`.
///
/// `args` is the slice of argv after `"pkg"` (i.e. `["list"]`,
/// `["describe", "base"]`, etc.).
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
        const e = &efw.interface;
        try e.print("rhc pkg: cannot open store: {}\n", .{err});
        try e.flush();
        std.process.exit(1);
    };
    defer s.deinit();

    if (std.mem.eql(u8, subcommand, "list")) {
        try cmdPkgList(alloc, io, &s);
        return;
    }

    if (std.mem.eql(u8, subcommand, "describe")) {
        if (sub_args.len == 0) {
            try writePkgStderr(io, "rhc pkg describe: missing package name\n");
            try writePkgStderr(io, "Usage: rhc pkg describe <name>\n");
            std.process.exit(1);
        }
        try cmdPkgDescribe(alloc, io, &s, sub_args[0]);
        return;
    }

    if (std.mem.eql(u8, subcommand, "install")) {
        if (sub_args.len == 0) {
            try writePkgStderr(io, "rhc pkg install: missing path to .rhc-pkg file\n");
            try writePkgStderr(io, "Usage: rhc pkg install <path-to-.rhc-pkg>\n");
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
            try writePkgStderr(io, "rhc pkg unregister: missing package id\n");
            try writePkgStderr(io, "Usage: rhc pkg unregister <name>-<version>\n");
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
                CheckError.CheckFailed => std.process.exit(1),
                else => return err,
            }
        };
        return;
    }

    {
        var ebuf: [512]u8 = undefined;
        var efw: File.Writer = .init(.stderr(), io, &ebuf);
        const e = &efw.interface;
        try e.print("rhc pkg: unknown subcommand '{s}'\n", .{subcommand});
        try e.flush();
    }
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

fn writePkgStderr(io: Io, msg: []const u8) !void {
    var buf: [512]u8 = undefined;
    var fw: File.Writer = .init(.stderr(), io, &buf);
    const out = &fw.interface;
    try out.writeAll(msg);
    try out.flush();
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

test "cmdPkgList: lists installed packages without error" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "alpha", "1.0.0");
    try registerTestPkg(std.testing.allocator, &s, "beta", "2.3.0");

    try cmdPkgList(std.testing.allocator, std.testing.io, &s);

    // Verify both packages remain registered (listing is non-destructive).
    const entries = try s.list(std.testing.io);
    defer {
        for (entries) |e| e.deinit(std.testing.allocator);
        std.testing.allocator.free(entries);
    }
    try std.testing.expectEqual(@as(usize, 2), entries.len);
}

test "cmdPkgList: succeeds on empty store" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try cmdPkgList(std.testing.allocator, std.testing.io, &s);
}

test "cmdPkgDescribe: known package runs without error" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "mypkg", "1.0.0");
    try cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "mypkg");
}

test "cmdPkgDescribe: unknown name is silent" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "ghost");
}

test "cmdPkgInstall: registers package from descriptor file" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    // Write a .rhc-pkg file into the tmp dir.
    const desc_content = "name = \"install-test\"\nversion = \"0.5.0\"\nexposed-modules = [\"Install.Test\"]\ndepends = []\n";
    const path_z = try std.Io.Dir.realPathFileAlloc(tmp.dir, std.testing.io, ".", std.testing.allocator);
    defer std.testing.allocator.free(path_z);
    const pkg_file_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/install-test.rhc-pkg", .{path_z});
    defer std.testing.allocator.free(pkg_file_path);

    const file = try std.Io.Dir.createFile(.cwd(), std.testing.io, pkg_file_path, .{});
    defer file.close(std.testing.io);
    try file.writeStreamingAll(std.testing.io, desc_content);

    try cmdPkgInstall(std.testing.allocator, std.testing.io, &s, pkg_file_path);

    const entry = try s.lookup(std.testing.io, "install-test", "0.5.0");
    try std.testing.expect(entry != null);
    if (entry) |e| e.deinit(std.testing.allocator);
}

test "cmdPkgUnregister: removes the package" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "mypkg", "1.0.0");
    try cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "mypkg-1.0.0");

    const entries = try s.list(std.testing.io);
    defer {
        for (entries) |e| e.deinit(std.testing.allocator);
        std.testing.allocator.free(entries);
    }
    try std.testing.expectEqual(@as(usize, 0), entries.len);
}

test "cmdPkgUnregister: returns PackageNotFound for unknown name_version" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try std.testing.expectError(
        error.PackageNotFound,
        cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "ghost-9.9.9"),
    );
}

test "cmdPkgCheck: empty store passes" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s);
}

test "cmdPkgCheck: package with no exposed modules passes" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "noop", "1.0.0");
    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s);
}

test "cmdPkgCheck: returns CheckFailed when rhi is missing" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    const content = "name = \"has-module\"\nversion = \"1.0.0\"\nexposed-modules = [\"Has.Module\"]\ndepends = []\n";
    const desc = try descriptor.parse(std.testing.allocator, content);
    defer desc.deinit(std.testing.allocator);
    const key = try store.computeKey(std.testing.allocator, desc.name, desc.version, content);
    defer std.testing.allocator.free(key);
    try s.register(std.testing.io, key, content, desc);

    // The .rhi file does NOT exist — check must return CheckFailed.
    try std.testing.expectError(
        CheckError.CheckFailed,
        cmdPkgCheck(std.testing.allocator, std.testing.io, &s),
    );
}

test "cmdPkgCheck: succeeds when rhi exists" {
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

    // Create subdirectory With/ and file With/Rhi.rhi inside install_path.
    const subdir_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/With", .{entry.install_path});
    defer std.testing.allocator.free(subdir_path);
    try std.Io.Dir.cwd().createDirPath(std.testing.io, subdir_path);

    const rhi_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/With/Rhi.rhi", .{entry.install_path});
    defer std.testing.allocator.free(rhi_path);
    const rhi_file = try std.Io.Dir.createFile(.cwd(), std.testing.io, rhi_path, .{});
    rhi_file.close(std.testing.io);

    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s);
}
