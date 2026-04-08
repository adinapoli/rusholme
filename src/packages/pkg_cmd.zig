//! Subcommand implementations for `rhc pkg`.
//!
//! Each public function accepts a `*store.Store` so callers (including tests)
//! can supply their own store instead of relying on the default path.
//! Each function that produces output accepts an `out: *std.Io.Writer` so
//! callers can redirect or discard output (tests pass `Allocating` writers;
//! the `cmdPkg` dispatcher passes a stdout-backed `File.Writer`).
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
const clap = @import("clap");
const store = @import("store.zig");
const descriptor = @import("descriptor.zig");

// ── Error types ───────────────────────────────────────────────────────────────

/// Returned by `cmdPkgCheck` when one or more `.rhi` files are absent.
pub const CheckError = error{CheckFailed};

// ── cmdPkgList ────────────────────────────────────────────────────────────────

/// Print one `<name>-<version>` line per installed package.
/// Output is written to `out`; callers are responsible for choosing the
/// destination (stdout in production, an `Allocating` writer in tests).
pub fn cmdPkgList(alloc: std.mem.Allocator, io: Io, s: *store.Store, out: *std.Io.Writer) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

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
pub fn cmdPkgDescribe(alloc: std.mem.Allocator, io: Io, s: *store.Store, name: []const u8, out: *std.Io.Writer) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

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
/// Prints `<name>-<version> installed` to `out` on success.
/// Returns `store.Error.DuplicatePackage` if the package is already registered.
pub fn cmdPkgInstall(alloc: std.mem.Allocator, io: Io, s: *store.Store, pkg_path: []const u8, out: *std.Io.Writer) !void {
    const content = try std.Io.Dir.readFileAlloc(.cwd(), io, pkg_path, alloc, .limited(1024 * 64));
    defer alloc.free(content);

    const desc = try descriptor.parse(alloc, content);
    defer desc.deinit(alloc);

    const key = try store.computeKey(alloc, desc.name, desc.version, content);
    defer alloc.free(key);

    try s.register(io, key, content, desc);

    try out.print("{s}-{s} installed\n", .{ desc.name, desc.version });
    try out.flush();
}

// ── cmdPkgUnregister ──────────────────────────────────────────────────────────

/// Unregister a package identified by `name_version` (e.g. `"base-0.1.0"`).
///
/// The argument must match `<name>-<version>` for some registered package
/// (i.e. `entry.name ++ "-" ++ entry.version == name_version`).
/// Prints `<name_version> unregistered` to `out` on success.
/// Returns `store.Error.PackageNotFound` if no matching package exists.
pub fn cmdPkgUnregister(alloc: std.mem.Allocator, io: Io, s: *store.Store, name_version: []const u8, out: *std.Io.Writer) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

    for (entries) |entry| {
        const full = try std.fmt.allocPrint(alloc, "{s}-{s}", .{ entry.name, entry.version });
        defer alloc.free(full);

        if (std.mem.eql(u8, full, name_version)) {
            try s.unregister(io, entry.key);

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
/// Prints one line per package to `out`:
///   `  <name>-<version>: OK`
///   `  <name>-<version>: MISSING <Module/Path>.rhi`
///
/// Returns `CheckError.CheckFailed` if any `.rhi` file is absent.
pub fn cmdPkgCheck(alloc: std.mem.Allocator, io: Io, s: *store.Store, out: *std.Io.Writer) !void {
    const entries = try s.list(io);
    defer {
        for (entries) |e| e.deinit(alloc);
        alloc.free(entries);
    }

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

/// All subcommands recognised by `rhc pkg`.
const PkgSubCommand = enum {
    list,
    describe,
    install,
    unregister,
    check,
};

/// Custom parser set that maps the `<command>` positional type to `PkgSubCommand`.
const pkg_parsers = .{
    .command = clap.parsers.enumeration(PkgSubCommand),
};

/// Top-level dispatcher for `rhc pkg <subcommand>`.
///
/// `it` is a SliceIterator positioned at the first argument after "pkg"
/// (i.e. the pkg subcommand name and its arguments).
pub fn cmdPkg(alloc: std.mem.Allocator, io: Io, it: *clap.args.SliceIterator) !void {
    const pkg_params = comptime clap.parseParamsComptime(
        \\-h, --help  Display this help and exit.
        \\<command>
        \\
    );

    var pkg_diag = clap.Diagnostic{};
    var pkg = clap.parseEx(clap.Help, &pkg_params, pkg_parsers, it, .{
        .allocator = alloc,
        .diagnostic = &pkg_diag,
        .terminating_positional = 0,
    }) catch |err| {
        try pkg_diag.reportToFile(io, .stderr(), err);
        std.process.exit(1);
    };
    defer pkg.deinit();

    if (pkg.args.help != 0) {
        var buf: [4096]u8 = undefined;
        var fw: File.Writer = .init(.stdout(), io, &buf);
        try clap.help(&fw.interface, clap.Help, &pkg_params, .{});
        try fw.interface.flush();
        return;
    }

    const subcommand: PkgSubCommand = pkg.positionals[0] orelse {
        var buf: [4096]u8 = undefined;
        var fw: File.Writer = .init(.stderr(), io, &buf);
        try clap.usage(&fw.interface, clap.Help, &pkg_params);
        try fw.interface.flush();
        std.process.exit(1);
    };

    var s = store.init(alloc, io, null) catch |err| {
        var buf: [512]u8 = undefined;
        var fw: File.Writer = .init(.stderr(), io, &buf);
        try fw.interface.print("rhc pkg: cannot open store: {}\n", .{err});
        try fw.interface.flush();
        std.process.exit(1);
    };
    defer s.deinit();

    // All subcommands that produce output share this single stdout writer.
    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    const out = &stdout_fw.interface;

    switch (subcommand) {
        .list => {
            try cmdPkgList(alloc, io, &s, out);
        },

        // ── describe <name> ───────────────────────────────────────────────────
        .describe => {
            const desc_params = comptime clap.parseParamsComptime(
                \\-h, --help  Display this help and exit.
                \\<str>
                \\
            );
            var desc_diag = clap.Diagnostic{};
            var desc_res = clap.parseEx(clap.Help, &desc_params, clap.parsers.default, it, .{
                .allocator = alloc,
                .diagnostic = &desc_diag,
            }) catch |err| {
                try desc_diag.reportToFile(io, .stderr(), err);
                std.process.exit(1);
            };
            defer desc_res.deinit();

            if (desc_res.args.help != 0) {
                var buf: [4096]u8 = undefined;
                var fw: File.Writer = .init(.stdout(), io, &buf);
                try clap.help(&fw.interface, clap.Help, &desc_params, .{});
                try fw.interface.flush();
                return;
            }

            const name = desc_res.positionals[0] orelse {
                var buf: [512]u8 = undefined;
                var fw: File.Writer = .init(.stderr(), io, &buf);
                try fw.interface.writeAll("rhc pkg describe: missing package name\n");
                try fw.interface.flush();
                std.process.exit(1);
            };
            try cmdPkgDescribe(alloc, io, &s, name, out);
        },

        // ── install <path> ────────────────────────────────────────────────────
        .install => {
            const inst_params = comptime clap.parseParamsComptime(
                \\-h, --help  Display this help and exit.
                \\<str>
                \\
            );
            var inst_diag = clap.Diagnostic{};
            var inst_res = clap.parseEx(clap.Help, &inst_params, clap.parsers.default, it, .{
                .allocator = alloc,
                .diagnostic = &inst_diag,
            }) catch |err| {
                try inst_diag.reportToFile(io, .stderr(), err);
                std.process.exit(1);
            };
            defer inst_res.deinit();

            if (inst_res.args.help != 0) {
                var buf: [4096]u8 = undefined;
                var fw: File.Writer = .init(.stdout(), io, &buf);
                try clap.help(&fw.interface, clap.Help, &inst_params, .{});
                try fw.interface.flush();
                return;
            }

            const path = inst_res.positionals[0] orelse {
                var buf: [512]u8 = undefined;
                var fw: File.Writer = .init(.stderr(), io, &buf);
                try fw.interface.writeAll("rhc pkg install: missing path to .rhc-pkg file\n");
                try fw.interface.flush();
                std.process.exit(1);
            };
            cmdPkgInstall(alloc, io, &s, path, out) catch |err| {
                var buf: [512]u8 = undefined;
                var fw: File.Writer = .init(.stderr(), io, &buf);
                switch (err) {
                    error.DuplicatePackage => try fw.interface.writeAll("rhc pkg install: package already registered\n"),
                    else => try fw.interface.print("rhc pkg install: {}\n", .{err}),
                }
                try fw.interface.flush();
                std.process.exit(1);
            };
        },

        // ── unregister <name>-<version> ───────────────────────────────────────
        .unregister => {
            const unreg_params = comptime clap.parseParamsComptime(
                \\-h, --help  Display this help and exit.
                \\<str>
                \\
            );
            var unreg_diag = clap.Diagnostic{};
            var unreg_res = clap.parseEx(clap.Help, &unreg_params, clap.parsers.default, it, .{
                .allocator = alloc,
                .diagnostic = &unreg_diag,
            }) catch |err| {
                try unreg_diag.reportToFile(io, .stderr(), err);
                std.process.exit(1);
            };
            defer unreg_res.deinit();

            if (unreg_res.args.help != 0) {
                var buf: [4096]u8 = undefined;
                var fw: File.Writer = .init(.stdout(), io, &buf);
                try clap.help(&fw.interface, clap.Help, &unreg_params, .{});
                try fw.interface.flush();
                return;
            }

            const name_ver = unreg_res.positionals[0] orelse {
                var buf: [512]u8 = undefined;
                var fw: File.Writer = .init(.stderr(), io, &buf);
                try fw.interface.writeAll("rhc pkg unregister: missing package id\n");
                try fw.interface.flush();
                std.process.exit(1);
            };
            cmdPkgUnregister(alloc, io, &s, name_ver, out) catch |err| {
                var buf: [512]u8 = undefined;
                var fw: File.Writer = .init(.stderr(), io, &buf);
                switch (err) {
                    error.PackageNotFound => try fw.interface.print(
                        "rhc pkg unregister: package not found: {s}\n",
                        .{name_ver},
                    ),
                    else => try fw.interface.print("rhc pkg unregister: {}\n", .{err}),
                }
                try fw.interface.flush();
                std.process.exit(1);
            };
        },

        // ── check ─────────────────────────────────────────────────────────────
        .check => {
            cmdPkgCheck(alloc, io, &s, out) catch |err| {
                switch (err) {
                    error.CheckFailed => std.process.exit(1),
                    else => return err,
                }
            };
        },
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

fn makeTestStore(alloc: std.mem.Allocator, tmp: *std.testing.TmpDir) !store.Store {
    const path = try std.Io.Dir.realPathFileAlloc(tmp.dir, std.testing.io, ".", alloc);
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

/// Create a heap-backed writer whose output is discarded on `deinit`.
/// Use this in tests to call command functions without writing to stdout.
fn makeDiscardWriter() std.Io.Writer.Allocating {
    return .init(std.testing.allocator);
}

test "cmdPkgList: lists installed packages without error" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "alpha", "1.0.0");
    try registerTestPkg(std.testing.allocator, &s, "beta", "2.3.0");

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgList(std.testing.allocator, std.testing.io, &s, &discard.writer);

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

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgList(std.testing.allocator, std.testing.io, &s, &discard.writer);
}

test "cmdPkgDescribe: known package runs without error" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "mypkg", "1.0.0");

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "mypkg", &discard.writer);
}

test "cmdPkgDescribe: unknown name is silent" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgDescribe(std.testing.allocator, std.testing.io, &s, "ghost", &discard.writer);
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

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgInstall(std.testing.allocator, std.testing.io, &s, pkg_file_path, &discard.writer);

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

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "mypkg-1.0.0", &discard.writer);

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

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try std.testing.expectError(
        error.PackageNotFound,
        cmdPkgUnregister(std.testing.allocator, std.testing.io, &s, "ghost-9.9.9", &discard.writer),
    );
}

test "cmdPkgCheck: empty store passes" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s, &discard.writer);
}

test "cmdPkgCheck: package with no exposed modules passes" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    var s = try makeTestStore(std.testing.allocator, &tmp);
    defer s.deinit();

    try registerTestPkg(std.testing.allocator, &s, "noop", "1.0.0");

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s, &discard.writer);
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
    var discard = makeDiscardWriter();
    defer discard.deinit();
    try std.testing.expectError(
        CheckError.CheckFailed,
        cmdPkgCheck(std.testing.allocator, std.testing.io, &s, &discard.writer),
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

    var discard = makeDiscardWriter();
    defer discard.deinit();
    try cmdPkgCheck(std.testing.allocator, std.testing.io, &s, &discard.writer);
}
