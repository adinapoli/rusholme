//! Package store for Rusholme package management.
//!
//! The store lives at `~/.rhc/store/<arch>-<os>-<version>/` with
//! `package.conf.d/` containing JSON entries for each installed package.
//!
//! ## Reference
//!
//! Design: `docs/plans/2026-03-31-package-store-design.md`
//! Issue: #650

const std = @import("std");
const descriptor = @import("descriptor.zig");
const builtin = @import("builtin");
const build_options = @import("build_options");

// ── Public types ─────────────────────────────────────────────────────────────

/// A package store manages installed packages and their metadata.
pub const Store = struct {
    allocator: std.mem.Allocator,
    root_path: []const u8,
    conf_dir_path: []const u8,

    pub fn deinit(self: *Store) void {
        self.allocator.free(self.root_path);
        self.allocator.free(self.conf_dir_path);
    }

    /// Register a package in the store.
    ///
    /// Creates:
    /// 1. .conf file in package.conf.d/
    /// 2. Empty package directory for artifacts
    ///
    /// Returns DuplicatePackage if the package key already exists.
    ///
    /// The operation is atomic in the sense that any partial state created
    /// before a failure is cleaned up via errdefer.
    pub fn register(
        self: *Store,
        io: std.Io,
        pkg_key: []const u8,
        descriptor_content: []const u8,
        desc: descriptor.PackageDescriptor,
    ) Error!void {
        const conf_path = try computeConfPath(self, pkg_key);
        defer self.allocator.free(conf_path);

        // Check if conf file already exists
        const file_exists = blk: {
            const f = std.Io.Dir.openFile(.cwd(), io, conf_path, .{}) catch |err| {
                if (err == error.FileNotFound) break :blk false;
                return err;
            };
            f.close(io);
            break :blk true;
        };
        if (file_exists) return error.DuplicatePackage;

        // Create package directory; remove it on error to avoid partial state.
        const pkg_path = try computePkgPath(self, desc.name, desc.version);
        defer self.allocator.free(pkg_path);
        try std.Io.Dir.cwd().createDirPath(io, pkg_path);
        errdefer std.Io.Dir.deleteDirAbsolute(io, pkg_path) catch {};

        // Resolve install_path to its canonical absolute form.
        // realPathFileAbsoluteAlloc returns [:0]u8; free it as-is so the allocator
        // accounts for the null terminator correctly.
        const install_path_z = try std.Io.Dir.realPathFileAbsoluteAlloc(io, pkg_path, self.allocator);
        defer self.allocator.free(install_path_z);
        const install_path: []const u8 = install_path_z;

        // Compute hash for the conf entry
        var hasher = std.crypto.hash.sha2.Sha256.init(.{});
        hasher.update(descriptor_content);
        var digest: [32]u8 = undefined;
        hasher.final(&digest);
        const digest_hex = std.fmt.bytesToHex(digest, .lower);

        // Serialise the conf entry to JSON using std.json.Stringify so that
        // all string values are properly escaped.
        const ConfJson = struct {
            key: []const u8,
            name: []const u8,
            version: []const u8,
            hash: []const u8,
            exposed_modules: []const []const u8,
            depends: []const []const u8,
            install_path: []const u8,
        };
        const conf_entry: ConfJson = .{
            .key = pkg_key,
            .name = desc.name,
            .version = desc.version,
            .hash = &digest_hex,
            .exposed_modules = desc.exposed_modules,
            .depends = desc.depends,
            .install_path = install_path,
        };

        var out: std.Io.Writer.Allocating = .init(self.allocator);
        defer out.deinit();
        var jw: std.json.Stringify = .{
            .writer = &out.writer,
            .options = .{ .whitespace = .indent_2 },
        };
        try jw.write(conf_entry);

        const json_content = try out.toOwnedSlice();
        defer self.allocator.free(json_content);

        // Write .conf file; remove it on error so the store stays consistent.
        const conf_file = try std.Io.Dir.createFile(.cwd(), io, conf_path, .{});
        errdefer std.Io.Dir.deleteFile(.cwd(), io, conf_path) catch {};
        defer conf_file.close(io);
        try conf_file.writeStreamingAll(io, json_content);
    }

    /// Look up a package by name and version.
    ///
    /// Scans all .conf files and compares name/version fields directly to avoid
    /// false positives from packages whose names contain hyphens.
    pub fn lookup(self: *const Store, io: std.Io, name: []const u8, version: []const u8) Error!?Entry {
        var dir = std.Io.Dir.cwd().openDir(io, self.conf_dir_path, .{ .iterate = true }) catch |err| {
            return if (err == error.FileNotFound) null else err;
        };
        defer dir.close(io);

        var iter = dir.iterate();
        while (try iter.next(io)) |dir_entry| {
            if (dir_entry.kind != .file) continue;
            if (!std.mem.endsWith(u8, dir_entry.name, ".conf")) continue;

            const conf_path = try std.fmt.allocPrint(self.allocator, "{s}/{s}", .{ self.conf_dir_path, dir_entry.name });
            defer self.allocator.free(conf_path);

            const entry = try parseConfFile(self.allocator, io, conf_path);
            if (std.mem.eql(u8, entry.name, name) and std.mem.eql(u8, entry.version, version)) {
                return entry;
            }
            entry.deinit(self.allocator);
        }

        return null;
    }

    /// Look up a package by its full key (hash-name-version).
    pub fn lookupByKey(self: *const Store, io: std.Io, key: []const u8) Error!?Entry {
        const conf_path = try std.fmt.allocPrint(self.allocator, "{s}/{s}.conf", .{ self.conf_dir_path, key });
        defer self.allocator.free(conf_path);

        return parseConfFile(self.allocator, io, conf_path) catch |err| {
            return if (err == error.FileNotFound) null else err;
        };
    }

    /// List all packages in the store.
    pub fn list(self: *const Store, io: std.Io) Error![]const Entry {
        var entries: std.ArrayListUnmanaged(Entry) = .{};
        errdefer {
            for (entries.items) |e| e.deinit(self.allocator);
            entries.deinit(self.allocator);
        }

        var dir = std.Io.Dir.cwd().openDir(io, self.conf_dir_path, .{ .iterate = true }) catch |err| {
            if (err == error.FileNotFound) return entries.toOwnedSlice(self.allocator);
            return err;
        };
        defer dir.close(io);

        var iter = dir.iterate();
        while (try iter.next(io)) |entry| {
            if (entry.kind != .file) continue;
            if (!std.mem.endsWith(u8, entry.name, ".conf")) continue;

            const conf_path = try std.fmt.allocPrint(self.allocator, "{s}/{s}", .{ self.conf_dir_path, entry.name });
            defer self.allocator.free(conf_path);

            const parsed_entry = try parseConfFile(self.allocator, io, conf_path);
            errdefer parsed_entry.deinit(self.allocator);

            try entries.append(self.allocator, parsed_entry);
        }

        return entries.toOwnedSlice(self.allocator);
    }

    /// Remove a package's registry entry from `package.conf.d/`.
    ///
    /// Deletes the `.conf` file identified by `key` (the string returned by
    /// `computeKey`). Does NOT delete the compiled artifact directory —
    /// artifacts survive unregistration and must be cleaned up separately.
    ///
    /// Returns `error.PackageNotFound` if no `.conf` file for `key` exists.
    pub fn unregister(
        self: *Store,
        io: std.Io,
        key: []const u8,
    ) Error!void {
        const conf_path = try computeConfPath(self, key);
        defer self.allocator.free(conf_path);

        const exists = blk: {
            std.Io.Dir.access(.cwd(), io, conf_path, .{}) catch |err| {
                if (err == error.FileNotFound) break :blk false;
                return err;
            };
            break :blk true;
        };
        if (!exists) return error.PackageNotFound;

        try std.Io.Dir.deleteFile(.cwd(), io, conf_path);
    }
};

/// An entry in the package store, parsed from a .conf file.
pub const Entry = struct {
    key: []const u8,              // "{hash}-{name}-{version}"
    name: []const u8,
    version: []const u8,
    hash: []const u8,             // descriptor SHA256
    exposed_modules: []const []const u8,
    depends: []const []const u8,
    install_path: []const u8,

    pub fn deinit(entry: Entry, alloc: std.mem.Allocator) void {
        alloc.free(entry.key);
        alloc.free(entry.name);
        alloc.free(entry.version);
        alloc.free(entry.hash);
        for (entry.exposed_modules) |m| alloc.free(m);
        alloc.free(entry.exposed_modules);
        for (entry.depends) |d| alloc.free(d);
        alloc.free(entry.depends);
        alloc.free(entry.install_path);
    }
};

/// Store-specific errors.
pub const Error = error{
    /// Attempted to register a package that already exists.
    DuplicatePackage,
    /// A .conf file exists but is malformed.
    InvalidConf,
    /// The HOME environment variable is not set (required for defaultPath).
    HomeDirectoryUnset,
    /// The requested package was not found in the store.
    PackageNotFound,
} || std.Io.File.OpenError
  || std.Io.Dir.OpenError
  || std.Io.Dir.CreateDirPathError
  || std.Io.Dir.ReadFileAllocError
  || std.Io.Dir.RealPathFileAllocError
  || std.Io.File.Writer.Error
  || std.Io.Writer.Error
  || std.json.ParseError(std.json.Scanner);

// ── Public functions ─────────────────────────────────────────────────────────

/// Return the default store path: `~/.rhc/store/<arch>-<os>-<version>/`.
///
/// Path components:
/// - `arch`: from `builtin.cpu.arch` (e.g., "x86_64")
/// - `os`: from `builtin.os.tag` (e.g., "linux", "macos", "windows")
/// - `version`: the compiler version injected by the build system via `build_options`
///
/// Returns `error.HomeDirectoryUnset` if `HOME` is not in the environment.
/// The caller owns the returned string and must free it with `alloc.free`.
///
pub fn defaultPath(alloc: std.mem.Allocator) Error![]const u8 {
    // tracked in: https://github.com/adinapoli/rusholme/issues/676
    const VERSION = build_options.version;
    const arch = switch (builtin.cpu.arch) {
        .x86_64 => "x86_64",
        .aarch64 => "aarch64",
        .riscv64 => "riscv64",
        else => @tagName(builtin.cpu.arch),
    };
    const os_tag = switch (builtin.os.tag) {
        .linux => "linux",
        .macos => "macos",
        .windows => "windows",
        .wasi => "wasi",
        else => @tagName(builtin.os.tag),
    };
    const home_ptr = std.c.getenv("HOME") orelse return error.HomeDirectoryUnset;
    const home: []const u8 = std.mem.span(home_ptr);
    // tracked in: https://github.com/adinapoli/rusholme/issues/676
    return std.fmt.allocPrint(alloc, "{s}/.rhc/store/{s}-{s}-{s}/", .{
        home, arch, os_tag, VERSION,
    });
}

/// Initialize a package store.
///
/// If `root_path` is null, uses `defaultPath()`.
/// Creates the root directory and `package.conf.d/` if missing.
pub fn init(alloc: std.mem.Allocator, io: std.Io, root_path: ?[]const u8) Error!Store {
    const root = if (root_path) |p|
        try alloc.dupe(u8, p)
    else
        try defaultPath(alloc);

    errdefer alloc.free(root);

    // Create root directory and package.conf.d/ (createDirPath is idempotent)
    try std.Io.Dir.cwd().createDirPath(io, root);

    const conf_dir = try std.fmt.allocPrint(alloc, "{s}/package.conf.d", .{root});
    errdefer alloc.free(conf_dir);

    try std.Io.Dir.cwd().createDirPath(io, conf_dir);

    return Store{
        .allocator = alloc,
        .root_path = root,
        .conf_dir_path = conf_dir,
    };
}

/// Compute the package key from name, version, and descriptor content.
///
/// Format: {sha256_hex}-{name}-{version}
///
/// Caller owns the returned string (allocated with alloc).
pub fn computeKey(alloc: std.mem.Allocator, name: []const u8, version: []const u8, descriptor_content: []const u8) std.mem.Allocator.Error![]const u8 {
    var hasher = std.crypto.hash.sha2.Sha256.init(.{});
    hasher.update(descriptor_content);
    var digest: [32]u8 = undefined;
    hasher.final(&digest);
    const hex = std.fmt.bytesToHex(digest, .lower);

    return std.fmt.allocPrint(alloc, "{s}-{s}-{s}", .{ &hex, name, version });
}

/// Compute the full path to a .conf file for a given key.
fn computeConfPath(store: *const Store, key: []const u8) std.mem.Allocator.Error![]const u8 {
    return std.fmt.allocPrint(store.allocator, "{s}/{s}.conf", .{
        store.conf_dir_path, key,
    });
}

/// Compute the full path to a package directory.
fn computePkgPath(store: *const Store, name: []const u8, version: []const u8) std.mem.Allocator.Error![]const u8 {
    return std.fmt.allocPrint(store.allocator, "{s}/{s}-{s}", .{
        store.root_path, name, version,
    });
}

/// Parse a .conf file and return an Entry.
fn parseConfFile(alloc: std.mem.Allocator, io: std.Io, path: []const u8) Error!Entry {
    const content = try std.Io.Dir.readFileAlloc(.cwd(), io, path, alloc, .limited(1024 * 64));
    defer alloc.free(content);

    const Parsed = struct {
        key: []const u8,
        name: []const u8,
        version: []const u8,
        hash: []const u8,
        exposed_modules: []const []const u8,
        depends: []const []const u8,
        install_path: []const u8,
    };

    const parsed = try std.json.parseFromSlice(Parsed, alloc, content, .{
        .ignore_unknown_fields = true,
    });
    defer parsed.deinit();

    const p = parsed.value;

    // Deep-copy scalar fields
    const key = try alloc.dupe(u8, p.key);
    errdefer alloc.free(key);
    const name = try alloc.dupe(u8, p.name);
    errdefer alloc.free(name);
    const version = try alloc.dupe(u8, p.version);
    errdefer alloc.free(version);
    const hash = try alloc.dupe(u8, p.hash);
    errdefer alloc.free(hash);
    const install_path = try alloc.dupe(u8, p.install_path);
    errdefer alloc.free(install_path);

    // Deep-copy exposed_modules with partial-init tracking
    const exposed_modules = try alloc.alloc([]const u8, p.exposed_modules.len);
    errdefer alloc.free(exposed_modules);
    var exposed_count: usize = 0;
    errdefer for (exposed_modules[0..exposed_count]) |m| alloc.free(m);
    for (p.exposed_modules, 0..) |m, i| {
        exposed_modules[i] = try alloc.dupe(u8, m);
        exposed_count += 1;
    }

    // Deep-copy depends with partial-init tracking
    const depends = try alloc.alloc([]const u8, p.depends.len);
    errdefer alloc.free(depends);
    var depends_count: usize = 0;
    errdefer for (depends[0..depends_count]) |d| alloc.free(d);
    for (p.depends, 0..) |d, i| {
        depends[i] = try alloc.dupe(u8, d);
        depends_count += 1;
    }

    return Entry{
        .key = key,
        .name = name,
        .version = version,
        .hash = hash,
        .install_path = install_path,
        .exposed_modules = exposed_modules,
        .depends = depends,
    };
}

// ── Tests ─────────────────────────────────────────────────────────────────────

/// Return the absolute path of a TmpDir as an owned plain `[]u8`.
///
/// Caller owns the returned memory and must free it with `alloc.free`.
fn tmpDirPath(alloc: std.mem.Allocator, tmp: *std.testing.TmpDir) ![]const u8 {
    // realPathFileAlloc returns [:0]u8.  Free the sentinel slice as-is so the
    // allocator accounts for the null terminator, then dupe to a plain []u8
    // for the caller (whose defer free won't carry sentinel type info).
    const path_z = try std.Io.Dir.realPathFileAlloc(tmp.dir, std.testing.io, ".", alloc);
    defer alloc.free(path_z);
    return alloc.dupe(u8, path_z);
}

test "defaultPath generates correct format" {
    const path = try defaultPath(std.testing.allocator);
    defer std.testing.allocator.free(path);

    // Should contain .rhc/store/ and version
    try std.testing.expect(std.mem.indexOf(u8, path, ".rhc/store/") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "0.1.0") != null);

    // Should contain arch and os in the correct {arch}-{os}-{version} segment
    const arch_tag = @tagName(builtin.cpu.arch);
    const os_tag = @tagName(builtin.os.tag);
    try std.testing.expect(std.mem.indexOf(u8, path, arch_tag) != null);
    try std.testing.expect(std.mem.indexOf(u8, path, os_tag) != null);
}

test "computeKey generates SHA256-based key" {
    const desc_content = "name = \"test\"\nversion = \"1.0.0\"\n";
    const key = try computeKey(std.testing.allocator, "test", "1.0.0", desc_content);
    defer std.testing.allocator.free(key);

    // Key format: {64-char hash}-{name}-{version}
    try std.testing.expect(key.len >= 74); // 64 + 2 dashes + at least 4 for name-version
    const first_dash = std.mem.indexOfScalar(u8, key, '-') orelse return error.TestExpectFailed;
    const second_dash = std.mem.indexOfScalarPos(u8, key, first_dash + 1, '-') orelse return error.TestExpectFailed;

    try std.testing.expectEqual(@as(usize, 64), first_dash);
    try std.testing.expectEqualStrings("test", key[first_dash + 1 .. second_dash]);
    try std.testing.expectEqualStrings("1.0.0", key[second_dash + 1 ..]);

    // Same descriptor content = same hash
    const key2 = try computeKey(std.testing.allocator, "test", "1.0.0", desc_content);
    defer std.testing.allocator.free(key2);
    try std.testing.expectEqualStrings(key, key2);

    // Different descriptor = different hash
    const desc_content2 = "version = \"1.0.0\"\nname = \"test\"\n";
    const key3 = try computeKey(std.testing.allocator, "test", "1.0.0", desc_content2);
    defer std.testing.allocator.free(key3);
    try std.testing.expect(!std.mem.eql(u8, key, key3));
}

test "Store.init creates directory structure" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    const root_path = try std.fmt.allocPrint(std.testing.allocator, "{s}/test-store", .{tmp_abs});
    defer std.testing.allocator.free(root_path);

    var store = try init(std.testing.allocator, std.testing.io, root_path);
    defer store.deinit();

    // Verify paths are stored
    try std.testing.expectEqualStrings(root_path, store.root_path);

    const expected_conf_dir = try std.fmt.allocPrint(std.testing.allocator, "{s}/package.conf.d", .{root_path});
    defer std.testing.allocator.free(expected_conf_dir);
    try std.testing.expectEqualStrings(expected_conf_dir, store.conf_dir_path);

    // Verify directories exist
    try tmp_dir.dir.access(std.testing.io, "test-store", .{});
    try tmp_dir.dir.access(std.testing.io, "test-store/package.conf.d", .{});
}

test "computeConfPath returns correct .conf file path" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const key = "abc123-test-1.0.0";
    const conf_path = try computeConfPath(&store, key);
    defer store.allocator.free(conf_path);

    try std.testing.expect(std.mem.indexOf(u8, conf_path, "package.conf.d") != null);
    try std.testing.expect(std.mem.indexOf(u8, conf_path, key ++ ".conf") != null);
}

test "computePkgPath returns correct package directory path" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const pkg_path = try computePkgPath(&store, "test", "1.0.0");
    defer store.allocator.free(pkg_path);

    try std.testing.expect(std.mem.indexOf(u8, pkg_path, "test-1.0.0") != null);
}

test "Store.register creates conf file and package directory" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const desc_content =
        \\name = "test-pkg"
        \\version = "1.0.0"
        \\exposed-modules = ["Test.Module"]
        \\depends = []
    ;

    const desc = try descriptor.parse(std.testing.allocator, desc_content);
    defer desc.deinit(std.testing.allocator);

    const key = try computeKey(std.testing.allocator, desc.name, desc.version, desc_content);
    defer std.testing.allocator.free(key);

    try store.register(std.testing.io, key, desc_content, desc);

    // Verify .conf file exists
    const conf_path = try computeConfPath(&store, key);
    defer store.allocator.free(conf_path);
    try std.Io.Dir.access(.cwd(), std.testing.io, conf_path, .{});

    // Verify package directory exists
    const pkg_path = try computePkgPath(&store, desc.name, desc.version);
    defer store.allocator.free(pkg_path);
    try std.Io.Dir.access(.cwd(), std.testing.io, pkg_path, .{});
}

test "Store.register returns DuplicatePackage for duplicate" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const desc_content = "name = \"test\"\nversion = \"1.0.0\"\n";
    const desc = try descriptor.parse(std.testing.allocator, desc_content);
    defer desc.deinit(std.testing.allocator);

    const key = try computeKey(std.testing.allocator, desc.name, desc.version, desc_content);
    defer std.testing.allocator.free(key);

    try store.register(std.testing.io, key, desc_content, desc);

    // Second registration should fail
    const result = store.register(std.testing.io, key, desc_content, desc);
    try std.testing.expectError(error.DuplicatePackage, result);
}

test "Store.lookup finds registered package" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const desc_content =
        \\name = "lookup-test"
        \\version = "2.0.0"
        \\exposed-modules = ["Lookup.Module"]
        \\depends = []
    ;
    const desc = try descriptor.parse(std.testing.allocator, desc_content);
    defer desc.deinit(std.testing.allocator);

    const key = try computeKey(std.testing.allocator, desc.name, desc.version, desc_content);
    defer std.testing.allocator.free(key);

    try store.register(std.testing.io, key, desc_content, desc);

    // Lookup by name+version
    const entry = (try store.lookup(std.testing.io, "lookup-test", "2.0.0")) orelse {
        try std.testing.expect(false); // should not be null
        return;
    };
    defer entry.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings("lookup-test", entry.name);
    try std.testing.expectEqualStrings("2.0.0", entry.version);
    try std.testing.expectEqual(@as(usize, 1), entry.exposed_modules.len);
    try std.testing.expectEqualStrings("Lookup.Module", entry.exposed_modules[0]);
}

test "Store.lookup does not return a package with a matching name suffix" {
    // Regression: a package named "foo-bar" must NOT be returned when
    // looking up name="bar", even though "-bar-1.0.conf" is a suffix of
    // the filename for "foo-bar-1.0.conf".
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const desc_content = "name = \"foo-bar\"\nversion = \"1.0\"\n";
    const desc = try descriptor.parse(std.testing.allocator, desc_content);
    defer desc.deinit(std.testing.allocator);

    const key = try computeKey(std.testing.allocator, desc.name, desc.version, desc_content);
    defer std.testing.allocator.free(key);

    try store.register(std.testing.io, key, desc_content, desc);

    // Looking up "bar" at "1.0" must return null, not "foo-bar"
    const entry = try store.lookup(std.testing.io, "bar", "1.0");
    try std.testing.expect(entry == null);
}

test "Store.lookup returns null for non-existent package" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const entry = try store.lookup(std.testing.io, "nonexistent", "1.0.0");
    try std.testing.expect(entry == null);
}

test "Store.lookupByKey finds package by full key" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const desc_content = "name = \"keytest\"\nversion = \"1.0.0\"\n";
    const desc = try descriptor.parse(std.testing.allocator, desc_content);
    defer desc.deinit(std.testing.allocator);

    const key = try computeKey(std.testing.allocator, desc.name, desc.version, desc_content);
    defer std.testing.allocator.free(key);

    try store.register(std.testing.io, key, desc_content, desc);

    const entry = (try store.lookupByKey(std.testing.io, key)) orelse {
        try std.testing.expect(false);
        return;
    };
    defer entry.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(key, entry.key);
}

test "Store.lookupByKey returns null for unknown key" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const entry = try store.lookupByKey(std.testing.io, "unknown-key");
    try std.testing.expect(entry == null);
}

test "Store.list returns all registered packages" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    // Register two packages
    const desc1_content = "name = \"list-test-1\"\nversion = \"1.0.0\"\n";
    const desc1 = try descriptor.parse(std.testing.allocator, desc1_content);
    defer desc1.deinit(std.testing.allocator);
    const key1 = try computeKey(std.testing.allocator, desc1.name, desc1.version, desc1_content);
    defer std.testing.allocator.free(key1);
    try store.register(std.testing.io, key1, desc1_content, desc1);

    const desc2_content = "name = \"list-test-2\"\nversion = \"2.0.0\"\n";
    const desc2 = try descriptor.parse(std.testing.allocator, desc2_content);
    defer desc2.deinit(std.testing.allocator);
    const key2 = try computeKey(std.testing.allocator, desc2.name, desc2.version, desc2_content);
    defer std.testing.allocator.free(key2);
    try store.register(std.testing.io, key2, desc2_content, desc2);

    // List and verify
    const entries = try store.list(std.testing.io);
    defer {
        for (entries) |e| e.deinit(std.testing.allocator);
        std.testing.allocator.free(entries);
    }

    try std.testing.expectEqual(@as(usize, 2), entries.len);

    // Both packages should be in the list
    const found1 = blk: {
        for (entries) |e| {
            if (std.mem.eql(u8, e.name, "list-test-1")) break :blk true;
        }
        break :blk false;
    };
    try std.testing.expect(found1);
    const found2 = blk: {
        for (entries) |e| {
            if (std.mem.eql(u8, e.name, "list-test-2")) break :blk true;
        }
        break :blk false;
    };
    try std.testing.expect(found2);
}

test "Store.list returns empty slice for empty store" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    const tmp_abs = try tmpDirPath(std.testing.allocator, &tmp_dir);
    defer std.testing.allocator.free(tmp_abs);

    var store = try init(std.testing.allocator, std.testing.io, tmp_abs);
    defer store.deinit();

    const entries = try store.list(std.testing.io);
    defer std.testing.allocator.free(entries);

    try std.testing.expectEqual(@as(usize, 0), entries.len);
}

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

    try s.unregister(std.testing.io, key);

    const after = try s.list(std.testing.io);
    defer {
        for (after) |e| e.deinit(std.testing.allocator);
        std.testing.allocator.free(after);
    }
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
        s.unregister(std.testing.io, "nonexistent-key"),
    );
}
