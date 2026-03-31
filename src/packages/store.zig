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
} || std.fs.File.OpenError || std.fs.Dir.OpenError || std.json.Error;

// ── Public functions ─────────────────────────────────────────────────────────

// ── Public functions ─────────────────────────────────────────────────────────

/// Return the default store path: `~/.rhc/store/<arch>-<os>-<version>/`.
///
/// Path components:
/// - `arch`: from `builtin.cpu.arch` (e.g., "x86_64")
/// - `os`: from `builtin.os.tag` (e.g., "linux", "macos", "windows")
/// - `version`: the compiler version (hardcoded as "0.1.0" for now)
///
/// The caller owns the returned string and must free it with `alloc.free`.
pub fn defaultPath(alloc: std.mem.Allocator) []const u8 {
    const VERSION = "0.1.0"; // TODO: Use @import("root").main.VERSION when accessible
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
    return std.fmt.allocPrint(alloc, "{s}/.rhc/store/{s}-{s}-{s}/", .{
        std.c.getenv("HOME") orelse ".",
        arch,
        os_tag,
        VERSION,
    }) catch unreachable; // Only path allocation could fail; let it bubble up
}

/// Initialize a package store.
///
/// If `root_path` is null, uses `defaultPath()`.
/// Creates the root directory and `package.conf.d/` if missing.
pub fn init(alloc: std.mem.Allocator, root_path: ?[]const u8) Error!Store {
    const root = if (root_path) |p|
        try alloc.dupe(u8, p)
    else
        defaultPath(alloc);

    errdefer alloc.free(root);

    // Create root directory
    std.fs.cwd().makePath(root) catch |err| switch (err) {
        error.PathAlreadyExists => {}, // OK if it exists
        else => return err,
    };

    // Create package.conf.d directory
    const conf_dir = try std.fs.path.joinZ(alloc, &.{ root, "package.conf.d" });
    errdefer alloc.free(conf_dir);

    std.fs.cwd().makePath(conf_dir) catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => return err,
    };

    return Store{
        .allocator = alloc,
        .root_path = root,
        .conf_dir_path = conf_dir,
    };
}

/// Compute the package key from name, version, and descriptor content.

/// Compute the package key from name, version, and descriptor content.
///
/// Format: {sha256_hex}-{name}-{version}
///
/// Caller owns the returned string (allocated with alloc).
fn computeKey(alloc: std.mem.Allocator, name: []const u8, version: []const u8, descriptor_content: []const u8) Error![]const u8 {
    var hasher = std.crypto.hash.sha256.Sha256.init(.{});
    hasher.update(descriptor_content);
    var digest: [32]u8 = undefined;
    hasher.final(&digest);

    var hash_hex: [64]u8 = undefined;
    for (digest, 0..) |byte, i| {
        _ = std.fmt.formatIntHex(&hash_hex[2 * i .. 2 * i + 2], byte, .lower, .{ .width = 2 });
    }

    return std.fmt.allocPrint(alloc, "{s}-{s}-{s}", .{ &hash_hex, name, version });
}

/// Compute the full path to a .conf file for a given key.
fn computeConfPath(store: *const Store, key: []const u8) []const u8 {
    return std.fmt.allocPrint(store.allocator, "{s}/{s}.conf", .{
        store.conf_dir_path, key,
    }) catch unreachable;
}

/// Compute the full path to a package directory.
fn computePkgPath(store: *const Store, name: []const u8, version: []const u8) []const u8 {
    return std.fmt.allocPrint(store.allocator, "{s}/{s}-{s}", .{
        store.root_path, name, version,
    }) catch unreachable;
}

/// Register a package in the store.
///
/// Creates:
/// 1. .conf file in package.conf.d/
/// 2. Empty package directory for artifacts
///
/// Returns DuplicatePackage if the package key already exists.
pub fn register(
    self: *Store,
    pkg_key: []const u8,
    descriptor_content: []const u8,
    desc: descriptor.PackageDescriptor,
) Error!void {
    const conf_path = computeConfPath(self, pkg_key);
    defer self.allocator.free(conf_path);

    // Check if conf file already exists
    if (std.fs.cwd().openFile(conf_path, .{}) catch |err| {
        if (err == error.FileNotFound) {
            // OK, continue to registration
            return false;
        } else {
            return err;
        }
    }) |_| {
        // File exists, must close it and return error
        return Error.DuplicatePackage;
    }

    // Create package directory
    const pkg_path = computePkgPath(self, desc.name, desc.version);
    defer self.allocator.free(pkg_path);
    std.fs.cwd().makePath(pkg_path) catch |err| switch (err) {
        error.PathAlreadyExists => {},
        else => return err,
    };

    // Write .conf file
    var conf_file = try std.fs.cwd().createFile(conf_path, .{});
    defer conf_file.close();

    const install_path = try std.fs.cwd().realpathAlloc(self.allocator, pkg_path);
    defer self.allocator.free(install_path);

    // Compute hash
    var hasher = std.crypto.hash.sha256.Sha256.init(.{});
    hasher.update(descriptor_content);
    var digest: [32]u8 = undefined;
    hasher.final(&digest);

    var hash_hex: [64]u8 = undefined;
    for (digest, 0..) |byte, i| {
        _ = std.fmt.formatIntHex(&hash_hex[2 * i .. 2 * i + 2], byte, .lower, .{ .width = 2 });
    }

    // Write JSON conf
    const writer = conf_file.writer();
    try writer.writeAll("{\n");
    try writer.print("  \"key\": \"{s}\",\n", .{pkg_key});
    try writer.print("  \"name\": \"{s}\",\n", .{desc.name});
    try writer.print("  \"version\": \"{s}\",\n", .{desc.version});
    try writer.print("  \"hash\": \"{s}\",\n", .{&hash_hex});
    try writer.writeAll("  \"exposed_modules\": [");
    for (desc.exposed_modules, 0..) |m, i| {
        if (i > 0) try writer.writeAll(", ");
        try writer.print("\"{s}\"", .{m});
    }
    try writer.writeAll("],\n");
    try writer.writeAll("  \"depends\": [");
    for (desc.depends, 0..) |d, i| {
        if (i > 0) try writer.writeAll(", ");
        try writer.print("\"{s}\"", .{d});
    }
    try writer.writeAll("],\n");
    try writer.print("  \"install_path\": \"{s}\"\n", .{install_path});
    try writer.writeAll("}\n");
}

/// Parse a .conf file and return an Entry.
fn parseConfFile(alloc: std.mem.Allocator, path: []const u8) Error!Entry {
    const content = try std.fs.cwd().readFileAlloc(alloc, path, 1024 * 64);
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

    // Deep copy strings
    const entry = Entry{
        .key = try alloc.dupe(u8, p.key),
        .name = try alloc.dupe(u8, p.name),
        .version = try alloc.dupe(u8, p.version),
        .hash = try alloc.dupe(u8, p.hash),
        .install_path = try alloc.dupe(u8, p.install_path),
        .exposed_modules = try alloc.alloc([]const u8, p.exposed_modules.len),
        .depends = try alloc.alloc([]const u8, p.depends.len),
    };

    errdefer {
        alloc.free(entry.key);
        alloc.free(entry.name);
        alloc.free(entry.version);
        alloc.free(entry.hash);
        alloc.free(entry.install_path);
        for (entry.exposed_modules) |m| alloc.free(m);
        alloc.free(entry.exposed_modules);
        for (entry.depends) |d| alloc.free(d);
        alloc.free(entry.depends);
    }

    for (p.exposed_modules, 0..) |m, i| {
        entry.exposed_modules[i] = try alloc.dupe(u8, m);
    }
    for (p.depends, 0..) |d, i| {
        entry.depends[i] = try alloc.dupe(u8, d);
    }

    return entry;
}

/// Look up a package by name and version.
pub fn lookup(self: *const Store, name: []const u8, version: []const u8) Error!?Entry {
    const expected_suffix = try std.fmt.allocPrint(self.allocator, "-{s}-{s}", .{ name, version });
    defer self.allocator.free(expected_suffix);

    // Scan package.conf.d/ for matching .conf files
    var dir = std.fs.cwd().openDir(self.conf_dir_path, .{ .iterate = true }) catch |err| {
        return if (err == error.FileNotFound) null else err;
    };
    defer dir.close();

    var iter = dir.iterate();
    while (try iter.next()) |entry| {
        if (entry.kind != .file) continue;
        if (!std.mem.endsWith(u8, entry.name, ".conf")) continue;

        // Check suffix match
        if (std.mem.endsWith(u8, entry.name, expected_suffix ++ ".conf")) {
            const conf_path = try std.fs.path.joinZ(self.allocator, &.{ self.conf_dir_path, entry.name });
            defer self.allocator.free(conf_path);
            return try parseConfFile(self.allocator, conf_path);
        }
    }

    return null;
}

/// Look up a package by its full key (hash-name-version).
pub fn lookupByKey(self: *const Store, key: []const u8) Error!?Entry {
    const conf_filename = try std.fmt.allocPrintZ(self.allocator, "{s}.conf", .{key});
    defer self.allocator.free(conf_filename);

    const conf_path = try std.fs.path.joinZ(self.allocator, &.{ self.conf_dir_path, conf_filename });
    defer self.allocator.free(conf_path);

    // Check if file exists
    const file = std.fs.cwd().openFile(conf_path, .{}) catch |err| {
        return if (err == error.FileNotFound) null else err;
    };
    file.close();

    return try parseConfFile(self.allocator, conf_path);
}

// ── Tests ─────────────────────────────────────────────────────────────────────

test "defaultPath generates correct format" {
    const path = defaultPath(std.testing.allocator);
    defer std.testing.allocator.free(path);

    // Should contain .rhc/store/ and version
    try std.testing.expect(std.mem.indexOf(u8, path, ".rhc/store/") != null);
    try std.testing.expect(std.mem.indexOf(u8, path, "0.1.0") != null);

    // Should contain valid arch/os
    const arch_tag = @tagName(builtin.cpu.arch);
    const os_tag = @tagName(builtin.os.tag);
    const has_arch_or_os =
        std.mem.indexOf(u8, path, arch_tag) != null or
        std.mem.indexOf(u8, path, os_tag) != null;
    try std.testing.expect(has_arch_or_os);
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

    const root_path = try std.fs.path.joinZ(std.testing.allocator, &.{
        tmp_dir.dir.path, "test-store",
    });
    defer std.testing.allocator.free(root_path);

    var store = try Store.init(std.testing.allocator, root_path);
    defer store.deinit();

    // Verify paths are stored
    try std.testing.expectEqualStrings(root_path, store.root_path);

    const expected_conf_dir = try std.fs.path.joinZ(std.testing.allocator, &.{ root_path, "package.conf.d" });
    defer std.testing.allocator.free(expected_conf_dir);
    try std.testing.expectEqualStrings(expected_conf_dir, store.conf_dir_path);

    // Verify directories exist
    try tmp_dir.dir.access("test-store", .{});
    try tmp_dir.dir.access("test-store/package.conf.d", .{});
}

test "computeConfPath returns correct .conf file path" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
    defer store.deinit();

    const key = "abc123-test-1.0.0";
    const conf_path = computeConfPath(&store, key);

    defer store.allocator.free(conf_path);
    try std.testing.expect(std.mem.indexOf(u8, conf_path, "package.conf.d") != null);
    try std.testing.expect(std.mem.indexOf(u8, conf_path, key ++ ".conf") != null);
}

test "computePkgPath returns correct package directory path" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
    defer store.deinit();

    const pkg_path = computePkgPath(&store, "test", "1.0.0");
    defer store.allocator.free(pkg_path);

    try std.testing.expect(std.mem.indexOf(u8, pkg_path, "test-1.0.0") != null);
}

test "Store.register creates conf file and package directory" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
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

    try store.register(key, desc_content, desc);

    // Verify .conf file exists
    const conf_path = computeConfPath(&store, key);
    defer store.allocator.free(conf_path);
    std.fs.cwd().access(conf_path, .{}) catch |err| {
        try std.testing.expect(error.FileNotFound == err);
    };

    // Verify package directory exists
    const pkg_path = computePkgPath(&store, desc.name, desc.version);
    defer store.allocator.free(pkg_path);
    std.fs.cwd().access(pkg_path, .{}) catch |err| {
        try std.testing.expect(error.FileNotFound == err);
    };
}

test "Store.register returns DuplicatePackage for duplicate" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
    defer store.deinit();

    const desc_content = "name = \"test\"\nversion = \"1.0.0\"\n";
    const desc = try descriptor.parse(std.testing.allocator, desc_content);
    defer desc.deinit(std.testing.allocator);

    const key = try computeKey(std.testing.allocator, desc.name, desc.version, desc_content);
    defer std.testing.allocator.free(key);

    try store.register(key, desc_content, desc);

    // Second registration should fail
    const result = store.register(key, desc_content, desc);
    try std.testing.expectError(Error.DuplicatePackage, result);
}

test "Store.lookup finds registered package" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
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

    try store.register(key, desc_content, desc);

    // Lookup by name+version
    const entry = (try store.lookup("lookup-test", "2.0.0")) orelse {
        try std.testing.expect(false); // should not be null
        return;
    };
    defer entry.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings("lookup-test", entry.name);
    try std.testing.expectEqualStrings("2.0.0", entry.version);
    try std.testing.expectEqual(@as(usize, 1), entry.exposed_modules.len);
    try std.testing.expectEqualStrings("Lookup.Module", entry.exposed_modules[0]);
}

test "Store.lookup returns null for non-existent package" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
    defer store.deinit();

    const entry = try store.lookup("nonexistent", "1.0.0");
    try std.testing.expect(entry == null);
}

test "Store.lookupByKey finds package by full key" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
    defer store.deinit();

    const desc_content = "name = \"keytest\"\nversion = \"1.0.0\"\n";
    const desc = try descriptor.parse(std.testing.allocator, desc_content);
    defer desc.deinit(std.testing.allocator);

    const key = try computeKey(std.testing.allocator, desc.name, desc.version, desc_content);
    defer std.testing.allocator.free(key);

    try store.register(key, desc_content, desc);

    const entry = (try store.lookupByKey(key)) orelse {
        try std.testing.expect(false);
        return;
    };
    defer entry.deinit(std.testing.allocator);

    try std.testing.expectEqualStrings(key, entry.key);
}

test "Store.lookupByKey returns null for unknown key" {
    var tmp_dir = std.testing.tmpDir(.{});
    defer tmp_dir.cleanup();

    var store = try Store.init(std.testing.allocator, tmp_dir.dir.path);
    defer store.deinit();

    const entry = try store.lookupByKey("unknown-key");
    try std.testing.expect(entry == null);
}
