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
};

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
    try std.testing.expect(key.len >= 74); // 64 + 2 dashes +最少
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
