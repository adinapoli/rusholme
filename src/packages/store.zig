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
