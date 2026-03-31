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
