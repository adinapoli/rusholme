//! Integration tests for `rhc pkg` subcommands.
//!
//! These tests exercise the public pkg_cmd API end-to-end using a real
//! tmpDir-backed package store. They use the `rusholme` module import path
//! and are registered as a separate test suite in build.zig.
//!
//! Issue: #651

const std = @import("std");
const rusholme = @import("rusholme");
const pkg_cmd = rusholme.packages.pkg_cmd;
const store_mod = rusholme.packages.store;
const descriptor = rusholme.packages.descriptor;

fn makeTestStore(alloc: std.mem.Allocator, tmp: *std.testing.TmpDir) !store_mod.Store {
    const path = try std.Io.Dir.realPathFileAlloc(tmp.dir, std.testing.io, ".", alloc);
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
    defer {
        for (entries) |e| e.deinit(std.testing.allocator);
        std.testing.allocator.free(entries);
    }
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
    defer {
        for (entries) |e| e.deinit(std.testing.allocator);
        std.testing.allocator.free(entries);
    }
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

    try std.testing.expectError(
        error.CheckFailed,
        pkg_cmd.cmdPkgCheck(std.testing.allocator, std.testing.io, &s),
    );
}
