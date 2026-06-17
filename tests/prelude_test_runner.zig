//! Prelude regression suite runner (#759, Epic #754 D2).
//!
//! Runs every program in tests/prelude/ through the shared harness
//! (`hs_test_harness.zig`). Together the programs exercise every binding
//! exported from lib/Prelude.hs — see tests/prelude/README.md for the
//! binding → test mapping. A Prelude regression fails CI here even if no
//! e2e test happens to touch the affected binding.

const std = @import("std");
const harness = @import("hs_test_harness.zig");

const prelude_dir = "tests/prelude";

fn testPrelude(allocator: std.mem.Allocator, comptime basename: []const u8) !void {
    return harness.testProgram(allocator, prelude_dir, basename, null);
}

test "prelude: p001_bool" {
    try testPrelude(std.testing.allocator, "p001_bool");
}

test "prelude: p002_arith" {
    try testPrelude(std.testing.allocator, "p002_arith");
}

test "prelude: p003_compare" {
    try testPrelude(std.testing.allocator, "p003_compare");
}

test "prelude: p004_combinators" {
    try testPrelude(std.testing.allocator, "p004_combinators");
}

test "prelude: p005_list_basic" {
    try testPrelude(std.testing.allocator, "p005_list_basic");
}

test "prelude: p006_folds" {
    try testPrelude(std.testing.allocator, "p006_folds");
}

test "prelude: p007_maybe_either" {
    try testPrelude(std.testing.allocator, "p007_maybe_either");
}

test "prelude: p008_io" {
    try testPrelude(std.testing.allocator, "p008_io");
}

test "prelude: p009_char" {
    try testPrelude(std.testing.allocator, "p009_char");
}

test "prelude: p010_show" {
    try testPrelude(std.testing.allocator, "p010_show");
}

test "prelude: p011_enum_bounded" {
    try testPrelude(std.testing.allocator, "p011_enum_bounded");
}

test "prelude: p012_error" {
    try testPrelude(std.testing.allocator, "p012_error");
}

test "prelude: p013_hof_prelude_arg (xfail #764)" {
    try testPrelude(std.testing.allocator, "p013_hof_prelude_arg");
}

test "prelude: p014_bounded" {
    try testPrelude(std.testing.allocator, "p014_bounded");
}
