//! End-to-end test runner for tests/e2e.
//!
//! Compile/run/compare logic lives in `hs_test_harness.zig` (shared with
//! the Prelude regression suite in `prelude_test_runner.zig`). See that
//! file for the sidecar (`.stdout`, `.stderr`) and `.properties`
//! directive format (skip/xfail/exit_code/stderr).
//!
//! ## Adding a new test
//!
//! 1. Create `tests/e2e/<name>.hs` and `tests/e2e/<name>.stdout`.
//! 2. Optionally create `tests/e2e/<name>.properties` with directives.
//! 3. Optionally create `tests/e2e/<name>.stderr` with expected stderr output.
//! 4. Add a test declaration at the bottom of this file.

const std = @import("std");
const process = std.process;
const harness = @import("hs_test_harness.zig");
const e2e_options = @import("e2e_options");

const e2e_dir = "tests/e2e";

fn testE2e(allocator: std.mem.Allocator, comptime basename: []const u8) !void {
    return harness.testProgram(allocator, e2e_dir, basename, null);
}

/// Like `testE2e` but additionally passes `-O<level>` to `rhc build`.
/// Used by the `-O2` smoke tests below to verify the LLVM mid-level
/// optimiser is invoked without crashing.
fn testE2eOpt(
    allocator: std.mem.Allocator,
    comptime basename: []const u8,
    opt_flag: ?[]const u8,
) !void {
    return harness.testProgram(allocator, e2e_dir, basename, opt_flag);
}

// ── Test declarations ─────────────────────────────────────────────────────────

test "e2e: e2e_001_hello" {
    try testE2e(std.testing.allocator, "e2e_001_hello");
}

test "e2e: e2e_002_bool" {
    try testE2e(std.testing.allocator, "e2e_002_bool");
}

test "e2e: e2e_003_multi_putStrLn" {
    try testE2e(std.testing.allocator, "e2e_003_multi_putStrLn");
}

test "e2e: e2e_004_string" {
    try testE2e(std.testing.allocator, "e2e_004_string");
}

test "e2e: e2e_005_nested_datatypes" {
    try testE2e(std.testing.allocator, "e2e_005_nested_datatypes");
}

test "e2e: ghc_001_negative_literal" {
    try testE2e(std.testing.allocator, "ghc_001_negative_literal");
}

test "e2e: ghc_002_nested_where" {
    try testE2e(std.testing.allocator, "ghc_002_nested_where");
}

test "e2e: ghc_003_sk_combinators" {
    try testE2e(std.testing.allocator, "ghc_003_sk_combinators");
}

test "e2e: ghc_004_length" {
    try testE2e(std.testing.allocator, "ghc_004_length");
}

test "e2e: ghc_005_arithmetic" {
    try testE2e(std.testing.allocator, "ghc_005_arithmetic");
}

test "e2e: ghc_006_infinite_list" {
    try testE2e(std.testing.allocator, "ghc_006_infinite_list");
}

test "e2e: ghc_007_tree" {
    try testE2e(std.testing.allocator, "ghc_007_tree");
}

test "e2e: ghc_008_list_comprehension" {
    try testE2e(std.testing.allocator, "ghc_008_list_comprehension");
}

test "e2e: e2e_prelude_utils" {
    try testE2e(std.testing.allocator, "e2e_prelude_utils");
}

test "e2e: ghc_009_list_comp" {
    try testE2e(std.testing.allocator, "ghc_009_list_comp");
}

test "e2e: ghc_010_sections_negate" {
    try testE2e(std.testing.allocator, "ghc_010_sections_negate");
}

test "e2e: ghc_011_listcomp_let (#734)" {
    try testE2e(std.testing.allocator, "ghc_011_listcomp_let");
}

test "e2e: ghc_012_let_multi_binding (#747)" {
    try testE2e(std.testing.allocator, "ghc_012_let_multi_binding");
}

test "e2e: e2e_006_peano" {
    try testE2e(std.testing.allocator, "e2e_006_peano");
}

test "e2e: e2e_011_lazy_function_arguments (#517)" {
    try testE2e(std.testing.allocator, "e2e_011_lazy_function_arguments");
}

test "e2e: e2e_007_inductive_list" {
    try testE2e(std.testing.allocator, "e2e_007_inductive_list");
}

test "e2e: e2e_008_higher_order" {
    try testE2e(std.testing.allocator, "e2e_008_higher_order");
}

test "e2e: e2e_009_infinite_recursion" {
    try testE2e(std.testing.allocator, "e2e_009_infinite_recursion");
}

test "e2e: e2e_010_lazy_let" {
    try testE2e(std.testing.allocator, "e2e_010_lazy_let");
}

test "e2e: e2e_011_foreign_import_prim" {
    try testE2e(std.testing.allocator, "e2e_011_foreign_import_prim");
}

test "e2e: e2e_012_prelude_bool" {
    try testE2e(std.testing.allocator, "e2e_012_prelude_bool");
}

test "e2e: e2e_013_prelude_arithmetic" {
    try testE2e(std.testing.allocator, "e2e_013_prelude_arithmetic");
}

test "e2e: e2e_014_prelude_comparison" {
    try testE2e(std.testing.allocator, "e2e_014_prelude_comparison");
}

test "e2e: e2e_015_prelude_higher_order" {
    try testE2e(std.testing.allocator, "e2e_015_prelude_higher_order");
}

test "e2e: e2e_016_prelude_maybe_either" {
    try testE2e(std.testing.allocator, "e2e_016_prelude_maybe_either");
}

test "e2e: e2e_017_prelude_list" {
    try testE2e(std.testing.allocator, "e2e_017_prelude_list");
}

test "e2e: e2e_dict_minimal" {
    try testE2e(std.testing.allocator, "e2e_dict_minimal");
}

test "e2e: e2e_show_basic" {
    try testE2e(std.testing.allocator, "e2e_show_basic");
}

test "e2e: e2e_showcase" {
    try testE2e(std.testing.allocator, "e2e_showcase");
}

test "e2e: e2e_factorial (#624)" {
    try testE2e(std.testing.allocator, "e2e_factorial");
}

test "e2e: e2e_show_polymorphic" {
    try testE2e(std.testing.allocator, "e2e_show_polymorphic");
}

test "e2e: e2e_eq_bool (#531)" {
    try testE2e(std.testing.allocator, "e2e_eq_bool");
}

test "e2e: e2e_660_class_after_default_method (#660)" {
    try testE2e(std.testing.allocator, "e2e_660_class_after_default_method");
}

test "e2e: e2e_019_where_local_function (#623)" {
    try testE2e(std.testing.allocator, "e2e_019_where_local_function");
}

test "e2e: e2e_020_where_constant (#623)" {
    try testE2e(std.testing.allocator, "e2e_020_where_constant");
}

test "e2e: e2e_021_type_annotation (#644)" {
    try testE2e(std.testing.allocator, "e2e_021_type_annotation");
}

test "e2e: e2e_022_declaration_order (#566)" {
    try testE2e(std.testing.allocator, "e2e_022_declaration_order");
}

test "e2e: e2e_023_mutual_recursion (#566)" {
    try testE2e(std.testing.allocator, "e2e_023_mutual_recursion");
}

test "e2e: e2e_024_stderr_empty (#460)" {
    try testE2e(std.testing.allocator, "e2e_024_stderr_empty");
}

test "e2e: e2e_025_stderr_inline (#460)" {
    try testE2e(std.testing.allocator, "e2e_025_stderr_inline");
}

test "e2e: e2e_026_stderr_mismatch (#460)" {
    try testE2e(std.testing.allocator, "e2e_026_stderr_mismatch");
}

test "e2e: e2e_617_show_escape (#617)" {
    try testE2e(std.testing.allocator, "e2e_617_show_escape");
}

test "e2e: e2e_show_nonascii_char (#682)" {
    try testE2e(std.testing.allocator, "e2e_show_nonascii_char");
}

test "e2e: e2e_679_deriving_eq (#679)" {
    try testE2e(std.testing.allocator, "e2e_679_deriving_eq");
}

test "e2e: e2e_605_zero_field_thunk (#605)" {
    try testE2e(std.testing.allocator, "e2e_605_zero_field_thunk");
}

test "e2e: e2e_708_bounded_enum (#708)" {
    try testE2e(std.testing.allocator, "e2e_708_bounded_enum");
}

test "e2e: e2e_713_enum_defaults (#713)" {
    try testE2e(std.testing.allocator, "e2e_713_enum_defaults");
}

test "e2e: ghc_744_let_in_default_body (#744)" {
    try testE2e(std.testing.allocator, "ghc_744_let_in_default_body");
}

test "e2e: e2e_536_foreign_ccall (#536)" {
    try testE2e(std.testing.allocator, "e2e_536_foreign_ccall");
}

// ── Optimisation-level smoke tests (#755) ────────────────────────────────────
//
// These verify that the `-O<level>` flag actually flows through `rhc build`
// to LLVM's mid-level optimiser without crashing.  They are a smoke check —
// not a performance assertion — and reuse the simplest e2e program so we
// can be sure any failure is in the optimisation path, not user code.

test "e2e: -O2 invokes LLVM mid-level optimiser without crashing (#755)" {
    try testE2eOpt(std.testing.allocator, "e2e_001_hello", "-O2");
}

test "e2e: -O0 disables LLVM mid-level optimiser (#755)" {
    try testE2eOpt(std.testing.allocator, "e2e_001_hello", "-O0");
}

test "e2e: -O3 invokes LLVM aggressive pipeline without crashing (#755)" {
    try testE2eOpt(std.testing.allocator, "e2e_001_hello", "-O3");
}

test "e2e: rhc build rejects unknown -O level (#755)" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    const rhc_path = e2e_options.rhc_path;

    const argv = [_][]const u8{ rhc_path, "build", "-O", "fast", "tests/e2e/e2e_001_hello.hs" };
    const result = try process.run(allocator, io, .{ .argv = &argv });
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    switch (result.term) {
        .exited => |code| try std.testing.expect(code != 0),
        else => return error.UnexpectedTermination,
    }
    try std.testing.expect(std.mem.indexOf(u8, result.stderr, "invalid optimisation level") != null);
}
