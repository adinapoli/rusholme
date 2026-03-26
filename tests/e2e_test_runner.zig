//! End-to-end test runner.
//!
//! For each `.hs` file in tests/e2e/:
//!   1. Compile with `rhc build <file> -o <tmp/binary>`.
//!   2. Run the binary, capturing stdout.
//!   3. Compare captured stdout against the `.stdout` sidecar file.
//!
//! ## Properties sidecar format (one directive per line)
//!
//! ```
//! skip:       <reason>  — skip this test entirely (unsupported feature)
//! xfail:      <reason>  — expected to fail; CI passes silently, notes if it passes
//! exit_code:  N         — expected process exit code (default 0)
//! ```
//!
//! ## Adding a new test
//!
//! 1. Create `tests/e2e/<name>.hs` and `tests/e2e/<name>.stdout`.
//! 2. Optionally create `tests/e2e/<name>.properties` with directives.
//! 3. Add a test declaration at the bottom of this file.
//!
//! ## rhc binary path
//!
//! The compiler binary path is baked in at build time via `e2e_options`
//! (a Zig `b.addOptions()` build option). The test step depends on the
//! install step, so `rhc` is guaranteed to exist when the tests run.

const std = @import("std");
const process = std.process;
const Dir = std.Io.Dir;
const e2e_options = @import("e2e_options");

const e2e_dir = "tests/e2e";

// ── Properties ────────────────────────────────────────────────────────────────

const Properties = struct {
    skip: bool = false,
    xfail: bool = false,
    /// Expected exit code of the compiled binary (default 0).
    exit_code: u8 = 0,
};

fn readProperties(
    allocator: std.mem.Allocator,
    comptime basename: []const u8,
) !Properties {
    const io = std.testing.io;
    const props_path = e2e_dir ++ "/" ++ basename ++ ".properties";

    const file = Dir.openFile(.cwd(), io, props_path, .{}) catch |err| switch (err) {
        error.FileNotFound => return .{},
        else => return err,
    };
    defer file.close(io);

    var read_buf: [1024]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    const content = try rdr.interface.allocRemaining(allocator, .limited(1024));
    defer allocator.free(content);

    var props = Properties{};
    var iter = std.mem.splitScalar(u8, content, '\n');
    while (iter.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t\r");
        if (trimmed.len == 0 or trimmed[0] == '#') continue;
        if (std.mem.startsWith(u8, trimmed, "skip:")) props.skip = true;
        if (std.mem.startsWith(u8, trimmed, "xfail:")) props.xfail = true;
        if (std.mem.startsWith(u8, trimmed, "exit_code:")) {
            const val = std.mem.trim(u8, trimmed["exit_code:".len..], " \t");
            props.exit_code = std.fmt.parseInt(u8, val, 10) catch 0;
        }
    }
    return props;
}

// ── Core test logic ───────────────────────────────────────────────────────────

/// Compile the Haskell source, run the binary, and compare stdout.
/// Returns true on success, false on any testable failure (wrong output,
/// non-zero exit, compile error). Infrastructure errors (spawn failure,
/// OOM) are propagated as errors.
fn runTest(
    allocator: std.mem.Allocator,
    comptime hs_path: []const u8,
    comptime stdout_ref_path: []const u8,
    expected_exit: u8,
) !bool {
    const io = std.testing.io;
    const rhc_path = e2e_options.rhc_path;

    // Create a temporary directory for the compiled binary.
    // std.testing.tmpDir always creates under .zig-cache/tmp/<sub_path>/.
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();

    const binary_path = try std.fmt.allocPrint(
        allocator,
        ".zig-cache/tmp/{s}/out",
        .{tmp.sub_path},
    );
    defer allocator.free(binary_path);

    // ── Step 1: Compile ───────────────────────────────────────────────────────
    const compile_argv = [_][]const u8{ rhc_path, "build", hs_path, "-o", binary_path };
    const compile_result = try process.run(allocator, io, .{
        .argv = &compile_argv,
    });
    defer allocator.free(compile_result.stdout);
    defer allocator.free(compile_result.stderr);

    switch (compile_result.term) {
        .exited => |code| if (code != 0) {
            std.debug.print(
                "  [e2e] compile failed (exit {d}):\n{s}\n",
                .{ code, compile_result.stderr },
            );
            return false;
        },
        else => {
            std.debug.print("  [e2e] compile terminated abnormally\n", .{});
            return false;
        },
    }

    // ── Step 2: Run binary, capture stdout ────────────────────────────────────
    const run_argv = [_][]const u8{binary_path};
    const run_result = try process.run(allocator, io, .{
        .argv = &run_argv,
    });
    defer allocator.free(run_result.stdout);
    defer allocator.free(run_result.stderr);

    const actual_exit: u8 = switch (run_result.term) {
        .exited => |code| @intCast(code),
        else => {
            std.debug.print("  [e2e] binary terminated abnormally\n", .{});
            return false;
        },
    };

    // ── Step 3: Read expected stdout ──────────────────────────────────────────
    const cwd = Dir.cwd();
    const expected_stdout = try cwd.readFileAlloc(io, stdout_ref_path, allocator, .unlimited);
    defer allocator.free(expected_stdout);

    // ── Step 4: Assert ────────────────────────────────────────────────────────
    if (!std.mem.eql(u8, run_result.stdout, expected_stdout)) {
        std.debug.print(
            "  [e2e] stdout mismatch:\n  expected: {s}  actual:   {s}\n",
            .{ expected_stdout, run_result.stdout },
        );
        return false;
    }

    if (actual_exit != expected_exit) {
        std.debug.print(
            "  [e2e] exit code mismatch: expected {d}, got {d}\n",
            .{ expected_exit, actual_exit },
        );
        return false;
    }

    return true;
}

// ── Public test helper ────────────────────────────────────────────────────────

fn testE2e(allocator: std.mem.Allocator, comptime basename: []const u8) !void {
    const props = try readProperties(allocator, basename);
    if (props.skip) return;

    const hs_path = e2e_dir ++ "/" ++ basename ++ ".hs";
    const stdout_ref_path = e2e_dir ++ "/" ++ basename ++ ".stdout";

    const passed = try runTest(allocator, hs_path, stdout_ref_path, props.exit_code);

    if (props.xfail) {
        if (passed) {
            // Unexpected pass — the gap was fixed. Log it but don't fail CI.
            std.debug.print(
                "  [xpass] e2e/{s}: unexpectedly passed — remove xfail: from .properties\n",
                .{basename},
            );
        }
        // Whether it passed or failed, xfail never fails CI.
        return;
    }

    if (!passed) return error.E2eTestFailed;
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
