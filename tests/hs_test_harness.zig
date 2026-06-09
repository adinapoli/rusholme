//! Shared harness for directory-based Haskell program test suites.
//!
//! Used by `e2e_test_runner.zig` (tests/e2e) and `prelude_test_runner.zig`
//! (tests/prelude). For each `.hs` file:
//!   1. Compile with `rhc build <file> -o <tmp/binary>`.
//!   2. Run the binary, capturing stdout and stderr.
//!   3. Compare captured stdout against the `.stdout` sidecar file.
//!   4. If a `.stderr` sidecar or inline `stderr:` directive is present,
//!      compare captured stderr against the expected value.
//!
//! ## Properties sidecar format (one directive per line)
//!
//! ```
//! skip:       <reason>  — skip this test entirely (unsupported feature)
//! xfail:      <reason>  — expected to fail; CI passes silently, notes if it passes
//! exit_code:  N         — expected process exit code (default 0)
//! stderr:     <text>    — expected binary stderr output (single-line, whitespace-trimmed).
//!                         CAUTION: captured stderr typically ends with '\n', so a binary that
//!                         writes `hPutStrLn stderr "msg"` produces `"msg\n"` which will NOT
//!                         match `stderr: msg` (no newline). Use a `.stderr` sidecar file for
//!                         exact byte-for-byte matching.
//! ```
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

// ── Properties ────────────────────────────────────────────────────────────────

pub const Properties = struct {
    skip: bool = false,
    xfail: bool = false,
    /// Expected exit code of the compiled binary (default 0).
    exit_code: u8 = 0,
    /// If non-null, the binary's stderr is compared against this string.
    /// Populated from the `stderr:` directive in `.properties` or the
    /// `.stderr` sidecar file (sidecar takes precedence).
    expected_stderr: ?[]const u8 = null,

    pub fn deinit(self: Properties, alloc: std.mem.Allocator) void {
        if (self.expected_stderr) |s| alloc.free(s);
    }
};

pub fn readProperties(
    allocator: std.mem.Allocator,
    comptime dir: []const u8,
    comptime basename: []const u8,
) !Properties {
    const io = std.testing.io;
    const props_path = dir ++ "/" ++ basename ++ ".properties";
    const stderr_sidecar_path = dir ++ "/" ++ basename ++ ".stderr";

    var props = Properties{};
    errdefer props.deinit(allocator);

    // ── Parse .properties directives (optional file) ──────────────────────────
    if (Dir.openFile(.cwd(), io, props_path, .{})) |file| {
        defer file.close(io);

        var read_buf: [1024]u8 = undefined;
        var rdr = file.reader(io, &read_buf);
        const content = try rdr.interface.allocRemaining(allocator, .limited(1024));
        defer allocator.free(content);

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
            if (std.mem.startsWith(u8, trimmed, "stderr:")) {
                const val = std.mem.trim(u8, trimmed["stderr:".len..], " \t");
                if (props.expected_stderr) |old| {
                    allocator.free(old);
                    props.expected_stderr = null; // prevent double-free if dupe fails
                }
                props.expected_stderr = try allocator.dupe(u8, val);
            }
        }
    } else |err| {
        if (err != error.FileNotFound) return err;
    }

    // ── .stderr sidecar overrides inline directive ─────────────────────────────
    if (Dir.cwd().readFileAlloc(io, stderr_sidecar_path, allocator, .unlimited)) |content| {
        if (props.expected_stderr) |old| allocator.free(old);
        props.expected_stderr = content;
    } else |err| {
        if (err != error.FileNotFound) return err;
    }

    return props;
}

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Print each line of `text` prefixed by `  | ` for visual separation from
/// the test runner's own diagnostic output.
fn printIndented(text: []const u8) void {
    var iter = std.mem.splitScalar(u8, text, '\n');
    while (iter.next()) |line| {
        // Skip the final empty segment produced by a trailing newline.
        if (iter.index == null and line.len == 0) break;
        std.debug.print("  | {s}\n", .{line});
    }
}

// ── Core test logic ───────────────────────────────────────────────────────────

/// Compile the Haskell source, run the binary, and compare stdout (and
/// optionally stderr). Returns true on success, false on any testable
/// failure (wrong output, wrong exit code, compile error). Infrastructure
/// errors (spawn failure, OOM) are propagated as errors.
///
/// `opt_flag` is an optional `-O<level>` to pass to `rhc build`. Passing
/// `null` exercises the CLI default (which is currently `-O2` for native).
fn runTest(
    allocator: std.mem.Allocator,
    comptime hs_path: []const u8,
    comptime stdout_ref_path: []const u8,
    expected_exit: u8,
    expected_stderr: ?[]const u8,
    quiet: bool,
    opt_flag: ?[]const u8,
    extra_build_args: []const []const u8,
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
    // Build argv with optional extra `rhc build` flags.  Flags must come
    // before the positional source path so clap parses them correctly.
    var argv_buf: [12][]const u8 = undefined;
    var argv_len: usize = 0;
    argv_buf[argv_len] = rhc_path;
    argv_len += 1;
    argv_buf[argv_len] = "build";
    argv_len += 1;
    if (opt_flag) |flag| {
        argv_buf[argv_len] = flag;
        argv_len += 1;
    }
    for (extra_build_args) |a| {
        argv_buf[argv_len] = a;
        argv_len += 1;
    }
    argv_buf[argv_len] = hs_path;
    argv_len += 1;
    argv_buf[argv_len] = "-o";
    argv_len += 1;
    argv_buf[argv_len] = binary_path;
    argv_len += 1;
    const compile_argv = argv_buf[0..argv_len];
    const compile_result = try process.run(allocator, io, .{
        .argv = compile_argv,
    });
    defer allocator.free(compile_result.stdout);
    defer allocator.free(compile_result.stderr);

    switch (compile_result.term) {
        .exited => |code| if (code != 0) {
            if (!quiet) {
                std.debug.print("  [e2e] compile failed (exit {d}):\n", .{code});
                printIndented(compile_result.stderr);
            }
            return false;
        },
        else => {
            if (!quiet) std.debug.print("  [e2e] compile terminated abnormally\n", .{});
            return false;
        },
    }

    // ── Step 2: Run binary, capture stdout and stderr ─────────────────────────
    const run_argv = [_][]const u8{binary_path};
    const run_result = try process.run(allocator, io, .{
        .argv = &run_argv,
    });
    defer allocator.free(run_result.stdout);
    defer allocator.free(run_result.stderr);

    const actual_exit: u8 = switch (run_result.term) {
        .exited => |code| @intCast(code),
        else => {
            if (!quiet) std.debug.print("  [e2e] binary terminated abnormally\n", .{});
            return false;
        },
    };

    // ── Step 3: Read expected stdout ──────────────────────────────────────────
    const cwd = Dir.cwd();
    const expected_stdout = try cwd.readFileAlloc(io, stdout_ref_path, allocator, .unlimited);
    defer allocator.free(expected_stdout);

    // ── Step 4: Assert stdout ─────────────────────────────────────────────────
    if (!std.mem.eql(u8, run_result.stdout, expected_stdout)) {
        if (!quiet) std.debug.print(
            "  [e2e] stdout mismatch:\n  expected: {s}  actual:   {s}\n",
            .{ expected_stdout, run_result.stdout },
        );
        return false;
    }

    // ── Step 5: Assert exit code ──────────────────────────────────────────────
    if (actual_exit != expected_exit) {
        if (!quiet) std.debug.print(
            "  [e2e] exit code mismatch: expected {d}, got {d}\n",
            .{ expected_exit, actual_exit },
        );
        return false;
    }

    // ── Step 6: Assert stderr (when expected_stderr is set) ───────────────────
    if (expected_stderr) |exp| {
        if (!std.mem.eql(u8, run_result.stderr, exp)) {
            if (!quiet) {
                std.debug.print("  [e2e] stderr mismatch:\n", .{});
                std.debug.print("  expected:\n", .{});
                printIndented(exp);
                std.debug.print("  actual:\n", .{});
                printIndented(run_result.stderr);
            }
            return false;
        }
    }

    return true;
}

// ── Public test entry point ───────────────────────────────────────────────────

/// Compile and check `<dir>/<basename>.hs` against its sidecars,
/// honouring `.properties` directives (skip/xfail/exit_code/stderr).
/// `opt_flag` optionally passes `-O<level>` to `rhc build`.
pub fn testProgram(
    allocator: std.mem.Allocator,
    comptime dir: []const u8,
    comptime basename: []const u8,
    opt_flag: ?[]const u8,
) !void {
    return testProgramWithFlags(allocator, dir, basename, opt_flag, &.{});
}

/// Like `testProgram` but additionally forwards `extra_build_args`
/// (e.g. `--rts=immix`) to `rhc build`. Used by the Immix end-to-end
/// smoke tests in `e2e_test_runner.zig` to verify the same programs
/// produce identical output under both heap backends.
pub fn testProgramWithFlags(
    allocator: std.mem.Allocator,
    comptime dir: []const u8,
    comptime basename: []const u8,
    opt_flag: ?[]const u8,
    extra_build_args: []const []const u8,
) !void {
    const props = try readProperties(allocator, dir, basename);
    defer props.deinit(allocator);
    if (props.skip) return;

    const hs_path = dir ++ "/" ++ basename ++ ".hs";
    const stdout_ref_path = dir ++ "/" ++ basename ++ ".stdout";

    const passed = try runTest(
        allocator,
        hs_path,
        stdout_ref_path,
        props.exit_code,
        props.expected_stderr,
        props.xfail,
        opt_flag,
        extra_build_args,
    );

    if (props.xfail) {
        if (passed) {
            // Unexpected pass — the gap was fixed. Log it but don't fail CI.
            std.debug.print(
                "  [xpass] {s}/{s}: unexpectedly passed — remove xfail: from .properties\n",
                .{ dir, basename },
            );
        }
        // Whether it passed or failed, xfail never fails CI.
        return;
    }

    if (!passed) return error.E2eTestFailed;
}
