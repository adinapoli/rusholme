//! Compile-failure test runner for post-parser diagnostics.
//!
//! Runs tests from:
//!
//!   tests/should_fail_compile/  — valid Haskell (parses successfully) that
//!                                 MUST produce a compilation error in a later
//!                                 stage (renamer, typechecker, or desugarer).
//!
//! Each .hs file gets its own `test` declaration so Zig's test runner reports
//! per-file pass / fail in the build summary.
//!
//! A `.properties` sidecar file next to a `.hs` file may contain:
//!   skip: <reason>           — silently skip this test.
//!   expected_code: <code>    — verify the diagnostic code (e.g. E010).
//!                              If omitted, any compilation error satisfies
//!                              the test.

const std = @import("std");
const Dir = std.Io.Dir;

const rusholme = @import("rusholme");
const Parser = rusholme.frontend.parser.Parser;
const Lexer = rusholme.frontend.lexer.Lexer;
const LayoutProcessor = rusholme.frontend.layout.LayoutProcessor;
const DiagnosticCollector = rusholme.diagnostics.diagnostic.DiagnosticCollector;
const DiagnosticCode = rusholme.diagnostics.diagnostic.DiagnosticCode;
const renamer_mod = rusholme.renamer.renamer;
const htype_mod = rusholme.tc.htype;
const infer_mod = rusholme.tc.infer;
const FileId = rusholme.FileId;

const test_dir = "tests/should_fail_compile";

// ── Properties sidecar ────────────────────────────────────────────────────

const Properties = struct {
    skip: bool = false,
    expected_code: ?[]const u8 = null,
};

fn readProperties(
    allocator: std.mem.Allocator,
    comptime basename: []const u8,
) !Properties {
    const io = std.testing.io;
    const props_path = test_dir ++ "/" ++ basename ++ ".properties";

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
        if (std.mem.startsWith(u8, trimmed, "skip:")) {
            props.skip = true;
        } else if (std.mem.startsWith(u8, trimmed, "expected_code:")) {
            const rest = trimmed["expected_code:".len..];
            const code = std.mem.trim(u8, rest, " \t");
            if (code.len > 0) {
                props.expected_code = code;
            }
        }
    }
    return props;
}

// ── Compilation result ────────────────────────────────────────────────────

const CompileResult = struct {
    had_errors: bool,
    /// Diagnostic codes emitted during compilation.
    codes: []const DiagnosticCode,
};

/// Run the full compilation pipeline (parse → rename → typecheck → desugar)
/// on a source file, returning whether errors were emitted and which codes.
fn tryCompile(
    allocator: std.mem.Allocator,
    comptime path: []const u8,
) !CompileResult {
    const io = std.testing.io;
    const file_id: FileId = 1;

    const file = try Dir.openFile(.cwd(), io, path, .{});
    defer file.close(io);

    var read_buf: [8192]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    const source = try rdr.interface.allocRemaining(allocator, .limited(512 * 1024));
    defer allocator.free(source);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const aa = arena.allocator();

    var diags = DiagnosticCollector.init();
    defer diags.deinit(aa);

    // ── Parse ────────────────────────────────────────────────────────────
    var lexer = Lexer.init(aa, source, file_id);
    var layout = LayoutProcessor.init(aa, &lexer);
    layout.setDiagnostics(&diags);

    var parser = Parser.init(aa, &layout, &diags) catch
        return .{ .had_errors = true, .codes = &.{} };

    const module = parser.parseModule() catch
        return .{ .had_errors = true, .codes = &.{} };

    if (diags.hasErrors()) {
        return collectCodes(allocator, &diags, aa);
    }

    // ── Rename ───────────────────────────────────────────────────────────
    var u_supply = rusholme.naming.unique.UniqueSupply{};
    const no_implicit_prelude = module.language_extensions.contains(.NoImplicitPrelude);
    var rename_env = try renamer_mod.RenameEnv.init(aa, &u_supply, &diags, no_implicit_prelude);
    defer rename_env.deinit();
    const renamed = renamer_mod.rename(module, &rename_env) catch
        return collectCodes(allocator, &diags, aa);

    if (diags.hasErrors()) {
        return collectCodes(allocator, &diags, aa);
    }

    // ── Typecheck ────────────────────────────────────────────────────────
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(aa);
    try rusholme.tc.env.initBuiltins(&ty_env, aa, &u_supply, no_implicit_prelude);
    var infer_ctx = infer_mod.InferCtx.init(aa, &ty_env, &mv_supply, &u_supply, &diags);
    var module_types = infer_mod.inferModule(&infer_ctx, renamed, null) catch
        return collectCodes(allocator, &diags, aa);
    defer module_types.deinit(aa);

    if (diags.hasErrors()) {
        return collectCodes(allocator, &diags, aa);
    }

    // ── Desugar ──────────────────────────────────────────────────────────
    _ = rusholme.core.desugar.desugarModule(aa, renamed, &module_types, &diags, &u_supply, null) catch
        return collectCodes(allocator, &diags, aa);

    return collectCodes(allocator, &diags, aa);
}

fn collectCodes(
    allocator: std.mem.Allocator,
    diags: *DiagnosticCollector,
    arena_alloc: std.mem.Allocator,
) !CompileResult {
    const all = try diags.getAll(arena_alloc);
    var codes = std.ArrayListUnmanaged(DiagnosticCode){};
    defer codes.deinit(allocator);
    for (all) |d| {
        if (d.severity == .@"error") {
            try codes.append(allocator, d.code);
        }
    }
    const owned = try allocator.alloc(DiagnosticCode, codes.items.len);
    @memcpy(owned, codes.items);
    return .{
        .had_errors = diags.hasErrors(),
        .codes = owned,
    };
}

// ── Test function ─────────────────────────────────────────────────────────

fn testShouldFailCompile(
    allocator: std.mem.Allocator,
    comptime basename: []const u8,
) !void {
    const props = try readProperties(allocator, basename);
    if (props.skip) return;

    const result = try tryCompile(allocator, test_dir ++ "/" ++ basename ++ ".hs");
    defer allocator.free(result.codes);

    if (!result.had_errors) {
        std.debug.print(
            "[FAIL] should_fail_compile/{s}.hs — compilation succeeded (expected failure)\n",
            .{basename},
        );
        return error.UnexpectedCompileSuccess;
    }

    // If expected_code is specified, verify it appears among the emitted codes.
    if (props.expected_code) |expected| {
        for (result.codes) |emitted_code| {
            if (std.mem.eql(u8, emitted_code.code(), expected)) return;
        }
        std.debug.print(
            "[FAIL] should_fail_compile/{s}.hs — expected diagnostic code {s}, got:",
            .{ basename, expected },
        );
        for (result.codes) |c| {
            std.debug.print(" {s}", .{c.code()});
        }
        std.debug.print("\n", .{});
        return error.WrongDiagnosticCode;
    }
}

// ── Test declarations ─────────────────────────────────────────────────────

test "should_fail_compile: sfc001_unknown_primop" {
    try testShouldFailCompile(std.testing.allocator, "sfc001_unknown_primop");
}

test "should_fail_compile: sfc002_unbound_variable" {
    try testShouldFailCompile(std.testing.allocator, "sfc002_unbound_variable");
}
