//! Golden test runner for GHC test programs.
//!
//! Four kinds of golden tests are supported:
//!
//! 1. **Parse tests** (`testParseGolden`): parse the `.hs` file and verify
//!    that it succeeds without errors.
//!
//! 2. **Parse output tests** (`testParseOutputGolden`): parse the `.hs` file,
//!    pretty-print the AST, and compare against a `.parse.golden` sidecar file.
//!
//! 3. **Core output tests** (`testCoreGolden`): run the full pipeline
//!    (parse → rename → typecheck → desugar) and compare the Core IR output
//!    against a `.core.golden` sidecar file.
//!
//! 4. **GRIN output tests** (`testGrinGolden`): run the full pipeline including
//!    lambda lifting and Core→GRIN translation, then compare the GRIN IR output
//!    against a `.grin.golden` sidecar file.
//!
//! ## Updating golden files
//!
//! Set the environment variable `RUSHOLME_GOLDEN_UPDATE=1` before running
//! tests to regenerate all golden files in place.
//!
//! ## Filtering by stage
//!
//! Set `RUSHOLME_GOLDEN_STAGE` to run only tests for a specific stage:
//!   - `parse`  — parse output golden tests only
//!   - `core`   — Core IR golden tests only
//!   - `grin`   — GRIN IR golden tests only
//! If unset, all golden test stages run.
//!
//! ## Adding a new golden test
//!
//! 1. Create `tests/golden/<name>.hs`.
//! 2. Optionally create `tests/golden/<name>.<stage>.golden` with expected
//!    output; if the file is absent and `RUSHOLME_GOLDEN_UPDATE=1` is set,
//!    it will be written automatically on first run.
//! 3. Add a test declaration at the bottom of this file.

const std = @import("std");
const Dir = std.Io.Dir;

const rusholme = @import("rusholme");
const Parser = rusholme.frontend.parser.Parser;
const Lexer = rusholme.frontend.lexer.Lexer;
const LayoutProcessor = rusholme.frontend.layout.LayoutProcessor;
const PrettyPrinter = rusholme.frontend.pretty.PrettyPrinter;
const DiagnosticCollector = rusholme.diagnostics.diagnostic.DiagnosticCollector;
const renamer_mod = rusholme.renamer.renamer;
const htype_mod = rusholme.tc.htype;
const infer_mod = rusholme.tc.infer;
const FileId = rusholme.FileId;

const golden_test_dir = "tests/golden";

// ── Helpers ──────────────────────────────────────────────────────────────────

/// Check whether a .properties file marks the test as skipped.
fn isSkipped(allocator: std.mem.Allocator, comptime basename: []const u8) !bool {
    const io = std.testing.io;
    const props_path = golden_test_dir ++ "/" ++ basename ++ ".properties";

    const file = Dir.openFile(.cwd(), io, props_path, .{}) catch |err| switch (err) {
        error.FileNotFound => return false,
        else => return err,
    };
    defer file.close(io);

    var read_buf: [1024]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    const content = try rdr.interface.allocRemaining(allocator, .limited(1024));
    defer allocator.free(content);

    var iter = std.mem.splitScalar(u8, content, '\n');
    while (iter.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t\r");
        if (trimmed.len == 0 or trimmed[0] == '#') continue;
        if (std.mem.startsWith(u8, trimmed, "skip:")) return true;
    }
    return false;
}

/// Return true when `RUSHOLME_GOLDEN_UPDATE=1` is set in the environment.
fn goldenUpdateMode() bool {
    const val: [*:0]const u8 = std.c.getenv("RUSHOLME_GOLDEN_UPDATE") orelse return false;
    return std.mem.eql(u8, std.mem.span(val), "1");
}

/// Return true when the given stage is enabled by `RUSHOLME_GOLDEN_STAGE`.
/// If the env var is unset, all stages are enabled.
fn stageEnabled(comptime stage: []const u8) bool {
    const val: [*:0]const u8 = std.c.getenv("RUSHOLME_GOLDEN_STAGE") orelse return true;
    return std.mem.eql(u8, std.mem.span(val), stage);
}

/// Read the Haskell source for a golden test by basename.
/// Caller owns the returned slice.
fn readSource(allocator: std.mem.Allocator, comptime basename: []const u8) ![]const u8 {
    const io = std.testing.io;
    const haskell_path = golden_test_dir ++ "/" ++ basename ++ ".hs";

    const file = try Dir.openFile(.cwd(), io, haskell_path, .{});
    defer file.close(io);

    var read_buf: [8192]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    return try rdr.interface.allocRemaining(allocator, .limited(1024 * 1024));
}

/// Compare `actual` output against a golden sidecar file, or write it
/// if `RUSHOLME_GOLDEN_UPDATE=1` is set.
fn compareOrUpdateGolden(
    allocator: std.mem.Allocator,
    comptime basename: []const u8,
    comptime extension: []const u8,
    actual: []const u8,
) !void {
    const io = std.testing.io;
    const golden_path = golden_test_dir ++ "/" ++ basename ++ extension;

    if (goldenUpdateMode()) {
        const gf = try Dir.createFile(.cwd(), io, golden_path, .{});
        defer gf.close(io);
        var wbuf: [4096]u8 = undefined;
        var fw: std.Io.File.Writer = .init(gf, io, &wbuf);
        try fw.interface.writeAll(actual);
        try fw.interface.flush();
        return;
    }

    const golden_file = Dir.openFile(.cwd(), io, golden_path, .{}) catch |err| {
        if (err == error.FileNotFound) {
            std.debug.print(
                "Golden file missing: {s}\n" ++
                    "  Run with RUSHOLME_GOLDEN_UPDATE=1 to create it.\n",
                .{golden_path},
            );
        }
        return err;
    };
    defer golden_file.close(io);

    var gbuf: [8192]u8 = undefined;
    var grdr = golden_file.reader(io, &gbuf);
    const expected = try grdr.interface.allocRemaining(allocator, .limited(1024 * 1024));
    defer allocator.free(expected);

    const actual_trimmed = std.mem.trimEnd(u8, actual, " \t\r\n");
    const expected_trimmed = std.mem.trimEnd(u8, expected, " \t\r\n");

    if (!std.mem.eql(u8, actual_trimmed, expected_trimmed)) {
        std.debug.print(
            "Golden output mismatch for {s} ({s}):\n--- expected ---\n{s}\n--- actual ---\n{s}\n",
            .{ basename, extension, expected_trimmed, actual_trimmed },
        );
        return error.GoldenMismatch;
    }
}

// ── Parse-only test ───────────────────────────────────────────────────────────

/// Read a Haskell source file and verify it parses successfully.
fn testParseGolden(allocator: std.mem.Allocator, comptime basename: []const u8) !void {
    const io = std.testing.io;

    if (try isSkipped(allocator, basename)) return;

    const haskell_path = golden_test_dir ++ "/" ++ basename ++ ".hs";

    const file = try Dir.openFile(.cwd(), io, haskell_path, .{});
    defer file.close(io);

    var read_buf: [8192]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    const source = try rdr.interface.allocRemaining(allocator, .limited(1024 * 1024));
    defer allocator.free(source);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    var lexer = Lexer.init(arena_alloc, source, 1);
    var layout = LayoutProcessor.init(arena_alloc, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena_alloc);
    var parser = Parser.init(arena_alloc, &layout, &diags) catch |err| {
        std.debug.print("Parser init failed for {s}: {}\n", .{ basename, err });
        return err;
    };

    _ = parser.parseModule() catch |err| {
        std.debug.print("Failed to parse {s}: {}\n", .{ basename, err });
        for (diags.diagnostics.items) |d| {
            std.debug.print("  {s}\n", .{d.message});
        }
        return err;
    };
}

// ── Parse output test ─────────────────────────────────────────────────────────

/// Parse a Haskell source file and return the AST pretty-printed as an owned
/// string.  The returned string must be freed with `allocator.free`.
fn pipelineToParse(allocator: std.mem.Allocator, source: []const u8) ![]const u8 {
    const file_id: FileId = 1;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    var lexer = Lexer.init(arena_alloc, source, file_id);
    var layout = LayoutProcessor.init(arena_alloc, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena_alloc);
    layout.setDiagnostics(&diags);

    var parser = try Parser.init(arena_alloc, &layout, &diags);
    const module = try parser.parseModule();
    if (diags.hasErrors()) return error.ParseError;

    var pp = PrettyPrinter.init(allocator);
    defer pp.deinit();
    return try pp.printModule(module);
}

/// Parse a Haskell source file and compare the AST pretty-printer output
/// against the corresponding `.parse.golden` sidecar file.
fn testParseOutputGolden(allocator: std.mem.Allocator, comptime basename: []const u8) !void {
    if (!stageEnabled("parse")) return;
    if (try isSkipped(allocator, basename)) return;

    const source = try readSource(allocator, basename);
    defer allocator.free(source);

    const actual = pipelineToParse(allocator, source) catch |err| {
        std.debug.print("Parse pipeline failed for {s}: {}\n", .{ basename, err });
        return err;
    };
    defer allocator.free(actual);

    try compareOrUpdateGolden(allocator, basename, ".parse.golden", actual);
}

// ── Core output test ──────────────────────────────────────────────────────────

/// Run the full pipeline (parse → rename → typecheck → desugar) on `source`
/// and return the Core IR pretty-printed as an owned string.
///
/// The returned string must be freed with `allocator.free`.
fn pipelineToCore(allocator: std.mem.Allocator, source: []const u8) ![]const u8 {
    const file_id: FileId = 1;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    // ── Parse ────────────────────────────────────────────────────────────
    var lexer = Lexer.init(arena_alloc, source, file_id);
    var layout = LayoutProcessor.init(arena_alloc, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena_alloc);
    layout.setDiagnostics(&diags);

    var parser = try Parser.init(arena_alloc, &layout, &diags);
    const module = try parser.parseModule();
    if (diags.hasErrors()) return error.ParseError;

    // ── Rename ───────────────────────────────────────────────────────────
    var u_supply = rusholme.naming.unique.UniqueSupply{};
    const no_implicit_prelude = module.language_extensions.contains(.NoImplicitPrelude);
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags, no_implicit_prelude);
    defer rename_env.deinit();
    const renamed = try renamer_mod.rename(module, &rename_env);
    if (diags.hasErrors()) return error.RenameError;

    // ── Typecheck ────────────────────────────────────────────────────────
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(arena_alloc);
    try rusholme.tc.env.initBuiltins(&ty_env, arena_alloc, &u_supply, no_implicit_prelude);
    var infer_ctx = infer_mod.InferCtx.init(arena_alloc, &ty_env, &mv_supply, &u_supply, &diags);
    var module_types = try infer_mod.inferModule(&infer_ctx, renamed, null);
    defer module_types.deinit(arena_alloc);
    if (diags.hasErrors()) return error.TypecheckError;

    // ── Desugar ──────────────────────────────────────────────────────────
    const desugar_result = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply, null);
    const core_prog = desugar_result.program;
    if (diags.hasErrors()) return error.DesugarError;

    // ── Pretty-print Core to a heap string ───────────────────────────────
    var out: std.Io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.print("=== Core Program ({} data, {} bindings) ===\n", .{
        core_prog.data_decls.len,
        core_prog.binds.len,
    });
    var pp = rusholme.core.pretty.CorePrinter(*std.Io.Writer).init(&out.writer);
    try pp.printProgram(core_prog);
    try out.writer.writeByte('\n');

    return try out.toOwnedSlice();
}

/// Run the full pipeline on a Haskell source file and compare the Core IR
/// output against the corresponding `.core.golden` sidecar file.
fn testCoreGolden(allocator: std.mem.Allocator, comptime basename: []const u8) !void {
    if (!stageEnabled("core")) return;
    if (try isSkipped(allocator, basename)) return;

    const source = try readSource(allocator, basename);
    defer allocator.free(source);

    const actual = pipelineToCore(allocator, source) catch |err| {
        std.debug.print("Core pipeline failed for {s}: {}\n", .{ basename, err });
        return err;
    };
    defer allocator.free(actual);

    try compareOrUpdateGolden(allocator, basename, ".core.golden", actual);
}

// ── GRIN output test ──────────────────────────────────────────────────────────

/// Run the full pipeline (parse → rename → typecheck → desugar → lambda lift
/// → Core→GRIN translate) on `source` and return the GRIN IR pretty-printed
/// as an owned string.
///
/// The returned string must be freed with `allocator.free`.
fn pipelineToGrin(allocator: std.mem.Allocator, source: []const u8) ![]const u8 {
    const file_id: FileId = 1;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    // ── Parse ────────────────────────────────────────────────────────────
    var lexer = Lexer.init(arena_alloc, source, file_id);
    var layout = LayoutProcessor.init(arena_alloc, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena_alloc);
    layout.setDiagnostics(&diags);

    var parser = try Parser.init(arena_alloc, &layout, &diags);
    const module = try parser.parseModule();
    if (diags.hasErrors()) return error.ParseError;

    // ── Rename ───────────────────────────────────────────────────────────
    var u_supply = rusholme.naming.unique.UniqueSupply{};
    const no_implicit_prelude = module.language_extensions.contains(.NoImplicitPrelude);
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags, no_implicit_prelude);
    defer rename_env.deinit();
    const renamed = try renamer_mod.rename(module, &rename_env);
    if (diags.hasErrors()) return error.RenameError;

    // ── Typecheck ────────────────────────────────────────────────────────
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(arena_alloc);
    try rusholme.tc.env.initBuiltins(&ty_env, arena_alloc, &u_supply, no_implicit_prelude);
    var infer_ctx = infer_mod.InferCtx.init(arena_alloc, &ty_env, &mv_supply, &u_supply, &diags);
    var module_types = try infer_mod.inferModule(&infer_ctx, renamed, null);
    defer module_types.deinit(arena_alloc);
    if (diags.hasErrors()) return error.TypecheckError;

    // ── Desugar ──────────────────────────────────────────────────────────
    const desugar_result = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply, null);
    const core_prog = desugar_result.program;
    if (diags.hasErrors()) return error.DesugarError;

    // ── Lambda lift ──────────────────────────────────────────────────────
    const lift_result = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog, null, 0);

    // ── Core → GRIN ──────────────────────────────────────────────────────
    const grin_prog = try rusholme.grin.translate.translateProgram(arena_alloc, lift_result.program, null, null);

    // ── Pretty-print GRIN to a heap string ───────────────────────────────
    var out: std.Io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();

    try out.writer.print("=== GRIN Program ({} definitions) ===\n", .{grin_prog.defs.len});
    var pp = rusholme.grin.pretty.GrinPrinter(*std.Io.Writer).init(&out.writer);
    try pp.printProgram(grin_prog);

    return try out.toOwnedSlice();
}

/// Run the full pipeline including GRIN translation on a Haskell source file
/// and compare the GRIN IR output against the `.grin.golden` sidecar file.
fn testGrinGolden(allocator: std.mem.Allocator, comptime basename: []const u8) !void {
    if (!stageEnabled("grin")) return;
    if (try isSkipped(allocator, basename)) return;

    const source = try readSource(allocator, basename);
    defer allocator.free(source);

    const actual = pipelineToGrin(allocator, source) catch |err| {
        std.debug.print("GRIN pipeline failed for {s}: {}\n", .{ basename, err });
        return err;
    };
    defer allocator.free(actual);

    try compareOrUpdateGolden(allocator, basename, ".grin.golden", actual);
}

// ---------------------------------------------------------------------------
// One test declaration per golden test file.
// ---------------------------------------------------------------------------

// ── Parse-only tests ─────────────────────────────────────────────────────────

test "golden: ghc_001_qualified_import" { try testParseGolden(std.testing.allocator, "ghc_001_qualified_import"); }
test "golden: ghc_002_fixity" { try testParseGolden(std.testing.allocator, "ghc_002_fixity"); }
test "golden: ghc_003_layout" { try testParseGolden(std.testing.allocator, "ghc_003_layout"); }
test "golden: ghc_004_empty_decls" { try testParseGolden(std.testing.allocator, "ghc_004_empty_decls"); }
test "golden: ghc_005_simple_function" { try testParseGolden(std.testing.allocator, "ghc_005_simple_function"); }
test "golden: ghc_006_adt" { try testParseGolden(std.testing.allocator, "ghc_006_adt"); }
test "golden: ghc_007_pattern_matching" { try testParseGolden(std.testing.allocator, "ghc_007_pattern_matching"); }
test "golden: ghc_008_typeclass" { try testParseGolden(std.testing.allocator, "ghc_008_typeclass"); }
test "golden: ghc_009_deriving" { try testParseGolden(std.testing.allocator, "ghc_009_deriving"); }
test "golden: ghc_010_gadt" { try testParseGolden(std.testing.allocator, "ghc_010_gadt"); }
test "golden: ghc_011_record" { try testParseGolden(std.testing.allocator, "ghc_011_record"); }
test "golden: ghc_012_type_operator" { try testParseGolden(std.testing.allocator, "ghc_012_type_operator"); }
test "golden: ghc_013_newtype" { try testParseGolden(std.testing.allocator, "ghc_013_newtype"); }
test "golden: ghc_014_type_synonym" { try testParseGolden(std.testing.allocator, "ghc_014_type_synonym"); }
test "golden: ghc_015_tuples" { try testParseGolden(std.testing.allocator, "ghc_015_tuples"); }

// ── Parse output tests ────────────────────────────────────────────────────────

test "golden: ghc_005_simple_function parse" { try testParseOutputGolden(std.testing.allocator, "ghc_005_simple_function"); }
test "golden: ghc_006_adt parse" { try testParseOutputGolden(std.testing.allocator, "ghc_006_adt"); }
test "golden: ghc_007_pattern_matching parse" { try testParseOutputGolden(std.testing.allocator, "ghc_007_pattern_matching"); }

// ── Core output tests ─────────────────────────────────────────────────────────

test "golden: ghc_016_tier1_patterns core" { try testCoreGolden(std.testing.allocator, "ghc_016_tier1_patterns"); }
test "golden: ghc_017_tier2_patterns core" { try testCoreGolden(std.testing.allocator, "ghc_017_tier2_patterns"); }
test "golden: ghc_018_list_patterns core" { try testCoreGolden(std.testing.allocator, "ghc_018_list_patterns"); }
test "golden: ghc_019_guards core" { try testCoreGolden(std.testing.allocator, "ghc_019_guards"); }

// ── GRIN output tests ─────────────────────────────────────────────────────────

test "golden: ghc_016_tier1_patterns grin" { try testGrinGolden(std.testing.allocator, "ghc_016_tier1_patterns"); }
test "golden: ghc_017_tier2_patterns grin" { try testGrinGolden(std.testing.allocator, "ghc_017_tier2_patterns"); }
test "golden: ghc_018_list_patterns grin" { try testGrinGolden(std.testing.allocator, "ghc_018_list_patterns"); }
test "golden: ghc_019_guards grin" { try testGrinGolden(std.testing.allocator, "ghc_019_guards"); }
