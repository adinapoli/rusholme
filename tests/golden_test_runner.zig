//! Golden test runner for GHC test programs.
//!
//! Each golden test file has its own test declaration so that Zig's test runner
//! reports per-file pass/fail/skip in the build summary. Tests with a
//! `.properties` sidecar containing `skip:` are silently skipped.
//!
//! When adding a new golden test file, add a corresponding test declaration
//! at the bottom of this file.

const std = @import("std");
const Dir = std.Io.Dir;

const rusholme = @import("rusholme");
const Parser = rusholme.frontend.parser.Parser;
const Lexer = rusholme.frontend.lexer.Lexer;
const LayoutProcessor = rusholme.frontend.layout.LayoutProcessor;
const DiagnosticCollector = rusholme.diagnostics.diagnostic.DiagnosticCollector;

const golden_test_dir = "tests/golden";

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

// ---------------------------------------------------------------------------
// One test declaration per golden test file.
// ---------------------------------------------------------------------------

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
