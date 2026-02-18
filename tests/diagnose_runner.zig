//! Temporary diagnostic runner — not part of the permanent test suite.
//! Run with: zig build diag
//! Prints the first diagnostic message for each failing test file.
const std = @import("std");
const Dir = std.Io.Dir;

const rusholme = @import("rusholme");
const Parser = rusholme.frontend.parser.Parser;
const Lexer = rusholme.frontend.lexer.Lexer;
const Layout = rusholme.frontend.layout.LayoutProcessor;
const DiagnosticCollector = rusholme.diagnostics.diagnostic.DiagnosticCollector;

fn diagnose(alloc: std.mem.Allocator, path: []const u8) !void {
    const io = std.testing.io;
    const file = Dir.openFile(.cwd(), io, path, .{}) catch |err| {
        std.debug.print("  open_error: {}\n", .{err});
        return;
    };
    defer file.close(io);

    var read_buf: [8192]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    const source = try rdr.interface.allocRemaining(alloc, .limited(512 * 1024));
    defer alloc.free(source);

    var arena = std.heap.ArenaAllocator.init(alloc);
    defer arena.deinit();
    const aa = arena.allocator();

    var lexer = Lexer.init(aa, source, 1);
    var layout = Layout.init(aa, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(aa);

    var parser = Parser.init(aa, &layout, &diags) catch |err| {
        std.debug.print("  init_error: {}\n", .{err});
        return;
    };
    _ = parser.parseModule() catch |err| {
        std.debug.print("  parse_error: {}\n", .{err});
    };
    for (diags.diagnostics.items) |d| {
        std.debug.print("  [{d}:{d}] {s}\n", .{ d.span.start.line, d.span.start.column, d.message });
    }
    if (diags.hasErrors()) std.debug.print("  => FAIL\n", .{}) else std.debug.print("  => OK\n", .{});
}

test "diag" {
    const alloc = std.testing.allocator;
    // All should_compile tests — show OK or FAIL for each
    const files = [_][]const u8{
        "tests/should_compile/sc001_module_header.hs",
        "tests/should_compile/sc002_qualified_imports.hs",
        "tests/should_compile/sc003_data_types.hs",
        "tests/should_compile/sc004_record_syntax.hs",
        "tests/should_compile/sc005_typeclasses.hs",
        "tests/should_compile/sc006_pattern_matching.hs",
        "tests/should_compile/sc007_where_let.hs",
        "tests/should_compile/sc008_do_notation.hs",
        "tests/should_compile/sc009_lambda.hs",
        "tests/should_compile/sc010_type_classes_advanced.hs",
        "tests/should_compile/sc011_newtype.hs",
        "tests/should_compile/sc012_type_synonyms.hs",
        "tests/should_compile/sc013_operators_fixity.hs",
        "tests/should_compile/sc014_list_comprehensions.hs",
        "tests/should_compile/sc015_forall_types.hs",
        "tests/should_compile/sc016_case_expressions.hs",
        "tests/should_compile/sc017_string_char_literals.hs",
        "tests/should_compile/sc018_numeric_literals.hs",
        "tests/should_compile/sc019_deriving.hs",
        "tests/should_compile/sc020_multiline_layout.hs",
        "tests/should_compile/sc021_tuple_types.hs",
        "tests/should_compile/sc022_list_syntax.hs",
        "tests/should_compile/sc023_type_classes_instances.hs",
        "tests/should_compile/sc024_gadt.hs",
        "tests/should_compile/sc025_default_decl.hs",
        "tests/should_compile/sc026_where_mutual_recursion.hs",
        "tests/should_compile/sc027_type_operator_kinds.hs",
        "tests/should_compile/sc028_multiway_if.hs",
        "tests/should_compile/sc029_bang_patterns.hs",
        "tests/should_compile/sc030_record_wildcards_update.hs",
        "tests/should_compile/sc031_multiline_do.hs",
        "tests/should_compile/sc032_type_signatures_complex.hs",
        "tests/should_compile/sc033_sections_operators.hs",
        "tests/should_compile/sc034_class_default_methods.hs",
        "tests/should_compile/sc035_import_hiding.hs",
        "tests/should_compile/sc036_arithmetic_sequences.hs",
        "tests/should_compile/sc037_multiparamtc.hs",
        "tests/should_compile/sc038_qualified_names_in_exprs.hs",
        "tests/should_compile/sc039_complex_guards.hs",
        "tests/should_compile/sc040_type_annotations_exprs.hs",
        "tests/should_compile/sc041_ghc_real_world_001.hs",
        "tests/should_compile/sc042_ghc_real_world_002.hs",
        "tests/should_compile/sc043_infix_constructors_in_types.hs",
        "tests/should_fail/sf005_bad_layout.hs",
    };
    for (files) |path| {
        const short = std.fs.path.basename(path);
        std.debug.print("\n--- {s} ---\n", .{short});
        diagnose(alloc, path) catch |err| std.debug.print("  fatal: {}\n", .{err});
    }
}
