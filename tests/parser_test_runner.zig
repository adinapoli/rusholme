//! Parser conformance test runner.
//!
//! Runs two categories of tests driven by files on disk:
//!
//!   tests/should_compile/  — valid Haskell that the parser MUST accept.
//!   tests/should_fail/     — programs with definite parse errors that the
//!                            parser MUST reject (i.e. return an error or
//!                            populate the DiagnosticCollector with errors).
//!
//! Each .hs file gets its own `test` declaration so Zig's test runner reports
//! per-file pass / fail in the build summary.
//!
//! A `.properties` sidecar file next to a `.hs` file may contain:
//!   skip: <reason>   — silently skip this test (known parser gap).
//!   xfail: <reason>  — mark as expected failure (parser can't handle it yet,
//!                       but we want to track it).  The test passes if the
//!                       parser *fails*, and is reported as an unexpected pass
//!                       if the parser *succeeds*.
//!
//! The xfail mechanism lets us land the full test corpus immediately and
//! graduate tests to passing as gaps are fixed, without keeping CI red.

const std = @import("std");
const Dir = std.Io.Dir;

const rusholme = @import("rusholme");
const Parser = rusholme.frontend.parser.Parser;
const Lexer = rusholme.frontend.lexer.Lexer;
const LayoutProcessor = rusholme.frontend.layout.LayoutProcessor;
const DiagnosticCollector = rusholme.diagnostics.diagnostic.DiagnosticCollector;

const should_compile_dir = "tests/should_compile";
const should_fail_dir = "tests/should_fail";

// ── Properties sidecar ────────────────────────────────────────────────────

const Properties = struct {
    skip: bool = false,
    xfail: bool = false,
};

fn readProperties(
    allocator: std.mem.Allocator,
    comptime dir: []const u8,
    comptime basename: []const u8,
) !Properties {
    const io = std.testing.io;
    const props_path = dir ++ "/" ++ basename ++ ".properties";

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
    }
    return props;
}

// ── Core parse helper ─────────────────────────────────────────────────────

/// Attempt to parse a Haskell source file.
/// Returns true if parsing succeeded (no errors emitted, parseModule returned
/// without error), false otherwise.
fn tryParse(allocator: std.mem.Allocator, comptime path: []const u8) !bool {
    const io = std.testing.io;

    const file = try Dir.openFile(.cwd(), io, path, .{});
    defer file.close(io);

    var read_buf: [8192]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    const source = try rdr.interface.allocRemaining(allocator, .limited(512 * 1024));
    defer allocator.free(source);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const aa = arena.allocator();

    var lexer = Lexer.init(aa, source, 1);
    var layout = LayoutProcessor.init(aa, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(aa);

    var parser = Parser.init(aa, &layout, &diags) catch return false;

    _ = parser.parseModule() catch return false;

    return !diags.hasErrors();
}

// ── should_compile ────────────────────────────────────────────────────────

/// Run a should_compile test.
/// PASS  — parser accepts the file.
/// SKIP  — .properties contains skip:.
/// XFAIL — .properties contains xfail: and parser rejects the file.
///         If parser *accepts* the file despite xfail:, the test *passes* with
///         a note (unexpected pass is good news — it means a gap was fixed).
fn testShouldCompile(
    allocator: std.mem.Allocator,
    comptime basename: []const u8,
) !void {
    const props = try readProperties(allocator, should_compile_dir, basename);
    if (props.skip) return;

    const ok = try tryParse(allocator, should_compile_dir ++ "/" ++ basename ++ ".hs");

    if (props.xfail) {
        // Expected to fail: if it passes, that's fine (gap fixed); if it
        // fails, also fine (gap still open).  We never make CI red for xfail.
        if (ok) {
            // Unexpected pass is still a pass — just log it so the developer
            // knows to remove the xfail annotation.
            std.debug.print(
                "[xfail-pass] {s}: parser now accepts this file — remove xfail:\n",
                .{basename},
            );
        }
        // Either way, don't fail the test.
        return;
    }

    if (!ok) {
        std.debug.print(
            "[FAIL] should_compile/{s}.hs — parser rejected a valid program\n",
            .{basename},
        );
        return error.UnexpectedParseFailure;
    }
}

// ── should_fail ───────────────────────────────────────────────────────────

/// Run a should_fail test.
/// PASS  — parser rejects the file (emits diagnostics or returns error).
/// SKIP  — .properties contains skip:.
/// XFAIL — .properties contains xfail: and parser *accepts* the file.
///         (Perversely, an xfail in should_fail means "we expect the parser
///          to erroneously accept this bad input for now".)
fn testShouldFail(
    allocator: std.mem.Allocator,
    comptime basename: []const u8,
) !void {
    const props = try readProperties(allocator, should_fail_dir, basename);
    if (props.skip) return;

    const ok = try tryParse(allocator, should_fail_dir ++ "/" ++ basename ++ ".hs");

    if (props.xfail) {
        // Expected to (erroneously) accept: don't fail CI, but log it.
        if (!ok) {
            std.debug.print(
                "[xfail-pass] {s}: parser now rejects this file — remove xfail:\n",
                .{basename},
            );
        }
        return;
    }

    if (ok) {
        std.debug.print(
            "[FAIL] should_fail/{s}.hs — parser accepted invalid syntax\n",
            .{basename},
        );
        return error.UnexpectedParseSuccess;
    }
}

// ── should_compile test declarations ─────────────────────────────────────

test "should_compile: sc001_module_header" { try testShouldCompile(std.testing.allocator, "sc001_module_header"); }
test "should_compile: sc002_qualified_imports" { try testShouldCompile(std.testing.allocator, "sc002_qualified_imports"); }
test "should_compile: sc003_data_types" { try testShouldCompile(std.testing.allocator, "sc003_data_types"); }
test "should_compile: sc004_record_syntax" { try testShouldCompile(std.testing.allocator, "sc004_record_syntax"); }
test "should_compile: sc005_typeclasses" { try testShouldCompile(std.testing.allocator, "sc005_typeclasses"); }
test "should_compile: sc006_pattern_matching" { try testShouldCompile(std.testing.allocator, "sc006_pattern_matching"); }
test "should_compile: sc007_where_let" { try testShouldCompile(std.testing.allocator, "sc007_where_let"); }
test "should_compile: sc008_do_notation" { try testShouldCompile(std.testing.allocator, "sc008_do_notation"); }
test "should_compile: sc009_lambda" { try testShouldCompile(std.testing.allocator, "sc009_lambda"); }
test "should_compile: sc010_type_classes_advanced" { try testShouldCompile(std.testing.allocator, "sc010_type_classes_advanced"); }
test "should_compile: sc011_newtype" { try testShouldCompile(std.testing.allocator, "sc011_newtype"); }
test "should_compile: sc012_type_synonyms" { try testShouldCompile(std.testing.allocator, "sc012_type_synonyms"); }
test "should_compile: sc013_operators_fixity" { try testShouldCompile(std.testing.allocator, "sc013_operators_fixity"); }
test "should_compile: sc014_list_comprehensions" { try testShouldCompile(std.testing.allocator, "sc014_list_comprehensions"); }
test "should_compile: sc015_forall_types" { try testShouldCompile(std.testing.allocator, "sc015_forall_types"); }
test "should_compile: sc016_case_expressions" { try testShouldCompile(std.testing.allocator, "sc016_case_expressions"); }
test "should_compile: sc017_string_char_literals" { try testShouldCompile(std.testing.allocator, "sc017_string_char_literals"); }
test "should_compile: sc018_numeric_literals" { try testShouldCompile(std.testing.allocator, "sc018_numeric_literals"); }
test "should_compile: sc019_deriving" { try testShouldCompile(std.testing.allocator, "sc019_deriving"); }
test "should_compile: sc020_multiline_layout" { try testShouldCompile(std.testing.allocator, "sc020_multiline_layout"); }
test "should_compile: sc021_tuple_types" { try testShouldCompile(std.testing.allocator, "sc021_tuple_types"); }
test "should_compile: sc022_list_syntax" { try testShouldCompile(std.testing.allocator, "sc022_list_syntax"); }
test "should_compile: sc023_type_classes_instances" { try testShouldCompile(std.testing.allocator, "sc023_type_classes_instances"); }
test "should_compile: sc024_gadt" { try testShouldCompile(std.testing.allocator, "sc024_gadt"); }
test "should_compile: sc025_default_decl" { try testShouldCompile(std.testing.allocator, "sc025_default_decl"); }
test "should_compile: sc026_where_mutual_recursion" { try testShouldCompile(std.testing.allocator, "sc026_where_mutual_recursion"); }
test "should_compile: sc027_type_operator_kinds" { try testShouldCompile(std.testing.allocator, "sc027_type_operator_kinds"); }
test "should_compile: sc028_multiway_if" { try testShouldCompile(std.testing.allocator, "sc028_multiway_if"); }
test "should_compile: sc029_bang_patterns" { try testShouldCompile(std.testing.allocator, "sc029_bang_patterns"); }
test "should_compile: sc030_record_wildcards_update" { try testShouldCompile(std.testing.allocator, "sc030_record_wildcards_update"); }
test "should_compile: sc031_multiline_do" { try testShouldCompile(std.testing.allocator, "sc031_multiline_do"); }
test "should_compile: sc032_type_signatures_complex" { try testShouldCompile(std.testing.allocator, "sc032_type_signatures_complex"); }
test "should_compile: sc033_sections_operators" { try testShouldCompile(std.testing.allocator, "sc033_sections_operators"); }
test "should_compile: sc034_class_default_methods" { try testShouldCompile(std.testing.allocator, "sc034_class_default_methods"); }
test "should_compile: sc035_import_hiding" { try testShouldCompile(std.testing.allocator, "sc035_import_hiding"); }
test "should_compile: sc036_arithmetic_sequences" { try testShouldCompile(std.testing.allocator, "sc036_arithmetic_sequences"); }
test "should_compile: sc037_multiparamtc" { try testShouldCompile(std.testing.allocator, "sc037_multiparamtc"); }
test "should_compile: sc038_qualified_names_in_exprs" { try testShouldCompile(std.testing.allocator, "sc038_qualified_names_in_exprs"); }
test "should_compile: sc039_complex_guards" { try testShouldCompile(std.testing.allocator, "sc039_complex_guards"); }
test "should_compile: sc040_type_annotations_exprs" { try testShouldCompile(std.testing.allocator, "sc040_type_annotations_exprs"); }
test "should_compile: sc041_ghc_real_world_001" { try testShouldCompile(std.testing.allocator, "sc041_ghc_real_world_001"); }
test "should_compile: sc042_ghc_real_world_002" { try testShouldCompile(std.testing.allocator, "sc042_ghc_real_world_002"); }
test "should_compile: sc043_infix_constructors_in_types" { try testShouldCompile(std.testing.allocator, "sc043_infix_constructors_in_types"); }

// ── should_fail test declarations ─────────────────────────────────────────

test "should_fail: sf001_missing_where" { try testShouldFail(std.testing.allocator, "sf001_missing_where"); }
test "should_fail: sf002_unclosed_paren" { try testShouldFail(std.testing.allocator, "sf002_unclosed_paren"); }
test "should_fail: sf003_bad_operator" { try testShouldFail(std.testing.allocator, "sf003_bad_operator"); }
test "should_fail: sf004_missing_equals" { try testShouldFail(std.testing.allocator, "sf004_missing_equals"); }
test "should_fail: sf005_bad_layout" { try testShouldFail(std.testing.allocator, "sf005_bad_layout"); }
test "should_fail: sf006_unclosed_brace" { try testShouldFail(std.testing.allocator, "sf006_unclosed_brace"); }
test "should_fail: sf007_data_no_constructors" { try testShouldFail(std.testing.allocator, "sf007_data_no_constructors"); }
test "should_fail: sf008_class_no_name" { try testShouldFail(std.testing.allocator, "sf008_class_no_name"); }
test "should_fail: sf009_lambda_no_arrow" { try testShouldFail(std.testing.allocator, "sf009_lambda_no_arrow"); }
test "should_fail: sf010_case_no_of" { try testShouldFail(std.testing.allocator, "sf010_case_no_of"); }
test "should_fail: sf011_reserved_as_var" { try testShouldFail(std.testing.allocator, "sf011_reserved_as_var"); }
test "should_fail: sf012_if_missing_else" { try testShouldFail(std.testing.allocator, "sf012_if_missing_else"); }
test "should_fail: sf013_double_dcolon" { try testShouldFail(std.testing.allocator, "sf013_double_dcolon"); }
test "should_fail: sf014_bad_constructor_name" { try testShouldFail(std.testing.allocator, "sf014_bad_constructor_name"); }
test "should_fail: sf015_let_no_in" { try testShouldFail(std.testing.allocator, "sf015_let_no_in"); }
test "should_fail: sf016_import_bad_syntax" { try testShouldFail(std.testing.allocator, "sf016_import_bad_syntax"); }
test "should_fail: sf017_forall_no_dot" { try testShouldFail(std.testing.allocator, "sf017_forall_no_dot"); }
test "should_fail: sf018_unclosed_string" { try testShouldFail(std.testing.allocator, "sf018_unclosed_string"); }
test "should_fail: sf019_missing_module_name" { try testShouldFail(std.testing.allocator, "sf019_missing_module_name"); }
