//! rhc — Rusholme Haskell Compiler CLI.
//!
//! Usage:
//!   rhc parse <file.hs>    Parse a Haskell file and print the AST
//!   rhc check <file.hs>    Parse, rename, and typecheck; print inferred types
//!   rhc --help             Show this help message
//!   rhc --version          Show version information

const std = @import("std");
const Io = std.Io;
const Dir = Io.Dir;
const File = Io.File;

const rusholme = @import("rusholme");
const Lexer = rusholme.frontend.lexer.Lexer;
const LayoutProcessor = rusholme.frontend.layout.LayoutProcessor;
const Parser = rusholme.frontend.parser.Parser;
const PrettyPrinter = rusholme.frontend.pretty.PrettyPrinter;
const TerminalRenderer = rusholme.diagnostics.terminal.TerminalRenderer;
const DiagnosticCollector = rusholme.diagnostics.diagnostic.DiagnosticCollector;
const FileId = rusholme.FileId;
const renamer_mod = rusholme.renamer.renamer;
const infer_mod = rusholme.tc.infer;
const htype_mod = rusholme.tc.htype;

const version = "0.1.0";

pub fn main(init: std.process.Init) !void {
    const allocator = init.gpa;
    const io = init.io;
    const arena_alloc = init.arena.allocator();

    // Parse command-line arguments.
    const args = try init.minimal.args.toSlice(arena_alloc);

    // Skip argv[0] (the program name).
    const user_args = if (args.len > 0) args[1..] else args;

    if (user_args.len == 0) {
        try printUsage(io);
        std.process.exit(1);
    }

    const command = user_args[0];

    if (std.mem.eql(u8, command, "--help") or std.mem.eql(u8, command, "-h")) {
        try printUsage(io);
        return;
    }

    if (std.mem.eql(u8, command, "--version") or std.mem.eql(u8, command, "-v")) {
        try printVersion(io);
        return;
    }

    if (std.mem.eql(u8, command, "parse")) {
        const cmd_args = user_args[1..];
        if (cmd_args.len == 0) {
            try writeStderr(io, "rhc parse: missing file argument\n");
            try writeStderr(io, "Usage: rhc parse <file.hs>\n");
            std.process.exit(1);
        }
        const file_path = cmd_args[0];
        try cmdParse(allocator, io, file_path);
        return;
    }

    if (std.mem.eql(u8, command, "check")) {
        const cmd_args = user_args[1..];
        if (cmd_args.len == 0) {
            try writeStderr(io, "rhc check: missing file argument\n");
            try writeStderr(io, "Usage: rhc check <file.hs>\n");
            std.process.exit(1);
        }
        const file_path = cmd_args[0];
        try cmdCheck(allocator, io, file_path);
        return;
    }

    // Unknown command.
    var stderr_buf: [4096]u8 = undefined;
    var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
    const stderr = &stderr_fw.interface;
    try stderr.print("rhc: unknown command '{s}'\n", .{command});
    try stderr.print("Run 'rhc --help' for usage information.\n", .{});
    try stderr.flush();
    std.process.exit(1);
}

/// Parse a Haskell source file and either pretty-print the AST or show errors.
fn cmdParse(allocator: std.mem.Allocator, io: Io, file_path: []const u8) !void {
    // Read the source file.
    const source = readSourceFile(allocator, io, file_path) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        switch (err) {
            error.FileNotFound => try stderr.print("rhc: file not found: {s}\n", .{file_path}),
            error.AccessDenied => try stderr.print("rhc: permission denied: {s}\n", .{file_path}),
            else => try stderr.print("rhc: cannot read file '{s}': {}\n", .{ file_path, err }),
        }
        try stderr.flush();
        std.process.exit(1);
    };
    defer allocator.free(source);

    // Set up the frontend pipeline: Lexer -> Layout -> Parser.
    const file_id: FileId = 1;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    var lexer = Lexer.init(arena_alloc, source, file_id);
    var layout = LayoutProcessor.init(arena_alloc, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena_alloc);

    var parser = Parser.init(arena_alloc, &layout, &diags) catch {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    };

    const module = parser.parseModule() catch {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    };

    // Check for accumulated diagnostics even on "success" (warnings, etc).
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // Pretty-print the AST to stdout.
    var pp = PrettyPrinter.init(arena_alloc);
    defer pp.deinit();
    const output = try pp.printModule(module);
    defer arena_alloc.free(output);

    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    const stdout = &stdout_fw.interface;
    try stdout.writeAll(output);
    // Ensure trailing newline.
    if (output.len > 0 and output[output.len - 1] != '\n') {
        try stdout.writeByte('\n');
    }
    try stdout.flush();
}

/// Parse, rename, and typecheck a Haskell source file.
/// Prints each top-level binding's inferred type to stdout as `name :: type`.
/// Prints structured diagnostics to stderr on any error.
fn cmdCheck(allocator: std.mem.Allocator, io: Io, file_path: []const u8) !void {
    const source = readSourceFile(allocator, io, file_path) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        switch (err) {
            error.FileNotFound => try stderr.print("rhc: file not found: {s}\n", .{file_path}),
            error.AccessDenied => try stderr.print("rhc: permission denied: {s}\n", .{file_path}),
            else => try stderr.print("rhc: cannot read file '{s}': {}\n", .{ file_path, err }),
        }
        try stderr.flush();
        std.process.exit(1);
    };
    defer allocator.free(source);

    const file_id: FileId = 1;

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    // ── Parse ──────────────────────────────────────────────────────────
    var lexer = Lexer.init(arena_alloc, source, file_id);
    var layout = LayoutProcessor.init(arena_alloc, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena_alloc);

    var parser = Parser.init(arena_alloc, &layout, &diags) catch {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    };

    const module = parser.parseModule() catch {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    };

    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Rename ─────────────────────────────────────────────────────────
    var u_supply = rusholme.naming.unique.UniqueSupply{};
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags);
    defer rename_env.deinit();

    const renamed = try renamer_mod.rename(module, &rename_env);

    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Typecheck ──────────────────────────────────────────────────────
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(arena_alloc);
    try rusholme.tc.env.initBuiltins(&ty_env, arena_alloc, &u_supply);

    var infer_ctx = infer_mod.InferCtx.init(arena_alloc, &ty_env, &mv_supply, &u_supply, &diags);
    var module_types = try infer_mod.inferModule(&infer_ctx, renamed);
    defer module_types.deinit(arena_alloc);

    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Print results ──────────────────────────────────────────────────
    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    const stdout = &stdout_fw.interface;

    // Walk declarations in source order to print types in a predictable order.
    for (renamed.declarations) |decl| {
        switch (decl) {
            .FunBind => |fb| {
                const scheme = module_types.get(fb.name.unique) orelse continue;
                const ty_str = try htype_mod.prettyScheme(scheme, arena_alloc);
                try stdout.print("{s} :: {s}\n", .{ fb.name.base, ty_str });
            },
            else => {},
        }
    }

    try stdout.flush();
}

/// Render all collected diagnostics to stderr using the terminal renderer.
fn renderDiagnostics(
    allocator: std.mem.Allocator,
    io: Io,
    diags: *DiagnosticCollector,
    file_id: FileId,
    file_path: []const u8,
    source: []const u8,
) !void {
    // Build the lookup tables needed by the terminal renderer.
    var path_lookup = std.AutoHashMap(FileId, []const u8).init(allocator);
    defer path_lookup.deinit();
    try path_lookup.put(file_id, file_path);

    var file_contents = std.AutoHashMap(FileId, []const u8).init(allocator);
    defer file_contents.deinit();
    try file_contents.put(file_id, source);

    const renderer = TerminalRenderer.init(&path_lookup, &file_contents);

    var stderr_buf: [4096]u8 = undefined;
    var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
    const stderr = &stderr_fw.interface;

    // Sort diagnostics by location for deterministic output.
    const sorted = diags.getAll(allocator) catch diags.diagnostics.items;
    defer if (sorted.ptr != diags.diagnostics.items.ptr) allocator.free(sorted);

    for (sorted) |diag| {
        try renderer.render(stderr, diag);
    }

    // Print error count summary.
    const err_count = diags.errorCount();
    if (err_count > 0) {
        try stderr.print("rhc: aborting due to {d} error{s}\n", .{
            err_count,
            if (err_count == 1) "" else "s",
        });
    }
    try stderr.flush();
}

/// Read a source file from disk into an owned allocation.
fn readSourceFile(allocator: std.mem.Allocator, io: Io, path: []const u8) ![]u8 {
    const file = try Dir.openFile(.cwd(), io, path, .{});
    defer file.close(io);

    var read_buf: [8192]u8 = undefined;
    var rdr = file.reader(io, &read_buf);
    return try rdr.interface.allocRemaining(allocator, .limited(10 * 1024 * 1024));
}

fn printUsage(io: Io) !void {
    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    const stdout = &stdout_fw.interface;
    try stdout.writeAll(
        \\rhc — Rusholme Haskell Compiler
        \\
        \\Usage:
        \\  rhc parse <file.hs>    Parse a Haskell file and pretty-print the AST
        \\  rhc check <file.hs>    Parse, rename, and typecheck; print inferred types
        \\  rhc --help             Show this help message
        \\  rhc --version          Show version information
        \\
    );
    try stdout.flush();
}

fn printVersion(io: Io) !void {
    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    const stdout = &stdout_fw.interface;
    try stdout.print("rhc {s}\n", .{version});
    try stdout.flush();
}

fn writeStderr(io: Io, msg: []const u8) !void {
    var stderr_buf: [4096]u8 = undefined;
    var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
    const stderr = &stderr_fw.interface;
    try stderr.writeAll(msg);
    try stderr.flush();
}

test "simple test" {
    const gpa = std.testing.allocator;
    var list: std.ArrayList(i32) = .empty;
    defer list.deinit(gpa);
    try list.append(gpa, 42);
    try std.testing.expectEqual(@as(i32, 42), list.pop());
}
