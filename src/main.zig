//! rhc — Rusholme Haskell Compiler CLI.
//!
//! Usage:
//!   rhc parse <file.hs>    Parse a Haskell file and print the AST
//!   rhc check <file.hs>    Parse, rename, and typecheck; print inferred types
//!   rhc core <file.hs>     Parse, typecheck, and desugar; print Core IR
//!   rhc grin <file.hs>     Full pipeline; print GRIN IR
//!   rhc ll <file.hs>       Full pipeline; emit LLVM IR
//!   rhc build [--backend <kind>] [-o <out>] <file.hs>
//!                          Full pipeline; compile to native executable
//!                          Backends: native (default), graalvm, wasm, c
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

/// Get the path to the RTS library baked in at compile time.
/// Returns the path to librts.a that should be linked into executables.
fn getRtsLibPath() []const u8 {
    return @embedFile("rts_lib_path");
}

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

    if (std.mem.eql(u8, command, "core")) {
        const cmd_args = user_args[1..];
        if (cmd_args.len == 0) {
            try writeStderr(io, "rhc core: missing file argument\n");
            try writeStderr(io, "Usage: rhc core <file.hs>\n");
            std.process.exit(1);
        }
        const file_path = cmd_args[0];
        try cmdCore(allocator, io, file_path);
        return;
    }

    if (std.mem.eql(u8, command, "grin")) {
        const cmd_args = user_args[1..];
        if (cmd_args.len == 0) {
            try writeStderr(io, "rhc grin: missing file argument\n");
            try writeStderr(io, "Usage: rhc grin <file.hs>\n");
            std.process.exit(1);
        }
        const file_path = cmd_args[0];
        try cmdGrin(allocator, io, file_path);
        return;
    }

    if (std.mem.eql(u8, command, "ll")) {
        const cmd_args = user_args[1..];
        if (cmd_args.len == 0) {
            try writeStderr(io, "rhc ll: missing file argument\n");
            try writeStderr(io, "Usage: rhc ll <file.hs>\n");
            std.process.exit(1);
        }
        const file_path = cmd_args[0];
        try cmdLl(allocator, io, file_path);
        return;
    }

    if (std.mem.eql(u8, command, "build")) {
        const cmd_args = user_args[1..];
        if (cmd_args.len == 0) {
            try writeStderr(io, "rhc build: missing file argument\n");
            try writeStderr(io, "Usage: rhc build [--backend <kind>] [-o <output>] <file.hs> [<file2.hs> ...]\n");
            std.process.exit(1);
        }
        // Parse optional flags: -o <output>, --backend <kind>; collect file paths.
        var output_name: ?[]const u8 = null;
        var file_paths: std.ArrayListUnmanaged([]const u8) = .{};
        var backend_kind = rusholme.backend.backend_mod.BackendKind.native;
        var i: usize = 0;
        while (i < cmd_args.len) : (i += 1) {
            if (std.mem.eql(u8, cmd_args[i], "-o")) {
                i += 1;
                if (i >= cmd_args.len) {
                    try writeStderr(io, "rhc build: -o requires an argument\n");
                    try writeStderr(io, "Usage: rhc build [--backend <kind>] [-o <output>] <file.hs> [<file2.hs> ...]\n");
                    std.process.exit(1);
                }
                output_name = cmd_args[i];
            } else if (std.mem.eql(u8, cmd_args[i], "--backend")) {
                i += 1;
                if (i >= cmd_args.len) {
                    try writeStderr(io, "rhc build: --backend requires an argument\n");
                    try writeStderr(io, "Usage: rhc build [--backend <kind>] [-o <output>] <file.hs> [<file2.hs> ...]\n");
                    std.process.exit(1);
                }
                backend_kind = rusholme.backend.backend_mod.parseBackendKind(cmd_args[i]) orelse {
                    var stderr_buf: [4096]u8 = undefined;
                    var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
                    const stderr = &stderr_fw.interface;
                    try stderr.print("rhc build: unknown backend '{s}'\n", .{cmd_args[i]});
                    try stderr.print("Valid backends: native, graalvm, wasm, c\n", .{});
                    try stderr.flush();
                    std.process.exit(1);
                };
            } else {
                try file_paths.append(arena_alloc, cmd_args[i]);
            }
        }
        if (file_paths.items.len == 0) {
            try writeStderr(io, "rhc build: missing file argument\n");
            try writeStderr(io, "Usage: rhc build [--backend <kind>] [-o <output>] <file.hs> [<file2.hs> ...]\n");
            std.process.exit(1);
        }
        // Derive output name from the first file when -o is not given.
        const out = output_name orelse std.fs.path.stem(std.fs.path.basename(file_paths.items[0]));
        try cmdBuild(allocator, io, file_paths.items, out, backend_kind);
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
    layout.setDiagnostics(&diags);

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
    layout.setDiagnostics(&diags);

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

/// Parse, check, and desugar a Haskell source file to Core IR.
/// Prints the resulting Core IR to stdout.
fn cmdCore(allocator: std.mem.Allocator, io: Io, file_path: []const u8) !void {
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

    var lexer = Lexer.init(arena_alloc, source, file_id);
    var layout = LayoutProcessor.init(arena_alloc, &lexer);
    var diags = DiagnosticCollector.init();
    defer diags.deinit(arena_alloc);
    layout.setDiagnostics(&diags);

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

    var u_supply = rusholme.naming.unique.UniqueSupply{};
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags);
    defer rename_env.deinit();
    const renamed = try renamer_mod.rename(module, &rename_env);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

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

    // ── Desugar ────────────────────────────────────────────────────────
    const core_prog = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Pretty-print ───────────────────────────────────────────────────
    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    var stdout = &stdout_fw.interface;

    var pp = rusholme.core.pretty.CorePrinter(*Io.Writer).init(stdout);
    try stdout.print("=== Core Program ({} data, {} bindings) ===\n", .{ core_prog.data_decls.len, core_prog.binds.len });
    try pp.printProgram(core_prog);
    try stdout.print("\n", .{});

    try stdout.flush();
}

/// Parse, check, desugar, lambda-lift, and translate to GRIN IR.
/// Prints the resulting GRIN IR to stdout.
fn cmdGrin(allocator: std.mem.Allocator, io: Io, file_path: []const u8) !void {
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
    layout.setDiagnostics(&diags);

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

    // ── Desugar ────────────────────────────────────────────────────────
    const core_prog = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Lambda lift ────────────────────────────────────────────────────
    const core_lifted = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Translate to GRIN ───────────────────────────────────────────────
    const grin_prog = try rusholme.grin.translate.translateProgram(arena_alloc, core_lifted);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Pretty-print ───────────────────────────────────────────────────
    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    var stdout = &stdout_fw.interface;

    var pp = rusholme.grin.pretty.GrinPrinter(*Io.Writer).init(stdout);
    try stdout.print("=== GRIN Program ({} defs) ===\n", .{grin_prog.defs.len});
    try pp.printProgram(grin_prog);
    try stdout.print("\n", .{});

    try stdout.flush();
}

/// Parse, check, desugar, lambda-lift, translate to GRIN IR, and emit LLVM IR.
/// Prints the resulting LLVM IR to stdout.
fn cmdLl(allocator: std.mem.Allocator, io: Io, file_path: []const u8) !void {
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
    layout.setDiagnostics(&diags);

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

    // ── Desugar ────────────────────────────────────────────────────────
    const core_prog = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Lambda lift ────────────────────────────────────────────────────
    const core_lifted = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Translate to GRIN ───────────────────────────────────────────────
    const grin_prog = try rusholme.grin.translate.translateProgram(arena_alloc, core_lifted);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }
    // ── Translate to LLVM ──────────────────────────────────────────────
    var translator = rusholme.backend.grin_to_llvm.GrinTranslator.init(arena_alloc);
    defer translator.deinit();

    const llvm_ir = translator.translateProgram(grin_prog) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM codegen failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    defer arena_alloc.free(llvm_ir);

    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    const stdout = &stdout_fw.interface;
    try stdout.writeAll(llvm_ir);
    if (llvm_ir.len > 0 and llvm_ir[llvm_ir.len - 1] != '\n') {
        try stdout.writeByte('\n');
    }
    try stdout.flush();
}

/// Full pipeline: parse, rename, typecheck, desugar (for each module in
/// topological order), merge, lambda-lift, translate to GRIN, emit LLVM
/// object code, and link into a native executable.
///
/// `file_paths` is a list of `.hs` source files to compile.  When multiple
/// files are given, the compiler builds a module graph, determines the
/// topological order, and compiles each module in turn using `CompileEnv`
/// so that cross-module names and types are available to downstream modules.
///
/// Only the `native` backend is fully implemented. Other backends are stubs
/// that will be fleshed out in follow-up issues.
fn cmdBuild(allocator: std.mem.Allocator, io: Io, file_paths: []const []const u8, output_name: []const u8, backend_kind: rusholme.backend.backend_mod.BackendKind) !void {
    // Dispatch non-native backends early; only `native` is implemented.
    switch (backend_kind) {
        .native => {}, // handled below
        .graalvm, .wasm, .c => {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc build: backend '{s}' is not yet implemented\n", .{
                rusholme.backend.backend_mod.backendName(backend_kind),
            });
            try stderr.flush();
            std.process.exit(1);
        },
    }

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    // ── Read all source files ──────────────────────────────────────────
    const compile_env_mod = rusholme.modules.compile_env;
    var source_modules: std.ArrayListUnmanaged(compile_env_mod.SourceModule) = .{};
    for (file_paths, 0..) |fp, idx| {
        const source = readSourceFile(arena_alloc, io, fp) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            switch (err) {
                error.FileNotFound => try stderr.print("rhc: file not found: {s}\n", .{fp}),
                error.AccessDenied => try stderr.print("rhc: permission denied: {s}\n", .{fp}),
                else => try stderr.print("rhc: cannot read file '{s}': {}\n", .{ fp, err }),
            }
            try stderr.flush();
            std.process.exit(1);
        };
        const mod_name = try rusholme.modules.module_graph.inferModuleName(arena_alloc, fp);
        try source_modules.append(arena_alloc, .{
            .module_name = mod_name,
            .source = source,
            .file_id = @intCast(idx + 1),
        });
    }

    // ── Compile all modules via CompileEnv ─────────────────────────────
    var session_result = try compile_env_mod.compileProgram(arena_alloc, io, source_modules.items);
    var session = &session_result.env;
    defer session.deinit();

    if (session_result.result.had_errors) {
        try renderMultiFileDiagnostics(allocator, io, &session.diags);
        std.process.exit(1);
    }

    const core_prog = session_result.result.core;

    // ── Lambda lift ────────────────────────────────────────────────────
    const core_lifted = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog);

    // ── Translate to GRIN ───────────────────────────────────────────────
    const grin_prog = try rusholme.grin.translate.translateProgram(arena_alloc, core_lifted);

    // ── Translate to LLVM ──────────────────────────────────────────────
    var translator = rusholme.backend.grin_to_llvm.GrinTranslator.init(arena_alloc);
    defer translator.deinit();

    const llvm_module = translator.translateProgramToModule(grin_prog) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM codegen failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

    // ── Emit object file ───────────────────────────────────────────────
    const llvm = rusholme.backend.llvm;
    const machine = llvm.createNativeTargetMachine() catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to create target machine: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    defer llvm.disposeTargetMachine(machine);

    llvm.setModuleDataLayout(llvm_module, machine);
    llvm.setModuleTriple(llvm_module);

    const obj_path = try std.fmt.allocPrint(arena_alloc, "{s}.o", .{output_name});

    llvm.emitObjectFile(machine, llvm_module, obj_path) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to emit object file: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

    // ── Link ───────────────────────────────────────────────────────────
    // Include the RTS library (librts.a) which provides rts_alloc,
    // rts_store_field, rts_load_field, etc.
    const rts_lib_path = getRtsLibPath();
    const linker = rusholme.backend.linker.Linker{
        .objects = &.{obj_path},
        .system_libs = &.{"c"},
        .runtime_objects = &.{rts_lib_path},
        .output_path = output_name,
    };

    linker.link(allocator, io) catch |err| {
        Dir.deleteFile(.cwd(), io, obj_path) catch {};
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: linking failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

    Dir.deleteFile(.cwd(), io, obj_path) catch {};
}

/// Render diagnostics from a multi-file compilation (no source text available).
///
/// Used by `cmdBuild` after `compileProgram`, which accumulates diagnostics
/// across multiple source files.  Without per-file source text we fall back
/// to printing the raw diagnostic messages.
fn renderMultiFileDiagnostics(
    allocator: std.mem.Allocator,
    io: Io,
    diags: *DiagnosticCollector,
) !void {
    var stderr_buf: [4096]u8 = undefined;
    var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
    const stderr = &stderr_fw.interface;

    const sorted = diags.getAll(allocator) catch diags.diagnostics.items;
    defer if (sorted.ptr != diags.diagnostics.items.ptr) allocator.free(sorted);

    for (sorted) |diag| {
        const sev = switch (diag.severity) {
            .@"error" => "error",
            .warning => "warning",
            .info => "info",
            .hint => "hint",
        };
        try stderr.print("{s}[{s}]: {s}\n", .{ sev, diag.code.code(), diag.message });
    }

    const err_count = diags.errorCount();
    if (err_count > 0) {
        try stderr.print("rhc: aborting due to {d} error{s}\n", .{
            err_count,
            if (err_count == 1) "" else "s",
        });
    }
    try stderr.flush();
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
        \\  rhc core <file.hs>     Parse, typecheck, and desugar; print Core IR
        \\  rhc grin <file.hs>     Full pipeline; print GRIN IR
        \\  rhc ll <file.hs>       Full pipeline; emit LLVM IR
        \\  rhc build [--backend <kind>] [-o <out>] <file.hs>
        \\                         Full pipeline; compile to an executable
        \\                         Backends: native (default), graalvm, wasm, c
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
