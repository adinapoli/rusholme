//! rhc — Rusholme Haskell Compiler CLI.
//!
//! Usage:
//!   rhc parse <file.hs>    Parse a Haskell file and print the AST
//!   rhc check <file.hs>    Parse, rename, and typecheck; print inferred types
//!   rhc core <file.hs>     Parse, typecheck, and desugar; print Core IR
//!   rhc grin <file.hs>     Full pipeline; print GRIN IR
//!   rhc ll <file.hs>       Full pipeline; emit LLVM IR
//!   rhc build [--backend <kind>] [-o <out>] [--package-db <path>] <file.hs>
//!                          Full pipeline; compile to native executable.
//!                          Backends: native (default), jit, wasm, c.
//!                          --package-db may be given multiple times; paths
//!                          are searched in order for pre-built .rhi files.
//!   rhc repl               Interactive REPL (read-eval-print loop)
//!   rhc pkg <subcommand>   Package management (list, describe, install, …)
//!   rhc --help             Show this help message
//!   rhc --version          Show version information

const std = @import("std");
const Io = std.Io;
const Dir = Io.Dir;
const File = Io.File;

const clap = @import("clap");

// ── Subcommand dispatch ───────────────────────────────────────────────────────

/// All top-level subcommands recognised by rhc.
const SubCommand = enum {
    parse,
    check,
    core,
    grin,
    ll,
    repl,
    build,
    pkg,
};

/// Custom parser set that maps the `<command>` positional type to `SubCommand`.
const main_parsers = .{
    .command = clap.parsers.enumeration(SubCommand),
};

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

pub const VERSION = "0.1.0";

// For --version flag (maintain backwards compatibility)
const version_display = VERSION;

/// Get the path to the native RTS library baked in at compile time.
/// Returns the path to librts.a that should be linked into native executables.
fn getRtsLibPath() []const u8 {
    return @embedFile("rts_lib_path");
}

/// Get the path to the WASM RTS library baked in at compile time.
/// Returns the path to librts_wasm.a that is linked into WASM binaries.
fn getWasmRtsLibPath() []const u8 {
    return @embedFile("wasm_rts_lib_path");
}

/// Get the path to the WASM compiler-rt library baked in at compile time.
/// Returns the path to libcompiler_rt_wasm.a that provides 128-bit arithmetic
/// builtins (__divti3, __modti3, etc.) required by the WASM RTS.
fn getWasmCompilerRtLibPath() []const u8 {
    return @embedFile("wasm_compiler_rt_lib_path");
}

/// Get the path to the JIT backend RTS LLVM bitcode baked in at compile time.
/// Returns the path to rts_jit.bc which is merged with program bitcode
/// in-process so that lli can resolve rts_alloc, rts_putStrLn, etc.
fn getJitRtsBcPath() []const u8 {
    return @embedFile("jit_rts_bc_path");
}

/// Get the path to the JIT backend compiler-rt LLVM bitcode baked in at compile time.
/// Provides __zig_probe_stack, __divti3, and other builtins that the Zig RTS
/// references but which are normally resolved by the system linker.
fn getJitCompilerRtBcPath() []const u8 {
    return @embedFile("jit_compiler_rt_bc_path");
}

/// Get the path to the Prelude source file baked in at compile time.
/// Returns the path to lib/Prelude.hs that is compiled before user modules.
fn getPreludePath() []const u8 {
    return @embedFile("prelude_path");
}

pub fn main(init: std.process.Init) !void {
    const allocator = init.gpa;
    const io = init.io;
    const arena_alloc = init.arena.allocator();

    const args = try init.minimal.args.toSlice(arena_alloc);
    const user_args = if (args.len > 0) args[1..] else args;

    // ── Top-level: global flags + subcommand ─────────────────────────────────
    const top_params = comptime clap.parseParamsComptime(
        \\-h, --help     Display this help and exit.
        \\    --version  Display version information and exit.
        \\<command>
        \\
    );

    var it = clap.args.SliceIterator{ .args = user_args };
    var top_diag = clap.Diagnostic{};
    var top = clap.parseEx(clap.Help, &top_params, main_parsers, &it, .{
        .allocator = arena_alloc,
        .diagnostic = &top_diag,
        .terminating_positional = 0,
    }) catch |err| {
        try top_diag.reportToFile(io, .stderr(), err);
        std.process.exit(1);
    };
    defer top.deinit();

    if (top.args.help != 0) {
        var buf: [4096]u8 = undefined;
        var fw: File.Writer = .init(.stdout(), io, &buf);
        try clap.help(&fw.interface, clap.Help, &top_params, .{});
        try fw.interface.flush();
        return;
    }

    if (top.args.version != 0) {
        try printVersion(io);
        return;
    }

    const subcommand: SubCommand = top.positionals[0] orelse {
        var buf: [4096]u8 = undefined;
        var fw: File.Writer = .init(.stderr(), io, &buf);
        try clap.usage(&fw.interface, clap.Help, &top_params);
        try fw.interface.flush();
        std.process.exit(1);
    };

    // ── Shared params for single-file subcommands ─────────────────────────────
    //
    // parse, check, core, grin, ll all accept exactly one <file.hs> argument.
    const file_params = comptime clap.parseParamsComptime(
        \\-h, --help  Display this help and exit.
        \\<str>
        \\
    );

    switch (subcommand) {
        .parse, .check, .core, .grin, .ll => {
            var file_diag = clap.Diagnostic{};
            var file_res = clap.parseEx(clap.Help, &file_params, clap.parsers.default, &it, .{
                .allocator = arena_alloc,
                .diagnostic = &file_diag,
            }) catch |err| {
                try file_diag.reportToFile(io, .stderr(), err);
                std.process.exit(1);
            };
            defer file_res.deinit();

            if (file_res.args.help != 0) {
                var buf: [4096]u8 = undefined;
                var fw: File.Writer = .init(.stdout(), io, &buf);
                try clap.help(&fw.interface, clap.Help, &file_params, .{});
                try fw.interface.flush();
                return;
            }

            const file_path = file_res.positionals[0] orelse {
                try writeStderr(io, "rhc ");
                try writeStderr(io, @tagName(subcommand));
                try writeStderr(io, ": missing file argument\n");
                std.process.exit(1);
            };

            switch (subcommand) {
                .parse => return cmdParse(allocator, io, file_path),
                .check => return cmdCheck(allocator, io, file_path),
                .core  => return cmdCore(allocator, io, file_path),
                .grin  => return cmdGrin(allocator, io, file_path),
                .ll    => return cmdLl(allocator, io, file_path),
                else   => unreachable,
            }
        },

        .repl => {
            const repl_params = comptime clap.parseParamsComptime(
                \\-h, --help    Display this help and exit.
                \\    --server  Run in JSON-RPC server mode.
                \\
            );
            var repl_diag = clap.Diagnostic{};
            var repl_res = clap.parseEx(clap.Help, &repl_params, clap.parsers.default, &it, .{
                .allocator = arena_alloc,
                .diagnostic = &repl_diag,
            }) catch |err| {
                try repl_diag.reportToFile(io, .stderr(), err);
                std.process.exit(1);
            };
            defer repl_res.deinit();

            if (repl_res.args.help != 0) {
                var buf: [4096]u8 = undefined;
                var fw: File.Writer = .init(.stdout(), io, &buf);
                try clap.help(&fw.interface, clap.Help, &repl_params, .{});
                try fw.interface.flush();
                return;
            }
            return cmdRepl(allocator, io, repl_res.args.server != 0);
        },

        .build => {
            const build_params = comptime clap.parseParamsComptime(
                \\-h, --help                   Display this help and exit.
                \\-o, --output <str>           Output file name (default: stem of first input).
                \\    --backend <str>          Backend: native (default), jit, wasm, c.
                \\    --package-db <str>...    Package database path (may be repeated).
                \\    --repl                   Compile for REPL use (internal).
                \\<str>...
                \\
            );
            var build_diag = clap.Diagnostic{};
            var build_res = clap.parseEx(clap.Help, &build_params, clap.parsers.default, &it, .{
                .allocator = arena_alloc,
                .diagnostic = &build_diag,
            }) catch |err| {
                try build_diag.reportToFile(io, .stderr(), err);
                std.process.exit(1);
            };
            defer build_res.deinit();

            if (build_res.args.help != 0) {
                var buf: [4096]u8 = undefined;
                var fw: File.Writer = .init(.stdout(), io, &buf);
                try clap.help(&fw.interface, clap.Help, &build_params, .{});
                try fw.interface.flush();
                return;
            }

            const file_paths = build_res.positionals[0];
            if (file_paths.len == 0) {
                try writeStderr(io, "rhc build: missing file argument\n");
                std.process.exit(1);
            }

            const backend_kind = if (build_res.args.backend) |b_str|
                rusholme.backend.backend_mod.parseBackendKind(b_str) orelse {
                    var buf: [512]u8 = undefined;
                    var fw: File.Writer = .init(.stderr(), io, &buf);
                    try fw.interface.print(
                        "rhc build: unknown backend '{s}'\nValid backends: native, jit, wasm, c\n",
                        .{b_str},
                    );
                    try fw.interface.flush();
                    std.process.exit(1);
                }
            else
                rusholme.backend.backend_mod.BackendKind.native;

            const out = build_res.args.output orelse
                std.fs.path.stem(std.fs.path.basename(file_paths[0]));

            return cmdBuild(
                allocator,
                io,
                file_paths,
                out,
                backend_kind,
                build_res.args.repl != 0,
                build_res.args.@"package-db",
            );
        },

        .pkg => {
            return rusholme.packages.pkg_cmd.cmdPkg(allocator, io, &it);
        },
    }
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
    const no_implicit_prelude = module.language_extensions.contains(.NoImplicitPrelude);
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags, no_implicit_prelude);
    defer rename_env.deinit();

    // ── Load Prelude before user rename ───────────────────────────────
    // The Prelude must be compiled and its bindings accumulated BEFORE
    // the user's module is renamed, so that Prelude symbols are in scope
    // during renaming.
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(arena_alloc);
    try rusholme.tc.env.initBuiltins(&ty_env, arena_alloc, &u_supply, no_implicit_prelude);

    // Respect the NoImplicitPrelude language extension: only load Prelude
    // when the user has NOT enabled NoImplicitPrelude.
    var prelude_result: ?PreludeResult = null;
    if (!no_implicit_prelude) {
        // Load the Prelude so its functions/operators are available for renaming.
        // Non-fatal: on failure the check continues with built-in names only.
        var pipeline_check = rusholme.repl.pipeline.Pipeline.init(arena_alloc, io);
        prelude_result = loadPrelude(arena_alloc, io, &pipeline_check, &u_supply, &rename_env, &ty_env, &mv_supply, &diags) catch null;
    }

    const renamed = try renamer_mod.rename(module, &rename_env);

    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Typecheck ──────────────────────────────────────────────────────
    var infer_ctx = infer_mod.InferCtx.init(arena_alloc, &ty_env, &mv_supply, &u_supply, &diags);
    // Seed class env with Prelude's class declarations and instances (#645).
    if (prelude_result) |pr| {
        try infer_ctx.class_env.mergeFrom(&pr.class_env);
    }
    var module_types = try infer_mod.inferModule(&infer_ctx, renamed, null);
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
    const no_implicit_prelude = module.language_extensions.contains(.NoImplicitPrelude);
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags, no_implicit_prelude);
    defer rename_env.deinit();

    // ── Load Prelude before user rename ───────────────────────────────
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(arena_alloc);
    try rusholme.tc.env.initBuiltins(&ty_env, arena_alloc, &u_supply, no_implicit_prelude);

    // Respect the NoImplicitPrelude language extension: only load Prelude
    // when the user has NOT enabled NoImplicitPrelude.
    var prelude_result: ?PreludeResult = null;
    if (!no_implicit_prelude) {
        var pipeline_core = rusholme.repl.pipeline.Pipeline.init(arena_alloc, io);
        prelude_result = loadPrelude(arena_alloc, io, &pipeline_core, &u_supply, &rename_env, &ty_env, &mv_supply, &diags) catch null;
    }

    const renamed = try renamer_mod.rename(module, &rename_env);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    var infer_ctx = infer_mod.InferCtx.init(arena_alloc, &ty_env, &mv_supply, &u_supply, &diags);
    if (prelude_result) |pr| {
        try infer_ctx.class_env.mergeFrom(&pr.class_env);
    }
    var module_types = try infer_mod.inferModule(&infer_ctx, renamed, null);
    defer module_types.deinit(arena_alloc);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Desugar ────────────────────────────────────────────────────────
    const ext_dict_names: ?*const rusholme.core.desugar.DesugarCtx.DictNameMap = if (prelude_result) |*pr| &pr.dict_names else null;
    const desugar_result = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply, ext_dict_names);
    const core_prog = desugar_result.program;
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
    const no_implicit_prelude = module.language_extensions.contains(.NoImplicitPrelude);
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags, no_implicit_prelude);
    defer rename_env.deinit();

    // ── Load Prelude before user rename ───────────────────────────────
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(arena_alloc);
    try rusholme.tc.env.initBuiltins(&ty_env, arena_alloc, &u_supply, no_implicit_prelude);

    // Respect the NoImplicitPrelude language extension: only load Prelude
    // when the user has NOT enabled NoImplicitPrelude.
    var prelude_result: ?PreludeResult = null;
    if (!no_implicit_prelude) {
        var pipeline_grin = rusholme.repl.pipeline.Pipeline.init(arena_alloc, io);
        prelude_result = loadPrelude(arena_alloc, io, &pipeline_grin, &u_supply, &rename_env, &ty_env, &mv_supply, &diags) catch null;
    }

    const renamed = try renamer_mod.rename(module, &rename_env);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Typecheck ──────────────────────────────────────────────────────
    var infer_ctx = infer_mod.InferCtx.init(arena_alloc, &ty_env, &mv_supply, &u_supply, &diags);
    if (prelude_result) |pr| {
        try infer_ctx.class_env.mergeFrom(&pr.class_env);
    }
    var module_types = try infer_mod.inferModule(&infer_ctx, renamed, null);
    defer module_types.deinit(arena_alloc);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Desugar ────────────────────────────────────────────────────────
    const ext_dict_names: ?*const rusholme.core.desugar.DesugarCtx.DictNameMap = if (prelude_result) |*pr| &pr.dict_names else null;
    const desugar_result = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply, ext_dict_names);
    const core_prog = desugar_result.program;
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Lambda lift ────────────────────────────────────────────────────
    const ext_scope_1 = try collectExternalScope(arena_alloc, &module_types);
    const lift_result_1 = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog, ext_scope_1, 0);
    const core_lifted = lift_result_1.program;
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Translate to GRIN ───────────────────────────────────────────────
    const grin_prog = try rusholme.grin.translate.translateProgram(arena_alloc, core_lifted, null, null);
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
    const no_implicit_prelude = module.language_extensions.contains(.NoImplicitPrelude);
    var rename_env = try renamer_mod.RenameEnv.init(arena_alloc, &u_supply, &diags, no_implicit_prelude);
    defer rename_env.deinit();

    // ── Load Prelude before user rename ───────────────────────────────
    var mv_supply = htype_mod.MetaVarSupply{};
    var ty_env = try rusholme.tc.env.TyEnv.init(arena_alloc);
    try rusholme.tc.env.initBuiltins(&ty_env, arena_alloc, &u_supply, no_implicit_prelude);

    // Respect the NoImplicitPrelude language extension: only load Prelude
    // when the user has NOT enabled NoImplicitPrelude.
    var prelude_result: ?PreludeResult = null;
    if (!no_implicit_prelude) {
        var pipeline_ll = rusholme.repl.pipeline.Pipeline.init(arena_alloc, io);
        prelude_result = loadPrelude(arena_alloc, io, &pipeline_ll, &u_supply, &rename_env, &ty_env, &mv_supply, &diags) catch null;
    }

    const renamed = try renamer_mod.rename(module, &rename_env);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Typecheck ──────────────────────────────────────────────────────
    var infer_ctx = infer_mod.InferCtx.init(arena_alloc, &ty_env, &mv_supply, &u_supply, &diags);
    if (prelude_result) |pr| {
        try infer_ctx.class_env.mergeFrom(&pr.class_env);
    }
    var module_types = try infer_mod.inferModule(&infer_ctx, renamed, null);
    defer module_types.deinit(arena_alloc);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Desugar ────────────────────────────────────────────────────────
    const ext_dict_names: ?*const rusholme.core.desugar.DesugarCtx.DictNameMap = if (prelude_result) |*pr| &pr.dict_names else null;
    const desugar_result = try rusholme.core.desugar.desugarModule(arena_alloc, renamed, &module_types, &diags, &u_supply, ext_dict_names);
    const core_prog = desugar_result.program;
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Lambda lift ────────────────────────────────────────────────────
    const ext_scope_2 = try collectExternalScope(arena_alloc, &module_types);
    const lift_result_2 = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog, ext_scope_2, 0);
    const core_lifted = lift_result_2.program;
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }

    // ── Translate to GRIN ───────────────────────────────────────────────
    const grin_prog = try rusholme.grin.translate.translateProgram(arena_alloc, core_lifted, null, null);
    if (diags.hasErrors()) {
        try renderDiagnostics(allocator, io, &diags, file_id, file_path, source);
        std.process.exit(1);
    }
    // ── Translate to LLVM ──────────────────────────────────────────────
    var registry = rusholme.backend.grin_to_llvm.TagRegistry.init();
    defer registry.deinit(arena_alloc);
    var translator = rusholme.backend.grin_to_llvm.GrinTranslator.init(arena_alloc, &registry);
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
/// topological order), merge, lambda-lift, translate to GRIN, emit to target
/// backend.
///
/// `file_paths` is a list of `.hs` source files to compile.  When multiple
/// files are given, the compiler builds a module graph, determines the
/// topological order, and compiles each module in turn using `CompileEnv`
/// so that cross-module names and types are available to downstream modules.
///
/// Launch the interactive REPL.
fn cmdRepl(allocator: std.mem.Allocator, io: Io, server_mode: bool) !void {
    if (server_mode) {
        try rusholme.repl.cli.runServer(allocator, io);
    } else {
        try rusholme.repl.cli.run(allocator, io);
    }
}

/// Load and compile the Prelude module, accumulating its bindings into
/// the rename and type environments. Returns error if loading fails
/// but makes a best-effort to continue execution (Prelude loading is
/// non-fatal, preserving CLI usability).
/// Result of loading the Prelude, carrying the class environment and
/// dictionary names so that downstream commands can seed their InferCtx
/// and desugarer with Prelude-provided class instances.
const PreludeResult = struct {
    class_env: rusholme.tc.class_env.ClassEnv,
    dict_names: rusholme.core.desugar.DesugarCtx.DictNameMap,
};

fn loadPrelude(
    arena_alloc: std.mem.Allocator,
    io: Io,
    pipeline: *rusholme.repl.pipeline.Pipeline,
    u_supply: *rusholme.naming.unique.UniqueSupply,
    rename_env: *renamer_mod.RenameEnv,
    ty_env: *rusholme.tc.env.TyEnv,
    mv_supply: *htype_mod.MetaVarSupply,
    diags: *DiagnosticCollector,
) !PreludeResult {
    const prelude_path = getPreludePath();

    // Push scope frames for Prelude bindings (so they persist across parsing).
    rename_env.scope.push() catch return .{
        .class_env = rusholme.tc.class_env.ClassEnv.init(arena_alloc),
        .dict_names = .empty,
    };
    errdefer rename_env.scope.pop();

    ty_env.push() catch {
        rename_env.scope.pop();
        return .{
            .class_env = rusholme.tc.class_env.ClassEnv.init(arena_alloc),
            .dict_names = .empty,
        };
    };
    errdefer ty_env.pop();

    const prelude_source = readSourceFile(arena_alloc, io, prelude_path) catch |err| {
        // error.FileNotFound is non-fatal — we continue without Prelude
        // The errdefer will clean up scopes for us
        if (err == error.FileNotFound) return .{
            .class_env = rusholme.tc.class_env.ClassEnv.init(arena_alloc),
            .dict_names = .empty,
        };
        return err;
    };

    const result = try pipeline.compileModule(
        prelude_source,
        0, // file_id 0 for Prelude
        u_supply,
        rename_env,
        ty_env,
        mv_supply,
        diags,
        null, // no external arities yet
        null, // no external con_map yet
        null, // no external class_env yet
        null, // no external dict_names yet
        null, // no external type_con_names yet
    );
    // Prelude bindings are now accumulated in rename_env and ty_env.
    // Return the class env and dict names so callers can seed their
    // InferCtx and desugarer with Prelude-provided instances (#645).
    return .{
        .class_env = result.class_env,
        .dict_names = result.dict_names,
    };
}

/// Supports the following backends:
/// - native: compiles to native executable via LLVM
/// - wasm: compiles to WebAssembly binary (.wasm)
/// - jit, c: not yet implemented
fn cmdBuild(allocator: std.mem.Allocator, io: Io, file_paths: []const []const u8, output_name: []const u8, backend_kind: rusholme.backend.backend_mod.BackendKind, is_repl: bool, package_dbs: []const []const u8) !void {
    // REPL mode placeholder - for WASM backend compiles stateful REPL
    _ = is_repl;

    // ── Compile program and translate to GRIN ───────────────────────────
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    const compile_env_mod = rusholme.modules.compile_env;
    var source_modules: std.ArrayListUnmanaged(compile_env_mod.SourceModule) = .{};

    // ── Auto-prepend Prelude unless the user explicitly passed it ────────
    // Check if any user-provided file is the Prelude module.
    var user_provides_prelude = false;
    for (file_paths) |fp| {
        const mod_name = try rusholme.modules.module_graph.inferModuleName(arena_alloc, fp);
        if (std.mem.eql(u8, mod_name, "Prelude")) {
            user_provides_prelude = true;
            break;
        }
    }

    // File ID 0 is reserved for the Prelude; user modules start at 1.
    var next_file_id: u32 = 0;

    if (!user_provides_prelude) {
        const prelude_path = getPreludePath();
        if (readSourceFile(arena_alloc, io, prelude_path)) |prelude_source| {
            try source_modules.append(arena_alloc, .{
                .module_name = "Prelude",
                .source = prelude_source,
                .file_id = next_file_id,
                .source_path = prelude_path,
            });
            next_file_id += 1;
        } else |err| {
            // Prelude not found is non-fatal in development; warn and continue
            // without implicit Prelude compilation. User modules will still
            // get wired-in names from populateWiredIn/initBuiltins.
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            switch (err) {
                error.FileNotFound => try stderr.print("rhc: warning: Prelude not found at '{s}'; using built-in names only\n", .{prelude_path}),
                else => try stderr.print("rhc: warning: cannot read Prelude '{s}': {}; using built-in names only\n", .{ prelude_path, err }),
            }
            try stderr.flush();
        }
    }

    for (file_paths) |fp| {
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
            .file_id = next_file_id,
        });
        next_file_id += 1;
    }

    var session_result = try compile_env_mod.compileProgram(arena_alloc, io, source_modules.items, package_dbs);
    var session = &session_result.env;
    defer session.deinit();

    if (session_result.result.had_errors) {
        try renderMultiFileDiagnostics(allocator, io, &session.diags);
        std.process.exit(1);
    }

    const module_order = session_result.result.module_order;

    // ── Per-module lambda lift + GRIN translation ───────────────────────
    // Each Haskell module is lambda-lifted and GRIN-translated independently.
    // The per-module GRIN programs are collected for global tag table
    // construction and for per-module LLVM emission.
    // Collect all top-level binding uniques across all modules so that the
    // lambda lifter for any single module treats cross-module references as
    // globally in-scope (not free variables).
    var all_binding_ids = std.ArrayListUnmanaged(u64){};
    {
        var prog_it = session.programs.valueIterator();
        while (prog_it.next()) |prog| {
            for (prog.binds) |bind| {
                switch (bind) {
                    .NonRec => |pair| try all_binding_ids.append(arena_alloc, pair.binder.name.unique.value),
                    .Rec => |pairs| {
                        for (pairs) |pair| try all_binding_ids.append(arena_alloc, pair.binder.name.unique.value);
                    },
                }
            }
        }
    }
    const cross_module_scope = try all_binding_ids.toOwnedSlice(arena_alloc);

    // Build a cross-module constructor map so that each module's GRIN
    // translation knows about data constructors declared in prior modules
    // (e.g. Prelude's `Just`, `Nothing`, `Left`, `Right`).
    //
    // Without this, a user module that applies `Just 42` would not find
    // `Just` in its local con_map and would emit a function call instead of
    // a heap Store — producing an undefined linker reference at link time.
    var cross_module_con_map = std.AutoHashMapUnmanaged(u64, u32){};
    defer cross_module_con_map.deinit(arena_alloc);

    var per_module_grin = std.ArrayListUnmanaged(rusholme.grin.ast.Program){};
    // Thread the lifted-function name counter across modules so that each
    // module's lifted functions get globally unique LLVM symbol names.
    var next_lift_id: u64 = 0;
    for (module_order) |mod_name| {
        const core_prog = session.programs.get(mod_name) orelse continue;
        const lift_result = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog, cross_module_scope, next_lift_id);
        next_lift_id = lift_result.next_lifted_id;
        const grin_prog = try rusholme.grin.translate.translateProgram(arena_alloc, lift_result.program, null, &cross_module_con_map);
        try per_module_grin.append(arena_alloc, grin_prog);

        // After translating this module, accumulate its constructor field
        // counts so that subsequent modules can use them as cross-module
        // constructors.  The field count is extracted from the CoreProgram's
        // data declarations, matching the REPL's accumulated_con_map logic.
        for (core_prog.data_decls) |decl| {
            for (decl.constructors) |con| {
                try cross_module_con_map.put(
                    arena_alloc,
                    con.name.unique.value,
                    rusholme.grin.translate.countConFields(con.ty),
                );
            }
        }
    }

    // ── Build merged GRIN for global tag table ──────────────────────────
    // The tag table must cover constructors from ALL modules because module B
    // may pattern-match on a constructor introduced in module A.
    var all_grin_defs = std.ArrayListUnmanaged(rusholme.grin.ast.Def){};
    for (per_module_grin.items) |prog| {
        try all_grin_defs.appendSlice(arena_alloc, prog.defs);
    }
    const all_grin = rusholme.grin.ast.Program{
        .defs = all_grin_defs.items,
        .field_types = .{},
        .arities = .{},
    };

    // ── Dispatch to backend-specific emission ─────────────────────────────
    switch (backend_kind) {
        .native => try emitNative(arena_alloc, io, session, module_order, per_module_grin.items, all_grin, output_name),
        .jit => try emitJit(arena_alloc, io, session, module_order, per_module_grin.items, all_grin, output_name),
        .wasm => try emitWasm(arena_alloc, io, session, module_order, per_module_grin.items, all_grin, output_name),
        .c => {
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
}

/// Emit native executable (the original cmdBuild logic).
fn emitNative(
    allocator: std.mem.Allocator,
    io: Io,
    session: *const rusholme.modules.compile_env.CompileEnv,
    module_order: []const []const u8,
    per_module_grin: []const rusholme.grin.ast.Program,
    all_grin: rusholme.grin.ast.Program,
    output_name: []const u8,
) !void {
    _ = session; // Unused for native backend
    const llvm = rusholme.backend.llvm;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    var registry = rusholme.backend.grin_to_llvm.TagRegistry.init();
    defer registry.deinit(arena_alloc);
    registry.registerDefsAndBodies(arena_alloc, all_grin.defs) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM tag table construction failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    registry.registerFieldTypes(arena_alloc, all_grin.field_types) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM field type registration failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    var translator = rusholme.backend.grin_to_llvm.GrinTranslator.init(arena_alloc, &registry);
    defer translator.deinit();

    // Translate each module to a separate LLVM module and emit its bitcode.
    // Per-module .bc files are durable artifacts (kept after linking).
    var llvm_modules = std.ArrayListUnmanaged(llvm.Module){};
    for (module_order, per_module_grin) |mod_name, grin_prog| {
        const llvm_mod = translator.translateModuleGrin(mod_name, grin_prog) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: LLVM codegen failed for module '{s}': {}\n", .{ mod_name, err });
            try stderr.flush();
            std.process.exit(1);
        };

        const bc_path = try std.fmt.allocPrint(arena_alloc, "{s}.bc", .{mod_name});
        llvm.writeBitcodeToFile(llvm_mod, bc_path) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: failed to write bitcode for module '{s}': {}\n", .{ mod_name, err });
            try stderr.flush();
            std.process.exit(1);
        };

        try llvm_modules.append(arena_alloc, llvm_mod);
    }

    // Emit the shared __rhc_force module.  Per-module code declares
    // __rhc_force as external; this module provides the definition.
    // The force module must be emitted after all per-module translations
    // so the tag table is fully populated with all F-tags.
    {
        const force_mod = translator.emitForceModule() catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: failed to emit __rhc_force module: {}\n", .{err});
            try stderr.flush();
            std.process.exit(1);
        };
        try llvm_modules.append(arena_alloc, force_mod);
    }

    // ── In-process bitcode linking ──────────────────────────────────────
    // Merge all per-module LLVM modules into one for object emission.
    // LLVMLinkModules2 disposes source modules; only the destination survives.
    const linked_mod: llvm.Module = if (llvm_modules.items.len == 1)
        llvm_modules.items[0]
    else blk: {
        const dest = llvm_modules.items[0];
        for (llvm_modules.items[1..]) |src| {
            llvm.linkModules(dest, src) catch |err| {
                var stderr_buf: [4096]u8 = undefined;
                var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
                const stderr = &stderr_fw.interface;
                try stderr.print("rhc: LLVM bitcode linking failed: {}\n", .{err});
                try stderr.flush();
                std.process.exit(1);
            };
        }
        break :blk dest;
    };

    // ── Emit object file ───────────────────────────────────────────────
    const machine = llvm.createNativeTargetMachine() catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to create target machine: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    defer llvm.disposeTargetMachine(machine);

    llvm.setModuleDataLayout(linked_mod, machine);
    llvm.setModuleTriple(linked_mod);

    const obj_path = try std.fmt.allocPrint(arena_alloc, "{s}.o", .{output_name});

    llvm.emitObjectFile(machine, linked_mod, obj_path) catch |err| {
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

    // Delete the temp .o (the .bc files are kept as durable artifacts).
    Dir.deleteFile(.cwd(), io, obj_path) catch {};
}

/// Emit LLVM IR for execution via lli (LLVM interpreter/JIT compiler).
///
/// The flow mirrors emitNative / emitWasm:
///   1. Translate each module's GRIN to LLVM IR.
///   2. Link LLVM modules in-process.
///   3. Set native data layout and triple.
///   4. Write combined program bitcode to a temp file.
///   5. Invoke llvm-link to merge program + RTS bitcode → final .bc artifact.
///   6. Clean up the intermediate program bitcode.
///
/// The final output is `{output_name}.bc` which can be run with:
///   lli {output_name}.bc
fn emitJit(
    allocator: std.mem.Allocator,
    io: Io,
    session: *const rusholme.modules.compile_env.CompileEnv,
    module_order: []const []const u8,
    per_module_grin: []const rusholme.grin.ast.Program,
    all_grin: rusholme.grin.ast.Program,
    output_name: []const u8,
) !void {
    _ = session;
    const llvm = rusholme.backend.llvm;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    var registry = rusholme.backend.grin_to_llvm.TagRegistry.init();
    defer registry.deinit(arena_alloc);
    registry.registerDefsAndBodies(arena_alloc, all_grin.defs) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM tag table construction failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    registry.registerFieldTypes(arena_alloc, all_grin.field_types) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM field type registration failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    var translator = rusholme.backend.grin_to_llvm.GrinTranslator.init(arena_alloc, &registry);
    defer translator.deinit();

    // ── Per-module LLVM translation ───────────────────────────────────────
    var llvm_modules = std.ArrayListUnmanaged(llvm.Module){};
    for (module_order, per_module_grin) |mod_name, grin_prog| {
        const llvm_mod = translator.translateModuleGrin(mod_name, grin_prog) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: LLVM codegen failed for JIT module '{s}': {}\n", .{ mod_name, err });
            try stderr.flush();
            std.process.exit(1);
        };
        try llvm_modules.append(arena_alloc, llvm_mod);
    }

    // Emit the shared __rhc_force module (same as native backend).
    {
        const force_mod = translator.emitForceModule() catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: failed to emit __rhc_force module: {}\n", .{err});
            try stderr.flush();
            std.process.exit(1);
        };
        try llvm_modules.append(arena_alloc, force_mod);
    }

    // ── In-process bitcode linking ──────────────────────────────────────
    const linked_mod: llvm.Module = if (llvm_modules.items.len == 1)
        llvm_modules.items[0]
    else blk: {
        const dest = llvm_modules.items[0];
        for (llvm_modules.items[1..]) |src| {
            llvm.linkModules(dest, src) catch |err| {
                var stderr_buf: [4096]u8 = undefined;
                var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
                const stderr = &stderr_fw.interface;
                try stderr.print("rhc: LLVM bitcode linking failed: {}\n", .{err});
                try stderr.flush();
                std.process.exit(1);
            };
        }
        break :blk dest;
    };

    // ── Set native target layout ────────────────────────────────────────
    // lli accepts bitcode/IR compiled for the host architecture.
    const machine = llvm.createNativeTargetMachine() catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to create target machine: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    defer llvm.disposeTargetMachine(machine);

    llvm.setModuleDataLayout(linked_mod, machine);
    llvm.setModuleTriple(linked_mod);

    // ── In-process RTS + compiler-rt bitcode linking ───────────────────
    // Parse the pre-built RTS and compiler-rt bitcode from disk and merge
    // them into the program module using LLVM's in-process linker.  This
    // avoids shelling out to llvm-link (which can fail on bitcode produced
    // by a different LLVM build — e.g. Zig's embedded LLVM vs Nix LLVM).
    const jit_rts_bc_path = getJitRtsBcPath();
    const rts_mod = llvm.parseBitcodeFile(jit_rts_bc_path) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to load RTS bitcode '{s}': {}\n", .{ jit_rts_bc_path, err });
        try stderr.flush();
        std.process.exit(1);
    };

    llvm.linkModules(linked_mod, rts_mod) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to link RTS bitcode: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

    const jit_compiler_rt_bc_path = getJitCompilerRtBcPath();
    const compiler_rt_mod = llvm.parseBitcodeFile(jit_compiler_rt_bc_path) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to load compiler-rt bitcode '{s}': {}\n", .{ jit_compiler_rt_bc_path, err });
        try stderr.flush();
        std.process.exit(1);
    };

    llvm.linkModules(linked_mod, compiler_rt_mod) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to link compiler-rt bitcode: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

    // ── Strip host-specific function attributes ──────────────────────
    // The Zig-compiled RTS/compiler-rt bitcode carries per-function
    // target-cpu and target-features attributes from the build host.
    // These can reference features unknown to the system lli, causing
    // noisy warnings.  Since lli JITs for the host anyway, the
    // attributes are unnecessary — strip them before emitting the IR.
    llvm.stripTargetAttributes(linked_mod);

    // ── Write final LLVM IR ────────────────────────────────────────────
    // We emit textual IR (.ll) rather than bitcode (.bc) because Zig
    // embeds its own LLVM build whose bitcode format may be incompatible
    // with the system's lli/llvm-link (even at the same version number).
    // Textual IR is portable across builds and lli accepts it directly.
    const final_ll_path = try std.fmt.allocPrint(arena_alloc, "{s}.ll", .{output_name});
    llvm.writeIRToFile(linked_mod, final_ll_path) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to write LLVM IR: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
}

/// Emit WebAssembly binary via the WASM backend.
fn emitWasm(
    allocator: std.mem.Allocator,
    io: Io,
    session: *const rusholme.modules.compile_env.CompileEnv,
    module_order: []const []const u8,
    per_module_grin: []const rusholme.grin.ast.Program,
    all_grin: rusholme.grin.ast.Program,
    output_name: []const u8,
) !void {
    _ = session; // Unused for WASM backend
    const llvm = rusholme.backend.llvm;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    var registry = rusholme.backend.grin_to_llvm.TagRegistry.init();
    defer registry.deinit(arena_alloc);
    registry.registerDefsAndBodies(arena_alloc, all_grin.defs) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM tag table construction failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    registry.registerFieldTypes(arena_alloc, all_grin.field_types) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM field type registration failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    var translator = rusholme.backend.grin_to_llvm.GrinTranslator.init(arena_alloc, &registry);
    defer translator.deinit();

    // ── Per-module LLVM translation ───────────────────────────────────────
    // For WASM, we translate each module separately (like native) and then
    // merge the bitcode before emission to WASI binary format.
    var llvm_modules = std.ArrayListUnmanaged(llvm.Module){};
    for (module_order, per_module_grin) |mod_name, grin_prog| {
        const llvm_mod = translator.translateModuleGrin(mod_name, grin_prog) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: LLVM codegen failed for WASM module '{s}': {}\n", .{ mod_name, err });
            try stderr.flush();
            std.process.exit(1);
        };
        try llvm_modules.append(arena_alloc, llvm_mod);
    }

    // Emit the shared __rhc_force module (same as native backend).
    {
        const force_mod = translator.emitForceModule() catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: failed to emit __rhc_force module: {}\n", .{err});
            try stderr.flush();
            std.process.exit(1);
        };
        try llvm_modules.append(arena_alloc, force_mod);
    }

    // ── In-process bitcode linking ──────────────────────────────────────
    // Merge all per-module LLVM modules into one for WASM emission.
    const linked_mod: llvm.Module = if (llvm_modules.items.len == 1)
        llvm_modules.items[0]
    else blk: {
        const dest = llvm_modules.items[0];
        for (llvm_modules.items[1..]) |src| {
            llvm.linkModules(dest, src) catch |err| {
                var stderr_buf: [4096]u8 = undefined;
                var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
                const stderr = &stderr_fw.interface;
                try stderr.print("rhc: LLVM bitcode linking failed: {}\n", .{err});
                try stderr.flush();
                std.process.exit(1);
            };
        }
        break :blk dest;
    };

    // ── Create target machine for WebAssembly ───────────────────────────
    const machine = llvm.createWasmTargetMachine() catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to create WebAssembly target machine: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };
    defer llvm.disposeTargetMachine(machine);

    // Set module target triple and data layout for WASM
    llvm.setModuleTargetTriple(linked_mod, "wasm32-wasi");
    llvm.setModuleDataLayout(linked_mod, machine);

    // ── Emit bitcode and link with wasm-ld ─────────────────────────────────
    // We use wasm-ld instead of direct emission to get proper WASI-compliant
    // memory exports. Direct LLVM emission creates `env::__linear_memory`
    // imports which WASI runtimes don't provide.
    // tracked in: https://github.com/adinapoli/rusholme/issues/474
    const bc_path = try std.fmt.allocPrint(arena_alloc, "{s}.bc", .{output_name});
    llvm.writeBitcodeToFile(linked_mod, bc_path) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to emit LLVM bitcode: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

    // ── Link with wasm-ld for WASI-compliant output ───────────────────────
    // Key flags:
    //   --export-memory: Export linear memory instead of importing it (issue #474)
    //   --no-entry: The RTS provides _start() which serves as the WASM start function
    //   --export-all: Export all symbols for runtime access
    //
    // The WASM RTS (librts_wasm.a) is linked explicitly so that rts_alloc,
    // rts_putStrLn, etc. are compiled into the module rather than imported
    // from an external host.  This removes the env::* undefined imports that
    // prevented WASI runtimes from instantiating the module.  (Issue #477.)
    const wasm_rts_lib_path = getWasmRtsLibPath();
    const wasm_compiler_rt_lib_path = getWasmCompilerRtLibPath();
    const wasm_ld_args = [_][]const u8{
        "wasm-ld",
        "--export-memory",
        "--no-entry",
        "--export-all",
        "-o",
        output_name,
        bc_path,
        wasm_rts_lib_path,
        wasm_compiler_rt_lib_path,
    };

    // Use std.process.run to execute wasm-ld
    const result = std.process.run(arena_alloc, io, .{
        .argv = &wasm_ld_args,
    }) catch |err| {
        Dir.deleteFile(.cwd(), io, bc_path) catch {};
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: failed to run wasm-ld: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

    // Clean up temp bitcode file
    Dir.deleteFile(.cwd(), io, bc_path) catch {};

    switch (result.term) {
        .exited => |code| if (code != 0) {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: wasm-ld failed with exit code {d}\n", .{code});
            if (result.stderr.len > 0) {
                try stderr.writeAll(result.stderr);
            }
            try stderr.flush();
            std.process.exit(1);
        },
        else => {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: wasm-ld terminated unexpectedly\n", .{});
            try stderr.flush();
            std.process.exit(1);
        },
    }
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

/// Collect unique IDs from the type environment's schemes map so that the
/// lambda lifter treats imported/Prelude names as globally in-scope rather
/// than capturing them as free variables of nested lambdas.
fn collectExternalScope(alloc: std.mem.Allocator, module_types: *const infer_mod.ModuleTypes) ![]const u64 {
    var ids = std.ArrayListUnmanaged(u64){};
    var it = module_types.schemes.iterator();
    while (it.next()) |entry| {
        try ids.append(alloc, entry.key_ptr.value);
    }
    return try ids.toOwnedSlice(alloc);
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

fn printVersion(io: Io) !void {
    var stdout_buf: [4096]u8 = undefined;
    var stdout_fw: File.Writer = .init(.stdout(), io, &stdout_buf);
    const stdout = &stdout_fw.interface;
    try stdout.print("rhc {s}\n", .{version_display});
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
