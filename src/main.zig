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
const deriving_mod = rusholme.deriving.deriving;
const infer_mod = rusholme.tc.infer;
const htype_mod = rusholme.tc.htype;

pub const VERSION = "0.1.0";

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

/// Get the path to the RHC.Prim source file baked in at compile time.
/// RHC.Prim is the innermost boot package and is compiled before Prelude.
fn getRhcPrimPath() []const u8 {
    return @embedFile("rhc_prim_path");
}

/// Get the path to the Data.Function source file baked in at compile time.
/// Compiled after RHC.Prim and before Prelude.
fn getDataFunctionPath() []const u8 {
    return @embedFile("data_function_path");
}

/// Get the path to the GHC.Base source file baked in at compile time.
/// Compiled after Data.Function and before Prelude.
fn getGhcBasePath() []const u8 {
    return @embedFile("ghc_base_path");
}

fn getDataListPath() []const u8 {
    return @embedFile("data_list_path");
}

fn getDataMaybePath() []const u8 {
    return @embedFile("data_maybe_path");
}

fn getDataEitherPath() []const u8 {
    return @embedFile("data_either_path");
}

fn getDataCharPath() []const u8 {
    return @embedFile("data_char_path");
}

fn getDataTuplePath() []const u8 {
    return @embedFile("data_tuple_path");
}

fn getDataOrdPath() []const u8 {
    return @embedFile("data_ord_path");
}

/// Get the default package-database path baked in at compile time.
/// Points at `zig-out/lib/rhc-store/` (or wherever
/// `-Ddefault-package-db=<path>` was set at build time).  Populated by
/// the stage-2 bootstrap step in `build.zig` with pre-built boot
/// module `.rhi`+`.bc` artifacts.  Prepended to the user's
/// `--package-db` list at startup so user `rhc build` invocations
/// resolve imports through cached interfaces.
///
/// At runtime the directory may not exist (clean tree, no
/// `zig build bootstrap` yet) — `tryLoadFromPackageDbs` swallows
/// missing-file errors as cache misses and falls back to the
/// auto-prepended source compilation path.
fn getDefaultPackageDb() []const u8 {
    return @embedFile("default_package_db");
}

/// Boot modules that the driver auto-prepends, in dependency order.
///
/// Mirror the layered Prelude per `docs/plans/2026-06-13-ghc-internal-base-split.md`:
///
///   RHC.Prim → Data.Function → GHC.Base
///     → Data.{List, Maybe, Either} → Prelude
///
/// Each entry pairs a declared module name with a callable that returns
/// the baked-in source path.  We use a callable rather than a path string
/// because `@embedFile` requires a compile-time-known import name.
const BootModule = struct {
    module_name: []const u8,
    pathFn: *const fn () []const u8,
};
const boot_modules = [_]BootModule{
    .{ .module_name = "RHC.Prim", .pathFn = getRhcPrimPath },
    .{ .module_name = "Data.Function", .pathFn = getDataFunctionPath },
    .{ .module_name = "GHC.Base", .pathFn = getGhcBasePath },
    .{ .module_name = "Data.List", .pathFn = getDataListPath },
    .{ .module_name = "Data.Maybe", .pathFn = getDataMaybePath },
    .{ .module_name = "Data.Either", .pathFn = getDataEitherPath },
    // Data.Char is not in the implicit Prelude (matches GHC: `Data.Char` is
    // explicit-import only).  We still source-prepend it so cross-references
    // and topo can resolve cleanly when user code does `import Data.Char`.
    .{ .module_name = "Data.Char", .pathFn = getDataCharPath },
    // Data.Tuple: pair accessors + curry/uncurry.  Like Data.Char,
    // not part of implicit Prelude — explicit import required.
    .{ .module_name = "Data.Tuple", .pathFn = getDataTuplePath },
    // Data.Ord: `clamp`, `Down` wrapper.  Explicit import only,
    // matching GHC.  `comparing` deferred pending typechecker fix
    // (#842).
    .{ .module_name = "Data.Ord", .pathFn = getDataOrdPath },
    .{ .module_name = "Prelude", .pathFn = getPreludePath },
};

pub fn main(init: std.process.Init) !void {
    const allocator = init.gpa;
    const io = init.io;
    const arena_alloc = init.arena.allocator();

    const args = try init.minimal.args.toSlice(arena_alloc);
    const user_args = if (args.len > 0) args[1..] else args;

    // ── Top-level: global flags + subcommand ─────────────────────────────────
    const top_params = comptime clap.parseParamsComptime(
        \\-h, --help        Display this help and exit.
        \\-v, --version     Display version information and exit.
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
            // Internal flags (e.g. `--repl`) are accepted by the parser but
            // omitted from `--help` output so they don't appear as user-facing
            // options. See issue #696.
            const build_params = comptime clap.parseParamsComptime(
                \\-h, --help                   Display this help and exit.
                \\-o, --output <str>           Output file name (default: stem of first input).
                \\-O, --opt-level <str>        Optimisation level: 0|1|2|3|s|z (default: 2 for native, 0 otherwise).
                \\    --backend <str>          Backend: native (default), jit, wasm, c.
                \\    --rts <str>              RTS heap backend: arena (default) or immix.
                \\    --package-db <str>...    Package database path (may be repeated).
                \\    --artifact-dir <str>     Write per-module .rhi+.bc artifacts to this dir; module name dots become subdirs.
                \\    --no-link                Skip the final link step; emit only per-module artifacts.
                \\    --no-boot                Skip auto-prepend of boot modules (RHC.Prim, Prelude, …).
                \\    --repl                   Compile for REPL use (internal).
                \\<str>...
                \\
            );
            // Keep in sync with `build_params` above: this slice MUST equal
            // `build_params` minus internal-only flags. zig-clap v0.11.0 has
            // no built-in hidden-parameter support, so we maintain two
            // comptime slices.
            const build_params_help = comptime clap.parseParamsComptime(
                \\-h, --help                   Display this help and exit.
                \\-o, --output <str>           Output file name (default: stem of first input).
                \\-O, --opt-level <str>        Optimisation level: 0|1|2|3|s|z (default: 2 for native, 0 otherwise).
                \\    --backend <str>          Backend: native (default), jit, wasm, c.
                \\    --rts <str>              RTS heap backend: arena (default) or immix.
                \\    --package-db <str>...    Package database path (may be repeated).
                \\    --artifact-dir <str>     Write per-module .rhi+.bc artifacts to this dir; module name dots become subdirs.
                \\    --no-link                Skip the final link step; emit only per-module artifacts.
                \\    --no-boot                Skip auto-prepend of boot modules (RHC.Prim, Prelude, …).
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
                try clap.help(&fw.interface, clap.Help, &build_params_help, .{});
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

            // Parse `-O <level>` if supplied; otherwise pick the per-backend
            // default. Native binaries default to `-O2` so that compute-bound
            // microbenchmarks aren't sandbagged by the unoptimised mid-level
            // pipeline (epic #754, Track A1).  Other backends keep `-O0` for
            // fast iteration / debug builds.
            const opt_level: rusholme.backend.llvm.OptLevel = if (build_res.args.@"opt-level") |level_str|
                rusholme.backend.llvm.OptLevel.parse(level_str) orelse {
                    var buf: [512]u8 = undefined;
                    var fw: File.Writer = .init(.stderr(), io, &buf);
                    try fw.interface.print(
                        "rhc build: invalid optimisation level '{s}'\nValid levels: 0, 1, 2, 3, s, z\n",
                        .{level_str},
                    );
                    try fw.interface.flush();
                    std.process.exit(1);
                }
            else switch (backend_kind) {
                .native => rusholme.backend.llvm.OptLevel.O2,
                .jit, .wasm, .c => rusholme.backend.llvm.OptLevel.O0,
            };

            const rts_backend: rusholme.backend.grin_to_llvm.RtsBackend = if (build_res.args.rts) |rts_str|
                rusholme.backend.grin_to_llvm.RtsBackend.parse(rts_str) orelse {
                    var buf: [512]u8 = undefined;
                    var fw: File.Writer = .init(.stderr(), io, &buf);
                    try fw.interface.print(
                        "rhc build: unknown RTS backend '{s}'\nValid backends: arena, immix\n",
                        .{rts_str},
                    );
                    try fw.interface.flush();
                    std.process.exit(1);
                }
            else
                rusholme.backend.grin_to_llvm.RtsBackend.arena;

            return cmdBuild(
                allocator,
                io,
                file_paths,
                out,
                backend_kind,
                build_res.args.repl != 0,
                build_res.args.@"package-db",
                opt_level,
                rts_backend,
                build_res.args.@"artifact-dir",
                build_res.args.@"no-link" != 0,
                build_res.args.@"no-boot" != 0,
            );
        },

        .pkg => {
            return rusholme.packages.pkg_cmd.cmdPkg(allocator, io, it.args[it.index..]);
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

    var module = parser.parseModule() catch {
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
    try rusholme.tc.env.initBuiltins(&ty_env, &u_supply, no_implicit_prelude);

    // Respect the NoImplicitPrelude language extension: only load Prelude
    // when the user has NOT enabled NoImplicitPrelude.
    var prelude_result: ?PreludeResult = null;
    if (!no_implicit_prelude) {
        // Load the Prelude so its functions/operators are available for renaming.
        // Non-fatal: on failure the check continues with built-in names only.
        var pipeline_check = rusholme.repl.pipeline.Pipeline.init(arena_alloc, io);
        prelude_result = loadPrelude(arena_alloc, io, &pipeline_check, &u_supply, &rename_env, &ty_env, &mv_supply, &diags) catch null;
    }

    try deriving_mod.derive(arena_alloc, &module, &diags);
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
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    const compile_env_mod = rusholme.modules.compile_env;

    // Compile the user file against the full boot Prelude stack (same path as
    // `rhc build`), so Prelude symbols like `show`/`++` resolve and the dumped
    // Core reflects what the compiler actually produces. `rhc core` assumes the
    // implicit Prelude; NoImplicitPrelude programs are not specially handled.
    const source_modules = try assembleSourceModules(arena_alloc, io, &.{file_path}, false, null);

    var effective_pkg_dbs: std.ArrayListUnmanaged([]const u8) = .empty;
    const default_db = getDefaultPackageDb();
    if (default_db.len > 0) try effective_pkg_dbs.append(arena_alloc, default_db);

    var session_result = try compile_env_mod.compileProgram(arena_alloc, io, source_modules, effective_pkg_dbs.items);
    var session = &session_result.env;
    defer session.deinit();
    if (session_result.result.had_errors) {
        try renderMultiFileDiagnostics(allocator, io, &session.diags);
        std.process.exit(1);
    }

    // ── Pretty-print the merged whole-program Core ─────────────────────
    const core_prog = session_result.result.core;
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
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    const compile_env_mod = rusholme.modules.compile_env;

    // Compile the user file against the full boot Prelude stack so Prelude
    // symbols resolve (see `cmdCore` / `assembleSourceModules`).
    const source_modules = try assembleSourceModules(arena_alloc, io, &.{file_path}, false, null);

    var effective_pkg_dbs: std.ArrayListUnmanaged([]const u8) = .empty;
    const default_db = getDefaultPackageDb();
    if (default_db.len > 0) try effective_pkg_dbs.append(arena_alloc, default_db);

    var session_result = try compile_env_mod.compileProgram(arena_alloc, io, source_modules, effective_pkg_dbs.items);
    var session = &session_result.env;
    defer session.deinit();
    if (session_result.result.had_errors) {
        try renderMultiFileDiagnostics(allocator, io, &session.diags);
        std.process.exit(1);
    }

    // ── Lambda lift + translate the merged whole-program Core to GRIN ──
    // The merged Core is self-contained (boot stack is source-compiled into
    // it), so there is no external scope.
    const lift_result = try rusholme.core.lift.lambdaLift(arena_alloc, session_result.result.core, null, 0);
    const grin_result = try rusholme.grin.translate.translateProgram(arena_alloc, lift_result.program, null, null, null, null, 0);
    const grin_prog = grin_result.program;

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
    var module = parser.parseModule() catch {
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
    try rusholme.tc.env.initBuiltins(&ty_env, &u_supply, no_implicit_prelude);

    // Respect the NoImplicitPrelude language extension: only load Prelude
    // when the user has NOT enabled NoImplicitPrelude.
    var prelude_result: ?PreludeResult = null;
    if (!no_implicit_prelude) {
        var pipeline_ll = rusholme.repl.pipeline.Pipeline.init(arena_alloc, io);
        prelude_result = loadPrelude(arena_alloc, io, &pipeline_ll, &u_supply, &rename_env, &ty_env, &mv_supply, &diags) catch null;
    }

    try deriving_mod.derive(arena_alloc, &module, &diags);
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
    const grin_result = try rusholme.grin.translate.translateProgram(arena_alloc, core_lifted, null, null, null, null, 0);
    const grin_prog = grin_result.program;
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
        null, // single-module loadPrelude: no shared SpecialiseEnv
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
/// Assemble the source-module list a multi-module compile needs: the boot
/// Prelude stack (`RHC.Prim` → … → `Prelude`, in dependency order, skipping any
/// the user shadows by module name) followed by the user's own files, with
/// monotonic `file_id`s (boot modules take the low IDs).
///
/// Shared by `cmdBuild` and the IR-dump subcommands so they all see the full
/// layered Prelude — without it, dumps compiled a user file against only
/// `lib/Prelude.hs`, leaving `show`, `++`, etc. unbound.
///
/// `artifact_dir` only affects whether boot modules carry a `source_path` (used
/// to auto-write `.rhi`); pass `null` for dumps. A missing boot module warns and
/// is skipped; an unreadable user file is fatal (exits).
fn assembleSourceModules(
    arena_alloc: std.mem.Allocator,
    io: Io,
    file_paths: []const []const u8,
    no_boot: bool,
    artifact_dir: ?[]const u8,
) std.mem.Allocator.Error![]rusholme.modules.compile_env.SourceModule {
    const compile_env_mod = rusholme.modules.compile_env;
    var source_modules: std.ArrayListUnmanaged(compile_env_mod.SourceModule) = .empty;

    var user_module_names: std.StringHashMapUnmanaged(void) = .empty;
    for (file_paths) |fp| {
        const mod_name = try rusholme.modules.module_graph.inferModuleName(arena_alloc, fp);
        try user_module_names.put(arena_alloc, mod_name, {});
    }

    var next_file_id: u32 = 0;
    if (!no_boot) {
        for (boot_modules) |boot| {
            if (user_module_names.contains(boot.module_name)) continue;
            const boot_path = boot.pathFn();
            if (readSourceFile(arena_alloc, io, boot_path)) |boot_source| {
                try source_modules.append(arena_alloc, .{
                    .module_name = boot.module_name,
                    .source = boot_source,
                    .file_id = next_file_id,
                    .source_path = if (artifact_dir == null) boot_path else null,
                });
                next_file_id += 1;
            } else |err| {
                var stderr_buf: [4096]u8 = undefined;
                var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
                const stderr = &stderr_fw.interface;
                switch (err) {
                    error.FileNotFound => stderr.print("rhc: warning: boot module '{s}' not found at '{s}'; using built-in names only\n", .{ boot.module_name, boot_path }) catch {},
                    else => stderr.print("rhc: warning: cannot read boot module '{s}' at '{s}': {}; using built-in names only\n", .{ boot.module_name, boot_path, err }) catch {},
                }
                stderr.flush() catch {};
            }
        }
    }

    for (file_paths) |fp| {
        const source = readSourceFile(arena_alloc, io, fp) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            switch (err) {
                error.FileNotFound => stderr.print("rhc: file not found: {s}\n", .{fp}) catch {},
                error.AccessDenied => stderr.print("rhc: permission denied: {s}\n", .{fp}) catch {},
                else => stderr.print("rhc: cannot read file '{s}': {}\n", .{ fp, err }) catch {},
            }
            stderr.flush() catch {};
            std.process.exit(1);
        };
        const mod_name = extractSourceModuleName(source) orelse
            try rusholme.modules.module_graph.inferModuleName(arena_alloc, fp);
        try source_modules.append(arena_alloc, .{
            .module_name = mod_name,
            .source = source,
            .file_id = next_file_id,
        });
        next_file_id += 1;
    }

    return source_modules.toOwnedSlice(arena_alloc);
}

fn cmdBuild(
    allocator: std.mem.Allocator,
    io: Io,
    file_paths: []const []const u8,
    output_name: []const u8,
    backend_kind: rusholme.backend.backend_mod.BackendKind,
    is_repl: bool,
    package_dbs: []const []const u8,
    opt_level: rusholme.backend.llvm.OptLevel,
    rts_backend: rusholme.backend.grin_to_llvm.RtsBackend,
    artifact_dir: ?[]const u8,
    no_link: bool,
    no_boot: bool,
) !void {
    // REPL mode placeholder - for WASM backend compiles stateful REPL
    _ = is_repl;

    // ── Compile program and translate to GRIN ───────────────────────────
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const arena_alloc = arena.allocator();

    const compile_env_mod = rusholme.modules.compile_env;

    // Prepend the baked-in default package db so user `rhc build` picks up
    // pre-built boot artifacts without needing an explicit
    // `--package-db zig-out/lib/rhc-store` flag.  User-supplied
    // `--package-db` paths still take precedence on lookup ties because the
    // default is searched last (first-match-wins in tryLoadFromPackageDbs).
    var effective_pkg_dbs: std.ArrayListUnmanaged([]const u8) = .empty;
    try effective_pkg_dbs.appendSlice(arena_alloc, package_dbs);
    const default_db = getDefaultPackageDb();
    if (default_db.len > 0) try effective_pkg_dbs.append(arena_alloc, default_db);

    // Boot Prelude stack (unless `--no-boot`) + the user's files, with
    // monotonic file_ids. See `assembleSourceModules`. We still source-prepend
    // the boot stack even when `effective_pkg_dbs` carries `.rhi`/`.bc`
    // artifacts: the LLVM tag registry and `__rhc_force` module are built from
    // the *fresh* per-module GRIN, and cached modules contribute none, so a
    // cache-only force module would be incomplete and fail to link (full
    // cache-only codegen is tracked separately).
    const source_modules = try assembleSourceModules(arena_alloc, io, file_paths, no_boot, artifact_dir);

    var session_result = try compile_env_mod.compileProgram(arena_alloc, io, source_modules, effective_pkg_dbs.items);
    var session = &session_result.env;
    defer session.deinit();

    if (session_result.result.had_errors) {
        try renderMultiFileDiagnostics(allocator, io, &session.diags);
        std.process.exit(1);
    }

    // Render warnings (e.g. non-exhaustive patterns, #378) even when the
    // build succeeds. Errors were handled above, so anything left in the
    // collector is warning-severity only.
    if (session.diags.diagnostics.items.len > 0) {
        try renderMultiFileDiagnostics(allocator, io, &session.diags);
    }

    const module_order = session_result.result.module_order;

    // ── Store-mode `.rhi` export ────────────────────────────────────────
    // When `--artifact-dir` is given, write one `.rhi` per locally-compiled
    // module into the canonical store layout
    // (`<artifact_dir>/<Module/Path>.rhi`, dots → slashes).  Modules pulled
    // from `--package-db` already have their `.rhi` in the source db and
    // are skipped (they have no entry in `session.programs`).
    if (artifact_dir) |dir| {
        for (module_order) |mod_name| {
            if (session.programs.get(mod_name) == null) continue; // package-db hit
            const iface = session.ifaces.get(mod_name) orelse continue;
            // Prefer the source-declared `module Foo where` name over
            // the path-inferred one so `lib/rhc-prim/RHC/Prim.hs`
            // lands as `RHC/Prim.rhi`, not `lib/rhc-prim/RHC/Prim.rhi`
            // (mirrors the `.bc` stem logic in `emitNative`).
            const stem_name: []const u8 = if (session.parsed_modules.get(mod_name)) |parsed|
                parsed.module_name
            else
                mod_name;
            try writeArtifactRhi(arena_alloc, io, dir, stem_name, iface);
        }
    }

    // ── Whole-program dictionary specialisation (#807) ──────────────────
    // Resolve class-method dispatch through statically-known dictionaries
    // (e.g. `(<) dict$Ord$Int x y` → `primLtInt x y`) before lambda
    // lifting. The environment spans all modules because user code
    // references Prelude dictionaries.
    {
        const specialise = rusholme.core.specialise;
        var spec_env = specialise.SpecialiseEnv{};
        defer spec_env.deinit(arena_alloc);
        for (module_order) |mod_name| {
            const core_prog = session.programs.get(mod_name) orelse continue;
            try specialise.collectEnv(arena_alloc, &spec_env, core_prog);
        }
        for (module_order) |mod_name| {
            const prog_ptr = session.programs.getPtr(mod_name) orelse continue;
            prog_ptr.* = try specialise.specialiseProgram(arena_alloc, &spec_env, prog_ptr.*);
        }
    }

    // ── Whole-program demand (strictness) analysis (#802) ───────────────
    // Runs after specialisation so class-method calls are already direct
    // calls to instance methods (better strictness). The resulting
    // strict-parameter masks let GRIN translation pass strict arguments
    // eagerly instead of allocating F-tag thunks.
    const demand_info: *rusholme.core.demand.AnalysisResult = blk: {
        var all_progs = std.ArrayListUnmanaged(rusholme.core.ast.CoreProgram).empty;
        for (module_order) |mod_name| {
            const core_prog = session.programs.get(mod_name) orelse continue;
            try all_progs.append(arena_alloc, core_prog);
        }
        const info = try arena_alloc.create(rusholme.core.demand.AnalysisResult);
        info.* = try rusholme.core.demand.analyse(arena_alloc, all_progs.items);
        break :blk info;
    };
    const strict_params: ?*const rusholme.core.demand.StrictnessMap = &demand_info.masks;
    const strict_lets: ?*const rusholme.core.demand.LetSet = &demand_info.strict_lets;

    // ── Per-module lambda lift + GRIN translation ───────────────────────
    // Each Haskell module is lambda-lifted and GRIN-translated independently.
    // The per-module GRIN programs are collected for global tag table
    // construction and for per-module LLVM emission.
    // Collect all top-level binding uniques across all modules so that the
    // lambda lifter for any single module treats cross-module references as
    // globally in-scope (not free variables).
    var all_binding_ids = std.ArrayListUnmanaged(u64).empty;
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

    // Build a cross-module arity map so that each module's GRIN translation
    // knows the arity of functions defined in prior modules (e.g. Prelude's
    // `foldl`, `odd`).  Without this, a user module that partially applies
    // `foldl f z` emits a direct 2-argument App instead of a P-tag node,
    // and a bare `odd` value reference never becomes a P-tag wrapper —
    // both crash at runtime (#386, #764).
    var cross_module_arities = std.AutoHashMapUnmanaged(u64, u32){};
    defer cross_module_arities.deinit(arena_alloc);

    var per_module_grin = std.ArrayListUnmanaged(rusholme.grin.ast.Program).empty;
    // Thread the lifted-function name counter across modules so that each
    // module's lifted functions get globally unique LLVM symbol names.
    var next_lift_id: u64 = 0;
    // Thread the GRIN name counter across modules so that each module's
    // lifted thunk names (e.g. _thunk_18) get globally unique LLVM symbols.
    // Without this, two modules that both create 19 thunks would both emit
    // _thunk_18, causing a linker "symbol multiply defined" error (#812).
    var next_grin_name_counter: u64 = 0;
    for (module_order) |mod_name| {
        const core_prog = session.programs.get(mod_name) orelse continue;
        const lift_result = try rusholme.core.lift.lambdaLift(arena_alloc, core_prog, cross_module_scope, next_lift_id);
        next_lift_id = lift_result.next_lifted_id;
        const grin_result = try rusholme.grin.translate.translateProgram(arena_alloc, lift_result.program, &cross_module_arities, &cross_module_con_map, strict_params, strict_lets, next_grin_name_counter);
        next_grin_name_counter = grin_result.next_name_counter;
        const grin_prog = grin_result.program;
        try per_module_grin.append(arena_alloc, grin_prog);

        // Accumulate this module's function arities for subsequent modules
        // (mirrors the constructor-map accumulation below).
        var arity_it = grin_prog.arities.iterator();
        while (arity_it.next()) |entry| {
            try cross_module_arities.put(arena_alloc, entry.key_ptr.*, entry.value_ptr.*);
        }

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
    var all_grin_defs = std.ArrayListUnmanaged(rusholme.grin.ast.Def).empty;
    for (per_module_grin.items) |prog| {
        try all_grin_defs.appendSlice(arena_alloc, prog.defs);
    }
    const all_grin = rusholme.grin.ast.Program{
        .defs = all_grin_defs.items,
        .field_types = .{},
        .arities = .{},
    };

    // ── Dispatch to backend-specific emission ─────────────────────────────
    // `--artifact-dir` is only supported on the native backend for now.  JIT
    // and WASM paths emit bitcode shapes that aren't directly consumable as
    // store artifacts yet; the boot-store layout only needs native bitcode.
    if (artifact_dir != null and backend_kind != .native) {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc build: --artifact-dir requires --backend=native\n", .{});
        try stderr.flush();
        std.process.exit(1);
    }
    switch (backend_kind) {
        .native => try emitNative(arena_alloc, io, session, module_order, per_module_grin.items, all_grin, output_name, opt_level, rts_backend, strict_params, artifact_dir, no_link),
        .jit => try emitJit(arena_alloc, io, session, module_order, per_module_grin.items, all_grin, output_name, opt_level, rts_backend, strict_params),
        .wasm => try emitWasm(arena_alloc, io, session, module_order, per_module_grin.items, all_grin, output_name, opt_level, rts_backend, strict_params),
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
///
/// When `artifact_dir` is non-null, per-module `.bc` files are written into
/// `<artifact_dir>/<Module/Path>.bc` (dots → slashes) instead of the current
/// working directory.  When `no_link` is true, the final link step is
/// skipped — useful when emitting boot-package artifacts that have no
/// `main`.
fn emitNative(
    allocator: std.mem.Allocator,
    io: Io,
    session: *const rusholme.modules.compile_env.CompileEnv,
    module_order: []const []const u8,
    per_module_grin: []const rusholme.grin.ast.Program,
    all_grin: rusholme.grin.ast.Program,
    output_name: []const u8,
    opt_level: rusholme.backend.llvm.OptLevel,
    rts_backend: rusholme.backend.grin_to_llvm.RtsBackend,
    strict_params: ?*const rusholme.core.demand.StrictnessMap,
    artifact_dir: ?[]const u8,
    no_link: bool,
) !void {
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
    translator.rts_backend = rts_backend;
    translator.strict_params = strict_params;
    defer translator.deinit();

    // Translate each module to a separate LLVM module and emit its bitcode.
    // Per-module .bc files are durable artifacts (kept after linking).
    var llvm_modules = std.ArrayListUnmanaged(llvm.Module).empty;
    for (module_order, per_module_grin) |mod_name, grin_prog| {
        const llvm_mod = translator.translateModuleGrin(mod_name, grin_prog) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print("rhc: LLVM codegen failed for module '{s}': {}\n", .{ mod_name, err });
            try stderr.flush();
            std.process.exit(1);
        };

        // Opt-in IR verification (`RHC_VERIFY_LLVM=1`): structural
        // errors (broken dominance, type mismatches) fail loudly here
        // rather than silently miscompiling downstream. Not always-on
        // yet: the translator currently reuses cached function values
        // across `translateModuleGrin` calls, so multi-module builds
        // carry cross-context references that trip the verifier on
        // issues unrelated to the current change.
        // tracked in: https://github.com/adinapoli/rusholme/issues/815
        if (std.c.getenv("RHC_VERIFY_LLVM") != null) {
            llvm.verifyModule(llvm_mod) catch {
                var stderr_buf: [4096]u8 = undefined;
                var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
                const stderr = &stderr_fw.interface;
                try stderr.print("rhc: internal compiler error — LLVM IR verification failed for module '{s}'\n", .{mod_name});
                try stderr.flush();
                std.process.exit(1);
            };
        }

        // Prefer the source-declared module name (`module Foo where`) for
        // the on-disk `.bc` stem so that files given as absolute paths
        // (e.g. `/tmp/Foo.hs`) produce `Foo.bc` rather than the
        // path-mangled `.tmp.Foo.bc` `inferModuleName` would yield (#453).
        const bc_stem: []const u8 = if (session.parsed_modules.get(mod_name)) |parsed|
            parsed.module_name
        else
            mod_name;
        const bc_path = if (artifact_dir) |dir| blk: {
            const full_stem = try artifactStem(arena_alloc, dir, bc_stem);
            defer arena_alloc.free(full_stem);
            const p = try std.fmt.allocPrint(arena_alloc, "{s}.bc", .{full_stem});
            try ensureParentDirs(io, p);
            break :blk p;
        } else try std.fmt.allocPrint(arena_alloc, "{s}.bc", .{bc_stem});
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

    // ── Pull cached-module bitcode into the link ─────────────────────────
    // For every module that was resolved through `--package-db` *and*
    // was NOT also source-compiled (so `session.programs` has no
    // bindings for it), parse its sibling `.bc` and append to the
    // link set.  When source-prepend is active for a boot module its
    // fresh `.bc` already provides the symbols, so loading the cached
    // copy would yield "multiple definition" errors.  This filter
    // matters when the user explicitly opts out of source-prepend
    // (e.g. `rhc build --no-boot --package-db <store> …`).
    var bc_it = session.cached_bc_paths.iterator();
    while (bc_it.next()) |entry| {
        const mod_name = entry.key_ptr.*;
        if (session.programs.get(mod_name)) |prog| {
            if (prog.binds.len > 0 or prog.data_decls.len > 0) continue;
        }
        const bc_path = entry.value_ptr.*;
        const cached_mod = llvm.parseBitcodeFile(bc_path) catch |err| {
            var stderr_buf: [4096]u8 = undefined;
            var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
            const stderr = &stderr_fw.interface;
            try stderr.print(
                "rhc: failed to parse cached bitcode for module '{s}' at '{s}': {}\n",
                .{ mod_name, bc_path, err },
            );
            try stderr.flush();
            std.process.exit(1);
        };
        try llvm_modules.append(arena_alloc, cached_mod);
    }

    // `--no-link` mode: per-module `.bc` artifacts are the only output.
    // Skip the shared `__rhc_force` module (it covers only this build's tag
    // table, which is incomplete in a per-package build), the in-process
    // bitcode merge, object emission, and final linker invocation.  The
    // user's downstream `rhc build` rebuilds the force module with a full
    // cross-package tag table.
    if (no_link) return;

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

    // ── Create target machine at the requested optimisation level ──────
    const machine = llvm.createNativeTargetMachine(opt_level) catch |err| {
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

    // ── Run the LLVM mid-level optimiser (no-op at -O0) ────────────────
    // Without this, the back-end's `LLVMCodeGenOptLevel` setting alone
    // produces essentially unoptimised code, because the front-end IR
    // emitted by `grin_to_llvm` is highly redundant (every Bind becomes
    // a fresh alloca + load/store). Running the new pass manager here
    // is the difference between O0 and O2 output (epic #754, Track A1).
    llvm.runOptimizationPasses(linked_mod, machine, opt_level) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM optimisation pipeline failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

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
    opt_level: rusholme.backend.llvm.OptLevel,
    rts_backend: rusholme.backend.grin_to_llvm.RtsBackend,
    strict_params: ?*const rusholme.core.demand.StrictnessMap,
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
    translator.rts_backend = rts_backend;
    translator.strict_params = strict_params;
    defer translator.deinit();

    // ── Per-module LLVM translation ───────────────────────────────────────
    var llvm_modules = std.ArrayListUnmanaged(llvm.Module).empty;
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
    const machine = llvm.createNativeTargetMachine(opt_level) catch |err| {
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

    // ── Run the LLVM mid-level optimiser (no-op at -O0) ────────────────
    // The default for the JIT backend is `-O0` so this is normally a
    // no-op, but if the user passed `-O<n>` we honour it.
    llvm.runOptimizationPasses(linked_mod, machine, opt_level) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM optimisation pipeline failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

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
    opt_level: rusholme.backend.llvm.OptLevel,
    rts_backend: rusholme.backend.grin_to_llvm.RtsBackend,
    strict_params: ?*const rusholme.core.demand.StrictnessMap,
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
    translator.rts_backend = rts_backend;
    translator.strict_params = strict_params;
    defer translator.deinit();

    // ── Per-module LLVM translation ───────────────────────────────────────
    // For WASM, we translate each module separately (like native) and then
    // merge the bitcode before emission to WASI binary format.
    var llvm_modules = std.ArrayListUnmanaged(llvm.Module).empty;
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
    const machine = llvm.createWasmTargetMachine(opt_level) catch |err| {
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

    // ── Run the LLVM mid-level optimiser (no-op at -O0) ────────────────
    llvm.runOptimizationPasses(linked_mod, machine, opt_level) catch |err| {
        var stderr_buf: [4096]u8 = undefined;
        var stderr_fw: File.Writer = .init(.stderr(), io, &stderr_buf);
        const stderr = &stderr_fw.interface;
        try stderr.print("rhc: LLVM optimisation pipeline failed: {}\n", .{err});
        try stderr.flush();
        std.process.exit(1);
    };

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
    var ids = std.ArrayListUnmanaged(u64).empty;
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
/// Compute the per-module store path stem (without extension).  Dots in the
/// module name become path separators so `Data.Maybe` lands under a
/// `Data/` subdir.  Caller owns the returned slice.
fn artifactStem(
    alloc: std.mem.Allocator,
    artifact_dir: []const u8,
    module_name: []const u8,
) ![]u8 {
    const sep = std.fs.path.sep;
    const rel = try alloc.dupe(u8, module_name);
    for (rel) |*c| if (c.* == '.') {
        c.* = sep;
    };
    defer alloc.free(rel);
    return std.fs.path.join(alloc, &.{ artifact_dir, rel });
}

/// Create all intermediate directories above `file_path`.  No-op if they
/// already exist.
fn ensureParentDirs(io: Io, file_path: []const u8) !void {
    if (std.fs.path.dirname(file_path)) |dir| {
        try Dir.cwd().createDirPath(io, dir);
    }
}

/// Write `iface` to `<artifact_dir>/<Module/Path>.rhi`, creating intermediate
/// directories as needed.
fn writeArtifactRhi(
    alloc: std.mem.Allocator,
    io: Io,
    artifact_dir: []const u8,
    module_name: []const u8,
    iface: rusholme.modules.mod_iface.ModIface,
) !void {
    const stem = try artifactStem(alloc, artifact_dir, module_name);
    defer alloc.free(stem);
    const rhi_path = try std.fmt.allocPrint(alloc, "{s}.rhi", .{stem});
    defer alloc.free(rhi_path);
    try ensureParentDirs(io, rhi_path);
    try rusholme.modules.mod_iface.writeRhiToDisk(alloc, io, rhi_path, iface);
}

test "artifactStem: dots become path separators under artifact_dir" {
    const testing = std.testing;
    const sep = std.fs.path.sep;
    const got = try artifactStem(testing.allocator, "/tmp/store", "Data.Maybe");
    defer testing.allocator.free(got);
    const expected = try std.fmt.allocPrint(
        testing.allocator,
        "/tmp/store{c}Data{c}Maybe",
        .{ sep, sep },
    );
    defer testing.allocator.free(expected);
    try testing.expectEqualStrings(expected, got);
}

test "extractSourceModuleName: basic header" {
    const got = extractSourceModuleName("module Foo.Bar where\n").?;
    try std.testing.expectEqualStrings("Foo.Bar", got);
}

test "extractSourceModuleName: pragma + comments before header" {
    const src =
        \\{-# LANGUAGE NoImplicitPrelude #-}
        \\-- top of file
        \\{- block comment -}
        \\
        \\module Data.List
        \\    ( map, filter
        \\    ) where
        \\
    ;
    const got = extractSourceModuleName(src).?;
    try std.testing.expectEqualStrings("Data.List", got);
}

test "extractSourceModuleName: missing header returns null" {
    try std.testing.expect(extractSourceModuleName("x = 42\n") == null);
}

test "artifactStem: top-level module name has no subdir" {
    const testing = std.testing;
    const got = try artifactStem(testing.allocator, "/tmp/store", "Main");
    defer testing.allocator.free(got);
    const sep = std.fs.path.sep;
    const expected = try std.fmt.allocPrint(testing.allocator, "/tmp/store{c}Main", .{sep});
    defer testing.allocator.free(expected);
    try testing.expectEqualStrings(expected, got);
}

/// Lexical scan of `source` for the first `module Foo.Bar` declaration.
/// Returns a borrowed sub-slice of `source` containing the dotted name, or
/// null if no module header is present (top-level `Main` style file).
///
/// Skips `--` line comments and `{- … -}` block comments before each
/// non-whitespace token, mirroring the lexer's prefix scanner.  Does not
/// validate that the identifier is well-formed beyond the first-character
/// class; the downstream parser will diagnose any malformed header.
fn extractSourceModuleName(source: []const u8) ?[]const u8 {
    var i: usize = 0;
    while (i < source.len) {
        // Skip whitespace.
        while (i < source.len and (source[i] == ' ' or source[i] == '\t' or source[i] == '\n' or source[i] == '\r')) i += 1;
        if (i >= source.len) return null;

        // Skip `-- …` line comments.
        if (i + 1 < source.len and source[i] == '-' and source[i + 1] == '-') {
            while (i < source.len and source[i] != '\n') i += 1;
            continue;
        }
        // Skip `{- … -}` block comments (no nesting — Haskell allows
        // nesting but for the header scan we don't bother).
        if (i + 1 < source.len and source[i] == '{' and source[i + 1] == '-') {
            i += 2;
            while (i + 1 < source.len and !(source[i] == '-' and source[i + 1] == '}')) i += 1;
            if (i + 1 < source.len) i += 2;
            continue;
        }
        // Skip `{-# … #-}` pragmas — caught by the block-comment branch above.
        break;
    }

    // Expect literal "module" followed by whitespace.
    const kw = "module";
    if (i + kw.len > source.len) return null;
    if (!std.mem.eql(u8, source[i .. i + kw.len], kw)) return null;
    i += kw.len;
    if (i >= source.len) return null;
    if (!(source[i] == ' ' or source[i] == '\t' or source[i] == '\n' or source[i] == '\r')) return null;
    while (i < source.len and (source[i] == ' ' or source[i] == '\t' or source[i] == '\n' or source[i] == '\r')) i += 1;

    // Read dotted identifier: start with [A-Z], continue with [A-Za-z0-9_'.].
    if (i >= source.len or !std.ascii.isUpper(source[i])) return null;
    const start = i;
    while (i < source.len) : (i += 1) {
        const c = source[i];
        if (std.ascii.isAlphanumeric(c) or c == '_' or c == '\'' or c == '.') continue;
        break;
    }
    if (i == start) return null;
    return source[start..i];
}

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
    try stdout.print("rhc {s}\n", .{VERSION});
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
