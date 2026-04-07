const std = @import("std");

// ═══════════════════════════════════════════════════════════════════════
// LLVM-C Discovery
// ═══════════════════════════════════════════════════════════════════════

/// Configure LLVM-C header and library paths on a module.
///
/// Uses `llvm-config` (expected on PATH, provided by the Nix devShell)
/// to discover the include and library directories at build-graph
/// construction time. This is necessary because:
///
///   1. LLVM does not ship a .pc file in Nixpkgs, so pkg-config
///      cannot find it.
///   2. Nix splits LLVM across separate store paths (-dev for headers,
///      -lib for shared objects), so a single --search-prefix is
///      insufficient.
///   3. Zig's build system does NOT inherit NIX_CFLAGS_COMPILE for
///      @cImport translate-C steps.
///
/// See BUILDING.md for the full rationale.
fn configureLlvm(b: *std.Build, mod: *std.Build.Module) void {
    var exit_code: u8 = undefined;

    const raw_include = b.runAllowFail(
        &.{ "llvm-config", "--includedir" },
        &exit_code,
        .ignore,
    ) catch @panic("Failed to run `llvm-config --includedir`. Is LLVM on PATH? Try `nix develop`.");

    const raw_libdir = b.runAllowFail(
        &.{ "llvm-config", "--libdir" },
        &exit_code,
        .ignore,
    ) catch @panic("Failed to run `llvm-config --libdir`. Is LLVM on PATH? Try `nix develop`.");

    const llvm_include_dir = std.mem.trimEnd(u8, raw_include, &.{ '\n', '\r', ' ' });
    const llvm_lib_dir = std.mem.trimEnd(u8, raw_libdir, &.{ '\n', '\r', ' ' });

    mod.addSystemIncludePath(.{ .cwd_relative = llvm_include_dir });
    mod.addLibraryPath(.{ .cwd_relative = llvm_lib_dir });
    mod.linkSystemLibrary("LLVM-19", .{});
    mod.link_libc = true;
}

/// Configure replxx headers and library on a module.
///
/// replxx ships no pkg-config file. Discover the include and library
/// paths from the REPLXX_PREFIX environment variable, which is set by
/// the Nix devShell shellHook (see flake.nix).
///
/// Without REPLXX_PREFIX the paths are omitted; the linker will still
/// find libreplxx.so if it is on the default library search path.
fn configureReplxx(b: *std.Build, mod: *std.Build.Module) void {
    if (b.graph.environ_map.get("REPLXX_PREFIX")) |prefix| {
        mod.addSystemIncludePath(.{ .cwd_relative = b.pathJoin(&.{ prefix, "include" }) });
        mod.addLibraryPath(.{ .cwd_relative = b.pathJoin(&.{ prefix, "lib" }) });
    }
    mod.linkSystemLibrary("replxx", .{});
    mod.link_libcpp = true;
}

// Although this function looks imperative, it does not perform the build
// directly and instead it mutates the build graph (`b`) that will be then
// executed by an external runner. The functions in `std.Build` implement a DSL
// for defining build steps and express dependencies between them, allowing the
// build runner to parallelize the build automatically (and the cache system to
// know when a step doesn't need to be re-run).
pub fn build(b: *std.Build) void {
    // Standard target options allow the person running `zig build` to choose
    // what target to build for. Here we do not override the defaults, which
    // means any target is allowed, and the default is native. Other options
    // for restricting supported target set are available.
    const target = b.standardTargetOptions(.{});
    // Standard optimization options allow the person running `zig build` to select
    // between Debug, ReleaseSafe, ReleaseFast, and ReleaseSmall. Here we do not
    // set a preferred release mode, allowing the user to decide how to optimize.
    const optimize = b.standardOptimizeOption(.{});
    // It's also possible to define more custom flags to toggle optional features
    // of this build script using `b.option()`. All defined flags (including
    // target and optimize options) will be listed when running `zig build --help`
    // in this directory.

    // This creates a module, which represents a collection of source files alongside
    // some compilation options, such as optimization mode and linked system libraries.
    // Zig modules are the preferred way of making Zig code available to consumers.
    // addModule defines a module that we intend to make available for importing
    // to our consumers. We must give it a name because a Zig package can expose
    // multiple modules and consumers will need to be able to specify which
    // module they want to access.
    // ── Compiler version ──────────────────────────────────────────────────────
    // The canonical version string for the Rusholme compiler.  Exposed as a
    // build-time constant so that any module (e.g. src/packages/store.zig) can
    // consume it without hard-coding the literal string.  Update this single
    // definition whenever the version changes.
    const compiler_version = "0.1.0";
    const build_options = b.addOptions();
    build_options.addOption([]const u8, "version", compiler_version);

    const mod = b.addModule("rusholme", .{
        // The root source file is the "entry point" of this module. Users of
        // this module will only be able to access public declarations contained
        // in this file, which means that if you have declarations that you
        // intend to expose to consumers that were defined in other files part
        // of this module, you will have to make sure to re-export them from
        // the root file.
        .root_source_file = b.path("src/root.zig"),
        // Later on we'll use this module as the root module of a test executable
        // which requires us to specify a target.
        .target = target,
    });
    mod.addOptions("build_options", build_options);
    mod.addImport("clap", b.dependency("clap", .{}).module("clap"));

    // Wire LLVM-C headers and shared library for the backend.
    // This must be called before any compilation step that transitively
    // imports src/backend/llvm.zig (which uses @cImport for LLVM-C).
    configureLlvm(b, mod);
    configureReplxx(b, mod);

    // Embed the Prelude source text so the REPL session can compile it
    // at init time without reading from disk.  The WASM REPL has no
    // filesystem access, so embedding is the only option there.
    mod.addAnonymousImport("prelude_source", .{
        .root_source_file = b.path("lib/Prelude.hs"),
    });

    // Runtime module - for LLVM-based runtime tests
    const runtime_mod = b.addModule("runtime", .{
        .root_source_file = b.path("src/rts/root.zig"),
        .target = target,
    });

    // ═══════════════════════════════════════════════════════════════════════
    // RTS Static Library
    // ═══════════════════════════════════════════════════════════════════════
    // Build the runtime system (src/rts/) as a static library that exports
    // rts_alloc, rts_store_field, rts_load_field, etc. This library is linked
    // into executables produced by `rhc build`.
    //
    // PIC is required because the static library will be linked into PIE
    // (Position Independent Executables) on modern Linux systems. Without PIC,
    // the linker fails with "relocation R_X86_64_32S ... can not be used when
    // making a PIE object".
    const rts_lib = b.addLibrary(.{
        .name = "rts",
        .linkage = .static,
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/rts/root.zig"),
            .target = target,
            .optimize = optimize,
            .pic = true,
        }),
    });
    b.installArtifact(rts_lib);

    // ═══════════════════════════════════════════════════════════════════════
    // WASM RTS Static Library (wasm32-wasi cross-compilation)
    // ═══════════════════════════════════════════════════════════════════════
    // The same src/rts/ source is cross-compiled for wasm32-wasi so that
    // rts_alloc, rts_putStrLn, etc. are compiled into WASM binaries produced
    // by `rhc build --backend wasm`.
    //
    // std.io in wasm32-wasi emits wasi_snapshot_preview1::fd_write imports
    // rather than native write() syscalls — no backend-specific IO code needed.
    // (See issue #477.)
    const wasm_rts_target = b.resolveTargetQuery(.{
        .cpu_arch = .wasm32,
        .os_tag = .wasi,
    });
    const wasm_rts_lib = b.addLibrary(.{
        .name = "rts_wasm",
        .linkage = .static,
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/rts/root.zig"),
            .target = wasm_rts_target,
            .optimize = optimize,
        }),
    });
    b.installArtifact(wasm_rts_lib);

    // compiler-rt for wasm32-wasi.
    //
    // When a Zig static library is compiled for wasm32-wasi, the resulting
    // object may reference compiler-rt builtins (__divti3, __modti3, etc.)
    // for 128-bit integer operations used internally by the standard library
    // allocator.  These must be provided at wasm-ld link time.
    //
    // We build compiler_rt.zig from the Zig standard library for the same
    // wasm32-wasi target and expose its path alongside the WASM RTS.
    const zig_lib_path = b.graph.zig_lib_directory.path orelse
        @panic("cannot determine Zig lib directory");
    const compiler_rt_zig_path = b.pathJoin(&.{ zig_lib_path, "compiler_rt.zig" });
    const wasm_compiler_rt_lib = b.addLibrary(.{
        .name = "compiler_rt_wasm",
        .linkage = .static,
        .root_module = b.createModule(.{
            .root_source_file = .{ .cwd_relative = compiler_rt_zig_path },
            .target = wasm_rts_target,
            .optimize = .ReleaseSmall,
        }),
    });
    b.installArtifact(wasm_compiler_rt_lib);

    // ═══════════════════════════════════════════════════════════════════════
    // JIT Backend RTS LLVM Bitcode
    // ═══════════════════════════════════════════════════════════════════════
    // The same src/rts/ source is compiled for the native target but emitted
    // as LLVM bitcode (.bc) instead of a static library (.a).  This bitcode
    // is merged with program bitcode in-process so that lli can execute
    // the result without undefined rts_* symbols.
    //
    // We use a baseline CPU model (no host-specific features) so the emitted
    // IR does not contain target-features strings (e.g. +amx-avx512) that
    // the system lli may not recognise, avoiding noisy warnings.
    const jit_target = b.resolveTargetQuery(.{
        .cpu_model = .baseline,
    });
    const jit_rts_lib = b.addLibrary(.{
        .name = "rts_jit",
        .linkage = .static,
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/rts/root.zig"),
            .target = jit_target,
            .optimize = optimize,
            .pic = true,
        }),
    });
    const jit_rts_bc = jit_rts_lib.getEmittedLlvmBc();
    // Install the bitcode to zig-out/lib/rts_jit.bc so the CLI can
    // find it at runtime (path baked in via @embedFile, same as librts.a).
    const install_jit_bc = b.addInstallLibFile(jit_rts_bc, "rts_jit.bc");
    b.getInstallStep().dependOn(&install_jit_bc.step);

    // compiler-rt as LLVM bitcode for the JIT backend.
    //
    // The Zig RTS references compiler-rt builtins (__zig_probe_stack,
    // __divti3, etc.) that are normally linked by the system linker.
    // When running via lli, these symbols must be present in the merged
    // bitcode.  We compile compiler_rt.zig for the native target and
    // emit its bitcode alongside the RTS bitcode.
    const jit_compiler_rt_lib = b.addLibrary(.{
        .name = "compiler_rt_jit",
        .linkage = .static,
        .root_module = b.createModule(.{
            .root_source_file = .{ .cwd_relative = compiler_rt_zig_path },
            .target = jit_target,
            .optimize = .ReleaseSmall,
            .pic = true,
        }),
    });
    const jit_compiler_rt_bc = jit_compiler_rt_lib.getEmittedLlvmBc();
    const install_jit_compiler_rt_bc = b.addInstallLibFile(
        jit_compiler_rt_bc,
        "compiler_rt_jit.bc",
    );
    b.getInstallStep().dependOn(&install_jit_compiler_rt_bc.step);

    // ═══════════════════════════════════════════════════════════════════════
    // CLI Executable with RTS Library Paths
    // ═══════════════════════════════════════════════════════════════════════
    // Expose both RTS library paths as build options so the CLI can find them
    // at runtime. Paths are baked in at compile time via @embedFile.
    //
    // We need the FULL path (including install prefix) because the binary might
    // be run from a different directory. The RTS static library is installed
    // alongside the CLI, so we compute its absolute path at build time.
    const rts_lib_path_option = b.option([]const u8, "rts-lib-path", "Path to RTS library") orelse blk: {
        // Default: get the absolute install path for librts.a
        const rts_lib_path = b.getInstallPath(.lib, "librts.a");
        break :blk rts_lib_path;
    };
    const rts_path = b.addNamedWriteFiles("rts_path");
    const rts_path_file = rts_path.add("path.txt", rts_lib_path_option);

    const wasm_rts_lib_path_option = b.option(
        []const u8,
        "wasm-rts-lib-path",
        "Path to WASM RTS library",
    ) orelse b.getInstallPath(.lib, "librts_wasm.a");
    const wasm_rts_path = b.addNamedWriteFiles("wasm_rts_path");
    const wasm_rts_path_file = wasm_rts_path.add("path.txt", wasm_rts_lib_path_option);

    const wasm_compiler_rt_lib_path_option = b.option(
        []const u8,
        "wasm-compiler-rt-lib-path",
        "Path to WASM compiler-rt library",
    ) orelse b.getInstallPath(.lib, "libcompiler_rt_wasm.a");
    const wasm_compiler_rt_path = b.addNamedWriteFiles("wasm_compiler_rt_path");
    const wasm_compiler_rt_path_file = wasm_compiler_rt_path.add(
        "path.txt",
        wasm_compiler_rt_lib_path_option,
    );

    const jit_rts_bc_path_option = b.option(
        []const u8,
        "jit-rts-bc-path",
        "Path to JIT backend RTS bitcode (.bc)",
    ) orelse b.getInstallPath(.lib, "rts_jit.bc");
    const jit_rts_bc_path_wf = b.addNamedWriteFiles("jit_rts_bc_path");
    const jit_rts_bc_path_file = jit_rts_bc_path_wf.add(
        "path.txt",
        jit_rts_bc_path_option,
    );

    const jit_compiler_rt_bc_path_option = b.option(
        []const u8,
        "jit-compiler-rt-bc-path",
        "Path to JIT backend compiler-rt bitcode (.bc)",
    ) orelse b.getInstallPath(.lib, "compiler_rt_jit.bc");
    const jit_compiler_rt_bc_path_wf = b.addNamedWriteFiles("jit_compiler_rt_bc_path");
    const jit_compiler_rt_bc_path_file = jit_compiler_rt_bc_path_wf.add(
        "path.txt",
        jit_compiler_rt_bc_path_option,
    );

    // Prelude source path: baked in at compile time so the compiler can
    // find lib/Prelude.hs at runtime for implicit Prelude compilation.
    const prelude_path_option = b.option(
        []const u8,
        "prelude-path",
        "Path to lib/Prelude.hs",
    ) orelse b.getInstallPath(.@"prefix", "lib/Prelude.hs");
    const prelude_path_wf = b.addNamedWriteFiles("prelude_path");
    const prelude_path_file = prelude_path_wf.add("path.txt", prelude_path_option);

    // Here we define an executable. An executable needs to have a root module
    // which needs to expose a `main` function. While we could add a main function
    // to the module defined above, it's sometimes preferable to split business
    // logic and the CLI into two separate modules.
    //
    // If your goal is to create a Zig library for others to use, consider if
    // it might benefit from also exposing a CLI tool. A parser library for a
    // data serialization format could also bundle a CLI syntax checker, for example.
    //
    // If instead your goal is to create an executable, consider if users might
    // be interested in also being able to embed the core functionality of your
    // program in their own executable in order to avoid the overhead involved in
    // subprocessing your CLI tool.
    //
    // If neither case applies to you, feel free to delete the declaration you
    // don't need and to put everything under a single module.
    const exe = b.addExecutable(.{
        .name = "rhc",
        .root_module = b.createModule(.{
            // b.createModule defines a new module just like b.addModule but,
            // unlike b.addModule, it does not expose the module to consumers of
            // this package, which is why in this case we don't have to give it a name.
            .root_source_file = b.path("src/main.zig"),
            // Target and optimization levels must be explicitly wired in when
            // defining an executable or library (in the root module), and you
            // can also hardcode a specific target for an executable or library
            // definition if desireable (e.g. firmware for embedded devices).
            .target = target,
            .optimize = optimize,
            // List of modules available for import in source files part of the
            // root module.
            .imports = &.{
                // Here "rusholme" is the name you will use in your source code to
                // import this module (e.g. `@import("rusholme")`). The name is
                // repeated because you are allowed to rename your imports, which
                // can be extremely useful in case of collisions (which can happen
                // importing modules from different packages).
                .{ .name = "rusholme", .module = mod },
                .{ .name = "clap", .module = b.dependency("clap", .{}).module("clap") },
            },
        }),
    });

    // Pass both RTS library paths as build options so the CLI can find them.
    exe.root_module.addAnonymousImport("rts_lib_path", .{
        .root_source_file = rts_path_file,
    });
    exe.root_module.addAnonymousImport("wasm_rts_lib_path", .{
        .root_source_file = wasm_rts_path_file,
    });
    exe.root_module.addAnonymousImport("wasm_compiler_rt_lib_path", .{
        .root_source_file = wasm_compiler_rt_path_file,
    });
    exe.root_module.addAnonymousImport("jit_rts_bc_path", .{
        .root_source_file = jit_rts_bc_path_file,
    });
    exe.root_module.addAnonymousImport("jit_compiler_rt_bc_path", .{
        .root_source_file = jit_compiler_rt_bc_path_file,
    });
    exe.root_module.addAnonymousImport("prelude_path", .{
        .root_source_file = prelude_path_file,
    });

    // This declares intent for the executable to be installed into the
    // install prefix when running `zig build` (i.e. when executing the default
    // step). By default the install prefix is `zig-out/` but can be overridden
    // by passing `--prefix` or `-p`.
    b.installArtifact(exe);

    // Install the Prelude source file alongside the binary so the compiler
    // can find it at runtime via the baked-in prelude_path.
    b.installFile("lib/Prelude.hs", "lib/Prelude.hs");

    // This creates a top level step. Top level steps have a name and can be
    // invoked by name when running `zig build` (e.g. `zig build run`).
    // This will evaluate the `run` step rather than the default step.
    // For a top level step to actually do something, it must depend on other
    // steps (e.g. a Run step, as we will see in a moment).
    const run_step = b.step("run", "Run the app");

    // This creates a RunArtifact step in the build graph. A RunArtifact step
    // invokes an executable compiled by Zig. Steps will only be executed by the
    // runner if invoked directly by the user (in the case of top level steps)
    // or if another step depends on it, so it's up to you to define when and
    // how this Run step will be executed. In our case we want to run it when
    // the user runs `zig build run`, so we create a dependency link.
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);

    // By making the run step depend on the default step, it will be run from the
    // installation directory rather than directly from within the cache directory.
    run_cmd.step.dependOn(b.getInstallStep());

    // This allows the user to pass arguments to the application in the build
    // command itself, like this: `zig build run -- arg1 arg2 etc`
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    // Creates an executable that will run `test` blocks from the provided module.
    // Here `mod` needs to define a target, which is why earlier we made sure to
    // set the releative field.
    const mod_tests = b.addTest(.{
        .root_module = mod,
    });

    // A run step that will run the test executable.
    const run_mod_tests = b.addRunArtifact(mod_tests);

    // Creates an executable that will run `test` blocks from the executable's
    // root module. Note that test executables only test one module at a time,
    // hence why we have to create two separate ones.
    const exe_tests = b.addTest(.{
        .root_module = exe.root_module,
    });

    // A run step that will run the second test executable.
    const run_exe_tests = b.addRunArtifact(exe_tests);

    // Golden test runner - reads test files from disk
    const golden_test_module = b.createModule(.{
        .root_source_file = b.path("tests/golden_test_runner.zig"),
        .target = target,
        .imports = &.{.{ .name = "rusholme", .module = mod }},
    });
    const golden_tests = b.addTest(.{
        .name = "golden-tests",
        .root_module = golden_test_module,
    });
    const run_golden_tests = b.addRunArtifact(golden_tests);

    // Parser conformance test runner (should_compile / should_fail)
    const parser_test_module = b.createModule(.{
        .root_source_file = b.path("tests/parser_test_runner.zig"),
        .target = target,
        .imports = &.{.{ .name = "rusholme", .module = mod }},
    });
    const parser_tests = b.addTest(.{
        .name = "parser-tests",
        .root_module = parser_test_module,
    });
    const run_parser_tests = b.addRunArtifact(parser_tests);

    // Runtime test runner - tests LLVM-based runtime (src/rts/)
    const runtime_test_module = b.createModule(.{
        .root_source_file = b.path("tests/runtime_test_runner.zig"),
        .target = target,
        .imports = &.{.{ .name = "runtime", .module = runtime_mod }},
    });
    const runtime_tests = b.addTest(.{
        .name = "runtime-tests",
        .root_module = runtime_test_module,
    });
    const run_runtime_tests = b.addRunArtifact(runtime_tests);

    // End-to-end test runner — compiles .hs files with `rhc build`, runs the
    // resulting binaries, and asserts stdout against .stdout sidecar files.
    // The rhc binary path is baked in as a compile-time option so the runner
    // can invoke the compiler without knowing the install prefix at test time.
    const e2e_opts = b.addOptions();
    e2e_opts.addOption([]const u8, "rhc_path", b.getInstallPath(.bin, "rhc"));
    const e2e_test_module = b.createModule(.{
        .root_source_file = b.path("tests/e2e_test_runner.zig"),
        .target = target,
    });
    e2e_test_module.addOptions("e2e_options", e2e_opts);
    const e2e_tests = b.addTest(.{
        .name = "e2e-tests",
        .root_module = e2e_test_module,
    });
    // e2e tests must run after `rhc` is installed so the binary exists.
    e2e_tests.step.dependOn(b.getInstallStep());
    const run_e2e_tests = b.addRunArtifact(e2e_tests);

    // REPL test runner - TDD tests for REPL behavior
    const repl_test_module = b.createModule(.{
        .root_source_file = b.path("tests/repl/repl_tests.zig"),
        .target = target,
        .imports = &.{.{ .name = "rusholme", .module = mod }},
    });
    const repl_tests = b.addTest(.{
        .name = "repl-tests",
        .root_module = repl_test_module,
    });
    // REPL tests JIT-compile and execute code that writes directly to fd 1
    // via the RTS (rts_putStrLn). This bypasses the Zig test runner's IPC
    // protocol (--listen=-) and corrupts the pipe, causing a deadlock.
    // Create the run step manually without enableTestRunnerMode so the
    // binary runs without --listen and communicates via exit code only.
    const run_repl_tests = std.Build.Step.Run.create(b, "run test repl-tests");
    run_repl_tests.addArtifactArg(repl_tests);
    run_repl_tests.expectExitCode(0);

    // CLI end-to-end REPL tests — spawn rhc repl as subprocess.
    // These test the real interactive experience: prompts, commands,
    // multiline accumulation, and :load from disk.
    const cli_e2e_module = b.createModule(.{
        .root_source_file = b.path("tests/repl/cli_e2e_tests.zig"),
        .target = target,
    });
    const cli_e2e_tests = b.addTest(.{
        .name = "cli-e2e-tests",
        .root_module = cli_e2e_module,
    });
    // CLI e2e tests need the rhc binary built first.
    cli_e2e_tests.step.dependOn(b.getInstallStep());
    // Same technique as repl-tests: no IPC mode, communicate via exit code.
    const run_cli_e2e_tests = std.Build.Step.Run.create(b, "run test cli-e2e-tests");
    run_cli_e2e_tests.addArtifactArg(cli_e2e_tests);
    run_cli_e2e_tests.expectExitCode(0);

    // WASM REPL end-to-end tests — spawn wasmtime with
    // repl.wasm and exercise the JSON-RPC protocol.
    const wasm_e2e_module = b.createModule(.{
        .root_source_file = b.path("tests/repl/wasm_e2e_tests.zig"),
        .target = target,
    });
    const wasm_e2e_tests = b.addTest(.{
        .name = "wasm-e2e-tests",
        .root_module = wasm_e2e_module,
    });
    // WASM e2e tests need repl.wasm built first.
    wasm_e2e_tests.step.dependOn(b.getInstallStep());
    // Same technique as repl-tests: no IPC mode, communicate via exit code.
    const run_wasm_e2e_tests = std.Build.Step.Run.create(b, "run test wasm-e2e-tests");
    run_wasm_e2e_tests.addArtifactArg(wasm_e2e_tests);
    run_wasm_e2e_tests.expectExitCode(0);

    // Diagnostic step — reports per-file parser errors for failing tests.
    // Usage: zig build diag
    const diag_module = b.createModule(.{
        .root_source_file = b.path("tests/diagnose_runner.zig"),
        .target = target,
        .imports = &.{.{ .name = "rusholme", .module = mod }},
    });
    const diag_tests = b.addTest(.{
        .name = "diag",
        .root_module = diag_module,
    });
    const run_diag = b.addRunArtifact(diag_tests);
    const diag_step = b.step("diag", "Diagnose parser conformance failures");
    diag_step.dependOn(&run_diag.step);

    const pkg_cmd_test_module = b.createModule(.{
        .root_source_file = b.path("tests/pkg_cmd_test.zig"),
        .target = target,
        .imports = &.{.{ .name = "rusholme", .module = mod }},
    });
    const pkg_cmd_tests = b.addTest(.{
        .name = "pkg-cmd-tests",
        .root_module = pkg_cmd_test_module,
    });
    const run_pkg_cmd_tests = b.addRunArtifact(pkg_cmd_tests);

    // A top level step for running all tests. dependOn can be called multiple
    // times and since the two run steps do not depend on one another, this will
    // make the two of them run in parallel.
    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_mod_tests.step);
    test_step.dependOn(&run_exe_tests.step);
    test_step.dependOn(&run_golden_tests.step);
    test_step.dependOn(&run_parser_tests.step);
    test_step.dependOn(&run_runtime_tests.step);
    test_step.dependOn(&run_e2e_tests.step);
    test_step.dependOn(&run_repl_tests.step);
    test_step.dependOn(&run_cli_e2e_tests.step);
    test_step.dependOn(&run_wasm_e2e_tests.step);
    test_step.dependOn(&run_pkg_cmd_tests.step);

    // Just like flags, top level steps are also listed in the `--help` menu.
    //
    // The Zig build system is entirely implemented in userland, which means
    // that it cannot hook into private compiler APIs. All compilation work
    // orchestrated by the build system will result in other Zig compiler
    // subcommands being invoked with the right flags defined. You can observe
    // these invocations when one fails (or you pass a flag to increase
    // verbosity) to validate assumptions and diagnose problems.
    //
    // Lastly, the Zig build system is relatively simple and self-contained,
    // and reading its source code will allow you to master it.

    // ═══════════════════════════════════════════════════════════════════════
    // WASM REPL Executable - wasm32-wasi target for browser
    // ═══════════════════════════════════════════════════════════════════════
    // Build the REPL WebAssembly module for browser-based evaluation.
    // Uses wasm32-wasi so that IO operations (fd_write) are standardised
    // and can be polyfilled in the browser via browser_wasi_shim.
    // See docs/decisions/0006-repl-architecture.md.
    //
    // The REPL pipeline files use `../frontend/`, `../grin/`, etc. relative
    // imports, so the module root must be at `src/` level. We use a thin
    // entry-point file (`src/repl_wasm_main.zig`) that re-exports from
    // `repl/exports.zig`.
    const repl_wasm = b.addExecutable(.{
        .name = "repl",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/repl_wasm_main.zig"),
            .target = b.resolveTargetQuery(.{
                .cpu_arch = .wasm32,
                .os_tag = .wasi,
            }),
            .optimize = .ReleaseSmall,
        }),
    });
    // Embed the Prelude source for the WASM REPL (same as the library module).
    repl_wasm.root_module.addAnonymousImport("prelude_source", .{
        .root_source_file = b.path("lib/Prelude.hs"),
    });
    // Reactor mode: the REPL is a long-lived module with exported functions,
    // not a command that runs once and exits. In reactor mode the entry point
    // is `_initialize` (no `proc_exit`), which avoids the noreturn trap that
    // occurs when the JS WASI shim returns from `proc_exit` in command mode.
    repl_wasm.wasi_exec_model = .reactor;
    // Export all `pub export` symbols so JavaScript can call them.
    repl_wasm.rdynamic = true;

    b.installArtifact(repl_wasm);

    // The unified repl.wasm binary serves both browser and headless use:
    //   Browser:  JS calls repl_process_jsonrpc() via shared buffers
    //   Headless: wasmtime run --invoke repl_server_run repl.wasm
}
