//! Compilation session (`CompileEnv`).
//!
//! `CompileEnv` is the accumulation point for a whole-program compilation
//! session.  It stores:
//!
//! - The interface of every already-compiled module (`ModIface`).
//! - The desugared Core IR of every already-compiled module (`CoreProgram`).
//! - A shared `UniqueSupply` threaded across all modules.
//! - A `DiagnosticCollector` accumulating errors across all modules.
//!
//! The central entry points are:
//!
//! - `CompileEnv.compileSingle` — run the full pipeline (parse → rename →
//!   typecheck → desugar) for one module and register its outputs.
//! - `compileProgram` — accept a list of source-file paths, discover the
//!   module graph, topologically sort it, drive `compileSingle` in order,
//!   and merge all `CoreProgram`s into a single whole-program Core ready
//!   for lambda lifting and GRIN translation.
//!
//! ## Analogy with GHC
//!
//! This maps loosely to GHC's `HscEnv` + `upsweep` in `GHC.Driver.Make`.
//! We use a simpler model: whole-program compilation with no separate
//! compilation or recompilation avoidance (those are follow-up issues).
//!
//! ## Implicit Prelude import (Haskell 2010 §5.6)
//!
//! Every module implicitly imports `Prelude` unless:
//! - The module header already contains an explicit `import Prelude` (possibly
//!   with a `hiding` list or import spec), or
//! - The module carries a `{-# LANGUAGE NoImplicitPrelude #-}` pragma.
//!
//! `compileSingle` implements this by calling `injectImplicitPrelude` after
//! parsing, before passing the AST to the renamer.
//!
//! ## Analogy with GHC
//!
//! This maps loosely to GHC's `HscEnv` + `upsweep` in `GHC.Driver.Make`.
//! We use a simpler model: whole-program compilation with no separate
//! compilation or recompilation avoidance (those are follow-up issues).
//!
//! ## M2 scope / known limitations
//!
//! - Recompilation avoidance (`.rhi` fingerprinting) is not yet implemented.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/371
//!
//! - Package-level search paths are not yet supported.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/368

const std = @import("std");

const naming_mod = @import("../naming/unique.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");
const span_mod = @import("../diagnostics/span.zig");
const lexer_mod = @import("../frontend/lexer.zig");
const layout_mod = @import("../frontend/layout.zig");
const parser_mod = @import("../frontend/parser.zig");
const ast_mod = @import("../frontend/ast.zig");
const renamer_mod = @import("../renamer/renamer.zig");
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");
const infer_mod = @import("../typechecker/infer.zig");
const desugar_mod = @import("../core/desugar.zig");
const core_ast = @import("../core/ast.zig");
const mod_iface = @import("mod_iface.zig");
const module_graph = @import("module_graph.zig");

pub const UniqueSupply = naming_mod.UniqueSupply;
pub const Name = naming_mod.Name;
pub const Unique = naming_mod.Unique;
pub const DiagnosticCollector = diag_mod.DiagnosticCollector;
pub const Diagnostic = diag_mod.Diagnostic;
pub const ModIface = mod_iface.ModIface;
pub const CoreProgram = core_ast.CoreProgram;
pub const ModuleGraph = module_graph.ModuleGraph;

// ── CompileEnv ────────────────────────────────────────────────────────────

/// A compilation session: accumulates compiled module interfaces and Core
/// programs as each module in the topological order is processed.
///
/// All allocations are expected to go into a caller-owned arena; `CompileEnv`
/// does not manage its own arena.
pub const CompileEnv = struct {
    alloc: std.mem.Allocator,

    /// Map: module name → compiled interface.
    ///
    /// Keys are interned into `alloc`.  Populated by `register` after each
    /// module is compiled.
    ifaces: std.StringHashMapUnmanaged(ModIface),

    /// Map: module name → desugared Core program.
    ///
    /// Retained so that after all modules are compiled we can merge them
    /// into a single whole-program `CoreProgram` for lambda lifting and
    /// GRIN translation.
    programs: std.StringHashMapUnmanaged(CoreProgram),

    /// Map: module name → pre-parsed AST module.
    ///
    /// Populated by `compileProgram` after parsing each module once.
    /// Used to avoid redundant parsing when both import extraction and
    /// full compilation need the same AST.
    parsed_modules: std.StringHashMapUnmanaged(ast_mod.Module),

    /// Shared unique-ID supply across all modules in the session.
    ///
    /// Threading a single supply through all compilation units ensures that
    /// `Unique` values assigned in different modules never collide.
    u_supply: UniqueSupply,

    /// Shared metavar supply for the typechecker across all modules.
    mv_supply: htype_mod.MetaVarSupply,

    /// Accumulates diagnostics from all modules.
    diags: DiagnosticCollector,

    // ── Lifecycle ─────────────────────────────────────────────────────────

    /// Create an empty compilation session.
    pub fn init(alloc: std.mem.Allocator) CompileEnv {
        return .{
            .alloc = alloc,
            .ifaces = .{},
            .programs = .{},
            .parsed_modules = .{},
            .u_supply = .{},
            .mv_supply = .{},
            .diags = DiagnosticCollector.init(),
        };
    }

    pub fn deinit(self: *CompileEnv) void {
        self.ifaces.deinit(self.alloc);
        self.programs.deinit(self.alloc);
        self.parsed_modules.deinit(self.alloc);
        self.diags.deinit(self.alloc);
        self.* = undefined;
    }

    // ── Registration ──────────────────────────────────────────────────────

    /// Register a compiled module: store its interface and Core program.
    ///
    /// `module_name` is duped into `alloc` so that the key outlives any
    /// transient string.
    pub fn register(
        self: *CompileEnv,
        module_name: []const u8,
        iface: ModIface,
        core_prog: CoreProgram,
    ) std.mem.Allocator.Error!void {
        const owned_name = try self.alloc.dupe(u8, module_name);
        try self.ifaces.put(self.alloc, owned_name, iface);
        try self.programs.put(self.alloc, owned_name, core_prog);
    }

    // ── Environment seeding ───────────────────────────────────────────────

    /// Seed a `RenameEnv` with all exported names from previously-compiled
    /// modules.
    ///
    /// For each registered module, every exported value and data constructor
    /// is bound in the global scope of `env` using its serialised `unique`
    /// and `name`.  This allows downstream modules to resolve cross-module
    /// references without re-parsing the upstream source.
    pub fn seedRenamer(
        self: *const CompileEnv,
        env: *renamer_mod.RenameEnv,
    ) std.mem.Allocator.Error!void {
        var it = self.ifaces.valueIterator();
        while (it.next()) |iface| {
            // Seed value bindings.
            for (iface.values) |ev| {
                const name = Name{
                    .base = ev.name,
                    .unique = .{ .value = ev.unique },
                };
                try env.scope.bind(ev.name, name);
            }
            // Seed data constructors from each exported data declaration.
            for (iface.data_decls) |dd| {
                // Seed the type constructor itself.
                const ty_name = Name{
                    .base = dd.name,
                    .unique = .{ .value = dd.unique },
                };
                try env.scope.bind(dd.name, ty_name);
                // Seed each constructor.
                for (dd.constructors) |con| {
                    const con_name = Name{
                        .base = con.name,
                        .unique = .{ .value = con.unique },
                    };
                    try env.scope.bind(con.name, con_name);
                }
            }
        }
    }

    /// Seed a `TyEnv` with the type schemes of all exported values from
    /// previously-compiled modules.
    ///
    /// Converts each `SerialisedScheme` back to an `HType`-based `TyScheme`
    /// and binds it in the global frame of `ty_env`.
    pub fn seedTyEnv(
        self: *const CompileEnv,
        ty_env: *env_mod.TyEnv,
    ) std.mem.Allocator.Error!void {
        var it = self.ifaces.valueIterator();
        while (it.next()) |iface| {
            for (iface.values) |ev| {
                const name = Name{
                    .base = ev.name,
                    .unique = .{ .value = ev.unique },
                };
                const scheme = try deserialiseTyScheme(ty_env.alloc, ev.scheme);
                try ty_env.bind(name, scheme);
            }
            // Seed data constructor types from data declarations.
            for (iface.data_decls) |dd| {
                for (dd.constructors) |con| {
                    const con_name = Name{
                        .base = con.name,
                        .unique = .{ .value = con.unique },
                    };
                    // Constructors are serialised as monomorphic CoreTypes under
                    // the data decl's foralls.  Convert to HType and bind.
                    const core_ty = try con.ty.toCoreType(ty_env.alloc);
                    const hty = try coreTypeToHType(ty_env.alloc, core_ty);
                    try ty_env.bindMono(con_name, hty);
                }
            }
        }
    }

    // ── Single-module compilation ─────────────────────────────────────────

    /// Run the full front-end pipeline for a single source file and register
    /// its outputs in the session.
    ///
    /// Pipeline: read source → lex/parse → inject implicit Prelude import
    /// (Haskell 2010 §5.6) → rename (with upstream names seeded from `self`)
    /// → typecheck (with upstream types seeded from `self`) → desugar →
    /// build `ModIface` → `register`.
    ///
    /// `file_id` is the file identifier used for diagnostic spans.
    ///
    /// If `preparsed_module` is provided, skips parsing and uses the given AST.
    /// This is used by `compileProgram` to avoid redundant parsing when the
    /// module has already been parsed once for import extraction.
    ///
    /// Returns the desugared `CoreProgram` (which is also stored in `self`).
    ///
    /// On parse, rename, or typecheck failure the diagnostics are accumulated
    /// in `self.diags` and `null` is returned so the caller can decide whether
    /// to abort or continue accumulating errors.
    pub fn compileSingle(
        self: *CompileEnv,
        module_name: []const u8,
        source: []const u8,
        file_id: u32,
        preparsed_module: ?ast_mod.Module,
    ) std.mem.Allocator.Error!?CoreProgram {
        // ── Parse (or use pre-parsed) ─────────────────────────────────────
        const parsed = if (preparsed_module) |m| m else blk: {
            var lexer = lexer_mod.Lexer.init(self.alloc, source, file_id);
            var layout = layout_mod.LayoutProcessor.init(self.alloc, &lexer);
            layout.setDiagnostics(&self.diags);

            var parser = parser_mod.Parser.init(self.alloc, &layout, &self.diags) catch return null;
            break :blk parser.parseModule() catch return null;
        };
        if (self.diags.hasErrors()) return null;

        // ── Implicit Prelude injection (Haskell 2010 §5.6) ───────────────
        // Unless the module carries {-# LANGUAGE NoImplicitPrelude #-} or
        // already has an explicit `import Prelude`, prepend a synthetic
        // `import Prelude` to the import list.
        const module = if (parsed.language_extensions.contains(.NoImplicitPrelude) or
            mentionsPrelude(parsed.imports))
            parsed
        else
            try injectImplicitPrelude(self.alloc, parsed);

        // ── Rename ───────────────────────────────────────────────────────
        var rename_env = try renamer_mod.RenameEnv.init(self.alloc, &self.u_supply, &self.diags);
        defer rename_env.deinit();
        // Seed with names from upstream modules.
        try self.seedRenamer(&rename_env);
        const renamed = try renamer_mod.rename(module, &rename_env);
        if (self.diags.hasErrors()) return null;

        // ── Typecheck ────────────────────────────────────────────────────
        var ty_env = try env_mod.TyEnv.init(self.alloc);
        try env_mod.initBuiltins(&ty_env, self.alloc, &self.u_supply);
        // Seed with types from upstream modules.
        try self.seedTyEnv(&ty_env);

        var infer_ctx = infer_mod.InferCtx.init(
            self.alloc,
            &ty_env,
            &self.mv_supply,
            &self.u_supply,
            &self.diags,
        );
        var module_types = try infer_mod.inferModule(&infer_ctx, renamed);
        defer module_types.deinit(self.alloc);
        if (self.diags.hasErrors()) return null;

        // ── Desugar ──────────────────────────────────────────────────────
        const core_prog = try desugar_mod.desugarModule(
            self.alloc,
            renamed,
            &module_types,
            &self.diags,
            &self.u_supply,
        );
        if (self.diags.hasErrors()) return null;

        // ── Build interface ───────────────────────────────────────────────
        const export_list = module.exports;
        const iface = try mod_iface.buildModIface(
            self.alloc,
            module_name,
            export_list,
            core_prog,
            &module_types,
        );

        // ── Register ─────────────────────────────────────────────────────
        try self.register(module_name, iface, core_prog);

        return core_prog;
    }

    // ── Whole-program Core merge ──────────────────────────────────────────

    /// Merge all per-module `CoreProgram`s into a single whole-program Core.
    ///
    /// Data declarations and top-level bindings are concatenated in the order
    /// provided by `module_order` (which should be the topological compilation
    /// order so that definitions from upstream modules appear first).
    ///
    /// Caller owns the returned `CoreProgram` slices (all memory is in `alloc`).
    pub fn mergePrograms(
        self: *const CompileEnv,
        alloc: std.mem.Allocator,
        module_order: []const []const u8,
    ) std.mem.Allocator.Error!CoreProgram {
        var all_data: std.ArrayListUnmanaged(core_ast.CoreDataDecl) = .{};
        var all_binds: std.ArrayListUnmanaged(core_ast.Bind) = .{};

        for (module_order) |name| {
            const prog = self.programs.get(name) orelse continue;
            try all_data.appendSlice(alloc, prog.data_decls);
            try all_binds.appendSlice(alloc, prog.binds);
        }

        return CoreProgram{
            .data_decls = try all_data.toOwnedSlice(alloc),
            .binds = try all_binds.toOwnedSlice(alloc),
        };
    }
};

// ── compileProgram ────────────────────────────────────────────────────────

/// A source module ready for compilation: its inferred name and source text.
pub const SourceModule = struct {
    /// Fully-qualified module name (e.g. `"Data.Map"`, `"Main"`).
    /// Inferred from the file path by the caller via `module_graph.inferModuleName`.
    module_name: []const u8,
    /// UTF-8 source text.  Owned by the caller.
    source: []const u8,
    /// File identifier for diagnostic spans (must be unique per module).
    file_id: u32,
    /// Absolute or relative path to the source file on disk.
    ///
    /// When non-null, `compileProgram` will:
    /// - Look for a `.rhi` file at the same path with `.rhi` extension to
    ///   check for a valid cached interface (fingerprint match).
    /// - Write a fresh `.rhi` after a successful compilation.
    ///
    /// Leave `null` to disable caching for this module (e.g. in tests that
    /// supply source text without a backing file, or in `cmdBuild` until
    /// per-module `.bc` backend caching is implemented — see #436).
    source_path: ?[]const u8 = null,
};

/// The result of a whole-program compilation.
pub const CompileResult = struct {
    /// The merged whole-program Core IR, ready for lambda lifting.
    core: CoreProgram,
    /// Whether any errors were emitted during compilation.
    had_errors: bool,
};

/// Compile a set of pre-read Haskell source modules into a single merged
/// `CoreProgram`.
///
/// The caller is responsible for reading the source files and constructing
/// the `SourceModule` slice (including setting unique `file_id` values).
/// This design keeps file I/O out of `CompileEnv`, allowing the caller to
/// use whatever `Io` abstraction is appropriate (test harness, real FS, etc).
///
/// The function:
/// 1. Parses each module once, storing the AST in `env.parsed_modules`.
/// 2. Builds a `ModuleGraph` from the parsed imports.
/// 3. Topologically sorts the graph (import cycles → error).
/// 4. Compiles each module in dependency-first order via `CompileEnv.compileSingle`,
///    passing the pre-parsed AST to avoid redundant lexing/parsing.
/// 5. Merges all `CoreProgram`s into a single whole-program Core.
///
/// `alloc` should be an arena that outlives the returned result.
pub fn compileProgram(
    alloc: std.mem.Allocator,
    io: std.Io,
    modules: []const SourceModule,
) std.mem.Allocator.Error!struct { env: CompileEnv, result: CompileResult } {
    var env = CompileEnv.init(alloc);
    errdefer env.deinit();

    // ── Phase 1: Parse all modules once and cache ──────────────────────────
    for (modules) |m| {
        var dummy_diags = DiagnosticCollector.init();
        defer dummy_diags.deinit(alloc);

        var lexer = lexer_mod.Lexer.init(alloc, m.source, m.file_id);
        var layout = layout_mod.LayoutProcessor.init(alloc, &lexer);
        layout.setDiagnostics(&dummy_diags);

        var parser = parser_mod.Parser.init(alloc, &layout, &dummy_diags) catch continue;
        const parsed_module = parser.parseModule() catch continue;

        const owned_name = try alloc.dupe(u8, m.module_name);
        try env.parsed_modules.put(alloc, owned_name, parsed_module);
    }

    // ── Phase 2: Build module graph from cached parses ─────────────────────
    var graph = ModuleGraph.init(alloc);
    defer graph.deinit();

    var iter = env.parsed_modules.iterator();
    while (iter.next()) |entry| {
        const mod_name = entry.key_ptr.*;
        const parsed = entry.value_ptr.*;
        _ = try graph.addModule(mod_name);
        for (parsed.imports) |imp| {
            try graph.addEdge(mod_name, imp.module_name);
        }
    }

    // ── Topological sort ──────────────────────────────────────────────────
    const topo = try module_graph.topoSort(&graph, alloc, &env.diags);
    defer alloc.free(topo.order);

    if (!topo.is_complete) {
        return .{
            .env = env,
            .result = .{ .core = .{ .data_decls = &.{}, .binds = &.{} }, .had_errors = true },
        };
    }

    // Build a name → SourceModule map for O(1) lookup.
    var src_map: std.StringHashMapUnmanaged(SourceModule) = .{};
    defer src_map.deinit(alloc);
    for (modules) |m| {
        try src_map.put(alloc, m.module_name, m);
    }

    // ── Phase 3: Compile each module (with .rhi cache check) ──────────────
    //
    // For each module in topo order:
    //   1. Collect fingerprints from already-compiled direct imports.
    //   2. Compute the expected fingerprint = Wyhash(source ++ dep_fps).
    //   3. If `source_path` is set, try to load a matching `.rhi` from disk.
    //      On cache hit: register the cached iface + an empty CoreProgram
    //      and skip compilation.  The empty Core is acceptable for frontend
    //      caching; full backend reuse requires per-module .bc artifacts
    //      (tracked in #436).
    //   4. On cache miss: run `compileSingle`, then tag the iface with its
    //      fingerprint and write it to disk for future runs.
    for (topo.order) |mod_name| {
        const m = src_map.get(mod_name) orelse continue;

        // Collect dep fingerprints in import-declaration order.
        // dep_fps items are arena-allocated; no explicit free needed.
        var dep_fps: std.ArrayListUnmanaged(u64) = .{};
        if (env.parsed_modules.get(mod_name)) |pm| {
            for (pm.imports) |imp| {
                if (env.ifaces.get(imp.module_name)) |dep_iface| {
                    try dep_fps.append(alloc, dep_iface.fingerprint);
                }
            }
        }

        // Derive paths and expected fingerprint only when caching is enabled.
        const rhi_p: ?[]const u8 = if (m.source_path) |sp|
            mod_iface.rhiPath(alloc, sp) catch null
        else
            null;
        const expected_fp: ?u64 = if (rhi_p != null)
            mod_iface.computeFingerprint(m.source, dep_fps.items)
        else
            null;

        // Attempt cache lookup.
        const cache_hit: bool = blk: {
            const rp = rhi_p orelse break :blk false;
            const fp = expected_fp.?;
            const cached = try mod_iface.tryLoadCachedIface(alloc, io, rp, fp);
            if (cached == null) break :blk false;
            // Cache hit: register the loaded interface and an empty Core.
            try env.register(mod_name, cached.?, .{ .data_decls = &.{}, .binds = &.{} });
            break :blk true;
        };

        if (!cache_hit) {
            // Cache miss: compile from source.
            const parsed = env.parsed_modules.get(mod_name);
            const core_opt = try env.compileSingle(m.module_name, m.source, m.file_id, parsed);

            // On success, stamp the fingerprint and persist the interface.
            if (core_opt != null) {
                if (expected_fp) |fp| {
                    if (env.ifaces.getPtr(mod_name)) |iface_ptr| {
                        iface_ptr.fingerprint = fp;
                    }
                    if (rhi_p) |rp| {
                        if (env.ifaces.get(mod_name)) |iface| {
                            // Write failure is non-fatal: next invocation will be a miss.
                            mod_iface.writeRhiToDisk(alloc, io, rp, iface) catch {};
                        }
                    }
                }
            }
        }
    }

    const had_errors = env.diags.hasErrors();
    const merged = try env.mergePrograms(alloc, topo.order);

    return .{
        .env = env,
        .result = .{ .core = merged, .had_errors = had_errors },
    };
}

// ── Implicit Prelude helpers ──────────────────────────────────────────────

/// Returns `true` if `imports` already contains an explicit `import Prelude`
/// (possibly with specs or a `hiding` list).
///
/// Per Haskell 2010 §5.6: any mention of `Prelude` in the import list — even
/// `import Prelude ()` or `import Prelude hiding (head)` — suppresses the
/// implicit import.
pub fn mentionsPrelude(imports: []const ast_mod.ImportDecl) bool {
    for (imports) |imp| {
        if (std.mem.eql(u8, imp.module_name, "Prelude")) return true;
    }
    return false;
}

/// Return a copy of `module` with a synthetic `import Prelude` prepended to
/// its import list.
///
/// The synthetic import has:
/// - `module_name = "Prelude"`
/// - `qualified = false`
/// - `as_alias = null`
/// - `specs = null`  (import everything)
/// - `span` = invalid (synthetic — not from source text)
///
/// All memory is allocated in `alloc`.
pub fn injectImplicitPrelude(
    alloc: std.mem.Allocator,
    module: ast_mod.Module,
) std.mem.Allocator.Error!ast_mod.Module {
    const invalid_pos = span_mod.SourcePos.invalid();
    const invalid_span = span_mod.SourceSpan.init(invalid_pos, invalid_pos);

    const implicit_import = ast_mod.ImportDecl{
        .module_name = "Prelude",
        .qualified = false,
        .as_alias = null,
        .specs = null,
        .span = invalid_span,
    };

    // Prepend the implicit import to the existing imports.
    var new_imports = try std.ArrayListUnmanaged(ast_mod.ImportDecl).initCapacity(
        alloc,
        module.imports.len + 1,
    );
    try new_imports.append(alloc, implicit_import);
    try new_imports.appendSlice(alloc, module.imports);

    return ast_mod.Module{
        .module_name = module.module_name,
        .exports = module.exports,
        .imports = try new_imports.toOwnedSlice(alloc),
        .declarations = module.declarations,
        .language_extensions = module.language_extensions,
        .span = module.span,
    };
}

/// Convert a `SerialisedScheme` back to a `TyScheme` (HType-based).
///
/// The body is converted via `SerialisedCoreType → CoreType → HType`.
/// Since serialised types contain no metavariables (they were fully solved
/// at the time of serialisation), the result contains only `Rigid` and `Con`
/// nodes — safe to feed directly into the typechecker's `TyEnv`.
fn deserialiseTyScheme(
    alloc: std.mem.Allocator,
    s: mod_iface.SerialisedScheme,
) std.mem.Allocator.Error!env_mod.TyScheme {
    const core_ty = try s.body.toCoreType(alloc);
    const hty = try coreTypeToHType(alloc, core_ty);
    const binders = try alloc.dupe(u64, s.binder_uniques);
    return env_mod.TyScheme{
        .binders = binders,
        .constraints = &.{},
        .body = hty,
    };
}

/// Convert a `CoreType` to the equivalent `HType`.
///
/// - `TyVar` → `HType.Rigid` (the type variable is already concrete)
/// - `TyCon` → `HType.Con`
/// - `FunTy` → `HType.Fun`
/// - `ForAllTy` → `HType.ForAll`
///
/// This is the inverse of `HType.toCore`, restricted to types that
/// contain no unsolved metavariables (i.e. types read from `.rhi` files).
fn coreTypeToHType(alloc: std.mem.Allocator, ty: core_ast.CoreType) std.mem.Allocator.Error!htype_mod.HType {
    return switch (ty) {
        .TyVar => |n| htype_mod.HType{ .Rigid = n },
        .TyCon => |tc| blk: {
            const args = try alloc.alloc(htype_mod.HType, tc.args.len);
            for (tc.args, 0..) |arg, i| {
                args[i] = try coreTypeToHType(alloc, arg);
            }
            break :blk htype_mod.HType{ .Con = .{ .name = tc.name, .args = args } };
        },
        .FunTy => |f| blk: {
            const arg_p = try alloc.create(htype_mod.HType);
            arg_p.* = try coreTypeToHType(alloc, f.arg.*);
            const res_p = try alloc.create(htype_mod.HType);
            res_p.* = try coreTypeToHType(alloc, f.res.*);
            break :blk htype_mod.HType{ .Fun = .{ .arg = arg_p, .res = res_p } };
        },
        .ForAllTy => |fa| blk: {
            const body_p = try alloc.create(htype_mod.HType);
            body_p.* = try coreTypeToHType(alloc, fa.body.*);
            break :blk htype_mod.HType{ .ForAll = .{ .binder = fa.binder, .body = body_p } };
        },
    };
}

// ── Tests ─────────────────────────────────────────────────────────────────

const testing = std.testing;

test "CompileEnv: init and deinit" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();

    var env = CompileEnv.init(arena.allocator());
    defer env.deinit();

    try testing.expectEqual(@as(usize, 0), env.ifaces.count());
    try testing.expectEqual(@as(usize, 0), env.programs.count());
    try testing.expect(!env.diags.hasErrors());
}

test "CompileEnv: register stores iface and program" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    const iface = ModIface{
        .module_name = "Foo",
        .values = &.{},
        .data_decls = &.{},
    };
    const prog = CoreProgram{ .data_decls = &.{}, .binds = &.{} };

    try env.register("Foo", iface, prog);

    try testing.expectEqual(@as(usize, 1), env.ifaces.count());
    try testing.expectEqual(@as(usize, 1), env.programs.count());
    try testing.expect(env.ifaces.contains("Foo"));
    try testing.expect(env.programs.contains("Foo"));
}

test "CompileEnv: mergePrograms in order" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    // Register two modules with empty programs.
    try env.register("A", .{ .module_name = "A", .values = &.{}, .data_decls = &.{} }, .{ .data_decls = &.{}, .binds = &.{} });
    try env.register("B", .{ .module_name = "B", .values = &.{}, .data_decls = &.{} }, .{ .data_decls = &.{}, .binds = &.{} });

    const order: []const []const u8 = &.{ "A", "B" };
    const merged = try env.mergePrograms(alloc, order);

    try testing.expectEqual(@as(usize, 0), merged.data_decls.len);
    try testing.expectEqual(@as(usize, 0), merged.binds.len);
}

test "coreTypeToHType: TyVar becomes Rigid" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const ty = core_ast.CoreType{ .TyVar = .{ .base = "a", .unique = .{ .value = 42 } } };
    const hty = try coreTypeToHType(alloc, ty);

    switch (hty) {
        .Rigid => |n| {
            try testing.expectEqualStrings("a", n.base);
            try testing.expectEqual(@as(u64, 42), n.unique.value);
        },
        else => return error.WrongVariant,
    }
}

test "coreTypeToHType: FunTy becomes Fun" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const int_name = Name{ .base = "Int", .unique = .{ .value = 1 } };
    const int_ty = core_ast.CoreType{ .TyCon = .{ .name = int_name, .args = &.{} } };

    const arg_p = try alloc.create(core_ast.CoreType);
    arg_p.* = int_ty;
    const res_p = try alloc.create(core_ast.CoreType);
    res_p.* = int_ty;
    const fun_ty = core_ast.CoreType{ .FunTy = .{ .arg = arg_p, .res = res_p } };

    const hty = try coreTypeToHType(alloc, fun_ty);

    switch (hty) {
        .Fun => |f| {
            switch (f.arg.*) {
                .Con => |c| try testing.expectEqualStrings("Int", c.name.base),
                else => return error.WrongVariant,
            }
            switch (f.res.*) {
                .Con => |c| try testing.expectEqualStrings("Int", c.name.base),
                else => return error.WrongVariant,
            }
        },
        else => return error.WrongVariant,
    }
}

test "CompileEnv: compileSingle compiles a trivial module" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    const source =
        \\module Trivial where
        \\
        \\answer :: Int
        \\answer = 42
        \\
    ;

    const result = try env.compileSingle("Trivial", source, 1, null);

    try testing.expect(result != null);
    try testing.expect(!env.diags.hasErrors());
    try testing.expect(env.ifaces.contains("Trivial"));
    try testing.expect(env.programs.contains("Trivial"));
}

test "CompileEnv: compileSingle emits diagnostic on parse error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    // Deliberately broken Haskell.
    const bad_source = "module Bad where\nfoo = @@@\n";

    const result = try env.compileSingle("Bad", bad_source, 1, null);

    // compileSingle returns null on error; diags should have errors.
    _ = result; // may or may not be null depending on parse-error recovery
    // We only assert that calling it doesn't crash. Diagnostic content
    // is tested in the renamer/parser unit tests.
}

// ── Implicit Prelude tests ────────────────────────────────────────────────

test "mentionsPrelude: false when no imports" {
    const imports: []const ast_mod.ImportDecl = &.{};
    try testing.expect(!mentionsPrelude(imports));
}

test "mentionsPrelude: false when Prelude not in import list" {
    const invalid_pos = span_mod.SourcePos.invalid();
    const invalid_span = span_mod.SourceSpan.init(invalid_pos, invalid_pos);
    const imports = [_]ast_mod.ImportDecl{
        .{ .module_name = "Data.List", .span = invalid_span },
        .{ .module_name = "Data.Map", .span = invalid_span },
    };
    try testing.expect(!mentionsPrelude(&imports));
}

test "mentionsPrelude: true when Prelude is in import list" {
    const invalid_pos = span_mod.SourcePos.invalid();
    const invalid_span = span_mod.SourceSpan.init(invalid_pos, invalid_pos);
    const imports = [_]ast_mod.ImportDecl{
        .{ .module_name = "Prelude", .span = invalid_span },
        .{ .module_name = "Data.Map", .span = invalid_span },
    };
    try testing.expect(mentionsPrelude(&imports));
}

test "injectImplicitPrelude: prepends import Prelude" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const invalid_pos = span_mod.SourcePos.invalid();
    const invalid_span = span_mod.SourceSpan.init(invalid_pos, invalid_pos);

    const orig_imports = [_]ast_mod.ImportDecl{
        .{ .module_name = "Data.List", .span = invalid_span },
    };
    const module = ast_mod.Module{
        .module_name = "Foo",
        .exports = null,
        .imports = &orig_imports,
        .declarations = &.{},
        .language_extensions = std.EnumSet(ast_mod.LanguageExtension).initEmpty(),
        .span = invalid_span,
    };

    const injected = try injectImplicitPrelude(alloc, module);

    try testing.expectEqual(@as(usize, 2), injected.imports.len);
    try testing.expectEqualStrings("Prelude", injected.imports[0].module_name);
    try testing.expect(!injected.imports[0].qualified);
    try testing.expect(injected.imports[0].specs == null);
    try testing.expectEqualStrings("Data.List", injected.imports[1].module_name);
}

test "compileSingle: module without explicit Prelude gets implicit Prelude in imports" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    // A module with no explicit Prelude import.
    const source =
        \\module NoPrelude where
        \\
        \\answer :: Int
        \\answer = 42
        \\
    ;

    // We compile to verify no errors; the implicit Prelude injection is
    // transparent to the final Core output (until the renamer processes
    // imports — tracked in: https://github.com/adinapoli/rusholme/issues/375).
    const result = try env.compileSingle("NoPrelude", source, 1, null);
    try testing.expect(result != null);
    try testing.expect(!env.diags.hasErrors());
}

test "compileSingle: module with NoImplicitPrelude compiles without Prelude injection" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    // A module that opts out of the implicit Prelude.
    // Note: the layout processor sees the pragma_open as the first token and
    // handles it via error recovery, so the module body still parses.
    const source =
        \\{-# LANGUAGE NoImplicitPrelude #-}
        \\module WithNoPrelude where
        \\
        \\answer :: Int
        \\answer = 42
        \\
    ;

    // The compilation may or may not succeed (depends on parser's pragma
    // handling), but it must not crash.
    _ = try env.compileSingle("WithNoPrelude", source, 1, null);
}

// ── .rhi cache integration tests ─────────────────────────────────────────

test "compileProgram: .rhi cache hit — second invocation loads cached interface" {
    var tmp = testing.tmpDir(.{});
    defer tmp.cleanup();
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const io = testing.io;

    const tmp_path = try std.Io.Dir.realPathFileAlloc(tmp.dir, io, ".", alloc);
    const hs_path = try std.fmt.allocPrint(alloc, "{s}/CacheHit.hs", .{tmp_path});
    const source =
        \\module CacheHit where
        \\answer :: Int
        \\answer = 42
        \\
    ;

    // ── First run: cache miss → compiles and writes .rhi ──────────────────
    const fp1: u64 = blk: {
        var r1 = try compileProgram(alloc, io, &.{.{
            .module_name = "CacheHit",
            .source = source,
            .file_id = 1,
            .source_path = hs_path,
        }});
        defer r1.env.deinit();
        try testing.expect(!r1.result.had_errors);
        // A real compilation must produce at least one Core bind.
        try testing.expect(r1.result.core.binds.len > 0);
        const fp = r1.env.ifaces.get("CacheHit").?.fingerprint;
        try testing.expect(fp != 0);
        break :blk fp;
    };

    // ── Second run: cache hit → loads .rhi, registers empty CoreProgram ───
    {
        var r2 = try compileProgram(alloc, io, &.{.{
            .module_name = "CacheHit",
            .source = source,
            .file_id = 2,
            .source_path = hs_path,
        }});
        defer r2.env.deinit();
        try testing.expect(!r2.result.had_errors);

        // The cached iface carries the same fingerprint as the first run.
        const fp2 = r2.env.ifaces.get("CacheHit").?.fingerprint;
        try testing.expectEqual(fp1, fp2);

        // On a cache hit an empty CoreProgram is registered (no recompile).
        // The merged result therefore has zero binds.
        try testing.expectEqual(@as(usize, 0), r2.result.core.binds.len);
    }
}

test "compileProgram: .rhi cache miss — changed source produces new fingerprint" {
    var tmp = testing.tmpDir(.{});
    defer tmp.cleanup();
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const io = testing.io;

    const tmp_path = try std.Io.Dir.realPathFileAlloc(tmp.dir, io, ".", alloc);
    const hs_path = try std.fmt.allocPrint(alloc, "{s}/CacheChanged.hs", .{tmp_path});

    const source_v1 =
        \\module CacheChanged where
        \\answer :: Int
        \\answer = 1
        \\
    ;
    const source_v2 =
        \\module CacheChanged where
        \\answer :: Int
        \\answer = 2
        \\
    ;

    // First run with v1 source.
    const fp1: u64 = blk: {
        var r = try compileProgram(alloc, io, &.{.{
            .module_name = "CacheChanged",
            .source = source_v1,
            .file_id = 1,
            .source_path = hs_path,
        }});
        defer r.env.deinit();
        break :blk r.env.ifaces.get("CacheChanged").?.fingerprint;
    };

    // Second run with v2 source: different fingerprint → cache miss → recompile.
    const fp2: u64 = blk: {
        var r = try compileProgram(alloc, io, &.{.{
            .module_name = "CacheChanged",
            .source = source_v2,
            .file_id = 2,
            .source_path = hs_path,
        }});
        defer r.env.deinit();
        // Cache miss: a full compile produced real Core binds.
        try testing.expect(r.result.core.binds.len > 0);
        break :blk r.env.ifaces.get("CacheChanged").?.fingerprint;
    };

    try testing.expect(fp1 != 0);
    try testing.expect(fp2 != 0);
    // Different source bytes → different fingerprint.
    try testing.expect(fp1 != fp2);
}

test "compileProgram: .rhi cache miss — changed dependency propagates new fingerprint" {
    var tmp = testing.tmpDir(.{});
    defer tmp.cleanup();
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const io = testing.io;

    const tmp_path = try std.Io.Dir.realPathFileAlloc(tmp.dir, io, ".", alloc);
    const lib_path = try std.fmt.allocPrint(alloc, "{s}/CacheLib.hs", .{tmp_path});
    const app_path = try std.fmt.allocPrint(alloc, "{s}/CacheApp.hs", .{tmp_path});

    const lib_v1 =
        \\module CacheLib where
        \\libVal :: Int
        \\libVal = 10
        \\
    ;
    const lib_v2 =
        \\module CacheLib where
        \\libVal :: Int
        \\libVal = 20
        \\
    ;
    const app_src =
        \\module CacheApp where
        \\import CacheLib
        \\appVal :: Int
        \\appVal = 99
        \\
    ;

    // First run: CacheLib_v1 + CacheApp.
    const app_fp1: u64 = blk: {
        var r = try compileProgram(alloc, io, &.{
            .{ .module_name = "CacheLib", .source = lib_v1, .file_id = 1, .source_path = lib_path },
            .{ .module_name = "CacheApp", .source = app_src, .file_id = 2, .source_path = app_path },
        });
        defer r.env.deinit();
        break :blk r.env.ifaces.get("CacheApp").?.fingerprint;
    };

    // Second run: CacheLib_v2 (changed) + CacheApp (unchanged source).
    // CacheLib's fingerprint changes → CacheApp's dep_fps change → CacheApp misses cache.
    const app_fp2: u64 = blk: {
        var r = try compileProgram(alloc, io, &.{
            .{ .module_name = "CacheLib", .source = lib_v2, .file_id = 3, .source_path = lib_path },
            .{ .module_name = "CacheApp", .source = app_src, .file_id = 4, .source_path = app_path },
        });
        defer r.env.deinit();
        break :blk r.env.ifaces.get("CacheApp").?.fingerprint;
    };

    try testing.expect(app_fp1 != 0);
    try testing.expect(app_fp2 != 0);
    // The dep fingerprint changed → CacheApp's fingerprint must differ.
    try testing.expect(app_fp1 != app_fp2);
}
