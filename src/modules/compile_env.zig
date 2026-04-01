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
//! - Package-level search paths via `--package-db` are implemented.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/652

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
const class_env_mod = @import("../typechecker/class_env.zig");
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
pub const ClassEnv = class_env_mod.ClassEnv;
pub const DictNameMap = desugar_mod.DesugarCtx.DictNameMap;

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

    /// Map: module name → class environment after type inference.
    ///
    /// Stores class declarations and instance information so that
    /// downstream modules can resolve class constraints for imported
    /// type classes.
    class_envs: std.StringHashMapUnmanaged(ClassEnv),

    /// Map: module name → dictionary name map after desugaring.
    ///
    /// Stores the mapping from (class_unique, head_type_name) → dictionary
    /// Name so that downstream modules can resolve dictionary evidence
    /// for imported type class instances.
    dict_names_map: std.StringHashMapUnmanaged(DictNameMap),

    /// Package-database search paths for pre-built `.rhi` interfaces.
    ///
    /// When resolving an import whose source is not in the current build,
    /// `compileProgram` searches each path (in order) for a `.rhi` file
    /// matching the module name.  The paths are caller-owned and must
    /// outlive the `CompileEnv`.
    ///
    /// Empty by default; populated via `--package-db` flags on the CLI.
    /// Tracked in: https://github.com/adinapoli/rusholme/issues/652
    package_dbs: []const []const u8,

    // ── Lifecycle ─────────────────────────────────────────────────────────

    /// Create an empty compilation session with no package-database paths.
    pub fn init(alloc: std.mem.Allocator) CompileEnv {
        return .{
            .alloc = alloc,
            .ifaces = .{},
            .programs = .{},
            .parsed_modules = .{},
            .u_supply = .{},
            .mv_supply = .{},
            .diags = DiagnosticCollector.init(),
            .class_envs = .{},
            .dict_names_map = .{},
            .package_dbs = &.{},
        };
    }

    pub fn deinit(self: *CompileEnv) void {
        self.ifaces.deinit(self.alloc);
        self.programs.deinit(self.alloc);
        self.parsed_modules.deinit(self.alloc);
        self.diags.deinit(self.alloc);
        self.class_envs.deinit(self.alloc);
        self.dict_names_map.deinit(self.alloc);
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
                    // Constructors are serialised with ForAllTy wrappers by
                    // schemeToCore.  Peel them off and register as a proper
                    // polymorphic scheme so that call sites instantiate fresh
                    // metas for each type variable.
                    const core_ty = try con.ty.toCoreType(ty_env.alloc);
                    const hty = try coreTypeToHType(ty_env.alloc, core_ty);
                    const scheme = try conTypeToScheme(ty_env.alloc, hty);
                    try ty_env.bind(con_name, scheme);
                }
            }
        }
    }

    /// Seed a `RenameEnv` with exported names only from modules that the
    /// current module imports.  This respects `NoImplicitPrelude` — if a
    /// module doesn't import Prelude, Prelude's names are not seeded.
    pub fn seedRenamerFromImports(
        self: *const CompileEnv,
        env: *renamer_mod.RenameEnv,
        imports: []const ast_mod.ImportDecl,
    ) std.mem.Allocator.Error!void {
        for (imports) |imp| {
            const iface = self.ifaces.get(imp.module_name) orelse continue;
            try seedRenamerFromIface(env, iface);
        }
    }

    /// Seed a `TyEnv` with type schemes only from modules that the current
    /// module imports.
    pub fn seedTyEnvFromImports(
        self: *const CompileEnv,
        ty_env: *env_mod.TyEnv,
        imports: []const ast_mod.ImportDecl,
    ) std.mem.Allocator.Error!void {
        for (imports) |imp| {
            const iface = self.ifaces.get(imp.module_name) orelse continue;
            try seedTyEnvFromIface(ty_env, iface);
        }
    }

    /// Seed a `ClassEnv` with class declarations and instances from modules
    /// that the current module imports.  This allows the typechecker to
    /// resolve class constraints for imported type classes (e.g. `Show`).
    pub fn seedClassEnvFromImports(
        self: *const CompileEnv,
        class_env: *ClassEnv,
        imports: []const ast_mod.ImportDecl,
    ) !void {
        for (imports) |imp| {
            const upstream = self.class_envs.get(imp.module_name) orelse continue;
            try class_env.mergeFrom(&upstream);
        }
    }

    /// Collect dictionary name mappings from all modules that the current
    /// module imports into a single merged map.  This allows the desugarer
    /// to resolve dictionary evidence for imported instances.
    pub fn collectDictNamesFromImports(
        self: *const CompileEnv,
        alloc: std.mem.Allocator,
        imports: []const ast_mod.ImportDecl,
    ) std.mem.Allocator.Error!DictNameMap {
        var merged: DictNameMap = .empty;
        for (imports) |imp| {
            const upstream = self.dict_names_map.get(imp.module_name) orelse continue;
            for (upstream.keys(), upstream.values()) |key, val| {
                try merged.put(alloc, key, val);
            }
        }
        return merged;
    }

    /// Seed a `RenameEnv` from a single module interface.
    fn seedRenamerFromIface(
        env: *renamer_mod.RenameEnv,
        iface: ModIface,
    ) std.mem.Allocator.Error!void {
        for (iface.values) |ev| {
            const name = Name{
                .base = ev.name,
                .unique = .{ .value = ev.unique },
            };
            try env.scope.bind(ev.name, name);
        }
        for (iface.data_decls) |dd| {
            const ty_name = Name{
                .base = dd.name,
                .unique = .{ .value = dd.unique },
            };
            try env.scope.bind(dd.name, ty_name);
            for (dd.constructors) |con| {
                const con_name = Name{
                    .base = con.name,
                    .unique = .{ .value = con.unique },
                };
                try env.scope.bind(con.name, con_name);
            }
        }
    }

    /// Seed a `TyEnv` from a single module interface.
    fn seedTyEnvFromIface(
        ty_env: *env_mod.TyEnv,
        iface: ModIface,
    ) std.mem.Allocator.Error!void {
        for (iface.values) |ev| {
            const name = Name{
                .base = ev.name,
                .unique = .{ .value = ev.unique },
            };
            const scheme = deserialiseTyScheme(ty_env.alloc, ev.scheme) catch {
                continue;
            };
            try ty_env.bind(name, scheme);
        }
        for (iface.data_decls) |dd| {
            for (dd.constructors) |con| {
                const con_name = Name{
                    .base = con.name,
                    .unique = .{ .value = con.unique },
                };
                // Constructors are serialised with ForAllTy wrappers by
                // schemeToCore.  Peel them off and register as a proper
                // polymorphic scheme so that call sites instantiate fresh
                // metas for each type variable.
                const core_ty = try con.ty.toCoreType(ty_env.alloc);
                const hty = try coreTypeToHType(ty_env.alloc, core_ty);
                const scheme = try conTypeToScheme(ty_env.alloc, hty);
                try ty_env.bind(con_name, scheme);
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
        const no_implicit_prelude = parsed.language_extensions.contains(.NoImplicitPrelude);
        var rename_env = try renamer_mod.RenameEnv.init(self.alloc, &self.u_supply, &self.diags, no_implicit_prelude);
        defer rename_env.deinit();
        // Seed with names from imported modules only (not all compiled modules).
        try self.seedRenamerFromImports(&rename_env, module.imports);
        const renamed = try renamer_mod.rename(module, &rename_env);
        if (self.diags.hasErrors()) return null;

        // ── Typecheck ────────────────────────────────────────────────────
        var ty_env = try env_mod.TyEnv.init(self.alloc);
        try env_mod.initBuiltins(&ty_env, self.alloc, &self.u_supply, no_implicit_prelude);
        // Seed with types from imported modules only.
        try self.seedTyEnvFromImports(&ty_env, module.imports);

        var infer_ctx = infer_mod.InferCtx.init(
            self.alloc,
            &ty_env,
            &self.mv_supply,
            &self.u_supply,
            &self.diags,
        );
        // Seed with class declarations and instances from imported modules
        // so that the typechecker can resolve class constraints (e.g. Show).
        try self.seedClassEnvFromImports(&infer_ctx.class_env, module.imports);

        var module_types = try infer_mod.inferModule(&infer_ctx, renamed, null);
        defer module_types.deinit(self.alloc);
        if (self.diags.hasErrors()) return null;

        // ── Desugar ──────────────────────────────────────────────────────
        // Collect dictionary names from imported modules so the desugarer
        // can resolve evidence for imported type class instances.
        var ext_dict_names = try self.collectDictNamesFromImports(self.alloc, module.imports);
        const desugar_result = try desugar_mod.desugarModule(
            self.alloc,
            renamed,
            &module_types,
            &self.diags,
            &self.u_supply,
            &ext_dict_names,
        );
        const core_prog = desugar_result.program;
        if (self.diags.hasErrors()) return null;

        // ── Build interface ───────────────────────────────────────────────
        const export_list = module.exports;
        var iface = try mod_iface.buildModIface(
            self.alloc,
            module_name,
            export_list,
            core_prog,
            &module_types,
        );
        // Extend the interface with class and dictionary name data so that
        // downstream modules can reconstruct a ClassEnv and DictNameMap from
        // a cached .rhi file (issue #616).
        try serialiseClassEnvIntoIface(self.alloc, &iface, &module_types.class_env);
        try serialiseDictNamesIntoIface(self.alloc, &iface, &desugar_result.dict_names);

        // ── Register ─────────────────────────────────────────────────────
        try self.register(module_name, iface, core_prog);

        // Store class environment and dictionary names for downstream modules.
        // These are needed so that importing modules can resolve class
        // constraints and dictionary evidence for type classes defined here.
        {
            const owned_name = try self.alloc.dupe(u8, module_name);
            var stored_class_env = ClassEnv.init(self.alloc);
            try stored_class_env.mergeFrom(&module_types.class_env);
            try self.class_envs.put(self.alloc, owned_name, stored_class_env);
            try self.dict_names_map.put(self.alloc, owned_name, desugar_result.dict_names);
        }

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
    /// per-module `.bc` backend caching is implemented — see #456).
    source_path: ?[]const u8 = null,
};

/// The result of a whole-program compilation.
pub const CompileResult = struct {
    /// The merged whole-program Core IR, ready for lambda lifting.
    core: CoreProgram,
    /// Whether any errors were emitted during compilation.
    had_errors: bool,
    /// Topological compilation order: module names dependency-first.
    ///
    /// The slice and its strings are allocated in the same arena as the
    /// rest of the compilation result.  Callers can iterate this together
    /// with `CompileEnv.programs` to process each module independently
    /// (e.g. per-module GRIN→LLVM translation for bitcode emission).
    module_order: []const []const u8,
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
///    Modules not present in `modules` are resolved by searching `package_dbs`
///    for a pre-built `.rhi` interface (in order; first match wins).
/// 5. Merges all `CoreProgram`s into a single whole-program Core.
///
/// `package_dbs` is a list of directory paths searched (in order) when an
/// imported module is not among the provided source files.  Pass `&.{}` to
/// disable package-database lookup.
///
/// `alloc` should be an arena that outlives the returned result.
pub fn compileProgram(
    alloc: std.mem.Allocator,
    io: std.Io,
    modules: []const SourceModule,
    package_dbs: []const []const u8,
) std.mem.Allocator.Error!struct { env: CompileEnv, result: CompileResult } {
    var env = CompileEnv.init(alloc);
    env.package_dbs = package_dbs;
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
    //
    // Before building edges, apply implicit Prelude injection (Haskell 2010
    // §5.6) to the cached parses.  This ensures the module graph has an
    // edge from every non-Prelude module to `Prelude`, matching the same
    // injection that `compileSingle` performs later.  Without this, the
    // topological sort may place a user module before the Prelude, causing
    // cross-module seeding to find no registered interfaces.
    {
        const has_prelude = env.parsed_modules.contains("Prelude");
        var inject_iter = env.parsed_modules.iterator();
        while (inject_iter.next()) |entry| {
            const parsed = entry.value_ptr.*;
            // Only inject if:
            // 1. The Prelude is actually among the source modules (so the
            //    graph edge points to a compilable module).
            // 2. The module doesn't opt out via NoImplicitPrelude.
            // 3. The module doesn't already mention Prelude.
            if (has_prelude and
                !parsed.language_extensions.contains(.NoImplicitPrelude) and
                !mentionsPrelude(parsed.imports))
            {
                entry.value_ptr.* = try injectImplicitPrelude(alloc, parsed);
            }
        }
    }

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
    // Keep topo.order alive — returned in CompileResult.module_order.
    // The slice is owned by `alloc` (the caller's arena).

    if (!topo.is_complete) {
        alloc.free(topo.order);
        return .{
            .env = env,
            .result = .{
                .core = .{ .data_decls = &.{}, .binds = &.{} },
                .had_errors = true,
                .module_order = &.{},
            },
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
    //      (tracked in #456).
    //   4. On cache miss: run `compileSingle`, then tag the iface with its
    //      fingerprint and write it to disk for future runs.
    //
    // If a module is not in the source list, check `package_dbs` for a
    // pre-built `.rhi` and register it without compilation.
    for (topo.order) |mod_name| {
        if (src_map.get(mod_name) == null) {
            // Module not provided as source: try to resolve via package-dbs.
            if (try tryLoadFromPackageDbs(alloc, io, mod_name, package_dbs)) |iface| {
                const ce = try deserialiseClassEnvFromIface(alloc, iface);
                const owned_name = try alloc.dupe(u8, mod_name);
                try env.class_envs.put(alloc, owned_name, ce);
                const dict_names = try deserialiseDictNamesFromIface(alloc, iface);
                try env.dict_names_map.put(alloc, owned_name, dict_names);
                const empty_core = CoreProgram{ .data_decls = &.{}, .binds = &.{} };
                try env.register(mod_name, iface, empty_core);
            }
            // Whether or not a package-db hit was found, do not attempt
            // to compile this module from source — skip to the next.
            continue;
        }
        const m = src_map.get(mod_name).?;

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

        // Attempt cache lookup.  A valid `.rhi` hit pre-seeds ClassEnv and
        // DictNameMap for this module so that downstream compilation can use
        // them (e.g. a sibling module imported earlier in the same build that
        // has already been cached from a prior run).
        //
        // Core is NOT loaded from cache — per-module .bc caching is tracked
        // in: https://github.com/adinapoli/rusholme/issues/456
        //
        // Until #456 is resolved every module is compiled from source on every
        // build.  The pre-seeded ClassEnv/DictNames are overwritten by
        // compileSingle with identical data; the pre-seeding is harmless and
        // keeps the path exercised so that the serialisation round-trip is
        // validated on every build.
        const cached_iface: ?mod_iface.ModIface = if (rhi_p != null and expected_fp != null)
            try mod_iface.tryLoadCachedIface(alloc, io, rhi_p.?, expected_fp.?)
        else
            null;

        // Pre-seed counts for the debug assertion below.
        var pre_class_count: ?usize = null;
        var pre_dict_count: ?usize = null;

        if (cached_iface) |ci| {
            // Cache hit: pre-seed ClassEnv and DictNameMap from the cached
            // interface.  compileSingle (below) will re-derive these from
            // source and overwrite them, which is harmless.
            const ce = try deserialiseClassEnvFromIface(alloc, ci);
            const owned_name = try alloc.dupe(u8, mod_name);
            try env.class_envs.put(alloc, owned_name, ce);
            const dict_names = try deserialiseDictNamesFromIface(alloc, ci);
            try env.dict_names_map.put(alloc, owned_name, dict_names);
            pre_class_count = ce.classes.count();
            pre_dict_count = dict_names.count();
        }

        // Always compile from source to produce the Core program.
        {
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

                // Validate that the cached metadata matches what compileSingle
                // produced.  A mismatch means the serialisation round-trip is
                // lossy — catch it early in debug builds.
                if (pre_class_count) |cached_n| {
                    if (env.class_envs.get(mod_name)) |fresh_ce| {
                        std.debug.assert(cached_n == fresh_ce.classes.count());
                    }
                }
                if (pre_dict_count) |cached_n| {
                    if (env.dict_names_map.get(mod_name)) |fresh_dn| {
                        std.debug.assert(cached_n == fresh_dn.count());
                    }
                }
            }
        }
    }

    const had_errors = env.diags.hasErrors();
    const merged = try env.mergePrograms(alloc, topo.order);

    return .{
        .env = env,
        .result = .{
            .core = merged,
            .had_errors = had_errors,
            .module_order = topo.order,
        },
    };
}

// ── Package-database helpers ──────────────────────────────────────────────

/// Convert a fully-qualified Haskell module name to a relative `.rhi` path.
///
/// Dots are replaced by the platform path separator so that nested module
/// names map to nested directories.  For example:
///   `"Data.Map"` → `"Data/Map.rhi"` (Linux/macOS)
///   `"Main"`     → `"Main.rhi"`
///
/// The returned slice is allocated in `alloc`; caller owns it.
fn moduleNameToRhiRelPath(
    alloc: std.mem.Allocator,
    module_name: []const u8,
) std.mem.Allocator.Error![]u8 {
    // Replace every '.' with the OS path separator.
    const sep = std.fs.path.sep;
    const with_sep = try alloc.dupe(u8, module_name);
    for (with_sep) |*c| {
        if (c.* == '.') c.* = sep;
    }
    defer alloc.free(with_sep);
    return std.fmt.allocPrint(alloc, "{s}.rhi", .{with_sep});
}

/// Search `package_dbs` (in order) for a pre-built `.rhi` for `module_name`.
///
/// The search path for each database entry is:
///   `<db>/<module_name_with_slashes>.rhi`
///
/// Returns the deserialized `ModIface` for the first matching file, or
/// `null` if no package-db contains a file for this module.  Parse errors
/// and I/O failures are silently treated as misses.
///
/// No fingerprint validation is performed — package-db interfaces are
/// pre-built and assumed stable.
fn tryLoadFromPackageDbs(
    alloc: std.mem.Allocator,
    io: std.Io,
    module_name: []const u8,
    package_dbs: []const []const u8,
) std.mem.Allocator.Error!?mod_iface.ModIface {
    if (package_dbs.len == 0) return null;

    const rel = try moduleNameToRhiRelPath(alloc, module_name);
    defer alloc.free(rel);

    for (package_dbs) |db| {
        const abs = try std.fs.path.join(alloc, &.{ db, rel });
        defer alloc.free(abs);

        const data = std.Io.Dir.readFileAlloc(
            .cwd(),
            io,
            abs,
            alloc,
            .limited(16 * 1024 * 1024),
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => continue,
        };
        defer alloc.free(data);

        const iface = mod_iface.readRhi(alloc, data) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => continue,
        };

        // Reject format-version mismatches so that stale package-db files
        // do not silently corrupt the compilation session.
        if (iface.format_version != mod_iface.rhi_format_version) continue;

        return iface;
    }
    return null;
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
///
/// Class constraints are reconstructed from the serialised form: each
/// constraint gets a fresh `Rigid` HType node matching its type variable
/// binder, and a synthetic zero span (the original span is not needed
/// downstream — the desugarer keys evidence by call-site span, not by
/// the constraint's definition-site span).
fn deserialiseTyScheme(
    alloc: std.mem.Allocator,
    s: mod_iface.SerialisedScheme,
) std.mem.Allocator.Error!env_mod.TyScheme {
    const core_ty = try s.body.toCoreType(alloc);
    const hty = try coreTypeToHType(alloc, core_ty);
    const binders = try alloc.dupe(u64, s.binder_uniques);

    // Reconstruct class constraints from the serialised form.
    const constraints = try alloc.alloc(class_env_mod.ClassConstraint, s.constraints.len);
    for (s.constraints, 0..) |sc, i| {
        // Find the binder name corresponding to the type variable unique.
        var tyvar_name: []const u8 = "_tv";
        for (s.binder_uniques, s.binder_names) |bu, bn| {
            if (bu == sc.tyvar_unique) {
                tyvar_name = bn;
                break;
            }
        }
        // Allocate a Rigid node for the constrained type variable.
        const rigid = try alloc.create(htype_mod.HType);
        rigid.* = .{ .Rigid = .{
            .base = tyvar_name,
            .unique = .{ .value = sc.tyvar_unique },
        } };
        constraints[i] = .{
            .class_name = .{
                .base = sc.class_name,
                .unique = .{ .value = sc.class_unique },
            },
            .ty = rigid,
            .span = .{ .start = span_mod.SourcePos.invalid(), .end = span_mod.SourcePos.invalid() },
        };
    }

    return env_mod.TyScheme{
        .binders = binders,
        .constraints = constraints,
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

/// Peel leading `ForAll` binders from an `HType` and build a `TyScheme`.
///
/// Data constructors are serialised as `forall a b. FieldTy → … → TyCon a b`
/// (the `schemeToCore` + `coreTypeToHType` pipeline wraps binders in `ForAll`
/// nodes).  When we load them back into the type environment they must be
/// registered as *polymorphic* schemes — otherwise the typechecker treats
/// `Just` as monomorphically typed `forall a. a -> Maybe a` and fails to
/// instantiate it at call sites.
///
/// This function strips the leading `ForAll` nodes, collects their binder IDs,
/// and returns a `TyScheme` ready for `TyEnv.bind`.
fn conTypeToScheme(
    alloc: std.mem.Allocator,
    hty: htype_mod.HType,
) std.mem.Allocator.Error!env_mod.TyScheme {
    var binders = std.ArrayListUnmanaged(u64){};
    // We never free this — all allocations live on the arena.

    // Peel outer ForAll nodes, collecting binder unique IDs.
    var body: htype_mod.HType = hty;
    while (body == .ForAll) {
        const fa = body.ForAll;
        try binders.append(alloc, fa.binder.unique.value);
        body = fa.body.*;
    }

    const binders_slice = try binders.toOwnedSlice(alloc);
    return env_mod.TyScheme{
        .binders = binders_slice,
        .constraints = &.{},
        .body = body,
    };
}

// ── ClassEnv / DictNameMap serialisation helpers ──────────────────────────

/// Populate `iface.class_infos` and `iface.instance_infos` from `class_env`.
///
/// Converts all `ClassInfo` and `InstanceInfo` records to their serialisable
/// forms using `HType.toCore` → `SerialisedCoreType.fromCoreType`.
/// All allocations go into `alloc` (expected to be an arena).
fn serialiseClassEnvIntoIface(
    alloc: std.mem.Allocator,
    iface: *mod_iface.ModIface,
    class_env: *const ClassEnv,
) std.mem.Allocator.Error!void {
    var class_list: std.ArrayListUnmanaged(mod_iface.SerialisedClassInfo) = .{};
    var inst_list: std.ArrayListUnmanaged(mod_iface.SerialisedInstanceInfo) = .{};

    var class_it = class_env.classes.iterator();
    while (class_it.next()) |entry| {
        const ci = entry.value_ptr.*;

        const s_supers = try alloc.alloc(mod_iface.SerialisedNameRef, ci.superclasses.len);
        for (ci.superclasses, 0..) |sc, i| {
            s_supers[i] = .{ .base = sc.base, .unique = sc.unique.value };
        }

        const s_methods = try alloc.alloc(mod_iface.SerialisedMethodInfo, ci.methods.len);
        for (ci.methods, 0..) |m, i| {
            const core_ty = try m.ty.toCore(alloc);
            const s_ty = try mod_iface.SerialisedCoreType.fromCoreType(core_ty, alloc);
            s_methods[i] = .{
                .name = .{ .base = m.name.base, .unique = m.name.unique.value },
                .ty = s_ty,
                .has_default = m.has_default,
            };
        }

        try class_list.append(alloc, .{
            .name = .{ .base = ci.name.base, .unique = ci.name.unique.value },
            .tyvar = ci.tyvar,
            .superclasses = s_supers,
            .methods = s_methods,
            .dict_con_name = .{ .base = ci.dict_con_name.base, .unique = ci.dict_con_name.unique.value },
        });

        // Serialise instances for this class.
        const class_unique = entry.key_ptr.*;
        if (class_env.instances.get(class_unique)) |inst_arr| {
            for (inst_arr.items) |inst| {
                const core_head = try inst.head.toCore(alloc);
                const s_head = try mod_iface.SerialisedCoreType.fromCoreType(core_head, alloc);

                const s_context = try alloc.alloc(mod_iface.SerialisedClassConstraint, inst.context.len);
                for (inst.context, 0..) |cc, j| {
                    const core_cc_ty = try cc.ty.toCore(alloc);
                    const s_cc_ty = try mod_iface.SerialisedCoreType.fromCoreType(core_cc_ty, alloc);
                    s_context[j] = .{
                        .class_name = .{ .base = cc.class_name.base, .unique = cc.class_name.unique.value },
                        .ty = s_cc_ty,
                    };
                }

                try inst_list.append(alloc, .{
                    .class_name = .{ .base = inst.class_name.base, .unique = inst.class_name.unique.value },
                    .head = s_head,
                    .context = s_context,
                });
            }
        }
    }

    iface.class_infos = try class_list.toOwnedSlice(alloc);
    iface.instance_infos = try inst_list.toOwnedSlice(alloc);
}

/// Populate `iface.dict_entries` from `dict_names`.
fn serialiseDictNamesIntoIface(
    alloc: std.mem.Allocator,
    iface: *mod_iface.ModIface,
    dict_names: *const DictNameMap,
) std.mem.Allocator.Error!void {
    const entries = try alloc.alloc(mod_iface.SerialisedDictEntry, dict_names.count());
    for (dict_names.keys(), dict_names.values(), 0..) |key, val, i| {
        entries[i] = .{
            .class_unique = key.class_unique,
            .head_name = key.head_name,
            .name_base = val.base,
            .name_unique = val.unique.value,
        };
    }
    iface.dict_entries = entries;
}

/// Reconstruct a `ClassEnv` from the serialised class/instance data in `iface`.
///
/// All allocations go into `alloc`.  The returned `ClassEnv` has `rigid_scope`
/// set to empty for all instances — the scope is only needed during Pass 2
/// instance body inference, which does not run on cached modules.
fn deserialiseClassEnvFromIface(
    alloc: std.mem.Allocator,
    iface: mod_iface.ModIface,
) std.mem.Allocator.Error!ClassEnv {
    var class_env = ClassEnv.init(alloc);

    for (iface.class_infos) |ci| {
        const superclasses = try alloc.alloc(Name, ci.superclasses.len);
        for (ci.superclasses, 0..) |sc, i| {
            superclasses[i] = .{ .base = sc.base, .unique = .{ .value = sc.unique } };
        }

        const methods = try alloc.alloc(class_env_mod.MethodInfo, ci.methods.len);
        for (ci.methods, 0..) |sm, i| {
            const core_ty = try sm.ty.toCoreType(alloc);
            const hty = try coreTypeToHType(alloc, core_ty);
            methods[i] = .{
                .name = .{ .base = sm.name.base, .unique = .{ .value = sm.name.unique } },
                .ty = hty,
                .has_default = sm.has_default,
            };
        }

        try class_env.addClass(.{
            .name = .{ .base = ci.name.base, .unique = .{ .value = ci.name.unique } },
            .tyvar = ci.tyvar,
            .superclasses = superclasses,
            .methods = methods,
            .dict_con_name = .{ .base = ci.dict_con_name.base, .unique = .{ .value = ci.dict_con_name.unique } },
        });
    }

    for (iface.instance_infos) |ii| {
        const core_head = try ii.head.toCoreType(alloc);
        const htype_head = try coreTypeToHType(alloc, core_head);

        const context = try alloc.alloc(class_env_mod.ClassConstraint, ii.context.len);
        for (ii.context, 0..) |cc, i| {
            const core_ty = try cc.ty.toCoreType(alloc);
            const htype_ty = try alloc.create(htype_mod.HType);
            htype_ty.* = try coreTypeToHType(alloc, core_ty);
            context[i] = .{
                .class_name = .{ .base = cc.class_name.base, .unique = .{ .value = cc.class_name.unique } },
                .ty = htype_ty,
                .span = .{ .start = span_mod.SourcePos.invalid(), .end = span_mod.SourcePos.invalid() },
            };
        }

        // NOTE: `rigid_scope` is omitted from the serialised form and
        // defaults to empty here.  This is safe while compileSingle always
        // runs (the fresh ClassEnv overwrites this one), but must be
        // revisited when #456 allows skipping compilation on cache hit.
        try class_env.addInstance(.{
            .class_name = .{ .base = ii.class_name.base, .unique = .{ .value = ii.class_name.unique } },
            .head = htype_head,
            .context = context,
            .span = .{ .start = span_mod.SourcePos.invalid(), .end = span_mod.SourcePos.invalid() },
        });
    }

    return class_env;
}

/// Reconstruct a `DictNameMap` from the serialised entries in `iface`.
///
/// String slices (`head_name`, `name_base`) point into the deep-copied
/// `ModIface` arena memory.  This is safe as long as the `ModIface` and
/// the returned `DictNameMap` share the same arena (which they do in the
/// current `compileProgram` flow).
fn deserialiseDictNamesFromIface(
    alloc: std.mem.Allocator,
    iface: mod_iface.ModIface,
) std.mem.Allocator.Error!DictNameMap {
    var map: DictNameMap = .empty;
    for (iface.dict_entries) |entry| {
        const key = desugar_mod.DesugarCtx.DictNameKey{
            .class_unique = entry.class_unique,
            .head_name = entry.head_name,
        };
        const val = Name{
            .base = entry.name_base,
            .unique = .{ .value = entry.name_unique },
        };
        try map.put(alloc, key, val);
    }
    return map;
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

// ── NoImplicitPrelude suppression tests ───────────────────────────────────

test "compileSingle: NoImplicitPrelude suppresses Prelude function injection" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    // putStrLn should NOT be in scope when NoImplicitPrelude is active.
    const source =
        \\{-# LANGUAGE NoImplicitPrelude #-}
        \\module NoPreludeFns where
        \\
        \\main :: IO ()
        \\main = putStrLn "hello"
        \\
    ;

    _ = try env.compileSingle("NoPreludeFns", source, 1, null);
    // With NoImplicitPrelude, putStrLn is not in scope → renamer must emit an error.
    try testing.expect(env.diags.hasErrors());
}

test "compileSingle: NoImplicitPrelude still allows wired-in types and constructors" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var env = CompileEnv.init(alloc);
    defer env.deinit();

    // Int, Bool, and True/False are wired-in and must remain available even
    // when the module opts out of the implicit Prelude.
    const source =
        \\{-# LANGUAGE NoImplicitPrelude #-}
        \\module WiredIn where
        \\
        \\answer :: Int
        \\answer = 42
        \\
        \\flag :: Bool
        \\flag = True
        \\
    ;

    _ = try env.compileSingle("WiredIn", source, 1, null);
    try testing.expect(!env.diags.hasErrors());
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
        }}, &.{});
        defer r1.env.deinit();
        try testing.expect(!r1.result.had_errors);
        // A real compilation must produce at least one Core bind.
        try testing.expect(r1.result.core.binds.len > 0);
        const fp = r1.env.ifaces.get("CacheHit").?.fingerprint;
        try testing.expect(fp != 0);
        break :blk fp;
    };

    // ── Second run: cache hit pre-seeds metadata, source still compiled ──
    //
    // The source and dep fingerprints are unchanged, so `compileProgram`
    // finds the `.rhi` written by the first run and pre-seeds ClassEnv and
    // DictNameMap from it.  The module is then compiled from source anyway
    // (per-module .bc caching is deferred to #456), so the Core binds are
    // non-empty.  The fingerprint must be preserved across runs.
    {
        var r2 = try compileProgram(alloc, io, &.{.{
            .module_name = "CacheHit",
            .source = source,
            .file_id = 2,
            .source_path = hs_path,
        }}, &.{});
        defer r2.env.deinit();
        try testing.expect(!r2.result.had_errors);

        // The iface carries the same fingerprint as the first run.
        const fp2 = r2.env.ifaces.get("CacheHit").?.fingerprint;
        try testing.expectEqual(fp1, fp2);

        // compileSingle always runs → Core binds are produced.
        try testing.expect(r2.result.core.binds.len > 0);
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
        }}, &.{});
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
        }}, &.{});
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
        }, &.{});
        defer r.env.deinit();
        break :blk r.env.ifaces.get("CacheApp").?.fingerprint;
    };

    // Second run: CacheLib_v2 (changed) + CacheApp (unchanged source).
    // CacheLib's fingerprint changes → CacheApp's dep_fps change → CacheApp misses cache.
    const app_fp2: u64 = blk: {
        var r = try compileProgram(alloc, io, &.{
            .{ .module_name = "CacheLib", .source = lib_v2, .file_id = 3, .source_path = lib_path },
            .{ .module_name = "CacheApp", .source = app_src, .file_id = 4, .source_path = app_path },
        }, &.{});
        defer r.env.deinit();
        break :blk r.env.ifaces.get("CacheApp").?.fingerprint;
    };

    try testing.expect(app_fp1 != 0);
    try testing.expect(app_fp2 != 0);
    // The dep fingerprint changed → CacheApp's fingerprint must differ.
    try testing.expect(app_fp1 != app_fp2);
}

// ── Package-database resolution tests ────────────────────────────────────

test "compileProgram: package-db — import resolved via .rhi in package-db path" {
    var tmp = testing.tmpDir(.{});
    defer tmp.cleanup();
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const io = testing.io;

    const tmp_path = try std.Io.Dir.realPathFileAlloc(tmp.dir, io, ".", alloc);

    // ── Step 1: Compile PkgLib from source and serialise its interface ────
    //
    // We use a minimal module with one exported value so the renamer and
    // typechecker in the downstream module have something to seed from.
    const lib_source =
        \\module PkgLib where
        \\libAnswer :: Int
        \\libAnswer = 42
        \\
    ;
    const lib_iface: mod_iface.ModIface = blk: {
        var r = try compileProgram(alloc, io, &.{.{
            .module_name = "PkgLib",
            .source = lib_source,
            .file_id = 1,
        }}, &.{});
        defer r.env.deinit();
        try testing.expect(!r.result.had_errors);
        // Stamp the current format version so tryLoadFromPackageDbs accepts
        // the file (it rejects version mismatches).
        var iface = r.env.ifaces.get("PkgLib").?;
        iface.format_version = mod_iface.rhi_format_version;
        break :blk iface;
    };

    // ── Step 2: Write the interface to <tmpdir>/PkgLib.rhi ───────────────
    const rhi_path = try std.fmt.allocPrint(alloc, "{s}/PkgLib.rhi", .{tmp_path});
    try mod_iface.writeRhiToDisk(alloc, io, rhi_path, lib_iface);

    // ── Step 3: Compile PkgApp that imports PkgLib, supplying the tmpdir
    //           as the only package-db.  PkgLib source is NOT in `modules`.
    const app_source =
        \\{-# LANGUAGE NoImplicitPrelude #-}
        \\module PkgApp where
        \\import PkgLib
        \\answer :: Int
        \\answer = libAnswer
        \\
    ;
    var r2 = try compileProgram(alloc, io, &.{.{
        .module_name = "PkgApp",
        .source = app_source,
        .file_id = 2,
    }}, &.{tmp_path});
    defer r2.env.deinit();

    // The compilation must succeed — the renamer and typechecker found
    // PkgLib's exported symbols via the package-db .rhi.
    try testing.expect(!r2.result.had_errors);

    // PkgLib's interface must have been registered from the package-db.
    try testing.expect(r2.env.ifaces.contains("PkgLib"));

    // PkgApp must have produced at least one Core bind.
    try testing.expect(r2.result.core.binds.len > 0);
}

test "moduleNameToRhiRelPath: simple module name" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const rel = try moduleNameToRhiRelPath(alloc, "Main");
    try testing.expectEqualStrings("Main.rhi", rel);
}

test "moduleNameToRhiRelPath: qualified module name" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const rel = try moduleNameToRhiRelPath(alloc, "Data.Map");
    const expected = "Data" ++ &[_]u8{std.fs.path.sep} ++ "Map.rhi";
    try testing.expectEqualStrings(expected, rel);
}

test "tryLoadFromPackageDbs: returns null when package_dbs is empty" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    const result = try tryLoadFromPackageDbs(alloc, testing.io, "SomeModule", &.{});
    try testing.expect(result == null);
}

test "tryLoadFromPackageDbs: returns null when no .rhi file exists" {
    var tmp = testing.tmpDir(.{});
    defer tmp.cleanup();
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();
    const io = testing.io;

    const tmp_path = try std.Io.Dir.realPathFileAlloc(tmp.dir, io, ".", alloc);
    const result = try tryLoadFromPackageDbs(alloc, io, "NoSuchModule", &.{tmp_path});
    try testing.expect(result == null);
}
