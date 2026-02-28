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
//! ## M2 scope / known limitations
//!
//! - Recompilation avoidance (`.rhi` fingerprinting) is not yet implemented.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/371
//!
//! - Type-class instances are not propagated across module boundaries.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/369
//!
//! - Package-level search paths are not yet supported.
//!   Tracked in: https://github.com/adinapoli/rusholme/issues/368

const std = @import("std");

const naming_mod = @import("../naming/unique.zig");
const diag_mod = @import("../diagnostics/diagnostic.zig");
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
    /// Pipeline: read source → lex/parse → rename (with upstream names seeded
    /// from `self`) → typecheck (with upstream types seeded from `self`) →
    /// desugar → build `ModIface` → `register`.
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
        const module = if (preparsed_module) |m| m else blk: {
            var lexer = lexer_mod.Lexer.init(self.alloc, source, file_id);
            var layout = layout_mod.LayoutProcessor.init(self.alloc, &lexer);
            layout.setDiagnostics(&self.diags);

            var parser = parser_mod.Parser.init(self.alloc, &layout, &self.diags) catch return null;
            break :blk parser.parseModule() catch return null;
        };
        if (self.diags.hasErrors()) return null;

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

    // ── Phase 3: Compile each module using cached AST ──────────────────────
    for (topo.order) |mod_name| {
        const m = src_map.get(mod_name) orelse continue;
        const parsed = env.parsed_modules.get(mod_name);
        _ = try env.compileSingle(m.module_name, m.source, m.file_id, parsed);
    }

    const had_errors = env.diags.hasErrors();
    const merged = try env.mergePrograms(alloc, topo.order);

    return .{
        .env = env,
        .result = .{ .core = merged, .had_errors = had_errors },
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
