//! REPL Pipeline Orchestrator
//!
//! Compiles a string of Haskell source through the full Rusholme pipeline:
//! Lexer -> Layout -> Parser -> Renamer -> Typechecker -> Desugarer
//! -> Lambda Lifter -> GRIN Translator.
//!
//! This module is backend-agnostic — it produces GRIN IR that can be
//! executed by any engine (GRIN tree-walker, LLVM JIT, etc.).
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");
const Allocator = std.mem.Allocator;

// ── Pipeline stage imports ────────────────────────────────────────────

const lexer_mod = @import("../frontend/lexer.zig");
const Lexer = lexer_mod.Lexer;

const layout_mod = @import("../frontend/layout.zig");
const LayoutProcessor = layout_mod.LayoutProcessor;

const parser_mod = @import("../frontend/parser.zig");
const Parser = parser_mod.Parser;

const renamer_mod = @import("../renamer/renamer.zig");
const RenameEnv = renamer_mod.RenameEnv;

const diag_mod = @import("../diagnostics/diagnostic.zig");
const DiagnosticCollector = diag_mod.DiagnosticCollector;
const Diagnostic = diag_mod.Diagnostic;
const Note = diag_mod.Note;

const span_mod = @import("../diagnostics/span.zig");
const FileId = span_mod.FileId;

const unique_mod = @import("../naming/unique.zig");
const UniqueSupply = unique_mod.UniqueSupply;

const infer_mod = @import("../typechecker/infer.zig");
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");

const desugar_mod = @import("../core/desugar.zig");
const lift_mod = @import("../core/lift.zig");

const translate_mod = @import("../grin/translate.zig");
const grin_ast = @import("../grin/ast.zig");

// ── Result types ──────────────────────────────────────────────────────

/// The kind of input that was compiled.
pub const InputKind = enum {
    /// A bare expression (e.g. `2 + 3`, `not True`).
    expression,
    /// A top-level declaration (e.g. `data Color = Red`, `f x = x + 1`).
    declaration,
};

/// Result of a successful compilation.
pub const CompileResult = struct {
    /// The GRIN program produced by the pipeline.
    program: grin_ast.Program,
    /// Whether the input was an expression or a declaration.
    kind: InputKind,
};

/// Errors that can occur during pipeline compilation.
pub const CompileError = error{
    /// One or more pipeline stages produced diagnostics.
    CompilationFailed,
    /// Out of memory.
    OutOfMemory,
    /// The parser could not be initialised.
    ParserInitFailed,
};

// ── Pipeline ──────────────────────────────────────────────────────────

/// Compiles Haskell source strings through the full Rusholme pipeline.
///
/// Each call to `compileModule` runs:
///   Lexer -> Layout -> Parser -> Renamer -> Typechecker
///   -> Desugarer -> Lambda Lifter -> GRIN Translator
///
/// The caller provides the compiler state (unique supply, rename env,
/// type env) so it can be shared across REPL inputs.
pub const Pipeline = struct {
    allocator: Allocator,
    io: std.Io,

    /// Source text from the most recent compilation attempt, for diagnostic
    /// rendering. Contains the full module wrapper (e.g.
    /// "module ReplInput where\n..."). Updated before each compilation
    /// attempt in `compileInput`, so on failure it holds the last-attempted
    /// wrapper source whose spans the diagnostics reference.
    last_source: []const u8 = "",

    /// Create a new pipeline.
    pub fn init(allocator: Allocator, io: std.Io) Pipeline {
        return .{
            .allocator = allocator,
            .io = io,
        };
    }

    /// Copy a diagnostic's message allocation into a new diagnostics list.
    ///
    /// This is needed when transferring diagnostics between
    /// DiagnosticCollectors, as each collector owns its diagnostic
    /// message allocations.
    fn copyDiagnostic(
        alloc: Allocator,
        src: Diagnostic,
        dest_diagnostics: *std.ArrayListUnmanaged(Diagnostic),
    ) !void {
        const owned_msg = try alloc.dupe(u8, src.message);
        errdefer alloc.free(owned_msg);
        const owned_notes = if (src.notes.len > 0)
            try alloc.dupe(Note, src.notes)
        else
            &.{};
        errdefer if (src.notes.len > 0) alloc.free(owned_notes);

        try dest_diagnostics.append(alloc, .{
            .severity = src.severity,
            .code = src.code,
            .span = src.span,
            .message = owned_msg,
            .notes = owned_notes,
        });
    }

    /// Copy all diagnostics from one collector to another with proper
    /// memory ownership. Both collectors' message allocations are preserved.
    fn copyDiagnostics(
        alloc: Allocator,
        src: *const DiagnosticCollector,
        dest: *DiagnosticCollector,
    ) !void {
        for (src.diagnostics.items) |d| {
            try copyDiagnostic(alloc, d, &dest.diagnostics);
        }
    }

    /// Compile a Haskell source string through the full pipeline.
    ///
    /// The source is wrapped as a module before parsing. The caller
    /// provides mutable references to the compiler state objects so
    /// that bindings accumulate across REPL inputs.
    ///
    /// On failure, diagnostics are collected but not rendered — the
    /// caller decides how to present them.
    pub fn compileModule(
        self: *Pipeline,
        source: []const u8,
        file_id: FileId,
        u_supply: *UniqueSupply,
        rename_env: *RenameEnv,
        ty_env: *env_mod.TyEnv,
        mv_supply: *htype_mod.MetaVarSupply,
        diags: *DiagnosticCollector,
    ) CompileError!grin_ast.Program {
        const alloc = self.allocator;

        // The RenameEnv holds pointers to its DiagnosticCollector and
        // UniqueSupply from init time. Session.init() constructs the
        // session as a local and returns it by value, so the pointers
        // captured during RenameEnv.init() become dangling once the
        // init frame returns. Update them to the caller's stable
        // addresses before each compilation.
        rename_env.diags = diags;
        rename_env.supply = u_supply;

        // ── Parse ──────────────────────────────────────────────────
        var lexer = Lexer.init(alloc, source, file_id);
        var layout = LayoutProcessor.init(alloc, &lexer);
        layout.setDiagnostics(diags);

        var parser = Parser.init(alloc, &layout, diags) catch {
            return CompileError.ParserInitFailed;
        };
        const module = parser.parseModule() catch {
            return CompileError.CompilationFailed;
        };
        if (diags.hasErrors()) return CompileError.CompilationFailed;

        // ── Rename ─────────────────────────────────────────────────
        const renamed = renamer_mod.rename(module, rename_env) catch {
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) return CompileError.CompilationFailed;

        // ── Typecheck ──────────────────────────────────────────────
        var infer_ctx = infer_mod.InferCtx.init(alloc, ty_env, mv_supply, u_supply, diags);
        var module_types = infer_mod.inferModule(&infer_ctx, renamed) catch {
            return CompileError.OutOfMemory;
        };
        defer module_types.deinit(alloc);
        if (diags.hasErrors()) return CompileError.CompilationFailed;

        // ── Desugar ────────────────────────────────────────────────
        const core_prog = desugar_mod.desugarModule(alloc, renamed, &module_types, diags, u_supply) catch {
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) return CompileError.CompilationFailed;

        // ── Lambda lift ────────────────────────────────────────────
        const core_lifted = lift_mod.lambdaLift(alloc, core_prog) catch {
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) return CompileError.CompilationFailed;

        // ── Translate to GRIN ──────────────────────────────────────
        const grin_prog = translate_mod.translateProgram(alloc, core_lifted) catch {
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) return CompileError.CompilationFailed;

        return grin_prog;
    }

    /// Compile a REPL input by wrapping it as a module and running
    /// the pipeline. Tries as a declaration first; if that fails,
    /// tries as an expression.
    pub fn compileInput(
        self: *Pipeline,
        input: []const u8,
        u_supply: *UniqueSupply,
        rename_env: *RenameEnv,
        ty_env: *env_mod.TyEnv,
        mv_supply: *htype_mod.MetaVarSupply,
        diags: *DiagnosticCollector,
    ) CompileError!CompileResult {
        const alloc = self.allocator;
        const file_id: FileId = 0;

        // Try as a declaration first: wrap as a module body.
        // Strip leading "let" keyword if present, as top-level module
        // declarations don't use "let" (that's GHCi-specific syntax).
        // NOTE: the wrapper source strings must NOT be freed here — the
        // GRIN program's Name.base fields are pointers into the source
        // buffer. They must live as long as the GRIN program (i.e. until
        // the caller's arena is destroyed).
        {
            var decl_input = input;
            if (std.mem.startsWith(u8, input, "let ")) {
                decl_input = input[4..]; // Skip past "let "
            }

            const decl_source = std.fmt.allocPrint(alloc, "module ReplInput where\n{s}\n", .{decl_input}) catch {
                return CompileError.OutOfMemory;
            };
            self.last_source = decl_source;

            var decl_diags = DiagnosticCollector.init();
            defer decl_diags.deinit(alloc);

            if (self.compileModule(decl_source, file_id, u_supply, rename_env, ty_env, mv_supply, &decl_diags)) |program| {
                // Copy any diagnostics from the attempt
                try copyDiagnostics(alloc, &decl_diags, diags);
                return .{ .program = program, .kind = .declaration };
            } else |_| {
                // Declaration attempt failed — preserve its diagnostics
                // before trying as expression
                copyDiagnostics(alloc, &decl_diags, diags) catch {};
                // Continue to expression attempt below
            }
        }

        // Try as an expression: wrap in replExpr__ = <expr>
        {
            // Clear diagnostics from the failed declaration attempt BEFORE
            // trying expression compilation only the expression succeeds.
            // If expression also fails, we'll merge both diagnostics.

            // First, save declaration diagnostics for possible merging
            const decl_diag_count = diags.diagnostics.items.len;

            const expr_source = std.fmt.allocPrint(alloc, "module ReplInput where\nreplExpr__ = {s}\n", .{input}) catch {
                return CompileError.OutOfMemory;
            };
            self.last_source = expr_source;

            if (self.compileModule(expr_source, file_id, u_supply, rename_env, ty_env, mv_supply, diags)) |program| {
                // Expression succeeded - clear declaration diagnostics since they're irrelevant now
                var i: usize = 0;
                while (i < decl_diag_count) : (i += 1) {
                    if (diags.diagnostics.items.len > 0) {
                        const diag = diags.diagnostics.orderedRemove(0);
                        alloc.free(diag.message);
                        if (diag.notes.len > 0) alloc.free(diag.notes);
                    }
                }
                return .{ .program = program, .kind = .expression };
            } else |_| {
                // Expression also failed - keep both declaration and expression diagnostics
                return CompileError.CompilationFailed;
            }
        }
    }
};

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "pipeline: compile simple literal expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var pipeline = Pipeline.init(alloc, testing.io);

    var u_supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var rename_env = try RenameEnv.init(alloc, &u_supply, &diags);
    defer rename_env.deinit();
    var ty_env = try env_mod.TyEnv.init(alloc);
    try env_mod.initBuiltins(&ty_env, alloc, &u_supply);
    var mv_supply = htype_mod.MetaVarSupply{};

    const result = try pipeline.compileInput(
        "42",
        &u_supply,
        &rename_env,
        &ty_env,
        &mv_supply,
        &diags,
    );

    try testing.expect(result.program.defs.len > 0);
    try testing.expect(result.kind == .expression);
    // Check that the def's base name is replExpr__
    try testing.expectEqualStrings("replExpr__", result.program.defs[0].name.base);
}

test "pipeline: compile data declaration" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var pipeline = Pipeline.init(alloc, testing.io);

    var u_supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var rename_env = try RenameEnv.init(alloc, &u_supply, &diags);
    defer rename_env.deinit();
    var ty_env = try env_mod.TyEnv.init(alloc);
    try env_mod.initBuiltins(&ty_env, alloc, &u_supply);
    var mv_supply = htype_mod.MetaVarSupply{};

    const result = try pipeline.compileInput(
        "data Color = Red | Green | Blue",
        &u_supply,
        &rename_env,
        &ty_env,
        &mv_supply,
        &diags,
    );

    // Data declarations are classified as declarations.
    // They may produce zero GRIN defs (constructors are GRIN tags,
    // not function definitions), so we only check the kind.
    try testing.expect(result.kind == .declaration);
}

test "pipeline: compile function declaration" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var pipeline = Pipeline.init(alloc, testing.io);

    var u_supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var rename_env = try RenameEnv.init(alloc, &u_supply, &diags);
    defer rename_env.deinit();
    var ty_env = try env_mod.TyEnv.init(alloc);
    try env_mod.initBuiltins(&ty_env, alloc, &u_supply);
    var mv_supply = htype_mod.MetaVarSupply{};

    // Use a simple function that doesn't require typeclasses
    const result = try pipeline.compileInput(
        "id x = x",
        &u_supply,
        &rename_env,
        &ty_env,
        &mv_supply,
        &diags,
    );

    try testing.expect(result.kind == .declaration);
    try testing.expect(result.program.defs.len > 0);
}

test "pipeline: handle let prefix in declarations" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var pipeline = Pipeline.init(alloc, testing.io);

    var u_supply = UniqueSupply{};
    var diags = DiagnosticCollector.init();
    defer diags.deinit(alloc);
    var rename_env = try RenameEnv.init(alloc, &u_supply, &diags);
    defer rename_env.deinit();
    var ty_env = try env_mod.TyEnv.init(alloc);
    try env_mod.initBuiltins(&ty_env, alloc, &u_supply);
    var mv_supply = htype_mod.MetaVarSupply{};

    // The "let " prefix should be stripped for module-level declarations
    const result = try pipeline.compileInput(
        "let id x = x",
        &u_supply,
        &rename_env,
        &ty_env,
        &mv_supply,
        &diags,
    );

    try testing.expect(result.kind == .declaration);
    try testing.expect(result.program.defs.len > 0);
}
