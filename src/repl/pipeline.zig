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

    /// Create a new pipeline.
    pub fn init(allocator: Allocator, io: std.Io) Pipeline {
        return .{
            .allocator = allocator,
            .io = io,
        };
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

        // The RenameEnv holds a pointer to its DiagnosticCollector from
        // init time. Each compileModule call creates a fresh collector,
        // so we must update the pointer before renaming.
        rename_env.diags = diags;

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

        // Debug: print the GRIN defs
        std.log.debug("GRIN program has {} defs", .{grin_prog.defs.len});
        for (grin_prog.defs) |*def| {
            std.log.debug("  GRIN def: {s}", .{def.name.base});
            if (def.body.* == .Return) {
                if (def.body.Return == .Lit) {
                    std.log.debug("    returns Lit: {}", .{def.body.Return.Lit});
                }
            }
        }

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
    ) CompileError!CompileResult {
        const alloc = self.allocator;
        const file_id: FileId = 0;

        // Try as a declaration first: wrap as a module body.
        // NOTE: the wrapper source strings must NOT be freed here — the
        // GRIN program's Name.base fields are pointers into the source
        // buffer. They must live as long as the GRIN program (i.e. until
        // the caller's arena is destroyed).
        {
            const decl_source = std.fmt.allocPrint(alloc, "module ReplInput where\n{s}\n", .{input}) catch {
                return CompileError.OutOfMemory;
            };

            var diags = DiagnosticCollector.init();
            defer diags.deinit(alloc);

            if (self.compileModule(decl_source, file_id, u_supply, rename_env, ty_env, mv_supply, &diags)) |program| {
                return .{ .program = program, .kind = .declaration };
            } else |_| {
                // Declaration parse failed — try as expression below
            }
        }

        // Try as an expression: wrap in replExpr__ = <expr>
        {
            const expr_source = std.fmt.allocPrint(alloc, "module ReplInput where\nreplExpr__ = {s}\n", .{input}) catch {
                return CompileError.OutOfMemory;
            };

            var diags = DiagnosticCollector.init();
            defer diags.deinit(alloc);

            const program = try self.compileModule(expr_source, file_id, u_supply, rename_env, ty_env, mv_supply, &diags);
            return .{ .program = program, .kind = .expression };
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
    );

    try testing.expect(result.kind == .declaration);
    try testing.expect(result.program.defs.len > 0);
}
