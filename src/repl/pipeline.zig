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
const Name = unique_mod.Name;

const infer_mod = @import("../typechecker/infer.zig");
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");

const desugar_mod = @import("../core/desugar.zig");
const lift_mod = @import("../core/lift.zig");

const translate_mod = @import("../grin/translate.zig");
const grin_ast = @import("../grin/ast.zig");
const core_ast = @import("../core/ast.zig");

const class_env_mod = @import("../typechecker/class_env.zig");
const ClassEnv = class_env_mod.ClassEnv;

const DictNameMap = desugar_mod.DesugarCtx.DictNameMap;

const ArityMap = std.AutoHashMapUnmanaged(u64, u32);
const ConMap = std.AutoHashMapUnmanaged(u64, u32);
const TypeConNames = std.StringHashMapUnmanaged(Name);

// ── Result types ──────────────────────────────────────────────────────

/// The kind of input that was compiled, and any prefix adjustments needed
/// for translating wrapper-relative spans back to user-input coordinates.
pub const InputKind = enum {
    /// A bare expression (e.g. `2 + 3`, `not True`).
    expression,
    /// A show-wrapped IO expression (e.g. `putStrLn (show expr)`).
    /// The display is handled by `putStrLn` as a side effect — the
    /// return value (`IO ()`) should be suppressed, matching GHCi.
    expression_io,
    /// A top-level declaration (e.g. `data Color = Red`, `f x = x + 1`).
    declaration,
    /// A declaration where `let ` was stripped (e.g. user typed `let f x = x`).
    /// Columns on the first user line need +4 adjustment.
    declaration_let_stripped,
};

/// Length of the expression wrapper prefix `"replExpr__ = "` (13 chars).
const EXPR_PREFIX_LEN: u32 = 13;

/// Length of the `"let "` prefix stripped from declaration input.
const LET_PREFIX_LEN: u32 = 4;

/// Translate a diagnostic span from wrapper-relative coordinates to
/// user-input-relative coordinates.
///
/// Both wrappers prepend `module ReplInput where\n` (line 1), so all
/// line numbers are decremented by 1. The expression wrapper additionally
/// prepends `replExpr__ = ` (13 chars) on the first user-code line
/// (wrapper line 2), so columns on that line are shifted left. The
/// `declaration_let_stripped` variant shifts columns right by 4 to
/// account for the stripped `let ` prefix.
///
/// Returns `null` if the span falls entirely within the wrapper prefix
/// (i.e. before the user's code), which shouldn't happen in practice.
pub fn translateSpan(span: span_mod.SourceSpan, kind: InputKind) ?span_mod.SourceSpan {
    const start = translatePos(span.start, kind) orelse return null;
    const end = translatePos(span.end, kind) orelse return null;
    return span_mod.SourceSpan.init(start, end);
}

fn translatePos(pos: span_mod.SourcePos, kind: InputKind) ?span_mod.SourcePos {
    // SourcePos.isValid() treats file_id 0 as invalid, but the REPL
    // legitimately uses file_id 0. Only skip truly zero positions
    // (line == 0 indicates a synthetic/invalid position).
    if (pos.line == 0) return pos;

    // The wrapper header `module ReplInput where\n` is line 1.
    // User code starts at wrapper line 2.
    if (pos.line < 2) return null;
    const user_line = pos.line - 1;

    var user_col = pos.column;
    if ((kind == .expression or kind == .expression_io) and pos.line == 2) {
        // First line of user code in expression wrapper has
        // `replExpr__ = ` prepended (13 chars).
        if (pos.column <= EXPR_PREFIX_LEN) return null;
        user_col = pos.column - EXPR_PREFIX_LEN;
    } else if (kind == .declaration_let_stripped and pos.line == 2) {
        // The `let ` prefix was stripped before wrapping, so the
        // wrapper column is 4 positions too early. Shift right.
        user_col = pos.column + LET_PREFIX_LEN;
    }

    return span_mod.SourcePos.init(pos.file_id, user_line, user_col);
}

// ── Diagnostic selection helpers ───────────────────────────────────────

/// Return the highest `DiagnosticCode` ordinal in a slice, or 0 if empty.
/// Used to determine which compilation attempt got furthest in the
/// pipeline (parse < rename < typecheck).
fn maxDiagCode(items: []const Diagnostic) u32 {
    var best: u32 = 0;
    for (items) |d| {
        const ord = @intFromEnum(d.code);
        if (ord > best) best = ord;
    }
    return best;
}

/// Free and remove the first `count` diagnostics from a collector.
fn clearLeadingDiags(alloc: Allocator, diags: *DiagnosticCollector, count: usize) void {
    var i: usize = 0;
    while (i < count) : (i += 1) {
        if (diags.diagnostics.items.len > 0) {
            const diag = diags.diagnostics.orderedRemove(0);
            alloc.free(diag.message);
            if (diag.notes.len > 0) alloc.free(diag.notes);
        }
    }
}

/// Free and remove diagnostics after index `keep_count` from a collector.
fn clearTrailingDiags(alloc: Allocator, diags: *DiagnosticCollector, keep_count: usize) void {
    while (diags.diagnostics.items.len > keep_count) {
        const diag = diags.diagnostics.pop() orelse break;
        alloc.free(diag.message);
        if (diag.notes.len > 0) alloc.free(diag.notes);
    }
}

/// Result of a successful compilation.
pub const CompileResult = struct {
    /// The GRIN program produced by the pipeline.
    program: grin_ast.Program,
    /// Whether the input was an expression or a declaration.
    kind: InputKind,
    /// Data declarations from the Core program. The REPL session
    /// accumulates these to build a constructor map for subsequent
    /// inputs, so that user-defined constructors are recognised
    /// across REPL interactions.
    core_data_decls: []const core_ast.CoreDataDecl,
    /// Class and instance environment from this compilation.
    /// The REPL session merges this into its persistent ClassEnv
    /// on successful compilation, so that type class declarations
    /// and instances accumulate across REPL inputs.
    class_env: ClassEnv,
    /// Dictionary name map from desugaring. Maps
    /// (class_unique, head_type_name) → dictionary Name.
    /// The REPL session persists this so that dictionary evidence
    /// resolution can find dictionaries from prior inputs (#578).
    dict_names: DictNameMap,
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

    /// Which kind of wrapper produced the most recent diagnostics.
    /// Used to translate wrapper-relative spans back to user-input-relative
    /// coordinates for rendering.
    last_input_kind: InputKind = .declaration,

    /// Whether to attempt show-wrapping expressions as
    /// `putStrLn (show (expr))`. Disabled for type queries (:type)
    /// which need the original expression type, not IO ().
    enable_show_wrapping: bool = true,

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
    const ModuleResult = struct {
        grin_prog: grin_ast.Program,
        core_data_decls: []const core_ast.CoreDataDecl,
        /// Class and instance environment from this compilation.
        /// Ownership is transferred to the caller (stolen from ModuleTypes).
        class_env: ClassEnv,
        /// Dictionary name map from desugaring.
        dict_names: DictNameMap,
    };

    pub fn compileModule(
        self: *Pipeline,
        source: []const u8,
        file_id: FileId,
        u_supply: *UniqueSupply,
        rename_env: *RenameEnv,
        ty_env: *env_mod.TyEnv,
        mv_supply: *htype_mod.MetaVarSupply,
        diags: *DiagnosticCollector,
        external_arities: ?*const ArityMap,
        external_con_map: ?*const ConMap,
        external_class_env: ?*const ClassEnv,
        external_dict_names: ?*const DictNameMap,
        external_type_con_names: ?*const TypeConNames,
    ) CompileError!ModuleResult {
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

        // Seed the InferCtx with classes/instances from prior REPL inputs
        // so that instance declarations can reference previously-declared
        // classes, and constraint resolution can find prior instances.
        if (external_class_env) |ext_env| {
            infer_ctx.class_env.mergeFrom(ext_env) catch {
                return CompileError.OutOfMemory;
            };
        }

        var module_types = infer_mod.inferModule(&infer_ctx, renamed, external_type_con_names) catch {
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) {
            module_types.deinit(alloc);
            return CompileError.CompilationFailed;
        }

        // ── Desugar ────────────────────────────────────────────────
        const desugar_result = desugar_mod.desugarModule(alloc, renamed, &module_types, diags, u_supply, external_dict_names) catch {
            module_types.deinit(alloc);
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) {
            module_types.deinit(alloc);
            return CompileError.CompilationFailed;
        }

        // ── Lambda lift ────────────────────────────────────────────
        const lift_result = lift_mod.lambdaLift(alloc, desugar_result.program, null, 0) catch {
            module_types.deinit(alloc);
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) {
            module_types.deinit(alloc);
            return CompileError.CompilationFailed;
        }

        // ── Translate to GRIN ──────────────────────────────────────
        const grin_prog = translate_mod.translateProgram(alloc, lift_result.program, external_arities, external_con_map) catch {
            module_types.deinit(alloc);
            return CompileError.OutOfMemory;
        };
        if (diags.hasErrors()) {
            module_types.deinit(alloc);
            return CompileError.CompilationFailed;
        }

        // Steal class_env from module_types before deinit — ownership
        // transfers to the caller so the REPL session can accumulate
        // class/instance declarations across inputs.
        const result_class_env = module_types.class_env;
        module_types.class_env = ClassEnv.init(alloc);
        module_types.deinit(alloc);

        return .{
            .grin_prog = grin_prog,
            .core_data_decls = lift_result.program.data_decls,
            .class_env = result_class_env,
            .dict_names = desugar_result.dict_names,
        };
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
        external_arities: ?*const ArityMap,
        external_con_map: ?*const ConMap,
        external_class_env: ?*const ClassEnv,
        external_dict_names: ?*const DictNameMap,
        external_type_con_names: ?*const TypeConNames,
    ) CompileError!CompileResult {
        const alloc = self.allocator;
        const file_id: FileId = 0;

        // Blank input: fail immediately before any show-wrapping.
        // Empty modules are rejected by the parser, so blank input would
        // fall through to show () which desugars () to todo_tuple_0 and
        // corrupts the JIT session state with an unresolvable symbol.
        if (std.mem.trim(u8, input, " \t\n\r").len == 0) {
            return CompileError.CompilationFailed;
        }

        // Try as a declaration first: wrap as a module body.
        // Strip leading "let" keyword if present, as top-level module
        // declarations don't use "let" (that's GHCi-specific syntax).
        // NOTE: the wrapper source strings must NOT be freed here — the
        // GRIN program's Name.base fields are pointers into the source
        // buffer. They must live as long as the GRIN program (i.e. until
        // the caller's arena is destroyed).
        {
            var decl_input = input;
            var decl_kind: InputKind = .declaration;
            if (std.mem.startsWith(u8, input, "let ")) {
                decl_input = input[4..]; // Skip past "let "
                decl_kind = .declaration_let_stripped;
            }

            const decl_source = std.fmt.allocPrint(alloc, "module ReplInput where\n{s}\n", .{decl_input}) catch {
                return CompileError.OutOfMemory;
            };
            self.last_source = decl_source;
            self.last_input_kind = decl_kind;

            var decl_diags = DiagnosticCollector.init();
            defer decl_diags.deinit(alloc);

            if (self.compileModule(decl_source, file_id, u_supply, rename_env, ty_env, mv_supply, &decl_diags, external_arities, external_con_map, external_class_env, external_dict_names, external_type_con_names)) |result| {
                // Copy any diagnostics from the attempt
                try copyDiagnostics(alloc, &decl_diags, diags);
                return .{ .program = result.grin_prog, .kind = decl_kind, .core_data_decls = result.core_data_decls, .class_env = result.class_env, .dict_names = result.dict_names };
            } else |_| {
                // Declaration attempt failed — preserve its diagnostics
                // before trying as expression
                copyDiagnostics(alloc, &decl_diags, diags) catch {};
                // Continue to expression attempt below
            }
        }

        // ── String-wrapped expression (Phase A1) ──────────────────────
        //
        // Try String-specific wrapping first:
        //   replExpr__ = putStrLn (showString (<input>))
        // where showString :: String -> String produces the correct quoted
        // form (e.g. "hello" → "\"hello\"") without going through the
        // polymorphic Show [a] instance.  Show [a] now exists and would
        // succeed for [Char], but it produces ['h','e','l','l','o'] rather
        // than the GHCi-style "hello" output.  showString preserves the
        // right representation for String values (#629).
        // For non-String expressions, this attempt fails at typechecking
        // and falls through to the generic show phase below.
        if (self.enable_show_wrapping) {
            rename_env.scope.push() catch return CompileError.OutOfMemory;
            ty_env.push() catch {
                rename_env.scope.pop();
                return CompileError.OutOfMemory;
            };

            var str_diags = DiagnosticCollector.init();
            defer str_diags.deinit(alloc);

            const str_source = std.fmt.allocPrint(alloc, "module ReplInput where\nreplExpr__ = putStrLn (showString ({s}))\n", .{input}) catch {
                ty_env.pop();
                rename_env.scope.pop();
                return CompileError.OutOfMemory;
            };
            self.last_source = str_source;
            self.last_input_kind = .expression;

            if (self.compileModule(str_source, file_id, u_supply, rename_env, ty_env, mv_supply, &str_diags, external_arities, external_con_map, external_class_env, external_dict_names, external_type_con_names)) |result| {
                const decl_diag_count = diags.diagnostics.items.len;
                clearLeadingDiags(alloc, diags, decl_diag_count);
                return .{ .program = result.grin_prog, .kind = .expression_io, .core_data_decls = result.core_data_decls, .class_env = result.class_env, .dict_names = result.dict_names };
            } else |_| {
                ty_env.pop();
                rename_env.scope.pop();
            }
        }

        // ── Show-wrapped expression (Phase A2) ─────────────────────────
        //
        // Attempt to wrap the expression as:
        //   replExpr__ = putStrLn (show (<input>))
        // matching GHCi's behavior.  Show drives evaluation through
        // demand (call-by-need), and putStrLn prints the result via IO.
        //
        // For monomorphic expressions (Bool, Char, known-type lists),
        // the desugarer specializes dictionaries away, so the GRIN
        // evaluator handles them correctly.  For polymorphic expressions
        // (e.g. numeric literals without defaulting), show-wrapping
        // will fail at the typechecker and fall through to bare display.
        if (self.enable_show_wrapping) {
            // Scope safety: push a transactional scope frame around this
            // attempt.  If it fails, pop the frame to discard any bindings
            // (e.g. `replExpr__`) that the renamer introduced.  If it
            // succeeds, the frame stays in place.
            rename_env.scope.push() catch return CompileError.OutOfMemory;
            ty_env.push() catch {
                rename_env.scope.pop();
                return CompileError.OutOfMemory;
            };

            var show_diags = DiagnosticCollector.init();
            defer show_diags.deinit(alloc);

            const show_source = std.fmt.allocPrint(alloc, "module ReplInput where\nreplExpr__ = putStrLn (show ({s}))\n", .{input}) catch {
                ty_env.pop();
                rename_env.scope.pop();
                return CompileError.OutOfMemory;
            };
            self.last_source = show_source;
            self.last_input_kind = .expression;

            if (self.compileModule(show_source, file_id, u_supply, rename_env, ty_env, mv_supply, &show_diags, external_arities, external_con_map, external_class_env, external_dict_names, external_type_con_names)) |result| {
                // Show-wrapped compilation succeeded — keep the scope
                // frame and clear any declaration diagnostics.
                const decl_diag_count = diags.diagnostics.items.len;
                clearLeadingDiags(alloc, diags, decl_diag_count);
                return .{ .program = result.grin_prog, .kind = .expression_io, .core_data_decls = result.core_data_decls, .class_env = result.class_env, .dict_names = result.dict_names };
            } else |_| {
                // No Show instance or other error — rollback the scope
                // frame and fall through to bare expression.
                ty_env.pop();
                rename_env.scope.pop();
            }
        }

        // Phase B: bare expression (existing behavior).
        {
            // Save declaration state for possible restoration.
            const decl_diag_count = diags.diagnostics.items.len;
            const decl_source = self.last_source;
            const decl_kind = self.last_input_kind;

            const expr_source = std.fmt.allocPrint(alloc, "module ReplInput where\nreplExpr__ = {s}\n", .{input}) catch {
                return CompileError.OutOfMemory;
            };
            self.last_source = expr_source;
            self.last_input_kind = .expression;

            if (self.compileModule(expr_source, file_id, u_supply, rename_env, ty_env, mv_supply, diags, external_arities, external_con_map, external_class_env, external_dict_names, external_type_con_names)) |result| {
                // Expression succeeded — clear declaration diagnostics.
                clearLeadingDiags(alloc, diags, decl_diag_count);
                return .{ .program = result.grin_prog, .kind = .expression, .core_data_decls = result.core_data_decls, .class_env = result.class_env, .dict_names = result.dict_names };
            } else |_| {
                // Both attempts failed. Keep whichever diagnostics came
                // from the later pipeline stage (more informative).
                // Parse errors (E001) < rename/type errors, so a higher
                // max code means the attempt got further.
                const decl_items = diags.diagnostics.items[0..decl_diag_count];
                const expr_items = diags.diagnostics.items[decl_diag_count..];
                const decl_max = maxDiagCode(decl_items);
                const expr_max = maxDiagCode(expr_items);

                if (expr_max > decl_max) {
                    // Expression diagnostics are more informative — keep
                    // them, discard declaration diagnostics.
                    clearLeadingDiags(alloc, diags, decl_diag_count);
                    self.last_input_kind = .expression;
                } else {
                    // Declaration diagnostics are at least as informative
                    // — keep them, discard expression diagnostics, and
                    // restore the declaration wrapper source.
                    clearTrailingDiags(alloc, diags, decl_diag_count);
                    self.last_source = decl_source;
                    self.last_input_kind = decl_kind;
                }
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
        null,
        null,
        null,
        null,
        null,
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
        null,
        null,
        null,
        null,
        null,
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
        null,
        null,
        null,
        null,
        null,
    );

    try testing.expect(result.kind == .declaration);
    try testing.expect(result.program.defs.len > 0);
}

test "translateSpan: expression wrapper adjusts line and column" {
    const SourcePos = span_mod.SourcePos;
    const SourceSpan = span_mod.SourceSpan;

    // Span at wrapper line 2, cols 14-27 (e.g. `replExpr__ = undefined_var`)
    // User code starts at col 14 (after 13-char prefix "replExpr__ = ").
    const span = SourceSpan.init(
        SourcePos.init(0, 2, 14),
        SourcePos.init(0, 2, 27),
    );

    const result = translateSpan(span, .expression).?;
    try testing.expectEqual(@as(u32, 1), result.start.line);
    try testing.expectEqual(@as(u32, 1), result.start.column);
    try testing.expectEqual(@as(u32, 1), result.end.line);
    try testing.expectEqual(@as(u32, 14), result.end.column);
}

test "translateSpan: declaration wrapper adjusts line only" {
    const SourcePos = span_mod.SourcePos;
    const SourceSpan = span_mod.SourceSpan;

    // Span at wrapper line 2, cols 1-10 (e.g. `data Color`)
    const span = SourceSpan.init(
        SourcePos.init(0, 2, 1),
        SourcePos.init(0, 2, 10),
    );

    const result = translateSpan(span, .declaration).?;
    try testing.expectEqual(@as(u32, 1), result.start.line);
    try testing.expectEqual(@as(u32, 1), result.start.column);
    try testing.expectEqual(@as(u32, 1), result.end.line);
    try testing.expectEqual(@as(u32, 10), result.end.column);
}

test "translateSpan: multiline expression preserves later lines" {
    const SourcePos = span_mod.SourcePos;
    const SourceSpan = span_mod.SourceSpan;

    // Error on wrapper line 3 (user line 2) — column unchanged for
    // expression wrapper since the prefix only affects wrapper line 2.
    const span = SourceSpan.init(
        SourcePos.init(0, 3, 5),
        SourcePos.init(0, 3, 10),
    );

    const result = translateSpan(span, .expression).?;
    try testing.expectEqual(@as(u32, 2), result.start.line);
    try testing.expectEqual(@as(u32, 5), result.start.column);
    try testing.expectEqual(@as(u32, 2), result.end.line);
    try testing.expectEqual(@as(u32, 10), result.end.column);
}

test "translateSpan: declaration_let_stripped shifts columns right" {
    const SourcePos = span_mod.SourcePos;
    const SourceSpan = span_mod.SourceSpan;

    // User typed `let f x = y`. Declaration wrapper strips `let `,
    // so wrapper contains `f x = y`. Span for `y` is at wrapper
    // line 2, col 7. User-relative: line 1, col 7 + 4 = 11.
    const span = SourceSpan.init(
        SourcePos.init(0, 2, 7),
        SourcePos.init(0, 2, 8),
    );

    const result = translateSpan(span, .declaration_let_stripped).?;
    try testing.expectEqual(@as(u32, 1), result.start.line);
    try testing.expectEqual(@as(u32, 11), result.start.column);
    try testing.expectEqual(@as(u32, 1), result.end.line);
    try testing.expectEqual(@as(u32, 12), result.end.column);
}

test "translateSpan: wrapper header line returns null" {
    const SourcePos = span_mod.SourcePos;
    const SourceSpan = span_mod.SourceSpan;

    // Span on wrapper line 1 (the `module ReplInput where` header) —
    // this shouldn't happen in practice, but we handle it gracefully.
    const span = SourceSpan.init(
        SourcePos.init(0, 1, 1),
        SourcePos.init(0, 1, 22),
    );

    try testing.expect(translateSpan(span, .expression) == null);
    try testing.expect(translateSpan(span, .declaration) == null);
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
        null,
        null,
        null,
        null,
        null,
    );

    try testing.expect(result.kind == .declaration_let_stripped);
    try testing.expect(result.program.defs.len > 0);
}
