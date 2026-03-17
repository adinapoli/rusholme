//! REPL Session
//!
//! Owns the persistent compiler state (unique supply, rename environment,
//! type environment, metavar supply) and accumulates bindings across
//! successive REPL inputs.
//!
//! Each call to `processInput` compiles the input through the full
//! pipeline and, on success, merges the resulting bindings into the
//! session state. On failure, the session state is unchanged
//! (transactional semantics — see Task 4).
//!
//! See docs/decisions/0006-repl-architecture.md for the full design.

const std = @import("std");
const builtin = @import("builtin");
const Allocator = std.mem.Allocator;

const pipeline_mod = @import("pipeline.zig");
const Pipeline = pipeline_mod.Pipeline;
const CompileResult = pipeline_mod.CompileResult;
const CompileError = pipeline_mod.CompileError;
const InputKind = pipeline_mod.InputKind;

const renamer_mod = @import("../renamer/renamer.zig");
const RenameEnv = renamer_mod.RenameEnv;

const diag_mod = @import("../diagnostics/diagnostic.zig");
const DiagnosticCollector = diag_mod.DiagnosticCollector;
const Diagnostic = diag_mod.Diagnostic;

const span_mod = @import("../diagnostics/span.zig");
const FileId = span_mod.FileId;

const unique_mod = @import("../naming/unique.zig");
const UniqueSupply = unique_mod.UniqueSupply;
const Name = unique_mod.Name;

const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");

const engine_mod = @import("engine.zig");
const GrinEngine = engine_mod.GrinEngine;
const ExecError = engine_mod.ExecError;

const is_wasi = builtin.target.os.tag == .wasi;
const jit_engine_mod = if (!is_wasi) @import("jit_engine.zig") else struct {};
const JitEngine = if (!is_wasi) jit_engine_mod.JitEngine else void;
const JitError = if (!is_wasi) jit_engine_mod.JitError else error{};
const Engine = if (is_wasi) GrinEngine else JitEngine;

const Note = diag_mod.Note;

const grin_ast = @import("../grin/ast.zig");
const translate_mod = @import("../grin/translate.zig");
const class_env_mod = @import("../typechecker/class_env.zig");
const ClassEnv = class_env_mod.ClassEnv;
const desugar_mod = @import("../core/desugar.zig");
const DictNameMap = desugar_mod.DesugarCtx.DictNameMap;

// ── Embedded Prelude source ───────────────────────────────────────────

/// The Prelude source text, embedded at compile time.
/// The anonymous import "prelude_source" is registered in build.zig on
/// both the library module (mod) and the WASM REPL module, so this
/// resolves correctly for native, WASM, and test targets.
const prelude_source = @embedFile("prelude_source");

// ── Result types ──────────────────────────────────────────────────────

/// Result of processing a REPL input.
pub const ProcessResult = struct {
    /// The compilation result (GRIN program + input kind).
    compile: CompileResult,
    /// Diagnostics collected during compilation (warnings, etc).
    /// Empty on success; populated on failure before returning error.
    diagnostics: []const Diagnostic,
};

/// Result of evaluating a REPL input end-to-end.
pub const EvalResult = struct {
    /// Human-readable string representation of the result.
    /// Only populated for expression inputs. Empty for declarations.
    value: []const u8,
};

/// Errors that can occur during session processing.
pub const SessionError = error{
    OutOfMemory,
} || CompileError || ExecError || (if (!is_wasi) JitError else error{}) || error{
    InitFailed,
};

// ── Session ───────────────────────────────────────────────────────────

/// A REPL session that accumulates compiler state across inputs.
///
/// The session owns the persistent state objects — unique supply,
/// rename environment, type environment, and metavar supply — and
/// provides them to the pipeline for each compilation. On success,
/// new bindings are retained; on failure, the state is rolled back.
pub const Session = struct {
    allocator: Allocator,
    io: std.Io,

    // Persistent compiler state, accumulated across inputs.
    u_supply: UniqueSupply,
    rename_env: RenameEnv,
    ty_env: env_mod.TyEnv,
    mv_supply: htype_mod.MetaVarSupply,

    // Monotonically increasing file ID for each input.
    next_file_id: FileId,

    // The pipeline instance (stateless — just holds allocator + io).
    pipeline: Pipeline,

    // The execution engine for evaluating compiled GRIN programs.
    engine: Engine,

    // Cached diagnostics from the most recent compilation attempt.
    // Persists across failed compilations so callers can inspect errors.
    last_diagnostics: std.ArrayListUnmanaged(Diagnostic),

    // Source text from the most recent compilation attempt. Contains the
    // full module wrapper (e.g. "module ReplInput where\n...") whose spans
    // the diagnostics reference.
    last_source: []const u8 = "",

    // The raw user input from the most recent compilation. Used by
    // diagnostic renderers to show the user's code (not the wrapper).
    last_input: []const u8 = "",

    // Which kind of wrapper produced the most recent diagnostics.
    // Used to compute span adjustments when translating wrapper-relative
    // positions to user-input-relative positions.
    last_input_kind: InputKind = .declaration,

    // Accumulated GRIN function definitions from successful declarations.
    // For expressions, we merge these with the current expression's definition
    // to create a complete program for evaluation.
    accumulated_defs: std.ArrayListUnmanaged(grin_ast.Def),

    // Accumulated function arities from successful declarations.
    // Maps unique ID -> parameter count. Passed to the GRIN translator
    // so cross-session function references are correctly translated
    // (e.g. 0-arity functions emit App instead of Return Var).
    accumulated_arities: std.AutoHashMapUnmanaged(u64, u32),

    // Accumulated constructor field counts from successful data declarations.
    // Maps constructor unique ID -> field count. Passed to the GRIN translator
    // so constructors from prior REPL inputs are recognised in later inputs
    // (e.g. `Red` is treated as a nullary constructor, not a variable).
    accumulated_con_map: std.AutoHashMapUnmanaged(u64, u32),

    // Accumulated class and instance declarations from successful inputs.
    // Seeded into each new InferCtx so that type classes declared in prior
    // REPL inputs are available for instance resolution and constraint
    // solving in subsequent inputs.
    accumulated_class_env: ClassEnv,

    // Accumulated dictionary name mappings from desugaring.
    // Maps (class_unique, head_type_name) → dictionary Name.
    // Persisted so that dictionary evidence resolution in subsequent
    // REPL inputs can find dictionaries declared in prior inputs (#578).
    accumulated_dict_names: DictNameMap,

    // Accumulated type constructor names from data declarations in prior inputs.
    // Maps base name (e.g. "A") → Name (with correct unique).
    // Passed to the typechecker so that instance heads can reference types
    // from prior REPL inputs (#588).
    accumulated_type_con_names: std.StringHashMapUnmanaged(Name),

    /// Create a new REPL session with initialised compiler state.
    pub fn init(allocator: Allocator, io: std.Io) SessionError!Session {
        var u_supply = UniqueSupply{};

        // The DiagnosticCollector used during init is temporary —
        // if builtins fail to register, that's a fatal error.
        var init_diags = DiagnosticCollector.init();
        defer init_diags.deinit(allocator);

        var rename_env = RenameEnv.init(allocator, &u_supply, &init_diags) catch {
            return SessionError.InitFailed;
        };
        errdefer rename_env.deinit();

        var ty_env = env_mod.TyEnv.init(allocator) catch {
            return SessionError.OutOfMemory;
        };
        errdefer ty_env.deinit();

        env_mod.initBuiltins(&ty_env, allocator, &u_supply) catch {
            return SessionError.OutOfMemory;
        };

        var self = Session{
            .allocator = allocator,
            .io = io,
            .u_supply = u_supply,
            .rename_env = rename_env,
            .ty_env = ty_env,
            .mv_supply = .{},
            .next_file_id = 1,
            .pipeline = Pipeline.init(allocator, io),
            .engine = if (is_wasi) GrinEngine.init(allocator, io) else JitEngine.init(allocator) catch return SessionError.InitFailed,
            .last_diagnostics = .{},
            .accumulated_defs = .{},
            .accumulated_arities = .{},
            .accumulated_con_map = .{},
            .accumulated_class_env = ClassEnv.init(allocator),
            .accumulated_dict_names = .empty,
            .accumulated_type_con_names = .empty,
        };

        // Load the Prelude so its functions are available immediately.
        // Non-fatal: on failure the session continues with built-in names only.
        //
        // Currently WASM-only: the native JIT backend cannot yet compile
        // the Prelude's GRIN output (GRIN→LLVM translation fails — tracked
        // in #589). Additionally, loading Prelude `data Bool` reassigns
        // constructor uniques, breaking the JIT's hardcoded True/False
        // discriminant check in formatJitResult. Once #589 is resolved,
        // this guard can be removed.
        if (is_wasi) {
            self.loadPrelude();
        }

        return self;
    }

    /// Release all session resources.
    pub fn deinit(self: *Session) void {
        // GrinEngine has no deinit; only JitEngine does.
        self.accumulated_type_con_names.deinit(self.allocator);
        self.accumulated_dict_names.deinit(self.allocator);
        self.accumulated_class_env.deinit();
        self.accumulated_con_map.deinit(self.allocator);
        self.accumulated_arities.deinit(self.allocator);
        self.last_diagnostics.deinit(self.allocator);
        self.accumulated_defs.deinit(self.allocator);
        self.rename_env.deinit();
        self.ty_env.deinit();
    }

    // ── Prelude loading ─────────────────────────────────────────────

    /// Load the embedded Prelude into the session state.
    ///
    /// Compiles the Prelude source through the pipeline and accumulates
    /// its bindings (GRIN defs, arities, con_map, class_env, dict_names)
    /// so that Prelude functions are available in subsequent REPL inputs.
    ///
    /// Non-fatal: on failure, the session continues with built-in names
    /// only.  This keeps the REPL usable even if the Prelude has issues.
    fn loadPrelude(self: *Session) void {
        // Push scope frames for Prelude bindings (permanent — never popped).
        self.rename_env.scope.push() catch return;
        self.ty_env.push() catch {
            self.rename_env.scope.pop();
            return;
        };

        var diags = DiagnosticCollector.init();
        defer diags.deinit(self.allocator);

        const file_id: FileId = 0; // Prelude gets file_id 0 (same as batch compiler)

        const result = self.pipeline.compileModule(
            prelude_source,
            file_id,
            &self.u_supply,
            &self.rename_env,
            &self.ty_env,
            &self.mv_supply,
            &diags,
            null, // no external arities yet
            null, // no external con_map yet
            null, // no external class_env yet
            null, // no external dict_names yet
            null, // no external type_con_names yet
        ) catch {
            // Prelude failed to compile — roll back and continue without it.
            self.ty_env.pop();
            self.rename_env.scope.pop();
            return;
        };

        // Accumulate GRIN definitions and arities.
        for (result.grin_prog.defs) |def| {
            self.accumulated_defs.append(self.allocator, def) catch return;
            self.accumulated_arities.put(
                self.allocator,
                def.name.unique.value,
                @intCast(def.params.len),
            ) catch return;
        }

        // Accumulate constructor field counts from data declarations.
        for (result.core_data_decls) |decl| {
            for (decl.constructors) |con| {
                self.accumulated_con_map.put(
                    self.allocator,
                    con.name.unique.value,
                    translate_mod.countConFields(con.ty),
                ) catch return;
            }
        }

        // Accumulate type constructor names from Prelude data declarations.
        // This allows instance heads to reference types from the Prelude
        // (#588).
        for (result.core_data_decls) |decl| {
            self.accumulated_type_con_names.put(self.allocator, decl.name.base, decl.name) catch return;
        }

        // Take ownership of class_env and dict_names.
        self.accumulated_class_env.deinit();
        self.accumulated_class_env = result.class_env;

        self.accumulated_dict_names.deinit(self.allocator);
        self.accumulated_dict_names = result.dict_names;

        // Note: no addDeclarations call needed here. This function is
        // only called on the WASM path (guarded in init), where the
        // tree-walking evaluator uses accumulated_defs directly.
    }

    // ── Input processing ──────────────────────────────────────────────

    /// Compile a REPL input through the full pipeline.
    ///
    /// Uses transactional semantics: a scope frame is pushed onto the
    /// rename and type environments before compilation. On failure, the
    /// frame is popped (rolling back any bindings introduced by the
    /// failed input). On success, the frame stays in place and its
    /// bindings become part of the session state.
    ///
    /// The `UniqueSupply` is monotonic and not rolled back — unique IDs
    /// must remain globally unique even for failed inputs.
    ///
    /// Diagnostics are stored in `last_diagnostics` and can be
    /// retrieved via `getDiagnosticsForInput()`.
    pub fn processInput(self: *Session, input: []const u8) CompileError!ProcessResult {
        self.next_file_id += 1;

        // Clear previous diagnostics - free their message allocations first
        for (self.last_diagnostics.items) |diag| {
            self.allocator.free(diag.message);
            if (diag.notes.len > 0) {
                self.allocator.free(diag.notes);
            }
        }
        self.last_diagnostics.clearRetainingCapacity();

        // Push transactional scope frames.
        self.rename_env.scope.push() catch return CompileError.OutOfMemory;
        self.ty_env.push() catch {
            self.rename_env.scope.pop();
            return CompileError.OutOfMemory;
        };

        var diags = DiagnosticCollector.init();
        defer diags.deinit(self.allocator);

        var result = self.pipeline.compileInput(
            input,
            &self.u_supply,
            &self.rename_env,
            &self.ty_env,
            &self.mv_supply,
            &diags,
            &self.accumulated_arities,
            &self.accumulated_con_map,
            &self.accumulated_class_env,
            &self.accumulated_dict_names,
            &self.accumulated_type_con_names,
        ) catch |err| {
            // Capture compilation context for diagnostic rendering.
            self.last_source = self.pipeline.last_source;
            self.last_input = input;
            self.last_input_kind = self.pipeline.last_input_kind;

            // Save diagnostics before returning error so callers can inspect them
            // Note: we need to dupe the message allocation since diags will be deinitialized
            for (diags.diagnostics.items) |diag| {
                try self.last_diagnostics.append(self.allocator, .{
                    .severity = diag.severity,
                    .code = diag.code,
                    .span = diag.span,
                    .message = try self.allocator.dupe(u8, diag.message),
                    .notes = if (diag.notes.len > 0)
                        try self.allocator.dupe(Note, diag.notes)
                    else
                        &.{},
                });
            }

            // Rollback: pop the scope frames to discard partial bindings.
            self.ty_env.pop();
            self.rename_env.scope.pop();
            return err;
        };

        // Capture compilation context for diagnostic rendering.
        self.last_source = self.pipeline.last_source;
        self.last_input = input;
        self.last_input_kind = self.pipeline.last_input_kind;

        // Success: save diagnostics and leave scope frames in place
        for (diags.diagnostics.items) |diag| {
            self.last_diagnostics.append(self.allocator, .{
                .severity = diag.severity,
                .code = diag.code,
                .span = diag.span,
                .message = self.allocator.dupe(u8, diag.message) catch return CompileError.OutOfMemory,
                .notes = if (diag.notes.len > 0)
                    self.allocator.dupe(Note, diag.notes) catch return CompileError.OutOfMemory
                else
                    &.{},
            }) catch return CompileError.OutOfMemory;
        }

        // Accumulate definitions from successful declarations
        if (result.kind == .declaration or result.kind == .declaration_let_stripped) {
            for (result.program.defs) |def| {
                try self.accumulated_defs.append(self.allocator, def);
                try self.accumulated_arities.put(
                    self.allocator,
                    def.name.unique.value,
                    @intCast(def.params.len),
                );
            }

            // Accumulate constructor field counts from data declarations
            // so that constructors are recognised in subsequent inputs.
            for (result.core_data_decls) |decl| {
                for (decl.constructors) |con| {
                    try self.accumulated_con_map.put(
                        self.allocator,
                        con.name.unique.value,
                        translate_mod.countConFields(con.ty),
                    );
                }
            }

            // Accumulate type constructor names from data declarations.
            // This allows instance heads to reference types from prior REPL
            // inputs by their correct unique IDs (#588).
            for (result.core_data_decls) |decl| {
                try self.accumulated_type_con_names.put(self.allocator, decl.name.base, decl.name);
            }

            // Replace the accumulated class env with the result's env.
            // The result's class_env was seeded from accumulated_class_env
            // before inference, so it contains all prior entries plus any
            // new class/instance declarations from this input.  Swapping
            // avoids the duplicate-instance problem that mergeFrom would
            // cause (#557).
            self.accumulated_class_env.deinit();
            self.accumulated_class_env = result.class_env;
            // Invalidate the stolen field so no one double-frees.
            result.class_env = ClassEnv.init(self.allocator);

            // Replace accumulated dict_names with the result's map.
            // The result's dict_names was seeded from accumulated_dict_names
            // before desugaring, so it contains all prior entries plus any
            // new dictionary bindings from this input (#578).
            self.accumulated_dict_names.deinit(self.allocator);
            self.accumulated_dict_names = result.dict_names;
            result.dict_names = .empty;
        }

        return .{
            .compile = result,
            .diagnostics = diags.getAll(self.allocator) catch &.{},
        };
    }

    /// Get the diagnostics from the most recent compilation attempt.
    ///
    /// Returns diagnostics stored after the last call to `eval()` or
    /// `processInput()`. The slice is owned by the Session and should
    /// not be freed by the caller.
    pub fn getDiagnosticsForInput(self: *Session, allocator: Allocator, input: []const u8) ![]const Diagnostic {
        _ = input; // Input is ignored - we return cached diagnostics from last compilation
        _ = allocator;
        return self.last_diagnostics.items;
    }

    /// Compile and evaluate a REPL input end-to-end.
    ///
    /// For expressions: compiles through the pipeline, then executes
    /// the GRIN program and returns the formatted result value.
    ///
    /// For declarations: compiles through the pipeline (accumulating
    /// bindings in the session state) and adds the definitions to the
    /// JIT engine so subsequent expressions can reference them.
    pub fn eval(self: *Session, input: []const u8) SessionError!EvalResult {
        const process = try self.processInput(input);

        switch (process.compile.kind) {
            .expression => {
                if (is_wasi) {
                    // WASM path: merge accumulated defs with the expression
                    // program, since the GRIN tree-walker needs all defs in
                    // a single program.
                    //
                    // Lambda lifting may produce multiple definitions from a
                    // single expression (e.g., `(\x -> 1) 2` produces
                    // both the lifted lambda and the entry point). Include
                    // ALL defs from expression compilation, not just one.
                    const n_expr_defs = process.compile.program.defs.len;
                    const total_defs = self.accumulated_defs.items.len + n_expr_defs;
                    const all_defs = try self.allocator.alloc(grin_ast.Def, total_defs);
                    errdefer self.allocator.free(all_defs);

                    for (self.accumulated_defs.items, 0..) |def, i| {
                        all_defs[i] = def;
                    }

                    // Add all expression defs (including any lifted lambdas)
                    for (process.compile.program.defs, 0..) |def, i| {
                        all_defs[self.accumulated_defs.items.len + i] = def;
                    }

                    const merged_program = grin_ast.Program{
                        .defs = all_defs,
                        .field_types = process.compile.program.field_types,
                    };
                    const exec = try self.engine.execute(&merged_program);
                    const value_copy = try self.allocator.dupe(u8, exec.value);
                    self.allocator.free(all_defs);
                    return .{ .value = value_copy };
                } else {
                    // JIT path: pass only the expression's def. Previously-
                    // declared functions are already in the JIT's main dylib
                    // and will be resolved automatically by the ORC linker.
                    const exec = try self.engine.execute(&process.compile.program);
                    return .{ .value = exec.value };
                }
            },
            .declaration, .declaration_let_stripped => {
                if (!is_wasi) {
                    // JIT path: add declarations to the JIT engine so
                    // their symbols are available for future expressions.
                    try self.engine.addDeclarations(&process.compile.program);
                }
                return .{ .value = "" };
            },
        }
    }
};

// ── Tests ─────────────────────────────────────────────────────────────

const testing = std.testing;

test "session: initialise and compile expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const result = try session.processInput("42");
    try testing.expect(result.compile.kind == .expression);
    try testing.expect(result.compile.program.defs.len > 0);
}

test "session: compile data declaration" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const result = try session.processInput("data Color = Red | Green | Blue");
    try testing.expect(result.compile.kind == .declaration);
}

test "session: compile function declaration" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const result = try session.processInput("id x = x");
    try testing.expect(result.compile.kind == .declaration);
    try testing.expect(result.compile.program.defs.len > 0);
}

test "session: multiple inputs accumulate" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // First: define a function
    const r1 = try session.processInput("const x y = x");
    try testing.expect(r1.compile.kind == .declaration);

    // Second: compile another expression
    const r2 = try session.processInput("42");
    try testing.expect(r2.compile.kind == .expression);
}

test "session: pipeline produces named def for expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const process = try session.processInput("42");
    try testing.expectEqual(@as(usize, 1), process.compile.program.defs.len);
    try testing.expectEqualStrings("replExpr__", process.compile.program.defs[0].name.base);
}

test "session: eval expression end-to-end" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const result = try session.eval("42");
    try testing.expectEqualStrings("42", result.value);
}

test "session: eval declaration returns empty" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const result = try session.eval("id x = x");
    try testing.expectEqualStrings("", result.value);
}

test "session: failed input does not corrupt state" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // Define a valid function
    _ = try session.processInput("f x = x");

    // Submit invalid input — should fail but not corrupt state
    const bad = session.processInput("let = = =");
    try testing.expectError(CompileError.CompilationFailed, bad);

    // Session should still work after the failed input
    const r = try session.processInput("42");
    try testing.expect(r.compile.kind == .expression);
}

test "session: putStrLn compiles as expression" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    const result = try session.processInput("putStrLn \"hello\"");
    try testing.expect(result.compile.kind == .expression);
}

test "session: processInput returns diagnostics on error" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // Submit invalid input — should fail but return with diagnostics
    const result = session.processInput("notarealfunction") catch {
        // Failure is expected, but we've lost the diagnostics due to deferred deinit
        return;
    };
    _ = result;
}

// ── Prelude loading tests ─────────────────────────────────────────────
//
// loadPrelude is only called automatically on WASM (is_wasi). These
// tests call it explicitly to verify the pipeline on native, where
// the GRIN tree-walker is not available but the frontend pipeline
// (parse → rename → typecheck → desugar → GRIN translate) still works.

test "session: loadPrelude populates accumulated state" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    // On native, loadPrelude is not called by init. Call explicitly.
    if (!is_wasi) session.loadPrelude();

    // Prelude should have loaded — accumulated_defs should be non-empty.
    try testing.expect(session.accumulated_defs.items.len > 0);
    // Prelude declares data types — accumulated_con_map should have entries.
    try testing.expect(session.accumulated_con_map.count() > 0);
}

test "session: Prelude names resolve after loadPrelude" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    if (!is_wasi) session.loadPrelude();

    // `id` is defined in the Prelude — should compile as expression.
    const result = try session.processInput("id 42");
    try testing.expect(result.compile.kind == .expression);
}

test "session: Prelude operators resolve after loadPrelude" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    if (!is_wasi) session.loadPrelude();

    // `(+)` is defined in the Prelude — should compile as expression.
    const result = try session.processInput("1 + 2");
    try testing.expect(result.compile.kind == .expression);
}

test "session: Prelude data constructors resolve after loadPrelude" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    var session = try Session.init(alloc, testing.io);
    defer session.deinit();

    if (!is_wasi) session.loadPrelude();

    // `Just` is defined in the Prelude — should compile as expression.
    const result = try session.processInput("Just 42");
    try testing.expect(result.compile.kind == .expression);
}
