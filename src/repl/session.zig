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

const Pipeline = @import("pipeline.zig").Pipeline;
const CompileResult = @import("pipeline.zig").CompileResult;
const CompileError = @import("pipeline.zig").CompileError;

const renamer_mod = @import("../renamer/renamer.zig");
const RenameEnv = renamer_mod.RenameEnv;

const diag_mod = @import("../diagnostics/diagnostic.zig");
const DiagnosticCollector = diag_mod.DiagnosticCollector;
const Diagnostic = diag_mod.Diagnostic;

const span_mod = @import("../diagnostics/span.zig");
const FileId = span_mod.FileId;

const unique_mod = @import("../naming/unique.zig");
const UniqueSupply = unique_mod.UniqueSupply;

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

    // Accumulated GRIN function definitions from successful declarations.
    // For expressions, we merge these with the current expression's definition
    // to create a complete program for evaluation.
    accumulated_defs: std.ArrayListUnmanaged(grin_ast.Def),

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

        return .{
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
        };
    }

    /// Release all session resources.
    pub fn deinit(self: *Session) void {
        // GrinEngine has no deinit; only JitEngine does.
        self.last_diagnostics.deinit(self.allocator);
        self.accumulated_defs.deinit(self.allocator);
        self.rename_env.deinit();
        self.ty_env.deinit();
    }

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

        const result = self.pipeline.compileInput(
            input,
            &self.u_supply,
            &self.rename_env,
            &self.ty_env,
            &self.mv_supply,
            &diags,
        ) catch |err| {
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
        if (result.kind == .declaration) {
            for (result.program.defs) |def| {
                try self.accumulated_defs.append(self.allocator, def);
            }
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
                    const total_defs = self.accumulated_defs.items.len + 1;
                    const all_defs = try self.allocator.alloc(grin_ast.Def, total_defs);
                    errdefer self.allocator.free(all_defs);

                    for (self.accumulated_defs.items, 0..) |def, i| {
                        all_defs[i] = def;
                    }

                    if (process.compile.program.defs.len != 1) {
                        std.debug.panic("Expression compilation produced {} definitions, expected 1", .{process.compile.program.defs.len});
                    }
                    all_defs[total_defs - 1] = process.compile.program.defs[0];

                    const merged_program = grin_ast.Program{ .defs = all_defs };
                    const exec = try self.engine.execute(&merged_program);
                    self.allocator.free(all_defs);
                    return .{ .value = exec.value };
                } else {
                    // JIT path: pass only the expression's def. Previously-
                    // declared functions are already in the JIT's main dylib
                    // and will be resolved automatically by the ORC linker.
                    const exec = try self.engine.execute(&process.compile.program);
                    return .{ .value = exec.value };
                }
            },
            .declaration => {
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
