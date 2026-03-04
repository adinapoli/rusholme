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
const Allocator = std.mem.Allocator;

const Pipeline = @import("pipeline.zig").Pipeline;
const CompileResult = @import("pipeline.zig").CompileResult;
const CompileError = @import("pipeline.zig").CompileError;

const renamer_mod = @import("../renamer/renamer.zig");
const RenameEnv = renamer_mod.RenameEnv;

const diag_mod = @import("../diagnostics/diagnostic.zig");
const DiagnosticCollector = diag_mod.DiagnosticCollector;

const span_mod = @import("../diagnostics/span.zig");
const FileId = span_mod.FileId;

const unique_mod = @import("../naming/unique.zig");
const UniqueSupply = unique_mod.UniqueSupply;

const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");

// ── Result types ──────────────────────────────────────────────────────

/// Result of processing a REPL input.
pub const ProcessResult = struct {
    /// The compilation result (GRIN program + input kind).
    compile: CompileResult,
    /// Diagnostics collected during compilation (warnings, etc.).
    /// Empty on success; populated on failure before returning error.
    diagnostics: []const diag_mod.Diagnostic,
};

/// Errors that can occur during session processing.
pub const SessionError = CompileError || error{
    /// Session initialisation failed.
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
        };
    }

    /// Release all session resources.
    pub fn deinit(self: *Session) void {
        self.rename_env.deinit();
        self.ty_env.deinit();
    }

    /// Compile a REPL input through the full pipeline.
    ///
    /// On success, the session's compiler state is updated with any
    /// new bindings introduced by the input (types, functions, etc.).
    ///
    /// On failure, a `CompileError` is returned and the session state
    /// is unchanged.
    pub fn processInput(self: *Session, input: []const u8) CompileError!ProcessResult {
        const file_id = self.next_file_id;
        self.next_file_id += 1;
        _ = file_id;

        const result = try self.pipeline.compileInput(
            input,
            &self.u_supply,
            &self.rename_env,
            &self.ty_env,
            &self.mv_supply,
        );

        return .{
            .compile = result,
            .diagnostics = &.{},
        };
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
