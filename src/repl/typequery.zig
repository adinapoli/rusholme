//! Type query for REPL `:type <expr>` command.
//!
//! This module provides the ability to type-check an expression without
//! modifying session state or evaluating the expression. Used for the
//! REPL's `:type` command to display inferred types.
//!
//! The `typeOf()` function:
//! - Does NOT modify session state (transactional typechecking)
//! - Does NOT evaluate the expression (no execution side effects)
//! - Does NOT perform IO (pure type inference)
//!
//! See docs/superpowers/plans/0005-repl-type-command.md for the full plan.

const std = @import("std");
const Allocator = std.mem.Allocator;

const Session = @import("session.zig").Session;
const htype_mod = @import("../typechecker/htype.zig");
const env_mod = @import("../typechecker/env.zig");

pub const TypeQueryResult = struct {
    /// The inferred type scheme (polymorphic or monomorphic).
    /// Note: The HType body is arena-allocated from the session's allocator.
    /// The result is valid only for the lifetime of the session arena.
    scheme: env_mod.TyScheme,
    /// Formatted display string: "<expr> :: <type>"
    /// Allocated by the caller's allocator; caller must free.
    display: []const u8,
    /// Diagnostics from type-checking (empty on success).
    /// These are owned by session.last_diagnostics and persist across queries.
    diags: []const @import("../diagnostics/diagnostic.zig").Diagnostic,
};

/// Type-check an expression and return its inferred type.
/// Does NOT modify session state, does NOT evaluate, does NOT execute IO.
pub fn typeOf(
    alloc: std.mem.Allocator,
    session: *Session,
    expr: []const u8,
) !TypeQueryResult {
    _ = alloc;
    _ = session;
    _ = expr;
    @panic("Not implemented");
}
