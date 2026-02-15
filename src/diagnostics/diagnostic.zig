//! Structured error types for diagnostics.
//!
//! This module defines the core diagnostic types for Rusholme's error
//! infrastructure. Errors are an AST, not strings — enabling rich rendering
//! (terminal, JSON, LSP) and programmatic matching.
//!
//! Modelled after GHC's MsgEnvelope / GhcMessage pattern.

const std = @import("std");
const span_mod = @import("span.zig");
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;

/// Severity level for a diagnostic message.
pub const Severity = enum {
    @"error",
    warning,
    info,
    hint,

    pub fn format(self: Severity, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        const s = switch (self) {
            .@"error" => "error",
            .warning => "warning",
            .info => "info",
            .hint => "hint",
        };
        try writer.writeAll(s);
    }
};

/// Machine-readable diagnostic code.
///
/// Each variant identifies a specific error kind, enabling programmatic
/// matching in LSP, JSON output, and tests. The enum will grow as
/// pipeline stages are implemented.
pub const DiagnosticCode = enum {
    parse_error,
    type_error,
    unbound_variable,
    duplicate_definition,
    kind_error,

    /// Returns a stable string code like "E001" for programmatic use.
    pub fn code(self: DiagnosticCode) []const u8 {
        return switch (self) {
            .parse_error => "E001",
            .type_error => "E002",
            .unbound_variable => "E003",
            .duplicate_definition => "E004",
            .kind_error => "E005",
        };
    }

    pub fn format(self: DiagnosticCode, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.writeAll(self.code());
    }
};

/// A secondary label or suggestion attached to a diagnostic.
///
/// Notes can optionally carry a source span — notes without a span are
/// used for general suggestions (e.g. "did you mean…").
pub const Note = struct {
    message: []const u8,
    span: ?SourceSpan = null,
};

/// A structured diagnostic message.
///
/// Every diagnostic carries a severity, a machine-readable code, the
/// primary source span, a human-readable message, and optional secondary
/// notes/suggestions.
pub const Diagnostic = struct {
    severity: Severity,
    code: DiagnosticCode,
    span: SourceSpan,
    message: []const u8,
    notes: []const Note = &.{},
};

/// Accumulates diagnostics across compilation stages.
///
/// Tracks whether any errors have been emitted to allow early termination
/// decisions without scanning the full list.
pub const DiagnosticBag = struct {
    diagnostics: std.ArrayListUnmanaged(Diagnostic),
    had_errors: bool = false,

    pub fn init() DiagnosticBag {
        return .{
            .diagnostics = .{},
        };
    }

    pub fn deinit(self: *DiagnosticBag, allocator: std.mem.Allocator) void {
        self.diagnostics.deinit(allocator);
        self.* = undefined;
    }

    pub fn add(self: *DiagnosticBag, allocator: std.mem.Allocator, diag: Diagnostic) !void {
        if (diag.severity == .@"error") {
            self.had_errors = true;
        }
        try self.diagnostics.append(allocator, diag);
    }

    pub fn errorCount(self: DiagnosticBag) usize {
        var count: usize = 0;
        for (self.diagnostics.items) |d| {
            if (d.severity == .@"error") count += 1;
        }
        return count;
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

test "Severity.format renders all variants" {
    var buf: [16]u8 = undefined;

    const err_str = try std.fmt.bufPrint(&buf, "{}", .{Severity.@"error"});
    try std.testing.expectEqualStrings("error", err_str);

    const warn_str = try std.fmt.bufPrint(&buf, "{}", .{Severity.warning});
    try std.testing.expectEqualStrings("warning", warn_str);

    const info_str = try std.fmt.bufPrint(&buf, "{}", .{Severity.info});
    try std.testing.expectEqualStrings("info", info_str);

    const hint_str = try std.fmt.bufPrint(&buf, "{}", .{Severity.hint});
    try std.testing.expectEqualStrings("hint", hint_str);
}

test "DiagnosticCode.code returns stable string codes" {
    try std.testing.expectEqualStrings("E001", DiagnosticCode.parse_error.code());
    try std.testing.expectEqualStrings("E002", DiagnosticCode.type_error.code());
    try std.testing.expectEqualStrings("E003", DiagnosticCode.unbound_variable.code());
    try std.testing.expectEqualStrings("E004", DiagnosticCode.duplicate_definition.code());
    try std.testing.expectEqualStrings("E005", DiagnosticCode.kind_error.code());
}

test "DiagnosticCode.format renders code string" {
    var buf: [8]u8 = undefined;

    const code_str = try std.fmt.bufPrint(&buf, "{}", .{DiagnosticCode.parse_error});
    try std.testing.expectEqualStrings("E001", code_str);
}

test "Diagnostic construction with all fields" {
    const span = SourceSpan.init(
        SourcePos.init(1, 10, 5),
        SourcePos.init(1, 10, 20),
    );

    const note_span = SourceSpan.init(
        SourcePos.init(1, 3, 1),
        SourcePos.init(1, 3, 10),
    );

    const notes = [_]Note{
        .{ .message = "defined here", .span = note_span },
        .{ .message = "did you mean 'foo'?" },
    };

    const diag = Diagnostic{
        .severity = .@"error",
        .code = .unbound_variable,
        .span = span,
        .message = "Variable 'bar' is not in scope",
        .notes = &notes,
    };

    try std.testing.expectEqual(Severity.@"error", diag.severity);
    try std.testing.expectEqual(DiagnosticCode.unbound_variable, diag.code);
    try std.testing.expectEqualStrings("Variable 'bar' is not in scope", diag.message);
    try std.testing.expectEqual(@as(usize, 2), diag.notes.len);

    // First note has a span
    try std.testing.expect(diag.notes[0].span != null);
    try std.testing.expectEqualStrings("defined here", diag.notes[0].message);

    // Second note has no span
    try std.testing.expect(diag.notes[1].span == null);
    try std.testing.expectEqualStrings("did you mean 'foo'?", diag.notes[1].message);
}

test "Diagnostic with default empty notes" {
    const span = SourceSpan.init(
        SourcePos.init(1, 1, 1),
        SourcePos.init(1, 1, 5),
    );

    const diag = Diagnostic{
        .severity = .warning,
        .code = .parse_error,
        .span = span,
        .message = "unexpected token",
    };

    try std.testing.expectEqual(@as(usize, 0), diag.notes.len);
}

test "Note with null span" {
    const note = Note{ .message = "suggestion: try using 'let'" };
    try std.testing.expect(note.span == null);
    try std.testing.expectEqualStrings("suggestion: try using 'let'", note.message);
}

test "Note with span" {
    const span = SourceSpan.init(
        SourcePos.init(1, 5, 1),
        SourcePos.init(1, 5, 10),
    );
    const note = Note{ .message = "previously defined here", .span = span };
    try std.testing.expect(note.span != null);
}

test "DiagnosticBag tracks errors" {
    var bag = DiagnosticBag.init();
    defer bag.deinit(std.testing.allocator);

    const span = SourceSpan.init(
        SourcePos.init(1, 1, 1),
        SourcePos.init(1, 1, 5),
    );

    // Initially no errors
    try std.testing.expect(!bag.had_errors);
    try std.testing.expectEqual(@as(usize, 0), bag.errorCount());

    // Add a warning — does not set had_errors
    try bag.add(std.testing.allocator, .{
        .severity = .warning,
        .code = .parse_error,
        .span = span,
        .message = "unused variable",
    });
    try std.testing.expect(!bag.had_errors);
    try std.testing.expectEqual(@as(usize, 0), bag.errorCount());
    try std.testing.expectEqual(@as(usize, 1), bag.diagnostics.items.len);

    // Add an error — sets had_errors
    try bag.add(std.testing.allocator, .{
        .severity = .@"error",
        .code = .unbound_variable,
        .span = span,
        .message = "not in scope: 'x'",
    });
    try std.testing.expect(bag.had_errors);
    try std.testing.expectEqual(@as(usize, 1), bag.errorCount());
    try std.testing.expectEqual(@as(usize, 2), bag.diagnostics.items.len);

    // Add an info — does not change error count
    try bag.add(std.testing.allocator, .{
        .severity = .info,
        .code = .type_error,
        .span = span,
        .message = "inferred type: Int",
    });
    try std.testing.expectEqual(@as(usize, 1), bag.errorCount());
    try std.testing.expectEqual(@as(usize, 3), bag.diagnostics.items.len);
}
