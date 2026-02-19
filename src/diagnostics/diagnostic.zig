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

    pub fn format(self: Severity, w: *std.Io.Writer) std.Io.Writer.Error!void {
        const s = switch (self) {
            .@"error" => "error",
            .warning => "warning",
            .info => "info",
            .hint => "hint",
        };
        try w.writeAll(s);
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
    missing_instance,
    overlapping_instances,
    ambiguous_type,

    /// Returns a stable string code like "E001" for programmatic use.
    pub fn code(self: DiagnosticCode) []const u8 {
        return switch (self) {
            .parse_error => "E001",
            .type_error => "E002",
            .unbound_variable => "E003",
            .duplicate_definition => "E004",
            .kind_error => "E005",
            .missing_instance => "E006",
            .overlapping_instances => "E007",
            .ambiguous_type => "E008",
        };
    }

    pub fn format(self: DiagnosticCode, w: *std.Io.Writer) std.Io.Writer.Error!void {
        try w.writeAll(self.code());
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

/// Structured payload for diagnostics with additional information.
///
/// Rich renderers can use this to provide enhanced output (e.g., type diffs,
/// syntax highlighting, etc.). The `message` field is always populated for
/// backward compatibility with plain-text sinks.
pub const DiagnosticPayload = union(enum) {
    /// Type error with structured type information.
    type_error: @import("../typechecker/type_error.zig").TypeError,
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
    /// Optional structured payload for rich renderers.
    ///
    /// When present, renderers can extract type information, syntax details,
    /// etc. to provide enhanced output (e.g., type diffs, highlighting).
    /// The `message` field is always populated as fallback for plain-text output.
    payload: ?DiagnosticPayload = null,
};

/// Accumulates diagnostics across compilation stages.
///
/// Tracks whether any errors have been emitted to allow early termination
/// decisions without scanning the full list.
///
/// Thread Safety: This implementation is single-threaded. If multi-threaded
/// compilation is needed in the future, wrap `diagnostics` in a mutex and
/// modify `hasErrors()` and `errorCount()` to read under lock protection.
pub const DiagnosticCollector = struct {
    diagnostics: std.ArrayListUnmanaged(Diagnostic),
    had_errors: bool = false,

    pub fn init() DiagnosticCollector {
        return .{
            .diagnostics = .{},
        };
    }

    pub fn deinit(self: *DiagnosticCollector, allocator: std.mem.Allocator) void {
        self.diagnostics.deinit(allocator);
        self.* = undefined;
    }

    /// Emit a diagnostic to the collector.
    pub fn emit(self: *DiagnosticCollector, allocator: std.mem.Allocator, diag: Diagnostic) !void {
        if (diag.severity == .@"error") {
            self.had_errors = true;
        }
        try self.diagnostics.append(allocator, diag);
    }

    /// Add a diagnostic to the collector (backward compatibility alias for emit).
    pub fn add(self: *DiagnosticCollector, allocator: std.mem.Allocator, diag: Diagnostic) !void {
        return self.emit(allocator, diag);
    }

    /// Returns true if any error-severity diagnostics have been emitted.
    pub fn hasErrors(self: DiagnosticCollector) bool {
        return self.had_errors;
    }

    /// Returns the total number of error-severity diagnostics.
    pub fn errorCount(self: DiagnosticCollector) usize {
        var count: usize = 0;
        for (self.diagnostics.items) |d| {
            if (d.severity == .@"error") count += 1;
        }
        return count;
    }

    /// Returns all diagnostics sorted by source location.
    /// For diagnostics with the same location, maintains insertion order.
    /// Caller owns the returned slice (free with allocator).
    /// Returns an empty slice that doesn't need freeing if collector is empty.
    pub fn getAll(self: *DiagnosticCollector, allocator: std.mem.Allocator) ![]const Diagnostic {
        if (self.diagnostics.items.len == 0) return &.{};

        // Create a mutable copy for sorting
        const sorted = try allocator.dupe(Diagnostic, self.diagnostics.items);
        errdefer allocator.free(sorted);

        // Sort the copy in place
        std.sort.block(Diagnostic, sorted, {}, compareDiagnostic);

        return sorted;
    }

    // Helper: Compare two diagnostics by source location for sorting
    fn compareDiagnostic(_: void, a: Diagnostic, b: Diagnostic) bool {
        // Compare by file_id first
        if (a.span.start.file_id != b.span.start.file_id) {
            return a.span.start.file_id < b.span.start.file_id;
        }

        // Same file: compare line
        if (a.span.start.line != b.span.start.line) {
            return a.span.start.line < b.span.start.line;
        }

        // Same line: compare column
        return a.span.start.column < b.span.start.column;
    }
};

/// Backward compatibility alias for existing code.
pub const DiagnosticBag = DiagnosticCollector;

// ── Tests ──────────────────────────────────────────────────────────────

test "Severity.format renders all variants" {
    var buf: [16]u8 = undefined;

    const err_str = try std.fmt.bufPrint(&buf, "{f}", .{Severity.@"error"});
    try std.testing.expectEqualStrings("error", err_str);

    const warn_str = try std.fmt.bufPrint(&buf, "{f}", .{Severity.warning});
    try std.testing.expectEqualStrings("warning", warn_str);

    const info_str = try std.fmt.bufPrint(&buf, "{f}", .{Severity.info});
    try std.testing.expectEqualStrings("info", info_str);

    const hint_str = try std.fmt.bufPrint(&buf, "{f}", .{Severity.hint});
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

    const code_str = try std.fmt.bufPrint(&buf, "{f}", .{DiagnosticCode.parse_error});
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
    try std.testing.expect(!bag.hasErrors());
    try std.testing.expectEqual(@as(usize, 0), bag.errorCount());

    // Add a warning via add() (backward compatibility)
    try bag.add(std.testing.allocator, .{
        .severity = .warning,
        .code = .parse_error,
        .span = span,
        .message = "unused variable",
    });
    try std.testing.expect(!bag.had_errors);
    try std.testing.expect(!bag.hasErrors());
    try std.testing.expectEqual(@as(usize, 0), bag.errorCount());
    try std.testing.expectEqual(@as(usize, 1), bag.diagnostics.items.len);

    // Add an error via emit() (new API)
    try bag.emit(std.testing.allocator, .{
        .severity = .@"error",
        .code = .unbound_variable,
        .span = span,
        .message = "not in scope: 'x'",
    });
    try std.testing.expect(bag.had_errors);
    try std.testing.expect(bag.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), bag.errorCount());
    try std.testing.expectEqual(@as(usize, 2), bag.diagnostics.items.len);

    // Add an info
    try bag.emit(std.testing.allocator, .{
        .severity = .info,
        .code = .type_error,
        .span = span,
        .message = "inferred type: Int",
    });
    try std.testing.expectEqual(@as(usize, 1), bag.errorCount());
    try std.testing.expectEqual(@as(usize, 3), bag.diagnostics.items.len);
}

test "DiagnosticCollector getAll returns sorted by location" {
    var collector = DiagnosticCollector.init();
    defer collector.deinit(std.testing.allocator);

    // Add diagnostics in random order
    try collector.emit(std.testing.allocator, .{
        .severity = .@"error",
        .code = .parse_error,
        .span = SourceSpan.init(SourcePos.init(1, 10, 5), SourcePos.init(1, 10, 20)),
        .message = "error at line 10",
    });

    try collector.emit(std.testing.allocator, .{
        .severity = .@"error",
        .code = .parse_error,
        .span = SourceSpan.init(SourcePos.init(1, 5, 1), SourcePos.init(1, 5, 10)),
        .message = "error at line 5",
    });

    try collector.emit(std.testing.allocator, .{
        .severity = .@"error",
        .code = .parse_error,
        .span = SourceSpan.init(SourcePos.init(1, 15, 1), SourcePos.init(1, 15, 5)),
        .message = "error at line 15",
    });

    // Get sorted diagnostics
    const diags = try collector.getAll(std.testing.allocator);
    defer std.testing.allocator.free(diags);
    try std.testing.expectEqual(@as(usize, 3), diags.len);

    // Should be sorted by line number: 5, 10, 15
    try std.testing.expectEqual(@as(u32, 5), diags[0].span.start.line);
    try std.testing.expectEqual(@as(u32, 10), diags[1].span.start.line);
    try std.testing.expectEqual(@as(u32, 15), diags[2].span.start.line);

    try std.testing.expectEqualStrings("error at line 5", diags[0].message);
    try std.testing.expectEqualStrings("error at line 10", diags[1].message);
    try std.testing.expectEqualStrings("error at line 15", diags[2].message);
}

test "DiagnosticCollector getAll handles empty collector" {
    var collector = DiagnosticCollector.init();
    defer collector.deinit(std.testing.allocator);

    const diags = try collector.getAll(std.testing.allocator);
    // Empty collector returns sentinel, don't free
    try std.testing.expectEqual(@as(usize, 0), diags.len);
}
