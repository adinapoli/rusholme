//! JSON diagnostic renderer for machine consumption.
//!
//! Serializes diagnostics to JSON format for tools that parse
//! compiler output programmatically: editors, CI, LSP, etc.
//!
//! JSON schema:
//! ```json
//! {
//!   "severity": "error",
//!   "code": "E003",
//!   "file": "Main.hs",
//!   "startLine": 10,
//!   "startCol": 5,
//!   "endLine": 10,
//!   "endCol": 20,
//!   "message": "Variable 'foo' is not in scope",
//!   "notes": [
//!     {
//!       "message": "did you mean 'baz'?",
//!       "file": "Main.hs",
//!       "startLine": 5,
//!       "startCol": 1,
//!       "endLine": 5,
//!       "endCol": 10
//!     }
//!   ]
//! }
//! ```

const std = @import("std");
const span_mod = @import("span.zig");
const diag_mod = @import("diagnostic.zig");
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;
const Diagnostic = diag_mod.Diagnostic;
const Severity = diag_mod.Severity;
const DiagnosticCode = diag_mod.DiagnosticCode;
const Note = diag_mod.Note;
const FileId = span_mod.FileId;

/// JSON-ready representation of a note.
const JsonNote = struct {
    message: []const u8,
    /// Optional span information (null if note has no span)
    file: ?[]const u8 = null,
    startLine: ?u32 = null,
    startCol: ?u32 = null,
    endLine: ?u32 = null,
    endCol: ?u32 = null,
};

/// JSON-ready representation of a diagnostic.
const JsonDiagnostic = struct {
    severity: []const u8,
    code: []const u8,
    file: []const u8,
    startLine: u32,
    startCol: u32,
    endLine: u32,
    endCol: u32,
    message: []const u8,
    notes: []const JsonNote = &.{},
};

/// JSON diagnostic renderer.
///
/// Serializes Diagnostic instances to JSON format using Zig's std.json.
pub const JsonRenderer = struct {
    /// Path lookup table (FileId -> file path)
    path_lookup: *const std.AutoHashMap(FileId, []const u8),
    /// Allocator for JSON serialization
    allocator: std.mem.Allocator,

    /// Initialize a new JsonRenderer.
    pub fn init(
        allocator: std.mem.Allocator,
        path_lookup: *const std.AutoHashMap(FileId, []const u8),
    ) JsonRenderer {
        return .{
            .allocator = allocator,
            .path_lookup = path_lookup,
        };
    }

    /// Render a single diagnostic to a JSON string.
    ///
    /// Caller owns the returned string and must free it with the allocator.
    pub fn render(self: JsonRenderer, diag: Diagnostic) ![]const u8 {
        const severity_str = switch (diag.severity) {
            .@"error" => "error",
            .warning => "warning",
            .info => "info",
            .hint => "hint",
        };

        const path = self.path_lookup.get(diag.span.start.file_id) orelse "<unknown>";

        var notes: std.ArrayListUnmanaged(JsonNote) = .{};

        for (diag.notes) |note| {
            var json_note: JsonNote = .{ .message = note.message };

            if (note.span) |span| {
                const note_path = self.path_lookup.get(span.start.file_id) orelse "<unknown>";
                json_note.file = note_path;
                json_note.startLine = span.start.line;
                json_note.startCol = span.start.column;
                json_note.endLine = span.end.line;
                json_note.endCol = span.end.column;
            }

            try notes.append(self.allocator, json_note);
        }

        const json_diag = JsonDiagnostic{
            .severity = severity_str,
            .code = diag.code.code(),
            .file = path,
            .startLine = diag.span.start.line,
            .startCol = diag.span.start.column,
            .endLine = diag.span.end.line,
            .endCol = diag.span.end.column,
            .message = diag.message,
            .notes = try notes.toOwnedSlice(self.allocator),
        };

        var out: std.Io.Writer.Allocating = .init(self.allocator);
        defer out.deinit();

        var write_stream: std.json.Stringify = .{
            .writer = &out.writer,
            .options = .{ .whitespace = .indent_2 },
        };

        try write_stream.write(json_diag);
        return try out.toOwnedSlice();
    }

    /// Render multiple diagnostics to a JSON array string.
    ///
    /// Caller owns the returned string and must free it with the allocator.
    pub fn renderAll(self: JsonRenderer, diagnostics: []const Diagnostic) ![]const u8 {
        var json_diags: std.ArrayListUnmanaged(JsonDiagnostic) = .{};

        for (diagnostics) |diag| {
            const severity_str = switch (diag.severity) {
                .@"error" => "error",
                .warning => "warning",
                .info => "info",
                .hint => "hint",
            };

            const path = self.path_lookup.get(diag.span.start.file_id) orelse "<unknown>";

            var notes: std.ArrayListUnmanaged(JsonNote) = .{};

            for (diag.notes) |note| {
                var json_note: JsonNote = .{ .message = note.message };

                if (note.span) |span| {
                    const note_path = self.path_lookup.get(span.start.file_id) orelse "<unknown>";
                    json_note.file = note_path;
                    json_note.startLine = span.start.line;
                    json_note.startCol = span.start.column;
                    json_note.endLine = span.end.line;
                    json_note.endCol = span.end.column;
                }

                try notes.append(self.allocator, json_note);
            }

            try json_diags.append(self.allocator, .{
                .severity = severity_str,
                .code = diag.code.code(),
                .file = path,
                .startLine = diag.span.start.line,
                .startCol = diag.span.start.column,
                .endLine = diag.span.end.line,
                .endCol = diag.span.end.column,
                .message = diag.message,
                .notes = try notes.toOwnedSlice(self.allocator),
            });
        }

        const diags_slice = try json_diags.toOwnedSlice(self.allocator);

        var out: std.Io.Writer.Allocating = .init(self.allocator);
        defer out.deinit();

        var write_stream: std.json.Stringify = .{
            .writer = &out.writer,
            .options = .{ .whitespace = .indent_2 },
        };

        try write_stream.write(diags_slice);
        return try out.toOwnedSlice();
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

test "JsonRenderer renders basic diagnostic" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var path_lookup = std.AutoHashMap(FileId, []const u8).init(allocator);
    try path_lookup.put(1, "test.hs");

    const renderer = JsonRenderer.init(allocator, &path_lookup);

    const span = SourceSpan.init(
        SourcePos.init(1, 10, 5),
        SourcePos.init(1, 10, 20),
    );

    const diag = Diagnostic{
        .severity = .@"error",
        .code = .unbound_variable,
        .span = span,
        .message = "Variable 'foo' is not in scope",
    };

    const json = try renderer.render(diag);

    // Verify the JSON contains expected fields
    try std.testing.expect(std.mem.indexOf(u8, json, "\"severity\": \"error\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"code\": \"E003\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"file\": \"test.hs\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"startLine\": 10") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"startCol\": 5") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"endLine\": 10") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"endCol\": 20") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"message\": \"Variable 'foo' is not in scope\"") != null);
}

test "JsonRenderer renders diagnostic with note" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var path_lookup = std.AutoHashMap(FileId, []const u8).init(allocator);
    try path_lookup.put(1, "test.hs");
    try path_lookup.put(2, "import.hs");

    const renderer = JsonRenderer.init(allocator, &path_lookup);

    const span = SourceSpan.init(
        SourcePos.init(1, 10, 5),
        SourcePos.init(1, 10, 20),
    );

    const note_span = SourceSpan.init(
        SourcePos.init(2, 5, 1),
        SourcePos.init(2, 5, 10),
    );

    const notes = [_]Note{
        .{ .message = "defined here", .span = note_span },
        .{ .message = "did you mean 'baz'?" },
    };

    const diag = Diagnostic{
        .severity = .@"error",
        .code = .duplicate_definition,
        .span = span,
        .message = "Duplicate definition",
        .notes = &notes,
    };

    const json = try renderer.render(diag);

    // Verify note with span
    try std.testing.expect(std.mem.indexOf(u8, json, "\"message\": \"defined here\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"file\": \"import.hs\"") != null);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"startLine\": 5") != null);

    // Verify note without span
    try std.testing.expect(std.mem.indexOf(u8, json, "\"message\": \"did you mean 'baz'?\"") != null);
}

test "JsonRenderer handles warning severity" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var path_lookup = std.AutoHashMap(FileId, []const u8).init(allocator);
    try path_lookup.put(1, "test.hs");

    const renderer = JsonRenderer.init(allocator, &path_lookup);

    const span = SourceSpan.init(
        SourcePos.init(1, 1, 1),
        SourcePos.init(1, 1, 50),
    );

    const diag = Diagnostic{
        .severity = .warning,
        .code = .parse_error,
        .span = span,
        .message = "Unused variable",
    };

    const json = try renderer.render(diag);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"severity\": \"warning\"") != null);
}

test "JsonRenderer handles unknown file" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var path_lookup = std.AutoHashMap(FileId, []const u8).init(allocator);
    // Don't add any paths

    const renderer = JsonRenderer.init(allocator, &path_lookup);

    const span = SourceSpan.init(
        SourcePos.init(999, 10, 5),
        SourcePos.init(999, 10, 20),
    );

    const diag = Diagnostic{
        .severity = .@"error",
        .code = .type_error,
        .span = span,
        .message = "Type error",
    };

    const json = try renderer.render(diag);
    try std.testing.expect(std.mem.indexOf(u8, json, "\"file\": \"<unknown>\"") != null);
}
