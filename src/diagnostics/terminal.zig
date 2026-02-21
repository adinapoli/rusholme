//! Terminal diagnostic renderer with colored output.
//!
//! Renders diagnostics to the terminal with ANSI escape codes for severity
//! coloring. Designed to match rustc-style error format.
//!
//! Source code snippets are rendered with context lines and highlighting.
//!
//! Diagnostics with structured payloads (e.g., type errors) are rendered
//! with enhanced formatting using the payload information.

const std = @import("std");
const Io = std.Io;
const span_mod = @import("span.zig");
const diag_mod = @import("diagnostic.zig");
const type_error_mod = @import("../typechecker/type_error.zig");
const SourceSpan = span_mod.SourceSpan;
const SourcePos = span_mod.SourcePos;
const Diagnostic = diag_mod.Diagnostic;
const Severity = diag_mod.Severity;
const DiagnosticCode = diag_mod.DiagnosticCode;
const DiagnosticPayload = diag_mod.DiagnosticPayload;
const Note = diag_mod.Note;
const TypeError = type_error_mod.TypeError;
const FileId = span_mod.FileId;

/// ANSI color codes for terminal output
inline fn reset() []const u8 { return "\x1b[0m"; }
inline fn brightRed() []const u8 { return "\x1b[1;31m"; }
inline fn brightYellow() []const u8 { return "\x1b[1;33m"; }
inline fn brightBlue() []const u8 { return "\x1b[1;34m"; }
inline fn brightMagenta() []const u8 { return "\x1b[1;35m"; }
inline fn brightCyan() []const u8 { return "\x1b[1;36m"; }
inline fn grey() []const u8 { return "\x1b[90m"; }
inline fn brightGreen() []const u8 { return "\x1b[1;32m"; }

/// Configuration for source context lines to show before and after errors.
const CONTEXT_LINES_BEFORE: u32 = 1;
const CONTEXT_LINES_AFTER: u32 = 1;

/// Terminal diagnostic renderer.
///
/// Takes a Diagnostic and produces formatted terminal output with ANSI coloring.
pub const TerminalRenderer = struct {
    // Source file path lookup (FileId -> file path)
    path_lookup: *const std.AutoHashMap(FileId, []const u8),
    // Source file contents lookup (FileId -> file content)
    file_contents: *const std.AutoHashMap(FileId, []const u8),
    // Flag to disable color output (for pipes/non-TTY)
    color_enabled: bool = true,

    /// Initialize a new TerminalRenderer with source file lookups.
    pub fn init(
        path_lookup: *const std.AutoHashMap(FileId, []const u8),
        file_contents: *const std.AutoHashMap(FileId, []const u8),
    ) TerminalRenderer {
        return .{
            .path_lookup = path_lookup,
            .file_contents = file_contents,
            .color_enabled = detectColorSupport(),
        };
    }

    /// Check if color output should be enabled (TTY detection).
    fn detectColorSupport() bool {
        // In production, this would check std.io.isTty for stderr
        // For now, enable colors by default
        return true;
    }

    /// Render a diagnostic to a writer.
    pub fn render(self: TerminalRenderer, writer: anytype, diag: Diagnostic) !void {
        // Render the primary diagnostic
        try self.renderPrimary(writer, diag);

        // Render the source code snippet
        try self.renderSnippet(writer, diag.span);

        // Render secondary notes
        for (diag.notes) |note| {
            try self.renderNote(writer, note);
        }
    }

    /// Render the primary diagnostic.
    fn renderPrimary(self: TerminalRenderer, writer: anytype, diag: Diagnostic) !void {
        // File:line:col header
        try self.renderLocation(writer, diag.span);

        // Severity and code with color
        try self.renderSeverity(writer, diag.severity, diag.code);

        // Primary message
        try writer.writeByte('\n');

        // If we have a type_error payload, render enhanced type information
        if (diag.payload) |payload| {
            switch (payload) {
                .type_error => |te| try self.renderTypeError(writer, te),
            }
        } else {
            // Fallback to simple message rendering
            try writer.writeAll("    ");
            try writer.print("{s}{s}{s}", .{
                if (self.color_enabled) brightMagenta() else "",
                diag.message,
                if (self.color_enabled) reset() else "",
            });
            try writer.writeByte('\n');
        }
    }

    /// Render a type error with enhanced formatting.
    fn renderTypeError(self: TerminalRenderer, writer: anytype, te: TypeError) !void {
        const indent = "    ";
        const err_color = if (self.color_enabled) brightRed() else "";
        const cyan_color = if (self.color_enabled) brightCyan() else "";
        const yellow_color = if (self.color_enabled) brightYellow() else "";
        const reset_color = if (self.color_enabled) reset() else "";

        try writer.writeAll(indent);

        switch (te) {
            .mismatch => |m| {
                try writer.print("{s}---{s} cannot unify types{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   {s}expected:{s} ", .{ cyan_color, reset_color });

                const lhs_str = try m.lhs.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, lhs_str, reset_color });

                try writer.writeAll(indent);
                try writer.print("     {s}found:{s} ", .{ cyan_color, reset_color });

                const rhs_str = try m.rhs.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ err_color, rhs_str, reset_color });
            },
            .infinite_type => |it| {
                try writer.print("{s}---{s} occurs check failed{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   metavariable: {s}?{d}{s}\n", .{ yellow_color, it.meta.id, reset_color });

                try writer.writeAll(indent);
                try writer.print("     appears in: {s}", .{ cyan_color });
                const ty_str = try it.ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, ty_str, reset_color });
            },
            .arity_mismatch => |am| {
                try writer.print("{s}---{s} arity mismatch{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   constructor: {s}`{s}`{s}\n", .{
                    yellow_color, am.name.base, reset_color,
                });
                try writer.writeAll(indent);
                try writer.print("   {s}expected: {d} argument(s){s}\n", .{
                    cyan_color, am.expected, reset_color,
                });
                try writer.writeAll(indent);
                try writer.print("     {s}got: {d} argument(s){s}\n", .{
                    cyan_color, am.got, reset_color,
                });
            },
            .application_error => |ae| {
                try writer.print("{s}---{s} non-function application{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   function type: {s}", .{ cyan_color });
                const fn_str = try ae.fn_ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, fn_str, reset_color });

                try writer.writeAll(indent);
                try writer.print("   argument type: {s}", .{ cyan_color });
                const arg_str = try ae.arg_ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ err_color, arg_str, reset_color });
            },
            .pattern_mismatch => |pm| {
                try writer.print("{s}---{s} pattern type mismatch{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   pattern type: {s}", .{ cyan_color });
                const pat_str = try pm.pat_ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, pat_str, reset_color });

                try writer.writeAll(indent);
                try writer.print("   scrutinee type: {s}", .{ cyan_color });
                const scrutinee_str = try pm.scrutinee_ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ err_color, scrutinee_str, reset_color });
            },
            .missing_instance => |mi| {
                try writer.print("{s}---{s} no instance for type class{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   class: {s}`{s}`{s}\n", .{ yellow_color, mi.class_name.base, reset_color });
                try writer.writeAll(indent);
                try writer.print("   type: {s}", .{ cyan_color });
                const ty_str = try mi.ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, ty_str, reset_color });
            },
            .overlapping_instances => |oi| {
                try writer.print("{s}---{s} overlapping instances{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   class: {s}`{s}`{s}\n", .{ yellow_color, oi.class_name.base, reset_color });
                try writer.writeAll(indent);
                try writer.print("   type: {s}", .{ cyan_color });
                const ty_str = try oi.ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, ty_str, reset_color });
            },
            .ambiguous_type => |at| {
                try writer.print("{s}---{s} ambiguous type variable{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   class: {s}`{s}`{s}\n", .{ yellow_color, at.class_name.base, reset_color });
                try writer.writeAll(indent);
                try writer.print("   type: {s}", .{ cyan_color });
                const ty_str = try at.ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, ty_str, reset_color });
            },
            .no_such_class => |nc| {
                try writer.print("{s}---{s} not a type class{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   name: {s}`{s}`{s}\n", .{ yellow_color, nc.name.base, reset_color });
            },
            .missing_method => |mm| {
                try writer.print("{s}---{s} missing method implementation{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   class: {s}`{s}`{s}\n", .{ yellow_color, mm.class_name.base, reset_color });
                try writer.writeAll(indent);
                try writer.print("   method: {s}`{s}`{s}\n", .{ yellow_color, mm.method_name.base, reset_color });
                try writer.writeAll(indent);
                try writer.print("   instance type: {s}", .{ cyan_color });
                const ty_str = try mm.instance_ty.pretty(self.file_contents.allocator);
                try writer.print("{s}`{s}`{s}\n", .{ yellow_color, ty_str, reset_color });
            },
            .infinite_type_cycle => |itc| {
                try writer.print("{s}---{s} infinite type cycle detected{c}", .{ err_color, reset_color, '\n' });
                try writer.writeAll(indent);
                try writer.print("   metavariable: {s}?{d}{s}\n", .{ yellow_color, itc.meta_id, reset_color });
                try writer.writeAll(indent);
                try writer.print("   {s}note:{s} a cycle was detected in the type variable chain.\n", .{ cyan_color, reset_color });
            },
        }
    }

    /// Render source code snippet with context and highlighting.
    fn renderSnippet(self: TerminalRenderer, writer: anytype, span: SourceSpan) !void {
        const content = self.file_contents.get(span.start.file_id) orelse return;

        // Parse the content into lines
        const lines = try parseLines(self.file_contents.allocator, content);
        defer self.file_contents.allocator.free(lines);

        const start_idx = @max(0, @as(isize, @intCast(span.start.line)) - @as(isize, CONTEXT_LINES_BEFORE) - 1);
        const end_idx = @min(lines.len, @as(usize, span.end.line) + CONTEXT_LINES_AFTER);

        // Calculate line number width for alignment
        const max_line_num = @as(usize, @intCast(end_idx));
        const line_num_width = @max(2, lineNumStrLen(max_line_num));

        // Render each line with context
        for (lines[start_idx..end_idx], start_idx + 1..) |line, line_num| {
            try writer.writeAll(if (self.color_enabled) grey() else "");
            try writeRightAligned(writer, line_num, line_num_width);
            try writer.writeAll(".");
            try writer.writeAll(if (self.color_enabled) reset() else "");
            try writer.writeAll(" ");
            try writer.writeAll(line);
            try writer.writeByte('\n');

            // If this line is the first line of the error span, render the highlight
            if (line_num == span.start.line) {
                try self.renderHighlight(writer, line, span, line_num_width);
            }
        }
    }

    /// Render the highlight (carets) under the error location.
    fn renderHighlight(
        self: TerminalRenderer,
        writer: anytype,
        line: []const u8,
        span: SourceSpan,
        line_num_width: usize,
    ) !void {
        // Calculate column positions (adjust for 1-based indexing)
        const start_col = @as(usize, span.start.column) - 1;
        const end_col = if (span.start.line == span.end.line)
            @as(usize, span.end.column) - 1
        else
            @min(line.len, 1000); // Cap at reasonable length

        // Check if we have enough characters in the line
        const line_len = line.len;
        if (start_col >= line_len or end_col > line_len) return;

        // Build the highlight line
        // Pad left for line number gutter
        try writer.writeAll(if (self.color_enabled) grey() else "");
        for (0..line_num_width) |_| try writer.writeByte(' ');
        try writer.writeAll(".");
        try writer.writeAll(if (self.color_enabled) reset() else "");
        try writer.writeByte(' ');

        // Add spaces up to start column
        const highlight_color = if (self.color_enabled) brightRed() else "";
        const reset_color = if (self.color_enabled) reset() else "";

        // Write leading spaces (considering tabs as 8 spaces)
        var col: usize = 0;
        while (col < start_col) {
            if (col < line.len and line[col] == '\t') {
                try writer.writeByte(' ');
                const stop = @min(start_col, col + 8);
                while (col < stop) : (col += 1) try writer.writeByte(' ');
            } else {
                try writer.writeByte(' ');
                col += 1;
            }
        }

        // Write the highlight (^ marks)
        try writer.print("{s}", .{highlight_color});
        while (col < end_col) {
            if (col < line.len and line[col] == '\t') {
                const stop = @min(end_col, col + 8);
                while (col < stop) : (col += 1) try writer.writeByte('^');
            } else {
                try writer.writeByte('^');
                col += 1;
            }
        }
        try writer.print("{s}\n", .{reset_color});
    }

    /// Render a secondary note.
    fn renderNote(self: TerminalRenderer, writer: anytype, note: Note) !void {
        // Note prefix with location span (if present)
        if (note.span) |span| {
            try writer.writeAll("   ┌─ ");
            try self.renderLocation(writer, span);
        } else {
            try writer.writeAll("   ├── ");
        }

        // Note message
        try writer.print("{s}  note{s} {s}\n", .{
            if (self.color_enabled) brightCyan() else "",
            if (self.color_enabled) reset() else "",
            note.message,
        });

        // Render snippet for notes with spans
        if (note.span) |span| {
            try self.renderSnippet(writer, span);
        }
    }

    /// Render source location (file:line:col-line:col).
    fn renderLocation(self: TerminalRenderer, writer: anytype, span: SourceSpan) !void {
        const path = self.path_lookup.get(span.start.file_id) orelse "<unknown>";

        if (span.start.file_id == span.end.file_id and span.start.line == span.end.line) {
            // Single file, single line: file.hs:10:5-20
            try writer.print("{s}:{d}:{d}-{d} ", .{ path, span.start.line, span.start.line, span.end.column });
        } else if (span.start.file_id == span.end.file_id) {
            // Single file, multiple lines: file.hs:10:5-15:20
            try writer.print("{s}:{d}:{d}-{d}:{d} ", .{
                path,
                span.start.line,
                span.start.column,
                span.end.line,
                span.end.column,
            });
        } else {
            // Multiple files: file1.hs:10:5-file2.hs:15:20 (rare, for synthetic errors)
            try writer.print("{s}:{d}:{d}-{s}:{d}:{d} ", .{
                path,
                span.start.line,
                span.start.column,
                self.path_lookup.get(span.end.file_id) orelse "<unknown>",
                span.end.line,
                span.end.column,
            });
        }
    }

    /// Render severity and diagnostic code.
    fn renderSeverity(self: TerminalRenderer, writer: anytype, severity: Severity, code: DiagnosticCode) !void {
        const color_str: []const u8 = switch (severity) {
            .@"error" => brightRed(),
            .warning => brightYellow(),
            .info => brightBlue(),
            .hint => brightMagenta(),
        };

        const severity_str: []const u8 = switch (severity) {
            .@"error" => "error",
            .warning => "warning",
            .info => "info",
            .hint => "hint",
        };

        if (self.color_enabled) {
            try writer.print("{s}{s}[{s}]{s}", .{ color_str, severity_str, code.code(), reset() });
        } else {
            try writer.print("{s}[{s}]", .{ severity_str, code.code() });
        }
    }
};

/// Parse a file's content into lines.
fn parseLines(allocator: std.mem.Allocator, content: []const u8) ![][]const u8 {
    var lines: std.ArrayListUnmanaged([]const u8) = .{};

    var start: usize = 0;
    for (content, 0..) |byte, i| {
        if (byte == '\n') {
            try lines.append(allocator, content[start..i]);
            start = i + 1;
        }
    }
    // Add the last line if there's no trailing newline
    if (start < content.len) {
        try lines.append(allocator, content[start..]);
    }

    return try lines.toOwnedSlice(allocator);
}

/// Write a number right-aligned to the given width.
fn writeRightAligned(writer: anytype, value: usize, width: usize) !void {
    const digits = lineNumStrLen(value);
    if (width > digits) {
        for (0..width - digits) |_| try writer.writeByte(' ');
    }
    var buf: [20]u8 = undefined;
    const slice = std.fmt.bufPrint(&buf, "{d}", .{value}) catch unreachable;
    try writer.writeAll(slice);
}

/// Calculate the number of characters needed to represent a line number.
fn lineNumStrLen(n: usize) usize {
    if (n < 10) return 1;
    if (n < 100) return 2;
    if (n < 1000) return 3;
    if (n < 10000) return 4;
    return 5;
}

// ── Tests ──────────────────────────────────────────────────────────────

test {
    // Test that ANSI color codes return valid strings
    try std.testing.expect(reset().len > 0);
    try std.testing.expect(brightRed().len > 0);
    try std.testing.expect(brightYellow().len > 0);
    try std.testing.expect(brightBlue().len > 0);
    try std.testing.expect(brightMagenta().len > 0);
    try std.testing.expect(brightCyan().len > 0);
    try std.testing.expect(grey().len > 0);
    try std.testing.expect(brightGreen().len > 0);
}

test "parseLines splits content correctly" {
    const content = "line1\nline2\nline3\n";
    const lines = try parseLines(std.testing.allocator, content);
    defer std.testing.allocator.free(lines);

    try std.testing.expectEqual(@as(usize, 3), lines.len);
    try std.testing.expectEqualStrings("line1", lines[0]);
    try std.testing.expectEqualStrings("line2", lines[1]);
    try std.testing.expectEqualStrings("line3", lines[2]);
}

test "parseLines handles no trailing newline" {
    const content = "line1\nline2\nline3";
    const lines = try parseLines(std.testing.allocator, content);
    defer std.testing.allocator.free(lines);

    try std.testing.expectEqual(@as(usize, 3), lines.len);
    try std.testing.expectEqualStrings("line1", lines[0]);
    try std.testing.expectEqualStrings("line2", lines[1]);
    try std.testing.expectEqualStrings("line3", lines[2]);
}

test "parseLines handles empty content" {
    const content = "";
    const lines = try parseLines(std.testing.allocator, content);
    defer std.testing.allocator.free(lines);

    try std.testing.expectEqual(@as(usize, 0), lines.len);
}

test "lineNumStrLen calculates correct widths" {
    try std.testing.expectEqual(@as(usize, 1), lineNumStrLen(9));
    try std.testing.expectEqual(@as(usize, 2), lineNumStrLen(10));
    try std.testing.expectEqual(@as(usize, 2), lineNumStrLen(99));
    try std.testing.expectEqual(@as(usize, 3), lineNumStrLen(100));
    try std.testing.expectEqual(@as(usize, 3), lineNumStrLen(999));
    try std.testing.expectEqual(@as(usize, 4), lineNumStrLen(1000));
}

test "TerminalRenderer initializes with lookups" {
    var path_lookup = std.AutoHashMap(FileId, []const u8).init(std.testing.allocator);
    defer path_lookup.deinit();
    try path_lookup.put(1, "test.hs");

    var file_contents = std.AutoHashMap(FileId, []const u8).init(std.testing.allocator);
    defer file_contents.deinit();
    try file_contents.put(1, "content");

    const renderer = TerminalRenderer.init(&path_lookup, &file_contents);

    try std.testing.expectEqualStrings("test.hs", renderer.path_lookup.get(1).?);
    try std.testing.expectEqualStrings("content", renderer.file_contents.get(1).?);
}
