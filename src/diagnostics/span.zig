//! Source location tracking diagnostics.
//!
//! This module provides types for tracking source positions and spans
//! throughout the compiler pipeline, enabling precise error reporting.

const std = @import("std");

/// An integer identifier for a source file.
/// Using file IDs instead of strings avoids duplicating file paths.
pub const FileId = u32;

const INVALID_FILE_ID: FileId = 0;

/// A position in a source file.
/// All line and column numbers are 1-based (as per GCC and editor conventions).
pub const SourcePos = struct {
    file_id: FileId,
    line: u32,
    column: u32,

    /// Creates a new SourcePos. Panics if line or column is 0.
    pub fn init(file_id: FileId, line: u32, column: u32) SourcePos {
        std.debug.assert(line > 0, "line numbers are 1-based");
        std.debug.assert(column > 0, "column numbers are 1-based");
        return .{
            .file_id = file_id,
            .line = line,
            .column = column,
        };
    }

    /// Creates an invalid SourcePos (used for synthetic code).
    pub fn invalid() SourcePos {
        return .{
            .file_id = INVALID_FILE_ID,
            .line = 0,
            .column = 0,
        };
    }

    /// Returns true if this SourcePos is invalid.
    pub fn isValid(self: SourcePos) bool {
        return self.file_id != INVALID_FILE_ID;
    }
};

/// A span of source code, from start_pos (inclusive) to end_pos (exclusive on column).
pub const SourceSpan = struct {
    start: SourcePos,
    end: SourcePos,

    /// Creates a new SourceSpan from two positions.
    pub fn init(start: SourcePos, end: SourcePos) SourceSpan {
        return .{
            .start = start,
            .end = end,
        };
    }

    /// Creates a SourceSpan that spans a single character position.
    pub fn point(pos: SourcePos) SourceSpan {
        const end_pos = SourcePos.init(pos.file_id, pos.line, pos.column + 1);
        return .{
            .start = pos,
            .end = end_pos,
        };
    }

    /// Merges two spans to create a span that covers both.
    /// Useful when combining spans from multiple tokens/AST nodes.
    pub fn merge(self: SourceSpan, other: SourceSpan) SourceSpan {
        return .{
            .start = if (comparePos(self.start, other.start) == .lt) self.start else other.start,
            .end = if (comparePos(self.end, other.end) == .gt) self.end else other.end,
        };
    }

    /// Returns a human-readable representation like "Foo.hs:10:5-10:20".
    /// Caller must free the returned string with the provided allocator.
    pub fn pretty(self: SourceSpan, allocator: std.mem.Allocator, path_lookup: *const std.StringHashMap([]const u8)) ![]u8 {
        const start_path = path_lookup.get(@as(FileId, self.start.file_id)) orelse "<unknown>";
        if (self.start.file_id != self.end.file_id) {
            // Multi-file span (rare, but possible for synthetic errors)
            return std.fmt.allocPrint(allocator, "{s}:{d}:{d}-{d}:{d}", .{
                start_path,
                self.start.line,
                self.start.column,
                self.end.line,
                self.end.column,
            });
        } else if (self.start.line == self.end.line) {
            // Single line span
            return std.fmt.allocPrint(allocator, "{s}:{d}:{d}-{d}", .{
                start_path,
                self.start.line,
                self.start.column,
                self.end.column,
            });
        } else {
            // Multi-line span
            return std.fmt.allocPrint(allocator, "{s}:{d}:{d}-{d}:{d}", .{
                start_path,
                self.start.line,
                self.start.column,
                self.end.line,
                self.end.column,
            });
        }
    }

    /// Returns true if this span contains the given position.
    pub fn contains(self: SourceSpan, pos: SourcePos) bool {
        if (self.start.file_id != pos.file_id) return false;
        const afterOrAtStart = switch (comparePos(pos, self.start)) {
            .lt => false,
            .eq, .gt => true,
        };
        const beforeOrAtEnd = switch (comparePos(pos, self.end)) {
            .lt, .eq => true,
            .gt => false,
        };
        return afterOrAtStart and beforeOrAtEnd;
    }
};

/// Order relation for comparing SourcePos values.
const Order = enum { lt, eq, gt };

/// Compares two SourcePos values, ignoring file_id.
fn comparePos(a: SourcePos, b: SourcePos) Order {
    if (a.line < b.line) return .lt;
    if (a.line > b.line) return .gt;
    // Same line, compare columns
    if (a.column < b.column) return .lt;
    if (a.column > b.column) return .gt;
    return .eq;
}

test "SourcePos.init creates valid position" {
    const pos = SourcePos.init(1, 10, 5);
    try std.testing.expectEqual(@as(FileId, 1), pos.file_id);
    try std.testing.expectEqual(@as(u32, 10), pos.line);
    try std.testing.expectEqual(@as(u32, 5), pos.column);
}

test "SourcePos.init validates non-zero positions" {
    const valid = SourcePos.init(1, 1, 1);
    try std.testing.expect(valid.isValid());
}

test "SourcePos.isValid" {
    const valid = SourcePos.init(1, 10, 5);
    const invalid = SourcePos.invalid();
    try std.testing.expect(valid.isValid());
    try std.testing.expect(!invalid.isValid());
}

test "SourceSpan.point creates single-character span" {
    const pos = SourcePos.init(1, 10, 5);
    const span = SourceSpan.point(pos);
    try std.testing.expectEqual(@as(u32, 5), span.start.column);
    try std.testing.expectEqual(@as(u32, 6), span.end.column);
}

test "SourceSpan.merge combines spans correctly" {
    const pos1 = SourcePos.init(1, 5, 10);
    const pos2 = SourcePos.init(1, 5, 20);
    const span1 = SourceSpan.point(pos1);
    const span2 = SourceSpan.point(pos2);
    const merged = span1.merge(span2);
    try std.testing.expectEqual(@as(u32, 10), merged.start.column);
    try std.testing.expectEqual(@as(u32, 21), merged.end.column);
}

test "SourceSpan.merge with multi-line spans" {
    const span1 = SourceSpan.init(SourcePos.init(1, 5, 10), SourcePos.init(1, 5, 20));
    const span2 = SourceSpan.init(SourcePos.init(1, 10, 5), SourcePos.init(1, 10, 30));
    const merged = span1.merge(span2);
    try std.testing.expectEqual(@as(u32, 5), merged.start.line);
    try std.testing.expectEqual(@as(u32, 10), merged.end.line);
}

test "SourceSpan.pretty single line" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var path_lookup = std.StringHashMap([]const u8).init(allocator);
    try path_lookup.put(@as(FileId, 1), "test.hs");

    const span = SourceSpan.init(
        SourcePos.init(1, 10, 5),
        SourcePos.init(1, 10, 20),
    );
    const pretty = try span.pretty(allocator, &path_lookup);
    try std.testing.expectEqualStrings("test.hs:10:5-20", pretty);
}

test "SourceSpan.pretty multi line" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var path_lookup = std.StringHashMap([]const u8).init(allocator);
    try path_lookup.put(@as(FileId, 1), "test.hs");

    const span = SourceSpan.init(
        SourcePos.init(1, 10, 5),
        SourcePos.init(1, 15, 10),
    );
    const pretty = try span.pretty(allocator, &path_lookup);
    try std.testing.expectEqualStrings("test.hs:10:5-15:10", pretty);
}

test "SourceSpan.contains position" {
    const span = SourceSpan.init(
        SourcePos.init(1, 10, 5),
        SourcePos.init(1, 10, 20),
    );

    // Position inside span
    const inside = SourcePos.init(1, 10, 10);
    try std.testing.expect(span.contains(inside));

    // Position before span
    const before = SourcePos.init(1, 10, 4);
    try std.testing.expect(!span.contains(before));

    // Position after span
    const after = SourcePos.init(1, 10, 21);
    try std.testing.expect(!span.contains(after));

    // Position at start of span
    const at_start = SourcePos.init(1, 10, 5);
    try std.testing.expect(span.contains(at_start));

    // Position at end of span
    const at_end = SourcePos.init(1, 10, 20);
    try std.testing.expect(span.contains(at_end));

    // Position in different file
    const different_file = SourcePos.init(2, 10, 10);
    try std.testing.expect(!span.contains(different_file));
}
