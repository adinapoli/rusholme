//! Structured error types for diagnostics.

const std = @import("std");
const span_mod = @import("span.zig");
const SourceSpan = span_mod.SourceSpan;

pub const Severity = enum {
    Error,
    Warning,
    Note,

    pub fn format(self: Severity, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        const s = switch (self) {
            .Error => "error",
            .Warning => "warning",
            .Note => "note",
        };
        try writer.writeAll(s);
    }
};

pub const Diagnostic = struct {
    severity: Severity,
    message: []const u8,
    span: SourceSpan,
    notes: []const Note = &.{},

    pub const Note = struct {
        message: []const u8,
        span: SourceSpan,
    };
};

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
        if (diag.severity == .Error) {
            self.had_errors = true;
        }
        try self.diagnostics.append(allocator, diag);
    }

    pub fn errorCount(self: DiagnosticBag) usize {
        var count: usize = 0;
        for (self.diagnostics.items) |d| {
            if (d.severity == .Error) count += 1;
        }
        return count;
    }
};
