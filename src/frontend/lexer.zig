//! Lexical analysis for Haskell source code.

const std = @import("std");

pub const Token = union(enum) {
    // Placeholder token types - to be expanded
    kw_module,
    kw_import,
    kw_data,
    kw_case,
    kw_of,
    kw_let,
    kw_in,
    kw_where,
    kw_if,
    kw_then,
    kw_else,
    Identifier: []const u8,

    pub fn format(self: Token, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        switch (self) {
            .kw_module => try writer.writeAll("kw_module"),
            .kw_import => try writer.writeAll("kw_import"),
            .kw_data => try writer.writeAll("kw_data"),
            .kw_case => try writer.writeAll("kw_case"),
            .kw_of => try writer.writeAll("kw_of"),
            .kw_let => try writer.writeAll("kw_let"),
            .kw_in => try writer.writeAll("kw_in"),
            .kw_where => try writer.writeAll("kw_where"),
            .kw_if => try writer.writeAll("kw_if"),
            .kw_then => try writer.writeAll("kw_then"),
            .kw_else => try writer.writeAll("kw_else"),
            .Identifier => |s| try writer.print("Identifier({s})", .{s}),
        }
    }
};
