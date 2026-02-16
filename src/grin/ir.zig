//! GRIN IR types (Modern GRIN dialect).

const std = @import("std");

pub const Expr = union(enum) {
    Unit: void,
    Const: struct { value: i64, type: Type },
    App: []const u8, // Function name
    Store: []const u8, // Node name
    Fetch: []const u8, // Variable name
    Update: []const u8, // Node name
    Case: struct { scrutinee: []const u8, alts: []const Alt },

    pub const Alt = union(enum) {
        Ctr: struct { name: []const u8, fields: []const []const u8, body: *const Expr },
        Default: *const Expr,
    };
};

pub const Type = union(enum) {
    Ptr: Box,
    Ctr: struct { tag: u32, fields: []const Type },
    Fn: []const Type,
    Scalar: enum { I64, F64, Bool },
};

pub const Box = enum {
    Heap,
    Stack,
};

test "GRIN IR: Type enum variants compile" {
    const scalar = Type{ .Scalar = .I64 };
    try std.testing.expectEqual(@intFromEnum(Type.Scalar), @intFromEnum(scalar));

    const box = Box.Heap;
    try std.testing.expectEqual(Box.Heap, box);

    const expr = Expr{ .Unit = {} };
    _ = expr;
}

test "GRIN IR: Const expression" {
    const expr = Expr{
        .Const = .{ .value = 42, .type = .{ .Scalar = .I64 } },
    };
    try std.testing.expectEqual(@as(i64, 42), expr.Const.value);
    try std.testing.expectEqual(@intFromEnum(Type.Scalar), @intFromEnum(expr.Const.type));
}
