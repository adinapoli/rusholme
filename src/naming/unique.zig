//! Name uniqueness infrastructure (GHC-style unique supply).
//!
//! Every binder in Core and GRIN gets a globally unique identifier, paired
//! with the original source name for debuggability. This follows the strategy
//! chosen in docs/decisions/004-naming-strategy.md.
//!
//! Usage:
//!
//!     var supply = UniqueSupply{};
//!     const x = supply.freshName("map");   // Name{ .base = "map", .unique = Unique{ .value = 0 } }
//!     const y = supply.freshName("map");   // Name{ .base = "map", .unique = Unique{ .value = 1 } }
//!     assert(!x.eql(y));                   // Different uniques, even though same base
//!

const std = @import("std");

/// A globally unique identifier for a binder.
///
/// Wraps a `u64` rather than aliasing it directly, so that `Unique` and
/// plain integers are not accidentally interchangeable.
pub const Unique = struct {
    value: u64,

    /// Equality: two uniques are equal iff their values are equal.
    pub fn eql(self: Unique, other: Unique) bool {
        return self.value == other.value;
    }

    /// Formats the unique as its raw integer value.
    pub fn format(self: Unique, w: *std.Io.Writer) std.Io.Writer.Error!void {
        try w.print("{d}", .{self.value});
    }
};

/// A monotonically increasing counter that produces fresh `Unique` values.
///
/// Intentionally simple — no splitting, no namespacing. Splitting can be
/// added later if parallel compilation requires independent supplies.
pub const UniqueSupply = struct {
    next: u64 = 0,

    /// Allocate a fresh unique.
    pub fn fresh(self: *UniqueSupply) Unique {
        const u = self.next;
        self.next += 1;
        return .{ .value = u };
    }

    /// Allocate a fresh `Name` with the given base string.
    ///
    /// Does not allocate — `base` is a borrowed slice whose lifetime must
    /// be managed by the caller (typically owned by the arena holding the
    /// AST or IR that contains this name).
    pub fn freshName(self: *UniqueSupply, base: []const u8) Name {
        return .{ .base = base, .unique = self.fresh() };
    }
};

/// A named binder: the original source identifier paired with a unique.
///
/// Equality compares only the unique — two `Name`s are the same variable
/// iff they share the same unique, regardless of their base strings.
/// This is the whole point of the unique supply: the base string is kept
/// purely for human-readable output.
pub const Name = struct {
    base: []const u8,
    unique: Unique,

    /// Equality: compares unique only.
    pub fn eql(self: Name, other: Name) bool {
        return self.unique.eql(other.unique);
    }

    /// Returns the original source identifier.
    pub fn baseName(self: Name) []const u8 {
        return self.base;
    }

    /// Formats as `base_unique` (e.g. `map_42`).
    pub fn format(self: Name, w: *std.Io.Writer) std.Io.Writer.Error!void {
        try w.print("{s}_{d}", .{ self.base, self.unique.value });
    }
};

// ── Tests ──────────────────────────────────────────────────────────────

test "Unique.eql: same value" {
    const a = Unique{ .value = 42 };
    const b = Unique{ .value = 42 };
    try std.testing.expect(a.eql(b));
}

test "Unique.eql: different values" {
    const a = Unique{ .value = 0 };
    const b = Unique{ .value = 1 };
    try std.testing.expect(!a.eql(b));
}

test "Unique.format: renders as integer" {
    const u = Unique{ .value = 99 };
    var buf: [32]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{u});
    try std.testing.expectEqualStrings("99", result);
}

test "UniqueSupply.fresh: monotonically increasing" {
    var supply = UniqueSupply{};
    const a = supply.fresh();
    const b = supply.fresh();
    const c = supply.fresh();
    try std.testing.expectEqual(@as(u64, 0), a.value);
    try std.testing.expectEqual(@as(u64, 1), b.value);
    try std.testing.expectEqual(@as(u64, 2), c.value);
}

test "UniqueSupply.fresh: successive calls return distinct uniques" {
    var supply = UniqueSupply{};
    const a = supply.fresh();
    const b = supply.fresh();
    try std.testing.expect(!a.eql(b));
}

test "UniqueSupply.freshName: produces correct Name" {
    var supply = UniqueSupply{};
    const name = supply.freshName("foo");
    try std.testing.expectEqualStrings("foo", name.base);
    try std.testing.expectEqual(@as(u64, 0), name.unique.value);
}

test "Name.eql: same unique, different base — equal" {
    const a = Name{ .base = "map", .unique = .{ .value = 7 } };
    const b = Name{ .base = "filter", .unique = .{ .value = 7 } };
    try std.testing.expect(a.eql(b));
}

test "Name.eql: different unique, same base — not equal" {
    const a = Name{ .base = "x", .unique = .{ .value = 0 } };
    const b = Name{ .base = "x", .unique = .{ .value = 1 } };
    try std.testing.expect(!a.eql(b));
}

test "Name.baseName: returns original identifier" {
    const name = Name{ .base = "foldr", .unique = .{ .value = 3 } };
    try std.testing.expectEqualStrings("foldr", name.baseName());
}

test "Name.format: renders as base_unique" {
    const name = Name{ .base = "map", .unique = .{ .value = 42 } };
    var buf: [32]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{name});
    try std.testing.expectEqualStrings("map_42", result);
}

test "Name.format: zero unique" {
    const name = Name{ .base = "x", .unique = .{ .value = 0 } };
    var buf: [32]u8 = undefined;
    const result = try std.fmt.bufPrint(&buf, "{f}", .{name});
    try std.testing.expectEqualStrings("x_0", result);
}
