//! Well-known unique IDs for Prelude built-ins.
//!
//! This file defines stable `Unique` values for standard Haskell types,
//! functions, and constructors. By assigning fixed IDs in a reserved range
//! (0-999), we ensure that these entities have the same identity across
//! different compilation units and compiler stages.

const unique_mod = @import("unique.zig");
const Unique = unique_mod.Unique;
const Name = unique_mod.Name;

/// Well-known names and their stable uniques.
pub const Fn = struct {
    pub const putStrLn = name("putStrLn", 0);
    pub const putStr = name("putStr", 1);
    pub const print = name("print", 2);
    pub const getLine = name("getLine", 3);
    pub const @"return" = name("return", 4);
    pub const @"error" = name("error", 5);
    pub const @"undefined" = name("undefined", 6);
    pub const negate = name("negate", 7);
    pub const abs = name("abs", 8);
    pub const signum = name("signum", 9);
    pub const fromInteger = name("fromInteger", 10);
    pub const head = name("head", 11);
    pub const tail = name("tail", 12);
    pub const null_ = name("null", 13);
    pub const length = name("length", 14);
    pub const map = name("map", 15);
    pub const filter = name("filter", 16);
    pub const foldl = name("foldl", 17);
    pub const foldr = name("foldr", 18);
    pub const concat = name("concat", 19);
    pub const zip = name("zip", 20);
    pub const unzip = name("unzip", 21);
    pub const show = name("show", 22);
    pub const read = name("read", 23);
    pub const otherwise = name("otherwise", 24);
    // Monad operators for do-notation desugaring (issue #464)
    pub const bind = name(">>=", 25);
    pub const then = name(">>", 26);
};

pub const Type = struct {
    pub const Int = name("Int", 100);
    pub const Integer = name("Integer", 101);
    pub const Double = name("Double", 102);
    pub const Float = name("Float", 103);
    pub const Bool = name("Bool", 104);
    pub const Char = name("Char", 105);
    pub const String = name("String", 106);
    pub const IO = name("IO", 107);
    pub const Maybe = name("Maybe", 108);
    pub const Either = name("Either", 109);
    pub const List = name("[]", 110);
    pub const Unit = name("()", 111);
};

/// Well-known type class names (IDs 300–399).
pub const Class = struct {
    pub const Eq = name("Eq", 300);
    pub const Ord = name("Ord", 301);
    pub const Show = name("Show", 302);
    pub const Read = name("Read", 303);
    pub const Num = name("Num", 304);
    pub const Enum = name("Enum", 305);
    pub const Bounded = name("Bounded", 306);
    pub const Monad = name("Monad", 307);
    pub const Functor = name("Functor", 308);
    pub const Applicative = name("Applicative", 309);
};

pub const Con = struct {
    pub const True = name("True", 200);
    pub const False = name("False", 201);
    pub const Nothing = name("Nothing", 202);
    pub const Just = name("Just", 203);
    pub const Left = name("Left", 204);
    pub const Right = name("Right", 205);
    pub const Unit = name("()", 206);
    pub const Nil = name("[]", 207);
    pub const Cons = name("(:)", 208);
    pub const Tuple2 = name("(,)", 209);
    pub const Tuple3 = name("(,,)", 210);
    pub const Tuple4 = name("(,,,)", 211);
    pub const Tuple5 = name("(,,,,)", 212);
    pub const Tuple6 = name("(,,,,,)", 213);
    pub const Tuple7 = name("(,,,,,,)", 214);

    /// Highest tuple arity wired end-to-end (constructor, scheme, GRIN,
    /// match-check). Matches GHC's boxed-tuple limit. Arities above this
    /// are not yet supported.
    pub const max_tuple_arity: usize = 62;

    /// Comptime table of tuple constructor name strings indexed by arity:
    /// index 2 → "(,)", index 3 → "(,,)", … up to `max_tuple_arity`.
    /// Indices 0 and 1 are unused (arity 0 is the unit `()` constructor;
    /// arity 1 is a parenthesised expression, not a tuple).
    const tuple_name_table: [max_tuple_arity + 1][]const u8 = blk: {
        @setEvalBranchQuota(10_000);
        var table: [max_tuple_arity + 1][]const u8 = undefined;
        for (&table, 0..) |*slot, arity| {
            if (arity < 2) {
                slot.* = "";
            } else {
                var buf: [arity + 1]u8 = undefined;
                buf[0] = '(';
                for (1..arity) |i| buf[i] = ',';
                buf[arity] = ')';
                const frozen = buf;
                slot.* = &frozen;
            }
        }
        break :blk table;
    };

    /// Return the well-known tuple constructor `Name` for the given arity,
    /// or `null` if the arity is outside the supported range (2..=62).
    /// Arity 1 is a parenthesised expression, not a tuple, and arity 0 is
    /// the `Unit` constructor — neither is handled here.
    ///
    /// Uniques are laid out contiguously after `Cons` (207), so arity `n`
    /// maps to `207 + n` (arity 2 → 209, matching `Tuple2`, … arity 62 →
    /// 269).  The range 215..269 is otherwise unused (classes start at 300).
    pub fn tuple(arity: usize) ?Name {
        if (arity < 2 or arity > max_tuple_arity) return null;
        return .{
            .base = tuple_name_table[arity],
            .unique = .{ .value = 207 + arity },
        };
    }

    /// Comptime table of instance-dictionary head names for tuple type
    /// constructors, indexed by arity: 2 → "Tuple2", 3 → "Tuple3", …
    ///
    /// Instance dictionaries are keyed by a head-name string, and the name is
    /// derived along two independent paths: from the surface AST at the
    /// declaration site and from the inferred `HType` at each use site.  Both
    /// must agree or the reference dangles until link time.  The names are
    /// arity-qualified so that `Show (a, b)` and `Show (a, b, c)` occupy
    /// distinct keys rather than colliding on a single "Tuple" (#927).
    const tuple_head_name_table: [max_tuple_arity + 1][]const u8 = blk: {
        @setEvalBranchQuota(10_000);
        var table: [max_tuple_arity + 1][]const u8 = undefined;
        const prefix = "Tuple";
        for (&table, 0..) |*slot, arity| {
            if (arity < 2) {
                slot.* = "";
                continue;
            }
            // Decimal digits of `arity`, most significant first.  Hand-rolled
            // because this file deliberately imports no std (see the header).
            const digits = if (arity < 10) 1 else 2;
            var buf: [prefix.len + digits]u8 = undefined;
            for (prefix, 0..) |c, i| buf[i] = c;
            var rest = arity;
            var i = digits;
            while (i > 0) : (i -= 1) {
                buf[prefix.len + i - 1] = '0' + @as(u8, @intCast(rest % 10));
                rest /= 10;
            }
            const frozen = buf;
            slot.* = &frozen;
        }
        break :blk table;
    };

    /// Instance-dictionary head name for a tuple of the given arity, or
    /// `null` if the arity is outside the supported range (2..=62).
    pub fn tupleHeadName(arity: usize) ?[]const u8 {
        if (arity < 2 or arity > max_tuple_arity) return null;
        return tuple_head_name_table[arity];
    }

    /// Arity of a tuple *constructor* name, or `null` if `base` is not one.
    /// The inverse of `tuple_name_table`: `"(,)"` → 2, `"(,,)"` → 3, …
    ///
    /// Recognises exactly `(` followed by `n - 1` commas and `)`, so it cannot
    /// be fooled by an unrelated operator name.
    pub fn tupleArity(base: []const u8) ?usize {
        if (base.len < 3) return null;
        if (base[0] != '(' or base[base.len - 1] != ')') return null;
        for (base[1 .. base.len - 1]) |c| {
            if (c != ',') return null;
        }
        const arity = base.len - 1;
        if (arity > max_tuple_arity) return null;
        return arity;
    }

    /// Instance-dictionary head name for a tuple *constructor* name, or `null`
    /// if `base` is not one: `"(,)"` → "Tuple2", `"(,,)"` → "Tuple3", …
    pub fn tupleHeadNameForCon(base: []const u8) ?[]const u8 {
        return tupleHeadName(tupleArity(base) orelse return null);
    }
};

/// The start of the non-reserved unique ID range.
/// Keep this in sync with src/naming/unique.zig.
pub const reserved_range_end: u64 = 1000;

fn name(base: []const u8, value: u64) Name {
    return .{
        .base = base,
        .unique = .{ .value = value },
    };
}

// ── Tests ──────────────────────────────────────────────────────────────

const testing = @import("std").testing;

test "Con.tupleArity: recognises tuple constructor names" {
    try testing.expectEqual(@as(?usize, 2), Con.tupleArity("(,)"));
    try testing.expectEqual(@as(?usize, 3), Con.tupleArity("(,,)"));
    try testing.expectEqual(@as(?usize, 10), Con.tupleArity("(,,,,,,,,,)"));
    try testing.expectEqual(Con.max_tuple_arity, Con.tupleArity(Con.tuple(Con.max_tuple_arity).?.base).?);
}

test "Con.tupleArity: rejects names that are not tuple constructors" {
    // `()` is the unit constructor and `(a)` is a parenthesised type; neither
    // is a tuple.  The scan must also not be fooled by other operator names.
    try testing.expectEqual(@as(?usize, null), Con.tupleArity("()"));
    try testing.expectEqual(@as(?usize, null), Con.tupleArity("[]"));
    try testing.expectEqual(@as(?usize, null), Con.tupleArity("(:)"));
    try testing.expectEqual(@as(?usize, null), Con.tupleArity("(+)"));
    try testing.expectEqual(@as(?usize, null), Con.tupleArity("(,a)"));
    try testing.expectEqual(@as(?usize, null), Con.tupleArity("Int"));
    try testing.expectEqual(@as(?usize, null), Con.tupleArity(""));
}

test "Con.tupleHeadName: arity-qualified, and agrees with tupleHeadNameForCon" {
    // The two derivation paths for an instance-dictionary head name must
    // produce identical strings or the reference dangles until link time
    // (#927).  This pins both spellings against each other for every
    // supported arity.
    try testing.expectEqualStrings("Tuple2", Con.tupleHeadName(2).?);
    try testing.expectEqualStrings("Tuple3", Con.tupleHeadName(3).?);
    try testing.expectEqualStrings("Tuple10", Con.tupleHeadName(10).?);

    var arity: usize = 2;
    while (arity <= Con.max_tuple_arity) : (arity += 1) {
        const con_name = Con.tuple(arity).?.base;
        try testing.expectEqualStrings(
            Con.tupleHeadName(arity).?,
            Con.tupleHeadNameForCon(con_name).?,
        );
    }

    // Out-of-range arities have no head name rather than a wrong one.
    try testing.expectEqual(@as(?[]const u8, null), Con.tupleHeadName(1));
    try testing.expectEqual(@as(?[]const u8, null), Con.tupleHeadName(Con.max_tuple_arity + 1));
}
