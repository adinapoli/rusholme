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
