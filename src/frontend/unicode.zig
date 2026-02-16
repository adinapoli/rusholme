//! Unicode character classification for Haskell 2010.
//!
//! This module provides character classification functions as specified in
//! Haskell 2010 Report Section 2.2.
//!
//! For full Unicode support, consider using a C library like ICU or
//! unicode-utils via Zig's C interop.

const std = @import("std");

/// Check if a Unicode code point is a lowercase letter (uniSmall in Haskell).
/// Corresponds to Unicode category Ll.
pub fn isUniSmall(c: u21) bool {
    // ASCII lowercase a-z
    if (c >= 'a' and c <= 'z') return true;

    // TODO: Add full Unicode Ll category support
    // For now, this is a simplified version that handles only ASCII.
    // In production, this would use Unicode character database lookup.
    return false;
}

/// Check if a Unicode code point is an uppercase or titlecase letter (uniLarge in Haskell).
/// Corresponds to Unicode categories Lu (uppercase) and Lt (titlecase).
pub fn isUniLarge(c: u21) bool {
    // ASCII uppercase A-Z
    if (c >= 'A' and c <= 'Z') return true;

    // TODO: Add full Unicode Lu, Lt category support
    return false;
}

/// Check if a Unicode code point is a Unicode letter (both small and large).
pub fn isUniLetter(c: u21) bool {
    return isUniSmall(c) or isUniLarge(c);
}

/// Check if a Unicode code point is a symbol or punctuation (uniSymbol in Haskell).
/// Corresponds to Unicode categories Sm, Sc, Sk, So.
pub fn isUniSymbol(c: u21) bool {
    // ASCII symbols: !#$%&*+./<=>?@\^|~- (excluding :, ', ", and specials)
    return switch (c) {
        '!', '#', '$', '%', '&', '*', '+', '.', '/', '<', '=', '>', '?', '@', '\\', '^', '|', '~', '-' => true,
        else => false,
    };
}

/// Check if a Unicode code point is a "special" character for Haskell.
/// These include isUniSymbol plus additional characters used in operators.
pub fn isUniSpecial(c: u21) bool {
    return isUniSymbol(c) or switch (c) {
        ':', '_' => true,
        else => false,
    };
}

/// Check if a Unicode code point is a decimal digit (uniDigit in Haskell).
/// Corresponds to Unicode category Nd.
pub fn isUniDigit(c: u21) bool {
    // ASCII digits 0-9
    return c >= '0' and c <= '9';

    // TODO: Add full Unicode Nd category support (Arabic-Indic, etc.)
}

/// Check if a Unicode code point is whitespace (uniWhite in Haskell).
/// Corresponds to Unicode category Zs plus ASCII control whitespace.
pub fn isUniWhite(c: u21) bool {
    // ASCII whitespace
    return switch (c) {
        ' ', '\t', '\n', '\r', '\x0C' => true, // space, tab, newline, CR, form feed
        '\x0B' => true, // vertical tab
        0x00A0 => true, // NO-BREAK SPACE (Zs)
        0x1680 => true, // OGHAM SPACE MARK (Zs)
        0x2000...0x200A => true, // EN QUAD...HAIR SPACE (Zs)
        0x2028 => true, // LINE SEPARATOR (Zl)
        0x2029 => true, // PARAGRAPH SEPARATOR (Zp)
        0x202F => true, // NARROW NO-BREAK SPACE (Zs)
        0x205F => true, // MEDIUM MATHEMATICAL SPACE (Zs)
        0x3000 => true, // IDEOGRAPHIC SPACE (Zs)
        else => false,
    };
}

/// Check if a character can be the first character of an identifier.
/// Haskell identifiers must start with a letter or underscore.
pub fn isIdStart(c: u21) bool {
    return isUniLetter(c) or c == '_';
}

/// Check if a character can be in the middle of an identifier.
/// Haskell identifiers can contain letters, digits, and apostrophes.
pub fn isIdContinue(c: u21) bool {
    return isIdStart(c) or isUniDigit(c) or c == '\'';
}

test "isUniSmall - ASCII lowercase" {
    try std.testing.expect(isUniSmall('a'));
    try std.testing.expect(isUniSmall('z'));
    try std.testing.expect(!isUniSmall('A'));
    try std.testing.expect(!isUniSmall('1'));
    try std.testing.expect(!isUniSmall('@'));
}

test "isUniLarge - ASCII uppercase" {
    try std.testing.expect(isUniLarge('A'));
    try std.testing.expect(isUniLarge('Z'));
    try std.testing.expect(!isUniLarge('a'));
    try std.testing.expect(!isUniLarge('1'));
}

test "isUniLetter - ASCII letters" {
    try std.testing.expect(isUniLetter('a'));
    try std.testing.expect(isUniLetter('A'));
    try std.testing.expect(!isUniLetter('1'));
    try std.testing.expect(!isUniLetter('@'));
}

test "isUniSymbol - ASCII symbols" {
    try std.testing.expect(isUniSymbol('+'));
    try std.testing.expect(isUniSymbol('*'));
    try std.testing.expect(isUniSymbol('!'));
    try std.testing.expect(isUniSymbol('|'));
    try std.testing.expect(!isUniSymbol('a'));
    try std.testing.expect(!isUniSymbol('1'));
}

test "isUniSpecial - symbols plus specials" {
    try std.testing.expect(isUniSpecial('+'));
    try std.testing.expect(isUniSpecial('_'));
    try std.testing.expect(isUniSpecial(':'));
    try std.testing.expect(!isUniSpecial('a'));
}

test "isUniDigit - ASCII digits" {
    try std.testing.expect(isUniDigit('0'));
    try std.testing.expect(isUniDigit('9'));
    try std.testing.expect(!isUniDigit('a'));
    try std.testing.expect(!isUniDigit('!'));
}

test "isUniWhite - whitespace" {
    try std.testing.expect(isUniWhite(' '));
    try std.testing.expect(isUniWhite('\t'));
    try std.testing.expect(isUniWhite('\n'));
    try std.testing.expect(isUniWhite('\r'));
    try std.testing.expect(isUniWhite(0x00A0)); // NO-BREAK SPACE
    try std.testing.expect(isUniWhite(0x2000)); // EN QUAD
    try std.testing.expect(!isUniWhite('a'));
    try std.testing.expect(!isUniWhite('1'));
}

test "isIdStart - identifier first character" {
    try std.testing.expect(isIdStart('a'));
    try std.testing.expect(isIdStart('A'));
    try std.testing.expect(isIdStart('_'));
    try std.testing.expect(!isIdStart('1'));
    try std.testing.expect(!isIdStart('+'));
}

test "isIdContinue - identifier continuation" {
    try std.testing.expect(isIdContinue('a'));
    try std.testing.expect(isIdContinue('_'));
    try std.testing.expect(isIdContinue('1'));
    try std.testing.expect(isIdContinue('\''));
    try std.testing.expect(!isIdContinue('+'));
    try std.testing.expect(!isIdContinue('!'));
}
