{-# LANGUAGE NoImplicitPrelude #-}
-- | Data.Char — character classification + case conversion.
--
-- Mirrors GHC's `base:Data.Char`.  Pure Haskell built on top of the
-- `intToChar`/`charToInt` primops re-exported through GHC.Base and
-- on the Int comparisons that the `Ord Char` instance is wired to.
--
-- Only the ASCII subset is supported — full Unicode classification
-- would need primops over Unicode general categories, which we
-- don't yet have.  Functions on non-ASCII code points behave as
-- if the character were a generic letter / non-letter on a
-- best-effort basis (e.g. `isAlpha` returns False, `toUpper`
-- returns the input unchanged).  Matches GHC's behaviour for ASCII
-- and diverges for the rest; tracked as future work.
module Data.Char
    ( ord, chr
    , isDigit, isHexDigit, isOctDigit
    , isUpper, isLower, isAlpha, isAlphaNum
    , isSpace
    , toUpper, toLower
    , digitToInt
    ) where

import GHC.Base

-- ── Code-point conversions ───────────────────────────────────────

ord :: Char -> Int
ord c = charToInt c

chr :: Int -> Char
chr n = intToChar n

-- ── ASCII classification ─────────────────────────────────────────

isDigit :: Char -> Bool
isDigit c = (c >= '0') && (c <= '9')

isOctDigit :: Char -> Bool
isOctDigit c = (c >= '0') && (c <= '7')

isHexDigit :: Char -> Bool
isHexDigit c =
    ((c >= '0') && (c <= '9')) ||
    ((c >= 'a') && (c <= 'f')) ||
    ((c >= 'A') && (c <= 'F'))

isUpper :: Char -> Bool
isUpper c = (c >= 'A') && (c <= 'Z')

isLower :: Char -> Bool
isLower c = (c >= 'a') && (c <= 'z')

isAlpha :: Char -> Bool
isAlpha c = isUpper c || isLower c

isAlphaNum :: Char -> Bool
isAlphaNum c = isAlpha c || isDigit c

-- ASCII whitespace: space, tab, newline, carriage return, form feed,
-- vertical tab.  Matches GHC's `isSpace` for the ASCII subset.
isSpace :: Char -> Bool
isSpace c =
    (c == ' ') ||
    (c == '\t') ||
    (c == '\n') ||
    (c == '\r') ||
    (c == '\f') ||
    (c == '\v')

-- ── Case conversion (ASCII only) ─────────────────────────────────

-- 'A'..'Z' lowercase to 'a'..'z' is +32 in ASCII.
toUpper :: Char -> Char
toUpper c = case isLower c of
    True  -> chr (ord c - 32)
    False -> c

toLower :: Char -> Char
toLower c = case isUpper c of
    True  -> chr (ord c + 32)
    False -> c

-- ── Digit conversion ─────────────────────────────────────────────

-- Converts a hex/oct/dec digit char to its integer value.  Behaviour
-- on non-digit input is `error` — matches GHC's `digitToInt`.
digitToInt :: Char -> Int
digitToInt c
    | isDigit c    = ord c - ord '0'
    | (c >= 'a') && (c <= 'f') = (ord c - ord 'a') + 10
    | (c >= 'A') && (c <= 'F') = (ord c - ord 'A') + 10
    | otherwise    = error "digitToInt: not a digit"
