module ListPatterns where

-- This is a *pattern-matching* golden test; the element type is `Bool`
-- deliberately.  A bare integer literal would now desugar to `fromInteger`
-- (#140), which needs the `Num` class / `instance Num Int` in scope — and the
-- golden pipeline runs against the minimal synthetic env (`initBuiltins`),
-- which has no class environment.  `Bool` keeps the list-pattern shapes
-- identical while the default branch uses `False` instead of `0`.
-- Numeric-literal support in the golden harness is tracked in #911.

-- Empty list pattern
isEmpty :: [Bool] -> Bool
isEmpty [] = True
isEmpty _  = False

-- Exact two-element list pattern: [a, b]
firstOfTwo :: [Bool] -> Bool
firstOfTwo [a, b] = a
firstOfTwo _      = False

-- Single-element list pattern: [x]
singleton :: [Bool] -> Bool
singleton [x] = x
singleton _   = False
