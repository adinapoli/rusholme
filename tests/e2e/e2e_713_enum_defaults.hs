module Main where

-- Test: Enum class default methods (issue #713).
--
-- The Enum class provides default implementations of enumFrom, enumFromTo,
-- enumFromThen and enumFromThenTo, defined (per the Haskell 2010 Report) by
-- mapping toEnum over the corresponding Int-domain index sequence.  Because
-- the bound passed to toEnum is always an in-range index, enumFromTo and
-- enumFromThenTo are TOTAL for finite enums and never crash with
-- "toEnum: out of range" — this exercises exactly the boundary cases that
-- previously truncated and crashed (see #745).
--
-- `Suit` defines ONLY the four primitive methods (succ, pred, toEnum,
-- fromEnum) and gets the ranged enumerations for free from the defaults.
data Suit = Clubs | Diamonds | Hearts | Spades

instance Show Suit where
  show Clubs    = "Clubs"
  show Diamonds = "Diamonds"
  show Hearts   = "Hearts"
  show Spades   = "Spades"

instance Enum Suit where
  succ Clubs    = Diamonds
  succ Diamonds = Hearts
  succ Hearts   = Spades
  succ Spades   = error "succ: Spades is maxBound for Suit"
  pred Diamonds = Clubs
  pred Hearts   = Diamonds
  pred Spades   = Hearts
  pred Clubs    = error "pred: Clubs is minBound for Suit"
  toEnum 0 = Clubs
  toEnum 1 = Diamonds
  toEnum 2 = Hearts
  toEnum 3 = Spades
  toEnum _ = error "toEnum: out of range for Suit"
  fromEnum Clubs    = 0
  fromEnum Diamonds = 1
  fromEnum Hearts   = 2
  fromEnum Spades   = 3

main :: IO ()
main = do
  -- enumFromTo from the class default, on the user instance.
  putStrLn (show (enumFromTo Clubs Spades))
  putStrLn (show (enumFromTo Diamonds Hearts))
  putStrLn (show (enumFromTo Spades Clubs))
  -- enumFromTo on the built-in Prelude instances, which now also rely on the
  -- shared class defaults rather than per-instance copies.
  putStrLn (show (enumFromTo False True))
  putStrLn (show (enumFromTo LT GT))
  putStrLn (show (enumFromTo 'a' 'e'))
  -- Boundary cases: enumFromThenTo where the step reaches maxBound exactly.
  -- These used to force toEnum one past the bound, truncating the last
  -- element and crashing.  They must now be total and GHC-correct.
  putStrLn (show (enumFromThenTo False True True))
  putStrLn (show (enumFromThenTo LT EQ GT))
  -- enumFromThenTo on the user instance, reaching maxBound (Spades).
  putStrLn (show (enumFromThenTo Clubs Diamonds Spades))
  -- enumFrom / enumFromThen on bounded instances must terminate at maxBound.
  putStrLn (show (enumFrom LT))                 -- [LT ..]
  putStrLn (show (enumFrom False))              -- [False ..]
  putStrLn (show (take 2 (enumFromThen False True)))
  -- Whole-enum enumeration of Bool.  GHC writes this as
  -- `[minBound .. maxBound] :: [Bool]`; here we spell the bounds as literals
  -- because `show (minBound :: Bool)` / `maxBound :: Bool` hit a pre-existing
  -- Bounded-codegen panic unrelated to the Enum defaults (the nullary-method
  -- selector asserts on n_fields).  This row exercises the very same total
  -- enumFromTo default path and asserts the same `[False,True]` result.
  putStrLn (show (enumFromTo False True))
