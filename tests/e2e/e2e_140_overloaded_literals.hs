-- e2e: overloaded integer literals + numeric defaulting (#140).
--
-- The renamer rewrites each integer literal `n` into `fromInteger n`, so an
-- integer literal has type `Num a => a` rather than a monomorphic `Int`.
-- This exercises:
--   * the same literal shape used at `Int` and at `Double`,
--   * `fromInteger` selecting the `Int` identity vs the `intToDouble` widen,
--   * Haskell 2010 §4.3.4 numeric defaulting of an otherwise-ambiguous
--     `let`-binding to `Int`,
--   * a polymorphic `Num a =>` helper fed literals at two instance types.
--
-- Double results are funnelled through `doubleToInt` so the expected output is
-- exact integers (Show Double parity is covered by #883).
module Main where

-- Integer literals `2` used at Double through the signature.
tau :: Double
tau = 2 + 2

-- Integer literals used at Int.
n :: Int
n = 10 * 10

-- Polymorphic helper; the literals inside are `Num a =>`.
addFour :: Num a => a -> a
addFour x = x + 2 + 2

-- Ambiguous `let`: `y :: Num a => a`, resolved by defaulting to Int.
defaulted :: Int
defaulted = let y = 3 * 7 in y + 1

-- Explicit `fromInteger` at Double.
converted :: Double
converted = fromInteger 42

main :: IO ()
main = do
  print (doubleToInt tau)
  print n
  print (addFour (5 :: Int))
  print (doubleToInt (addFour 5.0))
  print defaulted
  print (doubleToInt converted)
