-- e2e: `instance Show Double` (#883).  A `Double` value is a boxed `Float`
-- node; `show`/`print` render it through the RTS (`rts_show_double`, Zig's
-- shortest-round-trip formatter) and the C-string→[Char] conversion.
--
-- Covers: integral (`5.0`), fractional (`3.14`), negative, a `where`-free
-- Double helper, arithmetic results, `signum`/`abs` at Double, and
-- `Show [Double]` (via the generic `Show [a]` instance).
--
-- Output is diffed against a fixed sidecar; every value here also matches
-- GHC's `show` (all lie in the plain-decimal range — GHC's scientific
-- thresholds are a documented follow-up, not exercised here).
module Main where

scale :: Double -> Double
scale x = x * 2.5

main :: IO ()
main = do
  print (5.0 :: Double)
  print (3.14 :: Double)
  print (negate 2.5 :: Double)
  print (scale 3.0)
  print (2.0 * 3.5)
  print (100.0 - 0.5)
  print (signum (negate 7.5) :: Double)
  print (abs (negate 1.25) :: Double)
  print [1.5, 2.5, 3.5]
