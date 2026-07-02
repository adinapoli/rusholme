-- e2e: `Fractional` class + `instance Fractional Double` (#887).
-- Floating division `(/)` and `recip` over the `div_Double` primop
-- (LLVM `fdiv`, wired in #880).
--
-- Covers: exact divisions, a non-terminating decimal (shortest
-- round-trip rendering, matches GHC), `recip`, a signature-carrying
-- Double helper, `(/)` mixed with `Num Double` arithmetic, and infixl 7
-- fixity (`a / b / c` groups left, `a + b / c` divides first).
--
-- Output is diffed against a fixed sidecar; every line also matches
-- GHC's output for the same program.
module Main where

half :: Double -> Double
half x = x / 2.0

main :: IO ()
main = do
  print (7.0 / 2.0)
  print (1.0 / 4.0)
  print (1.0 / 3.0)
  print (negate 9.0 / 2.0)
  print (recip 2.0 :: Double)
  print (recip 0.25 :: Double)
  print (half 11.0)
  print (half (3.0 * 5.0))
  print (100.0 / 10.0 / 2.0)
  print (1.0 + 9.0 / 2.0)
