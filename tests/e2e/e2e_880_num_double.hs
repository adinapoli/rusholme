-- e2e: `Num`/`Eq`/`Ord Double`, dictionary-dispatched over boxed Float
-- heap nodes (#880).  A Double value cannot be a tagged immediate, so every
-- Double is a boxed `Float` node; arithmetic devirtualises to the `Double`
-- primops (fadd/fsub/fmul/fdiv/fneg/fcmp).  This exercises:
--   * a polymorphic `Num a =>` helper instantiated at Double (dictionary
--     passing — the same machinery #875/#879 built for Int),
--   * a signature-less inferred `Num a => a -> a -> a` used at Double,
--   * a `where`-bound Double helper,
--   * `negate`/`abs`/`signum`, `Ord` comparisons, and `Int`↔`Double`
--     conversion primops.
--
-- Results are funneled through `doubleToInt` so the expected output is exact
-- integers (Show Double is a separate follow-up).
module Main where

-- Explicit Num constraint, instantiated at Double below.
double :: Num a => a -> a
double x = x + x

-- No signature: inferred `Num a => a -> a -> a`, used at Double.
sumSquares x y = x * x + y * y

-- Double arithmetic in a where-bound helper.
area :: Double -> Double
area r = p * r * r
  where p = 3.0

main :: IO ()
main = do
  print (doubleToInt (double 2.5))
  print (doubleToInt (sumSquares 3.0 4.0))
  print (doubleToInt (negate (abs (2.0 - 5.0))))
  print (doubleToInt (signum 7.5))
  print (doubleToInt (area 10.0))
  print (3.0 < 4.0)
  print (5.5 == 5.5)
  print (9.0 <= 2.0)
  print (doubleToInt (intToDouble 42))
