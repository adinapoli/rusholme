-- e2e: arithmetic is a real `Num` type class, dictionary-dispatched (#879).
--
-- `(+)`, `(-)`, `(*)`, `negate`, `abs`, `signum` are methods of `class Num`
-- with `instance Num Int`, not monomorphic `Int` primitives. This exercises:
--   * an explicit `Num a =>` constraint (dictionary passing),
--   * a signature-less polymorphic arithmetic helper (constraint inferred and
--     threaded — see #875), and
--   * a local `where` helper using arithmetic at a concrete type.
module Main where

-- Explicit Num constraint.
double :: Num a => a -> a
double x = x + x

-- No signature: inferred `Num a => a -> a -> a`, used at Int.
sumSquares x y = x * x + y * y

-- Arithmetic in a where-bound helper.
quad :: Int -> Int
quad n = d (d n)
  where d x = x + x

-- No signature and no arguments: the monomorphism restriction keeps this
-- binding monomorphic and numeric defaulting resolves the otherwise-ambiguous
-- `Num a` to `Int` (Haskell 2010 §4.3.4; #879 uses Int until Integer lands).
answer = 6 * 7

main :: IO ()
main = do
  print (double (21 :: Int))
  print (sumSquares 3 4)
  print (negate (abs (5 - 9)))
  print (signum (negate 7))
  print (quad 5)
  print answer
