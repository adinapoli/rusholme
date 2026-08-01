module Main where

-- Regression test for #927: there was no `Show` instance for any tuple, not
-- even pairs, so `print (x, y)` did not compile.
--
-- Two things were needed. The instance dictionary head name is derived twice
-- along independent paths — from the surface AST at the declaration site and
-- from the inferred type at each use site — and the two disagreed for tuples
-- ("Tuple" vs "(,)"), so even a hand-written `instance Show (a, b)` failed at
-- link time with `undefined reference to dict$Show$(,)`. The names are now
-- arity-qualified ("Tuple2", "Tuple3", …) on both paths, which also keeps
-- distinct tuple widths in distinct dictionary slots.
--
-- Note: no component here is a String. `show` on a `[Char]` still renders as
-- a character list rather than a quoted string, which is a separate gap.

main :: IO ()
main = do
  print ((1 :: Int), (2 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int))
  print ('a', True, (4 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int))
  -- Nesting exercises the same instance recursively, and a tuple inside a
  -- list exercises it under `Show [a]`.
  print ((1 :: Int), ((2 :: Int), (3 :: Int)))
  print [((1 :: Int), (2 :: Int)), ((3 :: Int), (4 :: Int))]
  print (Just ((1 :: Int), (2 :: Int)))
  -- Distinct widths must not collide on a shared dictionary.
  putStrLn (show ((1 :: Int), (2 :: Int)) ++ " " ++ show ((1 :: Int), (2 :: Int), (3 :: Int)))
