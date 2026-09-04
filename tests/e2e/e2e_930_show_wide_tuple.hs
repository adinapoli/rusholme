module Main where

-- Regression test for #930: `Show` instances existed only for tuple widths 2
-- through 5, so `print` on a 6-tuple failed with
-- `no instance for Show (Int, Int, Int, Int, Int, Int)`.  GHC's `base`
-- provides instances through width 15 and so do we now.
--
-- The compiler side already handled every width up to
-- `Known.Con.max_tuple_arity` (#865); the gap was purely in the library.

main :: IO ()
main = do
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int), (11 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int), (11 :: Int), (12 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int), (11 :: Int), (12 :: Int), (13 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int), (11 :: Int), (12 :: Int), (13 :: Int), (14 :: Int))
  print ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), (10 :: Int), (11 :: Int), (12 :: Int), (13 :: Int), (14 :: Int), (15 :: Int))
  -- Heterogeneous components at width 15: every one of the fifteen
  -- dictionaries has to reach the right instance.
  print ('a', True, (1 :: Int), "s", LT, (2.5 :: Double), Just (2 :: Int), [(3 :: Int)], (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int), (8 :: Int), (9 :: Int), Nothing :: Maybe Int)
  -- A wide tuple nested inside the containers that delegate to it.
  print [((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int))]
  print (Just ((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int), (7 :: Int)))
  -- A wide tuple as a component of another tuple.
  print (((1 :: Int), (2 :: Int), (3 :: Int), (4 :: Int), (5 :: Int), (6 :: Int)), (7 :: Int))
