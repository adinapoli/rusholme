-- Prelude numeric boundary: `gcd 0 0` is 0 in GHC's `base`, which is the
-- reference the suite is diffed against.  (The Report's Prelude listing
-- makes it an error, but GHC does not implement that sentence; matching
-- GHC keeps the whole #970 batch byte-comparable.)  `lcm` is 0 whenever
-- either argument is 0.
module Main where

main :: IO ()
main = do
    print (gcd (0 :: Int) 0)
    print (lcm (0 :: Int) 0)
    print (gcd (0 :: Int) 5)
    print (gcd (5 :: Int) 0)
    print (lcm (0 :: Int) 5)
    print (lcm (5 :: Int) 0)
