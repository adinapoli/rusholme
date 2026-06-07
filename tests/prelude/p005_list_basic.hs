-- Prelude regression: map, filter, (++), head, tail, null, length,
-- String (#759).
--
-- NOTE: the predicate is user-defined because passing a *Prelude*
-- function as a HOF argument currently segfaults — tracked in #764
-- and pinned by p013_hof_prelude_arg.hs (xfail).
module Main where

dbl :: Int -> Int
dbl x = x * 2

myOdd :: Int -> Bool
myOdd n = mod n 2 /= 0

xs :: [Int]
xs = [1, 2, 3]

greeting :: String
greeting = "hi"

main :: IO ()
main = do
    print (map dbl xs)
    print (filter myOdd xs)
    print ([1, 2] ++ [3])
    print (head xs)
    print (tail xs)
    print (null xs)
    print (null (tail [1]))
    print (length xs)
    putStrLn greeting
