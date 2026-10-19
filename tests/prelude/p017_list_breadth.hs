-- Prelude regression: the everyday list functions from #970 reached through
-- the implicit Prelude (no explicit `import Data.List`), which is how most
-- code sees them.
module Main where

evens :: [Int]
evens = [2, 4, 6]

isBig :: Int -> Bool
isBig n = n > 3

main :: IO ()
main = do
    print (last evens)
    print (init evens)
    print (elem (4 :: Int) evens)
    print (notElem (5 :: Int) evens)
    print (lookup 'b' [('a', (1 :: Int)), ('b', (2 :: Int))])
    print (zip evens "xyz")
    print (unzip (zip evens "xyz"))
    print (zipWith (\a b -> a + b) evens [(1 :: Int), 1, 1])
    print (takeWhile isBig evens)
    print (dropWhile isBig evens)
    print (span isBig evens)
    print (splitAt 1 evens)
    print (any isBig evens)
    print (all isBig evens)
    print (and [True, True])
    print (or [False, False])
    print (concatMap (\n -> [n]) evens)
    print (scanl (\a b -> a + b) 0 evens)
    print (foldl1 (\a b -> a + b) evens)
    print (foldr1 (\a b -> a + b) evens)
    print (take 4 (iterate (\n -> n + (1 :: Int)) 0))
    print (take 2 (repeat 'q'))
    print (take 5 (cycle "ab"))
    print (words "one two")
    print (unwords ["one", "two"])
    print (lines "one\ntwo")
    print (unlines ["one", "two"])
    print (until isBig (\n -> n + (1 :: Int)) 0)
    print (gcd (12 :: Int) 18)
    print (lcm (4 :: Int) 6)
    -- Regression (#970): |x * y| overflows rhc's 63-bit Int while the
    -- result fits, so `lcm` must divide by `gcd` before multiplying.
    print (lcm (4000000000000000000 :: Int) 2)
    print (lcm (2 :: Int) 4000000000000000000)
    print (lcm (-4 :: Int) 6)
    -- Boundary cases: the singleton list is where an off-by-one in
    -- `last`/`init`/`foldr1`/`scanr1` would hide, and a `break` that
    -- consumes its matching element would show up on a mid-list split.
    print (last [7])
    print (init [7])
    print (foldl1 (\a b -> a + b) [7])
    print (foldr1 (\a b -> a + b) [7])
    print (scanl1 (\a b -> a + b) [7])
    print (scanr1 (\a b -> a + b) [7])
    print (scanr (\a b -> a + b) 0 evens)
    print (break isBig evens)
    print (break (\n -> n > 8) evens)
    print (break (\n -> n < 3) evens)
    print (zip3 evens "xy" [True, False, True])
    print (zipWith3 (\a b c -> a + b + c) evens [1, 2, 3] [10, 20, 30])
    print (unzip3 (zip3 evens "xy" [True, False, True]))
    print (lcm (-6 :: Int) (-4))
    print (lcm (6 :: Int) (-4))
