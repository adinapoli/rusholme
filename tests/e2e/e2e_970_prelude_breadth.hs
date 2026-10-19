module Main where

-- Regression test for #970: 31 everyday Prelude/Data.List functions were
-- `variable not in scope`, plus `until`, `gcd` and `lcm`.  All of them are
-- pure Haskell — this was a library gap, not a compiler one.
--
-- Every line below is checked against `ghc -O2`, including the boundary
-- cases GHC's semantics turn on: `or []`, `words ""`, `unwords []`,
-- `lines ""` vs `lines "\n"` vs `lines "a\n"` vs `lines "a\n\nb"`
-- (newline as terminator), `gcd 0 5`, `gcd` of a negative, `lcm 0 5`.

isPos :: Int -> Bool
isPos n = n > 0

lt4 :: Int -> Bool
lt4 n = n < 4

add :: Int -> Int -> Int
add a b = a + b

nums :: [Int]
nums = [1, 2, 3, 4, 5]

main :: IO ()
main = do
  print (last nums)
  print (init nums)
  print (foldl1 add nums)
  print (foldr1 add nums)
  print (concatMap (\n -> [n, n]) [(1::Int), 2])
  print (scanl add 0 nums)
  print (scanl1 add nums)
  print (scanr add 0 nums)
  print (scanr1 add nums)
  print (and [True, True])
  print (and [True, False])
  print (or [False, True])
  print (or ([] :: [Bool]))
  print (any isPos nums)
  print (all isPos nums)
  print (all lt4 nums)
  print (take 4 (iterate (\n -> n * (2::Int)) 1))
  print (take 3 (repeat 'z'))
  print (take 7 (cycle "ab"))
  print (takeWhile lt4 nums)
  print (dropWhile lt4 nums)
  print (span lt4 nums)
  print (break isPos nums)
  print (splitAt 2 nums)
  print (elem (3::Int) nums)
  print (elem (9::Int) nums)
  print (notElem (9::Int) nums)
  print (elem 'b' "abc")
  print (lookup (2::Int) [((1::Int),'a'), ((2::Int),'b')])
  print (lookup (9::Int) [((1::Int),'a')])
  print (lookup "k" [("k",(1::Int))])
  print (zip nums "abc")
  print (zip3 [(1::Int),2] "ab" [True,False])
  print (zipWith add nums [(10::Int),20,30])
  print (zipWith3 (\a b c -> a + b + c) [(1::Int),2] [(10::Int),20] [(100::Int),200])
  print (unzip [((1::Int),'a'), ((2::Int),'b')])
  print (unzip3 [((1::Int),'a',True), ((2::Int),'b',False)])
  print (lines "a\nb")
  print (lines "a\n")
  print (lines "\n")
  print (lines "")
  print (lines "a\n\nb")
  print (words "  hello   world  ")
  print (words "")
  print (unlines ["a", "b"])
  print (unwords ["a", "b"])
  print (unwords ([] :: [String]))
  print (until (\n -> n > (100::Int)) (\n -> n * 2) 1)
  print (gcd (12::Int) 18, gcd (0::Int) 5, gcd (-12::Int) 18)
  print (lcm (4::Int) 6, lcm (0::Int) 5)
  -- Regression: |x * y| overflows rhc's 63-bit Int while the result
  -- fits, so `lcm` must divide by `gcd` before multiplying (#970, #813).
  print (lcm (4000000000000000000 :: Int) 2)
  print (lcm (2 :: Int) 4000000000000000000)
  print (lcm (-4 :: Int) 6)
  -- `gcd 0 0` and `lcm 0 0`: GHC's base defines both as 0 (the Report's
  -- Prelude listing instead errors on gcd 0 0; GHC is the reference here).
  print (gcd (0 :: Int) 0)
  print (lcm (0 :: Int) 0)
