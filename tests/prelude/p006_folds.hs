-- Prelude regression: foldr, foldl, concat, take, drop, sum, product,
-- replicate (#759).
module Main where

add :: Int -> Int -> Int
add x y = x + y

sub :: Int -> Int -> Int
sub x y = x - y

main :: IO ()
main = do
    print (foldr add 0 [1, 2, 3])
    print (foldl add 0 [1, 2, 3])
    -- foldl/foldr differ on a non-associative operator:
    print (foldl sub 10 [1, 2, 3])
    print (foldr sub 10 [1, 2, 3])
    print (concat [[1], [2, 3], []])
    print (take 2 [1, 2, 3])
    print (drop 1 [1, 2, 3])
    print (sum [1, 2, 3, 4])
    print (product [1, 2, 3, 4])
    print (replicate 3 7)
