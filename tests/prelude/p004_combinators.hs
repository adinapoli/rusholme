-- Prelude regression: id, const, flip, (.), ($) (#759).
module Main where

inc :: Int -> Int
inc x = x + 1

dbl :: Int -> Int
dbl x = x * 2

sub :: Int -> Int -> Int
sub x y = x - y

main :: IO ()
main = do
    print (id 42)
    print (const 1 2)
    print (flip sub 1 10)
    print ((inc . dbl) 5)
    print (inc $ 41)
