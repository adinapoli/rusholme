-- Prelude regression: (+), (-), (*), negate, abs, div, mod, signum,
-- even, odd (#759).
module Main where

main :: IO ()
main = do
    print (1 + 2)
    print (5 - 9)
    print (3 * 4)
    print (negate 7)
    print (abs (negate 9))
    print (div 17 3)
    print (mod 17 3)
    print (signum (negate 3))
    print (signum 0)
    print (signum 5)
    print (even 4)
    print (even 7)
    print (odd 4)
    print (odd 7)
