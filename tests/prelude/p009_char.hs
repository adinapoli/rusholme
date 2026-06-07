-- Prelude regression: intToChar, charToInt, intToDigit (#759).
module Main where

main :: IO ()
main = do
    print (charToInt 'A')
    print (intToChar 66)
    print (intToDigit 7)
