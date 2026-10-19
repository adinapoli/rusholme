-- Prelude partiality: `last []` must error, not return a bogus value or
-- loop (#970).  The message is module-qualified (Data.List.last), matching
-- head/tail.
module Main where

main :: IO ()
main = do
    putStrLn "before"
    print (last ([] :: [Int]))
