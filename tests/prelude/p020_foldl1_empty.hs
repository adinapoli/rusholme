-- Prelude partiality: `foldl1 f []` must error (#970).  The message is
-- module-qualified (Data.List.foldl1), matching head/tail.
module Main where

main :: IO ()
main = do
    putStrLn "before"
    print (foldl1 (\a b -> a + b) ([] :: [Int]))
