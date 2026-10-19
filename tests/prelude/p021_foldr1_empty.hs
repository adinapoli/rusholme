-- Prelude partiality: `foldr1 f []` must error (#970).  The message is
-- module-qualified (Data.List.foldr1), matching head/tail.
module Main where

main :: IO ()
main = do
    putStrLn "before"
    print (foldr1 (\a b -> a + b) ([] :: [Int]))
