-- Prelude partiality: `cycle []` must error rather than loop (#970).  The
-- message is module-qualified (Data.List.cycle), matching head/tail.
module Main where

main :: IO ()
main = do
    putStrLn "before"
    print (take 3 (cycle ([] :: [Int])))
