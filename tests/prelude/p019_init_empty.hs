-- Prelude partiality: `init []` must error (#970).  The message is
-- module-qualified (Data.List.init), matching head/tail.
module Main where

main :: IO ()
main = do
    putStrLn "before"
    print (init ([] :: [Int]))
