-- Prelude regression: putChar, putStr, putStrLn, print (#759).
module Main where

main :: IO ()
main = do
    putChar 'a'
    putChar '\n'
    putStr "ab"
    putStr "cd\n"
    putStrLn "ef"
    print 42
