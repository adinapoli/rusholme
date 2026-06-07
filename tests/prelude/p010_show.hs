-- Prelude regression: Show(..), show, showString, showLitChar,
-- showListWith, showListTail (#759).
module Main where

main :: IO ()
main = do
    putStrLn (show 42)
    putStrLn (show (negate 7))
    putStrLn (show True)
    putStrLn (show 'q')
    putStrLn (show '\n')
    putStrLn (showString "hi")
    putStrLn (showLitChar '\t' "")
    putStrLn (showListWith [1, 2])
    putStrLn (showListTail [2, 3])
