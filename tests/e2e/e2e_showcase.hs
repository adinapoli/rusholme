-- e2e_showcase: Compiler feature showcase with Show type class
--
-- Demonstrates dictionary-passing type class infrastructure:
-- Show instances for Int, Bool, Char, and polymorphic showPair
-- that exercises constraint solving and dictionary plumbing.

module Showcase where

showPair :: Int -> Bool -> [Char]
showPair x y = show x ++ ", " ++ show y

main :: IO ()
main = do
    putStrLn (show 42)
    putStrLn (show True)
    putStrLn (show False)
    putStrLn (show 'a')
    putStrLn (showPair 42 True)
    putStrLn (show 'z')
    putStrLn (show 100)
    putStrLn (showPair 7 False)
    putStrLn (show 0)
