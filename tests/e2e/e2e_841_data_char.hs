module Main where

import Data.Char

main :: IO ()
main = do
  putStrLn (show (ord 'A'))
  putStrLn (show (chr 97))
  putStrLn (show (isDigit '7'))
  putStrLn (show (isAlpha 'z'))
  putStrLn (show (toUpper 'a'))
  putStrLn (show (toLower 'B'))
  putStrLn (show (isSpace ' '))
  putStrLn (show (digitToInt 'f'))
