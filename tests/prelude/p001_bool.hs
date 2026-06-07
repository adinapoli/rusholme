-- Prelude regression: Bool(..), not, (&&), (||), otherwise (#759).
module Main where

main :: IO ()
main = do
    print True
    print False
    print (not True)
    print (not False)
    print (True && False)
    print (True && True)
    print (False || True)
    print (False || False)
    print otherwise
