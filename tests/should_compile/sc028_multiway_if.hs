-- GHC testsuite: regular if/then/else in various positions
module Sc028MultiwayIf where

-- if in let
f :: Int -> Int
f x = let y = if x > 0 then x else -x
      in y * 2

-- if in do
g :: IO ()
g = do
    let flag = True
    if flag then return () else return ()

-- Nested if
classify :: Int -> Int -> String
classify x y =
    if x > 0
        then if y > 0
                 then "first quadrant"
                 else "fourth quadrant"
        else if y > 0
                 then "second quadrant"
                 else "third quadrant"

-- if as function argument
h :: Int -> String
h x = show (if x > 0 then x else -x)

-- if in case
j :: Maybe Int -> String
j mx = case mx of
    Nothing -> "nothing"
    Just x  -> if x > 0 then "positive" else "nonpositive"
