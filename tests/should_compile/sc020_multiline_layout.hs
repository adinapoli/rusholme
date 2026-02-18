-- GHC testsuite: tricky layout rule cases from the Haskell 2010 report
module Sc020MultilineLayout where

-- Indented where after do
f :: IO ()
f = do
    g
    h
  where
    g = return ()
    h = return ()

-- where binding references other where binding
v :: Int
v = a + b
  where
    a = x + y
    b = x - y
    x = 10
    y = 3

-- let in where
w :: Int
w = result
  where
    result = let a = 1
                 b = 2
             in a + b

-- Multiline function application
longApp :: Int
longApp = foldr
    (+)
    0
    [1,2,3,4,5]

-- Multiline type signature
multilineSig
    :: Int
    -> String
    -> Bool
    -> Double
multilineSig _ _ _ = 0.0

-- Guards on separate lines
classify :: Int -> String
classify n
    | n < 0     = "negative"
    | n == 0    = "zero"
    | n < 10    = "small"
    | n < 100   = "medium"
    | otherwise = "large"
