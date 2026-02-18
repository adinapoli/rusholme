-- GHC testsuite: type annotations in expressions
module Sc040TypeAnnotationsExprs where

-- Simple annotation
x :: Int
x = (42 :: Int)

-- Annotation in application
y :: Int
y = fromIntegral (42 :: Integer)

-- Annotation on complex expression
z :: Double
z = (1 + 2 :: Double) * 3.0

-- Annotation in let
w :: String
w = let s = ("hello" :: String) in s ++ " world"

-- Annotation disambiguates show
showIt :: String
showIt = show (maxBound :: Int)

-- Annotation on lambda result
f :: Int -> Int
f = \n -> (n + 1 :: Int)

-- Nested annotation
g :: Maybe Int
g = Just (0 :: Int)

-- Annotation in do
action :: IO ()
action = do
    let v = (True :: Bool)
    print v
