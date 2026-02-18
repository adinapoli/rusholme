-- GHC testsuite: operator definitions and fixity
module Sc013OperatorsFixity where

-- Custom infix operator
(|>) :: a -> (a -> b) -> b
x |> f = f x
infixl 1 |>

(<|) :: (a -> b) -> a -> b
f <| x = f x
infixr 0 <|

-- Backtick infix
divides :: Int -> Int -> Bool
divides d n = n `mod` d == 0

-- Custom operator with type class constraint
(.+.) :: Num a => a -> a -> a
(.+.) = (+)
infixl 6 .+.

(.*.) :: Num a => a -> a -> a
(.*.) = (*)
infixl 7 .*.

-- Composition-like
(>>>) :: (a -> b) -> (b -> c) -> (a -> c)
f >>> g = g . f
infixr 9 >>>

-- Operator in expressions
pipeline :: Int -> Int
pipeline n = n |> (+1) |> (*2) |> subtract 3

-- Backtick application
isFactorOf :: Int -> Int -> Bool
isFactorOf = flip divides
