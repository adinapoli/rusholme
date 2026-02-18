-- GHC testsuite: explicit forall in type signatures (Haskell 2010 + RankNTypes style)
module Sc015ForallTypes where

-- Simple forall (same as polymorphic)
identity :: forall a. a -> a
identity x = x

-- Forall with constraint
showAndReturn :: forall a. Show a => a -> String
showAndReturn x = show x

-- Multiple constrained type variables
zipWithBoth :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c]
zipWithBoth f xs ys = case (xs, ys) of
    ([], _)      -> []
    (_, [])      -> []
    (a:as, b:bs) -> f a b : zipWithBoth f as bs

-- Forall in data type
data ShowBox = forall a. Show a => MkShowBox a

-- Type with multiple constraints
bothConstraints :: (Show a, Eq a) => a -> a -> String
bothConstraints x y
    | x == y    = "equal: " ++ show x
    | otherwise = show x ++ " /= " ++ show y
