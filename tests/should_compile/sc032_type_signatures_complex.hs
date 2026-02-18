-- GHC testsuite: complex type signatures
module Sc032TypeSignaturesComplex where

-- Higher-kinded type variable
class Functor' f where
    fmap' :: (a -> b) -> f a -> f b

-- Rank-2 type (requires RankNTypes, but parses as standard Haskell)
applyToInt :: (forall a. a -> a) -> Int -> Int
applyToInt f n = f n

-- Multiple constraints
foo :: (Show a, Eq a, Ord a) => a -> a -> String
foo x y
    | x == y    = show x
    | x < y     = show x ++ " < " ++ show y
    | otherwise = show x ++ " > " ++ show y

-- Constraint on higher-kinded variable
bar :: (Functor f, Show (f Int)) => f Int -> String
bar = show

-- Nested Maybe in signature
baz :: Maybe (Maybe (Maybe Int)) -> Int
baz (Just (Just (Just n))) = n
baz _ = 0

-- Tuple in constraint (parenthesised class application)
qux :: (Eq (a, b), Show a, Show b) => a -> b -> String
qux a b = show a ++ show b

-- Long function type
longFun :: Int -> Bool -> String -> Double -> Char -> Maybe Int -> Either String Int
longFun _ _ _ _ _ Nothing  = Left "nothing"
longFun _ _ _ _ _ (Just n) = Right n
