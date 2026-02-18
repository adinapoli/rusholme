-- GHC testsuite: infix type constructors in data and type declarations
module Sc043InfixConstructorsInTypes where

-- Infix in data field types
data Tree f a = Leaf | Node (f a :+: f a) a
infixr 5 :+:

data a :+: b = Inl a | Inr b

-- Infix in type synonyms
type a ~> b = a -> b
infixr 0 ~>

-- Infix constructor in pattern
fromCoproduct :: (a :+: b) -> Either a b
fromCoproduct (Inl a) = Left a
fromCoproduct (Inr b) = Right b

-- Infix constructor in expression
toCoproduct :: Either a b -> (a :+: b)
toCoproduct (Left a)  = Inl a
toCoproduct (Right b) = Inr b

-- Using ~> type synonym
applyFn :: (a ~> b) -> a -> b
applyFn f x = f x
