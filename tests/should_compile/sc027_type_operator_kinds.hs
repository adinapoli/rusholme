-- GHC testsuite: type operators
module Sc027TypeOperatorKinds where

-- Infix type constructor
data a :-> b = Fn (a -> b)
infixr 0 :->

data a :+: b = InL a | InR b
infixr 6 :+:

data a :*: b = Both a b
infixr 7 :*:

-- Usage in signatures
applyFn :: (a :-> b) -> a -> b
applyFn (Fn f) x = f x

-- Operator type in constraint
class (f :+: g) ~ Either f g => Coproduct f g where
    inl :: f -> (f :+: g)
    inr :: g -> (f :+: g)

-- Nested type operators
type Sum3 a b c = a :+: b :+: c

-- Type-level application of operator
pairOp :: (Int :*: Bool)
pairOp = Both 1 True
