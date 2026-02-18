-- GHC testsuite: algebraic data types, all constructor forms
module Sc003DataTypes where

-- Nullary constructor
data Unit = Unit

-- Multiple constructors
data Bool' = False' | True'

-- Parameterised
data Maybe' a = Nothing' | Just' a

-- Multiple type parameters
data Either' a b = Left' a | Right' b

-- Recursive
data List a = Nil | Cons a (List a)

-- Infix constructor
data a :+: b = Inl a | Inr b

infixr 6 :+:

-- Multiple fields
data Triple a b c = Triple a b c

-- Nested type application
data Rose a = Rose a [Rose a]
