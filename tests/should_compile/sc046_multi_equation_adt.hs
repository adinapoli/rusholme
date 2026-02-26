-- Regression test for issue #407: multi-equation functions with user-defined
-- ADT constructor patterns must compile without "duplicate definition" errors
-- and without crashing in the desugar/typechecker stages.
module Sc046MultiEquationAdt where

data MyList a = Nil | Cons a (MyList a)

-- Multi-equation function using constructor patterns on a user-defined ADT.
headIt :: MyList a -> a
headIt (Cons x _) = x
headIt Nil = error "empty list"

-- Nullary constructor pattern (simpler case).
isNil :: MyList a -> Bool
isNil Nil = True
isNil (Cons _ _) = False
