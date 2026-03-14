-- Test infix operator definitions with complex patterns
module Sc049InfixOpDefinitions where

import Prelude hiding ((++))

-- Basic infix operator definition with cons pattern
infixl 5 ++
(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x : (xs ++ ys)
[] ++ ys = ys

-- Infix operator with literal pattern
infixr 0 `myOp`
5 `myOp` n = n + 10
x `myOp` n = n

-- Infix operator with tuple pattern
infixr 4 <->
(x, _) <-> (_, y) = (x, y)

-- Simple varsym operator
infixl 6 <+>
[] <+> ys = ys
(x:xs) <+> ys = x : (xs <+> ys)
