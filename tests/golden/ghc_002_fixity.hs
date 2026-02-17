-- !!! tests fixity reading and printing
module Ghc002Fixity where

infixl 1 `f`
infixr 2 \\

data Foo = MkFoo Int | Float :==> Double

x `f` y = x

(\\) :: (Eq a) => [a] -> [a] -> [a]
(\\) xs ys = xs
infix 3 :==>
infix 4 `MkFoo`
