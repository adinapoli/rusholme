-- Type operators
module Ghc012TypeOperator where

data a :-> b = Fun (a -> b)

infixr 9 :->
