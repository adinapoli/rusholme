-- Type classes
module Ghc008Typeclass where

class Show a where
  show :: a -> String

instance Show Bool where
  show True = "True"
  show False = "False"

instance Show Int where
  show x = "<Int>"
