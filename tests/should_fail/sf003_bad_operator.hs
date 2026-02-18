-- Should fail: operator starting with : used as varop (not valid in Haskell)
module Sf003BadOperator where

-- :foo is a consym and can only be a data constructor, not a function binding
:foo x = x
