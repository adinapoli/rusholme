-- Should fail: layout violation - binding at wrong indentation level
module Sf005BadLayout where

f x = x
 + 1
  where
 y = 2
