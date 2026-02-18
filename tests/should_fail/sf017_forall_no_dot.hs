-- Should fail: forall without the trailing dot
module Sf017ForallNoDot where

f :: forall a a -> a
f x = x
