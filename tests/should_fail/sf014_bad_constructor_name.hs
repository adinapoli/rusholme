-- Should fail: data constructor name starting with lowercase
module Sf014BadConstructorName where

data Foo = foo Int | Bar
