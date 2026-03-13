-- Should fail: foreign import prim missing type signature (no ::)
module Sf020ForeignMissingType where

foreign import prim "add_Int" primAddInt
