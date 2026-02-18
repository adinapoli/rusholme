-- Should fail: reserved keyword used as variable name
module Sf011ReservedAsVar where

where :: Int -> Int
where x = x
