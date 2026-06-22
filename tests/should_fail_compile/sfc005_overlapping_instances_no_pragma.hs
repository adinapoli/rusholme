module Sfc005OverlappingInstancesNoPragma where

-- Two instances match `Describe [Bool]` (the general `Describe [a]` and the
-- specific `Describe [Bool]`), but neither carries an overlap pragma, so the
-- solver must still reject the program as ambiguous (#872).

class Describe a where
  describe :: a -> String

instance Describe a => Describe [a] where
  describe _ = "list"

instance Describe [Bool] where
  describe _ = "list of bool"

main :: IO ()
main = putStrLn (describe [True])
