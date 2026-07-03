module Sfc006MissingSuperclassInstance where

-- `Boxed` declares `Sizeable` as a superclass, so `instance Boxed Wrapper`
-- requires a `Sizeable Wrapper` instance in scope (Haskell 2010 §4.3.2).
-- None exists, so the compiler must reject the program (#889).

data Wrapper = MkWrapper

class Sizeable a where
  measure :: a -> Wrapper

class Sizeable a => Boxed a where
  unbox :: a -> Wrapper

instance Boxed Wrapper where
  unbox w = w

main :: Wrapper
main = unbox MkWrapper
