-- GHC testsuite: multi-parameter type classes
module Sc037MultiparamTC where

-- Two-parameter class
class Convert a b where
    convert :: a -> b

instance Convert Int Double where
    convert = fromIntegral

instance Convert String [Char] where
    convert = id

-- Three-parameter class
class Relation a b c where
    relates :: a -> b -> c -> Bool

-- Class with functional dependency syntax (parse only, no semantics)
class Collection c e | c -> e where
    empty  :: c
    insert :: e -> c -> c
    member :: e -> c -> Bool
    toList :: c -> [e]

-- Multi-param instance
instance Collection [a] a where
    empty     = []
    insert    = (:)
    member    = elem
    toList xs = xs
