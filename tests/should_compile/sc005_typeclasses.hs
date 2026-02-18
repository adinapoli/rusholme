-- GHC testsuite: type classes with superclasses and multiple methods
module Sc005Typeclasses where

-- Simple class
class Describable a where
    describe :: a -> String

-- Class with superclass
class (Eq a) => Hashable a where
    hash :: a -> Int

-- Class with multiple methods and default implementation
class Container f where
    empty  :: f a
    insert :: a -> f a -> f a
    toList :: f a -> [a]
    size   :: f a -> Int
    size c = length (toList c)

-- Multi-param type class
class Convertible a b where
    convert :: a -> b

-- Instance with context
instance (Eq a, Show a) => Describable [a] where
    describe xs = show (length xs)

-- Instance with superclass constraint
data MySet a = MySet [a]

instance Eq a => Eq (MySet a) where
    MySet xs == MySet ys = xs == ys
