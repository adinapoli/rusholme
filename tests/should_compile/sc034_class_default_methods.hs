-- GHC testsuite: class declarations with default method implementations
module Sc034ClassDefaultMethods where

-- All methods have defaults
class Greet a where
    greet   :: a -> String
    greet _ = "Hello!"

    farewell :: a -> String
    farewell _ = "Goodbye!"

-- Partial defaults
class Shape a where
    area      :: a -> Double
    perimeter :: a -> Double
    isLarge   :: a -> Bool
    isLarge s = area s > 100.0

-- Defaults using other class methods
class Container f where
    toList   :: f a -> [a]
    fromList :: [a] -> f a
    isEmpty  :: f a -> Bool
    isEmpty = null . toList
    size     :: f a -> Int
    size = length . toList

-- Instance using all defaults
data Void

instance Greet Void

-- Instance overriding some defaults
data Circle = Circle Double

instance Shape Circle where
    area (Circle r) = 3.14159 * r * r
    perimeter (Circle r) = 2 * 3.14159 * r
    -- isLarge uses default

-- Multi-equation default methods
class Decision a where
    decide :: a -> Bool -> Bool
    decide True  _    = True
    decide False x    = x

    choose :: a -> Int -> Int
    choose x 0        = 0
    choose x 1        = x
    choose _ n        = n * 2
