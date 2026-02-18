-- GHC testsuite: deriving clauses, all stock classes
module Sc019Deriving where

-- Deriving Show
data Color = Red | Green | Blue deriving (Show)

-- Deriving multiple classes
data Direction = North | South | East | West
    deriving (Show, Eq, Ord, Enum, Bounded)

-- Deriving for parameterised type
data Pair a b = Pair a b deriving (Show, Eq)

-- Deriving for newtype
newtype Wrapper a = Wrap a deriving (Show, Eq, Ord)

-- Deriving Read
data Expr = Num Int | Add Expr Expr deriving (Show, Read)

-- Deriving Ix (for arrays)
data Axis = X | Y | Z deriving (Show, Eq, Ord, Enum, Bounded, Ix)

-- Separate deriving clause per constructor style
data List a = Nil | Cons a (List a)
    deriving (Show, Eq)
