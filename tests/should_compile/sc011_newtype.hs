-- GHC testsuite: newtype declarations
module Sc011Newtype where

-- Simple newtype
newtype Age = Age Int deriving (Show, Eq, Ord)

newtype Name = Name String deriving (Show, Eq)

-- Newtype with record syntax
newtype Wrapper a = Wrapper { unwrap :: a } deriving (Show)

-- Newtype with type variable
newtype Identity a = Identity { runIdentity :: a }

newtype Const a b = Const { getConst :: a }

-- Newtype for newtype deriving
newtype Sum a = Sum { getSum :: a } deriving (Show, Eq, Ord)

newtype Product a = Product { getProduct :: a } deriving (Show, Eq)

-- Usage
mkAge :: Int -> Maybe Age
mkAge n
    | n >= 0    = Just (Age n)
    | otherwise = Nothing
