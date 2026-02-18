-- GHC testsuite: type synonyms including complex ones
module Sc012TypeSynonyms where

type Name    = String
type Age     = Int
type Point2D = (Double, Double)
type Point3D = (Double, Double, Double)

-- Parameterised synonym
type Pair a   = (a, a)
type Triple a = (a, a, a)
type Assoc k v = [(k, v)]

-- Synonyms using other synonyms
type PersonRecord = (Name, Age)
type Database     = [PersonRecord]

-- Synonym for function type
type Predicate a  = a -> Bool
type Transform a  = a -> a
type BinOp a      = a -> a -> a

-- Synonym for IO action
type Action = IO ()

-- Nested
type Matrix a = [[a]]
type Vector a = [a]

-- Used in type signatures
lookupPerson :: Name -> Database -> Maybe Age
lookupPerson _ [] = Nothing
lookupPerson n ((name, age):rest)
    | n == name = Just age
    | otherwise = lookupPerson n rest
