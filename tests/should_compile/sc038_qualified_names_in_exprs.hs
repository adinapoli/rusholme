-- GHC testsuite: qualified names in expressions and patterns
module Sc038QualifiedNamesExprs where

import qualified Data.Maybe as Maybe
import qualified Data.List  as List

-- Using qualified name in expression
safeHead :: [a] -> Maybe a
safeHead = Maybe.listToMaybe

-- Qualified in pattern (constructor)
unwrap :: Maybe a -> a -> a
unwrap (Maybe.Just x) _ = x
unwrap Maybe.Nothing  d = d

-- Qualified operator (unusual but valid)
joinStrings :: [String] -> String
joinStrings = List.intercalate ", "

-- Chained qualified access
process :: [Int] -> [Int]
process = List.nub . List.sort . List.filter (> 0)

-- Qualified constructor in expression
wrapInJust :: a -> Maybe a
wrapInJust = Maybe.Just

-- Module-qualified in type signature
transform :: Maybe.Maybe Int -> Maybe.Maybe Int
transform = fmap (+ 1)
