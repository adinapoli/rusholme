-- GHC testsuite: import with hiding and explicit import lists
module Sc035ImportHiding where

import Prelude hiding (lookup, map, filter)
import Data.List (isPrefixOf, isSuffixOf, intercalate)
import Data.Char (isAlpha, isDigit, toUpper, toLower)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set (fromList, toList, member)

-- Use the imported things
capitalize :: String -> String
capitalize []     = []
capitalize (c:cs) = toUpper c : map toLower cs
  where
    map _ []     = []
    map f (x:xs) = f x : map f xs

-- Using qualified import
emptyMap :: Map.Map String Int
emptyMap = Map.empty

singletonMap :: String -> Int -> Map.Map String Int
singletonMap k v = Map.singleton k v
