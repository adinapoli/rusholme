{-# LANGUAGE NoImplicitPrelude #-}
-- | The public Prelude.
--
-- Re-exports the layered boot stack:
--
--   RHC.Prim → GHC.Base → Data.{Function,List,Maybe,Either} → Prelude
--
-- Local definitions are limited to glue that ties the layers together
-- (`print = putStrLn . show`).
module Prelude
    ( -- GHC.Base
      Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    , not, (&&), (||), otherwise
    , (+), (-), (*), negate, abs, div, mod
    , max, min, signum, even, odd
    , (==), (/=), (<), (>), (<=), (>=), compare
    , putChar, putStr, putStrLn
    , error
    , intToChar, charToInt
    , Eq(..)
    , Ord(..)
    , Bounded(..)
    , Enum(..)
    , Show(..), showString, showLitChar, showListWith, showListTail
    , intToDigit
    , enumFrom, enumFromTo, enumFromThen, enumFromThenTo
    -- Data.Function
    , id, const, flip, (.), ($)
    -- Data.List
    , map, filter, (++), head, tail, null, length
    , foldr, foldl, concat, take, drop, reverse
    , sum, product, replicate
    -- Data.Maybe
    , maybe, fromMaybe
    -- Data.Either
    , either
    -- Defined locally
    , print
    ) where

import GHC.Base
import Data.Function
import Data.List
import Data.Maybe
import Data.Either

-- print depends on Show (in GHC.Base) and putStrLn (in GHC.Base).
print :: Show a => a -> IO ()
print x = putStrLn (show x)
