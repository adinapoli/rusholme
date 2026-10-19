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
    , div, mod
    , even, odd
    , gcd, lcm
    , (==), (/=), (<), (>), (<=), (>=), compare
    , putChar, putStr, putStrLn
    , error
    , intToChar, charToInt
    , intToDouble, doubleToInt
    , Num(..)
    , Fractional(..)
    , Floating(..)
    , Eq(..)
    , Ord(..)
    , Bounded(..)
    , Enum(..)
    , Show(..), showString, showLitChar, showListWith, showListTail
    , Functor(..)
    , Applicative(..)
    , Monad(..)
    , intToDigit
    , enumFrom, enumFromTo, enumFromThen, enumFromThenTo
    -- Data.Function
    , id, const, flip, (.), ($), until
    -- Data.List
    , map, filter, (++), head, tail, null, length
    , last, init
    , foldr, foldl, concat, concatMap, take, drop, reverse
    , foldl1, foldr1
    , scanl, scanl1, scanr, scanr1
    , and, or, any, all
    , iterate, repeat, cycle
    , takeWhile, dropWhile, span, break, splitAt
    , elem, notElem, lookup
    , zip, zip3, zipWith, zipWith3, unzip, unzip3
    , lines, words, unlines, unwords
    , sum, product, replicate
    , maximum, minimum
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
