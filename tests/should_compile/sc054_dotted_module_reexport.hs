-- #822: dotted module name in `module M.N` export-list re-export.
{-# LANGUAGE NoImplicitPrelude #-}
module Foo
    ( module GHC.Base
    , module Data.List
    ) where

import GHC.Base
import Data.List
