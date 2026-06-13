-- #823: T(..) and T(C1, C2) constructor lists in import specs.
{-# LANGUAGE NoImplicitPrelude #-}
module Foo where

import GHC.Base (Bool(..), Maybe(Just, Nothing), Either(..), Ordering)
