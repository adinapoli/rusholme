-- GHC testsuite: qualified and aliased imports
module Sc002QualifiedImports where

import qualified Data.Map as Map
import qualified Data.Set as S
import Data.List (sort, nub, (\\))
import Data.Maybe hiding (fromJust)
import qualified Prelude as P

f :: P.Int -> P.Int
f x = x
