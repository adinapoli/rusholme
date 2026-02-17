-- !!! import qualified Prelude should leave (), [] etc in scope

module Ghc001QualifiedImport where

import qualified Prelude

f :: Prelude.IO ()
f = Prelude.return ()
