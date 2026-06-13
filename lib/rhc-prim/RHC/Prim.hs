{-# LANGUAGE NoImplicitPrelude #-}
-- | RHC.Prim — innermost boot package.
--
-- Houses every `foreign import prim` declaration: the raw doorway
-- into Rusholme's PrimOp registry.  Code above this module never
-- speaks primops directly; it imports the wrappers here.
--
-- Mirrors GHC's `ghc-prim` in role, not in naming — our primop ABI
-- is ours (`add_Int`, not `+#`), so we keep an `RHC.*` namespace
-- here and mirror GHC's *public* surface (`GHC.*`, `Data.*`, …) one
-- layer up.
--
-- Invariant: this is the only module that contains `foreign import
-- prim`.  `GHC.Base` and `base` may import from here; nothing
-- imports the other way.
module RHC.Prim
    ( primAddInt, primSubInt, primMulInt, primNegInt, primAbsInt
    , primQuotInt, primRemInt
    , primEqInt, primNeInt, primLtInt, primLeInt, primGtInt, primGeInt
    , primPutChar, primPutStr, primPutStrLn
    , primError
    , intToChar, charToInt
    ) where

-- ── Integer arithmetic ───────────────────────────────────────────────

foreign import prim "add_Int"   primAddInt   :: Int -> Int -> Int
foreign import prim "sub_Int"   primSubInt   :: Int -> Int -> Int
foreign import prim "mul_Int"   primMulInt   :: Int -> Int -> Int
foreign import prim "neg_Int"   primNegInt   :: Int -> Int
foreign import prim "abs_Int"   primAbsInt   :: Int -> Int
foreign import prim "quot_Int"  primQuotInt  :: Int -> Int -> Int
foreign import prim "rem_Int"   primRemInt   :: Int -> Int -> Int

-- ── Integer comparisons ──────────────────────────────────────────────

foreign import prim "eq_Int"    primEqInt    :: Int -> Int -> Bool
foreign import prim "ne_Int"    primNeInt    :: Int -> Int -> Bool
foreign import prim "lt_Int"    primLtInt    :: Int -> Int -> Bool
foreign import prim "le_Int"    primLeInt    :: Int -> Int -> Bool
foreign import prim "gt_Int"    primGtInt    :: Int -> Int -> Bool
foreign import prim "ge_Int"    primGeInt    :: Int -> Int -> Bool

-- ── Character ↔ Int ──────────────────────────────────────────────────

foreign import prim "intToChar" intToChar    :: Int -> Char
foreign import prim "charToInt" charToInt    :: Char -> Int

-- ── IO ───────────────────────────────────────────────────────────────

foreign import prim "putChar_"      primPutChar  :: Char -> IO ()
foreign import prim "primPutStr"    primPutStr   :: [Char] -> IO ()
foreign import prim "primPutStrLn"  primPutStrLn :: [Char] -> IO ()

-- ── Diverging ────────────────────────────────────────────────────────

foreign import prim "error"     primError    :: [Char] -> a
