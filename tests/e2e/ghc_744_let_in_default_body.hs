module Main where

-- Regression test for issue #744: `let`-bound names inside class default
-- method bodies and instance method bodies used to be mistranslated by the
-- GRIN -> LLVM backend (the case scrutinee resolved to a garbage value),
-- because default/instance bodies are not type-checked (#629) and the let-
-- bound binder was missing from the GRIN translator's var_map at codegen
-- time.  The desugarer's `registerExprBinders`/`registerRhsBinders` plus
-- the NonRec single-binding let lowering now make this correct end-to-end.
--
-- Exercises both shapes:
--   * `let` inside a class DEFAULT method body (inherited by the instance).
--   * `let` inside an INSTANCE method body that overrides a class method.
--
-- Both bodies use class methods from their type-class context (e.g. the
-- `Num`-style (+) / (-) defined for Int in the Prelude), so the test would
-- previously have segfaulted at runtime via the codegen garbage pointer.

-- A two-method class where the second method has a `let`-using default that
-- relies on the first method.  The inherited default must work for a user
-- instance that defines only the primitive (`measure`).
class HasMeasure a where
  measure :: a -> Int
  -- Default body uses `let` to bind an intermediate Int and then case-scrutinise
  -- it via the monomorphic Int primitive.  This exercises the same shape that
  -- triggered the original #744 segfault (let in an untyped default body).
  twiceMeasure :: a -> Int
  twiceMeasure x =
    let m = measure x
    in m + m

data Box = MkBox Int

instance HasMeasure Box where
  measure (MkBox n) = n
  -- inherits twiceMeasure default

-- A class whose instance overrides the default with a `let`-using body.
class Stride a where
  fromStride :: a -> Int
  toStride   :: Int -> a
  stride     :: a -> a -> Int
  stride x y = fromStride y - fromStride x  -- default (no let)

data Pos = MkPos Int

instance Stride Pos where
  fromStride (MkPos n) = n
  toStride n           = MkPos n
  -- Instance method body uses `let` to bind `step` and then references it
  -- twice — same shape as the original Enum default that triggered #744.
  stride x y =
    let step = fromStride y - fromStride x
    in step + step

-- A class default body whose let-bound name is the scrutinee of a case.
-- The original #744 report specifically pointed at translateCaseToValue
-- mis-resolving a let-bound Var as the scrutinee, so we exercise that path
-- directly.
class Sign a where
  asInt :: a -> Int
  signOf :: a -> Int
  signOf x =
    let n = asInt x
    in case primGeIntPub n 0 of
         True  -> 1
         False -> 0 - 1

-- Re-export of the primitive used by the case scrutinee, since the
-- prim foreign import in lib/Prelude.hs is not exported.  We import it
-- here as a module-local foreign primitive of the same shape.
foreign import prim "ge_Int" primGeIntPub :: Int -> Int -> Bool

data Token = MkToken Int

instance Sign Token where
  asInt (MkToken n) = n
  -- inherits signOf default

main :: IO ()
main = do
  -- twiceMeasure exercises let inside a class DEFAULT body.
  putStrLn (show (twiceMeasure (MkBox 21)))
  -- stride exercises let inside an INSTANCE method body that overrides a
  -- default.
  putStrLn (show (stride (MkPos 3) (MkPos 10)))
  -- signOf exercises let inside a class DEFAULT body where the let-bound
  -- name is the case scrutinee (the exact shape from the #744 report).
  putStrLn (show (signOf (MkToken 7)))
  putStrLn (show (signOf (MkToken (0 - 4))))
