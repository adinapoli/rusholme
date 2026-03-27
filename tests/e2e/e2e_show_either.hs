-- e2e_show_either: Show instance for Either
--
-- Tests the `Show (Either a b)` instance with multi-constraint dictionary passing.
-- Uses a helper function to avoid the TypeAnn erasure issue (#361).
--
-- This is the key regression test for issue #641: the Either instance has
-- two Show constraints (Show a, Show b), which previously caused dict_param_names
-- collisions and free-variable order inconsistencies in the lambda lifter.

module ShowEither where

showEitherIntBool :: Either Int Bool -> String
showEitherIntBool x = show x

main :: IO ()
main = do
    putStrLn (showEitherIntBool (Left 1))
    putStrLn (showEitherIntBool (Right True))
    putStrLn (showEitherIntBool (Left 42))
    putStrLn (showEitherIntBool (Right False))
