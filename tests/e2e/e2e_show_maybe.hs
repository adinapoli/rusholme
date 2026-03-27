-- e2e_show_maybe: Show instance for Maybe
--
-- Tests the `Show (Maybe a)` instance with dictionary passing.
-- Uses a helper function to avoid the TypeAnn erasure issue (#361),
-- ensuring the Show constraint is resolved via the polymorphic instance
-- rather than a monomorphic call site.
--
-- Exercises both constructors: Nothing (nullary) and Just (with argument).

module ShowMaybe where

showMaybeInt :: Maybe Int -> String
showMaybeInt x = show x

main :: IO ()
main = do
    putStrLn (show (Just 42))
    putStrLn (showMaybeInt Nothing)
    putStrLn (showMaybeInt (Just 0))
    putStrLn (showMaybeInt (Just 100))
