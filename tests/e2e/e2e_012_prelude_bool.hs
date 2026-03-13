-- e2e_012: Prelude boolean functions
--
-- Tests not, (&&), (||), and otherwise from the Prelude.
-- Self-contained with NoImplicitPrelude; uses foreign import prim
-- for output only.

{-# LANGUAGE NoImplicitPrelude #-}

foreign import prim "putStrLn" putStrLn :: String -> IO ()

data Bool = False | True

not :: Bool -> Bool
not True  = False
not False = True

(&&) :: Bool -> Bool -> Bool
True  && x = x
False && _ = False
infixr 3 &&

(||) :: Bool -> Bool -> Bool
True  || _ = True
False || x = x
infixr 2 ||

otherwise :: Bool
otherwise = True

showBool :: Bool -> String
showBool True  = "True"
showBool False = "False"

main :: IO ()
main = do
    -- not
    putStrLn (showBool (not True))
    putStrLn (showBool (not False))
    -- (&&)
    putStrLn (showBool (True && True))
    putStrLn (showBool (True && False))
    putStrLn (showBool (False && True))
    putStrLn (showBool (False && False))
    -- (||)
    putStrLn (showBool (True || True))
    putStrLn (showBool (True || False))
    putStrLn (showBool (False || True))
    putStrLn (showBool (False || False))
    -- otherwise
    putStrLn (showBool otherwise)
