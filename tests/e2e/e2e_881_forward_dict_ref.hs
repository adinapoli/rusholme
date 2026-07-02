-- e2e: instance dictionary CAFs forward-referencing later-declared
-- instances (#881).  `instance MyNum T` is declared *before*
-- `instance MyEq T`, and `mySignum` calls `myEq` — so `dict$MyNum$T`
-- references `dict$MyEq$T` ahead of its declaration.  Before the fix
-- this minted a dangling placeholder unique and failed at link time
-- (`undefined reference to dict$MyEq$T_NNNN`).  Output diffed against
-- GHC.
module Main where

class MyNum a where
  mySignum :: a -> a

data T = T Int

-- MyNum T declared BEFORE MyEq T; mySignum uses myEq (forward dict ref).
instance MyNum T where
  mySignum (T n) = case myEq (T n) (T 0) of
    True  -> T 0
    False -> T 1

class MyEq a where
  myEq :: a -> a -> Bool

instance MyEq T where
  myEq (T a) (T b) = a == b

unT :: T -> Int
unT (T n) = n

main :: IO ()
main = do
  print (unT (mySignum (T 5)))
  print (unT (mySignum (T 0)))
