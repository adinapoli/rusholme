{-# LANGUAGE NoImplicitPrelude #-}
module DictMinimal where

foreign import prim "eq_Int"   eqInt :: Int -> Int -> Bool
foreign import prim "putStrLn" putStrLn :: String -> IO ()

class Eq a where
  (==) :: a -> a -> Bool

instance Eq Int where
  (==) = eqInt

main = putStrLn (if (1 == 2) then "true" else "false")
