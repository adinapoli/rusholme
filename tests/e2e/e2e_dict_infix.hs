module DictInfix where

foreign import prim "eq_Int"   eqInt :: Int -> Int -> Bool
foreign import prim "putStrLn" putStrLn :: String -> IO ()

class Eq a where
  (==) :: a -> a -> Bool

instance Eq Int where
  (==) = eqInt

testInfix = 1 == 2
testLeft = (== 2) 1
testRight = (1 ==) 2

main = putStrLn "all dictionary arguments inserted"
