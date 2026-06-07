-- Constructors as higher-order values and partial application (#386).
--
-- In GRIN there are no code-pointer closures: a constructor used as a
-- value becomes a P-tag node over an eta-expanded wrapper function
-- (mkCon$<Con>), and the apply machinery saturates it one argument at
-- a time. This also exercises:
--   * a Prelude function passed as a HOF argument (#764: filter odd)
--   * partial application of a Prelude function (foldl f z)
--   * Prelude reverse (newly unblocked)
module Main where

data Pair = Pair Int Int

instance Show Pair where
  show (Pair a b) = "Pair " ++ show a ++ " " ++ show b

myFlip :: (a -> b -> c) -> b -> a -> c
myFlip f x y = f y x

rev :: [Int] -> [Int]
rev = foldl (myFlip (:)) []

main :: IO ()
main = do
    -- constructor as a bare HOF argument
    print (foldr (:) [] [1, 2, 3])
    -- partially applied constructor
    print (map (Pair 1) [10, 20])
    -- point-free CAF over a partially applied Prelude function
    print (rev [1, 2, 3])
    -- Prelude functions as HOF arguments (#764)
    print (filter odd [1, 2, 3, 4, 5])
    print (map negate [1, 2, 3])
    -- Prelude reverse (unblocked by this issue)
    print (reverse [4, 5, 6])
