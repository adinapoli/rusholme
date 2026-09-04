-- Prelude regression: Eq/Ord class defaults (#951) and the container
-- instances that rely on them (#952).
module Main where

data P = P Int

-- Only `compare`; the operators and max/min come from the Ord defaults.
instance Eq P where
    (==) (P x) (P y) = x == y

instance Ord P where
    compare (P x) (P y) = compare x y

unP :: P -> Int
unP (P n) = n

main :: IO ()
main = do
    print (P 1 < P 2)
    print (P 2 <= P 2)
    print (P 3 > P 4)
    print (P 3 >= P 3)
    print (P 1 /= P 2)
    print (unP (max (P 1) (P 2)))
    print (unP (min (P 1) (P 2)))
    print (max (3 :: Int) 5)
    print (min (3 :: Int) 5)
    print ("ab" == "ab")
    print (compare "ab" "b")
    print (Just 'x' == Just 'x')
    print (compare (Nothing :: Maybe Int) (Just 1))
    print (compare LT EQ)
    print (compare True False)
    print (((1 :: Int), 'a') == ((1 :: Int), 'a'))
    print (compare ((1 :: Int), 'a') ((1 :: Int), 'b'))
