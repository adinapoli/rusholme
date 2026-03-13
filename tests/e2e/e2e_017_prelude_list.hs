-- e2e_017: Prelude list functions
--
-- Tests map, filter, foldr, foldl, head, tail, null, length, (++),
-- reverse, take, drop, zip from the Prelude.
-- Self-contained with NoImplicitPrelude.

{-# LANGUAGE NoImplicitPrelude #-}

foreign import prim "putStrLn"  putStrLn  :: String -> IO ()
foreign import prim "add_Int"   primAddInt  :: Int -> Int -> Int
foreign import prim "sub_Int"   primSubInt  :: Int -> Int -> Int
foreign import prim "mul_Int"   primMulInt  :: Int -> Int -> Int
foreign import prim "eq_Int"    primEqInt   :: Int -> Int -> Bool
foreign import prim "lt_Int"    primLtInt   :: Int -> Int -> Bool
foreign import prim "le_Int"    primLeInt   :: Int -> Int -> Bool
foreign import prim "ge_Int"    primGeInt   :: Int -> Int -> Bool
foreign import prim "rem_Int"   primRemInt  :: Int -> Int -> Int
foreign import prim "quot_Int"  primQuotInt :: Int -> Int -> Int
foreign import prim "neg_Int"   primNegInt  :: Int -> Int

data Bool = False | True

-- Operators needed for list functions
(+) :: Int -> Int -> Int
(+) = primAddInt
infixl 6 +

(-) :: Int -> Int -> Int
(-) = primSubInt
infixl 6 -

(*) :: Int -> Int -> Int
(*) = primMulInt
infixl 7 *

(==) :: Int -> Int -> Bool
(==) = primEqInt
infix 4 ==

(<) :: Int -> Int -> Bool
(<) = primLtInt
infix 4 <

(<=) :: Int -> Int -> Bool
(<=) = primLeInt
infix 4 <=

(>=) :: Int -> Int -> Bool
(>=) = primGeInt
infix 4 >=

otherwise :: Bool
otherwise = True

-- ── List functions under test ──────────────────────────────────────

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter _ []     = []
filter p (x:xs)
    | p x       = x : filter p xs
    | otherwise  = filter p xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

head :: [a] -> a
head (x:_) = x

tail :: [a] -> [a]
tail (_:xs) = xs

null :: [a] -> Bool
null []    = True
null (_:_) = False

length :: [a] -> Int
length []     = 0
length (_:xs) = 1 + length xs

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)
infixr 5 ++

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

reverse :: [a] -> [a]
reverse = foldl (flip (:)) []

take :: Int -> [a] -> [a]
take _ []     = []
take n (x:xs)
    | n <= 0    = []
    | otherwise  = x : take (n - 1) xs

drop :: Int -> [a] -> [a]
drop _ []     = []
drop n xs
    | n <= 0    = xs
drop n (_:xs) = drop (n - 1) xs

zip :: [a] -> [b] -> [(a, b)]
zip []     _      = []
zip _      []     = []
zip (a:as) (b:bs) = (a, b) : zip as bs

-- ── Helpers for printing ───────────────────────────────────────────

showBool :: Bool -> String
showBool True  = "True"
showBool False = "False"

-- Simple Int-to-String for small non-negative integers
showInt :: Int -> String
showInt n
    | n < 0     = '-' : showInt (0 - n)
    | n < 10    = digitToChar n : []
    | otherwise = showInt (primQuotInt n 10) ++ (digitToChar (primRemInt n 10) : [])

digitToChar :: Int -> Char
digitToChar d
    | d == 0 = '0'
    | d == 1 = '1'
    | d == 2 = '2'
    | d == 3 = '3'
    | d == 4 = '4'
    | d == 5 = '5'
    | d == 6 = '6'
    | d == 7 = '7'
    | d == 8 = '8'
    | d == 9 = '9'

showIntList :: [Int] -> String
showIntList []     = "[]"
showIntList (x:xs) = '[' : showInt x ++ showTail xs

showTail :: [Int] -> String
showTail []     = "]"
showTail (x:xs) = ',' : showInt x ++ showTail xs

-- ── Tests ──────────────────────────────────────────────────────────

double :: Int -> Int
double x = x * 2

isPositive :: Int -> Bool
isPositive n = n >= 1

main :: IO ()
main = do
    -- map
    putStrLn (showIntList (map double [1, 2, 3]))
    -- filter
    putStrLn (showIntList (filter isPositive [0, 1, 0, 2, 0, 3]))
    -- foldr (sum)
    putStrLn (showInt (foldr (+) 0 [1, 2, 3, 4]))
    -- foldl (sum)
    putStrLn (showInt (foldl (+) 0 [10, 20, 30]))
    -- head
    putStrLn (showInt (head [7, 8, 9]))
    -- tail
    putStrLn (showIntList (tail [7, 8, 9]))
    -- null
    putStrLn (showBool (null ([] :: [Int])))
    putStrLn (showBool (null [1]))
    -- length
    putStrLn (showInt (length [10, 20, 30, 40, 50]))
    -- (++)
    putStrLn (showIntList ([1, 2] ++ [3, 4]))
    -- reverse
    putStrLn (showIntList (reverse [1, 2, 3]))
    -- take
    putStrLn (showIntList (take 2 [10, 20, 30, 40]))
    -- drop
    putStrLn (showIntList (drop 2 [10, 20, 30, 40]))
    -- zip (tested via showing first elements)
    putStrLn (showInt (length (zip [1, 2, 3] [10, 20])))
