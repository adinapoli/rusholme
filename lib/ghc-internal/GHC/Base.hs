{-# LANGUAGE NoImplicitPrelude #-}
-- | GHC.Base — compiler-magic types and core classes.
--
-- Mirrors GHC's `ghc-internal:GHC.Base` in role: every primitive
-- data type, the core Eq/Ord/Bounded/Enum/Show class hierarchy, the
-- Bool/arithmetic/IO operators backed by RHC.Prim primops, and the
-- helpers that the Show instances need to format primitive values.
--
-- Layer in the boot stack: imports RHC.Prim and Data.Function;
-- imported by `base`.  Carries `{-# LANGUAGE NoImplicitPrelude #-}`
-- because Prelude itself is being built on top of this module.
module GHC.Base
    ( -- Primitive data types
      Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    -- Error
    , error
    -- IO
    , putChar, putStr, putStrLn
    -- Boolean
    , not, (&&), (||), otherwise
    -- Arithmetic
    , div, mod
    , max, min, even, odd
    -- Double ↔ Int conversions (numeric tower, #880)
    , intToDouble, doubleToInt
    -- Classes
    , Num(..)
    , Eq(..)
    , Ord(..)
    , Bounded(..)
    , Enum(..)
    , Show(..)
    -- Show helpers
    , showString, showLitChar, showListWith, showListTail
    , intToDigit
    -- Enum helpers used by class defaults
    , enumFrom, enumFromTo, enumFromThen, enumFromThenTo
    , intToChar, charToInt
    ) where

import RHC.Prim

-- ========================================================================
-- Data types
-- ========================================================================

data Bool = False | True

data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

data Ordering = LT | EQ | GT

type String = [Char]

-- ========================================================================
-- Fixity declarations
-- ========================================================================

infixl 6 +, -
infixl 7 *, `div`, `mod`
infix  4 ==, /=, <, >, <=, >=
infixr 3 &&
infixr 2 ||

-- ========================================================================
-- Error
-- ========================================================================

error :: String -> a
error = primError

-- ========================================================================
-- IO wrappers
-- ========================================================================

putChar :: Char -> IO ()
putChar = primPutChar

putStr :: String -> IO ()
putStr []     = primPutStr ""
putStr (x:xs) = do
    primPutChar x
    putStr xs

putStrLn :: String -> IO ()
putStrLn s = do
    putStr s
    primPutChar '\n'

-- ========================================================================
-- Boolean functions
-- ========================================================================

not :: Bool -> Bool
not True  = False
not False = True

(&&) :: Bool -> Bool -> Bool
True  && x = x
False && _ = False

(||) :: Bool -> Bool -> Bool
True  || _ = True
False || x = x

otherwise :: Bool
otherwise = True

-- ========================================================================
-- Num type class
-- ========================================================================
--
-- The arithmetic operators are dictionary-dispatched class methods, so a
-- value of any `Num` instance shares one `(+)` / `(-)` / `(*)`.  At a
-- monomorphic call site (`x + y :: Int`) the solver picks `instance Num
-- Int` statically and the backend devirtualises the dictionary down to a
-- direct primop call, so this is as cheap as the previous monomorphic
-- definitions.  `fromInteger` is intentionally omitted until overloaded
-- literals and `Integer` land (see #140 / #212).

class Num a where
  (+)    :: a -> a -> a
  (-)    :: a -> a -> a
  (*)    :: a -> a -> a
  negate :: a -> a
  abs    :: a -> a
  signum :: a -> a

instance Num Int where
  (+) = primAddInt
  (-) = primSubInt
  (*) = primMulInt
  negate = primNegInt
  abs = primAbsInt
  -- Written with primops rather than `==`/`>`/`negate` so the instance is
  -- self-contained: a primitive instance must not depend on another
  -- instance's dictionary (`Eq Int`, `Ord Int`) being registered first,
  -- which is source-order-dependent in the desugarer.  Same style as the
  -- `Eq Int` / `Ord Int` instances below.  Tracked in
  -- https://github.com/adinapoli/rusholme/issues/881.
  signum n = case primEqInt n 0 of
      True  -> 0
      False -> case primGtInt n 0 of
          True  -> 1
          False -> primNegInt 1

instance Num Double where
  (+) = primAddDouble
  (-) = primSubDouble
  (*) = primMulDouble
  negate = primNegDouble
  -- Self-contained via `Double` primops and `Double` literals — same
  -- rationale as `instance Num Int` above (#881).  `fromInteger` is not yet
  -- available, so `0.0`/`1.0` are written as floating literals.
  abs x = case primLtDouble x 0.0 of
      True  -> primNegDouble x
      False -> x
  signum x = case primEqDouble x 0.0 of
      True  -> 0.0
      False -> case primGtDouble x 0.0 of
          True  -> 1.0
          False -> primNegDouble 1.0

-- ========================================================================
-- Integral / ordering helpers (still monomorphic on Int, pending the
-- Integral class and Ord-method defaults)
-- ========================================================================

div :: Int -> Int -> Int
div = primQuotInt

mod :: Int -> Int -> Int
mod = primRemInt

max :: Int -> Int -> Int
max x y = case x >= y of
    True  -> x
    False -> y

min :: Int -> Int -> Int
min x y = case x <= y of
    True  -> x
    False -> y

even :: Int -> Bool
even n = mod n 2 == 0

odd :: Int -> Bool
odd n = mod n 2 /= 0

-- ========================================================================
-- Eq type class
-- ========================================================================

eqBool :: Bool -> Bool -> Bool
eqBool True  True  = True
eqBool True  False = False
eqBool False True  = False
eqBool False False = True

neBool :: Bool -> Bool -> Bool
neBool True  True  = False
neBool True  False = True
neBool False True  = True
neBool False False = False

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

instance Eq Int where
  (==) = primEqInt
  (/=) = primNeInt

instance Eq Bool where
  (==) = eqBool
  (/=) = neBool

eqChar :: Char -> Char -> Bool
eqChar x y = primEqInt (charToInt x) (charToInt y)

neChar :: Char -> Char -> Bool
neChar x y = primNeInt (charToInt x) (charToInt y)

instance Eq Char where
  (==) = eqChar
  (/=) = neChar

instance Eq Double where
  (==) = primEqDouble
  (/=) = primNeDouble

-- ========================================================================
-- Ord type class
-- ========================================================================

compareInt :: Int -> Int -> Ordering
compareInt x y = case primLtInt x y of
    True  -> LT
    False -> case primEqInt x y of
        True  -> EQ
        False -> GT

class Ord a where
  compare :: a -> a -> Ordering
  (<)     :: a -> a -> Bool
  (<=)    :: a -> a -> Bool
  (>)     :: a -> a -> Bool
  (>=)    :: a -> a -> Bool

instance Ord Int where
  compare = compareInt
  (<)  = primLtInt
  (<=) = primLeInt
  (>)  = primGtInt
  (>=) = primGeInt

compareChar :: Char -> Char -> Ordering
compareChar x y = compareInt (charToInt x) (charToInt y)

ltChar :: Char -> Char -> Bool
ltChar x y = primLtInt (charToInt x) (charToInt y)

leChar :: Char -> Char -> Bool
leChar x y = primLeInt (charToInt x) (charToInt y)

gtChar :: Char -> Char -> Bool
gtChar x y = primGtInt (charToInt x) (charToInt y)

geChar :: Char -> Char -> Bool
geChar x y = primGeInt (charToInt x) (charToInt y)

instance Ord Char where
  compare = compareChar
  (<)  = ltChar
  (<=) = leChar
  (>)  = gtChar
  (>=) = geChar

compareDouble :: Double -> Double -> Ordering
compareDouble x y = case primLtDouble x y of
    True  -> LT
    False -> case primEqDouble x y of
        True  -> EQ
        False -> GT

instance Ord Double where
  compare = compareDouble
  (<)  = primLtDouble
  (<=) = primLeDouble
  (>)  = primGtDouble
  (>=) = primGeDouble

-- ========================================================================
-- Bounded type class
-- ========================================================================

class Bounded a where
  minBound :: a
  maxBound :: a

instance Bounded Char where
  minBound = '\NUL'
  maxBound = '\DEL'

instance Bounded Bool where
  minBound = False
  maxBound = True

instance Bounded Ordering where
  minBound = LT
  maxBound = GT

-- ========================================================================
-- Enum type class
-- ========================================================================

enumFromInt :: Int -> [Int]
enumFromInt i = i : enumFromInt (primAddInt i 1)

enumFromStepInt :: Int -> Int -> [Int]
enumFromStepInt i step = i : enumFromStepInt (primAddInt i step) step

enumIntFromTo :: Int -> Int -> [Int]
enumIntFromTo i j =
  if primGtInt i j then [] else i : enumIntFromTo (primAddInt i 1) j

enumIntFromThenToStep :: Int -> Int -> Int -> [Int]
enumIntFromThenToStep i step limit =
  if primGeInt step 0
  then if primGtInt i limit
       then []
       else i : enumIntFromThenToStep (primAddInt i step) step limit
  else if primLtInt i limit
       then []
       else i : enumIntFromThenToStep (primAddInt i step) step limit

-- A local map: the class defaults need `map` over Int sequences but
-- `Data.List.map` would create a cycle (Data.List → GHC.Base via
-- list functions referenced from class defaults).  Defining it here
-- keeps GHC.Base self-contained.
mapInt :: (Int -> a) -> [Int] -> [a]
mapInt f []     = []
mapInt f (x:xs) = f x : mapInt f xs

class Enum a where
  succ :: a -> a
  pred :: a -> a
  toEnum :: Int -> a
  fromEnum :: a -> Int
  enumFrom :: a -> [a]
  enumFromThen :: a -> a -> [a]
  enumFromTo :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]
  enumFrom n = mapInt toEnum (enumFromInt (fromEnum n))
  enumFromThen n n2 =
    let step = primSubInt (fromEnum n2) (fromEnum n)
    in mapInt toEnum (enumFromStepInt (fromEnum n) step)
  enumFromTo n m = mapInt toEnum (enumIntFromTo (fromEnum n) (fromEnum m))
  enumFromThenTo n n2 m =
    let step = primSubInt (fromEnum n2) (fromEnum n)
    in mapInt toEnum (enumIntFromThenToStep (fromEnum n) step (fromEnum m))

instance Enum Int where
  succ n = n + 1
  pred n = n - 1
  toEnum n = n
  fromEnum n = n
  enumFrom n = n : enumFrom (n + 1)
  enumFromTo n m = if n > m then [] else n : enumFromTo (n + 1) m
  enumFromThen n n2 = n : enumFromThen n2 (n2 + (n2 - n))
  enumFromThenTo n n2 m =
    let step = n2 - n
    in if step >= 0
       then if n > m then [] else n : enumFromThenTo n2 (n2 + step) m
       else if n < m then [] else n : enumFromThenTo n2 (n2 + step) m

instance Enum Char where
  succ c = intToChar (charToInt c + 1)
  pred c = intToChar (charToInt c - 1)
  toEnum n = intToChar n
  fromEnum c = charToInt c
  enumFrom c = enumFromTo c '\DEL'
  enumFromThen c d =
    if primGeInt (fromEnum d) (fromEnum c)
    then enumFromThenTo c d '\DEL'
    else enumFromThenTo c d '\NUL'

instance Enum Bool where
  succ False = True
  succ True  = error "succ: True is maxBound for Bool"
  pred True  = False
  pred False = error "pred: False is minBound for Bool"
  toEnum 0 = False
  toEnum 1 = True
  toEnum _ = error "toEnum: out of range for Bool"
  fromEnum False = 0
  fromEnum True  = 1
  enumFrom b = enumFromTo b True
  enumFromThen b c =
    if primGeInt (fromEnum c) (fromEnum b)
    then enumFromThenTo b c True
    else enumFromThenTo b c False

instance Enum Ordering where
  succ LT = EQ
  succ EQ = GT
  succ GT = error "succ: GT is maxBound for Ordering"
  pred GT = EQ
  pred EQ = LT
  pred LT = error "pred: LT is minBound for Ordering"
  toEnum 0 = LT
  toEnum 1 = EQ
  toEnum 2 = GT
  toEnum _ = error "toEnum: out of range for Ordering"
  fromEnum LT = 0
  fromEnum EQ = 1
  fromEnum GT = 2
  enumFrom o = enumFromTo o GT
  enumFromThen o p =
    if primGeInt (fromEnum p) (fromEnum o)
    then enumFromThenTo o p GT
    else enumFromThenTo o p LT

-- ========================================================================
-- Show typeclass
-- ========================================================================

class Show a where
  show :: a -> String

-- ── Character conversion ────────────────────────────────────────────

intToDigit :: Int -> Char
intToDigit i = case i >= 0 of
    True  -> case i <= 9 of
        True  -> intToChar (charToInt '0' + i)
        False -> error "intToDigit: not a digit"
    False -> error "intToDigit: not a digit"

-- ── Show Int helpers ────────────────────────────────────────────────

-- Local append used by showPosInt, showListWith etc. so GHC.Base stays
-- self-contained.  Prelude's polymorphic `(++)` lives in Data.List.
appendStr :: [Char] -> [Char] -> [Char]
appendStr []     ys = ys
appendStr (x:xs) ys = x : appendStr xs ys

showPosInt :: Int -> String
showPosInt n = case n < 10 of
    True  -> intToDigit n : []
    False -> appendStr (showPosInt (div n 10)) (intToDigit (mod n 10) : [])

-- ── Show helpers for lists ──────────────────────────────────────────

showListTail :: Show a => [a] -> String
showListTail []     = "]"
showListTail (x:xs) = ',' : appendStr (show x) (showListTail xs)

showListWith :: Show a => [a] -> String
showListWith []     = "[]"
showListWith (x:xs) = '[' : appendStr (show x) (showListTail xs)

showLitChar :: Char -> String -> String
showLitChar '\\'  rest = '\\' : '\\' : rest
showLitChar '\''  rest = '\\' : '\'' : rest
showLitChar '\n'  rest = '\\' : 'n'  : rest
showLitChar '\r'  rest = '\\' : 'r'  : rest
showLitChar '\t'  rest = '\\' : 't'  : rest
showLitChar '\NUL' rest = '\\' : '0' : rest
showLitChar '\a'  rest = '\\' : 'a'  : rest
showLitChar '\b'  rest = '\\' : 'b'  : rest
showLitChar '\f'  rest = '\\' : 'f'  : rest
showLitChar '\v'  rest = '\\' : 'v'  : rest
showLitChar '\DEL' rest = '\\' : 'D' : 'E' : 'L' : rest
showLitChar c     rest = case charToInt c > 127 of
    True  -> '\\' : appendStr (showPosInt (charToInt c)) rest
    False -> c : rest

showLitString :: String -> String
showLitString []         = "\""
showLitString ('"' : xs) = '\\' : '"' : showLitString xs
showLitString (x   : xs) = showLitChar x (showLitString xs)

showString :: String -> String
showString s = '"' : showLitString s

-- ── Show instances ──────────────────────────────────────────────────

instance Show Int where
  show n = case n < 0 of
      True  -> '-' : showPosInt (0 - n)
      False -> showPosInt n

instance Show Double where
  -- Rendered by the RTS via Zig's shortest-round-trip formatter (#883).
  -- Readable, not yet bit-for-bit GHC (scientific-notation thresholds
  -- differ — tracked as a follow-up).
  show = primShowDouble

instance Show Bool where
  show b = case b of
      True  -> "True"
      False -> "False"

instance Show Ordering where
  show o = case o of
      LT -> "LT"
      EQ -> "EQ"
      GT -> "GT"

instance Show Char where
  show c = '\'' : showLitChar c "'"

instance Show a => Show [a] where
  show xs = showListWith xs

instance Show a => Show (Maybe a) where
  show Nothing  = "Nothing"
  show (Just x) = appendStr "Just " (show x)

instance (Show a, Show b) => Show (Either a b) where
  show (Left x)  = appendStr "Left " (show x)
  show (Right y) = appendStr "Right " (show y)
