{-# LANGUAGE NoImplicitPrelude #-}
module Prelude
    ( Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    , not, (&&), (||), otherwise
    , (+), (-), (*), negate, abs, div, mod
    , (==), (/=), (<), (>), (<=), (>=)
    , id, const, flip, (.), ($)
    , map, filter, (++), head, tail, null, length
    , foldr, foldl, concat, take, drop
    , maybe, fromMaybe, either
    , putChar, putStr, putStrLn, print
    , error
    , intToChar, charToInt
    , max
    , Eq(..)
    , Show(..), show, showString, showLitChar, showListWith, showListTail
    , intToDigit
    , enumFrom, enumFromTo, enumFromThen, enumFromThenTo
    ) where

-- ========================================================================
-- PrimOp imports
-- ========================================================================

foreign import prim "add_Int"   primAddInt   :: Int -> Int -> Int
foreign import prim "sub_Int"   primSubInt   :: Int -> Int -> Int
foreign import prim "mul_Int"   primMulInt   :: Int -> Int -> Int
foreign import prim "neg_Int"   primNegInt   :: Int -> Int
foreign import prim "abs_Int"   primAbsInt   :: Int -> Int
foreign import prim "quot_Int"  primQuotInt  :: Int -> Int -> Int
foreign import prim "rem_Int"   primRemInt   :: Int -> Int -> Int
foreign import prim "eq_Int"    primEqInt    :: Int -> Int -> Bool
foreign import prim "ne_Int"    primNeInt    :: Int -> Int -> Bool
foreign import prim "lt_Int"    primLtInt    :: Int -> Int -> Bool
foreign import prim "le_Int"    primLeInt    :: Int -> Int -> Bool
foreign import prim "gt_Int"    primGtInt    :: Int -> Int -> Bool
foreign import prim "ge_Int"    primGeInt    :: Int -> Int -> Bool
foreign import prim "putChar_"      primPutChar  :: Char -> IO ()
foreign import prim "primPutStrLn"  primPutStrLn :: String -> IO ()
foreign import prim "primPutStr"    primPutStr   :: String -> IO ()
foreign import prim "error"     primError    :: String -> a
foreign import prim "intToChar" intToChar    :: Int -> Char
foreign import prim "charToInt" charToInt    :: Char -> Int

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
-- Identity and const
-- ========================================================================

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

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

-- putStr and putStrLn are implemented in Haskell (not as direct prim
-- wrappers) so that pattern matching on the list spine drives lazy
-- evaluation.  The prim versions (primPutStr/primPutStrLn) expect
-- fully-evaluated C strings and cannot handle lazy cons-cell chains
-- produced by e.g. (++) or show.
putStr :: String -> IO ()
putStr []     = primPutStr ""
putStr (x:xs) = do
    primPutChar x
    putStr xs

putStrLn :: String -> IO ()
putStrLn s = do
    putStr s
    primPutChar '\n'

print :: Show a => a -> IO ()
print x = putStrLn (show x)

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
-- Arithmetic (monomorphic on Int, pending type classes #531)
-- ========================================================================

(+) :: Int -> Int -> Int
(+) = primAddInt

(-) :: Int -> Int -> Int
(-) = primSubInt

(*) :: Int -> Int -> Int
(*) = primMulInt

negate :: Int -> Int
negate = primNegInt

abs :: Int -> Int
abs = primAbsInt

div :: Int -> Int -> Int
div = primQuotInt

mod :: Int -> Int -> Int
mod = primRemInt

max :: Int -> Int -> Int
max x y = case x >= y of
    True  -> x
    False -> y

-- ========================================================================
-- Comparison (monomorphic on Int, pending Ord class in #531)
-- ========================================================================

(<) :: Int -> Int -> Bool
(<) = primLtInt

(>) :: Int -> Int -> Bool
(>) = primGtInt

(<=) :: Int -> Int -> Bool
(<=) = primLeInt

(>=) :: Int -> Int -> Bool
(>=) = primGeInt

-- ========================================================================
-- Eq type class
-- ========================================================================

-- Helper functions for Eq Bool — can be inlined into the instance now that
-- #659 is fixed, but kept as top-level helpers until multi-equation instance
-- methods are verified to work end-to-end.
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

-- Note: the default method `x /= y = not (x == y)` is intentionally omitted.
-- A default method in the first class causes subsequent class methods to be
-- unbound in the typechecker (tracked in: https://github.com/adinapoli/rusholme/issues/660).
class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

instance Eq Int where
  (==) = primEqInt
  (/=) = primNeInt

instance Eq Bool where
  (==) = eqBool
  (/=) = neBool

-- ========================================================================
-- Higher-order combinators
-- ========================================================================

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

($) :: (a -> b) -> a -> b
($) f x = f x

-- ========================================================================
-- List functions
-- ========================================================================

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter p []     = []
filter p (x:xs) = case p x of
    True  -> x : filter p xs
    False -> filter p xs

(++) :: [a] -> [a] -> [a]
(++) []     ys = ys
(++) (x:xs) ys = x : (++) xs ys

head :: [a] -> a
head (x:xs) = x

tail :: [a] -> [a]
tail (x:xs) = xs

null :: [a] -> Bool
null []    = True
null (x:xs) = False

length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

concat :: [[a]] -> [a]
concat []     = []
concat (x:xs) = (++) x (concat xs)

take :: Int -> [a] -> [a]
take n []     = []
take n (x:xs) = case n <= 0 of
    True  -> []
    False -> x : take (n - 1) xs

drop :: Int -> [a] -> [a]
drop n []     = []
drop n (x:xs) = case n <= 0 of
    True  -> x : xs
    False -> drop (n - 1) xs

-- ========================================================================
-- Show typeclass
-- ========================================================================

-- Note: Haskell 2010's full Show class uses ShowS (String -> String) for
-- efficient difference-list concatenation, plus showsPrec for precedence.
-- Type synonym expansion in the typechecker is not yet implemented, so we
-- use a simplified single-method class. Follow-up: full ShowS/showsPrec
-- once type synonym unification is supported.

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

showPosInt :: Int -> String
showPosInt n = case n < 10 of
    True  -> intToDigit n : []
    False -> showPosInt (div n 10) ++ (intToDigit (mod n 10) : [])

-- ── Show helpers for lists ──────────────────────────────────────────

showListTail :: Show a => [a] -> String
showListTail []     = "]"
showListTail (x:xs) = ',' : show x ++ showListTail xs

showListWith :: Show a => [a] -> String
showListWith []     = "[]"
showListWith (x:xs) = '[' : show x ++ showListTail xs

-- showLitChar renders a single character as its escaped representation
-- (without surrounding quotes). Used by Show Char and showLitString.
--
-- Escape sequences handled: \\ \' \n \r \t \NUL \a \b \f \v \DEL
-- Note: '"' is NOT escaped here — it is a printable character and is
-- rendered literally. showLitString handles '"' separately because
-- strings are double-quote-delimited.
-- Non-printable characters with codepoint > 127 fall through to
-- literal rendering; proper unicode escape handling is tracked in:
-- https://github.com/adinapoli/rusholme/issues/682
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
showLitChar c     rest = c : rest

-- Monomorphic string display (avoids dictionary-passing, see #618).
-- showLitString must precede showString (callee before caller, #566).
--
-- '"' is handled explicitly before delegating to showLitChar because
-- showLitChar renders '"' literally (it is printable), but inside a
-- double-quoted string literal it must be escaped.
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
  show (Just x) = "Just " ++ show x

instance (Show a, Show b) => Show (Either a b) where
  show (Left x)  = "Left " ++ show x
  show (Right y) = "Right " ++ show y

-- ========================================================================
-- Maybe / Either
-- ========================================================================

maybe :: b -> (a -> b) -> Maybe a -> b
maybe n f Nothing  = n
maybe n f (Just x) = f x

fromMaybe :: a -> Maybe a -> a
fromMaybe d Nothing  = d
fromMaybe d (Just x) = x

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x)  = f x
either f g (Right y) = g y

-- ========================================================================
-- Arithmetic sequences
-- ========================================================================

-- [n..] infinite list starting at n
enumFrom :: Int -> [Int]
enumFrom n = n : enumFrom (n + 1)

-- [n..m] finite list from n to m inclusive
enumFromTo :: Int -> Int -> [Int]
enumFromTo n m = if n > m then [] else n : enumFromTo (n + 1) m

-- [n,n2..] infinite list with step (n2 - n)
enumFromThen :: Int -> Int -> [Int]
enumFromThen n n2 = n : enumFromThen n2 (n2 + (n2 - n))

-- [n,n2..m] finite list with step, up to m
enumFromThenTo :: Int -> Int -> Int -> [Int]
enumFromThenTo n n2 m =
    let step = n2 - n
    in if step >= 0
       then if n > m then [] else n : enumFromThenTo n2 (n2 + step) m
       else if n < m then [] else n : enumFromThenTo n2 (n2 + step) m

-- ========================================================================
-- Polymorphic functions still blocked:
--   - reverse: uses (:) as higher-order value, needs constructor closures (#386)
--   - zip, unzip: needs tuple codegen (#571)
--   - fst, snd: needs tuple codegen (#571)
--   - read: needs parser integration (no issue filed yet)
-- ========================================================================
