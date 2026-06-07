{-# LANGUAGE NoImplicitPrelude #-}
module Prelude
    ( Bool(..), Maybe(..), Either(..), Ordering(..)
    , String
    , not, (&&), (||), otherwise
    , (+), (-), (*), negate, abs, div, mod
    , (==), (/=), (<), (>), (<=), (>=), compare
    , id, const, flip, (.), ($)
    , map, filter, (++), head, tail, null, length
    , foldr, foldl, concat, take, drop
    , maybe, fromMaybe, either
    , reverse
    , putChar, putStr, putStrLn, print
    , error
    , intToChar, charToInt
    , max, min, signum
    , even, odd
    , sum, product, replicate
    , Eq(..)
    , Ord(..)
    , Bounded(..)
    , Enum(..)
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

min :: Int -> Int -> Int
min x y = case x <= y of
    True  -> x
    False -> y

signum :: Int -> Int
signum n = case n == 0 of
    True  -> 0
    False -> case n > 0 of
        True  -> 1
        False -> negate 1

even :: Int -> Bool
even n = mod n 2 == 0

odd :: Int -> Bool
odd n = mod n 2 /= 0

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
-- Ord type class
-- ========================================================================

-- `compareInt` is a top-level helper rather than an inline instance method
-- body because nested case-of inside instance methods historically tripped
-- desugarer/lifter bugs (now fixed by #704).  Kept top-level for clarity
-- and to avoid relying on the still-experimental default-method machinery
-- in the first class declaration (#660).
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

-- ========================================================================
-- Bounded type class
-- ========================================================================

class Bounded a where
  minBound :: a
  maxBound :: a

-- Bounded Int is deferred because Int.minBound (-9223372036854775808)
-- cannot be expressed as a static literal in the current backend.
-- The negative-literal syntax `-9223372036854775807 - 1` desugars to
-- a Negate AST node that the LLVM backend doesn't yet lower.
-- Tracked in: https://github.com/adinapoli/rusholme/issues/212

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

-- Int-domain enumeration helpers.
--
-- These are ordinary, fully-monomorphic Int functions (so they ARE
-- type-checked, unlike class-default bodies) that build the integer index
-- sequence the Haskell 2010 Report uses to define the ranged enumerations:
--
--   enumFromTo x y       = map toEnum [fromEnum x .. fromEnum y]
--   enumFromThenTo x y z = map toEnum [fromEnum x, fromEnum y .. fromEnum z]
--
-- The class defaults below call these to produce the list of indices and
-- then `map toEnum` over it.  The crucial correctness property: every index
-- they yield lies between `fromEnum n` and `fromEnum m`/`fromEnum z`
-- inclusive, and `m`/`z` are themselves valid values of the enum, so every
-- index is necessarily <= fromEnum maxBound (and >= fromEnum minBound).
-- `toEnum` is therefore *structurally* only ever applied in range — the
-- "toEnum: out of range" error is defined out of existence by construction
-- rather than guarded against after the fact.
--
-- They use the monomorphic Int primitives (primGtInt / primLtInt …) rather
-- than the Ord (>)/(<) methods purely so the class defaults that call them
-- need no Ord Int dictionary; the helpers themselves are well-typed and
-- could use Ord just as well.
-- Unbounded ascending/stepped Int sequences, used by the generic (unbounded)
-- enumFrom / enumFromThen class defaults.  These are correct only for
-- unbounded enums (Int); bounded instances override the two methods that use
-- them (see Bool/Ordering/Char below).
enumFromInt :: Int -> [Int]
enumFromInt i = i : enumFromInt (primAddInt i 1)

enumFromStepInt :: Int -> Int -> [Int]
enumFromStepInt i step = i : enumFromStepInt (primAddInt i step) step

enumIntFromTo :: Int -> Int -> [Int]
enumIntFromTo i j =
  if primGtInt i j then [] else i : enumIntFromTo (primAddInt i 1) j

-- `step` is computed ONCE by the caller and threaded through unchanged, so a
-- successor index is never recomputed from (and never forces) a later list
-- element.  An ascending range (step >= 0) stops once the index passes the
-- upper bound; a descending range (step < 0) stops once it passes the lower
-- bound.  A zero step with i <= j yields an infinite list of i, matching GHC.
enumIntFromThenToStep :: Int -> Int -> Int -> [Int]
enumIntFromThenToStep i step limit =
  if primGeInt step 0
  then if primGtInt i limit
       then []
       else i : enumIntFromThenToStep (primAddInt i step) step limit
  else if primLtInt i limit
       then []
       else i : enumIntFromThenToStep (primAddInt i step) step limit

class Enum a where
  succ :: a -> a
  pred :: a -> a
  toEnum :: Int -> a
  fromEnum :: a -> Int
  enumFrom :: a -> [a]
  enumFromThen :: a -> a -> [a]
  enumFromTo :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]
  -- Default implementations per the Haskell 2010 Report (§6.3.4).  The Report
  -- defines the ranged enumerations by mapping `toEnum` over the corresponding
  -- *Int-domain* sequence:
  --
  --   enumFrom x         = map toEnum [fromEnum x ..]
  --   enumFromThen x y   = map toEnum [fromEnum x, fromEnum y ..]
  --   enumFromTo x y     = map toEnum [fromEnum x .. fromEnum y]
  --   enumFromThenTo x y z = map toEnum [fromEnum x, fromEnum y .. fromEnum z]
  --
  -- We follow that formulation exactly, using the monomorphic Int helpers
  -- (enumIntFromTo / enumIntFromThenToStep / enumFromStepInt) for the
  -- bounded sequences.  The `step` of the stepped enumerations is bound by
  -- a `let` in the default body so it is computed ONCE per call rather than
  -- recomputed at each recursive step (a regression test exercises this:
  -- see tests/e2e/ghc_744_let_in_default_body.hs).  Because
  -- the upper/lower bound passed to those helpers is itself a valid value of
  -- the enum, every index they emit is in range, so `map toEnum` never applies
  -- `toEnum` to an out-of-range index.  enumFromTo and enumFromThenTo are thus
  -- TOTAL for every Enum instance, finite or not — no "toEnum: out of range"
  -- crash is possible by construction.
  --
  -- enumFrom and enumFromThen, by contrast, are inherently partial for FINITE
  -- types: the Report's generic default runs the Int sequence unbounded, which
  -- is correct only for unbounded types such as Int.  For the bounded Prelude
  -- instances (Bool, Ordering, Char) those two methods are OVERRIDDEN below to
  -- terminate at the type's maximum/minimum (mirroring GHC, where bounded
  -- instances override enumFrom/enumFromThen).
  --
  -- (`map` is referenced before its definition; that is fine because the
  -- renamer resolves all top-level names before processing bodies.)
  enumFrom n = map toEnum (enumFromInt (fromEnum n))
  enumFromThen n n2 =
    let step = primSubInt (fromEnum n2) (fromEnum n)
    in map toEnum (enumFromStepInt (fromEnum n) step)
  enumFromTo n m = map toEnum (enumIntFromTo (fromEnum n) (fromEnum m))
  enumFromThenTo n n2 m =
    let step = primSubInt (fromEnum n2) (fromEnum n)
    in map toEnum (enumIntFromThenToStep (fromEnum n) step (fromEnum m))

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

-- Char, Bool and Ordering inherit enumFromTo / enumFromThenTo from the class
-- defaults (those are total for finite types).  They OVERRIDE enumFrom and
-- enumFromThen, however: the generic defaults run the Int sequence unbounded
-- and would feed an out-of-range index to toEnum once they pass maxBound.  GHC
-- handles this exactly the same way — bounded instances terminate enumFrom /
-- enumFromThen at the type's bounds.
--
-- We express the bounded form directly in terms of the (total) enumFromTo /
-- enumFromThenTo methods, terminating at the type's concrete maxBound /
-- minBound *value*.  We write those bounds as the relevant constructor rather
-- than via the Bounded `maxBound`/`minBound` methods: an instance-method body
-- is not type-checked, so a bare `maxBound :: a` cannot be resolved to the
-- right Bounded instance.  Naming the constructor keeps the dispatch
-- unambiguous and the definition total.
--
--   enumFrom x       = enumFromTo x maxBound
--   enumFromThen x y = enumFromThenTo x y (if ascending then maxBound else minBound)
--
-- where "ascending" is `fromEnum y >= fromEnum x`.
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
-- More numeric and list utilities
-- ========================================================================

sum :: [Int] -> Int
sum []     = 0
sum (x:xs) = x + sum xs

product :: [Int] -> Int
product []     = 1
product (x:xs) = x * product xs

replicate :: Int -> a -> [a]
replicate n x = case n <= 0 of
    True  -> []
    False -> x : replicate (n - 1) x

-- Uses (:) as a higher-order value — relies on constructor wrappers (#386).
reverse :: [a] -> [a]
reverse = foldl (flip (:)) []

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
-- Non-printable characters with codepoint > 127 are rendered as \<decimal>.
-- Note: '"' is NOT escaped here — it is a printable character and is
-- rendered literally. showLitString handles '"' separately because
-- strings are double-quote-delimited.
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
    True  -> '\\' : showPosInt (charToInt c) ++ rest
    False -> c : rest

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
-- Arithmetic sequences are now methods of the Enum class (see above).
-- The monomorphic Int versions have been replaced by class methods.
-- ========================================================================


-- ========================================================================
-- Polymorphic functions still blocked:
--   - zip, unzip: needs tuple codegen (#571)
--   - fst, snd: needs tuple codegen (#571)
--   - read: needs parser integration (no issue filed yet)
-- ========================================================================
