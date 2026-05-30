module Main where

-- Test: Enum class default methods (issue #713).
--
-- The Enum class provides default implementations of enumFrom, enumFromTo,
-- enumFromThen and enumFromThenTo in terms of succ, fromEnum and toEnum.
--
-- `Suit` defines ONLY the four primitive methods (succ, pred, toEnum,
-- fromEnum) and gets the ranged enumerations for free from the defaults.
data Suit = Clubs | Diamonds | Hearts | Spades

instance Show Suit where
  show Clubs    = "Clubs"
  show Diamonds = "Diamonds"
  show Hearts   = "Hearts"
  show Spades   = "Spades"

instance Enum Suit where
  succ Clubs    = Diamonds
  succ Diamonds = Hearts
  succ Hearts   = Spades
  succ Spades   = error "succ: Spades is maxBound for Suit"
  pred Diamonds = Clubs
  pred Hearts   = Diamonds
  pred Spades   = Hearts
  pred Clubs    = error "pred: Clubs is minBound for Suit"
  toEnum 0 = Clubs
  toEnum 1 = Diamonds
  toEnum 2 = Hearts
  toEnum 3 = Spades
  toEnum _ = error "toEnum: out of range for Suit"
  fromEnum Clubs    = 0
  fromEnum Diamonds = 1
  fromEnum Hearts   = 2
  fromEnum Spades   = 3

main :: IO ()
main = do
  -- enumFromTo from the class default, on the user instance.
  putStrLn (show (enumFromTo Clubs Spades))
  putStrLn (show (enumFromTo Diamonds Hearts))
  putStrLn (show (enumFromTo Spades Clubs))
  -- enumFromTo on the built-in Prelude instances, which now also rely on the
  -- shared class defaults rather than per-instance copies.
  putStrLn (show (enumFromTo False True))
  putStrLn (show (enumFromTo LT GT))
  putStrLn (show (enumFromTo 'a' 'e'))
