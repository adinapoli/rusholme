module Main where

-- Regression test for #948: a class default method reached through the
-- dictionary of an instance that has a *context* crashed.
--
-- The dictionary of a context-carrying instance is a function from the
-- context dictionaries to a dictionary value, so the eta-expanded wrapper
-- that hands the instance dictionary to the compiled default method has to
-- saturate it first.  It used to pass the unapplied dictionary function, and
-- the default method then projected a method field out of a closure.

class C a where
  describe :: a -> String
  -- A default that calls the class's own method — this is the one that had
  -- to project a field out of the dictionary it was handed.
  label :: a -> String
  label x = describe x
  -- A default that calls *another* default, so the chain is exercised too.
  shout :: a -> String
  shout x = label x ++ "!"

data W a = W a

data P a b = P a b

instance C Int where
  describe n = show n

instance C Bool where
  describe b = show b

-- One-parameter context.
instance C a => C (W a) where
  describe (W x) = "W " ++ describe x

-- Two-parameter context: both dictionary parameters must reach the wrapper
-- in the right order.
instance (C a, C b) => C (P a b) where
  describe (P x y) = "P " ++ describe x ++ " " ++ describe y

main :: IO ()
main = do
  -- Context-free instance: this always worked.
  putStrLn (label (1 :: Int))
  putStrLn (shout (1 :: Int))
  -- One-parameter context.
  putStrLn (label (W (2 :: Int)))
  putStrLn (shout (W (2 :: Int)))
  -- Nested, so the wrapper's own dictionary argument is itself built from a
  -- context-carrying instance.
  putStrLn (label (W (W (3 :: Int))))
  -- Two-parameter context.
  putStrLn (label (P (4 :: Int) True))
  putStrLn (shout (P (W (5 :: Int)) False))
  -- The overridden method still wins over the default.
  putStrLn (describe (P True (6 :: Int)))
