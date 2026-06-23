-- e2e: dictionaries threaded through local (let/where) generalised bindings (#875).
--
-- A local `let`/`where` binding that is generalised over a class constraint
-- must have its dictionary abstracted as a parameter and supplied at each call
-- site.  Before #875 the desugarer emitted a bare, unbound `dict$<Class>`
-- placeholder, so these programs failed to link.
module Main where

-- where-bound helper, generalised to `Eq a => a -> Bool`, used at Int.
eqSelfInt :: Int -> Bool
eqSelfInt x = g x
  where g y = y == y

-- let-bound helper, same shape, used at Char (a DIFFERENT instance) — proves
-- the dictionary is threaded per use-type, not monomorphised to one instance.
eqSelfChar :: Char -> Bool
eqSelfChar c =
  let h z = z == z
  in h c

-- A single local helper used at TWO types within one body: genuine local
-- polymorphism, each call site supplying its own dictionary.
bothEq :: Bool
bothEq = p (0 :: Int) && p 'a'
  where p y = y == y

main :: IO ()
main = do
  print (eqSelfInt 5)
  print (eqSelfChar 'a')
  print bothEq
