module Main where

-- Regression test for #929: `show` on a `String` rendered a list of character
-- literals (`['h','i']`) instead of a quoted string.
--
-- Haskell 2010 §6.3.3 solves this with a `showList` method on `Show`: the
-- list instance delegates to the *element* type's `showList`, and `Show Char`
-- overrides it to produce a quoted, escaped literal.
--
-- Rusholme spells the method `showList :: [a] -> String` rather than GHC's
-- `[a] -> ShowS`, since there is no `ShowS` yet, so it is exercised here only
-- through the instances that delegate to it.

data Wrapped = Wrapped String

instance Show Wrapped where
  show (Wrapped s) = "Wrapped " ++ show s

main :: IO ()
main = do
  print "hi"
  -- The empty string is the base case of the quoted form, not "[]".
  print ""
  -- Escapes come from showLitChar (#617); a double quote needs escaping in a
  -- string literal but not in a character literal.
  print "a\nb\t\"q\"\\z"
  print "tab\there"
  -- A character still shows as a character.
  print 'x'
  print '\n'
  -- Nested inside the containers whose instances delegate to showList.
  print ("hi", "there")
  print ('a', True, (1 :: Int), "hi")
  print ["ab", "cd"]
  print [""]
  print (Just "hi")
  print [Just "a", Nothing]
  -- A list of non-Char elements must still render in list form.
  print [(1 :: Int), 2, 3]
  print [[(1 :: Int)], [2]]
  print ['a', 'b']
  -- A hand-written instance reaches `show` at String through the dictionary.
  print (Wrapped "hi")
