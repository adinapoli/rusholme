-- Regression test for issue #644: type annotations in expressions
-- Verifies that (expr :: Type) desugars to expr, not unit_0.
x :: Int
x = (42 :: Int)

doubled :: Int
doubled = (x :: Int) + (x :: Int)

main = do
  print (x :: Int)
  print doubled
