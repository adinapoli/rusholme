-- Regression test for issue #660: class default method name resolution
-- Ensure that defining a class with a default method does not corrupt the
-- name resolution environment for subsequently-defined classes and instances.
class Class1 a where
  method1 :: a -> Int
  doubled :: a -> Int
  doubled x = method1 x + method1 x

class Class2 a where
  method2 :: a -> Int

data Val = Val Int

instance Class2 Val where
  method2 (Val n) = n + 1

main = print (method2 (Val 41))
