-- e2e_863: Derived Show for constructors with fields.
--
-- Regression test for #863: deriving Show on a constructor that carries
-- fields used to crash at runtime. The derived body's field call
-- `show x0` was handed the instance's own dictionary (e.g. dict$Show$Age)
-- instead of the field type's (dict$Show$Int), because the field's
-- Show-constraint span collided with the instance method's own constraint
-- span in the desugarer's evidence map. The bug only surfaced when Show was
-- the first/only derived class (otherwise an earlier derivation shifted the
-- synthesised-occurrence span counter and hid the collision).
--
-- Covers single-field, multi-field, and multi-constructor-with-fields, with
-- Show derived ALONE so the regression is actually exercised.

data Age = Age Int deriving (Show)

data Point = Point Int Int deriving (Show)

data Shape = Circle Int | Square Int Int deriving (Show)

main :: IO ()
main = do
  putStrLn (show (Age 42))      -- Age 42
  putStrLn (show (Point 1 2))   -- Point 1 2
  putStrLn (show (Circle 5))    -- Circle 5
  putStrLn (show (Square 3 4))  -- Square 3 4
