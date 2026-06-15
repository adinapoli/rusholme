-- Test 855: record construction syntax `Con { field = expr, ... }`.
--
-- The renamer desugars record construction into a positional constructor
-- application, reordering the supplied fields into declaration order, so the
-- order fields are written in does not matter.  Fields are read back here with
-- ordinary positional pattern matching (record selectors are tracked
-- separately in #853) to pin down that the reordering is correct.

data Point = Point { px :: Int, py :: Int }

data Box a = Box { unBox :: a }

-- Fields deliberately written out of declaration order.
p :: Point
p = Point { py = 4, px = 3 }

b :: Box Int
b = Box { unBox = 9 }

firstOf :: Point -> Int
firstOf (Point a _) = a

secondOf :: Point -> Int
secondOf (Point _ c) = c

boxed :: Box Int -> Int
boxed (Box v) = v

main :: IO ()
main = do
    print (firstOf p)
    print (secondOf p)
    print (firstOf p + secondOf p)
    print (boxed b)
