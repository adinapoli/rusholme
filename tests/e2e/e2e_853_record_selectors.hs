-- Test 853: record field selectors used as functions.
--
-- The data types are declared with record syntax, but the values are built
-- with positional constructor application (`Point 3 4`) so this test exercises
-- only the selector functions — record construction/update/patterns are
-- tracked separately (#361, #418).
--
-- Covers a monomorphic single-constructor record and a parametric one.

data Point = Point { px :: Int, py :: Int }

data Box a = Box { unBox :: a }

p :: Point
p = Point 3 4

b :: Box Int
b = Box 5

main :: IO ()
main = do
    print (px p)
    print (py p)
    print (px p + py p)
    print (unBox b)
