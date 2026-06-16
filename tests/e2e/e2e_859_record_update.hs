-- Test 859: record update syntax `p { f = e, ... }` (Haskell 2010 §3.15.3).
--
-- The renamer desugars record update into a case that rebuilds the value,
-- copying the unchanged fields and substituting the updated ones.  The
-- original value is left unchanged (records are immutable).  Values are read
-- back with positional pattern matching (selectors are tracked in #853).

data Point = Point { px :: Int, py :: Int }

p0 :: Point
p0 = Point 1 2

-- Update a single field; the other is copied.
p1 :: Point
p1 = p0 { py = 9 }

-- Update both fields.
p2 :: Point
p2 = p0 { px = 5, py = 6 }

fstP :: Point -> Int
fstP (Point a _) = a

sndP :: Point -> Int
sndP (Point _ b) = b

main :: IO ()
main = do
    print (fstP p1)
    print (sndP p1)
    print (fstP p2)
    print (sndP p2)
    print (fstP p0)
    print (sndP p0)
