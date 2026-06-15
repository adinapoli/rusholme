-- Test 857: record patterns `Con { f = p, ... }`.
--
-- The renamer desugars record patterns into positional constructor patterns,
-- so field order does not matter, omitted fields become wildcards, and field
-- punning (`Con { f }`) binds the field name.  Values are built positionally
-- (record construction is exercised separately in #855).

data Point = Point { px :: Int, py :: Int }

data Triple = Triple { ta :: Int, tb :: Int, tc :: Int }

-- Explicit fields, written out of declaration order.
diffP :: Point -> Int
diffP (Point { py = b, px = a }) = a - b

-- Field punning with the other fields omitted.
firstT :: Triple -> Int
firstT (Triple { ta }) = ta

-- Mix: pun one field, give another explicitly (out of order), omit the third.
midSumT :: Triple -> Int
midSumT (Triple { tc = z, tb }) = tb + z

main :: IO ()
main = do
    print (diffP (Point 10 3))
    print (firstT (Triple 1 2 3))
    print (midSumT (Triple 1 2 3))
