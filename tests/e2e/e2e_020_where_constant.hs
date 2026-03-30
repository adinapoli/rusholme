-- Test: where clause in a function body with a local constant binding.
-- 'offset' is a non-lambda where binding; after where→let desugaring
-- it becomes a simple let binding visible in the function body.

addOffset :: Int -> Int
addOffset n = n + offset
  where offset = 10

main = print (addOffset 5)
