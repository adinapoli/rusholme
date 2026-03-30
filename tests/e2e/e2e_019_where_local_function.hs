-- Test: where clause in a function body with a non-capturing local helper.
-- The 'twice' helper is local to 'double' and takes no free variables
-- from the enclosing scope.

double :: Int -> Int
double n = twice n
  where twice x = x + x

main = print (double 7)
