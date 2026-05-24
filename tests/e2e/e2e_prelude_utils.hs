-- Prelude utilities: even, odd, min, signum, sum, product, replicate.
main :: IO ()
main = do
    print (even 4)
    print (odd 7)
    print (min 3 5)
    print (signum (negate 9))
    print (signum 0)
    print (signum 12)
    print (sum [1, 2, 3, 4, 5])
    print (product [1, 2, 3, 4])
    print (replicate 4 'x')
