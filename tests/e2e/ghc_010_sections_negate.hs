-- Operator sections and unary negation (#736).
--
-- Haskell 2010 §3.4 / §3.5:
--   (e op)  ≡  \x -> e  op x       -- left section
--   (op e)  ≡  \x -> x  op e       -- right section
--   -e      ≡  negate e

incOne :: Int -> Int
incOne = (+ 1)

prependZero :: Int -> Int
prependZero = (10 -)

negFive :: Int
negFive = -5

main :: IO ()
main = do
    print (incOne 7)
    print (prependZero 3)
    print negFive
    print (negate 8)
