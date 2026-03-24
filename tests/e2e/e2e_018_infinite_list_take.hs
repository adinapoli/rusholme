-- e2e_018: Infinite list with take (#631)

module InfiniteListTake where

main :: IO ()
main = print (length (take 3 [1..]))
