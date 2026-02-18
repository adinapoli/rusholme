-- GHC testsuite: do notation
module Sc008DoNotation where

-- Basic do
hello :: IO ()
hello = do
    putStrLn "Hello"
    putStrLn "World"

-- do with bind
readAndPrint :: IO ()
readAndPrint = do
    line <- getLine
    putStrLn line

-- do with let
compute :: IO ()
compute = do
    let x = 42
    let y = x * 2
    print y

-- Nested do
nested :: IO ()
nested = do
    result <- do
        putStr "Enter: "
        getLine
    putStrLn result

-- do with if
conditional :: Bool -> IO ()
conditional flag = do
    if flag
        then putStrLn "yes"
        else putStrLn "no"
    return ()
