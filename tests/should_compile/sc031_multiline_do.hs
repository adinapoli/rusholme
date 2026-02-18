-- GHC testsuite: do notation with complex patterns and binds
module Sc031MultilineDo where

-- do with tuple bind
pairAction :: IO (Int, String)
pairAction = do
    let x = 42
    let s = "hello"
    return (x, s)

-- do with case
conditionalAction :: Int -> IO String
conditionalAction n = do
    result <- return (n * 2)
    case result of
        0 -> return "zero"
        _ -> return "nonzero"

-- do with multiple lets
multiLet :: IO Int
multiLet = do
    let a = 1
    let b = 2
    let c = a + b
    return c

-- Nested do
nestedDo :: IO ()
nestedDo = do
    xs <- do
        let a = [1,2,3]
        return a
    mapM_ print xs

-- do with where
doWithWhere :: IO ()
doWithWhere = do
    action1
    action2
  where
    action1 = return ()
    action2 = return ()

-- do with if
ifInDo :: Bool -> IO ()
ifInDo flag = do
    if flag
        then putStrLn "yes"
        else return ()
    putStrLn "done"
