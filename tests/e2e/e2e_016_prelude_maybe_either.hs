-- e2e_016: Prelude Maybe and Either functions
--
-- Tests maybe, fromMaybe, either from the Prelude.
-- Self-contained with NoImplicitPrelude.

{-# LANGUAGE NoImplicitPrelude #-}

foreign import prim "putStrLn" putStrLn :: String -> IO ()

data Maybe a = Nothing | Just a

data Either a b = Left a | Right b

maybe :: b -> (a -> b) -> Maybe a -> b
maybe z _ Nothing  = z
maybe _ f (Just x) = f x

fromMaybe :: a -> Maybe a -> a
fromMaybe d Nothing  = d
fromMaybe _ (Just x) = x

either :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left  x) = f x
either _ g (Right y) = g y

id :: a -> a
id x = x

exclaim :: String -> String
exclaim s = s

main :: IO ()
main = do
    -- maybe with Nothing
    putStrLn (maybe "default" id Nothing)
    -- maybe with Just
    putStrLn (maybe "default" id (Just "value"))
    -- fromMaybe with Nothing
    putStrLn (fromMaybe "fallback" Nothing)
    -- fromMaybe with Just
    putStrLn (fromMaybe "fallback" (Just "present"))
    -- either with Left
    putStrLn (either id id (Left "left-val"))
    -- either with Right
    putStrLn (either id id (Right "right-val"))
