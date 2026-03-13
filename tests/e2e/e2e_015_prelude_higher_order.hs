-- e2e_015: Prelude higher-order and misc functions
--
-- Tests id, const, (.), ($), flip, fst, snd from the Prelude.
-- Self-contained with NoImplicitPrelude.

{-# LANGUAGE NoImplicitPrelude #-}

foreign import prim "putStrLn" putStrLn :: String -> IO ()

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)
infixr 9 .

($) :: (a -> b) -> a -> b
f $ x = f x
infixr 0 $

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

fst :: (a, b) -> a
fst (x, _) = x

snd :: (a, b) -> b
snd (_, y) = y

greet :: String -> String -> String
greet greeting name = greeting

main :: IO ()
main = do
    -- id
    putStrLn (id "id-ok")
    -- const
    putStrLn (const "const-ok" "ignored")
    -- (.)
    putStrLn ((id . id) "compose-ok")
    -- ($)
    putStrLn $ "dollar-ok"
    -- flip
    putStrLn (flip const "ignored" "flip-ok")
    -- fst
    putStrLn (fst ("fst-ok", "ignored"))
    -- snd
    putStrLn (snd ("ignored", "snd-ok"))
