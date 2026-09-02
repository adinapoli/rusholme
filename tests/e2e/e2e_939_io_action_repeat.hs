module Main where

import Control.Monad

-- #939: IO action values are repeatable — performing the same action value
-- twice runs its effect twice.
--
-- An action value is a suspended thunk that the perform operation
-- (`__rhc_perform`) evaluates *without* updating in place, so every
-- performance re-enters the body.  Before #939 the perform lowered to
-- `__rhc_force`, which memoised the thunk (`Ind → result`), and an action
-- value ran its effect only once.
--
-- GHC prints the same output for this program.

main :: IO ()
main = do
  -- The issue reproducer: the same list of actions performed twice.
  let acts = putStrLn "once" : []
  sequence_ acts
  sequence_ acts
  -- Same action value repeated within one list (replicateM_ n act
  -- semantics — replicateM_ itself does not exist yet).
  let act = putStrLn "x"
  sequence_ (act : act : act : [])
  -- The same action performed again after other work in between.
  let act2 = putStrLn "a"
  act2
  putStrLn "sep"
  act2
  putStrLn "end"