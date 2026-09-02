-- Characterisation test for native `main`'s process exit status.
--
-- `main`'s tail value here is a bare variable bound to an IO action, which
-- is pointer-typed at the LLVM boundary.  Returning it raw emitted
-- `ret ptr` inside `define i32 @main()` — rejected by the LLVM verifier —
-- and leaked the pointer's low bits as the exit code: this program exited
-- 200 before the guard in `translateReturn`.  The harness asserts exit 0,
-- so the regression cannot come back unnoticed.
--
-- IMPORTANT: the `.stdout` sidecar is deliberately Rusholme's *current*
-- output, which is INCOMPLETE.  GHC prints "start", "x", "x": the tail
-- action is never performed, and an action value reached by a plain force
-- runs once and then memoises.  Both gaps are tracked, and whoever closes
-- them must update the sidecar — this test failing at that point is the
-- intended tripwire, not a regression.
--   tail action never performed: https://github.com/adinapoli/rusholme/issues/943
--   action consumed by a force:  https://github.com/adinapoli/rusholme/issues/944
main :: IO ()
main = do
  putStrLn "start"
  let act = putStrLn "x"
  act
  act
