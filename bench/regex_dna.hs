-- Bench: nested case analysis (pattern-match dispatch overhead).
--
-- Inspired by the Benchmarks Game "regex-dna" benchmark's
-- pattern matching. Defines a small state machine with several
-- states and transitions, then runs a long input through it.
-- Stresses case dispatch on small ADTs, which tests how well
-- the codegen handles multi-branch pattern matches.

data State = S0 | S1 | S2 | S3 | S4
data Symbol = A | B | C | D

-- State transition function.
step :: State -> Symbol -> State
step S0 A = S1
step S0 B = S0
step S0 C = S0
step S0 D = S0
step S1 A = S1
step S1 B = S2
step S1 C = S0
step S1 D = S0
step S2 A = S3
step S2 B = S0
step S2 C = S1
step S2 D = S0
step S3 A = S1
step S3 B = S0
step S3 C = S4
step S3 D = S0
step S4 A = S1
step S4 B = S0
step S4 C = S0
step S4 D = S0

-- Run the state machine on a deterministic input stream.
runMachine :: State -> Int -> Int -> Int
runMachine state 0 count = count
runMachine state n count =
  let sym = symGen n
      nextState = step state sym
      newCount = case nextState of
                   S4 -> count + 1
                   _  -> count
  in runMachine nextState (n - 1) newCount

-- Deterministic symbol generator based on position.
symGen :: Int -> Symbol
symGen n = case mymod n 4 of
             0 -> A
             1 -> B
             2 -> C
             _ -> D

mymod :: Int -> Int -> Int
mymod a b = if a < b then a else mymod (a - b) b

main = putStrLn (show (runMachine S0 50000 0))