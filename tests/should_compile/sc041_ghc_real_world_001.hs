-- Real-world style: a simple state machine
module Sc041GhcRealWorld001 where

data State = Idle | Running | Paused | Done
    deriving (Show, Eq, Ord, Enum, Bounded)

data Event = Start | Pause | Resume | Stop
    deriving (Show, Eq)

transition :: State -> Event -> Maybe State
transition Idle    Start  = Just Running
transition Running Pause  = Just Paused
transition Running Stop   = Just Done
transition Paused  Resume = Just Running
transition Paused  Stop   = Just Done
transition _       _      = Nothing

runMachine :: State -> [Event] -> [State]
runMachine _ []     = []
runMachine s (e:es) =
    case transition s e of
        Nothing -> runMachine s es
        Just s' -> s' : runMachine s' es

-- All reachable states from initial
reachable :: State -> [Event] -> [State]
reachable s0 alphabet = go [s0] [s0]
  where
    go []     visited = visited
    go (s:queue) visited =
        let next    = [s' | e <- alphabet
                           , Just s' <- [transition s e]
                           , s' `notElem` visited]
        in go (queue ++ next) (visited ++ next)
