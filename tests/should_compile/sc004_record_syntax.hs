-- GHC testsuite: record syntax
module Sc004RecordSyntax where

data Point = Point
    { x :: Int
    , y :: Int
    } deriving (Show, Eq)

data Person = Person
    { personName :: String
    , personAge  :: Int
    , personAddr :: Maybe String
    } deriving (Show)

-- Record construction
origin :: Point
origin = Point { x = 0, y = 0 }

-- Record update syntax
moveRight :: Point -> Int -> Point
moveRight p dx = p { x = x p + dx }

-- Record in patterns
getX :: Point -> Int
getX Point { x = n } = n
