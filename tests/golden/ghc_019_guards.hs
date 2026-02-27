module Guards where

data Color = Red | Green | Blue

-- Guard with otherwise fallback
describeColor :: Color -> String
describeColor c
  | isRed c   = "red"
  | otherwise = "not red"

isRed :: Color -> Bool
isRed Red = True
isRed _   = False

-- otherwise-only guard (trivially true)
alwaysYes :: Int -> String
alwaysYes _
  | otherwise = "yes"
