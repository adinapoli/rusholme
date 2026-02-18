-- GHC testsuite: instances with constraints, overlapping-safe instances
module Sc023TypeClassesInstances where

-- Basic instance
class Printable a where
    display :: a -> String

data Color = Red | Green | Blue

instance Printable Color where
    display Red   = "red"
    display Green = "green"
    display Blue  = "blue"

-- Instance for parameterised type
instance Printable a => Printable (Maybe a) where
    display Nothing  = "nothing"
    display (Just x) = "just(" ++ display x ++ ")"

-- Instance for list
instance Printable a => Printable [a] where
    display []     = "[]"
    display (x:xs) = display x ++ ":" ++ display xs

-- Instance for tuple
instance (Printable a, Printable b) => Printable (a, b) where
    display (a, b) = "(" ++ display a ++ ", " ++ display b ++ ")"

-- Multiple class instance
class (Show a, Eq a) => SafeShow a where
    safeShow :: a -> Maybe String
    safeShow x = Just (show x)

instance SafeShow Int
instance SafeShow Bool
instance SafeShow Char

-- Class with functional dependency (syntax only)
class MyCollection c e | c -> e where
    myEmpty  :: c
    myInsert :: e -> c -> c
    myMember :: e -> c -> Bool
