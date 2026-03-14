module Sc049Minimal where

infixl 5 <+>
(x:xs) <+> ys = x : (xs <+> ys)
