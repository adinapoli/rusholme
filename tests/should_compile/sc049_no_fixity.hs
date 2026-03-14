module Sc049NoFixity where

(x:xs) <+> ys = x : (xs <+> ys)
