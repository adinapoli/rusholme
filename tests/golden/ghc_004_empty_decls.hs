module Ghc004EmptyDecls where {

f x = x;
;
;
g y z = z;

main = print (g (f False) (f True));
}
