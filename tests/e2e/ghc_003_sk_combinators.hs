-- S and K combinators
main = print (id2 (id2 id2) (42::Int))

id2 = s k k

s x y z = x z (y z)

k x y = x
