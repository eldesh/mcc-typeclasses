-- In this example we check that function patterns can be mixed with
-- constrained variables

diff x y | x =/= y = (x,y)

f (diff x y) = (x,y)

g (0,0) = 'a'
g (0,1) = 'b'
g (1,0) = 'c'
g (1,1) = 'd'

main = print (findall (\c -> c =:= g (f (unknown,unknown))))
