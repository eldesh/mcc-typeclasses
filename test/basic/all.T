eval pass test001.curry coin
eval fail test001.curry failed
eval pass test001.curry xs ++ ys =:= [1..3] where xs,ys free
type pass test001.curry coin
type fail test001.curry 'a' + 'b'
eval fail test002.curry goal1
eval fail test002.curry goal2
eval fail test002.curry goal3
eval pass test003.curry goal1
eval pass test003.curry goal2
eval fail test003.curry goal3
eval fail test003.curry goal4
