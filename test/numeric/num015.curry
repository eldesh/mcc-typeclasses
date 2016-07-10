-- Another test with overloading numeric literals testing that multiple
-- occurrences of a numeric literal are handled correctly.

f xy =
  case xy of
    (0,y) | y > 0 -> 'a'
    (x,0) | x > 0 -> 'b'
    (0,_)         -> 'c'
    (_,0)         -> 'd'
    _             -> 'e'

main = print (map f [(x,y) | x <- [-1,0,1], y <- [-1,0,1]])

