-- Here is an example using a top-level as-pattern
main = (x,y,xy) where xy@(x,y) = head (zip [0..] "abc")
