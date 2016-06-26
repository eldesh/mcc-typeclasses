-- This example demonstrates that function patterns in pattern
-- declarations can use functions defined in the same declaration
-- group. Note that the parentheses around (dup z) are necessary to
-- make this declaration a pattern declaration.

main = print z
  where dup x = (x,x); (dup z) = (1,1)
