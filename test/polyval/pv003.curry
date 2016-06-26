-- Here is an example where polymorphic generalization of a variable
-- is not accepted (even though it would be sound in this case)
-- because the declaration's right hand side is an expansive
-- expression.
main = ((1::Int):nil, 'a':nil)
  where nil = id []
