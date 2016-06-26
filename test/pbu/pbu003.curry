-- This example demonstrates how pattern binding updates can introduce
-- indirection nodes that point to an unevaluated application node.
-- Note: While this particular example is contrived, such updates are
-- much more likely when stability is enabled. See also pbu002.curry
-- for a variant of this example.

main = doSolve (x=:=x & r=:=y+1 & z=:=0) >> print r
  where (x,y) = ensureNotFree z=:=0 &> (r+1, 1+1)
        r,z free
