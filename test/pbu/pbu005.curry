-- In this example, multiple threads start evaluating components of the
-- same pattern binding.

f xys = head xs =:= 1 & head ys =:= 2
  where (xs,ys) = unzip xys

main | f (ensureNotFree xys) & xys =:= [(unknown,unknown)] = print xys
  where xys free
