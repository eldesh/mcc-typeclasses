-- Here is a rather artificial example that checks that nested lazy
-- patterns are transformed correctly. Note that by the way f's result is
-- fed back to itself in the main function, the program will deadlock if
-- any of the lazy patterns is converted into a non-lazy pattern.

f ~(x : ~(y : ~(z : _))) = guard 1 $ guard x $ guard y $ guard z []
  where guard x xs = if x > 0 then x : xs else []

main = print l where l = f l
