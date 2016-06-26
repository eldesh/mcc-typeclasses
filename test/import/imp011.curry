-- This example checks that the compiler correctly recognizes that the
-- occurrences of A.Pair in the interfaces of B and C are considered
-- equal. The important point is that A.Pair is reexported explicitly
-- from B but only implicitly from C. Thus, a newtype declaration occurs
-- in B's interface and a (hidden) data type declaration in C's
-- interface.

import B
import C
main = print (left p,right p)
  where p = mkPair 0 'a'
