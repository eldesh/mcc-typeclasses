-- This test checks that local module aliases are resolved correctly

module imp019 where
import A as imp019 {-sic!-}

class C a where
  h :: a -> Success

-- NB we cannot declare a type signature for test (nor an instance of
--    class C) because both C and imp019.C are ambiguous. However, the
--    method name h is unambiguous and therefore the definition should
--    be accepted
test x | h x = 0
