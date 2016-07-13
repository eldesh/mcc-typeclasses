module B where
import A

class C a where
  f :: a -> Bool

instance C T where
  f T = True
