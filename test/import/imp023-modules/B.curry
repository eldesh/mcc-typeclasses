module B where
import A

class C a where
  f :: a -> Success

instance C T where
  f T = success
