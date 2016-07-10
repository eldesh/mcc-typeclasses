-- This test checks that local infix declarations for class methods
-- are exported

import A

instance Equal Bool where
  False === False = True
  False === True = False
  True === False = False
  True === True = True

instance Equal a => Equal [a] where
  [] === [] = True
  _:_ === [] = False
  [] === _:_ = False
  x:xs === y:ys = x===y && xs===ys
