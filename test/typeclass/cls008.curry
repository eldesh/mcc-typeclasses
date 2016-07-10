-- This little example mixes omitted and implemented default and
-- instance methods. Furthermore, some of the (default) method
-- implementation requires the class/instance context, while others
-- don't.

class Coin a where
  zero, one :: a
  coin :: a

  -- NB zero's type is Coin a => a, however the default implementation
  --    does not need the class dictionary
  zero = error "zero"
  coin = zero ? one

instance Coin Bool where
  coin = False
  coin = True

instance Coin Int where
  coin = 0
  coin = 1

instance (Coin a,Coin b) => Coin (a,b) where
  -- NB coin's implementation is such that it does not use the
  --    dictionaries of the tuple's argument types.
  coin = (undefined,undefined)

instance Coin a => Coin (Maybe a) where
  coin = Nothing
  coin = Just coin
