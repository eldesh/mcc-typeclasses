-- Simple context for an existentially quantified variable

data Showable = forall a . Show a => Showable a

instance Show Showable where
  showsPrec p (Showable x) = showsPrec p x

main = mapM_ print [Showable "abc", Showable (Just 123), Showable ((),False,1.0)]
