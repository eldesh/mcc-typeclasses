-- fails because of a missing instance for Ord (() -> Bool)
bogus b f = x
  {- NB deliberately using a guarded definition -}
  where x | b = f <= f
          | otherwise = f ()
