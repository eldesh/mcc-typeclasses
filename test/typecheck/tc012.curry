-- fails because of a missing instance for Ord (() -> Bool)
bogus b f = x
  where x = if b then f <= f else f ()
