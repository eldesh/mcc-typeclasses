-- This is a subtle test introducing a derived instance where part of
-- the derived instance's context is not in scope
-- NB The Prelude's import specification is chosen in such way that
--    all functions used in the derived instance declaration are in
--    scope

import Prelude((.), Ord(..), Show(..), showParen, showString)
import A

data T a = T (N a) deriving Show
