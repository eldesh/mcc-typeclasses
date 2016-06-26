-- This is a rather tough example; the field labels hd and tl are
-- exported from A, but their type List isn't. Hugs and ghc can compile
-- this example, hbc and nhc98 complain that hd and tl are not field
-- labels (hbc in addition requires that the List type is exported).

module rec016 where
import A

swap l
  | isNil l || isNil (tl l) = l
  | otherwise = l{ hd = hd (tl l), tl = hd l `cons` tl (tl l) }
