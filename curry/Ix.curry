-- $Id: Ix.curry 2876 2009-07-28 08:46:16Z wlux $
--
-- Copyright (c) 2000-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

module Ix where

class Ord a => Ix a where
  -- NB The following laws must hold for every instance of Ix
  --      range (l,u) !! index (l,u) i == i    -- when i is in range
  --      inRange (l,u) i == i `elem` range (l,u)
  --      map index (range (l,u)) == [0 .. rangeSize (l,u)]
  range :: (a,a) -> [a]
  index :: (a,a) -> a -> Int
  inRange :: (a,a) -> a -> Bool
  rangeSize :: (a,a) -> Int

  rangeSize b@(l,h) = if null (range b) then 0 else index b h + 1
  -- NB Replacing (null (range b)) by (not (l <= h)) fails if the
  --    bounds are tuples. For example (1,2) <= (2,1), but the range
  --    is nevertheless empty.

instance Ix Bool where
  range (b,b') = [b .. b']
  index b@(b',_) i
    | inRange b i = fromEnum i - fromEnum b'
  inRange (b,b') i = b <= i && i <= b'
  rangeSize (b,b') = if b <= b' then fromEnum b' - fromEnum b + 1 else 0

instance Ix Ordering where
  range (o,o') = [o .. o']
  index b@(o,_) i
    | inRange b i = fromEnum i - fromEnum o
  inRange (o,o') i = o <= i && i <= o'
  rangeSize (o,o') = if o <= o' then fromEnum o' - fromEnum o + 1 else 0

instance Ix Char where
  range (m,n) = [m .. n]
  index b@(c,_) i
    | inRange b i = fromEnum i - fromEnum c
  inRange (c,c') i = c <= i && i <= c'
  rangeSize (c,c') = if c <= c' then fromEnum c' - fromEnum c + 1 else 0

instance Ix Int where
  range (m,n) = [m .. n]
  index b@(m,_) i
    | inRange b i = i - m
  inRange (m,n) i = m <= i && i <= n
  rangeSize (m,n) = if m <= n then n - m + 1 else 0

instance Ix Integer where
  range (m,n) = [m .. n]
  index b@(m,_) i
    | inRange b i = fromInteger (i - m)
  inRange (m,n) i = m <= i && i <= n
  rangeSize (m,n) = if m <= n then fromInteger (n - m) + 1 else 0

instance Ix () where
  range (u,u') = [u .. u']
  index b@(u,_) i
    | inRange b i = fromEnum i - fromEnum u
  inRange (u,u') i = u <= i && i <= u
  rangeSize (u,u') = fromEnum u' - fromEnum u + 1

instance (Ix a,Ix b) => Ix (a,b) where
  range ((l1,l2),(u1,u2)) =
    [(i1,i2) | i1 <- range (l1,u1), i2 <- range (l2,u2)]
  index ((l1,l2),(u1,u2)) (i1,i2) =
    index (l1,u1) i1 * rangeSize (l2,u2) + index (l2,u2) i2
  inRange ((l1,l2),(u1,u2)) (i1,i2) =
    inRange (l1,u1) i1 && inRange (l2,u2) i2

instance (Ix a,Ix b,Ix c) => Ix (a,b,c) where
  range ((l1,l2,l3),(u1,u2,u3)) =
    [(i1,i2,i3) | i1 <- range (l1,u1), i2 <- range (l2,u2), i3 <- range (l3,u3)]
  index ((l1,l2,l3),(u1,u2,u3)) (i1,i2,i3) =
    (index (l1,u1) i1 * rangeSize (l2,u2) + index (l2,u2) i2) * rangeSize (l3,u3) + index (l3,u3) i3
  inRange ((l1,l2,l3),(u1,u2,u3)) (i1,i2,i3) =
    inRange (l1,u1) i1 && inRange (l2,u2) i2 && inRange (l3,u3) i3

instance (Ix a,Ix b,Ix c,Ix d) => Ix (a,b,c,d) where
  range ((l1,l2,l3,l4),(u1,u2,u3,u4)) =
    [(i1,i2,i3,i4) | i1 <- range (l1,u1), i2 <- range (l2,u2), i3 <- range (l3,u3), i4 <- range (l4,u4)]
  index ((l1,l2,l3,l4),(u1,u2,u3,u4)) (i1,i2,i3,i4) =
    ((index (l1,u1) i1 * rangeSize (l2,u2) + index (l2,u2) i2) * rangeSize (l3,u3) + index (l3,u3) i3) * rangeSize (l4,u4) + index (l4,u4) i4
  inRange ((l1,l2,l3,l4),(u1,u2,u3,u4)) (i1,i2,i3,i4) =
    inRange (l1,u1) i1 && inRange (l2,u2) i2 && inRange (l3,u3) i3 && inRange (l4,u4) i4

instance (Ix a,Ix b,Ix c,Ix d,Ix e) => Ix (a,b,c,d,e) where
  range ((l1,l2,l3,l4,l5),(u1,u2,u3,u4,u5)) =
    [(i1,i2,i3,i4,i5) | i1 <- range (l1,u1), i2 <- range (l2,u2), i3 <- range (l3,u3), i4 <- range (l4,u4), i5 <- range (l5,u5)]
  index ((l1,l2,l3,l4,l5),(u1,u2,u3,u4,u5)) (i1,i2,i3,i4,i5) =
    (((index (l1,u1) i1 * rangeSize (l2,u2) + index (l2,u2) i2) * rangeSize (l3,u3) + index (l3,u3) i3) * rangeSize (l4,u4) + index (l4,u4) i4) * rangeSize (l5,u5) + index (l5,u5) i5
  inRange ((l1,l2,l3,l4,l5),(u1,u2,u3,u4,u5)) (i1,i2,i3,i4,i5) =
    inRange (l1,u1) i1 && inRange (l2,u2) i2 && inRange (l3,u3) i3 && inRange (l4,u4) i4 && inRange (l5,u5) i5

instance (Ix a,Ix b,Ix c,Ix d,Ix e,Ix f) => Ix (a,b,c,d,e,f) where
  range ((l1,l2,l3,l4,l5,l6),(u1,u2,u3,u4,u5,u6)) =
    [(i1,i2,i3,i4,i5,i6) | i1 <- range (l1,u1), i2 <- range (l2,u2), i3 <- range (l3,u3), i4 <- range (l4,u4), i5 <- range (l5,u5), i6 <- range (l6,u6)]
  index ((l1,l2,l3,l4,l5,l6),(u1,u2,u3,u4,u5,u6)) (i1,i2,i3,i4,i5,i6) =
    ((((index (l1,u1) i1 * rangeSize (l2,u2) + index (l2,u2) i2) * rangeSize (l3,u3) + index (l3,u3) i3) * rangeSize (l4,u4) + index (l4,u4) i4) * rangeSize (l5,u5) + index (l5,u5) i5) * rangeSize (l6,u6) + index (l6,u6) i6
  inRange ((l1,l2,l3,l4,l5,l6),(u1,u2,u3,u4,u5,u6)) (i1,i2,i3,i4,i5,i6) =
    inRange (l1,u1) i1 && inRange (l2,u2) i2 && inRange (l3,u3) i3 && inRange (l4,u4) i4 && inRange (l5,u5) i5 && inRange (l6,u6) i6

instance (Ix a,Ix b,Ix c,Ix d,Ix e,Ix f,Ix g) => Ix (a,b,c,d,e,f,g) where
  range ((l1,l2,l3,l4,l5,l6,l7),(u1,u2,u3,u4,u5,u6,u7)) =
    [(i1,i2,i3,i4,i5,i6,i7) | i1 <- range (l1,u1), i2 <- range (l2,u2), i3 <- range (l3,u3), i4 <- range (l4,u4), i5 <- range (l5,u5), i6 <- range (l6,u6), i7 <- range (l7,u7)]
  index ((l1,l2,l3,l4,l5,l6,l7),(u1,u2,u3,u4,u5,u6,u7)) (i1,i2,i3,i4,i5,i6,i7) =
    (((((index (l1,u1) i1 * rangeSize (l2,u2) + index (l2,u2) i2) * rangeSize (l3,u3) + index (l3,u3) i3) * rangeSize (l4,u4) + index (l4,u4) i4) * rangeSize (l5,u5) + index (l5,u5) i5) * rangeSize (l6,u6) + index (l6,u6) i6) * rangeSize (l7,u7) + index (l7,u7) i7
  inRange ((l1,l2,l3,l4,l5,l6,l7),(u1,u2,u3,u4,u5,u6,u7)) (i1,i2,i3,i4,i5,i6,i7) =
    inRange (l1,u1) i1 && inRange (l2,u2) i2 && inRange (l3,u3) i3 && inRange (l4,u4) i4 && inRange (l5,u5) i5 && inRange (l6,u6) i6 && inRange (l7,u7) i7
