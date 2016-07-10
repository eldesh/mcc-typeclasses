-- This is another example from the Haskell report. It shows that
-- kind defaults are chosen without regard to any uses of a type
-- in later declaration groups (cf. Sect. 4.6 of the Haskell'98
-- report).

-- Kind inference assigns kinds (*->*)->*->* and *->* to App and
-- Tree, respectively. Note that both could be used at any kind
-- of the form (k->*)->k->* and k->*.
data App f a = A (f a)
data Tree a  = Leaf | Fork (Tree a) (Tree a)

-- This is illegal because it uses Tree with kind (*->*)->*.
-- Strangely enough, this type could be made legal by making
-- the type definition part of a declaration group including
-- the Tree type, e.g., by adding a third case Unused FunnyTree
-- to the declaration.
type FunnyTree = Tree []
