-- The record syntax cannot be combined with existentially quantified
-- types because the type variables escape their scope with the types of
-- the selector functions.

module rec009(Key) where
data Key a = forall b . Key{ val :: b, key :: b -> a }

