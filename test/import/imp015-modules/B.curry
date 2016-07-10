-- This module deliberately omits constructor B in order to verify
-- that contexts on the left hand side of data type are correctly
-- sorted in interfaces
module B(T(O, BO)) where
import A
