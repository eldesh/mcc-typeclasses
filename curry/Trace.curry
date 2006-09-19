-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

-- Re-export trace function for compatibility with earlier release
-- of the Münster Curry compiler and Hugs

module Trace(trace) where
import Unsafe(trace)
