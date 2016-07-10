-- This test is supposed to check that method types are re-exported
-- correctly in interfaces. This is particularly important as long as
-- long the compiler saves contexts in expanded form, i.e., all
-- super class predicates are made explicit.
import B

main = g 1
