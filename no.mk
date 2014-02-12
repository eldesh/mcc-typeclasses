# Specific rules for building without a Haskell compiler
# NB This is intended to be used only for creating source distributions
# $Id: no.mk 3150 2014-02-12 17:58:48Z wlux $
#
# Copyright (c) 2013, Wolfgang Lux
# See LICENSE for the full license.
#

# programs
# We cannot build any programs without a Haskell compiler.
cycc:
	@echo This configuration only supports the dist target; exit 1
cymk:
	@echo This configuration only supports the dist target; exit 1
newer:
	@echo This configuration only supports the dist target; exit 1
cam2c:
	@echo This configuration only supports the dist target; exit 1
mach:
	@echo This configuration only supports the dist target; exit 1

# compute the dependencies
depend-dir:
	@: Do not delete this line
