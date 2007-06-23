# Specific rules for building with ghc
# $Id: ghc.mk 2371 2007-06-23 14:08:14Z wlux $
#
# Copyright (c) 2002-2007, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for ghc
GHC_HCFLAGS = -H12m -i$(HC_PATH_STYLE)

# additional suffix rules
.SUFFIXES: .hs .lhs .hi .o
.hs.o:
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) $($*_HCFLAGS) -c $< -o $@
.lhs.o:
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) $($*_HCFLAGS) -c $< -o $@
.o.hi:
	@test -f $@ || \
	(echo "$@ does not exist!"; \
	 echo "Remove $< and run make again."; exit 1)

# programs
cycc: $(cycc_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(cycc_OBJS)
cymk: $(cymk_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(cymk_OBJS)
newer: $(newer_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(newer_OBJS)
cam2c: $(cam2c_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(cam2c_OBJS)
mach: $(mach_OBJS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -o $@ $(mach_OBJS)

# additional cleanup rules
mostlyclean-dir::
	-rm -f Main.hi

# compute the dependencies
# NB: ./ prefixes stripped from dependencies for proper operation with BSD make
depend-dir: $(SRCS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -M -optdep-f -optdep.depend.cycc $(cycc_SRCS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -M -optdep-f -optdep.depend.cymk $(cymk_SRCS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -M -optdep-f -optdep.depend.newer $(newer_SRCS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -M -optdep-f -optdep.depend.cam2c $(cam2c_SRCS)
	$(HC) $(HCFLAGS) $(GHC_HCFLAGS) -M -optdep-f -optdep.depend.mach $(mach_SRCS)
	sed 's,\./,,' .depend.cycc .depend.cymk .depend.newer .depend.mach .depend.cam2c > .depend
	@rm -f -- .depend.cycc .depend.cymk .depend.newer .depend.cam2c .depend.mach
	@rm -f -- .depend.cycc.bak .depend.cymk.bak .depend.newer.bak .depend.cam2c.bak .depend.mach.bak
