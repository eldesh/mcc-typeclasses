# Specific rules for building with ghc
# $Id: ghc.mk 2611 2008-02-03 23:35:16Z wlux $
#
# Copyright (c) 2002-2008, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for ghc
GHC_HFLAGS = -H12m -i$(HC_PATH_STYLE)

# additional suffix rules
.SUFFIXES: .hs .lhs .hi .o
.hs.o:
	$(HC) $(HFLAGS) $(GHC_HFLAGS) $($*_HFLAGS) -c $< -o $@
.lhs.o:
	$(HC) $(HFLAGS) $(GHC_HFLAGS) $($*_HFLAGS) -c $< -o $@
.o.hi:
	@test -f $@ || \
	(echo "$@ does not exist!"; \
	 echo "Remove $< and run make again."; exit 1)

# programs
cycc: $(cycc_OBJS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -o $@ $(cycc_OBJS)
cymk: $(cymk_OBJS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -o $@ $(cymk_OBJS)
newer: $(newer_OBJS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -o $@ $(newer_OBJS)
cam2c: $(cam2c_OBJS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -o $@ $(cam2c_OBJS)
mach: $(mach_OBJS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -o $@ $(mach_OBJS)

# additional cleanup rules
mostlyclean-dir::
	-rm -f Main.hi

# compute the dependencies
# NB: ./ prefixes stripped from dependencies for proper operation with BSD make
depend-dir: $(SRCS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -M -optdep-f -optdep.depend.cycc $(cycc_SRCS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -M -optdep-f -optdep.depend.cymk $(cymk_SRCS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -M -optdep-f -optdep.depend.newer $(newer_SRCS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -M -optdep-f -optdep.depend.cam2c $(cam2c_SRCS)
	$(HC) $(HFLAGS) $(GHC_HFLAGS) -M -optdep-f -optdep.depend.mach $(mach_SRCS)
	sed 's,\./,,' .depend.cycc .depend.cymk .depend.newer .depend.mach .depend.cam2c > .depend
	@rm -f -- .depend.cycc .depend.cymk .depend.newer .depend.cam2c .depend.mach
	@rm -f -- .depend.cycc.bak .depend.cymk.bak .depend.newer.bak .depend.cam2c.bak .depend.mach.bak
