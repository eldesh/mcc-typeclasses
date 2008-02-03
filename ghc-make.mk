# Specific rules for building with ghc --make
# $Id: ghc-make.mk 2611 2008-02-03 23:35:16Z wlux $
#
# Copyright (c) 2002-2008, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for ghc
GHC_HFLAGS = -H12m -i$(HC_PATH_STYLE)

# programs
cycc: $(cycc_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-v0;; *) s=;; esac; \
	$(HC) --make $(HFLAGS) $(GHC_HFLAGS) $$s -o $@ $@
cymk: $(cymk_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-v0;; *) s=;; esac; \
	$(HC) --make $(HFLAGS) $(GHC_HFLAGS) $$s -o $@ $@
newer: $(newer_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-v0;; *) s=;; esac; \
	$(HC) --make $(HFLAGS) $(GHC_HFLAGS) $$s -o $@ $@
cam2c: $(cam2c_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-v0;; *) s=;; esac; \
	$(HC) --make $(HFLAGS) $(GHC_HFLAGS) $$s -o $@ $@
mach: $(mach_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-v0;; *) s=;; esac; \
	$(HC) --make $(HFLAGS) $(GHC_HFLAGS) $$s -o $@ $@

# compute the dependencies
depend-dir:
	@: Do not delete this line
