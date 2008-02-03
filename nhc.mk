# Specific rules for building with nhc
# $Id: nhc.mk 2611 2008-02-03 23:35:16Z wlux $
#
# Copyright (c) 2002-2008, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for nhc
HMAKE = hmake
NHC_HFLAGS = -nhc98 +CTS -H8M -CTS -Inhc -I$(HC_PATH_STYLE)

# programs
cycc: $(cycc_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HFLAGS) $(NHC_HFLAGS) $@
cymk: $(cymk_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HFLAGS) $(NHC_HFLAGS) $@
newer: $(newer_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HFLAGS) $(NHC_HFLAGS) $@
cam2c: $(cam2c_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HFLAGS) $(NHC_HFLAGS) $@
mach: $(mach_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HFLAGS) $(NHC_HFLAGS) $@

# compute the dependencies
depend-dir:
	@: Do not delete this line
