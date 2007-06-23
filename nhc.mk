# Specific rules for building with nhc
# $Id: nhc.mk 2371 2007-06-23 14:08:14Z wlux $
#
# Copyright (c) 2002-2007, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for nhc
HMAKE = hmake -nhc98
NHC_HCFLAGS = +CTS -H8M -CTS -Inhc -I$(HC_PATH_STYLE)

# programs
cycc: $(cycc_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@
cymk: $(cymk_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@
newer: $(newer_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@
cam2c: $(cam2c_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@
mach: $(mach_SRCS)
	@case "$(MFLAGS)" in -*s*) q=-q;; *) q=;; esac; \
	$(HMAKE) $$q $(HCFLAGS) $(NHC_HCFLAGS) $@

# compute the dependencies
depend-dir:
	@: Do not delete this line
