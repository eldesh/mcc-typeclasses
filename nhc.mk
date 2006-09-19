# Specific rules for building with nhc
# $Id: nhc.mk 1830 2005-11-09 17:09:12Z wlux $
#
# Copyright (c) 2002-2005, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for nhc
HMAKE = hmake -nhc98
NHC_HCFLAGS = +CTS -H8M -CTS -Inhc

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
