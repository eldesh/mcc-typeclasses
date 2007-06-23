# Specific rules for building with hbc
# $Id: hbc.mk 2371 2007-06-23 14:08:14Z wlux $
#
# Copyright (c) 2002-2007, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for hbc
HBCMAKE = hbcmake -f $(srcdir)/hbc.mk
HBC_HCFLAGS = -I hbc -I $(HC_PATH_STYLE)
HBCFLAGS = -H24m -noflags -s

# programs
cycc: $(cycc_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@
cymk: $(cymk_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@
newer: $(newer_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@
cam2c: $(cam2c_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@
mach: $(mach_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HCFLAGS) $(HBC_HCFLAGS) $@

# compute the dependencies
depend-dir:
	@: Do not delete this line
