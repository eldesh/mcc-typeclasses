# Specific rules for building with hbc
# $Id: hbc.mk 2611 2008-02-03 23:35:16Z wlux $
#
# Copyright (c) 2002-2008, Wolfgang Lux
# See LICENSE for the full license.
#

# specific definitions for hbc
HBCMAKE = hbcmake
HBC_HFLAGS = -f $(srcdir)/hbc.mk -I hbc -I $(HC_PATH_STYLE)
HBCFLAGS = -H24m -noflags

# programs
cycc: $(cycc_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HFLAGS) $(HBC_HFLAGS) $@
cymk: $(cymk_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HFLAGS) $(HBC_HFLAGS) $@
newer: $(newer_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HFLAGS) $(HBC_HFLAGS) $@
cam2c: $(cam2c_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HFLAGS) $(HBC_HFLAGS) $@
mach: $(mach_SRCS)
	@case "$(MFLAGS)" in -*s*) s=-s;; *) s=;; esac; \
	HBC=$(HC) $(HBCMAKE) $$s $(HFLAGS) $(HBC_HFLAGS) $@

# compute the dependencies
depend-dir:
	@: Do not delete this line
