# $Id: aclocal.m4 2371 2007-06-23 14:08:14Z wlux $
#
# Copyright (c) 2002-2007, Wolfgang Lux
#

########################################################################
# shell stuff

# CURRY_CHECK_RAW_READ(SHELL,ACTION-IF-TRUE,[ACTION-IF-FALSE])
# Checks whether the specified shell suppports raw reads.
# If so execute ACTION-IF-TRUE, other ACTION-IF-FALSE.

AC_DEFUN([CURRY_CHECK_RAW_READ],
[AC_CACHE_CHECK([whether $$1 supports raw read],[curry_cv_prog_$1_read_r],
[curry_cv_prog_$1_read_r=no
# first try if read is raw (ash), next if read -r works (POSIX sh, ksh, bash)
for curry_read_r in read "read -r"; do
  cat >conftest.sh <<EOF
#!$$1
input='foo\\nbar'
$curry_read_r line <<eof
\$input
eof
test "\$input" = "\$line"
EOF
  chmod +x conftest.sh
  if ./conftest.sh 2>/dev/null; then
    curry_cv_prog_$1_read_r="$curry_read_r"
    break;
  fi
done
rm -f conftest.sh])
case $curry_cv_prog_$1_read_r in
  no ) $3;;
  * ) curry_read_r="$curry_cv_prog_$1_read_r"; $2;;
esac])


# CURRY_RAW_SHELL
# Check for a shell that supports raw reads set the variable
# RAW_SHELL to the absolute path of this shell and AC_SUBST
# this variable.

AC_DEFUN([CURRY_RAW_SHELL_SH],
[SH=/bin/sh; CURRY_CHECK_RAW_READ(SH,[RAW_SHELL=/bin/sh])])

AC_DEFUN([CURRY_RAW_SHELL_KSH],
[AC_PATH_PROG(KSH, ksh)
case $KSH in
  "" ) ;;
  * ) CURRY_CHECK_RAW_READ(KSH,[RAW_SHELL="$KSH"]);;
esac])

AC_DEFUN([CURRY_RAW_SHELL_BASH],
[AC_PATH_PROG(BASH, bash)
case $BASH in
  "" ) ;;
  * ) CURRY_CHECK_RAW_READ(BASH,[RAW_SHELL="$BASH"]);;
esac])

AC_DEFUN([CURRY_RAW_SHELL_ALT_SH],
[AC_CHECK_PROG(ALT_SH, sh, yes, no, $PATH, /bin/sh)
case ALT_SH in
  yes ) unset ALT_SH; AC_PATH_PROG(ALT_SH, sh)
        CURRY_CHECK_RAW_READ(ALT_SH,[RAW_SHELL="$ALT_SH"]);;
  no ) unset ALT_SH;;
  * ) CURRY_CHECK_RAW_READ(ALT_SH,[RAW_SHELL="$ALT_SH"]);;
esac])

AC_DEFUN([CURRY_RAW_SHELL],
[AC_MSG_CHECKING([for a shell that supports raw read])
AC_MSG_RESULT([])
RAW_SHELL=; CURRY_RAW_SHELL_SH
if test -z "$RAW_SHELL"; then CURRY_RAW_SHELL_KSH; fi
if test -z "$RAW_SHELL"; then CURRY_RAW_SHELL_BASH; fi
if test -z "$RAW_SHELL"; then CURRY_RAW_SHELL_ALT_SH; fi
case $RAW_SHELL in
  "" ) AC_MSG_WARN([Could not find any shell which supports raw read])
       AC_MSG_WARN([Falling back to /bin/sh. You will have to escape])
       AC_MSG_WARN([backslashes in the interactive environment])
       RAW_SHELL=/bin/sh
       ;;
  * ) AC_MSG_RESULT([Using $RAW_SHELL for the interactive environment])
esac
AC_SUBST(RAW_SHELL)])


# CURRY_CYI_SHELL
# Check for a shell that is suitable for cyi. Set the variable
# CYI_SHELL to the absolute path of the selected shell program
# and AC_SUBST this variable.
#
# At present, only GNU Bash, the AT&T Korn shell, and Z shell
# support command line editing in read commands and therefore are
# preferred for cyi.

AC_DEFUN([CURRY_CYI_SHELL],[
if test -n "${CYI_SHELL+set}"; then
  # protect against bogus CYI_SHELL settings
  if ! test -x $CYI_SHELL; then
    AC_MSG_ERROR([$CYI_SHELL does not exist or is not executable])
  elif ! $CYI_SHELL -c 'test -n "${HOME+set}"' >/dev/null 2>&1; then
    AC_MSG_ERROR([$CYI_SHELL is not compatible with a Bourne shell])
  fi
else
  AC_MSG_CHECKING([whether /bin/sh is suitable for cyi])
  if /bin/sh -c 'test -n "${BASH_VERSION+set}"'; then
    AC_MSG_RESULT([yes (GNU Bash)])
    CYI_SHELL=/bin/sh
  elif /bin/sh -c 'test -n "${ZSH_VERSION+set}"'; then
    AC_MSG_RESULT([yes (Z shell)])
    CYI_SHELL=/bin/sh
  # Is there a better way to identify the AT&T Korn shell? Note that
  # bash as well as zsh define RANDOM, too. In fact, any Posix-compliant
  # shell will do so.
  elif /bin/sh -c 'test -n "${RANDOM+set}" && test -z "${KSH_VERSION+set}"'; then
    AC_MSG_RESULT([yes (Korn shell)])
    CYI_SHELL=/bin/sh
  else
    AC_MSG_RESULT([no])
    AC_PATH_PROGS(CYI_SHELL, [bash ksh zsh])
    if test -z "$CYI_SHELL"; then
      AC_MSG_NOTICE([falling back to /bin/sh])
      CYI_SHELL=/bin/sh
    fi
  fi
fi

if $CYI_SHELL -c 'test -n "${ZSH_VERSION+set}"'; then
  AC_MSG_WARN([Command line history will not work in cyi.])
elif $CYI_SHELL -c 'test -z "${RANDOM+set}"'; then
  AC_MSG_WARN([Command line editing will not work in cyi.

You should consider installing GNU Bash or the AT&T Korn shell.
])
  CURRY_CHECK_RAW_READ(CYI_SHELL,,
    AC_MSG_WARN([$CYI_SHELL does not support raw read

You will have to escape backslashes when entering goals in cyi.
]))
elif $CYI_SHELL -c 'test -n "${KSH_VERSION+set}"'; then
  AC_MSG_WARN([Command line editing may not work in cyi.

You should consider installing GNU Bash or the AT&T Korn shell.
Make sure that the latter is found in the path before $CYI_SHELL
or set the environment variable CYI_SHELL.
])
fi

AC_SUBST(CYI_SHELL)])

########################################################################
# Haskell compiler

# CURRY_HC_HASKELL98(HC,[ACTION-IF-TRUE],[ACTION-IF-FALSE])
# Check whether Haskell compiler HC compiles Haskell 98
AC_DEFUN([CURRY_HC_HASKELL98],
[AC_CACHE_CHECK([whether $$1 supports Haskell 98],
[curry_cv_prog_$1_haskell98],
[curry_cv_prog_$1_haskell98=no
# Check whether Char.isAlphaNum is available. This function was
# called isAlphanum in the pre Haskell 98 days.
cat <<EOF >conftest.hs
import Char
main = print (isAlphaNum 'a')
EOF
$$1 conftest.hs -o conftest 2>/dev/null && curry_cv_prog_$1_haskell98=yes
rm -f conftest* Main.hi])
case $curry_cv_prog_$1_haskell98 in
  yes ) $2;;
  no ) $3;;
esac])

# CURRY_PROG_GHC, CURRY_PROG_HBC, CURRY_PROG_NHC
# Check for ghc, hbc, nhc compiler in the path which handles Haskell 98
# Set the variables GHC, HBC, and NHC, resp. and AC_SUBST the variable

AC_DEFUN([CURRY_GHC_VERSION],
[AC_CACHE_CHECK([ghc version],[curry_cv_prog_ghc_version],
[curry_ghc_version=`$GHC --version 2>&1`
curry_cv_prog_ghc_version=`expr "$curry_ghc_version" : '.*version \([[0-9]]*.[[0-9]]*\)'`
test -n "$curry_cv_prog_ghc_version" || unset curry_cv_prog_ghc_version])])

AC_DEFUN([CURRY_HBC_VERSION],
[AC_CACHE_CHECK([hbc version],[curry_cv_prog_hbc_version],
[# NB: hbc 0.9999.3 and earlier do not support -v. Who cares?
curry_hbc_version=`$HBC -v 2>&1`
curry_cv_prog_hbc_version=`expr "$curry_hbc_version" : '.*version \(0.9999.[[0-9]]*\)'`
test -n "$curry_cv_prog_hbc_version" || unset curry_cv_prog_hbc_version])])

AC_DEFUN([CURRY_NHC_VERSION],
[AC_CACHE_CHECK([nhc version],[curry_cv_prog_nhc_version],
[# NB: most versions of nhc 1.3 do not support -v. Who cares?
curry_nhc_version=`$NHC --version 2>&1`
curry_cv_prog_nhc_version=`expr "$curry_nhc_version" : '.*: v\([[0-9]]*\.[[0-9]][[0-9]]*\)'`
test -n "$curry_cv_prog_nhc_version" || unset curry_cv_prog_nhc_version])])

AC_DEFUN([CURRY_PROG_GHC],
[AC_CHECK_PROG(GHC, ghc, ghc)
if test -n "$GHC"; then
  CURRY_GHC_VERSION(GHC)
  CURRY_HC_HASKELL98(GHC,[],[GHC=])
fi])

AC_DEFUN([CURRY_PROG_HBC],
[AC_CHECK_PROG(HBC, hbc, hbc)
if test -n "$HBC"; then
  CURRY_HBC_VERSION(HBC)
  CURRY_HC_HASKELL98(HBC,[],[HBC=])
fi])

AC_DEFUN([CURRY_PROG_NHC],
[AC_CHECK_PROGS(NHC, [nhc98 nhc])
if test -n "$NHC"; then
  CURRY_NHC_VERSION(NHC)
  CURRY_HC_HASKELL98(NHC,[],[NHC=])
fi])


# CURRY_HC_VERSION(HC)
# Check whether HC is one of the supported compilers and set either
# GHC, HBC, or NHC to this compiler
AC_DEFUN([CURRY_HC_VERSION],
[AC_MSG_CHECKING([Haskell compiler version])
cat <<EOF >conftest.hs
main = putStr (
#ifdef __GLASGOW_HASKELL__
  "ghc " ++ show (__GLASGOW_HASKELL__/100)
#endif
#ifdef __HBC__
# if __HASKELL1__==5
  "hbc 0.9999.5"
# else
#  ifdef __HASKELL_1_3__
  "hbc 0.9999.4"
#  else
  "hbc 0.9999.3"
#  endif
# endif
#endif
#ifdef __NHC__
# if __HASKELL__==3
  "nhc13"
# endif
# if __HASKELL__==98
  "nhc98"
# endif
#endif
  )
EOF
rm -f conftest; $$1 -cpp conftest.hs -o conftest 2>/dev/null; rm -f Main.hi
if curry_hc_version=`./conftest 2>/dev/null`; then
  AC_MSG_RESULT([$curry_hc_version])
else
  AC_MSG_ERROR([cannot determine version of $$1])
fi
rm -f conftest* Main.hi
CURRY_HC_HASKELL98([$1],
[# do not cache the result for this variable
unset curry_cv_prog_$1_haskell98
case $curry_hc_version in
  ghc* ) GHC=$$1; HBC=; NHC=;;
  hbc* ) HBC=$$1; GHC=; NHC=;;
  nhc* ) NHC=$$1; GHC=; HBC=;;
esac],
[GHC= HBC= NHC=])])

# CURRY_HC_HLIB(HC,[ACTION-IF-TRUE],[ACTION-IF-FALSE])
# Checks whether HC supports the standard hierarchical libraries.
# This should be true for ghc 5.x and later as well as nhc98 1.16 and later.
AC_DEFUN([CURRY_HC_HLIB],
[AC_CACHE_CHECK([whether $$1 supports the standard hierarchical libraries],
[curry_cv_prog_$1_hlib],
[curry_cv_prog_$1_hlib=no
cat <<EOF >ConfTest.hs
module ConfTest(module Data.IORef) where
import Data.IORef
EOF
$$1 -c ConfTest.hs 2>/dev/null && curry_cv_prog_$1_hlib=yes
rm -f ConfTest*])
case $curry_cv_prog_$1_hlib in
  yes ) $2;;
  no ) $3;;
esac])

# CURRY_GHC_IOEXTS
# Check how to import IOExts when compiling with ghc
# and add the appropriate switches to the variable HCFLAGS
# NB this should be used only for ghc version 4.x or earlier;
#    on later versions of ghc Data.IORef should be used instead
#    of IOExts
AC_DEFUN([CURRY_GHC_IOEXTS],
[AC_MSG_CHECKING([how to import IOExts])
cat >conftest.hs <<EOF
import IOExts
main = newIORef () >>= flip writeIORef ()
EOF
curry_ghc_ioexts_lib=
for lib in exts lang; do
  if $GHC $HCFLAGS -syslib $lib -c conftest.hs 2>/dev/null; then
    curry_ghc_ioexts_lib="-syslib $lib"
    break
  fi
done
rm -f conftest* Main.hi
case $curry_ghc_ioexts_lib in
  "" ) AC_MSG_ERROR([cannot determine how to import IOExts]);;
  * )
    AC_MSG_RESULT([$curry_ghc_ioexts_lib])
    HCFLAGS="$HCFLAGS $curry_ghc_ioexts_lib"
    ;;
esac])

# CURRY_HC_PATH_STYLE
# Checks whether Haskell compiler HC understands Posix-style paths
# Sets the variable HC_PATH_STYLE to posix if Posix-style paths can
# be used and to windows yet otherwise
AC_DEFUN([CURRY_HC_PATH_STYLE],
[AC_MSG_CHECKING([whether $HC understands Posix-style paths])
cat <<EOF >conftest.hs
main = readFile "`pwd`/conftest.hs"
EOF
rm -f conftest$EXEEXT
$HC conftest.hs -o conftest$EXEEXT 2>/dev/null
if ./conftest$EXEEXT 2>/dev/null; then
   AC_MSG_RESULT([yes])
   HC_PATH_STYLE=unix
else
   AC_MSG_RESULT([no])
   HC_PATH_STYLE=windows
fi
rm -f conftest* Main.hi
])


########################################################################
# C compiler particularities

# CURRY_C_DYNAMIC_NO_PIC
# On Darwin (Mac OS X) check whether the compiler understands the
# -mdynamic-no-pic option because Gnu C generates more efficient
# code with this model. Note that this option cannot be used when
# compiling shared libraries, which is not supported by the
# compiler at present.
AC_DEFUN([CURRY_C_DYNAMIC_NO_PIC],
[AC_REQUIRE([AC_PROG_CC]) dnl
 AC_REQUIRE([AC_CANONICAL_TARGET]) dnl
 case $target_os in
  darwin* )
    # use -mdynamic-no-pic when the compiler accepts this option
    # (it was introduced with gcc 3.1 on Mac OS X 10.2)
    # 
    AC_MSG_CHECKING([whether $CC accepts -mdynamic-no-pic])
    save_CC=$CC
    CC="$CC -mdynamic-no-pic"
    AC_COMPILE_IFELSE([AC_LANG_SOURCE([[extern void bar(void);
                                        int foo() { bar(); return 0; }]])],
                      [AC_MSG_RESULT(yes)],
                      [CC=$save_CC
		       AC_MSG_RESULT(no)]);;
 esac])


########################################################################
# runtime system

# CURRY_UNALIGNED_DOUBLE
# Check whether the current architecture requires doubles to be
# aligned on a double word boundary or not. Define UNALIGNED_DOUBLE
# with AC_DEFINE if there are no alignment restrictions.
AC_DEFUN([CURRY_UNALIGNED_DOUBLE],
[AC_REQUIRE([AC_PROG_CC]) dnl
 AC_CACHE_CHECK([whether unaligned double numbers can be used],
   [curry_cv_type_double_unaligned],
   AC_TRY_RUN([#include <stdio.h>
       void store(void *p, double x) { *(double *)p = x; }
       int main() { long x[[4]]; store(x, 3.14); store(x+1, 2.78); exit(0); }],
     curry_cv_type_double_unaligned=yes,
     curry_cv_type_double_unaligned=no,
     curry_cv_type_double_unaligned=no))
 if test "$curry_cv_type_double_unaligned" = yes; then
   AC_DEFINE(UNALIGNED_DOUBLE)
 fi
])
