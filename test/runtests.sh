#! /bin/sh
#
# $Id: runtests.sh 3203 2016-05-22 11:58:45Z wlux $
#
# Copyright (c) 2015-2016, Wolfgang Lux
# See ../LICENSE for the full license.
#

# This script is supposed to run all tests in the directories
# specified on the command line or the current directory.
# Unless command line options say otherwise, tests are run
# recursively in all subdirectories of the current directory

# Tests are run in each directory under control of a script file
# called all.T by default. The -t option allows using a different
# script for running alternative sets of tests cases. Each test case
# must be defined on a single line of the form
#   KIND EXPECT FILE ARGUMENTS
# The first word describes the kind of test and can be 'compile',
# 'run', 'eval' or 'type'. The second word describes the expected
# outcome and can be either 'pass' or 'fail'. The third word is the
# name of the main source file. Any remaining words are ignored for
# 'compile' and 'run' tests and specify the goal for 'eval' and 'type'
# tests. Lines starting with # can contain comments and are ignored
# when the tests are run.

# A 'compile' test case just attempts to compile the main module and
# all its imported modules using cymake. If the expected outcome is
# 'pass', the script only checks that compilation succeeds. If the
# expected outcome is 'fail', the script checks that compilation fails
# and that the error messages emitted by the compiler match the
# expected error messages found in file MAIN.compile.err. Here MAIN,
# is the name of the main module, i.e., the file name from the test
# case without the .curry or .lcurry suffix.
# A 'run' test case attempts to produce an executable from the main
# module with cymake using the default goal. The resulting executable
# is then run and its output is compared with the expected output in
# file MAIN.run.out. If the expected outcome is 'fail', the script
# also compares the error messages from running the executable with
# the expected errors in file MAIN.run.err. Input for the executable
# can optionally be supplied in a file MAIN.run.in. If this file does
# not exist, standard input is connected to /dev/null.
# An 'eval' test case is similar to a 'run' test case, but uses the
# explicit goal specified on the command line of the test script after
# the name of the main file. The expected output and optional input
# are found in files MAIN.eval-GOAL.out, MAIN.eval-GOAL.err and
# MAIN.eval-GOAL.in, respectively, where GOAL is the goal string with
# all space characters replaced by underscores.
# A 'type' test case is similar to an 'eval' test case, but instead of
# evaluating the goal the type of the goal is checked. If the expected
# outcome is 'pass', the type computed by the compiler is compared
# with the expected type found in file MAIN.type-GOAL.out. If the
# expected outcome is 'fail', the error messages from the compiler are
# compared with the expected errors found in file MAIN.type-GOAL.err.
# Test cases can be prefixed with the characters 'skip' to
# (temporarily) ignore the test case. In contrast to test cases that
# are commented out, skipped test cases are reported at the end of a
# test run.

# setup
: ${CYMAKE=cymake}
: ${CYFLAGS=}
: ${LDFLAGS=}
cwd=`pwd`
cmd=`basename $0`

# check whether diff supports the -u flag, also try gdiff and gnudiff
# FIXME This should be configure time check.
f=/tmp/`basename $0`.$$
touch $f
if diff -u $f $f >/dev/null 2>&1; then
  diff='diff -u'
elif gdiff -u $f $f >/dev/null 2>&1; then
  diff='gdiff -u'
elif gnudiff -u $f $f >/dev/null 2>&1; then
  diff='gnudiff -u'
else
  diff='diff -c'
fi
rm $f

# check options
script=all
recursive=default
while test $# -gt 0; do
  case $1 in
    "" ) ;;
    -[h?] | --help )
      cat <<EOF
Usage: $cmd {OPTIONS} DIR...

Evaluate all tests in directories DIR...
If no directory is specified evaluate tests in the current directory
and all its subdirectories.

Valid options:
  -?, -h, --help                 display this message
  -t SCRIPT, --test=SCRIPT       evaluate tests from SCRIPT.T
                                 (default: all.T)
  -r, --rec, --recursive         recurse into subdirectories
                                 (default if no directories given)
  -n, --nonrec, --non-recursive  do not recurse into subdirectories
                                 (default with explicit directories)
EOF
      exit;;
    -t | --test )
      case $# in 1 ) echo "$cmd: missing argument after -t" >&2; exit 1;; esac
      script=$2; shift 2;;
    --test=* ) script=`echo "$1" | sed 's/^--test=//'`; shift;;
    -r | --rec | --recursive ) recursive=yes; shift;;
    -n | --nonrec | --non-recursive ) recursive=no; shift;;
    -* )
      echo "$cmd: unknown option" >&2
      echo "Use $cmd -h to get a list of valid options" >&2
      exit 1;;
    * ) break;;
  esac
done
if test $recursive = default; then
  case $# in
    0 ) recursive=yes;;
    * ) recursive=no;;
  esac
fi

tests=0
passes=0
failures=0
disabled=0
unexpected_passes=0
unexpected_failures=0

# clean out temporary files created during the tests
clean ( ) {
  rm -f /tmp/compile.out /tmp/compile.err /tmp/run.out /tmp/run.err \
        /tmp/eval.out /tmp/eval.err /tmp/type.out /tmp/type.err
}
trap 'clean; exit 9' 1 2 3 15

# compile_success DIRECTORY SOURCE MODULE
# compile a source file expecting compilation to succeed
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
compile_success ( ) {
  if "$CYMAKE" $CYFLAGS -q -i$3-modules $2 > /tmp/compile.out 2> /tmp/compile.err; then
    status=expected_pass
  else
    echo "*** Unexpected failure for $1/$2 ***"
    cat /tmp/compile.err
    status=unexpected_fail
    return 1;
  fi
}

# compile_fail DIRECTORY SOURCE MODULE
# compile a source file expecting compilation to fail, the expected error
# messages must be present in file $MODULE.compile.err.
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
compile_fail ( ) {
  if "$CYMAKE" $CYFLAGS -q -i$3-modules $2 > /tmp/compile.out 2> /tmp/compile.err; then
    echo "*** Unexpected success for $1/$2 ***"
    status=unexpected_pass
  elif $diff $3.compile.err /tmp/compile.err; then
    status=expected_fail
  else
    status=unexpected_fail
  fi
}

# run_success DIRECTORY SOURCE MODULE
# compile and run a source file expecting the program to succeed, the
# expected output must be present in file $MODULE.run.out.
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
run_success ( ) {
  compile_success "$1" "$2" "$3" || return $?
  if "$CYMAKE" $LDFLAGS -q -i$3-modules $3 $LDLIBS; then
    if test -f $3.run.in; then stdin=$3.run.in; else stdin=/dev/null; fi
    ./$3 < $stdin > /tmp/run.out 2> /tmp/run.err
    $diff $3.run.out /tmp/run.out || status=unexpected_fail
    if test -s /tmp/run.err; then
      echo "*** Unexpected failure of $1/$3 ***"
      cat /tmp/run.err
      status=unexpected_fail
    fi
  else
    status=unexpected_fail
  fi
}

# run_fail DIRECTORY SOURCE MODULE
# compile and run a source file expecting the program to fail at runtime,
# the expected output of the program must be present in file $MODULE.run.out
# and the expected error must be present in file $MODULE.run.err
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
run_fail ( ) {
  compile_success "$1" "$2" "$3" || return $?
  if "$CYMAKE" $LDFLAGS -q -i$3-modules $3 $LDLIBS; then
    if test -f $3.run.in; then stdin=$3.run.in; else stdin=/dev/null; fi
    ./$3 < $stdin > /tmp/run.out 2> /tmp/run.err
    status=expected_fail
    $diff $3.run.out /tmp/run.out || status=unexpected_fail
    $diff $3.run.err /tmp/run.err || status=unexpected_fail
  else
    status=unexpected_fail
  fi
}

# eval_success DIRECTORY SOURCE MODULE GOAL
# compile a source file and evaluate a goal with respect to it expecting
# the goal to succeed, the expected output must be present in file
# $MODULE.eval-${GOAL:s/ /_/g}.out
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
# GOAL is the goal to be evaluated
eval_success ( ) {
  compile_success "$1" "$2" "$3" || return $?
  if "$CYMAKE" $LDFLAGS -q -i$3-modules $3 -e"$4" -o$3 $LDLIBS; then
    stem=$3.eval-`echo "$4" | tr ' ' _`
    if test -f $stem.in; then stdin=$stem.in; else stdin=/dev/null; fi
    ./$3 < $stdin > /tmp/eval.out 2> /tmp/eval.err
    $diff $stem.out /tmp/eval.out || status=unexpected_fail
    if test -s /tmp/eval.err; then
      echo "*** Unexpected failure of $1/$3 ***"
      cat /tmp/eval.err
      status=unexpected_fail
    fi
  else
    status=unexpected_fail
  fi
}

# eval_fail DIRECTORY SOURCE MODULE GOAL
# compile a source file and evaluate a goal with respect to it expecting
# the goal to to fail, the expected output must be present in file
# $MODULE.eval-${GOAL:s/ /_/g}.out and the expected error must be present
# in file $MODULE.eval-${GOAL:s/ /_/g}.err
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
# GOAL is the goal to be evaluated
eval_fail ( ) {
  compile_success "$1" "$2" "$3" || return $?
  if "$CYMAKE" $LDFLAGS -q -i$3-modules $3 -e"$4" -o$3 $LDLIBS; then
    stem=$3.eval-`echo "$4" | tr ' ' _`
    if test -f $stem.in; then stdin=$stem.in; else stdin=/dev/null; fi
    ./$3 < $stdin > /tmp/eval.out 2> /tmp/eval.err
    status=expected_fail
    $diff $stem.out /tmp/eval.out || status=unexpected_fail
    $diff $stem.err /tmp/eval.err || status=unexpected_fail
  else
    status=unexpected_fail
  fi
}

# type_success DIRECTORY SOURCE MODULE GOAL
# compile a source file and type a goal with respect to it expecting
# the goal to succeed, the expected type must be present in file
# $MODULE.type-${GOAL:s/ /_/g}.out
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
# GOAL is the goal to be typed
type_success ( ) {
  compile_success "$1" "$2" "$3" || return $?
  if "$CYMAKE" $LDFLAGS -q -i$3-modules $3 -T"$4" > /tmp/type.out 2> /tmp/type.err; then
    $diff $3.type-`echo "$4" | tr ' ' _`.out /tmp/type.out || status=unexpected_fail
  else
    echo "*** Unexpected failure of $1/$3 ***"
    cat /tmp/type.err
    status=unexpected_fail
  fi
}

# type_fail DIRECTORY SOURCE MODULE GOAL
# compile a source file and type a goal with respect to it expecting
# the goal to to fail, the expected error must be present in file
# $MODULE.type-${GOAL:s/ /_/g}.err
# DIRECTORY is the path of the directory containing the source (informational)
# SOURCE is the name of the source file (relative to DIRECTORY)
# MODULE is the name of the source file without the .curry or .lcurry extension
# GOAL is the goal to be typed
type_fail ( ) {
  compile_success "$1" "$2" "$3" || return $?
  if "$CYMAKE" $LDFLAGS -q -i$3-modules $3 -T"$4" > /tmp/type.out 2> /tmp/type.err; then
    echo "*** Unexpected success of $1/$3 ***"
    cat /tmp/type.out
    status=unexpected_pass
  else
    status=expected_fail
    $diff $3.type-`echo "$4" | tr ' ' _`.err /tmp/type.err || status=unexpected_fail
  fi
}

# do_test DIRECTORY
# run all tests specified in file all.T in the current directory
# DIRECTORY is the path of the directory containing the tests (informational)
do_test ( ) {
  cd "$1" || return $?
  if test -f "$script".T; then
    echo "* Running test(s) in $1 *"
    lineno=0
    while read test expect src goal; do
      lineno=`expr $lineno + 1`
      case $src in
	*.curry ) mod=`expr $src : '\(.*\)'.curry`;;
	*.lcurry ) mod=`expr $src : '\(.*\)'.lcurry`;;
	* ) mod=$src;;
      esac
      status=
      case $test in
	"" | \#* ) ;; # comment
	skip* )
	  echo "** $src (skipped) **"
	  tests=`expr $tests + 1`
	  disabled=`expr $disabled + 1`;;
        compile )
          echo "** $src (compile) **"
	  tests=`expr $tests + 1`
	  case $expect in
	    pass ) compile_success "$1" $src $mod;;
	    fail ) compile_fail "$1" $src $mod;;
	    * ) echo >&2 "*** Warning: unknown status $expect at $lineno in $1/$script.T ***"
	  esac;;
        run )
	  echo "** $src (run) **"
	  tests=`expr $tests + 1`
	  case $expect in
	    pass ) run_success "$1" $src $mod;;
	    fail ) run_fail "$1" $src $mod;;
	    * ) echo >&2 "*** Warning: unknown status $expect at $lineno in $1/$script.T ***"
	  esac;;
	eval )
	  echo "** $src (eval $goal) **"
	  tests=`expr $tests + 1`
	  case $expect in
	    pass ) eval_success "$1" $src $mod "$goal";;
	    fail ) eval_fail "$1" $src $mod "$goal";;
	    * ) echo >&2 "*** Warning: unknown status $expect at $lineno in $1/$script.T ***"
	  esac;;
	type )
	  echo "** $src (type $goal) **"
	  tests=`expr $tests + 1`
	  case $expect in
	    pass ) type_success "$1" $src $mod "$goal";;
	    fail ) type_fail "$1" $src $mod "$goal";;
	    * ) echo >&2 "*** Warning: unknown status $expect at $lineno in $1/$script.T ***"
	  esac;;
        * ) echo >&2 "*** Warning: unknown command $test at $lineno in $1/$script.T ***";;
      esac
      case $status in
      	expected_pass ) passes=`expr $passes + 1`;;
      	expected_fail ) passes=`expr $passes + 1`;;
      	unexpected_pass )
      	  unexpected_passes=`expr $unexpected_passes + 1`
      	  failures=`expr $failures + 1`;;
      	unexpected_fail )
	  unexpected_failures=`expr $unexpected_failures + 1`
	  failures=`expr $failures + 1`;;
      esac
    done < "$script".T
    while read test expect src goal; do
      case $src in
	*.curry ) mod=`expr $src : '\(.*\)'.curry`;;
	*.lcurry ) mod=`expr $src : '\(.*\)'.lcurry`;;
	* ) mod=$src;;
      esac
      case $test in
        compile ) "$CYMAKE" $CYFLAGS -q -i$mod-modules --clean $src;;
        run | eval | type ) "$CYMAKE" $CYFLAGS -q -i$mod-modules --clean $mod;;
      esac
    done < "$script".T
    clean
  fi
  cd "$cwd"
}

# run tests in the specified subdirectories or the current directory
# and eventually all of their subdirectories
case $# in 0 ) set .;; esac
for d in "$@"; do
  if test $recursive = yes; then
    for dd in "$d" `find "$d"/* -type d \( -name '.*' -prune -o -print \)`; do
      do_test "$dd"
    done
  else
    do_test "$d"
  fi
done

# print final statistics
echo
enabled=`expr $tests - $disabled`
if test $enabled -eq $passes; then
  echo "*** All tests completed successfully ***"
  status=0
else
  echo "*** Some tests did not complete successfully ***"
  status=1
fi
echo
printf "  %4d test cases\\n" $tests
printf "  %4d test(s) passed\\n" $passes
printf "  %4d test(s) failed\\n" $failures
if test $disabled -ne 0; then
  printf "  %4d test(s) skipped (disabled)\\n" $disabled
fi
echo
printf "  %4d unexpected pass(es)\\n" $unexpected_passes
printf "  %4d unexpected failure(s)\\n" $unexpected_failures
echo

exit $status
