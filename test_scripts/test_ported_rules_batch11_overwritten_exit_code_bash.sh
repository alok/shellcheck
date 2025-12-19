#!/usr/bin/env bash
# Batch 11: SC2319/SC2320 overwritten exit code ($?)
#
# NOTE: these checks require CFG analysis:
#   ./.lake/build/bin/shellcheck4 --extended-analysis -f gcc <this file>

x() { :; }

x; [ $? -eq 1 ] || [ $? -eq 2 ]          # warn SC2319 on second $?
x; [ $? -eq 1 ]                          # no SC2319 (only one $?)

x; echo "Exit is $?" ; [ $? -eq 0 ]      # warn SC2320 on second $?
x; [ $? -eq 0 ] && echo Success          # no SC2319/SC2320

x; if [ $? -eq 0 ]; then var=$?; fi      # warn SC2319 on var=$?
x; [ $? -gt 0 ] && fail=$?               # warn SC2319 on fail=$?

[ 1 -eq 2 ]; status=$?                   # no SC2319 (intended condition status)
[ 1 -eq 2 ]; exit $?                     # no SC2319 (intended condition status)

