#!/usr/bin/env bash
# Batch 9: parameter expansion patterns

# SC2295: Expansions inside ${var%pattern}/${var#pattern} need to be quoted
# separately, otherwise they match as patterns.

var="abcd"
x="b*"

echo "${var#$x}"          # warn SC2295 on $x
echo "${var%%$(echo b*)}" # warn SC2295 on $(...)

echo "${var[#$x]}"        # no SC2295 (array index)
echo "${var%\"$x\"}"      # no SC2295 (already quoted)

