#!/usr/bin/env bash
# Tests for SC2324 (var+=1 appends, not increments).
#
# Note: requires CFG analysis, so run with `--extended-analysis`.

x1+=1          # warn SC2324
x2+=42         # warn SC2324

(( x3 += 1 ))  # ok (arithmetic context)

declare -i x4=0
x4+=1          # ok (integer variable)

x5+='1'        # ok (quoted)

n=foo
x6+=n          # ok (n isn't numeric)

n=4
x7+=n          # warn SC2324
x8+=$n         # warn SC2324

