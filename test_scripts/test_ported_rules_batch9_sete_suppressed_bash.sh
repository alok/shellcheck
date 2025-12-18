#!/usr/bin/env bash
# Batch 9: errexit / set -e behavior

# SC2311: Bash implicitly disables set -e for function invocations inside
# command substitutions unless inherit_errexit is enabled or set -e is re-enabled.
# SC2310: Functions invoked in conditionals don't trigger errexit.

set -e

f() { :; }

x=$(f)              # warn SC2311
y=$(set -e; f)      # no SC2311 (set -e re-enabled inside substitution)

if f; then :; fi    # warn SC2310
while f; do :; done # warn SC2310
until f; do :; done # warn SC2310

f && echo ok        # warn SC2310
f || echo ok        # warn SC2310
! f                 # warn SC2310

echo ok && f        # no SC2310 (final command in && list)
echo ok || f        # no SC2310 (final command in || list)

