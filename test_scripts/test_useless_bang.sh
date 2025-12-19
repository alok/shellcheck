#!/usr/bin/env bash
# Regression: SC2251 (useless/unsafe `!` in `set -e` scripts).

set -e

! true
echo after

( ! true )

{ ! true; }

if ! true; then true; fi
if { ! true; }; then true; fi

while true; do ! true; done
while ! true; do true; done

