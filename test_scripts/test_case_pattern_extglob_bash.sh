#!/usr/bin/env bash
# Regression: case patterns with extglob use parentheses and |.
# Our parser should treat these as part of the pattern, not as shell operators.

shopt -s extglob

x="${1-foo}"

case "$x" in
  @(foo|bar)) echo "extglob";;
  [a|b]) echo "bracket";;
  *) echo "other";;
esac

