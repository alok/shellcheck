#!/usr/bin/env bash
# Regression: invalid unescaped '(' in case patterns should be a parse error (SC1072),
# even when the case statement is not the first command in the script.

x=foo

case $x in
  foo(bar)) echo hi ;;
  *) echo other ;;
esac

