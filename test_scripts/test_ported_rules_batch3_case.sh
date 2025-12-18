#!/bin/bash
# Case-related rules.

# SC2194: case statement word is constant (likely forgot `$`).
case foo in
  bar) echo hi ;;
esac

# SC2249: consider adding a default `*)` case.
case "$1" in
  a) echo a ;;
esac

# With a default branch, SC2249 should not trigger.
case "$1" in
  a) echo a ;;
  **) echo default ;;
esac

# SC2195: this pattern can never match the case statement word.
bar=xyz
case foo-$bar in
  ??|*) true ;;
esac

# SC2221/SC2222: earlier pattern overrides later pattern.
f=whatever
case $f in
  cow) true ;;
  bar|cow) false ;;
  *) : ;;
esac

# SC2221/SC2222 should ignore fallthrough branches (;;&).
case $f in
  x) true ;;&
  x) false ;;
  *) : ;;
esac

# SC2254: quote expansions in case patterns to match literally.
bar=thing
n=123
case $1 in
  *$bar*) echo glob-intended ;;
  lol$n) echo should-quote ;;
  $(echo hi)) echo should-quote ;;
  *) : ;;
esac
