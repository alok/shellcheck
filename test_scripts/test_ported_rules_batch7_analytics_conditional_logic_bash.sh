#!/bin/bash
# Conditional-logic rules (command-level &&/||).

a="x"

# SC2252: `||` with `!=` is always true in this idiom.
[ "$a" != foo ] || [ "$a" != bar ]
[ "$a" != foo ] || [ "$a" != bar ] || true

# Should not warn when the RHS is a glob pattern (user may be doing pattern checks).
[ "$a" != *foo* ] || [ "$a" != *bar* ]

# SC2333: `&&` with `=` is always false in this idiom.
[ "$a" = foo ] && [ "$a" = bar ]
