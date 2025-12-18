#!/bin/bash
# Batch 5 (bash): small Analytics.lean rule ports.
#
# Intended to be compared against upstream ShellCheck where possible.
# Covers (at least): SC2210, SC2212.

# SC2210: redirection to numeric literal (likely meant comparison or fd op)
( 1 > 2 )
foo 1>2

# Should not warn (quoted filename)
echo foo > '2'

# Should not warn (fd duplication, not file)
foo 1>&2

# SC2212: empty [ ] / [[ ]] conditionals
if [ ]; then echo "always true"; fi

# Should not warn
[ foo -o bar ]

