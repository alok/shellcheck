#!/bin/bash
# Batch 5 (bash): for-loop glob quoting rule ports.
#
# Intended to be compared against upstream ShellCheck where possible.
# Covers (at least): SC2231.

dir=/tmp

# SC2231: Quote expansions in this for loop glob
for i in $dir/*.txt; do true; done

# Should not warn (expansion is quoted)
for i in "$dir"/*.txt; do true; done

# Should not warn (no glob)
for i in $dir; do true; done

