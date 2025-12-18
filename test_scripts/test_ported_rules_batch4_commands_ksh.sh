#!/bin/ksh
# Batch 4 (ksh): ksh-specific command rules.

# SC2118: Ksh does not support |&. Use 2>&1 |
echo foo |& cat

