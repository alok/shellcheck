#!/bin/bash
# Grep-specific command checks.

# SC2062: Quote grep patterns so the shell won't interpret globs.
grep *foo* file.txt

# SC2063: Grep uses regex, but this looks like a glob.
grep '*bar*' file.txt

# SC2063 should not trigger when using fixed strings or include/exclude flags.
grep -F '*baz*' file.txt
grep --include=*.sh '*qux*' file.txt

# fgrep implies fixed strings, so SC2063 should not apply.
fgrep *wut* file.txt

# Pattern after `--` should still be considered a pattern.
grep -- -x* file.txt
