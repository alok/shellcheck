#!/usr/bin/env bash
# Batch 10: SC2312 extra masked returns

# process substitution masks exit status
cat < <(ls)              # warn SC2312 on ls
read -ra arr < <(ls)     # warn SC2312 on ls
ls >(cat)                # warn SC2312 on cat

# pipelines mask non-last commands unless pipefail is set
false | true              # warn SC2312 on false

# masking can be deliberate
false | true || true      # no SC2312 (deliberately ignored)

# multiple command substitutions in one word: all but last are masked
x=$(false)$(true)         # warn SC2312 on first $(false)

# assignment-only command: only earlier "command-y" assignments are masked
x=$(false) y=z            # no SC2312

# declaring commands are checked elsewhere (SC2155)
readonly x=$(false)       # no SC2312

# assignment + command: assignment substitution is masked by the command
x=$(false) false          # warn SC2312 on $(false)

# arrays: all but last element that contains a command substitution is masked
x=( $(false) false )      # no SC2312
x=( $(false) $(false) )   # warn SC2312 on first $(false)
