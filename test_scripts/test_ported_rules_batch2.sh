#!/bin/bash
# Batch 2: newly ported / corrected SC rules.

# SC2014: -exec arguments are expanded by the shell once, not per file.
find . -exec echo $(date) \;

# SC2032/SC2033: function passed to external command.
myfunc() { echo "$1"; }
sudo myfunc

# SC2069: 2>&1 must be last.
test 2>&1 > cow

# SC2083: "./ file" is probably "./file".
./ file

# SC2100: looks like arithmetic but isn't.
i=i+1

# SC2104: break/continue outside loops in functions.
f() { break; }
f

# SC2105: break/continue outside loops.
continue 2

# SC2106: break/continue inside subshells in loops.
while true; do ( break; ); done

# SC2119/SC2120: function uses positional params but never passed args.
g() { echo "$1"; }
g

# SC2122: <= and >= are not valid string operators in [[ ]].
[[ foo <= bar ]]

# SC2165/SC2167: nested loop overrides parent index variable.
for i in *; do for i in *.bar; do true; done; done

# SC2178/SC2179: array variables assigned as strings / appended incorrectly.
a=(1)
a=foo
a+=bar
declare -a arr
arr=baz

# SC2181: check exit status via control flow, not by comparing $?
[ $? -eq 0 ]

