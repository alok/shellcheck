#!/bin/bash
# Batch 5 (bash): subshelled test structures.
#
# Intended to be compared against upstream ShellCheck where possible.
# Covers (at least): SC2233, SC2234, SC2235.

a=1
b=1
c=1
var=
i=0

# SC2235: Use { ..; } instead of (..) to avoid subshell overhead.
a && ( [ b ] || ! [ c ] )
( [ a ] && [ b ] || test c )
( [ a ] && { [ b ] && [ c ]; } )

# SC2234: Remove superfluous (..) around test command
( [ a ] )

# SC2233: Remove superfluous (..) around condition
if ( [ a ] ); then echo hi; fi

# Should not warn (default assignment inside test)
( [[ ${var:=x} = y ]] )

# Should not warn (arithmetic side effects inside test)
( [[ $((i++)) = 10 ]] )
( [[ $((i+=1)) = 10 ]] )

# Should still warn (function body uses subshell syntax).
# shellcheck disable=SC2234
f() ( [[ x ]] )

