#!/bin/sh

# SC2039: In POSIX sh, arrays are undefined
arr=(one two three)

# SC2039: In POSIX sh, [[ ]] is undefined
if [[ $foo == "bar" ]]; then
  echo "match"
fi

# SC2039: In POSIX sh, $'...' is undefined
msg=$'\n\tindented'

# SC2116: Useless echo
foo=$(echo $(cat file.txt))

# SC2002: Useless cat
cat file.txt | grep pattern

# SC2015: Note that A && B || C is not if-then-else
test -f file && echo exists || echo missing

# SC2164: Use cd ... || exit in case cd fails
cd /some/dir
rm -rf *

# SC2155: Declare and assign separately to avoid masking return values
export foo=$(somecmd)

# SC2181: Check exit code directly, not through $?
somecmd
if [ $? -ne 0 ]; then
  echo "failed"
fi
