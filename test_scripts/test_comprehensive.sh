#!/bin/bash

# This script tests many ShellCheck warnings

# SC2086 - unquoted variable
echo $foo

# SC2034 - unused variable
unused_var="hello"

# SC2046 - quote to prevent word splitting
files=$(ls)

# SC2006 - use $() instead of backticks
old=`date`

# SC2154 - variable referenced but not assigned
echo $undefined_var

# SC2164 - cd without error handling
cd /tmp

# SC2068 - double quote array expansions
arr=(a b c)
for item in ${arr[@]}; do
    echo $item
done

# SC2115 - Use "${var:?}" to ensure this never expands to /*
rm -rf $dir/

# SC2091 - remove surrounding $()
$(echo foo)

# SC2012 - use find instead of ls
for f in $(ls *.txt); do
    echo "$f"
done

# SC2044 - use find -print0 with while read
find . -name "*.sh" | while read f; do
    echo "$f"
done

# SC2002 - useless use of cat
cat file.txt | grep foo

# SC2129 - multiple redirections to same file
echo foo >> file.log
echo bar >> file.log

# Function scope tests
function process_args {
    echo "First arg: $1"
    echo "All args: $@"
}

# Call xargs with function (should warn)
xargs process_args

# Call undefined function
call_undefined_func

# Define function after use
function forward_defined {
    echo "forward"
}
