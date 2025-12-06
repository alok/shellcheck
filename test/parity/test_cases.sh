#!/bin/bash

# SC2086 - Double quote to prevent globbing
echo $unquoted

# SC2046 - Quote to prevent word splitting
files=$(ls *.txt)

# SC2006 - Use $(...) instead of backticks
files=`ls`

# SC2034 - Variable appears unused
unused_var="hello"

# SC2154 - Variable referenced but not assigned
echo $undefined_var

# SC2164 - Use cd ... || exit
cd /some/dir

# SC2115 - Use "${var:?}" to ensure variable is set
rm -rf $dir/

# SC2129 - Consider using { cmd1; cmd2; } >> file
echo "line1" >> file
echo "line2" >> file

# SC2162 - read without -r mangles backslashes
read var

# SC2068 - Double quote array
arr=(a b c)
echo ${arr[@]}

# SC2128 - Expanding array without index
echo $arr

# SC2076 - Don't quote right-hand side of =~
[[ $var =~ "pattern" ]]

# SC2072 - Decimals not supported in [[ ]]
[[ 1.5 > 1.0 ]]

# SC2012 - Use find instead of ls
ls -l | grep foo

# SC2001 - See if you can use ${var//pattern/replacement}
echo "$var" | sed 's/foo/bar/'

# SC2002 - Useless cat
cat file | grep pattern

# SC2004 - $/${} is unnecessary on arithmetic variables
echo $((${x} + 1))

# SC2015 - Note that A && B || C is not if-then-else
true && echo yes || echo no

# SC2166 - Use || or && rather than -o or -a
[ "$a" = "1" -o "$b" = "2" ]
