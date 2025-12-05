#!/bin/bash
# A deliberately ugly script to test various ShellCheck warnings

# SC2086: Unquoted variables
filename=$1
cat $filename  # Should warn about unquoting

# SC2046: Unquoted command substitution
for f in $(find . -name "*.txt"); do
    echo $f
done

# SC2012: Use find instead of ls in for loop
for f in $(ls *.sh); do
    process $f
done

# SC2006: Use $() instead of backticks
files=`ls -la`

# SC2015: A && B || C is not if-then-else
test -f "$file" && cat "$file" || echo "Not found"

# SC2004: $ unnecessary in arithmetic
x=5
echo $((x + $x))

# SC2034: Unused variable
unused_var="never used"

# SC2154: Referenced but not assigned
echo $undefined_var

# SC2164: Use cd ... || exit
cd /some/directory

# Bad quoting in various contexts
arr=($input)  # SC2206: word splitting in array

# SC2076: Quoted right side of =~
[[ "$str" =~ "pattern" ]]

# SC2072: Decimals in arithmetic
if (( 3.14 > 2 )); then
    echo "pi"
fi

# SC2071: String comparison instead of integer
if [[ $num > 10 ]]; then
    echo "big"
fi

# Single bracket issues
[ $var = "value" ]  # Unquoted var in test
[ -n $str ]  # Unquoted in -n test

# Useless cat
cat file.txt | grep pattern

# Echo with -e in sh
echo -e "Hello\nWorld"

# SC2129: Multiple appends could be single redirect
echo "line1" >> file
echo "line2" >> file
echo "line3" >> file

# SC2162: read without -r
read line

# SC2181: Check exit code directly
command
if [ $? -ne 0 ]; then
    echo "failed"
fi

# Redirect issues
cmd > file 2>&1 > otherfile  # Confusing redirect order

# SC2035: Glob before flags
rm *.txt -f

# SC2044: For loop over find
for file in $(find . -type f); do
    echo "$file"
done
