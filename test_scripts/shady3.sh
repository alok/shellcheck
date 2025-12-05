#!/bin/bash

# SC2068: Double quote array expansions
args=("$@")
cmd ${args[@]}

# SC2076: Remove quotes from regex
if [[ "$string" =~ "pattern" ]]; then
  echo matched
fi

# SC2091: Remove surrounding $() to avoid execution
if $( grep -q pattern file ); then
  echo found
fi

# SC2103: Use pushd/popd for directory stack
cd dir
do_something
cd ..

# SC2129: Consider using { cmd1; cmd2; } >> file
echo one >> file
echo two >> file
echo three >> file

# SC2162: read without -r mangles backslashes
while read line; do
  echo "$line"
done < file

# SC2166: Prefer [ p ] && [ q ] over [ p -a q ]
if [ -f file -a -r file ]; then
  cat file
fi

# SC2194: This word is constant. Use a literal or command substitution
case $var in
  $pattern)
    echo "matched $pattern"
    ;;
esac
