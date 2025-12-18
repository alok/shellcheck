#!/bin/bash
# Batch 4 (bash): command + shell-support rule ports.
#
# Intended to be compared against upstream ShellCheck where possible.
# Covers (at least): SC2001, SC2213/SC2214/SC2220, SC2227, SC2229, SC2313,
# SC2253, SC2291, SC2293/SC2294, SC2308.

cow="foo"

# SC2001: echo/sed vs ${variable//search/replace}
FOO=$(echo "$cow" | sed 's/foo/bar/g')
FOO=$(sed 's/foo/bar/g' <<< "$cow")
rm $(echo $cow | sed -e 's,foo,bar,')
rm $(sed -e 's,foo,bar,' <<< $cow)

# SC2227: find redirections apply to find itself
find . -exec echo {} > file \;
find . -exec echo {} \; > file
find . -execdir sh -c 'foo > file' \;

# SC2229 / SC2313: read variables vs expansions, and array/glob indices
read $var
read -r $var
read -p $var
read -rd $delim name
read "$var"
read -a $var
read $1
read ${var?}
read arr[val]

# SC2253: chmod -r vs -R
chmod -r 0755 dir
chmod -R 0755 dir
chmod a-r dir

# SC2291: echo collapses repeated spaces between arguments
echo foo         bar
echo       foo
echo foo  bar
echo 'foo          bar'
echo a > myfile.txt b
        echo foo\
        bar

# SC2293 / SC2294: eval + arrays
eval $@
eval "${args[@]}"
eval "${args[@]@Q}"
eval "${args[*]@Q}"
eval "$*"

# SC2308: expr operators with unspecified results
expr match "$cow" '.*'
expr length "$cow"
expr substr "$cow" 1 3
expr index "$cow" abc

# SC2213 / SC2214 / SC2220: getopts + case coverage
while getopts 'a:b' x; do
  case $x in
    a) foo ;;
  esac
done

while getopts 'a:' x; do
  case $x in
    a) foo ;;
    b) bar ;;
  esac
done

while getopts 'a:b' x; do
  case $x in
    a) foo ;;
    b) bar ;;
    *) : ;;
  esac
done

while getopts 'a:123' x; do
  case $x in
    a) foo ;;
    [0-9]) bar ;;
  esac
done

while getopts 'a' x; do
  case $x in
    [a]) foo ;;
    *) : ;;
  esac
done
