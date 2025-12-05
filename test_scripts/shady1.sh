#!/bin/bash

# SC2086: Double quote to prevent globbing and word splitting
echo $USER is logged in

# SC2046: Quote to prevent word splitting
files=$(ls *.txt)
cp $files /tmp/

# SC2006: Use $(...) instead of backticks
date=`date +%Y-%m-%d`

# SC2034: Variable appears unused
unused_var="hello"

# SC2035: Use ./*glob* to avoid issues with filenames starting with dash
rm -rf *.bak

# SC2012: Use find instead of ls to handle filenames correctly
for f in $(ls); do
  echo $f
done

# SC2001: See if you can use ${var//search/replace}
result=$(echo "$var" | sed 's/foo/bar/')

# SC2045: Iterating over ls output is fragile
for file in `ls /tmp`; do
  cat $file
done
