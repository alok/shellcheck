#!/bin/bash

# This script intentionally triggers a handful of rules that were recently
# ported to the Lean implementation.

# SC2007: deprecated $[..] arithmetic form
echo $[1+2]

# SC2027: the surrounding quotes actually unquote this
echo "foo"$bar"baz"

# SC2030/SC2031: assignments in pipeline subshells don't persist
echo foo | read bar; echo $bar

# SC2087: ssh heredoc delimiter should be quoted to avoid client-side expansion
ssh host << foo
echo $PATH
foo

# SC2153: possible misspelling for all-caps variables
MY_VARIABLE_NAME=1
echo $MY_VARIABLE_NMAE

