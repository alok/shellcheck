#!/bin/bash

# SC2030/SC2031: assignments in subshells/pipelines don't persist
printf 'foo\n' | read bar
printf '%s\n' "$bar"

( A=foo; )
printf '%s\n' "$A"

cat /etc/passwd | while read line; do n=$line; done
printf '%s\n' "$n"

# SC2154: referenced but not assigned
printf '%s\n' "$undefined_var"

# SC2154 should not warn for guarded references
if [ -n "$x" ]; then
  printf '%s\n' "$x"
fi

printf '%s\n' "${foo:-}"
printf '%s\n' "${foo:+$foo}"

# SC2154 should not warn for assignments via commands
mapfile -t files 123
printf '%s\n' "${files[@]}"

wait -p pid
printf '%s\n' "$pid"

DEFINE_string foo default "help"
printf '%s\n' "$FLAGS_foo"

# SC2153: possible misspelling for globals
MY_VARIABLE_NAME=1
printf '%s\n' "$MY_VARIABLE_NMAE"

# SC2154 tip for command-looking locals
printf '%s\n' "$ls"

# SC2030/SC2031 should be suppressed with lastpipe in bash
shopt -s lastpipe
printf 'lastpipe\n' | read lastpipe_var
printf '%s\n' "$lastpipe_var"

# SC2154 should not warn for error/default guards
printf '%s\n' "${guard1?}"  # error if unset
printf '%s\n' "${guard2:?}"  # error if unset, colon variant

arr=(a b)
idx=1
printf '%s\n' "${arr[idx]:-}"
printf '%s\n' "${arr[$idx]:?}"
printf '%s\n' "${arr[bar baz]:-}"
