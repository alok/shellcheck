#!/bin/ksh

# SC2030/SC2031 should not trigger for ksh pipelines
printf 'foo\n' | read bar
printf '%s\n' "$bar"
