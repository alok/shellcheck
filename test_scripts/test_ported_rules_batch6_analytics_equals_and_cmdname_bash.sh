#!/bin/bash

# This file exercises Analytics/Commands parity around:
# - SC2270-SC2282: "= in command name" heuristics
# - SC2283-SC2285: "foo = bar" / "foo == bar" confusion
# - SC2286-SC2289: suspicious command names
# - SC2292: prefer [[ ]] over [ ] in bash/ksh

# SC2270: positional assignment interpreted as command
${1}='foo'
${2}='foo'

# SC2277: assigning to $0 in bash is not done this way
${0}='foo'

# SC2271: indirection/expansion in would-be variable name
var${x}=value

# SC2272: command name contains ==
$var==42

# SC2273: merge-conflict marker line (uncommented)
=======

# SC2274: starts with ===, likely an un-commented border line
======= Here =======

# SC2275: command name starts with = (bad line break?)
=42

# SC2282: variable names can't start with numbers
411toppm=true

# SC2281: don't use $/${} on the left side of assignments
$var=foo
${var}=foo

# SC2283-SC2285: accidental comparison/assignment syntax
foo = $bar
foo == $bar
var += 1

# SC2286: empty string interpreted as a command name
"" true

# SC2287: command name ends with /
/foo/ bar/baz

# SC2288: command name ends with punctuation
foo, bar

# SC2292: prefer [[ ]] over [ ] in bash/ksh
[ -x foo ]
