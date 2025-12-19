#!/usr/bin/env bash
# Batch 12: SC2327/SC2328 - command substitution output redirected away

foo() { echo out; echo err >&2; }

var=$(foo > bar)                # warn SC2327 + SC2328
var=`foo 1> bar`                # warn SC2327 + SC2328
var=$(foo | cat > baz)          # warn SC2327 + SC2328 (last pipeline cmd redirected)

stderr=$(foo 2>&1 > /dev/null)  # no SC2327/SC2328 (stderr captured)
var=$(foo; cat > baz)           # no SC2327/SC2328 (multiple commands)
var=$(foo > bar; echo baz)      # no SC2327/SC2328 (multiple commands)
var=$(cat <&3)                  # no SC2327/SC2328 (input redirection)

