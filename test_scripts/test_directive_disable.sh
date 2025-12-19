#!/usr/bin/env bash
# Regression: `# shellcheck disable=SCxxxx` should suppress warnings for the
# following command.

used[0]=x
# shellcheck disable=SC2178
used=y
# shellcheck disable=SC2179
used+=y

arr=( [2]= 3 )
# shellcheck disable=SC2192
arr2=( [2]= 3 )

: "${arr[2]-}" "${arr2[2]-}" "${used[0]-}"
