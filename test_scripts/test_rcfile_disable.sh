#!/usr/bin/env bash
# Regression: `--rcfile` should apply `.shellcheckrc` settings to a run.

arr=( [2]= 3 )

used[0]=x
used=y
used[0]=x
used+=y

: "${arr[2]-}" "${used[0]-}"

