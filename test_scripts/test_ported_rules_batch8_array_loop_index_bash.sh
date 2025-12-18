#!/usr/bin/env bash
#
# Batch 8: array/loop logic
#
# - SC2302: looping over array values but using loop variable as an index
# - SC2303: loop variable is a value, not a key

arr=(a b c)

# Triggers: loops over values, then uses i as an index.
for i in ${arr[@]}; do
  echo "${arr[i]}"
done

# Triggers: same, but index is explicitly expanded.
for i in ${arr[@]}; do
  echo "${arr[$i]}"
done

# Should NOT trigger: i is reassigned inside loop.
for i in ${arr[@]}; do
  i=42
  echo "${arr[i]}"
done

# Should NOT trigger: constant index.
for i in ${arr[@]}; do
  echo "${arr[K]}"
done

