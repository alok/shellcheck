#!/usr/bin/env bash
# Regression: parse indexed assignments and indexed array elements.
#
# This used to drop assignment indices and fail to emit T_IndexedElement for
# array literals, breaking array-related checks like SC2178/SC2179 and SC2192.

n=1

# Indexed assignment indices (should parse as T_Assignment with nonempty indices)
a[3]=42
a[3$n'']=42
a[4''$(echo hi)]=42
x[y[z=1]]=1
var[x]+=1

# Indexed elements in array literals (should parse as T_IndexedElement)
arr=( [2]=(3 4) )
arr2=( 1 [2]=(3 4) )
arr3=( (1 2) (3 4) )

# SC2192: value is empty; "3" becomes the next element.
arr4=( [2]= 3 )

# SC2178/SC2179 should trigger on these.
used[0]=x
used=y
used[0]=x
used+=y

# Silence "unused" warnings in both ShellCheck implementations.
: "${n}" "${a[3]-}" "${x[0]-}" "${arr[2]-}" "${arr2[2]-}" "${arr3[0]-}" "${arr4[2]-}" "${used[0]-}"
