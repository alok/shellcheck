#!/bin/bash
# Batch 3: newly ported / corrected SC rules.

# SC2170/SC2309: numeric operators with non-numeric literals (often missing $).
[ foo -eq 1 ]
[[ unassigned -eq 1 ]]

# SC2171: stray trailing bracket outside test context.
echo trailing ]
echo trailing ]]

# SC2188/SC2189: dangling redirections (including in pipelines).
> out.txt
> out.txt | cat
echo ok | > out2.txt

# SC2190/SC2191/SC2192: associative array literals need [index]=value and no space after =.
declare -A assoc
assoc=( foo )
assoc=( 1=foo )
assoc=( [key]= value )

# SC2198/SC2199: arrays as test operands.
arr=(a b)
[ ${arr[@]} = foo ]
[[ ${arr[@]} = foo ]]

# SC2200/SC2201: brace expansions as test operands.
[ {a,b} = a ]
[[ {a,b} = a ]]

# SC2202/SC2203: globs as test operands (not on RHS of = in [[ ]]).
[ -e *.txt ]
[[ -e *.txt ]]

# SC2255: [ ] does not apply arithmetic evaluation; globs in numeric operands are suspicious.
[ 1 -gt * ]

# SC2243/SC2244: prefer explicit -n in nullary [[ ]] tests.
[[ $(echo hi) ]]
[[ $foo ]]
[[ "$foo$bar" ]]

# SC2247: $"(foo)"/$"{foo}" likely meant quoted substitution.
echo $"(foo)"
echo $"{foo}"

# SC2204/SC2205: (..) is a subshell, not a test expression.
( -e file; )
( 1 -gt 2; )

# SC2322/SC2323: unnecessary parentheses in arithmetic contexts.
echo $(( (x) ))
echo $(( ((x)) ))
a[(i)]=1
for (((i); (i<10); (i++))); do :; done

# SC2331: prefer -e over legacy -a for file existence tests.
[ -a file ]

# SC2296-SC2301: invalid or nested parameter expansions.
echo ${.foo}
echo ${"var"}

# SC2082: indirection-style parameter expansion.
x=hi
echo ${$x}

# SC2298/SC2299: nested parameter expansions with modifiers.
echo ${${x}:-fallback}
echo ${${x%h}:-fallback}

# SC2300: parameter expansion can't be applied to command substitutions.
echo ${$(echo hi):foo}

echo ${'foo'}

# Commands checks:
# SC2290: remove spaces around =/+= in assignments passed as args to declaring commands.
local foo =bar
local foo +=bar

# SC2316: likely meant to use separate declaring commands.
local export foo=1

# SC2003/SC2304-SC2307: expr is antiquated + argument/glob pitfalls.
expr 1 * 2
expr 123 : *.txt
expr foo
expr foo bar
expr 1 + 2 + *
