#!/bin/bash
# Edge cases benchmark - tests unusual but valid shell syntax

# Empty command list in group
{ :; }

# Nested groups
{ { { echo nested; }; }; }

# Multiple redirects
cat < input.txt > output.txt 2>&1

# Complex redirects
exec 3>&1 4>&2
exec > /tmp/out.log 2>&1
exec 1>&3 2>&4

# Here-string
cat <<< "This is a here-string"

# Here-doc with command substitution
cat << EOF
Current date: $(date)
Current user: $USER
EOF

# Here-doc with tab stripping
cat <<-EOF
	This has leading tabs
	that get stripped
EOF

# Quoted here-doc delimiter (no expansion)
cat << 'LITERAL'
$USER is not expanded
$(date) is not executed
LITERAL

# Function with local arrays
func_with_arrays() {
    local -a arr=(1 2 3)
    local -A map=([a]=1 [b]=2)
    echo "${arr[@]}" "${!map[@]}"
}

# Coprocess
coproc MY_COPROC { cat; }
echo "test" >&"${MY_COPROC[1]}"
read -r line <&"${MY_COPROC[0]}"

# Arithmetic for loop
for ((i=0; i<10; i++)); do
    echo "$i"
done

# Select statement
select opt in "Option 1" "Option 2" "Quit"; do
    case $opt in
        "Option 1") echo "Selected 1" ;;
        "Option 2") echo "Selected 2" ;;
        "Quit") break ;;
        *) echo "Invalid" ;;
    esac
done < /dev/null

# Select without 'in' (uses positional parameters)
set -- a b c
select x; do
    echo "Selected: $x"
    break
done < /dev/null

# Declare variations
declare -a indexed_array
declare -A assoc_array
declare -i integer_var=42
declare -r readonly_var="constant"
declare -x exported_var="visible"
declare -l lowercase_var="WILL BE LOWER"
declare -u uppercase_var="will be upper"

# Array assignment forms
arr1=(one two three)
arr2=([0]=zero [5]=five [10]=ten)
arr3+=("appended")

# Typeset (alias for declare)
typeset -i num=5
typeset -a list

# Local in functions
inner_func() {
    local var="local value"
    local -n ref=outer_var  # nameref
    echo "$var $ref"
}

# Readonly
readonly CONST="immutable"

# Export variations
export PATH
export VAR=value
export -n UNEXPORT

# Subshells
(
    cd /tmp || exit
    pwd
)

# Command grouping
{ echo one; echo two; echo three; } > output.txt

# Pipelines with negation
! grep -q pattern file.txt && echo "Not found"

# Time command
time sleep 0.1

# Compound commands in pipelines
{ echo "a"; echo "b"; } | sort
(echo "x"; echo "y") | uniq

# Process substitution in various positions
diff <(ls /tmp) <(ls /var)
tee >(cat > /dev/null) < input.txt

# Extended test syntax
[[ -f file && -r file ]] && echo "readable file"
[[ $str =~ ^[0-9]+$ ]] && echo "is number"
[[ $a == $b ]] && echo "equal"

# Arithmetic evaluation
(( x = 5 + 3 ))
(( y += 10 ))
(( z == 0 )) && echo "zero"

# Let command
let "a = 1 + 2"
let "b++" "c--"

# Eval
eval "echo \$HOME"

# Exec variations
# exec ls -la  # Would replace shell

# Source/dot
# source script.sh
# . script.sh

# Builtin
builtin echo "Using builtin"

# Command
command ls -la

# Special parameters
echo "Script: $0"
echo "Args: $@"
echo "Arg count: $#"
echo "Last exit: $?"
echo "PID: $$"
echo "Last bg PID: $!"

# IFS manipulation
old_IFS="$IFS"
IFS=':'
read -ra parts <<< "a:b:c"
IFS="$old_IFS"

# Glob patterns
shopt -s nullglob
files=(*.nonexistent)
shopt -u nullglob

# Brace expansion
echo {1..10}
echo {a..z}
echo {01..10}
echo file{1,2,3}.txt

# Tilde expansion
echo ~
echo ~root
echo ~/subdir

# Parameter expansion forms
var="hello world"
echo "${var}"
echo "${var:-default}"
echo "${var:=assign}"
echo "${var:+alternate}"
echo "${var:?error message}"
echo "${var:0:5}"
echo "${var#h*}"
echo "${var##h*}"
echo "${var%d*}"
echo "${var%%o*}"
echo "${var/o/O}"
echo "${var//o/O}"
echo "${#var}"
echo "${!var@}"
echo "${var^}"
echo "${var^^}"
echo "${var,}"
echo "${var,,}"

# Special array operations
arr=(a b c d e)
echo "${arr[@]:1:3}"
echo "${arr[@]::3}"
echo "${arr[@]: -2}"
echo "${!arr[@]}"

# Indirect expansion
name="var"
var="value"
echo "${!name}"

# Namerefs
declare -n ref=var
echo "$ref"
