#!/bin/bash

# Test SC2218: Forward reference to function
# This calls myfunc before it's defined
myfunc arg1 arg2

myfunc() {
    echo "In myfunc: $1"
}

# Test SC2033: Function passed to external command
helper() {
    echo "helper: $1"
}

# These should all warn SC2033
xargs helper < input.txt
find . -exec helper {} \;
parallel helper ::: a b c
env helper arg
sudo helper arg
nohup helper &

# Test SC2119/SC2120: Positional params never passed
process() {
    echo "First arg: $1"
    echo "Second arg: $2"
    echo "All args: $@"
    echo "Arg count: $#"
}

# Called without args - should warn SC2120
process

# But this one is fine (called with args)
process_ok() {
    echo "$1"
}
process_ok "hello"

# Another case: function defined but never called
unused_func() {
    echo "$1 $2"
}

# Test alias passed to external command
alias myalias='echo hello'
xargs myalias < data.txt
