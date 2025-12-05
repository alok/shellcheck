#!/bin/bash
# Test script for function scope analysis checks

# SC2218: Use function before definition
my_func  # Called before defined!

my_func() {
    echo "Hello from my_func"
}

# SC2033: Pass function to external command
process_item() {
    echo "Processing: $1"
}

# This should warn - functions can't be passed to xargs
find . -name "*.txt" | xargs process_item

# This should warn - functions can't be passed to parallel
parallel process_item ::: item1 item2 item3

# SC2119/SC2120: Function uses positional params but never called with args
greet_user() {
    echo "Hello, $1!"
    echo "Your age is $2"
}

# Called without arguments - should warn
greet_user

# Another function that uses $@ but called without args
run_all() {
    for arg in "$@"; do
        echo "Arg: $arg"
    done
}

run_all  # No args passed!

# This one is fine - called with args
process_data() {
    echo "Data: $1"
}
process_data "some data"

# Alias test
alias ll='ls -la'
xargs ll  # Can't pass alias to xargs either
