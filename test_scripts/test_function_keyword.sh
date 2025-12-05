#!/bin/bash

# Test with function keyword
function helper {
    echo $1
}

# Pass to external command - should warn SC2033
xargs helper

# Test forward reference - should warn SC2218
forward_func arg

function forward_func {
    echo $1
}

# Test unpassed positional params - should warn SC2120
function uses_args {
    echo "First: $1"
    echo "Second: $2"
}
uses_args  # called without args

# Function called with args - should not warn
function with_args {
    echo $1
}
with_args "hello"
