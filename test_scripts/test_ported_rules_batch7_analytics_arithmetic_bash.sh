#!/bin/bash
# Arithmetic-related Analytics rules.

# SC2080: Numbers with leading 0 are considered octal.
echo $(( 0192 ))

# Should not warn for valid octal or hex forms.
echo $(( 0777 ))
echo $(( 0x192 ))

