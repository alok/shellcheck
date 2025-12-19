#!/usr/bin/env bash
# Regression: for-in loop quoting checks (SC2041/2042/2043/2066/2258).

for f in "$(ls)"; do echo "$f"; done
for f in "$@"; do echo "$f"; done
for f in *.mp3; do echo "$f"; done
for f in "*.mp3"; do echo "$f"; done
for f in 'find /'; do true; done
for f in 1,2,3; do true; done
for f in ls; do true; done
for f in "${!arr}"; do true; done
for f in ls, grep, mv; do true; done
for f in 'ls', 'grep', 'mv'; do true; done
for f in 'ls,' 'grep,' 'mv'; do true; done
