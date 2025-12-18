#!/bin/bash
# Batch 5 (bash): redirection-to-command checks.
#
# Intended to be compared against upstream ShellCheck where possible.
# Covers (at least): SC2238.

# SC2238: Redirecting to/from command name instead of file
ls > rm

# Should not warn (quoted)
ls > 'rm'

# Should not warn (normal file)
ls > myfile

