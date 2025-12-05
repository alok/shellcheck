import ShellCheck.Parser

open ShellCheck.Parser
open ShellCheck.AST

def testScript := "#!/bin/bash
echo hello
if [ -f test ]; then
  echo found
fi
for i in 1 2 3; do
  echo $i
done
"

#eval do
  let (result, positions, errors) := runFullParser testScript "test.sh"
  match result with
  | some tok => IO.println s!"Parsed successfully! Token count: {positions.size}"
  | none => IO.println s!"Parse failed: {errors}"
