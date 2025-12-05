import ShellCheck.Parser

open ShellCheck.Parser

def testScript (name : String) (script : String) : IO Unit := do
  let (result, positions, errors) := runFullParser script "test.sh"
  match result with
  | some _ => IO.println s!"{name}: OK ({positions.size} tokens)"
  | none => IO.println s!"{name}: FAILED - {errors.take 1}"

#eval do
  -- Control flow tests
  testScript "if-then-fi" "if test; then echo yes; fi"
  testScript "if-else" "if test; then echo yes; else echo no; fi"
  testScript "if-elif-else" "if test1; then cmd1; elif test2; then cmd2; else cmd3; fi"
  testScript "while" "while true; do echo loop; done"
  testScript "until" "until false; do echo loop; done"
  testScript "for-in" "for x in a b c; do echo $x; done"
  testScript "for-arith" "for ((i=0; i<10; i++)); do echo $i; done"
  testScript "case" "case $x in a) echo a;; b) echo b;; esac"

  -- Compound commands
  testScript "brace-group" "{ echo one; echo two; }"
  testScript "subshell" "(echo sub)"
  testScript "arithmetic" "((1 + 2))"

  -- Pipelines and chaining
  testScript "simple-pipe" "cat file | grep foo"
  testScript "triple-pipe" "cmd1 | cmd2 | cmd3"
  testScript "and-chain" "cmd1 && cmd2 && cmd3"
  testScript "or-chain" "cmd1 || cmd2 || cmd3"
  testScript "mixed-chain" "cmd1 && cmd2 || cmd3"
  testScript "bang-pipeline" "! cmd1 | cmd2"

  -- Nested structures
  testScript "nested-if" "if true; then if false; then echo deep; fi; fi"
  testScript "while-in-pipe" "cat file | while read line; do echo $line; done"
  testScript "if-in-brace" "{ if true; then echo yes; fi; }"

  -- Background
  testScript "background" "cmd1 & cmd2 &"

  -- Comments
  testScript "with-comment" "echo hello # this is a comment"
