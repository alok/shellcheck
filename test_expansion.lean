import ShellCheck.Parser.Expansion

open ShellCheck.Parser.Expansion

def testParse (name : String) (expr : String) : IO Unit := do
  match parseExpansion expr with
  | some result => IO.println s!"{name}: OK (var={result.varName}, op={repr result.op})"
  | none => IO.println s!"{name}: FAILED"

#eval do
  -- Simple variables
  testParse "simple-var" "var"
  testParse "underscore" "_var"
  testParse "with-num" "var123"

  -- Special parameters
  testParse "at-param" "@"
  testParse "star-param" "*"
  testParse "hash-param" "#"
  testParse "question-param" "?"
  testParse "dollar-param" "$"
  testParse "bang-param" "!"
  testParse "positional" "1"

  -- Length
  testParse "length" "#var"

  -- Indirect
  testParse "indirect" "!var"

  -- Default value
  testParse "default-colon" "var:-default"
  testParse "default-nocolon" "var-default"

  -- Assign default
  testParse "assign-colon" "var:=default"
  testParse "assign-nocolon" "var=default"

  -- Alternate value
  testParse "alt-colon" "var:+alt"
  testParse "alt-nocolon" "var+alt"

  -- Error if unset
  testParse "error-colon" "var:?error msg"
  testParse "error-nocolon" "var?error"

  -- Remove prefix
  testParse "prefix-short" "var#pattern"
  testParse "prefix-long" "var##pattern"

  -- Remove suffix
  testParse "suffix-short" "var%pattern"
  testParse "suffix-long" "var%%pattern"

  -- Replace
  testParse "replace-first" "var/find/repl"
  testParse "replace-all" "var//find/repl"

  -- Substring
  testParse "substring-offset" "var:5"
  testParse "substring-both" "var:5:10"

  -- Case modification
  testParse "upper-first" "var^"
  testParse "upper-all" "var^^"
  testParse "lower-first" "var,"
  testParse "lower-all" "var,,"

  -- Transform
  testParse "transform-Q" "var@Q"
  testParse "transform-E" "var@E"

  -- Array index
  testParse "array-num" "arr[0]"
  testParse "array-at" "arr[@]"
  testParse "array-star" "arr[*]"
