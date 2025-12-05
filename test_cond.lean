import ShellCheck.Parser.Condition

open ShellCheck.Parser.Condition

def testParse (name : String) (expr : String) (useDouble : Bool := true) : IO Unit := do
  let result := if useDouble then parseDoubleBracket expr else parseSingleBracket expr
  match result with
  | some _ => IO.println s!"{name}: OK"
  | none => IO.println s!"{name}: FAILED"

#eval do
  -- File tests
  testParse "file-exists" "-e /tmp/file"
  testParse "is-file" "-f /tmp/file"
  testParse "is-directory" "-d /tmp"
  testParse "is-readable" "-r /tmp/file"
  testParse "is-writable" "-w /tmp/file"
  testParse "is-executable" "-x /bin/sh"
  testParse "is-symlink" "-L /tmp/link"
  testParse "has-size" "-s /tmp/file"

  -- String tests
  testParse "is-empty" "-z var"
  testParse "is-nonempty" "-n var"
  testParse "string-equal" "a = b"
  testParse "string-equal2" "a == b"
  testParse "string-not-equal" "a != b"
  testParse "string-less" "a < b"
  testParse "string-greater" "a > b"

  -- Arithmetic comparison
  testParse "num-equal" "1 -eq 2"
  testParse "num-not-equal" "1 -ne 2"
  testParse "num-less" "1 -lt 2"
  testParse "num-less-eq" "1 -le 2"
  testParse "num-greater" "1 -gt 2"
  testParse "num-greater-eq" "1 -ge 2"

  -- File comparison
  testParse "newer-than" "a -nt b"
  testParse "older-than" "a -ot b"
  testParse "same-file" "a -ef b"

  -- Logical operators
  testParse "negation" "! -f /tmp/file"
  testParse "and-double" "-f a && -f b"
  testParse "or-double" "-f a || -f b"
  testParse "and-single" "-f a -a -f b" false
  testParse "or-single" "-f a -o -f b" false

  -- Grouping
  testParse "grouped" "( -f a )"

  -- Complex
  testParse "complex" "-f a && ( -r b || -w c )"

  -- Nullary (just word)
  testParse "nullary" "somevar"
