import ShellCheck.Parser.Arithmetic

open ShellCheck.Parser.Arithmetic

def testParse (name : String) (expr : String) : IO Unit := do
  match parse expr with
  | some _ => IO.println s!"{name}: OK"
  | none => IO.println s!"{name}: FAILED"

#eval do
  -- Basic expressions
  testParse "number" "42"
  testParse "hex" "16#ff"
  testParse "variable" "x"
  testParse "var-dollar" "$x"

  -- Binary operators
  testParse "addition" "1 + 2"
  testParse "subtraction" "a - b"
  testParse "multiplication" "x * y"
  testParse "division" "10 / 2"
  testParse "modulo" "7 % 3"
  testParse "exponent" "2 ** 10"

  -- Comparison
  testParse "less-than" "x < 10"
  testParse "greater-eq" "n >= 0"
  testParse "equality" "a == b"
  testParse "not-equal" "a != b"

  -- Logical
  testParse "logical-and" "x && y"
  testParse "logical-or" "a || b"

  -- Bitwise
  testParse "bitwise-and" "x & y"
  testParse "bitwise-or" "a | b"
  testParse "bitwise-xor" "x ^ y"
  testParse "shift-left" "1 << 8"
  testParse "shift-right" "256 >> 4"

  -- Assignment
  testParse "assign" "x = 5"
  testParse "add-assign" "x += 1"
  testParse "sub-assign" "x -= 1"

  -- Unary
  testParse "negate" "-x"
  testParse "not" "!x"
  testParse "complement" "~x"
  testParse "pre-increment" "++x"
  testParse "pre-decrement" "--x"
  testParse "post-increment" "x++"
  testParse "post-decrement" "x--"

  -- Complex
  testParse "precedence" "1 + 2 * 3"
  testParse "parens" "(1 + 2) * 3"
  testParse "chained" "a + b + c"
  testParse "mixed" "x < 10 && y > 0"

  -- Ternary
  testParse "ternary" "x ? 1 : 0"

  -- Sequence
  testParse "sequence" "x++, y++"

  -- Array
  testParse "array-index" "arr[0]"
  testParse "array-expr" "arr[i + 1]"
