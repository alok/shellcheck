import ShellCheck.Parser.Glob

open ShellCheck.Parser.Glob

def testExtGlob (name : String) (input : String) : IO Unit := do
  match parseExtGlobStr input with
  | some (.extGlob op patterns) =>
      IO.println s!"{name}: OK (op={op}, patterns={patterns})"
  | some other =>
      IO.println s!"{name}: unexpected result: {repr other}"
  | none => IO.println s!"{name}: FAILED"

def testBrace (name : String) (input : String) : IO Unit := do
  match parseBraceStr input with
  | some (.braceExpansion bt) =>
      match bt with
      | .alternatives alts => IO.println s!"{name}: OK (alternatives={alts})"
      | .numericRange s e p => IO.println s!"{name}: OK (numRange={s}..{e}, padding={p})"
      | .charRange s e => IO.println s!"{name}: OK (charRange={s}..{e})"
  | some other =>
      IO.println s!"{name}: unexpected result: {repr other}"
  | none => IO.println s!"{name}: FAILED"

#eval do
  IO.println "--- Extended Glob Tests ---"
  -- Zero or one
  testExtGlob "zero-or-one" "?(foo)"
  testExtGlob "zero-or-one-multi" "?(foo|bar|baz)"

  -- Zero or more
  testExtGlob "zero-or-more" "*(txt)"
  testExtGlob "zero-or-more-multi" "*(a|b)"

  -- One or more
  testExtGlob "one-or-more" "+(pattern)"

  -- Exactly one
  testExtGlob "exactly-one" "@(this|that)"

  -- Not matching
  testExtGlob "not-match" "!(exclude)"
  testExtGlob "not-match-multi" "!(*.o|*.a)"

  -- Nested
  testExtGlob "nested" "?(foo|+(bar))"

#eval do
  IO.println "\n--- Brace Expansion Tests ---"
  -- Simple alternatives
  testBrace "alts-simple" "{a,b,c}"
  testBrace "alts-words" "{foo,bar,baz}"

  -- Numeric ranges
  testBrace "num-range" "{1..10}"
  testBrace "num-range-neg" "{-5..5}"
  testBrace "num-range-down" "{10..1}"

  -- Zero-padded
  testBrace "num-padded" "{01..10}"
  testBrace "num-padded2" "{001..100}"

  -- Character ranges
  testBrace "char-range" "{a..z}"
  testBrace "char-range-up" "{A..Z}"
  testBrace "char-range-down" "{z..a}"

#eval do
  IO.println "\n--- Brace Expansion Results ---"
  let test1 := expandBrace (.alternatives ["foo", "bar", "baz"])
  IO.println s!"\{a,b,c} -> {test1}"

  let test2 := expandBrace (.numericRange 1 5 none)
  IO.println s!"\{1..5} -> {test2}"

  let test3 := expandBrace (.numericRange 1 5 (some 2))
  IO.println s!"\{01..05} -> {test3}"

  let test4 := expandBrace (.charRange 'a' 'e')
  IO.println s!"\{a..e} -> {test4}"

#eval do
  IO.println "\n--- Detection Tests ---"
  IO.println s!"hasExtGlob '?(foo)' = {hasExtGlob "?(foo)"}"
  IO.println s!"hasExtGlob '*.txt' = {hasExtGlob "*.txt"}"
  IO.println s!"hasExtGlob 'foo' = {hasExtGlob "foo"}"
  let braceTest := hasBraceExpansion "{a,b}"
  IO.println s!"hasBraceExpansion '\{a,b}' = {braceTest}"
  IO.println s!"hasBraceExpansion 'foo' = {hasBraceExpansion "foo"}"
