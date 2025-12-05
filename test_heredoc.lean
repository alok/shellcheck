import ShellCheck.Parser.HereDoc

open ShellCheck.Parser.HereDoc
open ShellCheck.AST

def testParse (name : String) (input : String) : IO Unit := do
  match parse input with
  | some result =>
      let dashStr := match result.dashed with | .dashed => "dashed" | .undashed => "undashed"
      let quotedStr := match result.quoted with | .quoted => "quoted" | .unquoted => "unquoted"
      IO.println s!"{name}: OK ({dashStr}, {quotedStr}, delim='{result.delimiter}')"
      IO.println s!"  content: {repr result.content}"
  | none => IO.println s!"{name}: FAILED"

#eval do
  -- Basic here-doc
  testParse "basic" "<<EOF\nhello world\nEOF\n"

  -- Dashed (tab stripping)
  testParse "dashed" "<<-EOF\n\thello world\n\tEOF\n"

  -- Single-quoted delimiter (no expansion)
  testParse "single-quoted" "<<'END'\nhello $var\nEND\n"

  -- Double-quoted delimiter (no expansion)
  testParse "double-quoted" "<<\"END\"\nhello $var\nEND\n"

  -- Escaped delimiter (no expansion)
  testParse "escaped" "<<\\END\nhello $var\nEND\n"

  -- Multi-line content
  testParse "multiline" "<<MARKER\nline 1\nline 2\nline 3\nMARKER\n"

  -- Empty content
  testParse "empty" "<<EOF\nEOF\n"

  -- Unusual delimiter
  testParse "unusual-delim" "<<_END_MARKER_\ncontent here\n_END_MARKER_\n"

  -- Here-doc with stuff after delimiter on header line
  testParse "after-header" "<<EOF | cat\nsome content\nEOF\n"

  -- Dashed with mixed tabs
  testParse "dashed-mixed" "<<-DONE\n\t\tindented\n\tless indented\nDONE\n"

-- Test header parsing only
def testHeader (name : String) (input : String) : IO Unit := do
  match parseHeader input with
  | some (dashed, quoted, delim) =>
      let dashStr := match dashed with | .dashed => "dashed" | .undashed => "undashed"
      let quotedStr := match quoted with | .quoted => "quoted" | .unquoted => "unquoted"
      IO.println s!"{name}: OK ({dashStr}, {quotedStr}, delim='{delim}')"
  | none => IO.println s!"{name}: FAILED"

#eval do
  IO.println "\n--- Header parsing tests ---"
  testHeader "header-basic" "<<EOF"
  testHeader "header-dashed" "<<-EOF"
  testHeader "header-quoted" "<<'EOF'"
  testHeader "header-double-quoted" "<<\"EOF\""
  testHeader "header-escaped" "<<\\EOF"
  testHeader "header-with-suffix" "<<EOF | cat"
