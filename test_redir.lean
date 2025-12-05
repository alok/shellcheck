import ShellCheck.Parser.Redirection

open ShellCheck.Parser.Redirection

def testParse (name : String) (input : String) : IO Unit := do
  match parse input with
  | some result =>
      let fdStr := match result.fdSource with
        | some n => s!"fd={n}"
        | none => "fd=default"
      IO.println s!"{name}: OK ({fdStr}, op={result.op}, target='{result.target}')"
  | none => IO.println s!"{name}: FAILED"

#eval do
  -- Basic output redirect
  testParse "out" ">file.txt"
  testParse "out-append" ">>file.txt"
  testParse "out-clobber" ">|file.txt"

  -- Basic input redirect
  testParse "in" "<file.txt"
  testParse "in-out" "<>file.txt"

  -- FD duplication
  testParse "dup-out" ">&2"
  testParse "dup-in" "<&0"

  -- With FD prefix
  testParse "fd-out" "2>error.log"
  testParse "fd-out-append" "2>>error.log"
  testParse "fd-dup" "2>&1"
  testParse "fd-in" "0<input.txt"

  -- Stderr shortcuts
  testParse "stderr" "&>all.log"
  testParse "stderr-append" "&>>all.log"

  -- Here strings
  testParse "herestring" "<<< hello world"
  testParse "herestring2" "<<<'quoted string'"

  -- Here doc (just delimiter)
  testParse "heredoc" "<<EOF"
  testParse "heredoc-dashed" "<<-EOF"
  testParse "heredoc-quoted" "<<'END'"

  -- Close FD
  testParse "close-out" ">&-"
  testParse "close-in" "<&-"

  -- Complex FDs
  testParse "fd3-out" "3>file"
  testParse "fd10-out" "10>file"

#eval do
  IO.println "\n--- isRedirStart tests ---"
  IO.println s!"'>' is redir start: {isRedirStart '>'}"
  IO.println s!"'<' is redir start: {isRedirStart '<'}"
  IO.println s!"'2' is redir start: {isRedirStart '2'}"
  IO.println s!"'a' is redir start: {isRedirStart 'a'}"
