import ShellCheck.Parser.ProcessSub

open ShellCheck.Parser.ProcessSub

def testParse (name : String) (input : String) : IO Unit := do
  match parse input with
  | some result =>
      IO.println s!"{name}: OK (dir={result.direction}, cmd='{result.command}')"
  | none => IO.println s!"{name}: FAILED"

#eval do
  IO.println "--- Process Substitution Tests ---"

  -- Basic input process substitution
  testParse "input-simple" "<(ls)"
  testParse "input-args" "<(ls -la)"
  testParse "input-pipe" "<(cat file | grep pattern)"

  -- Basic output process substitution
  testParse "output-simple" ">(cat)"
  testParse "output-tee" ">(tee output.log)"

  -- Nested
  testParse "nested-parens" "<(echo (foo))"
  testParse "nested-subshell" "<(bash -c '(subshell)')"

  -- Complex commands
  testParse "complex" "<(sort file1 | uniq)"
  testParse "with-redirect" "<(cat < input.txt)"

#eval do
  IO.println "\n--- Detection Tests ---"
  IO.println s!"startsWithProcessSub '<(ls)' = {startsWithProcessSub "<(ls)"}"
  IO.println s!"startsWithProcessSub '>(cat)' = {startsWithProcessSub ">(cat)"}"
  IO.println s!"startsWithProcessSub '< (ls)' = {startsWithProcessSub "< (ls)"}"
  IO.println s!"startsWithProcessSub '<file' = {startsWithProcessSub "<file"}"

  IO.println s!"isProcessSubAt '<(ls)' 0 = {isProcessSubAt "<(ls)" 0}"
  IO.println s!"isProcessSubAt '< (ls)' 0 = {isProcessSubAt "< (ls)" 0}"
