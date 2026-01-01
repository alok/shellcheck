import ShellCheck.Parser

open ShellCheck.Parser

#eval do
  let script := "while true; do echo loop; done"
  let (result, positions, errors) := runParser script "test.sh"
  match result with
  | some tok => IO.println s!"Parsed: {positions.size} tokens"
  | none => IO.println s!"FAILED: {errors}"
