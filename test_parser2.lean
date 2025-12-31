import ShellCheck.Parser

open ShellCheck.Parser

def script1 := "cmd1 | cmd2 | cmd3"
def script2 := "cmd1 && cmd2 || cmd3"
def script3 := "while true; do echo loop; done"
def script4 := "case $x in a) echo a;; b) echo b;; esac"
def script5 := "{ echo group; echo more; }"
def script6 := "(subshell command)"

#eval do
  for (name, script) in [("pipe", script1), ("andor", script2), ("while", script3), 
                         ("case", script4), ("brace", script5), ("subshell", script6)] do
    let (result, positions, errors) := runParser script "test.sh"
    match result with
    | some _ => IO.println s!"{name}: OK ({positions.size} tokens)"
    | none => IO.println s!"{name}: FAILED - {errors.take 1}"
