import ShellCheck.Formatter.GCC
import ShellCheck.Interface

namespace ShellCheck.Tests.FormatterGCC

open ShellCheck.Interface
open ShellCheck.Formatter.GCC

def test_gcc_format_comment_basic : Except String Bool := do
  let filename := "test.sh"
  let comment : PositionedComment := {
    pcStartPos := { posFile := filename, posLine := 2, posColumn := 5 }
    pcEndPos := { posFile := filename, posLine := 2, posColumn := 5 }
    pcComment := {
      cSeverity := .warningC
      cCode := 2086
      cMessage := "Double quote to prevent globbing and word splitting."
    }
    pcFix := none
  }
  let out := formatComment filename comment
  let expected :=
    "test.sh:2:5: SC2086 (warning): Double quote to prevent globbing and word splitting."
  pure (out == expected)

end ShellCheck.Tests.FormatterGCC
