import ShellCheck.Formatter.TTY
import ShellCheck.Interface

namespace ShellCheck.Tests.FormatterTTY

open ShellCheck.Interface
open ShellCheck.Formatter.TTY

def test_tty_format_line_group_basic : Except String Bool := do
  let filename := "test.sh"
  let contents := "foo\nbar baz\n"
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
  let cr : CheckResult := {
    crFilename := filename
    crComments := [comment]
  }
  let lines := formatResultWithSource noColor cr contents
  let expected := [
    "",
    "test.sh:2:",
    "2 | bar baz",
    "  |     ^-- SC2086 (warning): Double quote to prevent globbing and word splitting.",
    ""
  ]
  pure (lines == expected)

end ShellCheck.Tests.FormatterTTY
