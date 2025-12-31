import ShellCheck.Formatter.TTY
import ShellCheck.Formatter.Format
import ShellCheck.Interface

namespace ShellCheck.Tests.FormatterTTY

open ShellCheck.Interface
open ShellCheck.Formatter.TTY
open ShellCheck.Formatter.Format

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

def test_tty_footer_summary : Except String Bool := do
  let filename := "test.sh"
  let mkComment (line col : Nat) (sev : Severity) (code : Int) (msg : String) : PositionedComment := {
    pcStartPos := { posFile := filename, posLine := line, posColumn := col }
    pcEndPos := { posFile := filename, posLine := line, posColumn := col }
    pcComment := { cSeverity := sev, cCode := code, cMessage := msg }
    pcFix := none
  }
  let comments := [
    mkComment 1 1 .warningC 2086 "warn",
    mkComment 2 1 .errorC 1000 "err",
    mkComment 3 1 .infoC 9999 "info"
  ]
  let opts : ShellCheck.Formatter.Format.FormatterOptions := {
    foColorOption := .colorAuto
    foWikiLinkCount := 2
  }
  let lines := formatFooter noColor opts comments
  let expected := [
    "Summary: 3 issues (E:1 W:1 I:1 S:0)",
    "For more information:",
    s!"  {wikiLink}SC2086",
    s!"  {wikiLink}SC1000"
  ]
  pure (lines == expected)

end ShellCheck.Tests.FormatterTTY
