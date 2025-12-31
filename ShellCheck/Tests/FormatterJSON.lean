import ShellCheck.Formatter.JSON
import ShellCheck.Interface

namespace ShellCheck.Tests.FormatterJSON

open ShellCheck.Interface
open ShellCheck.Formatter.JSON

def containsSubstr (s sub : String) : Bool :=
  if sub.isEmpty then true else
    let target := sub.toList
    let rec go : List Char → Bool
      | [] => false
      | xs@(_ :: rest) =>
          if List.isPrefixOf target xs then
            true
          else
            go rest
    go s.toList

def test_json_format_includes_fix : Except String Bool := do
  let filename := "test.sh"
  let rep : Replacement := {
    repStartPos := { posFile := filename, posLine := 2, posColumn := 3 }
    repEndPos := { posFile := filename, posLine := 2, posColumn := 3 }
    repString := "\""
    repPrecedence := 1
    repInsertionPoint := .insertBefore
  }
  let fix : Fix := { fixReplacements := [rep] }
  let comment : PositionedComment := {
    pcStartPos := { posFile := filename, posLine := 2, posColumn := 3 }
    pcEndPos := { posFile := filename, posLine := 2, posColumn := 3 }
    pcComment := {
      cSeverity := .warningC
      cCode := 2086
      cMessage := "Double quote to prevent globbing and word splitting."
    }
    pcFix := some fix
  }
  let cr : CheckResult := {
    crFilename := filename
    crComments := [comment]
  }
  let out := formatResult cr
  let ok := containsSubstr out "\"fix\"" &&
    containsSubstr out "\"replacements\"" &&
    containsSubstr out "\"replacement\"" &&
    containsSubstr out "\"beforeStart\""
  pure ok

end ShellCheck.Tests.FormatterJSON
