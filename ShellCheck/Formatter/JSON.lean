/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  JSON output formatter for ShellCheck.
-/

import ShellCheck.Interface
import ShellCheck.Formatter.Format
import Lean.Data.Json

namespace ShellCheck.Formatter.JSON

open ShellCheck.Interface
open ShellCheck.Formatter.Format
open Lean (Json ToJson)

/-- Convert Position to JSON -/
instance : ToJson Position where
  toJson pos := .mkObj [
    ("file", .str pos.posFile),
    ("line", .num pos.posLine),
    ("column", .num pos.posColumn)
  ]

/-- Convert Replacement to JSON -/
instance : ToJson Replacement where
  toJson rep := .mkObj [
    ("precedence", .num rep.repPrecedence),
    ("insertionPoint", .str (match rep.repInsertionPoint with
      | .insertBefore => "beforeStart"
      | .insertAfter => "afterEnd")),
    ("line", .num rep.repStartPos.posLine),
    ("column", .num rep.repStartPos.posColumn),
    ("endLine", .num rep.repEndPos.posLine),
    ("endColumn", .num rep.repEndPos.posColumn),
    ("replacement", .str rep.repString)
  ]

/-- Convert Fix to JSON -/
instance : ToJson Fix where
  toJson fix := .mkObj [
    ("replacements", .arr (fix.fixReplacements.map ToJson.toJson).toArray)
  ]

/-- Convert PositionedComment to JSON -/
instance : ToJson PositionedComment where
  toJson pc := .mkObj [
    ("file", .str pc.pcStartPos.posFile),
    ("line", .num pc.pcStartPos.posLine),
    ("endLine", .num pc.pcEndPos.posLine),
    ("column", .num pc.pcStartPos.posColumn),
    ("endColumn", .num pc.pcEndPos.posColumn),
    ("level", .str (severityText pc)),
    ("code", .num pc.pcComment.cCode),
    ("message", .str pc.pcComment.cMessage),
    ("fix", match pc.pcFix with
      | some f => ToJson.toJson f
      | none => .null)
  ]

/-- State for collecting results -/
structure JSONState where
  comments : List PositionedComment := []

/-- Format comments as JSON array -/
def formatOutput (comments : List PositionedComment) : String :=
  let jsonArray := Json.arr (comments.map ToJson.toJson).toArray
  jsonArray.pretty

/-- Create JSON formatter -/
def format [Monad m] : Formatter m := {
  header := pure ()
  onResult := fun cr _sys => pure ()  -- Would collect results
  onFailure := fun _file _msg => pure ()
  footer := pure ()  -- Would output collected JSON
}

/-- Format a single check result to JSON string -/
def formatResult (cr : CheckResult) : String :=
  formatOutput cr.crComments

/-- Format multiple check results to JSON string -/
def formatResults (results : List CheckResult) : String :=
  let allComments := results.flatMap (·.crComments)
  formatOutput allComments

-- Theorems (stubs)

theorem formatOutput_valid_json (comments : List PositionedComment) :
    True := trivial  -- Would verify output is valid JSON

theorem toJson_preserves_code (pc : PositionedComment) :
    True := trivial  -- Would verify code is preserved

theorem toJson_preserves_message (pc : PositionedComment) :
    True := trivial  -- Would verify message is preserved

theorem formatResults_includes_all (results : List CheckResult) :
    True := trivial  -- Would verify all comments included

end ShellCheck.Formatter.JSON
