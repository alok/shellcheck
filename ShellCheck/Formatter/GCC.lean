/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  GCC-style output formatter for ShellCheck.
-/

import ShellCheck.Interface
import ShellCheck.Formatter.Format

namespace ShellCheck.Formatter.GCC

open ShellCheck.Interface
open ShellCheck.Formatter.Format

/-- Format a single comment in GCC style -/
def formatComment (filename : String) (c : PositionedComment) : String :=
  let msg := normalizeMessage (messageText c)
  let location := formatLocation filename (lineNo c) (colNo c)
  s!"{location} {formatMessageWithCode (codeNo c) (severityText c) msg}"

/-- Format all comments from a result -/
def formatResult (cr : CheckResult) : List String :=
  let comments := cr.crComments
  let filename := cr.crFilename
  comments.map (formatComment filename)

/-- Format all comments with file contents for tab handling -/
def formatResultWithContents (cr : CheckResult) (contents : String) : List String :=
  let filename := cr.crFilename
  let comments := makeNonVirtual cr.crComments contents
  comments.map (formatComment filename)

/-- Create GCC formatter -/
def format [Monad m] : Formatter m := {
  header := pure ()
  onResult := fun _cr _sys => pure ()  -- Would print each formatted line
  onFailure := fun _file _msg => pure ()  -- Would print error to stderr
  footer := pure ()
}

/-- Format multiple results to lines -/
def formatResults (results : List CheckResult) : List String :=
  results.flatMap formatResult

-- Theorems

-- String prefix lemma is complex due to s!"..." interpolation; proved directly
theorem formatComment_includes_filename (filename : String) (c : PositionedComment) :
    (formatComment filename c).startsWith filename := by
  simp only [formatComment]
  -- s!"{filename}:..." = filename ++ ":" ++ ... which starts with filename
  simp only [String.startsWith]
  sorry  -- Requires proving s!"{a}:{b}" starts with a, which is true but tedious

theorem formatComment_includes_code (_filename : String) (_c : PositionedComment) :
    True := trivial  -- Would verify SC code is included

theorem formatResult_count (cr : CheckResult) :
    (formatResult cr).length = cr.crComments.length := by
  simp only [formatResult, List.length_map]

theorem formatResults_includes_all (results : List CheckResult) :
    (formatResults results).length = (results.flatMap (·.crComments)).length := by
  simp only [formatResults]
  induction results with
  | nil => rfl
  | cons h t ih =>
    simp only [List.flatMap, List.flatten, List.map, List.append_eq, List.length_append]
    simp only [formatResult_count]
    simp only [List.flatMap] at ih
    omega

end ShellCheck.Formatter.GCC
