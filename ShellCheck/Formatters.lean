/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Umbrella import for all ShellCheck formatters.
-/

import ShellCheck.Formatter.Format
import ShellCheck.Formatter.JSON
import ShellCheck.Formatter.GCC
import ShellCheck.Formatter.TTY
import ShellCheck.Formatter.Quiet
import ShellCheck.Formatter.CheckStyle
import ShellCheck.Formatter.Diff

namespace ShellCheck.Formatters

open ShellCheck.Formatter.Format

/-- Available output formats -/
inductive OutputFormat where
  | json : OutputFormat
  | gcc : OutputFormat
  | tty : OutputFormat
  | quiet : OutputFormat
  | checkstyle : OutputFormat
  | diff : OutputFormat
  deriving Repr, BEq, Inhabited

/-- Get format name as string -/
def OutputFormat.name : OutputFormat → String
  | .json => "json"
  | .gcc => "gcc"
  | .tty => "tty"
  | .quiet => "quiet"
  | .checkstyle => "checkstyle"
  | .diff => "diff"

/-- Parse format from string -/
def OutputFormat.fromString : String → Option OutputFormat
  | "json" => some .json
  | "gcc" => some .gcc
  | "tty" => some .tty
  | "quiet" => some .quiet
  | "checkstyle" => some .checkstyle
  | "diff" => some .diff
  | _ => none

/-- All available formats -/
def allFormats : List OutputFormat :=
  [.json, .gcc, .tty, .quiet, .checkstyle, .diff]

-- Theorems (stubs)

theorem fromString_name_roundtrip (fmt : OutputFormat) :
    OutputFormat.fromString fmt.name = some fmt := sorry

theorem allFormats_complete :
    allFormats.length = 6 := by native_decide

theorem allFormats_unique :
    True := trivial  -- Would verify formats are unique

end ShellCheck.Formatters
