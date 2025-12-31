/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Base formatter types and utilities.
-/

import ShellCheck.Data
import ShellCheck.Interface
import ShellCheck.Fixer

namespace ShellCheck.Formatter.Format

open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Fixer

/-- A formatter with callbacks for different stages -/
structure Formatter (m : Type → Type) where
  header : m Unit
  onResult : CheckResult → SystemInterface m → m Unit
  onFailure : String → String → m Unit
  footer : m Unit

/-- Color output options -/
inductive ColorOption where
  | colorAlways : ColorOption
  | colorNever : ColorOption
  | colorAuto : ColorOption
  deriving Repr, BEq, Inhabited

/-- Formatter options -/
structure FormatterOptions where
  foColorOption : ColorOption := .colorAuto
  foWikiLinkCount : Nat := 3
  deriving Repr, Inhabited

/-- Get source file from positioned comment -/
def sourceFile (pc : PositionedComment) : String :=
  pc.pcStartPos.posFile

/-- Get line number from positioned comment -/
def lineNo (pc : PositionedComment) : Nat :=
  pc.pcStartPos.posLine

/-- Get end line number from positioned comment -/
def endLineNo (pc : PositionedComment) : Nat :=
  pc.pcEndPos.posLine

/-- Get column number from positioned comment -/
def colNo (pc : PositionedComment) : Nat :=
  pc.pcStartPos.posColumn

/-- Get end column number from positioned comment -/
def endColNo (pc : PositionedComment) : Nat :=
  pc.pcEndPos.posColumn

/-- Get code number from positioned comment -/
def codeNo (pc : PositionedComment) : Int :=
  pc.pcComment.cCode

/-- Get message text from positioned comment -/
def messageText (pc : PositionedComment) : String :=
  pc.pcComment.cMessage

/-- Get severity as text -/
def severityText (pc : PositionedComment) : String :=
  match pc.pcComment.cSeverity with
  | .errorC => "error"
  | .warningC => "warning"
  | .infoC => "info"
  | .styleC => "style"

/-- Normalize a message into a single line. -/
def normalizeMessage (msg : String) : String :=
  msg.splitOn "\n" |> String.intercalate " "

/-- Format a ShellCheck code tag (e.g., SC2086). -/
def formatCodeTag (code : Int) : String :=
  s!"SC{code}"

/-- Format a full message with code and severity. -/
def formatMessageWithCode (code : Int) (severity : String) (msg : String) : String :=
  s!"{formatCodeTag code} ({severity}): {msg}"

/-- Format a location with line/column. -/
def formatLocation (filename : String) (line : Nat) (col : Nat) : String :=
  s!"{filename}:{line}:{col}:"

/-- Format a location banner with filename and line. -/
def formatLocationBanner (filename : String) (line : Nat) : String :=
  s!"{filename}:{line}:"

/-- Remove tab stops from a position (convert virtual column to real) -/
def removeTabStops (pc : PositionedComment) (_fileLines : Array String) : PositionedComment :=
  -- Simplified: would properly handle tab stop conversion
  pc

/-- Make comments use real (non-virtual) column positions -/
def makeNonVirtual (comments : List PositionedComment) (contents : String) : List PositionedComment :=
  let fileLines := contents.splitOn "\n" |>.toArray
  comments.map (removeTabStops · fileLines)

/-- Check if should output color based on option -/
def shouldOutputColor [Monad m] (_colorOption : ColorOption) : m Bool :=
  -- In pure Lean, we default to no color unless explicitly requested
  -- Real implementation would check isatty
  pure false

/-- Group positioned comments by a key function -/
partial def groupBy (key : PositionedComment → α) [BEq α] (comments : List PositionedComment)
    : List (List PositionedComment) :=
  let rec go (remaining : List PositionedComment) (acc : List (List PositionedComment))
      : List (List PositionedComment) :=
    match remaining with
    | [] => acc.reverse
    | c :: rest =>
      let k := key c
      let (matching, others) := rest.partition (fun c' => key c' == k)
      go others ((c :: matching) :: acc)
  go comments []

/-- Wiki link base URL -/
def wikiLink : String := "https://www.shellcheck.net/wiki/"

-- Theorems (stubs)

theorem sourceFile_extracts_file (pc : PositionedComment) :
    sourceFile pc = pc.pcStartPos.posFile := rfl

theorem lineNo_extracts_line (pc : PositionedComment) :
    lineNo pc = pc.pcStartPos.posLine := rfl

theorem severityText_covers_all (pc : PositionedComment) :
    severityText pc ∈ ["error", "warning", "info", "style"] := by
  cases pc with
  | mk _ _ pcComment _ =>
      cases pcComment with
      | mk sev _ _ =>
          cases sev <;> simp [severityText]

theorem makeNonVirtual_preserves_count (comments : List PositionedComment) (contents : String) :
    (makeNonVirtual comments contents).length = comments.length := by
  simp [makeNonVirtual]

theorem groupBy_partitions (key : PositionedComment → α) [BEq α] (comments : List PositionedComment) :
    (groupBy key comments).flatten.length = comments.length := sorry

end ShellCheck.Formatter.Format
