/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  TTY (colorized terminal) output formatter for ShellCheck.
-/

import ShellCheck.Interface
import ShellCheck.Fixer
import ShellCheck.Formatter.Format

namespace ShellCheck.Formatter.TTY

open ShellCheck.Interface
open ShellCheck.Fixer
open ShellCheck.Formatter.Format

/-- ANSI color function type -/
def ColorFunc := String → String → String

/-- Get ANSI color code for severity level -/
def colorForLevel (level : String) : Nat :=
  match level with
  | "error" => 31    -- red
  | "warning" => 33  -- yellow
  | "info" => 32     -- green
  | "style" => 32    -- green
  | "verbose" => 32  -- green
  | "message" => 1   -- bold
  | "source" => 0    -- none
  | _ => 0           -- none

/-- Format ANSI escape sequence -/
def ansi (n : Nat) : String := s!"\x1B[{n}m"

/-- ANSI clear sequence -/
def clear : String := ansi 0

/-- Apply color to text -/
def colorComment (level : String) (text : String) : String :=
  ansi (colorForLevel level) ++ text ++ clear

/-- No-color function -/
def noColor (_level : String) (text : String) : String := text

/-- Get color function based on option -/
def getColorFunc (useColor : Bool) : ColorFunc :=
  if useColor then colorComment else noColor

/-- Format error code -/
def code (num : Int) : String := s!"SC{num}"

/-- Create cute arrow indicator for error position -/
def makeArrow (c : PositionedComment) : String :=
  let sameLine := lineNo c == endLineNo c
  let delta := endColNo c - colNo c
  if sameLine && delta > 2 && delta < 32 then
    "^" ++ String.ofList (List.replicate (delta - 2) '-') ++ "^"
  else
    "^--"

/-- Create indented error indicator -/
def cuteIndent (c : PositionedComment) : String :=
  let indent := String.ofList (List.replicate (colNo c - 1) ' ')
  let arrow := makeArrow c
  let codeStr := code (codeNo c)
  let sev := severityText c
  let msg := messageText c
  s!"{indent}{arrow} {codeStr} ({sev}): {msg}"

/-- Format output for a single line group -/
def formatLineGroup (color : ColorFunc) (filename : String) (lineNum : Nat)
    (sourceLine : String) (comments : List PositionedComment) : List String :=
  let header := color "message" s!"In {filename} line {lineNum}:"
  let source := color "source" sourceLine
  let indicators := comments.map fun c =>
    color (severityText c) (cuteIndent c)
  ["", header, source] ++ indicators ++ [""]

/-- Format a complete result with source context -/
def formatResultWithSource (color : ColorFunc) (cr : CheckResult) (contents : String)
    : List String :=
  let filename := cr.crFilename
  let fileLines := contents.splitOn "\n" |>.toArray
  let comments := makeNonVirtual cr.crComments contents
  let groups := groupBy lineNo comments
  groups.flatMap fun group =>
    match group with
    | [] => []
    | c :: _ =>
      let ln := lineNo c
      let line := if ln > 0 && ln ≤ fileLines.size then
        fileLines[ln - 1]!
      else ""
      formatLineGroup color filename ln line group

/-- Format result without source (fallback) -/
def formatResultSimple (color : ColorFunc) (cr : CheckResult) : List String :=
  cr.crComments.flatMap fun c =>
    [color (severityText c) s!"{cr.crFilename}:{lineNo c}:{colNo c}: {messageText c}"]

/-- Format wiki links for top errors -/
def formatWikiLinks (codes : List Nat) : List String :=
  if codes.isEmpty then []
  else
    ["For more information:"] ++
    codes.map fun c => s!"  {wikiLink}SC{c}"

/-- Create TTY formatter -/
def format [Monad m] (_options : Format.FormatterOptions) : Format.Formatter m := {
  header := pure ()
  onResult := fun _cr _sys => pure ()  -- Would print formatted output
  onFailure := fun _file _msg => pure ()  -- Would print error
  footer := pure ()  -- Would print wiki links
}

-- Theorems (stubs)

theorem colorForLevel_valid (level : String) :
    colorForLevel level ≤ 37 := by
  by_cases h1 : level = "error"
  · simp [colorForLevel, h1]
  by_cases h2 : level = "warning"
  · simp [colorForLevel, h2]
  by_cases h3 : level = "info"
  · simp [colorForLevel, h3]
  by_cases h4 : level = "style"
  · simp [colorForLevel, h4]
  by_cases h5 : level = "verbose"
  · simp [colorForLevel, h5]
  by_cases h6 : level = "message"
  · simp [colorForLevel, h6]
  by_cases h7 : level = "source"
  · simp [colorForLevel, h7]
  · simp [colorForLevel]

theorem cuteIndent_starts_with_spaces (c : PositionedComment) :
    (cuteIndent c).length ≥ colNo c := sorry

theorem makeArrow_not_empty (c : PositionedComment) :
    (makeArrow c).length > 0 := sorry

theorem formatLineGroup_includes_source (color : ColorFunc) (filename : String)
    (lineNum : Nat) (sourceLine : String) (comments : List PositionedComment) :
    sourceLine ∈ formatLineGroup color filename lineNum sourceLine comments := sorry

theorem formatWikiLinks_prefix (codes : List Nat) :
    codes.length > 0 →
    (formatWikiLinks codes).head? = some "For more information:" := by
  intro h
  cases codes with
  | nil =>
      simp at h
  | cons c cs =>
      simp [formatWikiLinks]

end ShellCheck.Formatter.TTY
