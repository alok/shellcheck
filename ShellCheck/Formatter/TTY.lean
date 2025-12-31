/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  TTY (colorized terminal) output formatter for ShellCheck.
-/

import ShellCheck.Interface
import ShellCheck.Fixer
import ShellCheck.Formatter.Format
import Std.Data.HashSet

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
  let sev := severityText c
  let msg := formatMessageWithCode (codeNo c) sev (messageText c)
  s!"{indent}{arrow} {msg}"

/-- Format output for a single line group -/
def formatLineGroup (color : ColorFunc) (filename : String) (lineNum : Nat)
    (sourceLine : String) (comments : List PositionedComment) : List String :=
  let lineNoStr := toString lineNum
  let gutter := lineNoStr ++ " | "
  let pad := String.ofList (List.replicate lineNoStr.length ' ') ++ " | "
  let header := color "message" (formatLocationBanner filename lineNum)
  let source := color "source" (gutter ++ sourceLine)
  let indicators := comments.map fun c =>
    color (severityText c) (pad ++ cuteIndent c)
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
    [color (severityText c)
      s!"{formatLocation cr.crFilename (lineNo c) (colNo c)} {formatMessageWithCode (codeNo c) (severityText c) (messageText c)}"]

/-- Format wiki links for top errors -/
def formatWikiLinks (codes : List Nat) : List String :=
  if codes.isEmpty then []
  else
    ["For more information:"] ++
    codes.map fun c => s!"  {wikiLink}SC{c}"

/-- Collect distinct wiki codes up to a limit, preserving order. -/
def collectWikiCodes (limit : Nat) (comments : List PositionedComment) : List Nat :=
  let codes := comments
    |>.map (·.pcComment.cCode)
    |>.filter (· > 0)
    |>.map (·.toNat)
  let (_, acc) := codes.foldl
    (fun (seen, acc) c =>
      if acc.length < limit && !seen.contains c then
        (seen.insert c, acc ++ [c])
      else
        (seen, acc))
    (({} : Std.HashSet Nat), [])
  acc

/-- Format a compact summary line for a list of comments. -/
def formatSummaryLine (color : ColorFunc) (comments : List PositionedComment) : Option String :=
  if comments.isEmpty then
    none
  else
    let (errors, warnings, infos, styles) :=
      comments.foldl
        (fun (e, w, i, s) c =>
          match severityText c with
          | "error" => (e + 1, w, i, s)
          | "warning" => (e, w + 1, i, s)
          | "info" => (e, w, i + 1, s)
          | _ => (e, w, i, s + 1))
        (0, 0, 0, 0)
    let total := errors + warnings + infos + styles
    some (color "message" s!"Summary: {total} issues (E:{errors} W:{warnings} I:{infos} S:{styles})")

/-- Format footer lines (summary + wiki links) for TTY output. -/
def formatFooter (color : ColorFunc) (options : Format.FormatterOptions)
    (comments : List PositionedComment) : List String :=
  let summary :=
    match formatSummaryLine color comments with
    | some line => [line]
    | none => []
  let wikiCodes := collectWikiCodes options.foWikiLinkCount comments
  summary ++ formatWikiLinks wikiCodes

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
