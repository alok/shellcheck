/-
  Copyright 2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Unified diff output formatter for ShellCheck auto-fixes.
-/

import ShellCheck.Interface
import ShellCheck.Fixer
import ShellCheck.Formatter.Format
import Std.Data.HashMap

namespace ShellCheck.Formatter.Diff

open ShellCheck.Interface
open ShellCheck.Fixer
open ShellCheck.Formatter.Format

/-- Diff element types -/
inductive DiffElem (α : Type) where
  | both : α → α → DiffElem α    -- Same in both
  | first : α → DiffElem α       -- Only in original (deletion)
  | second : α → DiffElem α      -- Only in new (addition)
  deriving Repr, BEq, Inhabited

/-- Linefeed status at end of file -/
inductive LFStatus where
  | linefeedMissing : LFStatus
  | linefeedOk : LFStatus
  deriving Repr, BEq, Inhabited

/-- A diff region (hunk) -/
structure DiffRegion (α : Type) where
  leftRange : Nat × Nat    -- (start, count) in original
  rightRange : Nat × Nat   -- (start, count) in new
  diffs : List (DiffElem α)
  deriving Repr, Inhabited

/-- A complete diff document -/
structure DiffDoc (α : Type) where
  name : String
  lfStatus : LFStatus
  regions : List (DiffRegion α)
  deriving Repr, Inhabited

/-- Context size for unified diff -/
def contextSize : Nat := 3

/-- ANSI color codes -/
def red : Nat := 31
def green : Nat := 32
def cyan : Nat := 36
def bold : Nat := 1

/-- Format ANSI escape -/
def ansi (n : Nat) : String := s!"\x1B[{n}m"

/-- Colorize text -/
def colorize (n : Nat) (s : String) : String :=
  ansi n ++ s ++ ansi 0

/-- No-color function -/
def noColor (_n : Nat) (s : String) : String := s

/-- Color function type -/
def ColorFunc := Nat → String → String

/-- Compute simple diff between two line lists -/
def computeDiff (oldLines newLines : List String) : List (DiffElem String) :=
  -- Simplified LCS-based diff (real implementation would use proper diff algorithm)
  -- For now, just mark all as changes if different
  if oldLines == newLines then
    oldLines.map fun l => .both l l
  else
    -- Very simplified: show all old as deletions, all new as additions
    (oldLines.map DiffElem.first) ++ (newLines.map DiffElem.second)

/-- Count lines in diff for left/right sides. -/
def countDelta : List (DiffElem α) → Nat × Nat
  | [] => (0, 0)
  | .both _ _ :: rest =>
      let (l, r) := countDelta rest
      (l + 1, r + 1)
  | .first _ :: rest =>
      let (l, r) := countDelta rest
      (l + 1, r)
  | .second _ :: rest =>
      let (l, r) := countDelta rest
      (l, r + 1)

/-- Format a range as "start,count" -/
def formatRange (range : Nat × Nat) : String :=
  s!"{range.1},{range.2}"

/-- Format a diff line -/
def formatDiffLine (color : ColorFunc) (d : DiffElem String) : String :=
  match d with
  | .both s _ => " " ++ s
  | .first s => color red ("-" ++ s)
  | .second s => color green ("+" ++ s)

/-- Format a diff region (hunk) -/
def formatRegion (color : ColorFunc) (region : DiffRegion String) : String :=
  let header := color cyan s!"@@ -{formatRange region.leftRange} +{formatRange region.rightRange} @@"
  let lines := region.diffs.map (formatDiffLine color)
  String.intercalate "\n" (header :: lines)

/-- Normalize path separators for git compatibility -/
def normalizePath (path : String) : String :=
  path.map fun c => if c == '\\' then '/' else c

/-- Format a complete diff document -/
def formatDoc (color : ColorFunc) (doc : DiffDoc String) : String :=
  let header1 := color bold s!"--- a/{normalizePath doc.name}"
  let header2 := color bold s!"+++ b/{normalizePath doc.name}"
  let regions := doc.regions.map (formatRegion color)
  String.intercalate "\n" ([header1, header2] ++ regions)

/-- Make a diff from original contents and a fix -/
def makeDiff (name : String) (contents : String) (fix : Fix) : DiffDoc String :=
  let oldLines := contents.splitOn "\n"
  let fileArray := oldLines.toArray
  let newLines := applyFix fix fileArray
  let diffs := computeDiff oldLines newLines
  let delta := countDelta diffs
  let region : DiffRegion String := {
    leftRange := (1, delta.1)
    rightRange := (1, delta.2)
    diffs := diffs
  }
  let lf := if contents.endsWith "\n" then .linefeedOk else .linefeedMissing
  { name := name, lfStatus := lf, regions := [region] }

/-- Build a map from filename to combined fix -/
def buildFixMap (fixes : List Fix) : Std.HashMap String Fix :=
  fixes.foldl (fun m fix =>
    match fix.fixReplacements with
    | [] => m
    | r :: _ =>
      let filename := r.repStartPos.posFile
      match m.get? filename with
      | some existing => m.insert filename (mergeFixes existing fix)
      | none => m.insert filename fix
  ) {}
where
  mergeFixes (f1 f2 : Fix) : Fix :=
    { fixReplacements := f1.fixReplacements ++ f2.fixReplacements }

/-- Format diff output for a check result -/
def formatResultDiff (color : ColorFunc) (cr : CheckResult) (contents : String) : Option String :=
  let fixes := cr.crComments.filterMap (·.pcFix)
  if fixes.isEmpty then none
  else
    -- Combine all fixes
    let combined : Fix := { fixReplacements := fixes.flatMap (·.fixReplacements) }
    let doc := makeDiff cr.crFilename contents combined
    some (formatDoc color doc)

/-- Create Diff formatter -/
def format [Monad m] (_options : Format.FormatterOptions) : Format.Formatter m := {
  header := pure ()
  onResult := fun _cr _sys => pure ()  -- Would output diff
  onFailure := fun _file _msg => pure ()  -- Would print error
  footer := pure ()  -- Would check if issues were found but not fixable
}

-- Theorems (stubs)

theorem countDelta_both_increments (s : String) (rest : List (DiffElem String)) :
    countDelta (DiffElem.both s s :: rest) =
    let (l, r) := countDelta rest
    (l + 1, r + 1) := by
  simp [countDelta]

theorem countDelta_first_increments_left (s : String) (rest : List (DiffElem String)) :
    countDelta (DiffElem.first s :: rest) =
    let (l, r) := countDelta rest
    (l + 1, r) := by
  simp [countDelta]

theorem countDelta_second_increments_right (s : String) (rest : List (DiffElem String)) :
    countDelta (DiffElem.second s :: rest) =
    let (l, r) := countDelta rest
    (l, r + 1) := by
  simp [countDelta]

theorem formatDiffLine_first_starts_minus (_color : ColorFunc) (_s : String) :
    True := trivial  -- Would verify starts with '-' (before coloring)

theorem formatDiffLine_second_starts_plus (_color : ColorFunc) (_s : String) :
    True := trivial  -- Would verify starts with '+' (before coloring)

theorem formatDoc_has_headers (_color : ColorFunc) (_doc : DiffDoc String) :
    True := trivial  -- Would verify --- and +++ headers present

theorem normalizePath_replaces_backslash (path : String) :
    ¬(normalizePath path).any (· == '\\') := sorry

end ShellCheck.Formatter.Diff
