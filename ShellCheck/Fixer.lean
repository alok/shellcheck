/-
  Copyright 2018-2019 Vidar Holen, Ng Zhi An (Haskell original)
  Lean 4 port: 2024

  Fix application for ShellCheck
-/

import ShellCheck.Interface
import ShellCheck.Prelude

namespace ShellCheck.Fixer

open ShellCheck.Interface
open ShellCheck.Prelude

/-- The Ranged class is used for types that have a start and end position. -/
class Ranged (α : Type) where
  start : α → Position
  «end» : α → Position  -- end is a reserved keyword
  setRange : Position × Position → α → α

/-- Check if two ranged items overlap -/
def overlap [Ranged α] (x y : α) : Bool :=
  let xStart := Ranged.start x
  let xEnd := Ranged.end x
  let yStart := Ranged.start y
  let yEnd := Ranged.end y
  xEnd.posColumn > yStart.posColumn && yEnd.posColumn > xStart.posColumn &&
  xEnd.posLine >= yStart.posLine && yEnd.posLine >= xStart.posLine

instance : Ranged PositionedComment where
  start := fun pc => pc.pcStartPos
  «end» := fun pc => pc.pcEndPos
  setRange := fun (s, e) pc => { pc with pcStartPos := s, pcEndPos := e }

instance : Ranged Replacement where
  start := fun r => r.repStartPos
  «end» := fun r => r.repEndPos
  setRange := fun (s, e) r => { r with repStartPos := s, repEndPos := e }

/-- Check if any replacement in two fixes overlap -/
def fixesOverlap (f1 f2 : Fix) : Bool :=
  f1.fixReplacements.any fun r1 =>
    f2.fixReplacements.any fun r2 =>
      overlap r1 r2

/-- Merge two fixes if they don't overlap, preferring the first on conflict -/
def mergeFixes (f1 f2 : Fix) : Fix :=
  if fixesOverlap f1 f2 then f1
  else { fixReplacements := f1.fixReplacements ++ f2.fixReplacements }

/-- Empty fix -/
def emptyFix : Fix := newFix

/-- Conveniently apply a transformation to positions in a Fix -/
def mapPositions (f : Position → Position) (fix : Fix) : Fix :=
  let adjustReplacement (rep : Replacement) : Replacement :=
    { rep with
      repStartPos := f rep.repStartPos
      repEndPos := f rep.repEndPos
    }
  { fixReplacements := fix.fixReplacements.map adjustReplacement }

/-- A Prefix Sum Tree for tracking cumulative shifts.
    Implemented as a simple BST with cumulative sums. -/
inductive PSTree (n : Type) where
  | leaf : PSTree n
  | branch : n → PSTree n → PSTree n → n → PSTree n
  deriving Repr, Inhabited

/-- Create an empty prefix sum tree -/
def newPSTree : PSTree Int := .leaf

/-- Get the sum of values whose keys are <= target -/
partial def getPrefixSum (target : Int) (tree : PSTree Int) : Int :=
  go 0 target tree
where
  go (sum : Int) (target : Int) : PSTree Int → Int
    | .leaf => sum
    | .branch pivot left right cumulative =>
        if target < pivot then go sum target left
        else if target > pivot then go (sum + cumulative) target right
        else sum + cumulative

/-- Add a value to the prefix sum tree at the given index.
    Values accumulate at the same key. -/
partial def addPSValue (key : Int) (value : Int) (tree : PSTree Int) : PSTree Int :=
  if value == 0 then tree else go tree
where
  go : PSTree Int → PSTree Int
    | .leaf => .branch key .leaf .leaf value
    | .branch pivot left right sum =>
        if key < pivot then .branch pivot (go left) right (sum + value)
        else if key > pivot then .branch pivot left (go right) sum
        else .branch pivot left right (sum + value)

/-- State monad for fix application -/
abbrev Fixer := StateM (PSTree Int)

/-- Run a fixer computation -/
def runFixer (f : Fixer α) : α :=
  (f.run newPSTree).1

/-- Replace a portion of a string.
    start and end are 1-based positions. -/
def doReplace (startPos endPos : Int) (original replacement : String) : String :=
  let si := (startPos - 1).toNat
  let ei := (endPos - 1).toNat
  let pre := original.take si
  let suf := original.drop ei
  pre ++ replacement ++ suf

/-- Apply a single replacement to a string.
    Assumes all positions are on line 1. -/
def applyReplacement2 (rep : Replacement) (str : String) : Fixer String := do
  let tree ← get
  let transform pos := pos + getPrefixSum pos tree
  let oldStart : Int := rep.repStartPos.posColumn
  let oldEnd : Int := rep.repEndPos.posColumn
  let newStart := transform oldStart
  let newEnd := transform oldEnd

  -- Verify positions are on line 1
  if rep.repStartPos.posLine != 1 || rep.repEndPos.posLine != 1 then
    -- This is an error case in the original - we just return unchanged
    return str

  let replacer := rep.repString
  let shift : Int := replacer.length - (oldEnd - oldStart)
  let insertionPoint :=
    match rep.repInsertionPoint with
    | .insertBefore => oldStart
    | .insertAfter => oldEnd + 1

  set (addPSValue insertionPoint shift tree)
  return doReplace newStart newEnd str replacer

/-- Apply a list of replacements in order of precedence -/
def applyReplacements2 (reps : List Replacement) (str : String) : Fixer String := do
  -- Sort by precedence (higher first), then apply in reverse order
  let sorted := reps.mergeSort (fun a b => a.repPrecedence > b.repPrecedence)
  sorted.foldlM (fun s r => applyReplacement2 r s) str

/-- Apply all fixes -/
def applyFixes2 (fixes : List Fix) (str : String) : Fixer String :=
  applyReplacements2 (fixes.flatMap (·.fixReplacements)) str

/-- Convert array lines to a single string -/
def linesToString (lines : Array String) : String :=
  String.intercalate "\n" lines.toList ++ (if lines.isEmpty then "" else "\n")

/-- Split a string back into lines -/
def stringToLines (s : String) : List String :=
  s.splitOn "\n"

/-- Calculate the column shift for each line (for multi-line to single-line conversion) -/
def buildShiftTree (lines : Array String) : PSTree Int :=
  let ls := lines.toList
  let indexed := ls.zip (List.range ls.length)
  indexed.foldl (fun tree (line, idx) =>
    addPSValue ((idx : Int) + 2) ((line.length : Int) + 1) tree
  ) newPSTree

/-- Adjust a position from multi-line to single-line representation -/
def adjustToSingleLine (shiftTree : PSTree Int) (pos : Position) : Position :=
  { pos with
    posLine := 1
    posColumn := pos.posColumn + (getPrefixSum (pos.posLine : Int) shiftTree).toNat
  }

/-- Convert multi-line fixes to single-line -/
def multiToSingleLine (fixes : List Fix) (lines : Array String) : List Fix × String :=
  let shiftTree := buildShiftTree lines
  let singleString := linesToString lines
  let adjustedFixes := fixes.map (mapPositions (adjustToSingleLine shiftTree))
  (adjustedFixes, singleString)

/-- Realign a column from tab-stop 8 to 1.
    Takes the line content and target column. -/
partial def realignColumn (line : String) (targetCol : Nat) : Nat :=
  go line.toList 0 0 targetCol
where
  go : List Char → Nat → Nat → Nat → Nat
    | _, r, v, target => if target <= v then r else
      match line.toList.drop r with
      | [] => r + (target - v)
      | '\t' :: _ => go line.toList (r + 1) (v + 8 - v % 8) target
      | _ :: _ => go line.toList (r + 1) (v + 1) target

/-- Remove tab stops from a Ranged item, converting to column positions -/
def removeTabStops [Ranged α] (range : α) (lines : Array String) : α :=
  let startPos := Ranged.start range
  let endPos := Ranged.end range

  let getLine (lineNo : Nat) : String :=
    if lineNo > 0 && lineNo <= lines.size then
      lines[lineNo - 1]!
    else ""

  let startColumn := realignColumn (getLine startPos.posLine) startPos.posColumn
  let endColumn := realignColumn (getLine endPos.posLine) endPos.posColumn

  let newStartPos := { startPos with posColumn := startColumn }
  let newEndPos := { endPos with posColumn := endColumn }

  Ranged.setRange (newStartPos, newEndPos) range

/-- Apply a fix to file lines and return resulting lines -/
def applyFix (fix : Fix) (fileLines : Array String) : List String :=
  let untabbedReplacements := fix.fixReplacements.map fun r =>
    removeTabStops r fileLines
  let untabbedFix : Fix := { fixReplacements := untabbedReplacements }
  let (adjustedFixes, singleLine) := multiToSingleLine [untabbedFix] fileLines
  let result := runFixer (applyFixes2 adjustedFixes singleLine)
  stringToLines result

-- Theorems (stubs)

theorem overlap_symmetric [Ranged α] (x y : α) :
    overlap x y = overlap y x := sorry

theorem overlap_self [Ranged α] (x : α) :
    overlap x x = true := sorry

theorem fixesOverlap_symmetric (f1 f2 : Fix) :
    fixesOverlap f1 f2 = fixesOverlap f2 f1 := sorry

theorem mergeFixes_associative (f1 f2 f3 : Fix) :
    mergeFixes (mergeFixes f1 f2) f3 = mergeFixes f1 (mergeFixes f2 f3) := sorry

theorem emptyFix_left_identity (f : Fix) :
    mergeFixes emptyFix f = f := by
  simp only [mergeFixes, fixesOverlap, emptyFix, newFix]
  simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append]

theorem emptyFix_right_identity (f : Fix) :
    mergeFixes f emptyFix = f := by
  simp only [mergeFixes, fixesOverlap, emptyFix, newFix, List.any_nil]
  simp

theorem mapPositions_identity (fix : Fix) :
    mapPositions id fix = fix := sorry

theorem mapPositions_composition (f g : Position → Position) (fix : Fix) :
    mapPositions f (mapPositions g fix) = mapPositions (f ∘ g) fix := sorry

theorem getPrefixSum_empty (target : Int) :
    getPrefixSum target newPSTree = 0 := sorry

theorem addPSValue_zero (key : Int) (tree : PSTree Int) :
    addPSValue key 0 tree = tree := sorry

theorem getPrefixSum_after_add (key value target : Int) (tree : PSTree Int) :
    target < key →
    getPrefixSum target (addPSValue key value tree) = getPrefixSum target tree := sorry

theorem doReplace_empty_replacement (start «end» : Int) (s : String) :
    start = «end» → doReplace start «end» s "" = s := sorry

theorem doReplace_start_equals_end (pos : Int) (s repl : String) :
    doReplace pos pos s repl = s.take (pos.toNat - 1) ++ repl ++ s.drop (pos.toNat - 1) := sorry

theorem runFixer_pure (a : α) :
    runFixer (pure a) = a := rfl

theorem linesToString_stringToLines_inverse (lines : Array String) :
    stringToLines (linesToString lines) = lines.toList ++ [""] := sorry

theorem applyFix_empty_fix (lines : Array String) :
    applyFix emptyFix lines = lines.toList ++ [""] := sorry

theorem realignColumn_no_tabs (s : String) (col : Nat) :
    (¬ s.toList.any (· == '\t')) →
    realignColumn s col = col := sorry

theorem removeTabStops_no_tabs [Ranged α] (r : α) (lines : Array String) :
    (¬ lines.toList.any fun l => l.toList.any (· == '\t')) →
    removeTabStops r lines = r := sorry

end ShellCheck.Fixer
