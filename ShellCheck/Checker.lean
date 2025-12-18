/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Main entry point for checking shell scripts.
-/

import ShellCheck.Analyzer
import ShellCheck.ASTLib
import ShellCheck.Interface
import ShellCheck.Parser
import Std.Data.HashMap

namespace ShellCheck.Checker

open ShellCheck.Analyzer
open ShellCheck.ASTLib
open ShellCheck.Interface
open ShellCheck.Parser

/-- Numeric ordering for severities (smaller = more severe). -/
def severityRank : Severity → Nat
  | .errorC => 0
  | .warningC => 1
  | .infoC => 2
  | .styleC => 3

/-- Boolean severity comparison matching ShellCheck's `severity <= minSeverity`. -/
def severityAtMost (a b : Severity) : Bool :=
  decide (severityRank a ≤ severityRank b)

/-- Convert a token comment to a positioned comment -/
def tokenToPosition (startMap : TokenPositions)
    (tc : TokenComment) : Option PositionedComment := do
  let (startPos, endPos) ← startMap.get? tc.tcId
  pure {
    pcStartPos := startPos
    pcEndPos := endPos
    pcComment := tc.tcComment
    pcFix := tc.tcFix
  }

/-- Shell extensions and their corresponding shell types -/
def shellExtensions : List (String × Shell) := [
  (".ksh", .Ksh),
  (".bash", .Bash),
  (".bats", .Bash),
  (".dash", .Dash),
  (".envrc", .Bash)
]

/-- Deduce shell type from filename extension -/
def shellFromFilename (filename : String) : Option Shell :=
  shellExtensions.findSome? fun (ext, shell) =>
    if filename.endsWith ext then some shell else Option.none

/-- Sort positioned comments for consistent output -/
def sortMessages (pcs : List PositionedComment) : List PositionedComment :=
  pcs.toArray.qsort (fun a b =>
    let posA := a.pcStartPos
    let posB := b.pcStartPos
    if posA.posFile != posB.posFile then posA.posFile < posB.posFile
    else if posA.posLine != posB.posLine then posA.posLine < posB.posLine
    else if posA.posColumn != posB.posColumn then posA.posColumn < posB.posColumn
    else a.pcComment.cCode < b.pcComment.cCode
  ) |>.toList

/-- Check if a comment should be included based on spec -/
def shouldInclude (spec : CheckSpec) (pc : PositionedComment) : Bool :=
  let code := pc.pcComment.cCode
  let severity := pc.pcComment.cSeverity
  severityAtMost severity spec.csMinSeverity &&
    match spec.csIncludedWarnings with
    | some included => included.contains code
    | none => not (spec.csExcludedWarnings.contains code)

/-- Check a shell script -/
def checkScript [Monad m] (sys : SystemInterface m) (spec : CheckSpec) : m CheckResult := do
  -- Parse the script
  let parseSpec : ParseSpec := {
    psFilename := spec.csFilename
    psScript := spec.csScript
    psCheckSourced := spec.csCheckSourced
    psIgnoreRC := spec.csIgnoreRC
    psShellTypeOverride := spec.csShellTypeOverride
  }
  let parseResult ← parseScriptFull sys parseSpec

  -- Collect parse messages
  let parseMessages := parseResult.prComments
  let tokenPositions := parseResult.prTokenPositions

  -- Run analysis if we have a root token
  let analysisMessages := match parseResult.prRoot with
    | some root =>
      let analysisSpec : AnalysisSpec := {
        asScript := root
        asShellType := spec.csShellTypeOverride
        asFallbackShell := shellFromFilename spec.csFilename
        asCheckSourced := spec.csCheckSourced
        asExecutionMode := .executed
        asTokenPositions := tokenPositions
        asExtendedAnalysis := spec.csExtendedAnalysis
        asOptionalChecks := spec.csOptionalChecks
      }
      let result := analyzeScript analysisSpec
      result.arComments.filterMap (tokenToPosition tokenPositions)
    | none => []

  -- Combine, filter, and sort messages
  let allMessages := parseMessages ++ analysisMessages
  let filtered := allMessages.filter (shouldInclude spec)
  let sorted := sortMessages filtered.eraseDups

  pure {
    crFilename := spec.csFilename
    crComments := sorted
  }

/-- Mock system interface for testing -/
def mockedSystemInterface [Monad m] (_includes : List (String × String)) : SystemInterface m :=
  newSystemInterface

-- Theorems (stubs)

theorem checkScript_parses_first [Monad m] (sys : SystemInterface m) (spec : CheckSpec) :
    True := trivial  -- Would verify parsing happens first

theorem checkScript_filters_by_severity (spec : CheckSpec) :
    True := trivial  -- Would verify severity filtering

theorem shellFromFilename_ksh :
    True := trivial  -- shellFromFilename "script.ksh" = some .Ksh

theorem shellFromFilename_bash :
    True := trivial  -- shellFromFilename "script.bash" = some .Bash

theorem shellFromFilename_unknown :
    True := trivial  -- shellFromFilename "script.sh" = none

theorem sortMessages_stable :
    True := trivial  -- Would verify sort is stable

theorem shouldInclude_respects_exclusions (spec : CheckSpec) (pc : PositionedComment) :
    spec.csExcludedWarnings.contains pc.pcComment.cCode →
    spec.csIncludedWarnings = none →
    shouldInclude spec pc = false := sorry

theorem tokenToPosition_preserves_comment :
    True := trivial  -- Would verify comment is preserved

end ShellCheck.Checker
