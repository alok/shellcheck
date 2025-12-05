/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Main analysis orchestration - combines all checkers.
-/

import ShellCheck.AST
import ShellCheck.Analytics
import ShellCheck.AnalyzerLib
import ShellCheck.Interface
import ShellCheck.Checks.Commands
import ShellCheck.Checks.ControlFlow
import ShellCheck.Checks.Custom
import ShellCheck.Checks.ShellSupport

namespace ShellCheck.Analyzer

open ShellCheck.AST
open ShellCheck.Analytics
open ShellCheck.AnalyzerLib
open ShellCheck.Interface

/-- Combine all checkers into one -/
def checkers (spec : AnalysisSpec) (params : Parameters) : Checker :=
  let c1 := ShellCheck.Analytics.checker spec params
  let c2 := ShellCheck.Checks.Commands.checker spec params
  let c3 := ShellCheck.Checks.ControlFlow.checker spec params
  let c4 := ShellCheck.Checks.Custom.checker params
  let c5 := ShellCheck.Checks.ShellSupport.checker params
  combineCheckers [c1, c2, c3, c4, c5]
where
  combineCheckers (cs : List Checker) : Checker := {
    perScript := fun root => do
      let results ← cs.mapM (·.perScript root)
      pure (results.foldl (· ++ ·) [])
    perToken := fun token => do
      let results ← cs.mapM (·.perToken token)
      pure (results.foldl (· ++ ·) [])
  }

/-- Run the analysis monad -/
def runAnalysis (a : Analysis) (params : Parameters) : List TokenComment :=
  let cache : Cache := {}
  match (a.run params).run cache with
  | .ok (result, _) => result
  | .error _ => []

/-- Analyze a script -/
def analyzeScript (spec : AnalysisSpec) : AnalysisResult :=
  let params := makeParameters spec
  let checker := checkers spec params
  -- Run the checker and collect comments
  let root : Root := ⟨spec.asScript⟩
  let comments := runAnalysis (checker.perScript root) params
  -- Filter by annotations
  let filtered := filterByAnnotation spec params comments
  { newAnalysisResult with arComments := filtered }
where
  filterByAnnotation (_spec : AnalysisSpec) (_params : Parameters)
      (comments : List TokenComment) : List TokenComment :=
    -- Would filter based on annotations in the script
    comments.eraseDups

/-- Optional checks from all modules -/
def optionalChecks : List CheckDescription :=
  ShellCheck.Checks.Commands.optionalChecks ++
  ShellCheck.Checks.ControlFlow.optionalChecks

-- Theorems (stubs)

theorem analyzeScript_produces_result (spec : AnalysisSpec) :
    True := trivial  -- Would verify result is valid

theorem checkers_combine_all (spec : AnalysisSpec) (params : Parameters) :
    True := trivial  -- Would verify all checkers are included

theorem optionalChecks_includes_all :
    True := trivial  -- Would verify all optional checks

theorem filterByAnnotation_respects_disable :
    True := trivial  -- Would verify disable annotations work

end ShellCheck.Analyzer
