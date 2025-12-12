/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Quiet output formatter - minimal output for scripting.
-/

import ShellCheck.Interface
import ShellCheck.Formatter.Format

namespace ShellCheck.Formatter.Quiet

open ShellCheck.Interface
open ShellCheck.Formatter.Format

/-- Check if result has any comments -/
def hasIssues (cr : CheckResult) : Bool :=
  not cr.crComments.isEmpty

/-- Count total issues across results -/
def countIssues (results : List CheckResult) : Nat :=
  results.foldl (fun acc cr => acc + cr.crComments.length) 0

/-- Create quiet formatter (produces no output, just tracks issues) -/
def format [Monad m] : Formatter m := {
  header := pure ()
  onResult := fun _cr _sys => pure ()
  onFailure := fun _file _msg => pure ()
  footer := pure ()
}

/-- Format result as just the exit code (0 = no issues, 1 = has issues) -/
def exitCode (results : List CheckResult) : Nat :=
  if countIssues results > 0 then 1 else 0

-- Theorems

theorem hasIssues_iff_nonempty (cr : CheckResult) :
    hasIssues cr ↔ cr.crComments.length > 0 := by
  simp only [hasIssues]
  cases cr.crComments with
  | nil => simp [List.isEmpty, List.length]
  | cons h t => simp [List.isEmpty, List.length]

theorem exitCode_reflects_issues (results : List CheckResult) :
    exitCode results = 0 ↔ countIssues results = 0 := by
  simp only [exitCode]
  split <;> omega

end ShellCheck.Formatter.Quiet
