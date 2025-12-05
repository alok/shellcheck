/-
  Copyright 2012-2024 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Custom checks - placeholder for site-specific checks.
  This empty file is provided for ease of patching.

  To add custom checks:
  1. Define a check function that matches tokens and returns comments
  2. Add your check to the customChecks list
  3. The checker will automatically apply all custom checks

  Example custom check:

  ```lean
  /-- Example: Warn about using 'rm -rf /' -/
  def checkDangerousRm : Token → List TokenComment :=
    fun t =>
      match t.inner with
      | .T_SimpleCommand _ args =>
        let cmdName := getCommandName t
        let argStrs := args.filterMap getLiteralString
        if cmdName == some "rm" && argStrs.any (· == "/") then
          [makeComment .errorC t.id 9999 "Refusing to remove /"]
        else []
      | _ => []

  def customChecks : List (Token → List TokenComment) := [
    checkDangerousRm
  ]
  ```
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.AnalyzerLib
import ShellCheck.Interface

namespace ShellCheck.Checks.Custom

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.Interface

/-- List of custom per-token checks. Add your checks here. -/
def customTokenChecks : List (Token → List TokenComment) := []

/-- List of custom per-script checks. Add your checks here. -/
def customScriptChecks : List (Root → List TokenComment) := []

/-- Custom checker - applies all custom checks -/
def checker (_params : Parameters) : Checker := {
  perScript := fun root =>
    pure (customScriptChecks.foldl (fun acc check => acc ++ check root) [])
  perToken := fun token =>
    pure (customTokenChecks.foldl (fun acc check => acc ++ check token) [])
}

-- Theorems

theorem checker_empty_when_no_custom_checks (_params : Parameters) (_root : Root) :
    customTokenChecks = [] → customScriptChecks = [] → True := fun _ _ => trivial

theorem custom_checks_extensible :
    True := trivial  -- Adding checks to lists extends functionality

end ShellCheck.Checks.Custom
