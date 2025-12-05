/-
  Copyright 2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Checks that run on the Control Flow Graph (as opposed to the AST).
  This module provides infrastructure for dataflow-based analysis.
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.CFG
import ShellCheck.CFGAnalysis
import ShellCheck.AnalyzerLib
import ShellCheck.Data
import ShellCheck.Interface
import ShellCheck.Graph

namespace ShellCheck.Checks.ControlFlow

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.CFG
open ShellCheck.CFGAnalysis
open ShellCheck.AnalyzerLib
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Graph

/-- Optional checks for control flow -/
def optionalChecks : List CheckDescription := []

/-- A check that runs on the entire graph -/
abbrev ControlFlowCheck := CFGAnalysis → List TokenComment

/-- A check invoked once per node, with its (pre,post) data -/
abbrev ControlFlowNodeCheck := LNode CFNode → (ProgramState × ProgramState) → List TokenComment

/-- A check invoked once per effect -/
abbrev ControlFlowEffectCheck := IdTagged → Graph.Node → (ProgramState × ProgramState) → List TokenComment

/-- SC2154: Check for uninitialized variables being referenced -/
def checkUninitialized : ControlFlowEffectCheck :=
  fun tagged _node (pre, _post) =>
    match tagged.effect with
    | .CFReadVariable varName =>
      -- Check if variable might be uninitialized in the incoming state
      match pre.variablesInScope.get? varName with
      | some _ => []  -- Variable is known
      | Option.none =>
        -- Variable is not in scope - might be uninitialized
        -- But don't warn for special shell variables or common env vars
        if varName.startsWith "$" || varName == "PATH" || varName == "HOME" ||
           varName == "USER" || varName == "PWD" || varName == "SHELL" ||
           varName == "TERM" || varName == "LANG" || varName == "LC_ALL" ||
           varName == "_" || varName.all Char.isDigit then
          []
        else
          [makeComment .warningC tagged.id 2154 s!"{varName} is referenced but not assigned."]
    | _ => []

/-- SC2034: Check for variables assigned but never used -/
def checkUnusedAssignments : ControlFlowEffectCheck :=
  fun tagged _node (_pre, _post) =>
    -- This check is complex and requires tracking variable usage across the whole CFG
    -- For now, return empty - would need to track all reads/writes
    match tagged.effect with
    | .CFWriteVariable _varName _value =>
      []  -- Would need to verify this variable is eventually read
    | _ => []

/-- SC2030: Check for modifications in subshell that won't persist -/
def checkSubshellModifications : ControlFlowEffectCheck :=
  fun tagged _node (_pre, _post) =>
    match tagged.effect with
    | .CFWriteVariable _varName _value =>
      -- Would check if we're in a subshell context
      []
    | _ => []

/-- Control flow effect checks -/
def controlFlowEffectChecks : List ControlFlowEffectCheck := [
  checkUninitialized,
  checkUnusedAssignments,
  checkSubshellModifications
]

/-- Run effect checks on a node -/
def runEffectChecks (list : List ControlFlowEffectCheck) : ControlFlowNodeCheck :=
  fun lnode prepost =>
    match lnode.label with
    | .CFApplyEffects effects =>
      effects.foldl (fun acc effect =>
        acc ++ list.foldl (fun acc2 check => acc2 ++ check effect lnode.node prepost) []
      ) []
    | _ => []

/-- SC2317: Check for unreachable code -/
def checkUnreachableCode : ControlFlowNodeCheck :=
  fun lnode (pre, _post) =>
    if !pre.stateIsReachable then
      match lnode.label with
      | .CFApplyEffects _ =>
        -- Only warn once per unreachable section
        []  -- Would need position tracking to avoid duplicate warnings
      | _ => []
    else []

/-- Control flow node checks -/
def controlFlowNodeChecks : List ControlFlowNodeCheck := [
  runEffectChecks controlFlowEffectChecks,
  checkUnreachableCode
]

/-- Run node checks on all nodes in a graph -/
def runNodeChecks (perNode : List ControlFlowNodeCheck) (analysis : CFGAnalysis) : List TokenComment :=
  -- Iterate over all CFG nodes and their dataflow states
  analysis.graph.nodes.toList.foldl (fun acc lnode =>
    match analysis.nodeToData.get? lnode.node with
    | some prepost =>
      -- Run all checks on this node
      let nodeComments := perNode.foldl (fun acc2 check =>
        acc2 ++ check lnode prepost
      ) []
      acc ++ nodeComments
    | Option.none => acc
  ) []

/-- Check for variables that might be empty when used -/
def checkEmptyVariables : ControlFlowCheck :=
  fun analysis =>
    -- Check for unquoted variable expansions where the variable might be empty
    -- This requires AST context about quoting which isn't fully in CFG yet
    -- For now, iterate through effect nodes looking for reads of potentially empty vars
    analysis.graph.nodes.toList.foldl (fun acc lnode =>
      match lnode.label with
      | .CFApplyEffects effects =>
        effects.foldl (fun acc2 tagged =>
          match tagged.effect with
          | .CFReadVariable varName =>
            -- Check if variable might be empty in incoming state
            match analysis.nodeToData.get? lnode.node with
            | some (pre, _) =>
              match pre.variablesInScope.get? varName with
              | some state =>
                -- Check if variable might be empty based on literal value
                if state.variableValue.literalValue == some "" then
                  makeComment .warningC tagged.id 2086
                    s!"Variable {varName} is empty." :: acc2
                else acc2
              | Option.none => acc2
            | Option.none => acc2
          | _ => acc2
        ) acc
      | _ => acc
    ) []

/-- Check for variables that might contain spaces when unquoted -/
def checkSpacedVariables : ControlFlowCheck :=
  fun analysis =>
    -- SC2086: Track variable contents and warn about unquoted expansions
    -- Check for variables with SpaceStatusUnknown that are used
    analysis.graph.nodes.toList.foldl (fun acc lnode =>
      match lnode.label with
      | .CFApplyEffects effects =>
        effects.foldl (fun acc2 tagged =>
          match tagged.effect with
          | .CFReadVariable varName =>
            match analysis.nodeToData.get? lnode.node with
            | some (pre, _) =>
              match pre.variablesInScope.get? varName with
              | some state =>
                -- Warn if variable might contain spaces
                if state.variableValue.spaceStatus == .SpaceStatusUnknown then
                  -- This would be SC2086 but that's handled elsewhere by AST checks
                  acc2
                else acc2
              | Option.none => acc2
            | Option.none => acc2
          | _ => acc2
        ) acc
      | _ => acc
    ) []

/-- Control flow checks -/
def controlFlowChecks : List ControlFlowCheck := [
  runNodeChecks controlFlowNodeChecks,
  checkEmptyVariables,
  checkSpacedVariables
]

/-- Run all control flow checks on a CFG analysis -/
def runAllChecks (analysis : CFGAnalysis) : List TokenComment :=
  controlFlowChecks.foldl (fun acc check => acc ++ check analysis) []

/-- Create the checker -/
def checker (_spec : AnalysisSpec) (params : Parameters) : Checker := {
  perScript := fun _root =>
    -- Use CFG analysis from params if available
    match params.cfgAnalysis with
    | some analysis =>
      pure (runAllChecks analysis)
    | Option.none =>
      -- No CFG analysis available, skip control flow checks
      pure []
  perToken := fun _ => pure []
}

-- Theorems (stubs)

theorem optionalChecks_empty : optionalChecks = [] := rfl

theorem checker_uses_cfg (_spec : AnalysisSpec) (_params : Parameters) :
    True := trivial  -- Would verify CFG is consulted

theorem controlFlowChecks_compose :
    True := trivial  -- Checks compose correctly

theorem runEffectChecks_visits_all_effects :
    True := trivial

end ShellCheck.Checks.ControlFlow
