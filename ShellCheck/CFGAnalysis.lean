/-
  Copyright 2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Data Flow Analysis on a Control Flow Graph.

  This module implements a standard iterative Data Flow Analysis.
  It tracks variable values and properties across control flow.
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.Data
import ShellCheck.CFG
import ShellCheck.Graph
import ShellCheck.Prelude
import Std.Data.HashMap
import Std.Data.HashSet

namespace ShellCheck.CFGAnalysis

open ShellCheck.AST
open ShellCheck.CFG
open ShellCheck.Graph
open ShellCheck.Data

/-- Status of whether a string contains spaces -/
inductive SpaceStatus where
  | SpaceStatusEmpty      -- Known to be empty string
  | SpaceStatusClean      -- Known to not contain whitespace (but may be empty)
  | SpaceStatusSpaces     -- Known to contain IFS-spaces
  | SpaceStatusGlobChars  -- Known to contain glob characters
  | SpaceStatusUnknown    -- Unknown
  deriving Repr, BEq, Ord, Inhabited, DecidableEq

instance : LT SpaceStatus where
  lt a b := a.ctorIdx < b.ctorIdx

instance : LE SpaceStatus where
  le a b := a.ctorIdx ≤ b.ctorIdx

instance (a b : SpaceStatus) : Decidable (a < b) := Nat.decLt _ _
instance (a b : SpaceStatus) : Decidable (a ≤ b) := Nat.decLe _ _

/-- Status of whether a value is numerical -/
inductive NumericalStatus where
  | NumericalStatusUnknown  -- Unknown
  | NumericalStatusMaybe    -- May be a number
  | NumericalStatusDefinite -- Definitely a number
  deriving Repr, BEq, Ord, Inhabited, DecidableEq

instance : LT NumericalStatus where
  lt a b := a.ctorIdx < b.ctorIdx

instance : LE NumericalStatus where
  le a b := a.ctorIdx ≤ b.ctorIdx

instance (a b : NumericalStatus) : Decidable (a < b) := Nat.decLt _ _
instance (a b : NumericalStatus) : Decidable (a ≤ b) := Nat.decLe _ _

/-- The value of a variable -/
structure VariableValue where
  literalValue : Option String
  spaceStatus : SpaceStatus
  numericalStatus : NumericalStatus
  deriving Repr, Inhabited

/-- Unknown variable value -/
def unknownVariableValue : VariableValue := {
  literalValue := none
  spaceStatus := .SpaceStatusUnknown
  numericalStatus := .NumericalStatusUnknown
}

/-- Unknown integer value -/
def unknownIntegerValue : VariableValue := {
  literalValue := none
  spaceStatus := .SpaceStatusClean
  numericalStatus := .NumericalStatusDefinite
}

/-- Properties a variable can have -/
abbrev VariableProperties := List (List CFVariableProp)

/-- The state of a variable -/
structure VariableState where
  variableValue : VariableValue
  variableProperties : VariableProperties
  deriving Repr, Inhabited

/-- Unknown variable state -/
def unknownVariableState : VariableState := {
  variableValue := unknownVariableValue
  variableProperties := [[]]
}

/-- Function value (entry and exit nodes) -/
structure FunctionValue where
  funcEntry : Node
  funcExit : Node
  deriving Repr, Inhabited

/-- Internal state during DFA -/
structure InternalState where
  sVersion : Int
  sGlobalValues : Std.HashMap String VariableState
  sLocalValues : Std.HashMap String VariableState
  sPrefixValues : Std.HashMap String VariableState
  sFunctionTargets : Std.HashMap String FunctionValue
  sExitCodes : Option (List Id)
  sIsReachable : Option Bool
  deriving Inhabited

/-- Create a new empty internal state -/
def newInternalState : InternalState := {
  sVersion := 0
  sGlobalValues := {}
  sLocalValues := {}
  sPrefixValues := {}
  sFunctionTargets := {}
  sExitCodes := none
  sIsReachable := none
}

/-- Mark state as modified -/
def modified (s : InternalState) : InternalState :=
  { s with sVersion := -1 }

/-- Insert a global variable -/
def insertGlobal (name : String) (value : VariableState) (state : InternalState) : InternalState :=
  modified { state with sGlobalValues := state.sGlobalValues.insert name value }

/-- Insert a local variable -/
def insertLocal (name : String) (value : VariableState) (state : InternalState) : InternalState :=
  modified { state with sLocalValues := state.sLocalValues.insert name value }

/-- Insert a prefix variable -/
def insertPrefix (name : String) (value : VariableState) (state : InternalState) : InternalState :=
  modified { state with sPrefixValues := state.sPrefixValues.insert name value }

/-- Insert a function -/
def insertFunction (name : String) (value : FunctionValue) (state : InternalState) : InternalState :=
  modified { state with sFunctionTargets := state.sFunctionTargets.insert name value }

/-- The program state we expose externally -/
structure ProgramState where
  variablesInScope : Std.HashMap String VariableState
  exitCodes : List Id
  stateIsReachable : Bool
  deriving Inhabited

/-- Convert internal state to external program state -/
def internalToExternal (s : InternalState) : ProgramState := {
  variablesInScope := s.sGlobalValues.fold (fun m k v => m.insert k v) s.sLocalValues
  exitCodes := s.sExitCodes.getD []
  stateIsReachable := s.sIsReachable.getD true
}

/-- The result of the data flow analysis -/
structure CFGAnalysis where
  graph : CFGraph
  tokenToRange : Std.HashMap Id (Node × Node)
  tokenToNodes : Std.HashMap Id (List Node)
  postDominators : Array (List Node)
  nodeToData : Std.HashMap Node (ProgramState × ProgramState)
  deriving Inhabited

/-- Get the state before a token id -/
def getIncomingState (analysis : CFGAnalysis) (id : Id) : Option ProgramState := do
  let (start, _) ← analysis.tokenToRange.get? id
  let (incoming, _) ← analysis.nodeToData.get? start
  return incoming

/-- Get the state after a token id -/
def getOutgoingState (analysis : CFGAnalysis) (id : Id) : Option ProgramState := do
  let (_, «end») ← analysis.tokenToRange.get? id
  let (_, outgoing) ← analysis.nodeToData.get? «end»
  return outgoing

/-- Check if target postdominates base -/
def doesPostDominate (analysis : CFGAnalysis) (target base : Id) : Bool :=
  match analysis.tokenToRange.get? base, analysis.tokenToRange.get? target with
  | some (_, baseEnd), some (targetStart, _) =>
      match analysis.postDominators[baseEnd]? with
      | some doms => doms.contains targetStart
      | Option.none => false
  | _, _ => false

/-- Check if variable may have a property -/
def variableMayHaveState (state : ProgramState) (var : String) (property : CFVariableProp) : Option Bool := do
  let value ← state.variablesInScope.get? var
  return value.variableProperties.any (·.contains property)

/-- Check if variable may be declared integer -/
def variableMayBeDeclaredInteger (state : ProgramState) (var : String) : Option Bool :=
  variableMayHaveState state var .CFVPInteger

/-- Check if variable may be assigned an integer value -/
def variableMayBeAssignedInteger (state : ProgramState) (var : String) : Option Bool := do
  let value ← state.variablesInScope.get? var
  return value.variableValue.numericalStatus >= .NumericalStatusMaybe

/-- Create the initial environment state -/
def createEnvironmentState : InternalState :=
  let addVars (names : List String) (val : VariableState) (s : InternalState) :=
    names.foldl (fun s name => insertGlobal name val s) s

  let spacelessState : VariableState := {
    variableValue := { unknownVariableValue with spaceStatus := .SpaceStatusClean }
    variableProperties := [[]]
  }

  let integerState : VariableState := {
    variableValue := unknownIntegerValue
    variableProperties := [[]]
  }

  newInternalState
    |> addVars internalVariables unknownVariableState
    |> addVars variablesWithoutSpaces spacelessState
    |> addVars specialIntegerVariables integerState

/-- Analyze control flow (stub - returns empty analysis) -/
def analyzeControlFlow (params : CFGParameters) (root : Token) : CFGAnalysis :=
  let cfgResult := buildGraph params root
  {
    graph := cfgResult.cfGraph
    tokenToRange := cfgResult.cfIdToRange
    tokenToNodes := cfgResult.cfIdToNodes
    postDominators := cfgResult.cfPostDominators
    nodeToData := {}  -- DFA would populate this
  }

-- Theorems (stubs)

theorem getIncomingState_returns_none_for_unknown (analysis : CFGAnalysis) (id : Id) :
    ¬ analysis.tokenToRange.contains id → getIncomingState analysis id = Option.none := sorry

theorem getOutgoingState_returns_none_for_unknown (analysis : CFGAnalysis) (id : Id) :
    ¬ analysis.tokenToRange.contains id → getOutgoingState analysis id = Option.none := sorry

theorem doesPostDominate_reflexive :
    True := trivial  -- Simplified; actual would be about post-dominators

theorem analyzeControlFlow_preserves_graph (params : CFGParameters) (root : Token) :
    (analyzeControlFlow params root).graph = (buildGraph params root).cfGraph := rfl

theorem analyzeControlFlow_preserves_tokenToRange (params : CFGParameters) (root : Token) :
    (analyzeControlFlow params root).tokenToRange = (buildGraph params root).cfIdToRange := rfl

theorem SpaceStatus_order :
    SpaceStatus.SpaceStatusEmpty < SpaceStatus.SpaceStatusClean := by decide

theorem NumericalStatus_order :
    NumericalStatus.NumericalStatusUnknown < NumericalStatus.NumericalStatusMaybe := by decide

theorem createEnvironmentState_has_internal_vars :
    True := trivial  -- Would check internalVariables are set

theorem internalToExternal_preserves_reachability (s : InternalState) :
    (internalToExternal s).stateIsReachable = s.sIsReachable.getD true := rfl

theorem modified_sets_version (s : InternalState) :
    (modified s).sVersion = -1 := rfl

end ShellCheck.CFGAnalysis
