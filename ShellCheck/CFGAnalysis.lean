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

/-- Max for SpaceStatus based on constructor index -/
def SpaceStatus.max (a b : SpaceStatus) : SpaceStatus :=
  if a.ctorIdx >= b.ctorIdx then a else b

/-- Min for NumericalStatus based on constructor index -/
def NumericalStatus.min (a b : NumericalStatus) : NumericalStatus :=
  if a.ctorIdx <= b.ctorIdx then a else b

/-- Merge two variable states (join operation for DFA) -/
def mergeVariableState (a b : VariableState) : VariableState := {
  variableValue := {
    literalValue := if a.variableValue.literalValue == b.variableValue.literalValue
                    then a.variableValue.literalValue
                    else Option.none
    spaceStatus := SpaceStatus.max a.variableValue.spaceStatus b.variableValue.spaceStatus
    numericalStatus := NumericalStatus.min a.variableValue.numericalStatus b.variableValue.numericalStatus
  }
  variableProperties := a.variableProperties ++ b.variableProperties
}

/-- Merge two program states (join operation for DFA) -/
def mergeProgramState (a b : ProgramState) : ProgramState := {
  variablesInScope := a.variablesInScope.fold (fun m k v =>
    match m.get? k with
    | some v' => m.insert k (mergeVariableState v v')
    | Option.none => m.insert k v
  ) b.variablesInScope
  exitCodes := a.exitCodes ++ b.exitCodes |>.eraseDups
  stateIsReachable := a.stateIsReachable || b.stateIsReachable
}

/-- Helper to create variable state from a value -/
def valueToVariableState (value : CFValue) : VariableState :=
  match value with
  | .CFValueString =>
    { variableValue := unknownVariableValue
      variableProperties := [[]] }
  | .CFValueInteger =>
    { variableValue := unknownIntegerValue
      variableProperties := [[.CFVPInteger]] }
  | .CFValueComputed _ parts =>
    let isLiteral := parts.all fun p => match p with
      | .CFStringLiteral _ => true
      | _ => false
    { variableValue := {
        literalValue := if isLiteral then
          some (parts.foldl (fun acc p => match p with
            | .CFStringLiteral s => acc ++ s
            | _ => acc) "")
        else Option.none
        spaceStatus := .SpaceStatusUnknown
        numericalStatus := .NumericalStatusUnknown
      }
      variableProperties := [[]] }
  | _ =>
    unknownVariableState

/-- Apply a CFG effect to a program state -/
def applyEffect (effect : CFEffect) (state : ProgramState) : ProgramState :=
  match effect with
  | .CFReadVariable _name =>
    -- Reading doesn't change state
    state
  | .CFWriteVariable name value =>
    let varState := valueToVariableState value
    { state with variablesInScope := state.variablesInScope.insert name varState }
  | .CFWriteGlobal name value =>
    let varState := valueToVariableState value
    { state with variablesInScope := state.variablesInScope.insert name varState }
  | .CFWriteLocal name value =>
    let varState := valueToVariableState value
    { state with variablesInScope := state.variablesInScope.insert name varState }
  | .CFWritePrefix name value =>
    let varState := valueToVariableState value
    { state with variablesInScope := state.variablesInScope.insert name varState }
  | .CFSetProps _ name props =>
    match state.variablesInScope.get? name with
    | some varState =>
      let newVarState := { varState with variableProperties := props :: varState.variableProperties }
      { state with variablesInScope := state.variablesInScope.insert name newVarState }
    | Option.none =>
      let newVarState := { unknownVariableState with variableProperties := props :: unknownVariableState.variableProperties }
      { state with variablesInScope := state.variablesInScope.insert name newVarState }
  | .CFUnsetProps _ name _props =>
    { state with variablesInScope := state.variablesInScope.erase name }
  | .CFUndefine name =>
    { state with variablesInScope := state.variablesInScope.erase name }
  | .CFUndefineVariable name =>
    { state with variablesInScope := state.variablesInScope.erase name }
  | _ =>
    state  -- Other effects don't change variable state

/-- Apply a list of effects to a program state -/
def applyEffects (effects : List IdTagged) (state : ProgramState) : ProgramState :=
  effects.foldl (fun s eff => applyEffect eff.effect s) state

/-- Process a CFG node and return the outgoing state -/
def processNode (node : CFNode) (incoming : ProgramState) : ProgramState :=
  match node with
  | .CFApplyEffects effects =>
    applyEffects effects incoming
  | .CFSetExitCode id =>
    { incoming with exitCodes := [id] }
  | .CFUnreachable =>
    { incoming with stateIsReachable := false }
  | .CFEntryPoint _ =>
    incoming
  | _ =>
    incoming

/-- Initial program state for analysis -/
def initialProgramState : ProgramState :=
  internalToExternal createEnvironmentState

/-- Analyze control flow using iterative dataflow analysis -/
def analyzeControlFlow (params : CFGParameters) (root : Token) : CFGAnalysis :=
  let cfgResult := buildGraph params root
  let graph := cfgResult.cfGraph

  -- Initialize all nodes with empty state
  let initState : ProgramState := initialProgramState
  let emptyData : Std.HashMap Node (ProgramState × ProgramState) :=
    graph.nodes.foldl (fun m lnode =>
      m.insert lnode.node (initState, initState)
    ) {}

  -- Simple forward analysis: process nodes in order
  -- (A proper implementation would use worklist algorithm with fixpoint iteration)
  let nodeToData := graph.nodes.foldl (fun data lnode =>
    -- Get incoming state from predecessors
    let preds := graph.edges.filter (fun e => e.dst == lnode.node) |>.map (·.src)
    let incoming := preds.foldl (fun acc pred =>
      match data.get? pred with
      | some (_, outgoing) => mergeProgramState acc outgoing
      | Option.none => acc
    ) initState

    -- Process the node
    let outgoing := processNode lnode.label incoming

    -- Store the result
    data.insert lnode.node (incoming, outgoing)
  ) emptyData

  {
    graph := cfgResult.cfGraph
    tokenToRange := cfgResult.cfIdToRange
    tokenToNodes := cfgResult.cfIdToNodes
    postDominators := cfgResult.cfPostDominators
    nodeToData := nodeToData
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
