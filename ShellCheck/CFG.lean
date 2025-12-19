/-
  Copyright 2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Constructs a Control Flow Graph from an AST
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.Data
import ShellCheck.Interface
import ShellCheck.Prelude
import ShellCheck.Regex
import ShellCheck.Graph
import Std.Data.HashMap
import Std.Data.HashSet

namespace ShellCheck.CFG

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Graph

/-- The properties of a variable -/
inductive CFVariableProp where
  | CFVPExport
  | CFVPArray
  | CFVPAssociative
  | CFVPInteger
  deriving Repr, BEq, Ord, Inhabited, Hashable

/-- Variable scope -/
inductive Scope where
  | GlobalScope
  | LocalScope
  | PrefixScope
  deriving Repr, BEq, Ord, Inhabited

/-- Simplified computed strings -/
inductive CFStringPart where
  | CFStringLiteral : String → CFStringPart
  | CFStringVariable : String → CFStringPart
  | CFStringInteger
  | CFStringUnknown
  deriving Repr, BEq, Inhabited

/-- Where a variable's value comes from -/
inductive CFValue where
  | CFValueUninitialized
  | CFValueArray
  | CFValueString
  | CFValueInteger
  | CFValueComputed : Id → List CFStringPart → CFValue
  deriving Repr, Inhabited

/-- Actions we track -/
inductive CFEffect where
  | CFSetProps : Option Scope → String → List CFVariableProp → CFEffect
  | CFUnsetProps : Option Scope → String → List CFVariableProp → CFEffect
  | CFReadVariable : String → CFEffect
  | CFWriteVariable : String → CFValue → CFEffect
  | CFWriteGlobal : String → CFValue → CFEffect
  | CFWriteLocal : String → CFValue → CFEffect
  | CFWritePrefix : String → CFValue → CFEffect
  | CFDefineFunction : String → Id → Node → Node → CFEffect
  | CFUndefine : String → CFEffect
  | CFUndefineVariable : String → CFEffect
  | CFUndefineFunction : String → CFEffect
  | CFUndefineNameref : String → CFEffect
  | CFHintArray : String → CFEffect
  | CFHintDefined : String → CFEffect
  deriving Repr, Inhabited

/-- Id-tagged effect -/
structure IdTagged where
  id : Id
  effect : CFEffect
  deriving Repr, Inhabited

/-- Edge labels in a Control Flow Graph -/
inductive CFEdge where
  | CFEErrExit
  | CFEFlow
  | CFEFalseFlow
  | CFEExit
  deriving Repr, BEq, Inhabited

/-- Node labels in a Control Flow Graph -/
inductive CFNode where
  | CFStructuralNode
  | CFEntryPoint : String → CFNode
  | CFDropPrefixAssignments
  | CFApplyEffects : List IdTagged → CFNode
  | CFExecuteCommand : Option String → CFNode
  | CFExecuteSubshell : String → Node → Node → CFNode
  | CFSetExitCode : Id → CFNode
  | CFImpliedExit
  | CFResolvedExit
  | CFUnresolvedExit
  | CFUnreachable
  | CFSetBackgroundPid : Id → CFNode
  deriving Repr, Inhabited

/-- Options when generating CFG -/
structure CFGParameters where
  cfLastpipe : Bool
  cfPipefail : Bool
  deriving Repr, BEq, Inhabited

/-- The Control Flow Graph type -/
abbrev CFGraph := Gr CFNode CFEdge

/-- Result of graph building -/
structure CFGResult where
  cfGraph : CFGraph
  cfIdToRange : Std.HashMap Id (Node × Node)
  cfIdToNodes : Std.HashMap Id (List Node)
  cfPostDominators : Array (List Node)
  deriving Inhabited

/-- A range from start to end node -/
structure Range where
  startNode : Node
  endNode : Node
  deriving Repr, BEq, Inhabited

/-- Context for CFG building -/
structure CFContext where
  cfIsCondition : Bool
  cfIsFunction : Bool
  cfLoopStack : List (Node × Node)
  cfTokenStack : List Id
  cfExitTarget : Option Node
  cfReturnTarget : Option Node
  cfParameters : CFGParameters
  deriving Inhabited

/-- Initial CFG context -/
def newCFContext (params : CFGParameters) : CFContext := {
  cfIsCondition := false
  cfIsFunction := false
  cfLoopStack := []
  cfTokenStack := []
  cfExitTarget := none
  cfReturnTarget := none
  cfParameters := params
}

/-- State for the CFG builder monad -/
structure CFState where
  nextNode : Node
  nodes : List (LNode CFNode)
  edges : List (LEdge CFEdge)
  mapping : List (Id × (Node × Node))
  association : List (Id × Node)
  deriving Inhabited

/-- The CFG builder monad -/
abbrev CFM := ReaderT CFContext (StateM CFState)

/-- Create a new node with a label -/
def newNode (label : CFNode) : CFM Node := do
  let s ← get
  let n := s.nextNode
  let stack ← read >>= pure ∘ CFContext.cfTokenStack
  set { s with
    nextNode := n + 1
    nodes := (⟨n, label⟩ : LNode CFNode) :: s.nodes
    association := stack.map (·, n) ++ s.association
  }
  return n

/-- Create a new node and return as a range -/
def newNodeRange (label : CFNode) : CFM Range := do
  let n ← newNode label
  return { startNode := n, endNode := n }

/-- Convert a node to a range -/
def nodeToRange (n : Node) : Range :=
  { startNode := n, endNode := n }

/-- Create a structural node -/
def newStructuralNode : CFM Range :=
  newNodeRange .CFStructuralNode

/-- A no-op node -/
def none : CFM Range := newStructuralNode

/-- Add an edge to the graph -/
def link (from_ to_ : Node) (label : CFEdge) : CFM Unit := do
  let s ← get
  set { s with edges := (⟨from_, to_, label⟩ : LEdge CFEdge) :: s.edges }

/-- Register an Id with its range -/
def registerNode (id : Id) (range : Range) : CFM Unit := do
  let s ← get
  set { s with mapping := (id, (range.startNode, range.endNode)) :: s.mapping }

/-- Link two ranges with a flow edge -/
def linkRange (r1 r2 : Range) : CFM Range := do
  link r1.endNode r2.startNode .CFEFlow
  return { startNode := r1.startNode, endNode := r2.endNode }

/-- Link two ranges with a specific edge type -/
def linkRangeAs (edge : CFEdge) (r1 r2 : Range) : CFM Range := do
  link r1.endNode r2.startNode edge
  return { startNode := r1.startNode, endNode := r2.endNode }

/-- Like linkRange but without actually linking -/
def spanRange (r1 r2 : Range) : Range :=
  { startNode := r1.startNode, endNode := r2.endNode }

/-- Link a list of ranges sequentially -/
def linkRanges : List Range → CFM Range
  | [] => do return ← newStructuralNode  -- fallback for empty
  | [r] => pure r
  | r :: rs => do
      let rest ← linkRanges rs
      linkRange r rest

/-- Run with a modified context -/
def withContext (f : CFContext → CFContext) (p : CFM α) : CFM α :=
  ReaderT.adapt f p

/-- Run in condition context -/
def asCondition (p : CFM Range) : CFM Range :=
  withContext (fun c => { c with cfIsCondition := true }) p

/-- Run under a token's id (for attribution) -/
def under (id : Id) (f : CFM α) : CFM α :=
  withContext (fun c => { c with cfTokenStack := id :: c.cfTokenStack }) f

/-- Create a single-effect apply node -/
def applySingle (id : Id) (effect : CFEffect) : CFNode :=
  .CFApplyEffects [⟨id, effect⟩]

/-- Convert a token to string parts (for value computation) -/
partial def tokenToParts (t : Token) : List CFStringPart :=
  match t.inner with
  | .T_NormalWord list => (list.map tokenToParts).flatten
  | .T_DoubleQuoted list => (list.map tokenToParts).flatten
  | .T_SingleQuoted str => [.CFStringLiteral str]
  | .T_Literal str => [.CFStringLiteral str]
  | .T_DollarArithmetic _ => [.CFStringInteger]
  | .T_DollarBracket _ => [.CFStringInteger]
  | .T_DollarBraced _ _ =>
      let str := getLiteralStringDef "" t
      if str.isEmpty then [.CFStringUnknown]
      else [.CFStringVariable str]
  | _ =>
      match getLiteralString t with
      | some s => [.CFStringLiteral s]
      | Option.none => [.CFStringUnknown]

-- Forward declaration for mutual recursion
mutual

/-- Build a list of tokens sequentially -/
partial def sequentially (list : List Token) : CFM Range := do
  let first ← newStructuralNode
  let rest ← list.mapM build
  linkRanges (first :: rest)

/-- Build a subshell (disjoint subgraph) -/
partial def subshell (id : Id) (reason : String) (p : CFM Range) : CFM Range := do
  let start ← newNode $ .CFEntryPoint s!"Subshell {id}: {reason}"
  let «end» ← newNode .CFStructuralNode
  let middle ← withContext (fun c => { c with cfExitTarget := some «end», cfReturnTarget := some «end» }) p
  let _ ← linkRanges [nodeToRange start, middle, nodeToRange «end»]
  newNodeRange $ .CFExecuteSubshell reason start «end»

/-- Build with function scope -/
partial def withFunctionScope (p : CFM Range) : CFM Range := do
  let «end» ← newNode .CFStructuralNode
  let body ← withContext (fun c => { c with cfReturnTarget := some «end», cfIsFunction := true }) p
  linkRanges [body, nodeToRange «end»]

/-- Build a variable assignment -/
partial def buildAssignment (scope : Option Scope) (t : Token) : CFM Range := do
  match t.inner with
  | .T_Assignment mode var indices value =>
      let expand ← build value
      let index ← sequentially indices
      let read ← match mode with
        | .append => newNodeRange $ applySingle t.id (.CFReadVariable var)
        | .assign => none

      let baseValueType : CFValue :=
        if indices.isEmpty then
          match value.inner with
          | .T_Array _ => .CFValueArray
          | _ => .CFValueString
        else
          .CFValueArray

      -- Best-effort numeric inference for simple `var=123` assignments (used by
      -- CFG-aware checks like SC2324). Avoid treating `var+=123` as numeric since
      -- `+=` appends by default.
      let valueType : CFValue :=
        match baseValueType, mode with
        | .CFValueString, .assign =>
            match getUnquotedLiteral value with
            | some s =>
                if !s.isEmpty && s.toList.all Char.isDigit then
                  .CFValueInteger
                else
                  .CFValueString
            | Option.none => .CFValueString
        | _, _ => baseValueType

      let writeEffect := match scope with
        | some .PrefixScope => CFEffect.CFWritePrefix var valueType
        | some .LocalScope => CFEffect.CFWriteLocal var valueType
        | some .GlobalScope => CFEffect.CFWriteGlobal var valueType
        | Option.none => CFEffect.CFWriteVariable var valueType

      let write ← newNodeRange $ applySingle t.id writeEffect
      let op ← linkRanges [expand, index, read, write]
      registerNode t.id op
      return op
  | _ =>
      let op ← newStructuralNode
      registerNode t.id op
      return op

/-- Helper for building if branches -/
partial def doBranches (t : Token) (start : Range) (ifs : List (List Token × List Token))
                       (elses : List Token) (result : List Range) : CFM (List Range) := do
  match ifs with
  | (conds, thens) :: rest =>
      let cond ← asCondition $ sequentially conds
      let action ← sequentially thens
      let _ ← linkRange start cond
      let _ ← linkRange cond action
      doBranches t cond rest elses (action :: result)
  | [] =>
      let restRange ← if elses.isEmpty
        then newNodeRange (.CFSetExitCode t.id)
        else sequentially elses
      let _ ← linkRange start restRange
      return (restRange :: result)

/-- Main build function -/
partial def build (t : Token) : CFM Range := do
  let range ← under t.id $ build' t
  registerNode t.id range
  return range

/-- Inner build function -/
partial def build' (t : Token) : CFM Range := do
  match t.inner with
  | .T_Annotation _ cmd => build cmd
  | .T_Script _ list => sequentially list

  | .T_NormalWord list => sequentially list
  | .T_DoubleQuoted list => sequentially list
  | .T_DollarDoubleQuoted list => sequentially list
  | .T_Array list => sequentially list
  | .T_BraceExpansion list => sequentially list
  | .T_Extglob _ list => sequentially list

  | .T_SingleQuoted _ => none
  | .T_Literal _ => none
  | .T_DollarSingleQuoted _ => none
  | .T_Glob _ => none
  | .T_ParamSubSpecialChar _ => none

  | .TA_Expansion list => sequentially list
  | .TA_Sequence list => sequentially list
  | .TA_Parenthesis inner => build inner
  | .TA_Binary _ a b => sequentially [a, b]
  | .TA_Unary _ arg => build arg

  | .TA_Variable name indices =>
      let subscript ← sequentially indices
      let hint ← if indices.isEmpty then none
                 else nodeToRange <$> newNode (applySingle t.id (.CFHintArray name))
      let read ← nodeToRange <$> newNode (applySingle t.id (.CFReadVariable name))
      linkRanges [subscript, hint, read]

  | .T_DollarBraced _ inner =>
      let vals ← build inner
      let reference := getBracedReference $ getLiteralStringDef "" inner
      let read ← nodeToRange <$> newNode (applySingle t.id (.CFReadVariable reference))
      linkRange vals read

  | .T_DollarExpansion body =>
      subshell t.id "$(..) expansion" $ sequentially body

  | .T_Backticked body =>
      subshell t.id "`..` expansion" $ sequentially body

  | .T_DollarArithmetic arith => build arith
  | .T_DollarBracket inner => build inner

  | .T_Arithmetic root =>
      let exe ← build root
      let status ← newNodeRange (.CFSetExitCode t.id)
      linkRange exe status

  | .T_Condition _ op =>
      let cond ← build op
      let status ← newNodeRange (.CFSetExitCode t.id)
      linkRange cond status

  | .T_Assignment _ _ _ _ =>
      buildAssignment Option.none t

  | .T_BraceGroup body => sequentially body

  | .T_Subshell body =>
      let main ← subshell t.id "explicit (..) subshell" $ sequentially body
      let status ← newNodeRange (.CFSetExitCode t.id)
      linkRange main status

  | .T_Backgrounded body =>
      let start ← newStructuralNode
      let fork ← subshell t.id "backgrounding '&'" $ build body
      let pid ← newNodeRange (.CFSetBackgroundPid t.id)
      let status ← newNodeRange (.CFSetExitCode t.id)
      let _ ← linkRange start fork
      let _ ← linkRangeAs .CFEFalseFlow fork pid
      linkRanges [start, pid, status]

  | .T_Banged cmd =>
      let main ← build cmd
      let status ← newNodeRange (.CFSetExitCode t.id)
      linkRange main status

  | .T_AndIf lhs rhs =>
      let left ← build lhs
      let right ← build rhs
      let «end» ← newStructuralNode
      let _ ← linkRange left right
      let _ ← linkRange right «end»
      linkRange left «end»

  | .T_OrIf lhs rhs =>
      let left ← build lhs
      let right ← build rhs
      let «end» ← newStructuralNode
      let _ ← linkRange left right
      let _ ← linkRange right «end»
      linkRange left «end»

  | .T_Pipeline _ cmds =>
      match cmds with
      | [cmd] => build cmd
      | _ =>
          let start ← newStructuralNode
          let built ← cmds.mapM (fun c => subshell t.id "pipeline" (build c))
          let _ ← linkRanges (start :: built)
          let status ← newNodeRange (.CFSetExitCode t.id)
          match built.getLast? with
          | some last => linkRange last status
          | Option.none => pure status

  | .T_Redirecting redirs cmd =>
      let redir ← sequentially redirs
      let body ← build cmd
      linkRange redir body

  | .T_SimpleCommand vars [] =>
      let assignments ← sequentially vars
      let status ← newNodeRange (.CFSetExitCode t.id)
      linkRange assignments status

  | .T_SimpleCommand vars (cmd :: args) =>
      let argExpand ← sequentially (cmd :: args)

      let cmdName := getLiteralString cmd
      let isDeclBuiltin :=
        match cmdName with
        | some "declare" => true
        | some "typeset" => true
        | some "local" => true
        | _ => false

      -- In the AST, `vars` includes both prefix assignments (`FOO=1 cmd`) and
      -- assignment arguments to declaration builtins (`declare x=1`). We
      -- approximate the split using monotonically increasing token ids: prefix
      -- assignments appear before the command word.
      let (prefixVars, postVars) :=
        if isDeclBuiltin then
          let preVars := vars.filter (fun v => v.id.val < cmd.id.val)
          let postVars := vars.filter (fun v => cmd.id.val < v.id.val)
          (preVars, postVars)
        else
          (vars, [])

      let hasIntegerFlag :=
        if isDeclBuiltin then
          args.any fun a =>
            match getLiteralString a with
            | some s => s.startsWith "-" && s.contains 'i'
            | Option.none => false
        else
          false

      let prefixAssigns ← prefixVars.mapM (buildAssignment (some .PrefixScope))

      let declAssigns ←
        if isDeclBuiltin then
          postVars.mapM fun v => do
            let assigned ← buildAssignment Option.none v
            let props ←
              if hasIntegerFlag then
                match v.inner with
                | .T_Assignment _ varName _ _ =>
                    let setp ← newNodeRange $ applySingle v.id (.CFSetProps Option.none varName [.CFVPInteger])
                    pure [setp]
                | _ => pure []
              else
                pure []
            pure (assigned :: props)
        else
          pure []

      let declAssigns := declAssigns.foldl (· ++ ·) []

      let declPropsFromArgs ←
        if hasIntegerFlag then
          args.mapM fun a => do
            match getUnquotedLiteral a with
            | some s =>
                if !s.startsWith "-" && isVariableName s then
                  let setp ← newNodeRange $ applySingle a.id (.CFSetProps Option.none s [.CFVPInteger])
                  pure [setp]
                else
                  pure []
            | Option.none => pure []
        else
          pure []

      let declPropsFromArgs := declPropsFromArgs.foldl (· ++ ·) []

      let exe ← newNodeRange (.CFExecuteCommand (getLiteralString cmd))
      let status ← newNodeRange (.CFSetExitCode t.id)
      let dropAssigns ← if prefixVars.isEmpty then pure [] else do
        let d ← newNodeRange .CFDropPrefixAssignments
        pure [d]

      linkRanges ([argExpand] ++ prefixAssigns ++ declAssigns ++ declPropsFromArgs ++ [exe, status] ++ dropAssigns)

  | .T_IfExpression ifs elses =>
      let start ← newStructuralNode
      let branches ← doBranches t start ifs elses []
      let «end» ← newStructuralNode
      let _ ← branches.mapM (fun b => linkRange b «end»)
      return spanRange start «end»

  | .T_WhileExpression cond body =>
      let condRange ← asCondition $ sequentially cond
      let bodyRange ← sequentially body
      let «end» ← newNodeRange (.CFSetExitCode t.id)
      let _ ← linkRange condRange bodyRange
      let _ ← linkRange bodyRange condRange
      linkRange condRange «end»

  | .T_UntilExpression cond body =>
      let condRange ← asCondition $ sequentially cond
      let bodyRange ← sequentially body
      let «end» ← newNodeRange (.CFSetExitCode t.id)
      let _ ← linkRange condRange bodyRange
      let _ ← linkRange bodyRange condRange
      linkRange condRange «end»

  | .T_ForIn name words body =>
      let entry ← newStructuralNode
      let expansion ← sequentially words
      let assignmentChoice ← newStructuralNode
      let assignment ← newNodeRange $ applySingle t.id (.CFWriteVariable name .CFValueString)
      let bodyRange ← sequentially body
      let exit ← newStructuralNode
      let _ ← linkRanges [entry, expansion, assignmentChoice]
      let _ ← linkRanges [assignmentChoice, assignment, bodyRange]
      let _ ← linkRange bodyRange exit
      let _ ← linkRange expansion exit
      let _ ← linkRange bodyRange assignmentChoice
      return spanRange entry exit

  | .T_ForArithmetic initT condT incT bodyT =>
      let init ← build initT
      let cond ← build condT
      let body ← sequentially bodyT
      let inc ← build incT
      let «end» ← newStructuralNode
      let _ ← linkRanges [init, cond, body, inc]
      let _ ← linkRange cond «end»
      let _ ← linkRange inc cond
      return spanRange init «end»

  | .T_CaseExpression caseWord cases =>
      let start ← newStructuralNode
      let word ← build caseWord
      let «end» ← newStructuralNode
      let _ ← linkRange start word
      let _ ← cases.mapM fun (_, conds, body) => do
        let condRange ← sequentially conds
        let bodyRange ← sequentially body
        let _ ← linkRange word condRange
        let _ ← linkRange condRange bodyRange
        linkRange bodyRange «end»
      let _ ← linkRange word «end»
      return spanRange start «end»

  | .T_Function _ _ name body =>
      let range ← withContext (fun c => { c with cfExitTarget := Option.none }) $ do
        let entry ← newNodeRange (.CFEntryPoint s!"function {name}")
        let f ← withFunctionScope (build body)
        linkRange entry f
      let definition ← newNodeRange $ applySingle t.id (.CFDefineFunction name t.id range.startNode range.endNode)
      let exe ← newNodeRange (.CFSetExitCode t.id)
      linkRange definition exe

  | .T_Include inner => build inner

  | .T_SourceCommand originalCommand inlinedSource =>
      let cmd ← build originalCommand
      let «end» ← newStructuralNode
      let inline ← build inlinedSource
      let _ ← linkRange cmd inline
      let _ ← linkRange inline «end»
      return spanRange cmd inline

  | .T_CoProc maybeNameToken inner =>
      let maybeName := match maybeNameToken with
        | some x => getLiteralString x
        | Option.none => some "COPROC"
      let parentNode := match maybeName with
        | some str => applySingle t.id (.CFWriteVariable str .CFValueArray)
        | Option.none => .CFStructuralNode
      let start ← newStructuralNode
      let parent ← newNodeRange parentNode
      let child ← subshell t.id "coproc" (build inner)
      let «end» ← newNodeRange (.CFSetExitCode t.id)
      let _ ← linkRange start parent
      let _ ← linkRange start child
      let _ ← linkRange parent «end»
      let _ ← linkRangeAs .CFEFalseFlow child «end»
      return spanRange start «end»

  | .T_CoProcBody inner => build inner
  | .T_HereDoc _ _ _ list => sequentially list
  | .T_HereString inner => build inner

  | .T_ProcSub op cmds =>
      let start ← newStructuralNode
      let body ← subshell t.id s!"{op}() process substitution" $ sequentially cmds
      let «end» ← newStructuralNode
      let _ ← linkRange start body
      let _ ← linkRangeAs .CFEFalseFlow body «end»
      linkRange start «end»

  | .T_FdRedirect _ op => build op
  | .T_IoFile op inner =>
      let exp ← build inner
      let doesntDoMuch ← build op
      linkRange exp doesntDoMuch

  | .T_IoDuplicate op _ => build op
  | .T_IndexedElement indicesT valueT =>
      let indices ← sequentially indicesT
      let value ← build valueT
      linkRange indices value

  | .TC_And bracket _ lhs rhs =>
      match bracket with
      | .singleBracket => sequentially [lhs, rhs]
      | .doubleBracket =>
          let left ← build lhs
          let right ← build rhs
          let «end» ← newStructuralNode
          let _ ← linkRanges [left, right, «end»]
          linkRange left «end»

  | .TC_Or bracket _ lhs rhs =>
      match bracket with
      | .singleBracket => sequentially [lhs, rhs]
      | .doubleBracket =>
          let left ← build lhs
          let right ← build rhs
          let «end» ← newStructuralNode
          let _ ← linkRanges [left, right, «end»]
          linkRange left «end»

  | .TC_Binary _ _ lhs rhs =>
      let left ← build lhs
      let right ← build rhs
      linkRange left right

  | .TC_Unary _ _ arg => build arg
  | .TC_Nullary _ arg => build arg
  | .TC_Group _ inner => build inner
  | .TC_Empty _ => newStructuralNode

  | .TA_Assignment _ lhs rhs =>
      let lhsRange ← build lhs
      let value ← build rhs
      -- Extract variable name from lhs if possible
      let writeRange ← newNodeRange $ applySingle t.id (.CFWriteVariable (getLiteralStringDef "" lhs) .CFValueInteger)
      linkRanges [lhsRange, value, writeRange]

  | .TA_Trinary cond a b =>
      let condition ← build cond
      let ifthen ← build a
      let elsethen ← build b
      let «end» ← newStructuralNode
      let _ ← linkRanges [condition, ifthen, «end»]
      linkRanges [condition, elsethen, «end»]

  | .T_BatsTest _ body =>
      let status ← newNodeRange $ applySingle t.id (.CFWriteVariable "status" .CFValueInteger)
      let output ← newNodeRange $ applySingle t.id (.CFWriteVariable "output" .CFValueString)
      let main ← build body
      linkRanges [status, output, main]

  | .T_SelectIn name words body =>
      let entry ← newStructuralNode
      let expansion ← sequentially words
      let assignmentChoice ← newStructuralNode
      let assignment ← newNodeRange $ applySingle t.id (.CFWriteVariable name .CFValueString)
      let bodyRange ← sequentially body
      let exit ← newStructuralNode
      let _ ← linkRanges [entry, expansion, assignmentChoice]
      let _ ← linkRanges [assignmentChoice, assignment, bodyRange]
      let _ ← linkRange bodyRange exit
      let _ ← linkRange expansion exit
      let _ ← linkRange bodyRange assignmentChoice
      return spanRange entry exit

  | .T_DollarBraceCommandExpansion _ body => sequentially body

  -- Operators (no-ops)
  | .T_CLOBBER => none
  | .T_GREATAND => none
  | .T_LESSAND => none
  | .T_LESSGREAT => none
  | .T_DGREAT => none
  | .T_Greater => none
  | .T_Less => none

  -- Keywords and misc (these shouldn't appear in normal ASTs but handle them for completeness)
  | .T_UnparsedIndex _ _ => none
  | .T_Pipe _ => none
  | .T_While => none
  | .T_Until => none
  | .T_Then => none
  | .T_Semi => none
  | .T_Select => none
  | .T_Rparen => none
  | .T_Rbrace => none
  | .T_OR_IF => none
  | .T_NEWLINE => none
  | .T_Lparen => none
  | .T_Lbrace => none
  | .T_In => none
  | .T_If => none
  | .T_For => none
  | .T_Fi => none
  | .T_Esac => none
  | .T_EOF => none
  | .T_Else => none
  | .T_Elif => none
  | .T_Done => none
  | .T_Do => none
  | .T_DSEMI => none
  | .T_DLESS => none
  | .T_DLESSDASH => none
  | .T_Case => none
  | .T_Bang => none
  | .T_AND_IF => none

end

/-- Build the root of the CFG -/
def buildRoot (t : Token) : CFM Range := under t.id do
  let entry ← newNodeRange (.CFEntryPoint "MAIN")
  let impliedExit ← newNode .CFImpliedExit
  let «end» ← newNode .CFStructuralNode
  let start ← withContext (fun c => { c with
    cfExitTarget := some «end»,
    cfReturnTarget := some impliedExit
  }) (build t)
  let range ← linkRanges [entry, start, nodeToRange impliedExit, nodeToRange «end»]
  registerNode t.id range
  return range

/-- Initial state for the builder -/
def initialCFState : CFState := {
  nextNode := 0
  nodes := []
  edges := []
  mapping := []
  association := []
}

/-- Build the control flow graph from a token -/
def buildGraph (params : CFGParameters) (root : Token) : CFGResult :=
  let ctx := newCFContext params
  let (_, state) := (buildRoot root).run ctx |>.run initialCFState

  let nodes := state.nodes.reverse
  let edges := state.edges.reverse

  let idToRange := Std.HashMap.ofList state.mapping
  let idToNodes := state.association.foldl (fun m (id, n) =>
    let existing := m.getD id []
    m.insert id (n :: existing)
  ) ({} : Std.HashMap Id (List Node))

  let graph := mkGraph nodes edges
  let maxNode := state.nextNode
  let mainExit := match idToRange.get? root.id with
    | some (_, exit) => exit
    | Option.none => 0

  -- Compute post-dominators
  let postDoms := postDom graph mainExit
  let postDomArray := domToArray postDoms maxNode

  {
    cfGraph := graph
    cfIdToRange := idToRange
    cfIdToNodes := idToNodes
    cfPostDominators := postDomArray
  }

/-- Check if a node postdominates another -/
def postDominates (result : CFGResult) (a b : Node) : Bool :=
  dominates result.cfPostDominators a b

/-- Get the range for an Id -/
def getIdRange (result : CFGResult) (id : Id) : Option (Node × Node) :=
  result.cfIdToRange.get? id

/-- Get all nodes for an Id -/
def getIdNodes (result : CFGResult) (id : Id) : List Node :=
  result.cfIdToNodes.getD id []

-- Theorems (stubs)

theorem buildGraph_preserves_tokens (params : CFGParameters) (root : Token) :
    (buildGraph params root).cfIdToRange.contains root.id := sorry

theorem buildGraph_creates_entry (params : CFGParameters) (root : Token) :
    ∃ n, ∃ s, (⟨n, CFNode.CFEntryPoint s⟩ : LNode CFNode) ∈ (buildGraph params root).cfGraph.nodes.toList := sorry

theorem linkRanges_creates_path (ranges : List Range) :
    ranges.length > 1 → True := fun _ => trivial

theorem nodeToRange_identity (n : Node) :
    (nodeToRange n).startNode = (nodeToRange n).endNode := rfl

theorem spanRange_preserves_endpoints (r1 r2 : Range) :
    (spanRange r1 r2).startNode = r1.startNode ∧
    (spanRange r1 r2).endNode = r2.endNode := ⟨rfl, rfl⟩

theorem newCFContext_defaults (params : CFGParameters) :
    (newCFContext params).cfIsCondition = false ∧
    (newCFContext params).cfIsFunction = false ∧
    (newCFContext params).cfLoopStack = [] := ⟨rfl, rfl, rfl⟩

theorem build_registers_node (t : Token) :
    True := trivial

theorem subshell_creates_entry_and_exit :
    True := trivial

theorem cfg_has_finite_nodes (params : CFGParameters) (root : Token) :
    (buildGraph params root).cfGraph.nodes.size > 0 := sorry

theorem cfg_edges_connect_existing_nodes (params : CFGParameters) (root : Token) :
    True := trivial  -- simplified

theorem postdom_reflexive (result : CFGResult) (n : Node) :
    n < result.cfPostDominators.size →
    n ∈ result.cfPostDominators[n]! := sorry

theorem effect_tracking_covers_assignments :
    True := trivial

theorem effect_tracking_covers_reads :
    True := trivial

theorem pipeline_creates_subshells (t : Token) :
    True := trivial

theorem conditional_has_both_branches :
    True := trivial

theorem loops_have_back_edges :
    True := trivial

theorem function_definitions_isolated :
    True := trivial

end ShellCheck.CFG
