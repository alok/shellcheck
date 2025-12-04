/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Parser types for ShellCheck
-/

import ShellCheck.AST
import ShellCheck.Interface
import Std.Data.HashMap

namespace ShellCheck.Parser.Types

open ShellCheck.AST
open ShellCheck.Interface

/-- Source position in the input -/
structure SourcePos where
  name : String
  line : Nat
  column : Nat
  deriving Repr, BEq, Inhabited

def SourcePos.initial (name : String) : SourcePos :=
  { name := name, line := 1, column := 1 }

/-- A parse note (error/warning during parsing) -/
structure ParseNote where
  startPos : SourcePos
  endPos : SourcePos
  severity : Severity
  code : Code
  message : String
  deriving Repr, BEq, Inhabited

/-- Context for parsing (for error messages) -/
inductive Context where
  | contextName : SourcePos → String → Context
  | contextAnnotation : List Annotation → Context
  | contextSource : String → Context
  deriving Repr, BEq, Inhabited

/-- Here document pending context -/
structure HereDocContext where
  id : Id
  dashed : Dashed
  quoted : Quoted
  endToken : String
  contexts : List Context
  deriving Repr, Inhabited

/-- User state for the parser -/
structure UserState where
  lastId : Int
  positionMap : Std.HashMap Id (SourcePos × SourcePos)
  parseNotes : List ParseNote
  hereDocMap : Std.HashMap Id (List Token)
  pendingHereDocs : List HereDocContext
  deriving Inhabited

/-- Initial user state -/
def initialUserState : UserState := {
  lastId := -1
  positionMap := {}
  parseNotes := []
  hereDocMap := {}
  pendingHereDocs := []
}

/-- System state (context stack) -/
structure SystemState where
  contextStack : List Context
  parseProblems : List ParseNote
  deriving Inhabited

/-- Initial system state -/
def initialSystemState : SystemState := {
  contextStack := []
  parseProblems := []
}

/-- Environment for parsing -/
structure Environment (m : Type → Type) where
  systemInterface : SystemInterface m
  checkSourced : Bool
  ignoreRC : Bool
  currentFilename : String
  shellTypeOverride : Option Shell

/-- Default environment (requires monad with SystemInterface) -/
instance [Inhabited (SystemInterface m)] : Inhabited (Environment m) where
  default := {
    systemInterface := default
    checkSourced := false
    ignoreRC := false
    currentFilename := ""
    shellTypeOverride := none
  }

/-- Parse result from the lexer/parser -/
inductive ParseResult (α : Type) where
  | success : α → SourcePos → String → ParseResult α
  | error : SourcePos → String → ParseResult α
  deriving Repr, Inhabited

/-- The parser monad stack -/
-- Simplified: just StateT over a base monad
abbrev SCParser (m : Type → Type) [Monad m] (α : Type) :=
  StateT UserState (StateT SystemState m) α

-- Theorems (stubs)

theorem initialUserState_lastId_negative :
    initialUserState.lastId < 0 := by decide

theorem initialUserState_no_notes :
    initialUserState.parseNotes = [] := rfl

theorem initialSystemState_empty_context :
    initialSystemState.contextStack = [] := rfl

theorem SourcePos_initial_line_one (name : String) :
    (SourcePos.initial name).line = 1 := rfl

theorem SourcePos_initial_column_one (name : String) :
    (SourcePos.initial name).column = 1 := rfl

end ShellCheck.Parser.Types
