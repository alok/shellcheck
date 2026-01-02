import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.AnalyzerLib
import ShellCheck.Interface

namespace ShellCheck.Checks.RuleDSL

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.Interface

class ToNames (α : Type) where
  toNames : α → List String

instance : ToNames (List String) where
  toNames names := names

instance : ToNames (Array String) where
  toNames names := names.toList

instance : ToNames String where
  toNames name := [name]

structure PipelineView where
  cmds : List Token
  names : List String

def pipelineCommands (t : Token) : Option (List Token) :=
  match t.inner with
  | .T_Pipeline _ cmds => some cmds
  | _ => none

def pipelineNames (cmds : List Token) : List String :=
  cmds.filterMap getCommandBasename

def pipelineView (t : Token) : Option PipelineView :=
  pipelineCommands t |>.map (fun cmds => { cmds := cmds, names := pipelineNames cmds })

def hasSubsequence (pattern : List String) (names : List String) : Bool :=
  match pattern with
  | [] => true
  | p :: ps =>
      match names with
      | [] => false
      | n :: ns =>
          if n == p then
            hasSubsequence ps ns
          else
            hasSubsequence pattern ns

def hasLeadingSequence (pattern : List String) (names : List String) : Bool :=
  match pattern, names with
  | [], _ => true
  | p :: ps, n :: ns =>
      if p == n then
        hasSubsequence ps ns
      else
        false
  | _, [] => false

def pipelineMatchesList (pattern : List String) (cmds : List Token) (requireLeading : Bool := false) : Bool :=
  let names := pipelineNames cmds
  if requireLeading then
    hasLeadingSequence pattern names
  else
    hasSubsequence pattern names

def pipelineMatches {α : Type} [ToNames α] (pattern : α) (cmds : List Token) (requireLeading : Bool := false) : Bool :=
  pipelineMatchesList (ToNames.toNames pattern) cmds (requireLeading := requireLeading)

def pipelineTargets (name : String) (cmds : List Token) : List Token :=
  cmds.filterMap fun c =>
    if getCommandBasename c == some name then some c else none

def pipelineRule {α : Type} [ToNames α] (code : Code) (severity : Severity) (message : String)
    (pattern : α) (targetName : String) (requireLeading : Bool := false)
    : Token → List TokenComment :=
  fun t =>
    match pipelineCommands t with
    | some cmds =>
      if pipelineMatches pattern cmds (requireLeading := requireLeading) then
        pipelineTargets targetName cmds |>.map fun c =>
            makeComment severity c.id code message
        else []
    | none => []

end ShellCheck.Checks.RuleDSL
