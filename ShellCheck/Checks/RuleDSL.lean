import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.AnalyzerLib
import ShellCheck.Interface

namespace ShellCheck.Checks.RuleDSL

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.Interface

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

def pipelineMatches (pattern : List String) (cmds : List Token) (requireLeading : Bool := false) : Bool :=
  let names := pipelineNames cmds
  if requireLeading then
    hasLeadingSequence pattern names
  else
    hasSubsequence pattern names

def pipelineTargets (name : String) (cmds : List Token) : List Token :=
  cmds.filterMap fun c =>
    if getCommandBasename c == some name then some c else none

end ShellCheck.Checks.RuleDSL
