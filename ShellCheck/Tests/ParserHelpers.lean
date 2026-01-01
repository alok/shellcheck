import ShellCheck.AST
import ShellCheck.ASTLib

namespace ShellCheck.Tests.ParserHelpers

open ShellCheck.AST
open ShellCheck.ASTLib

def hasAnyDollarExpansion (t : Token) : Bool :=
  let scan : StateM Bool Token :=
    ShellCheck.AST.analyze
      (m := StateM Bool)
      (f := fun tok => do
        match tok.inner with
        | .T_DollarBraced _ _
        | .T_DollarExpansion _
        | .T_DollarArithmetic _
        | .T_DollarBracket _
        | .T_DollarSingleQuoted _
        | .T_DollarDoubleQuoted _
        | .T_DollarBraceCommandExpansion _ _ =>
            modify (fun _ => true)
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run false
  found

def firstHereDoc? (t : Token) : Option (Quoted × List Token) :=
  let scan : StateM (Option (Quoted × List Token)) Token :=
    ShellCheck.AST.analyze
      (m := StateM (Option (Quoted × List Token)))
      (f := fun tok => do
        match tok.inner with
        | .T_HereDoc _ quotedFlag _ content =>
            match (← get) with
            | some _ => pure ()
            | none => set (some (quotedFlag, content))
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run none
  found

def collectHereDocs (t : Token) : List (Quoted × List Token) :=
  let scan : StateM (List (Quoted × List Token)) Token :=
    ShellCheck.AST.analyze
      (m := StateM (List (Quoted × List Token)))
      (f := fun tok => do
        match tok.inner with
        | .T_HereDoc _ quotedFlag _ content =>
            modify (fun acc => (quotedFlag, content) :: acc)
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run []
  found.reverse

def firstExtglob? (t : Token) : Option (String × List Token) :=
  let scan : StateM (Option (String × List Token)) Token :=
    ShellCheck.AST.analyze
      (m := StateM (Option (String × List Token)))
      (f := fun tok => do
        match tok.inner with
        | .T_Extglob pattern parts =>
            match (← get) with
            | some _ => pure ()
            | none => set (some (pattern, parts))
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run none
  found

def firstProcSub? (t : Token) : Option (String × List Token) :=
  let scan : StateM (Option (String × List Token)) Token :=
    ShellCheck.AST.analyze
      (m := StateM (Option (String × List Token)))
      (f := fun tok => do
        match tok.inner with
        | .T_ProcSub dir cmds =>
            match (← get) with
            | some _ => pure ()
            | none => set (some (dir, cmds))
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run none
  found

def firstBraceExpansion? (t : Token) : Option (List Token) :=
  let scan : StateM (Option (List Token)) Token :=
    ShellCheck.AST.analyze
      (m := StateM (Option (List Token)))
      (f := fun tok => do
        match tok.inner with
        | .T_BraceExpansion parts =>
            match (← get) with
            | some _ => pure ()
            | none => set (some parts)
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run none
  found

def firstUnparsedIndex? (t : Token) : Option String :=
  let scan : StateM (Option String) Token :=
    ShellCheck.AST.analyze
      (m := StateM (Option String))
      (f := fun tok => do
        match tok.inner with
        | .T_UnparsedIndex _ content =>
            match (← get) with
            | some _ => pure ()
            | none => set (some content)
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run none
  found

end ShellCheck.Tests.ParserHelpers
