/-
  Process substitution parser for ShellCheck
  Handles <(command) and >(command)
-/

import ShellCheck.AST

namespace ShellCheck.Parser.ProcessSub

open ShellCheck.AST

/-- Direction of process substitution -/
inductive ProcessDirection where
  | input   -- <(cmd) - provides input (read from command output)
  | output  -- >(cmd) - provides output (write to command input)
  deriving Repr, BEq, Inhabited

/-- Parsed process substitution -/
structure ParsedProcessSub where
  direction : ProcessDirection
  command : String  -- The command inside
  deriving Repr, Inhabited

/-- Get character at position -/
def getCharAt (s : String) (pos : Nat) : Option Char :=
  if pos < s.length then some (s.toList.getD pos ' ') else none

/-- Parser state -/
structure ProcState where
  input : String
  pos : Nat
  deriving Repr, Inhabited

/-- Result type -/
inductive ProcResult (α : Type) where
  | ok : α → ProcState → ProcResult α
  | error : String → ProcState → ProcResult α
  deriving Repr, Inhabited, Nonempty

/-- Process sub parser monad -/
def ProcParser (α : Type) := ProcState → ProcResult α

instance : Monad ProcParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative ProcParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Peek at current character -/
def peek : ProcParser (Option Char) := fun s =>
  .ok (getCharAt s.input s.pos) s

/-- Consume current character -/
def anyChar : ProcParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error "unexpected end" s
  | some c => .ok c { s with pos := s.pos + 1 }

/-- Consume specific character -/
def char (c : Char) : ProcParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error s!"expected '{c}'" s
  | some actual =>
      if actual == c then .ok c { s with pos := s.pos + 1 }
      else .error s!"expected '{c}'" s

/-- Take until matching paren (handles nesting) -/
partial def takeUntilMatchingParen : ProcParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) (depth : Nat) : ProcResult String :=
    match getCharAt s.input pos with
    | none => .error "unclosed process substitution" s
    | some c =>
        if c == ')' then
          if depth == 0 then
            .ok (String.ofList acc.reverse) { s with pos := pos }
          else
            go (pos + 1) (c :: acc) (depth - 1)
        else if c == '(' then
          go (pos + 1) (c :: acc) (depth + 1)
        else
          go (pos + 1) (c :: acc) depth
  go s.pos [] 0

/-- Parse process substitution -/
def parseProcessSub : ProcParser ParsedProcessSub := fun s =>
  match getCharAt s.input s.pos with
  | none => .error "unexpected end" s
  | some '<' =>
      match getCharAt s.input (s.pos + 1) with
      | some '(' =>
          let s' := { s with pos := s.pos + 2 }
          match takeUntilMatchingParen s' with
          | .ok cmd s'' =>
              match getCharAt s''.input s''.pos with
              | some ')' =>
                  .ok { direction := .input, command := cmd } { s'' with pos := s''.pos + 1 }
              | _ => .error "expected ')'" s''
          | .error msg s'' => .error msg s''
      | _ => .error "expected '(' after '<'" s
  | some '>' =>
      match getCharAt s.input (s.pos + 1) with
      | some '(' =>
          let s' := { s with pos := s.pos + 2 }
          match takeUntilMatchingParen s' with
          | .ok cmd s'' =>
              match getCharAt s''.input s''.pos with
              | some ')' =>
                  .ok { direction := .output, command := cmd } { s'' with pos := s''.pos + 1 }
              | _ => .error "expected ')'" s''
          | .error msg s'' => .error msg s''
      | _ => .error "expected '(' after '>'" s
  | _ => .error "expected '<(' or '>(' for process substitution" s

/-- Parse process substitution from string -/
def parse (input : String) : Option ParsedProcessSub :=
  let state : ProcState := { input, pos := 0 }
  match parseProcessSub state with
  | .ok result _ => some result
  | .error _ _ => none

/-- Check if string starts with process substitution -/
def startsWithProcessSub (s : String) : Bool :=
  (s.startsWith "<(" || s.startsWith ">(")

/-- Check if at position we have process substitution (not redirect + subshell) -/
def isProcessSubAt (s : String) (pos : Nat) : Bool :=
  match getCharAt s pos with
  | some '<' =>
      match getCharAt s (pos + 1) with
      | some '(' => true
      | _ => false
  | some '>' =>
      match getCharAt s (pos + 1) with
      | some '(' => true
      | _ => false
  | _ => false

/-- Convert direction to string -/
def ProcessDirection.toString : ProcessDirection → String
  | .input => "<"
  | .output => ">"

instance : ToString ProcessDirection := ⟨ProcessDirection.toString⟩

end ShellCheck.Parser.ProcessSub
