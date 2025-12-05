/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Core FullParser infrastructure with position tracking
-/

import ShellCheck.AST
import ShellCheck.Interface
import Std.Data.HashMap

namespace ShellCheck.Parser.Core

open ShellCheck.AST
open ShellCheck.Interface

/-- Parser state combined with token building -/
structure FullParserState where
  /-- Input string -/
  input : String
  /-- Current position in input -/
  pos : String.Pos.Raw
  /-- Current line number (1-indexed) -/
  line : Nat
  /-- Current column number (1-indexed) -/
  column : Nat
  /-- Next token ID to assign -/
  nextId : Nat
  /-- Map from token IDs to positions -/
  positions : Std.HashMap Id (Position × Position)
  /-- Current filename -/
  filename : String
  /-- Accumulated parse errors -/
  errors : List String
  deriving Inhabited

/-- Result of full parsing -/
inductive FullResult (α : Type) where
  | ok : α → FullParserState → FullResult α
  | error : String → FullParserState → FullResult α
  deriving Inhabited

/-- Full parser monad -/
def FullParser (α : Type) := FullParserState → FullResult α

instance : Monad FullParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative FullParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Create initial parser state -/
def mkFullState (input : String) (filename : String := "<stdin>") : FullParserState :=
  { input, pos := 0, line := 1, column := 1, nextId := 1,
    positions := {}, filename, errors := [] }

/-- Create a fresh token ID -/
def freshIdFull : FullParser Id := fun s =>
  let id := Id.mk s.nextId
  .ok id { s with nextId := s.nextId + 1 }

/-- Record a position for a token ID -/
def recordPosition (id : Id) (startLine startCol endLine endCol : Nat) : FullParser Unit := fun s =>
  let startPos : Position := { posFile := s.filename, posLine := startLine, posColumn := startCol }
  let endPos : Position := { posFile := s.filename, posLine := endLine, posColumn := endCol }
  .ok () { s with positions := s.positions.insert id (startPos, endPos) }

/-- Get current position -/
def currentPos : FullParser (Nat × Nat) := fun s =>
  .ok (s.line, s.column) s

/-- Check if at end of input -/
def isEofFull : FullParser Bool := fun s =>
  .ok (s.pos >= s.input.rawEndPos) s

/-- Peek at next character -/
def peekFull : FullParser (Option Char) := fun s =>
  if s.pos < s.input.rawEndPos then
    .ok (some (s.pos.get s.input)) s
  else
    .ok none s

/-- Consume a character -/
def anyCharFull : FullParser Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let c := s.pos.get s.input
    let newPos := s.pos.next s.input
    let (newLine, newCol) :=
      if c == '\n' then (s.line + 1, 1)
      else (s.line, s.column + 1)
    .ok c { s with pos := newPos, line := newLine, column := newCol }
  else
    .error "unexpected end of input" s

/-- Match a specific character -/
def charFull (c : Char) : FullParser Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let actual := s.pos.get s.input
    if actual == c then
      let newPos := s.pos.next s.input
      let (newLine, newCol) :=
        if c == '\n' then (s.line + 1, 1)
        else (s.line, s.column + 1)
      .ok c { s with pos := newPos, line := newLine, column := newCol }
    else
      .error s!"expected '{c}'" s
  else
    .error s!"expected '{c}'" s

/-- Match a string -/
partial def stringFull (str : String) : FullParser String := fun s =>
  let rec go (i : String.Pos.Raw) (state : FullParserState) : FullResult String :=
    if i >= str.rawEndPos then
      .ok str state
    else if state.pos >= state.input.rawEndPos then
      .error s!"expected \"{str}\"" s
    else
      let expected := i.get str
      let actual := state.pos.get state.input
      if expected == actual then
        let newPos := state.pos.next state.input
        let (newLine, newCol) :=
          if actual == '\n' then (state.line + 1, 1)
          else (state.line, state.column + 1)
        go (i.next str) { state with pos := newPos, line := newLine, column := newCol }
      else
        .error s!"expected \"{str}\"" s
  go 0 s

/-- Take characters while predicate holds -/
partial def takeWhileFull (p : Char → Bool) : FullParser String := fun s =>
  let rec go (acc : List Char) (state : FullParserState) : FullResult String :=
    if state.pos >= state.input.rawEndPos then
      .ok (String.ofList acc.reverse) state
    else
      let c := state.pos.get state.input
      if p c then
        let newPos := state.pos.next state.input
        let (newLine, newCol) :=
          if c == '\n' then (state.line + 1, 1)
          else (state.line, state.column + 1)
        go (c :: acc) { state with pos := newPos, line := newLine, column := newCol }
      else
        .ok (String.ofList acc.reverse) state
  go [] s

/-- Take at least one character while predicate holds -/
def takeWhile1Full (p : Char → Bool) : FullParser String := fun s =>
  match takeWhileFull p s with
  | .ok str s' => if str.isEmpty then .error "expected at least one character" s else .ok str s'
  | .error msg s' => .error msg s'

/-- Try parser with backtracking -/
def attemptFull (p : FullParser α) : FullParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Many combinator -/
partial def manyFull (p : FullParser α) : FullParser (List α) := fun s =>
  let rec go (acc : List α) (state : FullParserState) : FullResult (List α) :=
    match p state with
    | .ok a s' => go (a :: acc) s'
    | .error _ _ => .ok acc.reverse state
  go [] s

/-- Many1 combinator -/
def many1Full (p : FullParser α) : FullParser (List α) := do
  let first ← p
  let rest ← manyFull p
  pure (first :: rest)

/-- Optional combinator -/
def optionalFull (p : FullParser α) : FullParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Create a token with current position -/
def mkTokenFull (inner : InnerToken Token) : FullParser Token := do
  let (line, col) ← currentPos
  let id ← freshIdFull
  recordPosition id line col line col
  return ⟨id, inner⟩

/-- Run parser and return result -/
def runFullParser (p : FullParser α) (input : String) (filename : String := "<stdin>")
    : Option α × Std.HashMap Id (Position × Position) × List String :=
  let state := mkFullState input filename
  match p state with
  | .ok a s => (some a, s.positions, s.errors)
  | .error _ s => (none, s.positions, s.errors)

end ShellCheck.Parser.Core
