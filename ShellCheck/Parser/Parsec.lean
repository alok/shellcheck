/-
  Copyright 2024
  Lean 4 port

  Integration with Std.Internal.Parsec for shell parsing
  Provides position-tracking and MonadLift for nice combinators
-/

import Std.Internal.Parsec
import Std.Internal.Parsec.String
import ShellCheck.AST
import ShellCheck.Interface
import Std.Data.HashMap

namespace ShellCheck.Parser.Parsec

open ShellCheck.AST
open ShellCheck.Interface

/-!
## Position-Tracking Iterator

A wrapper around String.Iterator that tracks line/column numbers.
-/

/-- Iterator with position tracking -/
structure PosIterator where
  /-- The underlying string -/
  str : String
  /-- Current byte position -/
  pos : String.Pos.Raw
  /-- Current line number (1-indexed) -/
  line : Nat
  /-- Current column number (1-indexed) -/
  column : Nat
  deriving Repr, Inhabited

namespace PosIterator

/-- Create iterator at start of string -/
def create (s : String) : PosIterator :=
  { str := s, pos := 0, line := 1, column := 1 }

/-- Check if iterator has more input -/
@[inline]
def hasNext (it : PosIterator) : Bool :=
  it.pos < it.str.rawEndPos

/-- Get current character -/
@[inline]
def curr (it : PosIterator) : Char :=
  it.pos.get it.str

/-- Get current character with proof of hasNext -/
@[inline]
def curr' (it : PosIterator) (_ : it.hasNext) : Char :=
  it.pos.get it.str

/-- Advance iterator by one character -/
@[inline]
def next (it : PosIterator) : PosIterator :=
  if it.hasNext then
    let c := it.curr
    let newPos := it.pos.next it.str
    let (newLine, newCol) :=
      if c == '\n' then (it.line + 1, 1)
      else (it.line, it.column + 1)
    { it with pos := newPos, line := newLine, column := newCol }
  else
    it

/-- Advance iterator with proof -/
@[inline]
def next' (it : PosIterator) (_ : it.hasNext) : PosIterator :=
  let c := it.curr
  let newPos := it.pos.next it.str
  let (newLine, newCol) :=
    if c == '\n' then (it.line + 1, 1)
    else (it.line, it.column + 1)
  { it with pos := newPos, line := newLine, column := newCol }

end PosIterator

/-- Instance of Parsec.Input for PosIterator -/
instance : Std.Internal.Parsec.Input PosIterator Char String.Pos.Raw where
  pos it := it.pos
  next := PosIterator.next
  curr := PosIterator.curr
  hasNext := PosIterator.hasNext
  next' := PosIterator.next'
  curr' := PosIterator.curr'

/-!
## Parser Types

Extended parser with shellcheck-specific state.
-/

/-- Extra state for parsing -/
structure ParserState where
  /-- Next token ID to assign -/
  nextId : Nat
  /-- Map from token IDs to positions -/
  positions : Std.HashMap Id (Position × Position)
  /-- Current filename -/
  filename : String
  /-- Accumulated parse errors -/
  errors : List String
  deriving Inhabited

/-- Create initial parser state -/
def mkParserState (filename : String := "<stdin>") : ParserState :=
  { nextId := 1, positions := {}, filename, errors := [] }

/-- Base parser type using Parsec with position tracking -/
abbrev BaseParser := Std.Internal.Parsec PosIterator

/-- Nonempty instance for ParseResult -/
instance : Nonempty (Std.Internal.Parsec.ParseResult α PosIterator) :=
  ⟨.error default .eof⟩

/-- Parser with extra state -/
def Parser (α : Type) := ParserState → BaseParser (α × ParserState)

namespace Parser

/-- Pure value -/
@[inline]
protected def pure (a : α) : Parser α := fun st it =>
  .success it (a, st)

/-- Bind -/
@[inline]
protected def bind (p : Parser α) (f : α → Parser β) : Parser β := fun st it =>
  match p st it with
  | .success it' (a, st') => f a st' it'
  | .error it' err => .error it' err

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

/-- Failure -/
@[inline]
protected def fail (msg : String) : Parser α := fun _ it =>
  .error it (.other msg)

  /-- Alternative (Parsec semantics).

  If the left branch fails *without consuming input*, we run the right branch.
  If it fails *after consuming input*, we commit to that failure.

  Use `attempt` around a branch when it must backtrack even after
  consuming input. -/
  @[inline]
  protected def orElse (p : Parser α) (q : Unit → Parser α) : Parser α := fun st it =>
    match p st it with
    | .success it' res => .success it' res
    | .error it' err =>
        if it'.pos == it.pos then
          q () st it
        else
          .error it' err

instance : Alternative Parser where
  failure := Parser.fail ""
  orElse := Parser.orElse

end Parser

/-!
## MonadLift from BaseParser to Parser

Allows using Parsec combinators directly in Parser.
-/

/-- Lift base parser into parser -/
@[inline]
def liftBase (p : BaseParser α) : Parser α := fun st it =>
  match p it with
  | .success it' a => .success it' (a, st)
  | .error it' err => .error it' err

instance : MonadLift BaseParser Parser where
  monadLift := liftBase

/-!
## Position and State Utilities
-/

/-- Get current position -/
def getPos : Parser (Nat × Nat) := fun st it =>
  .success it ((it.line, it.column), st)

/-- Get current iterator state -/
def getIterator : Parser PosIterator := fun st it =>
  .success it (it, st)

/-- Get parser state -/
def getState : Parser ParserState := fun st it =>
  .success it (st, st)

/-- Modify parser state -/
def modifyState (f : ParserState → ParserState) : Parser Unit := fun st it =>
  .success it ((), f st)

/-- Create a fresh token ID -/
def freshId : Parser Id := fun st it =>
  let id := Id.mk st.nextId
  .success it (id, { st with nextId := st.nextId + 1 })

/-- Record a position for a token ID -/
def recordPosition (id : Id) (startLine startCol endLine endCol : Nat) : Parser Unit := fun st it =>
  let startPos : Position := { posFile := st.filename, posLine := startLine, posColumn := startCol }
  let endPos : Position := { posFile := st.filename, posLine := endLine, posColumn := endCol }
  .success it ((), { st with positions := st.positions.insert id (startPos, endPos) })

/-!
## Basic Combinators

Parsec combinators lifted into Parser.
-/

/-- Check if at end of input -/
def isEof : Parser Bool := liftBase Std.Internal.Parsec.isEof

/-- End of file -/
def eof : Parser Unit := liftBase Std.Internal.Parsec.eof

/-- Any character -/
def anyChar : Parser Char := liftBase Std.Internal.Parsec.any

/-- Peek at next character -/
def peek? : Parser (Option Char) := liftBase Std.Internal.Parsec.peek?

/-- Peek at next character (must exist) -/
def peek! : Parser Char := liftBase Std.Internal.Parsec.peek!

/-- Peek ahead `n` characters as a string without consuming input. -/
def peekString (n : Nat) : Parser String := fun st it =>
  let rec go (k : Nat) (pos : String.Pos.Raw) (acc : List Char) : List Char :=
    match k with
    | 0 => acc.reverse
    | k + 1 =>
        if pos < it.str.rawEndPos then
          let c := pos.get it.str
          go k (pos.next it.str) (c :: acc)
        else
          acc.reverse
  let chars := go n it.pos []
  .success it (String.ofList chars, st)

/-- Satisfy predicate -/
def satisfy (pred : Char → Bool) : Parser Char := liftBase (Std.Internal.Parsec.satisfy pred)

/-- Skip one character -/
def skip : Parser Unit := liftBase Std.Internal.Parsec.skip

/-- Many (zero or more) -/
partial def many (p : Parser α) : Parser (Array α) := fun st it =>
  go #[] st it
where
  go (acc : Array α) (st' : ParserState) (it' : PosIterator) : Std.Internal.Parsec.ParseResult (Array α × ParserState) PosIterator :=
    match p st' it' with
    | .success it'' (a, st'') =>
        if it''.pos == it'.pos then
          -- Prevent infinite loops when the parser can succeed without consuming input.
          .error it'' (.other "many: parser succeeded without consuming input")
        else
          go (acc.push a) st'' it''
    | .error it'' err =>
        if it''.pos == it'.pos then
          .success it' (acc, st')
        else
          .error it'' err

/-- Many1 (one or more) -/
def many1 (p : Parser α) : Parser (Array α) := do
  let first ← p
  let rest ← many p
  return #[first] ++ rest

/-- Many chars -/
def manyChars (p : Parser Char) : Parser String := do
  let chars ← many p
  return String.ofList chars.toList

/-- Many1 chars -/
def many1Chars (p : Parser Char) : Parser String := do
  let chars ← many1 p
  return String.ofList chars.toList

/-- Optional -/
def optional (p : Parser α) : Parser (Option α) := fun st it =>
  match p st it with
  | .success it' (a, st') => .success it' (some a, st')
  | .error it' err =>
      if it'.pos == it.pos then
        .success it (none, st)
      else
        .error it' err

/-- Try with backtracking -/
def attempt (p : Parser α) : Parser α := fun st it =>
  match p st it with
  | .success it' res => .success it' res
  | .error _ err => .error it err

/-!
## String Combinators

Character and string matching.
-/

/-- Match specific character -/
def pchar (c : Char) : Parser Char := do
  satisfy (fun actual => actual == c)

/-- Match string -/
partial def pstring (s : String) : Parser String := fun st it =>
  let rec go (i : String.Pos.Raw) (it' : PosIterator) : Std.Internal.Parsec.ParseResult (String × ParserState) PosIterator :=
    if i >= s.rawEndPos then
      .success it' (s, st)
    else if !it'.hasNext then
      .error it' (.other s!"expected \"{s}\"")
    else
      let expected := i.get s
      let actual := it'.curr
      if expected == actual then
        go (i.next s) it'.next
      else
        .error it' (.other s!"expected \"{s}\"")
  go 0 it

/-- Skip whitespace -/
def ws : Parser Unit := do
  let _ ← manyChars (satisfy fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
  return ()

/-- Take while predicate holds -/
def takeWhile (pred : Char → Bool) : Parser String :=
  manyChars (satisfy pred)

/-- Take while predicate holds (at least one) -/
def takeWhile1 (pred : Char → Bool) : Parser String :=
  many1Chars (satisfy pred)

/-!
## Token Building
-/

/-- Create a token with current position -/
def mkToken (inner : InnerToken Token) : Parser Token := do
  let (line, col) ← getPos
  let id ← freshId
  recordPosition id line col line col
  return ⟨id, inner⟩

/-- Create a token with explicit positions -/
def mkTokenAt (inner : InnerToken Token) (startLine startCol : Nat) : Parser Token := do
  let (endLine, endCol) ← getPos
  let id ← freshId
  recordPosition id startLine startCol endLine endCol
  return ⟨id, inner⟩

/-!
## Running Parsers
-/

/-- Run a shell parser -/
def run (p : Parser α) (input : String) (filename : String := "<stdin>")
    : Option α × Std.HashMap Id (Position × Position) × List String :=
  let it := PosIterator.create input
  let st := mkParserState filename
  match p st it with
  | .success _ (a, st') => (some a, st'.positions, st'.errors)
  | .error it' err =>
      let msg := s!"{filename}:{it'.line}:{it'.column}: {err}"
      (none, {}, [msg])

/-- Run a shell parser, returning Except -/
def runExcept (p : Parser α) (input : String) (filename : String := "<stdin>")
    : Except String (α × Std.HashMap Id (Position × Position)) :=
  let it := PosIterator.create input
  let st := mkParserState filename
  match p st it with
  | .success _ (a, st') => .ok (a, st'.positions)
  | .error it' err => .error s!"{filename}:{it'.line}:{it'.column}: {err}"

end ShellCheck.Parser.Parsec
