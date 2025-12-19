/-
  Copyright 2024
  Lean 4 port

  Parser combinator extensions for ShellCheck
  Provides Parsec-like combinators on top of Std.Internal.Parsec
-/

import Std.Internal.Parsec
import Std.Internal.Parsec.String

namespace ShellCheck.Parser.Ext

open Std.Internal.Parsec
open Std.Internal.Parsec.String

/-- Parser state with position tracking -/
structure ParserState where
  input : String
  pos : String.Pos.Raw
  line : Nat
  column : Nat
  deriving Repr, Inhabited

/-- Parser result -/
inductive Result (α : Type) where
  | ok : α → ParserState → Result α
  | error : String → ParserState → Result α
  deriving Repr, Inhabited

/-- Simple parser type -/
def Parser (α : Type) := ParserState → Result α

instance : Monad Parser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative Parser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Create initial parser state -/
def mkState (input : String) : ParserState := {
  input := input
  pos := 0
  line := 1
  column := 1
}

/-- Get current position -/
def getPos : Parser String.Pos.Raw := fun s => .ok s.pos s

/-- Get current line -/
def getLine : Parser Nat := fun s => .ok s.line s

/-- Get current column -/
def getColumn : Parser Nat := fun s => .ok s.column s

/-- Check if at end of input -/
def isEof : Parser Bool := fun s =>
  .ok (s.pos >= s.input.rawEndPos) s

/-- Peek at next character without consuming -/
def peek? : Parser (Option Char) := fun s =>
  if s.pos < s.input.rawEndPos then
    .ok (some (s.pos.get s.input)) s
  else
    .ok none s

/-- Consume a single character -/
def anyChar : Parser Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let c := s.pos.get s.input
    let newPos := s.pos.next s.input
    let (newLine, newCol) :=
      if c == '\n' then (s.line + 1, 1)
      else (s.line, s.column + 1)
    .ok c { s with pos := newPos, line := newLine, column := newCol }
  else
    .error "unexpected end of input" s

/-- Consume a character satisfying a predicate -/
def satisfy (p : Char → Bool) (desc : String := "character") : Parser Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let c := s.pos.get s.input
    if p c then
      let newPos := s.pos.next s.input
      let (newLine, newCol) :=
        if c == '\n' then (s.line + 1, 1)
        else (s.line, s.column + 1)
      .ok c { s with pos := newPos, line := newLine, column := newCol }
    else
      .error s!"expected {desc}, got '{c}'" s
  else
    .error s!"expected {desc}, got end of input" s

/-- Match a specific character -/
def char (c : Char) : Parser Char :=
  satisfy (· == c) s!"'{c}'"

/-- Match one of several characters -/
def oneOf (cs : String) : Parser Char :=
  satisfy (cs.toList.contains ·) s!"one of \"{cs}\""

/-- Match none of several characters -/
def noneOf (cs : String) : Parser Char :=
  satisfy (fun c => ¬ cs.toList.contains c) s!"none of \"{cs}\""

/-- Match a specific string -/
partial def string (str : String) : Parser String := fun s =>
  let rec go (i : String.Pos.Raw) (state : ParserState) : Result String :=
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

/-- Try a parser, backtracking on failure -/
def attempt (p : Parser α) : Parser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s  -- backtrack to original state

/-- Parse zero or more occurrences -/
partial def many (p : Parser α) : Parser (List α) := fun s =>
  let rec go (acc : List α) (state : ParserState) : Result (List α) :=
    match p state with
    | .ok a s' => go (a :: acc) s'
    | .error _ _ => .ok acc.reverse state
  go [] s

/-- Parse one or more occurrences -/
def many1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← many p
  return first :: rest

/-- Optional parser -/
def option (default : α) (p : Parser α) : Parser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error _ _ => .ok default s

/-- Optional parser returning Option -/
def optional (p : Parser α) : Parser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Parse p separated by sep -/
partial def sepBy (p : Parser α) (sep : Parser β) : Parser (List α) := fun s =>
  match p s with
  | .error _ _ => .ok [] s
  | .ok first s' =>
      let rec go (acc : List α) (state : ParserState) : Result (List α) :=
        match sep state with
        | .error _ _ => .ok acc.reverse state
        | .ok _ s'' =>
            match p s'' with
            | .error _ _ => .ok acc.reverse state
            | .ok a s''' => go (a :: acc) s'''
      go [first] s'

/-- Parse p separated by sep, requiring at least one -/
def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (sep *> p)
  return first :: rest

/-- Parse until a terminator -/
partial def manyTill (p : Parser α) (term : Parser β) : Parser (List α) := fun s =>
  let rec go (acc : List α) (state : ParserState) : Result (List α) :=
    match term state with
    | .ok _ s' => .ok acc.reverse s'
    | .error _ _ =>
        match p state with
        | .ok a s' => go (a :: acc) s'
        | .error msg s' => .error msg s'
  go [] s

/-- Lookahead without consuming -/
def lookAhead (p : Parser α) : Parser α := fun s =>
  match p s with
  | .ok a _ => .ok a s
  | .error msg _ => .error msg s

/-- Negative lookahead -/
def notFollowedBy (p : Parser α) : Parser Unit := fun s =>
  match p s with
  | .ok _ _ => .error "unexpected" s
  | .error _ _ => .ok () s

/-- End of input -/
def eof : Parser Unit := fun s =>
  if s.pos >= s.input.rawEndPos then
    .ok () s
  else
    .error "expected end of input" s

/-- Upper case letter -/
def upper : Parser Char := satisfy Char.isUpper "uppercase letter"

/-- Lower case letter -/
def lower : Parser Char := satisfy Char.isLower "lowercase letter"

/-- Letter -/
def letter : Parser Char := satisfy Char.isAlpha "letter"

/-- Digit -/
def digit : Parser Char := satisfy Char.isDigit "digit"

/-- Alphanumeric -/
def alphaNum : Parser Char := satisfy Char.isAlphanum "alphanumeric"

/-- Whitespace character -/
def space : Parser Char := satisfy (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r') "whitespace"

/-- Skip whitespace -/
def spaces : Parser Unit := do
  let _ ← many space
  return ()

/-- Choice from a list of parsers -/
def choice (ps : List (Parser α)) : Parser α := fun s =>
  let rec go : List (Parser α) → Result α
    | [] => .error "no alternative succeeded" s
    | p :: rest =>
        match p s with
        | .ok a s' => .ok a s'
        | .error _ _ => go rest
  go ps

/-- Label a parser for better error messages -/
def label (name : String) (p : Parser α) : Parser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error _ s' => .error s!"expected {name}" s'

/-- Infix synonym for label -/
scoped infixl:1 " <?> " => fun p name => label name p

/-- Run a parser on input -/
def run (p : Parser α) (input : String) : Except String α :=
  match p (mkState input) with
  | .ok a _ => .ok a
  | .error msg _ => .error msg

/-- Collect characters while predicate holds -/
partial def takeWhile (p : Char → Bool) : Parser String := fun s =>
  let rec go (acc : List Char) (state : ParserState) : Result String :=
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

/-- Collect at least one character while predicate holds -/
def takeWhile1 (p : Char → Bool) : Parser String := do
  let s ← takeWhile p
  if s.isEmpty then
    failure
  else
    return s

-- Theorems (stubs)

theorem run_pure (a : α) (input : String) :
    run (pure a) input = .ok a := sorry

theorem many_returns_list (p : Parser α) (input : String) :
    ∃ l, run (many p) input = .ok l := sorry

theorem option_never_fails (default : α) (p : Parser α) (input : String) :
    ∃ a, run (option default p) input = .ok a := sorry

theorem attempt_backtracks (_p : Parser α) :
    True := trivial  -- placeholder

theorem sepBy_empty_on_fail (_p : Parser α) (_sep : Parser β) (_input : String) :
    True := trivial  -- placeholder

end ShellCheck.Parser.Ext
