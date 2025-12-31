/-
  Copyright 2024
  Lean 4 port

  Parser combinator extensions for ShellCheck
  Provides Parsec-like combinators on top of Std.Internal.Parsec
  using the shared PosIterator infrastructure.
-/

import Std.Internal.Parsec
import ShellCheck.Parser.Parsec

namespace ShellCheck.Parser.Ext

open Std.Internal.Parsec
open ShellCheck.Parser.Parsec

/-- Parser state with position tracking (shared PosIterator). -/
abbrev ParserState := PosIterator

/-- Parser result -/
abbrev Result (α : Type) := Std.Internal.Parsec.ParseResult α ParserState

/-- Simple parser type -/
abbrev Parser (α : Type) := Std.Internal.Parsec ParserState α

/-- Create initial parser state -/
def mkState (input : String) : ParserState :=
  PosIterator.create input

/-- Get current position -/
def getPos : Parser String.Pos.Raw := fun it => .success it it.pos

/-- Get current line -/
def getLine : Parser Nat := fun it => .success it it.line

/-- Get current column -/
def getColumn : Parser Nat := fun it => .success it it.column

/-- Check if at end of input -/
def isEof : Parser Bool :=
  Std.Internal.Parsec.isEof

/-- Peek at next character without consuming -/
def peek? : Parser (Option Char) :=
  Std.Internal.Parsec.peek?

/-- Consume a single character -/
def anyChar : Parser Char :=
  Std.Internal.Parsec.any

/-- Consume a character satisfying a predicate -/
def satisfy (p : Char → Bool) (_desc : String := "character") : Parser Char :=
  Std.Internal.Parsec.satisfy p

/-- Match a specific character -/
def char (c : Char) : Parser Char :=
  attempt do
    let actual ← anyChar
    if actual == c then
      pure c
    else
      fail s!"expected '{c}'"

/-- Match one of several characters -/
def oneOf (cs : String) : Parser Char :=
  satisfy (fun c => cs.toList.contains c) s!"one of \"{cs}\""

/-- Match none of several characters -/
def noneOf (cs : String) : Parser Char :=
  satisfy (fun c => ¬ cs.toList.contains c) s!"none of \"{cs}\""

/-- Match a specific string -/
partial def string (str : String) : Parser String := fun it =>
  let rec go (i : String.Pos.Raw) (state : PosIterator) : Result String :=
    if i >= str.rawEndPos then
      .success state str
    else if !state.hasNext then
      .error state (.other s!"expected \"{str}\"")
    else
      let expected := i.get str
      let actual := state.curr
      if expected == actual then
        go (i.next str) state.next
      else
        .error state (.other s!"expected \"{str}\"")
  go 0 it

/-- Try a parser, backtracking on failure -/
def attempt (p : Parser α) : Parser α :=
  Std.Internal.Parsec.attempt p

/-- Parse zero or more occurrences -/
def many (p : Parser α) : Parser (List α) := do
  let xs ← Std.Internal.Parsec.many p
  pure xs.toList

/-- Parse one or more occurrences -/
def many1 (p : Parser α) : Parser (List α) := do
  let xs ← Std.Internal.Parsec.many1 p
  pure xs.toList

/-- Optional parser -/
def option (default : α) (p : Parser α) : Parser α := do
  match (← optional p) with
  | some a => pure a
  | none => pure default

/-- Optional parser returning Option -/
def optional (p : Parser α) : Parser (Option α) := fun it =>
  match p it with
  | .success it' a => .success it' (some a)
  | .error it' err =>
      if it'.pos == it.pos then
        .success it none
      else
        .error it' err

/-- Parse p separated by sep -/
def sepBy (p : Parser α) (sep : Parser β) : Parser (List α) := do
  match (← optional p) with
  | none => pure []
  | some first =>
      let rest ← many (sep *> p)
      pure (first :: rest)

/-- Parse p separated by sep, requiring at least one -/
def sepBy1 (p : Parser α) (sep : Parser β) : Parser (List α) := do
  let first ← p
  let rest ← many (sep *> p)
  pure (first :: rest)

/-- Parse until a terminator -/
partial def manyTill (p : Parser α) (term : Parser β) : Parser (List α) := fun it =>
  match term it with
  | .success it' _ => .success it' []
  | .error it' err =>
      if it'.pos != it.pos then
        .error it' err
      else
        match p it with
        | .success it'' a =>
            match manyTill p term it'' with
            | .success it''' rest => .success it''' (a :: rest)
            | .error it''' err' => .error it''' err'
        | .error it'' err' => .error it'' err'

/-- Lookahead without consuming -/
def lookAhead (p : Parser α) : Parser α := fun it =>
  match p it with
  | .success _ a => .success it a
  | .error _ err => .error it err

/-- Negative lookahead -/
def notFollowedBy (p : Parser α) : Parser Unit :=
  Std.Internal.Parsec.notFollowedBy p

/-- End of input -/
def eof : Parser Unit :=
  Std.Internal.Parsec.eof

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
def choice (ps : List (Parser α)) : Parser α := fun it =>
  match ps with
  | [] => .error it (.other "no alternative succeeded")
  | p :: rest =>
      rest.foldl (fun acc q => acc <|> q) p it

/-- Label a parser for better error messages -/
def label (name : String) (p : Parser α) : Parser α := fun it =>
  match p it with
  | .success it' a => .success it' a
  | .error it' _ => .error it' (.other s!"expected {name}")

/-- Infix synonym for label -/
scoped infixl:1 " <?> " => fun p name => label name p

/-- Run a parser on input -/
def run (p : Parser α) (input : String) : Except String α :=
  match p (mkState input) with
  | .success _ a => .ok a
  | .error it err => .error s!"{it.line}:{it.column}: {err}"

/-- Collect characters while predicate holds -/
def takeWhile (p : Char → Bool) : Parser String :=
  Std.Internal.Parsec.manyChars (satisfy p)

/-- Collect at least one character while predicate holds -/
def takeWhile1 (p : Char → Bool) : Parser String :=
  Std.Internal.Parsec.many1Chars (satisfy p)

end ShellCheck.Parser.Ext
