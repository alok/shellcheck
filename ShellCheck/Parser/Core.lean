/-
  Core Parser infrastructure.

  This module used to define a bespoke monad with manual position tracking.
  The parser now targets the Parsec‑based `ShellParser` defined in
  `ShellCheck.Parser.Parsec`, with the core parser type aliased to `Parser`.
-/

import ShellCheck.Parser.Parsec

namespace ShellCheck.Parser.Core

open ShellCheck.AST
open ShellCheck.Interface
open ShellCheck.Parser.Parsec

abbrev ParserState := ShellState
abbrev Parser (α : Type) := ShellParser α

/-- Create initial parser state (input is handled by the iterator). -/
@[inline]
def mkState (_input : String) (filename : String := "<stdin>") : ParserState :=
  mkShellState filename

@[inline] def freshId : Parser Id := ShellCheck.Parser.Parsec.freshId
@[inline] def recordPosition (id : Id) (startLine startCol endLine endCol : Nat) : Parser Unit :=
  ShellCheck.Parser.Parsec.recordPosition id startLine startCol endLine endCol
@[inline] def currentPos : Parser (Nat × Nat) := ShellCheck.Parser.Parsec.getPos
@[inline] def peek? : Parser (Option Char) := ShellCheck.Parser.Parsec.peek?
@[inline] def anyChar : Parser Char := ShellCheck.Parser.Parsec.anyChar
@[inline] def char (c : Char) : Parser Char := ShellCheck.Parser.Parsec.pchar c
@[inline] def string (s : String) : Parser String := ShellCheck.Parser.Parsec.pstring s
@[inline] def takeWhile (p : Char → Bool) : Parser String := ShellCheck.Parser.Parsec.takeWhile p
@[inline] def takeWhile1 (p : Char → Bool) : Parser String := ShellCheck.Parser.Parsec.takeWhile1 p
@[inline] def attempt (p : Parser α) : Parser α := ShellCheck.Parser.Parsec.attempt p
@[inline] def peekString (n : Nat) : Parser String := ShellCheck.Parser.Parsec.peekString n
@[inline] def optionalP (p : Parser α) : Parser (Option α) :=
  ShellCheck.Parser.Parsec.optional p

partial def many (p : Parser α) : Parser (List α) := do
  let arr ← ShellCheck.Parser.Parsec.many p
  pure arr.toList

def many1 (p : Parser α) : Parser (List α) := do
  let arr ← ShellCheck.Parser.Parsec.many1 p
  pure arr.toList

@[inline] def mkToken (inner : InnerToken Token) : Parser Token := ShellCheck.Parser.Parsec.mkToken inner
@[inline] def mkTokenAt (inner : InnerToken Token) (startLine startCol : Nat) : Parser Token :=
  ShellCheck.Parser.Parsec.mkTokenAt inner startLine startCol

/-- Run a parser on a string, returning the value, positions map and errors. -/
def runParserCore (p : Parser α) (input : String) (filename : String := "<stdin>")
    : Option α × Std.HashMap Id (Position × Position) × List String :=
  ShellCheck.Parser.Parsec.run p input filename

end ShellCheck.Parser.Core
