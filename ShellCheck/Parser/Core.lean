/-
  Core Parser infrastructure.

  This module used to define a bespoke monad with manual position tracking.
  The parser is now migrating to the Parsec‑based `ShellParser` defined in
  `ShellCheck.Parser.Parsec`. We keep the `*Full` helper names for now, but
  the core parser type is `Parser`.
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
def mkFullState (_input : String) (filename : String := "<stdin>") : ParserState :=
  mkShellState filename

@[inline] def freshIdFull : Parser Id := freshId
@[inline] def recordPosition (id : Id) (startLine startCol endLine endCol : Nat) : Parser Unit :=
  ShellCheck.Parser.Parsec.recordPosition id startLine startCol endLine endCol
@[inline] def currentPos : Parser (Nat × Nat) := getPos
@[inline] def isEofFull : Parser Bool := isEof
@[inline] def peekFull : Parser (Option Char) := peek?
@[inline] def anyCharFull : Parser Char := anyChar
@[inline] def charFull (c : Char) : Parser Char := pchar c
@[inline] def stringFull (s : String) : Parser String := pstring s
@[inline] def takeWhileFull (p : Char → Bool) : Parser String := takeWhile p
@[inline] def takeWhile1Full (p : Char → Bool) : Parser String := takeWhile1 p
@[inline] def attemptFull (p : Parser α) : Parser α := attempt p
@[inline] def peekStringFull (n : Nat) : Parser String := peekString n
@[inline] def optionalFull (p : Parser α) : Parser (Option α) :=
  ShellCheck.Parser.Parsec.optional p

partial def manyFull (p : Parser α) : Parser (List α) := do
  let arr ← ShellCheck.Parser.Parsec.many p
  pure arr.toList

def many1Full (p : Parser α) : Parser (List α) := do
  let arr ← ShellCheck.Parser.Parsec.many1 p
  pure arr.toList

@[inline] def mkTokenFull (inner : InnerToken Token) : Parser Token := mkToken inner
@[inline] def mkTokenFullAt (inner : InnerToken Token) (startLine startCol : Nat) : Parser Token :=
  mkTokenAt inner startLine startCol

/-- Run a full parser on a string, returning the value, positions map and errors. -/
def runFullParser (p : Parser α) (input : String) (filename : String := "<stdin>")
    : Option α × Std.HashMap Id (Position × Position) × List String :=
  ShellCheck.Parser.Parsec.run p input filename

end ShellCheck.Parser.Core
