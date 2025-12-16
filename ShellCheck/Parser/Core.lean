/-
  Core FullParser infrastructure.

  This module used to define a bespoke `FullParser` monad with manual position
  tracking.  The parser is now migrating to the Parsec‑based `ShellParser`
  defined in `ShellCheck.Parser.Parsec`.  To keep the rest of the codebase
  stable during the migration, we provide a compatibility layer that preserves
  the old names (`FullParser`, `peekFull`, `manyFull`, …) but delegates to the
  Parsec implementation.
-/

import ShellCheck.Parser.Parsec

namespace ShellCheck.Parser.Core

open ShellCheck.AST
open ShellCheck.Interface
open ShellCheck.Parser.Parsec

abbrev FullParserState := ShellState
abbrev FullParser (α : Type) := ShellParser α

/-- Create initial parser state (input is handled by the iterator). -/
@[inline]
def mkFullState (_input : String) (filename : String := "<stdin>") : FullParserState :=
  mkShellState filename

@[inline] def freshIdFull : FullParser Id := freshId
@[inline] def recordPosition (id : Id) (startLine startCol endLine endCol : Nat) : FullParser Unit :=
  ShellCheck.Parser.Parsec.recordPosition id startLine startCol endLine endCol
@[inline] def currentPos : FullParser (Nat × Nat) := getPos
@[inline] def isEofFull : FullParser Bool := isEof
@[inline] def peekFull : FullParser (Option Char) := peek?
@[inline] def anyCharFull : FullParser Char := anyChar
@[inline] def charFull (c : Char) : FullParser Char := pchar c
@[inline] def stringFull (s : String) : FullParser String := pstring s
@[inline] def takeWhileFull (p : Char → Bool) : FullParser String := takeWhile p
@[inline] def takeWhile1Full (p : Char → Bool) : FullParser String := takeWhile1 p
@[inline] def attemptFull (p : FullParser α) : FullParser α := attempt p
@[inline] def peekStringFull (n : Nat) : FullParser String := peekString n
@[inline] def optionalFull (p : FullParser α) : FullParser (Option α) :=
  ShellCheck.Parser.Parsec.optional p

partial def manyFull (p : FullParser α) : FullParser (List α) := do
  let arr ← ShellCheck.Parser.Parsec.many p
  pure arr.toList

def many1Full (p : FullParser α) : FullParser (List α) := do
  let arr ← ShellCheck.Parser.Parsec.many1 p
  pure arr.toList

@[inline] def mkTokenFull (inner : InnerToken Token) : FullParser Token := mkToken inner
@[inline] def mkTokenFullAt (inner : InnerToken Token) (startLine startCol : Nat) : FullParser Token :=
  mkTokenAt inner startLine startCol

/-- Run a full parser on a string, returning the value, positions map and errors. -/
def runFullParser (p : FullParser α) (input : String) (filename : String := "<stdin>")
    : Option α × Std.HashMap Id (Position × Position) × List String :=
  ShellCheck.Parser.Parsec.run p input filename

end ShellCheck.Parser.Core
