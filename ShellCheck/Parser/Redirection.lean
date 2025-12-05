/-
  Redirection parser for ShellCheck
  Handles >, >>, <, <>, >&, <&, >|, &>, &>>, <<<, <<
-/

import ShellCheck.AST

namespace ShellCheck.Parser.Redirection

open ShellCheck.AST

/-- Redirection operator types -/
inductive RedirOp where
  | redirectOut        -- >
  | redirectOutAppend  -- >>
  | redirectIn         -- <
  | redirectInOut      -- <>
  | duplicateFdOut     -- >&
  | duplicateFdIn      -- <&
  | clobber            -- >|
  | stderrRedirect     -- &>
  | stderrAppend       -- &>>
  | hereString         -- <<<
  | hereDoc            -- <<
  | hereDocDashed      -- <<-
  deriving Repr, BEq, Inhabited

/-- Parsed redirection -/
structure ParsedRedirection where
  fdSource : Option Nat      -- Source FD (None = default)
  op : RedirOp               -- Operator type
  target : String            -- Target (filename, FD number, or content)
  deriving Repr, Inhabited

/-- Get character at position -/
def getCharAt (s : String) (pos : Nat) : Option Char :=
  if pos < s.length then some (s.toList.getD pos ' ') else none

/-- Parser state -/
structure RedirState where
  input : String
  pos : Nat
  deriving Repr, Inhabited

/-- Result type -/
inductive RedirResult (α : Type) where
  | ok : α → RedirState → RedirResult α
  | error : String → RedirState → RedirResult α
  deriving Repr, Inhabited, Nonempty

/-- Redirection parser monad -/
def RedirParser (α : Type) := RedirState → RedirResult α

instance : Monad RedirParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative RedirParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Peek at current character -/
def peek : RedirParser (Option Char) := fun s =>
  .ok (getCharAt s.input s.pos) s

/-- Consume current character -/
def anyChar : RedirParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error "unexpected end" s
  | some c => .ok c { s with pos := s.pos + 1 }

/-- Consume specific character -/
def char (c : Char) : RedirParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error s!"expected '{c}'" s
  | some actual =>
      if actual == c then .ok c { s with pos := s.pos + 1 }
      else .error s!"expected '{c}'" s

/-- Consume specific string -/
def matchStr (str : String) : RedirParser String := fun s =>
  let remaining := s.input.drop s.pos
  if remaining.startsWith str then
    .ok str { s with pos := s.pos + str.length }
  else
    .error s!"expected \"{str}\"" s

/-- Optional parser -/
def optionalP (p : RedirParser α) : RedirParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Try parser, backtrack on failure -/
def attempt (p : RedirParser α) : RedirParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Take while predicate holds -/
partial def takeWhile (p : Char → Bool) : RedirParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) : (Nat × List Char) :=
    match getCharAt s.input pos with
    | none => (pos, acc)
    | some c =>
        if p c then go (pos + 1) (c :: acc)
        else (pos, acc)
  let (newPos, chars) := go s.pos []
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Skip whitespace -/
def skipSpaces : RedirParser Unit := do
  let _ ← takeWhile (· == ' ')
  pure ()

/-- Parse a number (for FD) -/
def parseNumber : RedirParser Nat := do
  let digits ← takeWhile Char.isDigit
  if digits.isEmpty then failure
  else
    match digits.toNat? with
    | some n => pure n
    | none => failure

/-- Parse word (filename or FD target) -/
def parseWord : RedirParser String := do
  skipSpaces
  let word ← takeWhile (fun c => !c.isWhitespace && c != '\n' && c != ';' && c != '&' && c != '|')
  if word.isEmpty then failure
  else pure word

/-- Parse here-string content (until newline) -/
def parseHereStringContent : RedirParser String := do
  skipSpaces
  let content ← takeWhile (· != '\n')
  pure content

/-- Parse a redirection operator -/
def parseRedirOp : RedirParser RedirOp :=
  -- Order matters: longer operators first
  attempt (matchStr "&>>" *> pure .stderrAppend) <|>
  attempt (matchStr "&>" *> pure .stderrRedirect) <|>
  attempt (matchStr "<<<" *> pure .hereString) <|>
  attempt (matchStr "<<-" *> pure .hereDocDashed) <|>
  attempt (matchStr "<<" *> pure .hereDoc) <|>
  attempt (matchStr ">>" *> pure .redirectOutAppend) <|>
  attempt (matchStr "><" *> pure .redirectInOut) <|>
  attempt (matchStr "<>" *> pure .redirectInOut) <|>
  attempt (matchStr ">|" *> pure .clobber) <|>
  attempt (matchStr ">&" *> pure .duplicateFdOut) <|>
  attempt (matchStr "<&" *> pure .duplicateFdIn) <|>
  attempt (matchStr ">" *> pure .redirectOut) <|>
  attempt (matchStr "<" *> pure .redirectIn)

/-- Parse a complete redirection -/
def parseRedirection : RedirParser ParsedRedirection := do
  -- Try to parse optional FD number first
  let fdOpt ← optionalP (attempt parseNumber)
  let op ← parseRedirOp
  -- Parse target based on operator
  let target ← match op with
    | .hereString => parseHereStringContent
    | .hereDoc | .hereDocDashed =>
        -- For here-docs, we just get the delimiter here
        -- The actual content would be read later (multi-phase)
        skipSpaces
        parseWord
    | _ => parseWord
  pure { fdSource := fdOpt, op, target }

/-- Parse redirection from string -/
def parse (input : String) : Option ParsedRedirection :=
  let state : RedirState := { input, pos := 0 }
  match parseRedirection state with
  | .ok result _ => some result
  | .error _ _ => none

/-- Check if string starts with a redirection operator -/
def startsWithRedir (s : String) : Bool :=
  if s.isEmpty then false
  else
    let c := s.toList.headD ' '
    let afterFirst := s.drop 1
    let hasRedirOutAfter := afterFirst.startsWith ">"
    let hasRedirInAfter := afterFirst.startsWith "<"
    let hasRedirAfter := hasRedirOutAfter || hasRedirInAfter
    if c == '>' then true
    else if c == '<' then true
    else if c == '&' then hasRedirOutAfter
    else if c.isDigit then hasRedirAfter
    else false

/-- Check if a character could start a redirection -/
def isRedirStart (c : Char) : Bool :=
  c == '>' || c == '<' || c.isDigit

/-- Convert RedirOp to string representation -/
def RedirOp.toString : RedirOp → String
  | .redirectOut => ">"
  | .redirectOutAppend => ">>"
  | .redirectIn => "<"
  | .redirectInOut => "<>"
  | .duplicateFdOut => ">&"
  | .duplicateFdIn => "<&"
  | .clobber => ">|"
  | .stderrRedirect => "&>"
  | .stderrAppend => "&>>"
  | .hereString => "<<<"
  | .hereDoc => "<<"
  | .hereDocDashed => "<<-"

instance : ToString RedirOp := ⟨RedirOp.toString⟩

end ShellCheck.Parser.Redirection
