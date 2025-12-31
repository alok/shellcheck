/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Lexical analysis: character classes, keywords, spacing, operators
-/

import ShellCheck.Parser.Core

namespace ShellCheck.Parser.Lexer

open ShellCheck.Parser.Core

/-! ## Character Classes -/

/-- Is character valid at start of variable name? -/
def variableStartChar (c : Char) : Bool :=
  c.isAlpha || c == '_'

/-- Is character valid in variable name? -/
def variableChar (c : Char) : Bool :=
  variableStartChar c || c.isDigit

/-- Special shell variable characters ($*, $@, $#, etc.) -/
def specialVariableChars : String := "*@#?-$!0123456789"

/-- Characters that need quoting -/
def quotableChars : String := "|&;<>()\\ '\t\n\r"

/-- Characters special inside double quotes -/
def doubleQuotableChars : String := "\\\"$`"

/-- Extglob pattern start characters -/
def extglobStartChars : String := "?*@!+"

/-- Is character a separator? -/
def isSeparatorChar (c : Char) : Bool :=
  c == ';' || c == '\n' || c == '&'

/-- Is character an operator start? -/
def isOperatorStart (c : Char) : Bool :=
  c == '|' || c == '&' || c == ';' || c == '<' || c == '>' || c == '(' || c == ')'

/-- Is character a word terminator? -/
def isWordTerminator (c : Char) : Bool :=
  c.isWhitespace || isOperatorStart c || c == '#'

/-- Is character a glob metacharacter? -/
def isGlobChar (c : Char) : Bool :=
  c == '*' || c == '?' || c == '[' || c == ']'

/-! ## Keywords -/

/-- Shell reserved words -/
def shellKeywords : List String :=
  ["if", "then", "else", "elif", "fi",
   "case", "esac", "for", "select", "while", "until",
   "do", "done", "in", "function",
   "time", "coproc", "{", "}", "!", "[[", "]]"]

/-- Is word a shell keyword? -/
def isKeyword (word : String) : Bool :=
  shellKeywords.contains word

/-- Reserved keywords (subset that can't start commands) -/
def reservedKeywords : List String :=
  ["then", "else", "elif", "fi", "esac", "do", "done", "in", "}", "]]"]

/-! ## Spacing Parsers -/

/-- Skip horizontal whitespace (space, tab) -/
partial def skipHSpaceFull : Parser Unit := do
  let _ ← takeWhileFull (fun c => c == ' ' || c == '\t')
  match ← peekFull with
  | some '\\' =>
      match ← optionalFull (attemptFull (stringFull "\\\n")) with
      | some _ => skipHSpaceFull
      | none => pure ()
  | some '#' =>
      let _ ← takeWhileFull (· != '\n')
      pure ()
  | _ => pure ()

/-- Skip all whitespace including newlines -/
partial def skipAllSpaceFull : Parser Unit := do
  let _ ← takeWhileFull (fun c => c.isWhitespace)
  match ← peekFull with
  | some '#' =>
      let _ ← takeWhileFull (· != '\n')
      skipAllSpaceFull
  | some '\\' =>
      match ← optionalFull (attemptFull (stringFull "\\\n")) with
      | some _ => skipAllSpaceFull
      | none => pure ()
  | _ => pure ()

/-! ## Keyword Parsers -/

/-- Check if next token is a specific keyword (without consuming) -/
partial def peekKeyword (kw : String) : Parser Bool := fun st it =>
  let remaining := it.str.drop it.pos.byteIdx
  if remaining.startsWith kw then
    let afterKw := remaining.drop kw.length
    let isTerminated :=
      afterKw.isEmpty ||
        match (0 : String.Pos.Raw).get? afterKw with
        | some c => isWordTerminator c || c == ';'
        | none => true
    .success it (isTerminated, st)
  else
    .success it (false, st)

/-- Consume a keyword -/
partial def consumeKeyword (kw : String) : Parser Unit := do
  let isKw ← peekKeyword kw
  if isKw then
    let _ ← stringFull kw
    pure ()
  else
    failure

/-- Check if at reserved keyword -/
def isReservedKeyword : Parser Bool := do
  let checks ← reservedKeywords.mapM peekKeyword
  pure (checks.any id)

/-! ## Theorems -/

theorem variableStartChar_underscore : variableStartChar '_' = true := rfl

theorem variableStartChar_letter (c : Char) (h : c.isAlpha = true) :
    variableStartChar c = true := by simp [variableStartChar, h]

theorem variableChar_includes_digit (c : Char) (h : c.isDigit = true) :
    variableChar c = true := by simp [variableChar, variableStartChar, h]

theorem isKeyword_if : isKeyword "if" = true := rfl
theorem isKeyword_notKeyword : isKeyword "foo" = false := rfl

theorem shellKeywords_contains_if : "if" ∈ shellKeywords := by decide
theorem shellKeywords_contains_done : "done" ∈ shellKeywords := by decide

end ShellCheck.Parser.Lexer
