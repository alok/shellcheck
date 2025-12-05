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
partial def skipHSpaceFull : FullParser Unit := do
  let _ ← takeWhileFull (fun c => c == ' ' || c == '\t')
  match ← peekFull with
  | some '\\' =>
      match ← optionalFull (stringFull "\\\n") with
      | some _ => skipHSpaceFull
      | none => pure ()
  | some '#' =>
      let _ ← takeWhileFull (· != '\n')
      pure ()
  | _ => pure ()

/-- Skip all whitespace including newlines -/
partial def skipAllSpaceFull : FullParser Unit := do
  let _ ← takeWhileFull (fun c => c.isWhitespace)
  match ← peekFull with
  | some '#' =>
      let _ ← takeWhileFull (· != '\n')
      skipAllSpaceFull
  | some '\\' =>
      match ← optionalFull (stringFull "\\\n") with
      | some _ => skipAllSpaceFull
      | none => pure ()
  | _ => pure ()

/-! ## Keyword Parsers -/

/-- Check if next token is a specific keyword (without consuming) -/
partial def peekKeyword (kw : String) : FullParser Bool := fun s =>
  let startPos := s.pos
  -- Check if we have the keyword followed by word terminator or EOF
  let rec checkChars (i : String.Pos.Raw) (pos : String.Pos.Raw) : Bool :=
    if i >= kw.rawEndPos then
      -- Keyword matched, check terminator
      pos >= s.input.rawEndPos || isWordTerminator (pos.get s.input)
    else if pos >= s.input.rawEndPos then
      false
    else
      let expected := i.get kw
      let actual := pos.get s.input
      if expected == actual then
        checkChars (i.next kw) (pos.next s.input)
      else
        false
  .ok (checkChars 0 startPos) s

/-- Consume a keyword -/
partial def consumeKeyword (kw : String) : FullParser Unit := do
  let isKw ← peekKeyword kw
  if isKw then
    let _ ← stringFull kw
    pure ()
  else
    failure

/-- Check if at reserved keyword -/
def isReservedKeyword : FullParser Bool := do
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
