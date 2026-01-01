/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Lexical analysis: character classes, keywords, spacing, operators
-/

import ShellCheck.Parser.Parsec

namespace ShellCheck.Parser.Lexer

open ShellCheck.Parser.Parsec

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

/-- True when a keyword is properly terminated (or at end of input). -/
def isKeywordTerminator (s : String) : Bool :=
  s.isEmpty ||
    match (0 : String.Pos.Raw).get? s with
    | some c => isWordTerminator c || c == ';'
    | none => true

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

/-- Core whitespace skipper with optional newline handling. -/
partial def skipSpaceCore (includeNewlines : Bool) : Parser Unit := do
  let _ ←
    takeWhile (fun c => if includeNewlines then c.isWhitespace else c == ' ' || c == '\t')
  match ← peek? with
  | some '#' =>
      let _ ← takeWhile (· != '\n')
      if includeNewlines then
        skipSpaceCore includeNewlines
      else
        pure ()
  | some '\\' =>
      match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "\\\n")) with
      | some _ => skipSpaceCore includeNewlines
      | none => pure ()
  | _ => pure ()

/-- Skip horizontal whitespace (space, tab) -/
partial def skipHSpace : Parser Unit := do
  skipSpaceCore false

/-- Skip all whitespace including newlines -/
partial def skipAllSpace : Parser Unit := do
  skipSpaceCore true

/-! ## Keyword Parsers -/

/-- Check if next token is a specific keyword (without consuming) -/
partial def peekKeyword (kw : String) : Parser Bool := fun st it =>
  let remaining := (it.str.drop it.pos.byteIdx).toString
  if remaining.startsWith kw then
    let afterKw := (remaining.drop kw.length).toString
    .success it (isKeywordTerminator afterKw, st)
  else
    .success it (false, st)

/-- Consume a keyword -/
partial def consumeKeyword (kw : String) : Parser Unit := do
  let isKw ← peekKeyword kw
  if isKw then
    let _ ← pstring kw
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
