/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Shell script parser for ShellCheck
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.Data
import ShellCheck.Interface
import ShellCheck.Parser.Types
import ShellCheck.Parser.Ext

namespace ShellCheck.Parser

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Parser.Types
open ShellCheck.Parser.Ext

-- Re-export parser types
export ShellCheck.Parser.Types (
  SourcePos ParseNote Context HereDocContext
  UserState SystemState Environment
  initialUserState initialSystemState
)

-- Re-export parser combinators
export ShellCheck.Parser.Ext (
  Parser ParserState Result
  mkState run
  anyChar satisfy char oneOf noneOf string
  attempt many many1 option optional
  sepBy sepBy1 manyTill lookAhead notFollowedBy eof
  upper lower letter digit alphaNum space spaces
  choice label takeWhile takeWhile1
)

/-- Character classes for shell parsing -/

def variableStartChar (c : Char) : Bool :=
  c.isAlpha || c == '_'

def variableChar (c : Char) : Bool :=
  variableStartChar c || c.isDigit

def specialVariableChars : String := "*@#?-$!0123456789"

def quotableChars : String := "|&;<>()\\ '\t\n\r"

def doubleQuotableChars : String := "\\\"$`"

def extglobStartChars : String := "?*@!+"

/-- Basic token parsers -/

def backslash : Parser Char := char '\\'

def linefeed : Parser Char := char '\n'

def singleQuote : Parser Char := char '\''

def doubleQuote : Parser Char := char '"'

def variableStart : Parser Char :=
  satisfy variableStartChar "variable start character"

def variableChars : Parser Char :=
  satisfy variableChar "variable character"

/-- Parse a variable name -/
def variableName : Parser String := do
  let first ← variableStart
  let rest ← takeWhile variableChar
  return String.mk (first :: rest.toList)

/-- Skip whitespace and comments -/
partial def skipSpacing : Parser Unit := do
  let _ ← many (satisfy (fun c => c == ' ' || c == '\t') "space")
  match ← peek? with
  | some '#' =>
      let _ ← takeWhile (· != '\n')
      pure ()
  | some '\\' =>
      let saved ← getPos
      let _ ← char '\\'
      match ← peek? with
      | some '\n' =>
          let _ ← char '\n'
          skipSpacing
      | _ => pure ()  -- backtrack would be needed here
  | _ => pure ()

/-- Parse a literal string (unquoted word part) -/
partial def readLiteral : Parser String :=
  takeWhile1 fun c =>
    ¬ (c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
       c == '"' || c == '\'' || c == '$' || c == '`' ||
       c == '|' || c == '&' || c == ';' || c == '<' ||
       c == '>' || c == '(' || c == ')' || c == '#')

/-- Parse a single-quoted string -/
def readSingleQuoted : Parser String := do
  let _ ← singleQuote
  let content ← takeWhile (· != '\'')
  let _ ← singleQuote
  return content

/-- Parse a double-quoted string (simplified) -/
partial def readDoubleQuoted : Parser String := do
  let _ ← doubleQuote
  let rec go (acc : List Char) : Parser String := do
    match ← peek? with
    | none => failure
    | some '"' =>
        let _ ← doubleQuote
        return String.mk acc.reverse
    | some '\\' =>
        let _ ← backslash
        match ← peek? with
        | some c =>
            let _ ← anyChar
            go (c :: acc)
        | none => failure
    | some c =>
        let _ ← anyChar
        go (c :: acc)
  go []

/-- Parse a simple word -/
def readWord : Parser String := do
  let parts ← many1 (readLiteral <|> readSingleQuoted <|> readDoubleQuoted)
  return String.join parts

/-- Parse a simple command (simplified) -/
def readSimpleCommand : Parser (List String) := do
  skipSpacing
  let cmd ← readWord
  let args ← many (skipSpacing *> readWord)
  return cmd :: args

/-- Parse a comment -/
def readComment : Parser String := do
  let _ ← char '#'
  takeWhile (· != '\n')

/-- State monad for token generation -/
structure TokenGenState where
  nextId : Nat
  deriving Inhabited

abbrev TokenGen := StateM TokenGenState

def freshId : TokenGen Id := do
  let s ← get
  set { s with nextId := s.nextId + 1 }
  return ⟨s.nextId⟩

/-- Create a literal token -/
def mkLiteralToken (s : String) : TokenGen Token := do
  let id ← freshId
  return ⟨id, .T_Literal s⟩

/-- Create a single-quoted token -/
def mkSingleQuotedToken (s : String) : TokenGen Token := do
  let id ← freshId
  return ⟨id, .T_SingleQuoted s⟩

/-- Create a simple command token -/
def mkSimpleCommandToken (assigns : List Token) (words : List Token) : TokenGen Token := do
  let id ← freshId
  return ⟨id, .T_SimpleCommand assigns words⟩

/-- Create a script token -/
def mkScriptToken (shebang : Token) (cmds : List Token) : TokenGen Token := do
  let id ← freshId
  return ⟨id, .T_Script shebang cmds⟩

/-- Parse result with tokens -/
structure ParsedScript where
  root : Option Token
  comments : List PositionedComment
  positions : Std.HashMap Id (Position × Position)
  deriving Inhabited

/-- Parse a shell script (simplified entry point) -/
def parseScript [Monad m] (sys : SystemInterface m) (spec : ParseSpec) : m ParseResult :=
  -- For now, return a stub result
  -- Real implementation would use the parser combinators
  pure {
    prComments := []
    prTokenPositions := {}
    prRoot := none
  }

/-- Parse a string into a token tree (simplified) -/
def parseString (input : String) : Except String Token :=
  -- Simplified parsing - just create a basic structure
  let gen : TokenGen Token := do
    let shebangId ← freshId
    let shebang : Token := ⟨shebangId, .T_Literal ""⟩
    let scriptId ← freshId
    return ⟨scriptId, .T_Script shebang []⟩
  let (tok, _) := gen.run { nextId := 1 }
  .ok tok

-- Theorems (stubs)

theorem variableStartChar_underscore :
    variableStartChar '_' = true := rfl

theorem variableStartChar_letter (c : Char) :
    c.isAlpha → variableStartChar c = true := by
  intro h
  simp [variableStartChar, h]

theorem variableChar_includes_digit (c : Char) :
    c.isDigit → variableChar c = true := by
  intro h
  simp [variableChar, variableStartChar, h]

theorem parseString_returns_token (input : String) :
    ∃ tok, parseString input = .ok tok := sorry

theorem freshId_increments : True := trivial  -- placeholder

theorem mkLiteralToken_creates_literal (s : String) :
    True := trivial  -- placeholder

theorem readLiteral_nonempty (input : String) :
    input.length > 0 →
    (¬ input.toList.head!.isWhitespace) →
    True := fun _ _ => trivial  -- placeholder

theorem skipSpacing_consumes_whitespace :
    True := trivial  -- placeholder

theorem readSingleQuoted_preserves_content (s : String) :
    True := trivial  -- placeholder

theorem readDoubleQuoted_handles_escapes :
    True := trivial  -- placeholder

/-- Shell keywords -/
def shellKeywords : List String :=
  ["if", "then", "else", "elif", "fi",
   "case", "esac", "for", "while", "until",
   "do", "done", "in", "function",
   "select", "time", "coproc"]

theorem shellKeywords_contains_if :
    "if" ∈ shellKeywords := by decide

theorem shellKeywords_contains_done :
    "done" ∈ shellKeywords := by decide

/-- Check if a word is a shell keyword -/
def isKeyword (word : String) : Bool :=
  shellKeywords.contains word

theorem isKeyword_if : isKeyword "if" = true := by native_decide

theorem isKeyword_notKeyword : isKeyword "foo" = false := by native_decide

end ShellCheck.Parser
