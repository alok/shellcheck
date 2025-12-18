/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Shell script parser for ShellCheck
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.Data
import ShellCheck.Interface
import ShellCheck.Regex
import ShellCheck.Parser.Types
import ShellCheck.Parser.Ext
import ShellCheck.Parser.Core
import ShellCheck.Parser.Lexer
import ShellCheck.Parser.Word
import ShellCheck.Parser.Arithmetic
import ShellCheck.Parser.Condition
import ShellCheck.Parser.Parsec
import ShellCheck.Checks.ParserErrors

namespace ShellCheck.Parser

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Parser.Types
open ShellCheck.Parser.Ext
open ShellCheck.Parser.Core
open ShellCheck.Parser.Lexer
open ShellCheck.Parser.Word
open ShellCheck.Parser.Condition

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
  return String.ofList (first :: rest.toList)

/-- Skip whitespace and comments -/
partial def skipSpacing : Parser Unit := do
  let _ ← many (satisfy (fun c => c == ' ' || c == '\t') "space")
  match ← peek? with
  | some '#' =>
      let _ ← takeWhile (· != '\n')
      pure ()
  | some '\\' =>
      let _ ← getPos
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
        return String.ofList acc.reverse
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

/-- Token creation with position tracking -/
structure TokenBuilder where
  nextId : Nat
  positions : Std.HashMap Id (Position × Position)
  filename : String
  deriving Inhabited

abbrev TokenBuilderM := StateM TokenBuilder

def freshTokenId : TokenBuilderM Id := do
  let s ← get
  set { s with nextId := s.nextId + 1 }
  return ⟨s.nextId⟩

def mkToken (inner : InnerToken Token) (line col : Nat := 1) : TokenBuilderM Token := do
  let s ← get
  let id ← freshTokenId
  let pos := { posFile := s.filename, posLine := line, posColumn := col : Position }
  let endPos := pos  -- Simplified: same as start
  modify fun st => { st with positions := st.positions.insert id (pos, endPos) }
  return ⟨id, inner⟩

/-- Split a string into shell words, respecting parentheses, quotes, and braces -/
def splitShellWords (s : String) : List String :=
  let chars := s.toList
  go chars "" 0 0 0 false false []
where
  go : List Char → String → Nat → Nat → Nat → Bool → Bool → List String → List String
  | [], curr, _, _, _, _, _, acc =>
    if curr.isEmpty then acc.reverse else (acc.cons curr).reverse
  | c :: rest, curr, parenDepth, braceDepth, bracketDepth, inSingle, inDouble, acc =>
    if inSingle then
      if c == '\'' then go rest (curr.push c) parenDepth braceDepth bracketDepth false inDouble acc
      else go rest (curr.push c) parenDepth braceDepth bracketDepth inSingle inDouble acc
    else if inDouble then
      if c == '"' then go rest (curr.push c) parenDepth braceDepth bracketDepth inSingle false acc
      else if c == '\\' then
        match rest with
        | c2 :: rest2 => go rest2 (curr.push c |>.push c2) parenDepth braceDepth bracketDepth inSingle inDouble acc
        | [] => go [] (curr.push c) parenDepth braceDepth bracketDepth inSingle inDouble acc
      else go rest (curr.push c) parenDepth braceDepth bracketDepth inSingle inDouble acc
    else if c == '\'' then go rest (curr.push c) parenDepth braceDepth bracketDepth true inDouble acc
    else if c == '"' then go rest (curr.push c) parenDepth braceDepth bracketDepth inSingle true acc
    else if c == '(' then go rest (curr.push c) (parenDepth + 1) braceDepth bracketDepth inSingle inDouble acc
    else if c == ')' then go rest (curr.push c) (parenDepth - 1) braceDepth bracketDepth inSingle inDouble acc
    else if c == '{' then go rest (curr.push c) parenDepth (braceDepth + 1) bracketDepth inSingle inDouble acc
    else if c == '}' then go rest (curr.push c) parenDepth (braceDepth - 1) bracketDepth inSingle inDouble acc
    else if c == '[' then go rest (curr.push c) parenDepth braceDepth (bracketDepth + 1) inSingle inDouble acc
    else if c == ']' then go rest (curr.push c) parenDepth braceDepth (bracketDepth - 1) inSingle inDouble acc
    else if c == ' ' && parenDepth == 0 && braceDepth == 0 && bracketDepth == 0 then
      if curr.isEmpty then go rest "" parenDepth braceDepth bracketDepth inSingle inDouble acc
      else go rest "" parenDepth braceDepth bracketDepth inSingle inDouble (acc.cons curr)
    else go rest (curr.push c) parenDepth braceDepth bracketDepth inSingle inDouble acc

/-- Simple tokenizer that creates basic token structures -/
partial def tokenizeScript (script : String) (filename : String) : (Option Token × Std.HashMap Id (Position × Position)) :=
  let lines := script.splitOn "\n"
  let builder : TokenBuilderM (Option Token) := do
    -- Parse shebang if present (first line starting with #!)
    let shebangStr := match lines.head? with
      | some firstLine =>
        if firstLine.startsWith "#!" then firstLine.drop 2  -- drop the #!
        else ""
      | none => ""
    let shebang ← mkToken (.T_Literal shebangStr) 1 1

    -- Parse each line into simple commands
    let mut commands : List Token := []
    let mut lineNum := 1
    let mut isFirstLine := true

    for line in lines do
      let trimmed := line.trim
      -- Skip shebang on first line (already processed), empty lines and comments
      if (isFirstLine && trimmed.startsWith "#!") || trimmed.isEmpty || trimmed.startsWith "#" then
        lineNum := lineNum + 1
        isFirstLine := false
        continue
      isFirstLine := false

      -- Tokenize the line as a simple command (respecting parentheses and quotes)
      let words := splitShellWords trimmed
      if words.isEmpty then
        lineNum := lineNum + 1
        continue

      -- Create word tokens
      let mut wordTokens : List Token := []
      let mut col := 1
      for word in words do
        let tok ← tokenizeWord word filename lineNum col
        wordTokens := wordTokens ++ [tok]
        col := col + word.length + 1

      -- Create simple command
      let cmd ← mkToken (.T_SimpleCommand [] wordTokens) lineNum 1
      commands := commands ++ [cmd]
      lineNum := lineNum + 1

    -- Create script token
    let script ← mkToken (.T_Script shebang commands) 1 1
    return some script

  let initState : TokenBuilder := {
    nextId := 1
    positions := {}
    filename := filename
  }
  let (result, finalState) := builder.run initState
  (result, finalState.positions)

where
  /-- Check if a string is a valid shell variable name -/
  isValidVarName (s : String) : Bool :=
    if s.isEmpty then false
    else
      let first := (0 : String.Pos.Raw).get! s
      (first.isAlpha || first == '_') &&
        s.toList.all fun c => c.isAlpha || c.isDigit || c == '_'

  /-- Tokenize a single word, recognizing $ variables -/
  tokenizeWord (word : String) (filename : String) (line col : Nat) : TokenBuilderM Token := do
    if word.startsWith "$" then
      -- Variable reference
      if word.startsWith "${" then
        -- Braced variable
        let varName := word.drop 2 |>.dropRight 1
        let inner ← mkToken (.T_Literal varName) line col
        mkToken (.T_DollarBraced true inner) line col
      else if word.startsWith "$(" then
        -- Command substitution
        let inner ← mkToken (.T_Literal (word.drop 2 |>.dropRight 1)) line col
        mkToken (.T_DollarExpansion [inner]) line col
      else
        -- Simple variable like $foo
        let varName := word.drop 1
        let inner ← mkToken (.T_Literal varName) line col
        mkToken (.T_DollarBraced true inner) line col
    else if word.startsWith "`" && word.endsWith "`" then
      -- Backtick command substitution
      let inner := word.drop 1 |>.dropRight 1
      let innerTok ← mkToken (.T_Literal inner) line col
      mkToken (.T_Backticked [innerTok]) line col
    else if word.startsWith "'" && word.endsWith "'" then
      -- Single quoted
      let content := word.drop 1 |>.dropRight 1
      mkToken (.T_SingleQuoted content) line col
    else if word.startsWith "\"" && word.endsWith "\"" then
      -- Double quoted
      let content := word.drop 1 |>.dropRight 1
      -- Check for $ inside
      let parts ← tokenizeDoubleQuotedParts content filename line (col + 1)
      mkToken (.T_DoubleQuoted parts) line col
    else
      -- Check for assignment pattern (var=value or var+=value)
      match word.splitOn "=" with
      | [beforeEq, afterEq] =>
        -- Check if it's a valid variable assignment (not ==, or comparison)
        if isValidVarName beforeEq || (beforeEq.endsWith "+" && isValidVarName (beforeEq.dropRight 1)) then
          let isAppend := beforeEq.endsWith "+"
          let mode : AST.AssignmentMode := if isAppend then .append else .assign
          let varName := if isAppend then beforeEq.dropRight 1 else beforeEq
          -- Parse the value part
          let valueTok ← if afterEq.startsWith "(" && afterEq.endsWith ")" then
            -- Array assignment like (a b c)
            let arrayContent := afterEq.drop 1 |>.dropRight 1
            let arrayWords := arrayContent.splitOn " " |>.filter (fun s => !s.isEmpty)
            let elems ← arrayWords.mapM fun w => mkToken (.T_Literal w) line col
            mkToken (.T_Array elems) line col
          else if afterEq.startsWith "\"" && afterEq.endsWith "\"" then
            let content := afterEq.drop 1 |>.dropRight 1
            let parts ← tokenizeDoubleQuotedParts content filename line col
            mkToken (.T_DoubleQuoted parts) line col
          else if afterEq.startsWith "'" && afterEq.endsWith "'" then
            mkToken (.T_SingleQuoted (afterEq.drop 1 |>.dropRight 1)) line col
          else if afterEq.startsWith "$" then
            tokenizeWord afterEq filename line col
          else
            mkToken (.T_Literal afterEq) line col
          mkToken (.T_Assignment mode varName [] valueTok) line col
        else
          -- Not a valid assignment, treat as literal
          mkToken (.T_Literal word) line col
      | _ =>
        -- Plain literal or multiple = signs
        mkToken (.T_Literal word) line col

  /-- Tokenize parts inside double quotes -/
  tokenizeDoubleQuotedParts (content : String) (filename : String) (line col : Nat) : TokenBuilderM (List Token) := do
    -- Simplified: just look for $ and split
    if content.any (· == '$') then
      -- Has variables - create a mix of literals and dollar expansions
      let mut parts : List Token := []
      let mut current := ""
      let mut i := 0
      let chars := content.toList
      while h : i < chars.length do
        let c := chars[i]
        if c == '$' && i + 1 < chars.length then
          -- Found variable
          if !current.isEmpty then
            let lit ← mkToken (.T_Literal current) line col
            parts := parts ++ [lit]
            current := ""
          -- Get variable name
          let varChars := chars.drop (i + 1) |>.takeWhile (fun c => c.isAlpha || c.isDigit || c == '_')
          let varName := String.ofList varChars
          if !varName.isEmpty then
            let inner ← mkToken (.T_Literal varName) line col
            let varTok ← mkToken (.T_DollarBraced true inner) line col
            parts := parts ++ [varTok]
            i := i + 1 + varName.length
          else
            current := current.push c
            i := i + 1
        else
          current := current.push c
          i := i + 1
      if !current.isEmpty then
        let lit ← mkToken (.T_Literal current) line col
        parts := parts ++ [lit]
      return parts
    else
      -- No variables, just a literal
      let lit ← mkToken (.T_Literal content) line col
      return [lit]

/-- Parse a shell script (basic implementation) -/
def parseScript [Monad m] (_sys : SystemInterface m) (spec : ParseSpec) : m ParseResult := do
  let (root, positions) := tokenizeScript spec.psScript spec.psFilename
  pure {
    prComments := []
    prTokenPositions := positions
    prRoot := root
  }

/-- Parse a string into a token tree (simplified) -/
def parseString (_input : String) : Except String Token :=
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

theorem mkLiteralToken_creates_literal (_s : String) :
    True := trivial  -- placeholder

theorem readLiteral_nonempty (input : String) :
    input.length > 0 →
    (¬ input.toList.head!.isWhitespace) →
    True := fun _ _ => trivial  -- placeholder

theorem skipSpacing_consumes_whitespace :
    True := trivial  -- placeholder

theorem readSingleQuoted_preserves_content (_s : String) :
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

/-!
## Shell Grammar Implementation

The shell grammar hierarchy (from lowest to highest precedence):

```
script        → term*
term          → andOr ((; | & | newline) andOr)*
andOr         → pipeline ((&&||| ) pipeline)*
pipeline      → [!] command (| command)*
command       → compound | simple | condition
compound      → braceGroup | subshell | for | while | until | if | case | function | select | coproc
simple        → [assignment]* word+ [redirection]*
```
-/

/-- Separator characters -/
def isSeparatorChar (c : Char) : Bool :=
  c == ';' || c == '&' || c == '\n'

/-- Operator start characters -/
def isOperatorStart (c : Char) : Bool :=
  c == '|' || c == '&' || c == ';' || c == '<' || c == '>' || c == '(' || c == ')'

/-- Check if character terminates a word -/
def isWordTerminator (c : Char) : Bool :=
  c.isWhitespace || isOperatorStart c || c == '#'

/-- Parse a specific keyword -/
def keyword (kw : String) : Parser String := do
  let word ← takeWhile1 (fun c => c.isAlpha || c == '_')
  if word == kw then return word
  else failure

/-- Parse optional whitespace (spaces and tabs, not newlines) -/
def hspace : Parser Unit := do
  let _ ← takeWhile (fun c => c == ' ' || c == '\t')
  return ()

/-- Parse mandatory horizontal whitespace -/
def hspace1 : Parser Unit := do
  let _ ← takeWhile1 (fun c => c == ' ' || c == '\t')
  return ()

/-- Parse line continuation (backslash followed by newline) -/
def lineContinuation : Parser Unit := do
  let _ ← char '\\'
  let _ ← char '\n'
  return ()

/-- Skip horizontal whitespace and line continuations -/
partial def skipHSpacing : Parser Unit := do
  hspace
  match ← peek? with
  | some '\\' =>
      match ← optional lineContinuation with
      | some () => skipHSpacing
      | none => pure ()
  | some '#' =>
      -- Skip comments (but not newlines)
      let _ ← takeWhile (· != '\n')
      pure ()
  | _ => pure ()

/-- Skip all whitespace including newlines and comments -/
partial def skipAllSpacing : Parser Unit := do
  spaces
  match ← peek? with
  | some '#' =>
      let _ ← takeWhile (· != '\n')
      skipAllSpacing
  | some '\\' =>
      match ← optional lineContinuation with
      | some () => skipAllSpacing
      | none => pure ()
  | _ => pure ()

/-- Parse && operator -/
def andIf : Parser Unit := do
  let _ ← string "&&"
  return ()

/-- Parse || operator -/
def orIf : Parser Unit := do
  let _ ← string "||"
  return ()

/-- Parse | or |& operator -/
def pipeOp : Parser String := do
  let _ ← char '|'
  match ← peek? with
  | some '&' =>
      let _ ← char '&'
      return "|&"
  | some '|' => failure  -- This is || not pipe
  | _ => return "|"

/-- Parse ; separator -/
def semiOp : Parser Unit := do
  let _ ← char ';'
  -- Make sure it's not ;;
  match ← peek? with
  | some ';' => failure
  | _ => return ()

/-- Parse & for backgrounding (not &&) -/
def bgOp : Parser Unit := do
  let _ ← char '&'
  match ← peek? with
  | some '&' => failure  -- This is && not &
  | some '>' => failure  -- This is &> redirection
  | _ => return ()

/-- Parse newline as separator -/
def newlineSep : Parser Unit := do
  let _ ← char '\n'
  return ()

/-!
### Word Parsing (Enhanced)
-/

/-- Characters that can start a glob pattern -/
def isGlobChar (c : Char) : Bool :=
  c == '*' || c == '?' || c == '['

/-- Parse a glob pattern character -/
def readGlobChar : Parser Char := do
  let c ← anyChar
  if isGlobChar c then return c
  else failure

/-- Read an unquoted word part (literal text) stopping at special chars -/
partial def readUnquotedPart : Parser String := do
  takeWhile1 fun c =>
    ¬ (c.isWhitespace ||
       c == '"' || c == '\'' || c == '`' ||
       c == '$' || c == '\\' ||
       c == '|' || c == '&' || c == ';' ||
       c == '<' || c == '>' ||
       c == '(' || c == ')' ||
       c == '{' || c == '}' ||
       c == '#' ||
       isGlobChar c)

/-- Parse an escape sequence in unquoted context -/
def readUnquotedEscape : Parser Char := do
  let _ ← char '\\'
  match ← peek? with
  | some '\n' =>
      let _ ← char '\n'
      failure  -- Line continuation, not an escape
  | some c =>
      let _ ← anyChar
      return c
  | none => failure

/-- Parse a dollar expression (variable, command sub, arithmetic) -/
partial def readDollarExpr (mkTok : InnerToken Token → Nat → Nat → TokenBuilderM Token) (line col : Nat) : TokenBuilderM Token := do
  -- We're positioned after the $
  match ← peekCharM with
  | some '{' =>
      -- ${var} braced expansion
      let _ ← charM '{'
      let content ← takeWhileM (· != '}')
      let _ ← charM '}'
      let inner ← mkTok (.T_Literal content) line col
      mkTok (.T_DollarBraced true inner) line col
  | some '(' =>
      let _ ← charM '('
      match ← peekCharM with
      | some '(' =>
          -- $(( arithmetic ))
          let _ ← charM '('
          let content ← takeUntilM "))"
          let _ ← stringM "))"
          -- Parse arithmetic expression properly
          let inner := match Arithmetic.parse content with
            | some arithToken => arithToken
            | none => ⟨⟨0⟩, .T_Literal content⟩  -- Fallback to literal
          mkTok (.T_DollarArithmetic inner) line col
      | _ =>
          -- $( command )
          let content ← readNestedCommandsM mkTok line col
          let _ ← charM ')'
          mkTok (.T_DollarExpansion content) line col
  | some '[' =>
      -- $[ arithmetic ] (deprecated ksh form)
      let _ ← charM '['
      let content ← takeWhileM (· != ']')
      let _ ← charM ']'
      let inner ← mkTok (.T_Literal content) line col
      mkTok (.T_DollarBracket inner) line col
  | some c =>
      if variableStartChar c then
        -- Simple variable $foo
        let name ← takeWhile1M variableChar
        let inner ← mkTok (.T_Literal name) line col
        mkTok (.T_DollarBraced false inner) line col
      else if specialVariableChars.toList.contains c then
        -- Special variable $@, $*, $?, etc.
        let _ ← anyCharM
        let inner ← mkTok (.T_Literal (String.ofList [c])) line col
        mkTok (.T_DollarBraced false inner) line col
      else
        -- Just a literal $
        mkTok (.T_Literal "$") line col
  | none =>
      mkTok (.T_Literal "$") line col

where
  /-- Peek at next char in builder monad -/
  peekCharM : TokenBuilderM (Option Char) := do
    -- This is a simplified peek - in real impl we'd thread parser state
    pure none  -- Stub

  charM (_c : Char) : TokenBuilderM Unit := pure ()  -- Stub
  stringM (_s : String) : TokenBuilderM Unit := pure ()  -- Stub
  takeWhileM (_p : Char → Bool) : TokenBuilderM String := pure ""  -- Stub
  takeWhile1M (_p : Char → Bool) : TokenBuilderM String := pure ""  -- Stub
  takeUntilM (_s : String) : TokenBuilderM String := pure ""  -- Stub
  anyCharM : TokenBuilderM Char := pure ' '  -- Stub

  /-- Read nested commands (for $()) - simplified -/
  readNestedCommandsM (_mkTok : InnerToken Token → Nat → Nat → TokenBuilderM Token) (_line _col : Nat) : TokenBuilderM (List Token) := do
    pure []  -- Stub - would recursively parse

/-!
### Full Parser with Token Generation

This file historically implemented a custom `FullParser` state monad.
We are migrating that infrastructure to the new Parsec-based `ShellParser`
defined in `ShellCheck.Parser.Parsec`. To keep the rest of the grammar stable
while we migrate incrementally, we provide a small compatibility layer that
preserves the old names (`FullParser`, `peekFull`, `manyFull`, …) but delegates
to the Parsec implementation.
-/

/-- Parse a shellcheck directive from comment text.
    Returns annotations for "# shellcheck disable=SC2001,SC2046" etc. -/
def parseShellCheckDirective (comment : String) : List Annotation :=
  let trimmed := comment.trim
  -- Check if it starts with "shellcheck "
  if !trimmed.startsWith "shellcheck " then []
  else
    let rest := (trimmed.drop 11).trim  -- drop "shellcheck "
    -- Parse key=value pairs
    parseDirectives (rest.splitOn " ")
where
  parseDirectives : List String → List Annotation
    | [] => []
    | part :: rest =>
        let annotations := if part.startsWith "disable=" then
          -- Parse comma-separated SC codes
          let codes := (part.drop 8).splitOn ","  -- drop "disable="
          codes.filterMap parseCode
        else if part.startsWith "enable=" then
          -- For now just track that something is enabled
          let names := (part.drop 7).splitOn ","
          names.map Annotation.enableComment
        else if part.startsWith "source=" then
          [Annotation.sourceOverride (part.drop 7)]
        else if part.startsWith "shell=" then
          [Annotation.shellOverride (part.drop 6)]
        else if part.startsWith "source-path=" then
          [Annotation.sourcePath (part.drop 12)]
        else if part.startsWith "external-sources=" then
          let val := part.drop 17
          [Annotation.externalSources (val == "true")]
        else
          []
        annotations ++ parseDirectives rest

  parseCode (s : String) : Option Annotation :=
    -- Parse SCnnnn format
    let stripped := if s.startsWith "SC" then s.drop 2 else s
    match stripped.toNat? with
    | some code => some (Annotation.disableComment (Int.ofNat code) (Int.ofNat code + 1))
    | none => none

/-- Skip whitespace and comments, collecting shellcheck annotations -/
partial def skipAllSpaceCollectAnnotations : FullParser (List Annotation) := do
  let _ ← takeWhileFull (fun c => c.isWhitespace)
  match ← peekFull with
  | some '#' =>
      let _ ← charFull '#'
      let commentText ← takeWhileFull (· != '\n')
      let annots := parseShellCheckDirective commentText
      let moreAnnots ← skipAllSpaceCollectAnnotations
      pure (annots ++ moreAnnots)
  | some '\\' =>
      match ← optionalFull (attemptFull (stringFull "\\\n")) with
      | some _ => skipAllSpaceCollectAnnotations
      | none => pure []
  | _ => pure []

/-!
### Word Parsing

The word-level parsers (`readWordFull`, `readDoubleQuotedFull`, …) live in
`ShellCheck.Parser.Word`.
-/

/-!
### Command Parsing (mutually recursive)
-/

/-- Read an array value: (elem1 elem2 ...) -/
partial def readArrayFull : FullParser Token := do
  let _ ← charFull '('
  let elems ← readArrayElements []
  let _ ← charFull ')'
  mkTokenFull (.T_Array elems)
where
  readArrayElements (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | none => pure acc.reverse
    | some ')' => pure acc.reverse
    | some _ =>
        let elem ← readWordFull
        readArrayElements (elem :: acc)

/-- Read an assignment: VAR=value or VAR=(array) or VAR+=value -/
partial def readAssignmentFull : FullParser Token := do
  -- Capture position at the START of the assignment
  let (startLine, startCol) ← currentPos
  -- Read variable name
  let varName ← takeWhile1Full (fun c => variableChar c || c == '_')
  -- Check for += or =
  let isAppend ← match ← peekFull with
    | some '+' =>
        let _ ← charFull '+'
        let _ ← charFull '='
        pure true
    | some '=' =>
        let _ ← charFull '='
        pure false
    | _ => failure
  -- Check if array assignment
  let value ← match ← peekFull with
    | some '(' => readArrayFull
    | _ =>
        -- Read value word (may be empty)
        match ← optionalFull readWordFull with
        | some v => pure v
        | none => mkTokenFull (.T_Literal "")
  let mode := if isAppend then AST.AssignmentMode.append else .assign
  -- Create token at the START position
  let id ← freshIdFull
  recordPosition id startLine startCol startLine startCol
  return ⟨id, .T_Assignment mode varName [] value⟩

/-- Read a simple command (assignments + words), with redirects -/
partial def readSimpleCommandFull : FullParser Token := do
  skipHSpaceFull
  -- Don't parse reserved keywords as commands
  let reserved ← isReservedKeyword
  if reserved then failure
  let (cmdStartLine, cmdStartCol) ← currentPos
  let (assigns, words, redirects) ← readAssignsWordsAndRedirects [] [] []
  if assigns.isEmpty && words.isEmpty && redirects.isEmpty then failure
  else
    let cmd ←
      match assigns with
      | [] =>
          match words with
          | first :: rest =>
              match first.inner with
              | .T_NormalWord [⟨_, .T_Literal "["⟩] =>
                  -- `[ ... ]` is syntactically a simple command, but we keep a
                  -- dedicated AST node so condition-related checks work.
                  match rest.reverse with
                  | last :: middleRev =>
                      match last.inner with
                      | .T_NormalWord [⟨_, .T_Literal "]"⟩] =>
                          let args := middleRev.reverse
                          match ← optionalFull (ShellCheck.Parser.Condition.parseConditionTokensFull .singleBracket args) with
                          | some expr => mkTokenFullAt (.T_Condition .singleBracket expr) cmdStartLine cmdStartCol
                          | none => mkTokenFull (.T_SimpleCommand assigns words)
                      | _ => mkTokenFull (.T_SimpleCommand assigns words)
                  | [] => mkTokenFull (.T_SimpleCommand assigns words)
              | _ => mkTokenFull (.T_SimpleCommand assigns words)
          | [] => mkTokenFull (.T_SimpleCommand assigns words)
      | _ => mkTokenFull (.T_SimpleCommand assigns words)
    let result ← if redirects.isEmpty then
      pure cmd
    else
      mkTokenFull (.T_Redirecting redirects cmd)
    -- Check if there are heredocs in redirects and consume their content
    let heredocDelims := redirects.filterMap getHereDocDelimiter
    for (delim, dashedFlag) in heredocDelims do
      consumeHereDocContent delim dashedFlag
    pure result
where
  /-- Extract heredoc delimiter from a T_HereDoc token -/
  getHereDocDelimiter (t : Token) : Option (String × Dashed) :=
    match t.inner with
    | .T_HereDoc dashedFlag _ delim _ => some (delim, dashedFlag)
    | _ => none

  /-- Consume heredoc content until we find the delimiter line -/
  consumeHereDocContent (delim : String) (dashedFlag : Dashed) : FullParser Unit := do
    -- First skip to end of current line if not already there
    let _ ← takeWhileFull (· != '\n')
    -- Consume the newline
    match ← peekFull with
    | some '\n' => let _ ← charFull '\n'; pure ()
    | _ => pure ()
    -- Now consume lines until we hit the delimiter
    let rec consumeLines : FullParser Unit := do
      match ← peekFull with
      | none => pure ()  -- EOF
      | some _ =>
          -- Read current line
          let line ← takeWhileFull (· != '\n')
          -- Check if this line matches the delimiter
          let lineToCheck := match dashedFlag with
            | .dashed => line.dropWhile (· == '\t')
            | .undashed => line
          if lineToCheck == delim then
            -- Found delimiter, consume the newline and we're done
            match ← peekFull with
            | some '\n' => let _ ← charFull '\n'; pure ()
            | _ => pure ()
          else
            -- Not the delimiter, consume newline and continue
            match ← peekFull with
            | some '\n' =>
                let _ ← charFull '\n'
                consumeLines
            | _ => pure ()  -- EOF without delimiter
    consumeLines
  -- Check if a word represents a declaration builtin that accepts assignments after options
  isDeclarationBuiltin (word : Token) : Bool :=
    match word.inner with
    | .T_NormalWord [⟨_, .T_Literal s⟩] =>
        s == "declare" || s == "local" || s == "export" || s == "typeset" || s == "readonly"
    | _ => false

  -- Check if the first word in the accumulator is a declaration builtin
  -- wordAcc is in reverse order, so the first word is at the end
  isInDeclarationContext (wordAcc : List Token) : Bool :=
    match wordAcc.getLast? with
    | some w => isDeclarationBuiltin w
    | none => false

  -- First read assignments, then words and redirects
  -- For declaration builtins (declare, local, export, etc.), we keep trying
  -- to parse assignments even after other words/options have been parsed.
  readAssignsWordsAndRedirects (assignAcc : List Token) (wordAcc : List Token) (redirAcc : List Token)
      : FullParser (List Token × List Token × List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | none => pure (assignAcc.reverse, wordAcc.reverse, redirAcc.reverse)
    | some c =>
        -- Check for command terminators
        if c == '\n' || c == ';' || c == '&' || c == '|' || c == ')' || c == '}' then
          pure (assignAcc.reverse, wordAcc.reverse, redirAcc.reverse)
        else if c == '#' then
          let _ ← takeWhileFull (· != '\n')
          pure (assignAcc.reverse, wordAcc.reverse, redirAcc.reverse)
        -- Check for redirects: >, >>, <, <<, etc.
        -- BUT: <(...) and >(...) are process substitutions, not redirects
        else if c == '>' || c == '<' then
          let nextTwo ← peekStringFull 2
          if nextTwo == "<(" || nextTwo == ">(" then
            -- Process substitution - parse as word
            let word ← readWordFull
            readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
          else
            let redir ← readRedirectFull
            readAssignsWordsAndRedirects assignAcc wordAcc (redir :: redirAcc)
        -- Check for fd redirect like 2>, 1>&2
        else if c.isDigit then
          match ← optionalFull (attemptFull readFdRedirectFull) with
          | some redir => readAssignsWordsAndRedirects assignAcc wordAcc (redir :: redirAcc)
          | none =>
              -- Not a fd redirect, could be assignment or word
              -- Try assignment if: no words yet OR first word is declaration builtin
              if wordAcc.isEmpty || isInDeclarationContext wordAcc then
                match ← optionalFull (attemptFull readAssignmentFull) with
                | some assign => readAssignsWordsAndRedirects (assign :: assignAcc) wordAcc redirAcc
                | none =>
                    let word ← readWordFull
                    readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
              else
                let word ← readWordFull
                readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
        else
          -- Could be an assignment or a word
          -- Try assignment if: no words yet OR first word is declaration builtin
          if wordAcc.isEmpty || isInDeclarationContext wordAcc then
            match ← optionalFull (attemptFull readAssignmentFull) with
            | some assign => readAssignsWordsAndRedirects (assign :: assignAcc) wordAcc redirAcc
            | none =>
                let word ← readWordFull
                readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
          else
            let word ← readWordFull
            readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc

  /-- Read a heredoc delimiter, returning (delimiter_string, is_quoted) -/
  readHereDocDelimiter : FullParser (String × Bool) := do
    skipHSpaceFull
    match ← peekFull with
    | some '\'' =>
        -- Single-quoted: 'DELIM'
        let _ ← charFull '\''
        let delim ← takeWhileFull (· != '\'')
        let _ ← charFull '\''
        pure (delim, true)
    | some '"' =>
        -- Double-quoted: "DELIM"
        let _ ← charFull '"'
        let delim ← takeWhileFull (· != '"')
        let _ ← charFull '"'
        pure (delim, true)
    | some '\\' =>
        -- Escaped: \DELIM (makes it quoted)
        let _ ← charFull '\\'
        let delim ← takeWhileFull (fun c => !c.isWhitespace && c != '\n')
        pure (delim, true)
    | _ =>
        -- Unquoted delimiter
        let delim ← takeWhileFull (fun c => !c.isWhitespace && c != '\n' && c != ';' && c != '&' && c != '|')
        pure (delim, false)

  /-- Read a redirect operator and its target -/
  readRedirectFull : FullParser Token := do
    let opStart ← peekFull
    let op ← match opStart with
      | some '>' =>
          let _ ← charFull '>'
          match ← peekFull with
          | some '>' =>
              let _ ← charFull '>'
              pure ">>"
          | some '&' =>
              let _ ← charFull '&'
              pure ">&"
          | some '|' =>
              let _ ← charFull '|'
              pure ">|"
          | _ => pure ">"
      | some '<' =>
          let _ ← charFull '<'
          match ← peekFull with
          | some '<' =>
              let _ ← charFull '<'
              match ← peekFull with
              | some '-' =>
                  let _ ← charFull '-'
                  pure "<<-"
              | _ => pure "<<"
          | some '>' =>
              let _ ← charFull '>'
              pure "<>"
          | some '&' =>
              let _ ← charFull '&'
              pure "<&"
          | _ => pure "<"
      | _ => failure
    let opTok ← mkTokenFull (.T_Literal op)
    skipHSpaceFull
    -- Handle here-doc specially
    if op == "<<" || op == "<<-" then
      -- Read the delimiter and determine if it's quoted
      let (delimStr, isQuoted) ← readHereDocDelimiter
      -- After reading the command line, we need to consume the heredoc content
      -- For now, register it to be consumed after the current line
      -- Mark whether content should be analyzed (unquoted) or not (quoted)
      let delimTok ← mkTokenFull (.T_Literal delimStr)
      let dashedFlag := if op == "<<-" then Dashed.dashed else Dashed.undashed
      let quotedFlag := if isQuoted then Quoted.quoted else Quoted.unquoted
      -- Create T_HereDoc with empty content for now - actual content consumed later
      mkTokenFull (.T_HereDoc dashedFlag quotedFlag delimStr [delimTok])
    else
      -- For file redirects, read the target
      match ← peekFull with
      | some '-' =>
          -- Close fd: >&- or <&-
          let _ ← charFull '-'
          let target ← mkTokenFull (.T_Literal "-")
          mkTokenFull (.T_IoFile opTok target)
      | some c =>
          if c.isDigit && (op == ">&" || op == "<&") then
            -- Dup fd: >&2, <&0
            let fd ← takeWhile1Full Char.isDigit
            mkTokenFull (.T_IoDuplicate opTok fd)
          else
            let target ← readWordFull
            mkTokenFull (.T_IoFile opTok target)
      | none => failure

  /-- Read a fd redirect like 2>, 2>>, 2>&1 -/
  readFdRedirectFull : FullParser Token := do
    let (startLine, startCol) ← currentPos
    let fd ← takeWhile1Full Char.isDigit
    let opStart ← peekFull
    if opStart != some '>' && opStart != some '<' then failure
    let redir ← readRedirectFull
    mkTokenFullAt (.T_FdRedirect fd redir) startLine startCol

/-- Read raw content until `terminator` (not consumed). Fails on EOF. -/
partial def readUntilStringFull (terminator : String) : FullParser String := do
  let rec go (acc : List Char) (inSingle inDouble escaped : Bool) : FullParser String := do
    -- Only consider the terminator when we're not in a quoted/escaped context.
    if !inSingle && !inDouble && !escaped then
      let look ← peekStringFull terminator.length
      if look == terminator then
        return String.ofList acc.reverse

    match ← peekFull with
    | none =>
        ShellCheck.Parser.Parsec.ShellParser.fail s!"expected closing {terminator}"
    | some c =>
        let _ ← anyCharFull
        let (inSingle', inDouble', escaped') :=
          if escaped then
            (inSingle, inDouble, false)
          else if inSingle then
            (c != '\'', false, false)
          else if inDouble then
            if c == '"' then
              (false, false, false)
            else if c == '\\' then
              (false, true, true)
            else
              (false, true, false)
          else
            if c == '\'' then
              (true, false, false)
            else if c == '"' then
              (false, true, false)
            else if c == '\\' then
              (false, false, true)
            else
              (false, false, false)
        go (c :: acc) inSingle' inDouble' escaped'
  go [] false false false

/-- Read a `[[ ... ]]` condition expression. -/
partial def readDoubleBracketConditionFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let _ ← stringFull "[["
  let condTokens ← readCondTokens []
  skipAllSpaceFull
  let _ ← stringFull "]]"
  let expr ←
    match ← optionalFull (ShellCheck.Parser.Condition.parseConditionTokensFull .doubleBracket condTokens) with
    | some e => pure e
    | none =>
        -- Fall back to a minimal tree so the rest of the file can still parse.
        if condTokens.isEmpty then
          mkTokenFullAt (.TC_Empty .doubleBracket) startLine startCol
        else
          let fallbackWord :=
            condTokens.find? (fun t => match t.inner with | .T_Literal _ => false | _ => true)
              |>.getD condTokens.head!
          mkTokenFullAt (.TC_Nullary .doubleBracket fallbackWord) startLine startCol
  mkTokenFullAt (.T_Condition .doubleBracket expr) startLine startCol
where
  /-- Tokenize the body of `[[ ... ]]` into a list of operator/word tokens. -/
  readCondTokens (acc : List Token) : FullParser (List Token) := do
    skipAllSpaceFull
    let done ← peekKeyword "]]"
    if done then
      pure acc.reverse
    else
      let (tokStartLine, tokStartCol) ← currentPos
      let look2 ← peekStringFull 2
      if look2 == "&&" || look2 == "||" then
        let op ← stringFull look2
        let tok ← mkTokenFullAt (.T_Literal op) tokStartLine tokStartCol
        readCondTokens (tok :: acc)
      else
        match ← peekFull with
        | some '(' | some ')' | some '<' | some '>' =>
            let c ← anyCharFull
            let tok ← mkTokenFullAt (.T_Literal (String.ofList [c])) tokStartLine tokStartCol
            readCondTokens (tok :: acc)
        | _ =>
            let w ← readWordFull
            readCondTokens (w :: acc)

/-- Read a pipe sequence: cmd | cmd | cmd -/
partial def readPipeSequenceFull : FullParser Token := do
  let first ← readPipeCommandFull
  skipHSpaceFull
  let (seps, cmds) ← readPipeContinuation [] [first]
  if cmds.length == 1 then
    pure first
  else
    mkTokenFull (.T_Pipeline seps cmds)
where
  /-- Read a command that can appear in a pipeline -/
  readPipeCommandFull : FullParser Token := do
    skipHSpaceFull
    let isDoubleBracket ← peekKeyword "[["
    if isDoubleBracket then
      readDoubleBracketConditionFull
    else match ← peekFull with
    | some '{' => readBraceGroupInPipe
    | some '(' => readSubshellInPipe
    | _ =>
        -- Check for keywords
        let isIf ← peekKeyword "if"
        if isIf then readIfInPipe
        else
          let isWhile ← peekKeyword "while"
          if isWhile then readWhileInPipe
          else
            let isUntil ← peekKeyword "until"
            if isUntil then readUntilInPipe
            else
              let isFor ← peekKeyword "for"
              if isFor then readForInPipe
              else
                let isCase ← peekKeyword "case"
                if isCase then readCaseInPipe
                else
                  let isSelect ← peekKeyword "select"
                  if isSelect then readSelectInPipe
                  else
                    let isFunction ← peekKeyword "function"
                    if isFunction then readFunctionInPipe
                    else
                      -- Try POSIX function syntax: name() { body }
                      match ← optionalFull (attemptFull readPosixFunctionInPipe) with
                      | some func => pure func
                      | none => readSimpleCommandFull

  /-- Read a POSIX function definition in pipe context: name() { body } -/
  readPosixFunctionInPipe : FullParser Token := do
    let name ← takeWhile1Full (fun c => variableChar c || c == '-' || c == '.')
    skipHSpaceFull
    let _ ← stringFull "()"
    skipAllSpaceFull
    let body ← readBraceGroupInPipe
    mkTokenFull (.T_Function ⟨false⟩ ⟨true⟩ name body)

  -- Forward declarations for compound commands in pipe
  readBraceGroupInPipe : FullParser Token := do
    let _ ← charFull '{'
    skipAllSpaceFull
    let cmds ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← charFull '}'
    mkTokenFull (.T_BraceGroup cmds)

  readSubshellInPipe : FullParser Token := do
    match ← optionalFull (attemptFull (stringFull "((")) with
    | some _ =>
        let content ← readArithContentHelper
        let _ ← stringFull "))"
        let inner ← mkTokenFull (.T_Literal content)
        mkTokenFull (.T_Arithmetic inner)
    | none =>
        let _ ← charFull '('
        skipAllSpaceFull
        let cmds ← readTermInPipe
        skipAllSpaceFull
        let _ ← charFull ')'
        mkTokenFull (.T_Subshell cmds)

  readIfInPipe : FullParser Token := do
    let _ ← consumeKeyword "if"
    skipAllSpaceFull
    let cond ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "then"
    skipAllSpaceFull
    let thenBody ← readTermInPipe
    let (branches, elseBody) ← readElifElseInPipe [(cond, thenBody)] []
    mkTokenFull (.T_IfExpression branches elseBody)

  readElifElseInPipe (branches : List (List Token × List Token)) (_acc : List Token)
      : FullParser (List (List Token × List Token) × List Token) := do
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let isElif ← peekKeyword "elif"
    if isElif then
      let _ ← consumeKeyword "elif"
      skipAllSpaceFull
      let cond ← readTermInPipe
      skipHSpaceFull
      let _ ← optionalFull (charFull ';')
      skipAllSpaceFull
      let _ ← consumeKeyword "then"
      skipAllSpaceFull
      let body ← readTermInPipe
      readElifElseInPipe (branches ++ [(cond, body)]) []
    else
      let isElse ← peekKeyword "else"
      if isElse then
        let _ ← consumeKeyword "else"
        skipAllSpaceFull
        let elseBody ← readTermInPipe
        skipHSpaceFull
        let _ ← optionalFull (charFull ';')
        skipAllSpaceFull
        let _ ← consumeKeyword "fi"
        pure (branches, elseBody)
      else
        let _ ← consumeKeyword "fi"
        pure (branches, [])

  readWhileInPipe : FullParser Token := do
    let _ ← consumeKeyword "while"
    skipAllSpaceFull
    let cond ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "do"
    skipAllSpaceFull
    let body ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "done"
    mkTokenFull (.T_WhileExpression cond body)

  readUntilInPipe : FullParser Token := do
    let _ ← consumeKeyword "until"
    skipAllSpaceFull
    let cond ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "do"
    skipAllSpaceFull
    let body ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "done"
    mkTokenFull (.T_UntilExpression cond body)

  readForInPipe : FullParser Token := do
    attemptFull readForArithInPipe <|> readForInInPipe

  readForArithInPipe : FullParser Token := do
    let _ ← consumeKeyword "for"
    skipHSpaceFull
    let _ ← stringFull "(("
    skipHSpaceFull
    let initContent ← takeWhileFull (· != ';')
    let init ← mkTokenFull (.T_Literal initContent)
    let _ ← charFull ';'
    skipHSpaceFull
    let condContent ← takeWhileFull (· != ';')
    let cond ← mkTokenFull (.T_Literal condContent)
    let _ ← charFull ';'
    skipHSpaceFull
    let incrContent ← readArithContentHelper
    let incr ← mkTokenFull (.T_Literal incrContent)
    let _ ← stringFull "))"
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "do"
    skipAllSpaceFull
    let body ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "done"
    mkTokenFull (.T_ForArithmetic init cond incr body)

  readForInInPipe : FullParser Token := do
    let _ ← consumeKeyword "for"
    skipHSpaceFull
    let varName ← takeWhile1Full variableChar
    skipHSpaceFull
    let hasIn ← peekKeyword "in"
    let words ← if hasIn then do
      let _ ← consumeKeyword "in"
      skipHSpaceFull
      readForWordsInPipe []
    else pure []
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "do"
    skipAllSpaceFull
    let body ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "done"
    mkTokenFull (.T_ForIn varName words body)

  readForWordsInPipe (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWordFull
            readForWordsInPipe (word :: acc)

  readCaseInPipe : FullParser Token := do
    let _ ← consumeKeyword "case"
    skipHSpaceFull
    let word ← readWordFull
    skipHSpaceFull
    let _ ← consumeKeyword "in"
    skipAllSpaceFull
    let cases ← readCaseItemsInPipe []
    let _ ← consumeKeyword "esac"
    mkTokenFull (.T_CaseExpression word cases)

  readCaseItemsInPipe (acc : List (CaseType × List Token × List Token))
      : FullParser (List (CaseType × List Token × List Token)) := do
    skipAllSpaceFull
    let isEsac ← peekKeyword "esac"
    if isEsac then pure acc.reverse
    else
      let _ ← optionalFull (charFull '(')
      let patterns ← readPatternsInPipe []
      let _ ← charFull ')'
      skipAllSpaceFull
      let (cmds, terminator) ← readCaseBodyInPipe [] .caseBreak
      readCaseItemsInPipe ((terminator, patterns, cmds) :: acc)

  readPatternsInPipe (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    let pat ← readWordFull
    skipHSpaceFull
    match ← peekFull with
    | some '|' =>
        let _ ← charFull '|'
        readPatternsInPipe (pat :: acc)
    | _ => pure (pat :: acc).reverse

  readCaseBodyInPipe (acc : List Token) (termType : CaseType) : FullParser (List Token × CaseType) := do
    skipAllSpaceFull  -- Skip newlines and spaces
    match ← peekFull with
    | none => pure (acc.reverse, termType)
    | some ';' =>
        let _ ← charFull ';'
        match ← peekFull with
        | some ';' =>
            let _ ← charFull ';'
            match ← peekFull with
            | some '&' =>
                let _ ← charFull '&'
                pure (acc.reverse, .caseContinue)
            | _ => pure (acc.reverse, .caseBreak)
        | some '&' =>
            let _ ← charFull '&'
            pure (acc.reverse, .caseFallThrough)
        | _ =>
            skipAllSpaceFull
            let cmd ← readAndOrInPipe
            readCaseBodyInPipe (cmd :: acc) termType
    | some _ =>
        let isEsac ← peekKeyword "esac"
        if isEsac then pure (acc.reverse, termType)
        else
          let cmd ← readAndOrInPipe
          readCaseBodyInPipe (cmd :: acc) termType

  readFunctionInPipe : FullParser Token := do
    let _ ← consumeKeyword "function"
    skipHSpaceFull
    let name ← takeWhile1Full (fun c => variableChar c || c == '-' || c == '.')
    skipHSpaceFull
    let _ ← optionalFull (attemptFull (stringFull "()"))
    skipAllSpaceFull
    let body ← readBraceGroupInPipe
    mkTokenFull (.T_Function ⟨true⟩ ⟨false⟩ name body)

  readSelectInPipe : FullParser Token := do
    let _ ← consumeKeyword "select"
    skipHSpaceFull
    let varName ← takeWhile1Full variableChar
    skipHSpaceFull
    -- "in" is optional - if omitted, uses positional parameters
    let hasIn ← peekKeyword "in"
    let words ← if hasIn then do
      let _ ← consumeKeyword "in"
      skipHSpaceFull
      readSelectWordsInPipe []
    else
      pure []
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "do"
    skipAllSpaceFull
    let body ← readTermInPipe
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let _ ← consumeKeyword "done"
    mkTokenFull (.T_SelectIn varName words body)

  readSelectWordsInPipe (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWordFull
            readSelectWordsInPipe (word :: acc)

  -- Self-contained term/andor for inside pipe context
  -- These form a mutually recursive group within the where clause

  readTermInPipe : FullParser (List Token) := do
    let first ← readAndOrInPipe
    readTermContinuationInPipe [first]

  readTermContinuationInPipe (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | some ';' =>
        let _ ← charFull ';'
        match ← peekFull with
        | some ';' => pure acc.reverse  -- This is ;; not ;
        | _ =>
            skipAllSpaceFull
            match ← optionalFull readAndOrInPipe with
            | some next => readTermContinuationInPipe (next :: acc)
            | none => pure acc.reverse
    | some '&' =>
        match ← optionalFull (attemptFull (stringFull "&&")) with
        | some _ => pure acc.reverse  -- Already handled by readAndOrInPipe
        | none =>
            let _ ← charFull '&'
            let last := acc.head!
            let rest := acc.tail!
            let bgLast ← mkTokenFull (.T_Backgrounded last)
            skipAllSpaceFull
            match ← optionalFull readAndOrInPipe with
            | some next => readTermContinuationInPipe (next :: bgLast :: rest)
            | none => pure (bgLast :: rest).reverse
    | some '\n' =>
        let _ ← charFull '\n'
        skipAllSpaceFull
        -- Check for terminating keywords
        let isDone ← peekKeyword "done"
        let isFi ← peekKeyword "fi"
        let isElif ← peekKeyword "elif"
        let isElse ← peekKeyword "else"
        let isEsac ← peekKeyword "esac"
        let isThen ← peekKeyword "then"
        let isDo ← peekKeyword "do"
        if isDone || isFi || isElif || isElse || isEsac || isThen || isDo then
          pure acc.reverse
        else
          match ← optionalFull readAndOrInPipe with
          | some next => readTermContinuationInPipe (next :: acc)
          | none => pure acc.reverse
    | _ => pure acc.reverse

  readAndOrInPipe : FullParser Token := do
    let first ← readPipelineInPipe
    readAndOrContinuationInPipe first

  readAndOrContinuationInPipe (left : Token) : FullParser Token := do
    skipHSpaceFull
    match ← peekFull with
    | some '&' =>
        match ← optionalFull (attemptFull (stringFull "&&")) with
        | some _ =>
            skipAllSpaceFull
            let right ← readPipelineInPipe
            let combined ← mkTokenFull (.T_AndIf left right)
            readAndOrContinuationInPipe combined
        | none => pure left
    | some '|' =>
        match ← optionalFull (attemptFull (stringFull "||")) with
        | some _ =>
            skipAllSpaceFull
            let right ← readPipelineInPipe
            let combined ← mkTokenFull (.T_OrIf left right)
            readAndOrContinuationInPipe combined
        | none => pure left
    | _ => pure left

  readPipelineInPipe : FullParser Token := do
    skipHSpaceFull
    let banged ← optionalFull (charFull '!' <* skipHSpaceFull)
    let pipeline ← readPipeSequenceInPipe
    match banged with
    | some _ => mkTokenFull (.T_Banged pipeline)
    | none => pure pipeline

  readPipeSequenceInPipe : FullParser Token := do
    let first ← readPipeCommandFull
    skipHSpaceFull
    let (seps, cmds) ← readPipeContinuationInPipe [] [first]
    if cmds.length == 1 then
      pure first
    else
      mkTokenFull (.T_Pipeline seps cmds)

  readPipeContinuationInPipe (seps : List Token) (cmds : List Token) : FullParser (List Token × List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | some '|' =>
        -- Use lookahead to check for || without consuming it
        let next2 ← peekStringFull 2
        if next2 == "||" then
          pure (seps.reverse, cmds.reverse)  -- This is || not |, don't consume
        else
          let pipeStr ← readPipeOpInPipe
          let sepTok ← mkTokenFull (.T_Pipe pipeStr)
          skipAllSpaceFull
          let cmd ← readPipeCommandFull
          readPipeContinuationInPipe (sepTok :: seps) (cmd :: cmds)
    | _ => pure (seps.reverse, cmds.reverse)

  readPipeOpInPipe : FullParser String := do
    let _ ← charFull '|'
    match ← peekFull with
    | some '&' =>
        let _ ← anyCharFull
        pure "|&"
    | _ => pure "|"

  readPipeContinuation (seps : List Token) (cmds : List Token) : FullParser (List Token × List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | some '|' =>
        -- Use lookahead to check for || without consuming it
        let next2 ← peekStringFull 2
        if next2 == "||" then
          pure (seps.reverse, cmds.reverse)  -- This is || not |, don't consume
        else
          let pipeStr ← readPipeOpFull
          let sepTok ← mkTokenFull (.T_Pipe pipeStr)
          skipAllSpaceFull
          let cmd ← readPipeCommandFull
          readPipeContinuation (sepTok :: seps) (cmd :: cmds)
    | _ => pure (seps.reverse, cmds.reverse)

  readPipeOpFull : FullParser String := do
    let _ ← charFull '|'
    match ← peekFull with
    | some '&' =>
        let _ ← anyCharFull
        pure "|&"
    | _ => pure "|"

/-- Read a pipeline: [!] pipe_sequence -/
def readPipelineFull : FullParser Token := do
  skipHSpaceFull
  let banged ← optionalFull (charFull '!' <* skipHSpaceFull)
  let pipeline ← readPipeSequenceFull
  match banged with
  | some _ => mkTokenFull (.T_Banged pipeline)
  | none => pure pipeline

/-- Read an and-or list: pipeline ((&&|||) pipeline)* -/
partial def readAndOrFull : FullParser Token := do
  let first ← readPipelineFull
  skipHSpaceFull
  readAndOrContinuation first
where
  readAndOrContinuation (left : Token) : FullParser Token := do
    skipHSpaceFull
    match ← peekFull with
    | some '&' =>
        match ← optionalFull (attemptFull (stringFull "&&")) with
        | some _ =>
            skipAllSpaceFull
            let right ← readPipelineFull
            let combined ← mkTokenFull (.T_AndIf left right)
            readAndOrContinuation combined
        | none =>
            pure left
    | some '|' =>
        match ← optionalFull (attemptFull (stringFull "||")) with
        | some _ =>
            skipAllSpaceFull
            let right ← readPipelineFull
            let combined ← mkTokenFull (.T_OrIf left right)
            readAndOrContinuation combined
        | none =>
            pure left
    | _ =>
        pure left

/-- Read an and-or with any preceding shellcheck annotations -/
partial def readAndOrWithAnnotations : FullParser Token := do
  let annotations ← skipAllSpaceCollectAnnotations
  let cmd ← readAndOrFull
  if annotations.isEmpty then
    pure cmd
  else
    mkTokenFull (.T_Annotation annotations cmd)

/-- Read a term: and-or ((;|&|newline) and-or)* -/
partial def readTermFull : FullParser (List Token) := do
  -- The caller should have already skipped initial space
  let first ← readAndOrFull
  readTermContinuation [first]
where
  readTermContinuation (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | some ';' =>
        let _ ← charFull ';'
        match ← peekFull with
        | some ';' => pure acc.reverse  -- This is ;; not ;
        | _ =>
            -- Use attemptFull to backtrack if the next command fails
            -- (readAndOrWithAnnotations consumes whitespace before parsing)
            match ← optionalFull (attemptFull readAndOrWithAnnotations) with
            | some next => readTermContinuation (next :: acc)
            | none => pure acc.reverse
    | some '&' =>
        match ← optionalFull (attemptFull (stringFull "&&")) with
        | some _ => pure acc.reverse  -- Already handled by readAndOrFull
        | none =>
            let _ ← charFull '&'
            -- Background the last command
            let last := acc.head!
            let rest := acc.tail!
            let bgLast ← mkTokenFull (.T_Backgrounded last)
            match ← optionalFull (attemptFull readAndOrWithAnnotations) with
            | some next => readTermContinuation (next :: bgLast :: rest)
            | none => pure (bgLast :: rest).reverse
    | some '\n' =>
        let _ ← charFull '\n'
        match ← optionalFull (attemptFull readAndOrWithAnnotations) with
        | some next => readTermContinuation (next :: acc)
        | none =>
            -- Check for end markers
            skipAllSpaceFull
            match ← peekFull with
            | none => pure acc.reverse
            | some ')' => pure acc.reverse  -- End of subshell
            | some '}' => pure acc.reverse  -- End of brace group
            | _ => pure acc.reverse
    | _ => pure acc.reverse

/-!
### Control Flow (if/while/for/case/select)

Now that readTermFull and readAndOrFull are defined, we can add control flow.
-/

/-- Read a subshell: ( commands ) -/
partial def readSubshellFull : FullParser Token := do
  let _ ← charFull '('
  skipAllSpaceFull
  let cmds ← readTermFull
  skipAllSpaceFull
  let _ ← charFull ')'
  mkTokenFull (.T_Subshell cmds)

/-- Read a brace group: { commands } -/
partial def readBraceGroupFull : FullParser Token := do
  let _ ← charFull '{'
  skipAllSpaceFull
  let cmds ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← charFull '}'
  mkTokenFull (.T_BraceGroup cmds)

/-- Read an if expression: if cond; then body; [elif cond; then body;]* [else body;] fi -/
partial def readIfExpressionFull : FullParser Token := do
  let _ ← consumeKeyword "if"
  skipAllSpaceFull
  let cond ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "then"
  skipAllSpaceFull
  let thenBody ← readTermFull
  let (branches, elseBody) ← readElifElse [(cond, thenBody)] []
  mkTokenFull (.T_IfExpression branches elseBody)
where
  readElifElse (branches : List (List Token × List Token)) (_elseAcc : List Token)
      : FullParser (List (List Token × List Token) × List Token) := do
    skipHSpaceFull
    let _ ← optionalFull (charFull ';')
    skipAllSpaceFull
    let isElif ← peekKeyword "elif"
    if isElif then
      let _ ← consumeKeyword "elif"
      skipAllSpaceFull
      let cond ← readTermFull
      skipHSpaceFull
      let _ ← optionalFull (charFull ';')
      skipAllSpaceFull
      let _ ← consumeKeyword "then"
      skipAllSpaceFull
      let body ← readTermFull
      readElifElse (branches ++ [(cond, body)]) []
    else
      let isElse ← peekKeyword "else"
      if isElse then
        let _ ← consumeKeyword "else"
        skipAllSpaceFull
        let elseBody ← readTermFull
        skipHSpaceFull
        let _ ← optionalFull (charFull ';')
        skipAllSpaceFull
        let _ ← consumeKeyword "fi"
        pure (branches, elseBody)
      else
        let _ ← consumeKeyword "fi"
        pure (branches, [])

/-- Read a while expression: while cond; do body; done -/
partial def readWhileExpressionFull : FullParser Token := do
  let _ ← consumeKeyword "while"
  skipAllSpaceFull
  let cond ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "do"
  skipAllSpaceFull
  let body ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "done"
  mkTokenFull (.T_WhileExpression cond body)

/-- Read an until expression: until cond; do body; done -/
partial def readUntilExpressionFull : FullParser Token := do
  let _ ← consumeKeyword "until"
  skipAllSpaceFull
  let cond ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "do"
  skipAllSpaceFull
  let body ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "done"
  mkTokenFull (.T_UntilExpression cond body)

/-- Read a for-in expression: for var [in words]; do body; done -/
partial def readForInFull : FullParser Token := do
  let _ ← consumeKeyword "for"
  skipHSpaceFull
  let varName ← takeWhile1Full variableChar
  skipHSpaceFull
  let hasIn ← peekKeyword "in"
  let words ← if hasIn then do
    let _ ← consumeKeyword "in"
    skipHSpaceFull
    readForWords []
  else pure []
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "do"
  skipAllSpaceFull
  let body ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "done"
  mkTokenFull (.T_ForIn varName words body)
where
  readForWords (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWordFull
            readForWords (word :: acc)

/-- Read a for arithmetic expression: for ((init; cond; incr)); do body; done -/
partial def readForArithmeticFull : FullParser Token := do
  let _ ← consumeKeyword "for"
  skipHSpaceFull
  let _ ← stringFull "(("
  skipHSpaceFull
  let initContent ← takeWhileFull (· != ';')
  let init ← mkTokenFull (.T_Literal initContent)
  let _ ← charFull ';'
  skipHSpaceFull
  let condContent ← takeWhileFull (· != ';')
  let cond ← mkTokenFull (.T_Literal condContent)
  let _ ← charFull ';'
  skipHSpaceFull
  let incrContent ← readArithContentHelper
  let incr ← mkTokenFull (.T_Literal incrContent)
  let _ ← stringFull "))"
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "do"
  skipAllSpaceFull
  let body ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "done"
  mkTokenFull (.T_ForArithmetic init cond incr body)

/-- Read a case expression: case word in pattern) cmds ;; ... esac -/
partial def readCaseExpressionFull : FullParser Token := do
  let _ ← consumeKeyword "case"
  skipHSpaceFull
  let word ← readWordFull
  skipHSpaceFull
  let _ ← consumeKeyword "in"
  skipAllSpaceFull
  let cases ← readCaseItems []
  let _ ← consumeKeyword "esac"
  mkTokenFull (.T_CaseExpression word cases)
where
  readCaseItems (acc : List (CaseType × List Token × List Token))
      : FullParser (List (CaseType × List Token × List Token)) := do
    skipAllSpaceFull
    let isEsac ← peekKeyword "esac"
    if isEsac then pure acc.reverse
    else
      let _ ← optionalFull (charFull '(')
      let patterns ← readPatterns []
      let _ ← charFull ')'
      skipAllSpaceFull
      let (cmds, terminator) ← readCaseBody [] .caseBreak
      readCaseItems ((terminator, patterns, cmds) :: acc)

  readPatterns (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    let pat ← readWordFull
    skipHSpaceFull
    match ← peekFull with
    | some '|' =>
        let _ ← charFull '|'
        readPatterns (pat :: acc)
    | _ => pure (pat :: acc).reverse

  readCaseBody (acc : List Token) (termType : CaseType) : FullParser (List Token × CaseType) := do
    skipAllSpaceFull  -- Skip newlines and spaces
    match ← peekFull with
    | none => pure (acc.reverse, termType)
    | some ';' =>
        let _ ← charFull ';'
        match ← peekFull with
        | some ';' =>
            let _ ← charFull ';'
            match ← peekFull with
            | some '&' =>
                let _ ← charFull '&'
                pure (acc.reverse, .caseContinue)
            | _ => pure (acc.reverse, .caseBreak)
        | some '&' =>
            let _ ← charFull '&'
            pure (acc.reverse, .caseFallThrough)
        | _ =>
            skipAllSpaceFull
            let cmd ← readAndOrFull
            readCaseBody (cmd :: acc) termType
    | some _ =>
        let isEsac ← peekKeyword "esac"
        if isEsac then pure (acc.reverse, termType)
        else
          let cmd ← readAndOrFull
          readCaseBody (cmd :: acc) termType

/-- Read a select expression: select var [in words]; do body; done -/
partial def readSelectFull : FullParser Token := do
  let _ ← consumeKeyword "select"
  skipHSpaceFull
  let varName ← takeWhile1Full variableChar
  skipHSpaceFull
  -- "in" is optional - if omitted, uses positional parameters
  let hasIn ← peekKeyword "in"
  let words ← if hasIn then do
    let _ ← consumeKeyword "in"
    skipHSpaceFull
    readSelectWords []
  else
    pure []
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "do"
  skipAllSpaceFull
  let body ← readTermFull
  skipHSpaceFull
  let _ ← optionalFull (charFull ';')
  skipAllSpaceFull
  let _ ← consumeKeyword "done"
  mkTokenFull (.T_SelectIn varName words body)
where
  readSelectWords (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWordFull
            readSelectWords (word :: acc)

/-- Read an arithmetic command: (( expr )) -/
partial def readArithmeticCommandFull : FullParser Token := do
  let _ ← stringFull "(("
  let content ← readArithContentHelper
  let _ ← stringFull "))"
  let inner ← mkTokenFull (.T_Literal content)
  mkTokenFull (.T_Arithmetic inner)

/-- Read a function definition: function name { body } or name() { body } -/
partial def readFunctionFull : FullParser Token := do
  let hasKeyword ← peekKeyword "function"
  if hasKeyword then
    let _ ← consumeKeyword "function"
    skipHSpaceFull
    let name ← takeWhile1Full (fun c => variableChar c || c == '-' || c == '.')
    skipHSpaceFull
    let _ ← optionalFull (attemptFull (stringFull "()"))
    skipAllSpaceFull
    let body ← readBraceGroupFull
    mkTokenFull (.T_Function ⟨true⟩ ⟨false⟩ name body)
  else failure

/-- Read a POSIX function definition: name() { body } -/
  partial def readPosixFunctionFull : FullParser Token := do
    -- Read function name (must be valid identifier)
    let name ← takeWhile1Full (fun c => variableChar c || c == '-' || c == '.')
    -- Must be followed by ()
    skipHSpaceFull
    let _ ← stringFull "()"
    skipAllSpaceFull
    let body ← readBraceGroupFull
    mkTokenFull (.T_Function ⟨false⟩ ⟨true⟩ name body)

  /-- Read any command (compound or simple) -/
  partial def readCommandFull : FullParser Token := do
    skipHSpaceFull
    let isDoubleBracket ← peekKeyword "[["
    if isDoubleBracket then
      readDoubleBracketConditionFull
    else match ← peekFull with
    | some '{' => readBraceGroupFull
    | some '(' =>
        match ← optionalFull (attemptFull (stringFull "((")) with
        | some _ =>
            let content ← readArithContentHelper
            let _ ← stringFull "))"
            let inner ← mkTokenFull (.T_Literal content)
            mkTokenFull (.T_Arithmetic inner)
        | none => readSubshellFull
    | _ =>
        let isIf ← peekKeyword "if"
        if isIf then readIfExpressionFull
        else
          let isWhile ← peekKeyword "while"
          if isWhile then readWhileExpressionFull
          else
            let isUntil ← peekKeyword "until"
            if isUntil then readUntilExpressionFull
            else
              let isFor ← peekKeyword "for"
              if isFor then attemptFull readForArithmeticFull <|> readForInFull
              else
                let isCase ← peekKeyword "case"
                if isCase then readCaseExpressionFull
                else
                  let isSelect ← peekKeyword "select"
                  if isSelect then readSelectFull
                  else
                    let isFunction ← peekKeyword "function"
                    if isFunction then readFunctionFull
                    else
                      -- Try POSIX function syntax: name() { body }
                      match ← optionalFull (attemptFull readPosixFunctionFull) with
                      | some func => pure func
                      | none => readSimpleCommandFull

/-- Read a complete script -/
def readScriptFull : FullParser Token := do
  -- Don't skip whitespace first - shebang must be at very start
  -- Check for shebang
  let firstChar ← peekFull
  let shebang ← match firstChar with
    | some '#' =>
        let secondChar ← do
          let _ ← anyCharFull  -- consume #
          peekFull
        match secondChar with
        | some '!' =>
            let _ ← anyCharFull  -- consume !
            let line ← takeWhileFull (· != '\n')
            let _ ← optionalFull (charFull '\n')
            mkTokenFull (.T_Literal ("#!" ++ line))
        | _ =>
            -- Just a comment, not a shebang - but we already consumed #
            let _ ← takeWhileFull (· != '\n')
            let _ ← optionalFull (charFull '\n')
            mkTokenFull (.T_Literal "")
    | _ =>
        mkTokenFull (.T_Literal "")

  skipAllSpaceFull
  let commands ← readTermFull
  skipAllSpaceFull
  mkTokenFull (.T_Script shebang commands)

/-- Parse a string as commands (for subshell content), with position offset -/
def parseSubshellContent (content : String) (filename : String) (startId : Nat) (offsetLine : Nat) (offsetCol : Nat) : (List Token × Nat × Std.HashMap Id (Position × Position)) :=
  let it := ShellCheck.Parser.Parsec.PosIterator.create content
  let initState : FullParserState :=
    { ShellCheck.Parser.Parsec.mkShellState filename with nextId := startId }
  match readTermFull initState it with
  | .success _ (tokens, st) =>
      -- Offset all positions by the original $() location
      let offsetPositions := st.positions.fold (init := {}) fun m k (startPos, endPos) =>
        let newStart : Position := {
          posFile := startPos.posFile
          posLine := startPos.posLine + offsetLine - 1  -- -1 because sub-parse starts at line 1
          posColumn := if startPos.posLine == 1
                       then startPos.posColumn + offsetCol - 1  -- Only offset column on first line
                       else startPos.posColumn
        }
        let newEnd : Position := {
          posFile := endPos.posFile
          posLine := endPos.posLine + offsetLine - 1
          posColumn := if endPos.posLine == 1
                       then endPos.posColumn + offsetCol - 1
                       else endPos.posColumn
        }
        m.insert k (newStart, newEnd)
      (tokens, st.nextId, offsetPositions)
  | .error _ _ =>
      -- On parse error, return a literal token
      let litTok : Token := ⟨⟨startId⟩, .T_Literal content⟩
      ([litTok], startId + 1, {})

/-- Post-process to recursively parse $() content -/
partial def expandDollarExpansions (t : Token) (filename : String) (nextId : Nat) (origPositions : Std.HashMap Id (Position × Position)) : (Token × Nat × Std.HashMap Id (Position × Position)) :=
  match t.inner with
  | .T_DollarExpansion children =>
      -- Check if children are just a literal that needs reparsing
      match children with
      | [child] =>
          match child.inner with
          | .T_Literal content =>
              -- This is unparsed content - parse it now
              -- Look up the original position of this T_DollarExpansion to get offset
              let (offsetLine, offsetCol) := match origPositions.get? t.id with
                | some (startPos, _) => (startPos.posLine, startPos.posColumn + 2)  -- +2 for "$("
                | none => (1, 1)  -- Fallback
              let (parsedCmds, newNextId, newPositions) := parseSubshellContent content filename nextId offsetLine offsetCol
              -- Recursively expand any nested $() in the parsed commands
              let (expandedCmds, finalNextId, allPositions) := parsedCmds.foldl (init := ([], newNextId, newPositions))
                fun (acc, nid, pos) cmd =>
                  let (expCmd, newNid, newPos) := expandDollarExpansions cmd filename nid origPositions
                  (acc ++ [expCmd], newNid, pos.fold (init := newPos) fun m k v => m.insert k v)
              (⟨t.id, .T_DollarExpansion expandedCmds⟩, finalNextId, allPositions)
          | _ =>
              -- Already parsed, just recurse into children
              let (expanded, newNextId, positions) := expandChildren children filename nextId origPositions
              (⟨t.id, .T_DollarExpansion expanded⟩, newNextId, positions)
      | _ =>
          -- Multiple children, already parsed, just recurse
          let (expanded, newNextId, positions) := expandChildren children filename nextId origPositions
          (⟨t.id, .T_DollarExpansion expanded⟩, newNextId, positions)
  | .T_DollarBraced braced content =>
      let (expanded, newNextId, positions) := expandDollarExpansions content filename nextId origPositions
      (⟨t.id, .T_DollarBraced braced expanded⟩, newNextId, positions)
  | .T_Script shebang cmds =>
      let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
      (⟨t.id, .T_Script shebang expanded⟩, newNextId, positions)
  | .T_Pipeline seps cmds =>
      let (expandedSeps, nid1, pos1) := expandChildren seps filename nextId origPositions
      let (expandedCmds, nid2, pos2) := expandChildren cmds filename nid1 origPositions
      (⟨t.id, .T_Pipeline expandedSeps expandedCmds⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_Redirecting redirs cmd =>
      let (expandedRedirs, nid1, pos1) := expandChildren redirs filename nextId origPositions
      let (expandedCmd, nid2, pos2) := expandDollarExpansions cmd filename nid1 origPositions
      (⟨t.id, .T_Redirecting expandedRedirs expandedCmd⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_SimpleCommand assigns words =>
      let (expandedAssigns, nid1, pos1) := expandChildren assigns filename nextId origPositions
      let (expandedWords, nid2, pos2) := expandChildren words filename nid1 origPositions
      (⟨t.id, .T_SimpleCommand expandedAssigns expandedWords⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_NormalWord parts =>
      let (expanded, newNextId, positions) := expandChildren parts filename nextId origPositions
      (⟨t.id, .T_NormalWord expanded⟩, newNextId, positions)
  | .T_DoubleQuoted parts =>
      let (expanded, newNextId, positions) := expandChildren parts filename nextId origPositions
      (⟨t.id, .T_DoubleQuoted expanded⟩, newNextId, positions)
  | .T_Assignment mode name indices val =>
      let (expandedVal, newNextId, positions) := expandDollarExpansions val filename nextId origPositions
      (⟨t.id, .T_Assignment mode name indices expandedVal⟩, newNextId, positions)
  | .T_BraceGroup cmds =>
      let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
      (⟨t.id, .T_BraceGroup expanded⟩, newNextId, positions)
  | .T_Subshell cmds =>
      let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
      (⟨t.id, .T_Subshell expanded⟩, newNextId, positions)
  | .T_AndIf t1 t2 =>
      let (exp1, nid1, pos1) := expandDollarExpansions t1 filename nextId origPositions
      let (exp2, nid2, pos2) := expandDollarExpansions t2 filename nid1 origPositions
      (⟨t.id, .T_AndIf exp1 exp2⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_OrIf t1 t2 =>
      let (exp1, nid1, pos1) := expandDollarExpansions t1 filename nextId origPositions
      let (exp2, nid2, pos2) := expandDollarExpansions t2 filename nid1 origPositions
      (⟨t.id, .T_OrIf exp1 exp2⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_Backgrounded inner =>
      let (expanded, newNextId, positions) := expandDollarExpansions inner filename nextId origPositions
      (⟨t.id, .T_Backgrounded expanded⟩, newNextId, positions)
  | .T_Function kw parens name body =>
      let (expanded, newNextId, positions) := expandDollarExpansions body filename nextId origPositions
      (⟨t.id, .T_Function kw parens name expanded⟩, newNextId, positions)
  | .T_Backticked cmds =>
      match cmds with
      | [child] =>
          match child.inner with
          | .T_Literal content =>
              -- This is unparsed content - parse it now (like $()).
              let (offsetLine, offsetCol) := match origPositions.get? t.id with
                | some (startPos, _) => (startPos.posLine, startPos.posColumn + 1)  -- +1 for "`"
                | none => (1, 1)  -- Fallback
              let (parsedCmds, newNextId, newPositions) := parseSubshellContent content filename nextId offsetLine offsetCol
              -- Recursively expand any nested $() in the parsed commands
              let (expandedCmds, finalNextId, allPositions) := parsedCmds.foldl (init := ([], newNextId, newPositions))
                fun (acc, nid, pos) cmd =>
                  let (expCmd, newNid, newPos) := expandDollarExpansions cmd filename nid origPositions
                  (acc ++ [expCmd], newNid, pos.fold (init := newPos) fun m k v => m.insert k v)
              (⟨t.id, .T_Backticked expandedCmds⟩, finalNextId, allPositions)
          | _ =>
              let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
              (⟨t.id, .T_Backticked expanded⟩, newNextId, positions)
      | _ =>
          let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
          (⟨t.id, .T_Backticked expanded⟩, newNextId, positions)
  | .T_IfExpression conditions elseBody =>
      -- Each condition is (condList, bodyList)
      let init : List (List Token × List Token) × Nat × Std.HashMap Id (Position × Position) := ([], nextId, {})
      let (expandedConds, nid1, pos1) := conditions.foldl (init := init)
        fun (acc, nid, pos) (condList, bodyList) =>
          let (expCond, nid', pos') := expandChildren condList filename nid origPositions
          let (expBody, nid'', pos'') := expandChildren bodyList filename nid' origPositions
          let merged := pos.fold (init := pos'') fun m k v => pos'.fold (init := m.insert k v) fun m' k' v' => m'.insert k' v'
          (acc ++ [(expCond, expBody)], nid'', merged)
      let (expandedElse, nid2, pos2) := expandChildren elseBody filename nid1 origPositions
      (⟨t.id, .T_IfExpression expandedConds expandedElse⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_WhileExpression cond body =>
      let (expandedCond, nid1, pos1) := expandChildren cond filename nextId origPositions
      let (expandedBody, nid2, pos2) := expandChildren body filename nid1 origPositions
      (⟨t.id, .T_WhileExpression expandedCond expandedBody⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_ForIn var words body =>
      let (expandedWords, nid1, pos1) := expandChildren words filename nextId origPositions
      let (expandedBody, nid2, pos2) := expandChildren body filename nid1 origPositions
      (⟨t.id, .T_ForIn var expandedWords expandedBody⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | .T_ForArithmetic init cond incr body =>
      let (expInit, nid1, pos1) := expandDollarExpansions init filename nextId origPositions
      let (expCond, nid2, pos2) := expandDollarExpansions cond filename nid1 origPositions
      let (expIncr, nid3, pos3) := expandDollarExpansions incr filename nid2 origPositions
      let (expBody, nid4, pos4) := expandChildren body filename nid3 origPositions
      let allPos := pos1.fold (init := pos4) fun m k v =>
        pos2.fold (init := m.insert k v) fun m' k' v' =>
          pos3.fold (init := m'.insert k' v') fun m'' k'' v'' => m''.insert k'' v''
      (⟨t.id, .T_ForArithmetic expInit expCond expIncr expBody⟩, nid4, allPos)
  | .T_CaseExpression word cases =>
      let (expWord, nid1, pos1) := expandDollarExpansions word filename nextId origPositions
      let caseInit : List (CaseType × List Token × List Token) × Nat × Std.HashMap Id (Position × Position) := ([], nid1, {})
      let (expCases, nid2, pos2) := cases.foldl (init := caseInit)
        fun (acc, nid, pos) (ctype, patterns, body) =>
          let (expPatterns, nid', pos') := expandChildren patterns filename nid origPositions
          let (expBody, nid'', pos'') := expandChildren body filename nid' origPositions
          let merged := pos.fold (init := pos'') fun m k v => pos'.fold (init := m.insert k v) fun m' k' v' => m'.insert k' v'
          (acc ++ [(ctype, expPatterns, expBody)], nid'', merged)
      (⟨t.id, .T_CaseExpression expWord expCases⟩, nid2, pos1.fold (init := pos2) fun m k v => m.insert k v)
  | _ => (t, nextId, {})
where
  expandChildren (children : List Token) (filename : String) (nextId : Nat) (origPos : Std.HashMap Id (Position × Position)) : (List Token × Nat × Std.HashMap Id (Position × Position)) :=
    children.foldl (init := ([], nextId, {})) fun (acc, nid, pos) child =>
      let (expanded, newNid, newPos) := expandDollarExpansions child filename nid origPos
      (acc ++ [expanded], newNid, pos.fold (init := newPos) fun m k v => m.insert k v)

/-- Run the full parser on a script -/
def runFullParser (script : String) (filename : String := "<stdin>") : (Option Token × Std.HashMap Id (Position × Position) × List String) :=
  let it := ShellCheck.Parser.Parsec.PosIterator.create script
  let initState : FullParserState := ShellCheck.Parser.Parsec.mkShellState filename
  match readScriptFull initState it with
  | .success _ (tok, st) =>
      -- Post-process to expand $() content, passing original positions for offset calculation
      let (expanded, _finalId, extraPositions) :=
        expandDollarExpansions tok filename st.nextId st.positions
      -- Merge extra positions (from sub-parsing) into original positions
      let allPositions :=
        extraPositions.fold (init := st.positions) fun m k v => m.insert k v
      (some expanded, allPositions, st.errors)
  | .error it' err =>
      let msg := s!"{filename}:{it'.line}:{it'.column}: {err}"
      (none, {}, msg :: initState.errors)

/-- Check if msg contains a substring (case-insensitive) -/
private def contains (msg sub : String) : Bool :=
  Regex.containsSubstring msg.toLower sub.toLower

set_option maxRecDepth 1024

/-- Infer SC code from error message patterns -/
def inferSCCode (msg : String) : Nat × Severity :=
  -- SC1000: $ not special
  if contains msg "$" && contains msg "not" && contains msg "special" then (1000, .errorC)
  -- Escaping errors (SC1001-SC1006, SC1012-SC1013, SC1117)
  else if contains msg "backslash" && contains msg "regular" then (1001, .infoC)
  else if contains msg "backslash" && contains msg "literal" && !contains msg "comment" then (1001, .infoC)
  else if contains msg "$\\" && contains msg "command substitution" then (1002, .errorC)
  else if contains msg "escape" && contains msg "single quote" then (1003, .errorC)
  else if contains msg "backslash" && contains msg "linefeed" then (1004, .warningC)
  else if contains msg "backslash" && contains msg "newline" then (1004, .warningC)
  else if contains msg "closing paren" && contains msg "arithmetic" then (1005, .errorC)
  else if contains msg "expected" && contains msg "))" then (1005, .errorC)
  else if contains msg "glob" && contains msg "pattern" then (1006, .errorC)
  else if contains msg "\\t" && contains msg "literal" then (1012, .warningC)
  else if contains msg "escaped newline" && contains msg "double quote" then (1013, .warningC)
  else if contains msg "\\n" && contains msg "literal" then (1117, .infoC)
  -- Whitespace errors (SC1007, SC1017-SC1027, SC1035, SC1054-SC1055, SC1068-SC1069, SC1095, SC1099)
  else if contains msg "space after =" then (1007, .errorC)
  else if contains msg "remove space" && contains msg "=" then (1007, .errorC)
  else if contains msg "carriage return" then (1017, .errorC)
  else if contains msg "non-breaking space" || contains msg "nbsp" then (1018, .errorC)
  else if contains msg "space before the ]" || contains msg "space before ]" then (1020, .errorC)
  else if contains msg "can't have a space" && contains msg "]" then (1021, .errorC)
  else if contains msg "don't put spaces before" && contains msg "bracket" then (1022, .errorC)
  else if contains msg "space after" && contains msg "redirection" then (1023, .errorC)
  else if contains msg "space before" && contains msg "here-doc" then (1024, .errorC)
  else if contains msg "single quotes" && contains msg "literal" then (1025, .errorC)
  else if contains msg "space between" && contains msg "operator" then (1027, .errorC)
  else if contains msg "space after" && contains msg "{" then (1054, .errorC)
  else if contains msg "space between" && contains msg "array" && contains msg "index" then (1055, .errorC)
  else if contains msg "spaces around the =" || (contains msg "don't put spaces" && contains msg "=") then (1068, .errorC)
  else if contains msg "space before" && contains msg "[" then (1069, .errorC)
  else if contains msg "space" && contains msg "function" && contains msg "body" then (1095, .errorC)
  else if contains msg "space" && contains msg "}" && contains msg "before" then (1095, .errorC)
  else if contains msg "space before the #" then (1099, .errorC)
  else if contains msg "trailing space" && contains msg "\\" then (1101, .errorC)
  else if contains msg "space before and after" && contains msg "=" then (1108, .errorC)
  else if contains msg "leading space" && contains msg "shebang" then (1114, .errorC)
  else if contains msg "space" && contains msg "#" && contains msg "!" then (1115, .errorC)
  else if contains msg "whitespace" && contains msg "here-doc" then (1118, .errorC)
  else if contains msg "space before the !" then (1129, .errorC)
  else if contains msg "space before the :" then (1130, .errorC)
  -- Quoting errors (SC1011, SC1015-SC1016, SC1078-SC1079, SC1110)
  else if contains msg "apostrophe" && contains msg "terminated" then (1011, .errorC)
  else if contains msg "unicode" && contains msg "double quote" then (1015, .errorC)
  else if contains msg "curly" && contains msg "quote" then (1015, .errorC)
  else if contains msg "unicode" && contains msg "single quote" then (1016, .errorC)
  else if contains msg "close" && contains msg "double quote" then (1078, .errorC)
  else if contains msg "unclosed" && contains msg "quote" then (1078, .errorC)
  else if contains msg "end quote" && contains msg "suspect" then (1079, .warningC)
  else if contains msg "unicode quote" then (1110, .errorC)
  -- Test bracket errors (SC1019, SC1026, SC1028-SC1034, SC1057, SC1080, SC1106, SC1139-SC1140)
  else if contains msg "unary condition" then (1019, .errorC)
  else if contains msg "grouping" && contains msg "[[" then (1026, .errorC)
  else if contains msg "escape" && contains msg "\\(" && contains msg "[" then (1028, .errorC)
  else if contains msg "shouldn't escape" && contains msg "[[" then (1029, .warningC)
  else if contains msg "expected" && contains msg "condition" && contains msg "test" then (1030, .errorC)
  else if contains msg "empty string" && contains msg "-eq" then (1031, .errorC)
  else if contains msg "-z" && contains msg "empty" then (1031, .errorC)
  else if contains msg ">" && contains msg "redirection" && contains msg "comparison" then (1032, .errorC)
  else if contains msg "[[" && contains msg "]" && contains msg "match" then (1033, .errorC)
  else if contains msg "[" && contains msg "]]" && contains msg "match" then (1034, .errorC)
  else if contains msg ">=" && contains msg "greater" then (1057, .infoC)
  else if contains msg "right bracket" && contains msg "matching" then (1080, .errorC)
  else if contains msg "arithmetic" && contains msg "-lt" then (1106, .infoC)
  else if contains msg "-o" && contains msg "||" then (1139, .errorC)
  else if contains msg "after condition" && (contains msg "&&" || contains msg "||") then (1140, .errorC)
  -- Shebang errors (SC1008, SC1071, SC1082, SC1084, SC1104, SC1113, SC1128)
  else if contains msg "bom" || contains msg "byte order mark" then (1082, .errorC)
  else if contains msg "!#" && contains msg "shebang" then (1084, .errorC)
  else if contains msg "not just !" && contains msg "shebang" then (1104, .errorC)
  else if contains msg "not just #" && contains msg "shebang" then (1113, .errorC)
  else if contains msg "shebang" && contains msg "first line" then (1128, .errorC)
  else if contains msg "shebang" && contains msg "unrecognized" then (1008, .warningC)
  else if contains msg "only supports" && (contains msg "sh" || contains msg "bash") then (1071, .errorC)
  -- Control flow errors (SC1009-SC1010, SC1014, SC1045-SC1053, SC1058, SC1060-SC1063, SC1074-SC1076, SC1131)
  else if contains msg "parser error was in" then (1009, .errorC)
  else if contains msg "semicolon" && contains msg "before" && contains msg "done" then (1010, .errorC)
  else if contains msg "if cmd; then" || contains msg "check exit code" then (1014, .errorC)
  else if contains msg "&;" || contains msg "@args" then (1045, .errorC)
  else if contains msg "fi" && contains msg "if" && !contains msg "elif" then (1046, .errorC)
  else if contains msg "couldn't find" && contains msg "fi" then (1046, .errorC)
  else if contains msg "fi" && contains msg "matching" then (1047, .errorC)
  else if contains msg "empty" && contains msg "then" then (1048, .errorC)
  else if contains msg "forget" && contains msg "then" then (1049, .errorC)
  else if contains msg "expected" && contains msg "then" then (1050, .errorC)
  else if contains msg "semicolon" && contains msg "after" && contains msg "then" then (1051, .errorC)
  else if contains msg "semicolon" && contains msg "after" && contains msg "else" then (1053, .errorC)
  else if contains msg "expected" && contains msg "do" then (1058, .errorC)
  else if contains msg "case" && contains msg "in" && contains msg "expected" then (1060, .errorC)
  else if contains msg "case" && contains msg "word" && contains msg "in" then (1060, .errorC)
  else if contains msg "done" && (contains msg "do" || contains msg "loop") then (1061, .errorC)
  else if contains msg "couldn't find" && contains msg "done" then (1061, .errorC)
  else if contains msg "done" && contains msg "matching" then (1062, .errorC)
  else if contains msg "linefeed" && contains msg "before" && contains msg "do" then (1063, .errorC)
  else if contains msg ";;" && contains msg "case" then (1074, .errorC)
  else if contains msg "elif" && contains msg "else if" then (1075, .errorC)
  else if contains msg "trying to do math" || (contains msg "math" && contains msg "$((" ) then (1076, .errorC)
  else if contains msg "missing" && contains msg "'in'" && contains msg "for" then (1079, .errorC)
  else if contains msg "elif" && contains msg "branch" then (1131, .errorC)
  -- Function errors (SC1064-SC1065, SC1085, SC1092-SC1093)
  else if contains msg "{" && contains msg "function" then (1064, .errorC)
  else if contains msg "parameter" && contains msg "$1" then (1065, .errorC)
  else if contains msg "esac" && contains msg "case" then (1064, .errorC)
  else if contains msg "function body" && contains msg "expected" then (1085, .errorC)
  else if contains msg "function name" && contains msg "expected" then (1092, .errorC)
  else if contains msg "()" && contains msg "function" && contains msg "expected" then (1093, .errorC)
  else if contains msg "{}" && contains msg "function" && contains msg "expected" then (1093, .errorC)
  -- Variable errors (SC1036-SC1037, SC1053, SC1066-SC1067, SC1086-SC1087, SC1096-SC1097, SC1103, SC1116, SC1134)
  else if contains msg "(" && contains msg "invalid" then (1036, .errorC)
  else if contains msg "brace" && contains msg "positional" then (1037, .errorC)
  else if contains msg "keyword" && contains msg "variable" then (1053, .errorC)
  else if contains msg "$" && contains msg "left side" then (1066, .errorC)
  else if contains msg "indirection" && contains msg "array" then (1067, .errorC)
  else if contains msg "$" && contains msg "iterator" && contains msg "for" then (1086, .errorC)
  else if contains msg "brace" && contains msg "array" then (1087, .errorC)
  else if contains msg "comment" && contains msg "allowed" && contains msg "bash" then (1096, .infoC)
  else if contains msg "==" && contains msg "assignment" then (1097, .errorC)
  else if contains msg "posix" && contains msg "allow" then (1103, .infoC)
  else if contains msg "missing $" && contains msg "((" then (1116, .errorC)
  else if contains msg "local" && contains msg "typeset" && contains msg "declare" then (1134, .errorC)
  -- Here-doc errors (SC1038-SC1044, SC1119-SC1122, SC1137-SC1138)
  else if contains msg "< <(" || contains msg "space sensitive" then (1038, .errorC)
  else if contains msg "indent" && contains msg "end token" then (1039, .errorC)
  else if contains msg "<<-" && contains msg "tab" then (1040, .errorC)
  else if contains msg "eof" && contains msg "separate line" then (1041, .errorC)
  else if contains msg "close match" && contains msg "eof" then (1042, .warningC)
  else if contains msg "single quotes" && contains msg "here-doc" && contains msg "terminator" then (1043, .errorC)
  else if contains msg "end token" && contains msg "here" then (1044, .errorC)
  else if contains msg "couldn't find" && contains msg "here" then (1044, .errorC)
  else if contains msg "linefeed" && contains msg "end token" && contains msg ")" then (1119, .errorC)
  else if contains msg "comment" && contains msg "here-doc" then (1120, .errorC)
  else if contains msg "terminator" && contains msg "<<" then (1121, .errorC)
  else if contains msg "after end token" then (1122, .errorC)
  else if contains msg "here-doc" && contains msg "unquoted" && contains msg "match" then (1137, .errorC)
  else if contains msg "invalid" && contains msg "here-doc" && contains msg "syntax" then (1138, .errorC)
  -- Sourcing errors (SC1090-SC1091, SC1094)
  else if contains msg "non-constant" && contains msg "source" then (1090, .warningC)
  else if contains msg "not following" then (1091, .infoC)
  else if contains msg "sourced file" && contains msg "failed" then (1094, .warningC)
  -- Syntax errors (SC1056, SC1059, SC1070, SC1077, SC1081, SC1083, SC1088-SC1089, SC1098, SC1132-SC1133, SC1136, SC1141-SC1143)
  else if contains msg "expected" && contains msg "}" then (1056, .errorC)
  else if contains msg "extglob" || contains msg "extended glob" then (1059, .warningC)
  else if contains msg "parsing stopped" && contains msg "parentheses" then (1088, .errorC)
  else if contains msg "parsing stopped" && contains msg "keyword" then (1089, .errorC)
  else if contains msg "parsing stopped" then (1070, .errorC)
  else if contains msg "tick" && contains msg "slant" then (1077, .errorC)
  else if contains msg "case sensitive" then (1081, .errorC)
  else if (contains msg "{" || contains msg "}") && contains msg "literal" then (1083, .errorC)
  else if contains msg "eval" && (contains msg "escape" || contains msg "quote") then (1098, .errorC)
  else if contains msg "&" && contains msg "terminate" then (1132, .errorC)
  else if contains msg "start of line" && (contains msg "|" || contains msg "&&") then (1133, .errorC)
  else if contains msg "after" && contains msg "]" && contains msg "semicolon" then (1136, .errorC)
  else if contains msg "after compound" && contains msg "redirection" then (1141, .errorC)
  else if contains msg "process substitution" && contains msg "redirect" then (1142, .errorC)
  else if contains msg "backslash" && contains msg "comment" then (1143, .infoC)
  -- Unicode errors (SC1100, SC1109)
  else if contains msg "unicode dash" then (1100, .errorC)
  else if contains msg "html entity" then (1109, .errorC)
  else if contains msg "unicode" then (1015, .errorC)
  -- Disambiguation errors (SC1102, SC1105)
  else if contains msg "disambiguate" && contains msg "$((" then (1102, .errorC)
  else if contains msg "disambiguate" && contains msg "((" then (1105, .errorC)
  -- Directive errors (SC1107, SC1123-SC1127, SC1135)
  else if contains msg "directive" && contains msg "unknown" then (1107, .warningC)
  else if contains msg "directive" && contains msg "compound" then (1123, .errorC)
  else if contains msg "directive" && contains msg "branch" then (1124, .errorC)
  else if contains msg "key=value" && contains msg "directive" then (1125, .errorC)
  else if contains msg "directive" && contains msg "before" then (1126, .errorC)
  else if contains msg "intended" && contains msg "comment" then (1127, .errorC)
  else if contains msg "escape" && contains msg "$" && contains msg "literal" then (1135, .infoC)
  -- Generic fallbacks
  else if contains msg "space" then (1035, .errorC)
  else if contains msg "unexpected" then (1072, .errorC)
  else if contains msg "couldn't parse" || contains msg "couldn't find" then (1073, .errorC)
  else if contains msg "expected" || contains msg "invalid" || contains msg "missing" then (1072, .errorC)
  -- Default
  else (0, .errorC)

/-- Enhanced parseScript using full parser -/
def parseScriptFull [Monad m] (_sys : SystemInterface m) (spec : ParseSpec) : m ParseResult := do
  let (root, positions, errors) := runFullParser spec.psScript spec.psFilename
  let parseErrors : List PositionedComment :=
    errors.map fun msg =>
      let mkAt (file : String) (line col : Nat) (message : String) : PositionedComment :=
        let pos : Position := { posFile := file, posLine := line, posColumn := col }
        let (code, severity) := inferSCCode message
        { pcStartPos := pos
          pcEndPos := pos
          pcComment := { cSeverity := severity, cCode := code, cMessage := message }
          pcFix := none }
      match msg.splitOn ":" with
      | file :: lineStr :: colStr :: rest =>
          match lineStr.trim.toNat?, colStr.trim.toNat? with
          | some line, some col =>
              let message := (String.intercalate ":" rest).trim
              mkAt file line col message
          | _, _ =>
              mkAt spec.psFilename 1 1 msg
      | _ =>
          mkAt spec.psFilename 1 1 msg
  pure {
    prComments := parseErrors
    prTokenPositions := positions
    prRoot := root
  }

end ShellCheck.Parser
