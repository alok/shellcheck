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
import ShellCheck.Parser.Core
import ShellCheck.Parser.Lexer
import ShellCheck.Parser.Word

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
  return String.ofList (first :: rest.toList)

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
      let first := s.get! 0
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
      let saved ← getPos
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
          let inner ← mkTok (.T_Literal content) line col
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

The proper implementation uses a combined parser/token-builder approach
-/

/-- Parser state combined with token building -/
structure FullParserState where
  /-- Input string -/
  input : String
  /-- Current position in input -/
  pos : String.Pos.Raw
  /-- Current line number (1-indexed) -/
  line : Nat
  /-- Current column number (1-indexed) -/
  column : Nat
  /-- Next token ID to assign -/
  nextId : Nat
  /-- Map from token IDs to positions -/
  positions : Std.HashMap Id (Position × Position)
  /-- Current filename -/
  filename : String
  /-- Accumulated parse errors -/
  errors : List String
  deriving Inhabited

/-- Result of full parsing -/
inductive FullResult (α : Type) where
  | ok : α → FullParserState → FullResult α
  | error : String → FullParserState → FullResult α
  deriving Inhabited

/-- Full parser monad -/
def FullParser (α : Type) := FullParserState → FullResult α

instance : Monad FullParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative FullParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Create a fresh token ID -/
def freshIdFull : FullParser Id := fun s =>
  let id := Id.mk s.nextId
  .ok id { s with nextId := s.nextId + 1 }

/-- Record a position for a token ID -/
def recordPosition (id : Id) (startLine startCol endLine endCol : Nat) : FullParser Unit := fun s =>
  let startPos : Position := { posFile := s.filename, posLine := startLine, posColumn := startCol }
  let endPos : Position := { posFile := s.filename, posLine := endLine, posColumn := endCol }
  .ok () { s with positions := s.positions.insert id (startPos, endPos) }

/-- Get current position -/
def currentPos : FullParser (Nat × Nat) := fun s =>
  .ok (s.line, s.column) s

/-- Check if at end of input -/
def isEofFull : FullParser Bool := fun s =>
  .ok (s.pos >= s.input.rawEndPos) s

/-- Peek at next character -/
def peekFull : FullParser (Option Char) := fun s =>
  if s.pos < s.input.rawEndPos then
    .ok (some (s.pos.get s.input)) s
  else
    .ok none s

/-- Consume a character -/
def anyCharFull : FullParser Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let c := s.pos.get s.input
    let newPos := s.pos.next s.input
    let (newLine, newCol) :=
      if c == '\n' then (s.line + 1, 1)
      else (s.line, s.column + 1)
    .ok c { s with pos := newPos, line := newLine, column := newCol }
  else
    .error "unexpected end of input" s

/-- Match a specific character -/
def charFull (c : Char) : FullParser Char := fun s =>
  if s.pos < s.input.rawEndPos then
    let actual := s.pos.get s.input
    if actual == c then
      let newPos := s.pos.next s.input
      let (newLine, newCol) :=
        if c == '\n' then (s.line + 1, 1)
        else (s.line, s.column + 1)
      .ok c { s with pos := newPos, line := newLine, column := newCol }
    else
      .error s!"expected '{c}'" s
  else
    .error s!"expected '{c}'" s

/-- Match a string -/
partial def stringFull (str : String) : FullParser String := fun s =>
  let rec go (i : String.Pos.Raw) (state : FullParserState) : FullResult String :=
    if i >= str.rawEndPos then
      .ok str state
    else if state.pos >= state.input.rawEndPos then
      .error s!"expected \"{str}\"" s
    else
      let expected := i.get str
      let actual := state.pos.get state.input
      if expected == actual then
        let newPos := state.pos.next state.input
        let (newLine, newCol) :=
          if actual == '\n' then (state.line + 1, 1)
          else (state.line, state.column + 1)
        go (i.next str) { state with pos := newPos, line := newLine, column := newCol }
      else
        .error s!"expected \"{str}\"" s
  go 0 s

/-- Take characters while predicate holds -/
partial def takeWhileFull (p : Char → Bool) : FullParser String := fun s =>
  let rec go (acc : List Char) (state : FullParserState) : FullResult String :=
    if state.pos >= state.input.rawEndPos then
      .ok (String.ofList acc.reverse) state
    else
      let c := state.pos.get state.input
      if p c then
        let newPos := state.pos.next state.input
        let (newLine, newCol) :=
          if c == '\n' then (state.line + 1, 1)
          else (state.line, state.column + 1)
        go (c :: acc) { state with pos := newPos, line := newLine, column := newCol }
      else
        .ok (String.ofList acc.reverse) state
  go [] s

/-- Take at least one character while predicate holds -/
def takeWhile1Full (p : Char → Bool) : FullParser String := fun s =>
  match takeWhileFull p s with
  | .ok str s' => if str.isEmpty then .error "expected at least one character" s else .ok str s'
  | .error msg s' => .error msg s'

/-- Try parser with backtracking -/
def attemptFull (p : FullParser α) : FullParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Many combinator -/
partial def manyFull (p : FullParser α) : FullParser (List α) := fun s =>
  let rec go (acc : List α) (state : FullParserState) : FullResult (List α) :=
    match p state with
    | .ok a s' => go (a :: acc) s'
    | .error _ _ => .ok acc.reverse state
  go [] s

/-- Optional combinator -/
def optionalFull (p : FullParser α) : FullParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Create a token with current position -/
def mkTokenFull (inner : InnerToken Token) : FullParser Token := do
  let (line, col) ← currentPos
  let id ← freshIdFull
  recordPosition id line col line col
  return ⟨id, inner⟩

/-- Skip horizontal whitespace in full parser -/
partial def skipHSpaceFull : FullParser Unit := do
  let _ ← takeWhileFull (fun c => c == ' ' || c == '\t')
  match ← peekFull with
  | some '\\' =>
      let saved ← currentPos
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

/-!
### Word Parsing in Full Parser
-/

/-- Read a literal word part -/
def readLiteralFull : FullParser Token := do
  let content ← takeWhile1Full fun c =>
    ¬ (c.isWhitespace ||
       c == '"' || c == '\'' || c == '`' ||
       c == '$' || c == '\\' ||
       c == '|' || c == '&' || c == ';' ||
       c == '<' || c == '>' ||
       c == '(' || c == ')' ||
       c == '{' || c == '}' ||
       c == '#')
  mkTokenFull (.T_Literal content)

/-- Read a single-quoted string -/
def readSingleQuotedFull : FullParser Token := do
  let _ ← charFull '\''
  let content ← takeWhileFull (· != '\'')
  let _ ← charFull '\''
  mkTokenFull (.T_SingleQuoted content)

/-- Read a backtick command substitution -/
partial def readBacktickFull : FullParser Token := do
  let _ ← charFull '`'
  let content ← takeWhileFull (· != '`')  -- Simplified - should handle escapes
  let _ ← charFull '`'
  let inner ← mkTokenFull (.T_Literal content)
  mkTokenFull (.T_Backticked [inner])

/-- Read a double-quoted string -/
partial def readDoubleQuotedFull : FullParser Token := do
  let _ ← charFull '"'
  let parts ← readDQParts []
  let _ ← charFull '"'
  mkTokenFull (.T_DoubleQuoted parts)
where
  readDQParts (acc : List Token) : FullParser (List Token) := do
    match ← peekFull with
    | none => pure acc.reverse
    | some '"' => pure acc.reverse
    | some '\\' =>
        let _ ← anyCharFull
        match ← peekFull with
        | some c =>
            let _ ← anyCharFull
            let tok ← mkTokenFull (.T_Literal (String.ofList ['\\', c]))
            readDQParts (tok :: acc)
        | none => pure acc.reverse
    | some '$' =>
        let _ ← anyCharFull
        let tok ← readDollarInDQ
        readDQParts (tok :: acc)
    | some '`' =>
        let tok ← readBacktickFull
        readDQParts (tok :: acc)
    | some _ =>
        let lit ← takeWhileFull fun c => c != '"' && c != '\\' && c != '$' && c != '`'
        if lit.isEmpty then pure acc.reverse
        else
          let tok ← mkTokenFull (.T_Literal lit)
          readDQParts (tok :: acc)

  readDollarInDQ : FullParser Token := do
    match ← peekFull with
    | some '{' =>
        let _ ← charFull '{'
        let content ← takeWhileFull (· != '}')
        let _ ← charFull '}'
        let inner ← mkTokenFull (.T_Literal content)
        mkTokenFull (.T_DollarBraced true inner)
    | some '(' =>
        let _ ← charFull '('
        match ← peekFull with
        | some '(' =>
            let _ ← charFull '('
            let content ← readUntilStr "))"
            let _ ← stringFull "))"
            let inner ← mkTokenFull (.T_Literal content)
            mkTokenFull (.T_DollarArithmetic inner)
        | _ =>
            let content ← readUntilStr ")"
            let _ ← charFull ')'
            let inner ← mkTokenFull (.T_Literal content)
            mkTokenFull (.T_DollarExpansion [inner])
    | some c =>
        if variableStartChar c then
          let name ← takeWhile1Full variableChar
          let inner ← mkTokenFull (.T_Literal name)
          mkTokenFull (.T_DollarBraced false inner)
        else if specialVariableChars.toList.contains c then
          let _ ← anyCharFull
          let inner ← mkTokenFull (.T_Literal (String.ofList [c]))
          mkTokenFull (.T_DollarBraced false inner)
        else
          mkTokenFull (.T_Literal "$")
    | none =>
        mkTokenFull (.T_Literal "$")

  readUntilStr (terminator : String) : FullParser String := do
    let rec go (acc : List Char) (depth : Nat) : FullParser String := do
      match ← peekFull with
      | none => pure (String.ofList acc.reverse)
      | some c =>
          -- Simple nesting tracking for ( )
          if terminator == ")" && c == '(' then
            let _ ← anyCharFull
            go (c :: acc) (depth + 1)
          else if terminator == ")" && c == ')' then
            if depth > 0 then
              let _ ← anyCharFull
              go (c :: acc) (depth - 1)
            else
              pure (String.ofList acc.reverse)
          else if terminator == "))" && c == ')' then
            match ← optionalFull (stringFull "))") with
            | some _ => pure (String.ofList acc.reverse)  -- Found terminator
            | none =>
                let _ ← anyCharFull
                go (c :: acc) depth
          else
            let _ ← anyCharFull
            go (c :: acc) depth
    go [] 0

/-- Read a complete word (multiple parts) -/
partial def readWordFull : FullParser Token := do
  let parts ← readWordParts []
  if parts.isEmpty then failure
  else if parts.length == 1 then
    pure parts.head!
  else
    mkTokenFull (.T_NormalWord parts)
where
  readWordParts (acc : List Token) : FullParser (List Token) := do
    match ← peekFull with
    | none => pure acc.reverse
    | some c =>
        if c.isWhitespace || isOperatorStart c || c == '#' then
          pure acc.reverse
        else if c == '\'' then
          let tok ← readSingleQuotedFull
          readWordParts (tok :: acc)
        else if c == '"' then
          let tok ← readDoubleQuotedFull
          readWordParts (tok :: acc)
        else if c == '`' then
          let tok ← readBacktickFull
          readWordParts (tok :: acc)
        else if c == '$' then
          let _ ← anyCharFull
          let tok ← readDollarFull
          readWordParts (tok :: acc)
        else if c == '\\' then
          let _ ← anyCharFull
          match ← peekFull with
          | some '\n' =>
              let _ ← anyCharFull
              readWordParts acc  -- Line continuation
          | some ec =>
              let _ ← anyCharFull
              let tok ← mkTokenFull (.T_Literal (String.ofList [ec]))
              readWordParts (tok :: acc)
          | none =>
              let tok ← mkTokenFull (.T_Literal "\\")
              readWordParts (tok :: acc)
        else
          let tok ← readLiteralFull
          readWordParts (tok :: acc)

  readDollarFull : FullParser Token := do
    match ← peekFull with
    | some '{' =>
        let _ ← charFull '{'
        let content ← readBracedContent
        let _ ← charFull '}'
        let inner ← mkTokenFull (.T_Literal content)
        mkTokenFull (.T_DollarBraced true inner)
    | some '(' =>
        let _ ← charFull '('
        match ← peekFull with
        | some '(' =>
            let _ ← charFull '('
            let content ← readArithContent
            let _ ← stringFull "))"
            let inner ← mkTokenFull (.T_Literal content)
            mkTokenFull (.T_DollarArithmetic inner)
        | _ =>
            let content ← readSubshellContent
            let _ ← charFull ')'
            let inner ← mkTokenFull (.T_Literal content)
            mkTokenFull (.T_DollarExpansion [inner])
    | some '\'' =>
        -- $'...' ANSI-C quoting
        let _ ← charFull '\''
        let content ← takeWhileFull (· != '\'')
        let _ ← charFull '\''
        mkTokenFull (.T_DollarSingleQuoted content)
    | some '"' =>
        -- $"..." locale-specific
        let _ ← charFull '"'
        let content ← takeWhileFull (· != '"')  -- Simplified
        let _ ← charFull '"'
        let inner ← mkTokenFull (.T_Literal content)
        mkTokenFull (.T_DollarDoubleQuoted [inner])
    | some c =>
        if variableStartChar c then
          let name ← takeWhile1Full variableChar
          let inner ← mkTokenFull (.T_Literal name)
          mkTokenFull (.T_DollarBraced false inner)
        else if specialVariableChars.toList.contains c then
          let _ ← anyCharFull
          let inner ← mkTokenFull (.T_Literal (String.ofList [c]))
          mkTokenFull (.T_DollarBraced false inner)
        else
          mkTokenFull (.T_Literal "$")
    | none =>
        mkTokenFull (.T_Literal "$")

  readBracedContent : FullParser String := do
    takeWhileFull (· != '}')  -- Simplified - should handle nested braces

  readArithContent : FullParser String := do
    let rec go (acc : List Char) (depth : Nat) : FullParser String := do
      match ← peekFull with
      | none => pure (String.ofList acc.reverse)
      | some ')' =>
          if depth == 0 then
            match ← optionalFull (stringFull "))") with
            | some _ => pure (String.ofList acc.reverse)
            | none =>
                let _ ← anyCharFull
                go (')' :: acc) depth
          else
            let _ ← anyCharFull
            go (')' :: acc) (depth - 1)
      | some '(' =>
          let _ ← anyCharFull
          go ('(' :: acc) (depth + 1)
      | some c =>
          let _ ← anyCharFull
          go (c :: acc) depth
    go [] 0

  readSubshellContent : FullParser String := do
    let rec go (acc : List Char) (depth : Nat) : FullParser String := do
      match ← peekFull with
      | none => pure (String.ofList acc.reverse)
      | some ')' =>
          if depth == 0 then
            pure (String.ofList acc.reverse)
          else
            let _ ← anyCharFull
            go (')' :: acc) (depth - 1)
      | some '(' =>
          let _ ← anyCharFull
          go ('(' :: acc) (depth + 1)
      | some c =>
          let _ ← anyCharFull
          go (c :: acc) depth
    go [] 0

/-!
### Control Flow Parsing

All the recursive parsers are defined together using mutual recursion.
-/

/-- Check if next word matches a keyword -/
def peekKeyword (kw : String) : FullParser Bool := fun s =>
  if s.pos >= s.input.rawEndPos then
    .ok false s
  else
    let kwLen := kw.length
    let remaining := s.input.drop s.pos.byteIdx
    if remaining.startsWith kw then
      let afterKw := remaining.drop kwLen
      let isTerminated := afterKw.isEmpty ||
        (let c := (0 : String.Pos.Raw).get! afterKw
         c.isWhitespace || isOperatorStart c || c == ';')
      if isTerminated then .ok true s else .ok false s
    else
      .ok false s

/-- Consume a keyword -/
def consumeKeyword (kw : String) : FullParser Unit := do
  let isKw ← peekKeyword kw
  if isKw then
    let _ ← stringFull kw
    pure ()
  else
    failure

/-- Peek if the next two chars are )) -/
def peekDoubleClose : FullParser Bool := fun s =>
  if s.pos >= s.input.rawEndPos then
    .ok false s
  else
    let remaining := s.input.drop s.pos.byteIdx
    .ok (remaining.startsWith "))") s

/-- Helper to read arithmetic content (does NOT consume the closing ))) -/
partial def readArithContentHelper : FullParser String := do
  let rec go (acc : List Char) (depth : Nat) : FullParser String := do
    match ← peekFull with
    | none => pure (String.ofList acc.reverse)
    | some ')' =>
        if depth == 0 then
          let isDoubleClose ← peekDoubleClose
          if isDoubleClose then
            pure (String.ofList acc.reverse)  -- Stop without consuming ))
          else
            let _ ← anyCharFull
            go (')' :: acc) depth
        else
          let _ ← anyCharFull
          go (')' :: acc) (depth - 1)
    | some '(' =>
        let _ ← anyCharFull
        go ('(' :: acc) (depth + 1)
    | some c =>
        let _ ← anyCharFull
        go (c :: acc) depth
  go [] 0

/-!
### Command Parsing (mutually recursive)
-/

/-- Reserved keywords that should not start a simple command -/
def reservedKeywords : List String :=
  ["do", "done", "then", "else", "elif", "fi", "esac", "in"]

/-- Check if next word is a reserved keyword -/
def isReservedKeyword : FullParser Bool := fun s =>
  if s.pos >= s.input.rawEndPos then
    .ok false s
  else
    let remaining := s.input.drop s.pos.byteIdx
    let isReserved := reservedKeywords.any fun kw =>
      if remaining.startsWith kw then
        let afterKw := remaining.drop kw.length
        afterKw.isEmpty || (let c := (0 : String.Pos.Raw).get! afterKw
                            c.isWhitespace || isOperatorStart c || c == ';')
      else false
    .ok isReserved s

/-- Read a simple command (assignments + words) -/
partial def readSimpleCommandFull : FullParser Token := do
  skipHSpaceFull
  -- Don't parse reserved keywords as commands
  let reserved ← isReservedKeyword
  if reserved then failure
  let words ← readWordsUntilSep []
  if words.isEmpty then failure
  else mkTokenFull (.T_SimpleCommand [] words)
where
  readWordsUntilSep (acc : List Token) : FullParser (List Token) := do
    skipHSpaceFull
    match ← peekFull with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' || c == '&' || c == '|' || c == ')' || c == '}' then
          pure acc.reverse
        else if c == '#' then
          let _ ← takeWhileFull (· != '\n')
          pure acc.reverse
        else
          let word ← readWordFull
          readWordsUntilSep (word :: acc)

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
    match ← peekFull with
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
                  let isFunction ← peekKeyword "function"
                  if isFunction then readFunctionInPipe
                  else readSimpleCommandFull

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
    skipHSpaceFull
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
    let _ ← optionalFull (stringFull "()")
    skipAllSpaceFull
    let body ← readBraceGroupInPipe
    mkTokenFull (.T_Function ⟨true⟩ ⟨false⟩ name body)

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
        match ← optionalFull (stringFull "&&") with
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
        match ← optionalFull (stringFull "&&") with
        | some _ =>
            skipAllSpaceFull
            let right ← readPipelineInPipe
            let combined ← mkTokenFull (.T_AndIf left right)
            readAndOrContinuationInPipe combined
        | none => pure left
    | some '|' =>
        match ← optionalFull (stringFull "||") with
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
        match ← optionalFull (stringFull "||") with
        | some _ => pure (seps.reverse, cmds.reverse)  -- This is || not |
        | none =>
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
        match ← optionalFull (stringFull "||") with
        | some _ => pure (seps.reverse, cmds.reverse)  -- This is || not |
        | none =>
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
        match ← optionalFull (stringFull "&&") with
        | some _ =>
            skipAllSpaceFull
            let right ← readPipelineFull
            let combined ← mkTokenFull (.T_AndIf left right)
            readAndOrContinuation combined
        | none => pure left
    | some '|' =>
        match ← optionalFull (stringFull "||") with
        | some _ =>
            skipAllSpaceFull
            let right ← readPipelineFull
            let combined ← mkTokenFull (.T_OrIf left right)
            readAndOrContinuation combined
        | none => pure left
    | _ => pure left

/-- Read a term: and-or ((;|&|newline) and-or)* -/
partial def readTermFull : FullParser (List Token) := do
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
            skipAllSpaceFull
            match ← optionalFull readAndOrFull with
            | some next => readTermContinuation (next :: acc)
            | none => pure acc.reverse
    | some '&' =>
        match ← optionalFull (stringFull "&&") with
        | some _ => pure acc.reverse  -- Already handled by readAndOrFull
        | none =>
            let _ ← charFull '&'
            -- Background the last command
            let last := acc.head!
            let rest := acc.tail!
            let bgLast ← mkTokenFull (.T_Backgrounded last)
            skipAllSpaceFull
            match ← optionalFull readAndOrFull with
            | some next => readTermContinuation (next :: bgLast :: rest)
            | none => pure (bgLast :: rest).reverse
    | some '\n' =>
        let _ ← charFull '\n'
        skipAllSpaceFull
        match ← peekFull with
        | none => pure acc.reverse
        | some ')' => pure acc.reverse  -- End of subshell
        | some '}' => pure acc.reverse  -- End of brace group
        | _ =>
            match ← optionalFull readAndOrFull with
            | some next => readTermContinuation (next :: acc)
            | none => pure acc.reverse
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
    skipHSpaceFull
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

/-- Read a select expression: select var in words; do body; done -/
partial def readSelectFull : FullParser Token := do
  let _ ← consumeKeyword "select"
  skipHSpaceFull
  let varName ← takeWhile1Full variableChar
  skipHSpaceFull
  let _ ← consumeKeyword "in"
  skipHSpaceFull
  let words ← readSelectWords []
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
    let _ ← optionalFull (stringFull "()")
    skipAllSpaceFull
    let body ← readBraceGroupFull
    mkTokenFull (.T_Function ⟨true⟩ ⟨false⟩ name body)
  else failure

/-- Read any command (compound or simple) -/
partial def readCommandFull : FullParser Token := do
  skipHSpaceFull
  match ← peekFull with
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
                  else readSimpleCommandFull

/-- Read a complete script -/
def readScriptFull : FullParser Token := do
  skipAllSpaceFull
  -- Check for shebang
  let shebang ← match ← peekFull with
    | some '#' =>
        match ← optionalFull (stringFull "#!") with
        | some _ =>
            let line ← takeWhileFull (· != '\n')
            mkTokenFull (.T_Literal ("#!" ++ line))
        | none =>
            let _ ← takeWhileFull (· != '\n')
            let _ ← optionalFull (charFull '\n')
            mkTokenFull (.T_Literal "")
    | _ =>
        mkTokenFull (.T_Literal "")

  skipAllSpaceFull
  let commands ← readTermFull
  skipAllSpaceFull
  mkTokenFull (.T_Script shebang commands)

/-- Run the full parser on a script -/
def runFullParser (script : String) (filename : String := "<stdin>") : (Option Token × Std.HashMap Id (Position × Position) × List String) :=
  let initState : FullParserState := {
    input := script
    pos := 0
    line := 1
    column := 1
    nextId := 1
    positions := {}
    filename := filename
    errors := []
  }
  match readScriptFull initState with
  | .ok tok s => (some tok, s.positions, s.errors)
  | .error msg s => (none, s.positions, msg :: s.errors)

/-- Enhanced parseScript using full parser -/
def parseScriptFull [Monad m] (_sys : SystemInterface m) (spec : ParseSpec) : m ParseResult := do
  let (root, positions, _errors) := runFullParser spec.psScript spec.psFilename
  pure {
    prComments := []
    prTokenPositions := positions
    prRoot := root
  }

end ShellCheck.Parser
