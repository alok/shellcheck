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
import ShellCheck.Parser.Lexer
import ShellCheck.Parser.Word
import ShellCheck.Parser.Arithmetic
import ShellCheck.Parser.Condition
import ShellCheck.Parser.Parsec
import ShellCheck.Parser.Diagnostics
import ShellCheck.Checks.ParserErrors

namespace ShellCheck.Parser

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Parser.Types
open ShellCheck.Parser.Lexer
open ShellCheck.Parser.Word
open ShellCheck.Parser.Condition

-- Re-export parser types
export ShellCheck.Parser.Types (
  SourcePos ParseNote Context HereDocContext
  UserState SystemState Environment
  initialUserState initialSystemState
)

/-!
### Parser with Token Generation

This section now uses the Parsec-based `Parser` directly from
`ShellCheck.Parser.Parsec`. The legacy `FullParser` layer has been removed.
-/

section Parser

open ShellCheck.Parser.Parsec

def trimAsciiString (s : String) : String :=
  s.trimAscii.toString

/-- Parse a token and then skip trailing whitespace/comments. -/
def lexemeAll (p : Parser α) : Parser α :=
  ShellCheck.Parser.Parsec.lexeme skipAllSpace p

/-- Parse a token and then skip trailing horizontal whitespace/comments. -/
def lexemeHSpace (p : Parser α) : Parser α :=
  ShellCheck.Parser.Parsec.lexeme skipHSpace p

/-- Consume an optional semicolon and then skip whitespace/comments. -/
def optionalSemicolon : Parser Unit := do
  let _ ← ShellCheck.Parser.Parsec.optional (pchar ';')
  skipAllSpace

/-- Parse a shellcheck directive from comment text.
    Returns annotations for "# shellcheck disable=SC2001,SC2046" etc. -/
def parseShellCheckDirective (comment : String) : List Annotation :=
  let trimmed := trimAsciiString comment
  -- Check if it starts with "shellcheck "
  if !trimmed.startsWith "shellcheck " then []
  else
    let rest := trimAsciiString (trimmed.drop 11).toString  -- drop "shellcheck "
    -- Parse key=value pairs
    parseDirectives (rest.splitOn " ")
where
  parseDirectives : List String → List Annotation
    | [] => []
    | part :: rest =>
        let annotations := if part.startsWith "disable=" then
          -- Parse comma-separated SC codes
          let codes := (part.drop 8).toString.splitOn ","  -- drop "disable="
          codes.filterMap parseCode
        else if part.startsWith "ignore=" then
          let codes := (part.drop 7).toString.splitOn ","  -- drop "ignore="
          codes.filterMap parseCode
        else if part.startsWith "enable=" then
          -- For now just track that something is enabled
          let names := (part.drop 7).toString.splitOn ","
          names.map Annotation.enableComment
        else if part.startsWith "source=" then
          [Annotation.sourceOverride (part.drop 7).toString]
        else if part.startsWith "shell=" then
          [Annotation.shellOverride (part.drop 6).toString]
        else if part.startsWith "source-path=" then
          [Annotation.sourcePath (part.drop 12).toString]
        else if part.startsWith "external-sources=" then
          let val := (part.drop 17).toString
          [Annotation.externalSources (val == "true")]
        else
          []
        annotations ++ parseDirectives rest

  parseCode (s : String) : Option Annotation :=
    -- Parse SCnnnn format
    let stripped := if s.startsWith "SC" then (s.drop 2).toString else s
    match stripped.toNat? with
    | some code => some (Annotation.disableComment (Int.ofNat code) (Int.ofNat code + 1))
    | none => none

/-- Skip whitespace and comments, collecting shellcheck annotations -/
partial def skipAllSpaceCollectAnnotations : Parser (List Annotation) := do
  let _ ← takeWhile (fun c => c.isWhitespace)
  match ← peek? with
  | some '#' =>
      let _ ← pchar '#'
      let commentText ← takeWhile (· != '\n')
      let annots := parseShellCheckDirective commentText
      let moreAnnots ← skipAllSpaceCollectAnnotations
      pure (annots ++ moreAnnots)
  | some '\\' =>
      match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "\\\n")) with
      | some _ => skipAllSpaceCollectAnnotations
      | none => pure []
  | _ => pure []

/-!
### Word Parsing

The word-level parsers (`readWord`, `readDoubleQuoted`, …) live in
`ShellCheck.Parser.Word`.
-/

/-!
### Command Parsing (mutually recursive)
-/

/-- Read an unparsed array index `[ ... ]`.

We keep the raw content as a string because array indices are interpreted
differently for associative arrays vs indexed arrays, and because reparsing them
(with proper tokenization) is a separate post-pass in the upstream
implementation. -/
partial def readArrayIndex : Parser Token := do
  let (startLine, startCol) ← getPos
  let _ ← pchar '['
  let (contentLine, contentCol) ← getPos
  let st ← ShellCheck.Parser.Parsec.getState
  let pos : ShellCheck.AST.SourcePos :=
    { sourceName := st.filename, sourceLine := contentLine, sourceColumn := contentCol }
  let content ← readIndexContent [] 0 false false false false
  let _ ← pchar ']'
  mkTokenAt (.T_UnparsedIndex pos content) startLine startCol
where
  /-- Read the payload inside an array index, stopping at the matching `]`.

  This is intentionally a string-level reader (not a full word parser) so it
  can represent nested brackets like `x[y[z=1]]=1` without prematurely stopping
  at the inner `]`. -/
  readIndexContent (acc : List Char) (depth : Nat)
      (inSingle inDouble inBacktick escaped : Bool) : Parser String := do
    match ← peek? with
    | none => pure (String.ofList acc.reverse)
    | some c =>
        if escaped then
          let _ ← anyChar
          readIndexContent (c :: acc) depth inSingle inDouble inBacktick false
        else if inSingle then
          let _ ← anyChar
          if c == '\'' then
            readIndexContent (c :: acc) depth false inDouble inBacktick false
          else
            readIndexContent (c :: acc) depth true inDouble inBacktick false
        else if inDouble then
          if c == '\\' then
            let _ ← anyChar
            readIndexContent ('\\' :: acc) depth false true inBacktick true
          else
            let _ ← anyChar
            if c == '"' then
              readIndexContent (c :: acc) depth false false inBacktick false
            else
              readIndexContent (c :: acc) depth false true inBacktick false
        else if inBacktick then
          if c == '\\' then
            let _ ← anyChar
            readIndexContent ('\\' :: acc) depth false false true true
          else
            let _ ← anyChar
            if c == '`' then
              readIndexContent (c :: acc) depth false false false false
            else
              readIndexContent (c :: acc) depth false false true false
        else if c == '\\' then
          let _ ← anyChar
          readIndexContent ('\\' :: acc) depth false false false true
        else if c == '\'' then
          let _ ← anyChar
          readIndexContent (c :: acc) depth true false false false
        else if c == '"' then
          let _ ← anyChar
          readIndexContent (c :: acc) depth false true false false
        else if c == '`' then
          let _ ← anyChar
          readIndexContent (c :: acc) depth false false true false
        else if c == '[' then
          let _ ← anyChar
          readIndexContent (c :: acc) (depth + 1) false false false false
        else if c == ']' then
          if depth == 0 then
            pure (String.ofList acc.reverse)
          else
            let _ ← anyChar
            readIndexContent (c :: acc) (depth - 1) false false false false
        else
          let _ ← anyChar
          readIndexContent (c :: acc) depth false false false false

/-- Read an array value: (elem1 elem2 ...) -/
partial def readArray : Parser Token := do
  let (startLine, startCol) ← getPos
  let _ ← lexemeAll (pchar '(')
  let elems ← readArrayElements []
  let _ ← pchar ')'
  mkTokenAt (.T_Array elems) startLine startCol
where
  readArrayElements (acc : List Token) : Parser (List Token) := do
    skipAllSpace
    match ← peek? with
    | none => pure acc.reverse
    | some ')' => pure acc.reverse
    | some _ =>
        let elem ← readArrayElement
        readArrayElements (elem :: acc)

  readArrayElement : Parser Token := do
    skipAllSpace
    match ← peek? with
    | some '[' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt readIndexedElement) with
        | some indexed => pure indexed
        | none => readRegularElement
    | _ => readRegularElement

  readRegularElement : Parser Token := do
    match ← peek? with
    | some '(' => readArray
    | _ => readWord

  readIndexedElement : Parser Token := do
    let (startLine, startCol) ← getPos
    let indices ← readIndices []
    let _ ← pchar '='
    let value ← match ← peek? with
      | some '(' => readArray
      | some c =>
          if c.isWhitespace || c == ')' then
            mkToken (.T_Literal "")
          else
            readWord
      | none => mkToken (.T_Literal "")
    mkTokenAt (.T_IndexedElement indices value) startLine startCol

  readIndices (acc : List Token) : Parser (List Token) := do
    let idx ← readArrayIndex
    match ← peek? with
    | some '[' => readIndices (idx :: acc)
    | _ => pure (idx :: acc).reverse

/-- Read an assignment: VAR=value or VAR=(array) or VAR+=value -/
partial def readAssignment : Parser Token := do
  -- Capture position at the START of the assignment
  let (startLine, startCol) ← getPos
  -- Read variable name
  let varName ← takeWhile1 (fun c => variableChar c || c == '_')
  -- Optional array indices, e.g. `var[0]=x` or `var[key]+=y`
  let indicesArr ← many (attempt readArrayIndex)
  let indices := indicesArr.toList
  -- Check for += or =
  let isAppend ← match ← peek? with
    | some '+' =>
        let _ ← pchar '+'
        let _ ← pchar '='
        pure true
    | some '=' =>
        let _ ← pchar '='
        pure false
    | _ => failure
  -- Check if array assignment
  let value ← match ← peek? with
    | some '(' => readArray
    | _ =>
        -- Read value word (may be empty)
        match ← ShellCheck.Parser.Parsec.optional readWord with
        | some v => pure v
        | none => mkToken (.T_Literal "")
  let mode := if isAppend then AST.AssignmentMode.append else .assign
  mkTokenAt (.T_Assignment mode varName indices value) startLine startCol

/-- Read a simple command (assignments + words), with redirects -/
partial def readSimpleCommand : Parser Token := do
  skipHSpace
  -- Don't parse reserved keywords as commands
  let reserved ← isReservedKeyword
  if reserved then failure
  let (cmdStartLine, cmdStartCol) ← getPos
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
                          match ← ShellCheck.Parser.Parsec.optional (ShellCheck.Parser.Condition.parseConditionTokens .singleBracket args) with
                          | some expr => mkTokenAt (.T_Condition .singleBracket expr) cmdStartLine cmdStartCol
                          | none => mkToken (.T_SimpleCommand assigns words)
                      | _ => mkToken (.T_SimpleCommand assigns words)
                  | [] => mkToken (.T_SimpleCommand assigns words)
              | _ => mkToken (.T_SimpleCommand assigns words)
          | [] => mkToken (.T_SimpleCommand assigns words)
      | _ => mkToken (.T_SimpleCommand assigns words)
    let redirects ← fillHereDocs redirects
    let result ← if redirects.isEmpty then
      pure cmd
    else
      mkToken (.T_Redirecting redirects cmd)
    pure result
where
  /-- Consume heredoc content and update any T_HereDoc redirects with parsed content. -/
  fillHereDocs (redirects : List Token) : Parser (List Token) := do
    let rec go (acc : List Token) (rest : List Token) (started : Bool) : Parser (List Token) := do
      match rest with
      | [] => pure acc.reverse
      | t :: ts =>
          match t.inner with
          | .T_HereDoc dashFlag quoteFlag delim _ =>
              -- Skip to the start of heredoc content once (after the command line).
              if !started then
                skipToHereDocStart
              else
                pure ()
              let content ←
                match quoteFlag with
                | .quoted =>
                    skipHereDocContent delim dashFlag
                    pure []
                | .unquoted =>
                    readHereDocContentTokens delim dashFlag
              let updated : Token := ⟨t.id, .T_HereDoc dashFlag quoteFlag delim content⟩
              go (updated :: acc) ts true
          | _ =>
              go (t :: acc) ts started
    go [] redirects false

  /-- Skip to the start of here-doc content (first line after command). -/
  skipToHereDocStart : Parser Unit := do
    let _ ← takeWhile (· != '\n')
    match ← peek? with
    | some '\n' => let _ ← pchar '\n'; pure ()
    | _ => pure ()

  /-- Consume heredoc content (quoted) without parsing expansions. -/
  skipHereDocContent (delim : String) (dashedFlag : Dashed) : Parser Unit := do
    let rec consumeLines : Parser Unit := do
      match ← peek? with
      | none => pure ()
      | some _ => do
          -- Optionally strip leading tabs for <<-
          if dashedFlag == .dashed then
            do
              let _ ← takeWhile (· == '\t')
              pure ()
          else
            pure ()
          let line ← takeWhile (· != '\n')
          if line == delim then
            match ← peek? with
            | some '\n' => let _ ← pchar '\n'; pure ()
            | _ => pure ()
          else
            match ← peek? with
            | some '\n' =>
                let _ ← pchar '\n'
                consumeLines
            | _ => pure ()
    consumeLines

  /-- Parse heredoc content (unquoted), collecting word-part tokens. -/
  readHereDocContentTokens (delim : String) (dashedFlag : Dashed) : Parser (List Token) := do
    let rec readLines (acc : List Token) : Parser (List Token) := do
      match ← peek? with
      | none => pure acc.reverse
      | some _ => do
          -- Optionally strip leading tabs for <<-
          if dashedFlag == .dashed then
            do
              let _ ← takeWhile (· == '\t')
              pure ()
          else
            pure ()
          -- Check for delimiter line
          let delimPrefix ← peekString delim.length
          let after ← peekString (delim.length + 1)
          let isDelim :=
            delimPrefix == delim &&
              (after.length == delim.length ||
                let nextChar := (String.Pos.Raw.mk delim.length).get after
                nextChar == '\n' || nextChar == '\r')
          if isDelim then
            let _ ← pstring delim
            match ← peek? with
            | some '\r' =>
                let _ ← pchar '\r'
                match ← peek? with
                | some '\n' => let _ ← pchar '\n'; pure ()
                | _ => pure ()
            | some '\n' => let _ ← pchar '\n'; pure ()
            | _ => pure ()
            pure acc.reverse
          else
            let parts ← readHereDocLineParts []
            let acc := parts.reverse ++ acc
            match ← peek? with
            | some '\n' =>
                let _ ← pchar '\n'
                readLines acc
            | some '\r' =>
                let _ ← pchar '\r'
                match ← peek? with
                | some '\n' => let _ ← pchar '\n'; pure ()
                | _ => pure ()
                readLines acc
            | _ => pure acc.reverse
    readLines []

  /-- Read tokens for a single heredoc line (stops before newline). -/
  readHereDocLineParts (acc : List Token) : Parser (List Token) := do
    match ← peek? with
    | none => pure acc.reverse
    | some '\n' => pure acc.reverse
    | some '$' =>
        let (startLine, startCol) ← getPos
        let _ ← anyChar
        let tok ← readDollar startLine startCol
        readHereDocLineParts (tok :: acc)
    | some '`' =>
        let tok ← readBacktick
        readHereDocLineParts (tok :: acc)
    | some '\\' =>
        let (escLine, escCol) ← getPos
        let _ ← anyChar
        match ← peek? with
        | some '$' =>
            let _ ← anyChar
            let tok ← mkTokenAt (.T_Literal "$") escLine escCol
            readHereDocLineParts (tok :: acc)
        | some '`' =>
            let _ ← anyChar
            let tok ← mkTokenAt (.T_Literal "`") escLine escCol
            readHereDocLineParts (tok :: acc)
        | some '\\' =>
            let _ ← anyChar
            let tok ← mkTokenAt (.T_Literal "\\") escLine escCol
            readHereDocLineParts (tok :: acc)
        | _ =>
            let tok ← mkTokenAt (.T_Literal "\\") escLine escCol
            readHereDocLineParts (tok :: acc)
    | some _ =>
        let (litLine, litCol) ← getPos
        let lit ← takeWhile fun c => c != '\n' && c != '$' && c != '`' && c != '\\'
        if lit.isEmpty then
          pure acc.reverse
        else
          let tok ← mkTokenAt (.T_Literal lit) litLine litCol
          readHereDocLineParts (tok :: acc)
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
      : Parser (List Token × List Token × List Token) := do
    skipHSpace
    match ← peek? with
    | none => pure (assignAcc.reverse, wordAcc.reverse, redirAcc.reverse)
    | some c =>
        -- Check for &> redirections before treating & as a terminator
        if c == '&' then
          let nextTwo ← peekString 2
          if nextTwo == "&>" then
            let redir ← readFdRedirect
            readAssignsWordsAndRedirects assignAcc wordAcc (redir :: redirAcc)
          else
            pure (assignAcc.reverse, wordAcc.reverse, redirAcc.reverse)
        -- Check for command terminators
        else if c == '\n' || c == ';' || c == '|' || c == ')' || c == '}' then
          pure (assignAcc.reverse, wordAcc.reverse, redirAcc.reverse)
        else if c == '#' then
          let _ ← takeWhile (· != '\n')
          pure (assignAcc.reverse, wordAcc.reverse, redirAcc.reverse)
        -- Check for redirects: >, >>, <, <<, etc.
        -- BUT: <(...) and >(...) are process substitutions, not redirects
        else if c == '>' || c == '<' then
          let (redirStartLine, redirStartCol) ← getPos
          let nextTwo ← peekString 2
          if nextTwo == "<(" || nextTwo == ">(" then
            -- Process substitution - parse as word
            let word ← readWord
            readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
          else
            let redir ← readRedirect
            let redir ←
              match redir.inner with
              | .T_IoFile op _ =>
                  match op.inner with
                  | .T_GREATAND =>
                      mkTokenAt (.T_FdRedirect "" redir) redirStartLine redirStartCol
                  | _ => pure redir
              | _ => pure redir
            readAssignsWordsAndRedirects assignAcc wordAcc (redir :: redirAcc)
        -- Check for fd redirect like 2>, 1>&2
        else if c.isDigit || c == '{' then
          match ← ShellCheck.Parser.Parsec.optional (attempt readFdRedirect) with
          | some redir => readAssignsWordsAndRedirects assignAcc wordAcc (redir :: redirAcc)
          | none =>
              -- Not a fd redirect, could be assignment or word
              -- Try assignment if: no words yet OR first word is declaration builtin
              if wordAcc.isEmpty || isInDeclarationContext wordAcc then
                match ← ShellCheck.Parser.Parsec.optional (attempt readAssignment) with
                | some assign => readAssignsWordsAndRedirects (assign :: assignAcc) wordAcc redirAcc
                | none =>
                    let word ← readWord
                    readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
              else
                let word ← readWord
                readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
        else
          -- Could be an assignment or a word
          -- Try assignment if: no words yet OR first word is declaration builtin
          if wordAcc.isEmpty || isInDeclarationContext wordAcc then
            match ← ShellCheck.Parser.Parsec.optional (attempt readAssignment) with
            | some assign => readAssignsWordsAndRedirects (assign :: assignAcc) wordAcc redirAcc
            | none =>
                let word ← readWord
                readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc
          else
            let word ← readWord
            readAssignsWordsAndRedirects assignAcc (word :: wordAcc) redirAcc

  /-- Read a heredoc delimiter, returning (delimiter_string, is_quoted) -/
  readHereDocDelimiter : Parser (String × Bool) := do
    skipHSpace
    match ← peek? with
    | some '\'' =>
        -- Single-quoted: 'DELIM'
        let _ ← pchar '\''
        let delim ← takeWhile (· != '\'')
        let _ ← pchar '\''
        pure (delim, true)
    | some '"' =>
        -- Double-quoted: "DELIM"
        let _ ← pchar '"'
        let delim ← takeWhile (· != '"')
        let _ ← pchar '"'
        pure (delim, true)
    | some '\\' =>
        -- Escaped: \DELIM (makes it quoted)
        let _ ← pchar '\\'
        let delim ← takeWhile (fun c => !c.isWhitespace && c != '\n')
        pure (delim, true)
    | _ =>
        -- Unquoted delimiter
        let delim ← takeWhile (fun c => !c.isWhitespace && c != '\n' && c != ';' && c != '&' && c != '|')
        pure (delim, false)

  /-- Read a redirect operator and its target -/
  readRedirect : Parser Token := do
    let opStart ← peek?
    let op ← match opStart with
      | some '>' =>
          let _ ← pchar '>'
          match ← peek? with
          | some '>' =>
              let _ ← pchar '>'
              pure ">>"
          | some '&' =>
              let _ ← pchar '&'
              pure ">&"
          | some '|' =>
              let _ ← pchar '|'
              pure ">|"
          | _ => pure ">"
      | some '<' =>
          let _ ← pchar '<'
          match ← peek? with
          | some '<' =>
              let _ ← pchar '<'
              match ← peek? with
              | some '<' =>
                  let _ ← pchar '<'
                  pure "<<<"
              | some '-' =>
                  let _ ← pchar '-'
                  pure "<<-"
              | _ => pure "<<"
          | some '>' =>
              let _ ← pchar '>'
              pure "<>"
          | some '&' =>
              let _ ← pchar '&'
              pure "<&"
          | _ => pure "<"
      | _ => failure
    skipHSpace
    -- Handle here-doc specially
    if op == "<<" || op == "<<-" then
      -- Read the delimiter and determine if it's quoted
      let (delimStr, isQuoted) ← readHereDocDelimiter
      -- After reading the command line, we consume heredoc content and attach it later.
      let dashedFlag := if op == "<<-" then Dashed.dashed else Dashed.undashed
      let quotedFlag := if isQuoted then Quoted.quoted else Quoted.unquoted
      -- Create T_HereDoc with empty content for now; filled in after command line.
      mkToken (.T_HereDoc dashedFlag quotedFlag delimStr [])
    else if op == "<<<" then
      let target ← readWord
      mkToken (.T_HereString target)
    else
      let opTok ←
        match op with
        | ">" => mkToken .T_Greater
        | ">>" => mkToken .T_DGREAT
        | ">&" => mkToken .T_GREATAND
        | ">|" => mkToken .T_CLOBBER
        | "<" => mkToken .T_Less
        | "<<" => mkToken .T_DLESS
        | "<<-" => mkToken .T_DLESSDASH
        | "<>" => mkToken .T_LESSGREAT
        | "<&" => mkToken .T_LESSAND
        | _ => mkToken (.T_Literal op)
      -- For file redirects, read the target
      match ← peek? with
      | some '-' =>
          -- Close fd: >&- or <&-
          let _ ← pchar '-'
          let target ← mkToken (.T_Literal "-")
          mkToken (.T_IoFile opTok target)
      | some c =>
          if c.isDigit && (op == ">&" || op == "<&") then
            -- Dup fd: >&2, <&0
            let fd ← takeWhile1 Char.isDigit
            mkToken (.T_IoDuplicate opTok fd)
          else
            let target ← readWord
            mkToken (.T_IoFile opTok target)
      | none => failure

  /-- Read a fd redirect like 2>, 2>>, 2>&1 -/
  readFdRedirect : Parser Token := do
    let (startLine, startCol) ← getPos
    let fd ←
      match ← peek? with
      | some '{' =>
          let _ ← pchar '{'
          let name ← takeWhile (· != '}')
          let _ ← pchar '}'
          pure ("{" ++ name ++ "}")
      | some '&' =>
          let _ ← pchar '&'
          pure "&"
      | some c =>
          if c.isDigit then
            takeWhile1 Char.isDigit
          else
            failure
      | none => failure
    let opStart ← peek?
    if opStart != some '>' && opStart != some '<' then failure
    let redir ← readRedirect
    mkTokenAt (.T_FdRedirect fd redir) startLine startCol

/-- Read raw content until `terminator` (not consumed). Fails on EOF. -/
partial def readUntilString (terminator : String) : Parser String := do
  let rec go (acc : List Char) (inSingle inDouble escaped : Bool) : Parser String := do
    -- Only consider the terminator when we're not in a quoted/escaped context.
    if !inSingle && !inDouble && !escaped then
      let look ← peekString terminator.length
      if look == terminator then
        return String.ofList acc.reverse

    match ← peek? with
    | none =>
        ShellCheck.Parser.Parsec.Parser.fail s!"expected closing {terminator}"
    | some c =>
        let _ ← anyChar
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
partial def readDoubleBracketCondition : Parser Token := do
  let (startLine, startCol) ← getPos
  let _ ← pstring "[["
  let condTokens ← readCondTokens []
  skipAllSpace
  let _ ← pstring "]]"
  let expr ←
    match ← ShellCheck.Parser.Parsec.optional (ShellCheck.Parser.Condition.parseConditionTokens .doubleBracket condTokens) with
    | some e => pure e
    | none =>
        -- Fall back to a minimal tree so the rest of the file can still parse.
        if condTokens.isEmpty then
          mkTokenAt (.TC_Empty .doubleBracket) startLine startCol
        else
          let fallbackWord :=
            condTokens.find? (fun t => match t.inner with | .T_Literal _ => false | _ => true)
              |>.getD condTokens.head!
          mkTokenAt (.TC_Nullary .doubleBracket fallbackWord) startLine startCol
  mkTokenAt (.T_Condition .doubleBracket expr) startLine startCol
where
  /-- Tokenize the body of `[[ ... ]]` into a list of operator/word tokens. -/
  readCondTokens (acc : List Token) : Parser (List Token) := do
    skipAllSpace
    let done ← peekKeyword "]]"
    if done then
      pure acc.reverse
    else
      let (tokStartLine, tokStartCol) ← getPos
      let look2 ← peekString 2
      if look2 == "&&" || look2 == "||" then
        let op ← pstring look2
        let tok ← mkTokenAt (.T_Literal op) tokStartLine tokStartCol
        readCondTokens (tok :: acc)
      else
        match ← peek? with
        | some '(' | some ')' | some '<' | some '>' =>
            let c ← anyChar
            let tok ← mkTokenAt (.T_Literal (String.ofList [c])) tokStartLine tokStartCol
            readCondTokens (tok :: acc)
        | _ =>
            let w ← readWord
            readCondTokens (w :: acc)

/-- Read a pipe sequence: cmd | cmd | cmd -/
partial def readPipeSequence : Parser Token := do
  let first ← readPipeCommand
  skipHSpace
  let (seps, cmds) ← readPipeContinuation [] [first]
  if cmds.length == 1 then
    pure first
  else
    mkToken (.T_Pipeline seps cmds)
where
  /-- Read a command that can appear in a pipeline -/
  readPipeCommand : Parser Token := do
    skipHSpace
    let isDoubleBracket ← peekKeyword "[["
    if isDoubleBracket then
      readDoubleBracketCondition
    else match ← peek? with
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
                      match ← ShellCheck.Parser.Parsec.optional (attempt readPosixFunctionInPipe) with
                      | some func => pure func
                      | none => readSimpleCommand

  /-- Read a POSIX function definition in pipe context: name() { body } -/
  readPosixFunctionInPipe : Parser Token := do
    let name ← takeWhile1 (fun c => variableChar c || c == '-' || c == '.')
    skipHSpace
    let _ ← pstring "()"
    skipAllSpace
    -- Bash allows `name() ( ... )` (subshell function bodies).
    let body ← attempt readBraceGroupInPipe <|> readSubshellInPipe
    mkToken (.T_Function ⟨false⟩ ⟨true⟩ name body)

  -- Forward declarations for compound commands in pipe
  readBraceGroupInPipe : Parser Token := do
    let _ ← lexemeAll (pchar '{')
    let cmds ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← pchar '}'
    mkToken (.T_BraceGroup cmds)

  readSubshellInPipe : Parser Token := do
    match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "((")) with
    | some _ =>
        let content ← readArithContentHelper
        let _ ← pstring "))"
        let inner ← mkToken (.T_Literal content)
        mkToken (.T_Arithmetic inner)
    | none =>
        let _ ← lexemeAll (pchar '(')
        let cmds ← readTermInPipe
        skipAllSpace
        let _ ← pchar ')'
        mkToken (.T_Subshell cmds)

  readIfInPipe : Parser Token := do
    let _ ← consumeKeyword "if"
    skipAllSpace
    let cond ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "then"
    skipAllSpace
    let thenBody ← readTermInPipe
    let (branches, elseBody) ← readElifElseInPipe [(cond, thenBody)] []
    mkToken (.T_IfExpression branches elseBody)

  readElifElseInPipe (branches : List (List Token × List Token)) (_acc : List Token)
      : Parser (List (List Token × List Token) × List Token) := do
    skipHSpace
    optionalSemicolon
    let isElif ← peekKeyword "elif"
    if isElif then
      let _ ← consumeKeyword "elif"
      skipAllSpace
      let cond ← readTermInPipe
      skipHSpace
      optionalSemicolon
      let _ ← consumeKeyword "then"
      skipAllSpace
      let body ← readTermInPipe
      readElifElseInPipe (branches ++ [(cond, body)]) []
    else
      let isElse ← peekKeyword "else"
      if isElse then
        let _ ← consumeKeyword "else"
        skipAllSpace
        let elseBody ← readTermInPipe
        skipHSpace
        optionalSemicolon
        let _ ← consumeKeyword "fi"
        pure (branches, elseBody)
      else
        let _ ← consumeKeyword "fi"
        pure (branches, [])

  readWhileInPipe : Parser Token := do
    let _ ← consumeKeyword "while"
    skipAllSpace
    let cond ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "do"
    skipAllSpace
    let body ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "done"
    mkToken (.T_WhileExpression cond body)

  readUntilInPipe : Parser Token := do
    let _ ← consumeKeyword "until"
    skipAllSpace
    let cond ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "do"
    skipAllSpace
    let body ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "done"
    mkToken (.T_UntilExpression cond body)

  readForInPipe : Parser Token := do
    attempt readForArithInPipe <|> readForInInPipe

  readForArithInPipe : Parser Token := do
    let _ ← consumeKeyword "for"
    skipHSpace
    let _ ← pstring "(("
    skipHSpace
    let initContent ← takeWhile (· != ';')
    let init ← mkToken (.T_Literal initContent)
    let _ ← pchar ';'
    skipHSpace
    let condContent ← takeWhile (· != ';')
    let cond ← mkToken (.T_Literal condContent)
    let _ ← pchar ';'
    skipHSpace
    let incrContent ← readArithContentHelper
    let incr ← mkToken (.T_Literal incrContent)
    let _ ← pstring "))"
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "do"
    skipAllSpace
    let body ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "done"
    mkToken (.T_ForArithmetic init cond incr body)

  readForInInPipe : Parser Token := do
    let _ ← consumeKeyword "for"
    skipHSpace
    let varName ← takeWhile1 variableChar
    skipHSpace
    let hasIn ← peekKeyword "in"
    let words ← if hasIn then do
      let _ ← consumeKeyword "in"
      skipHSpace
      readForWordsInPipe []
    else pure []
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "do"
    skipAllSpace
    let body ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "done"
    mkToken (.T_ForIn varName words body)

  readForWordsInPipe (acc : List Token) : Parser (List Token) := do
    skipHSpace
    match ← peek? with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWord
            readForWordsInPipe (word :: acc)

  readCaseInPipe : Parser Token := do
    let _ ← consumeKeyword "case"
    skipHSpace
    let word ← readWord
    skipHSpace
    let _ ← consumeKeyword "in"
    skipAllSpace
    let cases ← readCaseItemsInPipe []
    let _ ← consumeKeyword "esac"
    mkToken (.T_CaseExpression word cases)

  readCaseItemsInPipe (acc : List (CaseType × List Token × List Token))
      : Parser (List (CaseType × List Token × List Token)) := do
    skipAllSpace
    let isEsac ← peekKeyword "esac"
    if isEsac then pure acc.reverse
    else
      let _ ← ShellCheck.Parser.Parsec.optional (pchar '(')
      let patterns ← readPatternsInPipe []
      let _ ← lexemeAll (pchar ')')
      let (cmds, terminator) ← readCaseBodyInPipe [] .caseBreak
      readCaseItemsInPipe ((terminator, patterns, cmds) :: acc)

  readPatternsInPipe (acc : List Token) : Parser (List Token) := do
    skipHSpace
    let pat ← readPatternWord
    skipHSpace
    match ← peek? with
    | some '|' =>
        let _ ← pchar '|'
        readPatternsInPipe (pat :: acc)
    | _ => pure (pat :: acc).reverse

  readCaseBodyInPipe (acc : List Token) (termType : CaseType) : Parser (List Token × CaseType) := do
    skipAllSpace  -- Skip newlines and spaces
    match ← peek? with
    | none => pure (acc.reverse, termType)
    | some ';' =>
        let _ ← pchar ';'
        match ← peek? with
        | some ';' =>
            let _ ← pchar ';'
            match ← peek? with
            | some '&' =>
                let _ ← pchar '&'
                pure (acc.reverse, .caseContinue)
            | _ => pure (acc.reverse, .caseBreak)
        | some '&' =>
            let _ ← pchar '&'
            pure (acc.reverse, .caseFallThrough)
        | _ =>
            skipAllSpace
            let cmd ← readAndOrInPipe
            readCaseBodyInPipe (cmd :: acc) termType
    | some _ =>
        let isEsac ← peekKeyword "esac"
        if isEsac then pure (acc.reverse, termType)
        else
          let cmd ← readAndOrInPipe
          readCaseBodyInPipe (cmd :: acc) termType

  readFunctionInPipe : Parser Token := do
    let _ ← consumeKeyword "function"
    skipHSpace
    let name ← takeWhile1 (fun c => variableChar c || c == '-' || c == '.')
    skipHSpace
    let hasParens ← ShellCheck.Parser.Parsec.optional (attempt (pstring "()"))
    skipAllSpace
    let body ← readBraceGroupInPipe
    mkToken (.T_Function ⟨true⟩ ⟨hasParens.isSome⟩ name body)

  readSelectInPipe : Parser Token := do
    let _ ← consumeKeyword "select"
    skipHSpace
    let varName ← takeWhile1 variableChar
    skipHSpace
    -- "in" is ShellCheck.Parser.Parsec.optional - if omitted, uses positional parameters
    let hasIn ← peekKeyword "in"
    let words ← if hasIn then do
      let _ ← consumeKeyword "in"
      skipHSpace
      readSelectWordsInPipe []
    else
      pure []
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "do"
    skipAllSpace
    let body ← readTermInPipe
    skipHSpace
    optionalSemicolon
    let _ ← consumeKeyword "done"
    mkToken (.T_SelectIn varName words body)

  readSelectWordsInPipe (acc : List Token) : Parser (List Token) := do
    skipHSpace
    match ← peek? with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWord
            readSelectWordsInPipe (word :: acc)

  -- Self-contained term/andor for inside pipe context
  -- These form a mutually recursive group within the where clause

  readTermInPipe : Parser (List Token) := do
    let first ← readAndOrInPipe
    readTermContinuationInPipe [first]

  readTermContinuationInPipe (acc : List Token) : Parser (List Token) := do
    skipHSpace
    match ← peek? with
    | some ';' =>
        let _ ← pchar ';'
        match ← peek? with
        | some ';' => pure acc.reverse  -- This is ;; not ;
        | _ =>
            skipAllSpace
            match ← ShellCheck.Parser.Parsec.optional readAndOrInPipe with
            | some next => readTermContinuationInPipe (next :: acc)
            | none => pure acc.reverse
    | some '&' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "&&")) with
        | some _ => pure acc.reverse  -- Already handled by readAndOrInPipe
        | none =>
            let _ ← pchar '&'
            let last := acc.head!
            let rest := acc.tail!
            let bgLast ← mkToken (.T_Backgrounded last)
            skipAllSpace
            match ← ShellCheck.Parser.Parsec.optional readAndOrInPipe with
            | some next => readTermContinuationInPipe (next :: bgLast :: rest)
            | none => pure (bgLast :: rest).reverse
    | some '\n' =>
        let _ ← lexemeAll (pchar '\n')
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
          match ← ShellCheck.Parser.Parsec.optional readAndOrInPipe with
          | some next => readTermContinuationInPipe (next :: acc)
          | none => pure acc.reverse
    | _ => pure acc.reverse

  readAndOrInPipe : Parser Token := do
    let first ← readPipelineInPipe
    readAndOrContinuationInPipe first

  readAndOrContinuationInPipe (left : Token) : Parser Token := do
    skipHSpace
    match ← peek? with
    | some '&' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "&&")) with
        | some _ =>
            skipAllSpace
            let right ← readPipelineInPipe
            let combined ← mkToken (.T_AndIf left right)
            readAndOrContinuationInPipe combined
        | none => pure left
    | some '|' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "||")) with
        | some _ =>
            skipAllSpace
            let right ← readPipelineInPipe
            let combined ← mkToken (.T_OrIf left right)
            readAndOrContinuationInPipe combined
        | none => pure left
    | _ => pure left

  readPipelineInPipe : Parser Token := do
    skipHSpace
    let banged ← ShellCheck.Parser.Parsec.optional (pchar '!' <* skipHSpace)
    let pipeline ← readPipeSequenceInPipe
    match banged with
    | some _ => mkToken (.T_Banged pipeline)
    | none => pure pipeline

  readPipeSequenceInPipe : Parser Token := do
    let first ← readPipeCommand
    skipHSpace
    let (seps, cmds) ← readPipeContinuationInPipe [] [first]
    if cmds.length == 1 then
      pure first
    else
      mkToken (.T_Pipeline seps cmds)

  readPipeContinuationInPipe (seps : List Token) (cmds : List Token) : Parser (List Token × List Token) := do
    skipHSpace
    match ← peek? with
    | some '|' =>
        -- Use lookahead to check for || without consuming it
        let next2 ← peekString 2
        if next2 == "||" then
          pure (seps.reverse, cmds.reverse)  -- This is || not |, don't consume
        else
          let pipeStr ← readPipeOpInPipe
          let sepTok ← mkToken (.T_Pipe pipeStr)
          skipAllSpace
          let cmd ← readPipeCommand
          readPipeContinuationInPipe (sepTok :: seps) (cmd :: cmds)
    | _ => pure (seps.reverse, cmds.reverse)

  readPipeOpInPipe : Parser String := do
    let _ ← pchar '|'
    match ← peek? with
    | some '&' =>
        let _ ← anyChar
        pure "|&"
    | _ => pure "|"

  readPipeContinuation (seps : List Token) (cmds : List Token) : Parser (List Token × List Token) := do
    skipHSpace
    match ← peek? with
    | some '|' =>
        -- Use lookahead to check for || without consuming it
        let next2 ← peekString 2
        if next2 == "||" then
          pure (seps.reverse, cmds.reverse)  -- This is || not |, don't consume
        else
          let pipeStr ← readPipeOp
          let sepTok ← mkToken (.T_Pipe pipeStr)
          skipAllSpace
          let cmd ← readPipeCommand
          readPipeContinuation (sepTok :: seps) (cmd :: cmds)
    | _ => pure (seps.reverse, cmds.reverse)

  readPipeOp : Parser String := do
    let _ ← pchar '|'
    match ← peek? with
    | some '&' =>
        let _ ← anyChar
        pure "|&"
    | _ => pure "|"

/-- Read a pipeline: [!] pipe_sequence -/
def readPipeline : Parser Token := do
  skipHSpace
  let banged ← ShellCheck.Parser.Parsec.optional (pchar '!' <* skipHSpace)
  let pipeline ← readPipeSequence
  match banged with
  | some _ => mkToken (.T_Banged pipeline)
  | none => pure pipeline

/-- Read an and-or list: pipeline ((&&|||) pipeline)* -/
partial def readAndOr : Parser Token := do
  let first ← readPipeline
  skipHSpace
  readAndOrContinuation first
where
  readAndOrContinuation (left : Token) : Parser Token := do
    skipHSpace
    match ← peek? with
    | some '&' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "&&")) with
        | some _ =>
            skipAllSpace
            let right ← readPipeline
            let combined ← mkToken (.T_AndIf left right)
            readAndOrContinuation combined
        | none =>
            pure left
    | some '|' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "||")) with
        | some _ =>
            skipAllSpace
            let right ← readPipeline
            let combined ← mkToken (.T_OrIf left right)
            readAndOrContinuation combined
        | none =>
            pure left
    | _ =>
        pure left

/-- Read an and-or with any preceding shellcheck annotations -/
partial def readAndOrWithAnnotations : Parser Token := do
  let annotations ← skipAllSpaceCollectAnnotations
  let cmd ← readAndOr
  if annotations.isEmpty then
    pure cmd
  else
    mkToken (.T_Annotation annotations cmd)

/-- Read a term: and-or ((;|&|newline) and-or)* -/
partial def readTermFromFirst (first : Token) : Parser (List Token) := do
  readTermContinuation [first]
where
  /-- After a command separator (`;`, `&`, or newline), attempt to parse the next
  command *only if* we're not at an end marker (EOF/`)/`}`) or a reserved
  keyword that should terminate the surrounding construct (`then`, `fi`, `esac`,
  `done`, ...).

  This avoids silently truncating the parse when the next command exists but is
  malformed (e.g. an invalid `case` pattern). -/
  parseNextAfterSeparator : Parser (Option Token) := do
    let annots ← skipAllSpaceCollectAnnotations
    match ← peek? with
    | none => pure none
    | some ')' => pure none
    | some '}' => pure none
    | some _ =>
        let reserved ← isReservedKeyword
        if reserved then
          pure none
        else
          let cmd ← readAndOr
          if annots.isEmpty then
            pure (some cmd)
          else
            some <$> mkToken (.T_Annotation annots cmd)

  readTermContinuation (acc : List Token) : Parser (List Token) := do
    skipHSpace
    match ← peek? with
    | some ';' =>
        let _ ← pchar ';'
        match ← peek? with
        | some ';' => pure acc.reverse  -- This is ;; not ;
        | _ =>
            match ← parseNextAfterSeparator with
            | some next => readTermContinuation (next :: acc)
            | none => pure acc.reverse
    | some '&' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "&&")) with
        | some _ => pure acc.reverse  -- Already handled by readAndOr
        | none =>
            let _ ← pchar '&'
            -- Background the last command
            let last := acc.head!
            let rest := acc.tail!
            let bgLast ← mkToken (.T_Backgrounded last)
            match ← parseNextAfterSeparator with
            | some next => readTermContinuation (next :: bgLast :: rest)
            | none => pure (bgLast :: rest).reverse
    | some '\n' =>
        let _ ← pchar '\n'
        match ← parseNextAfterSeparator with
        | some next => readTermContinuation (next :: acc)
        | none => pure acc.reverse
    | _ => pure acc.reverse

/-- Read a term: and-or ((;|&|newline) and-or)* -/
partial def readTerm : Parser (List Token) := do
  let first ← readAndOrWithAnnotations
  readTermFromFirst first

/-!
### Control Flow (if/while/for/case/select)

Now that readTerm and readAndOr are defined, we can add control flow.
-/

/-- Read a subshell: ( commands ) -/
partial def readSubshell : Parser Token := do
  let _ ← lexemeAll (pchar '(')
  let cmds ← readTerm
  skipAllSpace
  let _ ← pchar ')'
  mkToken (.T_Subshell cmds)

/-- Read a brace group: { commands } -/
partial def readBraceGroup : Parser Token := do
  let _ ← lexemeAll (pchar '{')
  let cmds ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← pchar '}'
  mkToken (.T_BraceGroup cmds)

/-- Read an if expression: if cond; then body; [elif cond; then body;]* [else body;] fi -/
partial def readIfExpression : Parser Token := do
  let _ ← consumeKeyword "if"
  skipAllSpace
  let cond ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "then"
  skipAllSpace
  let thenBody ← readTerm
  let (branches, elseBody) ← readElifElse [(cond, thenBody)] []
  mkToken (.T_IfExpression branches elseBody)
where
  readElifElse (branches : List (List Token × List Token)) (_elseAcc : List Token)
      : Parser (List (List Token × List Token) × List Token) := do
    skipHSpace
    optionalSemicolon
    let isElif ← peekKeyword "elif"
    if isElif then
      let _ ← consumeKeyword "elif"
      skipAllSpace
      let cond ← readTerm
      skipHSpace
      optionalSemicolon
      let _ ← consumeKeyword "then"
      skipAllSpace
      let body ← readTerm
      readElifElse (branches ++ [(cond, body)]) []
    else
      let isElse ← peekKeyword "else"
      if isElse then
        let _ ← consumeKeyword "else"
        skipAllSpace
        let elseBody ← readTerm
        skipHSpace
        optionalSemicolon
        let _ ← consumeKeyword "fi"
        pure (branches, elseBody)
      else
        let _ ← consumeKeyword "fi"
        pure (branches, [])

/-- Read a while expression: while cond; do body; done -/
partial def readWhileExpression : Parser Token := do
  let _ ← consumeKeyword "while"
  skipAllSpace
  let cond ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "do"
  skipAllSpace
  let body ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "done"
  mkToken (.T_WhileExpression cond body)

/-- Read an until expression: until cond; do body; done -/
partial def readUntilExpression : Parser Token := do
  let _ ← consumeKeyword "until"
  skipAllSpace
  let cond ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "do"
  skipAllSpace
  let body ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "done"
  mkToken (.T_UntilExpression cond body)

/-- Read a for-in expression: for var [in words]; do body; done -/
partial def readForIn : Parser Token := do
  let _ ← consumeKeyword "for"
  skipHSpace
  let varName ← takeWhile1 variableChar
  skipHSpace
  let hasIn ← peekKeyword "in"
  let words ← if hasIn then do
    let _ ← consumeKeyword "in"
    skipHSpace
    readForWords []
  else pure []
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "do"
  skipAllSpace
  let body ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "done"
  mkToken (.T_ForIn varName words body)
where
  readForWords (acc : List Token) : Parser (List Token) := do
    skipHSpace
    match ← peek? with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWord
            readForWords (word :: acc)

/-- Read a for arithmetic expression: for ((init; cond; incr)); do body; done -/
partial def readForArithmetic : Parser Token := do
  let _ ← consumeKeyword "for"
  skipHSpace
  let _ ← pstring "(("
  skipHSpace
  let initContent ← takeWhile (· != ';')
  let init ← mkToken (.T_Literal initContent)
  let _ ← pchar ';'
  skipHSpace
  let condContent ← takeWhile (· != ';')
  let cond ← mkToken (.T_Literal condContent)
  let _ ← pchar ';'
  skipHSpace
  let incrContent ← readArithContentHelper
  let incr ← mkToken (.T_Literal incrContent)
  let _ ← pstring "))"
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "do"
  skipAllSpace
  let body ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "done"
  mkToken (.T_ForArithmetic init cond incr body)

/-- Read a case expression: case word in pattern) cmds ;; ... esac -/
partial def readCaseExpression : Parser Token := do
  let _ ← consumeKeyword "case"
  skipHSpace
  let word ← readWord
  skipHSpace
  let _ ← consumeKeyword "in"
  skipAllSpace
  let cases ← readCaseItems []
  let _ ← consumeKeyword "esac"
  mkToken (.T_CaseExpression word cases)
where
  readCaseItems (acc : List (CaseType × List Token × List Token))
      : Parser (List (CaseType × List Token × List Token)) := do
    skipAllSpace
    let isEsac ← peekKeyword "esac"
    if isEsac then pure acc.reverse
    else
      let _ ← ShellCheck.Parser.Parsec.optional (pchar '(')
      let patterns ← readPatterns []
      let _ ← lexemeAll (pchar ')')
      let (cmds, terminator) ← readCaseBody [] .caseBreak
      readCaseItems ((terminator, patterns, cmds) :: acc)

  readPatterns (acc : List Token) : Parser (List Token) := do
    skipHSpace
    let pat ← readPatternWord
    skipHSpace
    match ← peek? with
    | some '|' =>
        let _ ← pchar '|'
        readPatterns (pat :: acc)
    | _ => pure (pat :: acc).reverse

  readCaseBody (acc : List Token) (termType : CaseType) : Parser (List Token × CaseType) := do
    skipAllSpace  -- Skip newlines and spaces
    match ← peek? with
    | none => pure (acc.reverse, termType)
    | some ';' =>
        let _ ← pchar ';'
        match ← peek? with
        | some ';' =>
            let _ ← pchar ';'
            match ← peek? with
            | some '&' =>
                let _ ← pchar '&'
                pure (acc.reverse, .caseContinue)
            | _ => pure (acc.reverse, .caseBreak)
        | some '&' =>
            let _ ← pchar '&'
            pure (acc.reverse, .caseFallThrough)
        | _ =>
            skipAllSpace
            let cmd ← readAndOr
            readCaseBody (cmd :: acc) termType
    | some _ =>
        let isEsac ← peekKeyword "esac"
        if isEsac then pure (acc.reverse, termType)
        else
          let cmd ← readAndOr
          readCaseBody (cmd :: acc) termType

/-- Read a select expression: select var [in words]; do body; done -/
partial def readSelect : Parser Token := do
  let _ ← consumeKeyword "select"
  skipHSpace
  let varName ← takeWhile1 variableChar
  skipHSpace
  -- "in" is ShellCheck.Parser.Parsec.optional - if omitted, uses positional parameters
  let hasIn ← peekKeyword "in"
  let words ← if hasIn then do
    let _ ← consumeKeyword "in"
    skipHSpace
    readSelectWords []
  else
    pure []
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "do"
  skipAllSpace
  let body ← readTerm
  skipHSpace
  optionalSemicolon
  let _ ← consumeKeyword "done"
  mkToken (.T_SelectIn varName words body)
where
  readSelectWords (acc : List Token) : Parser (List Token) := do
    skipHSpace
    match ← peek? with
    | none => pure acc.reverse
    | some c =>
        if c == '\n' || c == ';' then pure acc.reverse
        else
          let isDo ← peekKeyword "do"
          if isDo then pure acc.reverse
          else
            let word ← readWord
            readSelectWords (word :: acc)

/-- Read an arithmetic command: (( expr )) -/
partial def readArithmeticCommand : Parser Token := do
  let _ ← pstring "(("
  let content ← readArithContentHelper
  let _ ← pstring "))"
  let inner ← mkToken (.T_Literal content)
  mkToken (.T_Arithmetic inner)

/-- Read a function definition: function name { body } or name() { body } -/
partial def readFunction : Parser Token := do
  let hasKeyword ← peekKeyword "function"
  if hasKeyword then
    let _ ← consumeKeyword "function"
    skipHSpace
    let name ← takeWhile1 (fun c => variableChar c || c == '-' || c == '.')
    skipHSpace
    let hasParens ← ShellCheck.Parser.Parsec.optional (attempt (pstring "()"))
    skipAllSpace
    let body ← readBraceGroup
    mkToken (.T_Function ⟨true⟩ ⟨hasParens.isSome⟩ name body)
  else failure

/-- Read a POSIX function definition: name() { body } -/
  partial def readPosixFunction : Parser Token := do
    -- Read function name (must be valid identifier)
    let name ← takeWhile1 (fun c => variableChar c || c == '-' || c == '.')
    -- Must be followed by ()
    skipHSpace
    let _ ← pstring "()"
    skipAllSpace
    -- Bash allows `name() ( ... )` (subshell function bodies). ShellCheck models this as a
    -- function whose body token is a `T_Subshell`.
    let body ← attempt readBraceGroup <|> readSubshell
    mkToken (.T_Function ⟨false⟩ ⟨true⟩ name body)

  /-- Read any command (compound or simple) -/
  partial def readCommand : Parser Token := do
    skipHSpace
    let isDoubleBracket ← peekKeyword "[["
    if isDoubleBracket then
      readDoubleBracketCondition
    else match ← peek? with
    | some '{' => readBraceGroup
    | some '(' =>
        match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "((")) with
        | some _ =>
            let content ← readArithContentHelper
            let _ ← pstring "))"
            let inner ← mkToken (.T_Literal content)
            mkToken (.T_Arithmetic inner)
        | none => readSubshell
    | _ =>
        let isIf ← peekKeyword "if"
        if isIf then readIfExpression
        else
          let isWhile ← peekKeyword "while"
          if isWhile then readWhileExpression
          else
            let isUntil ← peekKeyword "until"
            if isUntil then readUntilExpression
            else
              let isFor ← peekKeyword "for"
              if isFor then attempt readForArithmetic <|> readForIn
              else
                let isCase ← peekKeyword "case"
                if isCase then readCaseExpression
                else
                  let isSelect ← peekKeyword "select"
                  if isSelect then readSelect
                  else
                    let isFunction ← peekKeyword "function"
                    if isFunction then readFunction
                    else
                      -- Try POSIX function syntax: name() { body }
                      match ← ShellCheck.Parser.Parsec.optional (attempt readPosixFunction) with
                      | some func => pure func
                      | none => readSimpleCommand

/-- Read a complete script -/
def readScript : Parser Token := do
  -- Don't skip whitespace first - shebang must be at very start
  let shebang ←
    match ← ShellCheck.Parser.Parsec.optional (attempt (pstring "#!")) with
    | some _ =>
        let line ← takeWhile (· != '\n')
        let _ ← ShellCheck.Parser.Parsec.optional (pchar '\n')
        mkToken (.T_Literal ("#!" ++ line))
    | none =>
        mkToken (.T_Literal "")

  let annotations ← skipAllSpaceCollectAnnotations
  let (shebang, commands) ←
    match ← peek? with
    | none =>
        if annotations.isEmpty then
          pure (shebang, [])
        else
          let shebangAnnotated ← mkToken (.T_Annotation annotations shebang)
          pure (shebangAnnotated, [])
    | some _ =>
        let cmd ← readAndOr
        let first ←
          if annotations.isEmpty then
            pure cmd
          else
            mkToken (.T_Annotation annotations cmd)
        let commands ← readTermFromFirst first
        pure (shebang, commands)
  skipAllSpace
  mkToken (.T_Script shebang commands)

/-- Parse a string as commands (for subshell content), with position offset -/
def parseSubshellContent (content : String) (filename : String) (startId : Nat) (offsetLine : Nat) (offsetCol : Nat) : (List Token × Nat × Std.HashMap Id (Position × Position)) :=
  let it := ShellCheck.Parser.Parsec.PosIterator.create content
  let initState : ParserState :=
    { ShellCheck.Parser.Parsec.mkParserState filename with nextId := startId }
  match readTerm initState it with
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
              -- Recursively expand any nested $() in the parsed commands.
              -- IMPORTANT: include the newly created positions so nested expansions can compute offsets.
              let positionsForNested := mergePositions origPositions newPositions
              let (expandedCmds, finalNextId, extraPositions) :=
                expandChildren parsedCmds filename newNextId positionsForNested
              let allPositions := mergePositions newPositions extraPositions
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
  | .T_Array elems =>
      let (expanded, newNextId, positions) := expandChildren elems filename nextId origPositions
      (⟨t.id, .T_Array expanded⟩, newNextId, positions)
  | .T_FdRedirect fd redir =>
      let (expandedRedir, newNextId, positions) := expandDollarExpansions redir filename nextId origPositions
      (⟨t.id, .T_FdRedirect fd expandedRedir⟩, newNextId, positions)
  | .T_IoFile op file =>
      let (expandedOp, nid1, pos1) := expandDollarExpansions op filename nextId origPositions
      let (expandedFile, nid2, pos2) := expandDollarExpansions file filename nid1 origPositions
      (⟨t.id, .T_IoFile expandedOp expandedFile⟩, nid2, mergePositions pos1 pos2)
  | .T_IoDuplicate op fd =>
      let (expandedOp, newNextId, positions) := expandDollarExpansions op filename nextId origPositions
      (⟨t.id, .T_IoDuplicate expandedOp fd⟩, newNextId, positions)
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
              -- Recursively expand any nested $() in the parsed commands.
              -- IMPORTANT: include the newly created positions so nested expansions can compute offsets.
              let positionsForNested := mergePositions origPositions newPositions
              let (expandedCmds, finalNextId, extraPositions) :=
                expandChildren parsedCmds filename newNextId positionsForNested
              let allPositions := mergePositions newPositions extraPositions
              (⟨t.id, .T_Backticked expandedCmds⟩, finalNextId, allPositions)
          | _ =>
              let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
              (⟨t.id, .T_Backticked expanded⟩, newNextId, positions)
      | _ =>
          let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
          (⟨t.id, .T_Backticked expanded⟩, newNextId, positions)
  | .T_ProcSub dir cmds =>
      match cmds with
      | [child] =>
          match child.inner with
          | .T_Literal content =>
              -- Unparsed procsub content - parse it like $().
              let (offsetLine, offsetCol) := match origPositions.get? t.id with
                | some (startPos, _) => (startPos.posLine, startPos.posColumn + 2)  -- +2 for "<(" or ">("
                | none => (1, 1)  -- Fallback
              let (parsedCmds, newNextId, newPositions) := parseSubshellContent content filename nextId offsetLine offsetCol
              let positionsForNested := mergePositions origPositions newPositions
              let (expandedCmds, finalNextId, extraPositions) :=
                expandChildren parsedCmds filename newNextId positionsForNested
              let allPositions := mergePositions newPositions extraPositions
              (⟨t.id, .T_ProcSub dir expandedCmds⟩, finalNextId, allPositions)
          | _ =>
              let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
              (⟨t.id, .T_ProcSub dir expanded⟩, newNextId, positions)
      | _ =>
          let (expanded, newNextId, positions) := expandChildren cmds filename nextId origPositions
          (⟨t.id, .T_ProcSub dir expanded⟩, newNextId, positions)
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
  mergePositions (base extra : Std.HashMap Id (Position × Position)) : Std.HashMap Id (Position × Position) :=
    extra.fold (init := base) fun m k v => m.insert k v

  expandChildren (children : List Token) (filename : String) (nextId : Nat) (origPos : Std.HashMap Id (Position × Position)) : (List Token × Nat × Std.HashMap Id (Position × Position)) :=
    children.foldl (init := ([], nextId, {})) fun (acc, nid, pos) child =>
      let (expanded, newNid, newPos) := expandDollarExpansions child filename nid origPos
      (acc ++ [expanded], newNid, pos.fold (init := newPos) fun m k v => m.insert k v)

/-- Run the shell parser on a script -/
def runParser (script : String) (filename : String := "<stdin>") : (Option Token × Std.HashMap Id (Position × Position) × List String) :=
  let it := ShellCheck.Parser.Parsec.PosIterator.create script
  let initState : ParserState := ShellCheck.Parser.Parsec.mkParserState filename
  match readScript initState it with
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

set_option maxRecDepth 2048

/-- Infer SC code from error message patterns -/
def inferSCCode (msg : String) : Nat × Severity :=
  -- SC1000: $ not special
  if contains msg "$" && contains msg "not" && contains msg "special" then (1000, .errorC)
  else if contains msg "$" && contains msg "escape" && contains msg "should" then (1000, .errorC)
  -- Escaping errors (SC1001-SC1006, SC1012-SC1013, SC1117)
  else if contains msg "backslash" && contains msg "regular" then (1001, .infoC)
  else if contains msg "backslash" && contains msg "literal" && !contains msg "comment" then (1001, .infoC)
  else if contains msg "\\o" && contains msg "context" then (1001, .infoC)
  else if contains msg "useless escape" then (1001, .infoC)
  else if contains msg "unnecessary backslash" then (1001, .infoC)
  else if contains msg "$\\" && contains msg "command substitution" then (1002, .errorC)
  else if contains msg "backslash" && contains msg "$(" then (1002, .errorC)
  else if contains msg "escape" && contains msg "single quote" then (1003, .errorC)
  else if contains msg "how it" && contains msg "done" && contains msg "'" then (1003, .errorC)
  else if contains msg "can't escape" && contains msg "single" then (1003, .errorC)
  else if contains msg "end the string" && contains msg "'" then (1003, .errorC)
  else if contains msg "backslash" && contains msg "linefeed" then (1004, .warningC)
  else if contains msg "backslash" && contains msg "newline" then (1004, .warningC)
  else if contains msg "break outside" && contains msg "single quote" then (1004, .warningC)
  else if contains msg "line continuation" && contains msg "single" then (1004, .warningC)
  else if contains msg "closing paren" && contains msg "arithmetic" then (1005, .errorC)
  else if contains msg "expected" && contains msg "))" then (1005, .errorC)
  else if contains msg "missing ))" then (1005, .errorC)
  else if contains msg "unmatched ((" then (1005, .errorC)
  else if contains msg "glob" && contains msg "pattern" then (1006, .errorC)
  else if contains msg "quote to prevent" && contains msg "glob" then (1006, .errorC)
  else if contains msg "\\t" && contains msg "literal" then (1012, .warningC)
  else if contains msg "printf" && contains msg "tab" then (1012, .warningC)
  else if contains msg "$'\\t'" && contains msg "literal tab" then (1012, .warningC)
  else if contains msg "escaped newline" && contains msg "double quote" then (1013, .warningC)
  else if contains msg "\\n" && contains msg "doesn't mean" then (1013, .warningC)
  else if contains msg "\\n" && contains msg "literal" then (1117, .infoC)
  else if contains msg "prefer explicit" && contains msg "escaping" then (1117, .infoC)
  else if contains msg "$'\\n'" && contains msg "newline" then (1117, .infoC)
  -- Whitespace errors (SC1007, SC1017-SC1027, SC1035, SC1054, SC1068-SC1069, SC1095, SC1099, SC1101, SC1108, SC1114-SC1115, SC1118, SC1129-SC1130)
  else if contains msg "space after =" then (1007, .errorC)
  else if contains msg "remove space" && contains msg "=" then (1007, .errorC)
  else if contains msg "empty string" && contains msg "var=''" then (1007, .errorC)
  else if contains msg "no space before =" then (1007, .errorC)
  else if contains msg "var=" && contains msg "empty" && contains msg "space" then (1007, .errorC)
  else if contains msg "carriage return" then (1017, .errorC)
  else if contains msg "tr -d" && contains msg "\\r" then (1017, .errorC)
  else if contains msg "\\r" && contains msg "windows" then (1017, .errorC)
  else if contains msg "dos2unix" then (1017, .errorC)
  else if contains msg "non-breaking space" || contains msg "nbsp" then (1018, .errorC)
  else if contains msg "unicode" && contains msg "space" && contains msg "delete" then (1018, .errorC)
  else if contains msg "\\u00a0" && contains msg "space" then (1018, .errorC)
  else if contains msg "space before the ]" || contains msg "space before ]" then (1020, .errorC)
  else if contains msg "need a space" && contains msg "]" then (1020, .errorC)
  else if contains msg "missing space" && contains msg "[" && contains msg "]" then (1020, .errorC)
  else if contains msg "can't have a space" && contains msg "]" then (1021, .errorC)
  else if contains msg "extra space" && contains msg "]]" then (1021, .errorC)
  else if contains msg "don't put spaces before" && contains msg "bracket" then (1022, .errorC)
  else if contains msg "space after" && contains msg "redirection" then (1023, .errorC)
  else if contains msg "no space after" && contains msg ">" then (1023, .errorC)
  else if contains msg "space before" && contains msg "here-doc" && contains msg "marker" then (1024, .errorC)
  else if contains msg "<<" && contains msg "space" && contains msg "before" then (1024, .errorC)
  else if contains msg "single quotes" && contains msg "literal" && contains msg "string" then (1025, .errorC)
  else if contains msg "missing argument" && contains msg "operator" then (1027, .errorC)
  else if contains msg "expected" && contains msg "term" && contains msg "after" then (1027, .errorC)
  else if contains msg "operator" && contains msg "requires" && contains msg "argument" then (1027, .errorC)
  else if contains msg "space after" && contains msg "{" then (1054, .errorC)
  else if contains msg "{ needs space" then (1054, .errorC)
  else if contains msg "spaces around the =" || (contains msg "don't put spaces" && contains msg "=") then (1068, .errorC)
  else if contains msg "no spaces" && contains msg "=" && contains msg "assignment" then (1068, .errorC)
  else if contains msg "var = value" && contains msg "wrong" then (1068, .errorC)
  else if contains msg "space before" && contains msg "[" && !contains msg "]]" then (1069, .errorC)
  else if contains msg "need space" && contains msg "before [" then (1069, .errorC)
  else if contains msg "space" && contains msg "function" && contains msg "body" then (1095, .errorC)
  else if contains msg "linefeed" && contains msg "function" && contains msg "name" then (1095, .errorC)
  else if contains msg "function" && contains msg "()" && contains msg "space" then (1095, .errorC)
  else if contains msg "space before the #" then (1099, .errorC)
  else if contains msg "space before" && contains msg "comment" then (1099, .errorC)
  else if contains msg "# comment" && contains msg "needs space" then (1099, .errorC)
  else if contains msg "trailing space" && contains msg "\\" then (1101, .errorC)
  else if contains msg "delete" && contains msg "space" && contains msg "after \\" then (1101, .errorC)
  else if contains msg "line continuation" && contains msg "trailing space" then (1101, .errorC)
  else if contains msg "space before and after" && contains msg "=" then (1108, .errorC)
  else if contains msg "leading space" && contains msg "shebang" then (1114, .errorC)
  else if contains msg "remove" && contains msg "space" && contains msg "before shebang" then (1114, .errorC)
  else if contains msg "shebang" && contains msg "indented" then (1114, .errorC)
  else if contains msg "space" && contains msg "#" && contains msg "!" && contains msg "between" then (1115, .errorC)
  else if contains msg "# !" && contains msg "shebang" then (1115, .errorC)
  else if contains msg "whitespace" && contains msg "here-doc" && contains msg "end" then (1118, .errorC)
  else if contains msg "delete" && contains msg "whitespace" && contains msg "after" then (1118, .errorC)
  else if contains msg "heredoc end" && contains msg "whitespace" then (1118, .errorC)
  else if contains msg "space before the !" then (1129, .errorC)
  else if contains msg "! negation" && contains msg "space" then (1129, .errorC)
  else if contains msg "space before the :" then (1130, .errorC)
  else if contains msg ": builtin" && contains msg "space" then (1130, .errorC)
  -- Quoting errors (SC1011, SC1015-SC1016, SC1078-SC1079, SC1110-SC1112)
  else if contains msg "apostrophe" && contains msg "terminated" then (1011, .errorC)
  else if contains msg "single quoted" && contains msg "string" && contains msg "ended" then (1011, .errorC)
  else if contains msg "unterminated" && contains msg "single" && contains msg "quote" then (1011, .errorC)
  else if contains msg "'" && contains msg "unclosed" then (1011, .errorC)
  else if contains msg "unicode" && contains msg "double quote" then (1015, .errorC)
  else if contains msg "curly" && contains msg "quote" then (1015, .errorC)
  else if contains msg "retype" && contains msg "double quote" then (1015, .errorC)
  else if contains msg "smart quote" && contains msg "double" then (1015, .errorC)
  else if contains msg "replace" && contains msg "double" && contains msg "quote" then (1015, .errorC)
  else if contains msg "unicode" && contains msg "single quote" then (1016, .errorC)
  else if contains msg "retype" && contains msg "single quote" then (1016, .errorC)
  else if contains msg "smart quote" && contains msg "single" then (1016, .errorC)
  else if contains msg "replace" && contains msg "single" && contains msg "quote" then (1016, .errorC)
  else if contains msg "close" && contains msg "double quote" then (1078, .errorC)
  else if contains msg "unclosed" && contains msg "quote" then (1078, .errorC)
  else if contains msg "forget" && contains msg "close" && contains msg "quote" then (1078, .errorC)
  else if contains msg "unterminated" && contains msg "double" && contains msg "quote" then (1078, .errorC)
  else if contains msg "\"" && contains msg "never closed" then (1078, .errorC)
  else if contains msg "end quote" && contains msg "suspect" then (1079, .warningC)
  else if contains msg "next char" && contains msg "quote" then (1079, .warningC)
  else if contains msg "quote" && contains msg "looks wrong" then (1079, .warningC)
  else if contains msg "unicode quote" && contains msg "delete" then (1110, .errorC)
  else if contains msg "unicode quote" && contains msg "retype" then (1110, .errorC)
  else if contains msg "fancy quote" then (1110, .errorC)
  else if contains msg "unicode quote" && contains msg "single-quote" then (1111, .errorC)
  else if contains msg "unicode quote" && contains msg "double-quote" then (1112, .errorC)
  else if contains msg "unicode quote" then (1110, .errorC)
  -- Test bracket errors (SC1019, SC1026, SC1028-SC1034, SC1080, SC1106, SC1139-SC1140)
  else if contains msg "unary condition" then (1019, .errorC)
  else if contains msg "expected" && contains msg "argument" && contains msg "unary" then (1019, .errorC)
  else if contains msg "-z" && contains msg "requires" && contains msg "argument" then (1019, .errorC)
  else if contains msg "-n" && contains msg "requires" && contains msg "argument" then (1019, .errorC)
  else if contains msg "grouping" && contains msg "[[" then (1026, .errorC)
  else if contains msg "( .. )" && contains msg "[[" then (1026, .errorC)
  else if contains msg "use &&" && contains msg "||" && contains msg "[[" then (1026, .errorC)
  else if contains msg "escape" && contains msg "\\(" && contains msg "[" then (1028, .errorC)
  else if contains msg "combine expression" && contains msg "[" then (1028, .errorC)
  else if contains msg "\\(" && contains msg "test" && contains msg "[" then (1028, .errorC)
  else if contains msg "shouldn't escape" && contains msg "[[" then (1029, .warningC)
  else if contains msg "don't escape" && contains msg "[[" then (1029, .warningC)
  else if contains msg "no need to escape" && contains msg "[[" then (1029, .warningC)
  else if contains msg "expected" && contains msg "condition" && contains msg "test" then (1030, .errorC)
  else if contains msg "[ ]" && contains msg "no condition" then (1030, .errorC)
  else if contains msg "empty string" && contains msg "-eq" then (1031, .errorC)
  else if contains msg "-z" && contains msg "empty" then (1031, .errorC)
  else if contains msg "use -z" && contains msg "empty string" then (1031, .errorC)
  else if contains msg ">" && contains msg "redirection" && contains msg "comparison" then (1032, .errorC)
  else if contains msg "\\>" && contains msg "test" then (1032, .errorC)
  else if contains msg "comparison" && contains msg "redirect" && contains msg "escape" then (1032, .errorC)
  else if contains msg "[[" && contains msg "]" && contains msg "match" then (1033, .errorC)
  else if contains msg "opened with [[" && contains msg "closed with ]" then (1033, .errorC)
  else if contains msg "mismatched" && contains msg "[[" && contains msg "]" then (1033, .errorC)
  else if contains msg "[" && contains msg "]]" && contains msg "match" then (1034, .errorC)
  else if contains msg "opened with [" && contains msg "closed with ]]" then (1034, .errorC)
  else if contains msg "mismatched" && contains msg "[" && contains msg "]]" then (1034, .errorC)
  else if contains msg "backslash" && contains msg "line feed" && contains msg "[ ]" then (1080, .warningC)
  else if contains msg "\\\\" && contains msg "line feed" && contains msg "test" then (1080, .warningC)
  else if contains msg "line continuation" && contains msg "[ ]" then (1080, .warningC)
  else if contains msg "arithmetic" && contains msg "-lt" then (1106, .infoC)
  else if contains msg "use <" && contains msg "-lt" then (1106, .infoC)
  else if contains msg "use ((" && contains msg "arithmetic comparison" then (1106, .infoC)
  else if contains msg "-gt" && contains msg "((" then (1106, .infoC)
  else if contains msg "-o" && contains msg "||" then (1139, .errorC)
  else if contains msg "use ||" && contains msg "-o" then (1139, .errorC)
  else if contains msg "-a" && contains msg "&&" && contains msg "[" then (1139, .errorC)
  else if contains msg "after condition" && (contains msg "&&" || contains msg "||") then (1140, .errorC)
  else if contains msg "unexpected parameter" && contains msg "condition" then (1140, .errorC)
  else if contains msg "too many arguments" && contains msg "[" then (1140, .errorC)
  -- Shebang errors (SC1008, SC1071, SC1082, SC1084, SC1104, SC1113, SC1128)
  else if contains msg "bom" || contains msg "byte order mark" then (1082, .errorC)
  else if contains msg "utf-8 bom" then (1082, .errorC)
  else if contains msg "sed" && contains msg "remove" && contains msg "bom" then (1082, .errorC)
  else if contains msg "0xef 0xbb 0xbf" then (1082, .errorC)
  else if contains msg "!#" && contains msg "shebang" then (1084, .errorC)
  else if contains msg "#!" && contains msg "!#" then (1084, .errorC)
  else if contains msg "reversed" && contains msg "shebang" then (1084, .errorC)
  else if contains msg "not just !" && contains msg "shebang" then (1104, .errorC)
  else if contains msg "use #!" && contains msg "!" then (1104, .errorC)
  else if contains msg "incomplete shebang" && contains msg "!" then (1104, .errorC)
  else if contains msg "not just #" && contains msg "shebang" then (1113, .errorC)
  else if contains msg "use #!" && contains msg "#" then (1113, .errorC)
  else if contains msg "incomplete shebang" && contains msg "#" then (1113, .errorC)
  else if contains msg "shebang" && contains msg "first line" then (1128, .errorC)
  else if contains msg "delete blank" && contains msg "shebang" then (1128, .errorC)
  else if contains msg "move comment" && contains msg "shebang" then (1128, .errorC)
  else if contains msg "shebang" && contains msg "not on line 1" then (1128, .errorC)
  else if contains msg "shebang must be" && contains msg "first" then (1128, .errorC)
  else if contains msg "shebang" && contains msg "unrecognized" then (1008, .warningC)
  else if contains msg "add" && contains msg "shell directive" then (1008, .warningC)
  else if contains msg "unknown shell" && contains msg "shebang" then (1008, .warningC)
  else if contains msg "shellcheck" && contains msg "shell=" then (1008, .warningC)
  else if contains msg "only supports" && (contains msg "sh" || contains msg "bash") then (1071, .errorC)
  else if contains msg "only supports" && contains msg "ksh" then (1071, .errorC)
  else if contains msg "only supports" && contains msg "dash" then (1071, .errorC)
  -- Control flow errors (SC1009-SC1010, SC1014, SC1045-SC1063, SC1074-SC1076, SC1085, SC1131)
  else if contains msg "parser error was in" then (1009, .errorC)
  else if contains msg "mentioned" && contains msg "error" then (1009, .errorC)
  else if contains msg "original error" && contains msg "above" then (1009, .errorC)
  else if contains msg "semicolon" && contains msg "before" && contains msg "done" then (1010, .errorC)
  else if contains msg "linefeed" && contains msg "before" && contains msg "done" then (1010, .errorC)
  else if contains msg "quote to make" && contains msg "literal" && contains msg "done" then (1010, .errorC)
  else if contains msg "'done'" && contains msg "keyword" && contains msg "literal" then (1010, .errorC)
  else if contains msg "if cmd; then" || contains msg "check exit code" then (1014, .errorC)
  else if contains msg "check output" && contains msg "if" then (1014, .errorC)
  else if contains msg "use $?" && contains msg "exit code" then (1014, .errorC)
  else if contains msg "&;" then (1045, .errorC)
  else if contains msg "foo &" && contains msg "bar" && contains msg "just" then (1045, .errorC)
  else if contains msg "remove the ;" && contains msg "&" then (1045, .errorC)
  else if contains msg "fi" && contains msg "if" && !contains msg "elif" && contains msg "find" then (1046, .errorC)
  else if contains msg "couldn't find" && contains msg "fi" then (1046, .errorC)
  else if contains msg "missing" && contains msg "fi" then (1046, .errorC)
  else if contains msg "unclosed if" then (1046, .errorC)
  else if contains msg "fi" && contains msg "matching" then (1047, .errorC)
  else if contains msg "expected" && contains msg "fi" then (1047, .errorC)
  else if contains msg "unmatched" && contains msg "fi" then (1047, .errorC)
  else if contains msg "empty" && contains msg "then" && contains msg "clause" then (1048, .errorC)
  else if contains msg "true" && contains msg "no-op" && contains msg "then" then (1048, .errorC)
  else if contains msg "then" && contains msg "body" && contains msg "empty" then (1048, .errorC)
  else if contains msg "forget" && contains msg "then" then (1049, .errorC)
  else if contains msg "missing" && contains msg "then" then (1049, .errorC)
  else if contains msg "if" && contains msg "requires" && contains msg "then" then (1049, .errorC)
  else if contains msg "expected" && contains msg "then" then (1050, .errorC)
  else if contains msg "semicolon" && contains msg "after" && contains msg "then" then (1051, .errorC)
  else if contains msg "remove" && contains msg "semicolon" && contains msg "then" then (1051, .errorC)
  else if contains msg "semicolon" && contains msg "directly after" && contains msg "then" then (1052, .errorC)
  else if contains msg "then;" && contains msg "not allowed" then (1052, .errorC)
  else if contains msg "semicolon" && contains msg "after" && contains msg "else" then (1053, .errorC)
  else if contains msg "remove" && contains msg "semicolon" && contains msg "else" then (1053, .errorC)
  else if contains msg "need at least one" && contains msg "command" then (1055, .errorC)
  else if contains msg "true;" && contains msg "no-op" then (1055, .errorC)
  else if contains msg "missing" && contains msg "do" && contains msg "loop" then (1057, .errorC)
  else if contains msg "expected" && contains msg "do" then (1058, .errorC)
  else if contains msg "semicolon" && contains msg "after" && contains msg "do" then (1059, .errorC)
  else if contains msg "remove" && contains msg "semicolon" && contains msg "do" then (1059, .errorC)
  else if contains msg "empty" && contains msg "do" && contains msg "clause" then (1060, .errorC)
  else if contains msg "true;" && contains msg "no-op" && contains msg "do" then (1060, .errorC)
  else if contains msg "done" && contains msg "do" && contains msg "find" then (1061, .errorC)
  else if contains msg "couldn't find" && contains msg "done" then (1061, .errorC)
  else if contains msg "missing" && contains msg "done" then (1061, .errorC)
  else if contains msg "unclosed" && contains msg "loop" then (1061, .errorC)
  else if contains msg "done" && contains msg "matching" then (1062, .errorC)
  else if contains msg "expected" && contains msg "done" then (1062, .errorC)
  else if contains msg "unmatched" && contains msg "done" then (1062, .errorC)
  else if contains msg "linefeed" && contains msg "before" && contains msg "do" then (1063, .errorC)
  else if contains msg "semicolon" && contains msg "before" && contains msg "do" then (1063, .errorC)
  else if contains msg "for" && contains msg "requires" && contains msg "do" then (1063, .errorC)
  else if contains msg "while" && contains msg "requires" && contains msg "do" then (1063, .errorC)
  else if contains msg ";;" && contains msg "case" && contains msg "forget" then (1074, .errorC)
  else if contains msg ";;" && contains msg "previous" && contains msg "case" then (1074, .errorC)
  else if contains msg "terminate" && contains msg "case" && contains msg ";;" then (1074, .errorC)
  else if contains msg "case branch" && contains msg ";;" then (1074, .errorC)
  else if contains msg "missing" && contains msg ";;" && contains msg "case" then (1074, .errorC)
  else if contains msg "elif" && contains msg "else if" then (1075, .errorC)
  else if contains msg "use" && contains msg "elif" && contains msg "instead" then (1075, .errorC)
  else if contains msg "shell doesn't have" && contains msg "else if" then (1075, .errorC)
  else if contains msg "trying to do math" || (contains msg "math" && contains msg "$((" ) then (1076, .errorC)
  else if contains msg "$((i" && contains msg "-ge" then (1076, .errorC)
  else if contains msg "use ((" && contains msg "arithmetic" && contains msg "if" then (1076, .errorC)
  else if contains msg ";&" && contains msg ";;" then (1085, .errorC)
  else if contains msg ";;&" && contains msg ";;" then (1085, .errorC)
  else if contains msg "extending" && contains msg "case" && contains msg ";;" then (1085, .errorC)
  else if contains msg "fallthrough" && contains msg "case" then (1085, .errorC)
  else if contains msg "case" && contains msg ";&" && contains msg "bash" then (1085, .errorC)
  else if contains msg "missing" && contains msg "'in'" && contains msg "for" then (1079, .errorC)
  else if contains msg "for" && contains msg "in" && contains msg "missing" then (1079, .errorC)
  else if contains msg "case" && contains msg "'in'" && contains msg "missing" then (1072, .errorC)
  else if contains msg "case" && contains msg "pattern" && contains msg ")" then (1072, .errorC)
  else if contains msg "case" && contains msg "pattern" && contains msg "(" then (1072, .errorC)
  else if contains msg "esac" && contains msg "missing" then (1072, .errorC)
  else if contains msg "couldn't find" && contains msg "esac" then (1072, .errorC)
  else if contains msg "unclosed case" then (1072, .errorC)
  else if contains msg "elif" && contains msg "branch" then (1131, .errorC)
  else if contains msg "use" && contains msg "elif" && contains msg "another branch" then (1131, .errorC)
  else if contains msg "else" && contains msg "additional" && contains msg "elif" then (1131, .errorC)
  -- Function errors (SC1064-SC1067, SC1093)
  else if contains msg "{" && contains msg "function" then (1064, .errorC)
  else if contains msg "expected { after" && contains msg "function" then (1064, .errorC)
  else if contains msg "esac" && contains msg "case" then (1064, .errorC)
  else if contains msg "parameter" && contains msg "$1" then (1065, .errorC)
  else if contains msg "use $" && contains msg "function parameter" then (1065, .errorC)
  else if contains msg "function" && contains msg "body" && contains msg "expected" then (1064, .errorC)
  else if contains msg "}" && contains msg "function" && contains msg "missing" then (1064, .errorC)
  else if contains msg "function name" && contains msg "invalid" then (1093, .errorC)
  else if contains msg "function" && contains msg "keyword" && contains msg "expected" then (1093, .errorC)
  -- Variable errors (SC1036-SC1037, SC1053, SC1066-SC1067, SC1086-SC1087, SC1097, SC1103, SC1116, SC1134)
  else if contains msg "(" && contains msg "invalid" then (1036, .errorC)
  else if contains msg "(" && contains msg "expected" && contains msg "variable" then (1036, .errorC)
  else if contains msg "invalid variable" && contains msg "(" then (1036, .errorC)
  else if contains msg "brace" && contains msg "positional" then (1037, .errorC)
  else if contains msg "${" && contains msg "digit" then (1037, .errorC)
  else if contains msg "use ${10}" && contains msg "positional" then (1037, .errorC)
  else if contains msg "keyword" && contains msg "variable" then (1053, .errorC)
  else if contains msg "reserved" && contains msg "variable name" then (1053, .errorC)
  else if contains msg "$" && contains msg "left side" then (1066, .errorC)
  else if contains msg "don't use $" && contains msg "=" then (1066, .errorC)
  else if contains msg "no $ on" && contains msg "left" then (1066, .errorC)
  else if contains msg "indirection" && contains msg "array" then (1067, .errorC)
  else if contains msg "${!" && contains msg "[@]" then (1067, .errorC)
  else if contains msg "$" && contains msg "iterator" && contains msg "for" then (1086, .errorC)
  else if contains msg "remove the $" && contains msg "for" then (1086, .errorC)
  else if contains msg "brace" && contains msg "array" then (1087, .errorC)
  else if contains msg "${arr[@]}" && contains msg "brace" then (1087, .errorC)
  else if contains msg "==" && contains msg "assignment" then (1097, .errorC)
  else if contains msg "use =" && contains msg "not ==" then (1097, .errorC)
  else if contains msg "unexpected" && contains msg "]" && contains msg "arithmetic" then (1103, .errorC)
  else if contains msg "arithmetic" && contains msg "]" && contains msg "not array" then (1103, .errorC)
  else if contains msg "missing $" && contains msg "((" then (1116, .errorC)
  else if contains msg "use $" && contains msg "((" && contains msg "assign" then (1116, .errorC)
  else if contains msg "internal" && contains msg "variable" && contains msg "prefix" then (1134, .errorC)
  else if contains msg "_" && contains msg "underscore" && contains msg "internal" then (1134, .errorC)
  -- Here-doc errors (SC1038-SC1044, SC1119-SC1122)
  else if contains msg "< <(" || contains msg "space sensitive" then (1038, .errorC)
  else if contains msg "process substitution" && contains msg "space" then (1038, .errorC)
  else if contains msg "<<" && contains msg "< <" then (1038, .errorC)
  else if contains msg "indent" && contains msg "end token" then (1039, .errorC)
  else if contains msg "<<-" && contains msg "indent" then (1039, .errorC)
  else if contains msg "heredoc" && contains msg "tabs only" then (1039, .errorC)
  else if contains msg "<<-" && contains msg "tab" then (1040, .errorC)
  else if contains msg "<<-" && contains msg "indent with tabs" then (1040, .errorC)
  else if contains msg "eof" && contains msg "separate line" then (1041, .errorC)
  else if contains msg "end token" && contains msg "own line" then (1041, .errorC)
  else if contains msg "EOF" && contains msg "start of line" then (1041, .errorC)
  else if contains msg "close match" && contains msg "eof" then (1042, .warningC)
  else if contains msg "similar to" && contains msg "end token" then (1042, .warningC)
  else if contains msg "casing" && contains msg "end token" then (1043, .errorC)
  else if contains msg "eof" && contains msg "EOF" && contains msg "casing" then (1043, .errorC)
  else if contains msg "case sensitive" && contains msg "heredoc" then (1043, .errorC)
  else if contains msg "end token" && contains msg "here" then (1044, .errorC)
  else if contains msg "couldn't find" && contains msg "here" then (1044, .errorC)
  else if contains msg "unterminated" && contains msg "heredoc" then (1044, .errorC)
  else if contains msg "heredoc" && contains msg "unclosed" then (1044, .errorC)
  else if contains msg "linefeed" && contains msg "end token" && contains msg ")" then (1119, .errorC)
  else if contains msg ")" && contains msg "heredoc" && contains msg "end" then (1119, .errorC)
  else if contains msg "comment" && contains msg "here-doc" then (1120, .errorC)
  else if contains msg "comment" && contains msg "heredoc" && contains msg "after" then (1120, .errorC)
  else if contains msg "terminator" && contains msg "<<" then (1121, .errorC)
  else if contains msg "heredoc" && contains msg "terminator" && contains msg "expected" then (1121, .errorC)
  else if contains msg "after end token" then (1122, .errorC)
  else if contains msg "text after" && contains msg "heredoc end" then (1122, .errorC)
  -- Sourcing errors (SC1090-SC1092, SC1094)
  else if contains msg "non-constant" && contains msg "source" then (1090, .warningC)
  else if contains msg "can't follow" && contains msg "dynamic" then (1090, .warningC)
  else if contains msg "shellcheck -x" && contains msg "follow" then (1090, .warningC)
  else if contains msg "not following" then (1091, .infoC)
  else if contains msg "source" && contains msg "specify" && contains msg "-x" then (1091, .infoC)
  else if contains msg "100" && contains msg "source" && contains msg "frame" then (1092, .warningC)
  else if contains msg "stopping" && contains msg "source" then (1092, .warningC)
  else if contains msg "recursive" && contains msg "source" then (1092, .warningC)
  else if contains msg "source" && contains msg "depth" && contains msg "limit" then (1092, .warningC)
  else if contains msg "sourced file" && contains msg "failed" then (1094, .warningC)
  else if contains msg "could not" && contains msg "source" && contains msg "file" then (1094, .warningC)
  else if contains msg "source" && contains msg "file" && contains msg "not found" then (1094, .warningC)
  -- Arithmetic errors (SC1102-SC1105, SC1137-SC1138)
  else if contains msg "missing" && contains msg "(" && contains msg "((" && contains msg "loop" then (1137, .errorC)
  else if contains msg "second" && contains msg "(" && contains msg "arithmetic" then (1137, .errorC)
  else if contains msg "(( ;; ))" && contains msg "loop" then (1137, .errorC)
  else if contains msg "space" && contains msg "((" && contains msg "arithmetic" then (1138, .errorC)
  else if contains msg "remove space" && contains msg "((" then (1138, .errorC)
  else if contains msg "( (" && contains msg "remove space" then (1138, .errorC)
  else if contains msg "disambiguate" && contains msg "$((" then (1102, .errorC)
  else if contains msg "$( (" && contains msg "command substitution" then (1102, .errorC)
  else if contains msg "confuse" && contains msg "$((" then (1102, .errorC)
  else if contains msg "disambiguate" && contains msg "((" then (1105, .errorC)
  else if contains msg "avoid confusion" && contains msg "((" then (1105, .errorC)
  -- Syntax errors (SC1056, SC1059, SC1070, SC1077, SC1081, SC1083, SC1088-SC1089, SC1098, SC1132-SC1133, SC1136, SC1141-SC1143)
  else if contains msg "expected" && contains msg "}" then (1056, .errorC)
  else if contains msg "unmatched" && contains msg "{" then (1056, .errorC)
  else if contains msg "missing" && contains msg "}" then (1056, .errorC)
  else if contains msg "extglob" || contains msg "extended glob" then (1059, .warningC)
  else if contains msg "shopt" && contains msg "extglob" then (1059, .warningC)
  else if contains msg "+(" && contains msg "extglob" then (1059, .warningC)
  else if contains msg "parsing stopped" && contains msg "parentheses" then (1088, .errorC)
  else if contains msg "unbalanced" && contains msg "(" then (1088, .errorC)
  else if contains msg "parsing stopped" && contains msg "keyword" then (1089, .errorC)
  else if contains msg "invalid keyword" && contains msg "parsing" then (1089, .errorC)
  else if contains msg "parsing stopped" then (1070, .errorC)
  else if contains msg "parser gave up" then (1070, .errorC)
  else if contains msg "could not parse" then (1070, .errorC)
  else if contains msg "tick" && contains msg "slant" then (1077, .errorC)
  else if contains msg "backtick" && contains msg "accent" then (1077, .errorC)
  else if contains msg "case sensitive" then (1081, .errorC)
  else if contains msg "keyword" && contains msg "case" && contains msg "upper" then (1081, .errorC)
  else if (contains msg "{" || contains msg "}") && contains msg "literal" then (1083, .errorC)
  else if contains msg "escape" && contains msg "{" && contains msg "literal" then (1083, .errorC)
  else if contains msg "quote" && contains msg "{" && contains msg "literal" then (1083, .errorC)
  else if contains msg "eval" && (contains msg "escape" || contains msg "quote") then (1098, .errorC)
  else if contains msg "trap" && contains msg "escape" then (1098, .errorC)
  else if contains msg "&" && contains msg "terminate" then (1132, .errorC)
  else if contains msg "&" && contains msg "separate" && contains msg "command" then (1132, .errorC)
  else if contains msg "background" && contains msg "&" && contains msg "need" then (1132, .errorC)
  else if contains msg "start of line" && (contains msg "|" || contains msg "&&") then (1133, .errorC)
  else if contains msg "end previous line" && contains msg "|" then (1133, .errorC)
  else if contains msg "line continuation" && contains msg "|" then (1133, .errorC)
  else if contains msg "pipe" && contains msg "start" && contains msg "line" then (1133, .errorC)
  else if contains msg "||" && contains msg "beginning" && contains msg "line" then (1133, .errorC)
  else if contains msg "after" && contains msg "]" && contains msg "semicolon" then (1136, .errorC)
  else if contains msg "];" && contains msg "needed" then (1136, .errorC)
  else if contains msg "[ ]" && contains msg ";" && contains msg "after" then (1136, .errorC)
  else if contains msg "after compound" && contains msg "redirection" then (1141, .errorC)
  else if contains msg ">" && contains msg "after" && contains msg ")" then (1141, .errorC)
  else if contains msg "redirect" && contains msg "after" && contains msg "compound" then (1141, .errorC)
  else if contains msg "process substitution" && contains msg "redirect" then (1142, .errorC)
  else if contains msg "<(" && contains msg "redirection" then (1142, .errorC)
  else if contains msg ">(" && contains msg "process" then (1142, .errorC)
  else if contains msg "backslash" && contains msg "comment" then (1143, .infoC)
  else if contains msg "\\" && contains msg "before #" then (1143, .infoC)
  else if contains msg "escaped" && contains msg "#" && contains msg "not needed" then (1143, .infoC)
  -- Unicode errors (SC1100, SC1109)
  else if contains msg "unicode dash" then (1100, .errorC)
  else if contains msg "em dash" || contains msg "en dash" then (1100, .errorC)
  else if contains msg "−" && contains msg "ascii" then (1100, .errorC)
  else if contains msg "html entity" then (1109, .errorC)
  else if contains msg "&amp;" || contains msg "&lt;" || contains msg "&gt;" then (1109, .errorC)
  else if contains msg "decode" && contains msg "html" then (1109, .errorC)
  else if contains msg "unicode" && !contains msg "quote" && !contains msg "dash" && !contains msg "space" then (1015, .errorC)
  -- Directive errors (SC1107, SC1123-SC1127, SC1135, SC1144-SC1145)
  else if contains msg "directive" && contains msg "unknown" then (1107, .warningC)
  else if contains msg "shellcheck" && contains msg "unrecognized" && contains msg "directive" then (1107, .warningC)
  else if contains msg "directive" && contains msg "compound" then (1123, .errorC)
  else if contains msg "shellcheck directive" && contains msg "before compound" then (1123, .errorC)
  else if contains msg "directive" && contains msg "branch" then (1124, .errorC)
  else if contains msg "shellcheck directive" && contains msg "every branch" then (1124, .errorC)
  else if contains msg "key=value" && contains msg "directive" then (1125, .errorC)
  else if contains msg "directive" && contains msg "syntax" && contains msg "key" then (1125, .errorC)
  else if contains msg "directive" && contains msg "before" then (1126, .errorC)
  else if contains msg "shellcheck" && contains msg "directive" && contains msg "no effect" then (1126, .errorC)
  else if contains msg "intended" && contains msg "comment" then (1127, .errorC)
  else if contains msg "shellcheck" && contains msg "looks like" && contains msg "comment" then (1127, .errorC)
  else if contains msg "escape" && contains msg "$" && contains msg "literal" then (1135, .infoC)
  else if contains msg "prefer" && contains msg "\\$" && contains msg "literal" then (1135, .infoC)
  else if contains msg "external-sources" && contains msg "shellcheckrc" then (1144, .errorC)
  else if contains msg "external-sources" && contains msg ".shellcheckrc" then (1144, .errorC)
  else if contains msg "external-sources" && (contains msg "true" || contains msg "false") then (1145, .errorC)
  else if contains msg "external-sources" && contains msg "invalid value" then (1145, .errorC)
  -- Additional SC1xxx codes
  else if contains msg "array" && contains msg "assign" && contains msg "declare" then (1146, .errorC)
  else if contains msg "array reference" && contains msg "brace" then (1087, .errorC)
  else if contains msg "subshell" && contains msg "group" then (1088, .errorC)
  else if contains msg "command group" && contains msg "{" then (1083, .errorC)
  else if contains msg "read" && contains msg "-p" && contains msg "prompt" then (1097, .styleC)
  else if contains msg "glob" && contains msg "pattern" && contains msg "quote" then (1006, .errorC)
  else if contains msg "regex" && contains msg "quote" && contains msg "=~" then (1011, .warningC)
  else if contains msg "test" && contains msg "==" && contains msg "=" then (1106, .styleC)
  else if contains msg "printf" && contains msg "format" && contains msg "escape" then (1117, .infoC)
  else if contains msg "echo -n" && contains msg "printf" then (1117, .infoC)
  else if contains msg "seq" && contains msg "{..}" then (1059, .styleC)
  -- Generic fallbacks
  else if contains msg "space" && (contains msg "error" || contains msg "wrong" || contains msg "unexpected") then (1035, .errorC)
  else if contains msg "unexpected" && contains msg "token" then (1072, .errorC)
  else if contains msg "unexpected" then (1072, .errorC)
  else if contains msg "couldn't parse" || contains msg "couldn't find" then (1073, .errorC)
  else if contains msg "syntax error" then (1072, .errorC)
  else if contains msg "expected" && (contains msg "expression" || contains msg "statement") then (1072, .errorC)
  else if contains msg "invalid" && contains msg "syntax" then (1072, .errorC)
  else if contains msg "expected" || contains msg "invalid" || contains msg "missing" then (1072, .errorC)
  -- Default
  else (0, .errorC)

private structure ScanIssue where
  line : Nat
  col : Nat
  code : Nat
  deriving Repr

private def mkParserComment (filename : String) (issue : ScanIssue) : PositionedComment :=
  let pos : Position := { posFile := filename, posLine := issue.line, posColumn := issue.col }
  let comment :=
    match ShellCheck.Checks.ParserErrors.lookup issue.code with
    | some pe => { cSeverity := pe.severity, cCode := pe.code, cMessage := pe.message }
    | none => { cSeverity := .errorC, cCode := issue.code, cMessage := s!"SC{issue.code}" }
  { pcStartPos := pos, pcEndPos := pos, pcComment := comment, pcFix := none }

private def scanScriptDiagnostics (script : String) (filename : String) : List PositionedComment :=
  let chars := script.toList
  let rec skipSpaces : List Char → (Nat × List Char)
    | [] => (0, [])
    | c :: rest =>
        if c == ' ' || c == '\t' then
          let (n, tail) := skipSpaces rest
          (n + 1, tail)
        else
          (0, c :: rest)
  let rec go (cs : List Char) (line col idx : Nat) (acc : List ScanIssue) : List ScanIssue :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
        let isBom := idx == 0 && (c.toNat == 0xFEFF || c.toNat == 0xFFFE)
        let acc :=
          if isBom then
            { line := line, col := col, code := 1082 } :: acc
          else acc
        let acc :=
          if c == '\r' then
            { line := line, col := col, code := 1017 } :: acc
          else acc
        let acc :=
          if !isBom && ShellCheck.Parser.Diagnostics.isNonBreakingSpace c then
            { line := line, col := col, code := 1018 } :: acc
          else acc
        let acc :=
          if ShellCheck.Parser.Diagnostics.isSmartQuote c then
            { line := line, col := col, code := 1110 } :: acc
          else acc
        let acc :=
          if ShellCheck.Parser.Diagnostics.isSmartDash c then
            { line := line, col := col, code := 1100 } :: acc
          else acc
        let acc :=
          if c == '\\' then
            let (nSpaces, tail) := skipSpaces rest
            match tail with
            | '\n' :: _ =>
                if nSpaces > 0 then
                  { line := line, col := col, code := 1101 } :: acc
                else acc
            | _ => acc
          else acc
        let (line', col') :=
          if c == '\n' then
            (line + 1, 1)
          else
            (line, col + 1)
        go rest line' col' (idx + 1) acc
  let issues := go chars 1 1 0 []
  issues.map (mkParserComment filename)

/-- Enhanced parseScript using parser -/
def parseScript [Monad m] (_sys : SystemInterface m) (spec : ParseSpec) : m ParseResult := do
  let (root, positions, errors) := runParser spec.psScript spec.psFilename
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
          match (trimAsciiString lineStr).toNat?, (trimAsciiString colStr).toNat? with
          | some line, some col =>
              let message := trimAsciiString (String.intercalate ":" rest)
              mkAt file line col message
          | _, _ =>
              mkAt spec.psFilename 1 1 msg
      | _ =>
          mkAt spec.psFilename 1 1 msg
  let scanErrors := scanScriptDiagnostics spec.psScript spec.psFilename
  let scanFiltered :=
    scanErrors.filter fun sc =>
      !parseErrors.any (fun pe =>
        pe.pcComment.cCode == sc.pcComment.cCode &&
          pe.pcStartPos == sc.pcStartPos)
  pure {
    prComments := parseErrors ++ scanFiltered
    prTokenPositions := positions
    prRoot := root
  }

end Parser

end ShellCheck.Parser
