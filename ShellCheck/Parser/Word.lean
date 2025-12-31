/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Word parsing: literals, quotes, dollar expansions
-/

import ShellCheck.AST
import ShellCheck.Parser.Arithmetic
import ShellCheck.Parser.Core
import ShellCheck.Parser.Expansion
import ShellCheck.Parser.Lexer

namespace ShellCheck.Parser.Word

open ShellCheck.AST
open ShellCheck.Interface
open ShellCheck.Parser.Core
open ShellCheck.Parser.Expansion
open ShellCheck.Parser.Lexer

/-!
Word parsing helpers for the shell parser.

These functions are used by the grammar in `ShellCheck/Parser.lean` and are
intended to be the single source of truth for word parsing during the Parsec
migration.
-/

/-- Read a literal word part -/
def readLiteral : Parser Token := do
  let (startLine, startCol) ← currentPos
  let content ← takeWhile1 fun c =>
    ¬ (c.isWhitespace ||
       c == '"' || c == '\'' || c == '`' ||
       c == '$' || c == '\\' ||
       c == '|' || c == '&' || c == ';' ||
       c == '<' || c == '>' ||
       c == '(' || c == ')' ||
       c == '#')
       -- Note: { and } are allowed in word literals for brace expansion
  mkTokenAt (.T_Literal content) startLine startCol

/-- Read a single-quoted string -/
def readSingleQuoted : Parser Token := do
  let (startLine, startCol) ← currentPos
  let _ ← char '\''
  let content ← takeWhile (· != '\'')
  let _ ← char '\''
  mkTokenAt (.T_SingleQuoted content) startLine startCol

/-- Read backtick content until the next *unescaped* backtick, respecting quotes. -/
partial def readBacktickContent : Parser String := do
  let rec go (acc : List Char) (inSingle inDouble escaped : Bool) : Parser String := do
    match ← peek? with
    | none => pure (String.ofList acc.reverse)
    | some c =>
        if escaped then
          let _ ← anyChar
          go (c :: acc) inSingle inDouble false
        else if inSingle then
          let _ ← anyChar
          if c == '\'' then
            go (c :: acc) false inDouble false
          else
            go (c :: acc) true inDouble false
        else if inDouble then
          if c == '\\' then
            let _ ← anyChar
            go ('\\' :: acc) false true true
          else
            let _ ← anyChar
            if c == '"' then
              go (c :: acc) false false false
            else
              go (c :: acc) false true false
        else if c == '\\' then
          let _ ← anyChar
          go ('\\' :: acc) false false true
        else if c == '\'' then
          let _ ← anyChar
          go (c :: acc) true false false
        else if c == '"' then
          let _ ← anyChar
          go (c :: acc) false true false
        else if c == '`' then
          pure (String.ofList acc.reverse)
        else
          let _ ← anyChar
          go (c :: acc) false false false
  go [] false false false

/-- Read a backtick command substitution -/
partial def readBacktick : Parser Token := do
  let (startLine, startCol) ← currentPos
  let _ ← char '`'
  let (contentStartLine, contentStartCol) ← currentPos
  let content ← readBacktickContent
  let inner ← mkTokenAt (.T_Literal content) contentStartLine contentStartCol
  let _ ← char '`'
  mkTokenAt (.T_Backticked [inner]) startLine startCol

/-- Helper to read until a terminator string -/
partial def readUntilStr (terminator : String) : Parser String := do
  -- Important: must not consume the terminator.
  let rec go (acc : List Char) (depth : Nat) (inSingle inDouble inBacktick escaped : Bool) : Parser String := do
    match ← peek? with
    | none => pure (String.ofList acc.reverse)
    | some c =>
        if escaped then
          let _ ← anyChar
          go (c :: acc) depth inSingle inDouble inBacktick false
        else if inSingle then
          let _ ← anyChar
          if c == '\'' then
            go (c :: acc) depth false inDouble inBacktick false
          else
            go (c :: acc) depth true inDouble inBacktick false
        else if inDouble then
          if c == '\\' then
            let _ ← anyChar
            go ('\\' :: acc) depth false true inBacktick true
          else
            let _ ← anyChar
            if c == '"' then
              go (c :: acc) depth false false inBacktick false
            else
              go (c :: acc) depth false true inBacktick false
        else if inBacktick then
          if c == '\\' then
            let _ ← anyChar
            go ('\\' :: acc) depth false false true true
          else
            let _ ← anyChar
            if c == '`' then
              go (c :: acc) depth false false false false
            else
              go (c :: acc) depth false false true false
        else if c == '\\' then
          let _ ← anyChar
          go ('\\' :: acc) depth false false false true
        else if c == '\'' then
          let _ ← anyChar
          go (c :: acc) depth true false false false
        else if c == '"' then
          let _ ← anyChar
          go (c :: acc) depth false true false false
        else if c == '`' then
          let _ ← anyChar
          go (c :: acc) depth false false true false
        else if terminator == ")" then
          if c == '(' then
            let _ ← anyChar
            go (c :: acc) (depth + 1) false false false false
          else if c == ')' then
            if depth == 0 then
              pure (String.ofList acc.reverse)
            else
              let _ ← anyChar
              go (c :: acc) (depth - 1) false false false false
          else
            let _ ← anyChar
            go (c :: acc) depth false false false false
        else if terminator == "))" then
          if c == '(' then
            let _ ← anyChar
            go (c :: acc) (depth + 1) false false false false
          else if c == ')' then
            if depth == 0 then
              let next2 ← peekString 2
              if next2 == "))" then
                pure (String.ofList acc.reverse)
              else
                let _ ← anyChar
                go (c :: acc) depth false false false false
            else
              let _ ← anyChar
              go (c :: acc) (depth - 1) false false false false
          else
            let _ ← anyChar
            go (c :: acc) depth false false false false
        else
          let nextN ← peekString terminator.length
          if nextN == terminator then
            pure (String.ofList acc.reverse)
          else
            let _ ← anyChar
            go (c :: acc) depth false false false false
  go [] 0 false false false false

/-- Read `${ ... }` content (after consuming `{`), stopping before the matching `}`. -/
partial def readBracedExpansionContent : Parser String := do
  let rec go (acc : List Char) (braceDepth : Nat) (inSingle inDouble inBacktick escaped : Bool) : Parser String := do
    match ← peek? with
    | none => pure (String.ofList acc.reverse)
    | some c =>
        if escaped then
          let _ ← anyChar
          go (c :: acc) braceDepth inSingle inDouble inBacktick false
        else if inSingle then
          let _ ← anyChar
          if c == '\'' then
            go (c :: acc) braceDepth false inDouble inBacktick false
          else
            go (c :: acc) braceDepth true inDouble inBacktick false
        else if inDouble then
          if c == '\\' then
            let _ ← anyChar
            go ('\\' :: acc) braceDepth false true inBacktick true
          else
            let _ ← anyChar
            if c == '"' then
              go (c :: acc) braceDepth false false inBacktick false
            else
              go (c :: acc) braceDepth false true inBacktick false
        else if inBacktick then
          if c == '\\' then
            let _ ← anyChar
            go ('\\' :: acc) braceDepth false false true true
          else
            let _ ← anyChar
            if c == '`' then
              go (c :: acc) braceDepth false false false false
            else
              go (c :: acc) braceDepth false false true false
        else if c == '\\' then
          let _ ← anyChar
          go ('\\' :: acc) braceDepth false false false true
        else if c == '\'' then
          let _ ← anyChar
          go (c :: acc) braceDepth true false false false
        else if c == '"' then
          let _ ← anyChar
          go (c :: acc) braceDepth false true false false
        else if c == '`' then
          let _ ← anyChar
          go (c :: acc) braceDepth false false true false
        else if c == '{' then
          let _ ← anyChar
          go (c :: acc) (braceDepth + 1) false false false false
        else if c == '}' then
          if braceDepth == 0 then
            pure (String.ofList acc.reverse)
          else
            let _ ← anyChar
            go (c :: acc) (braceDepth - 1) false false false false
        else
          let _ ← anyChar
          go (c :: acc) braceDepth false false false false
  go [] 0 false false false false

/-!
## `${...}` parsing helpers

We scan the `${...}` payload as a string (so brace nesting and quoting is handled
correctly), then parse that string into a more structured token tree.

Crucially, for operators like `${a:-word}`, we also parse the `word` using the
normal word parser (with whitespace allowed) so nested `$()`, backticks, and
nested `${...}` are represented in the AST instead of left as raw strings.
-/

/-- Read a literal word part inside a `${...}` argument, allowing whitespace and operators. -/
def readLiteralInBracedArg : Parser Token := do
  let (startLine, startCol) ← currentPos
  let content ← takeWhile1 fun c =>
    c != '"' && c != '\'' && c != '`' && c != '$' && c != '\\'
  mkTokenAt (.T_Literal content) startLine startCol

/-- Offset a positions map returned by a sub-parse. -/
private def offsetPositions
    (positions : Std.HashMap Id (Position × Position))
    (offsetLine offsetCol : Nat) : Std.HashMap Id (Position × Position) :=
  positions.fold (init := {}) fun m k (startPos, endPos) =>
    let newStart : Position := {
      posFile := startPos.posFile
      posLine := startPos.posLine + offsetLine - 1
      posColumn := if startPos.posLine == 1 then startPos.posColumn + offsetCol - 1 else startPos.posColumn
    }
    let newEnd : Position := {
      posFile := endPos.posFile
      posLine := endPos.posLine + offsetLine - 1
      posColumn := if endPos.posLine == 1 then endPos.posColumn + offsetCol - 1 else endPos.posColumn
    }
    m.insert k (newStart, newEnd)

/-- Compute (line, col) at a character offset within a string. -/
private def posAtCharOffset (startLine startCol : Nat) (s : String) (n : Nat) : (Nat × Nat) :=
  let step (lc : Nat × Nat) (c : Char) : (Nat × Nat) :=
    if c == '\n' then (lc.1 + 1, 1) else (lc.1, lc.2 + 1)
  (s.take n).toList.foldl step (startLine, startCol)

mutual

/-- Read arithmetic content until `))` (does not consume the closing `))`). -/
partial def readArithContent : Parser String := do
  readUntilStr "))"

/-- Read subshell content until `)` (does not consume the closing `)`). -/
partial def readSubshellContent : Parser String := do
  readUntilStr ")"

/-- Read ANSI-C quoted content, keeping escape sequences like `\\'`. -/
partial def readAnsiCContent : Parser String := do
  let rec go (acc : List Char) : Parser String := do
    match ← peek? with
    | none => pure (String.ofList acc.reverse)
    | some '\'' => pure (String.ofList acc.reverse)
    | some '\\' =>
        let _ ← anyChar
        match ← peek? with
        | some c =>
            let _ ← anyChar
            go (c :: '\\' :: acc)
        | none =>
            pure (String.ofList ('\\' :: acc).reverse)
    | some c =>
        let _ ← anyChar
        go (c :: acc)
  go []

/-- Read a `${...}` argument as a list of word-part tokens (until EOF). -/
partial def readBracedArgParts : Parser (List Token) := do
  let rec go (acc : List Token) : Parser (List Token) := do
    match ← peek? with
    | none => pure acc.reverse
    | some '\'' =>
        let tok ← readSingleQuoted
        go (tok :: acc)
    | some '"' =>
        let tok ← readDoubleQuoted
        go (tok :: acc)
    | some '`' =>
        let tok ← readBacktick
        go (tok :: acc)
    | some '$' =>
        let (startLine, startCol) ← currentPos
        let _ ← anyChar
        let tok ← readDollar startLine startCol
        go (tok :: acc)
    | some '\\' =>
        let (escStartLine, escStartCol) ← currentPos
        let _ ← anyChar
        match ← peek? with
        | some '\n' =>
            let _ ← anyChar
            go acc  -- line continuation
        | some ec =>
            let _ ← anyChar
            let tok ← mkTokenAt (.T_Literal (String.ofList [ec])) escStartLine escStartCol
            go (tok :: acc)
        | none =>
            let tok ← mkTokenAt (.T_Literal "\\") escStartLine escStartCol
            go (tok :: acc)
    | some _ =>
        let tok ← readLiteralInBracedArg
        go (tok :: acc)
  go []

/-- Parse a braced-argument string into tokens, allocating fresh IDs starting at `startId`. -/
private partial def parseBracedArgParts
    (arg : String) (filename : String)
    (startId : Nat) (offsetLine offsetCol : Nat)
    : (List Token × Nat × Std.HashMap Id (Position × Position)) :=
  let initState : ParserState :=
    { ShellCheck.Parser.Parsec.mkShellState filename with nextId := startId }
  match ShellCheck.Parser.Parsec.runWithState readBracedArgParts arg initState with
  | (some (parts, st), _) =>
      let pos := offsetPositions st.positions offsetLine offsetCol
      (parts, st.nextId, pos)
  | (none, _) =>
      let litTok : Token := ⟨⟨startId⟩, .T_Literal arg⟩
      ([litTok], startId + 1, {})

/-- Parse the content of a `${...}` expansion into a structured token tree.

If parsing fails, fall back to a single literal token with the raw content. -/
private partial def parseBracedExpansionContent (content : String) (startLine startCol : Nat) : Parser Token := do
  let mkLitAt (s : String) : Parser Token :=
    mkTokenAt (.T_Literal s) startLine startCol
  let mkOpAt (s : String) : Parser Token :=
    mkTokenAt (.T_ParamSubSpecialChar s) startLine startCol

  let parseArgAt (arg : String) (charOffset : Nat) : Parser (List Token) := do
    let st ← ShellCheck.Parser.Parsec.getState
    let (argLine, argCol) := posAtCharOffset startLine startCol content charOffset
    let (parts, newNextId, newPositions) :=
      parseBracedArgParts arg st.filename st.nextId argLine argCol
    ShellCheck.Parser.Parsec.modifyState fun st =>
      { st with
        nextId := newNextId
        positions := newPositions.fold (init := st.positions) fun m k v => m.insert k v }
    pure parts

  match ShellCheck.Parser.Expansion.parseExpansion content with
  | none =>
      mkLitAt content
  | some exp =>
      let varTok ← mkLitAt exp.varName
      match exp.op with
      | .none =>
          mkTokenAt (.T_NormalWord [varTok]) startLine startCol
      | .length =>
          let hashTok ← mkOpAt "#"
          mkTokenAt (.T_NormalWord [hashTok, varTok]) startLine startCol
      | .indirect =>
          let bangTok ← mkOpAt "!"
          mkTokenAt (.T_NormalWord [bangTok, varTok]) startLine startCol
      | .useDefault =>
          let opStr := if exp.isColonVariant then ":-" else "-"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .assignDefault =>
          let opStr := if exp.isColonVariant then ":=" else "="
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .useAlternate =>
          let opStr := if exp.isColonVariant then ":+" else "+"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .errorIfUnset =>
          let opStr := if exp.isColonVariant then ":?" else "?"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .removePrefix =>
          let opStr := if exp.isDoubled then "##" else "#"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .removeSuffix =>
          let opStr := if exp.isDoubled then "%%" else "%"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .replace =>
          let opStr := if exp.isDoubled then "//" else "/"
          let op1Tok ← mkOpAt opStr
          let find := exp.arg1.getD ""
          let repl := exp.arg2.getD ""
          let findStart := exp.varName.length + opStr.length
          let rawDelimStart := findStart + find.length
          let replStart :=
            match (⟨rawDelimStart⟩ : String.Pos.Raw).get? content with
            | some '/' => rawDelimStart + 1
            | _ => rawDelimStart
          let findParts ← parseArgAt find findStart
          let op2Tok ← mkOpAt "/"
          let replParts ← parseArgAt repl replStart
          mkTokenAt (.T_NormalWord ([varTok, op1Tok] ++ findParts ++ [op2Tok] ++ replParts)) startLine startCol
      | .replacePrefix =>
          let opStr := "/#"
          let op1Tok ← mkOpAt opStr
          let find := exp.arg1.getD ""
          let repl := exp.arg2.getD ""
          let findStart := exp.varName.length + opStr.length
          let rawDelimStart := findStart + find.length
          let replStart :=
            match (⟨rawDelimStart⟩ : String.Pos.Raw).get? content with
            | some '/' => rawDelimStart + 1
            | _ => rawDelimStart
          let findParts ← parseArgAt find findStart
          let op2Tok ← mkOpAt "/"
          let replParts ← parseArgAt repl replStart
          mkTokenAt (.T_NormalWord ([varTok, op1Tok] ++ findParts ++ [op2Tok] ++ replParts)) startLine startCol
      | .replaceSuffix =>
          let opStr := "/%"
          let op1Tok ← mkOpAt opStr
          let find := exp.arg1.getD ""
          let repl := exp.arg2.getD ""
          let findStart := exp.varName.length + opStr.length
          let rawDelimStart := findStart + find.length
          let replStart :=
            match (⟨rawDelimStart⟩ : String.Pos.Raw).get? content with
            | some '/' => rawDelimStart + 1
            | _ => rawDelimStart
          let findParts ← parseArgAt find findStart
          let op2Tok ← mkOpAt "/"
          let replParts ← parseArgAt repl replStart
          mkTokenAt (.T_NormalWord ([varTok, op1Tok] ++ findParts ++ [op2Tok] ++ replParts)) startLine startCol
      | .substring =>
          let op1Tok ← mkOpAt ":"
          let off := exp.arg1.getD ""
          let offStart := exp.varName.length + 1
          let offParts ← parseArgAt off offStart
          match exp.arg2 with
          | some len =>
              let op2Tok ← mkOpAt ":"
              let lenStart := offStart + off.length + 1
              let lenParts ← parseArgAt len lenStart
              mkTokenAt (.T_NormalWord ([varTok, op1Tok] ++ offParts ++ [op2Tok] ++ lenParts)) startLine startCol
          | none =>
              mkTokenAt (.T_NormalWord ([varTok, op1Tok] ++ offParts)) startLine startCol
      | .caseUpper =>
          let opTok ← mkOpAt (if exp.isDoubled then "^^" else "^")
          mkTokenAt (.T_NormalWord [varTok, opTok]) startLine startCol
      | .caseLower =>
          let opTok ← mkOpAt (if exp.isDoubled then ",," else ",")
          mkTokenAt (.T_NormalWord [varTok, opTok]) startLine startCol
      | .transform =>
          let opTok ← mkOpAt "@"
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + 1)
          mkTokenAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol

/-- Read a `$...` expansion inside double quotes (assumes `$` already consumed). -/
partial def readDollarInDQ (startLine startCol : Nat) : Parser Token := do
  match ← peek? with
  | some '{' =>
      let _ ← char '{'
      let (contentStartLine, contentStartCol) ← currentPos
      let content ← readBracedExpansionContent
      let inner ← parseBracedExpansionContent content contentStartLine contentStartCol
      let _ ← char '}'
      mkTokenAt (.T_DollarBraced true inner) startLine startCol
  | some '(' =>
      let _ ← char '('
      match ← peek? with
      | some '(' =>
          let _ ← char '('
          let content ← readArithContent
          let _ ← string "))"
          let inner := match Arithmetic.parse content with
            | some arithToken => arithToken
            | none => ⟨⟨0⟩, .T_Literal content⟩
          mkTokenAt (.T_DollarArithmetic inner) startLine startCol
      | _ =>
          let (contentStartLine, contentStartCol) ← currentPos
          let content ← readSubshellContent
          let inner ← mkTokenAt (.T_Literal content) contentStartLine contentStartCol
          let _ ← char ')'
          mkTokenAt (.T_DollarExpansion [inner]) startLine startCol
  | some c =>
      if variableStartChar c then
        let (nameStartLine, nameStartCol) ← currentPos
        let name ← takeWhile1 variableChar
        let inner ← mkTokenAt (.T_Literal name) nameStartLine nameStartCol
        mkTokenAt (.T_DollarBraced false inner) startLine startCol
      else if specialVariableChars.toList.contains c then
        let (nameStartLine, nameStartCol) ← currentPos
        let _ ← anyChar
        let inner ← mkTokenAt (.T_Literal (String.ofList [c])) nameStartLine nameStartCol
        mkTokenAt (.T_DollarBraced false inner) startLine startCol
      else
        mkTokenAt (.T_Literal "$") startLine startCol
  | none =>
      mkTokenAt (.T_Literal "$") startLine startCol

/-- Read a `$...` expansion in normal word context (assumes `$` already consumed). -/
partial def readDollar (startLine startCol : Nat) : Parser Token := do
  match ← peek? with
  | some '{' =>
      let _ ← char '{'
      let (contentStartLine, contentStartCol) ← currentPos
      let content ← readBracedExpansionContent
      let inner ← parseBracedExpansionContent content contentStartLine contentStartCol
      let _ ← char '}'
      mkTokenAt (.T_DollarBraced true inner) startLine startCol
  | some '(' =>
      let _ ← char '('
      match ← peek? with
      | some '(' =>
          let _ ← char '('
          let content ← readArithContent
          let _ ← string "))"
          let inner := match Arithmetic.parse content with
            | some arithToken => arithToken
            | none => ⟨⟨0⟩, .T_Literal content⟩
          mkTokenAt (.T_DollarArithmetic inner) startLine startCol
      | _ =>
          let (contentStartLine, contentStartCol) ← currentPos
          let content ← readSubshellContent
          let inner ← mkTokenAt (.T_Literal content) contentStartLine contentStartCol
          let _ ← char ')'
          mkTokenAt (.T_DollarExpansion [inner]) startLine startCol
  | some '\'' =>
      -- $'...' ANSI-C quoting - keep escape sequences in the raw content.
      let _ ← char '\''
      let content ← readAnsiCContent
      let _ ← char '\''
      mkTokenAt (.T_DollarSingleQuoted content) startLine startCol
  | some '"' =>
      -- $"..." locale-specific string (treated as double quoted in AST)
      let _ ← char '"'
      let (contentStartLine, contentStartCol) ← currentPos
      let content ← takeWhile (· != '"')  -- Simplified
      let inner ← mkTokenAt (.T_Literal content) contentStartLine contentStartCol
      let _ ← char '"'
      mkTokenAt (.T_DollarDoubleQuoted [inner]) startLine startCol
  | some c =>
      if variableStartChar c then
        let (nameStartLine, nameStartCol) ← currentPos
        let name ← takeWhile1 variableChar
        let inner ← mkTokenAt (.T_Literal name) nameStartLine nameStartCol
        mkTokenAt (.T_DollarBraced false inner) startLine startCol
      else if specialVariableChars.toList.contains c then
        let (nameStartLine, nameStartCol) ← currentPos
        let _ ← anyChar
        let inner ← mkTokenAt (.T_Literal (String.ofList [c])) nameStartLine nameStartCol
        mkTokenAt (.T_DollarBraced false inner) startLine startCol
      else
        mkTokenAt (.T_Literal "$") startLine startCol
  | none =>
      mkTokenAt (.T_Literal "$") startLine startCol

/-- Read a double-quoted string. -/
partial def readDoubleQuoted : Parser Token := do
  let (startLine, startCol) ← currentPos
  let _ ← char '"'
  let parts ← readDQParts []
  let _ ← char '"'
  mkTokenAt (.T_DoubleQuoted parts) startLine startCol
where
  readDQParts (acc : List Token) : Parser (List Token) := do
    match ← peek? with
    | none => pure acc.reverse
    | some '"' => pure acc.reverse
    | some '\\' =>
        let (escStartLine, escStartCol) ← currentPos
        let _ ← anyChar
        match ← peek? with
        | some c =>
            let _ ← anyChar
            let tok ← mkTokenAt (.T_Literal (String.ofList ['\\', c])) escStartLine escStartCol
            readDQParts (tok :: acc)
        | none => pure acc.reverse
    | some '$' =>
        let (startLine, startCol) ← currentPos
        let _ ← anyChar
        let tok ← readDollarInDQ startLine startCol
        readDQParts (tok :: acc)
    | some '`' =>
        let tok ← readBacktick
        readDQParts (tok :: acc)
    | some _ =>
        let (litStartLine, litStartCol) ← currentPos
        let lit ← takeWhile fun c => c != '"' && c != '\\' && c != '$' && c != '`'
        if lit.isEmpty then pure acc.reverse
        else
          let tok ← mkTokenAt (.T_Literal lit) litStartLine litStartCol
          readDQParts (tok :: acc)

/-- Read process substitution <(...) or >(...) -/
partial def readProcSub : Parser Token := do
  let (startLine, startCol) ← currentPos
  let dir ← anyChar  -- < or >
  let _ ← char '('
  -- Read content until matching )
  let content ← readProcSubContent 1 []
  let _ ← char ')'
  let dirStr := String.ofList [dir]
  -- For now, create a T_ProcSub with the raw content as a literal
  let contentTok ← mkTokenAt (.T_Literal content) startLine startCol
  mkTokenAt (.T_ProcSub dirStr [contentTok]) startLine startCol
where
  /-- Read until matching ) accounting for nested parens and quotes -/
  readProcSubContent (depth : Nat) (acc : List Char) : Parser String := do
    match ← peek? with
    | none => pure (String.ofList acc.reverse)
    | some ')' =>
        if depth <= 1 then
          pure (String.ofList acc.reverse)
        else
          let _ ← anyChar
          readProcSubContent (depth - 1) (')' :: acc)
    | some '(' =>
        let _ ← anyChar
        readProcSubContent (depth + 1) ('(' :: acc)
    | some '\'' =>
        -- Skip single-quoted content
        let _ ← anyChar
        let quoted ← takeWhile (· != '\'')
        match ← peek? with
        | some '\'' =>
            let _ ← anyChar
            let newAcc := '\'' :: quoted.toList.reverse ++ ('\'' :: acc)
            readProcSubContent depth newAcc
        | _ => readProcSubContent depth ('\'' :: quoted.toList.reverse ++ ('\'' :: acc))
    | some '"' =>
        -- Skip double-quoted content (simplified - ignoring escapes within)
        let _ ← anyChar
        let quoted ← takeWhile (· != '"')
        match ← peek? with
        | some '"' =>
            let _ ← anyChar
            let newAcc := '"' :: quoted.toList.reverse ++ ('"' :: acc)
            readProcSubContent depth newAcc
        | _ => readProcSubContent depth ('"' :: quoted.toList.reverse ++ ('"' :: acc))
    | some c =>
        let _ ← anyChar
        readProcSubContent depth (c :: acc)

end

/-- Read a complete word (multiple parts) -/
partial def readWord : Parser Token := do
  let (startLine, startCol) ← currentPos
  let parts ← readWordParts []
  if parts.isEmpty then
    failure
  else
    mkTokenAt (.T_NormalWord parts) startLine startCol
where
  readWordParts (acc : List Token) : Parser (List Token) := do
    match ← peek? with
    | none => pure acc.reverse
    | some c =>
        -- Check for process substitution <(...) or >(...) first
        if c == '<' || c == '>' then
          let nextTwo ← peekString 2
          if nextTwo == "<(" || nextTwo == ">(" then
            let tok ← readProcSub
            readWordParts (tok :: acc)
          else
            -- Regular < or > is an operator, stop word
            pure acc.reverse
        else if c.isWhitespace || isOperatorStart c || c == '#' then
          pure acc.reverse
        else if c == '\'' then
          let tok ← readSingleQuoted
          readWordParts (tok :: acc)
        else if c == '"' then
          let tok ← readDoubleQuoted
          readWordParts (tok :: acc)
        else if c == '`' then
          let tok ← readBacktick
          readWordParts (tok :: acc)
        else if c == '$' then
          let (startLine, startCol) ← currentPos
          let _ ← anyChar
          let tok ← readDollar startLine startCol
          readWordParts (tok :: acc)
        else if c == '\\' then
          let (escStartLine, escStartCol) ← currentPos
          let _ ← anyChar
          match ← peek? with
          | some '\n' =>
              let _ ← anyChar
              readWordParts acc  -- Line continuation
          | some ec =>
              let _ ← anyChar
              let tok ← mkTokenAt (.T_Literal (String.ofList [ec])) escStartLine escStartCol
              readWordParts (tok :: acc)
          | none =>
              let tok ← mkTokenAt (.T_Literal "\\") escStartLine escStartCol
              readWordParts (tok :: acc)
        else
          let tok ← readLiteral
          readWordParts (tok :: acc)

/-- Read a word as it appears in `case` patterns.

Unlike normal words, `case` patterns may contain extglob syntax like `@(foo|bar)`,
which uses parentheses and `|` in a way that should not be interpreted as shell
operators. This reader:

- stops on `|` or `)` only at the top level (outside bracket classes and
  parenthesis nesting),
- allows `(` / `)` to appear as literal characters inside the pattern, and
- preserves normal handling of quotes, `$` expansions, backticks, and escapes.

This is a best-effort parser intended to improve `case` pattern coverage without
rewriting the full word lexer. -/
partial def readPatternWord : Parser Token := do
  let (startLine, startCol) ← currentPos
  let parts ← readParts [] none [] 0 false 0 false false
  if parts.isEmpty then
    failure
  else
    mkTokenAt (.T_NormalWord parts) startLine startCol
where
  flushLiteral (acc : List Token) (litStart : Option (Nat × Nat)) (litRev : List Char) :
      Parser (List Token) := do
    match litStart with
    | none => pure acc
    | some (line, col) =>
        let s := String.ofList litRev.reverse
        if s.isEmpty then
          pure acc
        else
          let tok ← mkTokenAt (.T_Literal s) line col
          pure (tok :: acc)

  /-- State machine for bracket expressions (`[...]`) so that we don't treat `]`
  immediately after `[`/`[!`/`[^` as a terminator. -/
  updateBracket (inClass : Bool) (classChars : Nat) (sawNegation : Bool) (c : Char) :
      Bool × Nat × Bool :=
    if inClass then
      if classChars == 0 && !sawNegation && (c == '!' || c == '^') then
        (true, 0, true)
      else if c == ']' && classChars == 0 then
        (true, 1, sawNegation)
      else if c == ']' then
        (false, 0, false)
      else
        (true, classChars + 1, sawNegation)
    else
      if c == '[' then
        (true, 0, false)
      else
        (false, 0, false)

  updateDepth (parenDepth : Nat) (_inClass : Bool) (c : Char) : Nat :=
    if c == ')' then
      match parenDepth with
      | 0 => 0
      | d + 1 => d
    else
      parenDepth

  /-- Read pattern parts, stopping before `|` / `)` that are part of the `case`
  item syntax (but not those inside extglob/bracket expressions). -/
  readParts
      (acc : List Token)
      (litStart : Option (Nat × Nat))
      (litRev : List Char)
      (parenDepth : Nat)
      (inClass : Bool)
      (classChars : Nat)
      (sawNegation : Bool)
      (extglobPending : Bool)
      : Parser (List Token) := do
    match ← peek? with
    | none => do
        let acc ← flushLiteral acc litStart litRev
        pure acc.reverse
    | some c =>
        -- Stop on case-pattern separators only when not nested.
        if parenDepth == 0 && (c == '|' || c == ')') then
          let acc ← flushLiteral acc litStart litRev
          pure acc.reverse
        else if c == '(' && !inClass then
          if extglobPending then
            let (litLine, litCol) ← currentPos
            let _ ← anyChar
            let litStart := litStart <|> some (litLine, litCol)
            readParts acc litStart (c :: litRev) (parenDepth + 1) inClass classChars sawNegation false
          else
            ShellCheck.Parser.Parsec.ShellParser.fail "case pattern: unexpected '('"
        else if c == ')' && parenDepth > 0 && inClass then
          ShellCheck.Parser.Parsec.ShellParser.fail "case pattern: unexpected ')'"
        else if c.isWhitespace || c == '#' ||
            (isOperatorStart c && c != ')' && c != '|') then
          let acc ← flushLiteral acc litStart litRev
          pure acc.reverse
        else if c == '\'' then
          let acc ← flushLiteral acc litStart litRev
          let tok ← readSingleQuoted
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation false
        else if c == '"' then
          let acc ← flushLiteral acc litStart litRev
          let tok ← readDoubleQuoted
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation false
        else if c == '`' then
          let acc ← flushLiteral acc litStart litRev
          let tok ← readBacktick
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation false
        else if c == '$' then
          let acc ← flushLiteral acc litStart litRev
          let (dl, dc) ← currentPos
          let _ ← anyChar
          let tok ← readDollar dl dc
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation false
        else if c == '\\' then
          let (escLine, escCol) ← currentPos
          let _ ← anyChar
          match ← peek? with
          | some '\n' =>
              let _ ← anyChar
              readParts acc litStart litRev parenDepth inClass classChars sawNegation false
          | some ec =>
              let _ ← anyChar
              let litStart := litStart <|> some (escLine, escCol)
              readParts acc litStart (ec :: litRev) parenDepth inClass classChars sawNegation false
          | none =>
              let litStart := litStart <|> some (escLine, escCol)
              readParts acc litStart ('\\' :: litRev) parenDepth inClass classChars sawNegation false
        else
          let (litLine, litCol) ← currentPos
          let _ ← anyChar
          let litStart := litStart <|> some (litLine, litCol)
          let (inClass', classChars', sawNegation') := updateBracket inClass classChars sawNegation c
          let parenDepth' := updateDepth parenDepth inClass c
          let extglobPending' :=
            -- Recognize extglob operators only outside bracket classes; we use this
            -- to decide whether a subsequent `(` should start an extglob group.
            if inClass' then
              false
            else
              c == '@' || c == '!' || c == '+' || c == '*' || c == '?'
          readParts acc litStart (c :: litRev) parenDepth' inClass' classChars' sawNegation' extglobPending'
/-- Read arithmetic content for `(( .. ))` / `for (( .. ))` (does not consume the closing `))`). -/
@[inline] def readArithContentHelper : Parser String :=
  readArithContent

end ShellCheck.Parser.Word
