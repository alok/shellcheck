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
Word parsing helpers for the full parser.

These functions are used by the grammar in `ShellCheck/Parser.lean` and are
intended to be the single source of truth for word parsing during the Parsec
migration.
-/

/-- Read a literal word part -/
def readLiteralFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let content ← takeWhile1Full fun c =>
    ¬ (c.isWhitespace ||
       c == '"' || c == '\'' || c == '`' ||
       c == '$' || c == '\\' ||
       c == '|' || c == '&' || c == ';' ||
       c == '<' || c == '>' ||
       c == '(' || c == ')' ||
       c == '#')
       -- Note: { and } are allowed in word literals for brace expansion
  mkTokenFullAt (.T_Literal content) startLine startCol

/-- Read a single-quoted string -/
def readSingleQuotedFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let _ ← charFull '\''
  let content ← takeWhileFull (· != '\'')
  let _ ← charFull '\''
  mkTokenFullAt (.T_SingleQuoted content) startLine startCol

/-- Read backtick content until the next *unescaped* backtick, respecting quotes. -/
partial def readBacktickContent : FullParser String := do
  let rec go (acc : List Char) (inSingle inDouble escaped : Bool) : FullParser String := do
    match ← peekFull with
    | none => pure (String.ofList acc.reverse)
    | some c =>
        if escaped then
          let _ ← anyCharFull
          go (c :: acc) inSingle inDouble false
        else if inSingle then
          let _ ← anyCharFull
          if c == '\'' then
            go (c :: acc) false inDouble false
          else
            go (c :: acc) true inDouble false
        else if inDouble then
          if c == '\\' then
            let _ ← anyCharFull
            go ('\\' :: acc) false true true
          else
            let _ ← anyCharFull
            if c == '"' then
              go (c :: acc) false false false
            else
              go (c :: acc) false true false
        else if c == '\\' then
          let _ ← anyCharFull
          go ('\\' :: acc) false false true
        else if c == '\'' then
          let _ ← anyCharFull
          go (c :: acc) true false false
        else if c == '"' then
          let _ ← anyCharFull
          go (c :: acc) false true false
        else if c == '`' then
          pure (String.ofList acc.reverse)
        else
          let _ ← anyCharFull
          go (c :: acc) false false false
  go [] false false false

/-- Read a backtick command substitution -/
partial def readBacktickFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let _ ← charFull '`'
  let (contentStartLine, contentStartCol) ← currentPos
  let content ← readBacktickContent
  let inner ← mkTokenFullAt (.T_Literal content) contentStartLine contentStartCol
  let _ ← charFull '`'
  mkTokenFullAt (.T_Backticked [inner]) startLine startCol

/-- Helper to read until a terminator string -/
partial def readUntilStr (terminator : String) : FullParser String := do
  -- Important: must not consume the terminator.
  let rec go (acc : List Char) (depth : Nat) (inSingle inDouble inBacktick escaped : Bool) : FullParser String := do
    match ← peekFull with
    | none => pure (String.ofList acc.reverse)
    | some c =>
        if escaped then
          let _ ← anyCharFull
          go (c :: acc) depth inSingle inDouble inBacktick false
        else if inSingle then
          let _ ← anyCharFull
          if c == '\'' then
            go (c :: acc) depth false inDouble inBacktick false
          else
            go (c :: acc) depth true inDouble inBacktick false
        else if inDouble then
          if c == '\\' then
            let _ ← anyCharFull
            go ('\\' :: acc) depth false true inBacktick true
          else
            let _ ← anyCharFull
            if c == '"' then
              go (c :: acc) depth false false inBacktick false
            else
              go (c :: acc) depth false true inBacktick false
        else if inBacktick then
          if c == '\\' then
            let _ ← anyCharFull
            go ('\\' :: acc) depth false false true true
          else
            let _ ← anyCharFull
            if c == '`' then
              go (c :: acc) depth false false false false
            else
              go (c :: acc) depth false false true false
        else if c == '\\' then
          let _ ← anyCharFull
          go ('\\' :: acc) depth false false false true
        else if c == '\'' then
          let _ ← anyCharFull
          go (c :: acc) depth true false false false
        else if c == '"' then
          let _ ← anyCharFull
          go (c :: acc) depth false true false false
        else if c == '`' then
          let _ ← anyCharFull
          go (c :: acc) depth false false true false
        else if terminator == ")" then
          if c == '(' then
            let _ ← anyCharFull
            go (c :: acc) (depth + 1) false false false false
          else if c == ')' then
            if depth == 0 then
              pure (String.ofList acc.reverse)
            else
              let _ ← anyCharFull
              go (c :: acc) (depth - 1) false false false false
          else
            let _ ← anyCharFull
            go (c :: acc) depth false false false false
        else if terminator == "))" then
          if c == '(' then
            let _ ← anyCharFull
            go (c :: acc) (depth + 1) false false false false
          else if c == ')' then
            if depth == 0 then
              let next2 ← peekStringFull 2
              if next2 == "))" then
                pure (String.ofList acc.reverse)
              else
                let _ ← anyCharFull
                go (c :: acc) depth false false false false
            else
              let _ ← anyCharFull
              go (c :: acc) (depth - 1) false false false false
          else
            let _ ← anyCharFull
            go (c :: acc) depth false false false false
        else
          let nextN ← peekStringFull terminator.length
          if nextN == terminator then
            pure (String.ofList acc.reverse)
          else
            let _ ← anyCharFull
            go (c :: acc) depth false false false false
  go [] 0 false false false false

/-- Read `${ ... }` content (after consuming `{`), stopping before the matching `}`. -/
partial def readBracedExpansionContent : FullParser String := do
  let rec go (acc : List Char) (braceDepth : Nat) (inSingle inDouble inBacktick escaped : Bool) : FullParser String := do
    match ← peekFull with
    | none => pure (String.ofList acc.reverse)
    | some c =>
        if escaped then
          let _ ← anyCharFull
          go (c :: acc) braceDepth inSingle inDouble inBacktick false
        else if inSingle then
          let _ ← anyCharFull
          if c == '\'' then
            go (c :: acc) braceDepth false inDouble inBacktick false
          else
            go (c :: acc) braceDepth true inDouble inBacktick false
        else if inDouble then
          if c == '\\' then
            let _ ← anyCharFull
            go ('\\' :: acc) braceDepth false true inBacktick true
          else
            let _ ← anyCharFull
            if c == '"' then
              go (c :: acc) braceDepth false false inBacktick false
            else
              go (c :: acc) braceDepth false true inBacktick false
        else if inBacktick then
          if c == '\\' then
            let _ ← anyCharFull
            go ('\\' :: acc) braceDepth false false true true
          else
            let _ ← anyCharFull
            if c == '`' then
              go (c :: acc) braceDepth false false false false
            else
              go (c :: acc) braceDepth false false true false
        else if c == '\\' then
          let _ ← anyCharFull
          go ('\\' :: acc) braceDepth false false false true
        else if c == '\'' then
          let _ ← anyCharFull
          go (c :: acc) braceDepth true false false false
        else if c == '"' then
          let _ ← anyCharFull
          go (c :: acc) braceDepth false true false false
        else if c == '`' then
          let _ ← anyCharFull
          go (c :: acc) braceDepth false false true false
        else if c == '{' then
          let _ ← anyCharFull
          go (c :: acc) (braceDepth + 1) false false false false
        else if c == '}' then
          if braceDepth == 0 then
            pure (String.ofList acc.reverse)
          else
            let _ ← anyCharFull
            go (c :: acc) (braceDepth - 1) false false false false
        else
          let _ ← anyCharFull
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
def readLiteralInBracedArgFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let content ← takeWhile1Full fun c =>
    c != '"' && c != '\'' && c != '`' && c != '$' && c != '\\'
  mkTokenFullAt (.T_Literal content) startLine startCol

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
partial def readArithContent : FullParser String := do
  readUntilStr "))"

/-- Read subshell content until `)` (does not consume the closing `)`). -/
partial def readSubshellContent : FullParser String := do
  readUntilStr ")"

/-- Read ANSI-C quoted content, keeping escape sequences like `\\'`. -/
partial def readAnsiCContentFull : FullParser String := do
  let rec go (acc : List Char) : FullParser String := do
    match ← peekFull with
    | none => pure (String.ofList acc.reverse)
    | some '\'' => pure (String.ofList acc.reverse)
    | some '\\' =>
        let _ ← anyCharFull
        match ← peekFull with
        | some c =>
            let _ ← anyCharFull
            go (c :: '\\' :: acc)
        | none =>
            pure (String.ofList ('\\' :: acc).reverse)
    | some c =>
        let _ ← anyCharFull
        go (c :: acc)
  go []

/-- Read a `${...}` argument as a list of word-part tokens (until EOF). -/
partial def readBracedArgPartsFull : FullParser (List Token) := do
  let rec go (acc : List Token) : FullParser (List Token) := do
    match ← peekFull with
    | none => pure acc.reverse
    | some '\'' =>
        let tok ← readSingleQuotedFull
        go (tok :: acc)
    | some '"' =>
        let tok ← readDoubleQuotedFull
        go (tok :: acc)
    | some '`' =>
        let tok ← readBacktickFull
        go (tok :: acc)
    | some '$' =>
        let (startLine, startCol) ← currentPos
        let _ ← anyCharFull
        let tok ← readDollarFull startLine startCol
        go (tok :: acc)
    | some '\\' =>
        let (escStartLine, escStartCol) ← currentPos
        let _ ← anyCharFull
        match ← peekFull with
        | some '\n' =>
            let _ ← anyCharFull
            go acc  -- line continuation
        | some ec =>
            let _ ← anyCharFull
            let tok ← mkTokenFullAt (.T_Literal (String.ofList [ec])) escStartLine escStartCol
            go (tok :: acc)
        | none =>
            let tok ← mkTokenFullAt (.T_Literal "\\") escStartLine escStartCol
            go (tok :: acc)
    | some _ =>
        let tok ← readLiteralInBracedArgFull
        go (tok :: acc)
  go []

/-- Parse a braced-argument string into tokens, allocating fresh IDs starting at `startId`. -/
private partial def parseBracedArgParts
    (arg : String) (filename : String)
    (startId : Nat) (offsetLine offsetCol : Nat)
    : (List Token × Nat × Std.HashMap Id (Position × Position)) :=
  let it := ShellCheck.Parser.Parsec.PosIterator.create arg
  let initState : FullParserState :=
    { ShellCheck.Parser.Parsec.mkShellState filename with nextId := startId }
  match readBracedArgPartsFull initState it with
  | .success _ (parts, st) =>
      let pos := offsetPositions st.positions offsetLine offsetCol
      (parts, st.nextId, pos)
  | .error _ _ =>
      let litTok : Token := ⟨⟨startId⟩, .T_Literal arg⟩
      ([litTok], startId + 1, {})

/-- Parse the content of a `${...}` expansion into a structured token tree.

If parsing fails, fall back to a single literal token with the raw content. -/
private partial def parseBracedExpansionContentFull (content : String) (startLine startCol : Nat) : FullParser Token := do
  let mkLitAt (s : String) : FullParser Token :=
    mkTokenFullAt (.T_Literal s) startLine startCol
  let mkOpAt (s : String) : FullParser Token :=
    mkTokenFullAt (.T_ParamSubSpecialChar s) startLine startCol

  let parseArgAt (arg : String) (charOffset : Nat) : FullParser (List Token) := do
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
          mkTokenFullAt (.T_NormalWord [varTok]) startLine startCol
      | .length =>
          let hashTok ← mkOpAt "#"
          mkTokenFullAt (.T_NormalWord [hashTok, varTok]) startLine startCol
      | .indirect =>
          let bangTok ← mkOpAt "!"
          mkTokenFullAt (.T_NormalWord [bangTok, varTok]) startLine startCol
      | .useDefault =>
          let opStr := if exp.isColonVariant then ":-" else "-"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenFullAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .assignDefault =>
          let opStr := if exp.isColonVariant then ":=" else "="
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenFullAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .useAlternate =>
          let opStr := if exp.isColonVariant then ":+" else "+"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenFullAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .errorIfUnset =>
          let opStr := if exp.isColonVariant then ":?" else "?"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenFullAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .removePrefix =>
          let opStr := if exp.isDoubled then "##" else "#"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenFullAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
      | .removeSuffix =>
          let opStr := if exp.isDoubled then "%%" else "%"
          let opTok ← mkOpAt opStr
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + opStr.length)
          mkTokenFullAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol
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
          mkTokenFullAt (.T_NormalWord ([varTok, op1Tok] ++ findParts ++ [op2Tok] ++ replParts)) startLine startCol
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
          mkTokenFullAt (.T_NormalWord ([varTok, op1Tok] ++ findParts ++ [op2Tok] ++ replParts)) startLine startCol
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
          mkTokenFullAt (.T_NormalWord ([varTok, op1Tok] ++ findParts ++ [op2Tok] ++ replParts)) startLine startCol
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
              mkTokenFullAt (.T_NormalWord ([varTok, op1Tok] ++ offParts ++ [op2Tok] ++ lenParts)) startLine startCol
          | none =>
              mkTokenFullAt (.T_NormalWord ([varTok, op1Tok] ++ offParts)) startLine startCol
      | .caseUpper =>
          let opTok ← mkOpAt (if exp.isDoubled then "^^" else "^")
          mkTokenFullAt (.T_NormalWord [varTok, opTok]) startLine startCol
      | .caseLower =>
          let opTok ← mkOpAt (if exp.isDoubled then ",," else ",")
          mkTokenFullAt (.T_NormalWord [varTok, opTok]) startLine startCol
      | .transform =>
          let opTok ← mkOpAt "@"
          let arg := exp.arg1.getD ""
          let argParts ← parseArgAt arg (exp.varName.length + 1)
          mkTokenFullAt (.T_NormalWord ([varTok, opTok] ++ argParts)) startLine startCol

/-- Read a `$...` expansion inside double quotes (assumes `$` already consumed). -/
partial def readDollarInDQFull (startLine startCol : Nat) : FullParser Token := do
  match ← peekFull with
  | some '{' =>
      let _ ← charFull '{'
      let (contentStartLine, contentStartCol) ← currentPos
      let content ← readBracedExpansionContent
      let inner ← parseBracedExpansionContentFull content contentStartLine contentStartCol
      let _ ← charFull '}'
      mkTokenFullAt (.T_DollarBraced true inner) startLine startCol
  | some '(' =>
      let _ ← charFull '('
      match ← peekFull with
      | some '(' =>
          let _ ← charFull '('
          let content ← readArithContent
          let _ ← stringFull "))"
          let inner := match Arithmetic.parse content with
            | some arithToken => arithToken
            | none => ⟨⟨0⟩, .T_Literal content⟩
          mkTokenFullAt (.T_DollarArithmetic inner) startLine startCol
      | _ =>
          let (contentStartLine, contentStartCol) ← currentPos
          let content ← readSubshellContent
          let inner ← mkTokenFullAt (.T_Literal content) contentStartLine contentStartCol
          let _ ← charFull ')'
          mkTokenFullAt (.T_DollarExpansion [inner]) startLine startCol
  | some c =>
      if variableStartChar c then
        let (nameStartLine, nameStartCol) ← currentPos
        let name ← takeWhile1Full variableChar
        let inner ← mkTokenFullAt (.T_Literal name) nameStartLine nameStartCol
        mkTokenFullAt (.T_DollarBraced false inner) startLine startCol
      else if specialVariableChars.toList.contains c then
        let (nameStartLine, nameStartCol) ← currentPos
        let _ ← anyCharFull
        let inner ← mkTokenFullAt (.T_Literal (String.ofList [c])) nameStartLine nameStartCol
        mkTokenFullAt (.T_DollarBraced false inner) startLine startCol
      else
        mkTokenFullAt (.T_Literal "$") startLine startCol
  | none =>
      mkTokenFullAt (.T_Literal "$") startLine startCol

/-- Read a `$...` expansion in normal word context (assumes `$` already consumed). -/
partial def readDollarFull (startLine startCol : Nat) : FullParser Token := do
  match ← peekFull with
  | some '{' =>
      let _ ← charFull '{'
      let (contentStartLine, contentStartCol) ← currentPos
      let content ← readBracedExpansionContent
      let inner ← parseBracedExpansionContentFull content contentStartLine contentStartCol
      let _ ← charFull '}'
      mkTokenFullAt (.T_DollarBraced true inner) startLine startCol
  | some '(' =>
      let _ ← charFull '('
      match ← peekFull with
      | some '(' =>
          let _ ← charFull '('
          let content ← readArithContent
          let _ ← stringFull "))"
          let inner := match Arithmetic.parse content with
            | some arithToken => arithToken
            | none => ⟨⟨0⟩, .T_Literal content⟩
          mkTokenFullAt (.T_DollarArithmetic inner) startLine startCol
      | _ =>
          let (contentStartLine, contentStartCol) ← currentPos
          let content ← readSubshellContent
          let inner ← mkTokenFullAt (.T_Literal content) contentStartLine contentStartCol
          let _ ← charFull ')'
          mkTokenFullAt (.T_DollarExpansion [inner]) startLine startCol
  | some '\'' =>
      -- $'...' ANSI-C quoting - keep escape sequences in the raw content.
      let _ ← charFull '\''
      let content ← readAnsiCContentFull
      let _ ← charFull '\''
      mkTokenFullAt (.T_DollarSingleQuoted content) startLine startCol
  | some '"' =>
      -- $"..." locale-specific string (treated as double quoted in AST)
      let _ ← charFull '"'
      let (contentStartLine, contentStartCol) ← currentPos
      let content ← takeWhileFull (· != '"')  -- Simplified
      let inner ← mkTokenFullAt (.T_Literal content) contentStartLine contentStartCol
      let _ ← charFull '"'
      mkTokenFullAt (.T_DollarDoubleQuoted [inner]) startLine startCol
  | some c =>
      if variableStartChar c then
        let (nameStartLine, nameStartCol) ← currentPos
        let name ← takeWhile1Full variableChar
        let inner ← mkTokenFullAt (.T_Literal name) nameStartLine nameStartCol
        mkTokenFullAt (.T_DollarBraced false inner) startLine startCol
      else if specialVariableChars.toList.contains c then
        let (nameStartLine, nameStartCol) ← currentPos
        let _ ← anyCharFull
        let inner ← mkTokenFullAt (.T_Literal (String.ofList [c])) nameStartLine nameStartCol
        mkTokenFullAt (.T_DollarBraced false inner) startLine startCol
      else
        mkTokenFullAt (.T_Literal "$") startLine startCol
  | none =>
      mkTokenFullAt (.T_Literal "$") startLine startCol

/-- Read a double-quoted string. -/
partial def readDoubleQuotedFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let _ ← charFull '"'
  let parts ← readDQParts []
  let _ ← charFull '"'
  mkTokenFullAt (.T_DoubleQuoted parts) startLine startCol
where
  readDQParts (acc : List Token) : FullParser (List Token) := do
    match ← peekFull with
    | none => pure acc.reverse
    | some '"' => pure acc.reverse
    | some '\\' =>
        let (escStartLine, escStartCol) ← currentPos
        let _ ← anyCharFull
        match ← peekFull with
        | some c =>
            let _ ← anyCharFull
            let tok ← mkTokenFullAt (.T_Literal (String.ofList ['\\', c])) escStartLine escStartCol
            readDQParts (tok :: acc)
        | none => pure acc.reverse
    | some '$' =>
        let (startLine, startCol) ← currentPos
        let _ ← anyCharFull
        let tok ← readDollarInDQFull startLine startCol
        readDQParts (tok :: acc)
    | some '`' =>
        let tok ← readBacktickFull
        readDQParts (tok :: acc)
    | some _ =>
        let (litStartLine, litStartCol) ← currentPos
        let lit ← takeWhileFull fun c => c != '"' && c != '\\' && c != '$' && c != '`'
        if lit.isEmpty then pure acc.reverse
        else
          let tok ← mkTokenFullAt (.T_Literal lit) litStartLine litStartCol
          readDQParts (tok :: acc)

/-- Read process substitution <(...) or >(...) -/
partial def readProcSubFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let dir ← anyCharFull  -- < or >
  let _ ← charFull '('
  -- Read content until matching )
  let content ← readProcSubContent 1 []
  let _ ← charFull ')'
  let dirStr := String.mk [dir]
  -- For now, create a T_ProcSub with the raw content as a literal
  let contentTok ← mkTokenFullAt (.T_Literal content) startLine startCol
  mkTokenFullAt (.T_ProcSub dirStr [contentTok]) startLine startCol
where
  /-- Read until matching ) accounting for nested parens and quotes -/
  readProcSubContent (depth : Nat) (acc : List Char) : FullParser String := do
    match ← peekFull with
    | none => pure (String.ofList acc.reverse)
    | some ')' =>
        if depth <= 1 then
          pure (String.ofList acc.reverse)
        else
          let _ ← anyCharFull
          readProcSubContent (depth - 1) (')' :: acc)
    | some '(' =>
        let _ ← anyCharFull
        readProcSubContent (depth + 1) ('(' :: acc)
    | some '\'' =>
        -- Skip single-quoted content
        let _ ← anyCharFull
        let quoted ← takeWhileFull (· != '\'')
        match ← peekFull with
        | some '\'' =>
            let _ ← anyCharFull
            let newAcc := '\'' :: quoted.toList.reverse ++ ('\'' :: acc)
            readProcSubContent depth newAcc
        | _ => readProcSubContent depth ('\'' :: quoted.toList.reverse ++ ('\'' :: acc))
    | some '"' =>
        -- Skip double-quoted content (simplified - ignoring escapes within)
        let _ ← anyCharFull
        let quoted ← takeWhileFull (· != '"')
        match ← peekFull with
        | some '"' =>
            let _ ← anyCharFull
            let newAcc := '"' :: quoted.toList.reverse ++ ('"' :: acc)
            readProcSubContent depth newAcc
        | _ => readProcSubContent depth ('"' :: quoted.toList.reverse ++ ('"' :: acc))
    | some c =>
        let _ ← anyCharFull
        readProcSubContent depth (c :: acc)

end

/-- Read a complete word (multiple parts) -/
partial def readWordFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let parts ← readWordParts []
  if parts.isEmpty then
    failure
  else
    mkTokenFullAt (.T_NormalWord parts) startLine startCol
where
  readWordParts (acc : List Token) : FullParser (List Token) := do
    match ← peekFull with
    | none => pure acc.reverse
    | some c =>
        -- Check for process substitution <(...) or >(...) first
        if c == '<' || c == '>' then
          let nextTwo ← peekStringFull 2
          if nextTwo == "<(" || nextTwo == ">(" then
            let tok ← readProcSubFull
            readWordParts (tok :: acc)
          else
            -- Regular < or > is an operator, stop word
            pure acc.reverse
        else if c.isWhitespace || isOperatorStart c || c == '#' then
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
          let (startLine, startCol) ← currentPos
          let _ ← anyCharFull
          let tok ← readDollarFull startLine startCol
          readWordParts (tok :: acc)
        else if c == '\\' then
          let (escStartLine, escStartCol) ← currentPos
          let _ ← anyCharFull
          match ← peekFull with
          | some '\n' =>
              let _ ← anyCharFull
              readWordParts acc  -- Line continuation
          | some ec =>
              let _ ← anyCharFull
              let tok ← mkTokenFullAt (.T_Literal (String.ofList [ec])) escStartLine escStartCol
              readWordParts (tok :: acc)
          | none =>
              let tok ← mkTokenFullAt (.T_Literal "\\") escStartLine escStartCol
              readWordParts (tok :: acc)
        else
          let tok ← readLiteralFull
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
partial def readPatternWordFull : FullParser Token := do
  let (startLine, startCol) ← currentPos
  let parts ← readParts [] none [] 0 false 0 false
  if parts.isEmpty then
    failure
  else
    mkTokenFullAt (.T_NormalWord parts) startLine startCol
where
  flushLiteral (acc : List Token) (litStart : Option (Nat × Nat)) (litRev : List Char) :
      FullParser (List Token) := do
    match litStart with
    | none => pure acc
    | some (line, col) =>
        let s := String.ofList litRev.reverse
        if s.isEmpty then
          pure acc
        else
          let tok ← mkTokenFullAt (.T_Literal s) line col
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

  updateDepth (parenDepth : Nat) (inClass : Bool) (c : Char) : Nat :=
    if inClass then
      parenDepth
    else if c == '(' then
      parenDepth + 1
    else if c == ')' then
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
      : FullParser (List Token) := do
    match ← peekFull with
    | none => do
        let acc ← flushLiteral acc litStart litRev
        pure acc.reverse
    | some c =>
        -- Stop on case-pattern separators only when not nested.
        if parenDepth == 0 && !inClass && (c == '|' || c == ')') then
          let acc ← flushLiteral acc litStart litRev
          pure acc.reverse
        else if c.isWhitespace || c == '#' ||
            (isOperatorStart c && c != '(' && c != ')' && c != '|') then
          let acc ← flushLiteral acc litStart litRev
          pure acc.reverse
        else if c == '\'' then
          let acc ← flushLiteral acc litStart litRev
          let tok ← readSingleQuotedFull
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation
        else if c == '"' then
          let acc ← flushLiteral acc litStart litRev
          let tok ← readDoubleQuotedFull
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation
        else if c == '`' then
          let acc ← flushLiteral acc litStart litRev
          let tok ← readBacktickFull
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation
        else if c == '$' then
          let acc ← flushLiteral acc litStart litRev
          let (dl, dc) ← currentPos
          let _ ← anyCharFull
          let tok ← readDollarFull dl dc
          readParts (tok :: acc) none [] parenDepth inClass classChars sawNegation
        else if c == '\\' then
          let (escLine, escCol) ← currentPos
          let _ ← anyCharFull
          match ← peekFull with
          | some '\n' =>
              let _ ← anyCharFull
              readParts acc litStart litRev parenDepth inClass classChars sawNegation
          | some ec =>
              let _ ← anyCharFull
              let litStart := litStart <|> some (escLine, escCol)
              readParts acc litStart (ec :: litRev) parenDepth inClass classChars sawNegation
          | none =>
              let litStart := litStart <|> some (escLine, escCol)
              readParts acc litStart ('\\' :: litRev) parenDepth inClass classChars sawNegation
        else
          let (litLine, litCol) ← currentPos
          let _ ← anyCharFull
          let litStart := litStart <|> some (litLine, litCol)
          let (inClass', classChars', sawNegation') := updateBracket inClass classChars sawNegation c
          let parenDepth' := updateDepth parenDepth inClass c
          readParts acc litStart (c :: litRev) parenDepth' inClass' classChars' sawNegation'
/-- Read arithmetic content for `(( .. ))` / `for (( .. ))` (does not consume the closing `))`). -/
@[inline] def readArithContentHelper : FullParser String :=
  readArithContent

end ShellCheck.Parser.Word
