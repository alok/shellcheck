/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Word parsing: literals, quotes, dollar expansions
-/

import ShellCheck.AST
import ShellCheck.Parser.Core
import ShellCheck.Parser.Lexer

namespace ShellCheck.Parser.Word

open ShellCheck.AST
open ShellCheck.Parser.Core
open ShellCheck.Parser.Lexer

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

/-- Helper to read until a terminator string -/
partial def readUntilStr (terminator : String) : FullParser String := do
  let rec go (acc : List Char) (depth : Nat) : FullParser String := do
    match ← peekFull with
    | none => pure (String.ofList acc.reverse)
    | some c =>
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
          | some _ => pure (String.ofList acc.reverse)
          | none =>
              let _ ← anyCharFull
              go (c :: acc) depth
        else
          let _ ← anyCharFull
          go (c :: acc) depth
  go [] 0

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

/-- Read arithmetic content until )) -/
partial def readArithContent : FullParser String := do
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

/-- Read subshell content until ) -/
partial def readSubshellContent : FullParser String := do
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
        let content ← takeWhileFull (· != '}')
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
        let _ ← charFull '\''
        let content ← takeWhileFull (· != '\'')
        let _ ← charFull '\''
        mkTokenFull (.T_DollarSingleQuoted content)
    | some '"' =>
        let _ ← charFull '"'
        let content ← takeWhileFull (· != '"')
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

/-- Read arithmetic content helper (for for-loops) -/
partial def readArithContentHelper : FullParser String := do
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

end ShellCheck.Parser.Word
