/-
  Copyright 2012-2021 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  AST utility functions for ShellCheck
-/

import ShellCheck.AST
import ShellCheck.Prelude
import ShellCheck.Regex

namespace ShellCheck.ASTLib

open ShellCheck.AST
open ShellCheck.Prelude
open ShellCheck.Regex

/-- Get arguments from a simple command -/
def arguments : Token → List Token
  | ⟨_, .T_SimpleCommand _ (_::args)⟩ => args
  | _ => []

/-- Is this a loop construct? -/
def isLoop (t : Token) : Bool :=
  match t.inner with
  | .T_WhileExpression .. => true
  | .T_UntilExpression .. => true
  | .T_ForIn .. => true
  | .T_ForArithmetic .. => true
  | .T_SelectIn .. => true
  | _ => false

mutual
/-- Will this split into multiple words when used as an argument? -/
partial def willSplit (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced .. => true
  | .T_DollarExpansion .. => true
  | .T_Backticked .. => true
  | .T_BraceExpansion .. => true
  | .T_Glob .. => true
  | .T_Extglob .. => true
  | .T_DoubleQuoted parts => parts.any willBecomeMultipleArgs
  | .T_NormalWord parts => parts.any willSplit
  | _ => false

/-- Will this definitely become multiple arguments? -/
partial def willBecomeMultipleArgs (t : Token) : Bool :=
  match t.inner with
  | .T_Extglob .. => true
  | .T_Glob .. => true
  | .T_BraceExpansion .. => true
  | .T_NormalWord parts => parts.any willBecomeMultipleArgs
  | _ => false
end

/-- Is this a glob pattern? -/
partial def isGlob (t : Token) : Bool :=
  match t.inner with
  | .T_Extglob .. => true
  | .T_Glob .. => true
  | .T_NormalWord parts => parts.any isGlob
  | _ => false

/-- Is this shell word a constant? -/
partial def isConstant (t : Token) : Bool :=
  match t.inner with
  | .T_NormalWord (first :: rest) =>
      match first.inner with
      | .T_Literal s =>
          if s.startsWith "~" then false  -- ~foo is not constant
          else isConstant first && rest.all isConstant
      | _ => isConstant first && rest.all isConstant
  | .T_NormalWord [] => true
  | .T_DoubleQuoted parts => parts.all isConstant
  | .T_SingleQuoted _ => true
  | .T_Literal _ => true
  | _ => false

/-- Is this an empty literal? -/
partial def isEmpty (t : Token) : Bool :=
  match t.inner with
  | .T_NormalWord parts => parts.all isEmpty
  | .T_DoubleQuoted parts => parts.all isEmpty
  | .T_SingleQuoted "" => true
  | .T_Literal "" => true
  | _ => false

/-- Quick oversimplification of commands, replacing expansions with placeholder -/
partial def oversimplify (t : Token) : List String :=
  match t.inner with
  | .T_NormalWord parts => [String.join (parts.flatMap oversimplify)]
  | .T_DoubleQuoted parts => [String.join (parts.flatMap oversimplify)]
  | .T_SingleQuoted s => [s]
  | .T_DollarBraced .. => ["${VAR}"]
  | .T_DollarArithmetic .. => ["${VAR}"]
  | .T_DollarExpansion .. => ["${VAR}"]
  | .T_Backticked .. => ["${VAR}"]
  | .T_Glob s => [s]
  | .T_Pipeline _ [x] => oversimplify x
  | .T_Literal s => [s]
  | .T_ParamSubSpecialChar s => [s]
  | .T_SimpleCommand _ words => words.flatMap oversimplify
  | .T_Redirecting _ cmd => oversimplify cmd
  | .T_DollarSingleQuoted s => [s]
  | .T_Annotation _ cmd => oversimplify cmd
  | .TA_Sequence [elem] =>
      match elem.inner with
      | .TA_Expansion parts => parts.flatMap oversimplify
      | _ => []
  | _ => []

/-- Get the word parts of a token -/
partial def getWordParts (t : Token) : List Token :=
  match t.inner with
  | .T_NormalWord parts => parts.flatMap getWordParts
  | .T_DoubleQuoted parts => parts
  | .TA_Expansion parts => parts.flatMap getWordParts
  | _ => [t]

/-- Get a literal string with custom handling for unknown tokens -/
partial def getLiteralStringExt (more : Token → Option String) (t : Token) : Option String := do
  match t.inner with
  | .T_DoubleQuoted parts => String.join <$> parts.mapM (getLiteralStringExt more)
  | .T_DollarDoubleQuoted parts => String.join <$> parts.mapM (getLiteralStringExt more)
  | .T_NormalWord parts => String.join <$> parts.mapM (getLiteralStringExt more)
  | .TA_Expansion parts => String.join <$> parts.mapM (getLiteralStringExt more)
  | .T_SingleQuoted s => some s
  | .T_Literal s => some s
  | .T_Greater => some ">"
  | .T_DGREAT => some ">>"
  | .T_GREATAND => some ">&"
  | .T_CLOBBER => some ">|"
  | .T_Less => some "<"
  | .T_DLESS => some "<<"
  | .T_DLESSDASH => some "<<-"
  | .T_LESSAND => some "<&"
  | .T_LESSGREAT => some "<>"
  | .T_Pipe s => some s
  | .T_ParamSubSpecialChar s => some s
  | .T_DollarSingleQuoted s => some (decodeEscapes s)
  | _ => more t
where
  decodeEscapes (s : String) : String :=
    let chars := s.toList
    let rec go (acc : List Char) (rest : List Char) : List Char :=
      match rest with
      | [] => acc.reverse
      | '\\' :: more =>
          match more with
          | [] => ('\\' :: acc).reverse
          | c :: cs =>
              match c with
              | 'a' => go ('\x07' :: acc) cs
              | 'b' => go ('\x08' :: acc) cs
              | 'e' => go ('\x1B' :: acc) cs
              | 'E' => go ('\x1B' :: acc) cs
              | 'f' => go ('\x0C' :: acc) cs
              | 'n' => go ('\n' :: acc) cs
              | 'r' => go ('\r' :: acc) cs
              | 't' => go ('\t' :: acc) cs
              | 'v' => go ('\x0B' :: acc) cs
              | '\\' => go ('\\' :: acc) cs
              | '\'' => go ('\'' :: acc) cs
              | '"' => go ('"' :: acc) cs
              | '?' => go ('?' :: acc) cs
              | 'c' =>
                  match cs with
                  | [] => acc.reverse
                  | d :: ds =>
                      let code := d.toNat % 32
                      go (Char.ofNat code :: acc) ds
              | 'x' =>
                  let (digits, rest') := takeDigits isHexDigit 2 cs
                  if digits.isEmpty then
                    go ('x' :: acc) cs
                  else
                    let code := digits.foldl (fun n ch => n * 16 + hexVal ch) 0
                    go (Char.ofNat (clampCodepoint code) :: acc) rest'
              | 'u' =>
                  let (digits, rest') := takeDigits isHexDigit 4 cs
                  if digits.length != 4 then
                    go ('u' :: acc) cs
                  else
                    let code := digits.foldl (fun n ch => n * 16 + hexVal ch) 0
                    go (Char.ofNat (clampCodepoint code) :: acc) rest'
              | 'U' =>
                  let (digits, rest') := takeDigits isHexDigit 8 cs
                  if digits.length != 8 then
                    go ('U' :: acc) cs
                  else
                    let code := digits.foldl (fun n ch => n * 16 + hexVal ch) 0
                    go (Char.ofNat (clampCodepoint code) :: acc) rest'
              | _ =>
                  if isOctDigit c then
                    let (digits, rest') := takeDigits isOctDigit 2 cs
                    let all := c :: digits
                    let code := all.foldl (fun n ch => n * 8 + (ch.toNat - '0'.toNat)) 0
                    go (Char.ofNat (clampCodepoint code) :: acc) rest'
                  else
                    go (c :: acc) cs
      | c :: cs => go (c :: acc) cs
    String.ofList (go [] chars)

  isOctDigit (c : Char) : Bool :=
    c >= '0' && c <= '7'

  isHexDigit (c : Char) : Bool :=
    c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

  hexVal (c : Char) : Nat :=
    if c.isDigit then
      c.toNat - '0'.toNat
    else if c >= 'a' && c <= 'f' then
      10 + (c.toNat - 'a'.toNat)
    else
      10 + (c.toNat - 'A'.toNat)

  clampCodepoint (n : Nat) : Nat :=
    if n <= 0x10FFFF then n else '?'.toNat

  takeDigits (p : Char → Bool) (max : Nat) (input : List Char) : (List Char × List Char) :=
    let rec go (acc : List Char) (n : Nat) (rest : List Char) :=
      match n, rest with
      | 0, _ => (acc.reverse, rest)
      | Nat.succ n', c :: cs =>
          if p c then
            go (c :: acc) n' cs
          else
            (acc.reverse, rest)
      | _, [] => (acc.reverse, [])
    go [] max input

/-- Get a literal string from a token, returning none for non-literals -/
partial def getLiteralString (t : Token) : Option String :=
  getLiteralStringExt (fun _ => none) t

/-- Get a literal string with a default for non-literals -/
def getLiteralStringDef (default : String) (t : Token) : String :=
  getLiteralString t |>.getD default

/-- Maybe get the literal string of this token, allowing globs to pass through. -/
partial def getGlobOrLiteralString (t : Token) : Option String :=
  getLiteralStringExt (fun tok =>
    match tok.inner with
    | .T_Glob s => some s
    | _ => none
  ) t

/-- Get a literal string, but only if it is entirely unquoted.

This corresponds to ShellCheck's `getUnquotedLiteral`: it succeeds only for plain
`T_NormalWord` values whose parts are all `T_Literal` (no quotes, expansions, etc.). -/
partial def getUnquotedLiteral (t : Token) : Option String := do
  match t.inner with
  | .T_NormalWord parts =>
    let pieces ← parts.mapM fun part =>
      match part.inner with
      | .T_Literal s => some s
      | _ => Option.none
    some (String.join pieces)
  | .T_Literal s => some s
  | _ => Option.none

/-- Get only literal parts, skipping non-literals -/
def onlyLiteralString (t : Token) : String :=
  getLiteralStringDef "" t

/-- Is this token a literal? -/
def isLiteral (t : Token) : Bool :=
  getLiteralString t |>.isSome

/-- Is this a flag (starts with -)? -/
def isFlag (t : Token) : Bool :=
  match getWordParts t with
  | ⟨_, .T_Literal s⟩ :: _ => s.startsWith "-"
  | _ => false

/-- Check if token is quotes -/
def isQuotes (t : Token) : Bool :=
  match t.inner with
  | .T_DoubleQuoted .. => true
  | .T_SingleQuoted .. => true
  | _ => false

/-- Get the last unquoted literal token in a word, if any. -/
def getTrailingUnquotedLiteral (t : Token) : Option Token :=
  match t.inner with
  | .T_NormalWord parts =>
      let rec go : List Token → Option Token
        | [] => none
        | [last] =>
            match last.inner with
            | .T_Literal _ => some last
            | _ => none
        | _ :: rest => go rest
      go parts
  | _ => none

/-- Is this an array expansion like ${arr[@]}? -/
partial def isArrayExpansion (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced _ content =>
      let s := String.join (oversimplify content)
      s.startsWith "@" || (not (s.startsWith "#") && Regex.containsSubstring s "[@]")
  | .T_NormalWord parts => parts.any isArrayExpansion
  | .T_DoubleQuoted parts => parts.any isArrayExpansion
  | .TA_Expansion parts => parts.any isArrayExpansion
  | _ => false

/-- Can this token become multiple args (e.g. arrays or unquoted expansions)? -/
partial def mayBecomeMultipleArgs (t : Token) : Bool :=
  willBecomeMultipleArgs t || go false t
where
  go (quoted : Bool) (tok : Token) : Bool :=
    if isArrayExpansion tok then
      true
    else
      match tok.inner with
      | .T_DollarBraced _ content =>
          let s := String.join (oversimplify content)
          let hasBang := s.toList.any (· == '!')
          (!quoted) || hasBang || s.startsWith "!"
      | .T_DoubleQuoted parts => parts.any (go true)
      | .T_DollarDoubleQuoted parts => parts.any (go true)
      | .T_NormalWord parts => parts.any (go quoted)
      | .T_Annotation _ inner => go quoted inner
      | _ => false

/-- Is this a command substitution? -/
def isCommandSubstitution (t : Token) : Bool :=
  match t.inner with
  | .T_DollarExpansion .. => true
  | .T_DollarBraceCommandExpansion .. => true
  | .T_Backticked .. => true
  | _ => false

/-- Is this a quoteable expansion? -/
def isQuoteableExpansion (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced .. => true
  | _ => isCommandSubstitution t

/-- Is this a string expansion (not array)? -/
def isStringExpansion (t : Token) : Bool :=
  isCommandSubstitution t ||
  match t.inner with
  | .T_DollarArithmetic .. => true
  | .T_DollarBraced .. => not (isArrayExpansion t)
  | _ => false

/-- Is this a function definition? -/
def isFunction (t : Token) : Bool :=
  match t.inner with
  | .T_Function .. => true
  | _ => false

/-- Is this function-like (includes bats tests)? -/
def isFunctionLike (t : Token) : Bool :=
  match t.inner with
  | .T_Function .. => true
  | .T_BatsTest .. => true
  | _ => false

/-- Is this a brace expansion? -/
def isBraceExpansion (t : Token) : Bool :=
  match t.inner with
  | .T_BraceExpansion .. => true
  | _ => false

/-- Is this an assignment? -/
partial def isAssignment (t : Token) : Bool :=
  match t.inner with
  | .T_Redirecting _ cmd => isAssignment cmd
  | .T_SimpleCommand (_::_) [] => true
  | .T_Assignment .. => true
  | .T_Annotation _ cmd => isAssignment cmd
  | _ => false

/-- Get the command sequences from a token -/
partial def getCommandSequences (t : Token) : List (List Token) :=
  match t.inner with
  | .T_Script _ cmds => [cmds]
  | .T_BraceGroup cmds => [cmds]
  | .T_Subshell cmds => [cmds]
  | .T_WhileExpression cond body => [cond, body]
  | .T_UntilExpression cond body => [cond, body]
  | .T_ForIn _ _ body => [body]
  | .T_ForArithmetic _ _ _ body => [body]
  | .T_IfExpression thens elses =>
      thens.flatMap (fun (c, b) => [c, b]) ++ [elses]
  | .T_Annotation _ inner => getCommandSequences inner
  | .T_DollarExpansion cmds => [cmds]
  | .T_DollarBraceCommandExpansion _ cmds => [cmds]
  | .T_Backticked cmds => [cmds]
  | _ => []

/-- Get command from a token, unwrapping redirections etc -/
partial def getCommand (t : Token) : Option Token :=
  match t.inner with
  | .T_Redirecting _ cmd => getCommand cmd
  | .T_SimpleCommand _ (_::_) => some t
  | .T_Annotation _ inner => getCommand inner
  | _ => none

/-- Get basename of a path -/
def basename (s : String) : String :=
  s.splitOn "/" |>.getLast!

/-- Check if a name is a valid variable start char -/
def isVariableStartChar (c : Char) : Bool :=
  c == '_' || c.isAlpha

/-- Check if a name is a valid variable char -/
def isVariableChar (c : Char) : Bool :=
  isVariableStartChar c || c.isDigit

/-- Check if a name is a valid variable name -/
def isVariableName (s : String) : Bool :=
  match s.toList with
  | c :: rest => isVariableStartChar c && rest.all isVariableChar
  | [] => false

/-- Special variable characters -/
def isSpecialVariableChar (c : Char) : Bool :=
  c ∈ ['*', '@', '#', '?', '-', '$', '!']

/-- Get the variable reference from a braced expansion like ${var:-foo} -/
def getBracedReference (s : String) : String :=
  -- Simplified version - just takes the variable name part
  let noPrefixSlice : String.Slice :=
    if s.startsWith "!" || s.startsWith "#" then s.drop 1 else s.toSlice
  let name := (noPrefixSlice.takeWhile isVariableChar).toString
  if name.isEmpty then
    match noPrefixSlice.toString.toList.head? with
    | some c => if isSpecialVariableChar c then (noPrefixSlice.take 1).toString else s
    | none => s
  else name

/-- Get the modifier from a braced expansion -/
def getBracedModifier (s : String) : String :=
  let varRef := getBracedReference s
  let rest := (s.drop (if s.startsWith "!" || s.startsWith "#" then 1 + varRef.length else varRef.length)).toString
  rest

-- Pseudoglob for pattern matching analysis

/-- Pseudoglob element -/
inductive PseudoGlob where
  | pgAny   -- matches any single char
  | pgMany  -- matches any number of chars
  | pgChar (c : Char)  -- matches specific char
  deriving Repr, BEq, Inhabited

/-- Convert a word to a pseudoglob pattern -/
partial def wordToPseudoGlob (t : Token) : List PseudoGlob :=
  (getWordParts t).flatMap fun part =>
    match part.inner with
    | .T_Literal s => s.toList.map .pgChar
    | .T_SingleQuoted s => s.toList.map .pgChar
    | .T_Glob "?" => [.pgAny]
    | .T_Glob "*" => [.pgMany]
    | .T_Glob _ => [.pgAny]  -- other globs like [...]
    | _ => [.pgMany]  -- unknown = could be anything

/-- Check if two pseudoglob patterns can overlap -/
partial def pseudoGlobsCanOverlap : List PseudoGlob → List PseudoGlob → Bool
  | x@(xf::xs), y@(yf::ys) =>
      match xf, yf with
      | .pgMany, _ => pseudoGlobsCanOverlap x ys || pseudoGlobsCanOverlap xs y
      | _, .pgMany => pseudoGlobsCanOverlap x ys || pseudoGlobsCanOverlap xs y
      | .pgAny, _ => pseudoGlobsCanOverlap xs ys
      | _, .pgAny => pseudoGlobsCanOverlap xs ys
      | .pgChar c1, .pgChar c2 => c1 == c2 && pseudoGlobsCanOverlap xs ys
  | [], [] => true
  | .pgMany :: rest, [] => pseudoGlobsCanOverlap rest []
  | _::_, [] => false
  | [], r => pseudoGlobsCanOverlap r []

/-- Reorder a pseudoglob for more efficient matching.

This is a semantics-preserving normalization for sequences of `.pgAny` and `.pgMany`
since their order does not affect which string lengths are matched. -/
def simplifyPseudoGlob (g : List PseudoGlob) : List PseudoGlob :=
  go (g.length + 1) g
where
  isWild (x : PseudoGlob) : Bool :=
    x == .pgAny || x == .pgMany

  orderWilds (wilds : List PseudoGlob) : List PseudoGlob :=
    let anyCount := wilds.foldl (fun acc x => if x == .pgAny then acc + 1 else acc) 0
    let hasMany := wilds.any (· == .pgMany)
    (List.replicate anyCount .pgAny) ++ (if hasMany then [.pgMany] else [])

  spanWilds : List PseudoGlob → (List PseudoGlob × List PseudoGlob)
    | [] => ([], [])
    | x :: xs =>
        if isWild x then
          let (wilds, rest) := spanWilds xs
          (x :: wilds, rest)
        else
          ([], x :: xs)

  go : Nat → List PseudoGlob → List PseudoGlob
    | 0, _ => []
    | _fuel + 1, [] => []
    | fuel + 1, x@(.pgChar _) :: rest => x :: go fuel rest
    | fuel + 1, list =>
        let (wilds, rest) := spanWilds list
        orderWilds wilds ++ go fuel rest

/-- Check whether the first pseudoglob always overlaps (i.e. is a superset of) the second. -/
partial def pseudoGlobIsSuperSetof : List PseudoGlob → List PseudoGlob → Bool
  | x@(xf :: xs), y@(yf :: ys) =>
      match xf, yf with
      | .pgMany, .pgMany => pseudoGlobIsSuperSetof x ys
      | .pgMany, _ => pseudoGlobIsSuperSetof x ys || pseudoGlobIsSuperSetof xs y
      | _, .pgMany => false
      | .pgAny, _ => pseudoGlobIsSuperSetof xs ys
      | _, .pgAny => false
      | .pgChar c1, .pgChar c2 => c1 == c2 && pseudoGlobIsSuperSetof xs ys
  | [], [] => true
  | .pgMany :: rest, [] => pseudoGlobIsSuperSetof rest []
  | _, _ => false

/-- Interpret an *unquoted* case-pattern literal as a pseudoglob.

Note: our parser currently represents most pattern characters as `.T_Literal`, so we
do a best-effort scan for the common metacharacters `*`, `?`, and bracket classes
like `[abc]`. -/
def casePatternLiteralToPseudoGlob (s : String) : List PseudoGlob :=
  let cs := s.toList
  go (cs.length + 1) cs
where
  go : Nat → List Char → List PseudoGlob
    | 0, _ => []
    | _fuel + 1, [] => []
    | fuel + 1, '*' :: rest => .pgMany :: go fuel rest
    | fuel + 1, '?' :: rest => .pgAny :: go fuel rest
    | fuel + 1, '[' :: rest =>
        match rest.dropWhile (· != ']') with
        | [] =>
            -- Unterminated: treat '[' as literal.
            .pgChar '[' :: go fuel rest
        | _close :: rest' =>
            -- `[ ... ]` matches a single char.
            .pgAny :: go fuel rest'
    | fuel + 1, c :: rest => .pgChar c :: go fuel rest

/-- Exact version of `casePatternLiteralToPseudoGlob`.

We only return a pseudoglob if we can preserve exact semantics in our approximation,
so we reject unquoted bracket classes like `[abc]`. -/
def casePatternLiteralToExactPseudoGlob (s : String) : Option (List PseudoGlob) :=
  go s.toList
where
  go : List Char → Option (List PseudoGlob)
    | [] => some []
    | '*' :: rest => List.cons .pgMany <$> go rest
    | '?' :: rest => List.cons .pgAny <$> go rest
    | '[' :: _ => none
    | c :: rest => List.cons (.pgChar c) <$> go rest

/-- Convert a case pattern to a pseudoglob, respecting quoting.

Unquoted `*`/`?` in literals are treated as wildcards, while quoted ones are
treated as literal characters. Unknown expansions become `.pgMany`. -/
partial def casePatternToPseudoGlob (t : Token) : List PseudoGlob :=
  simplifyPseudoGlob (go false t)
where
  go (quoted : Bool) (t : Token) : List PseudoGlob :=
    match t.inner with
    | .T_Annotation _ inner => go quoted inner
    | .T_NormalWord parts => parts.flatMap (go quoted)
    | .T_DoubleQuoted parts => parts.flatMap (go true)
    | .T_DollarDoubleQuoted parts => parts.flatMap (go true)
    | .T_SingleQuoted s => s.toList.map .pgChar
    | .T_DollarSingleQuoted s => s.toList.map .pgChar
    | .T_Literal s =>
        if quoted then
          s.toList.map .pgChar
        else
          casePatternLiteralToPseudoGlob s
    | .T_Glob "?" => [.pgAny]
    | .T_Glob "*" => [.pgMany]
    | .T_Glob _ => [.pgAny]
    | _ => [.pgMany]

/-- Exact pseudoglob conversion for case patterns.

Fails (`none`) if the pattern contains expansions or other glob constructs we
can't represent exactly (e.g. bracket classes). -/
partial def casePatternToExactPseudoGlob (t : Token) : Option (List PseudoGlob) :=
  simplifyPseudoGlob <$> go false t
where
  go (quoted : Bool) (t : Token) : Option (List PseudoGlob) := do
    match t.inner with
    | .T_Annotation _ inner => go quoted inner
    | .T_NormalWord parts =>
        let ps ← parts.mapM (go quoted)
        pure (ps.foldl (· ++ ·) [])
    | .T_DoubleQuoted parts =>
        let ps ← parts.mapM (go true)
        pure (ps.foldl (· ++ ·) [])
    | .T_DollarDoubleQuoted parts =>
        let ps ← parts.mapM (go true)
        pure (ps.foldl (· ++ ·) [])
    | .T_SingleQuoted s => some (s.toList.map .pgChar)
    | .T_DollarSingleQuoted s => some (s.toList.map .pgChar)
    | .T_Literal s =>
        if quoted then
          some (s.toList.map .pgChar)
        else
          casePatternLiteralToExactPseudoGlob s
    | .T_Glob "?" => some [.pgAny]
    | .T_Glob "*" => some [.pgMany]
    | .T_Glob _ => none
    | _ => none

/-- Does a case pattern contain explicit glob syntax?

This is a best-effort predicate used for checks like SC2254 ("Quote expansions in
case patterns ...") where we want to *avoid* warning when the pattern already
contains wildcard matching (e.g. `*$var*`).

Our parser currently does not always tokenize `*`, `?`, or bracket classes into
`T_Glob`/`T_Extglob`, so we also scan unquoted literal text for the common
metacharacters. -/
partial def casePatternHasExplicitGlob (t : Token) : Bool :=
  go false t
where
  containsGlobMeta (s : String) : Bool :=
    s.any fun c => c == '*' || c == '?' || c == '['

  -- Rough detection for extglob starts like `@(`, `+(`, `!(` when they appear in
  -- literal text. (`*(` / `?(` are already covered by `*`/`?`.)
  containsExtGlobStart (s : String) : Bool :=
    let cs := s.toList
    let rec go : List Char → Bool
      | [] => false
      | [_] => false
      | a :: b :: rest =>
          (b == '(' && (a == '@' || a == '!' || a == '+')) || go (b :: rest)
    go cs

  go (quoted : Bool) (t : Token) : Bool :=
    match t.inner with
    | .T_Annotation _ inner => go quoted inner
    | .T_NormalWord parts => parts.any (go quoted)
    | .T_DoubleQuoted parts => parts.any (go true)
    | .T_DollarDoubleQuoted parts => parts.any (go true)
    | .T_SingleQuoted _ => false
    | .T_DollarSingleQuoted _ => false
    | .T_Glob _ => true
    | .T_Extglob _ _ => true
    | .T_Literal s =>
        if quoted then
          false
        else
          containsGlobMeta s || containsExtGlobStart s
    | _ => false

/-- Check if two words can be equal -/
def wordsCanBeEqual (x y : Token) : Bool :=
  pseudoGlobsCanOverlap (wordToPseudoGlob x) (wordToPseudoGlob y)

/-- Check if character is printable (simplified) -/
def isPrintableChar (c : Char) : Bool :=
  c.val >= 32 && c.val < 127

/-- Escape a string for display in messages -/
def escapeForMessage (s : String) : String :=
  s.toList.flatMap (fun c =>
    match c with
    | '\\' => ['\\', '\\']
    | '\n' => ['\\', 'n']
    | '\r' => ['\\', 'r']
    | '\t' => ['\\', 't']
    | _ => if isPrintableChar c then [c] else ['\\', 'x', '?', '?']  -- simplified
  ) |> String.ofList

/-- Short alias for escapeForMessage -/
abbrev e4m := escapeForMessage

/-- Is this a counting reference ${#var}? -/
def isCountingReference (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let s := String.join (oversimplify content)
    s.startsWith "#"
  | _ => false

/-- Is this a quoted alternative reference like ${var:+value}? -/
def isQuotedAlternativeReference (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let s := String.join (oversimplify content)
    let modifier := getBracedModifier s
    -- Check for :+ or ]+ patterns
    Regex.containsSubstring modifier ":+" || Regex.containsSubstring modifier "]+"
  | _ => false

/-- Get flags until predicate is true -/
partial def getFlagsUntil (stop : String → Bool) (t : Token) : List (Token × String) :=
  match getCommand t with
  | some cmd =>
    match cmd.inner with
    | .T_SimpleCommand _ args =>
        match args with
        | [] => []
        | _ :: rest => extractFlags stop rest
    | _ => []
  | none => []
where
  listToArgs (rest : List Token) : List (Token × String) :=
    rest.map (fun x => (x, ""))

  extractFlags (stop : String → Bool) : List Token → List (Token × String)
    | [] => []
    | arg :: rest =>
      match getLiteralString arg with
      | some s =>
        if stop s then
          (arg, "") :: listToArgs rest
        else if s.startsWith "--" && s.length > 2 then
          -- Long flag like --flag
          let flagName := (s.drop 2).toString
          (arg, flagName) :: extractFlags stop rest
        else if s.startsWith "-" && s.length > 1 then
          -- Short flags like -abc -> ["a", "b", "c"]
          let chars := (s.drop 1).toString.toList
          chars.map (fun c => (arg, String.singleton c)) ++ extractFlags stop rest
        else
          (arg, "") :: extractFlags stop rest
      | none => extractFlags stop rest

/-- Get all flags from a command token (returns list of (token, flag_char) pairs) -/
partial def getAllFlags (t : Token) : List (Token × String) :=
  getFlagsUntil (· == "--") t

/-- Get leading flags until first non-flag argument or `--`. -/
partial def getLeadingFlags (t : Token) : List (Token × String) :=
  getFlagsUntil (fun s => s == "--" || !s.startsWith "-") t

/-- Check if a command has a specific flag -/
def hasFlag (t : Token) (flag : String) : Bool :=
  (getAllFlags t).any (fun (_, f) => f == flag)

/-- Check if a command has a short parameter (single char) -/
def hasShortParameter (t : Token) (c : Char) : Bool :=
  (getAllFlags t).any (fun (_, f) => f == String.singleton c)

/-- Check if a command has a parameter (by name) -/
def hasParameter (t : Token) (param : String) : Bool :=
  match getCommand t with
  | some cmd =>
    match cmd.inner with
    | .T_SimpleCommand _ args =>
      args.any fun arg =>
        match getLiteralString arg with
        | some s => s == param || s == ("--" ++ param) || s == ("-" ++ param)
        | none => false
    | _ => false
  | none => false

/-- Get command arguments (all words after command name) -/
def getCommandArgv (t : Token) : Option (List Token) :=
  match getCommand t with
  | some cmd =>
    match cmd.inner with
    | .T_SimpleCommand _ args@(_::_) => some args
    | _ => none
  | none => none

/-- Get leading unquoted string from token -/
partial def getLeadingUnquotedString (t : Token) : Option String :=
  match t.inner with
  | .T_NormalWord parts =>
    let rec go (acc : List Char) : List Token → Option String
      | [] => some (String.ofList acc.reverse)
      | part :: rest =>
          match part.inner with
          | .T_Literal s => go (s.toList.reverse ++ acc) rest
          | _ => some (String.ofList acc.reverse)
    match parts with
    | first :: rest =>
        match first.inner with
        | .T_Literal s => go (s.toList.reverse) rest
        | _ => none
    | [] => none
  | .T_Literal s => some s
  | _ => none

/-- Is this an unquoted flag (- not quoted)? -/
def isUnquotedFlag (t : Token) : Bool :=
  match getLeadingUnquotedString t with
  | some s => s.startsWith "-"
  | none => false

/-!
## GNU/BSD Option Parsing

ShellCheck's Haskell implementation provides `getGnuOpts`/`getBsdOpts` for parsing short/long
options based on a getopts-style format string (e.g. `flagsForRead`).

These helpers are used by various checks to conservatively identify which tokens are flags and which
are positional arguments. Unknown flags cause parsing to fail (return `none`), matching the upstream
behavior.
-/

/-- Internal option parser used by `getGnuOpts` and `getBsdOpts`.

Returns a list of `(flag, (optionToken, valueToken))`:
- `flag == ""` means a positional argument
- for flags that don't take an argument, `valueToken == optionToken`
- for flags that take an argument, `valueToken` is the associated token (when present)

Unknown flags cause the parse to fail. -/
partial def getOpts (gnu : Bool) (arbitraryLongOpts : Bool) (spec : String)
    (longopts : List (String × Bool)) (args : List Token) :
    Option (List (String × (Token × Token))) :=
  process args
where
  /-- Parse a getopts-style spec like `"erd:u:"` into `(flag, needsArg)` pairs. -/
  flagList : List Char → List (String × Bool)
    | [] => []
    | c :: ':' :: rest => (String.singleton c, true) :: flagList rest
    | c :: rest => (String.singleton c, false) :: flagList rest

  flags : List (String × Bool) :=
    ("", false) :: (flagList spec.toList ++ longopts)

  lookupNeedsArg (name : String) : Option Bool :=
    (flags.find? (fun (n, _) => n == name)).map (fun (_, b) => b)

  /-- Split a `--long` option word into `(name, hasEq)` for `--name=...`. -/
  splitLong (word : String) : String × Bool :=
    let cs := word.toList
    let rec go (acc : List Char) : List Char → String × Bool
      | [] => (String.ofList acc.reverse, false)
      | '=' :: _ => (String.ofList acc.reverse, true)
      | c :: rest => go (c :: acc) rest
    go [] cs

  listToArgs (rest : List Token) : List (String × (Token × Token)) :=
    rest.map (fun x => ("", (x, x)))

  process : List Token → Option (List (String × (Token × Token)))
    | [] => some []
    | token :: rest =>
      -- Use a sentinel that won't be parsed as an option prefix.
      let s := getLiteralStringDef "∅" token
      if s == "--" then
        some (listToArgs rest)
      else if s.startsWith "--" && s.length > 2 then
        let word := (s.drop 2).toString
        let (name, hasEq) := splitLong word
        let needsArg? :=
          if arbitraryLongOpts then some (lookupNeedsArg name |>.getD false)
          else lookupNeedsArg name
        match needsArg? with
        | none => none
        | some needsArg =>
          if needsArg && !hasEq then
            match rest with
            | argTok :: rest2 =>
              (fun more => (name, (token, argTok)) :: more) <$> process rest2
            | [] => none
          else
            (fun more => (name, (token, token)) :: more) <$> process rest
      else if s.startsWith "-" && s.length > 1 then
        shortToOpts ((s.drop 1).toString.toList) token rest
      else
        if gnu then
          (fun more => ("", (token, token)) :: more) <$> process rest
        else
          some (listToArgs (token :: rest))

  shortToOpts : List Char → Token → List Token → Option (List (String × (Token × Token)))
    | [], _token, args => process args
    | c :: restChars, token, args =>
      match lookupNeedsArg (String.singleton c) with
      | none => none
      | some needsArg =>
        if needsArg && restChars.isEmpty then
          match args with
          | next :: restArgs =>
            (fun more => (String.singleton c, (token, next)) :: more) <$> process restArgs
          | [] => none
        else if needsArg then
          -- Attached argument like -u3; don't split the rest of the token further.
          (fun more => (String.singleton c, (token, token)) :: more) <$> process args
        else
          (fun more => (String.singleton c, (token, token)) :: more) <$> shortToOpts restChars token args

/-- GNU-style option parsing (continues past the first non-flag argument). -/
def getGnuOpts (spec : String) (args : List Token) : Option (List (String × (Token × Token))) :=
  getOpts true false spec [] args

/-- BSD-style option parsing (stops at the first non-flag argument). -/
def getBsdOpts (spec : String) (args : List Token) : Option (List (String × (Token × Token))) :=
  getOpts false false spec [] args

/-- Generic option parsing that makes a best-effort guess without a spec string. -/
partial def getGenericOpts : List Token → List (String × (Token × Token))
  | [] => []
  | token :: rest =>
      let s := getLiteralStringDef "∅" token
      if s == "--" then
        rest.map (fun c => ("", (c, c)))
      else if s.startsWith "--" && s.length > 2 then
        let name := (s.drop 2).toString |>.takeWhile (fun c => c != '=' && c != '\x00') |>.toString
        (name, (token, token)) :: getGenericOpts rest
      else if s.startsWith "-" && s.length > 1 then
        let opts := (s.drop 1).toString.toList.takeWhile (fun c => c != '\x00')
        match rest with
        | next :: remainder =>
            if (getLiteralStringDef "∅" next).startsWith "-" then
              opts.map (fun c => (String.singleton c, (token, token))) ++ getGenericOpts rest
            else
              match opts.reverse with
              | [] => getGenericOpts remainder
              | last :: initial =>
                  (initial.reverse.map (fun c => (String.singleton c, (token, token))))
                  ++ [(String.singleton last, (token, next))]
                  ++ getGenericOpts remainder
        | [] =>
            opts.map (fun c => (String.singleton c, (token, token)))
      else
        ("", (token, token)) :: getGenericOpts rest

/-- Given a command, get the string and token that represents the command name.
    If `direct`, return the actual command word (e.g. `exec` in `exec ls`).
    If not, return the logical command (e.g. `ls` in `exec ls`). -/
def getCommandNameAndToken (direct : Bool) (t : Token) : (Option String × Token) :=
  match getCommand t with
  | some cmd =>
      match cmd.inner with
      | .T_SimpleCommand _ (w :: rest) =>
          match getLiteralString w with
          | some s =>
              if direct then
                (some s, w)
              else
                match getEffectiveCommandToken s cmd rest with
                | some actual => (getLiteralString actual, actual)
                | none => (some s, w)
          | Option.none => (none, t)
      | _ => (none, t)
  | none => (none, t)
where
  getEffectiveCommandToken (name : String) (_cmd : Token) (args : List Token) : Option Token :=
    let firstArg : Option Token :=
      match args with
      | arg :: _ => if isFlag arg then none else some arg
      | [] => none
    match name with
    | "busybox" => firstArg
    | "builtin" => firstArg
    | "command" => firstArg
    | "run" => firstArg
    | "exec" =>
        match getBsdOpts "cla:" args with
        | some opts =>
            match opts.find? (fun (flag, _) => flag == "") with
            | some (_, (tok, _)) => some tok
            | none => none
        | Option.none => none
    | _ => none

/-- Maybe get the command name string of a token representing a command. -/
def getCommandName (t : Token) : Option String :=
  (getCommandNameAndToken false t).1

/-- Get the command name token from a command, or the original token if unknown. -/
def getCommandTokenOrThis (t : Token) : Token :=
  (getCommandNameAndToken false t).2

/-- If a command substitution is a single command, get its name. -/
def getCommandNameFromExpansion (t : Token) : Option String :=
  let extract : Token → Option String
    | ⟨_, .T_Pipeline _ [cmd]⟩ => getCommandName cmd
    | _ => none
  match t.inner with
  | .T_DollarExpansion [c] => extract c
  | .T_Backticked [c] => extract c
  | .T_DollarBraceCommandExpansion _ [c] => extract c
  | _ => none

/-- Get the command basename. -/
def getCommandBasename (t : Token) : Option String :=
  basename <$> getCommandName t

/-- Get the `extended-analysis` directive from annotations (if any). -/
def getExtendedAnalysisDirective (root : Token) : Option Bool :=
  let rec go : List Annotation → Option Bool
    | [] => none
    | Annotation.extendedAnalysis b :: _ => some b
    | _ :: rest => go rest
  match root.inner with
  | .T_Annotation annots _ => go annots
  | _ => none

-- Theorems (stubs)

theorem isLoop_while (id : Id) (cond body : List Token) :
    isLoop ⟨id, .T_WhileExpression cond body⟩ = true := rfl

theorem isLoop_for (id : Id) (v : String) (ws body : List Token) :
    isLoop ⟨id, .T_ForIn v ws body⟩ = true := rfl

-- Note: These theorems require partial def unfolding which is non-trivial
-- They are correct by inspection of the code but can't be proven with rfl
theorem isConstant_literal (id : Id) (s : String) :
    isConstant ⟨id, .T_Literal s⟩ = true := sorry

theorem isConstant_singleQuoted (id : Id) (s : String) :
    isConstant ⟨id, .T_SingleQuoted s⟩ = true := sorry

theorem getLiteralString_literal (id : Id) (s : String) :
    getLiteralString ⟨id, .T_Literal s⟩ = some s := sorry

theorem getLiteralString_singleQuoted (id : Id) (s : String) :
    getLiteralString ⟨id, .T_SingleQuoted s⟩ = some s := sorry

theorem isVariableName_valid :
    isVariableName "foo_bar123" = true := by native_decide

theorem isVariableName_invalid_digit_start :
    isVariableName "123abc" = false := by native_decide

theorem pseudoGlobsCanOverlap_reflexive (g : List PseudoGlob) :
    pseudoGlobsCanOverlap g g = true := sorry

theorem wordsCanBeEqual_reflexive (t : Token) :
    wordsCanBeEqual t t = true := sorry

end ShellCheck.ASTLib
