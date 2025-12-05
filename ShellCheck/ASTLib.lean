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
  | .T_ParamSubSpecialChar s => some s
  | .T_DollarSingleQuoted s => some (decodeEscapes s)
  | _ => more t
where
  decodeEscapes (s : String) : String :=
    -- TODO: Implement proper $'...' escape decoding
    s

/-- Get a literal string from a token, returning none for non-literals -/
partial def getLiteralString (t : Token) : Option String :=
  getLiteralStringExt (fun _ => none) t

/-- Get a literal string with a default for non-literals -/
def getLiteralStringDef (default : String) (t : Token) : String :=
  getLiteralString t |>.getD default

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

/-- Is this an array expansion like ${arr[@]}? -/
def isArrayExpansion (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced _ content =>
      let s := String.join (oversimplify content)
      s.startsWith "@" || (not (s.startsWith "#") && Regex.containsSubstring s "[@]")
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

/-- Get the command name string -/
def getCommandName (t : Token) : Option String := do
  let cmd ← getCommand t
  match cmd.inner with
  | .T_SimpleCommand _ (w::_) => getLiteralString w
  | _ => none

/-- Get basename of a path -/
def basename (s : String) : String :=
  s.splitOn "/" |>.getLast!

/-- Get the command basename -/
def getCommandBasename (t : Token) : Option String :=
  basename <$> getCommandName t

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
  let noPrefix := if s.startsWith "!" || s.startsWith "#" then s.drop 1 else s
  let name := noPrefix.takeWhile isVariableChar
  if name.isEmpty then
    match noPrefix.toList.head? with
    | some c => if isSpecialVariableChar c then noPrefix.take 1 else s
    | none => s
  else name

/-- Get the modifier from a braced expansion -/
def getBracedModifier (s : String) : String :=
  let varRef := getBracedReference s
  let rest := s.drop (if s.startsWith "!" || s.startsWith "#" then 1 + varRef.length else varRef.length)
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
    | .T_SimpleCommand _ args => extractFlags stop args
    | _ => []
  | none => []
where
  extractFlags (stop : String → Bool) : List Token → List (Token × String)
    | [] => []
    | arg :: rest =>
      match getLiteralString arg with
      | some s =>
        if stop s then []
        else if s.startsWith "--" && s.length > 2 then
          -- Long flag like --flag
          let flagName := s.drop 2
          (arg, flagName) :: extractFlags stop rest
        else if s.startsWith "-" && s.length > 1 then
          -- Short flags like -abc -> ["a", "b", "c"]
          let chars := (s.drop 1).toList
          chars.map (fun c => (arg, String.singleton c)) ++ extractFlags stop rest
        else
          extractFlags stop rest
      | none => extractFlags stop rest

/-- Get all flags from a command token (returns list of (token, flag_char) pairs) -/
partial def getAllFlags (t : Token) : List (Token × String) :=
  getFlagsUntil (· == "--") t

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
    match parts with
    | first :: _ =>
      match first.inner with
      | .T_Literal s => some s
      | _ => none
    | [] => some ""
  | .T_Literal s => some s
  | _ => none

/-- Is this an unquoted flag (- not quoted)? -/
def isUnquotedFlag (t : Token) : Bool :=
  match getLeadingUnquotedString t with
  | some s => s.startsWith "-"
  | none => false

-- Theorems (stubs)

theorem isLoop_while (id : Id) (cond body : List Token) :
    isLoop ⟨id, .T_WhileExpression cond body⟩ = true := rfl

theorem isLoop_for (id : Id) (v : String) (ws body : List Token) :
    isLoop ⟨id, .T_ForIn v ws body⟩ = true := rfl

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
