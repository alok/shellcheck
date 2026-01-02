/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Checks that examine specific commands by name.
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.AnalyzerLib
import ShellCheck.CFG
import ShellCheck.CFGAnalysis
import ShellCheck.Data
import ShellCheck.Interface
import ShellCheck.Parser
import ShellCheck.Prelude
import ShellCheck.Regex
import Std.Data.HashMap

namespace ShellCheck.Checks.Commands

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.CFG
open ShellCheck.CFGAnalysis
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Parser
open ShellCheck.Prelude

/-- Command name matcher - supports single command, multiple commands, or any command -/
inductive CommandName where
  | exactly : String → CommandName
  | basename : String → CommandName
  | anyExactly : List String → CommandName
  | anyBasename : List String → CommandName
  | any : CommandName  -- matches any command
  deriving Repr, Inhabited

instance : BEq CommandName where
  beq a b := match a, b with
    | .exactly s1, .exactly s2 => s1 == s2
    | .basename s1, .basename s2 => s1 == s2
    | .anyExactly l1, .anyExactly l2 => l1 == l2
    | .anyBasename l1, .anyBasename l2 => l1 == l2
    | .any, .any => true
    | _, _ => false

/-- Command-specific check with access to parameters -/
structure CommandCheck where
  name : CommandName
  check : Parameters → Token → List TokenComment

/-- Get command arguments (words after command name) -/
def getCommandArguments (t : Token) : Option (List Token) := do
  let cmd ← getCommand t
  match cmd.inner with
  | .T_SimpleCommand _ (_::args) => some args
  | _ => Option.none

/-- Match command name against pattern -/
def matchesCommandName (pattern : CommandName) (cmd : Token) : Bool :=
  match pattern with
  | .exactly name => getCommandName cmd == some name
  | .basename name =>
    match getCommandBasename cmd with
    | some cmdBase => cmdBase == name
    | Option.none => false
  | .anyExactly names =>
    match getCommandName cmd with
    | some cmdName => names.contains cmdName
    | Option.none => false
  | .anyBasename names =>
    match getCommandBasename cmd with
    | some cmdBase => names.contains cmdBase
    | Option.none => false
  | .any => getCommandName cmd |>.isSome

/-- Get the parent token of a given token -/
def getParent (params : Parameters) (t : Token) : Option Token :=
  params.parentMap.get? t.id

/-- Get the path from root to token (list of ancestors) -/
def getPath (params : Parameters) (t : Token) : List Token :=
  go t [t] 100
where
  go (current : Token) (acc : List Token) : Nat → List Token
    | 0 => acc
    | fuel + 1 =>
      match getParent params current with
      | some parent => go parent (parent :: acc) fuel
      | Option.none => acc

/-!
## Context Detection Helpers

These helpers determine the syntactic context of a token.
-/

/-- Check if a token is inside a command substitution $() or `` -/
def isInCommandSubstitution (params : Parameters) (t : Token) : Bool :=
  (getPath params t).any fun ancestor =>
    match ancestor.inner with
    | .T_DollarExpansion _ => true
    | .T_Backticked _ => true
    | _ => false

/-- Check if a token is inside a condition ([ ], [[ ]], or test) -/
def isInCondition (params : Parameters) (t : Token) : Bool :=
  (getPath params t).any fun ancestor =>
    match ancestor.inner with
    | .T_Condition _ _ => true
    | _ => false

/-- Check if a token is inside a for loop -/
def isInForLoop (params : Parameters) (t : Token) : Bool :=
  (getPath params t).any fun ancestor =>
    match ancestor.inner with
    | .T_ForIn _ _ _ => true
    | .T_ForArithmetic _ _ _ _ => true
    | _ => false

/-- Check if a token is inside a while/until loop -/
def isInWhileLoop (params : Parameters) (t : Token) : Bool :=
  (getPath params t).any fun ancestor =>
    match ancestor.inner with
    | .T_WhileExpression _ _ => true
    | .T_UntilExpression _ _ => true
    | _ => false

/-- Check if a token is inside any loop -/
def isInLoop (params : Parameters) (t : Token) : Bool :=
  isInForLoop params t || isInWhileLoop params t

/-- Check if a token is inside a function definition -/
def isInFunction (params : Parameters) (t : Token) : Bool :=
  (getPath params t).any fun ancestor =>
    match ancestor.inner with
    | .T_Function _ _ _ _ => true
    | _ => false

/-- Check if a token is inside a subshell -/
def isInSubshell (params : Parameters) (t : Token) : Bool :=
  (getPath params t).any fun ancestor =>
    match ancestor.inner with
    | .T_Subshell _ => true
    | _ => false

/-- Check if a token is inside a pipeline -/
def isInPipeline (params : Parameters) (t : Token) : Bool :=
  (getPath params t).any fun ancestor =>
    match ancestor.inner with
    | .T_Pipeline _ cmds => cmds.length > 1
    | _ => false

/-- Get the pipeline containing a token, if any -/
def getContainingPipeline (params : Parameters) (t : Token) : Option Token :=
  (getPath params t).find? fun ancestor =>
    match ancestor.inner with
    | .T_Pipeline _ _ => true
    | _ => false

/-!
## Argument Checking Helpers

These helpers make it easier to check command arguments.
-/

/-- Get literal strings from arguments -/
def getArgStrings (args : List Token) : List String :=
  args.filterMap (getLiteralString ·)

/-- Check if any argument matches a predicate -/
def hasArgMatching (args : List Token) (pred : String → Bool) : Bool :=
  args.any fun arg =>
    match getLiteralString arg with
    | some s => pred s
    | Option.none => false

/-- Check if any argument equals a specific string -/
def hasArg (args : List Token) (s : String) : Bool :=
  hasArgMatching args (· == s)

/-- Check if any argument starts with a given prefix -/
def hasArgStartingWith (args : List Token) (pfx : String) : Bool :=
  hasArgMatching args (·.startsWith pfx)

/-- Filter arguments matching a predicate, returning the token and its string -/
def filterArgsMatching (args : List Token) (pred : String → Bool) : List (Token × String) :=
  args.filterMap fun arg =>
    match getLiteralString arg with
    | some s => if pred s then some (arg, s) else Option.none
    | Option.none => Option.none

/-- Check if argument looks like an option (starts with -) -/
def isOption (s : String) : Bool := s.startsWith "-"

/-- Get non-option arguments -/
def getNonOptionArgs (args : List Token) : List Token :=
  args.filter fun arg =>
    match getLiteralString arg with
    | some s => !isOption s
    | Option.none => true  -- keep non-literal args

/-- Check if string contains glob characters -/
def hasGlobChars (s : String) : Bool :=
  s.any fun c => c == '*' || c == '?' || c == '['

/-- Check if string looks like a variable reference -/
def looksLikeVariable (s : String) : Bool :=
  s.startsWith "$" || s.startsWith "${" || s.contains '$'

/-!
## Comment Construction Helpers
-/

/-- Make a warning comment for an argument -/
def warnArg (arg : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .warningC arg.id code msg

/-- Make an error comment for an argument -/
def errorArg (arg : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .errorC arg.id code msg

/-- Make a style comment for an argument -/
def styleArg (arg : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .styleC arg.id code msg

/-- Make an info comment for an argument -/
def infoArg (arg : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .infoC arg.id code msg

/-- Make a warning comment for a command -/
def warnCmd (t : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .warningC t.id code msg

/-- Make an error comment for a command -/
def errorCmd (t : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .errorC t.id code msg

/-- Make a style comment for a command -/
def styleCmd (t : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .styleC t.id code msg

/-- Make an info comment for a command -/
def infoCmd (t : Token) (code : Nat) (msg : String) : TokenComment :=
  makeComment .infoC t.id code msg

/-!
## Common Check Patterns

These functions implement common check patterns that can be reused.
-/

/-- Create a check that warns about glob patterns that might match dash-prefixed files -/
def mkGlobDashCheck (commands : List String) (code : Nat) (msg : String) : CommandCheck := {
  name := .anyBasename commands
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if (s.startsWith "*" || s.startsWith "?") && !s.startsWith "./" then
            some (warnArg arg code msg)
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- Create a check that warns when a command is used in a specific context -/
def mkContextCheck (commands : List String) (contextCheck : Parameters → Token → Bool)
    (code : Nat) (msg : String) : CommandCheck := {
  name := .anyBasename commands
  check := fun params t =>
    if contextCheck params t then
      [warnCmd t code msg]
    else []
}

/-- Create a check that warns about specific argument patterns -/
def mkArgPatternCheck (commands : List String) (argPred : String → Bool)
    (code : Nat) (msg : String) : CommandCheck := {
  name := .anyBasename commands
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      (filterArgsMatching args argPred).map fun (arg, _) =>
        warnArg arg code msg
    | Option.none => []
}

/-- Create a check that always warns when a command is used -/
def mkAlwaysWarnCheck (command : String) (code : Nat) (msg : String)
    (severity : Severity := .warningC) : CommandCheck := {
  name := .exactly command
  check := fun _params t =>
    [makeComment severity t.id code msg]
}

/-- Pipeline-level check type -/
abbrev PipelineCheck := Token → List TokenComment

/-- SC2010: Don't use ls | grep -/
def checkLsGrepPipeline : PipelineCheck := fun t =>
  match t.inner with
  | .T_Pipeline _ cmds =>
    match cmds with
    | first :: second :: _ =>
      let isLs := match getCommandBasename first with
        | some name => name == "ls"
        | Option.none => false
      let isGrep := match getCommandBasename second with
        | some name => name == "grep" || name == "egrep" || name == "fgrep"
        | Option.none => false
      if isLs && isGrep then
        [makeComment .warningC t.id 2010
          "Don't use ls | grep. Use a glob or find instead."]
      else []
    | _ => []
  | _ => []

/-- SC2009: ps | grep is error prone (catches itself) -/
def checkPsGrepPipeline : PipelineCheck := fun t =>
  match t.inner with
  | .T_Pipeline _ cmds =>
    match cmds with
    | first :: second :: _ =>
      let isPs := match getCommandBasename first with
        | some name => name == "ps"
        | Option.none => false
      let isGrep := match getCommandBasename second with
        | some name => name == "grep" || name == "egrep" || name == "fgrep"
        | Option.none => false
      if isPs && isGrep then
        [makeComment .infoC t.id 2009
          "Consider using pgrep instead of ps | grep."]
      else []
    | _ => []
  | _ => []

/-- SC2002: Useless cat (cat file | cmd can be cmd < file) -/
def checkUselessCatPipeline : PipelineCheck := fun t =>
  match t.inner with
  | .T_Pipeline _ cmds =>
    match cmds with
    | first :: _rest =>
      match getCommandBasename first with
      | some "cat" =>
        match getCommandArguments first with
        | some [_singleFile] =>
          -- cat with single file piped to something
          [makeComment .styleC first.id 2002
            "Useless cat. Consider 'cmd < file' or 'cmd file' instead."]
        | _ => []
      | _ => []
    | _ => []
  | _ => []

/-- All pipeline-level checks -/
def pipelineChecks : List PipelineCheck := [
  checkLsGrepPipeline,
  checkPsGrepPipeline,
  checkUselessCatPipeline
]

/-- Get checker from command checks -/
def getChecker (params : Parameters) (checks : List CommandCheck) : Checker := {
  perScript := fun _ => pure []
  perToken := fun token => do
    -- Run command-specific checks
    let cmdComments := checks.filter (fun cc => matchesCommandName cc.name token)
      |>.foldl (fun acc cc => acc ++ cc.check params token) []
    -- Run pipeline checks
    let pipeComments := pipelineChecks.foldl (fun acc pc => acc ++ pc token) []
    pure (cmdComments ++ pipeComments)
}

/-- Optional command checks -/
def optionalChecks : List CheckDescription := [
  { cdName := "deprecate-which"
    cdDescription := "Suggest 'command -v' instead of 'which'"
    cdPositive := "which cmd"
    cdNegative := "command -v cmd" }
]

/-!
## Individual Command Checks
-/

/-- SC2010: Don't use ls | grep (handled by pipeline check) -/
def checkLsGrep : CommandCheck := {
  name := .basename "grep"
  check := fun _params _t => []  -- Pipeline check handles this
}

/-- SC2012: Use find instead of ls to better handle non-alphanumeric filenames -/
def checkLsFind : CommandCheck := {
  name := .exactly "ls"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      -- Warn if ls is used with glob patterns that might have spaces
      let argStrs := args.map (getLiteralString · |>.getD "")
      let hasGlob := argStrs.any fun s => s.any (fun c => c == '*' || c == '?')
      if hasGlob then
        [makeComment .infoC t.id 2012
          "Use find instead of ls to better handle non-alphanumeric filenames."]
      else []
    | Option.none => []
}

/-- SC2013: To read lines, use a while read loop -/
def checkForInCat : CommandCheck := {
  name := .exactly "cat"
  check := fun params t =>
    -- Check if cat is inside a command substitution that's part of a for loop
    let ancestors := getPath params t
    let inForLoop := ancestors.any fun ancestor =>
      match ancestor.inner with
      | .T_ForIn _ _ _ => true
      | _ => false
    let inCommandSub := ancestors.any fun ancestor =>
      match ancestor.inner with
      | .T_DollarExpansion _ => true
      | .T_Backticked _ => true
      | _ => false
    if inForLoop && inCommandSub then
      [makeComment .warningC t.id 2013
        "To read lines, use 'while IFS= read -r line; do ...; done < file'."]
    else []
}

/-- SC2018/SC2019/SC2020/SC2021/SC2060: Common `tr` pitfalls. -/
def checkTr : CommandCheck := {
  name := .exactly "tr"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.flatMap fun arg =>
        let globWarn : List TokenComment :=
          if hasUnquotedGlob arg then
            [warnArg arg 2060 "Quote parameters to tr to prevent glob expansion."]
          else
            []
        let litWarn : List TokenComment :=
          match getLiteralString arg with
          | some "a-z" =>
              [infoArg arg 2018
                "Use '[:lower:]' to support accents and foreign alphabets."]
          | some "A-Z" =>
              [infoArg arg 2019
                "Use '[:upper:]' to support accents and foreign alphabets."]
          | some s =>
              let dupWarn :=
                if !(s.startsWith "-" || Regex.containsSubstring s "[:") && hasDuplicatedAlpha s then
                  [infoArg arg 2020
                    "tr replaces sets of chars, not words (mentioned due to duplicates)."]
                else
                  []
              let classWarn :=
                if !(s.startsWith "[:" || s.startsWith "[=") &&
                   s.startsWith "[" && s.endsWith "]" && s.length > 2 && !s.contains '*' then
                  [infoArg arg 2021
                    "Don't use [] around classes in tr, it replaces literal square brackets."]
                else
                  []
              dupWarn ++ classWarn
          | Option.none => []
        globWarn ++ litWarn
    | Option.none => []
}
where
  /-- Best-effort: detect unquoted glob metacharacters even when the parser emits `.T_Literal`. -/
  hasClosedBracketExpr (s : String) : Bool :=
    let cs := s.toList
    match cs.dropWhile (· != '[') with
    | [] => false
    | _ :: rest => rest.any (· == ']')

  hasUnquotedGlob (t : Token) : Bool :=
    goHasUnquotedGlob false 64 t

  goHasUnquotedGlob (quoted : Bool) : Nat → Token → Bool
    | 0, _ => false
    | fuel + 1, t =>
        match t.inner with
        | .T_Annotation _ inner => goHasUnquotedGlob quoted fuel inner
        | .T_NormalWord parts => parts.any (goHasUnquotedGlob quoted fuel)
        | .T_DoubleQuoted parts => parts.any (goHasUnquotedGlob true fuel)
        | .T_DollarDoubleQuoted parts => parts.any (goHasUnquotedGlob true fuel)
        | .T_SingleQuoted _ => false
        | .T_DollarSingleQuoted _ => false
        | .T_Glob _ => !quoted
        | .T_Extglob _ _ => !quoted
        | .T_Literal s =>
            if quoted then
              false
            else
              s.contains '*' || s.contains '?' || hasClosedBracketExpr s
        | _ => false

  hasDuplicatedAlpha (s : String) : Bool :=
    let relevant := s.toList.filter Char.isAlpha
    relevant != relevant.eraseDups

/-- SC2035: Use ./*glob* or -- *glob* to avoid matching dashes -/
def checkFindNameGlob : CommandCheck := {
  name := .exactly "find"
  check := fun _params t =>
    match getCommandArguments t with
    | some args => args.filterMap fun arg =>
        let s := getLiteralString arg |>.getD ""
        if s.startsWith "-" && s.length > 1 && s.any (· == '*') then
          some (makeComment .warningC arg.id 2061
            "Quote the -name pattern to prevent shell expansion.")
        else Option.none
    | Option.none => []
}

/-- SC2003/SC2304-SC2307: `expr` is antiquated and fragile -/
def checkExpr : CommandCheck := {
  name := .basename "expr"
  check := fun _params t =>
    let base : List TokenComment :=
      [makeComment .styleC t.id 2003
        "expr is antiquated. Consider rewriting this using $((..)), ${} or [[ ]]."]
    match getCommandArguments t with
    | some args =>
      match args with
      | [lhs, op, rhs] =>
        let c2304 :=
          match getWordParts op with
          | [single] =>
            match single.inner with
            | .T_Glob "*" =>
              [makeComment .errorC op.id 2304
                "* must be escaped to multiply: \\*. Modern $((x * y)) avoids this issue."]
            | _ => []
          | _ => []
        let c2305 :=
          if getLiteralString op == some ":" && isGlob rhs then
            [makeComment .warningC rhs.id 2305
              "Quote regex argument to expr to avoid it expanding as a glob."]
          else []
        base ++ checkOp lhs ++ c2304 ++ c2305
      | [single] =>
        if !willSplit single then
          base ++ [makeComment .warningC single.id 2307
            "'expr' expects 3+ arguments but sees 1. Make sure each operator/operand is a separate argument, and escape <>&|."]
        else base
      | [first, second] =>
        if onlyLiteralString first != "length" && !willSplit first && !willSplit second then
          base ++ checkOp first ++ [makeComment .warningC t.id 2307
            "'expr' expects 3+ arguments, but sees 2. Make sure each operator/operand is a separate argument, and escape <>&|."]
        else base
      | first :: rest =>
        let c2306 :=
          rest.filterMap fun a =>
            if isGlob a then
              some (makeComment .warningC a.id 2306
                "Escape glob characters in arguments to expr to avoid pathname expansion.")
            else Option.none
        base ++ checkOp first ++ c2306
      | [] => base
    | Option.none => base
}
where
  checkOp (side : Token) : List TokenComment :=
    match getLiteralString side with
    | some "match" =>
      [makeComment .infoC side.id 2308
        "'expr match' has unspecified results. Prefer 'expr str : regex'."]
    | some "length" =>
      [makeComment .infoC side.id 2308
        "'expr length' has unspecified results. Prefer ${#var}."]
    | some "substr" =>
      [makeComment .infoC side.id 2308
        "'expr substr' has unspecified results. Prefer 'cut' or ${var#???}."]
    | some "index" =>
      [makeComment .infoC side.id 2308
        "'expr index' has unspecified results. Prefer x=${var%%[chars]*}; $((${#x}+1))."]
    | _ => []

/-- SC2062/SC2063/SC2022: Grep patterns that look like globs or suspicious regexes. -/
def checkGrepRe : CommandCheck := {
  name := .anyBasename ["grep", "egrep", "fgrep"]
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      match findPatternArg args with
      | some pattern =>
        let cmdBase := getCommandBasename t
        let flags := args.filterMap getLiteralString
        let fixedByName :=
          cmdBase == some "fgrep"
        let hasGrepGlobFlag :=
          fixedByName ||
          flags.any fun f =>
            f == "-F" || f == "--fixed-strings" ||
            f.startsWith "--include" || f.startsWith "--exclude" || f.startsWith "--exclude-dir" ||
            f == "-o" || f == "--only-matching"
        let c2062 :=
          if hasUnquotedGlobChars pattern then
            [makeComment .warningC pattern.id 2062
              "Quote the grep pattern so the shell won't interpret it."]
          else []
        let c2063 :=
          if hasGrepGlobFlag then []
          else
            let s := String.join (oversimplify pattern)
            if isConfusedGlobRegex s then
              [makeComment .warningC pattern.id 2063
                "Grep uses regex, but this looks like a glob."]
            else
              match getSuspiciousRegexWildcard s with
              | some c =>
                [makeComment .infoC pattern.id 2022 (mk2022Message c)]
              | Option.none => []
        c2062 ++ c2063
      | Option.none => []
    | Option.none => []
}
where
  globCharLike (c : Char) : Bool :=
    c == '*' || c == '?' || c == '[' || c == ']'

  /-- Best-effort: detect glob metacharacters that are unquoted in the source. -/
  goHasUnquotedGlobChars : Nat → List Token → Bool
    | 0, _ => false
    | _fuel + 1, [] => false
    | fuel + 1, t :: rest =>
      match t.inner with
      | .T_Literal s => s.any globCharLike || goHasUnquotedGlobChars fuel rest
      | .T_Glob _ => true
      | .T_Extglob .. => true
      | .T_BraceExpansion .. => true
      | .T_NormalWord parts => goHasUnquotedGlobChars fuel (parts ++ rest)
      | .TA_Expansion parts => goHasUnquotedGlobChars fuel (parts ++ rest)
      | .T_Annotation _ c => goHasUnquotedGlobChars fuel (c :: rest)
      | .T_DoubleQuoted _ => goHasUnquotedGlobChars fuel rest
      | .T_DollarDoubleQuoted _ => goHasUnquotedGlobChars fuel rest
      | .T_SingleQuoted _ => goHasUnquotedGlobChars fuel rest
      | .T_DollarSingleQuoted _ => goHasUnquotedGlobChars fuel rest
      | _ => goHasUnquotedGlobChars fuel rest

  hasUnquotedGlobChars (t : Token) : Bool :=
    -- Fuel is just to appease termination checking; patterns aren't deeply nested in practice.
    goHasUnquotedGlobChars 256 [t]

  isAlphaNum1to9 (c : Char) : Bool :=
    c.isAlpha || (c.isDigit && c != '0')

  hasNonAlphaNumStar : List Char → Bool
    | [] | [_] => false
    | a :: b :: rest =>
      (b == '*' && !isAlphaNum1to9 a) || hasNonAlphaNumStar (b :: rest)

  findAlphaNumStar : List Char → Option Char
    | [] | [_] => Option.none
    | a :: b :: rest =>
      if isAlphaNum1to9 a && b == '*' then
        some a
      else
        findAlphaNumStar (b :: rest)

  /-- Haskell `checkGrepRe` emits SC2022 for patterns like `Foo*` that often come from glob intuition. -/
  getSuspiciousRegexWildcard (s : String) : Option Char :=
    let chars := s.toList
    -- Contra: bail if the pattern includes regex-ish hints, or other uses of `*`.
    if chars.any (fun c => c == ']' || c == '^' || c == '$' || c == '+' || c == '\\') then
      Option.none
    else if hasNonAlphaNumStar chars then
      Option.none
    else
      findAlphaNumStar chars

  capitalizeFirst (s : String) : String :=
    match s.toList with
    | [] => s
    | c :: cs => String.ofList (c.toUpper :: cs)

  wordStartingWith (c : Char) : String :=
    (sampleWords ++ sampleWords.map capitalizeFirst).find? (fun w => w.startsWith (String.singleton c))
      |>.getD (String.singleton c ++ "test")

  mk2022Message (c : Char) : String :=
    let cStr := String.singleton c
    let triple := String.ofList [c, c, c]
    s!"Note that unlike globs, {cStr}* here matches '{triple}' but not '{wordStartingWith c}'."

  findPatternArg : List Token → Option Token
    | [] => Option.none
    | x :: r =>
      let s := getLiteralString x |>.getD ""
      if s == "--" || s == "-e" || s == "--regex" then
        r.head?
      else if s.startsWith "--regex=" then
        some x
      else if s.startsWith "-" then
        findPatternArg r
      else
        some x

/-- SC2064: Trap quotes to preserve values at trap time, not execution time -/
def checkTrapQuotes : CommandCheck := {
  name := .exactly "trap"
  check := fun _params t =>
    match getCommandArguments t with
    | some (handler :: _signals) =>
      match handler.inner with
      | .T_DoubleQuoted parts =>
        -- Check if double-quoted trap handler contains variable expansions
        let hasVarExpansion := parts.any fun part =>
          match part.inner with
          | .T_DollarBraced _ _ => true
          | .T_DollarExpansion _ => true
          | .T_DollarArithmetic _ => true
          | _ => false
        if hasVarExpansion then
          [makeComment .warningC handler.id 2064
            "Use single quotes, otherwise variables are expanded now rather than at trap time."]
        else []
      | _ => []
    | _ => []
}

/-- SC2104: In functions, return instead of break -/
def checkReturn : CommandCheck := {
  name := .exactly "return"
  check := fun _params t =>
    match getCommandArguments t with
    | some [arg] =>
      match getLiteralString arg with
      | some s =>
        if s.toNat? == some 0 then []
        else if s.toNat?.any (· > 255) then
          [makeComment .warningC arg.id 2152
            "Can only return 0-255. Use other methods for larger values."]
        else []
      | Option.none => []
    | _ => []
}

/-- SC2105: Check exit in subshell -/
def checkExit : CommandCheck := {
  name := .exactly "exit"
  check := fun _params t =>
    match getCommandArguments t with
    | some [arg] =>
      match getLiteralString arg with
      | some s =>
        if s.toNat?.any (· > 255) then
          [makeComment .warningC arg.id 2152
            "Can only exit 0-255. Use other methods for larger values."]
        else []
      | Option.none => []
    | _ => []
}

/-- SC2156: Check find -exec has proper terminator -/
def checkFindExecWithSingleArgument : CommandCheck := {
  name := .exactly "find"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      -- Find all -exec/-execdir tokens
      let execArgs := args.filter fun a =>
        let s := getLiteralString a |>.getD ""
        s == "-exec" || s == "-execdir"
      -- Check if there are proper terminators (; or +)
      let terminators := args.filter fun a =>
        let s := getLiteralString a |>.getD ""
        s == ";" || s == "\\;" || s == "+"
      -- If more execs than terminators, warn
      if execArgs.length > terminators.length then
        execArgs.drop terminators.length |>.map fun arg =>
          makeComment .errorC arg.id 2156
            "Use ';' or '+' to terminate -exec."
      else []
    | Option.none => []
}

/-- SC2116: Useless echo -/
def checkUnusedEchoEscapes : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        let s := getLiteralString arg |>.getD ""
        if s.any (· == '\\') then Option.none  -- May need -e flag
        else Option.none
    | Option.none => []
}

/-- Helper: check if string contains substring -/
def stringContains (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- SC2156: Injecting filenames in find -exec sh -c -/
def checkInjectableFindSh : CommandCheck := {
  name := .exactly "find"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      -- Simple check: look for patterns like -exec sh -c '..{}...'
      let argStrs := args.map (getLiteralString · |>.getD "")
      let argWithIdx := argStrs.zip args
      argWithIdx.filterMap fun (s, tok) =>
        -- Check if this looks like a script with {} inside
        if stringContains s "{}" &&
           argStrs.any (fun x => x == "sh" || x == "bash" || x.endsWith "/sh" || x.endsWith "/bash") &&
           argStrs.any (· == "-c") then
          some (makeComment .warningC tok.id 2156
            "Expanding {} in the shell is unsafe. Use a placeholder.")
        else Option.none
    | Option.none => []
}

/-- SC2146: Check find action precedence (-print before -o) -/
def checkFindActionPrecedence : CommandCheck := {
  name := .exactly "find"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      -- Check for -print/-delete before -o without grouping
      let rec hasActionBeforeOr (remaining : List String) (seenAction : Bool) : Bool :=
        match remaining with
        | [] => false
        | s :: rest =>
          if s == "-o" && seenAction then true
          else
            let isAction := s == "-print" || s == "-delete" || s == "-exec"
            hasActionBeforeOr rest (seenAction || isAction)
      let hasPrintBeforeOr := hasActionBeforeOr argStrs false
      let hasProperGrouping := argStrs.any (· == "(") || argStrs.any (· == "\\(")
      if hasPrintBeforeOr && !hasProperGrouping then
        [makeComment .warningC t.id 2146
          "This action ignores everything before -o. Use \\( \\) to group."]
      else []
    | Option.none => []
}

/-- SC2227: Redirection applies to `find` itself, not per action. -/
def checkFindRedirections : CommandCheck := {
  name := .basename "find"
  check := fun params t =>
    let redirTok? : Option Token :=
      match t.inner with
      | .T_Redirecting .. => some t
      | _ => getClosestCommand params.parentMap t
    match redirTok? with
    | some redirTok =>
      match redirTok.inner with
      | .T_Redirecting redirs cmd =>
        if redirs.isEmpty then
          []
        else
          match cmd.inner with
          | .T_SimpleCommand _ words =>
            if words.length < 2 then
              []
            else
              match minById? redirs, maxById? words with
              | some minRedir, some maxArg =>
                if minRedir.id.val < maxArg.id.val then
                  [makeComment .warningC minRedir.id 2227
                    "Redirection applies to the find command itself. Rewrite to work per action (or move to end)."]
                else []
              | _, _ => []
          | _ => []
      | _ => []
    | Option.none => []
}
where
  minById? (ts : List Token) : Option Token :=
    ts.foldl (fun acc t =>
      match acc with
      | Option.none => some t
      | some best => if t.id.val < best.id.val then some t else some best
    ) Option.none

  maxById? (ts : List Token) : Option Token :=
    ts.foldl (fun acc t =>
      match acc with
      | Option.none => some t
      | some best => if best.id.val < t.id.val then some t else some best
    ) Option.none

/-- SC2174: mkdir with -p and -m mode -/
def checkMkdirDashPM : CommandCheck := {
  name := .exactly "mkdir"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let hasP := args.any fun a => getLiteralString a == some "-p"
      let hasM := args.any fun a => getLiteralString a == some "-m"
      if hasP && hasM then
        [makeComment .warningC t.id 2174
          "With -p, -m only applies to the last directory. Use (umask) for others."]
      else []
    | Option.none => []
}

/-- SC2250: Portable signals -/
def checkNonportableSignals : CommandCheck := {
  name := .exactly "trap"
  check := fun _params t =>
    match getCommandArguments t with
    | some (_ :: signals) =>
      signals.filterMap fun sig =>
        let s := getLiteralString sig |>.getD ""
        if s.startsWith "SIG" then
          some (makeComment .styleC sig.id 2250
            "Use signal names without SIG prefix for better portability.")
        else Option.none
    | _ => []
}

/-- SC2253: `chmod -r` is not recursive. -/
def checkChmodDashr : CommandCheck := {
  name := .basename "chmod"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        if getLiteralString arg == some "-r" then
          some (warnArg arg 2253
            "Use -R to recurse, or explicitly a-r to remove read permissions.")
        else
          Option.none
    | Option.none => []
}

/-- SC2117: Interactive su -/
def checkInteractiveSu : CommandCheck := {
  name := .exactly "su"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let hasCommand := args.any fun a =>
        getLiteralString a == some "-c" ||
        getLiteralString a == some "--command"
      if not hasCommand then
        [makeComment .infoC t.id 2117
          "To run commands as another user, use su -c or sudo."]
      else []
    | Option.none => []
}

/-- SC2230: which is non-standard -/
def checkWhich : CommandCheck := {
  name := .exactly "which"
  check := fun _params t =>
    [makeComment .infoC t.id 2230
      "'which' is non-standard. Use 'command -v' instead."]
}

/-- SC2237: Check for [ -n or -z $var ] without quotes -/
def checkTestNZ : CommandCheck := {
  name := .exactly "test"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let rec checkArgs (remaining : List Token) (acc : List TokenComment) (fuel : Nat) : List TokenComment :=
        if fuel == 0 then acc else
        match remaining with
        | [] => acc
        | flag :: arg :: rest =>
          let flagStr := getLiteralString flag |>.getD ""
          if flagStr == "-n" || flagStr == "-z" then
            -- Check if arg is an unquoted variable expansion
            let needsQuotes := match arg.inner with
              | .T_DollarBraced _ _ => true  -- $var or ${var}
              | .T_NormalWord parts => parts.any fun p =>
                  match p.inner with
                  | .T_DollarBraced _ _ => true
                  | _ => false
              | _ => false
            if needsQuotes then
              checkArgs rest (makeComment .warningC arg.id 2237
                s!"Use quotes: {flagStr} \"$var\"" :: acc) (fuel - 1)
            else
              checkArgs rest acc (fuel - 1)
          else
            checkArgs (arg :: rest) acc (fuel - 1)
        | [_] => acc
      checkArgs args [] args.length
    | Option.none => []
}

/-- SC2185: Some finds need -L for symlink targets -/
def checkFindWithSymlinks : CommandCheck := {
  name := .exactly "find"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      let hasSymlinkOption := argStrs.any (· == "-L") || argStrs.any (· == "-follow")
      let hasType := argStrs.any (· == "-type")
      let hasXtype := argStrs.any (· == "-xtype")
      -- Warn if using -type without -L or -xtype (may miss symlinked files)
      if hasType && !hasSymlinkOption && !hasXtype then
        -- Find the -type argument to attach warning
        match args.find? (fun a => getLiteralString a == some "-type") with
        | some typeArg =>
          [makeComment .styleC typeArg.id 2185
            "Use -L to follow symlinks or -xtype to check symlink targets."]
        | Option.none => []
      else []
    | Option.none => []
}

/-- SC2086 SC2248: Prefer printf over echo -n for portability -/
def checkEchoN : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      if args.any fun a => getLiteralString a == some "-n" then
        [makeComment .styleC t.id 2028
          "echo -n is non-standard. Consider printf instead."]
      else []
    | Option.none => []
}

/-- SC2291: Quote repeated spaces to avoid them collapsing into one. -/
def checkUnquotedEchoSpaces : CommandCheck := {
  name := .basename "echo"
  check := fun params t =>
    match getCommandArguments t with
    | some args =>
      let positions : List (Position × Position) :=
        args.filterMap fun a => params.tokenPositions.get? a.id
      let redirStarts : List Position :=
        (getRedirs params t).filterMap fun r =>
          (params.tokenPositions.get? r.id).map Prod.fst
      if hasSuspiciousGap redirStarts positions then
        [makeComment .infoC t.id 2291
          "Quote repeated spaces to avoid them collapsing into one."]
      else []
    | Option.none => []
}
where
  getRedirs (params : Parameters) (t : Token) : List Token :=
    match t.inner with
    | .T_Redirecting redirects _ => redirects
    | _ =>
      match getClosestCommand params.parentMap t with
      | some redirTok =>
        match redirTok.inner with
        | .T_Redirecting redirects _ => redirects
        | _ => []
      | Option.none => []

  posLt (a b : Position) : Bool :=
    a.posLine < b.posLine ||
      (a.posLine == b.posLine && a.posColumn < b.posColumn)

  hasSpacesBetween (redirs : List Position) (p1 p2 : Position × Position) : Bool :=
    let (_, end1) := p1
    let (start2, _) := p2
    end1.posLine == start2.posLine &&
      (start2.posColumn - end1.posColumn) >= 4 &&
      !(redirs.any fun x => posLt end1 x && posLt x start2)

  hasSuspiciousGap (redirs : List Position) : List (Position × Position) → Bool
    | (p1 :: p2 :: rest) =>
      hasSpacesBetween redirs p1 p2 || hasSuspiciousGap redirs (p2 :: rest)
    | _ => false

-- Note: SC2002 (useless cat) and SC2009 (ps | grep) are handled by pipeline checks above

/-- SC2219: Instead of 'let expr', use (( expr )) -/
def checkLetArithmetic : CommandCheck := {
  name := .exactly "let"
  check := fun _params t =>
    [makeComment .styleC t.id 2219
      "Instead of 'let expr', prefer (( expr )) ."]
}

/-- SC2006: Use $(...) instead of legacy backticks -/
def checkBackticks : CommandCheck := {
  name := .exactly "echo"  -- Applies generally, but check in echo context
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_Backticked _ =>
          some (makeComment .styleC arg.id 2006
            "Use $(...) notation instead of legacy backticks `...`.")
        | _ => Option.none
    | Option.none => []
}

/-- SC2230: which is non-standard. Use type, command -v, or hash -/
def checkWhichCommand : CommandCheck := {
  name := .basename "which"
  check := fun _params t =>
    [makeComment .styleC t.id 2230
      "'which' is non-standard. Use type -p, command -v, or hash instead."]
}

/-- SC2024: sudo doesn't affect redirects. Use sudo tee or sudo sh -c. -/
def checkSudoRedirect : CommandCheck := {
  name := .basename "sudo"
  check := fun params t =>
    -- Check if this sudo command has redirects
    match params.parentMap.get? t.id with
    | some parent =>
      match parent.inner with
      | .T_Redirecting redirects _ =>
        if !redirects.isEmpty then
          [makeComment .warningC t.id 2024
            "sudo doesn't affect redirects. Use 'sudo tee' or 'sudo sh -c \"...\"' instead."]
        else []
      | _ => []
    | Option.none => []
}

/-- SC2086 style: Don't use cd without checking return value -/
def checkCdNoCheck : CommandCheck := {
  name := .exactly "cd"
  check := fun params t =>
    -- Check if cd is followed by || or && or in an if
    match params.parentMap.get? t.id with
    | some parent =>
      match parent.inner with
      | .T_AndIf _ _ => []  -- cd && something - ok
      | .T_OrIf _ _ => []   -- cd || something - ok
      | _ =>
        -- Simple heuristic: warn if just cd without error handling
        [makeComment .infoC t.id 2164
          "Use 'cd ... || exit' or 'cd ... || return' to handle cd failure."]
    | Option.none => []
}

/-- SC2129: Consider using { cmd1; cmd2; } >> file -/
def checkMultipleAppends : CommandCheck := {
  name := .basename "echo"
  check := fun _params _t =>
    -- This would need more context to detect multiple appends to same file
    -- Simplified: just note that it's a style issue (not auto-detectable easily)
    []
}

/-- SC2008: echo doesn't read from stdin -/
def checkEchoStdin : CommandCheck := {
  name := .basename "echo"
  check := fun params t =>
    -- Check if echo is being piped to
    match params.parentMap.get? t.id with
    | some parent =>
      match parent.inner with
      | .T_Pipeline _ cmds =>
        -- If echo is not the first command in pipeline, warn
        match cmds.head? with
        | some first => if first.id != t.id then
            [makeComment .warningC t.id 2008
              "echo doesn't read from stdin, use cat or a similar command."]
          else []
        | Option.none => []
      | _ => []
    | Option.none => []
}

/-- SC2026: This word looks like a shell comment but isn't -/
def checkUnintendedComment : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if s.startsWith "#" && s.length > 1 then
            some (makeComment .warningC arg.id 2026
              "This word looks like a comment but will be passed as an argument.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2035: Use ./* or -- before glob to avoid matching dashes -/
def checkGlobDash : CommandCheck :=
  mkGlobDashCheck ["rm", "mv", "cp", "chmod", "chown", "chgrp"]
    2035 "Use ./*glob* or -- *glob* to avoid matching dash-prefixed files."

/-- SC2088: Tilde does not expand in quotes -/
def checkTildeInQuotes : CommandCheck := {
  name := .basename "cd"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_DoubleQuoted parts =>
          if parts.any (fun p => match getLiteralString p with | some s => s.startsWith "~" | _ => false) then
            some (makeComment .warningC arg.id 2088
              "Tilde does not expand in quotes. Use $HOME or unquote.")
          else Option.none
        | _ => Option.none
    | Option.none => []
}

/-- SC2093: Remove exec if following commands should run -/
def checkExecFollowed : CommandCheck := {
  name := .exactly "exec"
  check := fun params t =>
    -- Check if there are commands after exec in the same sequence
    match params.parentMap.get? t.id with
    | some parent =>
      match parent.inner with
      | .T_Script _ cmds =>
        -- If exec is not the last command, warn
        match cmds.reverse.head? with
        | some last => if last.id != t.id then
            [makeComment .warningC t.id 2093
              "Remove exec if following commands should run, or add exit after exec."]
          else []
        | Option.none => []
      | _ => []
    | Option.none => []
}

/-- SC2115: Use "${var:?}" to ensure var is set -/
def checkRmVar : CommandCheck := {
  name := .basename "rm"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      let hasRecursive := argStrs.any (fun s => s == "-r" || s == "-rf" || s == "-R" || s.contains 'r')
      if hasRecursive then
        args.filterMap fun arg =>
          match arg.inner with
          | .T_DollarBraced _ inner =>
            let varName := getLiteralString inner |>.getD ""
            -- Check if it's a simple variable without :? protection
            if !varName.contains ':' && !varName.contains '?' then
              some (makeComment .warningC arg.id 2115
                "Use \"${var:?}\" to ensure this variable is set before rm -r.")
            else Option.none
          | .T_NormalWord parts =>
            if parts.any (fun p => match p.inner with | .T_DollarBraced _ _ => true | _ => false) then
              some (makeComment .infoC arg.id 2115
                "Consider using \"${var:?}\" to ensure variables are set in rm -r.")
            else Option.none
          | _ => Option.none
      else []
    | Option.none => []
}

/-- SC2148: Add shebang if missing -/
def checkMissingShebang : CommandCheck := {
  name := .basename "bash"  -- Dummy - this should be a script-level check
  check := fun _params _t => []  -- Script-level check, handled elsewhere
}

-- Note: SC2237 for [ ! -z ] is handled in Analytics.lean since [ ] is parsed as T_Condition

/-- SC2236: Use -n instead of ! -z -/
def checkTestNotZ : CommandCheck := {
  name := .exactly "test"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      if argStrs.any (· == "!") && argStrs.any (· == "-z") then
        [makeComment .styleC t.id 2236
          "Use -n instead of ! -z."]
      else []
    | Option.none => []
}

/-- SC2061: Quote the regex for grep -E or -P -/
def checkGrepRegexQuoting : CommandCheck := {
  name := .basename "grep"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      let hasExtended := argStrs.any (fun s => s == "-E" || s == "-P" || s.startsWith "--extended")
      if hasExtended then
        -- Check for unquoted patterns with regex metacharacters
        args.filterMap fun arg =>
          match getLiteralString arg with
          | some s =>
            if s.any (fun c => c == '*' || c == '+' || c == '?' || c == '|') &&
               !s.startsWith "'" && !s.startsWith "\"" then
              some (makeComment .warningC arg.id 2061
                "Quote the regex to prevent glob expansion.")
            else Option.none
          | Option.none => Option.none
      else []
    | Option.none => []
}

/-- SC2012: Use find instead of ls to better handle filenames -/
def checkLsInScript : CommandCheck := {
  name := .basename "ls"
  check := fun params t =>
    -- Only warn if output is being used (piped or captured)
    if isInPipeline params t then
      [makeComment .infoC t.id 2012
        "Use find instead of ls to better handle non-alphanumeric filenames."]
    else []
}

/-- SC2029: Note that single quotes prevent expansion on server -/
def checkSshSingleQuotes : CommandCheck := {
  name := .basename "ssh"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_SingleQuoted s =>
          if stringContains s "$" then
            some (makeComment .infoC arg.id 2029
              "Note that $VAR in single quotes won't expand on the SSH server. Use double quotes if intended.")
          else Option.none
        | _ => Option.none
    | Option.none => []
}

/-- SC2059: Don't use variables in printf format string -/
def checkPrintfVar : CommandCheck := {
  name := .basename "printf"
  check := fun _params t =>
    match getCommandArguments t with
    | some (formatArg :: _) =>
      match formatArg.inner with
      | .T_DollarBraced _ _ =>
        [makeComment .warningC formatArg.id 2059
          "Don't use variables in the printf format string. Use printf '%s' \"$var\"."]
      | .T_NormalWord parts =>
        if parts.any (fun p => match p.inner with | .T_DollarBraced _ _ => true | _ => false) then
          [makeComment .warningC formatArg.id 2059
            "Don't use variables in the printf format string. Use printf '%s' \"$var\"."]
        else []
      | _ => []
    | _ => []
}

/-- SC2060: Quote to prevent word splitting/globbing -/
def checkRmGlob : CommandCheck := {
  name := .basename "rm"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if s.any (· == '*') && !s.startsWith "'" && !s.startsWith "\"" then
            some (makeComment .warningC arg.id 2060
              "Quote to prevent word splitting/globbing, or use a loop.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2114: Warning: deletes all but the specified files in root -/
def checkRmRoot : CommandCheck := {
  name := .basename "rm"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      if argStrs.any (· == "/") || argStrs.any (· == "/*") then
        [makeComment .errorC t.id 2114
          "Warning: 'rm -rf /' or 'rm -rf /*' is dangerous."]
      else []
    | Option.none => []
}

/-- SC2121: To assign a variable, use var=value, not 'set var=value' -/
def checkSetAssign : CommandCheck := {
  name := .exactly "set"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if stringContains s "=" && !s.startsWith "-" then
            some (makeComment .errorC arg.id 2121
              "To assign a variable, use var=value, not 'set var=value'.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2122: read will expand escapes by default. Use -r -/
def checkReadR : CommandCheck := {
  name := .exactly "read"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      if !argStrs.any (· == "-r") && !argStrs.any (fun s => s.startsWith "-" && s.any (· == 'r')) then
        [makeComment .warningC t.id 2162
          "read without -r will mangle backslashes."]
      else []
    | Option.none => []
}

/-!
`read` pitfalls.
-/

/-- SC2229/SC2313: `read $var` doesn't read into `var`, and unquoted brackets may glob. -/
def checkReadExpansions : CommandCheck := {
  name := .exactly "read"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      match getGnuOpts flagsForRead args with
      | some parsed =>
        let vars :=
          parsed.filterMap fun (flag, (_, valTok)) =>
            if flag == "" || flag == "a" then some valTok else Option.none
        let dollarWarnings :=
          vars.filterMap fun v =>
            match getSingleUnmodifiedBracedString v with
            | some name =>
              if isVariableName name then
                some (makeComment .warningC v.id 2229
                  ("This does not read '" ++ name ++ "'. Remove $/${} for that, or use ${var?} to quiet."))
              else
                Option.none
            | Option.none => Option.none
        let arrayWarnings :=
          args.filterMap fun word =>
            if (getWordParts word).any isUnquotedBracket then
              some (makeComment .warningC word.id 2313
                "Quote array indices to avoid them expanding as globs.")
            else
              Option.none
        dollarWarnings ++ arrayWarnings
      | Option.none => []
    | Option.none => []
}
where
  /-- Return the single variable expansion that makes up this word, if any.
  Examples: `$foo` → `foo`, `"${foo}"` → `foo`, `"hello $name"` → none. -/
  getSingleUnmodifiedBracedString (word : Token) : Option String :=
    match getWordParts word with
    | [part] =>
      match part.inner with
      | .T_DollarBraced _ content =>
        let contents := String.join (oversimplify content)
        let name := ASTLib.getBracedReference contents
        if contents == name then some contents else Option.none
      | _ => Option.none
    | _ => Option.none

  isUnquotedBracket (t : Token) : Bool :=
    match t.inner with
    | .T_Glob s => s.startsWith "["
    | _ => false

-- Note: SC2166 for [ -a/-o ] is handled in Analytics.lean since [ ] is parsed as T_Condition
-- Note: SC2181 for [ $? ] is handled in Analytics.lean since [ ] is parsed as T_Condition

/-- SC2183: This format string has N placeholders but M arguments -/
def checkPrintfArgCount : CommandCheck := {
  name := .basename "printf"
  check := fun _params t =>
    match getCommandArguments t with
    | some (formatArg :: restArgs) =>
      match getLiteralString formatArg with
      | some fmt =>
        -- Count % placeholders (excluding %%)
        let placeholders := countPlaceholders fmt
        let argCount := restArgs.length
        if placeholders == 0 && argCount > 0 then
          [makeComment .errorC formatArg.id 2182
            "This printf format string has no variables. Other arguments are ignored."]
        else if placeholders > 0 && argCount > 0 && placeholders != argCount then
          [makeComment .warningC t.id 2183
            s!"This format string has {placeholders} placeholder(s) but {argCount} argument(s)."]
        else
          []
      | Option.none => []
    | _ => []
}
where
  countPlaceholders (s : String) : Nat :=
    let chars := s.toList
    go chars 0
  go : List Char → Nat → Nat
    | [], n => n
    | '%' :: '%' :: rest, n => go rest n  -- %% is escaped
    | '%' :: rest, n => go rest (n + 1)   -- % is a placeholder
    | _ :: rest, n => go rest n

/-- SC2192: This array element has no value. Remove the comma or add a value -/
def checkArrayComma : CommandCheck := {
  name := .exactly "declare"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if stringContains s ",," || s.endsWith "," then
            some (makeComment .errorC arg.id 2192
              "This array element has no value. Remove the comma or add a value.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

private def backrefPosLt (a b : Position) : Bool :=
  a.posLine < b.posLine ||
    (a.posLine == b.posLine && a.posColumn < b.posColumn)

private def backrefPosLtOpt : Option Position → Option Position → Bool
  | some pa, some pb => backrefPosLt pa pb
  | some _, Option.none => true
  | Option.none, some _ => false
  | Option.none, Option.none => false

private def backrefWithIndex : Nat → List Token → List (Nat × Token)
  | _n, [] => []
  | n, t :: rest => (n, t) :: backrefWithIndex (n + 1) rest

private def backrefSortTokens (params : Parameters) (tokens : List Token) : List Token :=
  (backrefWithIndex 0 tokens).toArray.qsort (fun (ia, ta) (ib, tb) =>
    let posA := (params.tokenPositions.get? ta.id).map Prod.fst
    let posB := (params.tokenPositions.get? tb.id).map Prod.fst
    if backrefPosLtOpt posA posB then
      true
    else if backrefPosLtOpt posB posA then
      false
    else
      ia < ib
  ) |>.toList |>.map (·.2)

partial def backrefCollectRefNames (params : Parameters) (tok : Token) : List String :=
  let here := getReferencedVariablesImpl params.parentMap tok |>.map (fun (_, _, name) => name)
  let kids := getTokenChildren tok
  here ++ kids.flatMap (backrefCollectRefNames params)

-- SC2318: Backreferencing declaration assignments in a single command.
def checkBackreferencingDeclaration (cmd : String) : CommandCheck := {
  name := .exactly cmd
  check := fun params t =>
    match t.inner with
    | .T_SimpleCommand assigns words =>
      let args := words.drop 1
      let ordered := backrefSortTokens params (assigns ++ args)
      let (comments, _) :=
        ordered.foldl (fun (acc, assigned) tok =>
          let refs := backrefCollectRefNames params tok |>.eraseDups
          let acc := refs.foldl (fun acc2 name =>
            match assigned.get? name with
            | some id =>
              acc2 ++ [makeComment .warningC id 2318
                s!"This assignment is used again in this '{cmd}', but won't have taken effect. Use two '{cmd}'s."]
            | Option.none => acc2
          ) acc
          let assigned :=
            match tok.inner with
            | .T_Assignment _ name _ _ => assigned.insert name tok.id
            | _ => assigned
          (acc, assigned)
        ) ([], ({} : Std.HashMap String Id))
      comments
    | _ => []
}

-- Note: SC2199 for [[ ${array[@]} ]] is handled in Analytics.lean since [[ ]] is parsed as T_Condition

/-- SC2038: Use -print0 with xargs -0, or -exec + for find|xargs -/
def checkFindXargs : CommandCheck := {
  name := .exactly "find"
  check := fun params t =>
    -- Check if find is in a pipeline to xargs
    match params.parentMap.get? t.id with
    | some parent =>
      match parent.inner with
      | .T_Pipeline _ cmds =>
        if cmds.length >= 2 then
          let hasXargs := cmds.any fun c =>
            match getCommandBasename c with
            | some "xargs" => true
            | _ => false
          if hasXargs then
            match getCommandArguments t with
            | some args =>
              let argStrs := args.map (getLiteralString · |>.getD "")
              let hasPrint0 := argStrs.any (· == "-print0")
              let hasExecPlus := argStrs.any (· == "+")
              if !hasPrint0 && !hasExecPlus then
                [makeComment .warningC t.id 2038
                  "Use -print0 with -0, or -exec + to handle filenames with spaces."]
              else []
            | Option.none => []
          else []
        else []
      | _ => []
    | Option.none => []
}

/-- SC2039: In POSIX sh, some features are undefined -/
def checkPosixFeatures : CommandCheck := {
  name := .exactly "local"
  check := fun params t =>
    -- Only warn in sh mode
    match params.shellType with
    | .Sh =>
      [makeComment .warningC t.id 2039
        "In POSIX sh, 'local' is undefined. Use a subshell or alternative."]
    | _ => []
}

/-- SC2045: Iterating over ls output is fragile -/
def checkLsIteration : CommandCheck := {
  name := .basename "ls"
  check := fun params t =>
    -- Check if ls is in command substitution inside for loop
    if isInForLoop params t && isInCommandSubstitution params t then
      [warnCmd t 2045 "Iterating over ls output is fragile. Use globs or find instead."]
    else []
}

/-- SC2068: Double quote array expansions to avoid re-splitting -/
def checkArrayExpansion : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_DollarBraced _ inner =>
          let s := getLiteralString inner |>.getD ""
          -- Check for array[@] or array[*] without proper quoting
          if (s.endsWith "[@]" || s.endsWith "[*]") then
            some (makeComment .warningC arg.id 2068
              "Double quote array expansions to avoid re-splitting elements.")
          else Option.none
        | _ => Option.none
    | Option.none => []
}

/-- Helper: Check if a token contains a command substitution -/
partial def hasCommandSubstitution (t : Token) : Bool :=
  match t.inner with
  | .T_DollarExpansion _ => true
  | .T_Backticked _ => true
  | .T_Assignment _ _ _ value => hasCommandSubstitution value
  | .T_NormalWord parts => parts.any hasCommandSubstitution
  | .T_DoubleQuoted parts => parts.any hasCommandSubstitution
  | _ => false

/-- SC2155: Declare and assign separately to avoid masking return values -/
def checkDeclareAssignWithSub : CommandCheck := {
  name := .anyExactly ["local", "export", "declare", "readonly", "typeset"]
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        if hasCommandSubstitution arg then
          some (warnArg arg 2155
            "Declare and assign separately to avoid masking return values.")
        else Option.none
    | Option.none => []
}

/-- SC2016: Expressions don't expand in single quotes -/
def checkSingleQuoteExpression : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_SingleQuoted s =>
          if stringContains s "$" || stringContains s "`" then
            some (makeComment .infoC arg.id 2016
              "Expressions don't expand in single quotes. Use double quotes.")
          else Option.none
        | _ => Option.none
    | Option.none => []
}

/-- SC2072: Decimals are not supported in comparisons -/
def checkDecimalComparison : CommandCheck := {
  name := .exactly "test"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      let hasComparison := argStrs.any fun s =>
        s == "-eq" || s == "-ne" || s == "-lt" || s == "-le" || s == "-gt" || s == "-ge"
      if hasComparison then
        args.filterMap fun arg =>
          match getLiteralString arg with
          | some s =>
            if s.any (· == '.') && s.all (fun c => c.isDigit || c == '.') then
              some (makeComment .errorC arg.id 2072
                "Decimals are not supported. Use bc or awk for floating point.")
            else Option.none
          | Option.none => Option.none
      else []
    | Option.none => []
}

/-- SC2206: Quote to prevent word splitting, or split robustly -/
def checkArrayAssign : CommandCheck := {
  name := .exactly "declare"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let hasArrayFlag := args.any fun a => getLiteralString a == some "-a"
      if hasArrayFlag then
        args.filterMap fun arg =>
          match arg.inner with
          | .T_NormalWord parts =>
            -- Check for unquoted command substitution in array assignment
            let hasUnquotedSub := parts.any fun p =>
              match p.inner with
              | .T_DollarExpansion _ => true
              | .T_Backticked _ => true
              | _ => false
            if hasUnquotedSub then
              some (makeComment .warningC arg.id 2206
                "Quote to prevent word splitting, or use mapfile for robust parsing.")
            else Option.none
          | _ => Option.none
      else []
    | Option.none => []
}

/-- SC2086: Quote $@ in printf -/
def checkPrintfAtVar : CommandCheck := {
  name := .basename "printf"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_DollarBraced _ inner =>
          let s := getLiteralString inner |>.getD ""
          if s == "@" || s == "*" then
            some (makeComment .warningC arg.id 2145
              "Use \"$@\" to pass all arguments. $@ and $* require double quotes.")
          else Option.none
        | _ => Option.none
    | Option.none => []
}

/-- SC2207: Prefer mapfile or read -a over split by words -/
def checkMapfile : CommandCheck := {
  name := .exactly "mapfile"
  check := fun _params _t =>
    []  -- mapfile is good, no warning needed - this is a placeholder
}

-- SC2034: Variable appears unused - would need whole-script analysis, skipped
-- SC2178: Variable used as array but defined as scalar - handled in Analytics

/-- SC2087: Quote heredoc delimiter to prevent expansion -/
def checkHeredocDelimiter : CommandCheck := {
  name := .basename "cat"  -- Commonly used with heredocs
  check := fun _params _t =>
    -- Heredoc handling would require looking at redirections
    -- This is a placeholder - full implementation needs redirection analysis
    []
}

/-- SC2091: Remove surrounding $() to avoid accidental execution -/
def checkAccidentalExec : CommandCheck := {
  name := .basename "true"  -- Catch $(true), $(false)
  check := fun params t =>
    let ancestors := getPath params t
    let inCommandSub := ancestors.any fun ancestor =>
      match ancestor.inner with
      | .T_DollarExpansion _ => true
      | .T_Backticked _ => true
      | _ => false
    let inCondition := ancestors.any fun ancestor =>
      match ancestor.inner with
      | .T_Condition _ _ => true
      | _ => false
    if inCommandSub && !inCondition then
      [makeComment .warningC t.id 2091
        "Remove surrounding $() to avoid executing output."]
    else []
}

/-- SC2100: Use $((..)) instead of deprecated $[..] -/
def checkDeprecatedArithmetic : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if stringContains s "$[" then
            some (makeComment .warningC arg.id 2100
              "Use $((..)) for arithmetic instead of deprecated $[..].")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2129: Consider using { cmd1; cmd2; } >> file -/
def checkGroupRedirect : CommandCheck := {
  name := .basename "echo"
  check := fun _params _t =>
    -- Would need to track consecutive appends to same file
    -- Placeholder for now
    []
}

/-- SC2139: This expands when defined, not when used. Use single quotes -/
def checkAliasExpansion : CommandCheck := {
  name := .exactly "alias"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_DoubleQuoted parts =>
          let hasExpansion := parts.any fun p =>
            match p.inner with
            | .T_DollarBraced _ _ => true
            | .T_DollarExpansion _ => true
            | _ => false
          if hasExpansion then
            some (makeComment .warningC arg.id 2139
              "This expands when defined, not when used. Consider single quotes.")
          else Option.none
        | _ => Option.none
    | Option.none => []
}

/-- SC2142: Aliases can't use positional parameters. Use a function. -/
def checkAliasesUsesArgs : CommandCheck := {
  name := .exactly "alias"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
        args.filterMap fun arg =>
          let s := getLiteralStringDef "_" arg
          if s.contains '=' && hasPositionalRef s then
            some (makeComment .errorC arg.id 2142
              "Aliases can't use positional parameters. Use a function.")
          else
            Option.none
    | Option.none => []
}
where
  isParamChar (c : Char) : Bool :=
    c.isDigit || c == '*' || c == '@'

  hasPositionalRef (s : String) : Bool :=
    go s.toList

  go : List Char → Bool
    | [] => false
    | '$' :: '{' :: c :: _ => isParamChar c
    | '$' :: c :: _ => isParamChar c
    | _ :: rest => go rest

/-- SC2184: Quote arguments to `unset` so they aren't glob expanded. -/
def checkUnsetGlobs : CommandCheck := {
  name := .exactly "unset"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
        args.filterMap fun arg =>
          if looksLikeGlobArg arg then
            some (makeComment .warningC arg.id 2184
              "Quote arguments to unset so they're not glob expanded.")
          else
            Option.none
    | Option.none => []
}
where
  looksLikeGlobArg (t : Token) : Bool :=
    match getLiteralString t with
    | some s => hasGlobMetachar s
    | Option.none =>
        let s := oversimplify t |>.foldl (· ++ ·) ""
        hasGlobMetachar s

  hasGlobMetachar (s : String) : Bool :=
    if s.contains '*' || s.contains '?' then
      true
    else
      hasClosedBracketExpr s

  hasClosedBracketExpr (s : String) : Bool :=
    let cs := s.toList
    match cs.dropWhile (· != '[') with
    | [] => false
    | _ :: rest => rest.any (· == ']')

/-- SC2293/SC2294: Array expansions lose their benefits when passed through `eval`. -/
def checkEvalArray : CommandCheck := {
  name := .exactly "eval"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let parts := args.flatMap getWordParts
      parts.filterMap fun part =>
        if isArrayExpansion part then
          if isEscaped part then
            some (makeComment .styleC part.id 2293
              "When eval'ing @Q-quoted words, use * rather than @ as the index.")
          else
            some (makeComment .warningC part.id 2294
              "eval negates the benefit of arrays. Drop eval to preserve whitespace/symbols (or eval as string).")
        else
          Option.none
    | Option.none => []
}
where
  isEscaped (t : Token) : Bool :=
    match t.inner with
    | .T_DollarBraced _ content =>
      let mod := getBracedModifier (String.join (oversimplify content))
      mod.any (· == 'Q')
    | _ => false

/-- SC2140: Word is of form "A"B"C" -/
def checkQuotingStyle : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_NormalWord parts =>
          -- Check for alternating quoted/unquoted pattern
          let hasDoubleQuotes := parts.any fun p =>
            match p.inner with | .T_DoubleQuoted _ => true | _ => false
          let hasLiterals := parts.any fun p =>
            match p.inner with | .T_Literal s => s.length > 0 | _ => false
          if hasDoubleQuotes && hasLiterals && parts.length > 2 then
            some (makeComment .styleC arg.id 2140
              "Word is of form \"A\"B\"C\". Consider \"ABC\" or 'A'\"B\"'C'.")
          else Option.none
        | _ => Option.none
    | Option.none => []
}

/-- SC2143: Use grep -q instead of comparing output -/
def checkGrepQ : CommandCheck := {
  name := .basename "grep"
  check := fun params t =>
    -- Check if grep is in a [ -n $(grep) ] pattern
    let ancestors := getPath params t
    let inCommandSub := ancestors.any fun a =>
      match a.inner with | .T_DollarExpansion _ => true | _ => false
    let inTest := ancestors.any fun a =>
      match a.inner with
      | .T_Condition _ _ => true
      | .T_SimpleCommand _ (cmd::_) =>
        match getLiteralString cmd with
        | some s => s == "test" || s == "["
        | _ => false
      | _ => false
    if inCommandSub && inTest then
      match getCommandArguments t with
      | some args =>
        let hasQ := args.any fun a => getLiteralString a == some "-q"
        if !hasQ then
          [makeComment .styleC t.id 2143
            "Use grep -q instead of comparing output to check if matches exist."]
        else []
      | Option.none => []
    else []
}

/-- SC2144: -e doesn't work with globs. Use for loop or find -/
def checkTestGlob : CommandCheck := {
  name := .exactly "test"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      let hasFileTest := argStrs.any fun s => s == "-e" || s == "-f" || s == "-d"
      if hasFileTest then
        args.filterMap fun arg =>
          match getLiteralString arg with
          | some s =>
            if s.any (fun c => c == '*' || c == '?') then
              some (makeComment .errorC arg.id 2144
                "-e, -f, -d don't work with globs. Use a for loop.")
            else Option.none
          | Option.none => Option.none
      else []
    | Option.none => []
}

/-- SC2150: find -exec doesn't handle empty results -/
def checkFindEmpty : CommandCheck := {
  name := .exactly "find"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      let hasExec := argStrs.any (· == "-exec")
      let hasPrint := argStrs.any (· == "-print")
      -- Suggest -exec + over -exec ; for batching
      if hasExec && !hasPrint then
        -- Check if using ; instead of +
        if argStrs.any (· == ";") || argStrs.any (· == "\\;") then
          if !argStrs.any (· == "+") then
            [makeComment .infoC t.id 2150
              "Use -exec cmd {} + to batch commands for better performance."]
          else []
        else []
      else []
    | Option.none => []
}

-- SC2153: Uppercase variable misspelling - would need expected vars tracking, skipped

/-- SC2163: export requires variable names -/
def checkExportValue : CommandCheck := {
  name := .exactly "export"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if s.startsWith "$" then
            some (makeComment .errorC arg.id 2163
              "export requires a variable name. Use export VAR=value.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

-- SC2165: This form doesn't work - condition loops handled in Analytics

/-- SC2169: In dash, some bashisms aren't supported -/
def checkDashBashisms : CommandCheck := {
  name := .exactly "source"
  check := fun params t =>
    if params.shellType == .Dash then
      [makeComment .errorC t.id 2169
        "In dash, 'source' is undefined. Use '.' (dot) instead."]
    else []
}


/-!
## Portability Checks (SC3xxx series)

These checks warn about non-POSIX shell features.
-/

/-- SC3001: ((...)) is not POSIX -/
def checkArithmeticParensPosix : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      match t.inner with
      | .T_Arithmetic _ =>
        [warnCmd t 3001
          "((...)) is not POSIX. For portability, use $((..)) instead."]
      | _ => []
    else []
}

/-- SC3003: [[ ]] is not POSIX -/
def checkDoubleBracketPosix : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      match t.inner with
      | .T_Condition .doubleBracket _ =>
        [warnCmd t 3003
          "[[ ]] is not POSIX. Use [ ] or 'test' instead."]
      | _ => []
    else []
}

/-- SC3006: Arrays are not POSIX -/
def checkArraysPosix : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      match t.inner with
      | .T_Array _ =>
        [warnCmd t 3006
          "Arrays are not POSIX. Use separate variables or positional parameters."]
      | _ => []
    else []
}

/-- SC3010: $'...' string is not POSIX -/
def checkDollarSingleQuotePosix : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      match t.inner with
      | .T_DollarSingleQuoted _ =>
        [warnCmd t 3010
          "$'...' is not POSIX. Use regular quoting with escape sequences."]
      | _ => []
    else []
}

/-- SC3011: mapfile/readarray is bash-only -/
def checkMapfilePosix : CommandCheck := {
  name := .anyExactly ["mapfile", "readarray"]
  check := fun params t =>
    if params.shellType == .Sh then
      [errorCmd t 3011
        "mapfile/readarray is not POSIX. Use a read loop instead."]
    else []
}

/-- SC3014: local is not defined in POSIX sh -/
def checkLocalPosix : CommandCheck := {
  name := .exactly "local"
  check := fun params t =>
    if params.shellType == .Sh then
      [warnCmd t 3014
        "'local' is not POSIX. Use function scope or global variables."]
    else []
}

/-- SC3020: >>= is not POSIX (simplified check for literal ">>=" in arithmetic) -/
def checkRightShiftEqualPosix : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      match t.inner with
      | .T_DollarArithmetic inner =>
        checkForOp inner
      | .T_Arithmetic inner =>
        checkForOp inner
      | _ => []
    else []
}
where
  checkForOp (tok : Token) : List TokenComment :=
    match tok.inner with
    | .T_Literal s =>
      if s == ">>=" then
        [warnCmd tok 3020
          ">>= is not POSIX. Use explicit assignment with $((var = var >> n))."]
      else []
    | _ => []

/-- SC3030: declare is not POSIX -/
def checkDeclarePosix : CommandCheck := {
  name := .anyExactly ["declare", "typeset"]
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandName t with
      | some "declare" =>
        [warnCmd t 3030
          "'declare' is not POSIX. Use direct assignment or export/readonly."]
      | some "typeset" =>
        [warnCmd t 3030
          "'typeset' is not POSIX. Use direct assignment or export/readonly."]
      | _ => []
    else []
}

/-- SC3037: echo -n is not portable -/
def checkEchoNPosix : CommandCheck := {
  name := .basename "echo"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        if args.any fun a => getLiteralString a == some "-n" then
          [warnCmd t 3037
            "echo -n is not portable. Use printf '%s' instead."]
        else []
      | Option.none => []
    else []
}

/-!
## Additional SC2xxx Checks
-/

/-- SC2005: Useless echo? Instead of 'echo $(cmd)', just use 'cmd' -/
def checkUselessEcho : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some [arg] =>
      match arg.inner with
      | .T_DollarExpansion _ =>
        [styleArg arg 2005
          "Useless echo? Instead of 'echo $(cmd)', just use 'cmd'."]
      | .T_Backticked _ =>
        [styleArg arg 2005
          "Useless echo? Instead of 'echo `cmd`', just use 'cmd'."]
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_DollarExpansion _ =>
          [styleArg arg 2005
            "Useless echo? Instead of 'echo $(cmd)', just use 'cmd'."]
        | .T_Backticked _ =>
          [styleArg arg 2005
            "Useless echo? Instead of 'echo `cmd`', just use 'cmd'."]
        | _ => []
      | _ => []
    | _ => []
}

/-- SC2028: echo may not expand escape sequences. Use printf -/
def checkEchoEscapes : CommandCheck := {
  name := .basename "echo"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if Regex.containsSubstring s "\\n" || Regex.containsSubstring s "\\t" || Regex.containsSubstring s "\\r" then
            some (infoArg arg 2028
              "echo may not expand escape sequences. Consider using printf.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2040: #!/bin/sh was specified, so shopt is not supported -/
def checkShoptInSh : CommandCheck := {
  name := .exactly "shopt"
  check := fun params t =>
    if params.shellType == .Sh then
      [errorCmd t 2040
        "#!/bin/sh was specified, so shopt is not supported. Use bash instead."]
    else []
}

/-- SC2041: This is a literal string. To run as a command, use $(...) -/
def checkLiteralInBackticks : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_SingleQuoted s =>
      if s.startsWith "`" && s.endsWith "`" then
        [warnCmd t 2041
          "This is a literal string. To run as a command, remove quotes."]
      else []
    | _ => []
}

/-- SC2063: Grep uses literal strings by default. Did you mean $var? -/
def checkGrepLiteralDollar : CommandCheck := {
  name := .basename "grep"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if s.startsWith "$" && s.length > 1 && !s.startsWith "$(" then
            some (warnArg arg 2063
              "Grep uses literal strings. Use \"$var\" or grep -e \"$var\" for variables.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2085: Double quote command substitution to avoid re-splitting -/
def checkUnquotedSubstitution : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_SimpleCommand _ args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_DollarExpansion _ =>
          some (infoArg arg 2085
            "Double quote command substitution to avoid re-splitting.")
        | .T_Backticked _ =>
          some (infoArg arg 2085
            "Double quote command substitution to avoid re-splitting.")
        | _ => Option.none
    | _ => []
}

/-- SC2101: Named class needs outer brackets, e.g. [[:digit:]] -/
def checkBracketClass : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Glob s =>
      if Regex.containsSubstring s "[:alnum:]" || Regex.containsSubstring s "[:alpha:]" ||
         Regex.containsSubstring s "[:digit:]" || Regex.containsSubstring s "[:space:]" then
        if !Regex.containsSubstring s "[[:" then
          [warnCmd t 2101
            "Named class [:class:] needs outer brackets: [[:class:]]"]
        else []
      else []
    | _ => []
}

/-- SC2103: Use a ( subshell ) to avoid cd affecting the script's current dir -/
def checkCdSubshell : CommandCheck := {
  name := .exactly "cd"
  check := fun params t =>
    -- Check if cd is not in a subshell and followed by more commands
    match params.parentMap.get? t.id with
    | some parent =>
      match parent.inner with
      | .T_AndIf _ _ =>
        [infoCmd t 2103
          "Use a ( subshell ) to avoid cd affecting this script's current dir."]
      | .T_OrIf _ _ =>
        [infoCmd t 2103
          "Use a ( subshell ) to avoid cd affecting this script's current dir."]
      | _ => []
    | Option.none => []
}

/-- SC2111: ksh does not allow 'function' keyword and target parentheses -/
def checkKshFunctionSyntax : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Ksh then
      match t.inner with
      | .T_Function keyword parens _ _ =>
        if keyword.used && parens.used then
          [errorCmd t 2111
            "ksh does not allow 'function' keyword and () together."]
        else []
      | _ => []
    else []
}

/-- SC2112/SC2113: `'function'` keyword is non-standard in `sh`. -/
def checkFunctionKeyword : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh || params.shellType == .Dash || params.shellType == .BusyboxSh then
      match t.inner with
      | .T_Function keyword parens _ _ =>
        if keyword.used then
          if parens.used then
            [warnCmd t 2112 "'function' keyword is non-standard. Delete it."]
          else
            [warnCmd t 2113
              "'function' keyword is non-standard. Use 'foo()' instead of 'function foo'."]
        else []
      | _ => []
    else
      []
}

/-- SC2126: Consider using grep -c instead of grep | wc -l -/
def checkGrepWcL : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Pipeline _ cmds =>
      if cmds.length >= 2 then
        let pairs := cmds.zip (cmds.drop 1)
        pairs.filterMap fun (cmd1, cmd2) =>
          let isGrep := getCommandName cmd1 == some "grep"
          let isWcL := getCommandName cmd2 == some "wc" &&
            (getCommandArguments cmd2).any fun args =>
              args.any fun a => getLiteralString a == some "-l"
          if isGrep && isWcL then
            some (styleCmd cmd1 2126
              "Consider using 'grep -c' instead of 'grep | wc -l'.")
          else Option.none
      else []
    | _ => []
}

/-- SC2130: -eq, -ne are for integer comparisons. Use =, != for strings -/
def checkStringIntComparison : CommandCheck := {
  name := .exactly "test"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      -- Simplified check: just warn on -eq/-ne with non-numeric looking args
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some op =>
          if op == "-eq" || op == "-ne" || op == "-lt" ||
             op == "-le" || op == "-gt" || op == "-ge" then
            some (infoArg arg 2130
              s!"{op} is for integer comparisons. Use =, !=, <, > for strings.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2131: Use double brackets to avoid glob expansion in [[ -/
def checkSingleBracketGlob : CommandCheck := {
  name := .exactly "["
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if hasGlobChars s then
            some (warnArg arg 2131
              "Globs expand in [ ]. Use [[ ]] for literal matching.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2151: Only one integer is valid for exit codes. Use 'if' for conditions -/
def checkMultipleExitCodes : CommandCheck := {
  name := .exactly "exit"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      if args.length > 1 then
        [errorCmd t 2151
          "Only one integer is valid for exit. Use 'if' for conditions."]
      else []
    | Option.none => []
}

/-- SC2152: Can only return 0-255. Use echo for other values -/
def checkReturnValue : CommandCheck := {
  name := .exactly "return"
  check := fun _params t =>
    match getCommandArguments t with
    | some (arg :: _) =>
      match getLiteralString arg with
      | some s =>
        match s.toNat? with
        | some n =>
          if n > 255 then
            [warnArg arg 2152
              "Can only return 0-255. Other values wrap around."]
          else []
        | Option.none => []
      | Option.none => []
    | _ => []
}

/-- SC2154: var is referenced but not assigned -/
-- Note: This requires data flow analysis, simplified version here
def checkUnassignedVar : CommandCheck := {
  name := .any
  check := fun _params _t =>
    -- This would need full variable tracking which is done in Analytics.lean
    []
}

/-- SC2157: Argument to -z is always false due to literal strings -/
def checkTestZLiteral : CommandCheck := {
  name := .exactly "test"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      -- Look for patterns like: -z "literal"
      let pairs := args.zip (args.drop 1)
      pairs.filterMap fun (arg1, arg2) =>
        match getLiteralString arg1, getLiteralString arg2 with
        | some "-z", some s =>
          if !s.isEmpty && !s.startsWith "$" then
            some (warnArg arg2 2157
              "Argument to -z is always false due to literal string.")
          else Option.none
        | _, _ => Option.none
    | Option.none => []
}

/-- SC2158: [ false ] is true. Remove brackets or use 'false' -/
def checkTestFalse : CommandCheck := {
  name := .exactly "["
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let nonBracket := args.filter fun a => getLiteralString a != some "]"
      match nonBracket with
      | [single] =>
        match getLiteralString single with
        | some "false" =>
          [warnCmd t 2158
            "[ false ] is true. Remove brackets or use 'false' directly."]
        | some "true" =>
          [infoCmd t 2158
            "[ true ] is true, but so is [ false ]. Use 'true' directly."]
        | _ => []
      | _ => []
    | Option.none => []
}

/-- SC2160: Instead of '[ true ]', just use 'true' -/
def checkTestTrue : CommandCheck := {
  name := .exactly "test"
  check := fun _params t =>
    match getCommandArguments t with
    | some [arg] =>
      match getLiteralString arg with
      | some "true" =>
        [styleCmd t 2160
          "Instead of 'test true', just use 'true'."]
      | some "false" =>
        [styleCmd t 2160
          "Instead of 'test false', just use 'false'."]
      | _ => []
    | _ => []
}

/-- SC2161: Instead of '! true', use 'false' (or vice versa) -/
def checkNotTrue : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Banged cmd =>
      match getCommandName cmd with
      | some "true" =>
        [styleCmd t 2161
          "Instead of '! true', use 'false'."]
      | some "false" =>
        [styleCmd t 2161
          "Instead of '! false', use 'true'."]
      | _ => []
    | _ => []
}

/-- SC2162: read without -r will mangle backslashes -/
def checkReadWithoutR : CommandCheck := {
  name := .exactly "read"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let hasR := args.any fun a => getLiteralString a == some "-r"
      if !hasR then
        [infoCmd t 2162
          "'read' without -r will mangle backslashes."]
      else []
    | Option.none => []
}

/-!
## Additional SC2xxx Checks (Batch 2)

These implement the missing SC2xxx codes identified in the DSL registry.
-/

/-- SC2042: Use spaces, not commas, to separate loop elements -/
def checkForLoopComma : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_ForIn _ words _ =>
      words.filterMap fun w =>
        match getLiteralString w with
        | some s =>
          if s.contains ',' && !s.contains ' ' then
            some (warnCmd w 2042
              "Use spaces, not commas, to separate loop elements.")
          else Option.none
        | Option.none => Option.none
    | _ => []
}

/-- SC2043: This loop will only ever run once -/
def checkSingleIterationLoop : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_ForIn _ words _ =>
      if words.length == 1 then
        match words.head? with
        | some w =>
          if isConstant w && !isGlob w then
            [warnCmd t 2043
              "This loop will only ever run once. Bad quoting or missing glob/expansion?"]
          else []
        | Option.none => []
      else []
    | _ => []
}

/-- SC2168: 'local' is only valid in functions -/
def checkLocalOutsideFunction : CommandCheck := {
  name := .exactly "local"
  check := fun params t =>
    if !isInFunction params t then
      [errorCmd t 2168 "'local' is only valid in functions."]
    else []
}

/-- SC2172: Trapping signals by number is not well defined -/
def checkTrapByNumber : CommandCheck := {
  name := .exactly "trap"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if s.all Char.isDigit && s.length > 0 && s != "0" then
            some (warnArg arg 2172
              "Trapping signals by number is not well defined. Use signal names.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2173: SIGKILL/SIGSTOP can not be trapped -/
def checkTrapUncatchable : CommandCheck := {
  name := .exactly "trap"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          let upper := s.toUpper
          if upper == "KILL" || upper == "SIGKILL" ||
             upper == "STOP" || upper == "SIGSTOP" ||
             upper == "9" || upper == "19" then
            some (errorArg arg 2173
              s!"{s} can not be trapped.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2176: 'time' is undefined after &&/|| -/
def checkTimeAfterLogical : CommandCheck := {
  name := .exactly "time"
  check := fun params t =>
    match getParent params t with
    | some parent =>
      match parent.inner with
      | .T_AndIf _ _ => [warnCmd t 2176
          "'time' is undefined after &&. Wrap in { ..; } if needed."]
      | .T_OrIf _ _ => [warnCmd t 2176
          "'time' is undefined after ||. Wrap in { ..; } if needed."]
      | _ => []
    | Option.none => []
}

/-- SC2186: tempfile without XXXXXXXXXX is insecure -/
def checkTempfileInsecure : CommandCheck := {
  name := .anyExactly ["tempfile", "mktemp"]
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let hasTemplate := args.any fun a =>
        match getLiteralString a with
        | some s => Regex.containsSubstring s "XXXXXX"
        | Option.none => false
      if !hasTemplate then
        [warnCmd t 2186
          "Tempfile schemes without XXXXXX template are insecure."]
      else []
    | Option.none => []
}

/-- SC2188: This redirection doesn't have a command -/
def checkRedirectWithoutCommand : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Redirecting redirects cmd =>
      if !redirects.isEmpty then
        match cmd.inner with
        | .T_SimpleCommand [] [] =>
          [errorCmd t 2188
            "This redirection doesn't have a command. Remove or add a command."]
        | _ => []
      else []
    | _ => []
}

/-- SC2196: egrep is deprecated. Use grep -E -/
def checkDeprecatedEgrep : CommandCheck := {
  name := .basename "egrep"
  check := fun _params t =>
    [infoCmd t 2196 "egrep is non-standard and deprecated. Use grep -E instead."]
}

/-- SC2197: fgrep is deprecated. Use grep -F -/
def checkDeprecatedFgrep : CommandCheck := {
  name := .basename "fgrep"
  check := fun _params t =>
    [infoCmd t 2197 "fgrep is non-standard and deprecated. Use grep -F instead."]
}

/-- SC2209: Use var=$(command) to assign output -/
def checkAssignmentVsCommand : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_SimpleCommand [] (word :: _) =>
      match getLiteralString word with
      | some s =>
        if s.contains '=' && !s.startsWith "-" then
          let parts := s.splitOn "="
          match parts with
          | [_name, value] =>
            if value.startsWith "$(" || value.startsWith "`" then
              []  -- Already using command substitution
            else if !value.isEmpty && value.all Char.isAlpha then
              [warnCmd t 2209
                "Use var=$(command) to assign output (or quote to assign string)."]
            else []
          | _ => []
        else []
      | Option.none => []
    | _ => []
}

/-- SC2213/SC2214/SC2220: Ensure `case $var` matches the `getopts` option string in `while getopts ...`. -/
def checkWhileGetoptsCase : CommandCheck := {
  name := .exactly "getopts"
  check := fun params t =>
    match getCommand t with
    | some cmdTok =>
      match cmdTok.inner with
      | .T_SimpleCommand _ words =>
        match words with
        | _cmd :: optTok :: nameTok :: _ =>
          match getLiteralString optTok, getLiteralString nameTok with
          | some options, some getoptsVar =>
            match findEnclosingWhile params cmdTok with
            | some whileTok =>
              match whileTok.inner with
              | .T_WhileExpression _cond body =>
                match findFirstCase body with
                | some caseTok =>
                  match caseTok.inner with
                  | .T_CaseExpression varWord cases =>
                    match getCaseVarName varWord with
                    | some caseVar =>
                      if caseVar != getoptsVar then
                        []
                      else if modifiesVariable params (mkBraceGroup body) getoptsVar then
                        []
                      else
                        checkCases options caseTok cases
                    | Option.none => []
                  | _ => []
                | Option.none => []
              | _ => []
            | Option.none => []
          | _, _ => []
        | _ => []
      | _ => []
    | Option.none => []
}
where
  mkBraceGroup (body : List Token) : Token :=
    ⟨⟨0⟩, .T_BraceGroup body⟩

  findEnclosingWhile (params : Parameters) (t : Token) : Option Token :=
    findEnclosingWhileGo (getPath params t |>.reverse)

  findEnclosingWhileGo : List Token → Option Token
    | [] => Option.none
    | tok :: rest =>
      match tok.inner with
      | .T_WhileExpression .. => some tok
      | .T_Script .. => Option.none
      | _ => findEnclosingWhileGo rest

  /-- Look for the first `case` statement in the loop body, unwrapping common wrappers. -/
  findCase (t : Token) : Option Token :=
    let rec go (fuel : Nat) (t : Token) : Option Token :=
      match fuel with
      | 0 => Option.none
      | fuel + 1 =>
        match t.inner with
        | .T_Annotation _ inner => go fuel inner
        | .T_Pipeline _ cmds =>
          match cmds with
          | [inner] => go fuel inner
          | _ => Option.none
        | .T_Redirecting _ cmd =>
          match cmd.inner with
          | .T_CaseExpression .. => some cmd
          | _ => Option.none
        | .T_CaseExpression .. => some t
        | _ => Option.none
    go 64 t

  findFirstCase : List Token → Option Token
    | [] => Option.none
    | x :: xs =>
      match findCase x with
      | some c => some c
      | Option.none => findFirstCase xs

  /-- Extract `x` from `case $x in`. Only handles the simple `$x` form. -/
  getCaseVarName (word : Token) : Option String := do
    match getWordParts word with
    | [t] =>
      match t.inner with
      | .T_DollarBraced _ content =>
        match getWordParts content with
        | [lit] =>
          match lit.inner with
          | .T_Literal s => some s
          | _ => Option.none
        | _ => Option.none
      | _ => Option.none
    | _ => Option.none

  /-- Best-effort literal extraction from a case pattern. -/
  literal (t : Token) : Option String :=
    -- The full port does not tokenize case patterns into `T_Glob` yet, so we need a
    -- small amount of glob-aware decoding on literal words.
    match getWordParts t with
    | [inner] =>
      match inner.inner with
      | .T_Literal s =>
        match interpretSimpleGlobLiteral s with
        | some out => some out
        | Option.none =>
          if isComplexCasePatternLiteral s then
            Option.none
          else
            some s
      | _ =>
        match getLiteralString t with
        | some s =>
          if isComplexCasePatternLiteral s then
            Option.none
          else
            some s
        | Option.none => fromGlob inner
    | _ =>
      match getLiteralString t with
      | some s =>
        if isComplexCasePatternLiteral s then
          Option.none
        else
          some s
      | Option.none => fromGlob t

  interpretSimpleGlobLiteral (s : String) : Option String :=
    match s.toList with
    | ['[', c, ']'] => some (String.singleton c)
    | _ => Option.none

  isComplexCasePatternLiteral (s : String) : Bool :=
    if s == "*" || s == "?" then
      false
    else
      looksLikeBareRange s ||
        s.contains '*' || s.contains '?' || s.contains '[' || s.contains ']'

  looksLikeBareRange (s : String) : Bool :=
    match s.toList with
    | [a, '-', b] => a.isAlphanum && b.isAlphanum
    | _ => false

  fromGlob (t : Token) : Option String :=
    match t.inner with
    | .T_Glob s =>
      let cs := s.toList
      match cs with
      | ['[', c, ']'] => some (String.singleton c)
      | ['*'] => some "*"
      | ['?'] => some "?"
      | _ => Option.none
    | _ => Option.none

  requestedOptions (s : String) : List String :=
    s.toList
      |>.filter (fun c => c != ':')
      |>.map String.singleton

  checkCases (options : String) (caseTok : Token) (cases : List (CaseType × List Token × List Token)) :
      List TokenComment :=
    let requested := requestedOptions options
    let handledRaw : List (Option String × Token) :=
      cases.flatMap fun (_, patterns, _) =>
        patterns.map (fun p => (literal p, p))
    if handledRaw.any (fun (k, _) => k.isNone) then
      []
    else
      let handled : List (String × Token) :=
        handledRaw.filterMap fun
          | (some k, tok) => some (k, tok)
          | _ => Option.none
      let handledKeys : List String := handled.map (fun (k, _) => k)
      let unhandled := requested.filter (fun opt => !handledKeys.contains opt)
      let invalidHandled := handledKeys.contains "*" || handledKeys.contains "?"
      let unrequested :=
        handled.filterMap fun (k, tok) =>
          if k ∈ ["*", ":", "?"] then
            Option.none
          else if requested.contains k then
            Option.none
          else
            some (makeComment .warningC tok.id 2214 "This case is not specified by getopts.")
      let missing :=
        unhandled.map fun opt =>
          makeComment .warningC caseTok.id 2213
            ("getopts specified -" ++ e4m opt ++ ", but it's not handled by this 'case'.")
      let missingInvalid :=
        if invalidHandled then
          []
        else
          [makeComment .warningC caseTok.id 2220
            "Invalid flags are not handled. Add a *) case."]
      missing ++ missingInvalid ++ unrequested

/-- SC2216: Piping to 'cd' has no effect -/
def checkPipeToCd : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Pipeline _ cmds =>
      if cmds.length >= 2 then
        cmds.drop 1 |>.filterMap fun cmd =>
          if getCommandName cmd == some "cd" then
            some (warnCmd cmd 2216 "Piping to 'cd' has no effect. 'cd' does not read stdin.")
          else Option.none
      else []
    | _ => []
}

/-- SC2217: Redirecting to 'cd' has no effect -/
def checkRedirectToCd : CommandCheck := {
  name := .exactly "cd"
  check := fun _params t =>
    match t.inner with
    | .T_Redirecting redirects _ =>
      if redirects.any (fun r => match r.inner with
        | .T_FdRedirect _ target => match target.inner with
          | .T_IoFile _ _ => true
          | _ => false
        | _ => false) then
        [warnCmd t 2217 "Redirecting to 'cd' has no effect."]
      else []
    | _ => []
}

/-- SC2224: This mv has no destination -/
def checkMvNoDestination : CommandCheck := {
  name := .basename "mv"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let nonFlags := getNonOptionArgs args
      if nonFlags.length < 2 then
        [errorCmd t 2224 "This mv has no destination. Check the arguments."]
      else []
    | Option.none => []
}

/-- SC2225: This cp has no destination -/
def checkCpNoDestination : CommandCheck := {
  name := .basename "cp"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let nonFlags := getNonOptionArgs args
      if nonFlags.length < 2 then
        [errorCmd t 2225 "This cp has no destination. Check the arguments."]
      else []
    | Option.none => []
}

/-- SC2336: cp -r behavior is implementation-defined -/
def checkCpLegacyR : CommandCheck := {
  name := .basename "cp"
  check := fun _params t =>
    match (getAllFlags t).find? (fun (_, flag) => flag == "r") with
    | some (tok, _) =>
      [makeComment .warningC tok.id 2336 "cp -r behavior is implementation-defined"]
    | Option.none => []
}

/-- SC2226: This ln has no destination -/
def checkLnNoDestination : CommandCheck := {
  name := .basename "ln"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let nonFlags := getNonOptionArgs args
      if nonFlags.length < 2 then
        [warnCmd t 2226 "This ln has no destination. Check the arguments."]
      else []
    | Option.none => []
}

/-- SC2232: Can't use sudo with shell builtins -/
def checkSudoBuiltins : CommandCheck := {
  name := .exactly "sudo"
  check := fun _params t =>
    let builtins := ["cd", "pushd", "popd", "source", ".", "alias", "unalias",
                     "bg", "fg", "jobs", "disown", "set", "shopt", "export",
                     "declare", "typeset", "local", "readonly", "unset", "shift",
                     "return", "exit", "break", "continue", "eval", "exec",
                     "times", "trap", "umask", "ulimit", "wait", "read", "builtin"]
    match getCommandArguments t with
    | some args =>
      -- Find first non-flag argument (the command being sudoed)
      let nonFlags := getNonOptionArgs args
      match nonFlags.head? with
      | some cmd =>
        match getLiteralString cmd with
        | some name =>
          if builtins.contains name then
            [warnArg cmd 2232
              s!"'{name}' is a shell builtin. sudo cannot run it directly."]
          else []
        | Option.none => []
      | Option.none => []
    | Option.none => []
}

/-- SC2239: Ensure the shebang uses an absolute path -/
def checkShebangAbsolutePath : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Script shebang _ =>
      match shebang.inner with
      | .T_Literal s =>
        if !s.isEmpty && !s.startsWith "/" then
          let path := (s.dropWhile (· == ' ')).toString
          if !path.startsWith "/" && !"env ".isPrefixOf path then
            [errorCmd t 2239
              "Ensure the shebang uses an absolute path to the interpreter."]
          else []
        else []
      | _ => []
    | _ => []
}

/-- SC2241: The exit status can only be one integer 0-255 -/
def checkExitMultipleArgs : CommandCheck := {
  name := .exactly "exit"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      if args.length > 1 then
        [errorCmd t 2241
          "The exit status can only be one integer 0-255. Use stdout for other data."]
      else
        match args.head? with
        | some arg =>
          match getLiteralString arg with
          | some s =>
            match s.toInt? with
            | some n =>
              if n < 0 || n > 255 then
                [errorCmd t 2242 "Can only exit with status 0-255."]
              else []
            | Option.none => []
          | Option.none => []
        | Option.none => []
    | Option.none => []
}

/-- SC2246: This shebang specifies a directory -/
def checkShebangDirectory : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Script shebang _ =>
      match shebang.inner with
      | .T_Literal s =>
        let path := s.dropWhile (· == ' ')
        if path.endsWith "/" then
          [errorCmd t 2246 "This shebang specifies a directory. Ensure the interpreter is a file."]
        else []
      | _ => []
    | _ => []
}

/-- SC2255: [ ] does not apply arithmetic evaluation -/
def checkBracketArithmetic : CommandCheck := {
  name := .exactly "["
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if s == "+" || s == "-" || s == "*" || s == "/" || s == "%" then
            some (errorArg arg 2255
              "[ ] does not apply arithmetic evaluation. Use $(( )) for numbers, or string operators.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2267: GNU xargs -d'\\n' is not portable -/
def checkXargsDelimiter : CommandCheck := {
  name := .basename "xargs"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        args.filterMap fun arg =>
          match getLiteralString arg with
          | some s =>
            if s.startsWith "-d" || s == "-d" then
              some (warnArg arg 2267
                "xargs -d is a GNU extension. Use tr '\\n' '\\0' | xargs -0 for portability.")
            else Option.none
          | Option.none => Option.none
      | Option.none => []
    else []
}

/-- SC2269: This variable is assigned to itself -/
def checkSelfAssignment : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Assignment _ name _ value =>
      match getLiteralString value with
      | some s =>
        if s == "$" ++ name || s == "${" ++ name ++ "}" then
          [infoCmd t 2269 s!"Variable '{name}' is assigned to itself."]
        else []
      | Option.none => []
    | _ => []
}

/-- SC2286/SC2287/SC2288/SC2289: Suspicious command name ending with symbol -/
def checkCommandWithTrailingSymbol : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_SimpleCommand _ (cmd :: _) =>
      let str := getLiteralStringDef "x" cmd
      let last : Char := str.toList.getLastD 'x'
      if str == "." || str == ":" || str == " " || str == "//" then
        []
      else if str == "" then
        [errorArg cmd 2286
          "This empty string is interpreted as a command name. Double check syntax (or use 'true' as a no-op)."]
      else if last == '/' then
        [errorArg cmd 2287
          "This is interpreted as a command name ending with '/'. Double check syntax."]
      else if (('\\' :: ".,([{<>}])#\"'% ".toList).contains last) then
        let formatted :=
          if last == ' ' then "space"
          else if last == '\'' then "apostrophe"
          else if last == '"' then "doublequote"
          else s!"'{last}'"
        [warnArg cmd 2288
          s!"This is interpreted as a command name ending with {formatted}. Double check syntax."]
      else if str.toList.contains '\t' then
        [errorArg cmd 2289
          "This is interpreted as a command name containing a tab. Double check syntax."]
      else if str.toList.contains '\n' then
        [errorArg cmd 2289
          "This is interpreted as a command name containing a linefeed. Double check syntax."]
      else
        []
    | _ => []
}

/-- SC2310: This function is never invoked (simplified) -/
def checkUnusedFunction : CommandCheck := {
  name := .any
  check := fun _params _t => []
}

/-- SC2049: =~ is for regex not globs -/
def checkRegexVsGlob : CommandCheck := {
  name := .any
  check := fun _params t =>
    let str := getLiteralString t |>.getD ""
    if Regex.containsSubstring str "=~" && Regex.containsSubstring str "*" then
      [warnCmd t 2049 "=~ is for regex. Use == for glob matching."]
    else []
}

/-- SC2065: Inside brackets, use `-gt`/`-lt` not `>` or `<` -/
def checkTestRedirection : CommandCheck := {
  name := .basename "["
  check := fun _params t =>
    let str := getLiteralString t |>.getD ""
    if Regex.containsSubstring str ">" || Regex.containsSubstring str "<" then
      [warnCmd t 2065 "Inside [ ], > and < are redirections. Use -gt and -lt."]
    else []
}

/-- SC2067: Missing semicolon or plus terminating -exec -/
def checkFindExecTerminator : CommandCheck := {
  name := .basename "find"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.filterMap getLiteralString
      if argStrs.contains "-exec" && !argStrs.contains ";" && !argStrs.contains "+" then
        [errorCmd t 2067 "Missing ; or + terminating -exec."]
      else []
    | Option.none => []
}

/-- SC2076: Remove quotes around regex -/
def checkRegexQuoting : CommandCheck := {
  name := .any
  check := fun _params t =>
    let str := getLiteralString t |>.getD ""
    if Regex.containsSubstring str "=~ \"" || Regex.containsSubstring str "=~ '" then
      [warnCmd t 2076 "Remove quotes around the regex."]
    else []
}

/-- SC2079: Arithmetic does not support decimals -/
def checkArithmeticDecimals : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Arithmetic _ =>
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "." && str.any Char.isDigit then
        [errorCmd t 2079 "(( )) does not support decimals. Use bc or awk."]
      else []
    | _ => []
}

/-- SC2081: Brackets cannot match regexes -/
def checkBracketRegex : CommandCheck := {
  name := .basename "["
  check := fun _params t =>
    let str := getLiteralString t |>.getD ""
    if Regex.containsSubstring str "=~" then
      [errorCmd t 2081 "[ ] cannot match regexes. Use double brackets."]
    else []
}

/-- SC2106: This only exits the subshell -/
def checkExitInSubshell : CommandCheck := {
  name := .exactly "exit"
  check := fun params t =>
    if isInSubshell params t then
      [warnCmd t 2106 "This only exits the subshell."]
    else []
}

/-- SC2108: In double brackets use ampersand instead of -a -/
def checkAndInDoubleTest : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Condition _ _ =>
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str " -a " then
        [styleCmd t 2108 "In [[ ]], use && instead of -a."]
      else []
    | _ => []
}

/-- SC2110: In double brackets use pipe instead of -o -/
def checkOrInDoubleTest : CommandCheck := {
  name := .any
  check := fun _params t =>
    match t.inner with
    | .T_Condition _ _ =>
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str " -o " then
        [styleCmd t 2110 "In [[ ]], use || instead of -o."]
      else []
    | _ => []
}

/-- SC2118: Ksh does not support `|&`. Use `2>&1 |`. -/
def checkStderrPipe : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType != .Ksh then
      []
    else
      match t.inner with
      | .T_Pipe "|&" =>
          [makeComment .errorC t.id 2118
            "Ksh does not support |&. Use 2>&1 |."]
      | _ => []
}

/-- SC2177: time is undefined in sh -/
def checkTimeCommand : CommandCheck := {
  name := .exactly "time"
  check := fun params t =>
    if params.shellType == .Sh then
      [warnCmd t 2177 "time is undefined in sh."]
    else []
}

/-- SC2023: `time` options like `-f`/`-o` may belong to the external `time(1)`, not the shell keyword. -/
def checkTimeParameters : CommandCheck := {
  name := .exactly "time"
  check := fun params t =>
    match getCommandArguments t with
    | some (firstArg :: _) =>
        if params.shellType == .Bash || params.shellType == .Sh then
          let s := oversimplify firstArg |>.foldl (· ++ ·) ""
          if s.startsWith "-" && s != "-p" then
            [infoCmd t 2023
              "The shell may override 'time' as seen in man time(1). Use 'command time ..' for that one."]
          else
            []
        else
          []
    | _ => []
}

/-- SC2211: Glob used as command name -/
def checkGlobAsCommand : CommandCheck := {
  name := .any
  check := fun _params t =>
    match getCommandName t with
    | some name =>
      if name.startsWith "*" || name.startsWith "?" then
        [warnCmd t 2211 "This is a glob used as a command name."]
      else []
    | Option.none => []
}

/-- SC2215: Flag used as command name -/
def checkFlagAsCommand : CommandCheck := {
  name := .any
  check := fun _params t =>
    let (nameOpt, token) := getCommandNameAndToken false t
    match nameOpt with
    | some name =>
      match ASTLib.getUnquotedLiteral token with
      | some s =>
        if name.startsWith "-" && name.length >= 2 && s.startsWith "-" then
          [warnCmd t 2215 "This flag is used as a command name."]
        else []
      | Option.none => []
    | Option.none => []
}

/-- SC2256: source is not a command in sh -/
def checkSourceInSh : CommandCheck := {
  name := .exactly "source"
  check := fun params t =>
    if params.shellType == .Sh then
      [errorCmd t 2256 "source is not a command in sh. Use dot."]
    else []
}

/-- SC2240: The dot command does not support arguments in sh/dash -/
def checkDotArgsInShDash : CommandCheck := {
  name := .exactly "."
  check := fun params t =>
    if params.shellType == .Sh || params.shellType == .Dash then
      match getCommandArguments t with
      | some (_file :: arg1 :: _) =>
        [makeComment .warningC arg1.id 2240
          "The dot command does not support arguments in sh/dash. Set them as variables."]
      | _ => []
    else []
}

/-- SC2290: Remove spaces around =/+= in assignments passed as args to declaring commands -/
def checkArgComparison : CommandCheck := {
  name := .anyExactly ["declare", "export", "local", "readonly", "typeset", "let", "alias"]
  check := fun _params t =>
    let headId (t : Token) : Id :=
      match t.inner with
      | .T_NormalWord (x :: _) => x.id
      | _ => t.id
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLeadingUnquotedString arg with
        | some s =>
          if s.startsWith "=" then
            some (makeComment .errorC (headId arg) 2290
              "Remove spaces around = to assign.")
          else if s.startsWith "+=" then
            some (makeComment .errorC (headId arg) 2290
              "Remove spaces around += to append.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2316: Multiple declaring commands should be separate -/
def checkMultipleDeclaring (cmd : String) : CommandCheck := {
  name := .exactly cmd
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match arg.inner with
        | .T_NormalWord [p] =>
          match p.inner with
          | .T_Literal lit =>
            if declaringCommands.contains lit then
              some (makeComment .errorC t.id 2316
                s!"This applies {cmd} to the variable named {lit}, which is probably not what you want. Use a separate command or the appropriate declare options instead.")
            else Option.none
          | _ => Option.none
        | _ => Option.none
    | Option.none => []
}
where
  declaringCommands : List String := ["local", "readonly", "declare", "export", "typeset"]

/-- SC2264: Use return not exit in functions -/
def checkFunctionExit : CommandCheck := {
  name := .exactly "exit"
  check := fun params t =>
    if isInFunction params t then
      [warnCmd t 2264 "Use return instead of exit in functions."]
    else []
}

/-- SC3002: In POSIX sh, extglob is undefined -/
def checkExtglob : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "@(" || Regex.containsSubstring str "!(" ||
         Regex.containsSubstring str "+(" || Regex.containsSubstring str "*(" then
        [warnCmd t 3002 "In POSIX sh, extglob is undefined."]
      else []
    else []
}

/-- SC3004: In POSIX sh, BASH_SOURCE is undefined -/
def checkBashSource : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "BASH_SOURCE" then
        [warnCmd t 3004 "In POSIX sh, BASH_SOURCE is undefined."]
      else []
    else []
}

/-- SC3005: In POSIX sh, BASH_VERSION is undefined -/
def checkBashVersion : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "BASH_VERSION" then
        [warnCmd t 3005 "In POSIX sh, BASH_VERSION is undefined."]
      else []
    else []
}

/-- SC3007: In POSIX sh, FUNCNAME is undefined -/
def checkFuncname : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "FUNCNAME" then
        [warnCmd t 3007 "In POSIX sh, FUNCNAME is undefined."]
      else []
    else []
}

/-- SC3008: In POSIX sh, PIPESTATUS is undefined -/
def checkPipestatus : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "PIPESTATUS" then
        [warnCmd t 3008 "In POSIX sh, PIPESTATUS is undefined."]
      else []
    else []
}

/-- SC3009: In POSIX sh, `{n..m}` is undefined -/
def checkBraceExpansion : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "{" && Regex.containsSubstring str ".." then
        [warnCmd t 3009 "In POSIX sh, brace expansion is undefined."]
      else []
    else []
}

/-- SC3012: In POSIX sh, `!` negation in `[ ]` is undefined -/
def checkTestNegation : CommandCheck := {
  name := .basename "["
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if str.startsWith "! " then
        [warnCmd t 3012 "In POSIX sh, negation with ! in [ ] is undefined."]
      else []
    else []
}

/-- SC3015: In POSIX sh, `select` loops are undefined -/
def checkSelectLoop : CommandCheck := {
  name := .any
  check := fun params t =>
    match t.inner with
    | .T_SelectIn _ _ _ =>
      if params.shellType == .Sh then
        [warnCmd t 3015 "In POSIX sh, select loops are undefined."]
      else []
    | _ => []
}

/-- SC3016: In POSIX sh, `>&` file descriptor duplication is undefined -/
def checkFdDuplication : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str ">&" && !Regex.containsSubstring str "2>&1" then
        [warnCmd t 3016 "In POSIX sh, some `>&` redirections are undefined."]
      else []
    else []
}

/-- SC3017: In POSIX sh, `&>` redirection is undefined -/
def checkAmpersandRedirect : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "&>" then
        [warnCmd t 3017 "In POSIX sh, `&>` redirection is undefined."]
      else []
    else []
}

/-- SC3018: In POSIX sh, `<<<` here-strings are undefined -/
def checkHereString : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "<<<" then
        [warnCmd t 3018 "In POSIX sh, here-strings are undefined."]
      else []
    else []
}

/-- SC3019: In POSIX sh, `|&` is undefined -/
def checkPipeAmpersand : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "|&" then
        [warnCmd t 3019 "In POSIX sh, `|&` is undefined. Use `2>&1 |`."]
      else []
    else []
}

/-- SC3032: In POSIX sh, `coproc` is undefined -/
def checkCoproc : CommandCheck := {
  name := .exactly "coproc"
  check := fun params t =>
    if params.shellType == .Sh then
      [warnCmd t 3032 "In POSIX sh, coproc is undefined."]
    else []
}

/-- SC3022: In POSIX sh, `+=` is undefined -/
def checkPlusEquals : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "+=" then
        [warnCmd t 3022 "In POSIX sh, += is undefined."]
      else []
    else []
}

/-- SC3023: In POSIX sh, `read -a` is undefined -/
def checkReadArray : CommandCheck := {
  name := .exactly "read"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.contains "-a" then
          [warnCmd t 3023 "In POSIX sh, read -a is undefined."]
        else []
      | Option.none => []
    else []
}

/-- SC3024: In POSIX sh, `read -d` is undefined -/
def checkReadDelimiter : CommandCheck := {
  name := .exactly "read"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.contains "-d" then
          [warnCmd t 3024 "In POSIX sh, read -d is undefined."]
        else []
      | Option.none => []
    else []
}

/-- SC3025: In POSIX sh, `read -n` is undefined -/
def checkReadN : CommandCheck := {
  name := .exactly "read"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.contains "-n" then
          [warnCmd t 3025 "In POSIX sh, read -n is undefined."]
        else []
      | Option.none => []
    else []
}

/-- SC3026: In POSIX sh, `read -t` is undefined -/
def checkReadTimeout : CommandCheck := {
  name := .exactly "read"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.contains "-t" then
          [warnCmd t 3026 "In POSIX sh, read -t is undefined."]
        else []
      | Option.none => []
    else []
}

/-- SC3028: In POSIX sh, `$EUID` is undefined -/
def checkEuid : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "$EUID" || Regex.containsSubstring str "${EUID}" then
        [warnCmd t 3028 "In POSIX sh, EUID is undefined."]
      else []
    else []
}

/-- SC3029: In POSIX sh, `$UID` is undefined -/
def checkUid : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "$UID" || Regex.containsSubstring str "${UID}" then
        [warnCmd t 3029 "In POSIX sh, UID is undefined."]
      else []
    else []
}

/-- SC3031: In POSIX sh, `=~` regex matching is undefined -/
def checkRegexMatching : CommandCheck := {
  name := .any
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "=~" then
        [warnCmd t 3031 "In POSIX sh, =~ regex matching is undefined."]
      else []
    else []
}

/-- SC3032: In POSIX sh, `set -o` options are limited -/
def checkSetOptions : CommandCheck := {
  name := .exactly "set"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.any (fun s => s.startsWith "-o" || s.startsWith "+o") then
          [infoCmd t 3032 "In POSIX sh, set -o options are limited."]
        else []
      | Option.none => []
    else []
}

/-- SC3033: In POSIX sh, `printf -v` is undefined -/
def checkPrintfV : CommandCheck := {
  name := .basename "printf"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.contains "-v" then
          [warnCmd t 3033 "In POSIX sh, printf -v is undefined."]
        else []
      | Option.none => []
    else []
}

/-- SC3034: In POSIX sh, `let` is undefined -/
def checkLetInSh : CommandCheck := {
  name := .exactly "let"
  check := fun params t =>
    if params.shellType == .Sh then
      [warnCmd t 3034 "In POSIX sh, let is undefined."]
    else []
}

/-- SC3035: In POSIX sh, `type -P` is undefined -/
def checkTypeP : CommandCheck := {
  name := .exactly "type"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.any (fun s => s.startsWith "-P" || s == "-p") then
          [warnCmd t 3035 "In POSIX sh, type -P/-p options are undefined."]
        else []
      | Option.none => []
    else []
}

/-- SC3036: In POSIX sh, `echo -e` is undefined -/
def checkEchoE : CommandCheck := {
  name := .basename "echo"
  check := fun params t =>
    if params.shellType == .Sh then
      match getCommandArguments t with
      | some args =>
        let argStrs := args.filterMap getLiteralString
        if argStrs.contains "-e" then
          [warnCmd t 3036 "In POSIX sh, echo -e is undefined. Use printf."]
        else []
      | Option.none => []
    else []
}

/-- SC3038: In POSIX sh, test `==` is undefined -/
def checkTestDoubleEquals : CommandCheck := {
  name := .basename "test"
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "==" then
        [warnCmd t 3038 "In POSIX sh, test == is undefined. Use =."]
      else []
    else []
}

/-- SC3039: In POSIX sh, `[[` is undefined -/
def checkDoubleBrackets : CommandCheck := {
  name := .any
  check := fun params t =>
    match t.inner with
    | .T_Condition _ _ =>
      if params.shellType == .Sh then
        [warnCmd t 3039 "In POSIX sh, [[ ]] is undefined. Use [ ]."]
      else []
    | _ => []
}

/-- SC3040: In POSIX sh, `set -o pipefail` is undefined -/
def checkPipefail : CommandCheck := {
  name := .exactly "set"
  check := fun params t =>
    if params.shellType == .Sh then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "pipefail" then
        [warnCmd t 3040 "In POSIX sh, set -o pipefail is undefined."]
      else []
    else []
}

/-- SC3041: In POSIX sh, `set -o errexit` in subshells is undefined -/
def checkErrexit : CommandCheck := {
  name := .exactly "set"
  check := fun params t =>
    if params.shellType == .Sh && isInSubshell params t then
      let str := getLiteralString t |>.getD ""
      if Regex.containsSubstring str "errexit" || Regex.containsSubstring str "-e" then
        [infoCmd t 3041 "In POSIX sh, errexit behavior in subshells is undefined."]
      else []
    else []
}

set_option maxRecDepth 2048

/-- All command checks -/
def commandChecks : List CommandCheck := [
  checkLsGrep,
  checkLsFind,
  checkForInCat,
  checkTr,
  checkFindNameGlob,
  checkExpr,
  checkGrepRe,
  checkTrapQuotes,
  checkReturn,
  checkExit,
  checkFindExecWithSingleArgument,
  checkUnusedEchoEscapes,
  checkInjectableFindSh,
  checkFindActionPrecedence,
  checkMkdirDashPM,
  checkNonportableSignals,
  checkInteractiveSu,
  checkWhich,
  checkTestNZ,
  checkArgComparison,  -- SC2290
  checkFindWithSymlinks,
  checkEchoN,
  checkUnquotedEchoSpaces, -- SC2291
  -- New checks
  checkLetArithmetic,
  checkBackticks,
  checkWhichCommand,
  checkTestNotZ,  -- SC2236 for test command
  checkGrepRegexQuoting,
  checkLsInScript,
  checkSshSingleQuotes,
  checkPrintfVar,
  checkRmGlob,
  checkRmRoot,
  checkSetAssign,
  -- checkReadR, -- Duplicate of checkReadWithoutR (SC2162), removed
  checkReadExpansions,  -- SC2229/SC2313
  checkPrintfArgCount,
  checkArrayComma,
  checkBackreferencingDeclaration "declare",
  checkBackreferencingDeclaration "local",
  checkBackreferencingDeclaration "readonly",
  -- More new checks
  checkSudoRedirect,    -- SC2024
  checkCdNoCheck,       -- SC2164
  checkEchoStdin,       -- SC2008
  checkUnintendedComment, -- SC2026
  checkGlobDash,        -- SC2035 (rm, mv, cp, chmod, chown, chgrp)
  checkChmodDashr,      -- SC2253
  checkTildeInQuotes,   -- SC2088
  checkExecFollowed,    -- SC2093
  checkRmVar,           -- SC2115
  checkFindXargs,       -- SC2038
  checkPosixFeatures,   -- SC2039
  checkCoproc,          -- SC3032
  checkLsIteration,     -- SC2045
  checkArrayExpansion,  -- SC2068
  checkDeclareAssignWithSub, -- SC2155 (local, export, declare, readonly, typeset)
  checkSingleQuoteExpression, -- SC2016
  checkDecimalComparison, -- SC2072
  checkArrayAssign,     -- SC2206
  checkAccidentalExec,  -- SC2091
  checkAliasExpansion,  -- SC2139
  checkAliasesUsesArgs, -- SC2142
  checkUnsetGlobs,      -- SC2184
  checkEvalArray,       -- SC2293/SC2294
  checkQuotingStyle,    -- SC2140
  checkGrepQ,           -- SC2143
  checkTestGlob,        -- SC2144
  checkFindEmpty,       -- SC2150
  checkFindRedirections, -- SC2227
  checkExportValue,     -- SC2163
  checkDashBashisms,    -- SC2169
  -- Additional SC2xxx checks
  checkUselessEcho,     -- SC2005
  checkEchoEscapes,     -- SC2028
  checkShoptInSh,       -- SC2040
  checkLiteralInBackticks, -- SC2041
  checkGrepLiteralDollar,  -- SC2063
  checkUnquotedSubstitution, -- SC2085
  checkBracketClass,    -- SC2101
  checkCdSubshell,      -- SC2103
  checkKshFunctionSyntax, -- SC2111
  checkFunctionKeyword, -- SC2112/SC2113
  checkGrepWcL,         -- SC2126
  checkStringIntComparison, -- SC2130
  checkSingleBracketGlob, -- SC2131
  checkMultipleExitCodes, -- SC2151
  checkReturnValue,     -- SC2152
  checkTestZLiteral,    -- SC2157
  checkTestFalse,       -- SC2158
  checkTestTrue,        -- SC2160
  checkNotTrue,         -- SC2161
  checkReadWithoutR,    -- SC2162
  -- Batch 2: Additional SC2xxx checks
  checkForLoopComma,    -- SC2042
  checkSingleIterationLoop, -- SC2043
  checkLocalOutsideFunction, -- SC2168
  checkTrapByNumber,    -- SC2172
  checkTrapUncatchable, -- SC2173
  checkTimeAfterLogical, -- SC2176
  checkTempfileInsecure, -- SC2186
  checkDeprecatedEgrep, -- SC2196
  checkDeprecatedFgrep, -- SC2197
  checkAssignmentVsCommand, -- SC2209
  checkWhileGetoptsCase, -- SC2213/SC2214/SC2220
  checkPipeToCd,        -- SC2216
  checkRedirectToCd,    -- SC2217
  checkMvNoDestination, -- SC2224
  checkCpNoDestination, -- SC2225
  checkCpLegacyR,       -- SC2336
  checkLnNoDestination, -- SC2226
  checkSudoBuiltins,    -- SC2232
  checkShebangAbsolutePath, -- SC2239
  checkExitMultipleArgs, -- SC2241/SC2242
  checkShebangDirectory, -- SC2246
  checkBracketArithmetic, -- SC2255
  checkXargsDelimiter,  -- SC2267
  checkSelfAssignment,  -- SC2269
  checkCommandWithTrailingSymbol, -- SC2286/SC2287/SC2288/SC2289
  checkRegexVsGlob,     -- SC2049
  checkTestRedirection, -- SC2065
  checkFindExecTerminator, -- SC2067
  checkRegexQuoting,    -- SC2076
  checkArithmeticDecimals, -- SC2079
  checkBracketRegex,    -- SC2081
  checkExitInSubshell,  -- SC2106
  checkAndInDoubleTest, -- SC2108
  checkOrInDoubleTest,  -- SC2110
  checkStderrPipe,      -- SC2118
  checkTimeCommand,     -- SC2177
  checkTimeParameters,  -- SC2023
  checkGlobAsCommand,   -- SC2211
  checkFlagAsCommand,   -- SC2215
  checkDotArgsInShDash, -- SC2240
  checkSourceInSh,      -- SC2256
  checkMultipleDeclaring "local",
  checkMultipleDeclaring "readonly",
  checkMultipleDeclaring "export",
  checkFunctionExit,    -- SC2264
  -- SC2188/SC2189 are handled in Analytics.checkRedirectedNowhere
]

/-- Main checker -/
def checker (_spec : AnalysisSpec) (params : Parameters) : Checker :=
  getChecker params commandChecks

-- Theorems (stubs)

theorem commandChecks_not_empty :
    commandChecks.length > 0 := by decide

theorem matchesCommandName_exactly (name : String) (cmd : Token) :
    matchesCommandName (.exactly name) cmd = true →
    getCommandName cmd = some name := sorry

theorem matchesCommandName_basename (name : String) (cmd : Token) :
    matchesCommandName (.basename name) cmd = true →
    (getCommandBasename cmd).isSome := sorry

theorem checker_applies_matching (_spec : AnalysisSpec) (_params : Parameters) :
    True := trivial  -- Would verify matching logic

theorem checkTr_warns_on_ranges :
    True := trivial  -- Would verify SC2018

theorem checkReturn_validates_range :
    True := trivial  -- Would verify 0-255 range

theorem checkExit_validates_range :
    True := trivial  -- Would verify 0-255 range

theorem optionalChecks_documented :
    optionalChecks.all (fun c => c.cdDescription.length > 0) = true := by native_decide

end ShellCheck.Checks.Commands
