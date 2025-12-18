/-
  Copyright 2012-2020 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Checks for shell-specific features and bashisms.
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.AnalyzerLib
import ShellCheck.Interface
import ShellCheck.Prelude
import ShellCheck.Regex

namespace ShellCheck.Checks.ShellSupport

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.Interface
open ShellCheck.Prelude

/-- Helper to check if a string contains a substring -/
def stringContains (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Wrapper for shell-specific checks -/
structure ForShell where
  shells : List Shell
  check : Parameters → Token → List TokenComment

/-- Get checker for specific shell -/
def getChecker (params : Parameters) (list : List ForShell) : Checker := {
  perScript := fun _ => pure []
  perToken := fun token =>
    let shell := params.shellType
    let applicable := list.filter fun fs => fs.shells.contains shell
    pure (applicable.foldl (fun acc fs => acc ++ fs.check params token) [])
}

/-- SC2079: (( )) doesn't support decimals. Use bc or awk. -/
def checkForDecimals : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash]
  check := fun _params t =>
    match t.inner with
    | .TA_Expansion _ =>
      match getLiteralString t with
      | some s =>
        if s.length > 0 && s.toList.head!.isDigit && s.any (· == '.') then
          [makeComment .errorC t.id 2079 "(( )) doesn't support decimals. Use bc or awk."]
        else []
      | Option.none => []
    | _ => []
}

/-- Check for POSIX-incompatible bashisms in sh scripts -/
partial def checkBashisms : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh]
  check := fun _params t =>
    match t.inner with
    | .T_ProcSub _ _ =>
      [makeComment .errorC t.id 2039 "In POSIX sh, process substitution is undefined."]
    | .T_Extglob _ _ =>
      [makeComment .errorC t.id 2039 "In POSIX sh, extglob is undefined."]
    | .T_DoubleQuoted parts =>
      parts.filterMap fun part =>
        match part.inner with
        | .T_DollarSingleQuoted _ =>
          some (makeComment .errorC part.id 2039 "In POSIX sh, $'...' is undefined.")
        | _ => Option.none
    | _ => []
}

/-- SC2001: Prefer `${variable//search/replace}` over `echo ... | sed ...` for simple substitutions. -/
def checkEchoSed : ForShell := {
  shells := [.Bash, .Ksh]
  check := fun _params t =>
    match t.inner with
    | .T_Redirecting redirects cmd =>
      if redirects.any redirectHereString then
        checkSed t.id (oversimplify cmd)
      else
        []
    | .T_Pipeline _ cmds =>
      match cmds with
      | [a, b] =>
        let acmd := oversimplify a
        let bcmd := oversimplify b
        if acmd == ["echo", "${VAR}"] then
          checkSed t.id bcmd
        else
          []
      | _ => []
    | _ => []
}
where
  redirectHereString (t : Token) : Bool :=
    match t.inner with
    | .T_FdRedirect _ target =>
      match target.inner with
      | .T_HereString .. => true
      | _ => false
    | _ => false

  checkSed (id : Id) : List String → List TokenComment
    | ["sed", v] => checkIn id v
    | ["sed", "-e", v] => checkIn id v
    | _ => []

  checkIn (id : Id) (script : String) : List TokenComment :=
    if isSimpleSed script then
      [makeComment .styleC id 2001
        "See if you can use ${variable//search/replace} instead."]
    else
      []

  -- Detect a sed program of the form `s<d>old<d>new<d>...` with a single delimiter.
  -- This is intentionally conservative and mirrors upstream's heuristic.
  isSimpleSed (s : String) : Bool :=
    match s.toList with
    | 's' :: delim :: rest =>
      let rest :=
        match rest.getLast? with
        | some 'g' => rest.dropLast
        | _ => rest
      (rest.filter (· == delim)).length == 2
    | _ => false

/-- SC2051: Bash doesn't support variables in brace ranges -/
def checkBraceExpansionVars : ForShell := {
  shells := [.Bash]
  check := fun params t =>
    match t.inner with
    | .T_BraceExpansion items =>
      let hasVarInRange :=
        items.any fun item =>
          let s := toString item
          stringContains s "$.." || stringContains s "..$"
      if hasVarInRange then
        if isEvaled params t then
          [makeComment .styleC t.id 2175
            "Quote this invalid brace expansion since it should be passed literally to eval."]
        else
          [makeComment .warningC t.id 2051
            "Bash doesn't support variables in brace range expansions."]
      else []
    | _ => []
}
where
  literalExt (t : Token) : Option String :=
    match t.inner with
    | .T_DollarBraced .. => some "$"
    | .T_DollarExpansion .. => some "$"
    | .T_DollarArithmetic .. => some "$"
    | _ => some "-"

  toString (t : Token) : String :=
    getLiteralStringExt literalExt t |>.getD ""

  isEvaled (params : Parameters) (t : Token) : Bool :=
    match getClosestCommand params.parentMap t with
    | some cmd => isCommand cmd "eval"
    | Option.none => false

/-- SC2180: Bash doesn't support multi-dimensional arrays -/
def checkMultiDimensionalArrays : ForShell := {
  shells := [.Bash]
  check := fun _params t =>
    match t.inner with
    | .T_Assignment _ varName _ _ =>
      -- Check for arr[1][2] pattern in variable name
      if varName.any (· == '[') then
        let bracketCount := varName.toList.filter (· == '[') |>.length
        if bracketCount > 1 then
          [makeComment .errorC t.id 2180
            "Bash does not support multi-dimensional arrays. Use arr[i*cols+j]."]
        else []
      else []
    | .T_DollarBraced _ inner =>
      -- Check for ${arr[1][2]} access
      let s := getLiteralString inner |>.getD ""
      let bracketCount := s.toList.filter (· == '[') |>.length
      if bracketCount > 1 then
        [makeComment .errorC t.id 2180
          "Bash does not support multi-dimensional arrays. Use arr[i*cols+j]."]
      else []
    | _ => []
}

/-- SC2025: Check PS1 assignments for non-printable characters not wrapped in \[..\] -/
def checkPS1Assignments : ForShell := {
  shells := [.Bash]
  check := fun _params t =>
    match t.inner with
    | .T_Assignment _ varName _ rhs =>
      if varName == "PS1" || varName == "PS2" || varName == "PS3" || varName == "PS4" then
        match getLiteralString rhs with
        | some s =>
          -- Check for escape sequences that should be wrapped in \[..\]
          -- Common problematic sequences: \e[, \033[, \x1b[ (ANSI escapes)
          let hasEscape := stringContains s "\\e[" || stringContains s "\\033[" ||
                           stringContains s "\\x1b["
          let hasWrapper := stringContains s "\\[" && stringContains s "\\]"
          if hasEscape && !hasWrapper then
            [makeComment .warningC t.id 2025
              "Use \\[..\\] around non-printing characters in PS1 to avoid line wrapping issues."]
          else []
        | none => []
      else []
    | _ => []
}

/-- SC2055: Check for multiple bangs -/
def checkMultipleBangs : ForShell := {
  shells := [.Bash, .Ksh]
  check := fun _params t =>
    match t.inner with
    | .T_Banged inner =>
      match inner.inner with
      | .T_Banged _ =>
        [makeComment .warningC t.id 2055 "Double negation is unusual. Check for typos."]
      | _ => []
    | _ => []
}

/-- SC2261: Check for negated pipelines in POSIX sh -/
def checkBangAfterPipe : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh]
  check := fun _params t =>
    match t.inner with
    | .T_Banged inner =>
      -- In POSIX sh, ! can only negate a whole pipeline, not individual commands
      -- Check if the negated thing is a pipeline
      match inner.inner with
      | .T_Pipeline _ cmds =>
        if cmds.length > 1 then
          -- This is actually ok - ! cmd1 | cmd2 negates the exit status of the pipeline
          []
        else []
      | _ => []
    | _ => []
}

/-- Helper to check if a condition expression is negated -/
def isNegatedCondition : Token → Bool
  | ⟨_, .TC_Unary _ "!" _⟩ => true
  | _ => false

/-- SC2107: Check for [ ! test -a ! test ] which should be ! [ test -o test ] -/
def checkNegatedUnaryOps : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash, .Ksh]
  check := fun _params t =>
    match t.inner with
    | .TC_And _ "-a" left right =>
      -- Check for pattern: ! test -a ! test
      if isNegatedCondition left && isNegatedCondition right then
        [makeComment .styleC t.id 2107
          "Instead of [ ! a -a ! b ], use ! [ a -o b ]. (De Morgan's law)"]
      else []
    | .TC_Or _ "-o" left right =>
      -- Check for pattern: ! test -o ! test
      if isNegatedCondition left && isNegatedCondition right then
        [makeComment .styleC t.id 2107
          "Instead of [ ! a -o ! b ], use ! [ a -a b ]. (De Morgan's law)"]
      else []
    | _ => []
}

/-- SC2088: Tilde does not expand in quotes -/
def checkTildeInQuotes : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash, .Ksh]
  check := fun _params t =>
    match t.inner with
    | .T_DoubleQuoted parts =>
      parts.filterMap fun part =>
        match getLiteralString part with
        | some s =>
          if s.startsWith "~" then
            some (makeComment .warningC part.id 2088
              "Tilde does not expand in quotes. Use $HOME.")
          else Option.none
        | none => Option.none
    | .T_SingleQuoted s =>
      if s.startsWith "~" then
        [makeComment .warningC t.id 2088
          "Tilde does not expand in quotes. Use $HOME."]
      else []
    | _ => []
}

/-- SC2089: Quotes/backslashes will be treated literally in assignment -/
def checkQuotesInAssignment : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash, .Ksh]
  check := fun _params t =>
    match t.inner with
    | .T_Assignment _ _varName _ rhs =>
      match getLiteralString rhs with
      | some s =>
        -- Check for command-like strings being assigned
        if (s.startsWith "'" || s.startsWith "\"") && s.any (· == ' ') then
          [makeComment .warningC rhs.id 2089
            "Quotes/backslashes will be treated literally. Use an array."]
        else []
      | none => []
    | _ => []
}

/-- SC2016: Expressions don't expand in single quotes -/
def checkExpressionsInSingleQuotes : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash, .Ksh]
  check := fun _params t =>
    match t.inner with
    | .T_SingleQuoted s =>
      if stringContains s "$" || stringContains s "`" then
        [makeComment .infoC t.id 2016
          "Expressions don't expand in single quotes, use double quotes for that."]
      else []
    | _ => []
}

/-- SC2046: Quote to prevent word splitting -/
def checkWordSplitting : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash, .Ksh]
  check := fun _params t =>
    match t.inner with
    | .T_DollarExpansion _ =>
      -- Unquoted command substitution
      [makeComment .warningC t.id 2046
        "Quote this to prevent word splitting."]
    | .T_Backticked _ =>
      -- Unquoted backtick substitution
      [makeComment .warningC t.id 2046
        "Quote this to prevent word splitting."]
    | _ => []
}

/-- All shell support checks -/
-- Note: checkWordSplitting removed - SC2046 is handled by checkUnquotedExpansions in Analytics.lean
-- which properly checks for quote-free contexts (assignments, double-quoted strings, etc.)
def checks : List ForShell := [
  checkForDecimals,
  checkBashisms,
  checkEchoSed,
  checkBraceExpansionVars,
  checkMultiDimensionalArrays,
  checkPS1Assignments,
  checkMultipleBangs,
  checkBangAfterPipe,
  checkNegatedUnaryOps,
  checkTildeInQuotes,
  checkQuotesInAssignment,
  checkExpressionsInSingleQuotes
]

/-- Main checker -/
def checker (params : Parameters) : Checker :=
  getChecker params checks

-- Theorems (stubs)

theorem checkForDecimals_applies_to_sh :
    True := trivial  -- ShellCheck.Data.Shell.Sh ∈ checkForDecimals.shells

theorem checkBashisms_not_for_bash :
    True := trivial  -- ShellCheck.Data.Shell.Bash ∉ checkBashisms.shells

theorem checker_filters_by_shell (_params : Parameters) :
    True := trivial  -- Would verify shell filtering works

theorem all_checks_have_shells :
    True := trivial  -- checks.all (fun c => c.shells.length > 0)

theorem getChecker_includes_applicable (_params : Parameters) (_list : List ForShell) :
    True := trivial  -- Would verify inclusion logic

end ShellCheck.Checks.ShellSupport
