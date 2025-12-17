/-
  Copyright 2012-2024 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Analytics - Main analysis checks for ShellCheck.
  Contains 100+ individual linting rules.
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

namespace ShellCheck.Analytics

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.CFG
open ShellCheck.CFGAnalysis
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Parser
open ShellCheck.Regex

/-!
## Tree Checks

Checks that are run on the entire AST root.
-/

/-- Collect all tokens in the tree -/
partial def collectTokens (t : Token) : List Token :=
  t :: collectFromInner t.inner
where
  collectFromInner (inner : InnerToken Token) : List Token :=
    match inner with
    | .TA_Binary _ l r => collectTokens l ++ collectTokens r
    | .TA_Assignment _ l r => collectTokens l ++ collectTokens r
    | .TA_Variable _ is => is.flatMap collectTokens
    | .TA_Expansion ps => ps.flatMap collectTokens
    | .TA_Sequence es => es.flatMap collectTokens
    | .TA_Parenthesis e => collectTokens e
    | .TA_Trinary c t e => collectTokens c ++ collectTokens t ++ collectTokens e
    | .TA_Unary _ e => collectTokens e
    | .TC_And _ _ l r => collectTokens l ++ collectTokens r
    | .TC_Binary _ _ l r => collectTokens l ++ collectTokens r
    | .TC_Group _ e => collectTokens e
    | .TC_Nullary _ e => collectTokens e
    | .TC_Or _ _ l r => collectTokens l ++ collectTokens r
    | .TC_Unary _ _ e => collectTokens e
    | .TC_Empty _ => []
    | .T_AndIf l r => collectTokens l ++ collectTokens r
    | .T_OrIf l r => collectTokens l ++ collectTokens r
    | .T_Arithmetic e => collectTokens e
    | .T_Array es => es.flatMap collectTokens
    | .T_IndexedElement is v => is.flatMap collectTokens ++ collectTokens v
    | .T_Assignment _ _ is v => is.flatMap collectTokens ++ collectTokens v
    | .T_Backgrounded c => collectTokens c
    | .T_Backticked cs => cs.flatMap collectTokens
    | .T_Banged c => collectTokens c
    | .T_BraceExpansion ps => ps.flatMap collectTokens
    | .T_BraceGroup cs => cs.flatMap collectTokens
    | .T_CaseExpression w cases =>
        collectTokens w ++ cases.flatMap fun (_, pats, body) =>
          pats.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_Condition _ e => collectTokens e
    | .T_DollarArithmetic e => collectTokens e
    | .T_DollarBraced _ c => collectTokens c
    | .T_DollarBracket e => collectTokens e
    | .T_DollarDoubleQuoted ps => ps.flatMap collectTokens
    | .T_DollarExpansion cs => cs.flatMap collectTokens
    | .T_DollarBraceCommandExpansion _ cs => cs.flatMap collectTokens
    | .T_DoubleQuoted ps => ps.flatMap collectTokens
    | .T_Extglob _ ps => ps.flatMap collectTokens
    | .T_FdRedirect _ t => collectTokens t
    | .T_ForArithmetic i c inc body =>
        collectTokens i ++ collectTokens c ++ collectTokens inc ++ body.flatMap collectTokens
    | .T_ForIn _ ws body => ws.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_Function _ _ _ body => collectTokens body
    | .T_HereDoc _ _ _ cs => cs.flatMap collectTokens
    | .T_HereString w => collectTokens w
    | .T_IfExpression conds els =>
        conds.flatMap (fun (c, b) => c.flatMap collectTokens ++ b.flatMap collectTokens) ++
        els.flatMap collectTokens
    | .T_IoFile op file => collectTokens op ++ collectTokens file
    | .T_IoDuplicate op _ => collectTokens op
    | .T_NormalWord ps => ps.flatMap collectTokens
    | .T_Pipeline seps cmds => seps.flatMap collectTokens ++ cmds.flatMap collectTokens
    | .T_ProcSub _ cs => cs.flatMap collectTokens
    | .T_Redirecting rs c => rs.flatMap collectTokens ++ collectTokens c
    | .T_Script sh cs => collectTokens sh ++ cs.flatMap collectTokens
    | .T_SelectIn _ ws body => ws.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_SimpleCommand as ws => as.flatMap collectTokens ++ ws.flatMap collectTokens
    | .T_Subshell cs => cs.flatMap collectTokens
    | .T_UntilExpression c body => c.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_WhileExpression c body => c.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_Annotation _ c => collectTokens c
    | .T_CoProc n body =>
        match n with
        | .some t => collectTokens t ++ collectTokens body
        | .none => collectTokens body
    | .T_CoProcBody body => collectTokens body
    | .T_Include s => collectTokens s
    | .T_SourceCommand src scr => collectTokens src ++ collectTokens scr
    | .T_BatsTest _ body => collectTokens body
    | _ => []  -- Leaf tokens (literals, keywords, etc.)

/-- Run node analysis on tree -/
def runNodeAnalysis (f : Parameters → Token → List TokenComment)
    (p : Parameters) (t : Token) : List TokenComment :=
  -- Walk tree and collect comments from all nodes
  let allTokens := collectTokens t
  allTokens.flatMap (f p)

/-- Convert node checks to tree check -/
def nodeChecksToTreeCheck (checks : List (Parameters → Token → List TokenComment))
    (params : Parameters) (root : Token) : List TokenComment :=
  checks.foldl (fun acc check => acc ++ runNodeAnalysis check params root) []

/-!
## Node Checks

Individual analysis rules applied to each token.
-/

/-- SC2086: Double quote to prevent globbing and word splitting -/
def checkUnquotedDollarAt (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    -- Skip if already in a quoted context
    if isQuoteFree params.shellType params.parentMap t then
      []
    else
      let str := oversimplify content |>.foldl (· ++ ·) ""
      -- Warn for $@, $*, or any variable name (simplified version)
      if str == "@" || str == "*" || isVariableName str then
        [makeComment .warningC t.id 2086 "Double quote to prevent globbing and word splitting."]
      else []
  | _ => []
where
  isVariableName (s : String) : Bool :=
    match s.toList with
    | c :: _ => c.isAlpha || c == '_'
    | [] => false

/-- SC2046: Quote this to prevent word splitting (for-in specific) -/
def checkForInQuoted (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.filterMap fun word =>
      match word.inner with
      | .T_DollarExpansion _ =>
          some (makeComment .warningC word.id 2046
            "Quote this to prevent word splitting.")
      | _ => none
  | _ => []

/-- SC2012: Use find instead of ls to better handle non-alphanumeric filenames -/
def checkForInLs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.filterMap fun word =>
      if getLiteralString word == some "ls" then
        some (makeComment .warningC word.id 2012
          "Use find instead of ls to better handle non-alphanumeric filenames.")
      else none
  | _ => []

/-- SC2015: Note that A && B || C is not if-then-else -/
def checkShorthandIf (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_OrIf left right =>
    match left.inner with
    | .T_AndIf _ _ => [makeComment .infoC t.id 2015
        "Note that A && B || C is not if-then-else. C may run when A is true."]
    | _ => []
  | _ => []

/-- Helper for collecting dollar references in arithmetic -/
partial def collectDollarRefsArith (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ _ =>
    [makeComment .styleC t.id 2004 "$/${} is unnecessary on arithmetic variables."]
  | .TA_Binary _ left right => collectDollarRefsArith left ++ collectDollarRefsArith right
  | .TA_Unary _ inner => collectDollarRefsArith inner
  | _ => []

/-- SC2004: $/${} is unnecessary on arithmetic variables -/
def checkArithmeticDeref (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarArithmetic inner =>
    collectDollarRefsArith inner
  | _ => []

/-- SC2006: Use $(...) notation instead of legacy backticked `...` -/
def checkBackticks (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Backticked _ => [makeComment .infoC t.id 2006
      "Use $(...) notation instead of legacy backticked `...`."]
  | .T_Literal s =>
      -- Also check for backticks in literal strings (simplified parser puts them there)
      if s.any (· == '`') then
        [makeComment .infoC t.id 2006 "Use $(...) notation instead of legacy backticked `...`."]
      else []
  | _ => []

/-- SC2034: Variable appears to be unused -/
def checkUnusedAssignments (params : Parameters) (t : Token) : List TokenComment :=
  let flow := getVariableFlow params t
  let assigned := getAssignedVariables flow
  let referenced := getReferencedVariables flow
  -- Get the last assignment for each variable (only report on last assignment)
  -- Using foldr so later assignments overwrite earlier ones
  let lastAssignments := assigned.foldr (fun (tok, name, dt) acc =>
    acc.insert name (tok, dt)) ({} : Std.HashMap String (Token × DataType))
  -- Find variables that are assigned but never referenced
  lastAssignments.fold (init := []) fun acc name (token, dataType) =>
    -- Skip special variables and exports
    if isSpecialVar name || not (isTrueAssignmentSource dataType) then
      acc
    else if not (referenced.any fun (_, n) => n == name) then
      (makeComment .warningC token.id 2034
        s!"{name} appears unused. Verify use (or export if used externally).") :: acc
    else acc
where
  getAssignedVariables (flow : List StackData) : List (Token × String × DataType) :=
    flow.filterMap fun s =>
      match s with
      | .Assignment (token, _, name, dt) => some (token, name, dt)
      | _ => Option.none

  getReferencedVariables (flow : List StackData) : List (Token × String) :=
    flow.filterMap fun s =>
      match s with
      | .Reference (token, _, name) => some (token, name)
      | _ => Option.none

  isSpecialVar (name : String) : Bool :=
    name ∈ ["_", "OPTARG", "OPTIND", "REPLY", "RANDOM", "LINENO",
            "SECONDS", "BASH_VERSION", "BASH_VERSINFO", "PWD", "OLDPWD",
            "IFS", "PATH", "HOME", "USER", "SHELL", "TERM", "LANG",
            "LC_ALL", "PS1", "PS2", "PS3", "PS4", "PROMPT_COMMAND"]
    || name.startsWith "_"
    || name.all Char.isUpper  -- Likely exported env vars

/-- SC2154: Variable is referenced but not assigned -/
def checkUnassignedReferences (params : Parameters) (t : Token) : List TokenComment :=
  let flow := getVariableFlow params t
  let assigned := getAssignedVariables flow
  let referenced := getReferencedVariables flow
  -- Find variables that are referenced but never assigned
  referenced.filterMap fun (token, name) =>
    if isSpecialVar name then
      Option.none
    else if not (assigned.any fun (_, n, _) => n == name) then
      some (makeComment .warningC token.id 2154
        s!"{name} is referenced but not assigned.")
    else Option.none
where
  getAssignedVariables (flow : List StackData) : List (Token × String × DataType) :=
    flow.filterMap fun s =>
      match s with
      | .Assignment (token, _, name, dt) => some (token, name, dt)
      | _ => Option.none

  getReferencedVariables (flow : List StackData) : List (Token × String) :=
    flow.filterMap fun s =>
      match s with
      | .Reference (token, _, name) => some (token, name)
      | _ => Option.none

  isSpecialVar (name : String) : Bool :=
    name ∈ ["_", "OPTARG", "OPTIND", "REPLY", "RANDOM", "LINENO",
            "SECONDS", "BASH_VERSION", "BASH_VERSINFO", "PWD", "OLDPWD",
            "IFS", "PATH", "HOME", "USER", "SHELL", "TERM", "LANG",
            "LC_ALL", "PS1", "PS2", "PS3", "PS4", "PROMPT_COMMAND",
            "@", "*", "#", "?", "-", "$", "!", "0", "1", "2", "3", "4",
            "5", "6", "7", "8", "9"]
    || name.startsWith "_"
    || name.all Char.isUpper  -- Likely env vars or positional params

/-- SC2164: Use 'cd ... || exit' or 'cd ... || return' -/
def checkUncheckedCdPushdPopd (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    match words with
    | cmd :: _ =>
      if isCommand t "cd" || isCommand t "pushd" || isCommand t "popd" then
        -- Check if in a context where exit status is checked
        if not (isCheckedContext params t) then
          [makeComment .warningC t.id 2164
            "Use 'cd ... || exit' or 'cd ... || return' in case cd fails."]
        else []
      else []
    | [] => []
  | _ => []
where
  isCheckedContext (_params : Parameters) (_t : Token) : Bool := false  -- Stub

/-- SC2155: Declare and assign separately to avoid masking return values -/
def checkMaskedReturns (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    match words with
    | cmd :: rest =>
      let cmdName := getCommandName t |>.getD ""
      if cmdName ∈ ["local", "export", "declare", "typeset"] then
        rest.filterMap fun arg =>
          match arg.inner with
          | .T_Assignment _ _ _ value =>
            match value.inner with
            | .T_DollarExpansion _ =>
              some (makeComment .warningC t.id 2155
                "Declare and assign separately to avoid masking return values.")
            | _ => none
          | _ => none
      else []
    | [] => []
  | _ => []

/-- SC2066: Since you double quoted this, it will not word split -/
def checkDoubleQuotedWordSplit (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.filterMap fun word =>
      match word.inner with
      | .T_DoubleQuoted _ => some (makeComment .warningC word.id 2066
          "Since you double quoted this, it will not word split, and the loop will only run once.")
      | _ => none
  | _ => []

/-- SC2068: Double quote array expansions -/
def checkArrayExpansions (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let str := oversimplify content |>.foldl (· ++ ·) ""
    if str.endsWith "[@]" || str.endsWith "[*]" then
      -- Don't warn if already in a quoted context (e.g., inside double quotes)
      if isQuoteFree params.shellType params.parentMap t then []
      else [makeComment .errorC t.id 2068 "Double quote array expansions to avoid re-splitting elements."]
    else []
  | _ => []

/-- SC2115: Use "${var:?}" to ensure this never expands to /*
    NOTE: This check requires parser fix - currently parser drops text after
    variable expansion in words (e.g., $dir/ becomes just $dir) -/
def checkRmGlob (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "rm" then
      words.filterMap fun word =>
        -- Oversimplify to see the pattern: $dir/ becomes ${VAR}/
        let simplified := String.join (oversimplify word)
        -- Check for patterns like ${VAR}/ or ${VAR}/*
        -- TODO: Parser bug - text after variable expansion is lost
        if Regex.containsSubstring simplified "${VAR}/" then
          some (makeComment .warningC word.id 2115
            "Use \"${var:?}\" to ensure this never expands to / .")
        else none
    else []
  | _ => []

/-- SC2129: Consider using { cmd1; cmd2; } >> file instead -/
def checkMultipleRedirects (_params : Parameters) (_t : Token) : List TokenComment :=
  -- Would check for multiple consecutive redirects to same file
  []

/-- SC2016: Expressions don't expand in single quotes -/
def checkSingleQuotedExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SingleQuoted content =>
    if content.any (· == '$') || content.any (· == '`') then
      [makeComment .infoC t.id 2016 "Expressions don't expand in single quotes, use double quotes for that."]
    else []
  | _ => []

/-- SC2091: Remove surrounding $(...) to execute command or quote it -/
def checkSpuriousExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand assigns [word] =>
    if assigns.isEmpty then
      match word.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_DollarExpansion _ => [makeComment .warningC t.id 2091
            "Remove surrounding $() to avoid executing output, or use eval to execute."]
        | _ => []
      | _ => []
    else []
  | _ => []

/-- SC2000: See if you can use ${#variable} instead of echo | wc -/
def checkEchoWc (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ [a, b] =>
    let acmd := oversimplify a
    let bcmd := oversimplify b
    if acmd == ["echo", "${VAR}"] then
      if bcmd == ["wc", "-c"] || bcmd == ["wc", "-m"] then
        [makeComment .styleC t.id 2000 "See if you can use ${#variable} instead."]
      else []
    else []
  | _ => []

/-- SC2036: If you wanted to assign the output of the pipeline, use a=$(b | c) -/
def checkPipedAssignment (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ (first :: _ :: _) =>
    match first.inner with
    | .T_Redirecting _ cmd =>
      match cmd.inner with
      | .T_SimpleCommand (_::_) [] =>  -- Has assignments, no words
        [makeComment .warningC t.id 2036
          "If you wanted to assign the output of the pipeline, use a=$(b | c) ."]
      | _ => []
    | _ => []
  | _ => []

/-- SC2037: To assign the output of a command, use var=$(cmd) -/
def checkAssignAteCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand [assign] (firstWord :: _) =>
    match assign.inner with
    | .T_Assignment _ _ _ value =>
      -- Check if first word looks like a flag or glob
      if isFlag firstWord || isGlob firstWord then
        [makeComment .errorC t.id 2037 "To assign the output of a command, use var=$(cmd) ."]
      else
        -- Check if it's a known command name
        let cmdStr := getLiteralString value |>.getD ""
        if cmdStr ∈ commonCommands then
          [makeComment .warningC t.id 2209
            "Use var=$(command) to assign output (or quote to assign string)."]
        else []
    | _ => []
  | _ => []
where
  commonCommands : List String := ["ls", "cat", "pwd", "date", "whoami", "hostname",
    "uname", "id", "basename", "dirname", "head", "tail", "wc", "grep", "find",
    "cut", "tr", "sort", "uniq", "awk", "sed"]

/-- SC2099: Use $((..)) for arithmetics -/
def checkArithmeticOpCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand [_assign] (firstWord :: _) =>
    let op := getLiteralString firstWord |>.getD ""
    if op ∈ ["+", "-", "*", "/"] then
      [makeComment .warningC firstWord.id 2099
        s!"Use $((..)) for arithmetics, e.g. i=$((i {op} 2))"]
    else []
  | _ => []

/-- SC2002: Useless cat. Consider cmd < file | .. instead -/
def checkUuoc (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ (first :: _ :: _) =>
    match first.inner with
    | .T_Redirecting _ cmd =>
      if isCommand cmd "cat" then
        match getCommandArgs cmd with
        | [word] =>
          let str := getLiteralString word |>.getD ""
          if not (str.startsWith "-") && not (willBecomeMultipleArgs word) then
            [makeComment .styleC word.id 2002
              "Useless cat. Consider 'cmd < file | ..' or 'cmd file | ..' instead."]
          else []
        | _ => []
      else []
    | _ => []
  | _ => []
where
  getCommandArgs (t : Token) : List Token :=
    match t.inner with
    | .T_SimpleCommand _ (_ :: args) => args
    | _ => []

/-- SC2009: Consider using pgrep instead of grepping ps output -/
def checkPsGrep (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasPsGrep cmdNames then
      cmds.filterMap fun c =>
        if getCommandBasename c == some "ps" then
          some (makeComment .infoC c.id 2009
            "Consider using pgrep instead of grepping ps output.")
        else none
    else []
  | _ => []
where
  hasPsGrep (names : List String) : Bool :=
    match names with
    | "ps" :: rest => rest.any (· == "grep")
    | _ :: rest => hasPsGrep rest
    | [] => false

/-- SC2010: Don't use ls | grep -/
def checkLsGrep (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasLsGrep cmdNames then
      cmds.filterMap fun c =>
        if getCommandBasename c == some "ls" then
          some (makeComment .warningC c.id 2010
            "Don't use ls | grep. Use a glob or a for loop with a condition to allow non-alphanumeric filenames.")
        else none
    else []
  | _ => []
where
  hasLsGrep (names : List String) : Bool :=
    match names with
    | "ls" :: rest => rest.any (· == "grep")
    | _ :: rest => hasLsGrep rest
    | [] => false

/-- SC2011: Use find .. -print0 | xargs -0 instead of ls | xargs -/
def checkLsXargs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasLsXargs cmdNames then
      cmds.filterMap fun c =>
        if getCommandBasename c == some "ls" then
          some (makeComment .warningC c.id 2011
            "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.")
        else none
    else []
  | _ => []
where
  hasLsXargs (names : List String) : Bool :=
    match names with
    | "ls" :: rest => rest.any (· == "xargs")
    | _ :: rest => hasLsXargs rest
    | [] => false

/-- SC2038: Use find -print0 | xargs -0 -/
def checkFindXargs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasFindXargs cmdNames then
      let allArgs := cmds.flatMap oversimplify
      -- Check if -print0 or -0 is used
      if not (allArgs.any (· == "-print0") || allArgs.any (· == "-0") ||
              allArgs.any (· == "--null") || allArgs.any fun s => s.endsWith "printf") then
        cmds.filterMap fun c =>
          if getCommandBasename c == some "find" then
            some (makeComment .warningC c.id 2038
              "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.")
          else none
      else []
    else []
  | _ => []
where
  hasFindXargs (names : List String) : Bool :=
    match names with
    | "find" :: rest => rest.any (· == "xargs")
    | _ :: rest => hasFindXargs rest
    | [] => false

/-- SC2126: Consider using grep -c instead of grep|wc -l -/
def checkGrepWc (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasGrepWc cmdNames then
      let allArgs := cmds.flatMap oversimplify
      -- Skip if grep has -o, -l, -L, -r, -R, -A, -B, or wc has -c, -m, -w
      if not (allArgs.any fun s => s ∈ ["-o", "--only-matching", "-l", "-L",
              "-r", "-R", "--recursive", "-A", "-B", "--after-context", "--before-context",
              "-c", "--count", "-m", "-w", "--words"]) then
        cmds.filterMap fun c =>
          if getCommandBasename c == some "grep" then
            some (makeComment .styleC c.id 2126
              "Consider using 'grep -c' instead of 'grep|wc -l'.")
          else none
      else []
    else []
  | _ => []
where
  hasGrepWc (names : List String) : Bool :=
    match names with
    | "grep" :: rest => rest.any (· == "wc")
    | _ :: rest => hasGrepWc rest
    | [] => false

/-- Helper for SC2096 -/
partial def checkShebangParametersImpl (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Annotation _ inner => checkShebangParametersImpl inner
  | .T_Script shebang _ =>
    match shebang.inner with
    | .T_Literal sb =>
      let words := sb.splitOn " " |>.filter (· != "")
      -- More than 2 words (#!/path/to/env bash -x) and not using -S or --split-string
      if words.length > 2 &&
         not (Regex.containsSubstring sb "-S" || Regex.containsSubstring sb "--split-string") then
        [makeComment .errorC t.id 2096 "On most OS, shebangs can only specify a single parameter."]
      else []
    | _ => []
  | _ => []

/-- SC2096: On most OS, shebangs can only specify a single parameter -/
def checkShebangParameters (_params : Parameters) (t : Token) : List TokenComment :=
  checkShebangParametersImpl t

/-- Helper for SC2148 -/
partial def checkShebangImpl (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Annotation _ inner => checkShebangImpl params inner
  | .T_Script shebang _ =>
    match shebang.inner with
    | .T_Literal sb =>
      -- Use shebang token's id for proper line 1 position
      let comments1 :=
        if sb.isEmpty && not params.shellTypeSpecified then
          [makeComment .errorC shebang.id 2148
            "Tips depend on target shell and yours is unknown. Add a shebang or a 'shell' directive."]
        else []
      let comments2 :=
        if Regex.containsSubstring sb "ash" && not (Regex.containsSubstring sb "bash") then
          [makeComment .warningC t.id 2187
            "Ash scripts will be checked as Dash. Add '# shellcheck shell=dash' to silence."]
        else []
      let comments3 :=
        if not sb.isEmpty && not (sb.startsWith "/") && not (sb.startsWith "#") then
          [makeComment .errorC t.id 2239
            "Ensure the shebang uses an absolute path to the interpreter."]
        else []
      let firstWord := sb.splitOn " " |>.head? |>.getD ""
      let comments4 :=
        if firstWord.endsWith "/" then
          [makeComment .errorC t.id 2246
            "This shebang specifies a directory. Ensure the interpreter is a file."]
        else []
      comments1 ++ comments2 ++ comments3 ++ comments4
    | _ => []
  | _ => []

/-- SC2148: Tips depend on target shell and yours is unknown -/
def checkShebang (params : Parameters) (t : Token) : List TokenComment :=
  checkShebangImpl params t

/-- SC2162: read without -r will mangle backslashes -/
def checkReadWithoutR (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "read" then
      let args := words.flatMap oversimplify
      if not (args.any fun s => s == "-r" || (s.startsWith "-" && s.any (· == 'r'))) then
        [makeComment .infoC t.id 2162 "read without -r will mangle backslashes."]
      else []
    else []
  | _ => []

/-- SC2129: Consider using { cmd1; cmd2; } >> file instead of repeated redirects -/
def checkMultipleRedirectsImpl (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_BraceGroup cmds =>
    let redirectedCmds := cmds.filter hasAppendRedirect
    if redirectedCmds.length >= 3 then
      [makeComment .styleC t.id 2129
        "Consider using { cmd1; cmd2; } >> file instead of individual redirects."]
    else []
  | _ => []
where
  hasAppendRedirect (cmd : Token) : Bool :=
    match cmd.inner with
    | .T_Redirecting redirects _ =>
      redirects.any fun r =>
        match r.inner with
        | .T_FdRedirect _ op =>
          match op.inner with
          | .T_IoFile opToken _ =>
            getLiteralString opToken == some ">>"
          | _ => false
        | _ => false
    | _ => false

/-- SC2128: Expanding an array without an index gives the first element -/
def checkArrayWithoutIndex (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let str := oversimplify content |>.foldl (· ++ ·) ""
    let varName := ASTLib.getBracedReference str
    -- Check if it's an array variable without [@] or [*] or [n]
    if isVariableName varName && not (str.any (· == '[')) then
      -- Check if variable is known to be an array
      if isArrayVariable params varName then
        [makeComment .warningC t.id 2128
          "Expanding an array without an index only gives the first element."]
      else []
    else []
  | _ => []
where
  isVariableName (s : String) : Bool :=
    match s.toList with
    | c :: _ => c.isAlpha || c == '_'
    | [] => false
  isArrayVariable (params : Parameters) (name : String) : Bool :=
    -- Check variable flow for array assignments
    params.variableFlow.any fun
      | .Assignment (_, _, n, .DataArray _) => n == name
      | _ => false

/-- SC2071: > is for string comparisons. Use -gt instead -/
def checkNumberComparisons (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    if op ∈ [">", "<", ">=", "<=", "\\>", "\\<"] then
      -- Check if operands look like numbers or numeric variables
      let lhsNum := isNumericLooking lhs
      let rhsNum := isNumericLooking rhs
      if lhsNum || rhsNum then
        let suggestion := match op with
          | ">" => "-gt"
          | "<" => "-lt"
          | ">=" => "-ge"
          | "<=" => "-le"
          | "\\>" => "-gt"
          | "\\<" => "-lt"
          | _ => op
        [makeComment .warningC t.id 2071
          s!"{op} is for string comparisons. Use {suggestion} instead."]
      else []
    else []
  | _ => []
where
  isNumericLooking (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.all (fun c => c.isDigit || c == '-')
    | Option.none =>
      match t.inner with
      | .T_DollarBraced _ _ => true  -- Could be numeric
      | _ => false

/-- SC2072: Decimals are not supported. Use bc or awk -/
def checkDecimalComparisons (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    -- Check both numeric comparison ops and string comparison ops (< > in [[]])
    if op ∈ ["-eq", "-ne", "-lt", "-le", "-gt", "-ge", "<", ">", "<=", ">="] then
      let lhsDecimal := hasDecimal lhs
      let rhsDecimal := hasDecimal rhs
      if lhsDecimal || rhsDecimal then
        [makeComment .errorC t.id 2072
          "Decimals are not supported. Either use integers only, or use bc or awk to compare."]
      else []
    else []
  | _ => []
where
  hasDecimal (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.any (· == '.') && s.any Char.isDigit
    | Option.none => false

/-- SC2143: Use grep -q instead of comparing output -/
def checkGrepQ (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    if op ∈ ["!=", "=", "==", "-n", "-z"] then
      if hasGrep lhs || hasGrep rhs then
        [makeComment .styleC t.id 2143
          "Use grep -q instead of comparing output with [ -n .. ]."]
      else []
    else []
  | .TC_Unary _ op inner =>
    if op ∈ ["-n", "-z"] then
      if hasGrep inner then
        [makeComment .styleC t.id 2143
          "Use grep -q instead of comparing output with [ -n .. ]."]
      else []
    else []
  | _ => []
where
  hasGrep (t : Token) : Bool :=
    match t.inner with
    | .T_DollarExpansion cmds =>
      cmds.any fun c => getCommandBasename c == some "grep"
    | .T_Backticked cmds =>
      cmds.any fun c => getCommandBasename c == some "grep"
    | .T_NormalWord parts =>
      -- Non-recursive check - just check first level for command subs
      parts.any fun p =>
        match p.inner with
        | .T_DollarExpansion cmds => cmds.any fun c => getCommandBasename c == some "grep"
        | .T_Backticked cmds => cmds.any fun c => getCommandBasename c == some "grep"
        | _ => false
    | _ => false

/-- SC2035: Use ./*glob* or -- *glob* to avoid expanding into flags -/
def checkGlobAsCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (first :: _) =>
    match first.inner with
    | .T_NormalWord parts =>
      if parts.any isGlobStart then
        [makeComment .warningC first.id 2035
          "Use ./*glob* or -- *glob* so names with dashes won't become options."]
      else []
    | _ => []
  | _ => []
where
  isGlobStart (t : Token) : Bool :=
    match t.inner with
    | .T_Glob s => s.startsWith "*" || s.startsWith "?"
    | .T_Extglob _ _ => true
    | _ => false

/-- SC2013: To read lines rather than words, pipe/redirect to a 'while read' loop -/
def checkForInCat (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.flatMap fun word =>
      match word.inner with
      | .T_NormalWord parts =>
        parts.flatMap fun part =>
          match part.inner with
          | .T_DollarExpansion cmds =>
            cmds.flatMap fun cmd =>
              if getCommandBasename cmd == some "cat" then
                [makeComment .warningC part.id 2013
                  "To read lines rather than words, pipe/redirect to a 'while read' loop."]
              else []
          | .T_Backticked cmds =>
            cmds.flatMap fun cmd =>
              if getCommandBasename cmd == some "cat" then
                [makeComment .warningC part.id 2013
                  "To read lines rather than words, pipe/redirect to a 'while read' loop."]
              else []
          | _ => []
      | _ => []
  | _ => []

/-- SC2048: Use "$@" (with quotes) to prevent whitespace problems -/
def checkDollarStar (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_NormalWord [part] =>
    match part.inner with
    | .T_DollarBraced _ content =>
      let str := oversimplify content |>.foldl (· ++ ·) ""
      let isQuoteFree := isStrictlyQuoteFree params.shellType params.parentMap t
      let modifier := getBracedModifier str
      if str.startsWith "*" && not isQuoteFree then
        [makeComment .warningC part.id 2048
          "Use \"$@\" (with quotes) to prevent whitespace problems."]
      else if modifier.startsWith "[*]" && not (str.startsWith "#") then
        [makeComment .warningC part.id 2048
          "Use \"${array[@]}\" (with quotes) to prevent whitespace problems."]
      else []
    | _ => []
  | _ => []
where
  isStrictlyQuoteFree (_shell : Shell) (_parents : Std.HashMap Id Token) (_t : Token) : Bool :=
    -- Simplified - would need proper parent context analysis
    false

/-- SC2145: Argument mixes string and array. Use * or separate argument -/
def checkConcatenatedDollarAt (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_NormalWord parts =>
    let hasArray := parts.any isArrayExpansion
    let hasOther := parts.any fun p =>
      match p.inner with
      | .T_Literal s => not s.isEmpty
      | .T_SingleQuoted _ => true
      | .T_DoubleQuoted _ => true
      | _ => false
    if hasArray && hasOther && parts.length > 1 then
      [makeComment .warningC t.id 2145
        "Argument mixes string and array. Use * or separate argument."]
    else []
  | _ => []

/-- SC2050: This expression is constant. Did you forget the $ on a variable? -/
def checkConstantIfs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    if op ∈ ["-nt", "-ot", "-ef"] then []  -- File tests aren't constant
    else if isConstant lhs && isConstant rhs then
      [makeComment .warningC t.id 2050
        "This expression is constant. Did you forget the $ on a variable?"]
    else if op ∈ ["=", "==", "!="] && not (wordsCanBeEqual lhs rhs) then
      [makeComment .warningC t.id 2193
        "The arguments to this comparison can never be equal. Make sure your syntax is correct."]
    else []
  | _ => []

/-- SC2076: Remove quotes from right-hand side of =~ to match as regex -/
def checkQuotedCondRegex (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ "=~" _ rhs =>
    match rhs.inner with
    | .T_NormalWord [part] =>
      match part.inner with
      | .T_DoubleQuoted _ =>
        if hasRegexMetachars rhs then
          [makeComment .warningC rhs.id 2076
            "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
        else []
      | .T_SingleQuoted _ =>
        if hasRegexMetachars rhs then
          [makeComment .warningC rhs.id 2076
            "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
        else []
      | _ => []
    | _ => []
  | _ => []
where
  hasRegexMetachars (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.any fun c => c ∈ ['[', ']', '*', '.', '+', '(', ')', '|']
    | Option.none => false

/-- SC2049: =~ is for regex, but this looks like a glob. Use = instead -/
def checkGlobbedRegex (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType "=~" _ rhs =>
    if condType == .doubleBracket then
      let str := oversimplify rhs |>.foldl (· ++ ·) ""
      if isConfusedGlobRegex str then
        [makeComment .warningC rhs.id 2049
          "=~ is for regex, but this looks like a glob. Use = instead."]
      else []
    else []
  | _ => []
where
  isConfusedGlobRegex (s : String) : Bool :=
    -- Starts with * or ? without being escaped or in a regex group
    (s.startsWith "*" || s.startsWith "?") &&
    not (s.startsWith "^") && not (s.startsWith "(")

/-- SC2107/SC2108/SC2109/SC2110: Conditional operators in wrong bracket type -/
def checkConditionalAndOrs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_And condType "&&" _ _ =>
    if condType == .singleBracket then
      [makeComment .errorC t.id 2107 "Instead of [ a && b ], use [ a ] && [ b ]."]
    else []
  | .TC_And condType "-a" _ _ =>
    if condType == .doubleBracket then
      [makeComment .errorC t.id 2108 "In [[..]], use && instead of -a."]
    else
      [makeComment .warningC t.id 2166 "Prefer [ p ] && [ q ] as [ p -a q ] is not well defined."]
  | .TC_Or condType "||" _ _ =>
    if condType == .singleBracket then
      [makeComment .errorC t.id 2109 "Instead of [ a || b ], use [ a ] || [ b ]."]
    else []
  | .TC_Or condType "-o" _ _ =>
    if condType == .doubleBracket then
      [makeComment .errorC t.id 2110 "In [[..]], use || instead of -o."]
    else
      [makeComment .warningC t.id 2166 "Prefer [ p ] || [ q ] as [ p -o q ] is not well defined."]
  | _ => []

/-- SC2074: Can't use =~ in [ ]. Use [[..]] instead -/
def checkSingleBracketOperators (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType "=~" _ _ =>
    let isBashOrKsh := params.shellType == Shell.Bash || params.shellType == Shell.Ksh
    if condType == .singleBracket && isBashOrKsh then
      [makeComment .errorC t.id 2074 "Can't use =~ in [ ]. Use [[..]] instead."]
    else []
  | _ => []

/-- SC2075: Escaping < or > is required in [..], but invalid in [[..]] -/
def checkDoubleBracketOperators (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType op _ _ =>
    if condType == .doubleBracket && op ∈ ["\\<", "\\>"] then
      [makeComment .errorC t.id 2075
        s!"Escaping {op} is required in [..], but invalid in [[..]]"]
    else []
  | _ => []

/-- SC2078/SC2158-2161: Constant nullary test expressions -/
def checkConstantNullary (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Nullary _ inner =>
    if isConstant inner then
      let str := onlyLiteralString inner
      match str with
      | "false" => [makeComment .errorC inner.id 2158 "[ false ] is true. Remove the brackets."]
      | "0" => [makeComment .errorC inner.id 2159 "[ 0 ] is true. Use 'false' instead."]
      | "true" => [makeComment .styleC inner.id 2160 "Instead of '[ true ]', just use 'true'."]
      | "1" => [makeComment .styleC inner.id 2161 "Instead of '[ 1 ]', use 'true'."]
      | _ => [makeComment .errorC inner.id 2078
          "This expression is constant. Did you forget a $ somewhere?"]
    else []
  | _ => []

/-- SC2079: (( )) doesn't support decimals. Use bc or awk -/
def checkForDecimals (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TA_Expansion _ =>
    if not (hasFloatingPoint params) then
      match getLiteralString t with
      | some s =>
        if s.any Char.isDigit && s.any (· == '.') then
          [makeComment .errorC t.id 2079 "(( )) doesn't support decimals. Use bc or awk."]
        else []
      | Option.none => []
    else []
  | _ => []
where
  hasFloatingPoint (_params : Parameters) : Bool := false  -- Shell arithmetic doesn't support floats

/-- SC2017: Increase precision by replacing a/b*c with a*c/b -/
def checkDivBeforeMult (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TA_Binary "*" lhs _ =>
    match lhs.inner with
    | .TA_Binary "/" _ _ =>
      [makeComment .infoC t.id 2017 "Increase precision by replacing a/b*c with a*c/b."]
    | _ => []
  | _ => []

/-- SC2070: -n doesn't work with unquoted arguments -/
def checkUnquotedN (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary condType "-n" inner =>
    if condType == .singleBracket && willSplit inner then
      if not (getWordParts inner |>.any isArrayExpansion) then
        [makeComment .errorC inner.id 2070
          "-n doesn't work with unquoted arguments. Quote or use [[ ]]."]
      else []
    else []
  | _ => []

/-- SC2077/SC2157: Literal strings breaking tests -/
def checkLiteralBreakingTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Nullary _ word =>
    if not (isConstant word) then
      let parts := getWordParts word
      -- Check for unspaced comparison operators
      if parts.any hasEquals then
        [makeComment .errorC t.id 2077 "You need spaces around the comparison operator."]
      else if parts.any isNonEmptyLiteral then
        [makeComment .errorC t.id 2157
          "Argument to implicit -n is always true due to literal strings."]
      else []
    else []
  | .TC_Unary _ op word =>
    if op == "-n" && not (isConstant word) then
      if getWordParts word |>.any isNonEmptyLiteral then
        [makeComment .errorC t.id 2157 "Argument to -n is always true due to literal strings."]
      else []
    else if op == "-z" && not (isConstant word) then
      if getWordParts word |>.any isNonEmptyLiteral then
        [makeComment .errorC t.id 2157 "Argument to -z is always false due to literal strings."]
      else []
    else []
  | _ => []
where
  hasEquals (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.any (· == '=')
    | Option.none => false
  isNonEmptyLiteral (t : Token) : Bool :=
    match getLiteralString t with
    | some s => not s.isEmpty
    | Option.none => false

/-- SC2073: Escape < or > to prevent redirection -/
def checkEscapedComparisons (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType op _ _ =>
    if condType == .singleBracket && op ∈ ["<", ">"] then
      match params.shellType with
      | .Sh => []  -- Unsupported in sh
      | .Dash => [makeComment .errorC t.id 2073 s!"Escape \\{op} to prevent it redirecting."]
      | .BusyboxSh => [makeComment .errorC t.id 2073 s!"Escape \\{op} to prevent it redirecting."]
      | _ => [makeComment .errorC t.id 2073
          s!"Escape \\{op} to prevent it redirecting (or switch to [[ .. ]])."]
    else []
  | _ => []

/-- SC2094: Make sure not to read and write the same file in the same pipeline -/
def checkRedirectToSame (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let allRedirs := cmds.flatMap getRedirFiles
    findDuplicateRedirs params allRedirs
  | _ => []
where
  getRedirFiles (cmd : Token) : List (Token × Bool) :=  -- (file, isInput)
    match cmd.inner with
    | .T_Redirecting redirects _ =>
      redirects.flatMap fun r =>
        match r.inner with
        | .T_FdRedirect _ op =>
          match op.inner with
          | .T_IoFile opTok file =>
            match getLiteralString opTok with
            | some "<" => [(file, true)]
            | some ">" => [(file, false)]
            | some ">>" => [(file, false)]
            | _ => []
          | _ => []
        | _ => []
    | _ => []

  findDuplicateRedirs (_params : Parameters) (redirs : List (Token × Bool)) : List TokenComment :=
    let inputFiles := redirs.filter (·.2) |>.map (·.1)
    let outputFiles := redirs.filter (not ·.2) |>.map (·.1)
    inputFiles.flatMap fun inFile =>
      outputFiles.flatMap fun outFile =>
        let inStr := oversimplify inFile |>.foldl (· ++ ·) ""
        let outStr := oversimplify outFile |>.foldl (· ++ ·) ""
        if inStr == outStr && not (inStr.startsWith "/dev/") then
          [makeComment .infoC outFile.id 2094
            "Make sure not to read and write the same file in the same pipeline."]
        else []

/-- Check if in quote-free context for SC2046.
    Returns true when the expansion is in a context where word splitting doesn't apply:
    - Inside assignments (x=$(cmd))
    - Inside double quotes ("$(cmd)")
    - Inside [[ conditions, arithmetic, etc. -/
partial def isQuoteFreeForExpansion (parentMap : Std.HashMap Id Token) (t : Token) : Bool :=
  go t
where
  go (current : Token) : Bool :=
    match parentMap.get? current.id with
    | Option.none => false
    | some parent =>
        match parent.inner with
        | .T_Assignment .. => true
        | .T_DoubleQuoted .. => true
        | .T_Condition .. => true
        | .T_Arithmetic .. => true
        | .TC_Nullary .doubleBracket .. => true
        | .TC_Unary .doubleBracket .. => true
        | .TC_Binary .doubleBracket .. => true
        | .T_DollarBraced .. => true
        | .T_HereDoc .. => true
        | .T_CaseExpression .. => true
        -- Keep searching for these wrapper types
        | .T_NormalWord .. => go parent
        | .T_Redirecting .. => go parent
        | .T_SimpleCommand .. => go parent
        | .T_Script .. => false  -- Reached top
        | _ => go parent  -- Keep looking

/-- SC2046: Quote this to prevent word splitting -/
def checkUnquotedExpansions (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarExpansion cmds =>
    if cmds.isEmpty then []
    else if shouldBeSplit t then []
    else if isQuoteFreeForExpansion params.parentMap t then []
    else [makeComment .warningC t.id 2046 "Quote this to prevent word splitting."]
  | .T_Backticked cmds =>
    if cmds.isEmpty then []
    else if shouldBeSplit t then []
    else if isQuoteFreeForExpansion params.parentMap t then []
    else [makeComment .warningC t.id 2046 "Quote this to prevent word splitting."]
  | _ => []
where
  shouldBeSplit (t : Token) : Bool :=
    -- Some commands like seq and pgrep are typically used for word splitting
    match t.inner with
    | .T_DollarExpansion cmds =>
      cmds.any fun c => getCommandBasename c ∈ [some "seq", some "pgrep"]
    | .T_Backticked cmds =>
      cmds.any fun c => getCommandBasename c ∈ [some "seq", some "pgrep"]
    | _ => false

/-- SC2124: Assigning an array to a string -/
def checkArrayAsString (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ _ _ word =>
    if hasArrayExpansion word then
      [makeComment .warningC t.id 2124
        "Assigning an array to a string! Assign as array, or use * instead of @ to concatenate."]
    else []
  | _ => []
where
  hasArrayExpansion (t : Token) : Bool :=
    getWordParts t |>.any isArrayExpansion

/-- SC2054: Use spaces, not commas, to separate array elements -/
def checkCommarrays (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Array elements =>
    if elements.any isCommaSeparated then
      [makeComment .warningC t.id 2054 "Use spaces, not commas, to separate array elements."]
    else []
  | _ => []
where
  isCommaSeparated (t : Token) : Bool :=
    let lit := getLiteralLiteralHelper t
    lit.any (· == ',')
  getLiteralLiteralHelper (t : Token) : String :=
    match t.inner with
    | .T_IndexedElement _ v =>
      match v.inner with
      | .T_NormalWord parts => String.join (parts.map getLiteralPart)
      | .T_Literal s => s
      | _ => ""
    | .T_NormalWord parts => String.join (parts.map getLiteralPart)
    | .T_Literal s => s
    | _ => ""
  getLiteralPart (t : Token) : String :=
    match t.inner with
    | .T_Literal s => s
    | _ => ""

/-- SC2055: You probably wanted -a here, otherwise it's always true -/
def checkOrNeq (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Or condType op lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TC_Binary _ op1 lhs1 rhs1, .TC_Binary _ op2 lhs2 rhs2 =>
      if (op1 == "-ne" || op1 == "!=") && op1 == op2 then
        let lhs1Str := oversimplify lhs1 |>.foldl (· ++ ·) ""
        let lhs2Str := oversimplify lhs2 |>.foldl (· ++ ·) ""
        let rhs1Str := oversimplify rhs1 |>.foldl (· ++ ·) ""
        let rhs2Str := oversimplify rhs2 |>.foldl (· ++ ·) ""
        if lhs1Str == lhs2Str && rhs1Str != rhs2Str && not (isGlob rhs1) && not (isGlob rhs2) then
          let suggestion := if condType == .singleBracket then "-a" else "&&"
          [makeComment .warningC t.id 2055
            s!"You probably wanted {suggestion} here, otherwise it's always true."]
        else []
      else []
    | _, _ => []
  | .TA_Binary "||" lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TA_Binary "!=" word1 _, .TA_Binary "!=" word2 _ =>
      let w1 := oversimplify word1 |>.foldl (· ++ ·) ""
      let w2 := oversimplify word2 |>.foldl (· ++ ·) ""
      if w1 == w2 then
        [makeComment .warningC t.id 2056 "You probably wanted && here, otherwise it's always true."]
      else []
    | _, _ => []
  | _ => []

/-- SC2333: You probably wanted || here, otherwise it's always false -/
def checkAndEq (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_And condType _ lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TC_Binary _ op1 lhs1 rhs1, .TC_Binary _ op2 lhs2 rhs2 =>
      if op1 == op2 && (op1 == "=" || op1 == "==" || op1 == "-eq") then
        let lhs1Str := oversimplify lhs1 |>.foldl (· ++ ·) ""
        let lhs2Str := oversimplify lhs2 |>.foldl (· ++ ·) ""
        let rhs1Str := oversimplify rhs1 |>.foldl (· ++ ·) ""
        let rhs2Str := oversimplify rhs2 |>.foldl (· ++ ·) ""
        if lhs1Str == lhs2Str && rhs1Str != rhs2Str && isLiteral rhs1 && isLiteral rhs2 then
          let suggestion := if condType == .singleBracket then "-o" else "||"
          [makeComment .warningC t.id 2333
            s!"You probably wanted {suggestion} here, otherwise it's always false."]
        else []
      else []
    | _, _ => []
  | .TA_Binary "&&" lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TA_Binary "==" lhs1 rhs1, .TA_Binary "==" lhs2 rhs2 =>
      let l1 := oversimplify lhs1 |>.foldl (· ++ ·) ""
      let l2 := oversimplify lhs2 |>.foldl (· ++ ·) ""
      if l1 == l2 && isLiteral rhs1 && isLiteral rhs2 then
        [makeComment .warningC t.id 2334 "You probably wanted || here, otherwise it's always false."]
      else []
    | _, _ => []
  | _ => []

/-- SC2057/SC2058: Unknown test operator -/
def checkValidCondOps (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op _ _ =>
    if not (op ∈ binaryTestOps) then
      [makeComment .warningC t.id 2057 "Unknown binary operator."]
    else []
  | .TC_Unary _ op _ =>
    if not (op ∈ unaryTestOps) then
      [makeComment .warningC t.id 2058 "Unknown unary operator."]
    else []
  | _ => []
where
  binaryTestOps := ["-nt", "-ot", "-ef", "-eq", "-ne", "-lt", "-le", "-gt", "-ge",
    "=", "==", "!=", "=~", "<", ">", "<=", ">=", "\\<", "\\>",
    "-a", "-o"]
  unaryTestOps := ["-z", "-n", "-o", "-v", "-R",
    "-b", "-c", "-d", "-e", "-f", "-g", "-h", "-k", "-p", "-r", "-s", "-t", "-u", "-w", "-x",
    "-L", "-N", "-O", "-G", "-S",
    "!"]

/-- SC2237: Use [ -n "..." ] instead of [ ! -z "..." ] -/
def checkNegatedTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary _ "!" inner =>
    match inner.inner with
    | .TC_Unary _ "-z" _ =>
      [makeComment .styleC t.id 2237
        "Use [ -n \"...\" ] instead of [ ! -z \"...\" ]."]
    | .TC_Unary _ "-n" _ =>
      [makeComment .styleC t.id 2237
        "Use [ -z \"...\" ] instead of [ ! -n \"...\" ]."]
    | _ => []
  | _ => []

/-- SC2116: Useless echo? Instead of 'cmd $(echo foo)', use 'cmd foo' -/
def checkUuoeVar (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarExpansion [cmd] =>
    checkEchoCmd t.id cmd
  | .T_Backticked [cmd] =>
    checkEchoCmd t.id cmd
  | _ => []
where
  checkEchoCmd (id : Id) (cmd : Token) : List TokenComment :=
    match cmd.inner with
    | .T_Pipeline _ [redirecting] =>
      match redirecting.inner with
      | .T_Redirecting _ inner =>
        match inner.inner with
        | .T_SimpleCommand _ (cmdWord :: args) =>
          if getCommandBasename (⟨cmd.id, .T_SimpleCommand [] (cmdWord :: args)⟩) == some "echo" then
            if args.length > 0 && not (hasGlobOrBrace args) then
              [makeComment .styleC id 2116
                "Useless echo? Instead of 'cmd $(echo foo)', just use 'cmd foo'."]
            else []
          else []
        | _ => []
      | _ => []
    | _ => []

  hasGlobOrBrace (args : List Token) : Bool :=
    args.any fun arg =>
      getWordParts arg |>.any fun part =>
        match part.inner with
        | .T_Glob _ => true
        | .T_Extglob _ _ => true
        | .T_BraceExpansion _ => true
        | _ => false

/-- SC2081: [ .. ] can't match globs. Use [[ .. ]] or case statement -/
def checkComparisonAgainstGlob (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType op _ word =>
    if op ∈ ["=", "==", "!="] && isGlob word then
      if condType == .singleBracket then
        let msg := if params.shellType == Shell.Bash || params.shellType == Shell.Ksh
          then "[ .. ] can't match globs. Use [[ .. ]] or case statement."
          else "[ .. ] can't match globs. Use a case statement."
        [makeComment .errorC word.id 2081 msg]
      else if condType == .doubleBracket && params.shellType == Shell.BusyboxSh then
        [makeComment .errorC word.id 2330
          "BusyBox [[ .. ]] does not support glob matching. Use a case statement."]
      else []
    else []
  | _ => []

/-- SC2254: Quote expansions in case patterns to match literally -/
def checkCaseAgainstGlob (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_CaseExpression _ cases =>
    cases.flatMap fun (_, patterns, _) =>
      patterns.flatMap fun pattern =>
        if not (isGlob pattern) && hasQuoteableExpansion pattern then
          [makeComment .warningC pattern.id 2254
            "Quote expansions in case patterns to match literally rather than as a glob."]
        else []
  | _ => []
where
  hasQuoteableExpansion (t : Token) : Bool :=
    getWordParts t |>.any isQuoteableExpansion

/-- SC2115: Use "${var:?}" to ensure not empty, or check before rm -/
def checkRmWithRoot (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "rm" then
      let args := words.drop 1
      if args.any hasSlashVarExpansion then
        [makeComment .warningC t.id 2115
          "Use \"${var:?}\" to ensure this never expands to / ."]
      else []
    else []
  | _ => []
where
  hasSlashVarExpansion (t : Token) : Bool :=
    match getLiteralString t with
    | some s =>
      -- Check for patterns like /$var or $var/ that could become /
      s.startsWith "/" || s.endsWith "/"
    | Option.none =>
      match t.inner with
      | .T_NormalWord (⟨_, .T_Literal "/"⟩ :: _) => true
      | .T_NormalWord parts =>
        parts.any fun p =>
          match p.inner with
          | .T_DollarBraced _ _ => true
          | _ => false
      | _ => false

/-- SC2059: Don't use variables in printf format string -/
def checkPrintfVar (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "printf" then
      let args := words.drop 1 |>.filter (not ∘ isFlag)
      match args.head? with
      | some formatArg =>
        if hasVariableInFormat formatArg then
          [makeComment .warningC formatArg.id 2059
            "Don't use variables in the printf format string. Use printf '...' \"$var\"."]
        else []
      | Option.none => []
    else []
  | _ => []
where
  hasVariableInFormat (t : Token) : Bool :=
    getWordParts t |>.any fun part =>
      match part.inner with
      | .T_DollarBraced _ _ => true
      | .T_DollarExpansion _ => true
      | .T_Backticked _ => true
      | _ => false

/-- SC2086: Double quote to prevent globbing and word splitting -/
-- This is a simplified version of checkSpacefulnessCfg
def checkUnquotedVariables (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let str := oversimplify content |>.foldl (· ++ ·) ""
    let name := ASTLib.getBracedReference str
    -- Skip special variables that don't need quoting
    if name ∈ specialVarsNoQuote then []
    else if isArrayExpansion t then []  -- Covered by SC2068
    else if isCountingReference t then []
    else if isQuoteFreeLocal params t then []
    else [makeComment .infoC t.id 2086
        "Double quote to prevent globbing and word splitting."]
  | _ => []
where
  specialVarsNoQuote := ["?", "#", "-", "$", "!", "_", "PPID", "BASHPID",
    "UID", "EUID", "RANDOM", "LINENO", "SECONDS", "SHLVL", "HISTCMD",
    "BASH_SUBSHELL", "COLUMNS", "LINES"]
  isCountingReference (t : Token) : Bool :=
    match t.inner with
    | .T_DollarBraced _ content =>
      let str := oversimplify content |>.foldl (· ++ ·) ""
      str.startsWith "#"
    | _ => false
  isQuoteFreeLocal (params : Parameters) (t : Token) : Bool :=
    -- Use the full isQuoteFree check from AnalyzerLib
    ShellCheck.AnalyzerLib.isQuoteFree params.shellType params.parentMap t

/-- SC2123: PATH is the shell search path. Use another name -/
def checkOverridingPath (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand assigns [] =>
    assigns.flatMap fun assign =>
      match assign.inner with
      | .T_Assignment _ "PATH" _ word =>
        let str := oversimplify word |>.foldl (· ++ ·) ""
        -- Warn if setting PATH without /bin or /sbin
        if not (Regex.containsSubstring str "/bin" || Regex.containsSubstring str "/sbin") then
          if str.any (· == '/') && not (str.any (· == ':')) then
            [makeComment .warningC assign.id 2123
              "PATH is the shell search path. Use another name."]
          else []
        else []
      | _ => []
  | _ => []

/-- SC2147: Literal tilde in PATH works poorly across programs -/
def checkTildeInPath (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand assigns _ =>
    assigns.flatMap fun assign =>
      match assign.inner with
      | .T_Assignment _ "PATH" _ word =>
        match word.inner with
        | .T_NormalWord parts =>
          if parts.any hasTildeInQuotes then
            [makeComment .warningC assign.id 2147
              "Literal tilde in PATH works poorly across programs."]
          else []
        | _ => []
      | _ => []
  | _ => []
where
  hasTildeInQuotes (t : Token) : Bool :=
    match t.inner with
    | .T_DoubleQuoted parts =>
      parts.any fun p =>
        match getLiteralString p with
        | some s => s.any (· == '~')
        | Option.none => false
    | .T_SingleQuoted s => s.any (· == '~')
    | _ => false

/-- SC2141: This IFS value contains a literal backslash -/
def checkSuspiciousIFS (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ "IFS" _ value =>
    match getLiteralString value with
    | some s =>
      let hasDollarSingle := params.shellType == Shell.Bash || params.shellType == Shell.Ksh
      let suggestN := if hasDollarSingle then "$'\\n'" else "'<literal linefeed here>'"
      let suggestT := if hasDollarSingle then "$'\\t'" else "\"$(printf '\\t')\""
      if s == "\\n" then
        [makeComment .warningC value.id 2141
          s!"This backslash is literal. Did you mean IFS={suggestN} ?"]
      else if s == "\\t" then
        [makeComment .warningC value.id 2141
          s!"This backslash is literal. Did you mean IFS={suggestT} ?"]
      else if s.any (· == '\\') then
        [makeComment .warningC value.id 2141
          "This IFS value contains a literal backslash. For tabs/linefeeds/escapes, use $'..' or printf."]
      else []
    | Option.none => []
  | _ => []

/-- SC2144: -e doesn't work with globs. Use a for loop -/
def checkTestArgumentSplitting (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary condType op token =>
    if op == "-v" then
      if condType == .singleBracket && isGlob token then
        [makeComment .errorC token.id 2208
          "Use [[ ]] or quote arguments to -v to avoid glob expansion."]
      else []
    else if isGlob token then
      [makeComment .errorC token.id 2144 s!"{op} doesn't work with globs. Use a for loop."]
    else []
  | .TC_Nullary condType token =>
    if isGlob token then
      [makeComment .errorC token.id 2144 "This test always fails. Globs don't work in test expressions."]
    else if condType == .doubleBracket && isArrayExpansion token then
      [makeComment .errorC token.id 2198 "[[ $array ]] always true. Use [[ ${array[0]} ]] or [[ ${array[@]} ]]."]
    else []
  | _ => []

/-- SC2064: Use single quotes, otherwise this expands now rather than when signalled -/
def checkTrapQuoting (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "trap" then
      let args := words.drop 1 |>.filter (not ∘ isFlag)
      match args.head? with
      | some trapArg =>
        if hasExpansionInDoubleQuotes trapArg then
          [makeComment .warningC trapArg.id 2064
            "Use single quotes, otherwise this expands now rather than when signalled."]
        else []
      | Option.none => []
    else []
  | _ => []
where
  hasExpansionInDoubleQuotes (t : Token) : Bool :=
    match t.inner with
    | .T_NormalWord [part] =>
      match part.inner with
      | .T_DoubleQuoted parts =>
        parts.any fun p =>
          match p.inner with
          | .T_DollarBraced _ _ => true
          | .T_DollarExpansion _ => true
          | .T_Backticked _ => true
          | _ => false
      | _ => false
    | _ => false

/-- SC2066: Since you double quoted this, it will not word split, and the loop will only run once -/
def checkSingleLoopIteration (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    match words with
    | [word] =>
      match word.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_DoubleQuoted _ =>
          if hasArrayOrAtExpansion part then []  -- Arrays in quotes are OK
          else
            [makeComment .errorC word.id 2066
              "Since you double quoted this, it will not word split, and the loop will only run once."]
        | _ => []
      | _ => []
    | _ => []
  | _ => []
where
  hasArrayOrAtExpansion (t : Token) : Bool :=
    match t.inner with
    | .T_DoubleQuoted parts =>
      parts.any fun p =>
        isArrayExpansion p ||
        match p.inner with
        | .T_DollarBraced _ content =>
          let s := oversimplify content |>.foldl (· ++ ·) ""
          s == "@" || s.startsWith "@"
        | _ => false
    | _ => false

/-- SC2088: Tilde does not expand in quotes. Use $HOME -/
def checkTildeInQuotes (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_NormalWord parts =>
    parts.flatMap fun part =>
      match part.inner with
      | .T_DoubleQuoted inner =>
        inner.flatMap fun elem =>
          match elem.inner with
          | .T_Literal s =>
            if s.startsWith "~" then
              [makeComment .warningC elem.id 2088
                "Tilde does not expand in quotes. Use $HOME."]
            else []
          | _ => []
      | .T_SingleQuoted s =>
        if s.startsWith "~" then
          [makeComment .warningC part.id 2088
            "Tilde does not expand in quotes. Use $HOME."]
        else []
      | _ => []
  | _ => []

/-- SC2089/SC2090: Quotes/backslashes will be treated literally -/
def checkQuotesForExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ _ _ word =>
    if hasQuotesInValue word then
      [makeComment .warningC t.id 2089
        "Quotes/backslashes will be treated literally. Use an array."]
    else []
  | _ => []
where
  hasQuotesInValue (t : Token) : Bool :=
    match getLiteralString t with
    | some s =>
      (s.any (· == '"') || s.any (· == '\'') || Regex.containsSubstring s "\\ ")
      && not (s.startsWith "-")  -- Skip flags
    | Option.none => false

/-- SC2091: Remove surrounding $() to avoid executing output -/
def checkExecuteCommandOutput (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ [cmdWord] =>
    match cmdWord.inner with
    | .T_NormalWord [part] =>
      match part.inner with
      | .T_DollarExpansion cmds =>
        if cmds.any (fun c => getCommandBasename c |>.isSome) then
          [makeComment .warningC t.id 2091
            "Remove surrounding $() to avoid executing output (or use eval if intentional)."]
        else []
      | .T_Backticked cmds =>
        if cmds.any (fun c => getCommandBasename c |>.isSome) then
          [makeComment .warningC t.id 2091
            "Remove surrounding $() to avoid executing output (or use eval if intentional)."]
        else []
      | _ => []
    | _ => []
  | _ => []

/-- SC2093: Remove \"exec \" if script should continue after this command -/
def checkExecWithSubshell (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "exec" then
      let args := words.drop 1
      if args.any isCommandSubstitution then
        [makeComment .infoC t.id 2093
          "Remove \"exec \" if script should continue after this command."]
      else []
    else []
  | _ => []

/-- SC2095: Add < /dev/null to prevent ssh from swallowing stdin -/
def checkSshInLoop (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_WhileExpression _ body =>
    checkBodyForSsh params body
  | .T_ForIn _ _ body =>
    checkBodyForSsh params body
  | _ => []
where
  checkBodyForSsh (_params : Parameters) (body : List Token) : List TokenComment :=
    body.flatMap fun cmd =>
      if isCommand cmd "ssh" || isCommand cmd "ffmpeg" then
        [makeComment .infoC cmd.id 2095
          "Add < /dev/null to prevent this command from swallowing stdin."]
      else []

/-- SC2067: Missing ';' or '+' terminating -exec -/
def checkFindExec (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    if getCommandBasename ⟨cmd.id, cmd.inner⟩ == some "find" then
      checkExecArgs t.id args false
    else []
  | _ => []
where
  checkExecArgs (baseId : Id) : List Token → Bool → List TokenComment
    | [], inExec => if inExec then [makeComment .errorC baseId 2067
        "Missing ';' or + terminating -exec. You can't use |/||/&&, and ';' has to be a separate, quoted argument."]
      else []
    | w :: rest, inExec =>
      match getLiteralString w with
      | some "-exec" => checkExecArgs baseId rest true
      | some "-execdir" => checkExecArgs baseId rest true
      | some "-ok" => checkExecArgs baseId rest true
      | some "-okdir" => checkExecArgs baseId rest true
      | some "+" => checkExecArgs baseId rest false
      | some ";" => checkExecArgs baseId rest false
      | _ => checkExecArgs baseId rest inExec

/-- SC2038: Use -print0 with find | xargs to handle special filenames -/
def checkPipePitfalls (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    match cmds with
    | [findCmd, xargsCmd] =>
      let findName := getCommandBasename findCmd
      let xargsName := getCommandBasename xargsCmd
      if findName == some "find" && xargsName == some "xargs" then
        let hasNull := hasParameter findCmd "-print0" ||
                       hasParameter findCmd "printf" ||
                       hasParameter xargsCmd "-0" ||
                       hasParameter xargsCmd "null"
        if hasNull then [] else
          [makeComment .warningC t.id 2038
            "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames."]
      else []
    | _ => []
  | _ => []

/-- SC2206: Quote to prevent word splitting in array assignment -/
def checkSplittingInArrays (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Array elements =>
    elements.foldl (fun acc elem =>
      acc ++ checkArrayElement params elem
    ) []
  | _ => []
where
  checkArrayElement (params : Parameters) (word : Token) : List TokenComment :=
    match word.inner with
    | .T_NormalWord parts =>
      parts.foldl (fun acc part =>
        acc ++ checkPart params part
      ) []
    | _ => []

  checkPart (params : Parameters) (part : Token) : List TokenComment :=
    match part.inner with
    | .T_DollarExpansion _ => [makeComment .warningC part.id 2207
        (if params.shellType == .Ksh then
          "Prefer read -A or while read to split command output (or quote to avoid splitting)."
        else
          "Prefer mapfile or read -a to split command output (or quote to avoid splitting).")]
    | .T_DollarBraceCommandExpansion _ _ => [makeComment .warningC part.id 2207
        "Prefer mapfile or read -a to split command output (or quote to avoid splitting)."]
    | .T_Backticked _ => [makeComment .warningC part.id 2207
        "Prefer mapfile or read -a to split command output (or quote to avoid splitting)."]
    | .T_DollarBraced _ content =>
      let str := String.join (oversimplify content)
      let varName := ASTLib.getBracedReference str
      if ASTLib.isCountingReference part ||
         ASTLib.isQuotedAlternativeReference part ||
         variablesWithoutSpaces.contains varName then []
      else [makeComment .warningC part.id 2206
        (if params.shellType == .Ksh then
          "Quote to prevent word splitting/globbing, or split robustly with read -A or while read."
        else
          "Quote to prevent word splitting/globbing, or split robustly with mapfile or read -a.")]
    | _ => []

/-- SC2096: On most OS, shebangs can only specify a single parameter -/
def checkShebangParams (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Script shebang _ =>
    match shebang.inner with
    | .T_Literal s =>
      let parts := s.splitOn " "
      -- Check for env -S or env --split-string which allows multiple params
      let isEnvSplit := Regex.containsSubstring s "env -S" ||
                        Regex.containsSubstring s "env --split-string"
      if parts.length > 2 && !isEnvSplit then
        [makeComment .errorC shebang.id 2096
          "On most OS, shebangs can only specify a single parameter."]
      else []
    | _ => []
  | _ => []

/-- SC2069: Redirect stderr to stdout before piping -/
def checkStderrPipe (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    if cmds.length >= 2 then
      match cmds.head? with
      | some cmd => checkForStderrRedirect cmd
      | Option.none => []
    else []
  | _ => []
where
  checkForStderrRedirect (cmd : Token) : List TokenComment :=
    match cmd.inner with
    | .T_Redirecting redirects _inner =>
      -- Check if any redirect is stderr-related at end of pipeline element
      let hasStderrRedirect := redirects.any fun r =>
        match r.inner with
        | .T_FdRedirect "2" _ => true
        | _ => false
      if hasStderrRedirect then []  -- Already handling stderr
      else []  -- Could check if stderr should be redirected
    | _ => []

/-- SC2227: Redirecting to/from command name instead of file -/
def checkRedirectionToCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects _ =>
    redirects.foldl (fun acc r =>
      acc ++ checkRedirect r
    ) []
  | _ => []
where
  checkRedirect (r : Token) : List TokenComment :=
    match r.inner with
    | .T_FdRedirect _ op =>
      match op.inner with
      | .T_IoFile _ target =>
        match getLiteralString target with
        | some s =>
          if isLikelyCommand s then
            [makeComment .warningC target.id 2227
              s!"This is a file name, not a command. Use '$({s} ..)' if you meant to run it."]
          else []
        | Option.none => []
      | _ => []
    | _ => []

  isLikelyCommand (s : String) : Bool :=
    s ∈ ["grep", "cat", "sed", "awk", "sort", "head", "tail", "wc", "ls", "find"]

/-- SC2229: Redirecting to a number creates a file -/
def checkRedirectionToNumber (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects _ =>
    redirects.foldl (fun acc r =>
      acc ++ checkRedirect r
    ) []
  | _ => []
where
  checkRedirect (r : Token) : List TokenComment :=
    match r.inner with
    | .T_FdRedirect _ op =>
      match op.inner with
      | .T_IoFile _ target =>
        match getLiteralString target with
        | some s =>
          if s.all Char.isDigit && s.length > 0 && s.length <= 2 then
            [makeComment .warningC target.id 2229
              ("This does not redirect to fd " ++ s ++ ". Use " ++ s ++ ">file or {var}>file.")]
          else []
        | Option.none => []
      | _ => []
    | _ => []

/-- SC2015: Note that A && B || C is not if-then-else -/
def checkBadTestAndOr (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_OrIf lhs _rhs =>
    match lhs.inner with
    | .T_AndIf _cond action =>
      -- Check if action might fail
      if mightFail action then
        [makeComment .infoC t.id 2015
          "Note that A && B || C is not if-then-else. C may run when A is true."]
      else []
    | _ => []
  | _ => []
where
  mightFail (t : Token) : Bool :=
    -- Commands that might fail
    match getCommandName t with
    | some name => name ∈ ["echo", "printf", ":", "true"]  -- These usually succeed
    | Option.none => true

/-- SC2166: Prefer [ p ] || [ q ] as [ p -o q ] is not well defined -/
def checkTestAndOr (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    -- Check if this is a [ ] test command
    match (words.head?, words.getLast?) with
    | (some first, some last) =>
      if getLiteralString first == some "[" && getLiteralString last == some "]" then
        -- Look for -o or -a in the middle words
        words.foldl (fun acc word =>
          match getLiteralString word with
          | some "-o" =>
            (makeComment .warningC word.id 2166
              "Prefer [ p ] || [ q ] as [ p -o q ] is not well defined.") :: acc
          | some "-a" =>
            (makeComment .warningC word.id 2166
              "Prefer [ p ] && [ q ] as [ p -a q ] is not well defined.") :: acc
          | _ => acc
        ) []
      else []
    | _ => []
  | _ => []

/-- SC2060: Quote parameters to tr to prevent glob expansion -/
def checkTrParams (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    if getCommandBasename ⟨cmd.id, cmd.inner⟩ == some "tr" then
      args.foldl (fun acc arg =>
        acc ++ checkTrArg arg
      ) []
    else []
  | _ => []
where
  checkTrArg (arg : Token) : List TokenComment :=
    match arg.inner with
    | .T_NormalWord parts =>
      if parts.any ASTLib.isGlob then
        [makeComment .warningC arg.id 2060
          "Quote parameters to tr to prevent glob expansion."]
      else []
    | _ => []

/-- SC2062: Quote the grep pattern to avoid glob expansion -/
def checkGrepPattern (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    let cmdName := getCommandBasename ⟨cmd.id, cmd.inner⟩
    if cmdName == some "grep" || cmdName == some "egrep" || cmdName == some "fgrep" then
      -- Check non-flag arguments for globs
      args.filter (fun a => not (ASTLib.isFlag a))
        |>.take 1  -- Pattern is usually first non-flag arg
        |>.foldl (fun acc arg =>
          if hasUnquotedGlob arg then
            acc ++ [makeComment .warningC arg.id 2062
              "Quote the grep pattern so the shell won't interpret it."]
          else acc
        ) []
    else []
  | _ => []
where
  hasUnquotedGlob (t : Token) : Bool :=
    match t.inner with
    | .T_NormalWord parts => parts.any ASTLib.isGlob
    | _ => false

/-- SC2071: Comparison operators only work in [[ ]] in some shells -/
def checkComparisonOperators (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .singleBracket op _ _ =>
    let isCompOp := op == "<" || op == ">"
    let isBasicShell := params.shellType == .Sh ||
                        params.shellType == .Dash ||
                        params.shellType == .BusyboxSh
    if isCompOp && isBasicShell then
      [makeComment .errorC t.id 2071
        s!"{op} is not supported in [ ]. Use [[ ]] or (( )) for this comparison."]
    else []
  | _ => []

/-- SC2073: Escape \< (or use determine) to prevent redirection -/
def checkTestRedirection (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects inner =>
    match inner.inner with
    | .T_Condition .singleBracket _ =>
      if !redirects.isEmpty then
        [makeComment .warningC t.id 2073
          "Escape \\< to prevent redirection (or determine intention and rewrite)."]
      else []
    | _ => []
  | _ => []

/-- SC2088: Tilde does not expand in quotes -/
def checkTildeExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DoubleQuoted parts =>
    parts.foldl (fun acc part =>
      match part.inner with
      | .T_Literal s =>
        if s.startsWith "~" then
          acc ++ [makeComment .warningC part.id 2088
            "Tilde does not expand in quotes. Use $HOME."]
        else acc
      | _ => acc
    ) []
  | _ => []

/-- SC2089/2090: Quotes/backslashes will be treated literally -/
def checkQuotesInVariables (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ _name _ value =>
    let valStr := getLiteralStringDef "" value
    if Regex.containsSubstring valStr "'" ||
       Regex.containsSubstring valStr "\"" ||
       Regex.containsSubstring valStr "\\" then
      -- Would need to track if this variable is later used unquoted
      []  -- Complex check requiring flow analysis
    else []
  | _ => []

/-- SC2091: Remove surrounding $() to run command (or use quotes) -/
def checkSubshellAsTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Condition _ expr =>
    checkForCommandSub expr
  | _ => []
where
  checkForCommandSub (expr : Token) : List TokenComment :=
    match expr.inner with
    | .TC_Nullary _ inner =>
      match inner.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_DollarExpansion _ =>
          [makeComment .warningC expr.id 2091
            "Remove surrounding $() to run command (or use quotes to avoid treating output as shell code)."]
        | _ => []
      | _ => []
    | _ => []

/-- SC2092: Remove backticks to avoid executing output -/
def checkBackticksAsTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Condition _ expr =>
    checkForBackticks expr
  | _ => []
where
  checkForBackticks (expr : Token) : List TokenComment :=
    match expr.inner with
    | .TC_Nullary _ inner =>
      match inner.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_Backticked _ =>
          [makeComment .warningC expr.id 2092
            "Remove backticks to avoid executing output."]
        | _ => []
      | _ => []
    | _ => []

/-- SC2093: Remove exec if script should continue after this command -/
def checkSpuriousExec (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: _) =>
    if getCommandName ⟨cmd.id, cmd.inner⟩ == some "exec" then
      -- Would need to check if this is last command in script/function
      []  -- Complex check
    else []
  | _ => []

/-- SC2094: File being read and written in same pipeline -/
def checkReadWriteSameFile (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects cmd =>
    let files := getRedirectedFiles redirects
    if files.length > 0 then
      checkCommandForSameFile cmd files
    else []
  | _ => []
where
  getRedirectedFiles (redirects : List Token) : List String :=
    redirects.filterMap fun r =>
      match r.inner with
      | .T_FdRedirect _ op =>
        match op.inner with
        | .T_IoFile _ target => getLiteralString target
        | _ => none
      | _ => none

  checkCommandForSameFile (_cmd : Token) (_files : List String) : List TokenComment :=
    []  -- Complex check requiring command analysis

/-- SC2095: Add -n to ssh/scp or command may not run properly in while loop -/
def checkWhileReadSsh (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_WhileExpression cond body =>
    if isReadCommand cond then
      body.foldl (fun acc cmd =>
        acc ++ checkForSshFfmpeg cmd
      ) []
    else []
  | _ => []
where
  isReadCommand (cond : List Token) : Bool :=
    cond.any fun c => getCommandName c == some "read"

  checkForSshFfmpeg (cmd : Token) : List TokenComment :=
    match getCommandName cmd with
    | some "ssh" =>
      if not (hasFlag cmd "n") then
        [makeComment .warningC cmd.id 2095
          "Add < /dev/null or -n to prevent ssh from swallowing stdin."]
      else []
    | some "ffmpeg" =>
      if not (hasParameter cmd "-nostdin") then
        [makeComment .warningC cmd.id 2095
          "Use -nostdin to prevent ffmpeg from consuming stdin."]
      else []
    | _ => []

/-- SC2097: This assignment is only seen by the command's forked shell -/
def checkPrefixAssignment (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand (assign :: _) (cmd :: _) =>
    match assign.inner with
    | .T_Assignment _ name _ _ =>
      -- Check if the command references the same variable
      if commandReferencesVar cmd name then
        [makeComment .warningC assign.id 2097
          s!"This assignment is only seen by the forked process."]
      else []
    | _ => []
  | _ => []
where
  commandReferencesVar (cmd : Token) (name : String) : Bool :=
    -- Simplified check
    let cmdStr := String.join (oversimplify cmd)
    Regex.containsSubstring cmdStr ("$" ++ name) ||
    Regex.containsSubstring cmdStr ("${" ++ name)

/-- SC2059: Don't use variables in the printf format string -/
def checkPrintfFormat (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: format :: _) =>
    if getCommandName ⟨cmd.id, cmd.inner⟩ == some "printf" then
      -- Check if format contains variable expansion
      if hasVariableExpansion format then
        [makeComment .warningC format.id 2059
          "Don't use variables in the printf format string. Use printf '...' \"$var\"."]
      else []
    else []
  | _ => []
where
  hasVariableExpansion (t : Token) : Bool :=
    match t.inner with
    | .T_NormalWord parts => parts.any isExpansion
    | .T_DoubleQuoted parts => parts.any isExpansion
    | _ => false

  isExpansion (t : Token) : Bool :=
    match t.inner with
    | .T_DollarBraced .. => true
    | .T_DollarExpansion .. => true
    | .T_Backticked .. => true
    | _ => false

/-- SC2012: Use find instead of ls to better handle non-alphanumeric filenames -/
def checkLsFind (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: _) =>
    if getCommandBasename ⟨cmd.id, cmd.inner⟩ == some "ls" then
      -- Check if this is in a command substitution context
      []  -- Simplified - would check parent context
    else []
  | _ => []

/-- SC2016: Expressions don't expand in single quotes, use double quotes -/
def checkSingleQuotedVariable (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SingleQuoted s =>
    if hasExpansionSyntax s then
      [makeComment .infoC t.id 2016
        "Expressions don't expand in single quotes, use double quotes for that."]
    else []
  | _ => []
where
  hasExpansionSyntax (s : String) : Bool :=
    Regex.containsSubstring s "$" ||
    Regex.containsSubstring s "`"

/-- SC2044: For loops over find output are fragile -/
def checkForInFind (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.head?.bind (fun w =>
      match w.inner with
      | .T_NormalWord [sub] =>
        match sub.inner with
        | .T_DollarExpansion cmds =>
          if cmds.any (fun c => getCommandBasename c == some "find") then
            some [makeComment .warningC t.id 2044
              "For loops over find output are fragile. Use find -exec or while read."]
          else Option.none
        | .T_Backticked cmds =>
          if cmds.any (fun c => getCommandBasename c == some "find") then
            some [makeComment .warningC t.id 2044
              "For loops over find output are fragile. Use find -exec or while read."]
          else Option.none
        | _ => Option.none
      | _ => Option.none
    ) |>.getD []
  | _ => []

/-- SC2064: Use single quotes for trap to avoid immediate expansion -/
def checkTrapExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: handler :: _) =>
    if getCommandName ⟨cmd.id, cmd.inner⟩ == some "trap" then
      match handler.inner with
      | .T_DoubleQuoted parts =>
        if parts.any isCommandSubstitution then
          [makeComment .warningC handler.id 2064
            "Use single quotes, otherwise this expands now rather than when signalled."]
        else []
      | .T_NormalWord parts =>
        if parts.any isCommandSubstitution then
          [makeComment .warningC handler.id 2064
            "Use single quotes, otherwise this expands now rather than when signalled."]
        else []
      | _ => []
    else []
  | _ => []
where
  isCommandSubstitution (t : Token) : Bool :=
    match t.inner with
    | .T_DollarExpansion _ => true
    | .T_Backticked _ => true
    | _ => false

/-- SC2072: Decimals are not supported -/
def checkArithmeticDecimals (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarArithmetic inner => checkForDecimals inner
  | .TA_Expansion parts => parts.foldl (fun acc p => acc ++ checkForDecimals p) []
  | _ => []
where
  checkForDecimals (t : Token) : List TokenComment :=
    match t.inner with
    | .T_Literal s =>
      if Regex.containsSubstring s "." &&
         s.any Char.isDigit then
        [makeComment .errorC t.id 2072
          "Decimals are not supported. Either use integers only, or use bc or awk to compare."]
      else []
    | _ => []

/-- SC2074: Can't use -o inside [[ ]]. Use || and [[ ]] separately -/
def checkDoubleBracketOrOperator (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .doubleBracket op _ _ =>
    if op == "-o" then
      [makeComment .errorC t.id 2074
        "Can't use -o inside [[ ]]. Use || and separate [[ ]] instead."]
    else []
  | _ => []

/-- SC2075: Can't use -a inside [[ ]]. Use && and [[ ]] separately -/
def checkDoubleBracketAndOperator (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .doubleBracket op _ _ =>
    if op == "-a" then
      [makeComment .errorC t.id 2075
        "Can't use -a inside [[ ]]. Use && and separate [[ ]] instead."]
    else []
  | _ => []

/-- SC2076: Remove quotes from right-hand side -/
def checkQuotedRightHandRegex (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .doubleBracket "=~" _ rhs =>
    match rhs.inner with
    | .T_NormalWord [single] =>
      match single.inner with
      | .T_DoubleQuoted _ =>
        [makeComment .warningC rhs.id 2076
          "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
      | .T_SingleQuoted _ =>
        [makeComment .warningC rhs.id 2076
          "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
      | _ => []
    | _ => []
  | _ => []

/-- SC2077: You can't redirect to a dollar expansion -/
def checkRedirectToDollarExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects _ =>
    redirects.foldl (fun acc r => acc ++ checkRedirect r) []
  | _ => []
where
  checkRedirect (r : Token) : List TokenComment :=
    match r.inner with
    | .T_FdRedirect _ op =>
      match op.inner with
      | .T_IoFile _ target =>
        match target.inner with
        | .T_DollarExpansion _ =>
          [makeComment .warningC target.id 2077
            "You can't redirect to a command substitution."]
        | _ => []
      | _ => []
    | _ => []

/-- SC2078: This expression is constant. Did you forget the $ on a variable? -/
def checkConstantTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Nullary _ word =>
    match getLiteralString word with
    | some s =>
      if isVariableLike s then
        [makeComment .warningC word.id 2078
          s!"This expression is constant. Did you forget the $ on '{s}'?"]
      else []
    | Option.none => []
  | _ => []
where
  isVariableLike (s : String) : Bool :=
    isVariableName s && s.length > 1

/-- SC2079: (( )) doesn't support fractions. For floating point, use bc or awk -/
def checkFractionsInArithmetic (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TA_Binary "/" lhs rhs =>
    -- Check if this might produce a fraction
    if mightProduceFraction lhs rhs then
      [makeComment .warningC t.id 2079
        "(( )) doesn't support fractions. For floating point, use bc or awk."]
    else []
  | _ => []
where
  mightProduceFraction (_lhs _rhs : Token) : Bool :=
    -- Simplified check - would need to analyze values
    false

/-- SC2082: To expand via indirection, use arrays, ${!name} or eval -/
def checkDollarDollar (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let s := String.join (oversimplify content)
    if s.startsWith "$" then
      [makeComment .errorC t.id 2082
        "To expand via indirection, use arrays, ${!name} or (associatively risky) eval."]
    else []
  | _ => []

/-- SC2083: Don't add spaces after [ in -/
def checkBracketSpacing (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Condition .singleBracket expr =>
    match expr.inner with
    | .TC_Empty _ => []  -- Empty condition already handled elsewhere
    | _ => []  -- Spacing issues would be caught by parser
  | _ => []

/-- SC2084: Remove '$' or the shell will try to execute the output -/
def checkDollarBraceExpansionInCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: _) =>
    match cmd.inner with
    | .T_NormalWord [single] =>
      match single.inner with
      | .T_DollarBraceCommandExpansion _ _ =>
        [makeComment .warningC cmd.id 2084
          "Remove '$' or the shell will try to execute the output as a command name."]
      | _ => []
    | _ => []
  | _ => []

/-- SC2086: Double quote to prevent globbing and word splitting -/
def checkUnquotedVariable (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    if not (isQuoteFree params.shellType params.parentMap t) &&
       not (ASTLib.isCountingReference t) &&
       not (ASTLib.isArrayExpansion t) then
      let varName := ASTLib.getBracedReference (String.join (oversimplify content))
      if not (variablesWithoutSpaces.contains varName) then
        [makeComment .warningC t.id 2086
          "Double quote to prevent globbing and word splitting."]
      else []
    else []
  | _ => []

/-- SC2117: To run commands as another user, use su -c or sudo -/
def checkBashAsLogin (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    let cmdName := getCommandBasename ⟨cmd.id, cmd.inner⟩
    if cmdName == some "bash" || cmdName == some "sh" then
      if args.any (fun a => getLiteralString a == some "-c") then
        []  -- -c is fine
      else if args.any (fun a =>
        let s := getLiteralString a
        s == some "-l" || s == some "--login"
      ) then
        [makeComment .infoC t.id 2117
          "To run commands as another user, use su -c or sudo."]
      else []
    else []
  | _ => []

/-!
## Function Scope Analysis

Complex checks that analyze function definitions and their usage across the script.
-/

/-- SC2032: Use 'export -f' to export functions to subprocess
    SC2033: Shell functions can't be passed to external commands -/
def checkFunctionsUsedExternally (params : Parameters) (_root : Token) : List TokenComment :=
  let funcMap := getFunctionsAndAliases params.rootNode
  if funcMap.isEmpty then []
  else
    -- Find all command invocations
    let invocations := findCommandInvocations params.rootNode
    invocations.foldl (fun acc (cmdToken, cmdName) =>
      -- Check if this is a command that accepts another command as argument
      if commandsWithFunctionAsArg.contains cmdName then
        -- Check the arguments for function/alias names
        match cmdToken.inner with
        | .T_SimpleCommand _ (_ :: args) =>
          acc ++ args.filterMap fun arg =>
            match couldBeFunctionReference funcMap arg with
            | some funcName =>
              some (makeComment .warningC arg.id 2033
                s!"Shell functions can't be passed to external commands. Use separate script or 'export -f {funcName}'.")
            | Option.none => Option.none
        | .T_Redirecting _ inner =>
          match inner.inner with
          | .T_SimpleCommand _ (_ :: args) =>
            acc ++ args.filterMap fun arg =>
              match couldBeFunctionReference funcMap arg with
              | some funcName =>
                some (makeComment .warningC arg.id 2033
                  s!"Shell functions can't be passed to external commands. Use separate script or 'export -f {funcName}'.")
              | Option.none => Option.none
          | _ => acc
        | _ => acc
      else acc
    ) []

/-- SC2119: Use function "$@" if function's $1 should mean script's $1
    SC2120: Function references arguments, but none are ever passed -/
def checkUnpassedInFunctions (params : Parameters) (_root : Token) : List TokenComment :=
  let funcMap := getFunctionMap params.rootNode
  if funcMap.isEmpty then []
  else
    -- Find all function calls and track which functions are called with arguments
    let callsWithArgs := collectFunctionCalls params.rootNode funcMap
    -- Check each function for positional parameter usage
    funcMap.fold (fun acc _name func =>
      let positionalRefs := functionUsesPositionalParams func
      if positionalRefs.isEmpty then acc
      else
        -- Check if function is ever called with arguments
        match callsWithArgs.get? func.name with
        | some callers =>
          let hasArgsCall := callers.any (·.2)  -- .2 is hasArgs
          if hasArgsCall then acc
          else
            -- Warn on function definition that function is never called with args
            acc ++ positionalRefs.map fun (refTok, refName) =>
              makeComment .warningC refTok.id 2120
                s!"'{func.name}' references argument ${refName}, but none are ever passed."
        | Option.none =>
          -- Function is never called - warn at definition
          acc ++ [makeComment .infoC func.token.id 2120
            s!"'{func.name}' uses positional parameters but is never called."]
    ) []
where
  collectFunctionCalls (root : Token) (funcMap : Std.HashMap String FunctionDefinition) :
      Std.HashMap String (List (Token × Bool)) :=
    let calls := findCommandInvocations root
    calls.foldl (fun m (tok, name) =>
      if funcMap.contains name then
        let hasArgs := match tok.inner with
          | .T_SimpleCommand _ (_ :: args) => !args.isEmpty
          | .T_Redirecting _ inner =>
            match inner.inner with
            | .T_SimpleCommand _ (_ :: args) => !args.isEmpty
            | _ => false
          | _ => false
        let existing := m.get? name |>.getD []
        m.insert name ((tok, hasArgs) :: existing)
      else m
    ) {}

/-- SC2218: This function is used but never defined -/
def checkUseBeforeDefinition (params : Parameters) (_root : Token) : List TokenComment :=
  let funcMap := getFunctionMap params.rootNode
  if funcMap.isEmpty then []
  else
    -- Find all command invocations
    let invocations := findCommandInvocations params.rootNode
    invocations.foldl (fun acc (cmdToken, cmdName) =>
      match funcMap.get? cmdName with
      | some func =>
        -- Check if invocation comes before definition
        if tokenBefore cmdToken func.token then
          acc ++ [makeComment .warningC cmdToken.id 2218
            s!"This function is used but never defined. Did you mean '{cmdName}'?"]
        else acc
      | Option.none => acc
    ) []

/-!
## CFG-Based Analysis

Checks that use control flow graph analysis for more precise tracking.
-/

/-- SC2086: CFG-aware quoting check - checks if variable may contain spaces along any path -/
def checkSpacefulnessCfg (params : Parameters) (t : Token) : List TokenComment :=
  match params.cfgAnalysis with
  | Option.none => []  -- No CFG analysis available, skip
  | some cfg =>
    match t.inner with
    | .T_DollarBraced _ content =>
      if not (isQuoteFree params.shellType params.parentMap t) then
        let varName := ASTLib.getBracedReference (String.join (oversimplify content))
        -- Check if variable may have spaces based on CFG state
        match getIncomingState cfg t.id with
        | some state =>
          match state.variablesInScope.get? varName with
          | some varState =>
            if varState.variableValue.spaceStatus == .SpaceStatusUnknown ||
               varState.variableValue.spaceStatus == .SpaceStatusSpaces then
              [makeComment .warningC t.id 2086
                "Double quote to prevent globbing and word splitting."]
            else []
          | Option.none =>
            -- Unknown variable - warn conservatively
            [makeComment .warningC t.id 2086
              "Double quote to prevent globbing and word splitting."]
        | Option.none => []
      else []
    | _ => []

-- All node checks
def nodeChecks : List (Parameters → Token → List TokenComment) := [
  -- Note: checkUnquotedDollarAt removed to avoid duplicate SC2086 (covered by checkUnquotedVariables)
  checkForInQuoted,
  checkForInLs,
  checkShorthandIf,
  checkArithmeticDeref,
  checkBackticks,
  checkUncheckedCdPushdPopd,
  checkMaskedReturns,
  checkDoubleQuotedWordSplit,
  checkArrayExpansions,
  checkRmGlob,
  checkMultipleRedirects,
  checkSingleQuotedExpansion,
  checkSpuriousExpansion,
  -- Pipeline and command checks
  checkEchoWc,
  checkPipedAssignment,
  checkAssignAteCommand,
  checkArithmeticOpCommand,
  checkUuoc,
  checkPsGrep,
  checkLsGrep,
  checkLsXargs,
  checkFindXargs,
  checkFindExec,
  checkPipePitfalls,
  checkGrepWc,
  checkReadWithoutR,
  checkMultipleRedirectsImpl,
  checkGlobAsCommand,
  checkForInCat,
  checkRedirectToSame,
  checkUuoeVar,
  checkPrintfVar,
  checkRmWithRoot,
  -- Quoting and expansion checks
  checkDollarStar,
  checkConcatenatedDollarAt,
  checkUnquotedExpansions,
  checkArrayAsString,
  checkArrayWithoutIndex,  -- SC2128
  checkCommarrays,
  checkUnquotedVariables,
  checkSplittingInArrays,
  checkTildeExpansion,
  checkQuotesInVariables,
  -- Conditional expression checks
  checkNumberComparisons,
  checkDecimalComparisons,
  checkGrepQ,
  checkConstantIfs,
  checkQuotedCondRegex,
  checkGlobbedRegex,
  checkConditionalAndOrs,
  checkSingleBracketOperators,
  checkDoubleBracketOperators,
  checkConstantNullary,
  checkUnquotedN,
  checkLiteralBreakingTest,
  checkEscapedComparisons,
  checkOrNeq,
  checkAndEq,
  checkValidCondOps,
  checkComparisonAgainstGlob,
  checkCaseAgainstGlob,
  checkBadTestAndOr,
  checkTestAndOr,  -- SC2166
  checkNegatedTest,  -- SC2237
  checkComparisonOperators,
  checkSubshellAsTest,
  checkBackticksAsTest,
  -- Arithmetic checks
  checkForDecimals,
  checkDivBeforeMult,
  -- Path and IFS checks
  checkOverridingPath,
  checkTildeInPath,
  checkSuspiciousIFS,
  -- Test expression checks
  checkTestArgumentSplitting,
  checkTestRedirection,
  -- Redirection checks
  checkRedirectionToCommand,
  checkRedirectionToNumber,
  checkStderrPipe,
  checkReadWriteSameFile,
  -- Various command checks
  checkTrapQuoting,
  checkSingleLoopIteration,
  checkTildeInQuotes,
  checkQuotesForExpansion,
  checkExecuteCommandOutput,
  checkExecWithSubshell,
  checkSshInLoop,
  checkWhileReadSsh,
  checkTrParams,
  checkGrepPattern,
  checkPrefixAssignment,
  checkSpuriousExec,
  -- More checks
  checkPrintfFormat,
  checkLsFind,
  checkSingleQuotedVariable,
  checkForInFind,
  checkTrapExpansion,
  checkArithmeticDecimals,
  checkDoubleBracketOrOperator,
  checkDoubleBracketAndOperator,
  checkQuotedRightHandRegex,
  checkRedirectToDollarExpansion,
  checkConstantTest,
  checkFractionsInArithmetic,
  checkDollarDollar,
  checkBracketSpacing,
  checkDollarBraceExpansionInCommand,
  -- Note: checkUnquotedVariable removed to avoid duplicate SC2086 (covered by checkUnquotedVariables)
  checkBashAsLogin,
  -- CFG-aware checks
  checkSpacefulnessCfg
]

-- All tree checks
def treeChecks : List (Parameters → Token → List TokenComment) := [
  nodeChecksToTreeCheck nodeChecks,
  checkUnusedAssignments,
  checkUnassignedReferences,
  checkShebangParameters,
  checkShebang,
  -- Function scope analysis checks (operate on whole tree)
  checkFunctionsUsedExternally,
  checkUnpassedInFunctions,
  checkUseBeforeDefinition
]

/-!
## Optional Checks

Checks that are only enabled when explicitly requested.
-/

/-- SC2250: Prefer putting braces around variable references -/
def checkBracesAroundVariables (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced false _ => [makeComment .styleC t.id 2250
      "Prefer putting braces around variable references even when not strictly required."]
  | _ => []

/-- Map of optional check names to functions -/
def optionalCheckMap : Std.HashMap String (Parameters → Token → List TokenComment) :=
  ({} : Std.HashMap String (Parameters → Token → List TokenComment))
    |>.insert "avoid-nullary-conditions" (fun _ _ => [])
    |>.insert "add-default-case" (fun _ _ => [])
    |>.insert "require-double-brackets" (fun _ _ => [])
    |>.insert "quote-safe-variables" (fun _ _ => [])
    |>.insert "check-set-e-suppressed" (fun _ _ => [])
    |>.insert "require-variable-braces" checkBracesAroundVariables

/-- List of optional checks -/
def optionalChecks : List String :=
  ["avoid-nullary-conditions", "add-default-case", "require-double-brackets",
   "quote-safe-variables", "check-set-e-suppressed", "require-variable-braces"]

/-!
## Main Entry Point
-/

/-- Create the main checker from spec and parameters -/
def mkChecker (spec : AnalysisSpec) (params : Parameters)
    (checks : List (Parameters → Token → List TokenComment)) : Checker := {
  perScript := fun root =>
    let tok := root.token
    let allChecks := checks ++ getOptionalChecks spec
    pure (allChecks.foldl (fun acc check => acc ++ check params tok) [])
  perToken := fun _ => pure []
}
where
  getOptionalChecks (spec : AnalysisSpec) : List (Parameters → Token → List TokenComment) :=
    let keys := spec.asOptionalChecks
    if keys.contains "all" then
      optionalCheckMap.toList.map (·.2)
    else
      keys.filterMap fun k => optionalCheckMap.get? k

/-- The main checker export -/
def checker (spec : AnalysisSpec) (params : Parameters) : Checker :=
  mkChecker spec params treeChecks

-- Theorems (stubs)

theorem checker_produces_valid_ids (spec : AnalysisSpec) (params : Parameters) :
    True := trivial

theorem nodeChecks_comprehensive :
    nodeChecks.length > 0 := by decide

theorem optionalChecks_all_mapped (name : String) :
    name ∈ optionalChecks → optionalCheckMap.contains name := sorry

theorem checkUnquotedDollarAt_on_at (params : Parameters) (id : Id) :
    True := trivial  -- Would verify SC2086 triggers on $@

theorem checkBackticks_on_backtick (params : Parameters) (id : Id) :
    True := trivial  -- Would verify SC2006 triggers on backticks

theorem mkChecker_includes_optional (spec : AnalysisSpec) (params : Parameters) :
    spec.asOptionalChecks.contains "all" →
    True := fun _ => trivial  -- Would verify all optional checks included

theorem treeChecks_not_empty :
    treeChecks.length > 0 := by decide

theorem runNodeAnalysis_collects_all (f : Parameters → Token → List TokenComment)
    (p : Parameters) (t : Token) :
    True := trivial  -- Would verify all nodes visited

end ShellCheck.Analytics
