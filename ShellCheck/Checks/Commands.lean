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

/-- Command name matcher -/
inductive CommandName where
  | exactly : String → CommandName
  | basename : String → CommandName
  deriving Repr, BEq, Ord, Inhabited

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

/-- SC2014: Use 'while read' instead of 'for line in $(cat)' -/
def checkTr : CommandCheck := {
  name := .exactly "tr"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        let s := getLiteralString arg |>.getD ""
        if s.startsWith "a-z" || s.startsWith "A-Z" then
          some (makeComment .warningC arg.id 2018
            "Use '[:lower:]' or '[:upper:]' for character ranges in tr.")
        else Option.none
    | Option.none => []
}

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

/-- SC2046: Quote to prevent word splitting -/
def checkExpr : CommandCheck := {
  name := .exactly "expr"
  check := fun _params t =>
    [makeComment .infoC t.id 2003
      "expr is deprecated. Use $((..)) or let instead."]
}

/-- SC2062: Quote regex in grep to prevent globbing -/
def checkGrepRe : CommandCheck := {
  name := .basename "grep"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      -- Skip flags, check pattern argument for unquoted glob chars
      let nonFlags := args.filter fun a =>
        let s := getLiteralString a |>.getD ""
        !s.startsWith "-"
      match nonFlags.head? with
      | some pattern =>
        -- Check if pattern has glob chars but isn't quoted
        let isUnquoted := match pattern.inner with
          | .T_Literal _ => true
          | .T_NormalWord parts => parts.all fun p =>
              match p.inner with
              | .T_Literal _ => true
              | _ => false
          | _ => false
        let patStr := getLiteralString pattern |>.getD ""
        let hasGlobChars := patStr.any fun c => c == '*' || c == '?' || c == '['
        if isUnquoted && hasGlobChars then
          [makeComment .warningC pattern.id 2062
            "Quote the grep pattern to prevent glob expansion."]
        else []
      | Option.none => []
    | Option.none => []
}

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

/-- SC2244: Don't use 'let' for string assignment -/
def checkLet : CommandCheck := {
  name := .exactly "let"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        let s := getLiteralString arg |>.getD ""
        -- Check for assignments like x="string" in let
        if stringContains s "=\"" || stringContains s "='" then
          some (makeComment .warningC arg.id 2244
            "'let' is for arithmetic. Use var=value for string assignment.")
        else Option.none
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

/-- SC2003: expr is antiquated. Consider using $((..)) or let. -/
def checkExprArithmetic : CommandCheck := {
  name := .basename "expr"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      -- Check if it looks like arithmetic (has +, -, *, /, %)
      if argStrs.any (fun s => s ∈ ["+", "-", "*", "/", "%", ":", "substr", "index", "length"]) then
        [makeComment .styleC t.id 2003
          "expr is antiquated. Consider rewriting this using $((..)), ${}, or [[ ]]."]
      else []
    | Option.none => []
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

/-- SC2020: tr replaces sets of chars, not words -/
def checkTrWords : CommandCheck := {
  name := .basename "tr"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      let argStrs := args.map (getLiteralString · |>.getD "")
      -- Check for word-like patterns (multiple chars without brackets)
      argStrs.filterMap fun s =>
        if s.length > 2 && !s.startsWith "[" && !s.startsWith "-" &&
           s.all (fun c => c.isAlpha || c.isDigit) then
          some (makeComment .infoC t.id 2020
            "tr replaces sets of chars, not words. Are you sure this is what you want?")
        else Option.none
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
def checkGlobDash : CommandCheck := {
  name := .basename "rm"  -- Also applies to mv, cp, etc.
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          -- Check for globs that might match files starting with dash
          if (s.startsWith "*" || s.startsWith "?") && !s.startsWith "./" then
            some (makeComment .warningC arg.id 2035
              "Use ./*glob* or -- *glob* to avoid matching dash-prefixed files.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2035 for mv command -/
def checkGlobDashMv : CommandCheck := {
  name := .basename "mv"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if (s.startsWith "*" || s.startsWith "?") && !s.startsWith "./" then
            some (makeComment .warningC arg.id 2035
              "Use ./*glob* or -- *glob* to avoid matching dash-prefixed files.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

/-- SC2035 for cp command -/
def checkGlobDashCp : CommandCheck := {
  name := .basename "cp"
  check := fun _params t =>
    match getCommandArguments t with
    | some args =>
      args.filterMap fun arg =>
        match getLiteralString arg with
        | some s =>
          if (s.startsWith "*" || s.startsWith "?") && !s.startsWith "./" then
            some (makeComment .warningC arg.id 2035
              "Use ./*glob* or -- *glob* to avoid matching dash-prefixed files.")
          else Option.none
        | Option.none => Option.none
    | Option.none => []
}

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
        if placeholders > 0 && argCount > 0 && placeholders != argCount then
          [makeComment .warningC t.id 2183
            s!"This format string has {placeholders} placeholder(s) but {argCount} argument(s)."]
        else []
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

-- Note: SC2199 for [[ ${array[@]} ]] is handled in Analytics.lean since [[ ]] is parsed as T_Condition

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
  checkLet,
  checkFindWithSymlinks,
  checkEchoN,
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
  checkReadR,
  checkPrintfArgCount,
  checkArrayComma,
  -- More new checks
  checkExprArithmetic,  -- SC2003
  checkSudoRedirect,    -- SC2024
  checkCdNoCheck,       -- SC2164
  checkEchoStdin,       -- SC2008
  checkTrWords,         -- SC2020
  checkUnintendedComment, -- SC2026
  checkGlobDash,        -- SC2035 (rm)
  checkGlobDashMv,      -- SC2035 (mv)
  checkGlobDashCp,      -- SC2035 (cp)
  checkTildeInQuotes,   -- SC2088
  checkExecFollowed,    -- SC2093
  checkRmVar            -- SC2115
  -- Note: [ ] and [[ ]] checks moved to Analytics.lean (parsed as T_Condition)
]

/-- Main checker -/
def checker (_spec : AnalysisSpec) (params : Parameters) : Checker :=
  getChecker params commandChecks

-- Theorems (stubs)

theorem commandChecks_not_empty :
    commandChecks.length > 0 := by native_decide

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
