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

def shellNameLower : Shell → String
  | .Ksh => "ksh"
  | .Sh => "sh"
  | .Bash => "bash"
  | .Dash => "dash"
  | .BusyboxSh => "busyboxsh"

def shellSupport (t : Token) : String × List Shell :=
  match t.inner with
  | .T_CaseExpression _ cases =>
      let seps := cases.map (fun (ct, _, _) => ct)
      if seps.any (· == .caseContinue) then
        ("cases with ;;&", [.Bash])
      else if seps.any (· == .caseFallThrough) then
        ("cases with ;&", [.Bash, .Ksh])
      else
        ("", [])
  | .T_DollarBraceCommandExpansion _ _ =>
      ("${ ..; } command expansion", [.Bash, .Ksh])
  | _ => ("", [])

/-- Wrapper for shell-specific checks -/
structure ForShell where
  shells : List Shell
  check : Parameters → Token → List TokenComment

/-- SC2127: Unsupported shell feature for current shell type. -/
def checkUnsupported : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash, .Ksh]
  check := fun params t =>
    let (name, support) := shellSupport t
    if support.isEmpty || support.contains params.shellType then
      []
    else
      let shells := String.intercalate " or " (support.map shellNameLower)
      [makeComment .errorC t.id 2127
        s!"To use {name}, specify #!/usr/bin/env {shells}"]
}

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

abbrev TestOpSpec := Nat × List Shell × (String → String)

def bashismBinaryTestFlags : List (String × TestOpSpec) := [
  ("<", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  (">", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  ("\\<", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  ("\\>", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  ("<=", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  (">=", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  ("\\<=", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  ("\\>=", (3012, [.Dash, .BusyboxSh], fun op => s!"lexicographical {op} is")),
  ("==", (3014, [.BusyboxSh], fun op => s!"{op} in place of = is")),
  ("=~", (3015, [], fun op => s!"{op} regex matching is"))
]

def bashismUnaryTestFlags : List (String × TestOpSpec) := [
  ("-v", (3016, [], fun op => "test " ++ op ++ " (in place of [ -n \"${var+x}\" ]) is")),
  ("-a", (3017, [], fun op => s!"unary {op} in place of -e is")),
  ("-o", (3062, [], fun op => s!"test {op} to check options is")),
  ("-R", (3063, [], fun op => s!"test {op} and namerefs in general are")),
  ("-N", (3064, [], fun op => s!"test {op} is")),
  ("-k", (3065, [.Dash, .BusyboxSh], fun op => s!"test {op} is")),
  ("-G", (3066, [.Dash, .BusyboxSh], fun op => s!"test {op} is")),
  ("-O", (3067, [.Dash, .BusyboxSh], fun op => s!"test {op} is"))
]

def bashVars : List String := [
  "OSTYPE", "MACHTYPE", "HOSTTYPE", "HOSTNAME",
  "DIRSTACK", "EUID", "UID", "SHLVL", "PIPESTATUS", "SHELLOPTS",
  "_", "BASH", "BASHOPTS", "BASHPID", "BASH_ALIASES", "BASH_ARGC",
  "BASH_ARGV", "BASH_ARGV0", "BASH_CMDS", "BASH_COMMAND",
  "BASH_EXECUTION_STRING", "BASH_LINENO", "BASH_LOADABLES_PATH",
  "BASH_REMATCH", "BASH_SOURCE", "BASH_SUBSHELL", "BASH_VERSINFO",
  "COMP_CWORD", "COMP_KEY", "COMP_LINE", "COMP_POINT", "COMP_TYPE",
  "COMP_WORDBREAKS", "COMP_WORDS", "COPROC", "FUNCNAME", "GROUPS",
  "HISTCMD", "MAPFILE"
]

def bashDynamicVars : List String := [
  "BASH_MONOSECONDS", "EPOCHREALTIME", "EPOCHSECONDS", "RANDOM",
  "SECONDS", "SRANDOM"
]

def dashVars : List String := ["_"]

def isRadix (s : String) : Bool :=
  let chars := s.toList
  let digits := chars.takeWhile (·.isDigit)
  match (chars.drop digits.length).head? with
  | some '#' => !digits.isEmpty
  | _ => false

/-- Check for POSIX-incompatible bashisms in sh scripts -/
partial def checkBashisms : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh]
  check := fun params t =>
    let isBusyboxSh := params.shellType == .BusyboxSh
    let isDash := params.shellType == .Dash || isBusyboxSh
    let warnMsg (id : Id) (code : Nat) (msg : String) : TokenComment :=
      if isDash then
        makeComment .errorC id code s!"In dash, {msg} not supported."
      else
        makeComment .warningC id code s!"In POSIX sh, {msg} undefined."
    let checkTestOp (table : List (String × TestOpSpec)) (op : String) (id : Id) : List TokenComment :=
      match table.find? (fun (name, _) => name == op) with
      | some (_, (code, shells, msg)) =>
          if shells.contains params.shellType then [] else [warnMsg id code (msg op)]
      | none => []
    let isAssigned (var : String) : Bool :=
      params.variableFlow.any fun sd =>
        match sd with
        | .Assignment (_, _, name, _) => name == var
        | _ => false
    let isBashVariable (var : String) : Bool :=
      let isDynamic := bashDynamicVars.contains var
      let isStatic := bashVars.contains var && !isAssigned var
      (isDynamic || isStatic) && !(isDash && dashVars.contains var)
    let startsAfterOptionalIndex (modifier : String) (chars : List Char) : Bool :=
      let mchars := modifier.toList
      match mchars with
      | [] => false
      | c :: _ =>
          if chars.contains c then
            true
          else if c == '[' then
            let rec findAfter : List Char → Option Char
              | [] => none
              | ']' :: next :: _ => some next
              | _ :: rest => findAfter rest
            match findAfter mchars with
            | some next => chars.contains next
            | none => false
          else
            false
    let isStringIndexing (modifier : String) : Bool :=
      if modifier.startsWith ":" then
        match (modifier.drop 1).toString.toList.head? with
        | some c => !(c == '-' || c == '=' || c == '?' || c == '+')
        | none => false
      else
        false
    let isStringOpsOnAtStar (str : String) : Bool :=
      let prefixes := ["@%", "@#", "*%", "*#", "#@", "#*"]
      prefixes.any (fun pfx => str.startsWith pfx)
    let isStringReplacement (modifier : String) : Bool :=
      startsAfterOptionalIndex modifier ['/']
    let isCaseModification (modifier : String) : Bool :=
      startsAfterOptionalIndex modifier [',', '^']
    let rec isArithmeticAncestor (tok : Token) : Bool :=
      match params.parentMap.get? tok.id with
      | some parent =>
          match parent.inner with
          | .T_DollarArithmetic _ => true
          | .T_DollarBracket _ => true
          | .T_Arithmetic _ => true
          | .T_ForArithmetic _ _ _ _ => true
          | .TA_Binary _ _ _ => isArithmeticAncestor parent
          | .TA_Assignment _ _ _ => isArithmeticAncestor parent
          | .TA_Variable _ _ => isArithmeticAncestor parent
          | .TA_Trinary _ _ _ => isArithmeticAncestor parent
          | .TA_Parenthesis _ => isArithmeticAncestor parent
          | .TA_Expansion _ => isArithmeticAncestor parent
          | .TA_Sequence _ => isArithmeticAncestor parent
          | .TA_Unary _ _ => isArithmeticAncestor parent
          | _ => isArithmeticAncestor parent
      | none => false
    let checkSimpleCommand : Token → List TokenComment := fun cmdTok =>
      let name := getCommandName cmdTok |>.getD ""
      let flags := getLeadingFlags cmdTok
      let flagRegex := Regex.mkRegex "^-[eEsn]+$"
      let busyboxFlagRegex := Regex.mkRegex "^-[en]+$"
      let rec getLiteralArgs : List Token → List (Token × String)
        | [] => []
        | arg :: rest =>
            match getLiteralString arg with
            | some s => (arg, s) :: getLiteralArgs rest
            | none => []
      let options := "abCefhmnuvxo"
      let optionsSet := options.toList
      let isOptionChar (c : Char) : Bool := optionsSet.contains c
      let startsOption (s : String) : Bool :=
        (s.startsWith "+" && s.length > 1) ||
        (s.startsWith "-" && !s.startsWith "--" && s.length > 1)
      let beginsWithDoubleDash (s : String) : Bool :=
        s.startsWith "--" && s.length > 2
      let isValidFlags (s : String) : Bool :=
        match s.toList with
        | sign :: rest =>
            (sign == '-' || sign == '+') && !rest.isEmpty && rest.all isOptionChar
        | [] => false
      let isOFlag (s : String) : Bool :=
        match s.toList with
        | sign :: rest =>
            if sign == '-' || sign == '+' then
              match rest.getLast? with
              | some 'o' => (rest.dropLast).all isOptionChar
              | _ => false
            else
              false
        | [] => false
      let longOptions : List String :=
        [ "allexport", "errexit", "ignoreeof", "monitor", "noclobber"
        , "noexec", "noglob", "nolog", "notify" , "nounset", "pipefail"
        , "verbose", "vi", "xtrace" ]
      let rec checkSetArgs : List (Token × String) → List TokenComment := fun opts =>
        match opts with
        | [] => []
        | (flagTok, flagStr) :: rest =>
            if startsOption flagStr then
              let warnFlags :=
                if isValidFlags flagStr then [] else
                  (flagStr.drop 1).toString.toList.filterMap (fun c =>
                    if isOptionChar c then none
                    else some (warnMsg flagTok.id 3041 s!"set flag -{c} is"))
              if isOFlag flagStr then
                match rest with
                | (optTok, optStr) :: rest' =>
                    let warnOpt :=
                      if longOptions.contains optStr then [] else
                        [warnMsg optTok.id 3040 s!"set option {optStr} is"]
                    warnOpt ++ warnFlags ++ checkSetArgs rest'
                | [] => warnFlags
              else
                warnFlags ++ checkSetArgs rest
            else if beginsWithDoubleDash flagStr then
              [warnMsg flagTok.id 3042 s!"set flag {flagStr} is"] ++ checkSetArgs rest
            else
              []
      let allowedFlags : String → Option (List String)
        | "cd" => some ["L", "P"]
        | "exec" => some []
        | "export" => some ["p"]
        | "hash" => some (if isDash then ["r", "v"] else ["r"])
        | "jobs" => some ["l", "p"]
        | "printf" => some []
        | "read" => some (if isDash then ["r", "p"] else ["r"])
        | "readonly" => some ["p"]
        | "trap" => some []
        | "type" => some (if isBusyboxSh then ["p"] else [])
        | "ulimit" =>
            some (
              if isDash then
                ["H", "S", "a", "c", "d", "f", "l", "m", "n", "p", "r", "s", "t", "v", "w"]
              else
                ["H", "S", "a", "c", "d", "f", "n", "s", "t", "v"]
            )
        | "umask" => some ["S"]
        | "unset" => some ["f", "v"]
        | "wait" => some []
        | _ => none
      let unsupportedCommands : List String :=
        [ "let", "caller", "builtin", "complete", "compgen", "declare", "dirs", "disown"
        , "enable", "mapfile", "readarray", "pushd", "popd", "shopt", "suspend"
        , "typeset" ]
      match getCommandArgv cmdTok with
      | none => []
      | some [] => []
      | some (cmdWord :: rest) =>
          let echoCheck : Option (List TokenComment) :=
            match rest with
            | arg :: _ =>
                let argString := String.join (oversimplify arg)
                if isCommand cmdTok "echo" && Regex.isMatch argString flagRegex then
                  if isBusyboxSh then
                    if Regex.isMatch argString busyboxFlagRegex then some [] else
                      some [warnMsg arg.id 3036 "echo flags besides -n and -e"]
                  else if isDash then
                    if argString == "-n" then some [] else
                      some [warnMsg arg.id 3036 "echo flags besides -n"]
                  else
                    some [warnMsg arg.id 3037 "echo flags are"]
                else
                  none
            | [] => none
          match echoCheck with
          | some res => res
          | none =>
              let execCheck : Option (List TokenComment) :=
                match rest with
                | arg :: _ =>
                    let argString := String.join (oversimplify arg)
                    if getLiteralString cmdWord == some "exec" && argString.startsWith "-" then
                      some [warnMsg arg.id 3038 "exec flags are"]
                    else
                      none
                | [] => none
              match execCheck with
              | some res => res
              | none =>
                  if isCommand cmdTok "let" then
                    [warnMsg cmdTok.id 3039 "'let' is"]
                  else if isCommand cmdTok "set" then
                    if isDash then [] else checkSetArgs (getLiteralArgs rest)
                  else
                    let acc : List TokenComment := []
                    let acc :=
                      if name == "local" && !isDash then
                        acc ++ [warnMsg cmdTok.id 3043 "'local' is"]
                      else acc
                    let acc :=
                      if unsupportedCommands.contains name then
                        acc ++ [warnMsg cmdTok.id 3044 s!"'{name}' is"]
                      else acc
                    let acc :=
                      match allowedFlags name with
                      | some allowed =>
                          match flags.find? (fun (_, flag) => !flag.isEmpty && !allowed.contains flag) with
                          | some (word, flag) =>
                              acc ++ [warnMsg word.id 3045 s!"{name} -{flag} is"]
                          | none => acc
                      | none => acc
                    let acc :=
                      if name == "source" && !isBusyboxSh then
                        acc ++ [warnMsg cmdTok.id 3046 "'source' in place of '.' is"]
                      else acc
                    let acc :=
                      if name == "trap" then
                        let args := rest.drop 1
                        args.foldl (fun acc token =>
                          match getLiteralString token with
                          | some s =>
                              let upper := s.toUpper
                              let acc :=
                                if upper == "ERR" || upper == "DEBUG" || upper == "RETURN" then
                                  acc ++ [warnMsg token.id 3047 s!"trapping {s} is"]
                                else acc
                              let acc :=
                                if !isBusyboxSh && upper.startsWith "SIG" then
                                  acc ++ [warnMsg token.id 3048 "prefixing signal names with 'SIG' is"]
                                else acc
                              let acc :=
                                if !isDash && upper != s then
                                  acc ++ [warnMsg token.id 3049 "using lower/mixed case for signal names is"]
                                else acc
                              acc
                          | none => acc
                        ) acc
                      else acc
                    let acc :=
                      if name == "printf" then
                        match rest.head? with
                        | some formatTok =>
                            let literal := onlyLiteralString formatTok
                            if Regex.containsSubstring literal "%q" then
                              acc ++ [warnMsg formatTok.id 3050 "printf %q is"]
                            else acc
                        | none => acc
                      else acc
                    let acc :=
                      if name == "read" && rest.all isFlag then
                        acc ++ [warnMsg cmdWord.id 3061 "read without a variable is"]
                      else acc
                    acc
    match t.inner with
    | .T_ProcSub _ _ =>
        [warnMsg t.id 3001 "process substitution is"]
    | .T_Extglob _ _ =>
        [warnMsg t.id 3002 "extglob is"]
    | .T_DollarSingleQuoted _ =>
        if isBusyboxSh then [] else [warnMsg t.id 3003 "$'..' is"]
    | .T_DollarDoubleQuoted _ =>
        [warnMsg t.id 3004 "$\"..\" is"]
    | .T_ForArithmetic _ _ _ _ =>
        [warnMsg t.id 3005 "arithmetic for loops are"]
    | .T_Arithmetic _ =>
        [warnMsg t.id 3006 "standalone ((..)) is"]
    | .T_DollarBracket _ =>
        [warnMsg t.id 3007 "$[..] in place of $((..)) is"]
    | .T_SelectIn _ _ _ =>
        [warnMsg t.id 3008 "select loops are"]
    | .T_BraceExpansion _ =>
        [warnMsg t.id 3009 "brace expansion is"]
    | .T_Condition .doubleBracket _ =>
        if isBusyboxSh then [] else [warnMsg t.id 3010 "[[ ]] is"]
    | .T_HereString _ =>
        [warnMsg t.id 3011 "here-strings are"]
    | .TC_Binary _ op _ _ =>
        checkTestOp bashismBinaryTestFlags op t.id
    | .T_SimpleCommand _ [testTok, _lhs, opTok, _rhs] =>
        match getLiteralString testTok, getLiteralString opTok with
        | some "test", some op => checkTestOp bashismBinaryTestFlags op t.id
        | _, _ => checkSimpleCommand t
    | .TC_Unary _ op _ =>
        checkTestOp bashismUnaryTestFlags op t.id
    | .T_SimpleCommand _ [testTok, opTok, _arg] =>
        match getLiteralString testTok, getLiteralString opTok with
        | some "test", some op => checkTestOp bashismUnaryTestFlags op t.id
        | _, _ => checkSimpleCommand t
    | .TA_Unary op _ =>
        if op == "|++" || op == "|--" || op == "++|" || op == "--|" then
          let cleaned := String.join (op.toList.filter (· != '|') |>.map String.singleton)
          [warnMsg t.id 3018 s!"{cleaned} is"]
        else []
    | .TA_Binary "**" _ _ =>
        [warnMsg t.id 3019 "exponentials are"]
    | .T_FdRedirect fd target =>
        match fd, target.inner with
        | "&", .T_IoFile op _ =>
            match op.inner with
            | .T_Greater =>
                if isBusyboxSh then [] else [warnMsg t.id 3020 "&> is"]
            | _ => []
        | "", .T_IoFile op file =>
            match op.inner with
            | .T_GREATAND =>
                let literal := onlyLiteralString file
                if literal.toList.all (·.isDigit) then [] else [warnMsg t.id 3021 ">& filename (as opposed to >& fd) is"]
            | _ => []
        | _, _ =>
            if fd.startsWith "{" then
              [warnMsg t.id 3022 "named file descriptors are"]
            else if fd.toList.all (·.isDigit) && fd.length > 1 then
              [warnMsg t.id 3023 "FDs outside 0-9 are"]
            else []
    | .T_Assignment .append _ _ _ =>
        [warnMsg t.id 3024 "+= is"]
    | .T_IoFile _ word =>
        let file := onlyLiteralString word
        if file.startsWith "/dev/tcp" || file.startsWith "/dev/udp" then
          [warnMsg t.id 3025 "/dev/{tcp,udp} is"]
        else if isGlob word then
          [warnMsg t.id 3031 "redirecting to/from globs is"]
        else []
    | .T_Glob str =>
        if Regex.containsSubstring str "[^" then
          [warnMsg t.id 3026 "^ in place of ! in glob bracket expressions is"]
        else []
    | .TA_Variable name _ =>
        if isBashVariable name then
          [warnMsg t.id 3028 s!"{name} is"]
        else []
    | .T_DollarBraced _ content =>
        let str := String.join (oversimplify content)
        let var := ShellCheck.ASTLib.getBracedReference str
        let modifier := ShellCheck.ASTLib.getBracedModifier str
        let acc : List TokenComment := []
        let acc :=
          if !isBusyboxSh && isStringIndexing modifier then
            acc ++ [warnMsg t.id 3057 "string indexing is"]
          else acc
        let acc :=
          if !isBusyboxSh && isStringOpsOnAtStar str then
            acc ++ [warnMsg t.id 3058 "string operations on $@/$* are"]
          else acc
        let acc :=
          if !isBusyboxSh && isStringReplacement modifier then
            acc ++ [warnMsg t.id 3060 "string replacement is"]
          else acc
        let acc :=
          if str.startsWith "!" then
            match (str.drop 1).toString.toList.head? with
            | some c =>
                if isVariableChar c then
                  acc ++ [warnMsg t.id 3053 "indirect expansion is"]
                else
                  acc
            | none => acc
          else acc
        let acc :=
          if !str.startsWith "!" && !var.isEmpty &&
              modifier.startsWith "[" && modifier.endsWith "]" then
            acc ++ [warnMsg t.id 3054 "array references are"]
          else acc
        let acc :=
          if str.startsWith "!" && (modifier == "[@]" || modifier == "[*]") then
            acc ++ [warnMsg t.id 3055 "array key expansion is"]
          else acc
        let acc :=
          if str.startsWith "!" && (modifier == "*" || modifier == "@") then
            acc ++ [warnMsg t.id 3056 "name matching prefixes are"]
          else acc
        let acc :=
          if isCaseModification modifier then
            acc ++ [warnMsg t.id 3059 "case modification is"]
          else acc
        let acc :=
          if isBashVariable var then
            acc ++ [warnMsg t.id 3028 s!"{var} is"]
          else acc
        acc
    | .T_Pipe "|&" =>
        [warnMsg t.id 3029 "|& in place of 2>&1 | is"]
    | .T_Array _ =>
        [warnMsg t.id 3030 "arrays are"]
    | .T_CoProc _ _ =>
        [warnMsg t.id 3032 "coproc is"]
    | .T_Function _ _ name _ =>
        if isVariableName name then [] else [warnMsg t.id 3033 "naming functions outside [a-zA-Z_][a-zA-Z0-9_]* is"]
    | .T_DollarExpansion [cmd] =>
        if isOnlyRedirection cmd then
          [warnMsg t.id 3034 "$(<file) to read files is"]
        else []
    | .T_Backticked [cmd] =>
        if isOnlyRedirection cmd then
          [warnMsg t.id 3035 "`<file` to read files is"]
        else []
    | .T_SourceCommand src _ =>
        if getCommandName src == some "source" && !isBusyboxSh then
          [warnMsg t.id 3051 "'source' in place of '.' is"]
        else []
    | .TA_Expansion (tok :: _) =>
        match tok.inner with
        | .T_Literal str =>
            if isRadix str then
              [warnMsg tok.id 3052 "arithmetic base conversion is"]
            else []
        | _ => []
    | .T_Literal str =>
        if isRadix str && isArithmeticAncestor t then
          [warnMsg t.id 3052 "arithmetic base conversion is"]
        else []
    | .T_SimpleCommand _ _ =>
        checkSimpleCommand t
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

/-- Is this command effectively a bang/negation? -/
def isBangCommand : Token → Bool
  | ⟨_, .T_Banged _⟩ => true
  | ⟨_, .T_Redirecting _ inner⟩ => isBangCommand inner
  | ⟨_, .T_SimpleCommand _ (cmd :: _)⟩ => getLiteralString cmd == some "!"
  | _ => false

/-- SC2325: Multiple ! in front of pipelines are a bash/ksh extension. -/
def checkMultipleBangsPosix : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh]
  check := fun _params t =>
    match t.inner with
    | .T_Banged inner =>
      match inner.inner with
      | .T_Pipeline _ cmds =>
        if cmds.any isBangCommand then
          [makeComment .errorC t.id 2325
            "Multiple ! in front of pipelines are a bash/ksh extension. Use only 0 or 1."]
        else []
      | _ =>
        if isBangCommand inner then
          [makeComment .errorC t.id 2325
            "Multiple ! in front of pipelines are a bash/ksh extension. Use only 0 or 1."]
        else []
    | _ => []
}

/-- SC2326: ! is not allowed in the middle of pipelines. -/
def checkBangAfterPipe : ForShell := {
  shells := [.Sh, .Dash, .BusyboxSh, .Bash]
  check := fun _params t =>
    match t.inner with
    | .T_Pipeline _ cmds =>
      cmds.flatMap fun cmd =>
        if isBangCommand cmd then
          [makeComment .errorC cmd.id 2326
            "! is not allowed in the middle of pipelines. Use command group as in cmd | { ! cmd; } if necessary."]
        else []
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

/-- SC2332: Negated -o or -a in [ ] are always true in bash. -/
def checkNegatedUnaryOpsBash : ForShell := {
  shells := [.Bash]
  check := fun _params t =>
    match t.inner with
    | .TC_Unary .singleBracket "!" inner =>
      match inner.inner with
      | .TC_Unary _ op _ =>
        if op == "-o" then
          [makeComment .errorC t.id 2332
            "[ ! -o opt ] is always true because -o becomes logical OR. Use [[ ]] or ! [ -o opt ]."]
        else if op == "-a" then
          [makeComment .errorC t.id 2332
            "[ ! -a file ] is always true because -a becomes logical AND. Use -e instead."]
        else []
      | _ => []
    | .T_SimpleCommand _ (first :: bangTok :: opTok :: _rest) =>
      if getLiteralString first == some "[" &&
         getLiteralString bangTok == some "!" &&
         getLiteralString opTok == some "-o" then
        [makeComment .errorC t.id 2332
          "[ ! -o opt ] is always true because -o becomes logical OR. Use [[ ]] or ! [ -o opt ]."]
      else if getLiteralString first == some "[" &&
              getLiteralString bangTok == some "!" &&
              getLiteralString opTok == some "-a" then
        [makeComment .errorC t.id 2332
          "[ ! -a file ] is always true because -a becomes logical AND. Use -e instead."]
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
  checkUnsupported,
  checkForDecimals,
  checkBashisms,
  checkEchoSed,
  checkBraceExpansionVars,
  checkMultiDimensionalArrays,
  checkPS1Assignments,
  checkMultipleBangs,
  checkMultipleBangsPosix,
  checkBangAfterPipe,
  checkNegatedUnaryOps,
  checkNegatedUnaryOpsBash,
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
