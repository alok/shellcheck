/-
  ShellCheck configuration (.shellcheckrc) parsing.

  This is a pragmatic, partial port focused on the options we already expose on
  the CLI (`--rcfile`, `--norc`) and the most important config key: `disable=`.
-/

import ShellCheck.Interface

namespace ShellCheck.Config

open ShellCheck.Interface

structure RcConfig where
  disabledCodes : List Int := []
  enabledChecks : List String := []
  shellOverride? : Option Shell := none
  externalSources? : Option Bool := none
  sourcePaths : List String := []
  deriving Inhabited

def RcConfig.merge (a b : RcConfig) : RcConfig :=
  { disabledCodes := (a.disabledCodes ++ b.disabledCodes).eraseDups
    enabledChecks := (a.enabledChecks ++ b.enabledChecks).eraseDups
    shellOverride? := a.shellOverride? <|> b.shellOverride?
    externalSources? := a.externalSources? <|> b.externalSources?
    sourcePaths := (a.sourcePaths ++ b.sourcePaths).eraseDups
  }

def trimAsciiString (s : String) : String :=
  s.trimAscii.toString

def parseShell? (s : String) : Option Shell :=
  match (trimAsciiString s).toLower with
  | "sh" => some .Sh
  | "posix" => some .Sh
  | "bash" => some .Bash
  | "ksh" => some .Ksh
  | "dash" => some .Dash
  | "busybox" => some .BusyboxSh
  | "busyboxsh" => some .BusyboxSh
  | "busybox-sh" => some .BusyboxSh
  | _ => none

def parseBool? (s : String) : Option Bool :=
  match (trimAsciiString s).toLower with
  | "true" => some true
  | "false" => some false
  | _ => none

def parseScCode? (s : String) : Option Int :=
  let s := trimAsciiString s
  let s :=
    if s.length ≥ 2 && (s.take 2).toString.toLower == "sc" then
      (s.drop 2).toString
    else
      s
  match (trimAsciiString s).toNat? with
  | some n => some (Int.ofNat n)
  | none => none

def splitListValues (s : String) : List String :=
  -- Accept comma-separated lists with optional whitespace.
  -- We also accept spaces as separators to be forgiving.
  s.splitOn ","
    |>.flatMap (fun seg => seg.splitOn " ")
    |>.map trimAsciiString
    |>.filter (fun seg => !seg.isEmpty)

def parseRcLine (line : String) (cfg : RcConfig) : RcConfig :=
  let withoutComment := (line.splitOn "#").headD line
  let trimmed := trimAsciiString withoutComment
  if trimmed.isEmpty then
    cfg
  else
    let parts := trimmed.splitOn "="
    match parts with
    | [] => cfg
    | [_onlyKey] => cfg
    | key :: rest =>
        let value := trimAsciiString (String.intercalate "=" rest)
        let key := (trimAsciiString key).toLower
        match key with
        | "disable" =>
            let codes := splitListValues value |>.filterMap parseScCode?
            { cfg with disabledCodes := (cfg.disabledCodes ++ codes).eraseDups }
        | "enable" =>
            let checks := splitListValues value
            { cfg with enabledChecks := (cfg.enabledChecks ++ checks).eraseDups }
        | "shell" =>
            match parseShell? value with
            | some shell => { cfg with shellOverride? := some shell }
            | none => cfg
        | "external-sources" =>
            match parseBool? value with
            | some b => { cfg with externalSources? := some b }
            | none => cfg
        | "source-path" =>
            -- ShellCheck accepts a colon-separated search path.
            let paths := value.splitOn ":" |>.map trimAsciiString |>.filter (fun p => !p.isEmpty)
            { cfg with sourcePaths := (cfg.sourcePaths ++ paths).eraseDups }
        | _ =>
            cfg

def parseRcFile (contents : String) : RcConfig :=
  contents.splitOn "\n" |>.foldl (fun cfg line => parseRcLine line cfg) {}

def applyRcConfig (cfg : RcConfig) (spec : CheckSpec) : CheckSpec :=
  { spec with
    csExcludedWarnings := (spec.csExcludedWarnings ++ cfg.disabledCodes).eraseDups
    csOptionalChecks := (spec.csOptionalChecks ++ cfg.enabledChecks).eraseDups
    csShellTypeOverride := spec.csShellTypeOverride <|> cfg.shellOverride?
  }

end ShellCheck.Config
