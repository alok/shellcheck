import Cli
import ShellCheck
import ShellCheck.Checker
import ShellCheck.Parser
import ShellCheck.Formatter.GCC
import ShellCheck.Formatter.Format
import ShellCheck.Formatter.JSON
import ShellCheck.Formatter.TTY
import ShellCheck.Formatter.CheckStyle
import ShellCheck.Formatter.Diff
import ShellCheck.Formatters
import Std.Data.HashSet

open Cli
open ShellCheck.Interface
open ShellCheck.Checker
open ShellCheck.Data
open ShellCheck.Formatter.GCC
open ShellCheck.Formatters

/-- IO-based system interface that can read files -/
def ioSystemInterface : SystemInterface IO := {
  siReadFile := fun _ filename => do
    try
      let contents ← IO.FS.readFile filename
      pure (.ok contents)
    catch e =>
      pure (.error s!"Error reading {filename}: {e}")
  siFindSource := fun _ _ _ name => pure name
  siGetConfig := fun _ => pure none
}

/-- Support parsing `--shell=bash` etc via `Cli`. -/
instance : Cli.ParseableType Shell where
  name := "Shell"
  parse? s :=
    match s.trim.toLower with
    | "sh" => some .Sh
    | "posix" => some .Sh
    | "bash" => some .Bash
    | "ksh" => some .Ksh
    | "dash" => some .Dash
    | "busybox" => some .BusyboxSh
    | "busyboxsh" => some .BusyboxSh
    | "busybox-sh" => some .BusyboxSh
    | _ => none

/-- Support parsing `-f gcc|tty|json|...` via `Cli`. -/
instance : Cli.ParseableType OutputFormat where
  name := "Format"
  parse? s := OutputFormat.fromString s.trim.toLower

structure ScCode where
  n : Int
  deriving Repr, Inhabited, BEq

/-- Support parsing `SC2086` or `2086` via `Cli`. -/
instance : Cli.ParseableType ScCode where
  name := "SCCode"
  parse? s :=
    let s := s.trim
    let s :=
      if s.length ≥ 2 && (s.take 2).toLower == "sc" then
        s.drop 2
      else
        s
    match s.trim.toNat? with
    | some n => some ⟨Int.ofNat n⟩
    | none => none

/-- Support parsing `--severity=warning` via `Cli`. -/
instance : Cli.ParseableType Severity where
  name := "Severity"
  parse? s :=
    match s.trim.toLower with
    | "error" => some .errorC
    | "warning" => some .warningC
    | "info" => some .infoC
    | "style" => some .styleC
    | _ => none

/-- Support parsing `--color=auto|always|never` via `Cli`. -/
instance : Cli.ParseableType ColorOption where
  name := "Color"
  parse? s :=
    match s.trim.toLower with
    | "auto" => some .colorAuto
    | "always" => some .colorAlways
    | "never" => some .colorNever
    | _ => none

structure CheckedFile where
  filename : String
  contents : String
  result : CheckResult

structure RunConfig where
  debug : Bool := false
  shellOverride? : Option Shell := none
  checkSourced : Bool := false
  ignoreRC : Bool := false
  excludedWarnings : List Int := []
  includedWarnings? : Option (List Int) := none
  minSeverity : Severity := .styleC
  extendedAnalysis? : Option Bool := none
  optionalChecks : List String := []
  deriving Inhabited

def shouldUseColor (opt : ColorOption) : IO Bool := do
  match opt with
  | .colorAlways => pure true
  | .colorNever => pure false
  | .colorAuto =>
      let out ← IO.getStdout
      out.isTty

def flagsNamed (p : Parsed) (longName : String) : Array Parsed.Flag :=
  p.flags.filter (fun f => f.flag.longName = longName)

/-!
Pre-process CLI args to allow repeated array-like flags.

Lean's Cli library rejects duplicate flags by default. ShellCheck allows
repeating include/exclude/enable, so we merge repeated occurrences into a
single `--flag=...` with comma-separated values before parsing.
-/
private def repeatableShortToLong : String → Option String
  | "e" => some "exclude"
  | "i" => some "include"
  | "o" => some "enable"
  | _ => none

private def repeatableLong : Std.HashSet String :=
  ["exclude", "include", "enable"].foldl (fun s n => s.insert n) {}

private def addRepeat (name value : String)
    (out : Array String)
    (seen : Std.HashMap String (Nat × String))
    : Array String × Std.HashMap String (Nat × String) :=
  match seen.get? name with
  | Option.none =>
      let idx := out.size
      let out := out.push s!"--{name}={value}"
      let seen := seen.insert name (idx, value)
      (out, seen)
  | some (idx, existing) =>
      let newVal := if existing.isEmpty then value else existing ++ "," ++ value
      let out := out.set! idx s!"--{name}={newVal}"
      let seen := seen.insert name (idx, newVal)
      (out, seen)

private partial def preprocessArgsLoop (rest : List String)
    (out : Array String)
    (seen : Std.HashMap String (Nat × String)) : Array String :=
  match rest with
  | [] => out
  | "--" :: tail =>
      -- End of flags; keep remaining args as-is.
      (out.push "--").append tail.toArray
  | arg :: tail =>
      if arg.startsWith "--" then
        let content := arg.drop 2
        let parts := content.splitOn "="
        match parts with
        | [] => preprocessArgsLoop tail (out.push arg) seen
        | name :: restParts =>
            if repeatableLong.contains name then
              if restParts.isEmpty then
                match tail with
                | value :: tail2 =>
                    let (out, seen) := addRepeat name value out seen
                    preprocessArgsLoop tail2 out seen
                | [] =>
                    preprocessArgsLoop tail (out.push arg) seen
              else
                let value := String.intercalate "=" restParts
                let (out, seen) := addRepeat name value out seen
                preprocessArgsLoop tail out seen
            else
              preprocessArgsLoop tail (out.push arg) seen
      else if arg.startsWith "-" && !arg.startsWith "--" then
        let short := arg.drop 1
        match short.toList with
        | [] => preprocessArgsLoop tail (out.push arg) seen
        | _ =>
            if short.length == 1 then
              match repeatableShortToLong short with
              | some long =>
                  match tail with
                  | value :: tail2 =>
                      let (out, seen) := addRepeat long value out seen
                      preprocessArgsLoop tail2 out seen
                  | [] =>
                      preprocessArgsLoop tail (out.push arg) seen
              | Option.none =>
                  preprocessArgsLoop tail (out.push arg) seen
            else
              -- Support `-eVALUE` style for repeatable short flags.
              let first := short.take 1
              let restVal := short.drop 1
              match repeatableShortToLong first with
              | some long =>
                  let (out, seen) := addRepeat long restVal out seen
                  preprocessArgsLoop tail out seen
              | Option.none =>
                  preprocessArgsLoop tail (out.push arg) seen
      else
        preprocessArgsLoop tail (out.push arg) seen

private def preprocessArgs (args : List String) : List String :=
  preprocessArgsLoop args #[] {} |>.toList

def checkOneFile (sys : SystemInterface IO) (filename : String) (cfg : RunConfig)
    : IO (Option CheckedFile) := do
  let contents ←
    try
      IO.FS.readFile filename
    catch e =>
      IO.eprintln s!"Error reading {filename}: {e}"
      return none

  if cfg.debug then
    IO.eprintln s!"[DEBUG] Read {contents.length} bytes from {filename}"

  let spec : CheckSpec := {
    csFilename := filename
    csScript := contents
    csCheckSourced := cfg.checkSourced
    csIgnoreRC := cfg.ignoreRC
    csExcludedWarnings := cfg.excludedWarnings
    csIncludedWarnings := cfg.includedWarnings?
    csShellTypeOverride := cfg.shellOverride?
    csMinSeverity := cfg.minSeverity
    csExtendedAnalysis := cfg.extendedAnalysis?
    csOptionalChecks := cfg.optionalChecks
  }

  let result ← checkScript sys spec

  if cfg.debug then
    IO.eprintln s!"[DEBUG] Got {result.crComments.length} comments"

  return some { filename, contents, result }

def withRcFile (sys : SystemInterface IO) (rcPath : String) : IO (SystemInterface IO) := do
  let contents ← IO.FS.readFile rcPath
  pure { sys with siGetConfig := fun _ => pure (some (rcPath, contents)) }

def printOptionalChecks : IO Unit := do
  let fromAnalyzer : List CheckDescription := ShellCheck.Analyzer.optionalChecks
  let fromAnalytics : List CheckDescription :=
    ShellCheck.Analytics.optionalChecks.map fun name =>
      { newCheckDescription with
        cdName := name
        cdDescription := "(description not yet ported)"
        cdPositive := ""
        cdNegative := "" }
  let all := fromAnalyzer ++ fromAnalytics
  let sorted :=
    all.toArray.qsort (fun a b => a.cdName < b.cdName) |>.toList
  let mut seen : Std.HashSet String := {}
  for item in sorted do
    if !seen.contains item.cdName then
      seen := seen.insert item.cdName
      IO.println s!"name:    {item.cdName}"
      IO.println s!"desc:    {item.cdDescription}"
      IO.println s!"example: {item.cdPositive}"
      IO.println s!"fix:     {item.cdNegative}"
      IO.println ""

def runShellcheck4 (p : Parsed) : IO UInt32 := do
  if p.hasFlag "list-optional" then
    printOptionalChecks
    return 0

  let debug := p.hasFlag "debug"
  let fmt : OutputFormat := p.flag! "format" |>.as! OutputFormat
  let shellOverride? : Option Shell :=
    p.flag? "shell" |>.map (fun f => f.as! Shell)

  let excluded : List Int :=
    (flagsNamed p "exclude").toList.flatMap (fun f =>
      (f.as! (Array ScCode)).toList.map (·.n))

  let includedCodes : List Int :=
    (flagsNamed p "include").toList.flatMap (fun f =>
      (f.as! (Array ScCode)).toList.map (·.n))
  let included? : Option (List Int) :=
    if (flagsNamed p "include").isEmpty then none else some includedCodes

  let optionalChecks : List String :=
    (flagsNamed p "enable").toList.flatMap (fun f =>
      (f.as! (Array String)).toList)

  let checkSourced := p.hasFlag "check-sourced"
  let ignoreRC := p.hasFlag "norc"
  let rcfilePath? : Option String :=
    p.flag? "rcfile" |>.map (fun f => f.as! String)
  let minSeverity : Severity :=
    (p.flag? "severity" |>.map (fun f => f.as! Severity)).getD .styleC
  let extendedAnalysis? : Option Bool :=
    if p.hasFlag "extended-analysis" then some true else none

  let colorOpt : ColorOption := p.flag! "color" |>.as! ColorOption
  let useColor ← shouldUseColor colorOpt

  let wikiLinkCount : Nat := p.flag! "wiki-link-count" |>.as! Nat
  let formatterOptions : ShellCheck.Formatter.Format.FormatterOptions := {
    foWikiLinkCount := wikiLinkCount
  }

  let files : Array String := p.variableArgsAs! String
  if files.isEmpty then
    p.printError "No input files specified."
    return 1

  let mut checked : List CheckedFile := []
  let sys? : Option (SystemInterface IO) ←
    if ignoreRC then
      pure (some ioSystemInterface)
    else
      match rcfilePath? with
      | some rcPath =>
          try
            let sys ← withRcFile ioSystemInterface rcPath
            pure (some sys)
          catch e =>
            p.printError s!"Error reading rcfile {rcPath}: {e}"
            pure none
      | none =>
          pure (some ioSystemInterface)
  let sys ←
    match sys? with
    | some sys => pure sys
    | none => return (2 : UInt32)
  let cfg : RunConfig := {
    debug
    shellOverride?
    checkSourced
    ignoreRC
    excludedWarnings := excluded
    includedWarnings? := included?
    minSeverity
    extendedAnalysis?
    optionalChecks
  }

  for f in files do
    if let some cf ← checkOneFile sys f cfg then
      checked := cf :: checked

  let checkedFiles := checked.reverse
  let results := checkedFiles.map (·.result)
  let hasIssues := results.any (fun r => !r.crComments.isEmpty)

  match fmt with
  | .gcc =>
      for cf in checkedFiles do
        let lines := ShellCheck.Formatter.GCC.formatResultWithContents cf.result cf.contents
        for line in lines do
          IO.println line
  | .tty =>
      let color := ShellCheck.Formatter.TTY.getColorFunc useColor
      for cf in checkedFiles do
        let lines := ShellCheck.Formatter.TTY.formatResultWithSource color cf.result cf.contents
        for line in lines do
          IO.println line
      let allComments := checkedFiles.flatMap (fun cf => cf.result.crComments)
      for line in ShellCheck.Formatter.TTY.formatFooter color formatterOptions allComments do
        IO.println line
  | .json =>
      IO.println (ShellCheck.Formatter.JSON.formatResults results)
  | .quiet =>
      pure ()
  | .checkstyle =>
      IO.println (ShellCheck.Formatter.CheckStyle.formatResults results)
  | .diff =>
      let color :=
        if useColor then ShellCheck.Formatter.Diff.colorize else ShellCheck.Formatter.Diff.noColor
      for cf in checkedFiles do
        if let some diff := ShellCheck.Formatter.Diff.formatResultDiff color cf.result cf.contents then
          IO.println diff

  pure (if hasIssues then 1 else 0)

def shellcheck4Cmd : Cmd := `[Cli|
  shellcheck4 VIA runShellcheck4; [shellcheckVersion]
  "ShellCheck Lean 4 port"

  FLAGS:
    debug;                   "Enable debug output."
    a, "check-sourced";      "Include warnings from sourced files."
    C, color : ColorOption;  "Use color (auto, always, never)."
    f, format : OutputFormat; "Output format (gcc, tty, json, quiet, checkstyle, diff)."
    i, "include" : Array ScCode; "Consider only given types of warnings (comma-separated)."
    e, exclude : Array ScCode; "Exclude types of warnings (comma-separated)."
    "extended-analysis";        "Perform extended dataflow analysis."
    "list-optional";          "List checks disabled by default."
    norc;                     "Don't look for .shellcheckrc files."
    rcfile : String;          "Prefer the specified configuration file over searching for one."
    o, enable : Array String; "List of optional checks to enable (or 'all')."
    P, "source-path" : String; "Specify path when looking for sourced files."
    s, shell : Shell;         "Specify shell dialect (sh, bash, dash, ksh, busybox)."
    S, severity : Severity;   "Minimum severity (error, warning, info, style)."
    W, "wiki-link-count" : Nat; "Number of wiki links to show, when applicable."
    x, "external-sources";    "Allow 'source' outside of FILES."

  ARGS:
    ...files : String;  "Input files to check."

  EXTENSIONS:
    defaultValues! #[("format", "tty"), ("color", "auto"), ("wiki-link-count", "3")]
]

def main (args : List String) : IO UInt32 :=
  shellcheck4Cmd.validate (preprocessArgs args)
