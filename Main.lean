import ShellCheck
import ShellCheck.Checker
import ShellCheck.Parser
import ShellCheck.Formatter.GCC
import ShellCheck.Formatter.Format

open ShellCheck.Interface
open ShellCheck.Checker
open ShellCheck.Formatter.Format
open ShellCheck.Formatter.GCC

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

/-- Format severity for output -/
def formatSeverity (sev : Severity) : String :=
  match sev with
  | .errorC => "error"
  | .warningC => "warning"
  | .infoC => "note"
  | .styleC => "style"

/-- Format a positioned comment for output -/
def formatComment' (pc : PositionedComment) : String :=
  let file := pc.pcStartPos.posFile
  let line := pc.pcStartPos.posLine
  let col := pc.pcStartPos.posColumn
  let sev := formatSeverity pc.pcComment.cSeverity
  let code := pc.pcComment.cCode
  let msg := pc.pcComment.cMessage
  s!"{file}:{line}:{col}: {sev}: {msg} [SC{code}]"

/-- Check a single file and print results -/
def checkFile (filename : String) (debug : Bool := false) : IO UInt32 := do
  -- Read the file
  let contents ← IO.FS.readFile filename

  if debug then
    IO.eprintln s!"[DEBUG] Read {contents.length} bytes from {filename}"

  -- Create check spec
  let spec : CheckSpec := {
    csFilename := filename
    csScript := contents
    csCheckSourced := false
    csIgnoreRC := true
    csShellTypeOverride := none
    csIncludedWarnings := none
    csExcludedWarnings := []
    csMinSeverity := .styleC
    csOptionalChecks := []
    csExtendedAnalysis := none
  }

  -- First let's check if parsing works
  if debug then
    let parseSpec : ShellCheck.Interface.ParseSpec := {
      psFilename := filename
      psScript := contents
      psCheckSourced := false
      psIgnoreRC := true
      psShellTypeOverride := none
    }
    let parseResult ← ShellCheck.Parser.parseScript ioSystemInterface parseSpec
    IO.eprintln s!"[DEBUG] Parse result has root: {parseResult.prRoot.isSome}"
    IO.eprintln s!"[DEBUG] Token positions count: {parseResult.prTokenPositions.size}"
    -- Dump first few tokens
    match parseResult.prRoot with
    | some root =>
      let rootType := match root.inner with | .T_Script _ _ => "T_Script" | _ => "other"
      IO.eprintln s!"[DEBUG] Root token type: {rootType}"
      -- Collect and show token types
      let showToken (t : ShellCheck.AST.Token) : String :=
        match t.inner with
        | .T_Script _ _ => "T_Script"
        | .T_SimpleCommand _ ws => s!"T_SimpleCommand({ws.length} words)"
        | .T_Literal s => s!"T_Literal({s.take 20})"
        | .T_DollarBraced _ _ => "T_DollarBraced"
        | .T_Backticked _ => "T_Backticked"
        | .T_DoubleQuoted _ => "T_DoubleQuoted"
        | .T_SingleQuoted s => s!"T_SingleQuoted({s.take 10})"
        | .T_Function _ _ name _ => s!"T_Function({name})"
        | .T_BraceGroup _ => "T_BraceGroup"
        | .T_Redirecting _ _ => "T_Redirecting"
        | _ => "other"
      let tokenTypes := match root.inner with
        | .T_Script _ cs =>
          cs.take 10 |>.map fun cmd =>
            let cmdType := showToken cmd
            match cmd.inner with
            | .T_SimpleCommand _ ws =>
              let wordStrs := ws.map showToken
              s!"{cmdType}[{String.intercalate ", " wordStrs}]"
            | _ => cmdType
        | _ => ["not a script"]
      IO.eprintln s!"[DEBUG] Commands: {tokenTypes}"
    | none => pure ()

  -- Run the checker
  let result ← checkScript ioSystemInterface spec

  if debug then
    IO.eprintln s!"[DEBUG] Got {result.crComments.length} comments"

  -- Print results
  for comment in result.crComments do
    IO.println (formatComment' comment)

  -- Return exit code based on whether issues were found
  if result.crComments.isEmpty then
    if debug then
      IO.eprintln "[DEBUG] No issues found"
    pure 0
  else
    pure 1

/-- Print usage information -/
def printUsage : IO Unit := do
  IO.println "ShellCheck Lean4 port"
  IO.println ""
  IO.println "Usage: shellcheck4 [OPTIONS] FILE..."
  IO.println ""
  IO.println "Options:"
  IO.println "  --help      Show this help"
  IO.println "  --version   Show version"
  IO.println ""
  IO.println "Note: This is a work-in-progress port. Many checks are stubs."

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    printUsage
    pure 0
  | ["--help"] =>
    printUsage
    pure 0
  | ["--version"] =>
    IO.println "shellcheck4 0.1.0 (Lean 4 port)"
    pure 0
  | _ =>
    let debug := args.contains "--debug"
    let files := args.filter (fun a => !a.startsWith "--")
    if files.isEmpty then
      printUsage
      pure 0
    else
      let mut exitCode : UInt32 := 0
      for file in files do
        try
          let code ← checkFile file debug
          if code != 0 then
            exitCode := 1
        catch e =>
          IO.eprintln s!"{file}: {e}"
          exitCode := 1
      pure exitCode
