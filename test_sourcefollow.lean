import ShellCheck.Parser.SourceFollow

open ShellCheck.Parser.SourceFollow

#eval do
  IO.println "--- Source Command Detection ---"
  IO.println s!"isSourceCommand 'source' = {isSourceCommand "source"}"
  IO.println s!"isSourceCommand '.' = {isSourceCommand "."}"
  IO.println s!"isSourceCommand 'echo' = {isSourceCommand "echo"}"

  IO.println s!"startsWithSource 'source foo.sh' = {startsWithSource "source foo.sh"}"
  IO.println s!"startsWithSource '. ./lib.sh' = {startsWithSource ". ./lib.sh"}"
  IO.println s!"startsWithSource 'echo hi' = {startsWithSource "echo hi"}"

#eval do
  IO.println "\n--- Variable Detection ---"
  IO.println s!"hasVariableRef 'foo.sh' = {hasVariableRef "foo.sh"}"
  IO.println s!"hasVariableRef './lib.sh' = {hasVariableRef "./lib.sh"}"
  IO.println s!"hasVariableRef '$HOME/.bashrc' = {hasVariableRef "$HOME/.bashrc"}"
  IO.println s!"hasVariableRef (with braces) = {hasVariableRef "${DIR}/file.sh"}"

#eval do
  IO.println "\n--- Path Operations ---"
  IO.println s!"isAbsolutePath '/etc/profile' = {isAbsolutePath "/etc/profile"}"
  IO.println s!"isAbsolutePath '~/bashrc' = {isAbsolutePath "~/bashrc"}"
  IO.println s!"isAbsolutePath './lib.sh' = {isAbsolutePath "./lib.sh"}"
  IO.println s!"isAbsolutePath 'lib.sh' = {isAbsolutePath "lib.sh"}"

  IO.println s!"dirName '/home/user/script.sh' = {dirName "/home/user/script.sh"}"
  IO.println s!"dirName 'script.sh' = {dirName "script.sh"}"
  IO.println s!"dirName './lib/util.sh' = {dirName "./lib/util.sh"}"

  IO.println s!"joinPath '/home/user' 'lib.sh' = {joinPath "/home/user" "lib.sh"}"
  IO.println s!"joinPath '/home/user/' 'lib.sh' = {joinPath "/home/user/" "lib.sh"}"
  IO.println s!"joinPath '/home/user' '/etc/profile' = {joinPath "/home/user" "/etc/profile"}"

#eval do
  IO.println "\n--- Path Normalization ---"
  IO.println s!"normalizePath '/home/user/../other' = {normalizePath "/home/user/../other"}"
  IO.println s!"normalizePath '/home/./user' = {normalizePath "/home/./user"}"
  IO.println s!"normalizePath './lib/../util/file.sh' = {normalizePath "./lib/../util/file.sh"}"
  IO.println s!"normalizePath '/a/b/c/../../d' = {normalizePath "/a/b/c/../../d"}"

#eval do
  IO.println "\n--- Source Path Resolution ---"
  IO.println s!"resolveSourcePath '/home/user/main.sh' 'lib.sh' = {resolveSourcePath "/home/user/main.sh" "lib.sh"}"
  IO.println s!"resolveSourcePath '/home/user/main.sh' './lib/util.sh' = {resolveSourcePath "/home/user/main.sh" "./lib/util.sh"}"
  IO.println s!"resolveSourcePath '/home/user/main.sh' '../common/lib.sh' = {resolveSourcePath "/home/user/main.sh" "../common/lib.sh"}"
  IO.println s!"resolveSourcePath '/home/user/main.sh' '/etc/profile' = {resolveSourcePath "/home/user/main.sh" "/etc/profile"}"

#eval do
  IO.println "\n--- Parse Source Commands ---"
  let cmd1 := parseSourceCommand ["source", "lib.sh"]
  let cmd2 := parseSourceCommand [".", "./util.sh"]
  let cmd3 := parseSourceCommand ["source", "$HOME/.bashrc"]
  let cmd4 := parseSourceCommand ["echo", "hello"]

  match cmd1 with
  | some c => IO.println s!"'source lib.sh': cmd={c.command}, path={c.filePath}, const={c.isConstant}"
  | none => IO.println "'source lib.sh': not a source command"

  match cmd2 with
  | some c => IO.println s!"'. ./util.sh': cmd={c.command}, path={c.filePath}, const={c.isConstant}"
  | none => IO.println "'. ./util.sh': not a source command"

  match cmd3 with
  | some c => IO.println s!"'source $HOME/.bashrc': cmd={c.command}, path={c.filePath}, const={c.isConstant}"
  | none => IO.println "'source $HOME/.bashrc': not a source command"

  match cmd4 with
  | some c => IO.println s!"'echo hello': cmd={c.command}, path={c.filePath}, const={c.isConstant}"
  | none => IO.println "'echo hello': not a source command"

#eval do
  IO.println "\n--- Source State & Cycle Detection ---"
  let state := SourceState.initial "/home/user"
  IO.println s!"Initial depth: {state.depth}"
  IO.println s!"hasVisited '/foo' = {state.hasVisited "/foo"}"

  let state2 := state.addVisited "/foo"
  IO.println s!"After adding '/foo': hasVisited '/foo' = {state2.hasVisited "/foo"}"

  let state3 := state2.incrementDepth
  IO.println s!"After incrementDepth: depth = {state3.depth}"

  IO.println s!"atMaxDepth (depth=0) = {state.atMaxDepth}"

#eval do
  IO.println "\n--- Can Follow Checks ---"
  let state := SourceState.initial
  let cmd := { command := "source", filePath := "lib.sh", isConstant := true : SourceCommand }
  let result := canFollow state cmd "/home/user/main.sh"
  IO.println s!"Can follow 'source lib.sh': {result.canFollow}"
  match result.resolvedPath with
  | some p => IO.println s!"  Resolved path: {p}"
  | none => IO.println "  No resolved path"

  let cmdVar := { command := "source", filePath := "$DIR/lib.sh", isConstant := false : SourceCommand }
  let resultVar := canFollow state cmdVar "/home/user/main.sh"
  IO.println s!"Can follow 'source $DIR/lib.sh': {resultVar.canFollow}"
  match resultVar.reason with
  | some r => IO.println s!"  Reason: {r}"
  | none => pure ()

  -- Test cycle detection
  let stateWithVisit := state.addVisited "/home/user/lib.sh"
  let cmdCycle := { command := "source", filePath := "lib.sh", isConstant := true : SourceCommand }
  let resultCycle := canFollow stateWithVisit cmdCycle "/home/user/main.sh"
  IO.println s!"Can follow (cycle): {resultCycle.canFollow}"
  match resultCycle.reason with
  | some r => IO.println s!"  Reason: {r}"
  | none => pure ()

#eval do
  IO.println "\n--- Error Codes & Messages ---"
  IO.println s!"SC1090 = {SC1090}"
  IO.println s!"SC1091 = {SC1091}"
  IO.println s!"SC1094 = {SC1094}"

  IO.println s!"notConstant code: {sourceResultToCode .notConstant}"
  IO.println s!"notConstant msg: {sourceResultToMessage .notConstant}"
  IO.println s!"notFound msg: {sourceResultToMessage (.notFound "/missing.sh")}"
  IO.println s!"cycleDetected msg: {sourceResultToMessage (.cycleDetected "/circular.sh")}"

#eval do
  IO.println "\n--- Find Source Commands in Script ---"
  let script := "#!/bin/bash
source ./lib.sh
echo hello
. /etc/profile
source $HOME/.bashrc"
  let cmds := findAllSourceCommands script
  IO.println s!"Found {cmds.length} source commands:"
  for cmd in cmds do
    IO.println s!"  {cmd.command} {cmd.filePath} (const={cmd.isConstant})"

#eval do
  IO.println "\n--- Common Non-Constant Patterns ---"
  IO.println s!"matchesNonConstantPattern '$HOME/.bashrc' = {matchesNonConstantPattern "$HOME/.bashrc"}"
  IO.println s!"matchesNonConstantPattern './lib.sh' = {matchesNonConstantPattern "./lib.sh"}"
  IO.println s!"matchesNonConstantPattern (BASH_SOURCE) = {matchesNonConstantPattern "${BASH_SOURCE[0]}"}"
