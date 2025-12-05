/-
  Source file following for ShellCheck parser
  Handles `source file` and `. file` commands with cycle detection
-/

import ShellCheck.Interface

namespace ShellCheck.Parser.SourceFollow

open ShellCheck.Interface

/-- Check if a string contains a substring -/
def containsSubstr (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Maximum recursion depth for source following (matches Haskell: 100) -/
def maxSourceDepth : Nat := 100

/-- Result of attempting to follow a source command -/
inductive SourceResult where
  | success : String → SourceResult       -- File content successfully read
  | notFound : String → SourceResult      -- File not found
  | cycleDetected : String → SourceResult -- Circular inclusion detected
  | tooDeep : SourceResult                -- Exceeded max depth
  | notConstant : SourceResult            -- Path is not a constant (contains variables)
  | error : String → SourceResult         -- Other error
  deriving Repr, Inhabited

/-- State for tracking source file following -/
structure SourceState where
  /-- Files already visited (absolute paths) for cycle detection -/
  visitedFiles : List String
  /-- Current recursion depth -/
  depth : Nat
  /-- Base directory for relative path resolution -/
  baseDir : String
  deriving Repr, Inhabited

/-- Create initial source state -/
def SourceState.initial (baseDir : String := ".") : SourceState :=
  { visitedFiles := [], depth := 0, baseDir }

/-- Check if a path has already been visited -/
def SourceState.hasVisited (state : SourceState) (path : String) : Bool :=
  state.visitedFiles.contains path

/-- Add a path to visited files -/
def SourceState.addVisited (state : SourceState) (path : String) : SourceState :=
  { state with visitedFiles := path :: state.visitedFiles }

/-- Increment depth -/
def SourceState.incrementDepth (state : SourceState) : SourceState :=
  { state with depth := state.depth + 1 }

/-- Check if we're at max depth -/
def SourceState.atMaxDepth (state : SourceState) : Bool :=
  state.depth >= maxSourceDepth

/-- Parsed source command -/
structure SourceCommand where
  /-- The command used ("source" or ".") -/
  command : String
  /-- The file path argument -/
  filePath : String
  /-- Whether the path is constant (no variable expansion needed) -/
  isConstant : Bool
  deriving Repr, Inhabited

/-- Check if a string starts with a source command -/
def startsWithSource (s : String) : Bool :=
  s.startsWith "source " || s.startsWith ". "

/-- Check if a word is the source command -/
def isSourceCommand (word : String) : Bool :=
  word == "source" || word == "."

/-- Check if a path contains variable references -/
def hasVariableRef (path : String) : Bool :=
  path.any (· == '$') || containsSubstr path "${"

/-- Check if a path is absolute -/
def isAbsolutePath (path : String) : Bool :=
  path.startsWith "/" || path.startsWith "~"

/-- Simple path joining (not handling all edge cases) -/
def joinPath (base : String) (rel : String) : String :=
  if isAbsolutePath rel then rel
  else if base.endsWith "/" then base ++ rel
  else base ++ "/" ++ rel

/-- Get directory part of a path -/
def dirName (path : String) : String :=
  let chars := path.toList.reverse
  match chars.dropWhile (· != '/') with
  | [] => "."
  | _ :: rest => String.ofList rest.reverse

/-- Normalize path by removing redundant elements -/
partial def normalizePath (path : String) : String :=
  let parts := path.splitOn "/"
  let rec go (stack : List String) (remaining : List String) : List String :=
    match remaining with
    | [] => stack.reverse
    | "." :: rest => go stack rest
    | ".." :: rest =>
        match stack with
        | [] => go [".."] rest  -- Can't go above root
        | _ :: stackRest => go stackRest rest
    | "" :: rest =>
        if stack.isEmpty then go [""] rest  -- Keep leading /
        else go stack rest                   -- Skip empty
    | part :: rest => go (part :: stack) rest
  String.intercalate "/" (go [] parts)

/-- Parse a source command from a simple command structure -/
def parseSourceCommand (words : List String) : Option SourceCommand :=
  match words with
  | cmd :: path :: _ =>
      if isSourceCommand cmd then
        some {
          command := cmd,
          filePath := path,
          isConstant := !hasVariableRef path
        }
      else none
  | _ => none

/-- Resolve a source path relative to a base file -/
def resolveSourcePath (baseFile : String) (sourcePath : String) : String :=
  if isAbsolutePath sourcePath then
    normalizePath sourcePath
  else
    normalizePath (joinPath (dirName baseFile) sourcePath)

/-- Result of checking if we can follow a source -/
structure CanFollowResult where
  canFollow : Bool
  reason : Option String
  resolvedPath : Option String
  deriving Repr, Inhabited

/-- Check if we can follow a source command -/
def canFollow (state : SourceState) (cmd : SourceCommand) (currentFile : String) : CanFollowResult :=
  if !cmd.isConstant then
    { canFollow := false, reason := some "Non-constant source path", resolvedPath := none }
  else if state.atMaxDepth then
    { canFollow := false, reason := some s!"Max source depth ({maxSourceDepth}) exceeded", resolvedPath := none }
  else
    let resolved := resolveSourcePath currentFile cmd.filePath
    if state.hasVisited resolved then
      { canFollow := false, reason := some s!"Circular inclusion: {resolved}", resolvedPath := some resolved }
    else
      { canFollow := true, reason := none, resolvedPath := some resolved }

/-- Information about a followed source file -/
structure FollowedSource where
  /-- Original command -/
  command : SourceCommand
  /-- Resolved absolute path -/
  resolvedPath : String
  /-- Result of following -/
  result : SourceResult
  /-- Updated state after following -/
  newState : SourceState
  deriving Repr, Inhabited

/-- Common source file patterns that should be warned about -/
def commonNonConstantPatterns : List String :=
  [ "$HOME/.bashrc"
  , "$HOME/.bash_profile"
  , "${HOME}/.bashrc"
  , "$0"
  , "${0}"
  , "${BASH_SOURCE[0]}"
  , "$(dirname $0)"
  ]

/-- Check if path matches a common non-constant pattern -/
def matchesNonConstantPattern (path : String) : Bool :=
  commonNonConstantPatterns.any (containsSubstr path ·)

/-- ShellCheck error codes for source following -/
def SC1090 : Code := 1090  -- Can't follow non-constant source
def SC1091 : Code := 1091  -- Not following: (error message)
def SC1094 : Code := 1094  -- Parsing of sourced file failed

/-- Get error code for source result -/
def sourceResultToCode : SourceResult → Code
  | .success _ => 0  -- No error
  | .notFound _ => SC1091
  | .cycleDetected _ => SC1091
  | .tooDeep => SC1091
  | .notConstant => SC1090
  | .error _ => SC1091

/-- Get error message for source result -/
def sourceResultToMessage : SourceResult → String
  | .success _ => ""
  | .notFound path => s!"Not following: {path} (file not found)"
  | .cycleDetected path => s!"Not following: {path} (circular inclusion)"
  | .tooDeep => s!"Not following: source depth exceeds {maxSourceDepth}"
  | .notConstant => "Can't follow non-constant source"
  | .error msg => s!"Not following: {msg}"

/-- Extract source commands from a list of words (simple tokenization) -/
def findSourceCommands (words : List (List String)) : List SourceCommand :=
  words.filterMap parseSourceCommand

/-- Simple word splitter for testing -/
def splitIntoWords (line : String) : List String :=
  line.splitOn " " |>.filter (· != "")

/-- Find all source commands in script content -/
def findAllSourceCommands (content : String) : List SourceCommand :=
  let lines := content.splitOn "\n"
  let wordLists := lines.map splitIntoWords
  findSourceCommands wordLists

/-- Information about source tracking for a parsed script -/
structure SourceTracking where
  /-- All source commands found -/
  sourceCommands : List SourceCommand
  /-- Successfully followed files -/
  followedFiles : List String
  /-- Files that couldn't be followed (with reasons) -/
  unfollowedFiles : List (String × String)
  /-- Current state -/
  state : SourceState
  deriving Repr, Inhabited

/-- Create empty source tracking -/
def SourceTracking.empty : SourceTracking :=
  { sourceCommands := []
  , followedFiles := []
  , unfollowedFiles := []
  , state := SourceState.initial
  }

end ShellCheck.Parser.SourceFollow
