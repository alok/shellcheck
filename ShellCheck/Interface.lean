/-
  Copyright 2012-2024 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Public interface types for ShellCheck
-/

import ShellCheck.AST
import ShellCheck.Data
import Std.Data.HashMap

namespace ShellCheck.Interface

-- Re-export Shell from Data for public API
export ShellCheck.Data (Shell)

/-- Execution mode: whether script is being executed or sourced -/
inductive ExecutionMode where
  | executed  -- Script is being run directly
  | sourced   -- Script is being sourced by another script
  deriving Repr, BEq, Inhabited

/-- Error message type -/
abbrev ErrorMessage := String

/-- ShellCheck warning/error code -/
abbrev Code := Int

/-- Severity level for ShellCheck messages -/
inductive Severity where
  | errorC    -- Error: will cause script to fail
  | warningC  -- Warning: likely a bug
  | infoC     -- Info: might be an issue
  | styleC    -- Style: could be improved
  deriving Repr, BEq, Ord, Inhabited

/-- Position in source file -/
structure Position where
  posFile : String    -- Filename
  posLine : Nat       -- 1-based source line
  posColumn : Nat     -- 1-based source column (tabs count as 8)
  deriving Repr, BEq, Ord, Inhabited

/-- Default position -/
def newPosition : Position := {
  posFile := ""
  posLine := 1
  posColumn := 1
}

/-- A ShellCheck comment/warning -/
structure Comment where
  cSeverity : Severity
  cCode : Code
  cMessage : String
  deriving Repr, BEq, Inhabited

/-- Default comment -/
def newComment : Comment := {
  cSeverity := .styleC
  cCode := 0
  cMessage := ""
}

/-- Where to insert replacement text -/
inductive InsertionPoint where
  | insertBefore
  | insertAfter
  deriving Repr, BEq, Inhabited

/-- A text replacement for auto-fix -/
structure Replacement where
  repStartPos : Position
  repEndPos : Position
  repString : String
  repPrecedence : Int  -- Higher precedence = applied first
  repInsertionPoint : InsertionPoint
  deriving Repr, BEq, Inhabited

/-- Default replacement -/
def newReplacement : Replacement := {
  repStartPos := newPosition
  repEndPos := newPosition
  repString := ""
  repPrecedence := 1
  repInsertionPoint := .insertAfter
}

/-- A fix consisting of one or more replacements -/
structure Fix where
  fixReplacements : List Replacement
  deriving Repr, BEq, Inhabited

/-- Default fix -/
def newFix : Fix := {
  fixReplacements := []
}

/-- A comment with position information -/
structure PositionedComment where
  pcStartPos : Position
  pcEndPos : Position
  pcComment : Comment
  pcFix : Option Fix
  deriving Repr, BEq, Inhabited

/-- Default positioned comment -/
def newPositionedComment : PositionedComment := {
  pcStartPos := newPosition
  pcEndPos := newPosition
  pcComment := newComment
  pcFix := none
}

/-- A comment attached to a specific token -/
structure TokenComment where
  tcId : AST.Id
  tcComment : Comment
  tcFix : Option Fix
  deriving Repr, BEq, Inhabited

/-- Default token comment -/
def newTokenComment : TokenComment := {
  tcId := ⟨0⟩
  tcComment := newComment
  tcFix := none
}

/-- Color output option -/
inductive ColorOption where
  | colorAuto    -- Detect from terminal
  | colorAlways  -- Always use color
  | colorNever   -- Never use color
  deriving Repr, BEq, Ord, Inhabited

/-- Token position map: maps token IDs to (start, end) positions -/
abbrev TokenPositions := Std.HashMap AST.Id (Position × Position)

-- Spec and Result types

/-- Input specification for the checker -/
structure CheckSpec where
  csFilename : String
  csScript : String
  csCheckSourced : Bool
  csIgnoreRC : Bool
  csExcludedWarnings : List Int
  csIncludedWarnings : Option (List Int)
  csShellTypeOverride : Option Shell
  csMinSeverity : Severity
  csExtendedAnalysis : Option Bool
  csOptionalChecks : List String
  deriving Repr, Inhabited

/-- Default check spec -/
def emptyCheckSpec : CheckSpec := {
  csFilename := ""
  csScript := ""
  csCheckSourced := false
  csIgnoreRC := false
  csExcludedWarnings := []
  csIncludedWarnings := none
  csShellTypeOverride := none
  csMinSeverity := .styleC
  csExtendedAnalysis := none
  csOptionalChecks := []
}

/-- Output from the checker -/
structure CheckResult where
  crFilename : String
  crComments : List PositionedComment
  deriving Repr, Inhabited

/-- Default check result -/
def emptyCheckResult : CheckResult := {
  crFilename := ""
  crComments := []
}

/-- Input specification for the parser -/
structure ParseSpec where
  psFilename : String
  psScript : String
  psCheckSourced : Bool
  psIgnoreRC : Bool
  psShellTypeOverride : Option Shell
  deriving Repr, Inhabited

/-- Default parse spec -/
def newParseSpec : ParseSpec := {
  psFilename := ""
  psScript := ""
  psCheckSourced := false
  psIgnoreRC := false
  psShellTypeOverride := none
}

/-- Output from the parser -/
structure ParseResult where
  prComments : List PositionedComment
  prTokenPositions : TokenPositions
  prRoot : Option AST.Token
  deriving Inhabited

/-- Default parse result -/
def newParseResult : ParseResult := {
  prComments := []
  prTokenPositions := {}
  prRoot := none
}

/-- Input specification for the analyzer -/
structure AnalysisSpec where
  asScript : AST.Token
  asShellType : Option Shell
  asFallbackShell : Option Shell
  asExecutionMode : ExecutionMode
  asCheckSourced : Bool
  asOptionalChecks : List String
  asExtendedAnalysis : Option Bool
  asTokenPositions : TokenPositions
  deriving Inhabited

/-- Create a new analysis spec for a token -/
def newAnalysisSpec (token : AST.Token) : AnalysisSpec := {
  asScript := token
  asShellType := none
  asFallbackShell := none
  asExecutionMode := .executed
  asCheckSourced := false
  asOptionalChecks := []
  asExtendedAnalysis := none
  asTokenPositions := {}
}

/-- Output from the analyzer -/
structure AnalysisResult where
  arComments : List TokenComment
  deriving Repr, Inhabited

/-- Default analysis result -/
def newAnalysisResult : AnalysisResult := {
  arComments := []
}

/-- Options for output formatters -/
structure FormatterOptions where
  foColorOption : ColorOption
  foWikiLinkCount : Nat
  deriving Repr, Inhabited

/-- Default formatter options -/
def newFormatterOptions : FormatterOptions := {
  foColorOption := .colorAuto
  foWikiLinkCount := 3
}

/-- Description of an optional check -/
structure CheckDescription where
  cdName : String
  cdDescription : String
  cdPositive : String  -- Example that triggers the check
  cdNegative : String  -- Example that doesn't trigger
  deriving Repr, Inhabited

/-- Default check description -/
def newCheckDescription : CheckDescription := {
  cdName := ""
  cdDescription := ""
  cdPositive := ""
  cdNegative := ""
}

/-- System interface for file I/O operations -/
structure SystemInterface (m : Type → Type) where
  /-- Read a file given:
      - What annotations say about external files (if anything)
      - A resolved filename
      Returns file contents or error message -/
  siReadFile : Option Bool → String → m (Except ErrorMessage String)
  /-- Find a source file given:
      - Current script path
      - Annotation setting for external files
      - Source-path annotations in effect
      - The sourced filename
      Returns resolved path -/
  siFindSource : String → Option Bool → List String → String → m String
  /-- Get config file (name, contents) for a filename -/
  siGetConfig : String → m (Option (String × String))

/-- Default system interface that does nothing -/
def newSystemInterface [Monad m] : SystemInterface m := {
  siReadFile := fun _ _ => pure (.error "Not implemented")
  siFindSource := fun _ _ _ name => pure name
  siGetConfig := fun _ => pure none
}

/-- Create a mocked system interface for testing -/
def mockedSystemInterface (files : List (String × String)) : SystemInterface Id := {
  siReadFile := fun _ file =>
    match files.find? (fun p => p.1 == file) with
    | some (_, contents) => pure (.ok contents)
    | none => pure (.error "File not included in mock.")
  siFindSource := fun _ _ _ file => pure file
  siGetConfig := fun _ => pure none
}

/-- Add RC file to a mocked interface -/
def mockRcFile [Pure m] (rcfile : String) (mock : SystemInterface m) : SystemInterface m := {
  mock with
  siGetConfig := fun _ => pure (some (".shellcheckrc", rcfile))
}

-- Theorems (stubs)

theorem newPosition_valid :
    newPosition.posLine ≥ 1 ∧ newPosition.posColumn ≥ 1 := by decide

theorem emptyCheckSpec_no_exclusions :
    emptyCheckSpec.csExcludedWarnings = [] := rfl

theorem emptyCheckResult_no_comments :
    emptyCheckResult.crComments = [] := rfl

theorem newParseResult_no_root :
    newParseResult.prRoot = none := rfl

theorem newAnalysisResult_no_comments :
    newAnalysisResult.arComments = [] := rfl

/-- Severity comparison -/
theorem Severity_ordering : True := trivial  -- Placeholder

/-- Position ordering is transitive -/
theorem Position_ordering : True := trivial  -- Placeholder

end ShellCheck.Interface
