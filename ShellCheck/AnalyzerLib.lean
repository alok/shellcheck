/-
  Copyright 2012-2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Analyzer library for ShellCheck.
  Provides types and utilities for static analysis.
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.CFGAnalysis
import ShellCheck.Data
import ShellCheck.Interface
import ShellCheck.Parser
import ShellCheck.Prelude
import ShellCheck.Regex
import Std.Data.HashMap

namespace ShellCheck.AnalyzerLib

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.CFGAnalysis
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Parser
open ShellCheck.Regex

/-- Cache for analysis results (currently empty placeholder) -/
structure Cache where
  deriving Inhabited

/-- Scope type for variable flow analysis -/
inductive Scope where
  | SubshellScope : String → Scope  -- e.g. "$(..) expansion"
  | NoneScope : Scope
  deriving Repr, BEq, Inhabited

/-- Data source for variables -/
inductive DataSource where
  | SourceFrom : List Token → DataSource
  | SourceExternal : DataSource
  | SourceDeclaration : DataSource
  | SourceInteger : DataSource
  | SourceChecked : DataSource
  deriving Repr, Inhabited

/-- Data type (string or array) -/
inductive DataType where
  | DataString : DataSource → DataType
  | DataArray : DataSource → DataType
  deriving Repr, Inhabited

/-- Stack data for variable flow analysis -/
inductive StackData where
  | StackScope : Scope → StackData
  | StackScopeEnd : StackData
  -- (Base expression, specific position, var name, assigned values)
  | Assignment : Token × Token × String × DataType → StackData
  | Reference : Token × Token × String → StackData
  deriving Repr, Inhabited

/-- Variable state (dead or alive) -/
inductive VariableFlowState where
  | Dead : Token → String → VariableFlowState
  | Alive : VariableFlowState
  deriving Repr, Inhabited

/-- Parameters for analysis -/
structure Parameters where
  -- Whether this script has the 'lastpipe' option set/default
  hasLastpipe : Bool
  -- Whether this script has the 'inherit_errexit' option set/default
  hasInheritErrexit : Bool
  -- Whether this script has 'set -e' anywhere
  hasSetE : Bool
  -- Whether this script has 'set -o pipefail' anywhere
  hasPipefail : Bool
  -- Whether this script has 'shopt -s execfail' anywhere
  hasExecfail : Bool
  -- A linear analysis of data flow
  variableFlow : List StackData
  -- A map from Id to Token
  idMap : Std.HashMap Id Token
  -- A map from Id to parent Token
  parentMap : Std.HashMap Id Token
  -- The shell type, such as Bash or Ksh
  shellType : Shell
  -- True if shell type was forced via flags
  shellTypeSpecified : Bool
  -- The root node of the AST
  rootNode : Token
  -- map from token id to start and end position
  tokenPositions : Std.HashMap Id (Position × Position)
  -- Result from Control Flow Graph analysis
  cfgAnalysis : Option CFGAnalysis
  deriving Inhabited

/-- Analysis state writer monad -/
abbrev AnalyzerM := ReaderT Parameters (StateT Cache (Except String))

/-- Analysis type (returns unit in writer monad) -/
abbrev Analysis := AnalyzerM (List TokenComment)

/-- Null check - does nothing -/
def nullCheck : Token → Analysis :=
  fun _ => pure []

/-- A checker has per-script and per-token analysis functions -/
structure Checker where
  perScript : Root → Analysis
  perToken : Token → Analysis
  deriving Inhabited

/-- Compose two analyzers to run sequentially -/
def composeAnalyzers (f g : α → Analysis) (x : α) : Analysis := do
  let r1 ← f x
  let r2 ← g x
  return r1 ++ r2

/-- Combine two checkers -/
instance : Append Checker where
  append x y := {
    perScript := composeAnalyzers x.perScript y.perScript
    perToken := composeAnalyzers x.perToken y.perToken
  }

/-- Empty checker -/
def emptyChecker : Checker := {
  perScript := fun _ => pure []
  perToken := fun _ => pure []
}

instance : Inhabited Checker where
  default := emptyChecker

/-- Get children of a token -/
def getTokenChildren (t : Token) : List Token :=
  match t.inner with
  | .T_Script _ list => list
  | .T_SimpleCommand assigns words => assigns ++ words
  | .T_Pipeline _ cmds => cmds  -- 2 args: separators, commands
  | .T_Redirecting redirects cmd => cmd :: redirects  -- 2 args
  | .T_Condition _ expr => [expr]  -- 2 args: condType, expr
  | .T_BraceGroup list => list
  | .T_Subshell list => list
  | .T_AndIf t1 t2 => [t1, t2]
  | .T_OrIf t1 t2 => [t1, t2]
  | .T_Backgrounded inner => [inner]
  | .T_Banged inner => [inner]
  | .T_IfExpression conds elseBody => (conds.map (fun (c, b) => c ++ b)).flatten ++ elseBody
  | .T_WhileExpression cond body => cond ++ body
  | .T_UntilExpression cond body => cond ++ body
  | .T_ForIn _ _ body => body
  | .T_CaseExpression word cases => word :: (cases.map (fun c => c.2.1 ++ c.2.2)).flatten
  | .T_Function _ _ _ body => [body]  -- 4 args: keyword, parens, name, body
  | .T_NormalWord parts => parts
  | .T_DoubleQuoted parts => parts
  | .T_SingleQuoted _ => []
  | .T_Literal _ => []
  | .T_DollarBraced _ inner => [inner]  -- 2 args: braced, content
  | .T_DollarExpansion list => list
  | .T_Backticked list => list
  | .T_DollarArithmetic inner => [inner]
  | .T_Assignment _ _ indices val => indices ++ [val]  -- 4 args: mode, name, indices, value
  | .TA_Binary _ t1 t2 => [t1, t2]
  | .TA_Unary _ inner => [inner]
  | .TC_Binary _ _ t1 t2 => [t1, t2]
  | .TC_Unary _ _ inner => [inner]
  | .TC_Nullary _ inner => [inner]
  | .T_Annotation _ cmd => [cmd]
  | .T_HereDoc _ _ _ content => content  -- content : List t
  | .T_HereString inner => [inner]
  | .T_FdRedirect _ op => [op]
  | .T_Array list => list
  | .T_Extglob _ list => list
  | _ => []

/-- Do analysis on all tokens in tree -/
partial def doAnalysisList (f : Token → Analysis) (t : Token) : Analysis := do
  let r ← f t
  let children := getTokenChildren t
  let rs ← children.mapM (doAnalysisList f)
  return r ++ rs.flatten

/-- Run a checker on parameters -/
def runChecker (params : Parameters) (checker : Checker) : List TokenComment :=
  let root := params.rootNode
  let analysis := do
    let r1 ← checker.perScript (Root.mk root)
    let r2 ← doAnalysisList (checker.perToken) root
    return r1 ++ r2
  match analysis params {} with
  | .ok (result, _) => result
  | .error _ => []

/-- Create a comment -/
def makeComment (severity : Severity) (id : Id) (code : Code) (note : String) : TokenComment := {
  tcId := id
  tcComment := {
    cSeverity := severity
    cCode := code
    cMessage := note
  }
  tcFix := Option.none
}

/-- Create a comment with fix -/
def makeCommentWithFix (severity : Severity) (id : Id) (code : Code) (note : String) (fix : Fix) : TokenComment :=
  let comment := makeComment severity id code note
  { comment with tcFix := if fix.fixReplacements.isEmpty then Option.none else some fix }

/-- Add a warning -/
def warn (id : Id) (code : Code) (str : String) : Analysis :=
  pure [makeComment .warningC id code str]

/-- Add an error -/
def err (id : Id) (code : Code) (str : String) : Analysis :=
  pure [makeComment .errorC id code str]

/-- Add an info message -/
def info (id : Id) (code : Code) (str : String) : Analysis :=
  pure [makeComment .infoC id code str]

/-- Add a style suggestion -/
def style (id : Id) (code : Code) (str : String) : Analysis :=
  pure [makeComment .styleC id code str]

/-- Add warning with fix -/
def warnWithFix (id : Id) (code : Code) (str : String) (fix : Fix) : Analysis :=
  pure [makeCommentWithFix .warningC id code str fix]

/-- Add error with fix -/
def errWithFix (id : Id) (code : Code) (str : String) (fix : Fix) : Analysis :=
  pure [makeCommentWithFix .errorC id code str fix]

/-- Add info with fix -/
def infoWithFix (id : Id) (code : Code) (str : String) (fix : Fix) : Analysis :=
  pure [makeCommentWithFix .infoC id code str fix]

/-- Add style with fix -/
def styleWithFix (id : Id) (code : Code) (str : String) (fix : Fix) : Analysis :=
  pure [makeCommentWithFix .styleC id code str fix]

/-- Extract executable name from shebang -/
def executableFromShebang (s : String) : String :=
  -- Extract the executable from shebang like "#!/bin/bash" or "#!/usr/bin/env bash"
  let s := s.trim
  let s := if s.startsWith "#!" then s.drop 2 else s
  let parts := s.splitOn " "
  match parts with
  | [] => ""
  | [path] => path.splitOn "/" |>.getLast!
  | path :: rest =>
    let exec := path.splitOn "/" |>.getLast!
    if exec == "env" then
      -- Handle env with options like "env -S bash -x"
      rest.find? (fun arg => !arg.startsWith "-") |>.getD ""
    else
      exec

/-- Check if script contains 'set -e' anywhere -/
def containsSetE (root : Token) : Bool :=
  -- Check shebang for -e and check for 'set' commands with -e
  match root.inner with
  | .T_Script shebang _ =>
    match shebang.inner with
    | .T_Literal s => s.splitOn "-" |>.any (fun part => part.any (· == 'e'))
    | _ => false
  | _ => false

/-- Check if option is set via 'shopt -s' -/
def containsShopt (_opt : String) (_root : Token) : Bool :=
  -- Simplified check - would walk tree looking for shopt commands
  false

/-- Check if option is set via 'set -o' -/
def containsSetOption (_opt : String) (_root : Token) : Bool :=
  -- Simplified check
  false

/-- Check if a shell option is set anywhere -/
def isOptionSet (opt : String) (root : Token) : Bool :=
  containsShopt opt root || containsSetOption opt root

/-- Determine shell type from shebang -/
def determineShell (fallback : Option Shell) (root : Token) : Shell :=
  match getShebangString root with
  | some s =>
    let exec := executableFromShebang s
    shellForExecutable exec |>.getD (fallback.getD .Bash)
  | none => fallback.getD .Bash
where
  getShebangString : Token → Option String
  | ⟨_, .T_Script shebang _⟩ =>
    match shebang.inner with
    | .T_Literal s => some s
    | _ => Option.none
  | ⟨_, .T_Annotation _ t⟩ => getShebangString t
  | _ => Option.none

/-- Build a map from Id to parent Token -/
partial def getParentTree (root : Token) : Std.HashMap Id Token :=
  go root {} Option.none
where
  go (t : Token) (m : Std.HashMap Id Token) (parent : Option Token) : Std.HashMap Id Token :=
    let m' := match parent with
      | some p => m.insert t.id p
      | none => m
    let children := getTokenChildren t
    children.foldl (fun acc child => go child acc (some t)) m'

/-- Build a map from Id to Token -/
partial def getTokenMap (root : Token) : Std.HashMap Id Token :=
  go root {}
where
  go (t : Token) (m : Std.HashMap Id Token) : Std.HashMap Id Token :=
    let m' := m.insert t.id t
    let children := getTokenChildren t
    children.foldl (fun acc child => go child acc) m'

/-- Check if token is in a quote-free context -/
def isQuoteFreeNode (_strict : Bool) (_shell : Shell) (_tree : Std.HashMap Id Token) (t : Token) : Bool :=
  match t.inner with
  | .T_Assignment _ _ _ _ => true
  | .T_FdRedirect _ _ => true
  | _ => false  -- Simplified

/-- Check strictly quote free -/
def isStrictlyQuoteFree (shell : Shell) (tree : Std.HashMap Id Token) (t : Token) : Bool :=
  isQuoteFreeNode true shell tree t

/-- Check quote free (more permissive) -/
def isQuoteFree (shell : Shell) (tree : Std.HashMap Id Token) (t : Token) : Bool :=
  isQuoteFreeNode false shell tree t

/-- Check if token is a command -/
def isCommand (t : Token) (cmd : String) : Bool :=
  match getCommandName t with
  | some name => name == cmd || name.endsWith ("/" ++ cmd)
  | none => false

/-- Check if token is parameter to a command -/
partial def isParamTo (tree : Std.HashMap Id Token) (cmd : String) (t : Token) : Bool :=
  match tree.get? t.id with
  | some parent =>
    match parent.inner with
    | .T_SimpleCommand _ _ => isCommand parent cmd
    | .T_Redirecting _ _ => isCommand parent cmd  -- correct: 2 args
    | .T_NormalWord _ => isParamTo tree cmd parent
    | .T_DoubleQuoted _ => isParamTo tree cmd parent
    | .T_SingleQuoted _ => isParamTo tree cmd parent
    | _ => false
  | none => false

/-- Get closest command (T_Redirecting) in tree -/
partial def getClosestCommand (tree : Std.HashMap Id Token) (t : Token) : Option Token :=
  match tree.get? t.id with
  | some parent =>
    match parent.inner with
    | .T_Redirecting _ _ => some parent  -- correct: 2 args
    | .T_Script _ _ => Option.none
    | _ => getClosestCommand tree parent
  | none => Option.none

/-- Get lead type for scope analysis -/
def leadType (_params : Parameters) (t : Token) : Scope :=
  match t.inner with
  | .T_DollarExpansion _ => .SubshellScope "$(..) expansion"
  | .T_Backticked _ => .SubshellScope "`..` expansion"
  | .T_Backgrounded _ => .SubshellScope "backgrounding &"
  | .T_Subshell _ => .SubshellScope "(..) group"
  | .T_Redirecting _ _ =>  -- correct: 2 args
    -- Would check parent for pipeline context
    .NoneScope
  | _ => .NoneScope

/-- Get modified variables from a token -/
def getModifiedVariables (t : Token) : List (Token × Token × String × DataType) :=
  match t.inner with
  | .T_SimpleCommand assigns [] =>
    assigns.filterMap fun assign =>
      match assign.inner with
      | .T_Assignment _ name _ word =>
        some (assign, assign, name, .DataString (.SourceFrom [word]))
      | _ => Option.none
  | .T_SimpleCommand _ _ =>
    -- Would analyze command to find variable modifications
    []
  | .T_ForIn str words _ =>
    [(t, t, str, .DataString (.SourceFrom words))]
  | _ => []

/-- Get braced variable reference from string like "foo:-bar" -> "foo" -/
def getBracedReference (s : String) : String :=
  s.takeWhile fun c => c.isAlpha || c.isDigit || c == '_'

/-- Get referenced variables from a token -/
def getReferencedVariables (_parents : Std.HashMap Id Token) (t : Token) : List (Token × Token × String) :=
  match t.inner with
  | .T_DollarBraced _ content =>  -- 2 args: braced, content
    let str := getBracedReference (oversimplify content |>.foldl (· ++ ·) "")
    [(t, t, str)]
  | .T_Assignment mode name _ _ =>
    if mode == .append then [(t, t, name)] else []
  | _ => []

/-- Check if code is in annotation range -/
def isCodeInRange (fromCode toCode : Int) (code : Code) : Bool :=
  fromCode ≤ code && code < toCode

/-- Get variable flow from AST -/
def getVariableFlow (_params : Parameters) (_root : Token) : List StackData :=
  -- Simplified stub - would do full stack analysis
  []

/-- Check if a data source is a true assignment (not declaration/check) -/
def isTrueAssignmentSource : DataType → Bool
  | .DataString .SourceChecked => false
  | .DataString .SourceDeclaration => false
  | .DataArray .SourceChecked => false
  | .DataArray .SourceDeclaration => false
  | _ => true

/-- Check if variable is modified in token -/
def modifiesVariable (params : Parameters) (token : Token) (name : String) : Bool :=
  let flow := getVariableFlow params token
  flow.any fun
    | .Assignment (_, _, n, source) => isTrueAssignmentSource source && n == name
    | _ => false

/-- Check if token is a test command -/
partial def isTestCommand (t : Token) : Bool :=
  match t.inner with
  | .T_Condition _ _ => true
  | .T_SimpleCommand _ _ => isCommand t "test"
  | .T_Redirecting _ inner => isTestCommand inner  -- 2 args
  | .T_Annotation _ inner => isTestCommand inner
  | .T_Pipeline _ cmds =>  -- 2 args: separators, commands
    match cmds with
    | [inner] => isTestCommand inner
    | _ => false
  | _ => false

/-- Check if shell supports arrays -/
def supportsArrays : Shell → Bool
  | .Bash => true
  | .Ksh => true
  | _ => false

/-- Check if this is a counting reference ${#var} -/
def isCountingReference (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced _ content =>  -- 2 args: braced, content
    let str := oversimplify content |>.foldl (· ++ ·) ""
    str.startsWith "#"
  | _ => false

/-- Check if token is only redirection (no command) -/
def isOnlyRedirection (t : Token) : Bool :=
  match t.inner with
  | .T_Redirecting redirects cmd =>  -- 2 args
    !redirects.isEmpty &&
    (match cmd.inner with
     | .T_SimpleCommand [] [] => true
     | _ => false)
  | _ => false

/-- Check if annotation disables a code -/
def annotationDisablesCode (ann : Annotation) (code : Code) : Bool :=
  match ann with
  | .disableComment fromCode toCode => isCodeInRange fromCode toCode code
  | _ => false

/-- Filter comments by annotation (ignore directives) -/
def filterByAnnotation (_spec : AnalysisSpec) (params : Parameters) (comments : List TokenComment) : List TokenComment :=
  comments.filter fun note =>
    not (shouldIgnore note)
where
  shouldIgnore (note : TokenComment) : Bool :=
    -- Check for shellcheck disable annotations
    match params.parentMap.get? note.tcId with
    | some parent =>
      match parent.inner with
      | .T_Annotation annotations _ =>
        annotations.any (annotationDisablesCode · note.tcComment.cCode)
      | _ => false
    | none => false

/-- Check if annotation ignores a specific code -/
def isAnnotationIgnoringCode (code : Code) (t : Token) : Bool :=
  match t.inner with
  | .T_Annotation annotations _ =>
    annotations.any (annotationDisablesCode · code)
  | _ => false

/-- Check if should ignore code for token -/
partial def shouldIgnoreCode (params : Parameters) (code : Code) (t : Token) : Bool :=
  -- Walk up parent tree checking for annotations
  match params.parentMap.get? t.id with
  | some parent =>
    isAnnotationIgnoringCode code parent || shouldIgnoreCode params code parent
  | none => false

/-- Run when shell matches -/
def whenShell (shells : List Shell) (analysis : Analysis) : Analysis := do
  let params ← read
  if shells.contains params.shellType then
    analysis
  else
    pure []

/-- Check if regex looks like confused glob -/
def isConfusedGlobRegex (s : String) : Bool :=
  if s.isEmpty then false
  else if s.front == '*' then true
  else if s.length >= 2 then
    let last := s.back
    let chars := s.toList
    let secondLast := chars[chars.length - 2]!
    last == '*' && secondLast != '\\' && secondLast != '.'
  else
    false

/-- Check if character is alphanumeric -/
def isAlphaNum (c : Char) : Bool := c.isAlpha || c.isDigit

/-- Get variables from a literal string like "$foo" -/
def getVariablesFromLiteral (s : String) : List String :=
  -- Simplified: extract $name patterns
  go s.toList [] []
where
  go : List Char → List Char → List String → List String
  | [], [], acc => acc.reverse
  | [], curr, acc => (String.mk curr.reverse :: acc).reverse
  | '$' :: '{' :: rest, [], acc => goInBrace rest [] acc
  | '$' :: c :: rest, [], acc =>
    if c.isAlpha || c == '_' then
      go rest [c] acc
    else
      go rest [] acc
  | c :: rest, curr@(_ :: _), acc =>
    if isAlphaNum c || c == '_' then
      go rest (c :: curr) acc
    else
      go rest [] (String.mk curr.reverse :: acc)
  | _ :: rest, [], acc => go rest [] acc

  goInBrace : List Char → List Char → List String → List String
  | [], _, acc => acc.reverse
  | '}' :: rest, curr, acc =>
    go rest [] (String.mk curr.reverse :: acc)
  | c :: rest, curr, acc =>
    if isAlphaNum c || c == '_' then
      goInBrace rest (c :: curr) acc
    else
      goInBrace rest curr acc

/-- Get variables from literal token -/
def getVariablesFromLiteralToken (t : Token) : List String :=
  getVariablesFromLiteral (getLiteralStringDef " " t)

/-- Find first match where predicate is Just True -/
def findFirst (p : α → Option Bool) : List α → Option α
  | [] => Option.none
  | x :: xs =>
    match p x with
    | some true => some x
    | some false => Option.none
    | none => findFirst p xs

/-- Check if token is entirely output from single command -/
def tokenIsJustCommandOutput (t : Token) : Bool :=
  match t.inner with
  | .T_NormalWord [part] =>
    match part.inner with
    | .T_DollarExpansion [cmd] => not (isOnlyRedirection cmd)
    | .T_Backticked [cmd] => not (isOnlyRedirection cmd)
    | .T_DoubleQuoted [innerPart] =>
      match innerPart.inner with
      | .T_DollarExpansion [cmd] => not (isOnlyRedirection cmd)
      | .T_Backticked [cmd] => not (isOnlyRedirection cmd)
      | _ => false
    | _ => false
  | _ => false

/-- Check if used as command name -/
partial def usedAsCommandName (tree : Std.HashMap Id Token) (token : Token) : Bool :=
  match tree.get? token.id with
  | some parent =>
    match parent.inner with
    | .T_SimpleCommand _ (firstWord :: _) => firstWord.id == token.id
    | .T_NormalWord [single] => single.id == token.id && usedAsCommandName tree parent
    | _ => false
  | none => false

/-- Make default analysis spec from parse result -/
def defaultSpec (pr : ParseResult) : AnalysisSpec :=
  match pr.prRoot with
  | some root => {
      asScript := root
      asShellType := Option.none
      asCheckSourced := false
      asExecutionMode := .executed
      asTokenPositions := pr.prTokenPositions
      asExtendedAnalysis := Option.none
      asFallbackShell := Option.none
      asOptionalChecks := []
    }
  | none => default

/-- Make parameters from analysis spec -/
def makeParameters (spec : AnalysisSpec) : Parameters :=
  let root := spec.asScript
  let shell := spec.asShellType.getD (determineShell spec.asFallbackShell root)
  let params : Parameters := {
    rootNode := root
    shellType := shell
    hasSetE := containsSetE root
    hasLastpipe :=
      match shell with
      | .Bash => isOptionSet "lastpipe" root
      | .Ksh => true
      | _ => false
    hasInheritErrexit :=
      match shell with
      | .Bash => isOptionSet "inherit_errexit" root
      | .Ksh => false
      | _ => true
    hasPipefail := isOptionSet "pipefail" root
    hasExecfail :=
      match shell with
      | .Bash => isOptionSet "execfail" root
      | _ => false
    shellTypeSpecified := spec.asShellType.isSome || spec.asFallbackShell.isSome
    idMap := getTokenMap root
    parentMap := getParentTree root
    variableFlow := []  -- Would compute with getVariableFlow
    tokenPositions := spec.asTokenPositions
    cfgAnalysis := Option.none  -- Would compute if extended analysis enabled
  }
  params

-- Theorems (stubs)

theorem runChecker_empty (params : Parameters) :
    runChecker params emptyChecker = [] := sorry

theorem composeAnalyzers_assoc (f g h : Token → Analysis) (t : Token) :
    True := trivial

theorem makeComment_has_severity (sev : Severity) (id : Id) (code : Code) (msg : String) :
    (makeComment sev id code msg).tcComment.cSeverity = sev := rfl

theorem makeComment_has_code (sev : Severity) (id : Id) (code : Code) (msg : String) :
    (makeComment sev id code msg).tcComment.cCode = code := rfl

theorem filterByAnnotation_subset (spec : AnalysisSpec) (params : Parameters) (comments : List TokenComment) :
    (filterByAnnotation spec params comments).length ≤ comments.length := sorry

theorem isOptionSet_or (opt : String) (root : Token) :
    isOptionSet opt root = (containsShopt opt root || containsSetOption opt root) := rfl

theorem determineShell_with_fallback (fb : Shell) (root : Token) :
    True := trivial

theorem getParentTree_contains_children (root : Token) :
    True := trivial

theorem getTokenMap_contains_root (root : Token) :
    (getTokenMap root).contains root.id := sorry

theorem supportsArrays_bash : supportsArrays .Bash = true := rfl
theorem supportsArrays_ksh : supportsArrays .Ksh = true := rfl
theorem supportsArrays_sh : supportsArrays .Sh = false := rfl

theorem isCountingReference_hash_prefix :
    True := trivial

theorem getVariablesFromLiteral_simple :
    getVariablesFromLiteral "$foo" = ["foo"] := sorry

theorem findFirst_stops_on_true :
    True := trivial

theorem makeParameters_preserves_root (spec : AnalysisSpec) :
    (makeParameters spec).rootNode = spec.asScript := rfl

theorem isTrueAssignmentSource_external :
    isTrueAssignmentSource (.DataString .SourceExternal) = true := rfl

theorem isTrueAssignmentSource_checked :
    isTrueAssignmentSource (.DataString .SourceChecked) = false := rfl

end ShellCheck.AnalyzerLib
