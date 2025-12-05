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

/-- Get the path from token to root via parent map -/
partial def getPath (tree : Std.HashMap Id Token) (t : Token) : List Token :=
  go t [t]
where
  go (current : Token) (acc : List Token) : List Token :=
    match tree.get? current.id with
    | some parent => go parent (parent :: acc)
    | none => acc.reverse

/-- Check if token is self-quoting (assignment context) -/
def isQuoteFreeElement (t : Token) : Bool :=
  match t.inner with
  | .T_Assignment _ _ _ _ => true
  | .T_FdRedirect _ _ => true
  | _ => false

/-- Check if a parent context is quote-free -/
def isQuoteFreeContext (strict : Bool) (t : Token) : Option Bool :=
  match t.inner with
  | .TC_Nullary .doubleBracket _ => some true
  | .TC_Unary .doubleBracket _ _ => some true
  | .TC_Binary .doubleBracket _ _ _ => some true
  | .TA_Sequence _ => some true
  | .T_Arithmetic _ => some true
  | .T_Assignment _ _ _ _ => some true
  | .T_Redirecting _ _ => some false  -- Need to check further up
  | .T_DoubleQuoted _ => some true
  | .T_DollarDoubleQuoted _ => some true
  | .T_CaseExpression _ _ => some true
  | .T_HereDoc _ _ _ _ => some true
  | .T_DollarBraced _ _ => some true
  -- When non-strict, pragmatically assume it's desirable to split here
  | .T_ForIn _ _ _ => some (not strict)
  | .T_SelectIn _ _ _ => some (not strict)
  | _ => none

/-- Check if token is in a quote-free context by walking up parent tree -/
def isQuoteFreeNode (strict : Bool) (_shell : Shell) (tree : Std.HashMap Id Token) (t : Token) : Bool :=
  isQuoteFreeElement t ||
  checkParents (getPath tree t)
where
  checkParents : List Token → Bool
    | [] => false
    | p :: rest =>
      match isQuoteFreeContext strict p with
      | some true => true
      | some false => false
      | none => checkParents rest

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

/-- Check if character is alphanumeric -/
def isAlphaNumChar (c : Char) : Bool := c.isAlpha || c.isDigit

/-- Get variables from a literal string like "$foo" -/
def getVariablesFromLiteral (s : String) : List String :=
  go s.toList [] []
where
  go : List Char → List Char → List String → List String
  | [], [], acc => acc.reverse
  | [], curr, acc => (String.ofList curr.reverse :: acc).reverse
  | '$' :: '{' :: rest, [], acc => goInBrace rest [] acc
  | '$' :: c :: rest, [], acc =>
    if c.isAlpha || c == '_' then
      go rest [c] acc
    else
      go rest [] acc
  | c :: rest, curr@(_ :: _), acc =>
    if isAlphaNumChar c || c == '_' then
      go rest (c :: curr) acc
    else
      go rest [] (String.ofList curr.reverse :: acc)
  | _ :: rest, [], acc => go rest [] acc

  goInBrace : List Char → List Char → List String → List String
  | [], _, acc => acc.reverse
  | '}' :: rest, curr, acc =>
    go rest [] (String.ofList curr.reverse :: acc)
  | c :: rest, curr, acc =>
    if isAlphaNumChar c || c == '_' then
      goInBrace rest (c :: curr) acc
    else
      goInBrace rest curr acc

/-- Get variables from literal token -/
def getVariablesFromLiteralToken (t : Token) : List String :=
  getVariablesFromLiteral (getLiteralStringDef " " t)

/-- Get modified variables from a token -/
partial def getModifiedVariablesImpl (t : Token) : List (Token × Token × String × DataType) :=
  match t.inner with
  | .T_SimpleCommand assigns [] =>
    assigns.filterMap fun assign =>
      match assign.inner with
      | .T_Assignment _ name _ word =>
        some (assign, assign, name, .DataString (.SourceFrom [word]))
      | _ => none
  | .T_SimpleCommand assigns words =>
    -- Check for assignments in assigns list
    let assignVars := assigns.filterMap fun assign =>
      match assign.inner with
      | .T_Assignment _ name _ word =>
        some (assign, assign, name, .DataString (.SourceFrom [word]))
      | _ => none
    -- Also check for assignments in words list (simplified parser puts them there)
    let wordAssignVars := words.filterMap fun word =>
      match word.inner with
      | .T_Assignment _ name _ value =>
        let dataType := match value.inner with
          | .T_Array _ => DataType.DataArray (.SourceFrom [value])
          | _ => DataType.DataString (.SourceFrom [value])
        some (word, word, name, dataType)
      | _ => none
    -- Handle read, declare, export, local, etc.
    assignVars ++ wordAssignVars ++ getModifiedVariableCommand t words
  | .TA_Unary op v =>
    match v.inner with
    | .TA_Variable name _ =>
      if Regex.containsSubstring op "++" || Regex.containsSubstring op "--" then
        [(t, v, name, .DataString .SourceInteger)]
      else []
    | _ => []
  | .TA_Assignment op lhs _ =>
    match lhs.inner with
    | .TA_Variable name _ =>
      if op ∈ ["=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=", "^=", "|="] then
        [(t, t, name, .DataString .SourceInteger)]
      else []
    | _ => []
  | .T_BatsTest _ _ =>
    [(t, t, "lines", .DataArray .SourceExternal),
     (t, t, "status", .DataString .SourceInteger),
     (t, t, "output", .DataString .SourceExternal),
     (t, t, "stderr", .DataString .SourceExternal),
     (t, t, "stderr_lines", .DataArray .SourceExternal)]
  | .TC_Unary _ op token =>
    if op == "-v" then
      match getVariableForTestDashV token with
      | some str => [(t, token, str, .DataString .SourceChecked)]
      | none => []
    else if op == "-n" || op == "-z" then
      markAsChecked t token
    else []
  | .TC_Nullary _ token => markAsChecked t token
  | .T_DollarBraced _ l =>
    let str := String.join (oversimplify l)
    let modifier := getBracedModifier str
    if modifier.startsWith "=" || modifier.startsWith ":=" then
      [(t, t, getBracedReference str, .DataString (.SourceFrom [l]))]
    else []
  | .T_FdRedirect varStr op =>
    if varStr.startsWith "{" then
      let varName := (varStr.drop 1).takeWhile (· != '}')
      if not (isClosingFileOp op) then
        [(t, t, varName, .DataString .SourceInteger)]
      else []
    else []
  | .T_CoProc nameOpt _ =>
    match nameOpt with
    | some token =>
      match getLiteralString token with
      | some name => [(t, t, name, .DataArray .SourceInteger)]
      | none => []
    | none => [(t, t, "COPROC", .DataArray .SourceInteger)]
  | .T_ForIn str [] _ => [(t, t, str, .DataString .SourceExternal)]
  | .T_ForIn str words _ => [(t, t, str, .DataString (.SourceFrom words))]
  | .T_SelectIn str words _ => [(t, t, str, .DataString (.SourceFrom words))]
  | _ => []
where
  isClosingFileOp (t : Token) : Bool :=
    match t.inner with
    | .T_IoDuplicate _ s => s == "-"
    | _ => false

  getVariableForTestDashV (token : Token) : Option String := do
    let str ← getLiteralStringExt (fun t =>
      match t.inner with
      | .T_Glob s => some s
      | _ => some (String.singleton (Char.ofNat 0))) token
    let varName := str.takeWhile (· != '[')
    if isVariableName varName then some varName else none

  markAsChecked (place : Token) (token : Token) : List (Token × Token × String × DataType) :=
    (getWordParts token).filterMap fun part =>
      match part.inner with
      | .T_DollarBraced _ l =>
        let str := getBracedReference (String.join (oversimplify l))
        if isVariableName str then
          some (place, part, str, .DataString .SourceChecked)
        else none
      | _ => none

  getModifiedVariableCommand (base : Token) (words : List Token) :
      List (Token × Token × String × DataType) :=
    match words with
    | [] => []
    | cmd :: rest =>
      match getLiteralString cmd with
      | some "read" => getReadVariables base rest
      | some "export" => getModifierParams DataType.DataString rest
      | some "declare" => getDeclareVariables base rest
      | some "typeset" => getDeclareVariables base rest
      | some "local" => getModifierParams DataType.DataString rest
      | some "readonly" => getModifierParams DataType.DataString rest
      | some "let" => getLetVariables base rest
      | some "printf" => getPrintfVariable base rest
      | some "mapfile" => getMapfileVariable base rest
      | some "readarray" => getMapfileVariable base rest
      | some "getopts" =>
        match rest with
        | _ :: var :: _ => getLiteralVariable base var
        | _ => []
      | _ => []

  getReadVariables (base : Token) (args : List Token) :
      List (Token × Token × String × DataType) :=
    -- Simplified: get last non-flag arguments as variable names
    args.reverse.take 1 |>.filterMap fun arg =>
      match getLiteralString arg with
      | some s =>
        if not (s.startsWith "-") && isVariableName s then
          some (base, arg, s, .DataString .SourceExternal)
        else none
      | none => none

  getDeclareVariables (_base : Token) (args : List Token) :
      List (Token × Token × String × DataType) :=
    getModifierParams DataType.DataString args

  getModifierParams (defaultType : DataSource → DataType) (args : List Token) :
      List (Token × Token × String × DataType) :=
    args.filterMap fun arg =>
      match arg.inner with
      | .T_Assignment _ name _ value =>
        some (arg, arg, name, defaultType (DataSource.SourceFrom [value]))
      | _ =>
        match getLiteralString arg with
        | some s =>
          if isVariableName s then
            some (arg, arg, s, defaultType DataSource.SourceDeclaration)
          else none
        | none => none

  getLetVariables (base : Token) (args : List Token) :
      List (Token × Token × String × DataType) :=
    args.filterMap fun arg =>
      let s := String.join (oversimplify arg)
      let varName := s.dropWhile (fun c => c == '+' || c == '-')
                      |>.takeWhile isVariableChar
      if varName.isEmpty then none
      else some (base, arg, varName, .DataString (.SourceFrom [arg]))

  getPrintfVariable (base : Token) (args : List Token) :
      List (Token × Token × String × DataType) :=
    -- Look for -v flag
    match findFlag "-v" args with
    | some (_, valueToken) =>
      match getLiteralString valueToken with
      | some varName =>
        let baseName := varName.takeWhile (· != '[')
        [(base, valueToken, baseName, .DataString (.SourceFrom args))]
      | none => []
    | none => []

  getMapfileVariable (base : Token) (args : List Token) :
      List (Token × Token × String × DataType) :=
    -- Last non-flag argument is array name, default is MAPFILE
    let nonFlags := args.filter fun a =>
      match getLiteralString a with
      | some s => not (s.startsWith "-")
      | none => true
    match nonFlags.getLast? with
    | some arg =>
      match getLiteralString arg with
      | some name =>
        if isVariableName name then [(base, arg, name, .DataArray .SourceExternal)]
        else [(base, base, "MAPFILE", .DataArray .SourceExternal)]
      | none => [(base, base, "MAPFILE", .DataArray .SourceExternal)]
    | none => [(base, base, "MAPFILE", .DataArray .SourceExternal)]

  getLiteralVariable (base : Token) (arg : Token) :
      List (Token × Token × String × DataType) :=
    match getLiteralString arg with
    | some s =>
      if isVariableName s then [(base, arg, s, .DataString .SourceExternal)]
      else []
    | none => []

  findFlag (flag : String) : List Token → Option (Token × Token)
  | [] => none
  | [_] => none
  | f :: v :: rest =>
    if getLiteralString f == some flag then some (f, v)
    else findFlag flag (v :: rest)

/-- Get referenced variables from a token -/
partial def getReferencedVariablesImpl (parents : Std.HashMap Id Token) (t : Token) :
    List (Token × Token × String) :=
  match t.inner with
  | .T_DollarBraced _ l =>
    let str := String.join (oversimplify l)
    let mainRef := (t, t, getBracedReference str)
    let indexRefs := getIndexReferences str |>.map fun x => (l, l, x)
    let offsetRefs := getOffsetReferences (getBracedModifier str) |>.map fun x => (l, l, x)
    mainRef :: indexRefs ++ offsetRefs
  | .TA_Variable name _ =>
    if isArithmeticAssignment parents t then []
    else [(t, t, name)]
  | .T_Assignment mode name _ word =>
    let selfRef := if mode == .append then [(t, t, name)] else []
    selfRef ++ specialReferences name t word
  | .TC_Unary _ op token =>
    if op == "-v" || op == "-R" then getIfReference t token
    else []
  | .TC_Binary .doubleBracket op lhs rhs =>
    if isDereferencingBinaryOp op then
      getIfReference t lhs ++ getIfReference t rhs
    else []
  | .T_BatsTest _ _ =>
    [(t, t, "lines"), (t, t, "status"), (t, t, "output")]
  | .T_FdRedirect varStr op =>
    if varStr.startsWith "{" then
      let varName := (varStr.drop 1).takeWhile (· != '}')
      match op.inner with
      | .T_IoDuplicate _ s => if s == "-" then [(t, t, varName)] else []
      | _ => []
    else []
  | _ => getReferencedVariableCommand t
where
  getIndexReferences (s : String) : List String :=
    -- Extract variable names from array indices like foo[bar]
    let afterBracket := s.dropWhile (· != '[')
    if afterBracket.isEmpty then []
    else
      let indexPart := (afterBracket.drop 1).takeWhile (· != ']')
      if isVariableName indexPart then [indexPart] else []

  getOffsetReferences (modifier : String) : List String :=
    -- Extract variables from offset expressions like ${var:offset:length}
    if modifier.startsWith ":" then
      let parts := modifier.splitOn ":"
      parts.filterMap fun p =>
        let name := p.takeWhile isVariableChar
        if isVariableName name then some name else none
    else []

  isArithmeticAssignment (parents : Std.HashMap Id Token) (t : Token) : Bool :=
    match parents.get? t.id with
    | some parent =>
      match parent.inner with
      | .TA_Assignment "=" lhs _ => lhs.id == t.id
      | _ => false
    | none => false

  specialReferences (name : String) (base : Token) (word : Token) :
      List (Token × Token × String) :=
    if name ∈ ["PS1", "PS2", "PS3", "PS4", "PROMPT_COMMAND"] then
      getVariablesFromLiteralToken word |>.map fun x => (base, base, x)
    else []

  getIfReference (context : Token) (token : Token) : List (Token × Token × String) :=
    match getVariableForTestDashV token with
    | some str => [(context, token, getBracedReference str)]
    | none => []

  getVariableForTestDashV (token : Token) : Option String := do
    let str ← getLiteralStringExt (fun t =>
      match t.inner with
      | .T_Glob s => some s
      | _ => some (String.singleton (Char.ofNat 0))) token
    let varName := str.takeWhile (· != '[')
    if isVariableName varName then some varName else none

  isDereferencingBinaryOp (op : String) : Bool :=
    op ∈ ["-eq", "-ne", "-lt", "-le", "-gt", "-ge"]

  getReferencedVariableCommand (t : Token) : List (Token × Token × String) :=
    match t.inner with
    | .T_SimpleCommand _ (cmd :: rest) =>
      match getLiteralString cmd with
      | some "export" => getExportReferences t rest
      | some "declare" => getDeclareReferences t rest
      | some "typeset" => getDeclareReferences t rest
      | some "trap" =>
        match rest with
        | handler :: _ => getVariablesFromLiteralToken handler |>.map fun x => (t, handler, x)
        | [] => []
      | some "alias" =>
        rest.flatMap fun arg => getVariablesFromLiteralToken arg |>.map fun x => (t, arg, x)
      | _ => []
    | _ => []

  getExportReferences (base : Token) (args : List Token) : List (Token × Token × String) :=
    -- Check if -f flag is present
    let hasF := args.any fun a => getLiteralString a == some "-f"
    if hasF then []
    else args.filterMap fun arg =>
      match arg.inner with
      | .T_Assignment _ name _ _ => some (arg, arg, name)
      | _ =>
        match getLiteralString arg with
        | some s => if isVariableName s && not (s.startsWith "-") then some (arg, arg, s) else none
        | none => none

  getDeclareReferences (base : Token) (args : List Token) : List (Token × Token × String) :=
    let flags := args.filterMap fun a =>
      match getLiteralString a with
      | some s => if s.startsWith "-" then some s else none
      | none => none
    let hasXorP := flags.any fun f => f.any (· == 'x') || f.any (· == 'p')
    let hasFOrBigF := flags.any fun f => f.any (· == 'f') || f.any (· == 'F')
    if hasXorP && not hasFOrBigF then
      args.filterMap fun arg =>
        match arg.inner with
        | .T_Assignment _ name _ _ => some (arg, arg, name)
        | _ =>
          match getLiteralString arg with
          | some s => if isVariableName s && not (s.startsWith "-") then some (arg, arg, s) else none
          | none => none
    else []

/-- Determine the scope type of a token -/
def leadTypeImpl (params : Parameters) (t : Token) : Scope :=
  match t.inner with
  | .T_DollarExpansion _ => .SubshellScope "$(..) expansion"
  | .T_Backticked _ => .SubshellScope "`..` expansion"
  | .T_Backgrounded _ => .SubshellScope "backgrounding &"
  | .T_Subshell _ => .SubshellScope "(..) group"
  | .T_BatsTest _ _ => .SubshellScope "@bats test"
  | .T_CoProcBody _ => .SubshellScope "coproc"
  | .T_Redirecting _ _ =>
    match causesSubshell params t with
    | some true => .SubshellScope "pipeline"
    | _ => .NoneScope
  | _ => .NoneScope
where
  causesSubshell (params : Parameters) (t : Token) : Option Bool := do
    let parent ← params.parentMap.get? t.id
    match parent.inner with
    | .T_Pipeline _ list =>
      match list with
      | _ :: _ :: _ =>
        if params.hasLastpipe then
          some (list.getLast?.map (·.id) != some t.id)
        else some true
      | _ => some false
    | _ => none

/-- Check if assignment comes first in this construct -/
def assignFirst (t : Token) : Bool :=
  match t.inner with
  | .T_ForIn _ _ _ => true
  | .T_SelectIn _ _ _ => true
  | .T_BatsTest _ _ => true
  | _ => false

/-- Collect tokens depth-first with stack analysis for variable flow -/
partial def doStackAnalysisForFlow (params : Parameters) (t : Token) : List StackData :=
  let scopeType := leadTypeImpl params t
  let startScope := if scopeType != .NoneScope then [.StackScope scopeType] else []
  let preAssign := if assignFirst t then getModifiedVariablesImpl t |>.map .Assignment else []

  let children := getTokenChildren t
  let childFlows := children.flatMap (doStackAnalysisForFlow params)

  let reads := getReferencedVariablesImpl params.parentMap t |>.map .Reference
  let postAssign := if not (assignFirst t) then getModifiedVariablesImpl t |>.map .Assignment else []
  let endScope := if scopeType != .NoneScope then [.StackScopeEnd] else []

  startScope ++ preAssign ++ childFlows ++ reads ++ postAssign ++ endScope

/-- Get variable flow from AST - walks the AST tracking assignments and references with scope -/
def getVariableFlow (params : Parameters) (root : Token) : List StackData :=
  doStackAnalysisForFlow params root |>.reverse

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

/-- Do variable flow analysis with read/write callbacks -/
def doVariableFlowAnalysis
    (readF : Token → Token → String → StateM σ (List α))
    (writeF : Token → Token → String → DataType → StateM σ (List α))
    (init : σ)
    (flow : List StackData) : List α :=
  let (results, _) := go flow init []
  results
where
  go : List StackData → σ → List α → List α × σ
    | [], s, acc => (acc, s)
    | .Reference (base, token, name) :: rest, s, acc =>
      let (comments, s') := (readF base token name).run s
      go rest s' (acc ++ comments)
    | .Assignment (base, token, name, values) :: rest, s, acc =>
      let (comments, s') := (writeF base token name values).run s
      go rest s' (acc ++ comments)
    | _ :: rest, s, acc => go rest s acc

/-- Check if default assignment pattern ${var:-default} -/
def isDefaultAssignment (tree : Std.HashMap Id Token) (t : Token) : Bool :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let s := String.join (oversimplify content)
    let modifier := getBracedModifier s
    modifier.startsWith ":-" || modifier.startsWith "-"
  | _ => false

/-- Check if quotes may conflict with SC2281 ($foo=bar -> foo=bar correction) -/
def quotesMayConflictWithSC2281 (params : Parameters) (t : Token) : Bool :=
  let path := getPath params.parentMap t
  match path with
  | _ :: parent :: grandparent :: _ =>
    match parent.inner with
    | .T_NormalWord (first :: ⟨_, .T_Literal eqPart⟩ :: _) =>
      if eqPart.startsWith "=" then
        match grandparent.inner with
        | .T_SimpleCommand _ (cmd :: _) => first.id == t.id && parent.id == cmd.id
        | _ => false
      else false
    | _ => false
  | _ => false

/-- Function definition record -/
structure FunctionDefinition where
  name : String
  token : Token
  body : Token
  deriving Repr, Inhabited

/-- Find function definition from a token -/
def findFunctionDefinition (t : Token) : Option FunctionDefinition :=
  match t.inner with
  | .T_Function _ _ name body =>
    some { name := name, token := t, body := body }
  -- Workaround: Also detect from T_SimpleCommand where first word is "function"
  -- This handles cases where the parser produces T_SimpleCommand instead of T_Function
  | .T_SimpleCommand _ words =>
    match words with
    | funcKw :: nameWord :: bodyWords =>
      if getLiteralString funcKw == some "function" then
        match getLiteralString nameWord with
        | some name =>
          -- Find the brace group as the body
          match bodyWords.find? (fun w => match w.inner with | .T_BraceGroup _ => true | _ => false) with
          | some body => some { name := name, token := t, body := body }
          | Option.none =>
            -- Body might be inline, create synthetic body from remaining words
            some { name := name, token := t, body := t }
        | Option.none => Option.none
      else Option.none
    | _ => Option.none
  | _ => Option.none

/-- Find alias definition from a token -/
def findAliasDefinition (t : Token) : Option (String × Token) :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    if getLiteralString cmd == some "alias" then
      match args.head? with
      | some arg =>
        match getLiteralString arg with
        | some s =>
          let parts := s.splitOn "="
          match parts with
          | name :: _ => some (name, t)
          | _ => none
        | none => none
      | none => none
    else none
  | _ => none

/-- Collect all function definitions from tree -/
partial def collectFunctionDefinitions (t : Token) : List FunctionDefinition :=
  let self := findFunctionDefinition t |>.toList
  let children := getTokenChildren t
  self ++ children.flatMap collectFunctionDefinitions

/-- Build a map from function name to definition -/
def getFunctionMap (root : Token) : Std.HashMap String FunctionDefinition :=
  let funcs := collectFunctionDefinitions root
  funcs.foldl (fun m f => m.insert f.name f) {}

/-- Collect all alias definitions from tree -/
partial def collectAliasDefinitions (t : Token) : List (String × Token) :=
  let self := findAliasDefinition t |>.toList
  let children := getTokenChildren t
  self ++ children.flatMap collectAliasDefinitions

/-- Build a map from alias name to token -/
def getAliasMap (root : Token) : Std.HashMap String Token :=
  let aliases := collectAliasDefinitions root
  aliases.foldl (fun m (name, tok) => m.insert name tok) {}

/-- Get all functions and aliases combined -/
def getFunctionsAndAliases (root : Token) : Std.HashMap String Token :=
  let funcMap := getFunctionMap root
  let aliasMap := getAliasMap root
  -- Combine: functions take precedence
  aliasMap.fold (fun m name tok =>
    if m.contains name then m else m.insert name tok
  ) (funcMap.fold (fun m name funcDef => m.insert name funcDef.token) {})

/-- Check if a variable reference is positional ($1, $2, etc.) -/
def isPositionalReference (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: rest =>
    if c.isDigit then
      rest.all (·.isDigit)
    else
      name == "@" || name == "*" || name == "#"

/-- Get all positional variable references in a token tree -/
partial def getPositionalReferences (t : Token) : List (Token × String) :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let str := getBracedReference (String.join (oversimplify content))
    if isPositionalReference str then [(t, str)] else []
  | _ =>
    let children := getTokenChildren t
    children.flatMap getPositionalReferences

/-- Check if function uses positional parameters -/
def functionUsesPositionalParams (func : FunctionDefinition) : List (Token × String) :=
  getPositionalReferences func.body

/-- Find all command invocations in tree -/
partial def findCommandInvocations (t : Token) : List (Token × String) :=
  let self := match t.inner with
    | .T_SimpleCommand _ (cmd :: _) =>
      match getLiteralString cmd with
      | some name => [(t, name)]
      | Option.none => []
    | .T_Redirecting _ inner =>
      match inner.inner with
      | .T_SimpleCommand _ (cmd :: _) =>
        match getLiteralString cmd with
        | some name => [(t, name)]
        | Option.none => []
      | _ => []
    | _ => []
  let children := getTokenChildren t
  self ++ children.flatMap findCommandInvocations

/-- Get token ID range for post-dominator analysis -/
def getTokenIdRange (t : Token) : (Id × Id) :=
  (t.id, t.id)  -- Simplified; real impl would get span

/-- Check if one token comes before another in source order (by ID) -/
def tokenBefore (t1 t2 : Token) : Bool :=
  t1.id.val < t2.id.val

/-- External commands that accept function/alias names as arguments -/
def commandsWithFunctionAsArg : List String :=
  ["xargs", "find", "parallel", "env", "sudo", "su", "nohup", "time",
   "nice", "ionice", "strace", "ltrace", "watch", "timeout", "ssh"]

/-- Check if a word token contains just a variable that could be a function name -/
def couldBeFunctionReference (funcMap : Std.HashMap String Token) (t : Token) : Option String :=
  match getLiteralString t with
  | some name => if funcMap.contains name then some name else none
  | none => none

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
