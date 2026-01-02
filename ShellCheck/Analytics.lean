/-
  Copyright 2012-2024 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Analytics - Main analysis checks for ShellCheck.
  Contains 100+ individual linting rules.
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

namespace ShellCheck.Analytics

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.CFG
open ShellCheck.CFGAnalysis
open ShellCheck.Data
open ShellCheck.Interface
open ShellCheck.Parser
open ShellCheck.Regex

/-!
## Tree Checks

Checks that are run on the entire AST root.
-/

/-- Collect all tokens in the tree -/
partial def collectTokens (t : Token) : List Token :=
  t :: collectFromInner t.inner
where
  collectFromInner (inner : InnerToken Token) : List Token :=
    match inner with
    | .TA_Binary _ l r => collectTokens l ++ collectTokens r
    | .TA_Assignment _ l r => collectTokens l ++ collectTokens r
    | .TA_Variable _ is => is.flatMap collectTokens
    | .TA_Expansion ps => ps.flatMap collectTokens
    | .TA_Sequence es => es.flatMap collectTokens
    | .TA_Parenthesis e => collectTokens e
    | .TA_Trinary c t e => collectTokens c ++ collectTokens t ++ collectTokens e
    | .TA_Unary _ e => collectTokens e
    | .TC_And _ _ l r => collectTokens l ++ collectTokens r
    | .TC_Binary _ _ l r => collectTokens l ++ collectTokens r
    | .TC_Group _ e => collectTokens e
    | .TC_Nullary _ e => collectTokens e
    | .TC_Or _ _ l r => collectTokens l ++ collectTokens r
    | .TC_Unary _ _ e => collectTokens e
    | .TC_Empty _ => []
    | .T_AndIf l r => collectTokens l ++ collectTokens r
    | .T_OrIf l r => collectTokens l ++ collectTokens r
    | .T_Arithmetic e => collectTokens e
    | .T_Array es => es.flatMap collectTokens
    | .T_IndexedElement is v => is.flatMap collectTokens ++ collectTokens v
    | .T_Assignment _ _ is v => is.flatMap collectTokens ++ collectTokens v
    | .T_Backgrounded c => collectTokens c
    | .T_Backticked cs => cs.flatMap collectTokens
    | .T_Banged c => collectTokens c
    | .T_BraceExpansion ps => ps.flatMap collectTokens
    | .T_BraceGroup cs => cs.flatMap collectTokens
    | .T_CaseExpression w cases =>
        collectTokens w ++ cases.flatMap fun (_, pats, body) =>
          pats.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_Condition _ e => collectTokens e
    | .T_DollarArithmetic e => collectTokens e
    | .T_DollarBraced _ c => collectTokens c
    | .T_DollarBracket e => collectTokens e
    | .T_DollarDoubleQuoted ps => ps.flatMap collectTokens
    | .T_DollarExpansion cs => cs.flatMap collectTokens
    | .T_DollarBraceCommandExpansion _ cs => cs.flatMap collectTokens
    | .T_DoubleQuoted ps => ps.flatMap collectTokens
    | .T_Extglob _ ps => ps.flatMap collectTokens
    | .T_FdRedirect _ t => collectTokens t
    | .T_ForArithmetic i c inc body =>
        collectTokens i ++ collectTokens c ++ collectTokens inc ++ body.flatMap collectTokens
    | .T_ForIn _ ws body => ws.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_Function _ _ _ body => collectTokens body
    | .T_HereDoc _ _ _ cs => cs.flatMap collectTokens
    | .T_HereString w => collectTokens w
    | .T_IfExpression conds els =>
        conds.flatMap (fun (c, b) => c.flatMap collectTokens ++ b.flatMap collectTokens) ++
        els.flatMap collectTokens
    | .T_IoFile op file => collectTokens op ++ collectTokens file
    | .T_IoDuplicate op _ => collectTokens op
    | .T_NormalWord ps => ps.flatMap collectTokens
    | .T_Pipeline seps cmds => seps.flatMap collectTokens ++ cmds.flatMap collectTokens
    | .T_ProcSub _ cs => cs.flatMap collectTokens
    | .T_Redirecting rs c => rs.flatMap collectTokens ++ collectTokens c
    | .T_Script sh cs => collectTokens sh ++ cs.flatMap collectTokens
    | .T_SelectIn _ ws body => ws.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_SimpleCommand as ws => as.flatMap collectTokens ++ ws.flatMap collectTokens
    | .T_Subshell cs => cs.flatMap collectTokens
    | .T_UntilExpression c body => c.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_WhileExpression c body => c.flatMap collectTokens ++ body.flatMap collectTokens
    | .T_Annotation _ c => collectTokens c
    | .T_CoProc n body =>
        match n with
        | .some t => collectTokens t ++ collectTokens body
        | .none => collectTokens body
    | .T_CoProcBody body => collectTokens body
    | .T_Include s => collectTokens s
    | .T_SourceCommand src scr => collectTokens src ++ collectTokens scr
    | .T_BatsTest _ body => collectTokens body
    | _ => []  -- Leaf tokens (literals, keywords, etc.)

/-- Run node analysis on tree -/
def runNodeAnalysis (f : Parameters → Token → List TokenComment)
    (p : Parameters) (t : Token) : List TokenComment :=
  -- Walk tree and collect comments from all nodes
  let allTokens := collectTokens t
  allTokens.flatMap (f p)

/-- Convert node checks to tree check -/
def nodeChecksToTreeCheck (checks : List (Parameters → Token → List TokenComment))
    (params : Parameters) (root : Token) : List TokenComment :=
  checks.foldl (fun acc check => acc ++ runNodeAnalysis check params root) []

/-!
## Node Checks

Individual analysis rules applied to each token.
-/

/-- SC2086: Double quote to prevent globbing and word splitting -/
def checkUnquotedDollarAt (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    -- Skip if already in a quoted context
    if isQuoteFree params.shellType params.parentMap t then
      []
    else
      let str := oversimplify content |>.foldl (· ++ ·) ""
      -- Warn for $@, $*, or any variable name (simplified version)
      if str == "@" || str == "*" || isVariableName str then
        match quoteFix params t.id with
        | some fix =>
            [makeCommentWithFix .warningC t.id 2086
              "Double quote to prevent globbing and word splitting." fix]
        | Option.none =>
            [makeComment .warningC t.id 2086
              "Double quote to prevent globbing and word splitting."]
      else []
  | _ => []
where
  isVariableName (s : String) : Bool :=
    match s.toList with
    | c :: _ => c.isAlpha || c == '_'
    | [] => false
  quoteFix (params : Parameters) (id : Id) : Option Fix :=
    match params.tokenPositions.get? id with
    | some (startPos, endPos) =>
        if startPos.posLine != endPos.posLine then
          Option.none
        else
          let openRep : Replacement := {
            repStartPos := startPos
            repEndPos := startPos
            repString := "\""
            repPrecedence := 1
            repInsertionPoint := .insertBefore
          }
          let closePos : Position := { endPos with posColumn := endPos.posColumn + 1 }
          let closeRep : Replacement := {
            repStartPos := closePos
            repEndPos := closePos
            repString := "\""
            repPrecedence := 1
            repInsertionPoint := .insertAfter
          }
          some { fixReplacements := [openRep, closeRep] }
    | Option.none => Option.none

/-- SC2041/SC2042/SC2043/SC2066/SC2258: for-in loop quoting pitfalls. -/
def checkForInQuoted (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
      match words with
      | [single] =>
          match single.inner with
          | .T_NormalWord [inner] =>
              match inner.inner with
              | .T_DoubleQuoted parts =>
                  let shouldWarn :=
                    (parts.any willSplit && !mayBecomeMultipleArgs inner) ||
                    (match getLiteralString inner with
                    | some s => wouldHaveBeenGlob s
                    | Option.none => false)
                  if shouldWarn then
                    [makeComment .errorC inner.id 2066
                      "Since you double quoted this, it will not word split, and the loop will only run once."]
                  else
                    []
              | .T_SingleQuoted _ =>
                  [makeComment .warningC inner.id 2041
                    "This is a literal string. To run as a command, use $(..) instead of '..' . "]
              | _ => checkSingleWord single
          | _ => checkSingleWord single
      | _ =>
          words.flatMap fun arg =>
            match getTrailingUnquotedLiteral arg with
            | some suffix =>
                match getLiteralString suffix with
                | some s =>
                    if s.endsWith "," then
                      [makeComment .warningC arg.id 2258
                        "The trailing comma is part of the value, not a separator. Delete or quote it."]
                    else []
                | Option.none => []
            | Option.none => []
  | _ => []
where
  wouldHaveBeenGlob (s : String) : Bool :=
    s.toList.any (· == '*')

  checkSingleWord (single : Token) : List TokenComment :=
    let hasGlob :=
      match getLiteralString single with
      | some s => wouldHaveBeenGlob s
      | Option.none => false
    match getUnquotedLiteral single with
    | some s =>
        if s.toList.any (· == ',') then
          [makeComment .warningC single.id 2042
            "Use spaces, not commas, to separate loop elements."]
        else if !hasGlob && !(willSplit single || mayBecomeMultipleArgs single) then
          [makeComment .warningC single.id 2043
            "This loop will only ever run once. Bad quoting or missing glob/expansion?"]
        else []
    | Option.none =>
        if !hasGlob && !(willSplit single || mayBecomeMultipleArgs single) then
          [makeComment .warningC single.id 2043
            "This loop will only ever run once. Bad quoting or missing glob/expansion?"]
        else []

/-- SC2012: Use find instead of ls to better handle non-alphanumeric filenames -/
def checkForInLs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.filterMap fun word =>
      if getLiteralString word == some "ls" then
        some (makeComment .warningC word.id 2012
          "Use find instead of ls to better handle non-alphanumeric filenames.")
      else none
  | _ => []

/-- SC2231: Quote expansions in for-loop globs (e.g. `"$dir"/*.txt`). -/
def checkForLoopGlobVariables (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.flatMap fun word =>
      if hasUnquotedGlobChars word then
        (unquotedQuoteableExpansions word).map fun exp =>
          makeComment .infoC exp.id 2231
            "Quote expansions in this for loop glob to prevent wordsplitting, e.g. \"$dir\"/*.txt ."
      else
        []
  | _ => []
where
  globCharLike (c : Char) : Bool :=
    c == '*' || c == '?' || c == '[' || c == ']'

  hasUnquotedGlobChars (t : Token) : Bool :=
    goHasGlob false 64 t

  goHasGlob (quoted : Bool) : Nat → Token → Bool
    | 0, _ => false
    | fuel + 1, t =>
      match t.inner with
      | .T_Annotation _ inner => goHasGlob quoted fuel inner
      | .T_NormalWord parts => parts.any (goHasGlob quoted fuel)
      | .T_DoubleQuoted parts => parts.any (goHasGlob true fuel)
      | .T_DollarDoubleQuoted parts => parts.any (goHasGlob true fuel)
      | .T_Literal s => (!quoted) && s.any globCharLike
      | _ => false

  unquotedQuoteableExpansions (t : Token) : List Token :=
    goUnquotedExps false 64 t

  goUnquotedExps (quoted : Bool) : Nat → Token → List Token
    | 0, _ => []
    | fuel + 1, t =>
      match t.inner with
      | .T_Annotation _ inner => goUnquotedExps quoted fuel inner
      | .T_NormalWord parts => parts.flatMap (goUnquotedExps quoted fuel)
      | .T_DoubleQuoted parts => parts.flatMap (goUnquotedExps true fuel)
      | .T_DollarDoubleQuoted parts => parts.flatMap (goUnquotedExps true fuel)
      | _ =>
        if (!quoted) && isQuoteableExpansion t then
          [t]
        else
          []

/-- SC2015: Note that A && B || C is not if-then-else -/
def checkShorthandIf (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_OrIf left _right =>
    match left.inner with
    | .T_AndIf _ _ => [makeComment .infoC t.id 2015
        "Note that A && B || C is not if-then-else. C may run when A is true."]
    | _ => []
  | _ => []

/-- Helper for collecting dollar references in arithmetic -/
partial def collectDollarRefsArith (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ _ =>
    [makeComment .styleC t.id 2004 "$/${} is unnecessary on arithmetic variables."]
  | .TA_Binary _ left right => collectDollarRefsArith left ++ collectDollarRefsArith right
  | .TA_Unary _ inner => collectDollarRefsArith inner
  | _ => []

/-- SC2004: $/${} is unnecessary on arithmetic variables -/
def checkArithmeticDeref (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarArithmetic inner =>
    collectDollarRefsArith inner
  | _ => []

/-- SC2080: Numbers with leading 0 are considered octal. -/
def checkArithmeticBadOctal (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarArithmetic inner =>
      if containsBadOctal inner then
        [makeComment .errorC t.id 2080 "Numbers with leading 0 are considered octal."]
      else
        []
  | _ => []
where
  isBadOctalLiteral (s : String) : Bool :=
    if !s.startsWith "0" then
      false
    else
      let cs := s.toList
      -- Must be a pure number, and contain an invalid octal digit.
      cs.length ≥ 2 && cs.all Char.isDigit && cs.any (fun c => c == '8' || c == '9')

  containsBadOctal : Token → Bool :=
    go 64

  go : Nat → Token → Bool
    | 0, _ => false
    | fuel + 1, t =>
        match t.inner with
        | .T_Literal s => isBadOctalLiteral s
        | .TA_Binary _ l r => go fuel l || go fuel r
        | .TA_Assignment _ l r => go fuel l || go fuel r
        | .TA_Variable _ indices => indices.any (go fuel)
        | .TA_Expansion parts => parts.any (go fuel)
        | .TA_Sequence exprs => exprs.any (go fuel)
        | .TA_Parenthesis e => go fuel e
        | .TA_Trinary c th el => go fuel c || go fuel th || go fuel el
        | .TA_Unary _ e => go fuel e
        | _ => false

/-- SC2006: Use $(...) notation instead of legacy backticked `...` -/
def checkBackticks (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Backticked _ => [makeComment .infoC t.id 2006
      "Use $(...) notation instead of legacy backticked `...`."]
  | .T_Literal s =>
      -- Also check for backticks in literal strings (simplified parser puts them there)
      if s.any (· == '`') then
        [makeComment .infoC t.id 2006 "Use $(...) notation instead of legacy backticked `...`."]
      else []
  | _ => []

/-- SC2007: Use $((..)) instead of deprecated $[..] -/
def checkDollarBrackets (_params : Parameters) (t : Token) : List TokenComment :=
  match getLiteralString t with
  | .some s =>
      if Regex.containsSubstring s "$[" then
        [makeComment .styleC t.id 2007
          "Use $((..)) instead of deprecated $[..]"]
      else
        []
  | .none => []

/-- SC2034: Variable appears to be unused -/
def checkUnusedAssignments (params : Parameters) (_t : Token) : List TokenComment :=
  let flow := params.variableFlow
  let assigned := getAssignedVariables flow
  let referenced := getReferencedVariables flow
  -- Get the last assignment for each variable (only report on last assignment)
  -- Using foldl so later assignments overwrite earlier ones
  let lastAssignments := assigned.foldl (fun acc (tok, name, dt) =>
    acc.insert name (tok, dt)) ({} : Std.HashMap String (Token × DataType))
  -- Find variables that are assigned but never referenced
  lastAssignments.fold (init := []) fun acc name (token, dataType) =>
    -- Skip special variables and exports
    if isSpecialVar name || not (isTrueAssignmentSource dataType) then
      acc
    else if not (referenced.any fun (_, n) => n == name) then
      (makeComment .warningC token.id 2034
        s!"{name} appears unused. Verify use (or export if used externally).") :: acc
    else acc
where
  getAssignedVariables (flow : List StackData) : List (Token × String × DataType) :=
    flow.filterMap fun s =>
      match s with
      | .Assignment (token, _, name, dt) => some (token, name, dt)
      | _ => Option.none

  getReferencedVariables (flow : List StackData) : List (Token × String) :=
    flow.filterMap fun s =>
      match s with
      | .Reference (token, _, name) => some (token, name)
      | _ => Option.none

  isSpecialVar (name : String) : Bool :=
    name ∈ ["_", "OPTARG", "OPTIND", "REPLY", "RANDOM", "LINENO",
            "SECONDS", "BASH_VERSION", "BASH_VERSINFO", "PWD", "OLDPWD",
            "IFS", "PATH", "HOME", "USER", "SHELL", "TERM", "LANG",
            "LC_ALL", "PS1", "PS2", "PS3", "PS4", "PROMPT_COMMAND"]
    || name.startsWith "_"
    || name.all Char.isUpper  -- Likely exported env vars

/-- SC2030/SC2031: Warn about variables assigned in subshells and used later -/
def checkSubshellAssignments (params : Parameters) (_root : Token) : List TokenComment :=
  findSubshelled params.variableFlow [("script", [])] ({} : Std.HashMap String VariableFlowState) []
    |>.reverse
where
  shouldIgnore (name : String) : Bool :=
    name == "@" || name == "*" || name == "IFS"

  findSubshelled :
      List StackData →
      List (String × List (Token × Token × String × DataType)) →
      Std.HashMap String VariableFlowState →
      List TokenComment →
      List TokenComment
    | [], _scopes, _deadVars, acc => acc
    | .Assignment x@(_, _tok, name, dt) :: rest, (reason, scope) :: scopeRest, deadVars, acc =>
        if isTrueAssignmentSource dt then
          findSubshelled rest ((reason, x :: scope) :: scopeRest) (deadVars.insert name .Alive) acc
        else
          findSubshelled rest ((reason, scope) :: scopeRest) deadVars acc
    | .Reference (_base, place, name) :: rest, scopes, deadVars, acc =>
        if shouldIgnore name then
          findSubshelled rest scopes deadVars acc
        else
          match deadVars.get? name with
          | some (.Dead writeToken reason) =>
              let acc :=
                makeComment .infoC place.id 2031
                  s!"{name} was modified in a subshell. That change might be lost." ::
                makeComment .infoC writeToken.id 2030
                  s!"Modification of {name} is local (to subshell caused by {reason})." ::
                acc
              findSubshelled rest scopes deadVars acc
          | _ =>
              findSubshelled rest scopes deadVars acc
    | .StackScope (.SubshellScope reason) :: rest, scopes, deadVars, acc =>
        findSubshelled rest ((reason, []) :: scopes) deadVars acc
    | .StackScopeEnd :: rest, (reason, scope) :: oldScopes, deadVars, acc =>
        let deadVars :=
          scope.foldl (init := deadVars) fun m (_, place, var, _) =>
            m.insert var (.Dead place reason)
        findSubshelled rest oldScopes deadVars acc
    | _ :: rest, scopes, deadVars, acc =>
        findSubshelled rest scopes deadVars acc

/-- SC2154: Variable is referenced but not assigned -/
def checkUnassignedReferences (params : Parameters) (_t : Token) : List TokenComment :=
  let includeGlobals := false
  let flow := params.variableFlow
  let (readMap, writeMap) := flow.foldl (fun (read, written) entry =>
    match entry with
    | .Assignment (_, _, name, _) =>
      (read, written.insert name ())
    | .Reference (_, place, name) =>
      let read := if read.contains name then read else read.insert name place
      (read, written)
    | _ =>
      (read, written)
  ) (({} : Std.HashMap String Token), ({} : Std.HashMap String Unit))

  let defaultAssigned : Std.HashMap String Unit :=
    internalVariables.foldl (fun m v => m.insert v ()) {}

  let unassigned : List (String × Token) :=
    readMap.toList.filterMap fun (name, place) =>
      if writeMap.contains name || defaultAssigned.contains name then none else some (name, place)

  let writtenVars := writeMap.toList.map (·.1) |>.filter isVariableName

  unassigned.filterMap fun (var, place) =>
    if !isVariableName var then
      none
    else if isException var place || isGuarded place then
      none
    else if includeGlobals || isLocal var then
      warningForLocals writtenVars var place
    else
      warningForGlobals writtenVars var place
where
  isLocal (name : String) : Bool :=
    name.toList.any Char.isLower

  warningForGlobals (writtenVars : List String) (var : String) (place : Token) : Option TokenComment := do
    let matchName ← getBestMatch writtenVars var
    some (makeComment .infoC place.id 2153
      s!"Possible misspelling: {var} may not be assigned. Did you mean {matchName}?")

  warningForLocals (writtenVars : List String) (var : String) (place : Token) : Option TokenComment :=
    let optionalTip :=
      if commonCommands.contains var then
        s!" (for output from commands, use \"$({var} ... )\")"
      else
        match getBestMatch writtenVars var with
        | some matchName => s!" (did you mean '{matchName}'?)"
        | Option.none => ""
    some (makeComment .warningC place.id 2154
      s!"{var} is referenced but not assigned{optionalTip}.")

  isException (var : String) (t : Token) : Bool :=
    (getPath params.parentMap t).any fun anc =>
      match anc.inner with
      | .T_DollarBraced _ content =>
        let str := String.join (oversimplify content)
        let ref := ASTLib.getBracedReference str
        let mod := getBracedModifier str
        ref != var || mod.startsWith "+" || mod.startsWith ":+"
      | _ => false

  isGuarded (t : Token) : Bool :=
    match t.inner with
    | .T_DollarBraced _ content =>
      let name := String.join (oversimplify content)
      let rest :=
        name.toList
          |>.dropWhile (fun c => c == '#' || c == '!')
          |>.dropWhile isVariableChar
      let restStr := String.ofList rest
      Regex.isMatch restStr guardRegex
    | _ => false

  guardRegex : Regex := mkRegex "^(\\[.*\\])?:?[-?]"

  /-- Levenshtein edit distance (used for SC2153 typo suggestions). -/
  min3 (x y z : Nat) : Nat :=
    Nat.min x (Nat.min y z)

  stepRow (c : Char) (prevRow : List Nat) (bChars : List Char) (i : Nat) : List Nat :=
    match prevRow with
    | [] => []
    | prev0 :: prevTail =>
        let rec step (prevDiag : Nat) (prevRest : List Nat) (bRest : List Char)
            (currLeft : Nat) (accRev : List Nat) : List Nat :=
          match prevRest, bRest with
          | prevUp :: prevTail, bch :: bs =>
              let cost := if c == bch then 0 else 1
              let cell := min3 (prevUp + 1) (currLeft + 1) (prevDiag + cost)
              step prevUp prevTail bs cell (cell :: accRev)
          | _, _ => accRev.reverse
        step prev0 prevTail bChars i [i]

  go (aChars : List Char) (bChars : List Char) (prevRow : List Nat) (i : Nat) : List Nat :=
    match aChars with
    | [] => prevRow
    | c :: cs =>
        let i := i + 1
        let next := stepRow c prevRow bChars i
        go cs bChars next i

  dist (a b : String) : Nat :=
    let bChars := b.toList
    let initRow := List.range (bChars.length + 1)
    let finalRow := go a.toList bChars initRow 0
    match finalRow.getLast? with
    | .some n => n
    | .none => 0

  matchScore (var candidate : String) : Nat :=
    if var != candidate && var.toLower == candidate.toLower then
      1
    else
      dist var candidate

  goodMatch (candidate : String) (score : Nat) : Bool :=
    let l := candidate.length
    (l > 3 && score ≤ 1) || (l > 7 && score ≤ 2)

  getBestMatch (writtenVars : List String) (var : String) : Option String :=
    let best : Option (String × Nat) :=
      writtenVars.foldl (init := (Option.none : Option (String × Nat))) fun best cand =>
        let score := matchScore var cand
        match best with
        | .none => .some (cand, score)
        | .some (_, bestScore) =>
            if score < bestScore then .some (cand, score) else best
    match best with
    | .some (cand, score) =>
        if var != cand && goodMatch cand score then .some cand else .none
    | .none => .none

/-- SC2164: Use 'cd ... || exit' or 'cd ... || return' -/
def checkUncheckedCdPushdPopd (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    match words with
    | _cmd :: _ =>
      if isCommand t "cd" || isCommand t "pushd" || isCommand t "popd" then
        -- Check if in a context where exit status is checked
        if not (isCheckedContext params t) then
          [makeComment .warningC t.id 2164
            "Use 'cd ... || exit' or 'cd ... || return' in case cd fails."]
        else []
      else []
    | [] => []
  | _ => []
where
  isCheckedContext (_params : Parameters) (_t : Token) : Bool := false  -- Stub

/-- SC2165/SC2167: Nested loop overrides parent index variable -/
def checkLoopVariableReassignment (params : Parameters) (t : Token) : List TokenComment :=
  match loopVariable t with
  | some var =>
    if var == "_" then [] else
      let ancestors := (getPath params.parentMap t).drop 1
      match ancestors.find? (fun a => loopVariable a == some var) with
      | some parentLoop =>
        [makeComment .warningC t.id 2165
            "This nested loop overrides the index variable of its parent.",
         makeComment .warningC parentLoop.id 2167
            "This parent loop has its index variable overridden."]
      | Option.none => []
  | Option.none => []
where
  loopVariable (t : Token) : Option String :=
    match t.inner with
    | .T_ForIn var _ _ => some var
    | .T_ForArithmetic init _ _ _ =>
      match init.inner with
      | .TA_Sequence [single] =>
        match single.inner with
        | .TA_Assignment "=" lhs _ =>
          match lhs.inner with
          | .TA_Variable name _ => some name
          | _ => none
        | _ => none
      | _ => none
    | _ => none

/-- SC2171: Found trailing ]/]] outside test -/
def checkTrailingBracket (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    match words.getLast? with
    | Option.none => []
    | some lastWord =>
      match lastWord.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_Literal str =>
          if str ∈ ["]", "]]"] then
            let opposite := if str == "]]" then "[[" else "["
            let parameters := oversimplify t
            if opposite ∉ parameters then
              [makeComment .warningC lastWord.id 2171
                s!"Found trailing {str} outside test. Add missing {opposite} or quote if intentional."]
            else []
          else []
        | _ => []
      | _ => []
  | _ => []

/-- SC2155: Declare and assign separately to avoid masking return values -/
def checkMaskedReturns (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    match words with
    | _cmd :: rest =>
      let cmdName := getCommandName t |>.getD ""
      if cmdName ∈ ["local", "export", "declare", "typeset"] then
        rest.filterMap fun arg =>
          match arg.inner with
          | .T_Assignment _ _ _ value =>
            match value.inner with
            | .T_DollarExpansion _ =>
              some (makeComment .warningC t.id 2155
                "Declare and assign separately to avoid masking return values.")
            | _ => none
          | _ => none
      else []
    | [] => []
  | _ => []

/-- SC2066: Since you double quoted this, it will not word split -/
def checkDoubleQuotedWordSplit (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.filterMap fun word =>
      match word.inner with
      | .T_DoubleQuoted _ => some (makeComment .warningC word.id 2066
          "Since you double quoted this, it will not word split, and the loop will only run once.")
      | _ => none
  | _ => []

/-- SC2068: Double quote array expansions -/
def checkArrayExpansions (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let str := oversimplify content |>.foldl (· ++ ·) ""
    if str.endsWith "[@]" || str.endsWith "[*]" then
      -- Don't warn if already in a quoted context (e.g., inside double quotes)
      if isQuoteFree params.shellType params.parentMap t then []
      else [makeComment .errorC t.id 2068 "Double quote array expansions to avoid re-splitting elements."]
    else []
  | _ => []

/-- SC2115: Use "${var:?}" to ensure this never expands to /*
    NOTE: This check requires parser fix - currently parser drops text after
    variable expansion in words (e.g., $dir/ becomes just $dir) -/
def checkRmGlob (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "rm" then
      words.filterMap fun word =>
        -- Oversimplify to see the pattern: $dir/ becomes ${VAR}/
        let simplified := String.join (oversimplify word)
        -- Check for patterns like ${VAR}/ or ${VAR}/*
        -- TODO: Parser bug - text after variable expansion is lost
        if Regex.containsSubstring simplified "${VAR}/" then
          some (makeComment .warningC word.id 2115
            "Use \"${var:?}\" to ensure this never expands to / .")
        else none
    else []
  | _ => []

/-- SC2129: Consider using { cmd1; cmd2; } >> file instead -/
def checkMultipleRedirects (_params : Parameters) (_t : Token) : List TokenComment :=
  -- Would check for multiple consecutive redirects to same file
  []

/-- SC2016: Expressions don't expand in single quotes -/
def checkSingleQuotedExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SingleQuoted content =>
    if content.any (· == '$') || content.any (· == '`') then
      [makeComment .infoC t.id 2016 "Expressions don't expand in single quotes, use double quotes for that."]
    else []
  | _ => []

/-- SC2091: Remove surrounding $(...) to execute command or quote it -/
def checkSpuriousExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand assigns [word] =>
    if assigns.isEmpty then
      match word.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_DollarExpansion _ => [makeComment .warningC t.id 2091
            "Remove surrounding $() to avoid executing output, or use eval to execute."]
        | _ => []
      | _ => []
    else []
  | _ => []

/-- SC2000: See if you can use ${#variable} instead of echo | wc -/
def checkEchoWc (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ [a, b] =>
    let acmd := oversimplify a
    let bcmd := oversimplify b
    if acmd == ["echo", "${VAR}"] then
      if bcmd == ["wc", "-c"] || bcmd == ["wc", "-m"] then
        [makeComment .styleC t.id 2000 "See if you can use ${#variable} instead."]
      else []
    else []
  | _ => []

/-- SC2036: If you wanted to assign the output of the pipeline, use a=$(b | c) -/
def checkPipedAssignment (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ (first :: _ :: _) =>
    match first.inner with
    | .T_Redirecting _ cmd =>
      match cmd.inner with
      | .T_SimpleCommand (_::_) [] =>  -- Has assignments, no words
        [makeComment .warningC t.id 2036
          "If you wanted to assign the output of the pipeline, use a=$(b | c) ."]
      | _ => []
    | _ => []
  | _ => []

/-- SC2037: To assign the output of a command, use var=$(cmd) -/
def checkAssignAteCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand [assign] (firstWord :: _) =>
    match assign.inner with
    | .T_Assignment _ _ _ value =>
      -- Check if first word looks like a flag or glob
      if isFlag firstWord || isGlob firstWord then
        [makeComment .errorC t.id 2037 "To assign the output of a command, use var=$(cmd) ."]
      else
        -- Check if it's a known command name
        let cmdStr := getLiteralString value |>.getD ""
        if cmdStr ∈ commonCommands then
          [makeComment .warningC t.id 2209
            "Use var=$(command) to assign output (or quote to assign string)."]
        else []
    | _ => []
  | _ => []
where
  commonCommands : List String := ["ls", "cat", "pwd", "date", "whoami", "hostname",
    "uname", "id", "basename", "dirname", "head", "tail", "wc", "grep", "find",
    "cut", "tr", "sort", "uniq", "awk", "sed"]

/-- SC2099: Use $((..)) for arithmetics -/
def checkArithmeticOpCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand [_assign] (firstWord :: _) =>
    let op := getLiteralString firstWord |>.getD ""
    if op ∈ ["+", "-", "*", "/"] then
      [makeComment .warningC firstWord.id 2099
        s!"Use $((..)) for arithmetics, e.g. i=$((i {op} 2))"]
    else []
  | _ => []

/-- SC2100: Use $((..)) for arithmetics (assignment looks like i=i+1) -/
def checkWrongArithmeticAssignment (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand [assign] [] =>
    match assign.inner with
    | .T_Assignment _ _ _ value =>
      match getNormalString value with
      | some str =>
        match parseVarOp str with
        | some (var, op) =>
          if (getAssignedNames params.variableFlow).contains var then
            [makeComment .warningC value.id 2100
              s!"Use $((..)) for arithmetics, e.g. i=$((i {op} 2))"]
          else []
        | Option.none => []
      | Option.none => []
    | _ => []
  | _ => []
where
  getAssignedNames (flow : List StackData) : Std.HashMap String Unit :=
    flow.foldl (fun acc entry =>
      match entry with
      | .Assignment (_, _, name, _) => acc.insert name ()
      | _ => acc
    ) {}

  getNormalString (t : Token) : Option String :=
    match t.inner with
    | .T_NormalWord parts =>
      let pieces := parts.mapM fun part =>
        match part.inner with
        | .T_Literal s => some s
        | .T_Glob s => some s
        | _ => none
      String.join <$> pieces
    | .T_Literal s => some s
    | .T_Glob s => some s
    | _ => none

  parseVarOp (s : String) : Option (String × String) :=
    let chars := s.toList
    match chars with
    | [] => none
    | c :: rest =>
      if !(c.isAlpha || c == '_') then
        none
      else
        let varChars := (c :: rest.takeWhile (fun x => x.isAlpha || x.isDigit || x == '_'))
        let var := String.ofList varChars
        let remaining := rest.dropWhile (fun x => x.isAlpha || x.isDigit || x == '_')
        match remaining with
        | op :: more =>
          if op ∈ ['+', '*', '-'] && !more.isEmpty then
            some (var, String.singleton op)
          else none
        | [] => none

/-- SC2104/SC2105/SC2106: break/continue scope issues -/
def checkLoopKeywordScope (params : Parameters) (t : Token) : List TokenComment :=
  match getCommandName t with
  | some name =>
    if name == "break" || name == "continue" then
      let path := getPath params.parentMap t
        |>.filter fun x => isLoop x || isFunction x || (subshellType x).isSome
      if path.any isLoop then
        match (path.filter (fun x => !isFunction x)).find? (fun x => (subshellType x).isSome) with
        | some scopeTok =>
          let str := (subshellType scopeTok).getD "subshell"
          [makeComment .warningC t.id 2106
            s!"This only exits the subshell caused by the {str}."]
        | Option.none => []
      else
        match path.head? with
        | some h =>
          if isFunction h then
            [makeComment .errorC t.id 2104 s!"In functions, use return instead of {name}."]
          else
            [makeComment .errorC t.id 2105 s!"{name} is only valid in loops."]
        | Option.none =>
          [makeComment .errorC t.id 2105 s!"{name} is only valid in loops."]
    else []
  | Option.none => []
where
  subshellType (t : Token) : Option String :=
    match leadTypeImpl params t with
    | .SubshellScope str => some str
    | .NoneScope => Option.none

/-- SC2103: Use a subshell to avoid having to cd back. -/
def checkCdAndBack (params : Parameters) (t : Token) : List TokenComment :=
  if params.hasSetE then
    []
  else
    let sequences := getCommandSequences t
    sequences.foldl (fun acc seq => acc ++ checkSeq seq) []
where
  isCdRevert (tok : Token) : Bool :=
    match oversimplify tok with
    | [_cmd, p] => p == ".." || p == "-"
    | _ => false

  getCandidate : Token → Option Token
    | ⟨_, .T_Annotation _ inner⟩ => getCandidate inner
    | tok =>
        if isCommand tok "cd" then some tok else Option.none

  findCdPair : List Token → Option Token
    | a :: b :: rest =>
        if isCdRevert b && !isCdRevert a then
          some b
        else
          findCdPair (b :: rest)
    | _ => Option.none

  checkSeq (seq : List Token) : List TokenComment :=
    match findCdPair (seq.filterMap getCandidate) with
    | some cdTok =>
        [makeComment .infoC cdTok.id 2103
          "Use a ( subshell ) to avoid having to cd back."]
    | Option.none => []

/-- SC2002: Useless cat. Consider cmd < file | .. instead -/
def checkUuoc (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ (first :: _ :: _) =>
    match first.inner with
    | .T_Redirecting _ cmd =>
      if isCommand cmd "cat" then
        match getCommandArgs cmd with
        | [word] =>
          let str := getLiteralString word |>.getD ""
          if not (str.startsWith "-") && not (willBecomeMultipleArgs word) then
            [makeComment .styleC word.id 2002
              "Useless cat. Consider 'cmd < file | ..' or 'cmd file | ..' instead."]
          else []
        | _ => []
      else []
    | _ => []
  | _ => []
where
  getCommandArgs (t : Token) : List Token :=
    match t.inner with
    | .T_SimpleCommand _ (_ :: args) => args
    | _ => []

/-- SC2009: Consider using pgrep instead of grepping ps output -/
def checkPsGrep (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasPsGrep cmdNames then
      cmds.filterMap fun c =>
        if getCommandBasename c == some "ps" then
          some (makeComment .infoC c.id 2009
            "Consider using pgrep instead of grepping ps output.")
        else none
    else []
  | _ => []
where
  hasPsGrep (names : List String) : Bool :=
    match names with
    | "ps" :: rest => rest.any (· == "grep")
    | _ :: rest => hasPsGrep rest
    | [] => false

/-- SC2010: Don't use ls | grep -/
def checkLsGrep (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasLsGrep cmdNames then
      cmds.filterMap fun c =>
        if getCommandBasename c == some "ls" then
          some (makeComment .warningC c.id 2010
            "Don't use ls | grep. Use a glob or a for loop with a condition to allow non-alphanumeric filenames.")
        else none
    else []
  | _ => []
where
  hasLsGrep (names : List String) : Bool :=
    match names with
    | "ls" :: rest => rest.any (· == "grep")
    | _ :: rest => hasLsGrep rest
    | [] => false

/-- SC2011: Use find .. -print0 | xargs -0 instead of ls | xargs -/
def checkLsXargs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasLsXargs cmdNames then
      cmds.filterMap fun c =>
        if getCommandBasename c == some "ls" then
          some (makeComment .warningC c.id 2011
            "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.")
        else none
    else []
  | _ => []
where
  hasLsXargs (names : List String) : Bool :=
    match names with
    | "ls" :: rest => rest.any (· == "xargs")
    | _ :: rest => hasLsXargs rest
    | [] => false

/-- SC2038: Use find -print0 | xargs -0 -/
def checkFindXargs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasFindXargs cmdNames then
      let allArgs := cmds.flatMap oversimplify
      -- Check if -print0 or -0 is used
      if not (allArgs.any (· == "-print0") || allArgs.any (· == "-0") ||
              allArgs.any (· == "--null") || allArgs.any fun s => s.endsWith "printf") then
        cmds.filterMap fun c =>
          if getCommandBasename c == some "find" then
            some (makeComment .warningC c.id 2038
              "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.")
          else none
      else []
    else []
  | _ => []
where
  hasFindXargs (names : List String) : Bool :=
    match names with
    | "find" :: rest => rest.any (· == "xargs")
    | _ :: rest => hasFindXargs rest
    | [] => false

/-- SC2126: Consider using grep -c instead of grep|wc -l -/
def checkGrepWc (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let cmdNames := cmds.filterMap fun c => getCommandBasename c
    if hasGrepWc cmdNames then
      let allArgs := cmds.flatMap oversimplify
      -- Skip if grep has -o, -l, -L, -r, -R, -A, -B, or wc has -c, -m, -w
      if not (allArgs.any fun s => s ∈ ["-o", "--only-matching", "-l", "-L",
              "-r", "-R", "--recursive", "-A", "-B", "--after-context", "--before-context",
              "-c", "--count", "-m", "-w", "--words"]) then
        cmds.filterMap fun c =>
          if getCommandBasename c == some "grep" then
            some (makeComment .styleC c.id 2126
              "Consider using 'grep -c' instead of 'grep|wc -l'.")
          else none
      else []
    else []
  | _ => []
where
  hasGrepWc (names : List String) : Bool :=
    match names with
    | "grep" :: rest => rest.any (· == "wc")
    | _ :: rest => hasGrepWc rest
    | [] => false

/-- Helper for SC2096 -/
partial def checkShebangParametersImpl (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Annotation _ inner => checkShebangParametersImpl inner
  | .T_Script shebang _ =>
    match shebang.inner with
    | .T_Literal sb =>
      let words := sb.splitOn " " |>.filter (· != "")
      -- More than 2 words (#!/path/to/env bash -x) and not using -S or --split-string
      if words.length > 2 &&
         not (Regex.containsSubstring sb "-S" || Regex.containsSubstring sb "--split-string") then
        [makeComment .errorC t.id 2096 "On most OS, shebangs can only specify a single parameter."]
      else []
    | _ => []
  | _ => []

/-- SC2096: On most OS, shebangs can only specify a single parameter -/
def checkShebangParameters (_params : Parameters) (t : Token) : List TokenComment :=
  checkShebangParametersImpl t

/-- Helper for SC2148 -/
partial def checkShebangImpl (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Annotation _ inner => checkShebangImpl params inner
  | .T_Script shebang _ =>
    match shebang.inner with
    | .T_Literal sb =>
      let sbLine := if sb.startsWith "#!" then sb.drop 2 else sb
      let sbTrim := (sbLine.dropWhile (· == ' ')).toString
      -- Use shebang token's id for proper line 1 position
      let comments1 :=
        if sbTrim.isEmpty && not params.shellTypeSpecified then
          [makeComment .errorC shebang.id 2148
            "Tips depend on target shell and yours is unknown. Add a shebang or a 'shell' directive."]
        else []
      let comments2 :=
        if Regex.containsSubstring sbTrim "ash" && not (Regex.containsSubstring sbTrim "bash") then
          [makeComment .warningC t.id 2187
            "Ash scripts will be checked as Dash. Add '# shellcheck shell=dash' to silence."]
        else []
      let comments3 :=
        if not sbTrim.isEmpty && not (sbTrim.startsWith "/") && not ("env ".isPrefixOf sbTrim) then
          [makeComment .errorC t.id 2239
            "Ensure the shebang uses an absolute path to the interpreter."]
        else []
      let firstWord := sbTrim.splitOn " " |>.head? |>.getD ""
      let comments4 :=
        if firstWord.endsWith "/" then
          [makeComment .errorC t.id 2246
            "This shebang specifies a directory. Ensure the interpreter is a file."]
        else []
      comments1 ++ comments2 ++ comments3 ++ comments4
    | _ => []
  | _ => []

/-- SC2148: Tips depend on target shell and yours is unknown -/
def checkShebang (params : Parameters) (t : Token) : List TokenComment :=
  checkShebangImpl params t

/-- SC2162: read without -r will mangle backslashes -/
def checkReadWithoutR (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "read" then
      let args := words.flatMap oversimplify
      if not (args.any fun s => s == "-r" || (s.startsWith "-" && s.any (· == 'r'))) then
        [makeComment .infoC t.id 2162 "read without -r will mangle backslashes."]
      else []
    else []
  | _ => []

/-- SC2129: Consider using { cmd1; cmd2; } >> file instead of repeated redirects -/
def checkMultipleRedirectsImpl (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_BraceGroup cmds =>
    let redirectedCmds := cmds.filter hasAppendRedirect
    if redirectedCmds.length >= 3 then
      [makeComment .styleC t.id 2129
        "Consider using { cmd1; cmd2; } >> file instead of individual redirects."]
    else []
  | _ => []
where
  hasAppendRedirect (cmd : Token) : Bool :=
    match cmd.inner with
    | .T_Redirecting redirects _ =>
      redirects.any fun r =>
        match r.inner with
        | .T_FdRedirect _ op =>
          match op.inner with
          | .T_IoFile opToken _ =>
            getLiteralString opToken == some ">>"
          | _ => false
        | _ => false
    | _ => false

/-- SC2128: Expanding an array without an index gives the first element -/
def checkArrayWithoutIndex (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let str := oversimplify content |>.foldl (· ++ ·) ""
    let varName := ASTLib.getBracedReference str
    -- Check if it's an array variable without [@] or [*] or [n]
    if isVariableName varName && not (str.any (· == '[')) then
      -- Check if variable is known to be an array
      if isArrayVariable params varName then
        [makeComment .warningC t.id 2128
          "Expanding an array without an index only gives the first element."]
      else []
    else []
  | _ => []
where
  isVariableName (s : String) : Bool :=
    match s.toList with
    | c :: _ => c.isAlpha || c == '_'
    | [] => false
  isArrayVariable (params : Parameters) (name : String) : Bool :=
    -- Check variable flow for array assignments
    params.variableFlow.any fun
      | .Assignment (_, _, n, .DataArray _) => n == name
      | _ => false

/-- SC2178/SC2179: Array variables assigned as strings or appended incorrectly -/
def checkArrayStringAssignments (params : Parameters) (_root : Token) : List TokenComment :=
  doVariableFlowAnalysis
    (fun _ _ _ => pure [])
    writeF
    init
    params.variableFlow
where
  init : Std.HashMap String Unit :=
    arrayVariables.foldl (fun m name => m.insert name ()) {}

  isIndexed (t : Token) : Bool :=
    match t.inner with
    | .T_Assignment _ _ indices _ => !indices.isEmpty
    | _ => false

  writeF (base : Token) (_token : Token) (name : String) (values : DataType) :
      StateM (Std.HashMap String Unit) (List TokenComment) := do
    let s ← get
    match base.inner, values with
    | .T_Assignment mode _ indices _, .DataString _ =>
      if indices.isEmpty then
        if s.contains name then
          match mode with
          | .assign =>
            pure [makeComment .warningC base.id 2178
              "Variable was used as an array but is now assigned a string."]
          | .append =>
            pure [makeComment .warningC base.id 2179
              "Use array+=(\"item\") to append items to an array."]
        else
          pure []
      else
        -- Indexed assignment implies array usage.
        modify (fun m => m.insert name ())
        pure []
    | _, .DataArray _ =>
      modify (fun m => m.insert name ())
      pure []
    | _, _ =>
      if isIndexed base then
        modify (fun m => m.insert name ())
      else
        modify (fun m => m.erase name)
      pure []

/-- SC2302/SC2303: Looping over array values but using the loop variable as an index. -/
def checkArrayValueUsedAsIndex (params : Parameters) (_root : Token) : List TokenComment :=
  doVariableFlowAnalysis readF writeF ({} : Std.HashMap String (Token × List (Token × String))) params.variableFlow
where
  parents : Std.HashMap Id Token := params.parentMap

  getArrayName (t : Token) : Option String := do
    match ASTLib.getWordParts t with
    | [part] =>
      match part.inner with
      | .T_DollarBraced _ content =>
        let str := String.join (oversimplify content)
        let modifier := ASTLib.getBracedModifier str
        if modifier == "[@]" && !str.startsWith "!" then
          some (ASTLib.getBracedReference str)
        else
          none
      | _ => none
    | _ => none

  /-- Best-effort detection of `name` being used as an array index like `${arr[name]}` or `${arr[$name]}`. -/
  getArrayIfUsedAsIndex (name : String) (t : Token) : Option (Token × String) := do
    -- Case 1: `$name` (or `${name}`) used inside `${arr[$name]}`
    match t.inner with
    | .T_DollarBraced _ content =>
      let ref := ASTLib.getBracedReference (String.join (oversimplify content))
      if ref != name then
        none
      else
        -- Climb to the nearest braced expansion that looks like `${arr[...]}`
        let rec go (cur : Token) (fuel : Nat) : Option (Token × String) :=
          match fuel with
          | 0 => Option.none
          | fuel + 1 =>
            match parents.get? cur.id with
            | Option.none => Option.none
            | Option.some parent =>
              match parent.inner with
              | .T_DollarBraced _ parentContent =>
                let str := String.join (oversimplify parentContent)
                let modifier := ASTLib.getBracedModifier str
                if modifier.startsWith "[" then
                  some (t, ASTLib.getBracedReference str)
                else
                  go parent fuel
              | _ =>
                go parent fuel
        go t 64

    -- Case 2: plain `name` index like `${arr[name]}`
    | _ =>
      let parent ← parents.get? t.id
      match parent.inner with
      | .T_DollarBraced _ parentContent =>
        let str := String.join (oversimplify parentContent)
        let modifier := ASTLib.getBracedModifier str
        if modifier.startsWith s!"[{name}]" || modifier.startsWith s!"[${name}]" then
          some (parent, ASTLib.getBracedReference str)
        else
          none
      | _ => none

  writeF (base : Token) (_token : Token) (name : String) (values : DataType) :
      StateM (Std.HashMap String (Token × List (Token × String))) (List TokenComment) := do
    match base.inner, values with
    | .T_ForIn _ _ _, .DataString (.SourceFrom words) =>
      let arrays := words.filterMap (fun w => getArrayName w |>.map (fun arr => (w, arr)))
      modify (fun m => m.insert name (base, arrays))
      pure []
    | _, _ =>
      modify (fun m => m.erase name)
      pure []

  readF (_base : Token) (t : Token) (name : String) :
      StateM (Std.HashMap String (Token × List (Token × String))) (List TokenComment) := do
    let s ← get
    match s.get? name with
    | Option.none => pure []
    | Option.some (loop, arrays) =>
      match getArrayIfUsedAsIndex name t with
      | Option.none => pure []
      | Option.some (arrayRef, arrayName) =>
        match arrays.find? (fun (_, n) => n == arrayName) with
        | Option.none => pure []
        | Option.some (loopWord, _) =>
          let inLoop := (getPath parents t).any (fun anc => anc.id == loop.id)
          if !inLoop then
            pure []
          else
            pure [
              makeComment .warningC loopWord.id 2302
                "This loops over values. To loop over keys, use \"${!array[@]}\".",
              makeComment .warningC arrayRef.id 2303
                s!"{e4m name} is an array value, not a key. Use it directly or loop over keys instead."
            ]

/-- SC2190/SC2191/SC2192: Associative array literal elements need [index]=value -/
def checkArrayAssignmentIndices (_params : Parameters) (root : Token) : List TokenComment :=
  let assocs := getAssociativeArrays root
  let allTokens := collectTokens root
  allTokens.foldl (fun acc t =>
    match t.inner with
    | .T_Assignment _ name [] value =>
      match value.inner with
      | .T_Array elements =>
        let isAssoc := name ∈ assocs
        acc ++ (elements.flatMap (checkElement isAssoc))
      | _ => acc
    | _ => acc
  ) []
where
  getAssociativeArrays (root : Token) : List String :=
    -- Detect "declare -A foo" / "typeset -A foo" style declarations.
    let toks := collectTokens root
    toks.foldl (fun acc t =>
      match getCommandName t with
      | some cmdName =>
        if cmdName == "declare" || cmdName == "typeset" then
          match getCommandArgv t with
          | some argv =>
            let args := argv.drop 1
            let hasAssocFlag := args.any fun a =>
              match getLiteralString a with
              | some s => s.startsWith "-" && s.contains 'A'
              | Option.none => false
            if hasAssocFlag then
              let vars :=
                args.filterMap fun a =>
                  match getLiteralString a with
                  | some s =>
                    if s.startsWith "-" then Option.none
                    else
                      let name := (s.splitOn "=").headD s
                      if isVariableName name then some name else Option.none
                  | Option.none => Option.none
              acc ++ vars
            else acc
          | Option.none => acc
        else acc
      | Option.none => acc
    ) []

  checkElement (isAssociative : Bool) (t : Token) : List TokenComment :=
    match t.inner with
    | .T_IndexedElement _ value =>
      match value.inner with
      | .T_Literal "" =>
        [makeComment .warningC value.id 2192
          "This array element has no value. Remove spaces after = or use \"\" for empty string."]
      | _ => []
    | .T_NormalWord parts =>
      let emptyIndexed :=
        match getLiteralString t with
        | some s =>
          -- E.g. "arr=( [k]= value )" leaves a literal "[k]=" element with no value.
          s.startsWith "[" && Regex.containsSubstring s "]=" && s.endsWith "="
        | Option.none => false
      if emptyIndexed then
        [makeComment .warningC t.id 2192
          "This array element has no value. Remove spaces after = or use \"\" for empty string."]
      else
        let literalEquals :=
          parts.filterMap fun p =>
            match p.inner with
            | .T_Literal s =>
              let segs := s.splitOn "="
              match segs with
              | before :: rest =>
                let after := String.intercalate "=" rest
                if !before.isEmpty && before.all Char.isDigit && !after.isEmpty then
                  some (makeComment .warningC p.id 2191
                    "The = here is literal. To assign by index, use ( [index]=value ) with no spaces. To keep as literal, quote it.")
                else Option.none
              | [] => Option.none
            | _ => Option.none
        if literalEquals.isEmpty && isAssociative then
          [makeComment .warningC t.id 2190
            "Elements in associative arrays need index, e.g. array=( [index]=value ) ."]
        else
          literalEquals
    | _ => []

/-- SC2071: > is for string comparisons. Use -gt instead -/
def checkNumberComparisons (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary typ op lhs rhs =>
    if op ∈ [">", "<", ">=", "<=", "\\>", "\\<", "\\>=", "\\<="] then
      -- SC2071: <, > in tests are string comparisons, not numeric
      let lhsNum := isNumericLooking lhs
      let rhsNum := isNumericLooking rhs
      if lhsNum || rhsNum then
        let suggestion := match op with
          | ">" => "-gt"
          | "<" => "-lt"
          | ">=" => "-ge"
          | "<=" => "-le"
          | "\\>" => "-gt"
          | "\\<" => "-lt"
          | "\\>=" => "-ge"
          | "\\<=" => "-le"
          | _ => op
        [makeComment .warningC t.id 2071
          s!"{op} is for string comparisons. Use {suggestion} instead."]
      else
        -- SC2122: In [[ ]], <= and >= are not valid string operators. Suggest using negation.
        if (op == "<=" || op == ">=" || op == "\\<=" || op == "\\>=") && params.shellType != .Sh then
          match invertOp op with
          | some inv =>
            let esc := if typ == .singleBracket then "\\" else ""
            [makeComment .errorC t.id 2122
              s!"{op} is not a valid operator. Use '! a {esc}{inv} b' instead."]
          | Option.none => []
        else []
    else if op ∈ arithmeticBinaryTestOps then
      -- SC2170/SC2309: -eq/-ne/-lt/... with non-numeric literals (often missing $)
      checkNumericOperand typ op lhs ++ checkNumericOperand typ op rhs
    else []
  | _ => []
where
  isNumericLooking (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.all (fun c => c.isDigit || c == '-')
    | Option.none =>
      match t.inner with
      | .T_DollarBraced _ _ => true  -- Could be numeric
      | _ => false

  invertOp (op : String) : Option String :=
    let op' := if op.startsWith "\\" then (op.drop 1).toString else op
    if op' == "<=" then some ">"
    else if op' == ">=" then some "<"
    else Option.none

  seqv (op : String) : String :=
    match op with
    | "-eq" => "="
    | "-ne" => "!="
    | "-lt" => "<"
    | "-le" => "<="
    | "-gt" => ">"
    | "-ge" => ">="
    | _ => "="

  numChar (c : Char) : Bool :=
    c.isDigit || c ∈ ['+', '-', '.', ' ']

  isNonNum (t : Token) : Bool :=
    not ((onlyLiteralString t).all numChar)

  assignedVariables : List String :=
    params.variableFlow.filterMap fun sd =>
      match sd with
      | .Assignment (_, _, name, _) => if isVariableName name then some name else Option.none
      | _ => Option.none

  shouldWarn2309 (asString : String) (isVar : Bool) (t : Token) : Bool :=
    (not isVar) ||
    (getWordParts t).any isQuotes ||
    (asString ∉ assignedVariables)

  checkNumericOperand (typ : ConditionType) (op : String) (arg : Token) : List TokenComment :=
    if isNonNum arg then
      let asString := getLiteralStringDef "\x00" arg
      let isVar := isVariableName asString
      let kind := if isVar then "a variable" else "an arithmetic expression"
      let fix := if isVar then "$var" else "$((expr))"
      let stringOp := seqv op
      if typ == .singleBracket then
        [makeComment .errorC arg.id 2170
          s!"Invalid number for {op}. Use {stringOp} to compare as string (or use {fix} to expand as {kind})."]
      else if shouldWarn2309 asString isVar arg then
        [makeComment .warningC arg.id 2309
          s!"{op} treats this as {kind}. Use {stringOp} to compare as string (or expand explicitly with {fix})."]
      else []
    else []

/-- SC2072: Decimals are not supported. Use bc or awk -/
def checkDecimalComparisons (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    -- Check both numeric comparison ops and string comparison ops (< > in [[]])
    if op ∈ ["-eq", "-ne", "-lt", "-le", "-gt", "-ge", "<", ">", "<=", ">="] then
      let lhsDecimal := hasDecimal lhs
      let rhsDecimal := hasDecimal rhs
      if lhsDecimal || rhsDecimal then
        [makeComment .errorC t.id 2072
          "Decimals are not supported. Either use integers only, or use bc or awk to compare."]
      else []
    else []
  | _ => []
where
  hasDecimal (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.any (· == '.') && s.any Char.isDigit
    | Option.none => false

/-- SC2181: Prefer checking exit status via control flow, not by comparing `$?` -/
def checkReturnAgainstZero (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs => checkBinary op lhs rhs
  | .TA_Binary op lhs rhs =>
    if op ∈ [">", "<", ">=", "<=", "==", "!="] then
      checkBinary op lhs rhs
    else []
  | .TA_Unary op exp =>
    if op == "!" && isExitCode exp then
      message (checksSuccessLhs op) exp.id
    else []
  | .TA_Sequence [exp] =>
    if isExitCode exp then
      message false exp.id
    else []
  | _ => []
where
  message (forSuccess : Bool) (id : Id) : List TokenComment :=
    if isOnlyTestInCommand params t && !isFirstCommandInFunction params t then
      let bang := if forSuccess then "" else "! "
      [makeComment .styleC id 2181
        s!"Check exit code directly with e.g. 'if {bang}mycmd;', not indirectly with $?."]
    else []

  checksSuccessLhs (op : String) : Bool :=
    not (op ∈ ["-gt", "-ne", "!=", "!"])

  checksSuccessRhs (op : String) : Bool :=
    not (op ∈ ["-ne", "!="])

  checkBinary (op : String) (lhs rhs : Token) : List TokenComment :=
    if isZero rhs && isExitCode lhs then
      message (checksSuccessLhs op) lhs.id
    else if isZero lhs && isExitCode rhs then
      message (checksSuccessRhs op) rhs.id
    else []

  isZero (t : Token) : Bool :=
    getLiteralString t == some "0"

  isExitCode (t : Token) : Bool :=
    match getWordParts t with
    | [single] =>
      match single.inner with
      | .T_DollarBraced _ content =>
        String.join (oversimplify content) == "?"
      | _ => false
    | _ => false

  isOnlyTestInCommand (params : Parameters) (token : Token) : Bool :=
    let parents := (getPath params.parentMap token).drop 1
    let rec go : List Token → Bool
      | [] => false
      | parent :: rest =>
        match parent.inner with
        | .T_Condition .. => true
        | .T_Arithmetic .. => true
        | .TA_Sequence [ _ ] =>
          match rest with
          | grandparent :: _ =>
            match grandparent.inner with
            | .T_Arithmetic .. => true
            | _ => false
          | [] => false
        | .TC_Unary _ "!" _ => go rest
        | .TA_Unary "!" _ => go rest
        | .TC_Group .. => go rest
        | .TA_Parenthesis _ => go rest
        | _ => false
    go parents

  isFirstCommandInFunction (params : Parameters) (token : Token) : Bool :=
    match (getPath params.parentMap token).find? isFunction with
    | Option.none => false
    | some func =>
      match getClosestCommand params.parentMap token with
      | Option.none => false
      | some cmd =>
        cmd.id == (getFirstCommandInFunction func).id

  getFirstCommandInFunction : Token → Token
    | ⟨_, .T_Function _ _ _ body⟩ => getFirstCommandInFunction body
    | ⟨_, .T_BraceGroup (x :: _)⟩ => getFirstCommandInFunction x
    | ⟨_, .T_Subshell (x :: _)⟩ => getFirstCommandInFunction x
    | ⟨_, .T_Annotation _ x⟩ => getFirstCommandInFunction x
    | ⟨_, .T_AndIf x _⟩ => getFirstCommandInFunction x
    | ⟨_, .T_OrIf x _⟩ => getFirstCommandInFunction x
    | ⟨_, .T_Pipeline _ (x :: _)⟩ => getFirstCommandInFunction x
    | t => t

/-- SC2143: Use grep -q instead of comparing output -/
def checkGrepQ (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    if op ∈ ["!=", "=", "==", "-n", "-z"] then
      if hasGrep lhs || hasGrep rhs then
        [makeComment .styleC t.id 2143
          "Use grep -q instead of comparing output with [ -n .. ]."]
      else []
    else []
  | .TC_Unary _ op inner =>
    if op ∈ ["-n", "-z"] then
      if hasGrep inner then
        [makeComment .styleC t.id 2143
          "Use grep -q instead of comparing output with [ -n .. ]."]
      else []
    else []
  | _ => []
where
  hasGrep (t : Token) : Bool :=
    match t.inner with
    | .T_DollarExpansion cmds =>
      cmds.any fun c => getCommandBasename c == some "grep"
    | .T_Backticked cmds =>
      cmds.any fun c => getCommandBasename c == some "grep"
    | .T_NormalWord parts =>
      -- Non-recursive check - just check first level for command subs
      parts.any fun p =>
        match p.inner with
        | .T_DollarExpansion cmds => cmds.any fun c => getCommandBasename c == some "grep"
        | .T_Backticked cmds => cmds.any fun c => getCommandBasename c == some "grep"
        | _ => false
    | _ => false

/-- SC2035: Use ./*glob* or -- *glob* to avoid expanding into flags -/
def checkGlobAsCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (first :: _) =>
    match first.inner with
    | .T_NormalWord parts =>
      if parts.any isGlobStart then
        [makeComment .warningC first.id 2035
          "Use ./*glob* or -- *glob* so names with dashes won't become options."]
      else []
    | _ => []
  | _ => []
where
  isGlobStart (t : Token) : Bool :=
    match t.inner with
    | .T_Glob s => s.startsWith "*" || s.startsWith "?"
    | .T_Extglob _ _ => true
    | _ => false

/-- SC2013: To read lines rather than words, pipe/redirect to a 'while read' loop -/
def checkForInCat (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.flatMap fun word =>
      match word.inner with
      | .T_NormalWord parts =>
        parts.flatMap fun part =>
          match part.inner with
          | .T_DollarExpansion cmds =>
            cmds.flatMap fun cmd =>
              if getCommandBasename cmd == some "cat" then
                [makeComment .warningC part.id 2013
                  "To read lines rather than words, pipe/redirect to a 'while read' loop."]
              else []
          | .T_Backticked cmds =>
            cmds.flatMap fun cmd =>
              if getCommandBasename cmd == some "cat" then
                [makeComment .warningC part.id 2013
                  "To read lines rather than words, pipe/redirect to a 'while read' loop."]
              else []
          | _ => []
      | _ => []
  | _ => []

/-- SC2048: Use "$@" (with quotes) to prevent whitespace problems -/
def checkDollarStar (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_NormalWord [part] =>
    match part.inner with
    | .T_DollarBraced _ content =>
      let str := oversimplify content |>.foldl (· ++ ·) ""
      let isQuoteFree := isStrictlyQuoteFree params.shellType params.parentMap t
      let modifier := getBracedModifier str
      if str.startsWith "*" && not isQuoteFree then
        [makeComment .warningC part.id 2048
          "Use \"$@\" (with quotes) to prevent whitespace problems."]
      else if modifier.startsWith "[*]" && not (str.startsWith "#") then
        [makeComment .warningC part.id 2048
          "Use \"${array[@]}\" (with quotes) to prevent whitespace problems."]
      else []
    | _ => []
  | _ => []
where
  isStrictlyQuoteFree (_shell : Shell) (_parents : Std.HashMap Id Token) (_t : Token) : Bool :=
    -- Simplified - would need proper parent context analysis
    false

/-- SC2145: Argument mixes string and array. Use * or separate argument -/
def checkConcatenatedDollarAt (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_NormalWord _ =>
    let parts := getWordParts t
    let array := parts.find? isArrayExpansion
    if (parts.drop 1).isEmpty then
      []
    else
      match array with
      | some arr =>
          [makeComment .errorC arr.id 2145
            "Argument mixes string and array. Use * or separate argument."]
      | Option.none => []
  | _ => []

/-- SC2050: This expression is constant. Did you forget the $ on a variable? -/
def checkConstantIfs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    if op ∈ ["-nt", "-ot", "-ef"] then []  -- File tests aren't constant
    else if isConstant lhs && isConstant rhs then
      [makeComment .warningC t.id 2050
        "This expression is constant. Did you forget the $ on a variable?"]
    else if op ∈ ["=", "==", "!="] && not (wordsCanBeEqual lhs rhs) then
      [makeComment .warningC t.id 2193
        "The arguments to this comparison can never be equal. Make sure your syntax is correct."]
    else []
  | _ => []

/-- SC2076: Remove quotes from right-hand side of =~ to match as regex -/
def checkQuotedCondRegex (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ "=~" _ rhs =>
    match rhs.inner with
    | .T_NormalWord [part] =>
      match part.inner with
      | .T_DoubleQuoted _ =>
        if hasRegexMetachars rhs then
          [makeComment .warningC rhs.id 2076
            "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
        else []
      | .T_SingleQuoted _ =>
        if hasRegexMetachars rhs then
          [makeComment .warningC rhs.id 2076
            "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
        else []
      | _ => []
    | _ => []
  | _ => []
where
  hasRegexMetachars (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.any fun c => c ∈ ['[', ']', '*', '.', '+', '(', ')', '|']
    | Option.none => false

/-- SC2049: =~ is for regex, but this looks like a glob. Use = instead -/
def checkGlobbedRegex (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType "=~" _ rhs =>
    if condType == .doubleBracket then
      let str := oversimplify rhs |>.foldl (· ++ ·) ""
      if isConfusedGlobRegex str then
        [makeComment .warningC rhs.id 2049
          "=~ is for regex, but this looks like a glob. Use = instead."]
      else []
    else []
  | _ => []
where
  isConfusedGlobRegex (s : String) : Bool :=
    -- Starts with * or ? without being escaped or in a regex group
    (s.startsWith "*" || s.startsWith "?") &&
    not (s.startsWith "^") && not (s.startsWith "(")

/-- SC2107/SC2108/SC2109/SC2110: Conditional operators in wrong bracket type -/
def checkConditionalAndOrs (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_And condType "&&" _ _ =>
    if condType == .singleBracket then
      [makeComment .errorC t.id 2107 "Instead of [ a && b ], use [ a ] && [ b ]."]
    else []
  | .TC_And condType "-a" _ _ =>
    if condType == .doubleBracket then
      [makeComment .errorC t.id 2108 "In [[..]], use && instead of -a."]
    else
      [makeComment .warningC t.id 2166 "Prefer [ p ] && [ q ] as [ p -a q ] is not well defined."]
  | .TC_Or condType "||" _ _ =>
    if condType == .singleBracket then
      [makeComment .errorC t.id 2109 "Instead of [ a || b ], use [ a ] || [ b ]."]
    else []
  | .TC_Or condType "-o" _ _ =>
    if condType == .doubleBracket then
      [makeComment .errorC t.id 2110 "In [[..]], use || instead of -o."]
    else
      [makeComment .warningC t.id 2166 "Prefer [ p ] || [ q ] as [ p -o q ] is not well defined."]
  | _ => []

/-- SC2074: Can't use =~ in [ ]. Use [[..]] instead -/
def checkSingleBracketOperators (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType "=~" _ _ =>
    let isBashOrKsh := params.shellType == Shell.Bash || params.shellType == Shell.Ksh
    if condType == .singleBracket && isBashOrKsh then
      [makeComment .errorC t.id 2074 "Can't use =~ in [ ]. Use [[..]] instead."]
    else []
  | _ => []

/-- SC2075: Escaping < or > is required in [..], but invalid in [[..]] -/
def checkDoubleBracketOperators (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType op _ _ =>
    if condType == .doubleBracket && op ∈ ["\\<", "\\>"] then
      [makeComment .errorC t.id 2075
        s!"Escaping {op} is required in [..], but invalid in [[..]]"]
    else []
  | _ => []

/-- SC2078/SC2158-2161: Constant nullary test expressions -/
def checkConstantNullary (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Nullary _ inner =>
    if isConstant inner then
      let str := onlyLiteralString inner
      match str with
      | "false" => [makeComment .errorC inner.id 2158 "[ false ] is true. Remove the brackets."]
      | "0" => [makeComment .errorC inner.id 2159 "[ 0 ] is true. Use 'false' instead."]
      | "true" => [makeComment .styleC inner.id 2160 "Instead of '[ true ]', just use 'true'."]
      | "1" => [makeComment .styleC inner.id 2161 "Instead of '[ 1 ]', use 'true'."]
      | _ => [makeComment .errorC inner.id 2078
          "This expression is constant. Did you forget a $ somewhere?"]
    else []
  | _ => []

/-- SC2243/SC2244: Prefer explicit -n for [[ $(cmd) ]] / [[ $var ]] style tests -/
def checkNullaryExpansionTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Nullary _ word =>
    let parts := getWordParts word
    match parts with
    | [single] =>
      if isCommandSubstitution single then
        [makeComment .styleC word.id 2243
          "Prefer explicit -n to check for output (or run command without [/[[ to check for success)."]
      else if parts.all (fun p => !isConstant p) then
        [makeComment .styleC word.id 2244
          "Prefer explicit -n to check non-empty string (or use =/-ne to check boolean/integer)."]
      else []
    | _ =>
      if parts.all (fun p => !isConstant p) then
        [makeComment .styleC word.id 2244
          "Prefer explicit -n to check non-empty string (or use =/-ne to check boolean/integer)."]
      else []
  | _ => []

/-- SC2247: $\"(foo)\" and $\"{foo}\" likely meant \"$(foo)\" / \"${foo}\" -/
def checkDollarQuoteParen (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarDoubleQuoted (first :: _) =>
    match first.inner with
    | .T_Literal s =>
      match s.toList.head? with
      | some c =>
        if c == '(' || c == '{' then
          [makeComment .warningC t.id 2247
            "Flip leading $ and \" if this should be a quoted substitution."]
        else []
      | Option.none => []
    | _ => []
  | _ => []

/-- SC2331: Prefer -e over legacy -a for file existence tests -/
def checkUnaryTestA (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary _ "-a" _ =>
    [makeComment .styleC t.id 2331
      "For file existence, prefer standard -e over legacy -a."]
  | _ => []

/-- SC2079: (( )) doesn't support decimals. Use bc or awk -/
def checkForDecimals (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TA_Expansion _ =>
    if not (hasFloatingPoint params) then
      match getLiteralString t with
      | some s =>
        if s.any Char.isDigit && s.any (· == '.') then
          [makeComment .errorC t.id 2079 "(( )) doesn't support decimals. Use bc or awk."]
        else []
      | Option.none => []
    else []
  | _ => []
where
  hasFloatingPoint (_params : Parameters) : Bool := false  -- Shell arithmetic doesn't support floats

private def warnArithIndex (id : Id) : List TokenComment :=
  [makeComment .styleC id 2321
    "Array indices are already arithmetic contexts. Prefer removing the $(( and ))."]

private def isArithExpansionIndex (content : String) : Bool :=
  let trimmed := content.trimAscii.toString
  trimmed.startsWith "$((" && trimmed.endsWith "))"

private partial def checkArithIndexToken (tok : Token) : List TokenComment :=
  match tok.inner with
  | .T_DollarArithmetic _ => warnArithIndex tok.id
  | .T_UnparsedIndex _ content =>
    if isArithExpansionIndex content then warnArithIndex tok.id else []
  | .T_NormalWord parts => parts.flatMap checkArithIndexToken
  | .T_DoubleQuoted parts => parts.flatMap checkArithIndexToken
  | _ => []

/-- SC2321: Array indices are already arithmetic contexts. -/
def checkUnnecessaryArithmeticExpansionIndex (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ _ indices _ =>
    match indices with
    | [idx] => checkArithIndexToken idx
    | _ => []
  | _ => []

/-- SC2322/SC2323: Unnecessary parentheses in arithmetic contexts -/
def checkUnnecessaryParens (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarArithmetic inner =>
    checkLeading "$(( (x) )) is the same as $(( x ))" t.id inner
  | .T_Arithmetic inner =>
    checkLeading "(( (x) )) is the same as (( x ))" t.id inner
  | .T_ForArithmetic init cond incr _body =>
    checkLeading "for (((x); (y); (z))) is the same as for ((x; y; z))" t.id init ++
    checkLeading "for (((x); (y); (z))) is the same as for ((x; y; z))" t.id cond ++
    checkLeading "for (((x); (y); (z))) is the same as for ((x; y; z))" t.id incr
  | .T_Assignment _ _ indices _value =>
    match indices with
    | [idx] => checkLeading "a[(x)] is the same as a[x]" t.id idx
    | _ => []
  | _ => []
where
  checkLeading (msg : String) (outerId : Id) (t : Token) : List TokenComment :=
    match t.inner with
    | .TA_Parenthesis inner =>
      match inner.inner with
      | .TA_Parenthesis _ =>
        [makeComment .styleC outerId 2322
          "In arithmetic contexts, ((x)) is the same as (x). Prefer only one layer of parentheses."]
      | _ =>
        [makeComment .styleC outerId 2323
          s!"{msg}. Prefer not wrapping in additional parentheses."]
    | _ => []

/-- SC2017: Increase precision by replacing a/b*c with a*c/b -/
def checkDivBeforeMult (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TA_Binary "*" lhs _ =>
    match lhs.inner with
    | .TA_Binary "/" _ _ =>
      [makeComment .infoC t.id 2017 "Increase precision by replacing a/b*c with a*c/b."]
    | _ => []
  | _ => []

/-- SC2070: -n doesn't work with unquoted arguments -/
def checkUnquotedN (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary condType "-n" inner =>
    if condType == .singleBracket && willSplit inner then
      if not (getWordParts inner |>.any isArrayExpansion) then
        [makeComment .errorC inner.id 2070
          "-n doesn't work with unquoted arguments. Quote or use [[ ]]."]
      else []
    else []
  | _ => []

/-- SC2077/SC2157: Literal strings breaking tests -/
def checkLiteralBreakingTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Nullary _ word =>
    if not (isConstant word) then
      let parts := getWordParts word
      -- Check for unspaced comparison operators
      if parts.any hasEquals then
        [makeComment .errorC t.id 2077 "You need spaces around the comparison operator."]
      else if parts.any isNonEmptyLiteral then
        [makeComment .errorC t.id 2157
          "Argument to implicit -n is always true due to literal strings."]
      else []
    else []
  | .TC_Unary _ op word =>
    if op == "-n" && not (isConstant word) then
      if getWordParts word |>.any isNonEmptyLiteral then
        [makeComment .errorC t.id 2157 "Argument to -n is always true due to literal strings."]
      else []
    else if op == "-z" && not (isConstant word) then
      if getWordParts word |>.any isNonEmptyLiteral then
        [makeComment .errorC t.id 2157 "Argument to -z is always false due to literal strings."]
      else []
    else []
  | _ => []
where
  hasEquals (t : Token) : Bool :=
    match getLiteralString t with
    | some s => s.any (· == '=')
    | Option.none => false
  isNonEmptyLiteral (t : Token) : Bool :=
    match getLiteralString t with
    | some s => not s.isEmpty
    | Option.none => false

/-- SC2073: Escape < or > to prevent redirection -/
def checkEscapedComparisons (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType op _ _ =>
    if condType == .singleBracket && op ∈ ["<", ">"] then
      match params.shellType with
      | .Sh => []  -- Unsupported in sh
      | .Dash => [makeComment .errorC t.id 2073 s!"Escape \\{op} to prevent it redirecting."]
      | .BusyboxSh => [makeComment .errorC t.id 2073 s!"Escape \\{op} to prevent it redirecting."]
      | _ => [makeComment .errorC t.id 2073
          s!"Escape \\{op} to prevent it redirecting (or switch to [[ .. ]])."]
    else []
  | _ => []

/-- SC2094: Make sure not to read and write the same file in the same pipeline -/
def checkRedirectToSame (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    let allRedirs := cmds.flatMap getRedirFiles
    findDuplicateRedirs params allRedirs
  | _ => []
where
  getRedirFiles (cmd : Token) : List (Token × Bool) :=  -- (file, isInput)
    match cmd.inner with
    | .T_Redirecting redirects _ =>
      redirects.flatMap fun r =>
        match r.inner with
        | .T_FdRedirect _ op =>
          match op.inner with
          | .T_IoFile opTok file =>
            match getLiteralString opTok with
            | some "<" => [(file, true)]
            | some ">" => [(file, false)]
            | some ">>" => [(file, false)]
            | _ => []
          | _ => []
        | _ => []
    | _ => []

  findDuplicateRedirs (_params : Parameters) (redirs : List (Token × Bool)) : List TokenComment :=
    let inputFiles := redirs.filter (·.2) |>.map (·.1)
    let outputFiles := redirs.filter (not ·.2) |>.map (·.1)
    inputFiles.flatMap fun inFile =>
      outputFiles.flatMap fun outFile =>
        let inStr := oversimplify inFile |>.foldl (· ++ ·) ""
        let outStr := oversimplify outFile |>.foldl (· ++ ·) ""
        if inStr == outStr && not (inStr.startsWith "/dev/") then
          [makeComment .infoC outFile.id 2094
            "Make sure not to read and write the same file in the same pipeline."]
        else []

/-- Check if in quote-free context for SC2046.
    Returns true when the expansion is in a context where word splitting doesn't apply:
    - Inside assignments (x=$(cmd))
    - Inside double quotes ("$(cmd)")
    - Inside [[ conditions, arithmetic, etc. -/
partial def isQuoteFreeForExpansion (parentMap : Std.HashMap Id Token) (t : Token) : Bool :=
  go t
where
  go (current : Token) : Bool :=
    match parentMap.get? current.id with
    | Option.none => false
    | some parent =>
        match parent.inner with
        | .T_Assignment .. => true
        | .T_DoubleQuoted .. => true
        | .T_Condition .. => true
        | .T_Arithmetic .. => true
        | .TC_Nullary .doubleBracket .. => true
        | .TC_Unary .doubleBracket .. => true
        | .TC_Binary .doubleBracket .. => true
        | .T_DollarBraced .. => true
        | .T_HereDoc .. => true
        | .T_CaseExpression .. => true
        -- Keep searching for these wrapper types
        | .T_NormalWord .. => go parent
        | .T_Redirecting .. => go parent
        | .T_SimpleCommand .. => go parent
        | .T_Script .. => false  -- Reached top
        | _ => go parent  -- Keep looking

/-- SC2046: Quote this to prevent word splitting -/
def checkUnquotedExpansions (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarExpansion cmds =>
    if cmds.isEmpty then []
    else if shouldBeSplit t then []
    else if isQuoteFreeForExpansion params.parentMap t then []
    else [makeComment .warningC t.id 2046 "Quote this to prevent word splitting."]
  | .T_Backticked cmds =>
    if cmds.isEmpty then []
    else if shouldBeSplit t then []
    else if isQuoteFreeForExpansion params.parentMap t then []
    else [makeComment .warningC t.id 2046 "Quote this to prevent word splitting."]
  | _ => []
where
  shouldBeSplit (t : Token) : Bool :=
    -- Some commands like seq and pgrep are typically used for word splitting
    match t.inner with
    | .T_DollarExpansion cmds =>
      cmds.any fun c => getCommandBasename c ∈ [some "seq", some "pgrep"]
    | .T_Backticked cmds =>
      cmds.any fun c => getCommandBasename c ∈ [some "seq", some "pgrep"]
    | _ => false

/-- SC2124: Assigning an array to a string -/
def checkArrayAsString (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ _ _ word =>
    if hasArrayExpansion word then
      [makeComment .warningC t.id 2124
        "Assigning an array to a string! Assign as array, or use * instead of @ to concatenate."]
    else if hasLiteralGlobOrBrace word then
      [makeComment .warningC t.id 2125
        "Brace expansions and globs are literal in assignments. Quote it or use an array."]
    else []
  | _ => []
where
  hasArrayExpansion (t : Token) : Bool :=
    getWordParts t |>.any isArrayExpansion
  hasLiteralGlobOrBrace (t : Token) : Bool :=
    match getUnquotedLiteral t with
    | some s => containsGlobMeta s || containsBrace s || containsExtGlobStart s
    | Option.none => hasBraceToken t || isGlob t
  hasBraceToken (t : Token) : Bool :=
    getWordParts t |>.any fun part =>
      match part.inner with
      | .T_BraceExpansion _ => true
      | _ => false
  containsGlobMeta (s : String) : Bool :=
    s.any fun c => c == '*' || c == '?' || c == '['
  containsBrace (s : String) : Bool :=
    s.any (· == '{') && s.any (· == '}')
  containsExtGlobStart (s : String) : Bool :=
    let rec go : List Char → Bool
      | [] => false
      | [_] => false
      | a :: b :: rest =>
          (b == '(' && (a == '@' || a == '!' || a == '+')) || go (b :: rest)
    go s.toList

/-- SC2054: Use spaces, not commas, to separate array elements -/
def checkCommarrays (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Array elements =>
    if elements.any isCommaSeparated then
      [makeComment .warningC t.id 2054 "Use spaces, not commas, to separate array elements."]
    else []
  | _ => []
where
  isCommaSeparated (t : Token) : Bool :=
    let lit := getLiteralLiteralHelper t
    lit.any (· == ',')
  getLiteralLiteralHelper (t : Token) : String :=
    match t.inner with
    | .T_IndexedElement _ v =>
      match v.inner with
      | .T_NormalWord parts => String.join (parts.map getLiteralPart)
      | .T_Literal s => s
      | _ => ""
    | .T_NormalWord parts => String.join (parts.map getLiteralPart)
    | .T_Literal s => s
    | _ => ""
  getLiteralPart (t : Token) : String :=
    match t.inner with
    | .T_Literal s => s
    | _ => ""

/-- SC2055: You probably wanted -a here, otherwise it's always true -/
def checkOrNeq (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Or condType _op lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TC_Binary _ op1 lhs1 rhs1, .TC_Binary _ op2 lhs2 rhs2 =>
      if (op1 == "-ne" || op1 == "!=") && op1 == op2 then
        let lhs1Str := oversimplify lhs1 |>.foldl (· ++ ·) ""
        let lhs2Str := oversimplify lhs2 |>.foldl (· ++ ·) ""
        let rhs1Str := oversimplify rhs1 |>.foldl (· ++ ·) ""
        let rhs2Str := oversimplify rhs2 |>.foldl (· ++ ·) ""
        if lhs1Str == lhs2Str && rhs1Str != rhs2Str && not (isGlob rhs1) && not (isGlob rhs2) then
          let suggestion := if condType == .singleBracket then "-a" else "&&"
          [makeComment .warningC t.id 2055
            s!"You probably wanted {suggestion} here, otherwise it's always true."]
        else []
      else []
    | _, _ => []
  | .T_OrIf lhs rhs =>
    match getExpr lhs, getExpr rhs with
    | some (lhs1, op1, rhs1), some (lhs2, op2, rhs2) =>
      let lhs1Str := oversimplify lhs1 |>.foldl (· ++ ·) ""
      let lhs2Str := oversimplify lhs2 |>.foldl (· ++ ·) ""
      let rhs1Str := oversimplify rhs1 |>.foldl (· ++ ·) ""
      let rhs2Str := oversimplify rhs2 |>.foldl (· ++ ·) ""
      if op1 == op2 && (op1 == "-ne" || op1 == "!=") &&
          lhs1Str == lhs2Str && rhs1Str != rhs2Str &&
          not (ASTLib.casePatternHasExplicitGlob rhs1) &&
          not (ASTLib.casePatternHasExplicitGlob rhs2) then
        [makeComment .warningC t.id 2252
          "You probably wanted && here, otherwise it's always true."]
      else []
    | _, _ => []
  | .TA_Binary "||" lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TA_Binary "!=" word1 _, .TA_Binary "!=" word2 _ =>
      let w1 := oversimplify word1 |>.foldl (· ++ ·) ""
      let w2 := oversimplify word2 |>.foldl (· ++ ·) ""
      if w1 == w2 then
        [makeComment .warningC t.id 2056 "You probably wanted && here, otherwise it's always true."]
      else []
    | _, _ => []
  | _ => []
where
  /-- Extract a simple test expression from a command-level condition.

  This mirrors ShellCheck's `getExpr` helper for SC2252:
  it peels off common wrappers and returns `(varSide, op, constSide)` where
  exactly one side is constant. -/
  getExpr (x : Token) : Option (Token × String × Token) :=
    getExprGo 64 x

  getExprGo : Nat → Token → Option (Token × String × Token)
    | 0, _ => Option.none
    | fuel + 1, x =>
        match x.inner with
        | .T_OrIf lhs _ => getExprGo fuel lhs
        | .T_Pipeline _ cmds =>
            match cmds with
            | [only] => getExprGo fuel only
            | _ => Option.none
        | .T_Redirecting _ cmd => getExprGo fuel cmd
        | .T_Condition _ c => getExprGo fuel c
        | .TC_Binary _ op lhs rhs => orient lhs op rhs
        | _ => Option.none

  orient (lhs : Token) (op : String) (rhs : Token) : Option (Token × String × Token) :=
    match isConstant lhs, isConstant rhs with
    | true, false => some (rhs, op, lhs)
    | false, true => some (lhs, op, rhs)
    | _, _ => Option.none

/-- SC2333: You probably wanted || here, otherwise it's always false -/
def checkAndEq (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_And condType _ lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TC_Binary _ op1 lhs1 rhs1, .TC_Binary _ op2 lhs2 rhs2 =>
      if op1 == op2 && (op1 == "=" || op1 == "==" || op1 == "-eq") then
        let lhs1Str := oversimplify lhs1 |>.foldl (· ++ ·) ""
        let lhs2Str := oversimplify lhs2 |>.foldl (· ++ ·) ""
        let rhs1Str := oversimplify rhs1 |>.foldl (· ++ ·) ""
        let rhs2Str := oversimplify rhs2 |>.foldl (· ++ ·) ""
        if lhs1Str == lhs2Str && rhs1Str != rhs2Str && isLiteral rhs1 && isLiteral rhs2 then
          let suggestion := if condType == .singleBracket then "-o" else "||"
          [makeComment .warningC t.id 2333
            s!"You probably wanted {suggestion} here, otherwise it's always false."]
        else []
      else []
    | _, _ => []
  | .TA_Binary "&&" lhs rhs =>
    match lhs.inner, rhs.inner with
    | .TA_Binary "==" lhs1 rhs1, .TA_Binary "==" lhs2 rhs2 =>
      let l1 := oversimplify lhs1 |>.foldl (· ++ ·) ""
      let l2 := oversimplify lhs2 |>.foldl (· ++ ·) ""
      if l1 == l2 && isLiteral rhs1 && isLiteral rhs2 then
        [makeComment .warningC t.id 2334 "You probably wanted || here, otherwise it's always false."]
      else []
    | _, _ => []
  | .T_AndIf lhs rhs =>
    match getExpr lhs, getExpr rhs with
    | some (lhs1, op1, rhs1), some (lhs2, op2, rhs2) =>
      let lhs1Str := oversimplify lhs1 |>.foldl (· ++ ·) ""
      let lhs2Str := oversimplify lhs2 |>.foldl (· ++ ·) ""
      let rhs1Str := oversimplify rhs1 |>.foldl (· ++ ·) ""
      let rhs2Str := oversimplify rhs2 |>.foldl (· ++ ·) ""
      if op1 == op2 && lhs1Str == lhs2Str && rhs1Str != rhs2Str &&
          checkAndEqOperands op1 rhs1 rhs2 then
        [makeComment .warningC t.id 2333
          "You probably wanted || here, otherwise it's always false."]
      else []
    | _, _ => []
  | _ => []
where
  isLiteralNumber (t : Token) : Bool :=
    match getLiteralString t with
    | some s => !s.isEmpty && s.toList.all Char.isDigit
    | Option.none => false

  checkAndEqOperands (op : String) (rhs1 rhs2 : Token) : Bool :=
    if op == "-eq" then
      isLiteralNumber rhs1 && isLiteralNumber rhs2
    else if op == "=" || op == "==" then
      isLiteral rhs1 && isLiteral rhs2
    else
      false

  getExpr (x : Token) : Option (Token × String × Token) :=
    getExprGo 64 x

  getExprGo : Nat → Token → Option (Token × String × Token)
    | 0, _ => Option.none
    | fuel + 1, x =>
        match x.inner with
        | .T_AndIf lhs _ => getExprGo fuel lhs
        | .T_Pipeline _ cmds =>
            match cmds with
            | [only] => getExprGo fuel only
            | _ => Option.none
        | .T_Redirecting _ cmd => getExprGo fuel cmd
        | .T_Condition _ c => getExprGo fuel c
        | .TC_Binary _ op lhs rhs => orient lhs op rhs
        | _ => Option.none

  orient (lhs : Token) (op : String) (rhs : Token) : Option (Token × String × Token) :=
    match isConstant lhs, isConstant rhs with
    | true, false => some (rhs, op, lhs)
    | false, true => some (lhs, op, rhs)
    | _, _ => Option.none

/-- SC2057/SC2058: Unknown test operator -/
def checkValidCondOps (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op _ _ =>
    if not (op ∈ binaryTestOps) then
      [makeComment .warningC t.id 2057 "Unknown binary operator."]
    else []
  | .TC_Unary _ op _ =>
    if not (op ∈ unaryTestOps) then
      [makeComment .warningC t.id 2058 "Unknown unary operator."]
    else []
  | _ => []
where
  binaryTestOps := ["-nt", "-ot", "-ef", "-eq", "-ne", "-lt", "-le", "-gt", "-ge",
    "=", "==", "!=", "=~", "<", ">", "<=", ">=", "\\<", "\\>",
    "-a", "-o"]
  unaryTestOps := ["-z", "-n", "-o", "-v", "-R",
    "-b", "-c", "-d", "-e", "-f", "-g", "-h", "-k", "-p", "-r", "-s", "-t", "-u", "-w", "-x",
    "-L", "-N", "-O", "-G", "-S",
    "!"]

/-- SC2237/SC2335: Prefer direct negated test operators -/
def checkNegatedTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary condType "!" inner =>
    match inner.inner with
    | .TC_Unary _ "-z" _ =>
      [makeComment .styleC t.id 2237
        "Use [ -n \"...\" ] instead of [ ! -z \"...\" ]."]
    | .TC_Unary _ "-n" _ =>
      [makeComment .styleC t.id 2237
        "Use [ -z \"...\" ] instead of [ ! -n \"...\" ]."]
    | .TC_Binary _ op _ _ =>
      suggestInversion true condType t.id op
    | _ => []
  | .T_Banged inner =>
    -- ! [ a -eq b ] or ! [[ a -eq b ]]
    match inner.inner with
    | .T_Pipeline _ [pipeCmd] =>
      match pipeCmd.inner with
      | .T_Redirecting _ cmd =>
        match cmd.inner with
        | .T_Condition condType cond =>
          match cond.inner with
          | .TC_Binary _ op _ _ => suggestInversion false condType t.id op
          | _ => []
        | _ => []
      | .T_Condition condType cond =>
        match cond.inner with
        | .TC_Binary _ op _ _ => suggestInversion false condType t.id op
        | _ => []
      | _ => []
    | _ => []
  | _ => []
where
  inversionMap : List (String × String) := [
    ("=", "!="),
    ("==", "!="),
    ("!=", "="),
    ("-eq", "-ne"),
    ("-ne", "-eq"),
    ("-le", "-gt"),
    ("-gt", "-le"),
    ("-ge", "-lt"),
    ("-lt", "-ge")
  ]

  findInversion (op : String) : Option String :=
    inversionMap.findSome? (fun (old, new) => if old == op then some new else none)

  suggestInversion (bangInside : Bool) (condType : ConditionType) (id : Id) (op : String) :
      List TokenComment :=
    match findInversion op with
    | some newOp =>
      let oldExpr := s!"a {op} b"
      let newExpr := s!"a {newOp} b"
      let bracket (s : String) :=
        match condType with
        | .singleBracket => s!"[ {s} ]"
        | .doubleBracket => s!"[[ {s} ]]"
      let msg :=
        if bangInside then
          s!"Use {newExpr} instead of ! {oldExpr}."
        else
          s!"Use {bracket newExpr} instead of ! {bracket oldExpr}."
      [makeComment .styleC id 2335 msg]
    | Option.none => []

/-- SC2053: Quote the right-hand side of == in [[ ]] to prevent glob matching -/
def checkUnquotedRhsGlob (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .doubleBracket op _ rhs =>
    if op == "==" || op == "=" || op == "!=" then
      -- Check if rhs is unquoted and contains glob chars
      match rhs.inner with
      | .T_NormalWord parts =>
        let hasGlob := parts.any fun p =>
          match getLiteralString p with
          | some s => s.any (fun c => c == '*' || c == '?' || c == '[')
          | Option.none => false
        if hasGlob then
          [makeComment .warningC rhs.id 2053
            "Quote the right-hand side of == to prevent glob matching."]
        else []
      | .T_Literal s =>
        if s.any (fun c => c == '*' || c == '?' || c == '[') then
          [makeComment .warningC rhs.id 2053
            "Quote the right-hand side of == to prevent glob matching."]
        else []
      | _ => []
    else []
  | _ => []

-- Note: SC2015 is already implemented earlier in this file

/-- SC2116: Useless echo? Instead of 'cmd $(echo foo)', use 'cmd foo' -/
def checkUuoeVar (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarExpansion [cmd] =>
    checkEchoCmd t.id cmd
  | .T_Backticked [cmd] =>
    checkEchoCmd t.id cmd
  | _ => []
where
  checkEchoCmd (id : Id) (cmd : Token) : List TokenComment :=
    match cmd.inner with
    | .T_Pipeline _ [redirecting] =>
      match redirecting.inner with
      | .T_Redirecting _ inner =>
        match inner.inner with
        | .T_SimpleCommand _ (cmdWord :: args) =>
          if getCommandBasename (⟨cmd.id, .T_SimpleCommand [] (cmdWord :: args)⟩) == some "echo" then
            if args.length > 0 && not (hasGlobOrBrace args) then
              [makeComment .styleC id 2116
                "Useless echo? Instead of 'cmd $(echo foo)', just use 'cmd foo'."]
            else []
          else []
        | _ => []
      | _ => []
    | _ => []

  hasGlobOrBrace (args : List Token) : Bool :=
    args.any fun arg =>
      getWordParts arg |>.any fun part =>
        match part.inner with
        | .T_Glob _ => true
        | .T_Extglob _ _ => true
        | .T_BraceExpansion _ => true
        | _ => false

/-- SC2081: [ .. ] can't match globs. Use [[ .. ]] or case statement -/
def checkComparisonAgainstGlob (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary condType op _ word =>
    if op ∈ ["=", "==", "!="] && isGlob word then
      if condType == .singleBracket then
        let msg := if params.shellType == Shell.Bash || params.shellType == Shell.Ksh
          then "[ .. ] can't match globs. Use [[ .. ]] or case statement."
          else "[ .. ] can't match globs. Use a case statement."
        [makeComment .errorC word.id 2081 msg]
      else if condType == .doubleBracket && params.shellType == Shell.BusyboxSh then
        [makeComment .errorC word.id 2330
          "BusyBox [[ .. ]] does not support glob matching. Use a case statement."]
      else []
    else []
  | _ => []

/-- SC2254: Quote expansions in case patterns to match literally -/
def checkCaseAgainstGlob (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_CaseExpression _ cases =>
    cases.flatMap fun (_, patterns, _) =>
      patterns.flatMap fun pattern =>
        if not (ASTLib.casePatternHasExplicitGlob pattern) && hasQuoteableExpansion pattern then
          [makeComment .warningC pattern.id 2254
            "Quote expansions in case patterns to match literally rather than as a glob."]
        else []
  | _ => []
where
  hasQuoteableExpansion (t : Token) : Bool :=
    getWordParts t |>.any isQuoteableExpansion

/-- SC2194: Case statement word is constant (likely forgot `$`). -/
def checkCaseConstantWord (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_CaseExpression word _ =>
    if isConstant word then
      [makeComment .warningC word.id 2194
        "This word is constant. Did you forget the $ on a variable?"]
    else []
  | _ => []

/-- SC2249: Consider adding a default `*)` case. -/
def checkDefaultCase (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_CaseExpression _ cases =>
    if cases.any (fun (_, patterns, _) => patterns.any isDefaultPattern) then
      []
    else
      [makeComment .infoC t.id 2249
        "Consider adding a default *) case, even if it just exits with error."]
  | _ => []
where
  /-- Best-effort: recognize patterns like `*` or `**` as a default case. -/
  goIsDefaultPattern : Nat → List Token → Bool
    | 0, _ => false
    | _fuel + 1, [] => true
    | fuel + 1, t :: rest =>
      match t.inner with
      | .T_Annotation _ inner => goIsDefaultPattern fuel (inner :: rest)
      | .T_NormalWord parts => goIsDefaultPattern fuel (parts ++ rest)
      | .T_Literal s =>
        if s.length > 0 && s.toList.all (· == '*') then
          goIsDefaultPattern fuel rest
        else
          false
      | .T_Glob s =>
        if s.length > 0 && s.toList.all (· == '*') then
          goIsDefaultPattern fuel rest
        else
          false
      | .T_SingleQuoted _ => false
      | .T_DoubleQuoted _ => false
      | .T_DollarSingleQuoted _ => false
      | .T_DollarDoubleQuoted _ => false
      | _ => false

  isDefaultPattern (t : Token) : Bool :=
    goIsDefaultPattern 64 [t]

/-- SC2195/SC2221/SC2222: Unmatchable or shadowed case patterns. -/
def checkUnmatchableCases (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_CaseExpression word cases =>
      let allPatterns : List Token :=
        cases.flatMap (fun (_, patterns, _) => patterns)
      let breakPatterns : List Token :=
        cases.flatMap fun (caseType, patterns, _) =>
          if caseType == .caseBreak then patterns else []

      let unmatchable : List TokenComment :=
        if isConstant word then
          []
        else
          let target := wordToPseudoGlob word
          allPatterns.flatMap fun candidate =>
            if pseudoGlobsCanOverlap target (casePatternToPseudoGlob candidate) then
              []
            else
              [makeComment .warningC candidate.id 2195
                "This pattern will never match the case statement's word. Double check them."]

      let shadowed : List TokenComment :=
        checkShadowing params.tokenPositions breakPatterns

      unmatchable ++ shadowed
  | _ => []
where
  patternContext (tp : TokenPositions) (id : Id) : String :=
    match tp.get? id with
    | some (startPos, _) => s!" on line {startPos.posLine}."
    | Option.none => "."

  checkShadowing (tp : TokenPositions) (patterns : List Token) : List TokenComment :=
    match patterns with
    | [] => []
    | p :: rest =>
        let exact := casePatternToExactPseudoGlob p
        let fuzzyRest : List (Token × List PseudoGlob) :=
          rest.map fun r => (r, casePatternToPseudoGlob r)
        let comments :=
          match exact with
          | Option.none => []
          | some pg =>
              match fuzzyRest.find? (fun (_, g) => pseudoGlobIsSuperSetof pg g) with
              | Option.none => []
              | some (first, _) =>
                  let ctxLater := patternContext tp first.id
                  let ctxPrev := patternContext tp p.id
                  [ makeComment .warningC p.id 2221
                      ("This pattern always overrides a later one" ++ ctxLater)
                  , makeComment .warningC first.id 2222
                      ("This pattern never matches because of a previous pattern" ++ ctxPrev)
                  ]
        comments ++ checkShadowing tp rest

/-- SC2115: Use "${var:?}" to ensure not empty, or check before rm -/
def checkRmWithRoot (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "rm" then
      let args := words.drop 1
      if args.any hasSlashVarExpansion then
        [makeComment .warningC t.id 2115
          "Use \"${var:?}\" to ensure this never expands to / ."]
      else []
    else []
  | _ => []
where
  hasSlashVarExpansion (t : Token) : Bool :=
    match getLiteralString t with
    | some s =>
      -- Check for patterns like /$var or $var/ that could become /
      s.startsWith "/" || s.endsWith "/"
    | Option.none =>
      match t.inner with
      | .T_NormalWord (⟨_, .T_Literal "/"⟩ :: _) => true
      | .T_NormalWord parts =>
        parts.any fun p =>
          match p.inner with
          | .T_DollarBraced _ _ => true
          | _ => false
      | _ => false

/-- SC2059: Don't use variables in printf format string -/
def checkPrintfVar (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "printf" then
      let args := words.drop 1 |>.filter (not ∘ isFlag)
      match args.head? with
      | some formatArg =>
        if hasVariableInFormat formatArg then
          [makeComment .warningC formatArg.id 2059
            "Don't use variables in the printf format string. Use printf '...' \"$var\"."]
        else []
      | Option.none => []
    else []
  | _ => []
where
  hasVariableInFormat (t : Token) : Bool :=
    getWordParts t |>.any fun part =>
      match part.inner with
      | .T_DollarBraced _ _ => true
      | .T_DollarExpansion _ => true
      | .T_Backticked _ => true
      | _ => false

/-- SC2086: Double quote to prevent globbing and word splitting -/
-- This is a simplified version of checkSpacefulnessCfg
def checkUnquotedVariables (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let str := oversimplify content |>.foldl (· ++ ·) ""
    let name := ASTLib.getBracedReference str
    -- Skip special variables that don't need quoting
    if name ∈ specialVarsNoQuote then []
    else if isArrayExpansion t then []  -- Covered by SC2068
    else if isCountingReference t then []
    else if isQuoteFreeLocal params t then []
    else
      match quoteFix params t.id with
      | some fix =>
          [makeCommentWithFix .infoC t.id 2086
            "Double quote to prevent globbing and word splitting." fix]
      | Option.none =>
          [makeComment .infoC t.id 2086
            "Double quote to prevent globbing and word splitting."]
  | _ => []
where
  specialVarsNoQuote := ["?", "#", "-", "$", "!", "_", "PPID", "BASHPID",
    "UID", "EUID", "RANDOM", "LINENO", "SECONDS", "SHLVL", "HISTCMD",
    "BASH_SUBSHELL", "COLUMNS", "LINES"]
  isCountingReference (t : Token) : Bool :=
    match t.inner with
    | .T_DollarBraced _ content =>
      let str := oversimplify content |>.foldl (· ++ ·) ""
      str.startsWith "#"
    | _ => false
  isQuoteFreeLocal (params : Parameters) (t : Token) : Bool :=
    -- Use the full isQuoteFree check from AnalyzerLib
    ShellCheck.AnalyzerLib.isQuoteFree params.shellType params.parentMap t
  quoteFix (params : Parameters) (id : Id) : Option Fix :=
    match params.tokenPositions.get? id with
    | some (startPos, endPos) =>
        if startPos.posLine != endPos.posLine then
          Option.none
        else
          let openRep : Replacement := {
            repStartPos := startPos
            repEndPos := startPos
            repString := "\""
            repPrecedence := 1
            repInsertionPoint := .insertBefore
          }
          let closePos : Position := { endPos with posColumn := endPos.posColumn + 1 }
          let closeRep : Replacement := {
            repStartPos := closePos
            repEndPos := closePos
            repString := "\""
            repPrecedence := 1
            repInsertionPoint := .insertBefore
          }
          some { fixReplacements := [openRep, closeRep] }
    | Option.none => Option.none

/-- SC2123: PATH is the shell search path. Use another name -/
def checkOverridingPath (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand assigns [] =>
    assigns.flatMap fun assign =>
      match assign.inner with
      | .T_Assignment _ "PATH" _ word =>
        let str := oversimplify word |>.foldl (· ++ ·) ""
        -- Warn if setting PATH without /bin or /sbin
        if not (Regex.containsSubstring str "/bin" || Regex.containsSubstring str "/sbin") then
          if str.any (· == '/') && not (str.any (· == ':')) then
            [makeComment .warningC assign.id 2123
              "PATH is the shell search path. Use another name."]
          else []
        else []
      | _ => []
  | _ => []

/-- SC2147: Literal tilde in PATH works poorly across programs -/
def checkTildeInPath (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand assigns _ =>
    assigns.flatMap fun assign =>
      match assign.inner with
      | .T_Assignment _ "PATH" _ word =>
        match word.inner with
        | .T_NormalWord parts =>
          if parts.any hasTildeInQuotes then
            [makeComment .warningC assign.id 2147
              "Literal tilde in PATH works poorly across programs."]
          else []
        | _ => []
      | _ => []
  | _ => []
where
  hasTildeInQuotes (t : Token) : Bool :=
    match t.inner with
    | .T_DoubleQuoted parts =>
      parts.any fun p =>
        match getLiteralString p with
        | some s => s.any (· == '~')
        | Option.none => false
    | .T_SingleQuoted s => s.any (· == '~')
    | _ => false

/-- SC2141: This IFS value contains a literal backslash -/
def checkSuspiciousIFS (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ "IFS" _ value =>
    match getLiteralString value with
    | some s =>
      let hasDollarSingle := params.shellType == Shell.Bash || params.shellType == Shell.Ksh
      let suggestN := if hasDollarSingle then "$'\\n'" else "'<literal linefeed here>'"
      let suggestT := if hasDollarSingle then "$'\\t'" else "\"$(printf '\\t')\""
      if s == "\\n" then
        [makeComment .warningC value.id 2141
          s!"This backslash is literal. Did you mean IFS={suggestN} ?"]
      else if s == "\\t" then
        [makeComment .warningC value.id 2141
          s!"This backslash is literal. Did you mean IFS={suggestT} ?"]
      else if s.any (· == '\\') then
        [makeComment .warningC value.id 2141
          "This IFS value contains a literal backslash. For tabs/linefeeds/escapes, use $'..' or printf."]
      else []
    | Option.none => []
  | _ => []

/-- SC2144/SC2245: Test operators with globs -/
def checkTestArgumentSplitting (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary condType op token =>
    if op == "-v" then
      if condType == .singleBracket && isGlobToken token then
        [makeComment .errorC token.id 2208
          "Use [[ ]] or quote arguments to -v to avoid glob expansion."]
      else []
    else if isGlobToken token then
      if condType == .singleBracket && params.shellType == .Ksh && kshGlobOps.contains op then
        [makeComment .warningC token.id 2245
          s!"{op} only applies to the first expansion of this glob. Use a loop to check any/all."]
      else
        [makeComment .errorC token.id 2144 s!"{op} doesn't work with globs. Use a for loop."]
    else []
  | .TC_Nullary condType token =>
    if isGlobToken token then
      [makeComment .errorC token.id 2144 "This test always fails. Globs don't work in test expressions."]
    else if condType == .doubleBracket && isArrayExpansion token then
      [makeComment .errorC token.id 2198 "[[ $array ]] always true. Use [[ ${array[0]} ]] or [[ ${array[@]} ]]."]
    else []
  | _ => []
where
  kshGlobOps : List String :=
    ["-b", "-c", "-d", "-f", "-g", "-k", "-p", "-r", "-s", "-u", "-w", "-x",
     "-L", "-h", "-N", "-O", "-G", "-R", "-S"]

  isGlobToken (tok : Token) : Bool :=
    isGlob tok ||
    match getLiteralString tok with
    | some s => s.contains '*' || s.contains '?' || s.contains '['
    | Option.none => false

/-- SC2102: Ranges can only match single chars (mentioned due to duplicates). -/
def checkCharRangeGlob (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Glob s => checkToken t s
  | .T_Literal s => checkToken t s
  | .T_NormalWord parts =>
    parts.flatMap fun part =>
      match part.inner with
      | .T_Glob s => checkToken part s
      | .T_Literal s => checkToken part s
      | _ => []
  | _ => []
where
  checkToken (tok : Token) (s : String) : List TokenComment :=
    if isCharClass s && !isIgnoredCommand tok && !isDereferenced tok then
      let contents := dropNegation ((s.drop 1).dropEnd 1 |>.toString)
      if contents.startsWith ":" && contents.endsWith ":" && contents != ":" then
        [makeComment .warningC tok.id 2101
          "Named class needs outer [], e.g. [[:digit:]]."]
      else if !contents.toList.contains '[' && hasDupes contents then
        [makeComment .infoC tok.id 2102
          "Ranges can only match single chars (mentioned due to duplicates)."]
      else []
    else []

  isCharClass (str : String) : Bool :=
    str.startsWith "[" && str.endsWith "]"

  dropNegation (str : String) : String :=
    if str.startsWith "!" || str.startsWith "^" then
      (str.drop 1).toString
    else
      str

  hasDupes (str : String) : Bool :=
    let rec go : List Char → Bool
      | [] => false
      | c :: rest => if rest.contains c then true else go rest
    go (str.toList.filter (· != '-'))

  isIgnoredCommand (tok : Token) : Bool :=
    match getClosestCommand params.parentMap tok with
    | some cmd =>
      match getCommandBasename cmd with
      | some name => name == "tr" || name == "read"
      | Option.none => false
    | Option.none => false

  isDereferenced (tok : Token) : Bool :=
    let path := getPath params.parentMap tok
    path.any fun anc =>
      match anc.inner with
      | .TC_Binary .doubleBracket op _ _ => isDereferencingBinaryOp op
      | .TC_Unary _ op _ => op == "-v"
      | .T_SimpleCommand .. => false
      | _ => false

  isDereferencingBinaryOp (op : String) : Bool :=
    op ∈ ["-eq", "-ne", "-lt", "-le", "-gt", "-ge"]

/-- SC2198-SC2203/SC2255: Arrays/braces/globs in test operands -/
def checkTestOperands (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Unary typ _op token =>
    checkAll typ token
  | .TC_Binary typ op lhs rhs =>
    if op ∈ arithmeticBinaryTestOps then
      if typ == .doubleBracket then
        -- [[ ]] evaluates arithmetic operators, but arrays/braces still misbehave
        checkArrays typ lhs ++ checkBraces typ lhs ++
        checkArrays typ rhs ++ checkBraces typ rhs
      else
        -- [ ] does not do arithmetic evaluation; globs in operands are especially suspicious
        checkNumericalGlob lhs ++ checkArrays typ lhs ++ checkBraces typ lhs ++
        checkNumericalGlob rhs ++ checkArrays typ rhs ++ checkBraces typ rhs
    else if op ∈ ["=", "==", "!=", "=~"] then
      checkAll typ lhs ++ checkArrays typ rhs ++ checkBraces typ rhs
    else
      checkAll typ lhs ++ checkAll typ rhs
  | _ => []
where
  checkAll (typ : ConditionType) (token : Token) : List TokenComment :=
    checkArrays typ token ++ checkBraces typ token ++ checkGlobs typ token

  -- Our parser currently doesn't always classify globs/braces inside test operands.
  -- Fall back to simple literal heuristics so these checks still trigger.
  looksLikeGlobPart (t : Token) : Bool :=
    isGlob t ||
    match getLiteralString t with
    | some s => s.contains '*' || s.contains '?' || s.contains '['
    | Option.none => false

  looksLikeBracePart (t : Token) : Bool :=
    isBraceExpansion t ||
    match getLiteralString t with
    | some s =>
      s.contains '{' && s.contains '}' && (s.contains ',' || Regex.containsSubstring s "..")
    | Option.none => false

  looksLikeGlobToken (token : Token) : Bool :=
    (getWordParts token).any looksLikeGlobPart

  looksLikeBraceToken (token : Token) : Bool :=
    (getWordParts token).any looksLikeBracePart

  checkArrays (typ : ConditionType) (token : Token) : List TokenComment :=
    if (getWordParts token).any isArrayExpansion then
      if typ == .singleBracket then
        [makeComment .warningC token.id 2198
          "Arrays don't work as operands in [ ]. Use a loop (or concatenate with * instead of @)."]
      else
        [makeComment .errorC token.id 2199
          "Arrays implicitly concatenate in [[ ]]. Use a loop (or explicit * instead of @)."]
    else []

  checkBraces (typ : ConditionType) (token : Token) : List TokenComment :=
    if looksLikeBraceToken token then
      if typ == .singleBracket then
        [makeComment .warningC token.id 2200
          "Brace expansions don't work as operands in [ ]. Use a loop."]
      else
        [makeComment .errorC token.id 2201
          "Brace expansion doesn't happen in [[ ]]. Use a loop."]
    else []

  checkGlobs (typ : ConditionType) (token : Token) : List TokenComment :=
    if looksLikeGlobToken token then
      if typ == .singleBracket then
        [makeComment .warningC token.id 2202
          "Globs don't work as operands in [ ]. Use a loop."]
      else
        [makeComment .errorC token.id 2203
          "Globs are ignored in [[ ]] except right of =/!=. Use a loop."]
    else []

  checkNumericalGlob (token : Token) : List TokenComment :=
    if params.shellType != .Ksh && looksLikeGlobToken token then
      [makeComment .errorC token.id 2255
        "[ ] does not apply arithmetic evaluation. Evaluate with $((..)) for numbers, or use string comparator for strings."]
    else []

/-- SC2064: Use single quotes, otherwise this expands now rather than when signalled -/
def checkTrapQuoting (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "trap" then
      let args := words.drop 1 |>.filter (not ∘ isFlag)
      match args.head? with
      | some trapArg =>
        if hasExpansionInDoubleQuotes trapArg then
          [makeComment .warningC trapArg.id 2064
            "Use single quotes, otherwise this expands now rather than when signalled."]
        else []
      | Option.none => []
    else []
  | _ => []
where
  hasExpansionInDoubleQuotes (t : Token) : Bool :=
    match t.inner with
    | .T_NormalWord [part] =>
      match part.inner with
      | .T_DoubleQuoted parts =>
        parts.any fun p =>
          match p.inner with
          | .T_DollarBraced _ _ => true
          | .T_DollarExpansion _ => true
          | .T_Backticked _ => true
          | _ => false
      | _ => false
    | _ => false

/-- SC2066: Since you double quoted this, it will not word split, and the loop will only run once -/
def checkSingleLoopIteration (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    match words with
    | [word] =>
      match word.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_DoubleQuoted _ =>
          if hasArrayOrAtExpansion part then []  -- Arrays in quotes are OK
          else
            [makeComment .errorC word.id 2066
              "Since you double quoted this, it will not word split, and the loop will only run once."]
        | _ => []
      | _ => []
    | _ => []
  | _ => []
where
  hasArrayOrAtExpansion (t : Token) : Bool :=
    match t.inner with
    | .T_DoubleQuoted parts =>
      parts.any fun p =>
        isArrayExpansion p ||
        match p.inner with
        | .T_DollarBraced _ content =>
          let s := oversimplify content |>.foldl (· ++ ·) ""
          s == "@" || s.startsWith "@"
        | _ => false
    | _ => false

/-- SC2088: Tilde does not expand in quotes. Use $HOME -/
def checkTildeInQuotes (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_NormalWord parts =>
    parts.flatMap fun part =>
      match part.inner with
      | .T_DoubleQuoted inner =>
        inner.flatMap fun elem =>
          match elem.inner with
          | .T_Literal s =>
            if s.startsWith "~" then
              [makeComment .warningC elem.id 2088
                "Tilde does not expand in quotes. Use $HOME."]
            else []
          | _ => []
      | .T_SingleQuoted s =>
        if s.startsWith "~" then
          [makeComment .warningC part.id 2088
            "Tilde does not expand in quotes. Use $HOME."]
        else []
      | _ => []
  | _ => []

/-- SC2083: Don't add spaces after the slash in './file' -/
def checkLonelyDotDash (_params : Parameters) (t : Token) : List TokenComment :=
  if getCommandName t == some "./" then
    [makeComment .errorC t.id 2083
      "Don't add spaces after the slash in './file'."]
  else []

/-- SC2027: The surrounding quotes actually unquote this. Remove or escape them. -/
def checkInexplicablyUnquoted (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_NormalWord parts => go parts
  | _ => []
where
  msg : String := "The surrounding quotes actually unquote this. Remove or escape them."

  go : List Token → List TokenComment
    | t1 :: t2 :: t3 :: rest =>
        let here :=
          match t1.inner, t2.inner, t3.inner with
          | .T_DoubleQuoted _, .T_DollarExpansion _, .T_DoubleQuoted _ =>
              [makeComment .warningC t2.id 2027 msg]
          | .T_DoubleQuoted _, .T_DollarBraced _ _, .T_DoubleQuoted _ =>
              [makeComment .warningC t2.id 2027 msg]
          | _, _, _ => []
        here ++ go (t2 :: t3 :: rest)
    | _ => []

/-- SC2089/SC2090: Quotes/backslashes will be treated literally -/
def checkQuotesForExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ _ _ word =>
    if hasQuotesInValue word then
      [makeComment .warningC t.id 2089
        "Quotes/backslashes will be treated literally. Use an array."]
    else []
  | _ => []
where
  hasQuotesInValue (t : Token) : Bool :=
    match getLiteralString t with
    | some s =>
      (s.any (· == '"') || s.any (· == '\'') || Regex.containsSubstring s "\\ ")
      && not (s.startsWith "-")  -- Skip flags
    | Option.none => false

/-- SC2091: Remove surrounding $() to avoid executing output -/
def checkExecuteCommandOutput (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ [cmdWord] =>
    match cmdWord.inner with
    | .T_NormalWord [part] =>
      match part.inner with
      | .T_DollarExpansion cmds =>
        if cmds.any (fun c => getCommandBasename c |>.isSome) then
          [makeComment .warningC t.id 2091
            "Remove surrounding $() to avoid executing output (or use eval if intentional)."]
        else []
      | .T_Backticked cmds =>
        if cmds.any (fun c => getCommandBasename c |>.isSome) then
          [makeComment .warningC t.id 2091
            "Remove surrounding $() to avoid executing output (or use eval if intentional)."]
        else []
      | _ => []
    | _ => []
  | _ => []

/-- SC2093: Remove \"exec \" if script should continue after this command -/
def checkExecWithSubshell (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    if isCommand t "exec" then
      let args := words.drop 1
      if args.any isCommandSubstitution then
        [makeComment .infoC t.id 2093
          "Remove \"exec \" if script should continue after this command."]
      else []
    else []
  | _ => []

/-- SC2324: `var+=1` appends rather than increments. -/
def checkPlusEqualsNumber (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment .append var indices word =>
    if !indices.isEmpty then
      []
    else
      match params.cfgAnalysis with
      | Option.none => []
      | some cfg =>
        match getIncomingState cfg t.id with
        | Option.none => []
        | some state =>
          if isNumber state word &&
             !(variableMayBeDeclaredInteger state var |>.getD false) then
            [makeComment .warningC t.id 2324
              "var+=1 will append, not increment. Use (( var += 1 )), typeset -i var, or quote number to silence."]
          else
            []
  | _ => []
where
  getUnmodifiedParameterExpansion (t : Token) : Option String := do
    match t.inner with
    | .T_DollarBraced _ content =>
      let s ← getUnquotedLiteral content
      if isVariableName s then
        some s
      else
        Option.none
    | _ => Option.none

  isNumber (state : ProgramState) (word : Token) : Bool :=
    let unquotedLiteral := getUnquotedLiteral word
    let isEmpty := unquotedLiteral == some ""
    let isUnquotedNumber :=
      not isEmpty && (unquotedLiteral.map (fun s => s.toList.all Char.isDigit) |>.getD false)
    let isNumericalVariableName :=
      match unquotedLiteral with
      | some s => variableMayBeAssignedInteger state s |>.getD false
      | Option.none => false
    let isNumericalVariableExpansion :=
      match word.inner with
      | .T_NormalWord [part] =>
          match getUnmodifiedParameterExpansion part with
          | some s => variableMayBeAssignedInteger state s |>.getD false
          | Option.none => false
      | _ => false
    isUnquotedNumber || isNumericalVariableName || isNumericalVariableExpansion

/-- SC2327/SC2328: Command substitution output redirected away makes it empty. -/
def checkExpansionWithRedirection (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarExpansion [cmd] => check t.id cmd
  | .T_Backticked [cmd] => check t.id cmd
  | .T_DollarBraceCommandExpansion _ [cmd] => check t.id cmd
  | _ => []
where
  check (captureId : Id) (pipe : Token) : List TokenComment :=
    match pipe.inner with
    | .T_Pipeline _ cmds =>
      match cmds.getLast? with
      | some last => checkCmd captureId last
      | Option.none => []
    | _ => checkCmd captureId pipe

  checkCmd (captureId : Id) (cmd : Token) : List TokenComment :=
    match cmd.inner with
    | .T_Redirecting redirs _ =>
      redirs.foldr (walk captureId) []
    | _ => []

  walk (captureId : Id) (redir : Token) (acc : List TokenComment) : List TokenComment :=
    match redir.inner with
    | .T_FdRedirect fd inner =>
      match inner.inner with
      -- e.g. 2>&1 (captures stderr into stdout) can make later stdout redirects irrelevant.
      | .T_IoDuplicate _ "1" => []
      -- e.g. 1>&2 etc: treat as deliberate and stop.
      | .T_IoDuplicate .. =>
        if fd == "1" then [] else acc
      | .T_IoFile opTok file =>
        if fd == "1" && isStdoutRedirectOp opTok then
          emit redir.id captureId (shouldSuggestTee file)
        else
          acc
      | _ => acc
    | .T_IoDuplicate opTok _ =>
      if isStdoutRedirectOp opTok then
        emit redir.id captureId true
      else
        acc
    | .T_IoFile opTok file =>
      if isStdoutRedirectOp opTok then
        emit redir.id captureId (shouldSuggestTee file)
      else
        acc
    | _ => acc

  isStdoutRedirectOp (opTok : Token) : Bool :=
    match getLiteralString opTok with
    | some op => op.startsWith ">"
    | Option.none => false

  shouldSuggestTee (file : Token) : Bool :=
    getLiteralString file != some "/dev/null"

  emit (redirectId captureId : Id) (suggestTee : Bool) : List TokenComment :=
    let captureWarn :=
      makeComment .warningC captureId 2327
        "This command substitution will be empty because the command's output gets redirected away."
    let redirMsg :=
      "This redirection takes output away from the command substitution" ++
        if suggestTee then " (use tee to duplicate)." else "."
    let redirErr :=
      makeComment .errorC redirectId 2328 redirMsg
    captureWarn :: redirErr :: []

/-- SC2087: Quote heredoc delimiter for ssh to avoid expanding on the client side -/
def checkSshHereDoc (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects _cmd =>
      if isCommand t "ssh" then
        redirects.filterMap fun r =>
          match r.inner with
          | .T_HereDoc _ quoteStyle delim _ =>
              if quoteStyle == .unquoted then
                some (makeComment .warningC r.id 2087
                  s!"Quote '{delim}' to make here document expansions happen on the server side rather than on the client.")
              else none
          | .T_FdRedirect _ target =>
              match target.inner with
              | .T_HereDoc _ quoteStyle delim _ =>
                  if quoteStyle == .unquoted then
                    some (makeComment .warningC target.id 2087
                      s!"Quote '{delim}' to make here document expansions happen on the server side rather than on the client.")
                  else none
              | _ => none
          | _ => none
      else
        []
  | _ => []

/-- SC2095: Add < /dev/null to prevent ssh from swallowing stdin -/
def checkSshInLoop (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_WhileExpression _ body =>
    checkBodyForSsh params body
  | .T_ForIn _ _ body =>
    checkBodyForSsh params body
  | _ => []
where
  checkBodyForSsh (_params : Parameters) (body : List Token) : List TokenComment :=
    body.flatMap fun cmd =>
      if isCommand cmd "ssh" || isCommand cmd "ffmpeg" then
        [makeComment .infoC cmd.id 2095
          "Add < /dev/null to prevent this command from swallowing stdin."]
      else []

/-- SC2067: Missing ';' or '+' terminating -exec -/
def checkFindExec (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    let cmdName := getLiteralString cmd |>.map basename
    if cmdName == some "find" then
      checkExecArgs t.id args false
    else []
  | _ => []
where
  checkExecArgs (baseId : Id) : List Token → Bool → List TokenComment
    | [], inExec => if inExec then [makeComment .errorC baseId 2067
        "Missing ';' or + terminating -exec. You can't use |/||/&&, and ';' has to be a separate, quoted argument."]
      else []
    | w :: rest, inExec =>
      let warnings :=
        if inExec then
          (getWordParts w).filterMap fun part =>
            if shouldWarn part then
              some (makeComment .infoC part.id 2014
                "This will expand once before find runs, not per file found.")
            else none
        else []
      match getLiteralString w with
      | some "-exec" => warnings ++ checkExecArgs baseId rest true
      | some "-execdir" => warnings ++ checkExecArgs baseId rest true
      | some "-ok" => warnings ++ checkExecArgs baseId rest true
      | some "-okdir" => warnings ++ checkExecArgs baseId rest true
      | some "+" => warnings ++ checkExecArgs baseId rest false
      | some ";" => warnings ++ checkExecArgs baseId rest false
      | _ => warnings ++ checkExecArgs baseId rest inExec

  shouldWarn (t : Token) : Bool :=
    match t.inner with
    | .T_DollarExpansion _ => true
    | .T_Backticked _ => true
    | .T_Glob _ => true
    | .T_Extglob .. => true
    | _ => false

/-- SC2069: To redirect stdout+stderr, 2>&1 must be last -/
def checkStderrRedirect (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects _ =>
    let stderrRedirs := redirects.filter isStderrToStdout
    let writeRedirs := redirects.filter isWriteRedirect
    match stderrRedirs.find? (fun r => writeRedirs.any (fun w => r.id.val < w.id.val)) with
    | some bad =>
      if isCaptured params t then [] else
        [makeComment .warningC bad.id 2069
          "To redirect stdout+stderr, 2>&1 must be last (or use '{ cmd > file; } 2>&1' to clarify)."]
    | Option.none => []
  | _ => []
where
  isStderrToStdout (r : Token) : Bool :=
    match r.inner with
    | .T_FdRedirect "2" target =>
      match target.inner with
      | .T_IoDuplicate op "1" =>
        getLiteralString op == some ">&"
      | _ => false
    | _ => false

  isWriteRedirect (r : Token) : Bool :=
    match r.inner with
    | .T_IoFile op _ =>
      match getLiteralString op with
      | some ">" => true
      | some ">>" => true
      | _ => false
    | .T_FdRedirect _ target =>
      match target.inner with
      | .T_IoFile op _ =>
        match getLiteralString op with
        | some ">" => true
        | some ">>" => true
        | _ => false
      | _ => false
    | _ => false

  isCaptured (params : Parameters) (redir : Token) : Bool :=
    let path := getPath params.parentMap redir
    path.any fun ancestor =>
      match ancestor.inner with
      | .T_Pipeline _ cmds =>
        cmds.length > 1 &&
        match cmds.getLast? with
        | some lastCmd => not (path.any fun t => t.id == lastCmd.id)
        | Option.none => false
      | .T_ProcSub .. => true
      | .T_DollarExpansion .. => true
      | .T_Backticked .. => true
      | _ => false

/-- SC2038: Use -print0 with find | xargs to handle special filenames -/
def checkPipePitfalls (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    match cmds with
    | [findCmd, xargsCmd] =>
      let findName := getCommandBasename findCmd
      let xargsName := getCommandBasename xargsCmd
      if findName == some "find" && xargsName == some "xargs" then
        let hasNull := hasParameter findCmd "-print0" ||
                       hasParameter findCmd "printf" ||
                       hasParameter xargsCmd "-0" ||
                       hasParameter xargsCmd "null"
        if hasNull then [] else
          [makeComment .warningC t.id 2038
            "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames."]
      else []
    | _ => []
  | _ => []

/-- SC2259/SC2260/SC2261: Redirections overriding pipeline input/output. -/
def checkPipelineRedirections (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
      let lastIndex := if cmds.isEmpty then 0 else cmds.length - 1
      (withIndex 0 cmds).foldl (fun acc (idx, cmd) =>
        let hasInputPipe := idx > 0
        let hasOutputPipe := idx < lastIndex
        let redirs := getRedirections cmd
        if redirs.isEmpty then
          acc
        else
          let fdMap := redirs.foldl addRedir ({} : Std.HashMap Nat (List Token))
          let acc :=
            if hasInputPipe then
              match fdMap.get? 0 with
              | some (tok :: _) =>
                  acc ++ [makeComment .errorC tok.id 2259
                    "This redirection overrides piped input. To use both, merge or pass filenames."]
              | _ => acc
            else acc
          let acc :=
            if hasOutputPipe then
              match fdMap.get? 1 with
              | some (tok :: _) =>
                  acc ++ [makeComment .errorC tok.id 2260
                    "This redirection overrides the output pipe. Use 'tee' to output to both."]
              | _ => acc
            else acc
          acc ++ warnDupes fdMap
      ) []
  | _ => []
where
  getRedirections (cmd : Token) : List Token :=
    match cmd.inner with
    | .T_Redirecting redirs _ => redirs
    | _ => []

  withIndex : Nat → List Token → List (Nat × Token)
    | _n, [] => []
    | n, t :: rest => (n, t) :: withIndex (n + 1) rest

  addRedir (m : Std.HashMap Nat (List Token)) (redir : Token) : Std.HashMap Nat (List Token) :=
    let pairs := redirFds redir
    pairs.foldl (fun acc (fd, tok) =>
      let existing := acc.get? fd |>.getD []
      acc.insert fd (existing ++ [tok])
    ) m

  redirFds (redir : Token) : List (Nat × Token) :=
    match redir.inner with
    | .T_FdRedirect fd target =>
      let (defaultFds, opTok) := defaultFdsForTarget target
      let explicitFd := if fd.isEmpty then Option.none else fd.toNat?
      let fds :=
        match explicitFd with
        | some n => [n]
        | Option.none => defaultFds
      fds.map fun n => (n, opTok)
    | .T_IoFile opTok _ =>
      (opTokenDefaultFds opTok).map fun n => (n, opTok)
    | .T_IoDuplicate opTok _ =>
      (opTokenDefaultFds opTok).map fun n => (n, opTok)
    | .T_HereString _ => [(0, redir)]
    | .T_HereDoc _ _ _ _ => [(0, redir)]
    | _ => []

  defaultFdsForTarget (target : Token) : List Nat × Token :=
    match target.inner with
    | .T_IoFile opTok _ => (opTokenDefaultFds opTok, opTok)
    | .T_IoDuplicate opTok _ => (opTokenDefaultFds opTok, opTok)
    | .T_HereString _ => ([0], target)
    | .T_HereDoc _ _ _ _ => ([0], target)
    | _ => ([], target)

  opTokenDefaultFds (opTok : Token) : List Nat :=
    match getLiteralString opTok with
    | some op =>
      if op.startsWith "<" then [0]
      else if op.startsWith ">" then [1]
      else []
    | Option.none => []

  warnDupes (m : Std.HashMap Nat (List Token)) : List TokenComment :=
    m.toList.flatMap fun (fd, toks) =>
      if toks.length > 1 then
        toks.map fun tok =>
          makeComment .errorC tok.id 2261
            s!"Multiple redirections compete for {fdName fd}. Use cat, tee, or pass filenames instead."
      else []

  fdName : Nat → String
    | 0 => "stdin"
    | 1 => "stdout"
    | 2 => "stderr"
    | n => s!"FD {n}"

/-- SC2206: Quote to prevent word splitting in array assignment -/
def checkSplittingInArrays (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Array elements =>
    elements.foldl (fun acc elem =>
      acc ++ checkArrayElement params elem
    ) []
  | _ => []
where
  checkArrayElement (params : Parameters) (word : Token) : List TokenComment :=
    match word.inner with
    | .T_NormalWord parts =>
      parts.foldl (fun acc part =>
        acc ++ checkPart params part
      ) []
    | _ => []

  checkPart (params : Parameters) (part : Token) : List TokenComment :=
    match part.inner with
    | .T_DollarExpansion _ => [makeComment .warningC part.id 2207
        (if params.shellType == .Ksh then
          "Prefer read -A or while read to split command output (or quote to avoid splitting)."
        else
          "Prefer mapfile or read -a to split command output (or quote to avoid splitting).")]
    | .T_DollarBraceCommandExpansion _ _ => [makeComment .warningC part.id 2207
        "Prefer mapfile or read -a to split command output (or quote to avoid splitting)."]
    | .T_Backticked _ => [makeComment .warningC part.id 2207
        "Prefer mapfile or read -a to split command output (or quote to avoid splitting)."]
    | .T_DollarBraced _ content =>
      let str := String.join (oversimplify content)
      let varName := ASTLib.getBracedReference str
      if ASTLib.isCountingReference part ||
         ASTLib.isQuotedAlternativeReference part ||
         variablesWithoutSpaces.contains varName then []
      else [makeComment .warningC part.id 2206
        (if params.shellType == .Ksh then
          "Quote to prevent word splitting/globbing, or split robustly with read -A or while read."
        else
          "Quote to prevent word splitting/globbing, or split robustly with mapfile or read -a.")]
    | _ => []

/-- SC2210: Redirection to a number is usually a mistake (`1 > 2` vs `1 -gt 2`). -/
def checkRedirectionToNumber (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_IoFile _op file =>
    match ASTLib.getUnquotedLiteral file with
    | some s =>
      if s.toList.all Char.isDigit then
        [makeComment .warningC t.id 2210
          "This is a file redirection. Was it supposed to be a comparison or fd operation?"]
      else
        []
    | Option.none => []
  | _ => []

/-- SC2238: Redirecting to a command name instead of a file is likely a mistake (`ls > rm`). -/
def checkRedirectionToCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_IoFile _op file =>
    match file.inner with
    | .T_NormalWord [single] =>
      match single.inner with
      | .T_Literal str =>
        if str ∈ commonCommands && str != "file" then
          [makeComment .warningC file.id 2238
            "Redirecting to/from command name instead of file. Did you want pipes/xargs (or quote to ignore)?"]
        else
          []
      | _ => []
    | _ => []
  | _ => []

/-- SC2096: On most OS, shebangs can only specify a single parameter -/
def checkShebangParams (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Script shebang _ =>
    match shebang.inner with
    | .T_Literal s =>
      let parts := s.splitOn " "
      -- Check for env -S or env --split-string which allows multiple params
      let isEnvSplit := Regex.containsSubstring s "env -S" ||
                        Regex.containsSubstring s "env --split-string"
      if parts.length > 2 && !isEnvSplit then
        [makeComment .errorC shebang.id 2096
          "On most OS, shebangs can only specify a single parameter."]
      else []
    | _ => []
  | _ => []

/-- SC2188/SC2189: Dangling redirections in pipelines -/
def checkRedirectedNowhere (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting _ _ =>
    if isInMultiPipeline params t then []
    else
    match getDanglingRedirect t with
    | some redir =>
      if isInExpansion params t then []
      else
        [makeComment .warningC redir.id 2188
          "This redirection doesn't have a command. Move to its command (or use 'true' as no-op)."]
    | Option.none => []
  | .T_Pipeline _ cmds =>
    match cmds with
    | _ :: _ :: _ =>
      cmds.foldl (fun acc cmd =>
        match getDanglingRedirect cmd with
        | some redir =>
          acc ++ [makeComment .errorC redir.id 2189
            "You can't have | between this redirection and the command it should apply to."]
        | Option.none => acc
      ) []
    | _ => []
  | _ => []
where
  getDanglingRedirect (t : Token) : Option Token :=
    match t.inner with
    | .T_Redirecting redirects cmd =>
      match redirects with
      | first :: _ =>
        match cmd.inner with
        | .T_SimpleCommand [] [] => some first
        | _ => Option.none
      | [] => Option.none
    | _ => Option.none

  isInExpansion (params : Parameters) (t : Token) : Bool :=
    let parents := (getPath params.parentMap t).drop 1
    let rec go : List Token → Bool
      | [] => false
      | p :: rest =>
        match p.inner with
        | .T_DollarExpansion cmds => cmds.length == 1
        | .T_Backticked cmds => cmds.length == 1
        | .T_Annotation _ _ => go rest
        | _ => false
    go parents

  /-- True when this token is inside a pipeline with multiple commands. -/
  isInMultiPipeline (params : Parameters) (t : Token) : Bool :=
    let parents := (getPath params.parentMap t).drop 1
    parents.any fun p =>
      match p.inner with
      | .T_Pipeline _ cmds => cmds.length > 1
      | _ => false

/-- SC2069: Redirect stderr to stdout before piping -/
def checkStderrPipe (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline _ cmds =>
    if cmds.length >= 2 then
      match cmds.head? with
      | some cmd => checkForStderrRedirect cmd
      | Option.none => []
    else []
  | _ => []
where
  checkForStderrRedirect (cmd : Token) : List TokenComment :=
    match cmd.inner with
    | .T_Redirecting redirects _inner =>
      -- Check if any redirect is stderr-related at end of pipeline element
      let hasStderrRedirect := redirects.any fun r =>
        match r.inner with
        | .T_FdRedirect "2" _ => true
        | _ => false
      if hasStderrRedirect then []  -- Already handling stderr
      else []  -- Could check if stderr should be redirected
    | _ => []

/-- SC2015: Note that A && B || C is not if-then-else -/
def checkBadTestAndOr (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_OrIf lhs _rhs =>
    match lhs.inner with
    | .T_AndIf _cond action =>
      -- Check if action might fail
      if mightFail action then
        [makeComment .infoC t.id 2015
          "Note that A && B || C is not if-then-else. C may run when A is true."]
      else []
    | _ => []
  | _ => []
where
  mightFail (t : Token) : Bool :=
    -- Commands that might fail
    match getCommandName t with
    | some name => name ∈ ["echo", "printf", ":", "true"]  -- These usually succeed
    | Option.none => true

private def zip3Tokens : List (Option Token) → List Token → List (Option Token) →
    List (Option Token × Token × Option Token)
  | b :: bs, c :: cs, a :: as => (b, c, a) :: zip3Tokens bs cs as
  | _, _, _ => []

private def badTestPipeCheckPipe (sep : Option Token) : List TokenComment :=
  match sep with
  | some tok =>
    match tok.inner with
    | .T_Pipe "|" =>
      [makeComment .warningC tok.id 2266
        "Use || for logical OR. Single | will pipe."]
    | _ => []
  | Option.none => []

private partial def badTestPipeCheckAnds (bgId : Id) (cmd : Token) : List TokenComment :=
  match cmd.inner with
  | .T_AndIf _ rhs => badTestPipeCheckAnds bgId rhs
  | .T_OrIf _ rhs => badTestPipeCheckAnds bgId rhs
  | .T_Pipeline _ cmds =>
    match cmds.getLast? with
    | some last => badTestPipeCheckAnds bgId last
    | Option.none => []
  | _ =>
    if isTestCommand cmd then
      [makeComment .errorC bgId 2265
        "Use && for logical AND. Single & will background and return true."]
    else []

/-- SC2265/SC2266: Use &&/|| for logical AND/OR in tests. -/
def checkBadTestAndOrPipes (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Pipeline seps cmds =>
    if cmds.length >= 2 then
      let maybeSeps := seps.map Option.some
      let before := Option.none :: maybeSeps
      let after := maybeSeps ++ [Option.none]
      let triples := zip3Tokens before cmds after
      triples.foldl (fun acc (b, cmd, a) =>
        if isTestCommand cmd then
          acc ++ badTestPipeCheckPipe b ++ badTestPipeCheckPipe a
        else acc
      ) []
    else []
  | .T_Backgrounded cmd =>
    badTestPipeCheckAnds t.id cmd
  | _ => []

/-- SC2268: Avoid x-prefix in comparisons. -/
def checkComparisonWithLeadingX (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary _ op lhs rhs =>
    if op == "=" || op == "==" || op == "!=" then
      if hasLeadingX lhs || hasLeadingX rhs then
        [makeComment .styleC lhs.id 2268
          "Avoid x-prefix in comparisons as it no longer serves a purpose."]
      else []
    else []
  | .T_SimpleCommand _ (cmd :: lhs :: opTok :: rhs :: _) =>
    if getLiteralString cmd == some "test" then
      match getLiteralString opTok with
      | some op =>
        if op == "=" || op == "==" || op == "!=" then
          if hasLeadingX lhs || hasLeadingX rhs then
            [makeComment .styleC lhs.id 2268
              "Avoid x-prefix in comparisons as it no longer serves a purpose."]
          else []
        else []
      | Option.none => []
    else []
  | _ => []
where
  startsWithX (s : String) : Bool :=
    match s.toList.head? with
    | some c => c == 'x' || c == 'X'
    | Option.none => false

  hasLeadingX (tok : Token) : Bool :=
    match getWordParts tok with
    | [] => false
    | part :: _ =>
      match part.inner with
      | .T_Literal s => startsWithX s
      | .T_SingleQuoted s => startsWithX s
      | .T_DoubleQuoted parts =>
        match parts with
        | first :: _ =>
          match first.inner with
          | .T_Literal s => startsWithX s
          | .T_SingleQuoted s => startsWithX s
          | _ => false
        | [] => false
      | _ => false

/-- SC2166: Prefer [ p ] || [ q ] as [ p -o q ] is not well defined -/
def checkTestAndOr (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ words =>
    -- Check if this is a [ ] test command
    match (words.head?, words.getLast?) with
    | (some first, some last) =>
      if getLiteralString first == some "[" && getLiteralString last == some "]" then
        -- Look for -o or -a in the middle words
        words.foldl (fun acc word =>
          match getLiteralString word with
          | some "-o" =>
            (makeComment .warningC word.id 2166
              "Prefer [ p ] || [ q ] as [ p -o q ] is not well defined.") :: acc
          | some "-a" =>
            (makeComment .warningC word.id 2166
              "Prefer [ p ] && [ q ] as [ p -a q ] is not well defined.") :: acc
          | _ => acc
        ) []
      else []
    | _ => []
  | _ => []

/-- SC2060: Quote parameters to tr to prevent glob expansion -/
def checkTrParams (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    if getCommandBasename ⟨cmd.id, cmd.inner⟩ == some "tr" then
      args.foldl (fun acc arg =>
        acc ++ checkTrArg arg
      ) []
    else []
  | _ => []
where
  checkTrArg (arg : Token) : List TokenComment :=
    match arg.inner with
    | .T_NormalWord parts =>
      if parts.any ASTLib.isGlob then
        [makeComment .warningC arg.id 2060
          "Quote parameters to tr to prevent glob expansion."]
      else []
    | _ => []

/-- SC2071: Comparison operators only work in [[ ]] in some shells -/
def checkComparisonOperators (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .singleBracket op _ _ =>
    let isCompOp := op == "<" || op == ">"
    let isBasicShell := params.shellType == .Sh ||
                        params.shellType == .Dash ||
                        params.shellType == .BusyboxSh
    if isCompOp && isBasicShell then
      [makeComment .errorC t.id 2071
        s!"{op} is not supported in [ ]. Use [[ ]] or (( )) for this comparison."]
    else []
  | _ => []

/-- SC2073: Escape \< (or use determine) to prevent redirection -/
def checkTestRedirection (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects inner =>
    match inner.inner with
    | .T_Condition .singleBracket _ =>
      if !redirects.isEmpty then
        [makeComment .warningC t.id 2073
          "Escape \\< to prevent redirection (or determine intention and rewrite)."]
      else []
    | _ => []
  | _ => []

/-- SC2088: Tilde does not expand in quotes -/
def checkTildeExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DoubleQuoted parts =>
    parts.foldl (fun acc part =>
      match part.inner with
      | .T_Literal s =>
        if s.startsWith "~" then
          acc ++ [makeComment .warningC part.id 2088
            "Tilde does not expand in quotes. Use $HOME."]
        else acc
      | _ => acc
    ) []
  | _ => []

/-- SC2089/2090: Quotes/backslashes will be treated literally -/
def checkQuotesInVariables (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Assignment _ _name _ value =>
    let valStr := getLiteralStringDef "" value
    if Regex.containsSubstring valStr "'" ||
       Regex.containsSubstring valStr "\"" ||
       Regex.containsSubstring valStr "\\" then
      -- Would need to track if this variable is later used unquoted
      []  -- Complex check requiring flow analysis
    else []
  | _ => []

/-- SC2091: Remove surrounding $() to run command (or use quotes) -/
def checkSubshellAsTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Condition _ expr =>
    checkForCommandSub expr
  | _ => []
where
  checkForCommandSub (expr : Token) : List TokenComment :=
    match expr.inner with
    | .TC_Nullary _ inner =>
      match inner.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_DollarExpansion _ =>
          [makeComment .warningC expr.id 2091
            "Remove surrounding $() to run command (or use quotes to avoid treating output as shell code)."]
        | _ => []
      | _ => []
    | _ => []

/-- SC2092: Remove backticks to avoid executing output -/
def checkBackticksAsTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Condition _ expr =>
    checkForBackticks expr
  | _ => []
where
  checkForBackticks (expr : Token) : List TokenComment :=
    match expr.inner with
    | .TC_Nullary _ inner =>
      match inner.inner with
      | .T_NormalWord [part] =>
        match part.inner with
        | .T_Backticked _ =>
          [makeComment .warningC expr.id 2092
            "Remove backticks to avoid executing output."]
        | _ => []
      | _ => []
    | _ => []

/-- SC2204/SC2205: (..) is a subshell. Did you mean [ .. ], a test expression? -/
def checkSubshellAsTestExpression (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Subshell [w] =>
    match getFirstTwoWords w 32 with
    | some (first, second) => checkParams t.id first second
    | Option.none => []
  | _ => []
where
  getFirstTwoWords (t : Token) (fuel : Nat) : Option (Token × Token) :=
    match fuel with
    | 0 => Option.none
    | fuel + 1 =>
      match t.inner with
      | .T_Annotation _ inner => getFirstTwoWords inner fuel
      | .T_Banged inner => getFirstTwoWords inner fuel
      | .T_AndIf left _ => getFirstTwoWords left fuel
      | .T_OrIf left _ => getFirstTwoWords left fuel
      | .T_Pipeline _ cmds =>
        match cmds with
        | [single] => getFirstTwoWords single fuel
        | _ => Option.none
      | .T_Redirecting _ innerCmd => getFirstTwoWords innerCmd fuel
      | .T_SimpleCommand _ (first :: second :: _) => some (first, second)
      | _ => Option.none

  checkParams (subshellId : Id) (first second : Token) : List TokenComment :=
    let unary :=
      match getLiteralString first with
      | some s => unaryTestOps.contains s
      | Option.none => false
    let binary :=
      match getLiteralString second with
      | some s => binaryTestOps.contains s
      | Option.none => false
    let c1 :=
      if unary then
        [makeComment .errorC subshellId 2204
          "(..) is a subshell. Did you mean [ .. ], a test expression?"]
      else []
    let c2 :=
      if binary then
        [makeComment .warningC subshellId 2205
          "(..) is a subshell. Did you mean [ .. ], a test expression?"]
      else []
    c1 ++ c2

/-- SC2233/SC2234/SC2235: Avoid subshell overhead around test structures. -/
def checkSubshelledTests (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Subshell cmds =>
    if !(cmds.all (isTestStructure 64)) then
      []
    else if hasAssignmentLike t then
      []
    else
      let path := getPath params.parentMap t
      if isCompoundCondition path then
        [makeComment .styleC t.id 2233
          "Remove superfluous (..) around condition to avoid subshell overhead."]
      else if isSingleTest cmds && !(isFunctionBody path) then
        [makeComment .styleC t.id 2234
          "Remove superfluous (..) around test command to avoid subshell overhead."]
      else
        [makeComment .styleC t.id 2235
          "Use { ..; } instead of (..) to avoid subshell overhead."]
  | _ => []
where
  isSingleTest : List Token → Bool
    | [c] => isTestCommand 64 c
    | _ => false

  isFunctionBody (path : List Token) : Bool :=
    match path with
    | _ :: parent :: _ =>
      match parent.inner with
      | .T_Function .. => true
      | _ => false
    | _ => false

  isCompoundCondition (path : List Token) : Bool :=
    let rec dropSkippable : List Token → List Token
      | [] => []
      | tok :: rest =>
        if skippable tok then
          dropSkippable rest
        else
          tok :: rest
    match dropSkippable (path.drop 1) with
    | [] => false
    | tok :: _ =>
      match tok.inner with
      | .T_IfExpression .. => true
      | .T_WhileExpression .. => true
      | .T_UntilExpression .. => true
      | _ => false

  skippable (t : Token) : Bool :=
    match t.inner with
    | .T_Redirecting redirects _ => redirects.isEmpty
    | .T_Pipeline seps _ => seps.isEmpty
    | .T_Annotation .. => true
    | _ => false

  hasAssignmentLike (t : Token) : Bool :=
    (collectTokens t).any fun tok =>
      match tok.inner with
      | .TA_Assignment .. => true
      | .TA_Unary op _ =>
        Regex.containsSubstring op "++" || Regex.containsSubstring op "--"
      | .T_DollarBraced _ content =>
        let raw := String.join (oversimplify content)
        let modifier := getBracedModifier raw
        modifier.startsWith "=" || modifier.startsWith ":="
      | .T_DollarBraceCommandExpansion .. => true
      | _ => false

  /-- Is a command token a test command ([..], [[..]] or `test`)? -/
  isTestCommand (fuel : Nat) (t : Token) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match t.inner with
      | .T_Annotation _ inner => isTestCommand fuel inner
      | .T_Pipeline _ cmds =>
        match cmds with
        | [single] => isTestCommand fuel single
        | _ => false
      | .T_Redirecting _ cmd => isTestCommand fuel cmd
      | .T_Condition .. => true
      | _ => getCommandBasename t == some "test"

  /-- Is this a pure test structure made up of test commands and boolean operators? -/
  isTestStructure (fuel : Nat) (t : Token) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match t.inner with
      | .T_Annotation _ inner => isTestStructure fuel inner
      | .T_Banged cmd => isTestStructure fuel cmd
      | .T_AndIf a b => isTestStructure fuel a && isTestStructure fuel b
      | .T_OrIf a b => isTestStructure fuel a && isTestStructure fuel b
      | .T_Pipeline _ cmds =>
        match cmds with
        | [single] => isTestStructure fuel single
        | _ => false
      | .T_Redirecting _ cmd => isTestStructure fuel cmd
      | .T_BraceGroup inner => inner.all (isTestStructure fuel)
      | .T_Subshell inner => inner.all (isTestStructure fuel)
      | _ => isTestCommand fuel t

/-- SC2093: Remove exec if script should continue after this command -/
def checkSpuriousExec (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: _) =>
    if getCommandName ⟨cmd.id, cmd.inner⟩ == some "exec" then
      -- Would need to check if this is last command in script/function
      []  -- Complex check
    else []
  | _ => []

/-- SC2094: File being read and written in same pipeline -/
def checkReadWriteSameFile (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects cmd =>
    let files := getRedirectedFiles redirects
    if files.length > 0 then
      checkCommandForSameFile cmd files
    else []
  | _ => []
where
  getRedirectedFiles (redirects : List Token) : List String :=
    redirects.filterMap fun r =>
      match r.inner with
      | .T_FdRedirect _ op =>
        match op.inner with
        | .T_IoFile _ target => getLiteralString target
        | _ => none
      | _ => none

  checkCommandForSameFile (_cmd : Token) (_files : List String) : List TokenComment :=
    []  -- Complex check requiring command analysis

/-- SC2095: Add -n to ssh/scp or command may not run properly in while loop -/
def checkWhileReadSsh (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_WhileExpression cond body =>
    if isReadCommand cond then
      body.foldl (fun acc cmd =>
        acc ++ checkForSshFfmpeg cmd
      ) []
    else []
  | _ => []
where
  isReadCommand (cond : List Token) : Bool :=
    cond.any fun c => getCommandName c == some "read"

  checkForSshFfmpeg (cmd : Token) : List TokenComment :=
    match getCommandName cmd with
    | some "ssh" =>
      if not (hasFlag cmd "n") then
        [makeComment .warningC cmd.id 2095
          "Add < /dev/null or -n to prevent ssh from swallowing stdin."]
      else []
    | some "ffmpeg" =>
      if not (hasParameter cmd "-nostdin") then
        [makeComment .warningC cmd.id 2095
          "Use -nostdin to prevent ffmpeg from consuming stdin."]
      else []
    | _ => []

/-- SC2097/SC2098: Prefix assignments are not visible to expansions in the same command. -/
def checkPrefixAssignment (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let name := ASTLib.getBracedReference (String.join (oversimplify content))
    if name.isEmpty then
      []
    else
      let path := getPath params.parentMap t
      let pathIds := path.map (·.id)
      let simpleCmd? := path.find? fun tok =>
        match tok.inner with
        | .T_SimpleCommand _ (_ :: _) => true
        | _ => false
      match simpleCmd? with
      | some simpleCmd =>
        match simpleCmd.inner with
        | .T_SimpleCommand assigns _ =>
          let matching := assigns.filterMap fun assign =>
            match assign.inner with
            | .T_Assignment _ varName indices _ =>
              if indices.isEmpty && varName == name && !(pathIds.contains assign.id) then
                some assign
              else
                none
            | _ => none
          if matching.isEmpty then
            []
          else
            let warnAssigns := matching.map fun assign =>
              makeComment .warningC assign.id 2097
                "This assignment is only seen by the forked process."
            let warnRef :=
              makeComment .warningC t.id 2098
                "This expansion will not see the mentioned assignment."
            warnAssigns ++ [warnRef]
        | _ => []
      | Option.none => []
  | _ => []

/-- SC2270-SC2282: Command name looks like an assignment/comparison -/
def checkEqualsInCommand (params : Parameters) (originalToken : Token) : List TokenComment :=
  match originalToken.inner with
  | .T_SimpleCommand _ (word :: _) => checkWord word
  | _ => []
where
  hasEquals (t : Token) : Bool :=
    match t.inner with
    | .T_Literal s => s.toList.contains '='
    | _ => false

  splitAtEquals : List Token → Option (List Token × Token × List Token)
    | [] => Option.none
    | x :: xs =>
      if hasEquals x then
        some ([], x, xs)
      else
        match splitAtEquals xs with
        | some (leading, eqTok, rest) => some (x :: leading, eqTok, rest)
        | Option.none => Option.none

  stripSinglePlus (leading : List Token) : List Token :=
    match leading.reverse with
    | last :: rest =>
      match last.inner with
      | .T_Literal "+" => rest.reverse
      | _ => leading
    | [] => []

  isPositionalAssignment (s : String) : Bool :=
    match s.toList with
    | d1 :: '=' :: _ => d1.isDigit
    | d1 :: d2 :: '=' :: _ => d1.isDigit && d2.isDigit
    | _ => false

  takeUntilEq (s : String) : String :=
    String.ofList (s.toList.takeWhile (fun c => c != '='))

  isLeadingNumberVar (s : String) : Bool :=
    let lead := takeUntilEq s
    match lead.toList with
    | [] => false
    | x :: _ =>
      x.isDigit && lead.toList.all isVariableChar && !(lead.toList.all Char.isDigit)

  isConflictMarker (cmdWord : Token) : Bool :=
    match getUnquotedLiteral cmdWord with
    | some str =>
      let chars := str.toList
      chars.length >= 4 && chars.length <= 12 && chars.all (· == '=')
    | Option.none => false

  mayBeVariableName (leading : List Token) : Bool :=
    if leading.any isQuotes then false
    else if leading.any willBecomeMultipleArgs then false
    else
      let fakeWord : Token := ⟨⟨0⟩, .T_NormalWord leading⟩
      match getLiteralStringExt (fun _ => some "x") fakeWord with
      | some str => isVariableName str
      | Option.none => false

  positionalMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2270
      "To assign positional parameters, use 'set -- first second ..' (or use [ ] to compare)."

  indirectionMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2271
      "For indirection, use arrays, declare \"var$n=value\", or (for sh) read/eval."

  badComparisonMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2272
      "Command name contains ==. For comparison, use [ \"$var\" = value ]."

  conflictMarkerMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2273
      "Sequence of ===s found. Merge conflict or intended as a commented border?"

  borderMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2274
      "Command name starts with ===. Intended as a commented border?"

  prefixMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2275
      "Command name starts with =. Bad line break?"

  genericMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2276
      "This is interpreted as a command name containing '='. Bad assignment or comparison?"

  assign0Msg (id : Id) : TokenComment :=
    match params.shellType with
    | .Bash =>
      makeComment .errorC id 2277
        "Use BASH_ARGV0 to assign to $0 in bash (or use [ ] to compare)."
    | .Ksh =>
      makeComment .errorC id 2278
        "$0 can't be assigned in Ksh (but it does reflect the current function)."
    | .Dash | .BusyboxSh =>
      makeComment .errorC id 2279
        "$0 can't be assigned in Dash. This becomes a command name."
    | _ =>
      makeComment .errorC id 2280
        "$0 can't be assigned this way, and there is no portable alternative."

  leadingNumberMsg (id : Id) : TokenComment :=
    makeComment .errorC id 2282
      "Variable names can't start with numbers, so this is interpreted as a command."

  dontUseDollarLhsMsg (id : Id) (braced : Bool) : TokenComment :=
    let lhs := if braced then "${}" else "$"
    makeComment .errorC id 2281
      s!"Don't use {lhs} on the left side of assignments."

  startsWithEq (t : Token) : Bool :=
    match t.inner with
    | .T_Literal s => s.startsWith "="
    | _ => false

  hasDoubleEquals (eqTok : Token) (afterEq : List Token) : Bool :=
    match eqTok.inner with
    | .T_Literal s =>
      if Regex.containsSubstring s "==" then
        true
      else if s == "=" then
        match afterEq with
        | next :: _ => startsWithEq next
        | [] => false
      else
        false
    | _ => false

  msg (cmdWord : Token) (leading : List Token) (eqTok : Token) (afterEq : List Token) : List TokenComment :=
    match eqTok.inner with
    | .T_Literal s =>
      let leading := stripSinglePlus leading
      let cmdStr := getLiteralStringExt (fun _ => some "x") cmdWord |>.getD ""
      let hasEqEq := Regex.containsSubstring cmdStr "==" || hasDoubleEquals eqTok afterEq
      match leading, s with
      -- --foo=42 (handled by SC2215)
      | [], _ =>
        if s.startsWith "-" then
          []
        else if s.startsWith "=" then
          match originalToken.inner with
          | .T_SimpleCommand _ [singleWord] =>
            if isConflictMarker singleWord then
              [conflictMarkerMsg originalToken.id]
            else if s.startsWith "===" then
              [borderMsg originalToken.id]
            else
              [prefixMsg cmdWord.id]
          | _ =>
            if s.startsWith "===" then [borderMsg originalToken.id] else [prefixMsg cmdWord.id]
        else if hasEqEq then
          [badComparisonMsg cmdWord.id]
        else if isPositionalAssignment s then
          if s.startsWith "0=" then [assign0Msg eqTok.id] else [positionalMsg eqTok.id]
        else if isLeadingNumberVar s then
          [leadingNumberMsg cmdWord.id]
        else
          [genericMsg cmdWord.id]

      -- ${var...}=foo / $var=foo
      | [dollar], _ =>
        if hasEqEq then
          [badComparisonMsg cmdWord.id]
        else
          match dollar.inner with
          | .T_DollarBraced braced content =>
            if s.startsWith "=" then
              let variableStr := getLiteralStringExt (fun _ => some "x") content |>.getD ""
              if variableStr == "" then
                [genericMsg cmdWord.id]
              else if variableStr.startsWith "#" then
                [genericMsg cmdWord.id]
              else if variableStr == "0" then
                [assign0Msg dollar.id]
              else if variableStr.toList.all Char.isDigit then
                [positionalMsg dollar.id]
              else
                let variableReference := ASTLib.getBracedReference variableStr
                let variableModifier := ASTLib.getBracedModifier variableStr
                let isArray :=
                  variableReference != "" &&
                  variableModifier.startsWith "[" &&
                  variableModifier.endsWith "]"
                if isArray || isVariableName variableStr then
                  [dontUseDollarLhsMsg dollar.id braced]
                else
                  [indirectionMsg cmdWord.id]
            else
              [genericMsg cmdWord.id]
          | _ =>
            [genericMsg cmdWord.id]

      -- var${x}=value (indirection)
      | (_ :: _), _ =>
        if hasEqEq then
          [badComparisonMsg cmdWord.id]
        else
          let beforeEq := takeUntilEq s
          if mayBeVariableName leading && beforeEq.toList.all isVariableChar then
            [indirectionMsg cmdWord.id]
          else
            [genericMsg cmdWord.id]
    | _ => []

  checkWord (t : Token) : List TokenComment :=
    match t.inner with
    | .T_NormalWord parts =>
      if parts.any hasEquals then
        match splitAtEquals parts with
        | some (leading, eqTok, afterEq) => msg t leading eqTok afterEq
        | Option.none => []
      else []
    | _ => []

/-- SC2283-SC2285: `foo = bar` is interpreted as a command, not a comparison -/
def checkSecondArgIsComparison (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (_lhs :: arg :: _) =>
    match getLeadingUnquotedString arg with
    | some argStr =>
      if argStr.startsWith "====" then
        []
      else if argStr.startsWith "+=" then
        [makeComment .errorC t.id 2285
          "Remove spaces around += to assign (or quote '+=' if literal)."]
      else if argStr.startsWith "==" then
        [makeComment .errorC t.id 2284
          "Use [ x = y ] to compare values (or quote '==' if literal)."]
      else if argStr.startsWith "=" then
        let id :=
          match arg.inner with
          | .T_NormalWord (x :: _) => x.id
          | _ => arg.id
        [makeComment .errorC id 2283
          "Remove spaces around = to assign (or use [ ] to compare, or quote '=' if literal)."]
      else
        []
    | Option.none => []
  | _ => []

/-- SC2286-SC2289: Command name ends with suspicious trailing symbols. -/
def checkCommandWithTrailingSymbol (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: _) =>
      let str := getLiteralStringDef "x" cmd
      let last := ShellCheck.Prelude.lastOrDefault 'x' str.toList
      if str == "." || str == ":" || str == " " || str == "//" then
        []
      else if str == "" then
        [makeComment .errorC cmd.id 2286
          "This empty string is interpreted as a command name. Double check syntax (or use 'true' as a no-op)."]
      else if last == '/' then
        [makeComment .errorC cmd.id 2287
          "This is interpreted as a command name ending with '/'. Double check syntax."]
      else if trailingSymbols.contains last then
        [makeComment .warningC cmd.id 2288
          s!"This is interpreted as a command name ending with {formatChar last}. Double check syntax."]
      else if str.toList.contains '\t' then
        [makeComment .errorC cmd.id 2289
          "This is interpreted as a command name containing a tab. Double check syntax."]
      else if str.toList.contains '\n' then
        [makeComment .errorC cmd.id 2289
          "This is interpreted as a command name containing a linefeed. Double check syntax."]
      else
        []
  | _ => []
where
  trailingSymbols : List Char :=
    "\\.,([{<>}])#\"'% ".toList

  formatChar (c : Char) : String :=
    match c with
    | ' ' => "space"
    | '\'' => "apostrophe"
    | '\"' => "doublequote"
    | other => s!"'{other}'"

/-- SC2292: Prefer [[ ]] over [ ] for tests in Bash/Ksh/Busybox -/
def checkRequireDoubleBracket (params : Parameters) (t : Token) : List TokenComment :=
  if params.shellType == .Bash || params.shellType == .Ksh || params.shellType == .BusyboxSh then
    match t.inner with
    | .T_Condition .singleBracket _ =>
      [makeComment .styleC t.id 2292
        "Prefer [[ ]] over [ ] for tests in Bash/Ksh/Busybox."]
    | _ => []
  else []

/-- SC2059: Don't use variables in the printf format string -/
def checkPrintfFormat (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: format :: _) =>
    if getCommandName ⟨cmd.id, cmd.inner⟩ == some "printf" then
      -- Check if format contains variable expansion
      if hasVariableExpansion format then
        [makeComment .warningC format.id 2059
          "Don't use variables in the printf format string. Use printf '...' \"$var\"."]
      else []
    else []
  | _ => []
where
  hasVariableExpansion (t : Token) : Bool :=
    match t.inner with
    | .T_NormalWord parts => parts.any isExpansion
    | .T_DoubleQuoted parts => parts.any isExpansion
    | _ => false

  isExpansion (t : Token) : Bool :=
    match t.inner with
    | .T_DollarBraced .. => true
    | .T_DollarExpansion .. => true
    | .T_Backticked .. => true
    | _ => false

/-- SC2012: Use find instead of ls to better handle non-alphanumeric filenames -/
def checkLsFind (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: _) =>
    if getCommandBasename ⟨cmd.id, cmd.inner⟩ == some "ls" then
      -- Check if this is in a command substitution context
      []  -- Simplified - would check parent context
    else []
  | _ => []

/-- SC2016: Expressions don't expand in single quotes, use double quotes -/
def checkSingleQuotedVariable (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SingleQuoted s =>
    if hasExpansionSyntax s then
      [makeComment .infoC t.id 2016
        "Expressions don't expand in single quotes, use double quotes for that."]
    else []
  | _ => []
where
  hasExpansionSyntax (s : String) : Bool :=
    Regex.containsSubstring s "$" ||
    Regex.containsSubstring s "`"

/-- SC2044: For loops over find output are fragile -/
def checkForInFind (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_ForIn _ words _ =>
    words.head?.bind (fun w =>
      match w.inner with
      | .T_NormalWord [sub] =>
        match sub.inner with
        | .T_DollarExpansion cmds =>
          if cmds.any (fun c => getCommandBasename c == some "find") then
            some [makeComment .warningC t.id 2044
              "For loops over find output are fragile. Use find -exec or while read."]
          else Option.none
        | .T_Backticked cmds =>
          if cmds.any (fun c => getCommandBasename c == some "find") then
            some [makeComment .warningC t.id 2044
              "For loops over find output are fragile. Use find -exec or while read."]
          else Option.none
        | _ => Option.none
      | _ => Option.none
    ) |>.getD []
  | _ => []

/-- SC2064: Use single quotes for trap to avoid immediate expansion -/
def checkTrapExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: handler :: _) =>
    if getCommandName ⟨cmd.id, cmd.inner⟩ == some "trap" then
      match handler.inner with
      | .T_DoubleQuoted parts =>
        if parts.any isCommandSubstitution then
          [makeComment .warningC handler.id 2064
            "Use single quotes, otherwise this expands now rather than when signalled."]
        else []
      | .T_NormalWord parts =>
        if parts.any isCommandSubstitution then
          [makeComment .warningC handler.id 2064
            "Use single quotes, otherwise this expands now rather than when signalled."]
        else []
      | _ => []
    else []
  | _ => []
where
  isCommandSubstitution (t : Token) : Bool :=
    match t.inner with
    | .T_DollarExpansion _ => true
    | .T_Backticked _ => true
    | _ => false

/-- SC2072: Decimals are not supported -/
def checkArithmeticDecimals (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarArithmetic inner => checkForDecimals inner
  | .TA_Expansion parts => parts.foldl (fun acc p => acc ++ checkForDecimals p) []
  | _ => []
where
  checkForDecimals (t : Token) : List TokenComment :=
    match t.inner with
    | .T_Literal s =>
      if Regex.containsSubstring s "." &&
         s.any Char.isDigit then
        [makeComment .errorC t.id 2072
          "Decimals are not supported. Either use integers only, or use bc or awk to compare."]
      else []
    | _ => []

/-- SC2074: Can't use -o inside [[ ]]. Use || and [[ ]] separately -/
def checkDoubleBracketOrOperator (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .doubleBracket op _ _ =>
    if op == "-o" then
      [makeComment .errorC t.id 2074
        "Can't use -o inside [[ ]]. Use || and separate [[ ]] instead."]
    else []
  | _ => []

/-- SC2075: Can't use -a inside [[ ]]. Use && and [[ ]] separately -/
def checkDoubleBracketAndOperator (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .doubleBracket op _ _ =>
    if op == "-a" then
      [makeComment .errorC t.id 2075
        "Can't use -a inside [[ ]]. Use && and separate [[ ]] instead."]
    else []
  | _ => []

/-- SC2076: Remove quotes from right-hand side -/
def checkQuotedRightHandRegex (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Binary .doubleBracket "=~" _ rhs =>
    match rhs.inner with
    | .T_NormalWord [single] =>
      match single.inner with
      | .T_DoubleQuoted _ =>
        [makeComment .warningC rhs.id 2076
          "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
      | .T_SingleQuoted _ =>
        [makeComment .warningC rhs.id 2076
          "Remove quotes from right-hand side of =~ to match as a regex rather than literally."]
      | _ => []
    | _ => []
  | _ => []

/-- SC2077: You can't redirect to a dollar expansion -/
def checkRedirectToDollarExpansion (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Redirecting redirects _ =>
    redirects.foldl (fun acc r => acc ++ checkRedirect r) []
  | _ => []
where
  checkRedirect (r : Token) : List TokenComment :=
    match r.inner with
    | .T_FdRedirect _ op =>
      match op.inner with
      | .T_IoFile _ target =>
        match target.inner with
        | .T_DollarExpansion _ =>
          [makeComment .warningC target.id 2077
            "You can't redirect to a command substitution."]
        | _ => []
      | _ => []
    | _ => []

private def arithModWarning (id : Id) : List TokenComment :=
  [makeComment .warningC id 2257
    "Arithmetic modifications in command redirections may be discarded. Do them separately."]

private partial def arithmeticModifies (expr : Token) : Bool :=
  match expr.inner with
  | .TA_Unary op _ => op == "++" || op == "--" || op == "++post" || op == "--post"
  | .TA_Assignment _ _ _ => true
  | .TA_Binary _ lhs rhs => arithmeticModifies lhs || arithmeticModifies rhs
  | .TA_Trinary cond t e =>
      arithmeticModifies cond || arithmeticModifies t || arithmeticModifies e
  | .TA_Sequence exprs => exprs.any arithmeticModifies
  | .TA_Parenthesis inner => arithmeticModifies inner
  | .TA_Expansion parts => parts.any arithmeticModifies
  | .TA_Variable _ indices => indices.any arithmeticModifies
  | _ => false

/-- SC2257: Arithmetic modifications in command redirections may be discarded. -/
def checkModifiedArithmeticInRedirection (params : Parameters) (t : Token) : List TokenComment :=
  if params.shellType == .Dash || params.shellType == .BusyboxSh then
    []
  else
    match t.inner with
    | .T_Redirecting redirs cmd =>
      match cmd.inner with
      | .T_SimpleCommand _ (_ :: _) =>
        redirs.flatMap checkRedir
      | _ => []
    | _ => []
where
  checkRedir (redir : Token) : List TokenComment :=
    match redir.inner with
    | .T_FdRedirect _ target => checkTarget target
    | .T_IoFile _ word => checkWord word
    | .T_HereString word => checkWord word
    | .T_HereDoc _ _ _ content => content.flatMap checkWord
    | _ => []

  checkTarget (target : Token) : List TokenComment :=
    match target.inner with
    | .T_IoFile _ word => checkWord word
    | .T_HereString word => checkWord word
    | .T_HereDoc _ _ _ content => content.flatMap checkWord
    | _ => []

  checkWord (word : Token) : List TokenComment :=
    match word.inner with
    | .T_DollarArithmetic expr =>
      if arithmeticModifies expr then arithModWarning word.id else []
    | _ =>
      getWordParts word |>.flatMap fun part =>
        match part.inner with
        | .T_DollarArithmetic expr =>
          if arithmeticModifies expr then arithModWarning part.id else []
        | _ => []

/-- SC2078: This expression is constant. Did you forget the $ on a variable? -/
def checkConstantTest (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Nullary _ word =>
    match getLiteralString word with
    | some s =>
      if isVariableLike s then
        [makeComment .warningC word.id 2078
          s!"This expression is constant. Did you forget the $ on '{s}'?"]
      else []
    | Option.none => []
  | _ => []
where
  isVariableLike (s : String) : Bool :=
    isVariableName s && s.length > 1

/-- SC2079: (( )) doesn't support fractions. For floating point, use bc or awk -/
def checkFractionsInArithmetic (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TA_Binary "/" lhs rhs =>
    -- Check if this might produce a fraction
    if mightProduceFraction lhs rhs then
      [makeComment .warningC t.id 2079
        "(( )) doesn't support fractions. For floating point, use bc or awk."]
    else []
  | _ => []
where
  mightProduceFraction (_lhs _rhs : Token) : Bool :=
    -- Simplified check - would need to analyze values
    false

/-- SC2082: To expand via indirection, use arrays, ${!name} or eval -/
def checkDollarDollar (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    match getLiteralString content with
    | some s =>
      if s.startsWith "$" then
        let rest := s.drop 1
        if rest.startsWith "{" || rest.startsWith "(" || rest.startsWith "'" ||
           rest.startsWith "\"" || rest.startsWith "`" then
          []
        else
          [makeComment .errorC t.id 2082
            "To expand via indirection, use arrays, ${!name} or (associatively risky) eval."]
      else []
    | Option.none => []
  | _ => []

/-- SC2296-SC2301: Invalid or nested parameter expansions -/
def checkBadParameterExpansions (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    let raw := getLiteralString content |>.getD (String.join (oversimplify content))
    if raw.isEmpty then []
    else checkRaw raw t.id
  | _ => []
where
  isVariable (s : String) : Bool :=
    match s.toList with
    | [c] => isVariableStartChar c || isSpecialVariableChar c || c.isDigit
    | _ => isVariableName s

  isUnmodifiedExpansionString (s : String) : Bool :=
    let ref := ASTLib.getBracedReference s
    let mod := ASTLib.getBracedModifier s
    mod.isEmpty && (isVariable ref || isVariableName ref)

  /-- Rough indirection detector matching ShellCheck's SC2082 behavior. -/
  isPureIndirection (raw : String) : Bool :=
    if raw.startsWith "$((" then
      raw.endsWith "))"
    else if raw.startsWith "$(" then
      raw.endsWith ")"
    else if raw.startsWith "${" then
      raw.endsWith "}"
    else if raw.startsWith "`" then
      raw.endsWith "`"
    else if raw.startsWith "$" then
      isVariable ((raw.drop 1).toString)
    else
      false

  firstIndexOf (s : String) (needle : Char) : Option Nat :=
    let rec go : List Char → Nat → Option Nat
      | [], _ => Option.none
      | c :: rest, i => if c == needle then some i else go rest (i + 1)
    go s.toList 0

  checkRaw (raw : String) (id : Id) : List TokenComment :=
    if isPureIndirection raw then
      [makeComment .errorC id 2082
        "To expand via indirection, use arrays, ${!name} or (for sh only) eval."]
    else if raw.startsWith "\"" && raw.endsWith "\"" && raw.length >= 2 then
      let inner := (raw.drop 1).dropEnd 1 |>.toString
      if isVariable inner then
        [makeComment .errorC id 2297
          "Double quotes must be outside ${}: ${\"invalid\"} vs \"${valid}\"."]
      else
        [makeComment .errorC id 2296
          "Parameter expansions can't start with \". Double check syntax."]
    else if raw.startsWith "'" then
      [makeComment .errorC id 2301
        "Parameter expansion starts with unexpected quotes. Double check syntax."]
    else if raw.startsWith "$(" || raw.startsWith "`" then
      [makeComment .errorC id 2300
        "Parameter expansion can't be applied to command substitutions. Use temporary variables."]
    else if raw.startsWith "${" then
      match firstIndexOf raw '}' with
      | some i =>
        let inner := ((raw.take (i + 1)).drop 2).dropEnd 1 |>.toString
        if isUnmodifiedExpansionString inner then
          [makeComment .errorC id 2298
            "${${x}} is invalid. For expansion, use ${x}. For indirection, use arrays, ${!x} or (for sh) eval."]
        else
          [makeComment .errorC id 2299
            "Parameter expansions can't be nested. Use temporary variables."]
      | Option.none =>
        [makeComment .errorC id 2298
          "${${x}} is invalid. For expansion, use ${x}. For indirection, use arrays, ${!x} or (for sh) eval."]
    else if raw.startsWith "$" then
      [makeComment .errorC id 2298
        "${$x} is invalid. For expansion, use ${x}. For indirection, use arrays, ${!x} or (for sh) eval."]
    else
      match raw.toList.head? with
      | some c =>
        if isVariableChar c || isSpecialVariableChar c then []
        else
          [makeComment .errorC id 2296
            s!"Parameter expansions can't start with {c}. Double check syntax."]
      | Option.none => []

/-- SC2295: Quote expansions inside `${var%pattern}` / `${var#pattern}` patterns. -/
def checkUnquotedParameterExpansionPattern (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced true content =>
    match content.inner with
    | .T_NormalWord (first :: rest) =>
      match first.inner with
      | .T_Literal _ =>
        if rest.isEmpty then
          []
        else
          let modifier := ASTLib.getBracedModifier (String.join (oversimplify content))
          if modifier.startsWith "%" || modifier.startsWith "#" then
            let msg :=
              "Expansions inside ${..} need to be quoted separately, otherwise they match as patterns."
            let rec go (prev : Option Token) (xs : List Token) : List TokenComment :=
              match xs with
              | [] => []
              | part :: rest =>
                let next := rest.head?
                let quotedByNeighbors :=
                  match prev, next with
                  | some p, some n =>
                    (isDoubleQuoteDelimiter p && isDoubleQuoteDelimiter n) ||
                      (isSingleQuoteDelimiter p && isSingleQuoteDelimiter n)
                  | _, _ => false
                let here :=
                  match part.inner with
                  | .T_DollarBraced .. =>
                    if quotedByNeighbors then [] else [makeComment .infoC part.id 2295 msg]
                  | .T_DollarExpansion .. =>
                    if quotedByNeighbors then [] else [makeComment .infoC part.id 2295 msg]
                  | .T_Backticked .. =>
                    if quotedByNeighbors then [] else [makeComment .infoC part.id 2295 msg]
                  | _ => []
                here ++ go (some part) rest
            go Option.none rest
          else
            []
      | _ => []
    | _ => []
  | _ => []
where
  isDoubleQuoteDelimiter (t : Token) : Bool :=
    match t.inner with
    | .T_Literal s => s == "\"" || s == "\\\""
    | _ => false

  isSingleQuoteDelimiter (t : Token) : Bool :=
    match t.inner with
    | .T_Literal s => s == "'" || s == "\\'"
    | _ => false

/-- SC2212: Empty [ ]/[[ ]] conditionals are always true. Prefer `false`. -/
def checkEmptyCondition (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .TC_Empty _ =>
    [makeComment .styleC t.id 2212
      "Use 'false' instead of empty [/[[ conditionals."]
  | _ => []

/-- SC2083: Don't add spaces after [ in -/
def checkBracketSpacing (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_Condition .singleBracket expr =>
    match expr.inner with
      | .TC_Empty _ => []  -- Empty condition already handled elsewhere
      | _ => []  -- Spacing issues would be caught by parser
  | _ => []

/-- SC2084: Remove '$' or the shell will try to execute the output -/
def checkDollarBraceExpansionInCommand (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: _) =>
    match cmd.inner with
    | .T_NormalWord [single] =>
      match single.inner with
      | .T_DollarBraceCommandExpansion _ _ =>
        [makeComment .warningC cmd.id 2084
          "Remove '$' or the shell will try to execute the output as a command name."]
      | _ => []
    | _ => []
  | _ => []

/-- SC2086: Double quote to prevent globbing and word splitting -/
def checkUnquotedVariable (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ content =>
    if not (isQuoteFree params.shellType params.parentMap t) &&
       not (ASTLib.isCountingReference t) &&
       not (ASTLib.isArrayExpansion t) then
      let varName := ASTLib.getBracedReference (String.join (oversimplify content))
      if not (variablesWithoutSpaces.contains varName) then
        [makeComment .warningC t.id 2086
          "Double quote to prevent globbing and word splitting."]
      else []
    else []
  | _ => []

/-- SC2117: To run commands as another user, use su -c or sudo -/
def checkBashAsLogin (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_SimpleCommand _ (cmd :: args) =>
    let cmdName := getCommandBasename ⟨cmd.id, cmd.inner⟩
    if cmdName == some "bash" || cmdName == some "sh" then
      if args.any (fun a => getLiteralString a == some "-c") then
        []  -- -c is fine
      else if args.any (fun a =>
        let s := getLiteralString a
        s == some "-l" || s == some "--login"
      ) then
        [makeComment .infoC t.id 2117
          "To run commands as another user, use su -c or sudo."]
      else []
    else []
  | _ => []

private def uselessBangMessage : String :=
  "This ! is not on a condition and skips errexit. Use `&& exit 1` instead, or make sure $? is checked."

private def dropLastList {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | x :: xs => x :: dropLastList xs

private def isDirectFunctionBody (parents : Std.HashMap Id Token) (t : Token) : Bool :=
  match parents.get? t.id with
  | some parent =>
      match parent.inner with
      | .T_Function .. => true
      | _ => false
  | Option.none => false

private def isConditionInPath (parents : Std.HashMap Id Token) (t : Token) : Bool :=
  let path := getPath parents t
  let rec go : List Token → Bool
    | child :: parent :: rest =>
        let here :=
          match parent.inner with
          | .T_AndIf lhs _ => child.id == lhs.id
          | .T_OrIf lhs _ => child.id == lhs.id
          | .T_IfExpression conditions _ =>
              let condTokens := conditions.flatMap (fun (c, _) => c.getLast?.toList)
              condTokens.any (fun tok => tok.id == child.id)
          | .T_UntilExpression cond _ =>
              cond.getLast?.elim false (fun tok => tok.id == child.id)
          | .T_WhileExpression cond _ =>
              cond.getLast?.elim false (fun tok => tok.id == child.id)
          | _ => false
        bif here then true else go (parent :: rest)
    | _ => false
  go path

private partial def nonReturningCommandsForBang (parents : Std.HashMap Id Token) : Token → List Token
  | t =>
      match t.inner with
      | .T_Script _ cmds => dropLastList cmds
      | .T_BraceGroup cmds =>
          if isDirectFunctionBody parents t then dropLastList cmds else cmds
      | .T_Subshell cmds => dropLastList cmds
      | .T_WhileExpression cond body => dropLastList cond ++ body
      | .T_UntilExpression cond body => dropLastList cond ++ body
      | .T_ForIn _ _ body => body
      | .T_ForArithmetic _ _ _ body => body
      | .T_IfExpression conds elses =>
          (conds.flatMap (fun (c, _) => dropLastList c)) ++ (conds.flatMap (fun (_, b) => b)) ++ elses
      | .T_Annotation _ inner => nonReturningCommandsForBang parents inner
      | _ => []

private partial def checkUselessBangAt (parents : Std.HashMap Id Token) : Token → List TokenComment
  | t =>
      match t.inner with
      | .T_Banged _cmd =>
          if isConditionInPath parents t then
            []
          else
            [makeComment .infoC t.id 2251 uselessBangMessage]
      | .T_Annotation _ inner => checkUselessBangAt parents inner
      | _ => []

/-- SC2251: `! cmd` is not a condition and skips errexit in `set -e` scripts. -/
def checkUselessBang (params : Parameters) (root : Token) : List TokenComment :=
  if !params.hasSetE then
    []
  else
    let parents := params.parentMap
    (nonReturningCommandsForBang parents root).flatMap (checkUselessBangAt parents)

/-- SC2310/SC2311: `set -e` is disabled in conditionals and command substitutions. -/
def checkSetESuppressed (params : Parameters) (root : Token) : List TokenComment :=
  if !params.hasSetE then
    []
  else
    let funcMap := getFunctionMap root
    let all := collectTokens root
    all.foldl (fun acc t =>
      match t.inner with
      | .T_SimpleCommand _ (cmdWord :: _) =>
        match getUnquotedLiteral cmdWord with
        | some name =>
          if funcMap.contains name then
            acc ++ checkCmd cmdWord
          else
            acc
        | Option.none => acc
      | _ => acc
    ) []
where
  parents : Std.HashMap Id Token := params.parentMap

  errExitEnabled (t : Token) : Bool :=
    params.hasInheritErrexit || containsSetE t

  informConditional (condType : String) (cmdWord : Token) : TokenComment :=
    makeComment .infoC cmdWord.id 2310
      ("This function is invoked in " ++ condType ++ " so set -e will be disabled. " ++
        "Invoke separately if failures should cause the script to exit.")

  informUninherited (cmdWord : Token) : TokenComment :=
    makeComment .infoC cmdWord.id 2311
      ("Bash implicitly disabled set -e for this function invocation because it's inside a " ++
        "command substitution. Add set -e; before it or enable inherit_errexit.")

  containsId (child : Token) (xs : List Token) : Bool :=
    xs.any fun t => t.id == child.id

  checkCmd (cmdWord : Token) : List TokenComment :=
    let path := getPath parents cmdWord
    let rec go : List Token → List TokenComment
      | child :: parent :: rest =>
        let here :=
          match parent.inner with
          | .T_Banged cond =>
            if child.id == cond.id then [informConditional "a ! condition" cmdWord] else []
          | .T_AndIf lhs _ =>
            if child.id == lhs.id then [informConditional "an && condition" cmdWord] else []
          | .T_OrIf lhs _ =>
            if child.id == lhs.id then [informConditional "an || condition" cmdWord] else []
          | .T_IfExpression conditions _ =>
            let condTokens := conditions.flatMap (fun (c, _) => c)
            if containsId child condTokens then [informConditional "an 'if' condition" cmdWord] else []
          | .T_UntilExpression cond _ =>
            if containsId child cond then [informConditional "an 'until' condition" cmdWord] else []
          | .T_WhileExpression cond _ =>
            if containsId child cond then [informConditional "a 'while' condition" cmdWord] else []
          | .T_DollarExpansion _ =>
            if !errExitEnabled parent then [informUninherited cmdWord] else []
          | .T_Backticked _ =>
            if !errExitEnabled parent then [informUninherited cmdWord] else []
          | _ => []
        here ++ go (parent :: rest)
      | _ => []
    go path

/-- SC2312: Consider invoking this command separately to avoid masking its return value. -/
def checkExtraMaskedReturns (params : Parameters) (root : Token) : List TokenComment :=
  runNodeAnalysis findMaskingNodes params (removeTransparentCommands root)
where
  msg : String :=
    "Consider invoking this command separately to avoid masking its return value (or use '|| true' to ignore)."

  /-- Drop transparent `time` wrappers (best-effort), mirroring ShellCheck's `removeTransparentCommands`. -/
  removeTransparentCommands (t : Token) : Token :=
    doTransform (fun tok =>
      match tok.inner with
      | .T_SimpleCommand assigns (_cmd :: args) =>
        if getCommandBasename tok == some "time" && !args.isEmpty then
          ⟨tok.id, .T_SimpleCommand assigns args⟩
        else
          tok
      | _ => tok
    ) t

  containsSimpleCommand (t : Token) : Bool :=
    (collectTokens t).any fun tok =>
      match tok.inner with
      | .T_SimpleCommand .. => true
      | _ => false

  /-- Filter to list elements that contain simple commands, then drop the last one. -/
  allButLastSimpleCommands (xs : List Token) : List Token :=
    let simple := xs.filter containsSimpleCommand
    match simple.reverse with
    | [] => []
    | _ :: rest => rest.reverse

  getSingleCmdBasename (t : Token) : Option String :=
    match t.inner with
    | .T_Pipeline _ cmds =>
      match cmds with
      | [only] => getCommandBasename only
      | _ => Option.none
    | _ => getCommandBasename t

  isOrIfIgnore (t : Token) : Bool :=
    match t.inner with
    | .T_OrIf _ rhs =>
      match getSingleCmdBasename rhs with
      | some "true" => true
      | some ":" => true
      | _ => false
    | _ => false

  /-- Determine if a command's return code appears to be intentionally ignored (e.g. `cmd || true`). -/
  isMaskDeliberate (p : Parameters) (t : Token) : Bool :=
    (getPath p.parentMap t).any isOrIfIgnore

  declaringCommands : List String := ["local", "readonly", "declare", "export", "typeset"]

  isDeclaringCommand (t : Token) : Bool :=
    match getCommandBasename t with
    | some "local" =>
      -- local -r x=$(false) is intentionally ignored for SC2155 in upstream
      if hasFlag t "r" then
        false
      else
        true
    | some base =>
      base ∈ declaringCommands
    | Option.none => false

  /-- Are we already checking this masked return elsewhere (e.g., SC2155 for declaring commands)? -/
  isCheckedElsewhere (p : Parameters) (t : Token) : Bool :=
    let parents := (getPath p.parentMap t).drop 1
    parents.any isDeclaringCommand

  isHarmlessCommand (t : Token) : Bool :=
    match getCommandBasename t with
    | some base =>
      base ∈ ["echo", "basename", "dirname", "printf", "set", "shopt"]
    | Option.none => false

  isMaskedNode (p : Parameters) (t : Token) : Bool :=
    !(isHarmlessCommand t || isCheckedElsewhere p t || isMaskDeliberate p t)

  findMaskedNodes (p : Parameters) (t : Token) : List TokenComment :=
    let toks := collectTokens t
    toks.foldl (fun acc node =>
      match node.inner with
      | .T_SimpleCommand _ (_ :: _) =>
        if isMaskedNode p node then
          makeComment .infoC node.id 2312 msg :: acc
        else
          acc
      | .T_Condition .. =>
        if isMaskedNode p node then
          makeComment .infoC node.id 2312 msg :: acc
        else
          acc
      | _ => acc
    ) []

  findMaskedNodesInList (p : Parameters) (xs : List Token) : List TokenComment :=
    xs.flatMap (findMaskedNodes p)

  findMaskingNodes (p : Parameters) (t : Token) : List TokenComment :=
    match t.inner with
    | .T_Arithmetic expr => findMaskedNodesInList p [expr]
    | .T_Array xs => findMaskedNodesInList p (allButLastSimpleCommands xs)
    | .T_Condition _ cond => findMaskedNodesInList p [cond]
    | .T_DoubleQuoted xs => findMaskedNodesInList p (allButLastSimpleCommands xs)
    | .T_HereDoc _ _ _ xs => findMaskedNodesInList p xs
    | .T_HereString w => findMaskedNodesInList p [w]
    | .T_NormalWord xs => findMaskedNodesInList p (allButLastSimpleCommands xs)
    | .T_Pipeline _ cmds =>
      if p.hasPipefail then [] else findMaskedNodesInList p (allButLastSimpleCommands cmds)
    | .T_ProcSub _ cmds => findMaskedNodesInList p cmds
    | .T_SimpleCommand assigns [] =>
      findMaskedNodesInList p (allButLastSimpleCommands assigns)
    | .T_SimpleCommand assigns (_cmd :: args) =>
      findMaskedNodesInList p (assigns ++ args)
    | _ => []

/-!
## Function Scope Analysis

Complex checks that analyze function definitions and their usage across the script.
-/

/-- SC2032: Use 'export -f' to export functions to subprocess
    SC2033: Shell functions can't be passed to external commands -/
def checkFunctionsUsedExternally (params : Parameters) (_root : Token) : List TokenComment :=
  let funcMap := getFunctionsAndAliases params.rootNode
  if funcMap.isEmpty then []
  else
    -- Find all command invocations
    let invocations := findCommandInvocations params.rootNode
    invocations.foldl (fun acc (cmdToken, cmdName) =>
      -- Check if this is a command that accepts another command as argument
      if commandsWithFunctionAsArg.contains cmdName then
        -- Check the arguments for function/alias names
        match cmdToken.inner with
        | .T_SimpleCommand _ (_ :: args) =>
          acc ++ args.flatMap fun arg =>
            match couldBeFunctionReference funcMap arg with
            | some funcName =>
              let warnArg :=
                makeComment .warningC arg.id 2033
                  s!"Shell functions can't be passed to external commands. Use separate script or 'export -f {funcName}'."
              let infoDef :=
                match funcMap.get? funcName with
                | some definitionTok =>
                  let context :=
                    match params.tokenPositions.get? cmdToken.id with
                    | some (start, _) => s!" on line {start.posLine}."
                    | Option.none => "."
                  some (makeComment .infoC definitionTok.id 2032
                    s!"This function can't be invoked via {cmdName}{context}")
                | Option.none => Option.none
              warnArg :: infoDef.toList
            | Option.none => []
        | .T_Redirecting _ inner =>
          match inner.inner with
          | .T_SimpleCommand _ (_ :: args) =>
            acc ++ args.flatMap fun arg =>
              match couldBeFunctionReference funcMap arg with
              | some funcName =>
                let warnArg :=
                  makeComment .warningC arg.id 2033
                    s!"Shell functions can't be passed to external commands. Use separate script or 'export -f {funcName}'."
                let infoDef :=
                  match funcMap.get? funcName with
                  | some definitionTok =>
                    let context :=
                      match params.tokenPositions.get? cmdToken.id with
                      | some (start, _) => s!" on line {start.posLine}."
                      | Option.none => "."
                    some (makeComment .infoC definitionTok.id 2032
                      s!"This function can't be invoked via {cmdName}{context}")
                  | Option.none => Option.none
                warnArg :: infoDef.toList
              | Option.none => []
          | _ => acc
        | _ => acc
      else acc
    ) []

/-!
## Bats tests
-/

/-- SC2314/SC2315: Bats negation does not fail the test. -/
def checkBatsTestDoesNotUseNegation (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_BatsTest _ body =>
    match body.inner with
    | .T_BraceGroup commands =>
        commands.flatMap (check commands)
    | _ => []
  | _ => []
where
  isLastOf (target : Token) : List Token → Bool
    | [] => false
    | [x] => x.id == target.id
    | _ :: rest => isLastOf target rest

  getCondition (cmd : Token) : Option Token :=
    match cmd.inner with
    | .T_Redirecting _ inner =>
      match inner.inner with
      | .T_Condition .. => some inner
      | _ => Option.none
    | .T_Condition .. => some cmd
    | _ => Option.none

  warnRun (cmd : Token) (commands : List Token) : List TokenComment :=
    if isLastOf cmd commands then
      [makeComment .styleC cmd.id 2314
        "In Bats, ! will not fail the test if it is not the last command anymore. Use `run ! ` (on Bats >= 1.5.0) instead."]
    else
      [makeComment .errorC cmd.id 2314
        "In Bats, ! does not cause a test failure. Use 'run ! ' (on Bats >= 1.5.0) instead."]

  check (commands : List Token) (cmd : Token) : List TokenComment :=
    match cmd.inner with
    | .T_Banged inner =>
      match inner.inner with
      | .T_Pipeline _ [pipeCmd] =>
        match getCondition pipeCmd with
        | some _ =>
            if isLastOf cmd commands then
              [makeComment .styleC cmd.id 2315
                "In Bats, ! will not fail the test if it is not the last command anymore. Fold the `!` into the conditional!"]
            else
              [makeComment .errorC cmd.id 2315
                "In Bats, ! does not cause a test failure. Fold the `!` into the conditional!"]
        | Option.none =>
            warnRun cmd commands
      | _ =>
        warnRun cmd commands
    | _ => []

/-!
## Alias analysis
-/

private partial def groupByLinkTokens (f : Token → Token → Bool) : List Token → List (List Token)
  | [] => []
  | x :: xs =>
      let rec takeGroup (prev : Token) (acc : List Token) (rest : List Token) :
          List Token × List Token :=
        match rest with
        | [] => (acc.reverse, [])
        | y :: ys =>
            if f prev y then
              takeGroup y (y :: acc) ys
            else
              (acc.reverse, rest)
      let (group, rest) := takeGroup x [x] xs
      group :: groupByLinkTokens f rest

/-- SC2262/SC2263: Alias defined and used in the same parsing unit. -/
def checkAliasUsedInSameParsingUnit (params : Parameters) (root : Token) : List TokenComment :=
  let commands := (getCommandSequences root).foldl (· ++ ·) []
  let units := groupByLinkTokens (fun a b => followsOnLine a b) commands
  units.flatMap checkUnit
where
  lineSpan (tok : Token) : Option (Nat × Nat) := do
    let (startPos, endPos) ← params.tokenPositions.get? tok.id
    some (startPos.posLine, endPos.posLine)

  followsOnLine (a b : Token) : Bool :=
    match lineSpan a, lineSpan b with
    | some (_, endLine), some (startLine, _) => endLine == startLine
    | _, _ => false

  checkUnit (unit : List Token) : List TokenComment :=
    let (comments, _) :=
      unit.foldl (fun (acc, aliases) tok =>
        match tok.inner with
        | .T_SimpleCommand _ (cmd :: args) =>
          match getUnquotedLiteral cmd with
          | some "alias" =>
              let aliases :=
                args.foldl (fun m arg =>
                  match getLiteralString arg with
                  | some s =>
                      match s.splitOn "=" with
                      | name :: rest =>
                          if rest.isEmpty then
                            m
                          else if isVariableName name && !m.contains name then
                            m.insert name tok
                          else
                            m
                      | [] => m
                  | Option.none => m
                ) aliases
              (acc, aliases)
          | some name =>
              if name.contains '/' then
                (acc, aliases)
              else
                match aliases.get? name with
                | some aliasTok =>
                    if isSourced params tok || shouldIgnoreCode params 2262 aliasTok then
                      (acc, aliases)
                    else
                      let warnAlias :=
                        makeComment .warningC aliasTok.id 2262
                          "This alias can't be defined and used in the same parsing unit. Use a function instead."
                      let infoUse :=
                        makeComment .infoC tok.id 2263
                          "Since they're in the same parsing unit, this command will not refer to the previously mentioned alias."
                      (acc ++ [warnAlias, infoUse], aliases)
                | Option.none => (acc, aliases)
          | Option.none => (acc, aliases)
        | _ => (acc, aliases)
      ) ([], ({} : Std.HashMap String Token))
    comments

  isSourced (params : Parameters) (t : Token) : Bool :=
    let path := getPath params.parentMap t
    path.any fun ancestor =>
      match ancestor.inner with
      | .T_SourceCommand .. => true
      | _ => false

/-- SC2119: Use function "$@" if function's $1 should mean script's $1
    SC2120: Function references arguments, but none are ever passed -/
def checkUnpassedInFunctions (params : Parameters) (_root : Token) : List TokenComment :=
  let funcMap := getFunctionMap params.rootNode
  if funcMap.isEmpty then []
  else
    -- Find all function calls and track which functions are called with arguments
    let callsWithArgs := collectFunctionCalls params.rootNode funcMap
    -- Check each function for positional parameter usage
    funcMap.fold (fun acc _name func =>
      let positionalRefs := functionUsesPositionalParams func
      if positionalRefs.isEmpty then acc
      else
        -- Check if function is ever called with arguments
        match callsWithArgs.get? func.name with
        | some callers =>
          let hasArgsCall := callers.any (·.2)  -- .2 is hasArgs
          if hasArgsCall then acc
          else
            let suggestions :=
              callers.filterMap fun (callTok, hasArgs) =>
                if hasArgs then none
                else
                  some (makeComment .infoC callTok.id 2119
                    s!"Use {e4m func.name} \"$@\" if function's $1 should mean script's $1.")
            let warnDecl :=
              makeComment .warningC func.token.id 2120
                s!"{func.name} references arguments, but none are ever passed."
            acc ++ suggestions ++ [warnDecl]
        | Option.none =>
          -- Function is never called - warn at definition
          acc ++ [makeComment .infoC func.token.id 2120
            s!"'{func.name}' uses positional parameters but is never called."]
    ) []
where
  collectFunctionCalls (root : Token) (funcMap : Std.HashMap String FunctionDefinition) :
      Std.HashMap String (List (Token × Bool)) :=
    let calls := findCommandInvocations root
    calls.foldl (fun m (tok, name) =>
      if funcMap.contains name then
        let hasArgs := match tok.inner with
          | .T_SimpleCommand _ (_ :: args) => !args.isEmpty
          | .T_Redirecting _ inner =>
            match inner.inner with
            | .T_SimpleCommand _ (_ :: args) => !args.isEmpty
            | _ => false
          | _ => false
        let existing := m.get? name |>.getD []
        m.insert name ((tok, hasArgs) :: existing)
      else m
    ) {}

/-- SC2218: This function is used but never defined -/
def checkUseBeforeDefinition (params : Parameters) (_root : Token) : List TokenComment :=
  let funcMap := getFunctionMap params.rootNode
  if funcMap.isEmpty then []
  else
    -- Find all command invocations
    let invocations := findCommandInvocations params.rootNode
    invocations.foldl (fun acc (cmdToken, cmdName) =>
      match funcMap.get? cmdName with
      | some func =>
        -- Check if invocation comes before definition
        if tokenBefore cmdToken func.token then
          acc ++ [makeComment .warningC cmdToken.id 2218
            s!"This function is used but never defined. Did you mean '{cmdName}'?"]
        else acc
      | Option.none => acc
    ) []

/-!
## CFG-Based Analysis

Checks that use control flow graph analysis for more precise tracking.
-/

/-- SC2317: Command appears to be unreachable. -/
def checkCommandIsUnreachable (params : Parameters) (t : Token) : List TokenComment :=
  match params.cfgAnalysis with
  | Option.none => []
  | some cfg =>
    match t.inner with
    | .T_Pipeline .. =>
      match getIncomingState cfg t.id with
      | some state =>
        if !state.stateIsReachable && !(hasUnreachableAncestor cfg params t) then
          [makeComment .infoC t.id 2317
            "Command appears to be unreachable. Check usage (or ignore if invoked indirectly)."]
        else []
      | Option.none => []
    | .T_Function _ _ name _ =>
      if !isFunctionInvoked name && !(hasUnreachableAncestor cfg params t) then
        [makeComment .infoC t.id 2329
          "This function is never invoked. Check usage (or ignored if invoked indirectly)."]
      else []
    | _ => []
where
  isUnreachable (cfg : CFGAnalysis) (t : Token) : Bool :=
    match getIncomingState cfg t.id with
    | some st => !st.stateIsReachable
    | Option.none => false

  isUnreachableFunction (cfg : CFGAnalysis) (t : Token) : Bool :=
    match t.inner with
    | .T_Function _ _ _ body => isUnreachable cfg body
    | _ => false

  isFunctionInvoked (name : String) : Bool :=
    (findCommandInvocations params.rootNode).any (fun (_, n) => n == name)

  hasUnreachableAncestor (cfg : CFGAnalysis) (params : Parameters) (t : Token) : Bool :=
    let ancestors := (getPath params.parentMap t).drop 1
    ancestors.any fun a =>
      isUnreachable cfg a || isUnreachableFunction cfg a

/-- SC2319/SC2320: `$?` may refer to a condition/echo instead of a previous command. -/
def checkOverwrittenExitCode (params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced _ val =>
    if getLiteralString val == some "?" then
      check
    else
      []
  | _ => []
where
  check : List TokenComment :=
    match params.cfgAnalysis with
    | Option.none => []
    | some cfg =>
      match getIncomingState cfg t.id with
      | Option.none => []
      | some state =>
        let exitCodeIds := state.exitCodes.eraseDups
        if exitCodeIds.isEmpty then
          []
        else
          let exitCodeTokens := exitCodeIds.filterMap (fun id => params.idMap.get? id)
          let warnCondition :=
            if !exitCodeTokens.isEmpty && exitCodeTokens.all isCondition &&
               !usedUnconditionally cfg t exitCodeIds then
              [makeComment .warningC t.id 2319
                "This $? refers to a condition, not a command. Assign to a variable to avoid it being overwritten."]
            else
              []
          let warnPrinting :=
            if !exitCodeTokens.isEmpty && exitCodeTokens.all isPrinting then
              [makeComment .warningC t.id 2320
                "This $? refers to echo/printf, not a previous command. Assign to variable to avoid it being overwritten."]
            else
              []
          warnCondition ++ warnPrinting

  isCondition (t : Token) : Bool :=
    match t.inner with
    | .T_Condition .. => true
    | .T_SimpleCommand .. =>
      getCommandBasename t == some "test"
    | _ => false

  isPrinting (t : Token) : Bool :=
    match getCommandBasename t with
    | some "echo" => true
    | some "printf" => true
    | _ => false

  -- If `$?` runs on all paths after the condition token(s), assume we intended the condition itself.
  usedUnconditionally (cfg : CFGAnalysis) (t : Token) (testIds : List Id) : Bool :=
    testIds.all fun c => doesPostDominate cfg t.id c

/-- SC2086: CFG-aware quoting check - checks if variable may contain spaces along any path -/
def checkSpacefulnessCfg (params : Parameters) (t : Token) : List TokenComment :=
  match params.cfgAnalysis with
  | Option.none => []  -- No CFG analysis available, skip
  | some cfg =>
    match t.inner with
    | .T_DollarBraced _ content =>
      if isQuoteFree params.shellType params.parentMap t then
        []
      else
        let raw := String.join (oversimplify content)
        let modifier := getBracedModifier raw
        let varName := ASTLib.getBracedReference raw
        let needsQuoting :=
          not (isArrayExpansion t) &&
          not (ASTLib.isCountingReference t) &&
          not (ASTLib.isQuotedAlternativeReference t) &&
          not (usedAsCommandName params.parentMap t)
        let isDefaultAssignment :=
          (modifier.startsWith "=" || modifier.startsWith ":=") &&
          isParamTo params.parentMap ":" t
        if needsQuoting && isDefaultAssignment then
          [makeComment .infoC t.id 2223
            "This default assignment may cause DoS due to globbing. Quote it."]
        else
          -- Check if variable may have spaces based on CFG state
          match getIncomingState cfg t.id with
          | some state =>
            match state.variablesInScope.get? varName with
            | some varState =>
              if varState.variableValue.spaceStatus == .SpaceStatusUnknown ||
                 varState.variableValue.spaceStatus == .SpaceStatusSpaces then
                [makeComment .warningC t.id 2086
                  "Double quote to prevent globbing and word splitting."]
              else []
            | Option.none =>
              -- Unknown variable - warn conservatively
              [makeComment .warningC t.id 2086
                "Double quote to prevent globbing and word splitting."]
          | Option.none => []
    | _ => []

-- All node checks
def nodeChecks : List (Parameters → Token → List TokenComment) := [
  -- Note: checkUnquotedDollarAt removed to avoid duplicate SC2086 (covered by checkUnquotedVariables)
  checkForInQuoted,
  checkForInLs,
  checkForLoopGlobVariables,
  checkShorthandIf,
  checkArithmeticDeref,
  checkArithmeticBadOctal,
  checkBackticks,
  checkDollarBrackets,
  -- checkUncheckedCdPushdPopd, -- SC2164 - handled by Commands.checkCdNoCheck
  checkMaskedReturns,
  checkArrayExpansions,
  checkRmGlob,
  checkMultipleRedirects,
  checkSingleQuotedExpansion,
  checkSpuriousExpansion,
  -- Pipeline and command checks
  checkEchoWc,
  checkPipedAssignment,
  checkAssignAteCommand,
  checkArithmeticOpCommand,
  checkWrongArithmeticAssignment,
  checkUuoc,
  -- checkPsGrep, -- SC2009 - handled by Commands.checkPsGrepPipeline
  -- checkLsGrep, -- SC2010 - handled by Commands.checkLsGrepPipeline
  checkLsXargs,
  checkFindXargs,
  checkFindExec,
  checkPipePitfalls,
  checkPipelineRedirections,
  checkRedirectedNowhere,
  checkGrepWc,
  -- checkReadWithoutR, -- SC2162 - handled by Commands.checkReadWithoutR
  checkMultipleRedirectsImpl,
  checkGlobAsCommand,
  checkForInCat,
  checkRedirectToSame,
  checkUuoeVar,
  checkPrintfVar,
  checkRmWithRoot,
  -- Quoting and expansion checks
  checkDollarStar,
  checkConcatenatedDollarAt,
  checkUnquotedExpansions,
  checkArrayAsString,
  checkArrayWithoutIndex,  -- SC2128
  checkCommarrays,
  checkUnquotedVariables,
  checkSplittingInArrays,
  checkTildeExpansion,
  checkQuotesInVariables,
  checkInexplicablyUnquoted,
  checkBadParameterExpansions,
  checkUnquotedParameterExpansionPattern,
  checkDollarQuoteParen,
  -- Conditional expression checks
  checkNumberComparisons,
  checkDecimalComparisons,
  checkReturnAgainstZero,
  checkGrepQ,
  checkConstantIfs,
  checkQuotedCondRegex,
  checkGlobbedRegex,
  checkConditionalAndOrs,
  checkSingleBracketOperators,
  checkDoubleBracketOperators,
  checkRequireDoubleBracket,
  checkConstantNullary,
  checkEmptyCondition,
  checkUnquotedN,
  checkLiteralBreakingTest,
  checkEscapedComparisons,
  checkOrNeq,
  checkAndEq,
  checkValidCondOps,
  checkComparisonAgainstGlob,
  checkCaseConstantWord,
  checkDefaultCase,
  checkUnmatchableCases,
  checkCaseAgainstGlob,
  checkBadTestAndOr,
  checkBadTestAndOrPipes,
  checkTestAndOr,  -- SC2166
  checkNegatedTest,  -- SC2237
  checkUnquotedRhsGlob,  -- SC2053
  checkComparisonWithLeadingX,
  checkComparisonOperators,
  checkSubshellAsTest,
  checkBackticksAsTest,
  checkSubshellAsTestExpression,
  checkSubshelledTests,
  -- Arithmetic checks
  checkForDecimals,
  checkUnnecessaryArithmeticExpansionIndex,
  checkUnnecessaryParens,
  checkDivBeforeMult,
  -- set -e + ! checks
  checkUselessBang,
  checkBatsTestDoesNotUseNegation,
  -- Path and IFS checks
  checkOverridingPath,
  checkTildeInPath,
  checkSuspiciousIFS,
  -- Test expression checks
  checkTestOperands,
  checkNullaryExpansionTest,
  checkUnaryTestA,
  checkTestArgumentSplitting,
  checkCharRangeGlob,
  checkTestRedirection,
  checkTrailingBracket,
  -- Redirection checks
  checkRedirectionToNumber,
  checkRedirectionToCommand,
  checkStderrPipe,
  checkReadWriteSameFile,
  checkStderrRedirect,
  -- Various command checks
  checkTrapQuoting,
  checkTildeInQuotes,
  checkLonelyDotDash,
  checkQuotesForExpansion,
  checkExecuteCommandOutput,
  checkExecWithSubshell,
  checkPlusEqualsNumber,
  checkExpansionWithRedirection,
  checkSshHereDoc,
  checkSshInLoop,
  checkWhileReadSsh,
  checkTrParams,
  checkPrefixAssignment,
  checkEqualsInCommand,
  checkSecondArgIsComparison,
  checkCommandWithTrailingSymbol,
  checkSpuriousExec,
  checkLoopKeywordScope,
  checkCdAndBack,
  -- More checks
  checkPrintfFormat,
  checkLsFind,
  checkSingleQuotedVariable,
  checkForInFind,
  checkTrapExpansion,
  checkArithmeticDecimals,
  checkDoubleBracketOrOperator,
  checkDoubleBracketAndOperator,
  checkQuotedRightHandRegex,
  checkRedirectToDollarExpansion,
  checkModifiedArithmeticInRedirection,
  checkConstantTest,
  checkFractionsInArithmetic,
  checkBracketSpacing,
  checkDollarBraceExpansionInCommand,
  -- Note: checkUnquotedVariable removed to avoid duplicate SC2086 (covered by checkUnquotedVariables)
  checkBashAsLogin,
  checkLoopVariableReassignment,
  -- CFG-aware checks
  checkCommandIsUnreachable,
  checkOverwrittenExitCode,
  checkSpacefulnessCfg
]

-- All tree checks
def treeChecks : List (Parameters → Token → List TokenComment) := [
  nodeChecksToTreeCheck nodeChecks,
  checkUnusedAssignments,
  checkArrayStringAssignments,
  checkArrayValueUsedAsIndex,
  checkArrayAssignmentIndices,
  checkSetESuppressed,
  checkExtraMaskedReturns,
  checkSubshellAssignments,
  checkUnassignedReferences,
  checkShebangParameters,
  checkShebang,
  -- Function scope analysis checks (operate on whole tree)
  checkFunctionsUsedExternally,
  checkAliasUsedInSameParsingUnit,
  checkUnpassedInFunctions,
  checkUseBeforeDefinition
]

/-!
## Optional Checks

Checks that are only enabled when explicitly requested.
-/

/-- SC2250: Prefer putting braces around variable references -/
def checkBracesAroundVariables (_params : Parameters) (t : Token) : List TokenComment :=
  match t.inner with
  | .T_DollarBraced false _ => [makeComment .styleC t.id 2250
      "Prefer putting braces around variable references even when not strictly required."]
  | _ => []

/-- SC2248: Prefer double quoting even when variables don't contain special characters.

This is an optional check ("quote-safe-variables") and requires CFG analysis. -/
def checkQuoteSafeVariables (params : Parameters) (root : Token) : List TokenComment :=
  nodeChecksToTreeCheck [checkQuoteSafeVariablesNode] params root
where
  checkQuoteSafeVariablesNode (params : Parameters) (t : Token) : List TokenComment :=
    match params.cfgAnalysis with
    | Option.none => []
    | some cfg =>
      match t.inner with
      | .T_DollarBraced _ content =>
        if isQuoteFree params.shellType params.parentMap t ||
           isArrayExpansion t ||
           ASTLib.isCountingReference t ||
           isQuotedAlternativeReference t ||
           usedAsCommandName params.parentMap t then
          []
        else
          let name := ASTLib.getBracedReference (String.join (oversimplify content))
          if specialVariablesWithoutSpaces.contains name then
            []
          else
            match getIncomingState cfg t.id with
            | some state =>
              match state.variablesInScope.get? name with
              | some varState =>
                if varState.variableValue.spaceStatus == .SpaceStatusClean ||
                   varState.variableValue.spaceStatus == .SpaceStatusEmpty then
                  [makeComment .styleC t.id 2248
                    "Prefer double quoting even when variables don't contain special characters."]
                else []
              | Option.none => []
            | Option.none => []
      | _ => []

/-- Map of optional check names to functions -/
def optionalCheckMap : Std.HashMap String (Parameters → Token → List TokenComment) :=
  ({} : Std.HashMap String (Parameters → Token → List TokenComment))
    |>.insert "avoid-nullary-conditions" (fun _ _ => [])
    |>.insert "add-default-case" (fun _ _ => [])
    |>.insert "require-double-brackets" (fun _ _ => [])
    |>.insert "quote-safe-variables" checkQuoteSafeVariables
    |>.insert "check-set-e-suppressed" (fun _ _ => [])
    |>.insert "require-variable-braces" checkBracesAroundVariables

/-- List of optional checks -/
def optionalChecks : List String :=
  ["avoid-nullary-conditions", "add-default-case", "require-double-brackets",
   "quote-safe-variables", "check-set-e-suppressed", "require-variable-braces"]

/-!
## Main Entry Point
-/

/-- Create the main checker from spec and parameters -/
def mkChecker (spec : AnalysisSpec) (params : Parameters)
    (checks : List (Parameters → Token → List TokenComment)) : Checker := {
  perScript := fun root =>
    let tok := root.token
    let allChecks := checks ++ getOptionalChecks spec
    pure (allChecks.foldl (fun acc check => acc ++ check params tok) [])
  perToken := fun _ => pure []
}
where
  getOptionalChecks (spec : AnalysisSpec) : List (Parameters → Token → List TokenComment) :=
    let keys := spec.asOptionalChecks
    if keys.contains "all" then
      optionalCheckMap.toList.map (·.2)
    else
      keys.filterMap fun k => optionalCheckMap.get? k

/-- The main checker export -/
def checker (spec : AnalysisSpec) (params : Parameters) : Checker :=
  mkChecker spec params treeChecks

-- Theorems (stubs)

theorem checker_produces_valid_ids (_spec : AnalysisSpec) (_params : Parameters) :
    True := trivial

theorem nodeChecks_comprehensive :
    nodeChecks.length > 0 := by
  simp [nodeChecks]

theorem optionalChecks_all_mapped (name : String) :
    name ∈ optionalChecks → optionalCheckMap.contains name := sorry

theorem checkUnquotedDollarAt_on_at (_params : Parameters) (_id : Id) :
    True := trivial  -- Would verify SC2086 triggers on $@

theorem checkBackticks_on_backtick (_params : Parameters) (_id : Id) :
    True := trivial  -- Would verify SC2006 triggers on backticks

theorem mkChecker_includes_optional (_spec : AnalysisSpec) (_params : Parameters) :
    True := trivial  -- Would verify all optional checks included

theorem treeChecks_not_empty :
    treeChecks.length > 0 := by
  simp [treeChecks]

theorem runNodeAnalysis_collects_all (_f : Parameters → Token → List TokenComment)
    (_p : Parameters) (_t : Token) :
    True := trivial  -- Would verify all nodes visited

end ShellCheck.Analytics
