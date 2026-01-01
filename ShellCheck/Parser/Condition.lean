/-
  Test condition parser for ShellCheck
  Handles [[ expr ]] (bash) and [ expr ] (POSIX) test conditions
-/

import ShellCheck.AST
import ShellCheck.Parser.Parsec

namespace ShellCheck.Parser.Condition

open ShellCheck.AST
open ShellCheck.Parser.Parsec

/-- Unary file test operators -/
def fileTestOps : List String :=
  ["-e", "-f", "-d", "-L", "-h", "-S", "-p", "-b", "-c", "-r", "-w", "-x",
   "-u", "-g", "-k", "-O", "-G", "-t", "-s", "-N"]

/-- Unary string test operators -/
def stringTestOps : List String := ["-z", "-n"]

/-- All unary operators -/
def unaryOps : List String := fileTestOps ++ stringTestOps

/-- Binary comparison operators -/
def binaryCompareOps : List String :=
  ["-eq", "-ne", "-lt", "-le", "-gt", "-ge", "-nt", "-ot", "-ef"]

/-- Binary string operators -/
def binaryStringOps : List String :=
  ["=", "==", "!=", "<", ">", "=~"]

/-- All binary operators -/
def binaryOps : List String := binaryCompareOps ++ binaryStringOps

/-- Parser state for conditions -/
structure CondState where
  tokens : List String  -- Pre-tokenized words
  pos : Nat
  condType : ConditionType
  deriving Repr, Inhabited

/-- Result type -/
inductive CondResult (α : Type) where
  | ok : α → CondState → CondResult α
  | error : String → CondState → CondResult α
  deriving Repr

/-- Condition parser monad -/
def CondParser (α : Type) := CondState → CondResult α

instance : Monad CondParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative CondParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Check if at end -/
def isEnd : CondParser Bool := fun s =>
  .ok (s.pos >= s.tokens.length) s

/-- Get element at position safely -/
def listGetAt (l : List α) (n : Nat) : Option α :=
  match l, n with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGetAt xs n

/-- Get token at position safely -/
def getToken (tokens : List String) (pos : Nat) : Option String :=
  listGetAt tokens pos

/-- Peek current token -/
def peek : CondParser (Option String) := fun s =>
  .ok (getToken s.tokens s.pos) s

/-- Consume current token -/
def consume : CondParser String := fun s =>
  match getToken s.tokens s.pos with
  | none => .error "unexpected end" s
  | some tok => .ok tok { s with pos := s.pos + 1 }

/-- Consume specific token -/
def expect (tok : String) : CondParser Unit := fun s =>
  match getToken s.tokens s.pos with
  | none => .error s!"expected '{tok}'" s
  | some actual =>
      if actual == tok then .ok () { s with pos := s.pos + 1 }
      else .error s!"expected '{tok}', got '{actual}'" s

/-- Try parser, backtrack on failure -/
def attempt (p : CondParser α) : CondParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Optional parser -/
def optionalP (p : CondParser α) : CondParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Get condition type -/
def getCondType : CondParser ConditionType := fun s => .ok s.condType s

/-- Create token with default ID -/
def mkTok (inner : InnerToken Token) : Token := ⟨⟨0⟩, inner⟩

-- Forward declarations for mutual recursion
mutual

/-- Parse a primary condition (atom, unary, or grouped) -/
partial def parsePrimary : CondParser Token := do
  match ← peek with
  | none =>
      let ct ← getCondType
      pure (mkTok (InnerToken.TC_Empty ct))
  | some "!" =>
      let _ ← consume
      let inner ← parsePrimary
      let ct ← getCondType
      pure (mkTok (InnerToken.TC_Unary ct "!" inner))
  | some "(" =>
      let _ ← consume
      let inner ← parseOr
      expect ")"
      let ct ← getCondType
      pure (mkTok (InnerToken.TC_Group ct inner))
  | some op =>
      if unaryOps.contains op then
        let _ ← consume
        let arg ← consume
        let ct ← getCondType
        let argTok := mkTok (InnerToken.T_Literal arg)
        pure (mkTok (InnerToken.TC_Unary ct op argTok))
      else
        -- Check for binary operator: word OP word
        let left ← consume
        match ← peek with
        | none =>
            -- Just a word (nullary test for non-empty)
            let ct ← getCondType
            let leftTok := mkTok (InnerToken.T_Literal left)
            pure (mkTok (InnerToken.TC_Nullary ct leftTok))
        | some binOp =>
            if binaryOps.contains binOp then
              let _ ← consume
              let right ← consume
              let ct ← getCondType
              let leftTok := mkTok (InnerToken.T_Literal left)
              let rightTok := mkTok (InnerToken.T_Literal right)
              pure (mkTok (InnerToken.TC_Binary ct binOp leftTok rightTok))
            else
              -- Just the left word (nullary test)
              let ct ← getCondType
              let leftTok := mkTok (InnerToken.T_Literal left)
              pure (mkTok (InnerToken.TC_Nullary ct leftTok))

/-- Parse AND expressions -/
partial def parseAnd : CondParser Token := do
  let left ← parsePrimary
  parseAndCont left

partial def parseAndCont (left : Token) : CondParser Token := do
  match ← peek with
  | some "-a" | some "&&" =>
      let op ← consume
      let right ← parsePrimary
      let ct ← getCondType
      let combined := mkTok (InnerToken.TC_And ct op left right)
      parseAndCont combined
  | _ => pure left

/-- Parse OR expressions -/
partial def parseOr : CondParser Token := do
  let left ← parseAnd
  parseOrCont left

partial def parseOrCont (left : Token) : CondParser Token := do
  match ← peek with
  | some "-o" | some "||" =>
      let op ← consume
      let right ← parseAnd
      let ct ← getCondType
      let combined := mkTok (InnerToken.TC_Or ct op left right)
      parseOrCont combined
  | _ => pure left

end

/-- Tokenize condition string (simple word splitting) -/
def tokenize (s : String) : List String :=
  s.splitOn " " |>.filter (·.length > 0)

/-- Parse a condition expression from tokens -/
def parseCondition (tokens : List String) (ct : ConditionType) : Option Token :=
  let state : CondState := { tokens := tokens, pos := 0, condType := ct }
  match parseOr state with
  | .ok result s =>
      if s.pos >= s.tokens.length then
        some (mkTok (InnerToken.T_Condition ct result))
      else none  -- Didn't consume all tokens
  | .error _ _ => none

/-- Parse [[ expr ]] style condition -/
def parseDoubleBracket (content : String) : Option Token :=
  parseCondition (tokenize content) .doubleBracket

/-- Parse [ expr ] style condition -/
def parseSingleBracket (content : String) : Option Token :=
  parseCondition (tokenize content) .singleBracket

/-
  Token-based condition parsing (used by the full parser).

  This is a substantial upgrade over the older `tokenize`-by-space approach:
  the full shell parser already tokenizes/quotes/escapes words into `Token`s.
  Here we interpret a list of already-parsed word-ish tokens as a condition
  expression, producing `TC_*` nodes that preserve the original operands.
-/

namespace TokenParse

private def bareWordString? (t : Token) : Option String :=
  match t.inner with
  | .T_Literal s => some s
  | .T_NormalWord [p] =>
      match p.inner with
      | .T_Literal s => some s
      | _ => none
  | _ => none

private def spanOf (t : Token) : ShellParser (Nat × Nat × Nat × Nat) := do
  let st ← ShellCheck.Parser.Parsec.getState
  match st.positions.get? t.id with
  | some (startPos, endPos) =>
      pure (startPos.posLine, startPos.posColumn, endPos.posLine, endPos.posColumn)
  | none =>
      let (line, col) ← getPos
      pure (line, col, line, col)

private def mkSpan (inner : InnerToken Token) (first last : Token) : ShellParser Token := do
  let (startLine, startCol, _, _) ← spanOf first
  let (_, _, endLine, endCol) ← spanOf last
  let id ← freshId
  recordPosition id startLine startCol endLine endCol
  pure ⟨id, inner⟩

private def isAndOp (ct : ConditionType) (op : String) : Bool :=
  match ct with
  | .doubleBracket => op == "&&" || op == "-a"
  | .singleBracket => op == "-a"

private def isOrOp (ct : ConditionType) (op : String) : Bool :=
  match ct with
  | .doubleBracket => op == "||" || op == "-o"
  | .singleBracket => op == "-o"

mutual

  partial def parsePrimary (ct : ConditionType) (ts : List Token) : ShellParser (Token × List Token) := do
    match ts with
    | [] =>
        let empty ← mkToken (.TC_Empty ct)
        pure (empty, [])
    | t :: rest =>
        match bareWordString? t with
        | some "!" =>
            let (inner, rest') ← parsePrimary ct rest
            let node ← mkSpan (.TC_Unary ct "!" inner) t inner
            pure (node, rest')
        | some "(" =>
            let (inner, rest') ← parseOr ct rest
            match rest' with
            | closeTok :: rest'' =>
                match bareWordString? closeTok with
                | some ")" =>
                    let node ← mkSpan (.TC_Group ct inner) t closeTok
                    pure (node, rest'')
                | _ => failure
            | [] => failure
        | some op =>
            if unaryOps.contains op then
              match rest with
              | arg :: rest' =>
                  let node ← mkSpan (.TC_Unary ct op arg) t arg
                  pure (node, rest')
              | [] => failure
            else
              parseBinaryOrNullary ct t rest
        | none =>
            parseBinaryOrNullary ct t rest

  partial def parseBinaryOrNullary (ct : ConditionType) (lhs : Token) (ts : List Token) : ShellParser (Token × List Token) := do
    match ts with
    | opTok :: rhsTok :: rest =>
        match bareWordString? opTok with
        | some op =>
            if binaryOps.contains op then
              let node ← mkSpan (.TC_Binary ct op lhs rhsTok) lhs rhsTok
              pure (node, rest)
            else
              let node ← mkSpan (.TC_Nullary ct lhs) lhs lhs
              pure (node, ts)
        | none =>
            let node ← mkSpan (.TC_Nullary ct lhs) lhs lhs
            pure (node, ts)
    | _ =>
        let node ← mkSpan (.TC_Nullary ct lhs) lhs lhs
        pure (node, ts)

  partial def parseAnd (ct : ConditionType) (ts : List Token) : ShellParser (Token × List Token) := do
    let (left, rest) ← parsePrimary ct ts
    parseAndCont ct left rest

  partial def parseAndCont (ct : ConditionType) (left : Token) (ts : List Token) : ShellParser (Token × List Token) := do
    match ts with
    | opTok :: rest =>
        match bareWordString? opTok with
        | some op =>
            if isAndOp ct op then
              let (right, rest') ← parsePrimary ct rest
              let node ← mkSpan (.TC_And ct op left right) left right
              parseAndCont ct node rest'
            else
              pure (left, ts)
        | none => pure (left, ts)
    | [] => pure (left, [])

  partial def parseOr (ct : ConditionType) (ts : List Token) : ShellParser (Token × List Token) := do
    let (left, rest) ← parseAnd ct ts
    parseOrCont ct left rest

  partial def parseOrCont (ct : ConditionType) (left : Token) (ts : List Token) : ShellParser (Token × List Token) := do
    match ts with
    | opTok :: rest =>
        match bareWordString? opTok with
        | some op =>
            if isOrOp ct op then
              let (right, rest') ← parseAnd ct rest
              let node ← mkSpan (.TC_Or ct op left right) left right
              parseOrCont ct node rest'
            else
              pure (left, ts)
        | none => pure (left, ts)
    | [] => pure (left, [])

end

end TokenParse

/-- Parse a list of already-tokenized condition arguments into a `TC_*` tree. -/
partial def parseConditionTokensFull (ct : ConditionType) (tokens : List Token) : ShellParser Token := do
  let (expr, rest) := (← TokenParse.parseOr ct tokens)
  if rest.isEmpty then
    pure expr
  else
    failure

end ShellCheck.Parser.Condition
