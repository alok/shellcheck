/-
  Test condition parser for ShellCheck
  Handles [[ expr ]] (bash) and [ expr ] (POSIX) test conditions
-/

import ShellCheck.AST

namespace ShellCheck.Parser.Condition

open ShellCheck.AST

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

end ShellCheck.Parser.Condition
