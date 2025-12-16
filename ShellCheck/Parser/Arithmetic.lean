/-
  Arithmetic expression parser for ShellCheck
  Implements precedence climbing for shell arithmetic $(( )) and (( ))
-/

import ShellCheck.AST

namespace ShellCheck.Parser.Arithmetic

open ShellCheck.AST

/-- Operator associativity -/
inductive Assoc where
  | left
  | right
  deriving Repr, BEq

/-- Binary operator info: precedence and associativity -/
structure BinOpInfo where
  prec : Nat
  assoc : Assoc
  deriving Repr

/-- Operator precedence table (lower number = lower precedence) -/
def getBinOpInfo (op : String) : Option BinOpInfo :=
  match op with
  -- Assignment operators (right associative)
  | "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "<<=" | ">>=" | "&=" | "^=" | "|=" =>
      some ⟨1, .right⟩
  -- Ternary handled separately (prec 2)
  -- Logical or
  | "||" => some ⟨3, .left⟩
  -- Logical and
  | "&&" => some ⟨4, .left⟩
  -- Bitwise or
  | "|" => some ⟨5, .left⟩
  -- Bitwise xor
  | "^" => some ⟨6, .left⟩
  -- Bitwise and
  | "&" => some ⟨7, .left⟩
  -- Equality
  | "==" | "!=" => some ⟨8, .left⟩
  -- Relational
  | "<" | "<=" | ">" | ">=" => some ⟨9, .left⟩
  -- Shift
  | "<<" | ">>" => some ⟨10, .left⟩
  -- Additive
  | "+" | "-" => some ⟨11, .left⟩
  -- Multiplicative
  | "*" | "/" | "%" => some ⟨12, .left⟩
  -- Exponentiation (bash-specific, right associative)
  | "**" => some ⟨13, .right⟩
  | _ => none

/-- Unary operators -/
def isUnaryOp (op : String) : Bool :=
  op ∈ ["!", "~", "+", "-", "++", "--"]

/-- Assignment operators -/
def isAssignmentOp (op : String) : Bool :=
  op ∈ ["=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "&=", "^=", "|="]

/-- Parser state for arithmetic expressions -/
structure ArithState where
  input : String
  pos : Nat
  deriving Repr, Inhabited

/-- Result type for arithmetic parser -/
inductive ArithResult (α : Type) where
  | ok : α → ArithState → ArithResult α
  | error : String → ArithState → ArithResult α
  deriving Repr

/-- Arithmetic parser monad -/
def ArithParser (α : Type) := ArithState → ArithResult α

instance : Monad ArithParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative ArithParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Check if at end -/
def isEof : ArithParser Bool := fun s =>
  .ok (s.pos >= s.input.length) s

/-- Peek at current character -/
def peek : ArithParser (Option Char) := fun s =>
  if s.pos >= s.input.length then .ok none s
  else .ok (some ((String.Pos.Raw.mk s.pos).get s.input)) s

/-- Consume a character satisfying predicate -/
def satisfy (p : Char → Bool) : ArithParser Char := fun s =>
  if s.pos >= s.input.length then .error "unexpected end" s
  else
    let c := (String.Pos.Raw.mk s.pos).get s.input
    if p c then .ok c { s with pos := s.pos + 1 }
    else .error s!"unexpected '{c}'" s

/-- Consume a specific character -/
def char (c : Char) : ArithParser Char := satisfy (· == c)

/-- Consume a specific string -/
def matchStr (str : String) : ArithParser String := fun s =>
  if s.input.drop s.pos |>.startsWith str then
    .ok str { s with pos := s.pos + str.length }
  else
    .error s!"expected \"{str}\"" s

/-- Try parser, backtrack on failure -/
def attempt (p : ArithParser α) : ArithParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Optional parser -/
def optionalP (p : ArithParser α) : ArithParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Take while predicate holds -/
partial def takeWhile (p : Char → Bool) : ArithParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) : (Nat × List Char) :=
    if pos >= s.input.length then (pos, acc)
    else
      let c := (String.Pos.Raw.mk pos).get s.input
      if p c then go (pos + 1) (c :: acc)
      else (pos, acc)
  let (newPos, chars) := go s.pos []
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Skip whitespace -/
def skipWhitespace : ArithParser Unit := do
  let _ ← takeWhile (fun c => c == ' ' || c == '\t' || c == '\n')
  pure ()

/-- Create a token with default ID -/
def mkTok (inner : InnerToken Token) : Token := ⟨⟨0⟩, inner⟩

/-- Parse a number (including base prefix like 16#ff) -/
partial def parseNumber : ArithParser Token := do
  skipWhitespace
  let numStr ← takeWhile (fun c => c.isDigit || c == '#' || c.isAlpha)
  if numStr.isEmpty then failure
  else
    pure (mkTok (InnerToken.T_Literal numStr))

/-- Parse a variable name -/
def parseVarName : ArithParser String := do
  let firstChar ← satisfy (fun c => c.isAlpha || c == '_')
  let rest ← takeWhile (fun c => c.isAlphanum || c == '_')
  pure (String.ofList [firstChar] ++ rest)

/-- Parse a unary operator -/
def parseUnaryOp : ArithParser String := do
  skipWhitespace
  -- Try two-char ops first
  attempt (matchStr "++") <|> attempt (matchStr "--") <|>
  attempt (do let c ← satisfy (fun c => c == '!' || c == '~' || c == '+' || c == '-'); pure (String.ofList [c]))

/-- Try to parse a binary operator -/
partial def parseBinOp : ArithParser String := do
  skipWhitespace
  -- Try three-char ops first
  attempt (matchStr "<<=") <|> attempt (matchStr ">>=") <|>
  -- Two-char ops
  attempt (matchStr "**") <|> attempt (matchStr "||") <|> attempt (matchStr "&&") <|>
  attempt (matchStr "==") <|> attempt (matchStr "!=") <|>
  attempt (matchStr "<=") <|> attempt (matchStr ">=") <|>
  attempt (matchStr "<<") <|> attempt (matchStr ">>") <|>
  attempt (matchStr "+=") <|> attempt (matchStr "-=") <|>
  attempt (matchStr "*=") <|> attempt (matchStr "/=") <|>
  attempt (matchStr "%=") <|> attempt (matchStr "&=") <|>
  attempt (matchStr "^=") <|> attempt (matchStr "|=") <|>
  -- Single-char ops
  attempt (do let c ← satisfy (fun c => c ∈ ['+', '-', '*', '/', '%', '<', '>', '&', '|', '^', '=']); pure (String.ofList [c]))

/-- Get current position -/
def getPos : ArithParser Nat := fun s => .ok s.pos s

/-- Set position -/
def setPos (pos : Nat) : ArithParser Unit := fun s => .ok () { s with pos }

-- Mutually recursive parsers
mutual

/-- Parse array index [expr] -/
partial def parseArrayIndex : ArithParser Token := do
  let _ ← char '['
  skipWhitespace
  let idx ← parseExpr 0
  skipWhitespace
  let _ ← char ']'
  pure idx

/-- Parse a variable (possibly with array indices) -/
partial def parseVariable : ArithParser Token := do
  skipWhitespace
  let _hasDollar ← optionalP (char '$')
  let name ← parseVarName
  -- Check for array indices
  let mut indices : List Token := []
  repeat do
    skipWhitespace
    match ← optionalP (attempt parseArrayIndex) with
    | some idx => indices := indices ++ [idx]
    | none => break
  pure (mkTok (InnerToken.TA_Variable name indices))

/-- Parse primary expression (atoms and unary) -/
partial def parsePrimary : ArithParser Token := do
  skipWhitespace
  match ← peek with
  | none => failure
  | some '(' =>
      let _ ← char '('
      skipWhitespace
      let inner ← parseExpr 0
      skipWhitespace
      let _ ← char ')'
      pure (mkTok (InnerToken.TA_Parenthesis inner))
  | some c =>
      if c.isDigit then parseNumber
      else if c.isAlpha || c == '_' || c == '$' then
        let var ← parseVariable
        -- Check for postfix ++ or --
        skipWhitespace
        match ← optionalP (attempt (matchStr "++")) with
        | some _ => pure (mkTok (InnerToken.TA_Unary "++post" var))
        | none =>
            match ← optionalP (attempt (matchStr "--")) with
            | some _ => pure (mkTok (InnerToken.TA_Unary "--post" var))
            | none => pure var
      else if c == '!' || c == '~' || c == '+' || c == '-' then
        let op ← parseUnaryOp
        let operand ← parsePrimary
        pure (mkTok (InnerToken.TA_Unary op operand))
      else failure

/-- Parse expression with minimum precedence -/
partial def parseExpr (minPrec : Nat) : ArithParser Token := do
  skipWhitespace
  let lhs ← parsePrimary
  parseBinOpRhs minPrec lhs

/-- Parse binary operator right-hand side (precedence climbing) -/
partial def parseBinOpRhs (minPrec : Nat) (lhs : Token) : ArithParser Token := do
  skipWhitespace
  -- Check for ternary ?
  let lhs' ← if minPrec <= 2 then
    match ← optionalP (attempt (char '?')) with
    | some _ =>
        skipWhitespace
        let thenExpr ← parseExpr 0
        skipWhitespace
        let _ ← char ':'
        skipWhitespace
        let elseExpr ← parseExpr 2  -- Right associative
        let result : Token := mkTok (InnerToken.TA_Trinary lhs thenExpr elseExpr)
        parseBinOpRhs minPrec result
    | none => pure lhs
  else pure lhs
  -- Save position before trying operator
  let savedPos ← getPos
  -- Try to parse binary operator
  match ← optionalP parseBinOp with
  | none => pure lhs'
  | some op =>
      match getBinOpInfo op with
      | none =>
          -- Not a valid binary op, restore position
          setPos savedPos
          pure lhs'
      | some info =>
          if info.prec < minPrec then
            -- Precedence too low, restore position and return
            setPos savedPos
            pure lhs'
          else
            skipWhitespace
            let nextMinPrec := if info.assoc == .left then info.prec + 1 else info.prec
            let rhs ← parseExpr nextMinPrec
            let result : Token :=
              if isAssignmentOp op then mkTok (InnerToken.TA_Assignment op lhs' rhs)
              else mkTok (InnerToken.TA_Binary op lhs' rhs)
            parseBinOpRhs minPrec result

/-- Parse comma-separated expressions (for sequences) -/
partial def parseSequence : ArithParser Token := do
  let first ← parseExpr 0
  let mut exprs : List Token := [first]
  repeat do
    skipWhitespace
    match ← optionalP (char ',') with
    | some _ =>
        skipWhitespace
        let next ← parseExpr 0
        exprs := exprs ++ [next]
    | none => break
  if exprs.length == 1 then pure first
  else pure (mkTok (InnerToken.TA_Sequence exprs))

end

/-- Main entry point: parse arithmetic expression string -/
def parse (input : String) : Option Token :=
  let state : ArithState := { input := input, pos := 0 }
  match parseSequence state with
  | .ok result s =>
      -- Skip trailing whitespace and check we consumed everything
      let remaining := s.input.drop s.pos
      if remaining.all (fun c => c == ' ' || c == '\t' || c == '\n') then some result
      else none
  | .error _ _ => none

end ShellCheck.Parser.Arithmetic
