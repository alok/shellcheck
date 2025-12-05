/-
  Parameter expansion parser for ShellCheck
  Handles ${var}, ${var:-default}, ${var%pattern}, etc.
-/

import ShellCheck.AST

namespace ShellCheck.Parser.Expansion

open ShellCheck.AST

/-- Types of parameter expansion operations -/
inductive ExpansionOp where
  | none          -- Just ${var}
  | useDefault    -- ${var:-default} or ${var-default}
  | assignDefault -- ${var:=default} or ${var=default}
  | useAlternate  -- ${var:+alt} or ${var+alt}
  | errorIfUnset  -- ${var:?error} or ${var?error}
  | removePrefix  -- ${var#pattern} or ${var##pattern}
  | removeSuffix  -- ${var%pattern} or ${var%%pattern}
  | replace       -- ${var/find/repl} or ${var//find/repl}
  | replacePrefix -- ${var/#find/repl}
  | replaceSuffix -- ${var/%find/repl}
  | substring     -- ${var:offset} or ${var:offset:length}
  | length        -- ${#var}
  | indirect      -- ${!var}
  | caseUpper     -- ${var^} or ${var^^}
  | caseLower     -- ${var,} or ${var,,}
  | transform     -- ${var@op}
  deriving Repr, BEq

/-- Parsed parameter expansion -/
structure ParsedExpansion where
  varName : String
  op : ExpansionOp
  isColonVariant : Bool  -- For :-, :=, :+, :? variants
  isDoubled : Bool       -- For ##, %%, //, ^^, ,,
  arg1 : Option String   -- pattern/default/offset
  arg2 : Option String   -- replacement/length
  deriving Repr

/-- Parser state -/
structure ExpState where
  input : String
  pos : Nat
  deriving Repr, Inhabited

/-- Result type -/
inductive ExpResult (α : Type) where
  | ok : α → ExpState → ExpResult α
  | error : String → ExpState → ExpResult α
  deriving Repr

/-- Expansion parser monad -/
def ExpParser (α : Type) := ExpState → ExpResult α

instance : Monad ExpParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative ExpParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Check if at end -/
def isEnd : ExpParser Bool := fun s =>
  .ok (s.pos >= s.input.length) s

/-- Peek at current character -/
def peek : ExpParser (Option Char) := fun s =>
  if s.pos >= s.input.length then .ok none s
  else .ok (some (s.input.get ⟨s.pos⟩)) s

/-- Consume current character -/
def anyChar : ExpParser Char := fun s =>
  if s.pos >= s.input.length then .error "unexpected end" s
  else .ok (s.input.get ⟨s.pos⟩) { s with pos := s.pos + 1 }

/-- Consume specific character -/
def char (c : Char) : ExpParser Char := fun s =>
  if s.pos >= s.input.length then .error s!"expected '{c}'" s
  else if s.input.get ⟨s.pos⟩ == c then .ok c { s with pos := s.pos + 1 }
  else .error s!"expected '{c}'" s

/-- Consume specific string -/
def matchStr (str : String) : ExpParser String := fun s =>
  if s.input.drop s.pos |>.startsWith str then
    .ok str { s with pos := s.pos + str.length }
  else
    .error s!"expected \"{str}\"" s

/-- Optional parser -/
def optionalP (p : ExpParser α) : ExpParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Try parser, backtrack on failure -/
def attempt (p : ExpParser α) : ExpParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Take while predicate holds -/
partial def takeWhile (p : Char → Bool) : ExpParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) : (Nat × List Char) :=
    if pos >= s.input.length then (pos, acc)
    else
      let c := s.input.get ⟨pos⟩
      if p c then go (pos + 1) (c :: acc)
      else (pos, acc)
  let (newPos, chars) := go s.pos []
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Take until specific char (not consuming it) -/
partial def takeUntil (stop : Char) : ExpParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) (depth : Nat) : (Nat × List Char) :=
    if pos >= s.input.length then (pos, acc)
    else
      let c := s.input.get ⟨pos⟩
      if c == stop && depth == 0 then (pos, acc)
      else if c == '{' then go (pos + 1) (c :: acc) (depth + 1)
      else if c == '}' && depth > 0 then go (pos + 1) (c :: acc) (depth - 1)
      else go (pos + 1) (c :: acc) depth
  let (newPos, chars) := go s.pos [] 0
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Variable name character -/
def isVarChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Special parameter characters -/
def isSpecialParam (c : Char) : Bool :=
  c ∈ ['@', '*', '#', '?', '-', '$', '!', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

/-- Parse variable name -/
def parseVarName : ExpParser String := do
  match ← peek with
  | none => failure
  | some c =>
      if isSpecialParam c then
        let _ ← anyChar
        pure (String.ofList [c])
      else if c.isAlpha || c == '_' then
        takeWhile isVarChar
      else failure

mutual

/-- Parse the expansion operation -/
partial def parseOperation : ExpParser ParsedExpansion := do
  -- Check for length prefix
  match ← optionalP (char '#') with
  | some _ =>
      -- ${#var} - length
      let name ← parseVarName
      pure { varName := name, op := .length, isColonVariant := false, isDoubled := false, arg1 := none, arg2 := none }
  | none =>
      -- Check for indirect prefix
      match ← optionalP (char '!') with
      | some _ =>
          let name ← parseVarName
          pure { varName := name, op := .indirect, isColonVariant := false, isDoubled := false, arg1 := none, arg2 := none }
      | none =>
          -- Regular variable
          let name ← parseVarName
          -- Check for array index
          match ← optionalP (char '[') with
          | some _ =>
              let idx ← takeUntil ']'
              let _ ← char ']'
              parseModifier { varName := name ++ "[" ++ idx ++ "]", op := .none, isColonVariant := false, isDoubled := false, arg1 := none, arg2 := none }
          | none =>
              parseModifier { varName := name, op := .none, isColonVariant := false, isDoubled := false, arg1 := none, arg2 := none }

/-- Parse modifier after variable name -/
partial def parseModifier (base : ParsedExpansion) : ExpParser ParsedExpansion := do
  match ← peek with
  | none => pure base
  | some ':' =>
      let _ ← anyChar
      match ← peek with
      | some '-' =>
          let _ ← anyChar
          let arg ← takeUntil '}'
          pure { base with op := .useDefault, isColonVariant := true, arg1 := some arg }
      | some '=' =>
          let _ ← anyChar
          let arg ← takeUntil '}'
          pure { base with op := .assignDefault, isColonVariant := true, arg1 := some arg }
      | some '+' =>
          let _ ← anyChar
          let arg ← takeUntil '}'
          pure { base with op := .useAlternate, isColonVariant := true, arg1 := some arg }
      | some '?' =>
          let _ ← anyChar
          let arg ← takeUntil '}'
          pure { base with op := .errorIfUnset, isColonVariant := true, arg1 := some arg }
      | some c =>
          if c.isDigit || c == '-' then
            -- Substring ${var:offset} or ${var:offset:length}
            let offset ← takeWhile (fun c => c.isDigit || c == '-' || c == ' ')
            match ← optionalP (char ':') with
            | some _ =>
                let len ← takeUntil '}'
                pure { base with op := .substring, arg1 := some offset, arg2 := some len }
            | none =>
                pure { base with op := .substring, arg1 := some offset }
          else failure
      | none => failure
  | some '-' =>
      let _ ← anyChar
      let arg ← takeUntil '}'
      pure { base with op := .useDefault, isColonVariant := false, arg1 := some arg }
  | some '=' =>
      let _ ← anyChar
      let arg ← takeUntil '}'
      pure { base with op := .assignDefault, isColonVariant := false, arg1 := some arg }
  | some '+' =>
      let _ ← anyChar
      let arg ← takeUntil '}'
      pure { base with op := .useAlternate, isColonVariant := false, arg1 := some arg }
  | some '?' =>
      let _ ← anyChar
      let arg ← takeUntil '}'
      pure { base with op := .errorIfUnset, isColonVariant := false, arg1 := some arg }
  | some '#' =>
      let _ ← anyChar
      match ← optionalP (char '#') with
      | some _ =>
          let pattern ← takeUntil '}'
          pure { base with op := .removePrefix, isDoubled := true, arg1 := some pattern }
      | none =>
          let pattern ← takeUntil '}'
          pure { base with op := .removePrefix, isDoubled := false, arg1 := some pattern }
  | some '%' =>
      let _ ← anyChar
      match ← optionalP (char '%') with
      | some _ =>
          let pattern ← takeUntil '}'
          pure { base with op := .removeSuffix, isDoubled := true, arg1 := some pattern }
      | none =>
          let pattern ← takeUntil '}'
          pure { base with op := .removeSuffix, isDoubled := false, arg1 := some pattern }
  | some '/' =>
      let _ ← anyChar
      let doubled ← match ← optionalP (char '/') with
        | some _ => pure true
        | none =>
            match ← peek with
            | some '#' =>
                let _ ← anyChar
                pure false  -- prefix replace
            | some '%' =>
                let _ ← anyChar
                pure false  -- suffix replace
            | _ => pure false
      let find ← takeUntil '/'
      match ← optionalP (char '/') with
      | some _ =>
          let repl ← takeUntil '}'
          pure { base with op := .replace, isDoubled := doubled, arg1 := some find, arg2 := some repl }
      | none =>
          pure { base with op := .replace, isDoubled := doubled, arg1 := some find, arg2 := some "" }
  | some '^' =>
      let _ ← anyChar
      match ← optionalP (char '^') with
      | some _ => pure { base with op := .caseUpper, isDoubled := true }
      | none => pure { base with op := .caseUpper, isDoubled := false }
  | some ',' =>
      let _ ← anyChar
      match ← optionalP (char ',') with
      | some _ => pure { base with op := .caseLower, isDoubled := true }
      | none => pure { base with op := .caseLower, isDoubled := false }
  | some '@' =>
      let _ ← anyChar
      let op ← anyChar
      pure { base with op := .transform, arg1 := some (String.ofList [op]) }
  | _ => pure base

end

/-- Parse a ${...} expansion -/
def parseExpansion (content : String) : Option ParsedExpansion :=
  let state : ExpState := { input := content, pos := 0 }
  match parseOperation state with
  | .ok result s =>
      if s.pos >= s.input.length then some result
      else none  -- Didn't consume all input
  | .error _ _ => none

/-- Check if a string represents a simple variable reference -/
def isSimpleVar (s : String) : Bool :=
  s.all isVarChar && s.length > 0 && (s.get ⟨0⟩).isAlpha

end ShellCheck.Parser.Expansion
