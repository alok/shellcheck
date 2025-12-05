/-
  Extended glob and brace expansion parser for ShellCheck
  Handles ?(pat), *(pat), +(pat), @(pat), !(pat) and {a,b,c}, {1..10}
-/

import ShellCheck.AST

namespace ShellCheck.Parser.Glob

open ShellCheck.AST

/-- Extended glob operator types -/
inductive ExtGlobOp where
  | zeroOrOne   -- ?(pattern)
  | zeroOrMore  -- *(pattern)
  | oneOrMore   -- +(pattern)
  | exactlyOne  -- @(pattern)
  | notMatching -- !(pattern)
  deriving Repr, BEq, Inhabited

/-- Brace expansion types -/
inductive BraceType where
  | alternatives : List String → BraceType     -- {a,b,c}
  | numericRange : Int → Int → Option Nat → BraceType  -- {1..10} or {01..10} (with padding)
  | charRange : Char → Char → BraceType        -- {a..z}
  deriving Repr, BEq, Inhabited

/-- Parsed glob element -/
inductive GlobElement where
  | literal : String → GlobElement
  | extGlob : ExtGlobOp → List String → GlobElement  -- operator and patterns (pipe-separated)
  | braceExpansion : BraceType → GlobElement
  | singleChar : GlobElement     -- ?
  | anyString : GlobElement      -- *
  | charClass : String → Bool → GlobElement  -- [abc] or [!abc]
  deriving Repr, Inhabited

/-- Get character at position -/
def getCharAt (s : String) (pos : Nat) : Option Char :=
  if pos < s.length then some (s.toList.getD pos ' ') else none

/-- Parser state -/
structure GlobState where
  input : String
  pos : Nat
  deriving Repr, Inhabited

/-- Result type -/
inductive GlobResult (α : Type) where
  | ok : α → GlobState → GlobResult α
  | error : String → GlobState → GlobResult α
  deriving Repr, Inhabited, Nonempty

/-- Glob parser monad -/
def GlobParser (α : Type) := GlobState → GlobResult α

instance : Monad GlobParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative GlobParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Peek at current character -/
def peek : GlobParser (Option Char) := fun s =>
  .ok (getCharAt s.input s.pos) s

/-- Consume current character -/
def anyChar : GlobParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error "unexpected end" s
  | some c => .ok c { s with pos := s.pos + 1 }

/-- Consume specific character -/
def char (c : Char) : GlobParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error s!"expected '{c}'" s
  | some actual =>
      if actual == c then .ok c { s with pos := s.pos + 1 }
      else .error s!"expected '{c}'" s

/-- Consume specific string -/
def matchStr (str : String) : GlobParser String := fun s =>
  let remaining := s.input.drop s.pos
  if remaining.startsWith str then
    .ok str { s with pos := s.pos + str.length }
  else
    .error s!"expected \"{str}\"" s

/-- Optional parser -/
def optionalP (p : GlobParser α) : GlobParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Try parser, backtrack on failure -/
def attempt (p : GlobParser α) : GlobParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Take while predicate holds -/
partial def takeWhile (p : Char → Bool) : GlobParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) : (Nat × List Char) :=
    match getCharAt s.input pos with
    | none => (pos, acc)
    | some c =>
        if p c then go (pos + 1) (c :: acc)
        else (pos, acc)
  let (newPos, chars) := go s.pos []
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Take until specific char (not consuming it) -/
partial def takeUntil (stop : Char) : GlobParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) (depth : Nat) : (Nat × List Char) :=
    match getCharAt s.input pos with
    | none => (pos, acc)
    | some c =>
        if c == stop && depth == 0 then (pos, acc)
        else if c == '(' then go (pos + 1) (c :: acc) (depth + 1)
        else if c == ')' && depth > 0 then go (pos + 1) (c :: acc) (depth - 1)
        else go (pos + 1) (c :: acc) depth
  let (newPos, chars) := go s.pos [] 0
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Get current position -/
def getPos : GlobParser Nat := fun s => .ok s.pos s

/-- Set position -/
def setPos (pos : Nat) : GlobParser Unit := fun s => .ok () { s with pos }

/-- Parse extended glob operator -/
def parseExtGlobOp : GlobParser ExtGlobOp :=
  attempt (char '?' *> char '(' *> pure .zeroOrOne) <|>
  attempt (char '*' *> char '(' *> pure .zeroOrMore) <|>
  attempt (char '+' *> char '(' *> pure .oneOrMore) <|>
  attempt (char '@' *> char '(' *> pure .exactlyOne) <|>
  attempt (char '!' *> char '(' *> pure .notMatching)

/-- Parse extended glob: op(pattern|pattern|...) -/
def parseExtGlob : GlobParser GlobElement := do
  let op ← parseExtGlobOp
  -- We're now past the opening (
  let content ← takeUntil ')'
  let _ ← char ')'
  let patterns := content.splitOn "|"
  pure (.extGlob op patterns)

/-- Parse a number (potentially negative) -/
def parseInteger : GlobParser Int := do
  let neg ← optionalP (char '-')
  let digits ← takeWhile Char.isDigit
  if digits.isEmpty then failure
  else
    match digits.toNat? with
    | some n =>
        match neg with
        | some _ => pure (-(n : Int))
        | none => pure (n : Int)
    | none => failure

/-- Helper: parse comma-separated alternatives -/
partial def parseAltsLoop (acc : List String) : GlobParser (List String) := do
  match ← peek with
  | some ',' =>
      let _ ← char ','
      let alt ← takeWhile (fun c => c != ',' && c != '}')
      parseAltsLoop (alt :: acc)
  | _ => pure acc.reverse

/-- Parse brace expansion content -/
def parseBraceContent : GlobParser BraceType := do
  -- Check for range syntax: start..end
  let start ← takeWhile (fun c => c != ',' && c != '.' && c != '}')
  match ← peek with
  | some '.' =>
      let _ ← matchStr ".."
      let endStr ← takeWhile (fun c => c != '}')
      -- Check if numeric or character range
      match (start.toInt?, endStr.toInt?) with
      | (some startN, some endN) =>
          -- Check for zero-padding
          let padding := if start.startsWith "0" && start.length > 1
            then some start.length
            else none
          pure (.numericRange startN endN padding)
      | _ =>
          -- Character range
          if start.length == 1 && endStr.length == 1 then
            let sc := start.toList.headD 'a'
            let ec := endStr.toList.headD 'z'
            pure (.charRange sc ec)
          else failure
  | some ',' =>
      -- Comma-separated alternatives
      let rest ← parseAltsLoop []
      pure (.alternatives (start :: rest))
  | _ =>
      -- Single item (will expand to just itself)
      pure (.alternatives [start])

/-- Parse brace expansion: {content} -/
def parseBraceExpansion : GlobParser GlobElement := do
  let _ ← char '{'
  let content ← parseBraceContent
  let _ ← char '}'
  pure (.braceExpansion content)

/-- Parse character class: [abc] or [!abc] or [^abc] -/
def parseCharClass : GlobParser GlobElement := do
  let _ ← char '['
  let negated ← match ← peek with
    | some '!' => let _ ← char '!'; pure true
    | some '^' => let _ ← char '^'; pure true
    | _ => pure false
  let chars ← takeUntil ']'
  let _ ← char ']'
  pure (.charClass chars negated)

/-- Parse any glob element -/
def parseGlobElement : GlobParser GlobElement :=
  attempt parseExtGlob <|>
  attempt parseBraceExpansion <|>
  attempt parseCharClass <|>
  attempt (char '?' *> pure .singleChar) <|>
  attempt (char '*' *> pure .anyString) <|>
  (do let c ← anyChar; pure (.literal (String.ofList [c])))

/-- Check if a character could start an extended glob -/
def isExtGlobStart (c : Char) : Bool :=
  c == '?' || c == '*' || c == '+' || c == '@' || c == '!'

/-- Check if string contains extended glob patterns -/
def hasExtGlob (s : String) : Bool :=
  let chars := s.toList
  let rec check (prev : Option Char) (rest : List Char) : Bool :=
    match rest with
    | [] => false
    | c :: cs =>
        if c == '(' then
          match prev with
          | some p => if isExtGlobStart p then true else check (some c) cs
          | none => check (some c) cs
        else check (some c) cs
  check none chars

/-- Check if string contains brace expansion -/
def hasBraceExpansion (s : String) : Bool :=
  s.any (· == '{') && s.any (· == '}')

/-- Parse extended glob from string -/
def parseExtGlobStr (input : String) : Option GlobElement :=
  let state : GlobState := { input, pos := 0 }
  match parseExtGlob state with
  | .ok result _ => some result
  | .error _ _ => none

/-- Parse brace expansion from string -/
def parseBraceStr (input : String) : Option GlobElement :=
  let state : GlobState := { input, pos := 0 }
  match parseBraceExpansion state with
  | .ok result _ => some result
  | .error _ _ => none

/-- Expand a brace expansion to list of strings -/
def expandBrace : BraceType → List String
  | .alternatives alts => alts
  | .numericRange start endN padding =>
      let count := if start <= endN
        then (endN - start).toNat + 1
        else (start - endN).toNat + 1
      let indices := List.range count
      let nums := indices.map fun (i : Nat) =>
        let iInt : Int := i
        if start <= endN then start + iInt else start - iInt
      nums.map fun (n : Int) =>
        let absN := n.natAbs
        let s := toString absN
        match padding with
        | some p =>
            let sign := if n < 0 then "-" else ""
            let padLen := if p > s.length then p - s.length else 0
            let padded := String.ofList (List.replicate padLen '0') ++ s
            sign ++ padded
        | none => toString n
  | .charRange startC endC =>
      let startN := startC.toNat
      let endNat := endC.toNat
      let count := if startN <= endNat then endNat - startN + 1 else startN - endNat + 1
      let indices := List.range count
      let range := indices.map fun i =>
        if startN <= endNat then startN + i else startN - i
      range.map fun n => String.ofList [Char.ofNat n]

/-- Convert ExtGlobOp to string -/
def ExtGlobOp.toString : ExtGlobOp → String
  | .zeroOrOne => "?"
  | .zeroOrMore => "*"
  | .oneOrMore => "+"
  | .exactlyOne => "@"
  | .notMatching => "!"

instance : ToString ExtGlobOp := ⟨ExtGlobOp.toString⟩

end ShellCheck.Parser.Glob
