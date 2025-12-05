/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Regex module for ShellCheck using Brzozowski derivatives

  This is a simple regex engine supporting:
  - Literals, concatenation, alternation, Kleene star
  - Character classes: \d, \w, \s, [abc], [^abc], .
  - Quantifiers: ?, +, *
-/

namespace ShellCheck.Regex

/-! ## Core Regex AST -/

/-- Regular expression abstract syntax tree -/
inductive RE where
  | empty      : RE                      -- Matches nothing (∅)
  | epsilon    : RE                      -- Matches empty string (ε)
  | char       : Char → RE               -- Matches single character
  | charClass  : (Char → Bool) → RE      -- Matches if predicate holds
  | seq        : RE → RE → RE            -- Concatenation (r1 r2)
  | alt        : RE → RE → RE            -- Alternation (r1 | r2)
  | star       : RE → RE                 -- Kleene star (r*)
  deriving Inhabited

namespace RE

/-- Smart constructor for alternation (simplifies) -/
def mkAlt : RE → RE → RE
  | .empty, r => r
  | r, .empty => r
  | r1, r2 => .alt r1 r2

/-- Smart constructor for sequence (simplifies) -/
def mkSeq : RE → RE → RE
  | .empty, _ => .empty
  | _, .empty => .empty
  | .epsilon, r => r
  | r, .epsilon => r
  | r1, r2 => .seq r1 r2

/-- Smart constructor for star (simplifies) -/
def mkStar : RE → RE
  | .empty => .epsilon
  | .epsilon => .epsilon
  | .star r => .star r
  | r => .star r

/-! ## Brzozowski Derivatives -/

/-- Does the regex accept the empty string? -/
def nullable : RE → Bool
  | .empty => false
  | .epsilon => true
  | .char _ => false
  | .charClass _ => false
  | .seq r1 r2 => nullable r1 && nullable r2
  | .alt r1 r2 => nullable r1 || nullable r2
  | .star _ => true

/-- Brzozowski derivative: D_c(r) is the regex matching what r matches after c -/
def derivative (c : Char) : RE → RE
  | .empty => .empty
  | .epsilon => .empty
  | .char c' => if c == c' then .epsilon else .empty
  | .charClass p => if p c then .epsilon else .empty
  | .seq r1 r2 =>
    if nullable r1 then
      mkAlt (mkSeq (derivative c r1) r2) (derivative c r2)
    else
      mkSeq (derivative c r1) r2
  | .alt r1 r2 => mkAlt (derivative c r1) (derivative c r2)
  | .star r => mkSeq (derivative c r) (.star r)

/-- Match a string against a regex using derivatives -/
def isMatch (r : RE) (s : List Char) : Bool :=
  match s with
  | [] => nullable r
  | c :: cs => isMatch (derivative c r) cs

end RE

/-! ## Regex Parser -/

/-- Parse state -/
structure ParseState where
  input : List Char
  pos : Nat := 0

/-- Parser monad -/
abbrev Parser := StateT ParseState (Except String)

def peek : Parser (Option Char) := do
  let s ← get
  pure s.input.head?

def advance : Parser Unit := do
  let s ← get
  set { s with input := s.input.drop 1, pos := s.pos + 1 }

def consume : Parser (Option Char) := do
  let c ← peek
  if c.isSome then advance
  pure c

def expect (c : Char) : Parser Unit := do
  match ← consume with
  | some c' => if c != c' then throw s!"Expected '{c}' but got '{c}'"
  | none => throw s!"Expected '{c}' but got end of input"

/-- Character class predicates -/
def isDigit (c : Char) : Bool := c >= '0' && c <= '9'
def isWordChar (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_'
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Parse a character class like [abc] or [^abc] -/
partial def parseCharClass : Parser RE := do
  expect '['
  let negated ← do
    match ← peek with
    | some '^' => advance; pure true
    | _ => pure false
  let mut chars : List Char := []
  while true do
    match ← peek with
    | some ']' => advance; break
    | some c => advance; chars := c :: chars
    | none => throw "Unterminated character class"
  let charSet := chars.reverse
  let pred := fun c => charSet.contains c
  pure $ .charClass (if negated then (fun c => !pred c) else pred)

/-- Parse an escape sequence -/
def parseEscape : Parser RE := do
  match ← consume with
  | some 'd' => pure $ .charClass isDigit
  | some 'D' => pure $ .charClass (!isDigit ·)
  | some 'w' => pure $ .charClass isWordChar
  | some 'W' => pure $ .charClass (!isWordChar ·)
  | some 's' => pure $ .charClass isSpace
  | some 'S' => pure $ .charClass (!isSpace ·)
  | some 'n' => pure $ .char '\n'
  | some 't' => pure $ .char '\t'
  | some 'r' => pure $ .char '\r'
  | some c => pure $ .char c  -- Escaped literal
  | none => throw "Unexpected end after backslash"

mutual
  /-- Parse a single atom (char, group, class) -/
  partial def parseAtom : Parser RE := do
    match ← peek with
    | some '(' => advance; let r ← parseAlt; expect ')'; pure r
    | some '[' => parseCharClass
    | some '\\' => advance; parseEscape
    | some '.' => advance; pure $ .charClass (fun _ => true)
    | some '^' => advance; pure .epsilon  -- Simplified: ignore anchors
    | some '$' => advance; pure .epsilon  -- Simplified: ignore anchors
    | some c =>
      if c == ')' || c == '|' || c == '*' || c == '+' || c == '?' || c == '{' then
        pure .epsilon
      else
        advance; pure $ .char c
    | none => pure .epsilon

  /-- Parse quantified atom -/
  partial def parseQuantified : Parser RE := do
    let atom ← parseAtom
    match ← peek with
    | some '*' => advance; pure $ RE.mkStar atom
    | some '+' => advance; pure $ RE.mkSeq atom (RE.mkStar atom)
    | some '?' => advance; pure $ RE.mkAlt .epsilon atom
    | some '{' =>
      -- Parse {n}, {n,}, {n,m} - simplified to just repeat
      advance
      let mut numStr := ""
      while true do
        match ← peek with
        | some c =>
          if c.isDigit then advance; numStr := numStr.push c
          else break
        | none => break
      -- Skip rest of quantifier
      while true do
        match ← peek with
        | some '}' => advance; break
        | some _ => advance
        | none => break
      let n := numStr.toNat?.getD 1
      -- Repeat n times (simplified)
      let mut result := atom
      for _ in [1:n] do
        result := RE.mkSeq atom result
      pure result
    | _ => pure atom

  /-- Parse concatenation -/
  partial def parseSeq : Parser RE := do
    let mut result := RE.epsilon
    while true do
      match ← peek with
      | some ')' | some '|' | none => break
      | _ =>
        let atom ← parseQuantified
        result := RE.mkSeq result atom
    pure result

  /-- Parse alternation -/
  partial def parseAlt : Parser RE := do
    let mut result ← parseSeq
    while true do
      match ← peek with
      | some '|' => advance; result := RE.mkAlt result (← parseSeq)
      | _ => break
    pure result
end

/-- Parse a regex pattern string -/
def parse (pattern : String) : Except String RE :=
  match StateT.run parseAlt ⟨pattern.toList, 0⟩ with
  | .ok (re, _) => .ok re
  | .error e => .error e

/-! ## Public API -/

/-- Compiled regex pattern -/
structure Regex where
  re : RE
  pattern : String
  deriving Inhabited

/-- Compile a regex pattern string -/
def mkRegex? (pattern : String) : Option Regex :=
  match parse pattern with
  | .ok re => some ⟨re, pattern⟩
  | .error _ => none

/-- Compile a regex, returning empty-matching regex for invalid patterns -/
def mkRegex (pattern : String) : Regex :=
  mkRegex? pattern |>.getD ⟨.epsilon, ""⟩

/-- Check if a string matches the regex (full match) -/
def isMatch (str : String) (re : Regex) : Bool :=
  RE.isMatch re.re str.toList

/-- Check if regex matches anywhere in the string -/
def containsMatch (str : String) (re : Regex) : Bool :=
  -- .*pattern.* effectively
  let wrappedRe := RE.mkSeq (RE.mkStar (.charClass fun _ => true))
                   (RE.mkSeq re.re (RE.mkStar (.charClass fun _ => true)))
  RE.isMatch wrappedRe str.toList

/-- Find first match position, returns (start, end) -/
partial def findMatch (str : String) (re : Regex) : Option (Nat × Nat) :=
  let chars := str.toList
  let rec tryFrom (start : Nat) (remaining : List Char) : Option (Nat × Nat) :=
    match remaining with
    | [] => if RE.nullable re.re then some (start, start) else none
    | _ =>
      -- Try matching from this position
      let rec tryLength (len : Nat) (substr : List Char) (r : RE) : Option Nat :=
        if RE.nullable r then some len
        else match substr with
        | [] => if RE.nullable r then some len else none
        | c :: cs => tryLength (len + 1) cs (RE.derivative c r)
      match tryLength 0 remaining re.re with
      | some len => some (start, start + len)
      | none => tryFrom (start + 1) remaining.tail!
  tryFrom 0 chars

/-- Get captured groups from the first match (simplified: just full match) -/
def matchRegex (re : Regex) (str : String) : Option (List String) :=
  match findMatch str re with
  | some (s, e) =>
    let matched := (str.toList.drop s).take (e - s)
    some [String.ofList matched]
  | none => none

/-- Get all non-overlapping matches -/
partial def matchAllStrings (re : Regex) (str : String) : List String :=
  let chars := str.toList
  let rec go (pos : Nat) (remaining : List Char) (acc : List String) : List String :=
    if remaining.isEmpty then acc.reverse
    else
      -- Try to match at current position
      let rec findEnd (len : Nat) (substr : List Char) (r : RE) (lastMatch : Option Nat) : Option Nat :=
        let lastMatch' := if RE.nullable r then some len else lastMatch
        match substr with
        | [] => lastMatch'
        | c :: cs => findEnd (len + 1) cs (RE.derivative c r) lastMatch'
      match findEnd 0 remaining re.re none with
      | some len =>
        if len == 0 then
          go (pos + 1) remaining.tail! acc  -- Avoid infinite loop on empty match
        else
          let matched := String.ofList (remaining.take len)
          go (pos + len) (remaining.drop len) (matched :: acc)
      | none =>
        go (pos + 1) remaining.tail! acc
  go 0 chars []

/-- Get all subgroups from all matches (simplified: just full matches) -/
def matchAllSubgroups (re : Regex) (str : String) : List (List String) :=
  (matchAllStrings re str).map (fun s => [s])

/-- Replace all occurrences of regex with replacement -/
partial def subRegex (re : Regex) (input replacement : String) : String :=
  let chars := input.toList
  let rec go (remaining : List Char) (acc : List Char) : List Char :=
    if remaining.isEmpty then acc.reverse
    else
      let rec findEnd (len : Nat) (substr : List Char) (r : RE) (lastMatch : Option Nat) : Option Nat :=
        let lastMatch' := if RE.nullable r then some len else lastMatch
        match substr with
        | [] => lastMatch'
        | c :: cs => findEnd (len + 1) cs (RE.derivative c r) lastMatch'
      match findEnd 0 remaining re.re none with
      | some len =>
        if len == 0 then
          match remaining with
          | c :: cs => go cs (c :: acc)
          | [] => acc.reverse
        else
          go (remaining.drop len) (replacement.toList.reverse ++ acc)
      | none =>
        match remaining with
        | c :: cs => go cs (c :: acc)
        | [] => acc.reverse
  String.ofList (go chars [])

/-- Split a string on a regex pattern -/
partial def splitOn (input : String) (re : Regex) : List String :=
  let chars := input.toList
  let rec go (remaining : List Char) (current : List Char) (acc : List String) : List String :=
    if remaining.isEmpty then
      (String.ofList current.reverse :: acc).reverse
    else
      let rec findEnd (len : Nat) (substr : List Char) (r : RE) (lastMatch : Option Nat) : Option Nat :=
        let lastMatch' := if RE.nullable r then some len else lastMatch
        match substr with
        | [] => lastMatch'
        | c :: cs => findEnd (len + 1) cs (RE.derivative c r) lastMatch'
      match findEnd 0 remaining re.re none with
      | some len =>
        if len == 0 then
          match remaining with
          | c :: cs => go cs (c :: current) acc
          | [] => (String.ofList current.reverse :: acc).reverse
        else
          go (remaining.drop len) [] (String.ofList current.reverse :: acc)
      | none =>
        match remaining with
        | c :: cs => go cs (c :: current) acc
        | [] => (String.ofList current.reverse :: acc).reverse
  go chars [] []

/-! ## Simple string operations -/

/-- Check if haystack contains needle as a substring -/
partial def containsSubstring (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else
    let needleChars := needle.toList
    let rec go : List Char → Bool
      | [] => false
      | cs@(_ :: rest) =>
        if cs.take needleChars.length == needleChars then true
        else go rest
    go haystack.toList

/-- Check if string starts with prefix -/
def hasPrefix (str pref : String) : Bool :=
  str.startsWith pref

/-- Check if string ends with suffix -/
def hasSuffix (str suff : String) : Bool :=
  str.endsWith suff

/-- Simple glob-style matching (*, ?) -/
partial def globMatch (pattern text : String) : Bool :=
  let rec go (p t : List Char) : Bool :=
    match p, t with
    | [], [] => true
    | [], _ => false
    | '*' :: ps, ts =>
      go ps ts || (match ts with | [] => false | _ :: ts' => go p ts')
    | '?' :: ps, _ :: ts => go ps ts
    | '?' :: _, [] => false
    | pc :: ps, tc :: ts => pc == tc && go ps ts
    | _ :: _, [] => false
  go pattern.toList text.toList

-- Theorems

theorem mkRegex_pattern (pat : String) : (mkRegex pat).pattern = pat ∨ (mkRegex pat).pattern = "" := by
  simp [mkRegex, mkRegex?]
  cases parse pat <;> simp [Option.getD]

theorem RE.nullable_epsilon : RE.nullable .epsilon = true := rfl
theorem RE.nullable_empty : RE.nullable .empty = false := rfl
theorem RE.nullable_star (r : RE) : RE.nullable (.star r) = true := rfl

end ShellCheck.Regex
