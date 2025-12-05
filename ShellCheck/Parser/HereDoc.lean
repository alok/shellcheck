/-
  Here document parser for ShellCheck
  Handles <<EOF, <<-EOF, <<'EOF', etc.
-/

import ShellCheck.AST

namespace ShellCheck.Parser.HereDoc

open ShellCheck.AST

/-- Get character at byte position (0-indexed) -/
def getCharAt (s : String) (pos : Nat) : Option Char :=
  if pos < s.length then some (s.data.getD pos ' ') else none

/-- Parser state for here documents -/
structure HereState where
  input : String
  pos : Nat
  deriving Repr, Inhabited

/-- Result type -/
inductive HereResult (α : Type) where
  | ok : α → HereState → HereResult α
  | error : String → HereState → HereResult α
  deriving Repr, Inhabited, Nonempty

/-- Here document parser monad -/
def HereParser (α : Type) := HereState → HereResult α

instance : Monad HereParser where
  pure a := fun s => .ok a s
  bind p f := fun s =>
    match p s with
    | .ok a s' => f a s'
    | .error msg s' => .error msg s'

instance : Alternative HereParser where
  failure := fun s => .error "failure" s
  orElse p q := fun s =>
    match p s with
    | .ok a s' => .ok a s'
    | .error _ _ => q () s

/-- Check if at end -/
def isEnd : HereParser Bool := fun s =>
  .ok (s.pos >= s.input.length) s

/-- Peek at current character -/
def peek : HereParser (Option Char) := fun s =>
  .ok (getCharAt s.input s.pos) s

/-- Consume current character -/
def anyChar : HereParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error "unexpected end" s
  | some c => .ok c { s with pos := s.pos + 1 }

/-- Consume specific character -/
def char (c : Char) : HereParser Char := fun s =>
  match getCharAt s.input s.pos with
  | none => .error s!"expected '{c}'" s
  | some actual =>
      if actual == c then .ok c { s with pos := s.pos + 1 }
      else .error s!"expected '{c}'" s

/-- Consume specific string -/
def matchStr (str : String) : HereParser String := fun s =>
  let remaining := s.input.drop s.pos
  if remaining.startsWith str then
    .ok str { s with pos := s.pos + str.length }
  else
    .error s!"expected \"{str}\"" s

/-- Optional parser -/
def optionalP (p : HereParser α) : HereParser (Option α) := fun s =>
  match p s with
  | .ok a s' => .ok (some a) s'
  | .error _ _ => .ok none s

/-- Try parser, backtrack on failure -/
def attempt (p : HereParser α) : HereParser α := fun s =>
  match p s with
  | .ok a s' => .ok a s'
  | .error msg _ => .error msg s

/-- Take while predicate holds -/
partial def takeWhile (p : Char → Bool) : HereParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) : (Nat × List Char) :=
    match getCharAt s.input pos with
    | none => (pos, acc)
    | some c =>
        if p c then go (pos + 1) (c :: acc)
        else (pos, acc)
  let (newPos, chars) := go s.pos []
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Take until newline (not consuming it) -/
partial def takeUntilNewline : HereParser String := fun s =>
  let rec go (pos : Nat) (acc : List Char) : (Nat × List Char) :=
    match getCharAt s.input pos with
    | none => (pos, acc)
    | some c =>
        if c == '\n' then (pos, acc)
        else go (pos + 1) (c :: acc)
  let (newPos, chars) := go s.pos []
  .ok (String.ofList chars.reverse) { s with pos := newPos }

/-- Get current position -/
def getPos : HereParser Nat := fun s => .ok s.pos s

/-- Get remaining input -/
def getRemainingInput : HereParser String := fun s =>
  .ok (s.input.drop s.pos) s

/-- Parsed here document info -/
structure ParsedHereDoc where
  dashed : Dashed       -- Whether <<- was used
  quoted : Quoted       -- Whether delimiter was quoted
  delimiter : String    -- The end marker
  content : String      -- The document content
  deriving Repr

/-- Check if a line matches the delimiter (with optional leading tabs for dashed) -/
def lineMatchesDelimiter (line : String) (delimiter : String) (dash : Dashed) : Bool :=
  match dash with
  | .dashed => line.dropWhile (· == '\t') == delimiter
  | .undashed => line == delimiter

/-- Strip leading tabs from content lines if dashed -/
def stripLeadingTabs (content : String) (dash : Dashed) : String :=
  match dash with
  | .undashed => content
  | .dashed =>
      let lines := content.splitOn "\n"
      let stripped := lines.map fun line => line.dropWhile (· == '\t')
      String.intercalate "\n" stripped

/-- Parse the delimiter (handles quoting) -/
def parseDelimiter : HereParser (String × Quoted) := do
  let _ ← takeWhile (· == ' ')  -- Skip whitespace
  match ← peek with
  | none => failure
  | some '\'' =>
      -- Single-quoted: 'delimiter'
      let _ ← char '\''
      let delim ← takeWhile (· != '\'')
      let _ ← char '\''
      pure (delim, .quoted)
  | some '"' =>
      -- Double-quoted: "delimiter"
      let _ ← char '"'
      let delim ← takeWhile (· != '"')
      let _ ← char '"'
      pure (delim, .quoted)
  | some '\\' =>
      -- Escaped first char: \delimiter makes it quoted
      let _ ← char '\\'
      let delim ← takeWhile (fun c => !c.isWhitespace && c != '\n')
      pure (delim, .quoted)
  | some '$' =>
      -- $'...' style
      match ← optionalP (matchStr "$'") with
      | some _ =>
          let delim ← takeWhile (· != '\'')
          let _ ← char '\''
          pure (delim, .quoted)
      | none =>
          -- Just starts with $, unquoted
          let delim ← takeWhile (fun c => !c.isWhitespace && c != '\n')
          pure (delim, .unquoted)
  | _ =>
      -- Unquoted delimiter
      let delim ← takeWhile (fun c => !c.isWhitespace && c != '\n')
      if delim.isEmpty then failure
      else pure (delim, .unquoted)

/-- Read here-doc content until delimiter is found -/
partial def readHereDocContent (delimiter : String) (dash : Dashed) : HereParser String := fun s =>
  let rec go (pos : Nat) (contentAcc : List String) (lineAcc : List Char) : HereResult String :=
    match getCharAt s.input pos with
    | none =>
        -- End of input without finding delimiter - error
        .error s!"here-doc delimiter '{delimiter}' not found" s
    | some c =>
        if c == '\n' then
          let line := String.ofList lineAcc.reverse
          -- Check if this line is the delimiter
          if lineMatchesDelimiter line delimiter dash then
            -- Found delimiter - return content
            let content := String.intercalate "\n" contentAcc.reverse
            .ok content { s with pos := pos + 1 }
          else
            -- Not delimiter - add line to content and continue
            go (pos + 1) (line :: contentAcc) []
        else
          go (pos + 1) contentAcc (c :: lineAcc)
  -- First consume the newline after the here-doc operator line
  match getCharAt s.input s.pos with
  | none => .error "expected newline after here-doc operator" s
  | some c =>
      if c != '\n' then
        -- The here-doc content starts on the next line
        -- First consume until newline
        let rec skipToNewline (pos : Nat) : Nat :=
          match getCharAt s.input pos with
          | none => pos
          | some ch => if ch == '\n' then pos + 1 else skipToNewline (pos + 1)
        let startPos := skipToNewline s.pos
        go startPos [] []
      else
        go (s.pos + 1) [] []

/-- Parse a complete here document starting from << -/
def parseHereDoc : HereParser ParsedHereDoc := do
  let _ ← matchStr "<<"
  -- Check for dash (tab stripping)
  let dash ← match ← optionalP (char '-') with
    | some _ => pure Dashed.dashed
    | none => pure Dashed.undashed
  -- Parse delimiter
  let (delimiter, quot) ← parseDelimiter
  -- Read content
  let content ← readHereDocContent delimiter dash
  -- Strip tabs if dashed
  let finalContent := stripLeadingTabs content dash
  pure { dashed := dash, quoted := quot, delimiter, content := finalContent }

/-- Entry point: parse here-doc from a string starting at << -/
def parse (input : String) : Option ParsedHereDoc :=
  let state : HereState := { input, pos := 0 }
  match parseHereDoc state with
  | .ok result _ => some result
  | .error _ _ => none

/-- Check if string starts with here-doc operator -/
def startsWithHereDoc (str : String) : Bool :=
  str.startsWith "<<"

/-- Parse just the here-doc header (<<[-]DELIM) without content -/
def parseHereDocHeader : HereParser (Dashed × Quoted × String) := do
  let _ ← matchStr "<<"
  let dash ← match ← optionalP (char '-') with
    | some _ => pure Dashed.dashed
    | none => pure Dashed.undashed
  let (delimiter, quot) ← parseDelimiter
  pure (dash, quot, delimiter)

/-- Parse just the header, returning delimiter info -/
def parseHeader (input : String) : Option (Dashed × Quoted × String) :=
  let state : HereState := { input, pos := 0 }
  match parseHereDocHeader state with
  | .ok result _ => some result
  | .error _ _ => none

end ShellCheck.Parser.HereDoc
