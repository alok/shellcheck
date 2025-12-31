import Plausible
import ShellCheck.AST
import ShellCheck.Interface
import ShellCheck.Parser

namespace ShellCheck.Tests.ParserProps

open Plausible
open ShellCheck.AST
open ShellCheck.Interface
open ShellCheck.Parser

/-- A word made only of safe literal characters for parser round-trips. -/
structure SafeWord where
  value : String
  deriving Repr, BEq, Inhabited

/-- A variable name that starts with a valid identifier character. -/
structure SafeVar where
  value : String
  deriving Repr, BEq, Inhabited

private def safeChars : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_".toList

private def safeVarStartChars : List Char :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_".toList

private def genSafeChar : Gen Char :=
  Gen.elements safeChars (by decide)

private def genChars (n : Nat) : Gen (List Char) :=
  let rec go : Nat → Gen (List Char)
    | 0 => pure []
    | n + 1 => do
        let c ← genSafeChar
        let rest ← go n
        pure (c :: rest)
  go n

private def genSafeWord : Gen String := do
  let size ← Gen.getSize
  let ⟨n, _⟩ ← Gen.choose Nat 1 (size + 1) (by
    exact Nat.succ_le_succ (Nat.zero_le size))
  let chars ← genChars n
  pure (String.ofList chars)

private def genSafeVar : Gen String := do
  let size ← Gen.getSize
  let ⟨n, _⟩ ← Gen.choose Nat 1 (size + 1) (by
    exact Nat.succ_le_succ (Nat.zero_le size))
  let first ← Gen.elements safeVarStartChars (by decide)
  let rest ← genChars (n - 1)
  pure (String.ofList (first :: rest))

instance : Arbitrary SafeWord where
  arbitrary := do
    let w ← genSafeWord
    pure ⟨w⟩

instance : Shrinkable SafeWord where
  shrink w :=
    (Shrinkable.shrink w.value).filter (fun s => !s.isEmpty) |>.map fun s => ⟨s⟩

instance : Arbitrary SafeVar where
  arbitrary := do
    let v ← genSafeVar
    pure ⟨v⟩

instance : Shrinkable SafeVar where
  shrink _ := []

/-- Render a simple script consisting of `echo` and literal words. -/
private def renderEchoScript (words : List String) : String :=
  String.intercalate " " ("echo" :: words)

private def parseScriptOk (script : String) : Except String Token :=
  let (root, _positions, errors) := runFullParser script "<test>"
  match root with
  | some t =>
      if errors.isEmpty then
        .ok t
      else
        .error (String.intercalate "\n" errors)
  | none =>
      .error (String.intercalate "\n" errors)

private def literalWord? (t : Token) : Option String :=
  match t.inner with
  | .T_NormalWord [part] =>
      match part.inner with
      | .T_Literal s => some s
      | _ => none
  | .T_Literal s => some s
  | _ => none

private partial def extractSimpleCommandWords (t : Token) : Option (List String) :=
  match t.inner with
  | .T_SimpleCommand _ words =>
      let lits := words.filterMap literalWord?
      if lits.length == words.length then some lits else none
  | .T_Redirecting _ cmd =>
      extractSimpleCommandWords cmd
  | _ => none

private def extractScriptWords (t : Token) : Option (List String) :=
  match t.inner with
  | .T_Script _ cmds =>
      match cmds with
      | [cmd] => extractSimpleCommandWords cmd
      | _ => none
  | _ => none

private def roundtripOk (words : List SafeWord) : Bool :=
  if words.any (fun w => w.value.isEmpty) then
    true
  else
    let raw := words.map (·.value)
    let script := renderEchoScript raw
    match parseScriptOk script with
    | .ok tok =>
        match extractScriptWords tok with
        | some parsed =>
            let expected := "echo" :: raw
            if decide (parsed = expected) then
            match parseScriptOk (String.intercalate " " parsed) with
              | .ok tok2 => decide (extractScriptWords tok2 = some parsed)
              | .error _ => false
            else
              false
        | none => false
    | .error _ => false

/-- Round-trip for simple literal `echo` scripts. -/
abbrev prop_simple_echo_roundtrip : Prop :=
  Plausible.NamedBinder "words" <| ∀ words : List SafeWord,
    roundtripOk words = true

private def posLe (a b : Position) : Bool :=
  if a.posLine < b.posLine then true
  else if a.posLine == b.posLine then decide (a.posColumn ≤ b.posColumn) else false

private def posValid (p : Position) : Bool :=
  decide (p.posLine ≥ 1 ∧ p.posColumn ≥ 1)

private def positionsOk (positions : Std.HashMap Id (Position × Position)) : Bool :=
  positions.fold (init := true) fun ok _ (startPos, endPos) =>
    ok && posValid startPos && posValid endPos && posLe startPos endPos

private def simpleScriptPositionsOk (words : List SafeWord) : Bool :=
  let script := renderEchoScript (words.map (·.value))
  let (root, positions, errors) := runFullParser script "<test>"
  match root with
  | some _ => errors.isEmpty && positionsOk positions
  | none => false

/-- Positions are nonzero and ordered for simple literal scripts. -/
abbrev prop_positions_valid_for_simple_scripts : Prop :=
  Plausible.NamedBinder "words" <| ∀ words : List SafeWord,
    simpleScriptPositionsOk words = true

private def assignmentScript (name : SafeVar) (value : SafeWord) : String :=
  s!"{name.value}={value.value}"

private def parseOk (script : String) : Bool :=
  match parseScriptOk script with
  | .ok _ => true
  | .error _ => false

/-- Assignments with safe names and literal values parse without errors. -/
abbrev prop_simple_assignment_parses : Prop :=
  Plausible.NamedBinder "var" <| ∀ name : SafeVar,
    Plausible.NamedBinder "value" <| ∀ value : SafeWord,
      parseOk (assignmentScript name value) = true

private def doubleQuotedEchoScript (a b : SafeWord) : String :=
  s!"echo \"{a.value} {b.value}\""

private def singleQuotedEchoScript (a b : SafeWord) : String :=
  s!"echo '{a.value} {b.value}'"

private def redirectScript (word fname : SafeWord) : String :=
  s!"echo {word.value} >{fname.value}"

private def redirectFdScript (word fname : SafeWord) : String :=
  s!"echo {word.value} 2>{fname.value}"

/-- Double-quoted words with spaces parse. -/
abbrev prop_double_quoted_word_parses : Prop :=
  Plausible.NamedBinder "a" <| ∀ a : SafeWord,
    Plausible.NamedBinder "b" <| ∀ b : SafeWord,
      parseOk (doubleQuotedEchoScript a b) = true

/-- Single-quoted words with spaces parse. -/
abbrev prop_single_quoted_word_parses : Prop :=
  Plausible.NamedBinder "a" <| ∀ a : SafeWord,
    Plausible.NamedBinder "b" <| ∀ b : SafeWord,
      parseOk (singleQuotedEchoScript a b) = true

/-- Simple redirections parse. -/
abbrev prop_redirect_parses : Prop :=
  Plausible.NamedBinder "word" <| ∀ word : SafeWord,
    Plausible.NamedBinder "fname" <| ∀ fname : SafeWord,
      parseOk (redirectScript word fname) = true ∧
      parseOk (redirectFdScript word fname) = true

private def commandSubScript (word : SafeWord) : String :=
  "echo $(echo " ++ word.value ++ ")"

private def backtickScript (word : SafeWord) : String :=
  "echo `echo " ++ word.value ++ "`"

private def heredocScript (content : SafeWord) : String :=
  "cat <<EOF\n" ++ content.value ++ "\nEOF\n"

private def ifScript (cond body : SafeWord) : String :=
  s!"if echo {cond.value}; then echo {body.value}; fi"

private def whileScript (cond body : SafeWord) : String :=
  s!"while echo {cond.value}; do echo {body.value}; done"

private def forInScript (name : SafeVar) (a b : SafeWord) : String :=
  s!"for {name.value} in {a.value} {b.value}; do echo ${name.value}; done"

private def pipelineScript (a b : SafeWord) : String :=
  s!"echo {a.value} | cat {b.value}"

private def andOrScript (a b : SafeWord) : String :=
  s!"echo {a.value} && echo {b.value}"

private def orOrScript (a b : SafeWord) : String :=
  s!"echo {a.value} || echo {b.value}"

private def caseScript (word pat body : SafeWord) : String :=
  s!"case {word.value} in {pat.value}) echo {body.value} ;; esac"

private def functionScript (name : SafeVar) (body : SafeWord) : String :=
  name.value ++ "() { echo " ++ body.value ++ "; }"

private def subshellScript (word : SafeWord) : String :=
  s!"(echo {word.value})"

/-- Command substitution parses. -/
abbrev prop_command_substitution_parses : Prop :=
  Plausible.NamedBinder "word" <| ∀ word : SafeWord,
    parseOk (commandSubScript word) = true

/-- Backtick command substitution parses. -/
abbrev prop_backtick_parses : Prop :=
  Plausible.NamedBinder "word" <| ∀ word : SafeWord,
    parseOk (backtickScript word) = true

/-- Simple heredoc parses. -/
abbrev prop_heredoc_parses : Prop :=
  Plausible.NamedBinder "content" <| ∀ content : SafeWord,
    parseOk (heredocScript content) = true

/-- If/then/fi blocks parse. -/
abbrev prop_if_parses : Prop :=
  Plausible.NamedBinder "cond" <| ∀ cond : SafeWord,
    Plausible.NamedBinder "body" <| ∀ body : SafeWord,
      parseOk (ifScript cond body) = true

/-- While loops parse. -/
abbrev prop_while_parses : Prop :=
  Plausible.NamedBinder "cond" <| ∀ cond : SafeWord,
    Plausible.NamedBinder "body" <| ∀ body : SafeWord,
      parseOk (whileScript cond body) = true

/-- For-in loops parse. -/
abbrev prop_for_in_parses : Prop :=
  Plausible.NamedBinder "name" <| ∀ name : SafeVar,
    Plausible.NamedBinder "a" <| ∀ a : SafeWord,
      Plausible.NamedBinder "b" <| ∀ b : SafeWord,
        parseOk (forInScript name a b) = true

/-- Pipelines parse. -/
abbrev prop_pipeline_parses : Prop :=
  Plausible.NamedBinder "a" <| ∀ a : SafeWord,
    Plausible.NamedBinder "b" <| ∀ b : SafeWord,
      parseOk (pipelineScript a b) = true

/-- && chains parse. -/
abbrev prop_and_or_parses : Prop :=
  Plausible.NamedBinder "a" <| ∀ a : SafeWord,
    Plausible.NamedBinder "b" <| ∀ b : SafeWord,
      parseOk (andOrScript a b) = true

/-- || chains parse. -/
abbrev prop_or_or_parses : Prop :=
  Plausible.NamedBinder "a" <| ∀ a : SafeWord,
    Plausible.NamedBinder "b" <| ∀ b : SafeWord,
      parseOk (orOrScript a b) = true

/-- Case blocks parse. -/
abbrev prop_case_parses : Prop :=
  Plausible.NamedBinder "word" <| ∀ word : SafeWord,
    Plausible.NamedBinder "pat" <| ∀ pat : SafeWord,
      Plausible.NamedBinder "body" <| ∀ body : SafeWord,
        parseOk (caseScript word pat body) = true

/-- Function definitions parse. -/
abbrev prop_function_definition_parses : Prop :=
  Plausible.NamedBinder "name" <| ∀ name : SafeVar,
    Plausible.NamedBinder "body" <| ∀ body : SafeWord,
      parseOk (functionScript name body) = true

/-- Subshells parse. -/
abbrev prop_subshell_parses : Prop :=
  Plausible.NamedBinder "word" <| ∀ word : SafeWord,
    parseOk (subshellScript word) = true

private def assignmentPositionsOk (name : SafeVar) (value : SafeWord) : Bool :=
  let script := assignmentScript name value
  let (root, positions, errors) := runFullParser script "<test>"
  match root with
  | some _ => errors.isEmpty && positionsOk positions
  | none => false

/-- Positions are nonzero and ordered for simple assignments. -/
abbrev prop_assignment_positions_valid : Prop :=
  Plausible.NamedBinder "var" <| ∀ name : SafeVar,
    Plausible.NamedBinder "value" <| ∀ value : SafeWord,
      assignmentPositionsOk name value = true

end ShellCheck.Tests.ParserProps
