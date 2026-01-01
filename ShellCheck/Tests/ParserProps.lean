import Plausible
import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.Interface
import ShellCheck.Parser

namespace ShellCheck.Tests.ParserProps

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.Interface
open ShellCheck.Parser

def sanitizeChar (c : Char) : Char :=
  if c.isAlpha then c else 'a'

def sanitizeWord (s : String) : String :=
  let w := String.ofList (s.toList.map sanitizeChar)
  if w.isEmpty then "x" else w

def reverseString (s : String) : String :=
  String.ofList s.toList.reverse

def scriptFromSeedQuoted (seed : String) : String :=
  let name := sanitizeWord seed
  let value := sanitizeWord (reverseString seed)
  let assign := name ++ "=\"" ++ value ++ "\""
  let varRef := "$" ++ name
  let echoLine := "echo \"" ++ varRef ++ "\" '" ++ value ++ "'"
  let printfLine := "printf '%s\\n' \"" ++ varRef ++ "\""
  if seed.length % 2 == 0 then
    String.intercalate "\n" [assign, echoLine]
  else
    String.intercalate "\n" [assign, echoLine, printfLine]

def scriptFromSeed (seed : String) : List (List String) :=
  let w1 := sanitizeWord seed
  let w2 := sanitizeWord (reverseString seed)
  let w3 := sanitizeWord (seed ++ "x")
  let cmd1 := [s!"{w1}={w2}", w1, w3]
  let cmd2 := ["echo", w2]
  if seed.length % 2 == 0 then [cmd1] else [cmd1, cmd2]

def renderScript (cmds : List (List String)) : String :=
  String.intercalate "\n" (cmds.map (String.intercalate " "))

def assignmentString? (t : Token) : Option String :=
  match t.inner with
  | .T_Assignment _ name indices value =>
      if indices.isEmpty then
        match getLiteralString value with
        | some v => some (name ++ "=" ++ v)
        | none => none
      else
        none
  | _ => none

def wordString? (t : Token) : Option String :=
  getLiteralString t

partial def normalizeCommand (t : Token) : Option (List String) :=
  match t.inner with
  | .T_Redirecting _ cmd => normalizeCommand cmd
  | .T_SimpleCommand assigns words =>
      match assigns.mapM assignmentString?, words.mapM wordString? with
      | some assignStrs, some wordStrs => some (assignStrs ++ wordStrs)
      | _, _ => none
  | _ => none

partial def normalizeScript (root : Token) : Option (List (List String)) :=
  match root.inner with
  | .T_Annotation _ inner => normalizeScript inner
  | .T_Script _ commands =>
      commands.mapM normalizeCommand
  | _ => none

def posLe (a b : Position) : Bool :=
  if a.posLine < b.posLine then
    true
  else if a.posLine == b.posLine then
    a.posColumn <= b.posColumn
  else
    false

def listGet? (xs : List α) (n : Nat) : Option α :=
  match xs, n with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: rest, n + 1 => listGet? rest n

def posInBounds (script : String) (pos : Position) : Bool :=
  let lines := script.splitOn "\n"
  if pos.posLine == 0 then
    false
  else
    match listGet? lines (pos.posLine - 1) with
    | none => false
    | some line =>
        pos.posColumn >= 1 && pos.posColumn <= line.length + 1

def positionsValid (script : String) (positions : Std.HashMap Id (Position × Position)) : Bool :=
  positions.toList.all (fun (_, (startPos, endPos)) =>
    posLe startPos endPos &&
    posInBounds script startPos &&
    posInBounds script endPos)

def parseOk (script : String) : Bool :=
  let (rootOpt, _positions, errors) := runParser script "<prop>"
  match rootOpt with
  | none => false
  | some _ => errors.isEmpty

def simpleRoundtrip (seed : String) : Bool :=
  let cmds := scriptFromSeed seed
  let script := renderScript cmds
  let (rootOpt, _positions, errors) := runParser script "<prop>"
  match rootOpt with
  | none => false
  | some root =>
      if !errors.isEmpty then
        false
      else
        match normalizeScript root with
        | none => false
        | some norm =>
            let script2 := renderScript norm
            let (rootOpt2, _positions2, errors2) := runParser script2 "<prop2>"
            match rootOpt2 with
            | none => false
            | some root2 =>
                errors2.isEmpty &&
                  decide (normalizeScript root2 = some norm)

def positionsOk (seed : String) : Bool :=
  let script := renderScript (scriptFromSeed seed)
  let (rootOpt, positions, errors) := runParser script "<prop>"
  match rootOpt with
  | none => false
  | some _ => errors.isEmpty && positionsValid script positions

def parseOkQuoted (seed : String) : Bool :=
  let script := scriptFromSeedQuoted seed
  parseOk script

def positionsOkQuoted (seed : String) : Bool :=
  let script := scriptFromSeedQuoted seed
  let (rootOpt, positions, errors) := runParser script "<prop>"
  match rootOpt with
  | none => false
  | some _ => errors.isEmpty && positionsValid script positions

abbrev prop_simple_roundtrip : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    simpleRoundtrip seed = true

abbrev prop_positions_valid : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    positionsOk seed = true

abbrev prop_parse_ok_quoted : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    parseOkQuoted seed = true

abbrev prop_positions_valid_quoted : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    positionsOkQuoted seed = true

end ShellCheck.Tests.ParserProps
