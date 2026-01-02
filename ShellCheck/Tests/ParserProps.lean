import Plausible
import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.Interface
import ShellCheck.Parser
import ShellCheck.Tests.ParserHelpers

namespace ShellCheck.Tests.ParserProps

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.Interface
open ShellCheck.Parser
open ShellCheck.Tests.ParserHelpers

def sanitizeChar (c : Char) : Char :=
  if c.isAlpha then c else 'a'

def sanitizeWord (s : String) : String :=
  let w := String.ofList (s.toList.map sanitizeChar)
  if w.isEmpty then "x" else w

def sanitizeIdent (s : String) : String :=
  let chars := s.toList.map (fun c => if c.isAlphanum || c == '_' then c else 'a')
  let chars := if chars.isEmpty then ['x'] else chars
  let head := chars.head!
  let head := if head.isAlpha || head == '_' then head else 'x'
  String.ofList (head :: chars.tail)

def reverseString (s : String) : String :=
  String.ofList s.toList.reverse

def scriptFromSeedQuoted (seed : String) : String :=
  let name := sanitizeIdent seed
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

def scriptFromSeedComplex (seed : String) : String :=
  let name := sanitizeIdent seed
  let arr := sanitizeIdent (seed ++ "arr")
  let value := sanitizeWord (reverseString seed)
  let idx := sanitizeWord (seed ++ "i")
  let heredocTag := "SC_EOF_1"
  let line1 := s!"{name}={value}"
  let line2 := s!"{arr}[{idx}]={value}"
  let line3 := s!"echo $(printf '%s' \"{value}\")"
  let line4 := s!"echo $((1+2)) ${name}"
  let line5 := s!"cat <<{heredocTag}"
  let line6 := s!"${name}"
  let line7 := heredocTag
  String.intercalate "\n" [line1, line2, line3, line4, line5, line6, line7]

def scriptFromSeedVariants (seed : String) : String :=
  let name := sanitizeIdent seed
  let value := sanitizeWord (reverseString seed)
  let alt := sanitizeWord (seed ++ "alt")
  let line1 := s!"{name}={value}"
  let line2 := s!"echo $'{value}\\n{alt}\\t'"
  let line3 := s!"echo $\"{alt}\""
  let line4 := "echo \"${" ++ name ++ ":-" ++ alt ++ "}\""
  let line5 := "cat <<< \"${" ++ name ++ "}\""
  let line6 := s!"echo $(printf '%s' \"{value}\")"
  let line7 := "echo `printf '%s' \"" ++ alt ++ "\"`"
  let line8 := s!"echo <(printf '%s' {value})"
  let line9 := "echo $((1+2))"
  String.intercalate "\n" [line1, line2, line3, line4, line5, line6, line7, line8, line9]

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

def positionsHas (positions : Std.HashMap Id (Position × Position)) (id : Id) : Bool :=
  match positions.get? id with
  | some _ => true
  | none => false

def positionsCoverTokens (positions : Std.HashMap Id (Position × Position)) (root : Token) : Bool :=
  collectTokenIds root |>.all (positionsHas positions)

def parseOk (script : String) : Bool :=
  let (rootOpt, _positions, errors) := runParser script "<prop>"
  match rootOpt with
  | none => false
  | some _ => errors.isEmpty

def parseRoot? (script : String) : Option Token :=
  let (rootOpt, _positions, errors) := runParser script "<prop>"
  match rootOpt with
  | none => none
  | some root =>
      if errors.isEmpty then some root else none

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

def positionsOkScript (script : String) : Bool :=
  let (rootOpt, positions, errors) := runParser script "<prop>"
  match rootOpt with
  | none => false
  | some root =>
      errors.isEmpty &&
        positionsValid script positions &&
        positionsCoverTokens positions root

def positionsOk (seed : String) : Bool :=
  positionsOkScript (renderScript (scriptFromSeed seed))

def parseOkQuoted (seed : String) : Bool :=
  let script := scriptFromSeedQuoted seed
  parseOk script

def parseOkComplex (seed : String) : Bool :=
  parseOk (scriptFromSeedComplex seed)

def parseOkVariants (seed : String) : Bool :=
  parseOk (scriptFromSeedVariants seed)

def positionsOkQuoted (seed : String) : Bool :=
  positionsOkScript (scriptFromSeedQuoted seed)

def positionsOkComplex (seed : String) : Bool :=
  positionsOkScript (scriptFromSeedComplex seed)

def positionsOkVariants (seed : String) : Bool :=
  positionsOkScript (scriptFromSeedVariants seed)

def tokenIdsUnique (root : Token) : Bool :=
  let ids := collectTokenIds root
  let set := ids.foldl (fun acc id => acc.insert id) ({} : Std.HashSet Id)
  set.size == ids.length

def idsUniqueScript (script : String) : Bool :=
  match parseRoot? script with
  | none => false
  | some root => tokenIdsUnique root

def idsUnique (seed : String) : Bool :=
  idsUniqueScript (renderScript (scriptFromSeed seed))

def idsUniqueComplex (seed : String) : Bool :=
  idsUniqueScript (scriptFromSeedComplex seed)

def idsUniqueVariants (seed : String) : Bool :=
  idsUniqueScript (scriptFromSeedVariants seed)

def braceExpansionSplits (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let w2 := sanitizeWord (reverseString seed)
  let script := "echo {" ++ w1 ++ "," ++ w2 ++ "}"
  match parseRoot? script with
  | none => false
  | some root =>
      match firstBraceExpansion? root with
      | none => false
      | some parts =>
          parts.map getLiteralString == [some w1, some w2]

def braceExpansionNestedLiteral (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let w2 := sanitizeWord (reverseString seed)
  let w3 := sanitizeWord (seed ++ "x")
  let script := "echo {" ++ w1 ++ ",{" ++ w2 ++ "," ++ w3 ++ "}}"
  match parseRoot? script with
  | none => false
  | some root =>
      match firstBraceExpansion? root with
      | none => false
      | some parts =>
          let expected := "{" ++ w2 ++ "," ++ w3 ++ "}"
          parts.map getLiteralString == [some w1, some expected]

def braceExpansionRangeIsExpansion (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let w2 := sanitizeWord (reverseString seed)
  let script := "echo {" ++ w1 ++ ".." ++ w2 ++ "}"
  match parseRoot? script with
  | none => false
  | some root =>
      match firstBraceExpansion? root with
      | none => false
      | some parts =>
          parts.map getLiteralString == [some (w1 ++ ".." ++ w2)]

def extglobSplits (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let w2 := sanitizeWord (reverseString seed)
  let script := "echo @(" ++ w1 ++ "|" ++ w2 ++ ")"
  match parseRoot? script with
  | none => false
  | some root =>
      match firstExtglob? root with
      | none => false
      | some (_, parts) =>
          parts.map getLiteralString == [some w1, some w2]

def extglobBracketKeepsPipe (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "echo @([|]|" ++ w1 ++ ")"
  match parseRoot? script with
  | none => false
  | some root =>
      match firstExtglob? root with
      | none => false
      | some (_, parts) =>
          parts.map getLiteralString == [some "[|]", some w1]

def heredocUnquotedExpands (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "cat <<EOF\n$" ++ w1 ++ "\nEOF\n"
  match parseRoot? script with
  | none => false
  | some root =>
      match collectHereDocs root with
      | [] => false
      | (quotedFlag, content) :: _ =>
          quotedFlag == .unquoted && content.any hasAnyDollarExpansion

def heredocMultipleExpands (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let w2 := sanitizeWord (reverseString seed)
  let script :=
    "cat <<EOF1 <<EOF2\n$" ++ w1 ++ "\nEOF1\n$" ++ w2 ++ "\nEOF2\n"
  match parseRoot? script with
  | none => false
  | some root =>
      let docs := collectHereDocs root
      let okCount := docs.length == 2
      let okContent := docs.all (fun (quotedFlag, content) =>
        quotedFlag == .unquoted && content.any hasAnyDollarExpansion)
      okCount && okContent

def heredocDashedExpands (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "cat <<-EOF\n\t$" ++ w1 ++ "\n\tEOF\n"
  match parseRoot? script with
  | none => false
  | some root =>
      match collectHereDocs root with
      | [] => false
      | (quotedFlag, content) :: _ =>
          quotedFlag == .unquoted && content.any hasAnyDollarExpansion

def procSubEscapedQuote (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "cat <(echo \"\\\"" ++ w1 ++ "\\\"\")"
  match parseRoot? script with
  | none => false
  | some root =>
      match firstProcSub? root with
      | none => false
      | some _ => true

def unparsedIndexPreservesContent (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "arr[" ++ w1 ++ "]=1"
  match parseRoot? script with
  | none => false
  | some root =>
      match firstUnparsedIndex? root with
      | some content => content == w1
      | none => false

def unquotedDollarExpands (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "echo $" ++ w1
  match parseRoot? script with
  | none => false
  | some root => hasAnyDollarExpansion root

def doubleQuotedDollarExpands (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "echo \"$" ++ w1 ++ "\""
  match parseRoot? script with
  | none => false
  | some root => hasAnyDollarExpansion root

def singleQuotedDollarLiteral (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "echo '$" ++ w1 ++ "'"
  match parseRoot? script with
  | none => false
  | some root => !hasAnyDollarExpansion root

def escapedDollarLiteral (seed : String) : Bool :=
  let w1 := sanitizeWord seed
  let script := "echo \\$" ++ w1
  match parseRoot? script with
  | none => false
  | some root => !hasAnyDollarExpansion root

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

abbrev prop_parse_ok_complex : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    parseOkComplex seed = true

abbrev prop_positions_valid_complex : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    positionsOkComplex seed = true

abbrev prop_parse_ok_variants : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    parseOkVariants seed = true

abbrev prop_positions_valid_variants : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    positionsOkVariants seed = true

abbrev prop_ids_unique_simple : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    idsUnique seed = true

abbrev prop_ids_unique_complex : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    idsUniqueComplex seed = true

abbrev prop_ids_unique_variants : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    idsUniqueVariants seed = true

abbrev prop_brace_expansion_splits : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    braceExpansionSplits seed = true

abbrev prop_brace_expansion_nested_literal : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    braceExpansionNestedLiteral seed = true

abbrev prop_brace_expansion_range : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    braceExpansionRangeIsExpansion seed = true

abbrev prop_extglob_splits : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    extglobSplits seed = true

abbrev prop_extglob_bracket_pipe : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    extglobBracketKeepsPipe seed = true

abbrev prop_heredoc_unquoted_expands : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    heredocUnquotedExpands seed = true

abbrev prop_heredoc_multiple_expands : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    heredocMultipleExpands seed = true

abbrev prop_heredoc_dashed_expands : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    heredocDashedExpands seed = true

abbrev prop_procsub_escaped_quote : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    procSubEscapedQuote seed = true

abbrev prop_unparsed_index_preserves_content : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    unparsedIndexPreservesContent seed = true

abbrev prop_unquoted_dollar_expands : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    unquotedDollarExpands seed = true

abbrev prop_double_quoted_dollar_expands : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    doubleQuotedDollarExpands seed = true

abbrev prop_single_quoted_dollar_literal : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    singleQuotedDollarLiteral seed = true

abbrev prop_escaped_dollar_literal : Prop :=
  Plausible.NamedBinder "seed" <| ∀ seed : String,
    escapedDollarLiteral seed = true

end ShellCheck.Tests.ParserProps
