import ShellCheck.ASTLib
import ShellCheck.Parser
import ShellCheck.Tests.ParserHelpers

namespace ShellCheck.Tests.ParserRegression

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.Parser
open ShellCheck.Parser.Parsec
open ShellCheck.Tests.ParserHelpers

def parseOnly (p : Parser α) (input : String) : Except String α :=
  match ShellCheck.Parser.Parsec.runExcept p input with
  | .ok (a, _) => .ok a
  | .error e => .error e

def hasNontrivialDollarExpansion (t : Token) : Bool :=
  let scan : StateM Bool Token :=
    ShellCheck.AST.analyze
      (m := StateM Bool)
      (f := fun tok => do
        match tok.inner with
        | .T_DollarExpansion children =>
            let nontrivial :=
              match children with
              | [child] =>
                  match child.inner with
                  | .T_Literal _ => false
                  | _ => true
              | _ => true
            if nontrivial then
              modify (fun _ => true)
            else
              pure ()
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run false
  found

def hasNontrivialBackticked (t : Token) : Bool :=
  let scan : StateM Bool Token :=
    ShellCheck.AST.analyze
      (m := StateM Bool)
      (f := fun tok => do
        match tok.inner with
        | .T_Backticked children =>
            let nontrivial :=
              match children with
              | [child] =>
                  match child.inner with
                  | .T_Literal _ => false
                  | _ => true
              | _ => true
            if nontrivial then
              modify (fun _ => true)
            else
              pure ()
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run false
  found

def firstBracedUseDefaultTriple? (t : Token) : Option (String × String × String) :=
  let scan : StateM (Option (String × String × String)) Token :=
    ShellCheck.AST.analyze
      (m := StateM (Option (String × String × String)))
      (f := fun tok => do
        match tok.inner with
        | .T_DollarBraced true content =>
            match content.inner with
            | .T_NormalWord [a, op, rhs] =>
                match a.inner, op.inner with
                | .T_Literal var, .T_ParamSubSpecialChar opStr =>
                    -- Get the rhs as a string - could be literal or nested expansion
                    let argStr := match rhs.inner with
                      | .T_Literal s => s
                      | .T_DollarBraced true inner =>
                          -- For nested ${x}, reconstruct "${x}"
                          match inner.inner with
                          | .T_NormalWord [lit] =>
                              match lit.inner with
                              | .T_Literal s => s!"$\{{s}}"
                              | _ => "<complex>"
                          | _ => "<complex>"
                      | _ => "<other>"
                    match (← get) with
                    | some _ => pure ()
                    | none => set (some (var, opStr, argStr))
                | _, _ => pure ()
            | _ => pure ()
        | _ => pure ())
      (g := fun _ => pure ())
      (transform := fun tok => pure tok)
      t
  let (_, found) := scan.run none
  found

def parseScriptOk (script : String) : Except String Token :=
  let (root, _positions, errors) := ShellCheck.Parser.runParser script "<test>"
  match root with
  | some t =>
      if errors.isEmpty then
        .ok t
      else
        .error (String.intercalate "\n" errors)
  | none =>
      .error (String.intercalate "\n" errors)

def test_readUntil_doubleBracket_ignores_quoted_terminator : Except String Bool := do
  let p : Parser String := do
    let _ ← pstring "[["
    readUntilString "]]"
  let out ← parseOnly p "[[ \"]]\" ]]"
  pure (out == " \"]]\" ")

def test_readUntil_singleBracket_ignores_quoted_terminator : Except String Bool := do
  let p : Parser String := do
    let _ ← pchar '['
    readUntilString "]"
  let out ← parseOnly p "[ \"]\" ]"
  pure (out == " \"]\" ")

def test_readUntil_doubleBracket_ignores_escaped_terminator : Except String Bool := do
  let p : Parser String := do
    let _ ← pstring "[["
    readUntilString "]]"
  let out ← parseOnly p "[[ \\]] ]]"
  pure (out == " \\]] ")

def test_fdRedirect_parses_as_T_FdRedirect : Except String Bool := do
  let root ← parseScriptOk "echo hi 2>out"
  match root.inner with
  | .T_Script _ cmds =>
      let hasFd2 :=
        cmds.any fun cmd =>
          match cmd.inner with
          | .T_Redirecting redirects _ =>
              redirects.any fun r =>
                match r.inner with
                | .T_FdRedirect fd _ => fd == "2"
                | _ => false
          | _ => false
      pure hasFd2
  | _ => .error "unexpected root token (expected T_Script)"

def test_fdRedirect_duplicate_parses_nested_IoDuplicate : Except String Bool := do
  let root ← parseScriptOk "echo hi 2>&1"
  match root.inner with
  | .T_Script _ cmds =>
      let ok :=
        cmds.any fun cmd =>
          match cmd.inner with
          | .T_Redirecting redirects _ =>
              redirects.any fun r =>
                match r.inner with
                | .T_FdRedirect fd target =>
                    fd == "2" &&
                      match target.inner with
                      | .T_IoDuplicate _ fd2 => fd2 == "1"
                      | _ => false
                | _ => false
          | _ => false
      pure ok
  | _ => .error "unexpected root token (expected T_Script)"

def test_singleBracket_unescaped_lt_is_redirect : Except String Bool := do
  let root ← parseScriptOk "[ a < b ]"
  match root.inner with
  | .T_Script _ cmds =>
      let ok :=
        cmds.any fun cmd =>
          match cmd.inner with
          | .T_Redirecting redirects inner =>
              match inner.inner with
              | .T_Condition .singleBracket _ => !redirects.isEmpty
              | _ => false
          | _ => false
      pure ok
  | _ => .error "unexpected root token (expected T_Script)"

def test_singleBracket_escaped_lt_is_binary : Except String Bool := do
  let root ← parseScriptOk "[ a \\< b ]"
  match root.inner with
  | .T_Script _ cmds =>
      let ok :=
        cmds.any fun cmd =>
          match cmd.inner with
          | .T_Condition .singleBracket expr =>
              match expr.inner with
              | .TC_Binary .singleBracket "<" _ _ => true
              | _ => false
          | _ => false
      pure ok
  | _ => .error "unexpected root token (expected T_Script)"

def test_doubleBracket_binary_parses_words : Except String Bool := do
  let root ← parseScriptOk "[[ \"$x\" == \"a b\" ]]"
  match root.inner with
  | .T_Script _ cmds =>
      let ok :=
        cmds.any fun cmd =>
          match cmd.inner with
          | .T_Condition .doubleBracket expr =>
              match expr.inner with
              | .TC_Binary .doubleBracket "==" _ _ => true
              | _ => false
          | _ => false
      pure ok
  | _ => .error "unexpected root token (expected T_Script)"

def test_doubleBracket_or_group_parses : Except String Bool := do
  let root ← parseScriptOk "[[ ( -z \"$x\" ) || -n \"$y\" ]]"
  match root.inner with
  | .T_Script _ cmds =>
      let ok :=
        cmds.any fun cmd =>
          match cmd.inner with
          | .T_Condition .doubleBracket expr =>
              match expr.inner with
              | .TC_Or .doubleBracket "||" _ _ => true
              | _ => false
          | _ => false
      pure ok
  | _ => .error "unexpected root token (expected T_Script)"

def test_dollarExpansion_paren_in_doubleQuotes_parses : Except String Bool := do
  let root ← parseScriptOk "echo $(echo \")\")"
  pure (hasNontrivialDollarExpansion root)

def test_dollarExpansion_paren_in_singleQuotes_parses : Except String Bool := do
  let root ← parseScriptOk "echo $(echo ')')"
  pure (hasNontrivialDollarExpansion root)

def test_backtick_escaped_backtick_parses : Except String Bool := do
  let root ← parseScriptOk "echo `echo \\`hi\\``"
  pure (hasNontrivialBackticked root)

def test_backtick_backtick_in_singleQuotes_parses : Except String Bool := do
  let root ← parseScriptOk "echo `echo '`'`"
  pure (hasNontrivialBackticked root)

def test_bracedExpansion_nested_parameterExpansions_parses : Except String Bool := do
  let root ← parseScriptOk "echo ${a:-${b}}"
  match firstBracedUseDefaultTriple? root with
  | some (var, op, arg) => pure (var == "a" && op == ":-" && arg == "${b}")
  | none => .error "did not find braced expansion content"

def test_bracedExpansion_nested_braceExpansions_parses : Except String Bool := do
  let root ← parseScriptOk "echo ${a:-{x,y}}"
  match firstBracedUseDefaultTriple? root with
  | some (var, op, arg) => pure (var == "a" && op == ":-" && arg == "{x,y}")
  | none => .error "did not find braced expansion content"

def test_heredoc_unquoted_parses_expansions : Except String Bool := do
  let root ← parseScriptOk "cat <<EOF\n$foo\nEOF\n"
  match firstHereDoc? root with
  | some (.unquoted, content) =>
      pure (content.any hasAnyDollarExpansion)
  | some (.quoted, _) =>
      .error "expected unquoted heredoc"
  | none =>
      .error "did not find heredoc"

def test_heredoc_quoted_skips_expansions : Except String Bool := do
  let root ← parseScriptOk "cat <<'EOF'\n$foo\nEOF\n"
  match firstHereDoc? root with
  | some (.quoted, content) =>
      pure content.isEmpty
  | some (.unquoted, _) =>
      .error "expected quoted heredoc"
  | none =>
      .error "did not find heredoc"

def test_heredoc_multiple_parses : Except String Bool := do
  let root ← parseScriptOk "cat <<EOF1 <<EOF2\n$foo\nEOF1\n$bar\nEOF2\n"
  let docs := collectHereDocs root
  let okCount := docs.length == 2
  let okContent := docs.all (fun (quotedFlag, content) =>
    quotedFlag == .unquoted && content.any hasAnyDollarExpansion)
  pure (okCount && okContent)

def test_heredoc_dashed_strips_tabs : Except String Bool := do
  let root ← parseScriptOk "cat <<-EOF\n\t$foo\n\tEOF\n"
  match firstHereDoc? root with
  | some (.unquoted, content) =>
      pure (content.any hasAnyDollarExpansion)
  | some (.quoted, _) =>
      .error "expected unquoted heredoc"
  | none =>
      .error "did not find heredoc"

def test_braceExpansion_splits_alternatives : Except String Bool := do
  let root ← parseScriptOk "echo {foo,bar}"
  match firstBraceExpansion? root with
  | some parts =>
      let alts := parts.map getLiteralString
      pure (alts == [some "foo", some "bar"])
  | none => .error "did not find brace expansion"

def test_braceExpansion_nested_brace_literal : Except String Bool := do
  let root ← parseScriptOk "echo {a,{b,c}}"
  match firstBraceExpansion? root with
  | some parts =>
      let alts := parts.map getLiteralString
      pure (alts == [some "a", some "{b,c}"])
  | none => .error "did not find brace expansion"

def test_braceExpansion_range_is_expansion : Except String Bool := do
  let root ← parseScriptOk "echo {1..3}"
  match firstBraceExpansion? root with
  | some parts =>
      let alts := parts.map getLiteralString
      pure (alts == [some "1..3"])
  | none => .error "did not find brace expansion"

def test_extglob_splits_alternatives : Except String Bool := do
  let root ← parseScriptOk "echo @(foo|bar)"
  match firstExtglob? root with
  | some (_pattern, parts) =>
      let alts := parts.map getLiteralString
      pure (alts == [some "foo", some "bar"])
  | none => .error "did not find extglob"

def test_extglob_bracket_class_keeps_pipe : Except String Bool := do
  let root ← parseScriptOk "echo @([|]|foo)"
  match firstExtglob? root with
  | some (_pattern, parts) =>
      let alts := parts.map getLiteralString
      pure (alts == [some "[|]", some "foo"])
  | none => .error "did not find extglob"

def test_unparsedIndex_nested_brackets : Except String Bool := do
  let root ← parseScriptOk "arr[x[y]]=1"
  match firstUnparsedIndex? root with
  | some content => pure (content == "x[y]")
  | none => .error "did not find unparsed index"

def test_unparsedIndex_quoted_bracket : Except String Bool := do
  let root ← parseScriptOk "arr[\"a]b\"]=1"
  match firstUnparsedIndex? root with
  | some content => pure (content == "\"a]b\"")
  | none => .error "did not find unparsed index"

def test_procsub_escaped_quote_parses : Except String Bool := do
  let root ← parseScriptOk "cat <(echo \"\\\"\")"
  match firstProcSub? root with
  | some _ => pure true
  | none => .error "did not find procsub"

end ShellCheck.Tests.ParserRegression
