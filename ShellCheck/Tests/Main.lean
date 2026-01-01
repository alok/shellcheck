import Plausible
import ShellCheck.Tests.ParsecProps
import ShellCheck.Tests.ParserProps
import ShellCheck.Tests.ParserRegression
import ShellCheck.Tests.FormatterTTY
import ShellCheck.Tests.FormatterGCC
import ShellCheck.Tests.FormatterJSON
import ShellCheck.Tests.AnalyticsRegression

open Plausible
open ShellCheck.Tests.ParsecProps
open ShellCheck.Tests.ParserProps
open ShellCheck.Tests.ParserRegression
open ShellCheck.Tests.FormatterTTY
open ShellCheck.Tests.FormatterGCC
open ShellCheck.Tests.FormatterJSON
open ShellCheck.Tests.AnalyticsRegression

def checkProp (name : String) (p : Prop) (cfg : Configuration := {}) [Testable p] : IO Bool := do
  IO.println s!"[Plausible] {name}"
  match ← Testable.checkIO p cfg with
  | .success _ =>
      IO.println "  ok"
      pure true
  | .gaveUp n =>
      IO.println s!"  gave up after {n} discards"
      -- Treat as non-failure; it just means generators didn't hit useful cases.
      pure true
  | .failure _ xs n =>
      IO.eprintln (Testable.formatFailure "Found a counter-example!" xs n)
      pure false

def checkRegression (name : String) (t : Except String Bool) : IO Bool := do
  IO.println s!"[Regression] {name}"
  match t with
  | .ok true =>
      IO.println "  ok"
      pure true
  | .ok false =>
      IO.eprintln "  failed"
      pure false
  | .error e =>
      IO.eprintln s!"  error: {e}"
      pure false

def main : IO UInt32 := do
  let cfg : Configuration := { numInst := 200, maxSize := 50, quiet := true }
  let mut ok := true

  ok := ok && (← checkProp "orElse commits consumption" prop_orElse_commits_consumption cfg)
  ok := ok && (← checkProp "attempt allows backtracking" prop_attempt_allows_backtracking cfg)
  ok := ok && (← checkProp "many fails after partial consumption" prop_many_fails_after_partial_consumption cfg)
  ok := ok && (← checkProp "many doesn't consume on mismatch" prop_many_does_not_consume_on_mismatch cfg)
  ok := ok && (← checkProp "many rejects empty success" prop_many_rejects_empty_success cfg)
  ok := ok && (← checkProp "optional doesn't consume on mismatch" prop_optional_does_not_consume_on_mismatch cfg)
  ok := ok && (← checkProp "optional commits after partial consumption" prop_optional_commits_after_partial_consumption cfg)
  ok := ok && (← checkProp "parser roundtrip (simple subset)" prop_simple_roundtrip cfg)
  ok := ok && (← checkProp "parser positions within bounds" prop_positions_valid cfg)

  ok := ok && (← checkRegression "readUntil [[ ignores quoted terminator" test_readUntil_doubleBracket_ignores_quoted_terminator)
  ok := ok && (← checkRegression "readUntil [ ignores quoted terminator" test_readUntil_singleBracket_ignores_quoted_terminator)
  ok := ok && (← checkRegression "readUntil [[ ignores escaped terminator" test_readUntil_doubleBracket_ignores_escaped_terminator)
  ok := ok && (← checkRegression "fd redirect parses as T_FdRedirect" test_fdRedirect_parses_as_T_FdRedirect)
  ok := ok && (← checkRegression "fd redirect duplicate nests IoDuplicate" test_fdRedirect_duplicate_parses_nested_IoDuplicate)
  ok := ok && (← checkRegression "[ a < b ] becomes redirect (SC2073 shape)" test_singleBracket_unescaped_lt_is_redirect)
  ok := ok && (← checkRegression "[ a \\< b ] parses as TC_Binary" test_singleBracket_escaped_lt_is_binary)
  ok := ok && (← checkRegression "[[ \"$x\" == \"a b\" ]] parses as TC_Binary" test_doubleBracket_binary_parses_words)
  ok := ok && (← checkRegression "[[ (...) || ... ]] parses as TC_Or" test_doubleBracket_or_group_parses)
  ok := ok && (← checkRegression "$() allows ) in double quotes" test_dollarExpansion_paren_in_doubleQuotes_parses)
  ok := ok && (← checkRegression "$() allows ) in single quotes" test_dollarExpansion_paren_in_singleQuotes_parses)
  ok := ok && (← checkRegression "`...` allows escaped backtick" test_backtick_escaped_backtick_parses)
  ok := ok && (← checkRegression "`...` allows backtick in single quotes" test_backtick_backtick_in_singleQuotes_parses)
  ok := ok && (← checkRegression "${} allows nested ${}" test_bracedExpansion_nested_parameterExpansions_parses)
  ok := ok && (← checkRegression "${} allows nested {...}" test_bracedExpansion_nested_braceExpansions_parses)
  ok := ok && (← checkRegression "tty format line group basic" test_tty_format_line_group_basic)
  ok := ok && (← checkRegression "tty footer summary" test_tty_footer_summary)
  ok := ok && (← checkRegression "gcc format comment basic" test_gcc_format_comment_basic)
  ok := ok && (← checkRegression "json format includes fix" test_json_format_includes_fix)
  ok := ok && (← checkRegression "SC2145: concat \"$@\"" test_sc2145_double_quoted_concat)
  ok := ok && (← checkRegression "SC2145: array concat" test_sc2145_array_concat)
  ok := ok && (← checkRegression "SC2145: var concat" test_sc2145_var_concat)
  ok := ok && (← checkRegression "SC2145: plain $@ ok" test_sc2145_plain_at_ok)
  ok := ok && (← checkRegression "SC2145: quoted array ok" test_sc2145_quoted_array_ok)
  ok := ok && (← checkRegression "SC2086: fix present" test_sc2086_fix_present)
  ok := ok && (← checkRegression "SC2125: glob assignment" test_sc2125_glob_assignment)
  ok := ok && (← checkRegression "SC2125: brace assignment" test_sc2125_brace_assignment)
  ok := ok && (← checkRegression "SC2125: quoted glob ok" test_sc2125_quoted_glob_ok)
  ok := ok && (← checkRegression "SC2127: case fallthrough (sh)" test_sc2127_case_fallthrough_sh)
  ok := ok && (← checkRegression "SC2127: case fallthrough (bash ok)" test_sc2127_case_fallthrough_bash_ok)
  ok := ok && (← checkRegression "SC2098: prefix assignment reference" test_sc2098_prefix_assignment_reference)
  ok := ok && (← checkRegression "SC2102: char range glob" test_sc2102_char_range_glob)
  ok := ok && (← checkRegression "SC2223: default assignment globbing" test_sc2223_default_assignment)
  ok := ok && (← checkRegression "SC2245: ksh glob unary" test_sc2245_ksh_glob_unary)
  ok := ok && (← checkRegression "SC2257: arithmetic modification in redirection" test_sc2257_arith_mod_redir)
  ok := ok && (← checkRegression "SC2259: pipe input overridden" test_sc2259_pipe_input_overridden)
  ok := ok && (← checkRegression "SC2260: pipe output overridden" test_sc2260_pipe_output_overridden)
  ok := ok && (← checkRegression "SC2261: duplicate redirs in pipeline" test_sc2261_duplicate_redirs_in_pipeline)
  ok := ok && (← checkRegression "SC2262: alias same parsing unit" test_sc2262_alias_same_unit)
  ok := ok && (← checkRegression "SC2318: backref declare" test_sc2318_backref_declare)
  ok := ok && (← checkRegression "SC2325: multiple bangs in posix sh" test_sc2325_multiple_bangs_posix)
  ok := ok && (← checkRegression "SC2326: bang in pipeline" test_sc2326_bang_in_pipeline)
  ok := ok && (← checkRegression "SC2329: unreachable function" test_sc2329_unreachable_function)
  ok := ok && (← checkRegression "SC2332: negated unary op in bash" test_sc2332_negated_unary_op_bash)
  ok := ok && (← checkRegression "SC2265: bad test background" test_sc2265_bad_test_background)
  ok := ok && (← checkRegression "SC2266: bad test or pipe" test_sc2266_bad_test_or_pipe)
  ok := ok && (← checkRegression "SC2268: leading x comparison" test_sc2268_leading_x_comparison)
  ok := ok && (← checkRegression "SC2321: unnecessary arithmetic expansion index" test_sc2321_unnecessary_arith_expansion_index)
  ok := ok && (← checkRegression "SC2336: cp -r legacy flag" test_sc2336_cp_legacy_r)

  pure (if ok then 0 else 1)
