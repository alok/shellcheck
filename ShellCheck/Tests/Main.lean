import LSpec
import Plausible
import ShellCheck.Tests.ParsecProps
import ShellCheck.Tests.ParserProps
import ShellCheck.Tests.ParserRegression
import ShellCheck.Tests.FormatterTTY
import ShellCheck.Tests.FormatterGCC
import ShellCheck.Tests.FormatterJSON
import ShellCheck.Tests.AnalyticsRegression
import ShellCheck.Tests.SCCoverage

open LSpec
open ShellCheck.Tests.ParsecProps
open ShellCheck.Tests.ParserProps
open ShellCheck.Tests.ParserRegression
open ShellCheck.Tests.FormatterTTY
open ShellCheck.Tests.FormatterGCC
open ShellCheck.Tests.FormatterJSON
open ShellCheck.Tests.AnalyticsRegression
open ShellCheck.Tests.SCCoverage

set_option maxRecDepth 2048

structure PropCase where
  name : String
  prop : Prop
  inst : Plausible.Testable prop := by infer_instance

structure RegressionCase where
  name : String
  test : Except String Bool

def plausibleCfg : Plausible.Configuration :=
  { numInst := 200, maxSize := 50, quiet := true }

def runPropCase (cfg : Plausible.Configuration) (c : PropCase) : IO TestSeq := do
  let _ : Plausible.Testable c.prop := c.inst
  let res ← Plausible.Testable.checkIO c.prop cfg
  match res with
  | .success _ =>
      pure (test c.name True)
  | .gaveUp n =>
      IO.eprintln s!"[Plausible] {c.name}: gave up after {n} discards"
      pure (test c.name True)
  | .failure _ xs n =>
      let msg := Plausible.Testable.formatFailure "Found a counter-example!" xs n
      pure (test c.name (ExpectationFailure "success" msg))

def runRegressionCase (c : RegressionCase) : TestSeq :=
  match c.test with
  | .ok true =>
      test c.name True
  | .ok false =>
      test c.name (ExpectationFailure "true" "false")
  | .error e =>
      test c.name (ExpectationFailure "ok true" s!"error {e}")

def propCases : List PropCase := [
  { name := "orElse commits consumption", prop := prop_orElse_commits_consumption },
  { name := "attempt allows backtracking", prop := prop_attempt_allows_backtracking },
  { name := "many fails after partial consumption", prop := prop_many_fails_after_partial_consumption },
  { name := "many doesn't consume on mismatch", prop := prop_many_does_not_consume_on_mismatch },
  { name := "many rejects empty success", prop := prop_many_rejects_empty_success },
  { name := "optional doesn't consume on mismatch", prop := prop_optional_does_not_consume_on_mismatch },
  { name := "optional commits after partial consumption", prop := prop_optional_commits_after_partial_consumption },
  { name := "peekString does not consume input", prop := prop_peekString_does_not_consume },
  { name := "takeWhile1 requires a match", prop := prop_takeWhile1_requires_match },
  { name := "parser roundtrip (simple subset)", prop := prop_simple_roundtrip },
  { name := "parser positions within bounds", prop := prop_positions_valid },
  { name := "parser parses quoting subset", prop := prop_parse_ok_quoted },
  { name := "parser quoted positions within bounds", prop := prop_positions_valid_quoted },
  { name := "parser parses complex script", prop := prop_parse_ok_complex },
  { name := "parser complex positions within bounds", prop := prop_positions_valid_complex },
  { name := "parser parses variant quoting", prop := prop_parse_ok_variants },
  { name := "parser variant positions within bounds", prop := prop_positions_valid_variants },
  { name := "token ids unique (simple)", prop := prop_ids_unique_simple },
  { name := "token ids unique (complex)", prop := prop_ids_unique_complex },
  { name := "token ids unique (variants)", prop := prop_ids_unique_variants },
  { name := "brace expansion splits alternatives", prop := prop_brace_expansion_splits },
  { name := "brace expansion nested braces stay literal", prop := prop_brace_expansion_nested_literal },
  { name := "brace expansion range stays expansion", prop := prop_brace_expansion_range },
  { name := "extglob splits alternatives", prop := prop_extglob_splits },
  { name := "extglob keeps | in bracket class", prop := prop_extglob_bracket_pipe },
  { name := "heredoc unquoted expands", prop := prop_heredoc_unquoted_expands },
  { name := "heredoc multiple expands", prop := prop_heredoc_multiple_expands },
  { name := "heredoc <<- expands", prop := prop_heredoc_dashed_expands },
  { name := "procsub escaped quotes parse", prop := prop_procsub_escaped_quote },
  { name := "unparsed index preserves content", prop := prop_unparsed_index_preserves_content },
  { name := "unquoted $ expands", prop := prop_unquoted_dollar_expands },
  { name := "double-quoted $ expands", prop := prop_double_quoted_dollar_expands },
  { name := "single-quoted $ is literal", prop := prop_single_quoted_dollar_literal },
  { name := "escaped $ is literal", prop := prop_escaped_dollar_literal },
  { name := "SC2xxx coverage cases", prop := prop_sc2xxx_coverage },
  { name := "SC3xxx coverage cases", prop := prop_sc3xxx_coverage }
]

def regressionCases : List RegressionCase := [
  { name := "readUntil [[ ignores quoted terminator", test := test_readUntil_doubleBracket_ignores_quoted_terminator },
  { name := "readUntil [ ignores quoted terminator", test := test_readUntil_singleBracket_ignores_quoted_terminator },
  { name := "readUntil [[ ignores escaped terminator", test := test_readUntil_doubleBracket_ignores_escaped_terminator },
  { name := "fd redirect parses as T_FdRedirect", test := test_fdRedirect_parses_as_T_FdRedirect },
  { name := "fd redirect duplicate nests IoDuplicate", test := test_fdRedirect_duplicate_parses_nested_IoDuplicate },
  { name := "[ a < b ] becomes redirect (SC2073 shape)", test := test_singleBracket_unescaped_lt_is_redirect },
  { name := "[ a \\< b ] parses as TC_Binary", test := test_singleBracket_escaped_lt_is_binary },
  { name := "[[ \"$x\" == \"a b\" ]] parses as TC_Binary", test := test_doubleBracket_binary_parses_words },
  { name := "[[ (...) || ... ]] parses as TC_Or", test := test_doubleBracket_or_group_parses },
  { name := "$() allows ) in double quotes", test := test_dollarExpansion_paren_in_doubleQuotes_parses },
  { name := "$() allows ) in single quotes", test := test_dollarExpansion_paren_in_singleQuotes_parses },
  { name := "`...` allows escaped backtick", test := test_backtick_escaped_backtick_parses },
  { name := "`...` allows backtick in single quotes", test := test_backtick_backtick_in_singleQuotes_parses },
  { name := "$foo expands", test := test_unquoted_dollar_expands },
  { name := "\"$foo\" expands", test := test_double_quoted_dollar_expands },
  { name := "'$foo' is literal", test := test_single_quoted_dollar_literal },
  { name := "\\$foo is literal", test := test_escaped_dollar_literal },
  { name := "${} allows nested ${}", test := test_bracedExpansion_nested_parameterExpansions_parses },
  { name := "${} allows nested {...}", test := test_bracedExpansion_nested_braceExpansions_parses },
  { name := "heredoc unquoted parses expansions", test := test_heredoc_unquoted_parses_expansions },
  { name := "heredoc quoted skips expansions", test := test_heredoc_quoted_skips_expansions },
  { name := "heredoc multiple parses", test := test_heredoc_multiple_parses },
  { name := "heredoc <<- strips tabs", test := test_heredoc_dashed_strips_tabs },
  { name := "brace expansion splits alternatives", test := test_braceExpansion_splits_alternatives },
  { name := "brace expansion keeps nested braces literal", test := test_braceExpansion_nested_brace_literal },
  { name := "brace expansion range is expansion", test := test_braceExpansion_range_is_expansion },
  { name := "extglob splits alternatives", test := test_extglob_splits_alternatives },
  { name := "extglob keeps | in bracket class", test := test_extglob_bracket_class_keeps_pipe },
  { name := "unparsed index nested brackets", test := test_unparsedIndex_nested_brackets },
  { name := "unparsed index quoted bracket", test := test_unparsedIndex_quoted_bracket },
  { name := "procsub handles escaped quote", test := test_procsub_escaped_quote_parses },
  { name := "tty format line group basic", test := test_tty_format_line_group_basic },
  { name := "tty footer summary", test := test_tty_footer_summary },
  { name := "gcc format comment basic", test := test_gcc_format_comment_basic },
  { name := "json format includes fix", test := test_json_format_includes_fix },
  { name := "SC2145: concat \"$@\"", test := test_sc2145_double_quoted_concat },
  { name := "SC2145: array concat", test := test_sc2145_array_concat },
  { name := "SC2145: var concat", test := test_sc2145_var_concat },
  { name := "SC2145: plain $@ ok", test := test_sc2145_plain_at_ok },
  { name := "SC2145: quoted array ok", test := test_sc2145_quoted_array_ok },
  { name := "SC2086: fix present", test := test_sc2086_fix_present },
  { name := "SC2125: glob assignment", test := test_sc2125_glob_assignment },
  { name := "SC2125: brace assignment", test := test_sc2125_brace_assignment },
  { name := "SC2125: quoted glob ok", test := test_sc2125_quoted_glob_ok },
  { name := "SC2127: case fallthrough (sh)", test := test_sc2127_case_fallthrough_sh },
  { name := "SC2127: case fallthrough (bash ok)", test := test_sc2127_case_fallthrough_bash_ok },
  { name := "SC2098: prefix assignment reference", test := test_sc2098_prefix_assignment_reference },
  { name := "SC2102: char range glob", test := test_sc2102_char_range_glob },
  { name := "SC2103: cd and back", test := test_sc2103_cd_and_back },
  { name := "SC2103: set -e ok", test := test_sc2103_set_e_ok },
  { name := "SC2215: flag as command", test := test_sc2215_flag_as_command },
  { name := "SC2215: quoted flag ok", test := test_sc2215_quoted_flag_ok },
  { name := "SC2286: empty command", test := test_sc2286_empty_command },
  { name := "SC2287: trailing slash command", test := test_sc2287_trailing_slash_command },
  { name := "SC2288: trailing symbol command", test := test_sc2288_trailing_symbol_command },
  { name := "SC2289: tab in command", test := test_sc2289_tab_in_command },
  { name := "SC2223: default assignment globbing", test := test_sc2223_default_assignment },
  { name := "SC2245: ksh glob unary", test := test_sc2245_ksh_glob_unary },
  { name := "SC2257: arithmetic modification in redirection", test := test_sc2257_arith_mod_redir },
  { name := "SC2259: pipe input overridden", test := test_sc2259_pipe_input_overridden },
  { name := "SC2260: pipe output overridden", test := test_sc2260_pipe_output_overridden },
  { name := "SC2261: duplicate redirs in pipeline", test := test_sc2261_duplicate_redirs_in_pipeline },
  { name := "SC2262: alias same parsing unit", test := test_sc2262_alias_same_unit },
  { name := "SC2318: backref declare", test := test_sc2318_backref_declare },
  { name := "SC2325: multiple bangs in posix sh", test := test_sc2325_multiple_bangs_posix },
  { name := "SC2326: bang in pipeline", test := test_sc2326_bang_in_pipeline },
  { name := "SC2329: unreachable function", test := test_sc2329_unreachable_function },
  { name := "SC2332: negated unary op in bash", test := test_sc2332_negated_unary_op_bash },
  { name := "SC2265: bad test background", test := test_sc2265_bad_test_background },
  { name := "SC2266: bad test or pipe", test := test_sc2266_bad_test_or_pipe },
  { name := "SC2268: leading x comparison", test := test_sc2268_leading_x_comparison },
  { name := "SC2321: unnecessary arithmetic expansion index", test := test_sc2321_unnecessary_arith_expansion_index },
  { name := "SC2336: cp -r legacy flag", test := test_sc2336_cp_legacy_r },
  { name := "SC3053: indirect expansion (busybox)", test := test_sc3053_indirect_expansion_busybox },
  { name := "SC3054: array reference (busybox)", test := test_sc3054_array_reference_busybox },
  { name := "SC3055: array key expansion (busybox)", test := test_sc3055_array_key_expansion_busybox },
  { name := "SC3056: name prefix expansion (busybox)", test := test_sc3056_name_prefix_expansion_busybox },
  { name := "SC3057: string indexing (dash)", test := test_sc3057_string_indexing_dash },
  { name := "SC3057: string indexing (busybox ok)", test := test_sc3057_string_indexing_busybox_ok },
  { name := "SC3059: case modification (busybox)", test := test_sc3059_case_modification_busybox },
  { name := "SC3060: string replacement (dash)", test := test_sc3060_string_replacement_dash },
  { name := "SC3060: string replacement (busybox ok)", test := test_sc3060_string_replacement_busybox_ok },
  { name := "SC2xxx coverage cases", test := test_sc2xxx_coverage },
  { name := "SC3xxx coverage cases", test := test_sc3xxx_coverage }
]

def main : IO UInt32 := do
  let propSeqs ← propCases.mapM (runPropCase plausibleCfg)
  let regSeqs := regressionCases.map runRegressionCase
  let suites : Std.HashMap String (List TestSeq) :=
    ({} : Std.HashMap String (List TestSeq))
      |>.insert "Plausible" propSeqs
      |>.insert "Regression" regSeqs
  lspecIO suites []
