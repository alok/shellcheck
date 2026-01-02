import ShellCheck.Checker
import ShellCheck.Interface

namespace ShellCheck.Tests.AnalyticsRegression

open ShellCheck.Checker
open ShellCheck.Data
open ShellCheck.Interface

def idSystemInterface : SystemInterface Id := {
  siReadFile := fun _ _ => .error "no file access"
  siFindSource := fun _ _ _ name => name
  siGetConfig := fun _ => none
}

def runCheck (script : String) : CheckResult :=
  let spec : CheckSpec := {
    csFilename := "<test>"
    csScript := script
    csCheckSourced := false
    csIgnoreRC := true
    csExcludedWarnings := []
    csIncludedWarnings := none
    csShellTypeOverride := none
    csMinSeverity := .styleC
    csExtendedAnalysis := none
    csOptionalChecks := []
  }
  checkScript idSystemInterface spec

def runCheckWithShell (shell : Shell) (script : String) : CheckResult :=
  let spec : CheckSpec := {
    csFilename := "<test>"
    csScript := script
    csCheckSourced := false
    csIgnoreRC := true
    csExcludedWarnings := []
    csIncludedWarnings := none
    csShellTypeOverride := some shell
    csMinSeverity := .styleC
    csExtendedAnalysis := none
    csOptionalChecks := []
  }
  checkScript idSystemInterface spec

def runCheckWithExtended (script : String) : CheckResult :=
  let spec : CheckSpec := {
    csFilename := "<test>"
    csScript := script
    csCheckSourced := false
    csIgnoreRC := true
    csExcludedWarnings := []
    csIncludedWarnings := none
    csShellTypeOverride := none
    csMinSeverity := .styleC
    csExtendedAnalysis := some true
    csOptionalChecks := []
  }
  checkScript idSystemInterface spec

def runCheckWithShellExtended (shell : Shell) (script : String) : CheckResult :=
  let spec : CheckSpec := {
    csFilename := "<test>"
    csScript := script
    csCheckSourced := false
    csIgnoreRC := true
    csExcludedWarnings := []
    csIncludedWarnings := none
    csShellTypeOverride := some shell
    csMinSeverity := .styleC
    csExtendedAnalysis := some true
    csOptionalChecks := []
  }
  checkScript idSystemInterface spec

def hasCode (cr : CheckResult) (code : Int) : Bool :=
  cr.crComments.any (fun c => c.pcComment.cCode == code)

def findComment (cr : CheckResult) (code : Int) : Option PositionedComment :=
  cr.crComments.find? (fun c => c.pcComment.cCode == code)

def hasFix (cr : CheckResult) (code : Int) : Bool :=
  match findComment cr code with
  | some c => c.pcFix.isSome
  | none => false

def test_sc2145_double_quoted_concat : Except String Bool := do
  let cr := runCheck "echo \"foo$@\""
  pure (hasCode cr 2145)

def test_sc2145_array_concat : Except String Bool := do
  let cr := runCheck "echo ${arr[@]}lol"
  pure (hasCode cr 2145)

def test_sc2145_var_concat : Except String Bool := do
  let cr := runCheck "echo $a$@"
  pure (hasCode cr 2145)

def test_sc2145_plain_at_ok : Except String Bool := do
  let cr := runCheck "echo $@"
  pure (!hasCode cr 2145)

def test_sc2145_quoted_array_ok : Except String Bool := do
  let cr := runCheck "echo \"${arr[@]}\""
  pure (!hasCode cr 2145)

def test_sc2086_fix_present : Except String Bool := do
  let cr := runCheck "echo $foo"
  pure (hasFix cr 2086)

def test_sc2089_quotes_literal_warn : Except String Bool := do
  let cr := runCheck "param='--foo=\"bar\"'; app $param"
  pure (hasCode cr 2089)

def test_sc2090_quotes_literal_warn : Except String Bool := do
  let cr := runCheck "param='--foo=\"bar\"'; app $param"
  pure (hasCode cr 2090)

def test_sc2089_sc2090_quoted_ok : Except String Bool := do
  let cr := runCheck "param='--foo=\"bar\"'; app \"$param\""
  pure (!hasCode cr 2089 && !hasCode cr 2090)

def test_sc2005_useless_echo_subst : Except String Bool := do
  let cr := runCheck "echo $(date)"
  pure (hasCode cr 2005)

def test_sc2005_useless_echo_backticks : Except String Bool := do
  let cr := runCheck "echo `date`"
  pure (hasCode cr 2005)

def test_sc2005_useless_echo_quoted_subst : Except String Bool := do
  let cr := runCheck "echo \"$(date)\""
  pure (hasCode cr 2005)

def test_sc2005_useless_echo_quoted_backticks : Except String Bool := do
  let cr := runCheck "echo \"`date`\""
  pure (hasCode cr 2005)

def test_sc2005_useless_echo_mixed_text_ok : Except String Bool := do
  let cr := runCheck "echo \"The time is $(date)\""
  pure (!hasCode cr 2005)

def test_sc2005_useless_echo_redir_only_ok : Except String Bool := do
  let cr := runCheck "echo \"$(<file)\""
  pure (!hasCode cr 2005)

def test_sc2002_uuoc_cat_pipe : Except String Bool := do
  let cr := runCheck "cat foo | grep bar"
  pure (hasCode cr 2002)

def test_sc2009_ps_grep : Except String Bool := do
  let cr := runCheck "ps aux | grep foo"
  pure (hasCode cr 2009)

def test_sc2010_ls_grep : Except String Bool := do
  let cr := runCheck "ls | grep foo"
  pure (hasCode cr 2010)

def test_sc2011_ls_xargs : Except String Bool := do
  let cr := runCheck "ls | xargs rm"
  pure (hasCode cr 2011)

def test_sc2038_find_xargs_missing_null : Except String Bool := do
  let cr := runCheck "find . | xargs foo"
  pure (hasCode cr 2038)

def test_sc2038_find_xargs_null_ok : Except String Bool := do
  let cr := runCheck "find . -print0 | xargs -0 foo"
  pure (!hasCode cr 2038)

def test_sc2126_grep_wc : Except String Bool := do
  let cr := runCheck "grep foo file | wc -l"
  pure (hasCode cr 2126)

def test_sc2126_grep_wc_ok : Except String Bool := do
  let cr := runCheck "grep -c foo file"
  pure (!hasCode cr 2126)

def test_sc2018_tr_lower_class : Except String Bool := do
  let cr := runCheck "tr a-z A-Z"
  pure (hasCode cr 2018)

def test_sc2019_tr_upper_class : Except String Bool := do
  let cr := runCheck "tr a-z A-Z"
  pure (hasCode cr 2019)

def test_sc2020_tr_duplicates : Except String Bool := do
  let cr := runCheck "tr aa bb"
  pure (hasCode cr 2020)

def test_sc2021_tr_bracket_class : Except String Bool := do
  let cr := runCheck "tr '[a]' b"
  pure (hasCode cr 2021)

def test_sc2060_tr_unquoted_glob : Except String Bool := do
  let cr := runCheck "tr * a"
  pure (hasCode cr 2060)

def test_sc2125_glob_assignment : Except String Bool := do
  let cr := runCheck "a=*.png"
  pure (hasCode cr 2125)

def test_sc2125_brace_assignment : Except String Bool := do
  let cr := runCheck "a={1..10}"
  pure (hasCode cr 2125)

def test_sc2125_quoted_glob_ok : Except String Bool := do
  let cr := runCheck "a='*.gif'"
  pure (!hasCode cr 2125)

def test_sc2127_case_fallthrough_sh : Except String Bool := do
  let cr := runCheckWithShell .Sh "case foo in bar) echo hi ;& baz) echo ok ;; esac"
  pure (hasCode cr 2127)

def test_sc2127_case_fallthrough_bash_ok : Except String Bool := do
  let cr := runCheckWithShell .Bash "case foo in bar) echo hi ;& baz) echo ok ;; esac"
  pure (!hasCode cr 2127)

def test_sc2098_prefix_assignment_reference : Except String Bool := do
  let cr := runCheck "var=foo echo ${var}"
  pure (hasCode cr 2098)

def test_sc2102_char_range_glob : Except String Bool := do
  let cr := runCheck "ls [10-15]"
  pure (hasCode cr 2102)

def test_sc2103_cd_and_back : Except String Bool := do
  let cr := runCheck "for f in *; do cd $f; git pull; cd ..; done"
  pure (hasCode cr 2103)

def test_sc2103_set_e_ok : Except String Bool := do
  let cr := runCheck "set -e; for dir in */; do cd \"$dir\"; some_cmd; cd ..; done"
  pure (!hasCode cr 2103)

def test_sc2215_flag_as_command : Except String Bool := do
  let cr := runCheck "-e file"
  pure (hasCode cr 2215)

def test_sc2215_quoted_flag_ok : Except String Bool := do
  let cr := runCheck "'--myexec--' args"
  pure (!hasCode cr 2215)

def test_sc2286_empty_command : Except String Bool := do
  let cr := runCheck "\"\""
  pure (hasCode cr 2286)

def test_sc2287_trailing_slash_command : Except String Bool := do
  let cr := runCheck "/foo/ bar"
  pure (hasCode cr 2287)

def test_sc2288_trailing_symbol_command : Except String Bool := do
  let cr := runCheck "foo, bar"
  pure (hasCode cr 2288)

def test_sc2289_tab_in_command : Except String Bool := do
  let cr := runCheck "$'foo\tbar' baz"
  pure (hasCode cr 2289)

def test_sc2223_default_assignment : Except String Bool := do
  let cr := runCheckWithExtended ": ${var:=*}"
  pure (hasCode cr 2223)

def test_sc2245_ksh_glob_unary : Except String Bool := do
  let cr := runCheckWithShell .Ksh "[ -d foo* ]"
  pure (hasCode cr 2245)

def test_sc2257_arith_mod_redir : Except String Bool := do
  let cr := runCheck "echo hi > $((i++))"
  pure (hasCode cr 2257)

def test_sc2259_pipe_input_overridden : Except String Bool := do
  let cr := runCheck "echo foo | cat < input"
  pure (hasCode cr 2259)

def test_sc2260_pipe_output_overridden : Except String Bool := do
  let cr := runCheck "echo foo > out | cat"
  pure (hasCode cr 2260)

def test_sc2261_duplicate_redirs_in_pipeline : Except String Bool := do
  let cr := runCheck "echo foo > a > b | cat"
  pure (hasCode cr 2261)

def test_sc2262_alias_same_unit : Except String Bool := do
  let cr := runCheck "alias x=y; x"
  pure (hasCode cr 2262)

def test_sc2318_backref_declare : Except String Bool := do
  let cr := runCheckWithShell .Bash "declare x=1 y=$x"
  pure (hasCode cr 2318)

def test_sc2325_multiple_bangs_posix : Except String Bool := do
  let cr := runCheckWithShell .Sh "! ! true"
  pure (hasCode cr 2325)

def test_sc2326_bang_in_pipeline : Except String Bool := do
  let cr := runCheckWithShell .Sh "true | ! true"
  pure (hasCode cr 2326)

def test_sc2329_unreachable_function : Except String Bool := do
  let cr := runCheckWithExtended "f() { echo hi; }; exit"
  pure (hasCode cr 2329)

def test_sc2332_negated_unary_op_bash : Except String Bool := do
  let cr := runCheckWithShell .Bash "[ ! -o braceexpand ]"
  pure (hasCode cr 2332)

def test_sc2265_bad_test_background : Except String Bool := do
  let cr := runCheck "[ x ] & [ y ]"
  pure (hasCode cr 2265)

def test_sc2266_bad_test_or_pipe : Except String Bool := do
  let cr := runCheck "[ x ] | [ y ]"
  pure (hasCode cr 2266)

def test_sc2268_leading_x_comparison : Except String Bool := do
  let cr := runCheck "[ x$foo = xlol ]"
  pure (hasCode cr 2268)

def test_sc2321_unnecessary_arith_expansion_index : Except String Bool := do
  let cr := runCheck "a[$((1+1))]=n"
  pure (hasCode cr 2321)

def test_sc2336_cp_legacy_r : Except String Bool := do
  let cr := runCheck "cp -r foo bar"
  pure (hasCode cr 2336)

def test_sc3053_indirect_expansion_busybox : Except String Bool := do
  let cr := runCheckWithShell .BusyboxSh "x='test'\necho ${!x}"
  pure (hasCode cr 3053)

def test_sc3054_array_reference_busybox : Except String Bool := do
  let cr := runCheckWithShell .BusyboxSh "x='test'\necho ${x[1]}"
  pure (hasCode cr 3054)

def test_sc3055_array_key_expansion_busybox : Except String Bool := do
  let cr := runCheckWithShell .BusyboxSh "x='test'\necho ${!x[@]}"
  pure (hasCode cr 3055)

def test_sc3056_name_prefix_expansion_busybox : Except String Bool := do
  let cr := runCheckWithShell .BusyboxSh "xyz=1\necho ${!x*}"
  pure (hasCode cr 3056)

def test_sc3057_string_indexing_dash : Except String Bool := do
  let cr := runCheckWithShell .Dash "x='test'\necho ${x:0:3}"
  pure (hasCode cr 3057)

def test_sc3057_string_indexing_busybox_ok : Except String Bool := do
  let cr := runCheckWithShell .BusyboxSh "x='test'\necho ${x:0:3}"
  pure (!hasCode cr 3057)

def test_sc3059_case_modification_busybox : Except String Bool := do
  let cr := runCheckWithShell .BusyboxSh "x='test'\necho ${x^^[t]}"
  pure (hasCode cr 3059)

def test_sc3060_string_replacement_dash : Except String Bool := do
  let cr := runCheckWithShell .Dash "x='test'\necho ${x/st/xt}"
  pure (hasCode cr 3060)

def test_sc3060_string_replacement_busybox_ok : Except String Bool := do
  let cr := runCheckWithShell .BusyboxSh "x='test'\necho ${x/st/xt}"
  pure (!hasCode cr 3060)

end ShellCheck.Tests.AnalyticsRegression
