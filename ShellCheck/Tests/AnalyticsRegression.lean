import ShellCheck.Checker
import ShellCheck.Interface

namespace ShellCheck.Tests.AnalyticsRegression

open ShellCheck.Checker
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

def test_sc2125_glob_assignment : Except String Bool := do
  let cr := runCheck "a=*.png"
  pure (hasCode cr 2125)

def test_sc2125_brace_assignment : Except String Bool := do
  let cr := runCheck "a={1..10}"
  pure (hasCode cr 2125)

def test_sc2125_quoted_glob_ok : Except String Bool := do
  let cr := runCheck "a='*.gif'"
  pure (!hasCode cr 2125)

end ShellCheck.Tests.AnalyticsRegression
