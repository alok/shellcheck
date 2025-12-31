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

end ShellCheck.Tests.AnalyticsRegression
