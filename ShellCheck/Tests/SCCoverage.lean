import Plausible
import ShellCheck.Tests.AnalyticsRegression

namespace ShellCheck.Tests.SCCoverage

open ShellCheck.Interface
open ShellCheck.Tests.AnalyticsRegression

structure CoverageCase where
  code : Int
  script : String
  shell : Option Shell := none
  extended : Bool := false

def runCase (c : CoverageCase) : Bool :=
  let cr :=
    match c.shell, c.extended with
    | none, false => runCheck c.script
    | some sh, false => runCheckWithShell sh c.script
    | none, true => runCheckWithExtended c.script
    | some sh, true => runCheckWithShellExtended sh c.script
  hasCode cr c.code

def sc2xxxCases : List CoverageCase := [
  { code := 2086, script := "echo $foo" },
  { code := 2098, script := "var=foo echo ${var}" },
  { code := 2102, script := "ls [10-15]" },
  { code := 2103, script := "for f in *; do cd $f; git pull; cd ..; done" },
  { code := 2125, script := "a=*.png" },
  { code := 2127, script := "case foo in bar) echo hi ;& baz) echo ok ;; esac", shell := some .Sh },
  { code := 2145, script := "echo \"foo$@\"" },
  { code := 2215, script := "-e file" },
  { code := 2223, script := ": ${var:=*}", extended := true },
  { code := 2245, script := "[ -d foo* ]", shell := some .Ksh },
  { code := 2257, script := "echo hi > $((i++))" },
  { code := 2259, script := "echo foo | cat < input" },
  { code := 2260, script := "echo foo > out | cat" },
  { code := 2261, script := "echo foo > a > b | cat" },
  { code := 2262, script := "alias x=y; x" },
  { code := 2265, script := "[ x ] & [ y ]" },
  { code := 2266, script := "[ x ] | [ y ]" },
  { code := 2268, script := "[ x$foo = xlol ]" },
  { code := 2286, script := "\"\"" },
  { code := 2287, script := "/foo/ bar" },
  { code := 2288, script := "foo, bar" },
  { code := 2289, script := "$'foo\\tbar' baz" },
  { code := 2318, script := "declare x=1 y=$x", shell := some .Bash },
  { code := 2321, script := "a[$((1+1))]=n" },
  { code := 2325, script := "! ! true", shell := some .Sh },
  { code := 2326, script := "true | ! true", shell := some .Sh },
  { code := 2329, script := "f() { echo hi; }; exit", extended := true },
  { code := 2332, script := "[ ! -o braceexpand ]", shell := some .Bash },
  { code := 2336, script := "cp -r foo bar" }
]

def sc2xxxFailures : List CoverageCase :=
  sc2xxxCases.filter (fun c => !runCase c)

abbrev prop_sc2xxx_coverage : Prop :=
  sc2xxxFailures.isEmpty = true

def test_sc2xxx_coverage : Except String Bool := do
  let failures := sc2xxxFailures
  if failures.isEmpty then
    pure true
  else
    let codes := failures.map (fun c => toString c.code)
    .error s!"Missing SC2xxx coverage: {String.intercalate ", " codes}"

end ShellCheck.Tests.SCCoverage
