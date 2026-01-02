import Plausible
import ShellCheck.Tests.AnalyticsRegression

namespace ShellCheck.Tests.SCCoverage

open ShellCheck.Interface
open ShellCheck.Tests.AnalyticsRegression

set_option maxRecDepth 2048

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
  { code := 2000, script := "echo $foo | wc -c" },
  { code := 2002, script := "cat file | grep foo" },
  { code := 2004, script := "echo $(( ${foo} + 1 ))" },
  { code := 2005, script := "echo $(date)" },
  { code := 2006, script := "echo `date`" },
  { code := 2007, script := "echo $[1+2]" },
  { code := 2009, script := "ps aux | grep foo" },
  { code := 2010, script := "ls | grep foo" },
  { code := 2011, script := "ls | xargs rm" },
  { code := 2013, script := "for i in $(cat file); do echo $i; done" },
  { code := 2015, script := "true && false || echo hi" },
  { code := 2016, script := "echo 'foo $bar'" },
  { code := 2017, script := "echo $((a / b * c))" },
  { code := 2028, script := "echo 'foo\\nbar'" },
  { code := 2037, script := "var=ls -l" },
  { code := 2078, script := "[ foo ]" },
  { code := 2086, script := "echo $foo" },
  { code := 2098, script := "var=foo echo ${var}" },
  { code := 2102, script := "ls [10-15]" },
  { code := 2103, script := "for f in *; do cd $f; git pull; cd ..; done" },
  { code := 2120, script := "f() { echo \"$1\"; }\nf" },
  { code := 2125, script := "a=*.png" },
  { code := 2127, script := "case foo in bar) echo hi ;& baz) echo ok ;; esac", shell := some .Sh },
  { code := 2145, script := "echo \"foo$@\"" },
  { code := 2155, script := "f() { local \"$(false)\"; }\nf", shell := some .Bash },
  { code := 2157, script := "test -z \"foo\"" },
  { code := 2198, script := "arr=(a b); [[ ${arr[@]} ]]", shell := some .Bash },
  { code := 2215, script := "-e file" },
  { code := 2223, script := ": ${var:=*}", extended := true },
  { code := 2234, script := "( [ -f foo ] )" },
  { code := 2239, script := "#!bash\necho hi" },
  { code := 2245, script := "[ -d foo* ]", shell := some .Ksh },
  { code := 2257, script := "echo hi > $((i++))" },
  { code := 2259, script := "echo foo | cat < input" },
  { code := 2260, script := "echo foo > out | cat" },
  { code := 2261, script := "echo foo > a > b | cat" },
  { code := 2262, script := "alias x=y; x" },
  { code := 2265, script := "[ x ] & [ y ]" },
  { code := 2266, script := "[ x ] | [ y ]" },
  { code := 2268, script := "[ x$foo = xlol ]" },
  { code := 2281, script := "$var=foo" },
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

def sc3xxxCases : List CoverageCase := [
  { code := 3001, script := "cat <(echo hi)", shell := some .Sh },
  { code := 3002, script := "echo @(foo|bar)", shell := some .Sh },
  { code := 3003, script := "echo $'hi'", shell := some .Sh },
  { code := 3004, script := "echo $\"hi\"", shell := some .Sh },
  { code := 3005, script := "for ((i=0;i<1;i++)); do echo $i; done", shell := some .Sh },
  { code := 3006, script := "((i++))", shell := some .Sh },
  { code := 3007, script := "echo $[1+1]", shell := some .Sh },
  { code := 3008, script := "select x in a b; do echo $x; break; done", shell := some .Sh },
  { code := 3009, script := "echo {1..3}", shell := some .Sh },
  { code := 3010, script := "if [[ -n \"$x\" ]]; then echo ok; fi", shell := some .Sh },
  { code := 3011, script := "cat <<< \"hi\"", shell := some .Sh },
  { code := 3019, script := "echo $((2**3))", shell := some .Sh },
  { code := 3020, script := "echo hi &> out", shell := some .Sh },
  { code := 3021, script := "echo hi >& out", shell := some .Sh },
  { code := 3022, script := "exec {fd}>out", shell := some .Sh },
  { code := 3023, script := "exec 10>out", shell := some .Sh },
  { code := 3024, script := "foo+=1", shell := some .Sh },
  { code := 3025, script := "echo hi >/dev/tcp/localhost/80", shell := some .Sh },
  { code := 3026, script := "echo [^a]", shell := some .Sh },
  { code := 3028, script := "echo $BASH_SOURCE", shell := some .Sh },
  { code := 3029, script := "echo hi |& cat", shell := some .Sh },
  { code := 3030, script := "arr=(a b)", shell := some .Sh },
  { code := 3031, script := "echo hi > *.txt", shell := some .Sh },
  { code := 3032, script := "coproc sleep 1", shell := some .Sh },
  { code := 3033, script := "foo-bar() { :; }", shell := some .Sh },
  { code := 3034, script := "echo $(<foo)", shell := some .Sh },
  { code := 3035, script := "echo `</etc/hosts`", shell := some .Sh },
  { code := 3036, script := "echo -e hi", shell := some .Dash },
  { code := 3037, script := "echo -e hi", shell := some .Sh },
  { code := 3038, script := "exec -a foo", shell := some .Sh },
  { code := 3039, script := "let x=1", shell := some .Sh },
  { code := 3040, script := "set -o foobar", shell := some .Sh },
  { code := 3041, script := "set -z", shell := some .Sh },
  { code := 3042, script := "set --foo", shell := some .Sh },
  { code := 3043, script := "local x=1", shell := some .Sh },
  { code := 3044, script := "declare x=1", shell := some .Sh },
  { code := 3045, script := "read -a foo", shell := some .Sh },
  { code := 3046, script := "source foo", shell := some .Sh },
  { code := 3047, script := "trap 'echo hi' ERR", shell := some .Sh },
  { code := 3048, script := "trap 'echo hi' SIGINT", shell := some .Sh },
  { code := 3049, script := "trap 'echo hi' sigint", shell := some .Sh },
  { code := 3050, script := "printf '%q' foo", shell := some .Sh },
  { code := 3052, script := "echo $((16#ff))", shell := some .Sh },
  { code := 3053, script := "echo ${!foo}", shell := some .Sh },
  { code := 3054, script := "echo ${arr[1]}", shell := some .Sh },
  { code := 3055, script := "echo ${!arr[@]}", shell := some .Sh },
  { code := 3056, script := "echo ${!foo*}", shell := some .Sh },
  { code := 3057, script := "echo ${foo:1:2}", shell := some .Sh },
  { code := 3058, script := "echo ${@%foo}", shell := some .Sh },
  { code := 3059, script := "echo ${foo^}", shell := some .Sh },
  { code := 3060, script := "echo ${foo/foo/bar}", shell := some .Sh },
  { code := 3061, script := "read", shell := some .Sh },
  { code := 3062, script := "test -o noclobber", shell := some .Sh },
  { code := 3063, script := "test -R file", shell := some .Sh },
  { code := 3064, script := "test -N file", shell := some .Sh },
  { code := 3065, script := "test -k file", shell := some .Sh },
  { code := 3066, script := "test -G file", shell := some .Sh },
  { code := 3067, script := "test -O file", shell := some .Sh }
]

def sc3xxxFailures : List CoverageCase :=
  sc3xxxCases.filter (fun c => !runCase c)

abbrev prop_sc2xxx_coverage : Prop :=
  sc2xxxFailures.isEmpty = true

abbrev prop_sc3xxx_coverage : Prop :=
  sc3xxxFailures.isEmpty = true

def test_sc2xxx_coverage : Except String Bool := do
  let failures := sc2xxxFailures
  if failures.isEmpty then
    pure true
  else
    let codes := failures.map (fun c => toString c.code)
    .error s!"Missing SC2xxx coverage: {String.intercalate ", " codes}"

def test_sc3xxx_coverage : Except String Bool := do
  let failures := sc3xxxFailures
  if failures.isEmpty then
    pure true
  else
    let codes := failures.map (fun c => toString c.code)
    .error s!"Missing SC3xxx coverage: {String.intercalate ", " codes}"

end ShellCheck.Tests.SCCoverage
