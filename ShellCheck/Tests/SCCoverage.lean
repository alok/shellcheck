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

def mkCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script }

def mkShCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script, shell := some .Sh }

def mkBashCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script, shell := some .Bash }

def mkKshCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script, shell := some .Ksh }

def mkDashCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script, shell := some .Dash }

def mkExtCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script, extended := true }

def mkShExtCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script, shell := some .Sh, extended := true }

def mkBashExtCase (code : Int) (script : String) : CoverageCase :=
  { code := code, script := script, shell := some .Bash, extended := true }

def runCase (c : CoverageCase) : Bool :=
  let cr :=
    match c.shell, c.extended with
    | none, false => runCheck c.script
    | some sh, false => runCheckWithShell sh c.script
    | none, true => runCheckWithExtended c.script
    | some sh, true => runCheckWithShellExtended sh c.script
  hasCode cr c.code

def sc1xxxCases : List CoverageCase := [
  mkCase 1005 "echo $((1+2)",
  mkCase 1072 "echo 'foo",
  mkCase 1082 "\u{FEFF}echo hi",
  mkCase 1017 "echo hi\r\n",
  mkCase 1018 "echo\u{00A0}hi",
  mkCase 1100 "echo \u{2013}n hi",
  mkCase 1110 "echo \u{201C}hi\u{201D}"
]

def sc1xxxFailures : List CoverageCase :=
  sc1xxxCases.filter (fun c => !runCase c)

def sc2xxxCases : List CoverageCase := [
  mkCase 2000 "echo $foo | wc -c",
  mkCase 2002 "cat file | grep foo",
  mkCase 2004 "echo $(( ${foo} + 1 ))",
  mkCase 2005 "echo $(date)",
  mkCase 2006 "echo `date`",
  mkCase 2007 "echo $[1+2]",
  mkCase 2008 "cat foo | echo bar",
  mkCase 2009 "ps aux | grep foo",
  mkCase 2010 "ls | grep foo",
  mkCase 2011 "ls | xargs rm",
  mkCase 2013 "for i in $(cat file); do echo $i; done",
  mkCase 2015 "true && false || echo hi",
  mkCase 2016 "echo 'foo $bar'",
  mkCase 2017 "echo $((a / b * c))",
  mkCase 2028 "echo 'foo\\nbar'",
  mkCase 2037 "var=ls -l",
  mkShCase 2039 "local foo=1",
  mkShCase 2040 "shopt -s extglob",
  mkCase 2078 "[ foo ]",
  mkCase 2085 "printf %s $(date)",
  mkCase 2086 "echo $foo",
  mkCase 2089 "param='--foo=\"bar\"'; app $param",
  mkCase 2090 "param='--foo=\"bar\"'; app $param",
  mkCase 2098 "var=foo echo ${var}",
  mkCase 2102 "ls [10-15]",
  mkCase 2103 "for f in *; do cd $f; git pull; cd ..; done",
  mkCase 2120 "f() { echo \"$1\"; }\nf",
  mkCase 2125 "a=*.png",
  mkShCase 2127 "case foo in bar) echo hi ;& baz) echo ok ;; esac",
  mkCase 2130 "test foo -eq bar",
  mkCase 2131 "[ foo = bar* ]",
  mkCase 2145 "echo \"foo$@\"",
  mkBashCase 2155 "f() { local \"$(false)\"; }\nf",
  mkCase 2157 "test -z \"foo\"",
  mkDashCase 2169 "source foo",
  mkBashCase 2198 "arr=(a b); [[ ${arr[@]} ]]",
  mkCase 2215 "-e file",
  mkExtCase 2223 ": ${var:=*}",
  mkCase 2234 "( [ -f foo ] )",
  mkCase 2239 "#!bash\necho hi",
  mkKshCase 2245 "[ -d foo* ]",
  mkCase 2257 "echo hi > $((i++))",
  mkCase 2259 "echo foo | cat < input",
  mkCase 2260 "echo foo > out | cat",
  mkCase 2261 "echo foo > a > b | cat",
  mkCase 2262 "alias x=y; x",
  mkCase 2265 "[ x ] & [ y ]",
  mkCase 2266 "[ x ] | [ y ]",
  mkCase 2268 "[ x$foo = xlol ]",
  mkCase 2281 "$var=foo",
  mkCase 2286 "\"\"",
  mkCase 2287 "/foo/ bar",
  mkCase 2288 "foo, bar",
  mkCase 2289 "$'foo\\tbar' baz",
  mkBashCase 2318 "declare x=1 y=$x",
  mkCase 2321 "a[$((1+1))]=n",
  mkShCase 2325 "! ! true",
  mkShCase 2326 "true | ! true",
  mkExtCase 2329 "f() { echo hi; }; exit",
  mkBashCase 2332 "[ ! -o braceexpand ]",
  mkCase 2336 "cp -r foo bar"
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

abbrev prop_sc1xxx_coverage : Prop :=
  sc1xxxFailures.isEmpty = true

abbrev prop_sc2xxx_coverage : Prop :=
  sc2xxxFailures.isEmpty = true

abbrev prop_sc3xxx_coverage : Prop :=
  sc3xxxFailures.isEmpty = true

def test_sc1xxx_coverage : Except String Bool := do
  let failures := sc1xxxFailures
  if failures.isEmpty then
    pure true
  else
    let codes := failures.map (fun c => toString c.code)
    .error s!"Missing SC1xxx coverage: {String.intercalate ", " codes}"

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
