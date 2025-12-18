/-
  ShellCheck DSL for concise check definitions.

  This module provides macros and helpers for defining SC checks
  with minimal boilerplate.
-/

import ShellCheck.AST
import ShellCheck.ASTLib
import ShellCheck.AnalyzerLib
import ShellCheck.Interface

namespace ShellCheck.Checks.DSL

open ShellCheck.AST
open ShellCheck.ASTLib
open ShellCheck.AnalyzerLib
open ShellCheck.Interface

/-!
## Severity Enum with Syntax
-/

/-- Severity levels for checks -/
inductive CheckSeverity where
  | error | warn | style | info
  deriving Repr, BEq, Inhabited

def CheckSeverity.toSeverity : CheckSeverity → Severity
  | .error => .errorC
  | .warn => .warningC
  | .style => .styleC
  | .info => .infoC

/-!
## SC Code Registry

A centralized registry of all SC codes with their metadata.
This enables:
1. Compile-time validation of SC codes
2. Auto-generation of documentation
3. Easy lookup of check descriptions
-/

/-- Metadata for an SC code -/
structure SCCode where
  code : Nat
  severity : CheckSeverity
  message : String
  wiki : Option String := none  -- URL to wiki page
  deriving Repr, Inhabited

/-- SC code ranges -/
def isValidSCCode (n : Nat) : Bool :=
  (n >= 1000 && n < 2000) ||  -- SC1xxx: Parser errors
  (n >= 2000 && n < 3000) ||  -- SC2xxx: Semantic warnings
  (n >= 3000 && n < 4000)     -- SC3xxx: Portability

/-!
## Check Definition Helpers
-/

/-- A stub check that always returns an empty list (for unimplemented checks) -/
def stubCheck (_code : Nat) (_severity : CheckSeverity) (_msg : String) :
    Parameters → Token → List TokenComment :=
  fun _params _t => []

/-- A check that always emits the message for any token -/
def alwaysEmit (code : Nat) (severity : CheckSeverity) (msg : String) :
    Parameters → Token → List TokenComment :=
  fun _params t => [makeComment severity.toSeverity t.id code msg]

/-- Make a simple command check -/
def simpleCommandCheck (commands : List String) (code : Nat) (severity : CheckSeverity)
    (msg : String) (pred : Parameters → Token → Bool) :
    Parameters → Token → List TokenComment :=
  fun params t =>
    match getCommandName t with
    | some name =>
      if commands.contains name && pred params t then
        [makeComment severity.toSeverity t.id code msg]
      else []
    | none => []

/-- Check that warns about specific argument values -/
def argValueCheck (commands : List String) (code : Nat) (severity : CheckSeverity)
    (msg : String) (argPred : String → Bool) :
    Parameters → Token → List TokenComment :=
  fun _params t =>
    match getCommandName t with
    | some name =>
      if commands.contains name then
        match getCommandArgv t with
        | some args =>
          args.filterMap fun arg =>
            match getLiteralString arg with
            | some s => if argPred s then some (makeComment severity.toSeverity arg.id code msg) else none
            | none => none
        | none => []
      else []
    | none => []

/-!
## SC Code Database

All SC codes with their descriptions, organized by category.
These are stubs - actual check logic to be filled in.
-/

/-- SC2xxx codes (semantic warnings) - missing from current implementation -/
def sc2xxxMissing : List SCCode := [
  -- Control flow
  { code := 2007, severity := .warn, message := "Use $((..)) instead of deprecated $((..))" },
  { code := 2019, severity := .info, message := "Use ${var//search/replace} instead of sed" },
  { code := 2021, severity := .warn, message := "Use $ instead of \\$ in strings" },
  { code := 2022, severity := .warn, message := "Note that unlike globs, o* here matches 'ooo' but not 'o'" },
  { code := 2023, severity := .style, message := "Use @Q for shell quoting" },
  { code := 2027, severity := .warn, message := "The function keyword is non-standard. Delete it." },
  { code := 2031, severity := .info, message := "var was modified in a subshell. That change might be lost." },
  { code := 2042, severity := .warn, message := "Use spaces, not commas, to separate loop elements." },
  { code := 2043, severity := .warn, message := "This loop will only ever run once." },
  { code := 2056, severity := .warn, message := "This pattern will never match" },
  { code := 2065, severity := .warn, message := "Use $ instead of \\$ in [[ ]]" },
  { code := 2080, severity := .warn, message := "Use expansion without quotes for numeric operations" },
  { code := 2098, severity := .info, message := "Use $var, not 'var'" },
  { code := 2102, severity := .error, message := "Ranges can only match single chars (not strings)" },
  { code := 2106, severity := .warn, message := "SC2106: This flag is used as a command name" },
  { code := 2113, severity := .error, message := "Use :; instead of ; for empty function body" },
  { code := 2118, severity := .warn, message := "Ksh does not support multidimensional arrays" },
  { code := 2125, severity := .warn, message := "Brace expansions don't work in globs in older shells" },
  { code := 2127, severity := .warn, message := "To expand via indirection, use ${!var}" },
  { code := 2142, severity := .warn, message := "Variables in single quotes won't expand" },
  { code := 2159, severity := .error, message := "[ 0 ] is true. Use 'false' instead." },
  { code := 2168, severity := .error, message := "'local' is only valid in functions." },
  { code := 2170, severity := .warn, message := "Numerical comparison requires integers" },
  { code := 2171, severity := .warn, message := "Found trailing space in arithmetic" },
  { code := 2172, severity := .warn, message := "Trapping signals by number is not portable" },
  { code := 2173, severity := .error, message := "SIGKILL/SIGSTOP can not be trapped" },
  { code := 2175, severity := .warn, message := "Quote to prevent word splitting on command output" },
  { code := 2176, severity := .warn, message := "'time' is undefined after &&/||. Use { ..; }" },
  { code := 2177, severity := .warn, message := "'time' is undefined in composite commands." },
  { code := 2179, severity := .warn, message := "Use array in quotes to avoid expansion issues" },
  { code := 2182, severity := .warn, message := "Variable is used before it's assigned" },
  { code := 2184, severity := .warn, message := "Quote arguments to -exec/-ok to prevent unwanted expansion" },
  { code := 2186, severity := .warn, message := "Tempfile schemes without XXXXXXXXXX are insecure." },
  { code := 2187, severity := .warn, message := "Ash scripts will be checked as Dash." },
  { code := 2188, severity := .error, message := "This redirection doesn't have a command." },
  { code := 2189, severity := .error, message := "You can't have | between this redirection and the command." },
  { code := 2190, severity := .warn, message := "Elements may be concatenated. Quote or use array" },
  { code := 2191, severity := .warn, message := "Bash associative arrays require explicit declare -A" },
  { code := 2193, severity := .warn, message := "Comparison uses numeric mode for string value" },
  { code := 2194, severity := .warn, message := "This expansion will not be treated as number" },
  { code := 2195, severity := .error, message := "Escape '\\!' to prevent history expansion" },
  { code := 2196, severity := .error, message := "egrep is deprecated. Use grep -E." },
  { code := 2197, severity := .error, message := "fgrep is deprecated. Use grep -F." },
  { code := 2198, severity := .warn, message := "Arrays don't work as positional parameters" },
  { code := 2200, severity := .warn, message := "Brace expansions don't work inside globs" },
  { code := 2201, severity := .error, message := "Brace expansion doesn't happen in [[ ]]. Use a loop." },
  { code := 2202, severity := .warn, message := "Globs don't work reliably with ==/!=" },
  { code := 2203, severity := .error, message := "Globs are ignored in [[ ]] except right of =/!=" },
  { code := 2204, severity := .warn, message := "(..) is a subshell. Use { ..; } for grouping" },
  { code := 2205, severity := .warn, message := "(..) is a subshell. Use [[ ]] instead" },
  { code := 2208, severity := .warn, message := "Use [[ ]] or quotes to avoid glob expansion" },
  { code := 2209, severity := .warn, message := "Use var=$(command) to assign output" },
  { code := 2210, severity := .warn, message := "This is a file redirection. Is it intentional?" },
  { code := 2211, severity := .warn, message := "This is a glob. Use [[ ]] or quotes." },
  { code := 2212, severity := .warn, message := "Use 'false' instead of empty [/[[" },
  { code := 2213, severity := .style, message := "getopts specified -n, but it's not handled" },
  { code := 2214, severity := .warn, message := "This pattern has no wildcards. Use = instead." },
  { code := 2215, severity := .warn, message := "This flag is used as a command name" },
  { code := 2216, severity := .warn, message := "Piping to 'cd' has no effect" },
  { code := 2217, severity := .warn, message := "Redirecting to 'cd' has no effect" },
  { code := 2220, severity := .warn, message := "Invalid flags are not handled" },
  { code := 2221, severity := .warn, message := "Ignoring in-place variable" },
  { code := 2222, severity := .warn, message := "Adding the -x flag is recommended" },
  { code := 2223, severity := .warn, message := "This pattern has no special meaning in [ ]" },
  { code := 2224, severity := .error, message := "This mv has no destination. Check arguments" },
  { code := 2225, severity := .error, message := "This cp has no destination. Check arguments" },
  { code := 2226, severity := .warn, message := "This ln has no destination. Check arguments" },
  { code := 2231, severity := .info, message := "Quote this to prevent word splitting" },
  { code := 2232, severity := .warn, message := "Can't run shell builtins with sudo" },
  { code := 2233, severity := .style, message := "Remove superfluous (..) around condition" },
  { code := 2234, severity := .style, message := "Remove superfluous (..) around test command" },
  { code := 2235, severity := .style, message := "Use { ..; } instead of (..) to avoid subshell" },
  { code := 2238, severity := .warn, message := "Redirecting to/from command name instead of file" },
  { code := 2239, severity := .error, message := "Ensure shebang uses an absolute path" },
  { code := 2240, severity := .warn, message := "The dot command does not support arguments in sh/dash" },
  { code := 2241, severity := .error, message := "Exit status can only be 0-255" },
  { code := 2242, severity := .error, message := "Can only exit with status 0-255" },
  { code := 2243, severity := .warn, message := "Prefer printf over echo for special characters" },
  { code := 2245, severity := .warn, message := "Superfluous test after [/[[" },
  { code := 2246, severity := .error, message := "This shebang specifies a directory" },
  { code := 2247, severity := .warn, message := "Flip leading and trailing space in argument" },
  { code := 2249, severity := .info, message := "Consider adding a default case" },
  { code := 2251, severity := .info, message := "This test is always true/false" },
  { code := 2252, severity := .style, message := "Prefer [[ ]] over [ ] in bash/ksh" },
  { code := 2253, severity := .warn, message := "Use -R to recursively copy directories" },
  { code := 2255, severity := .error, message := "[ ] does not apply arithmetic evaluation" },
  { code := 2256, severity := .warn, message := "This path contains tildes that won't expand" },
  { code := 2257, severity := .warn, message := "Arithmetic modification ignored in subshell" },
  { code := 2258, severity := .warn, message := "Use 'in - do' not 'in; do' for reading stdin" },
  { code := 2259, severity := .warn, message := "This does not expand tilde. Use $HOME" },
  { code := 2260, severity := .warn, message := "This command redirects to itself" },
  { code := 2261, severity := .warn, message := "Multiple redirections compete for output" },
  { code := 2262, severity := .warn, message := "This alias definition is never invoked" },
  { code := 2263, severity := .warn, message := "Unsupported to have both stdout and stderr go to different pipes" },
  { code := 2264, severity := .warn, message := "This function only runs as its argument" },
  { code := 2265, severity := .style, message := "Use #!/usr/bin/env bash for portability" },
  { code := 2266, severity := .error, message := "Expected an expression after &&/||" },
  { code := 2267, severity := .warn, message := "GNU xargs -d'\\n' is not portable" },
  { code := 2268, severity := .warn, message := "Avoid non-word characters in variable names" },
  { code := 2269, severity := .info, message := "This variable is assigned to itself" },
  { code := 2270, severity := .warn, message := "To expand '\\t' use $'\\t' or printf" },
  { code := 2271, severity := .warn, message := "For indentation, tabs are more reliable than spaces" },
  { code := 2272, severity := .error, message := "Shell does not support here-string" },
  { code := 2273, severity := .error, message := "This here-doc has mismatched end tokens" },
  { code := 2274, severity := .error, message := "Expected here-doc content on the line after <<" },
  { code := 2275, severity := .error, message := "The delimiter is missing or the function keyword" },
  { code := 2276, severity := .error, message := "This is interpreted as string instead of condition" },
  { code := 2277, severity := .warn, message := "Use 'cd ... || exit' to fail on cd failure" },
  { code := 2278, severity := .warn, message := "VARIABLE+=.. is bash. Use VARIABLE=\"${VARIABLE}..\""  },
  { code := 2279, severity := .warn, message := "VARIABLE[..]=.. is not portable. Use ${VARIABLE%..}.." },
  { code := 2280, severity := .warn, message := "$(<file) is not portable. Use $(cat file)" },
  { code := 2281, severity := .error, message := "Don't use $[$..], use $((..))" },
  { code := 2282, severity := .error, message := "Variable 'for' should not be used as variable" },
  { code := 2283, severity := .warn, message := "Remove trailing ; from case pattern" },
  { code := 2284, severity := .warn, message := "Use [[ $var == pattern ]] without quotes" },
  { code := 2285, severity := .warn, message := "Remove double backslash for literal backslash" },
  { code := 2286, severity := .error, message := "Empty string is interpreted as command name" },
  { code := 2287, severity := .error, message := "Command name ends with '/'. Check syntax" },
  { code := 2288, severity := .warn, message := "This does not concatenate. Use var=\"$var..\"" },
  { code := 2289, severity := .error, message := "Command name contains linefeed/tab" },
  { code := 2290, severity := .warn, message := "Remove spaces around = in variable assignment" },
  { code := 2291, severity := .warn, message := "Use double quotes to prevent glob expansion" },
  { code := 2292, severity := .style, message := "Prefer 'bash -c' over deprecated backticks" },
  { code := 2293, severity := .warn, message := "Var is not in IFS. Use 'read -a' or split manually." },
  { code := 2294, severity := .warn, message := "eval negates the benefit of arrays. Use direct invocation." },
  { code := 2295, severity := .info, message := "Expansions inside ${..} need to be quoted separately, otherwise they match as patterns." },
  { code := 2296, severity := .error, message := "Parameter expansions can't start with (. Check syntax" },
  { code := 2297, severity := .error, message := "Double quotes can't nest. Use \\\" or single quotes inside." },
  { code := 2298, severity := .error, message := "$\"{..}\" is invalid. For ${..} in \"..\", use \"..${..}..\"" },
  { code := 2299, severity := .error, message := "Parameter expansions can't be nested. Use temp vars." },
  { code := 2300, severity := .error, message := "Parameter expansion can't apply to command substitution." },
  { code := 2301, severity := .error, message := "Parameter expansion starts with unexpected character" },
  { code := 2302, severity := .warn, message := "This loops over values. To loop over keys, use \"${!array[@]}\"." },
  { code := 2303, severity := .warn, message := "This is an array value, not a key. Use it directly or loop over keys instead." },
  { code := 2304, severity := .error, message := "* is not a glob. Use regular [ ] to check for files." },
  { code := 2305, severity := .warn, message := "Quote this to prevent word splitting." },
  { code := 2306, severity := .warn, message := "Option delimiters are not portable. Use separate args." },
  { code := 2307, severity := .warn, message := "Sed flag 'i' is non-standard. Use 'I' for GNU sed." },
  { code := 2308, severity := .warn, message := "Neither brace expansion nor globs will work in quotes." },
  { code := 2309, severity := .error, message := "-eq is for comparing integers. Use = for strings." },
  { code := 2310, severity := .info, message := "This function is invoked in a conditional so set -e will be disabled." },
  { code := 2311, severity := .info, message := "Bash implicitly disabled set -e for this function invocation because it's inside a command substitution." },
  { code := 2312, severity := .warn, message := "Consider using dirname \"$path\" instead." },
  { code := 2313, severity := .warn, message := "Consider using basename \"$path\" instead." },
  { code := 2314, severity := .warn, message := "Consider using realpath \"$path\" instead." },
  { code := 2315, severity := .error, message := "In Bats, ! does not cause test failure. Use run/negate." },
  { code := 2316, severity := .warn, message := "This is not a glob. For brace expansion, remove quotes." },
  { code := 2318, severity := .info, message := "This grep option is non-standard." },
  { code := 2319, severity := .info, message := "This command exits with return of last command." },
  { code := 2320, severity := .info, message := "This subshell hides exit code of the commands." },
  { code := 2321, severity := .warn, message := "Line continues in next line and may break syntax." },
  { code := 2322, severity := .error, message := "In [[ ]], always escape regex metacharacters outside (..)." },
  { code := 2323, severity := .warn, message := "Arithmetic compound has no effect." },
  { code := 2324, severity := .warn, message := "read does not split on \\n by default." },
  { code := 2325, severity := .warn, message := "Multiple ! in front of pipelines are a bash/ksh extension." },
  { code := 2326, severity := .warn, message := "This & appears to be unintentional." },
  { code := 2327, severity := .info, message := "This case clause is superseded by a previous one." },
  { code := 2328, severity := .warn, message := "Consider removing this redundant pipeline." },
  { code := 2329, severity := .style, message := "Prefer explicit > /dev/null 2>&1 over &> /dev/null." },
  { code := 2330, severity := .error, message := "BusyBox [[ ]] does not support glob matching." },
  { code := 2331, severity := .warn, message := "=~ regex comparison is not supported in [ ]." },
  { code := 2332, severity := .warn, message := "The shell does not support \\d, \\w etc in regex." },
  { code := 2333, severity := .warn, message := "Remove any here-doc from functions." },
  { code := 2334, severity := .info, message := "Use $ to expand arrays with [@]." },
  { code := 2335, severity := .warn, message := "Command not found. Try without leading dash." },
  { code := 2336, severity := .warn, message := "read in this position only affects subshell." }
]

/-- SC3xxx codes (POSIX portability) - missing from current implementation -/
def sc3xxxMissing : List SCCode := [
  { code := 3002, severity := .warn, message := "In POSIX sh, extglob is not supported." },
  { code := 3004, severity := .warn, message := "In POSIX sh, $'..' is not supported." },
  { code := 3005, severity := .warn, message := "In POSIX sh, arithmetic for loops are not supported." },
  { code := 3007, severity := .warn, message := "In POSIX sh, $ in single quotes is literal." },
  { code := 3008, severity := .warn, message := "In POSIX sh, select is not supported." },
  { code := 3009, severity := .warn, message := "In POSIX sh, &> is not supported." },
  { code := 3012, severity := .warn, message := "In POSIX sh, '\\e' is not a valid escape." },
  { code := 3015, severity := .warn, message := "In POSIX sh, +=  is not supported." },
  { code := 3016, severity := .warn, message := "In POSIX sh, conditional expressions with && and || are not supported." },
  { code := 3017, severity := .warn, message := "In POSIX sh, (( )) is not supported." },
  { code := 3018, severity := .warn, message := "In POSIX sh, process substitution is not supported." },
  { code := 3019, severity := .warn, message := "In POSIX sh, |& is not supported. Use 2>&1 |" },
  { code := 3021, severity := .warn, message := "In POSIX sh, <> redirection is not supported." },
  { code := 3022, severity := .warn, message := "In POSIX sh, ${#arr[@]} is not supported." },
  { code := 3023, severity := .warn, message := "In POSIX sh, ${!var} is not supported." },
  { code := 3024, severity := .warn, message := "In POSIX sh, \"${var[@]}\" is not supported." },
  { code := 3025, severity := .warn, message := "In POSIX sh, ${var/pat/rep} is not supported." },
  { code := 3026, severity := .warn, message := "In POSIX sh, let is not supported." },
  { code := 3028, severity := .warn, message := "In POSIX sh, += is not supported." },
  { code := 3029, severity := .warn, message := "In POSIX sh, herestrings are not supported." },
  { code := 3031, severity := .warn, message := "In POSIX sh, &>> is not supported." },
  { code := 3032, severity := .warn, message := "In POSIX sh, setting PATH for command requires env." },
  { code := 3033, severity := .warn, message := "In POSIX sh, -v is not supported by test." },
  { code := 3034, severity := .warn, message := "In POSIX sh, -a for 'and' is deprecated." },
  { code := 3035, severity := .warn, message := "In POSIX sh, -o for 'or' is deprecated." },
  { code := 3036, severity := .warn, message := "In POSIX sh, echo with backslash escapes is undefined." },
  { code := 3038, severity := .warn, message := "In POSIX sh, \\ continuation in ${..} is undefined." },
  { code := 3039, severity := .warn, message := "In POSIX sh, ${var:start:length} is undefined." },
  { code := 3040, severity := .warn, message := "In POSIX sh, set -o pipefail is undefined." },
  { code := 3041, severity := .warn, message := "In POSIX sh, the errexit option is unreliable." },
  { code := 3042, severity := .warn, message := "In POSIX sh, set -E is undefined." },
  { code := 3043, severity := .warn, message := "In POSIX sh, local is undefined." },
  { code := 3044, severity := .warn, message := "In POSIX sh, declare is undefined." },
  { code := 3045, severity := .warn, message := "In POSIX sh, some sed commands are undefined." },
  { code := 3046, severity := .warn, message := "In POSIX sh, source is undefined. Use dot." },
  { code := 3047, severity := .warn, message := "In POSIX sh, trapping ERR is undefined." },
  { code := 3048, severity := .warn, message := "In POSIX sh, trapping DEBUG is undefined." },
  { code := 3049, severity := .warn, message := "In POSIX sh, trapping RETURN is undefined." },
  { code := 3050, severity := .warn, message := "In POSIX sh, printf %q is undefined." },
  { code := 3051, severity := .warn, message := "In POSIX sh, source is undefined. Use '.'." },
  { code := 3052, severity := .warn, message := "In POSIX sh, read -a is undefined." },
  { code := 3053, severity := .warn, message := "In POSIX sh, read -d is undefined." },
  { code := 3054, severity := .warn, message := "In POSIX sh, read -n is undefined." },
  { code := 3055, severity := .warn, message := "In POSIX sh, read -p is undefined." },
  { code := 3056, severity := .warn, message := "In POSIX sh, read -s is undefined." },
  { code := 3057, severity := .warn, message := "In POSIX sh, read -t is undefined." },
  { code := 3058, severity := .warn, message := "In POSIX sh, read -u is undefined." },
  { code := 3059, severity := .warn, message := "In POSIX sh, string indexing is undefined." },
  { code := 3060, severity := .warn, message := "In POSIX sh, string replacement is undefined." },
  { code := 3061, severity := .warn, message := "In POSIX sh, this word is treated literally." },
  { code := 3062, severity := .warn, message := "In POSIX sh, function is not portable." },
  { code := 3063, severity := .warn, message := "In POSIX sh, command -v is undefined." },
  { code := 3064, severity := .warn, message := "In POSIX sh, disown is undefined." },
  { code := 3065, severity := .warn, message := "In POSIX sh, pushd is undefined." },
  { code := 3066, severity := .warn, message := "In POSIX sh, popd is undefined." },
  { code := 3067, severity := .warn, message := "In POSIX sh, shopt is undefined." }
]

/-- All missing SC codes combined -/
def allMissingSCCodes : List SCCode :=
  sc2xxxMissing ++ sc3xxxMissing

/-!
## Code Lookup Functions
-/

/-- Look up an SC code's metadata -/
def lookupSCCode (code : Nat) : Option SCCode :=
  allMissingSCCodes.find? (·.code == code)

/-- Get the wiki URL for an SC code -/
def getWikiUrl (code : Nat) : String :=
  s!"https://www.shellcheck.net/wiki/SC{code}"

/-- Format an SC code for display -/
def formatSCCode (sc : SCCode) : String :=
  let sev := match sc.severity with
    | .error => "error"
    | .warn => "warning"
    | .style => "style"
    | .info => "info"
  s!"SC{sc.code} [{sev}]: {sc.message}"

/-!
## Bulk Stub Generation
-/

/-- Generate a stub check that logs when hit (for debugging) -/
def mkStubCheck (sc : SCCode) : Parameters → Token → List TokenComment :=
  stubCheck sc.code sc.severity sc.message

/-- Generate all stub checks as a list -/
def allStubChecks : List (Nat × (Parameters → Token → List TokenComment)) :=
  allMissingSCCodes.map fun sc => (sc.code, mkStubCheck sc)

end ShellCheck.Checks.DSL
