/-
  ShellCheck SC1xxx Parser Errors

  These are errors emitted during parsing, not semantic analysis.
  They cover syntax issues, quoting problems, and shell compatibility.
-/

import ShellCheck.Interface

namespace ShellCheck.Checks.ParserErrors

open ShellCheck.Interface

/-!
## Parser Error Registry

All SC1xxx codes with their severity and messages.
These are used by the parser to emit diagnostics.
-/

/-- Parser error metadata -/
structure ParserError where
  code : Nat
  severity : Severity
  message : String
  deriving Repr, Inhabited

/-- Create a parser error with error severity -/
def err (code : Nat) (msg : String) : ParserError :=
  { code := code, severity := .errorC, message := msg }

/-- Create a parser error with warning severity -/
def warn (code : Nat) (msg : String) : ParserError :=
  { code := code, severity := .warningC, message := msg }

/-- Create a parser error with info severity -/
def info (code : Nat) (msg : String) : ParserError :=
  { code := code, severity := .infoC, message := msg }

/-- Create a parser error with style severity -/
def style (code : Nat) (msg : String) : ParserError :=
  { code := code, severity := .styleC, message := msg }

/-!
## SC1xxx Error Definitions

Organized by category for easy navigation.
-/

namespace Escaping
  def sc1000 := err 1000 "$ is not used specially and should therefore be escaped."
  def sc1001 := info 1001 "This \\o will be a regular 'o' in this context."
  def sc1002 := err 1002 "This $\\( is not part of a command substitution."
  def sc1003 := err 1003 "Want to escape a single quote? echo 'This is how it'\\''s done'."
  def sc1004 := warn 1004 "This backslash+linefeed is literal. Break outside single quotes if you just want to break the line."
  def sc1005 := err 1005 "Expected closing paren for arithmetic expression."
  def sc1006 := err 1006 "Expected a glob pattern; got something else."
  def sc1012 := warn 1012 "\\t is just literal 't' here. For tab, use \"$(printf '\\t')\" instead."
  def sc1013 := warn 1013 "Escaped newline in double quotes is not interpreted."
  def sc1117 := info 1117 "Backslash is literal in \"\\n\". Prefer explicit escaping: \"\\\\n\"."
end Escaping

namespace Whitespace
  def sc1007 := err 1007 "Remove space after = if trying to assign a value (or for empty string, use var='' ... )."
  def sc1017 := err 1017 "Literal carriage return. Run script through `tr -d '\\r'`."
  def sc1018 := err 1018 "This is a unicode non-breaking space. Delete it and retype as space."
  def sc1020 := err 1020 "You need a space before the ] or ]]"
  def sc1021 := err 1021 "Can't have a space before the ]."
  def sc1022 := err 1022 "Don't put spaces before the closing bracket."
  def sc1023 := err 1023 "Expected space after redirection."
  def sc1024 := err 1024 "Don't put a space before a here-doc marker."
  def sc1025 := err 1025 "Use single quotes to quote literal strings."
  def sc1027 := err 1027 "Missing argument for operator. Expected a term after comparison."
  def sc1035 := err 1035 "You need a space here"
  def sc1054 := err 1054 "You need a space after the '{'."
  def sc1068 := err 1068 "Don't put spaces around the = in assignments."
  def sc1069 := err 1069 "You need a space before the `[`."
  def sc1095 := err 1095 "You need a space or linefeed between the function name and body."
  def sc1099 := err 1099 "You need a space before the #."
  def sc1101 := err 1101 "Delete trailing spaces after `\\` to break line (or quote for literal space)."
  def sc1108 := err 1108 "You need a space before and after the = ."
  def sc1114 := err 1114 "Remove leading spaces before the shebang."
  def sc1115 := err 1115 "Remove spaces between # and ! in the shebang."
  def sc1118 := err 1118 "Delete whitespace after the here-doc end token."
  def sc1129 := err 1129 "You need a space before the !."
  def sc1130 := err 1130 "You need a space before the :."
end Whitespace

namespace Quoting
  def sc1011 := err 1011 "This apostrophe terminated the single quoted string!"
  def sc1015 := err 1015 "This is a unicode double quote. Delete and retype it."
  def sc1016 := err 1016 "This is a Unicode single quote. Delete and retype it."
  def sc1078 := err 1078 "Did you forget to close this double quoted string?"
  def sc1079 := warn 1079 "This is actually an end quote, but due to next char it looks suspect."
  def sc1110 := err 1110 "This is a unicode quote. Delete and retype it (or quote to make literal)."
  def sc1111 := err 1111 "This is a unicode quote. Delete and retype it (or single-quote for literal)."
  def sc1112 := err 1112 "This is a unicode quote. Delete and retype it (or double-quote for literal)."
end Quoting

namespace TestBrackets
  def sc1019 := err 1019 "Expected this to be an argument to the unary condition."
  def sc1026 := err 1026 "If grouping expressions inside `[[..]]`, use ( .. )."
  def sc1028 := err 1028 "In `[..]` you have to escape `\\(` `\\)` or combine expressions."
  def sc1029 := warn 1029 "In `[[..]]` you shouldn't escape `(` or `)`."
  def sc1030 := err 1030 "Expected a condition to test."
  def sc1031 := err 1031 "Can't compare to empty string with -eq. Use -z."
  def sc1032 := err 1032 "This '>' is a redirection, not a comparison."
  def sc1033 := err 1033 "Test expression opened with `[[` but closed with `]`. Match them."
  def sc1034 := err 1034 "Test expression opened with `[` but closed with `]]`. Match them."
  def sc1080 := warn 1080 "Use `\\\\` before line feeds in `[ ]` to keep parsing."
  def sc1106 := info 1106 "In arithmetic contexts, use `<` instead of `-lt`"
  def sc1139 := err 1139 "Use || instead of '-o' between test commands."
  def sc1140 := err 1140 "Unexpected parameters after condition. Missing &&/||, or bad expression?"
end TestBrackets

namespace Shebang
  def sc1008 := warn 1008 "This shebang was unrecognized. ShellCheck only supports sh/bash/dash/ksh."
  def sc1071 := err 1071 "ShellCheck only supports sh/bash/dash/ksh scripts. Sorry!"
  def sc1082 := err 1082 "This file has a UTF-8 BOM. Remove it with: `LC_CTYPE=C sed '1s/^...//' < script`"
  def sc1084 := err 1084 "Use #!, not !#, for the shebang."
  def sc1104 := err 1104 "Use #!, not just !, for the shebang."
  def sc1113 := err 1113 "Use #!, not just #, for the shebang."
  def sc1128 := err 1128 "The shebang must be on the first line. Delete blanks and move comments."
end Shebang

namespace ControlFlow
  def sc1009 := err 1009 "The mentioned parser error was in ..."
  def sc1010 := err 1010 "Use semicolon or linefeed before 'done' (or quote to make it literal)."
  def sc1014 := err 1014 "Use 'if cmd; then ..' to check exit code, or 'if [ \"$(cmd)\" = .. ]' to check output."
  def sc1045 := err 1045 "It's not 'foo &; bar', just 'foo & bar'."
  def sc1046 := err 1046 "Couldn't find 'fi' for this 'if'."
  def sc1047 := err 1047 "Expected 'fi' matching previously mentioned 'if'."
  def sc1048 := err 1048 "Can't have empty then clauses (use 'true' as a no-op)."
  def sc1049 := err 1049 "Did you forget the 'then' for this 'if'?"
  def sc1050 := err 1050 "Expected 'then'."
  def sc1051 := err 1051 "Semicolons directly after 'then' are not allowed. Just remove it."
  def sc1052 := err 1052 "Semicolons directly after 'then' are not allowed. Just remove it."
  def sc1053 := err 1053 "Semicolons directly after 'else' are not allowed. Just remove it."
  def sc1055 := err 1055 "Need at least one command in the body. Use `true;` as a no-op."
  def sc1057 := err 1057 "Missing 'do' for this loop."
  def sc1058 := err 1058 "Expected `do`."
  def sc1059 := err 1059 "Semicolons directly after 'do' are not allowed. Just remove it."
  def sc1060 := err 1060 "Empty 'do' clause is not allowed. Use `true;` as a no-op."
  def sc1061 := err 1061 "Couldn't find 'done' for this 'do'."
  def sc1062 := err 1062 "Expected 'done' matching previously mentioned 'do'."
  def sc1063 := err 1063 "You need a line feed or semicolon before the 'do'."
  def sc1074 := err 1074 "Did you forget the `;;` after the previous case item?"
  def sc1075 := err 1075 "Use 'elif' instead of 'else if'."
  def sc1076 := err 1076 "Trying to do math? Use [ $((i/2+7)) -ge 18 ] instead."
  def sc1085 := err 1085 "Missing `;;` after extending case item with `;&` or `;;&`."
  def sc1131 := err 1131 "Use `elif` to start another branch."
end ControlFlow

namespace Functions
  def sc1064 := err 1064 "Expected a { to open the function definition."
  def sc1065 := err 1065 "Trying to declare parameters? Don't. Use () and refer to params as $1, $2."
end Functions

namespace Variables
  def sc1036 := err 1036 "`(` is invalid here. Did you forget to escape it?"
  def sc1037 := err 1037 "Braces are required for positionals over 9, e.g. ${10}."
  def sc1066 := err 1066 "Don't use $ on the left side of assignments."
  def sc1067 := err 1067 "For indirection, use arrays, `declare \"var$n=value\"`, or read/eval."
  def sc1086 := err 1086 "Don't use $ on the iterator name in for loops."
  def sc1087 := err 1087 "Use braces when expanding arrays, e.g. `${array[idx]}`."
  def sc1097 := err 1097 "Unexpected ==. For assignment, use =. For comparison, use `[`/`[[`."
  def sc1116 := err 1116 "Missing $ on a `$((..))` expression? (or use `( (` for arrays)."
end Variables

namespace HereDoc
  def sc1038 := err 1038 "Shells are space sensitive. Use '< <(cmd)', not '<<(cmd)'."
  def sc1039 := err 1039 "Remove indentation before end token (or use `<<-` and indent with tabs)."
  def sc1040 := err 1040 "When using <<-, you can only indent with tabs."
  def sc1041 := err 1041 "Found 'eof' further down, but not on a separate line."
  def sc1042 := warn 1042 "Close matches include '-eof' (!= 'eof')."
  def sc1043 := err 1043 "End token has wrong casing. Did you mean 'EOF' instead of 'eof'?"
  def sc1044 := err 1044 "Couldn't find end token `EOF' in the here document."
  def sc1119 := err 1119 "Add a linefeed between end token and terminating ')'."
  def sc1120 := err 1120 "No comments allowed after here-doc token. Comment the next line instead."
  def sc1121 := err 1121 "Add ;/& terminators on the line with the <<, not here."
  def sc1122 := err 1122 "Nothing allowed after end token. Put continuation on the line with `<<`."
end HereDoc

namespace Sourcing
  def sc1090 := warn 1090 "Can't follow non-constant source. Use a directive to specify location."
  def sc1091 := info 1091 "Not following: (error message here)"
  def sc1092 := warn 1092 "Stopping at 100 source frames. Consider using a directive."
  def sc1094 := warn 1094 "Parsing of sourced file failed. Ignoring it."
end Sourcing

namespace Arithmetic
  def sc1137 := err 1137 "Missing second `(` for arithmetic `((;;))` loop."
  def sc1138 := err 1138 "Remove spaces between `((` in arithmetic for loop."
end Arithmetic

namespace Syntax
  def sc1056 := err 1056 "Expected a '}'. If you have one, try a ; or `\\n` in front of it."
  def sc1070 := err 1070 "Parsing stopped here. Mismatched keywords or invalid parentheses?"
  def sc1072 := err 1072 "Unexpected .."
  def sc1073 := err 1073 "Couldn't parse this (thing). Fix to allow more checks."
  def sc1077 := err 1077 "For command expansion, the tick should slant left (` vs ´)."
  def sc1081 := err 1081 "Scripts are case sensitive. Use 'if', not 'If'."
  def sc1083 := err 1083 "This `{`/`}` is literal. Check expression (missing `;/\\n?`) or quote it."
  def sc1088 := err 1088 "Parsing stopped here. Invalid use of parentheses?"
  def sc1089 := err 1089 "Parsing stopped here. Is this keyword correctly matched up?"
  def sc1098 := err 1098 "Quote/escape special characters when using eval, e.g. eval \"a=(b)\"."
  def sc1132 := err 1132 "This `&` terminates the command. Escape it or add space after it."
  def sc1133 := err 1133 "Unexpected start of line. Place |/||/&& at the end of the previous line."
  def sc1136 := err 1136 "Unexpected characters after terminating `]`. Missing semicolon/linefeed?"
  def sc1141 := err 1141 "Unexpected tokens after compound command. Bad redirection or missing ;/&&/||/|?"
  def sc1142 := err 1142 "Use 'done < <(cmd)' to redirect from process substitution."
  def sc1143 := info 1143 "This backslash is part of a comment and does not continue the line."
end Syntax

namespace Unicode
  def sc1100 := err 1100 "This is a unicode dash. Delete and retype as ASCII minus."
  def sc1109 := err 1109 "This is an unquoted HTML entity. Replace with corresponding character."
end Unicode

namespace Disambiguation
  def sc1102 := err 1102 "Shells disambiguate `$((` differently. Add space after `$(` for command substitution or fix `$((arithmetics))`."
  def sc1105 := err 1105 "Shells disambiguate `((` differently. Add space after first `(` for subshells."
end Disambiguation

namespace Directives
  def sc1107 := warn 1107 "This directive is unknown. It will be ignored."
  def sc1123 := err 1123 "ShellCheck directives only valid in front of complete compound commands."
  def sc1124 := err 1124 "ShellCheck directives valid in front of complete commands, not individual branches."
  def sc1125 := err 1125 "Invalid key=value pair in directive"
  def sc1126 := err 1126 "Place shellcheck directives before commands, not after."
  def sc1127 := err 1127 "Was this intended as a comment? Use `#` in sh."
  def sc1135 := info 1135 "Prefer escape over ending quote to make `$` literal."
  def sc1144 := err 1144 "`external-sources` is only valid in a `.shellcheckrc` file."
  def sc1145 := err 1145 "Unknown `external-sources` value. Expected `true` or `false`."
end Directives

/-!
## All Parser Errors Combined
-/

def allParserErrors : List ParserError := [
  -- Escaping
  Escaping.sc1000, Escaping.sc1001, Escaping.sc1002, Escaping.sc1003,
  Escaping.sc1004, Escaping.sc1005, Escaping.sc1006, Escaping.sc1012,
  Escaping.sc1013, Escaping.sc1117,
  -- Whitespace
  Whitespace.sc1007, Whitespace.sc1017, Whitespace.sc1018, Whitespace.sc1020,
  Whitespace.sc1021, Whitespace.sc1022, Whitespace.sc1023, Whitespace.sc1024,
  Whitespace.sc1025, Whitespace.sc1027, Whitespace.sc1035, Whitespace.sc1054,
  Whitespace.sc1068, Whitespace.sc1069, Whitespace.sc1095, Whitespace.sc1099,
  Whitespace.sc1101, Whitespace.sc1108, Whitespace.sc1114, Whitespace.sc1115,
  Whitespace.sc1118, Whitespace.sc1129, Whitespace.sc1130,
  -- Quoting
  Quoting.sc1011, Quoting.sc1015, Quoting.sc1016, Quoting.sc1078,
  Quoting.sc1079, Quoting.sc1110, Quoting.sc1111, Quoting.sc1112,
  -- Test brackets
  TestBrackets.sc1019, TestBrackets.sc1026, TestBrackets.sc1028,
  TestBrackets.sc1029, TestBrackets.sc1030, TestBrackets.sc1031,
  TestBrackets.sc1032, TestBrackets.sc1033, TestBrackets.sc1034,
  TestBrackets.sc1080, TestBrackets.sc1106, TestBrackets.sc1139,
  TestBrackets.sc1140,
  -- Shebang
  Shebang.sc1008, Shebang.sc1071, Shebang.sc1082, Shebang.sc1084,
  Shebang.sc1104, Shebang.sc1113, Shebang.sc1128,
  -- Control flow
  ControlFlow.sc1009, ControlFlow.sc1010, ControlFlow.sc1014,
  ControlFlow.sc1045, ControlFlow.sc1046, ControlFlow.sc1047,
  ControlFlow.sc1048, ControlFlow.sc1049, ControlFlow.sc1050,
  ControlFlow.sc1051, ControlFlow.sc1052, ControlFlow.sc1053,
  ControlFlow.sc1055, ControlFlow.sc1057, ControlFlow.sc1058,
  ControlFlow.sc1059, ControlFlow.sc1060, ControlFlow.sc1061,
  ControlFlow.sc1062, ControlFlow.sc1063, ControlFlow.sc1074,
  ControlFlow.sc1075, ControlFlow.sc1076, ControlFlow.sc1085,
  ControlFlow.sc1131,
  -- Functions
  Functions.sc1064, Functions.sc1065,
  -- Variables
  Variables.sc1036, Variables.sc1037, Variables.sc1066, Variables.sc1067,
  Variables.sc1086, Variables.sc1087, Variables.sc1097, Variables.sc1116,
  -- HereDoc
  HereDoc.sc1038, HereDoc.sc1039, HereDoc.sc1040, HereDoc.sc1041,
  HereDoc.sc1042, HereDoc.sc1043, HereDoc.sc1044, HereDoc.sc1119,
  HereDoc.sc1120, HereDoc.sc1121, HereDoc.sc1122,
  -- Sourcing
  Sourcing.sc1090, Sourcing.sc1091, Sourcing.sc1092, Sourcing.sc1094,
  -- Arithmetic
  Arithmetic.sc1137, Arithmetic.sc1138,
  -- Syntax
  Syntax.sc1056, Syntax.sc1070, Syntax.sc1072, Syntax.sc1073,
  Syntax.sc1077, Syntax.sc1081, Syntax.sc1083, Syntax.sc1088,
  Syntax.sc1089, Syntax.sc1098, Syntax.sc1132, Syntax.sc1133,
  Syntax.sc1136, Syntax.sc1141, Syntax.sc1142, Syntax.sc1143,
  -- Unicode
  Unicode.sc1100, Unicode.sc1109,
  -- Disambiguation
  Disambiguation.sc1102, Disambiguation.sc1105,
  -- Directives
  Directives.sc1107, Directives.sc1123, Directives.sc1124,
  Directives.sc1125, Directives.sc1126, Directives.sc1127,
  Directives.sc1135, Directives.sc1144, Directives.sc1145
]

/-!
## Lookup Functions
-/

/-- Look up a parser error by code -/
def lookup (code : Nat) : Option ParserError :=
  allParserErrors.find? (·.code == code)

/-- Get wiki URL for a parser error -/
def wikiUrl (code : Nat) : String :=
  s!"https://www.shellcheck.net/wiki/SC{code}"

/-- Format parser error for display -/
def format (pe : ParserError) : String :=
  let sev := match pe.severity with
    | .errorC => "error"
    | .warningC => "warning"
    | .infoC => "info"
    | .styleC => "style"
  s!"SC{pe.code} [{sev}]: {pe.message}"

/-!
## Parser Error Emission Helpers

These functions are meant to be called from the parser.
-/

/-- Create a positioned comment from a parser error at a given position -/
def emitAt (pe : ParserError) (id : Nat) : TokenComment :=
  { tcId := ⟨id⟩
  , tcComment := { cSeverity := pe.severity, cCode := pe.code, cMessage := pe.message }
  , tcFix := none }

/-- Emit SC1000: $ not special -/
def emit1000 (id : Nat) : TokenComment := emitAt Escaping.sc1000 id

/-- Emit SC1007: space after = -/
def emit1007 (id : Nat) : TokenComment := emitAt Whitespace.sc1007 id

/-- Emit SC1008: unrecognized shebang -/
def emit1008 (id : Nat) : TokenComment := emitAt Shebang.sc1008 id

/-- Emit SC1009: parser error location -/
def emit1009 (id : Nat) : TokenComment := emitAt ControlFlow.sc1009 id

/-- Emit SC1010: semicolon before done -/
def emit1010 (id : Nat) : TokenComment := emitAt ControlFlow.sc1010 id

/-- Emit SC1035: space needed -/
def emit1035 (id : Nat) : TokenComment := emitAt Whitespace.sc1035 id

/-- Emit SC1037: braces for positionals -/
def emit1037 (id : Nat) : TokenComment := emitAt Variables.sc1037 id

/-- Emit SC1046: missing fi -/
def emit1046 (id : Nat) : TokenComment := emitAt ControlFlow.sc1046 id

/-- Emit SC1058: expected do -/
def emit1058 (id : Nat) : TokenComment := emitAt ControlFlow.sc1058 id

/-- Emit SC1061: missing done -/
def emit1061 (id : Nat) : TokenComment := emitAt ControlFlow.sc1061 id

/-- Emit SC1064: expected { for function -/
def emit1064 (id : Nat) : TokenComment := emitAt Functions.sc1064 id

/-- Emit SC1068: no spaces in assignment -/
def emit1068 (id : Nat) : TokenComment := emitAt Whitespace.sc1068 id

/-- Emit SC1070: parsing stopped -/
def emit1070 (id : Nat) : TokenComment := emitAt Syntax.sc1070 id

/-- Emit SC1072: unexpected token -/
def emit1072 (id : Nat) : TokenComment := emitAt Syntax.sc1072 id

/-- Emit SC1073: couldn't parse -/
def emit1073 (id : Nat) : TokenComment := emitAt Syntax.sc1073 id

/-- Emit SC1087: braces for arrays -/
def emit1087 (id : Nat) : TokenComment := emitAt Variables.sc1087 id

/-- Emit SC1090: non-constant source -/
def emit1090 (id : Nat) : TokenComment := emitAt Sourcing.sc1090 id

end ShellCheck.Checks.ParserErrors
