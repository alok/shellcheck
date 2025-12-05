/-
  Diagnostics and error recovery for ShellCheck parser
  Provides error codes, suggestions, and Unicode detection
-/

import ShellCheck.Interface

namespace ShellCheck.Parser.Diagnostics

open ShellCheck.Interface

-- Error code ranges (matching Haskell ShellCheck)
-- SC1000-SC1199: Parser errors
-- SC2000-SC2999: Analysis warnings

-- Common parse error codes (Code = Int alias)
def SC1001 : Code := 1001  -- This `\c` will be a regular 'c' in this context
def SC1003 : Code := 1003  -- Want to escape a single quote? Use '\''
def SC1004 : Code := 1004  -- Expected 'fi', found end of file
def SC1006 : Code := 1006  -- Expected 'do'
def SC1007 : Code := 1007  -- Expected 'then'
def SC1008 : Code := 1008  -- This word is constant - Alias/function names should be alphanumeric
def SC1009 : Code := 1009  -- The mentioned parser error was in this X block
def SC1010 : Code := 1010  -- Use semicolon or linefeed before 'done'
def SC1011 : Code := 1011  -- This XX is unquoted
def SC1012 : Code := 1012  -- \\t is just literal 't' here
def SC1014 : Code := 1014  -- Use 'if cmd; then ..' to check exit code, or 'if [[ $(cmd) == .. ]]' to check output
def SC1015 : Code := 1015  -- This is a Unicode quote. Delete and retype it
def SC1016 : Code := 1016  -- This is a Unicode dash. Delete and retype it
def SC1017 : Code := 1017  -- Literal carriage return. Run script through tr -d '\r'
def SC1018 : Code := 1018  -- This is a Unicode non-breaking space
def SC1019 : Code := 1019  -- Expected this to be an argument to the unary condition
def SC1020 : Code := 1020  -- You need spaces around the comparison operator
def SC1035 : Code := 1035  -- You need a space here
def SC1036 : Code := 1036  -- ( is invalid here. Did you forget to escape it?
def SC1037 : Code := 1037  -- Braces are literal in [[ ]]
def SC1038 : Code := 1038  -- Shells are space sensitive. Use '< <(cmd)' instead
def SC1039 : Code := 1039  -- Remove indentation before end token
def SC1040 : Code := 1040  -- Use 'elif' instead of 'else if'
def SC1044 : Code := 1044  -- Couldn't find end token for this here-doc
def SC1045 : Code := 1045  -- It's not 'foo @args', just 'foo args'
def SC1046 : Code := 1046  -- Couldn't find 'fi' for this 'if'
def SC1047 : Code := 1047  -- Expected 'fi' matching previously mentioned 'if'
def SC1048 : Code := 1048  -- Can't have empty then clauses
def SC1049 : Code := 1049  -- Did you forget the 'then' for this 'if'?
def SC1050 : Code := 1050  -- Expected 'then'
def SC1051 : Code := 1051  -- Semicolons directly after 'then' are optional
def SC1052 : Code := 1052  -- Semicolons before 'then' are optional
def SC1053 : Code := 1053  -- Reserved keyword used as variable name
def SC1054 : Code := 1054  -- Use 'elif' instead of 'else if'
def SC1058 : Code := 1058  -- Expected 'do'
def SC1059 : Code := 1059  -- Not following extended globs
def SC1061 : Code := 1061  -- Couldn't find 'done' for this 'do'
def SC1062 : Code := 1062  -- Expected 'done' matching previously mentioned 'do'
def SC1064 : Code := 1064  -- Expected 'esac' matching previously mentioned 'case'
def SC1065 : Code := 1065  -- Trying to declare parameters
def SC1066 : Code := 1066  -- Don't use $ on the left side of assignments
def SC1068 : Code := 1068  -- Don't put spaces around the = in assignments
def SC1069 : Code := 1069  -- You need a space before the [
def SC1071 : Code := 1071  -- ShellCheck only supports sh/bash/dash/ksh scripts
def SC1072 : Code := 1072  -- Unexpected ..
def SC1073 : Code := 1073  -- Couldn't parse this X expression
def SC1074 : Code := 1074  -- Did you forget to escape the end of line?
def SC1075 : Code := 1075  -- Use 'elif' instead of 'else if'
def SC1077 : Code := 1077  -- For command expansion, use $(cmd) instead of %cmd
def SC1078 : Code := 1078  -- Did you forget to close this double quoted string?
def SC1079 : Code := 1079  -- Missing 'in' after 'for'
def SC1081 : Code := 1081  -- Scripts are case sensitive
def SC1082 : Code := 1082  -- This file has a Unicode BOM
def SC1083 : Code := 1083  -- This X is literal. Check expression (missing ;/\n?) or quote it
def SC1084 : Code := 1084  -- Use #!, not just #, for the shebang
def SC1086 : Code := 1086  -- Don't use $ on the iterator name in for loops
def SC1087 : Code := 1087  -- Braces are literal in [[ ]]
def SC1088 : Code := 1088  -- Parsing stopped here. Invalid use of parentheses?
def SC1089 : Code := 1089  -- Parsing stopped here. Mismatched keywords or invalid nesting?
def SC1090 : Code := 1090  -- Can't follow non-constant source
def SC1091 : Code := 1091  -- Not following: (error message)
def SC1094 : Code := 1094  -- Parsing of sourced file failed
def SC1095 : Code := 1095  -- You need a space or semicolon before the }
def SC1097 : Code := 1097  -- Unexpected ==. For assignment, use =
def SC1098 : Code := 1098  -- Quote/escape special characters when using eval
def SC1099 : Code := 1099  -- You need a space before the #

-- Unicode detection helpers

/-- Check if character is a smart/curly quote -/
def isSmartQuote (c : Char) : Bool :=
  c.toNat ∈ [0x2018, 0x2019, 0x201C, 0x201D,  -- '' ""
             0x00AB, 0x00BB,                   -- « »
             0x2039, 0x203A,                   -- ‹ ›
             0xFF02, 0xFF07]                   -- ＂ ＇

/-- Check if character is a smart dash -/
def isSmartDash (c : Char) : Bool :=
  c.toNat ∈ [0x2010, 0x2011, 0x2012, 0x2013, 0x2014, 0x2015,  -- ‐ ‑ ‒ – — ―
             0x2212, 0xFE58, 0xFE63, 0xFF0D]                   -- − ﹘ ﹣ －

/-- Check if character is a non-breaking space -/
def isNonBreakingSpace (c : Char) : Bool :=
  c.toNat ∈ [0x00A0,  -- NO-BREAK SPACE
             0x2007,  -- FIGURE SPACE
             0x202F,  -- NARROW NO-BREAK SPACE
             0xFEFF]  -- ZERO WIDTH NO-BREAK SPACE (BOM)

/-- Check if character is problematic Unicode -/
def isProblematicUnicode (c : Char) : Bool :=
  isSmartQuote c || isSmartDash c || isNonBreakingSpace c

/-- Get suggestion for replacing problematic Unicode -/
def unicodeReplacement (c : Char) : Option Char :=
  if isSmartQuote c then
    if c.toNat ∈ [0x2018, 0x2019, 0xFF07] then some '\''  -- single quote
    else some '"'  -- double quote
  else if isSmartDash c then some '-'
  else if isNonBreakingSpace c then some ' '
  else none

/-- Scan string for problematic Unicode characters -/
def findProblematicUnicode (s : String) : List (Nat × Char × Code) :=
  let chars := s.toList
  let positions := List.range chars.length
  (positions.zip chars).filterMap fun (pos, c) =>
    if isSmartQuote c then some (pos, c, SC1015)
    else if isSmartDash c then some (pos, c, SC1016)
    else if isNonBreakingSpace c then some (pos, c, SC1018)
    else none

/-- Check for BOM at start of file -/
def hasBOM (s : String) : Bool :=
  let bom1 : Char := Char.ofNat 0xFEFF
  let bom2 : Char := Char.ofNat 0xFFFE
  (s.toList.headD ' ' == bom1) || (s.toList.headD ' ' == bom2)

/-- Check for carriage returns -/
def hasCarriageReturn (s : String) : Bool :=
  s.any (· == '\r')

/-- Parse error structure -/
structure ParseError where
  line : Nat
  column : Nat
  code : Code
  message : String
  suggestion : Option String := none
  deriving Repr, Inhabited

/-- Create a parse error -/
def mkError (line col : Nat) (code : Code) (msg : String) (suggestion : Option String := none) : ParseError :=
  { line, column := col, code, message := msg, suggestion }

/-- Common error messages -/
def errExpectedFi := "Expected 'fi' to close 'if' statement"
def errExpectedDone := "Expected 'done' to close loop"
def errExpectedEsac := "Expected 'esac' to close 'case' statement"
def errExpectedThen := "Expected 'then' after condition"
def errExpectedDo := "Expected 'do' after loop condition"
def errMissingSpace := "Missing space"
def errUnexpectedToken := "Unexpected token"

-- Suggestion generators

/-- Suggest fix for missing keyword -/
def suggestMissingKeyword (expected : String) (found : Option String) : String :=
  match found with
  | some f => s!"Expected '{expected}', but found '{f}'. Add '{expected}' before this."
  | none => s!"Expected '{expected}'. Add it here."

/-- Suggest fix for smart quotes -/
def suggestSmartQuoteFix (c : Char) : String :=
  match unicodeReplacement c with
  | some r => s!"Replace Unicode character (U+{String.ofList (Nat.toDigits 16 c.toNat)}) with ASCII '{r}'"
  | none => "Delete this Unicode character and retype it"

/-- Context for error messages -/
inductive ParseContext where
  | inIfClause
  | inWhileLoop
  | inUntilLoop
  | inForLoop
  | inCaseStatement
  | inFunction (name : String)
  | inSubshell
  | inBraceGroup
  | inDoubleQuote
  | inSingleQuote
  | inArithmetic
  | inCondition
  | inHereDoc (delimiter : String)
  deriving Repr, BEq, Inhabited

/-- Get context description -/
def ParseContext.describe : ParseContext → String
  | .inIfClause => "if statement"
  | .inWhileLoop => "while loop"
  | .inUntilLoop => "until loop"
  | .inForLoop => "for loop"
  | .inCaseStatement => "case statement"
  | .inFunction name => s!"function '{name}'"
  | .inSubshell => "subshell"
  | .inBraceGroup => "brace group"
  | .inDoubleQuote => "double-quoted string"
  | .inSingleQuote => "single-quoted string"
  | .inArithmetic => "arithmetic expression"
  | .inCondition => "test condition"
  | .inHereDoc delim => s!"here-document (delimiter: {delim})"

/-- Shell dialect for feature checking -/
inductive ShellDialect where
  | bash
  | sh
  | dash
  | ksh
  | zsh
  deriving Repr, BEq, Inhabited

/-- Feature availability per dialect -/
structure DialectFeatures where
  hasDoubleBracket : Bool
  hasArrays : Bool
  hasProcessSub : Bool
  hasExtGlob : Bool
  hasCoproc : Bool
  hasSelect : Bool
  hasFunctionKeyword : Bool
  deriving Repr, Inhabited

/-- Get features for a dialect -/
def dialectFeatures : ShellDialect → DialectFeatures
  | .bash => { hasDoubleBracket := true, hasArrays := true, hasProcessSub := true,
               hasExtGlob := true, hasCoproc := true, hasSelect := true, hasFunctionKeyword := true }
  | .ksh => { hasDoubleBracket := true, hasArrays := true, hasProcessSub := true,
              hasExtGlob := true, hasCoproc := true, hasSelect := true, hasFunctionKeyword := true }
  | .zsh => { hasDoubleBracket := true, hasArrays := true, hasProcessSub := true,
              hasExtGlob := true, hasCoproc := true, hasSelect := true, hasFunctionKeyword := true }
  | .dash => { hasDoubleBracket := false, hasArrays := false, hasProcessSub := false,
               hasExtGlob := false, hasCoproc := false, hasSelect := false, hasFunctionKeyword := false }
  | .sh => { hasDoubleBracket := false, hasArrays := false, hasProcessSub := false,
             hasExtGlob := false, hasCoproc := false, hasSelect := false, hasFunctionKeyword := false }

/-- Check if feature is supported by dialect -/
def featureSupported (dialect : ShellDialect) (feature : String) : Bool :=
  let f := dialectFeatures dialect
  match feature with
  | "[[" => f.hasDoubleBracket
  | "arrays" => f.hasArrays
  | "process-sub" => f.hasProcessSub
  | "extglob" => f.hasExtGlob
  | "coproc" => f.hasCoproc
  | "select" => f.hasSelect
  | "function" => f.hasFunctionKeyword
  | _ => true

end ShellCheck.Parser.Diagnostics
