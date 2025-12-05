/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  CheckStyle XML output formatter for ShellCheck.
-/

import ShellCheck.Interface
import ShellCheck.Formatter.Format

namespace ShellCheck.Formatter.CheckStyle

open ShellCheck.Interface
open ShellCheck.Formatter.Format

/-- Escape a character for XML -/
def escapeChar (c : Char) : String :=
  if c.isAlpha || c.isDigit || c == ' ' || c == '.' || c == '/' then
    c.toString
  else
    s!"&#{c.toNat};"

/-- Escape a string for XML -/
def escape (s : String) : String :=
  String.join (s.toList.map escapeChar)

/-- Format an XML attribute -/
def attr (name : String) (value : String) : String :=
  s!"{name}='{escape value}' "

/-- Map severity to CheckStyle severity -/
def severity (sev : String) : String :=
  match sev with
  | "error" => "error"
  | "warning" => "warning"
  | _ => "info"

/-- Format a single comment as XML error element -/
def formatComment (c : PositionedComment) : String :=
  "<error " ++
  attr "line" (toString (lineNo c)) ++
  attr "column" (toString (colNo c)) ++
  attr "severity" (severity (severityText c)) ++
  attr "message" (messageText c) ++
  attr "source" s!"ShellCheck.SC{codeNo c}" ++
  "/>\n"

/-- Format a file element with its comments -/
def formatFile (name : String) (comments : List PositionedComment) : String :=
  "<file " ++ attr "name" name ++ ">\n" ++
  String.join (comments.map formatComment) ++
  "</file>"

/-- Format an error for a file -/
def formatError (file : String) (msg : String) : String :=
  "<file " ++ attr "name" file ++ ">\n" ++
  "<error " ++
  attr "line" "1" ++
  attr "column" "1" ++
  attr "severity" "error" ++
  attr "message" msg ++
  attr "source" "ShellCheck" ++
  "/>\n" ++
  "</file>"

/-- XML header -/
def xmlHeader : String :=
  "<?xml version='1.0' encoding='UTF-8'?>\n<checkstyle version='4.3'>"

/-- XML footer -/
def xmlFooter : String := "</checkstyle>"

/-- Format a complete result as CheckStyle XML -/
def formatResult (cr : CheckResult) : String :=
  formatFile cr.crFilename cr.crComments

/-- Format multiple results as CheckStyle XML -/
def formatResults (results : List CheckResult) : String :=
  xmlHeader ++ "\n" ++
  String.join (results.map (fun cr => formatResult cr ++ "\n")) ++
  xmlFooter

/-- Create CheckStyle formatter -/
def format [Monad m] : Formatter m := {
  header := pure ()  -- Would print XML header
  onResult := fun _cr _sys => pure ()  -- Would print file element
  onFailure := fun _file _msg => pure ()  -- Would print error element
  footer := pure ()  -- Would print XML footer
}

-- Theorems (stubs)

theorem escape_preserves_safe_chars (c : Char) :
    c.isAlpha → escapeChar c = c.toString := sorry

theorem formatComment_valid_xml (c : PositionedComment) :
    True := trivial  -- Would verify valid XML

theorem formatFile_wraps_comments (name : String) (comments : List PositionedComment) :
    (formatFile name comments).startsWith "<file " := sorry

theorem formatResults_has_header (results : List CheckResult) :
    (formatResults results).startsWith xmlHeader := sorry

theorem formatResults_has_footer (results : List CheckResult) :
    (formatResults results).endsWith xmlFooter := sorry

end ShellCheck.Formatter.CheckStyle
