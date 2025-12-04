/-
  ShellCheck - Shell script static analysis tool
  Lean 4 port of the Haskell original by Vidar Holen
-/

-- Core modules
import ShellCheck.Prelude
import ShellCheck.Data
import ShellCheck.AST
import ShellCheck.Interface
import ShellCheck.Regex
import ShellCheck.ASTLib
import ShellCheck.Fixer
import ShellCheck.Graph
import ShellCheck.Parser
import ShellCheck.CFG
import ShellCheck.CFGAnalysis
import ShellCheck.AnalyzerLib
