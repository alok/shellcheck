# ShellCheck Lean 4 Port - Agent Guide

This document provides context for AI agents (Claude, Codex, etc.) working on this codebase.

## Project Overview

A Lean 4 port of [ShellCheck](https://github.com/koalaman/shellcheck), the shell script static analysis tool. The goal is feature parity with the original Haskell implementation while leveraging Lean 4's type system for correctness.

## Architecture

```
ShellCheck/
├── AST.lean           # Shell script AST types (Token, InnerToken, etc.)
├── ASTLib.lean        # AST traversal utilities
├── Parser.lean        # Main shell parser (~2700 lines) - FullParser monad
├── Parser/
│   ├── Core.lean      # FullParser infrastructure with position tracking
│   ├── Ext.lean       # Basic Parser combinators (simpler, no token tracking)
│   ├── Parsec.lean    # NEW: Std.Internal.Parsec integration with MonadLift
│   ├── Arithmetic.lean # $(()) arithmetic expression parser
│   └── ...
├── Analytics.lean     # Main analysis checks (~120 check functions)
├── AnalyzerLib.lean   # Analysis infrastructure, parent maps, variable tracking
├── Checks/
│   ├── Commands.lean  # Command-specific checks (26 functions)
│   ├── ControlFlow.lean # Control flow checks
│   ├── ShellSupport.lean # Shell feature checks
│   └── Custom.lean    # Custom/project-specific checks
├── CFG.lean           # Control flow graph construction
├── CFGAnalysis.lean   # Dataflow analysis on CFG
├── Interface.lean     # Core types: Position, Severity, Comment, etc.
├── Checker.lean       # Main entry point combining all checks
└── Formatter/         # Output formatters (JSON, GCC, TTY, etc.)
```

## Key Types

```lean
-- Token with unique ID for position tracking
structure Token where
  id : Id
  inner : InnerToken Token

-- Position in source file
structure Position where
  posFile : String
  posLine : Nat
  posColumn : Nat

-- Analysis result
structure Comment where
  cSeverity : Severity
  cCode : Nat           -- SC code (e.g., 2086 for SC2086)
  cMessage : String
```

## Parser Architecture

### Current: FullParser (Parser.lean + Parser/Core.lean)
```lean
def FullParser (α : Type) := FullParserState → FullResult α

structure FullParserState where
  input : String
  pos : String.Pos.Raw
  line : Nat
  column : Nat
  nextId : Nat
  positions : Std.HashMap Id (Position × Position)
  filename : String
  errors : List String
```

### New: ShellParser with Parsec (Parser/Parsec.lean)
```lean
-- Built on Std.Internal.Parsec with position-tracking iterator
abbrev BaseParser := Std.Internal.Parsec PosIterator
def ShellParser (α : Type) := ShellState → BaseParser (α × ShellState)

-- MonadLift allows using Parsec combinators directly
instance : MonadLift BaseParser ShellParser
```

## Running the Tool

```bash
# Build
lake build

# Run on a script
.lake/build/bin/shellcheck4 script.sh

# With JSON output
.lake/build/bin/shellcheck4 -f json script.sh
```

## Testing

```bash
# Quick test on a file
.lake/build/bin/shellcheck4 test_scripts/test_simple.sh

# Compare with real shellcheck
shellcheck test_scripts/test_simple.sh
diff <(.lake/build/bin/shellcheck4 -f json script.sh | jq) <(shellcheck -f json script.sh | jq)
```

## Recent Fixes (Dec 2024)

1. **ANSI-C quoting** (`$'...\'..'`): Fixed escape sequence handling in `readAnsiCContent`
2. **SC2046 false positives**: Added `isQuoteFreeForExpansion` to detect quote-free contexts
3. **Position tracking**: Fixed `parseSubshellContent` to offset positions correctly
4. **Recursive `$()` parsing**: Added `expandDollarExpansions` for nested command substitution

## Next Steps (Priority Order)

### 1. Migrate Parser to New Parsec Infrastructure
**Why**: The new `Parser/Parsec.lean` provides cleaner combinators via `MonadLift`.
**How**:
- Update `Parser.lean` to use `ShellParser` instead of `FullParser`
- The `PosIterator` already tracks line/column in the iterator itself
- `liftBase` allows using any `Std.Internal.Parsec` combinator

### 2. Add Property-Based Testing
**Why**: Current testing is ad-hoc shell scripts.
**How**:
- Use `plausible` (already a dependency via mathlib) for property tests
- Test parser round-trips: `parse(print(ast)) == ast`
- Test position tracking: positions always valid and monotonic
- Test check coverage: each SC code has at least one triggering case

### 3. Reduce `sorry` Count
**Why**: Many functions have `sorry` placeholders.
**How**:
```bash
grep -r "sorry" ShellCheck/*.lean | wc -l  # Currently ~50+
```
Focus on:
- `Fixer.lean` - fix suggestion generation
- `Formatter/*.lean` - output formatting
- `CFGAnalysis.lean` - dataflow proofs

### 4. Missing Checks
Compare with original shellcheck:
```bash
# In original shellcheck repo
grep -o "SC[0-9]\+" src/ShellCheck/Analytics.hs | sort -u | wc -l
```
Priority missing checks:
- SC2030/SC2031 (subshell variable modification)
- SC2145 (array as argument)
- SC2154 (referenced but not assigned)

### 5. Performance Optimization
- Profile with `lake build -KreleaseFast`
- The parser does multiple passes (parse → expand $() → analyze)
- Consider single-pass where possible

### 6. Better Error Messages
- Current errors are basic strings
- Add source context snippets
- Suggest fixes inline

## Code Patterns

### Adding a New Check
```lean
-- In Analytics.lean or Checks/*.lean
def checkMyNewThing : ForToken := fun params t => do
  match t.inner with
  | .T_SomePattern args =>
      if someCondition args then
        warn params t.id 2999 "Description of issue"
  | _ => pure ()
```

### Position Tracking
```lean
-- Get position from token ID
let pos := params.tokenPositions.get? t.id
-- Record position for new token
recordPosition id startLine startCol endLine endCol
```

### Parent Tree Traversal
```lean
-- Check if token is inside a specific context
partial def isInContext (parentMap : Std.HashMap Id Token) (t : Token) : Bool :=
  match parentMap.get? t.id with
  | some parent => match parent.inner with
      | .T_TargetContext .. => true
      | _ => isInContext parentMap parent
  | none => false
```

## Common Issues

### False Positives
1. Check `isQuoteFreeForExpansion` for quote context
2. Check `isInHereDoc` for heredoc content
3. Check directive comments `# shellcheck disable=SC####`

### Parser Bugs
1. ANSI-C quoting needs escape handling
2. Here-strings (`<<<`) interact with quotes
3. Process substitution `<()` vs arithmetic `$(())`

## Useful Commands

```bash
# Build specific module
lake build ShellCheck.Parser

# See AST for a script
# (would need to add --dump-ast flag)

# Check which SC codes are implemented
grep -o "warn.*[0-9]\{4\}" ShellCheck/Analytics.lean | sort -u

# Find check by SC code
grep -n "2086" ShellCheck/*.lean
```

## Contact

This is Alok Singh's project. See `~/.claude/CLAUDE.md` for preferences.
