/-
  Copyright 2022 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Generic basic utility functions for ShellCheck
-/

import ShellCheck.DocRoles

namespace ShellCheck.Prelude

/-- Get element 0 or a default. Like `head` but safe. -/
def headOrDefault (default : α) : List α → α
  | a :: _ => a
  | [] => default

/-- Get the last element or a default. Like `last` but safe. -/
def lastOrDefault (default : α) : List α → α
  | [] => default
  | [x] => x
  | _ :: xs => lastOrDefault default xs

/-- Get element n of a list, or none. Like `!!` but safe. -/
def getAt? (list : List α) (i : Nat) : Option α :=
  list[i]?

/-- Infix operator for safe indexing -/
infixl:75 " !!! " => getAt?

/-- Like fold but for Semigroups, requires non-empty list.
    Panics on empty list. -/
def sconcat1 [Append α] [Inhabited α] : List α → α
  | [x] => x
  | x :: xs => x ++ sconcat1 xs
  | [] => panic! "sconcat1: empty list"

/-- sconcat with a default for empty lists -/
def sconcatOrDefault [Append α] [Inhabited α] (default : α) : List α → α
  | [] => default
  | list => sconcat1 list

/-- For more actionable "impossible" errors -/
def pleaseReport (str : String) : String :=
  s!"ShellCheck internal error, please report: {str}"

-- Theorems (unproven stubs)
theorem headOrDefault_cons (d : α) (x : α) (xs : List α) :
  headOrDefault d (x :: xs) = x := rfl

theorem lastOrDefault_singleton (d : α) (x : α) :
  lastOrDefault d [x] = x := rfl

theorem getAt?_zero (x : α) (xs : List α) :
    (x :: xs) !!! 0 = some x := rfl

theorem getAt?_succ (x : α) (xs : List α) (n : Nat) :
    (x :: xs) !!! (n + 1) = xs !!! n := rfl

end ShellCheck.Prelude
