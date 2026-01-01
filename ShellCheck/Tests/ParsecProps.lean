import Plausible
import ShellCheck.Parser.Parsec

namespace ShellCheck.Tests.ParsecProps

open ShellCheck.Parser.Parsec

def parseOnly (p : Parser α) (input : String) : Except String α :=
  match ShellCheck.Parser.Parsec.runExcept p input with
  | .ok (a, _) => .ok a
  | .error e => .error e

def isOk (e : Except ε α) : Bool :=
  match e with
  | .ok _ => true
  | .error _ => false

def okVal (e : Except ε α) : Option α :=
  match e with
  | .ok a => some a
  | .error _ => none

abbrev prop_orElse_commits_consumption : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "a" ++ tail
    let p : Parser String := (pstring "ab" <|> pstring "a")
    if tail.startsWith "b" then
      okVal (parseOnly p input) = some "ab"
    else
      okVal (parseOnly p input) = none

abbrev prop_attempt_allows_backtracking : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "a" ++ tail
    let p : Parser String := (attempt (pstring "ab") <|> pstring "a")
    let expected := if tail.startsWith "b" then "ab" else "a"
    okVal (parseOnly p input) = some expected

abbrev prop_many_fails_after_partial_consumption : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "a" ++ tail
    let p : Parser (Array String) := many (pstring "ab")
    if tail.startsWith "b" then
      True
    else
      okVal (parseOnly p input) = none

abbrev prop_many_does_not_consume_on_mismatch : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "c" ++ tail
    let p : Parser (Nat × Char) := do
      let xs ← many (pstring "ab")
      let c ← anyChar
      pure (xs.size, c)
    okVal (parseOnly p input) = some (0, 'c')

abbrev prop_optional_does_not_consume_on_mismatch : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "c" ++ tail
    let p : Parser (Option String × Char) := do
      let r ← ShellCheck.Parser.Parsec.optional (pstring "ab")
      let c ← anyChar
      pure (r, c)
    okVal (parseOnly p input) = some (none, 'c')

abbrev prop_optional_commits_after_partial_consumption : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "a" ++ tail
    let p : Parser (Option String) := ShellCheck.Parser.Parsec.optional (pstring "ab")
    if tail.startsWith "b" then
      okVal (parseOnly p input) = some (some "ab")
    else
      okVal (parseOnly p input) = none

abbrev prop_many_rejects_empty_success : Prop :=
  let p : Parser (Array Nat) := many (pure (1 : Nat))
  okVal (parseOnly p "") = none

abbrev prop_peekString_does_not_consume : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "abc" ++ tail
    let p : Parser (String × Char) := do
      let peeked ← peekString 2
      let c ← anyChar
      pure (peeked, c)
    okVal (parseOnly p input) = some ("ab", 'a')

abbrev prop_takeWhile1_requires_match : Prop :=
  Plausible.NamedBinder "tail" <| ∀ tail : String,
    let input := "a" ++ tail
    let p : Parser String := takeWhile1 (fun c => c != 'a')
    okVal (parseOnly p input) = none

end ShellCheck.Tests.ParsecProps
