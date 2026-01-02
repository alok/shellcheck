/-
  Haskell docstring role for ShellCheck parity.

  Usage in docstrings:
    /-- Mirrors {haskell}`checkInclusion` in ShellCheck.Analytics. -/
    /-- Also works without module: {haskell}`checkInclusion` -/
-/

import Lean.Elab.DocString
import Std.Data.HashMap

open Lean Doc Elab
open scoped Lean.Doc.Syntax

namespace ShellCheck.DocRoles.Haskell

/-- Extract the code content from inline syntax (single code element). -/
private def onlyCode {M : Type → Type} [Monad M] [MonadError M]
    (xs : TSyntaxArray `inline) : M StrLit := do
  if h : xs.size = 1 then
    match xs[0] with
    | `(inline|code($s)) => return s
    | other => throwErrorAt other "Expected code"
  else
    throwError "Expected precisely 1 code argument"

private def repoRoot : IO System.FilePath :=
  IO.currentDir

private def haskellRoot : IO System.FilePath := do
  return (← repoRoot) / "src" / "ShellCheck"

private def stripShellCheckPrefix (mod : String) : String :=
  if mod == "ShellCheck" then
    ""
  else
    match mod.toSlice.dropPrefix? "ShellCheck." with
    | some rest => rest.toString
    | none => mod

private def moduleToPath (mod : String) : System.FilePath :=
  let mod := stripShellCheckPrefix mod
  if mod.isEmpty then
    System.FilePath.addExtension (System.FilePath.mk "src" / "ShellCheck") "hs"
  else
    let parts := mod.splitOn "."
    System.FilePath.addExtension (System.FilePath.mk "src" / "ShellCheck" / System.mkFilePath parts) "hs"

private def splitModule (s : String) : Option String × String :=
  let parts := s.splitOn "."
  match parts.reverse with
  | [] => (none, s)
  | name :: rest =>
    if rest.isEmpty then
      (none, name)
    else
      (some (String.intercalate "." rest.reverse), name)

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

private def isDefTail (rest : String) : Bool :=
  let t := rest.trimAsciiStart.toString
  t.startsWith "::" || t.startsWith "=" || t.contains " =" || t.contains "= "

private def matchesDef (name line : String) : Bool :=
  let trimmed := line.trimAsciiStart.toString
  if trimmed.startsWith "--" then
    false
  else if !trimmed.startsWith name then
    false
  else
    let rest := (trimmed.toSlice.drop name.length).toString
    if name.startsWith "(" then
      isDefTail rest
    else
      match rest.front? with
      | some c =>
        if isIdentChar c then false else isDefTail rest
      | none => false

private def findDefInFile (path : System.FilePath) (name : String) : IO (Option Nat) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
  let mut idx : Nat := 0
  for line in lines do
    idx := idx + 1
    if matchesDef name line then
      return some idx
  return none

partial def collectHaskellFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for entry in ← root.readDir do
    let md ← entry.path.metadata
    if md.type == IO.FS.FileType.dir then
      out := out ++ (← collectHaskellFiles entry.path)
    else if entry.path.extension == some "hs" then
      out := out.push entry.path
  return out

builtin_initialize haskellFilesCache : IO.Ref (Option (Array System.FilePath)) ← IO.mkRef none
builtin_initialize haskellDefCache : IO.Ref (Std.HashMap String (Option (System.FilePath × Nat))) ←
  IO.mkRef {}

private def getHaskellFiles : IO (Array System.FilePath) := do
  let cache ← haskellFilesCache.get
  match cache with
  | some files => return files
  | none =>
    let files ← collectHaskellFiles (← haskellRoot)
    let files := files.qsort (fun a b => a.toString < b.toString)
    haskellFilesCache.set (some files)
    return files

private def resolveHaskellInModule (mod name : String) : IO (Option (System.FilePath × Nat)) := do
  let path := moduleToPath mod
  if !(← path.pathExists) then
    return none
  match (← findDefInFile path name) with
  | some line => return some (path, line)
  | none => return none

private def resolveHaskellGlobal (name : String) : IO (Option (System.FilePath × Nat)) := do
  let files ← getHaskellFiles
  for path in files do
    if let some line ← findDefInFile path name then
      return some (path, line)
  return none

private def resolveHaskell (query : String) : IO (Option (System.FilePath × Nat)) := do
  let cache ← haskellDefCache.get
  if let some hit := cache.get? query then
    return hit
  let (mod?, name) := splitModule query
  let loc ←
    match mod? with
    | some mod => resolveHaskellInModule mod name
    | none => resolveHaskellGlobal name
  haskellDefCache.modify (·.insert query loc)
  return loc

private def fileUrl (path : System.FilePath) (line : Nat) : IO String := do
  let real ← IO.FS.realPath path
  pure s!"file://{real.toString}#L{line}"

private def haddockBase : String :=
  "https://hackage.haskell.org/package/ShellCheck/docs/"

private def moduleToHaddock (mod : String) : String :=
  (if mod.isEmpty then "ShellCheck" else mod).replace "." "-"

private def haddockUrl (mod name : String) : String :=
  s!"{haddockBase}{moduleToHaddock mod}.html#v:{name}"

/--
Role for Haskell references to the original ShellCheck source.

Resolves `{haskell}``Symbol`` to a local `file://` link when possible,
falling back to Haddock links for module-qualified references.
-/
@[doc_role]
def haskell (xs : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  let s ← onlyCode xs
  let raw := s.getString.trimAscii.toString
  if raw.isEmpty then
    return .code s.getString
  let loc? ← liftM <| resolveHaskell raw
  match loc? with
  | some (path, line) =>
    let url ← liftM <| fileUrl path line
    return .link #[.code raw] url
  | none =>
    let (mod?, name) := splitModule raw
    match mod? with
    | some mod => return .link #[.code raw] (haddockUrl mod name)
    | none => return .code raw

end ShellCheck.DocRoles.Haskell
