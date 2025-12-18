/-
  Copyright 2012-2019 Vidar Holen (Haskell original)
  Lean 4 port: 2024

  Abstract Syntax Tree for shell scripts
-/

namespace ShellCheck.AST

/-- Unique identifier for AST nodes -/
structure Id where
  val : Nat
  deriving Repr, BEq, Hashable, Ord, Inhabited

instance : ToString Id where
  toString id := s!"Id({id.val})"

/-- Source position in the input -/
structure SourcePos where
  sourceName : String
  sourceLine : Nat
  sourceColumn : Nat
  deriving Repr, BEq, Inhabited

/-- Whether something is quoted -/
inductive Quoted where
  | quoted
  | unquoted
  deriving Repr, BEq, Inhabited

/-- Whether a heredoc uses - for tab stripping -/
inductive Dashed where
  | dashed
  | undashed
  deriving Repr, BEq, Inhabited

/-- Whether piped -/
inductive Piped where
  | piped
  | unpiped
  deriving Repr, BEq, Inhabited

/-- Assignment mode: = vs += -/
inductive AssignmentMode where
  | assign
  | append
  deriving Repr, BEq, Inhabited

/-- Whether function keyword was used -/
structure FunctionKeyword where
  used : Bool
  deriving Repr, BEq, Inhabited

/-- Whether function parentheses were used -/
structure FunctionParentheses where
  used : Bool
  deriving Repr, BEq, Inhabited

/-- Case clause terminator type -/
inductive CaseType where
  | caseBreak        -- ;;
  | caseFallThrough  -- ;&
  | caseContinue     -- ;;&
  deriving Repr, BEq, Inhabited

/-- Type of condition: [[ ]] vs [ ] -/
inductive ConditionType where
  | doubleBracket
  | singleBracket
  deriving Repr, BEq, Inhabited

/-- ShellCheck annotation/directive -/
inductive Annotation where
  | disableComment (fromCode toCode : Int)  -- [from, to)
  | enableComment (name : String)
  | sourceOverride (path : String)
  | shellOverride (shell : String)
  | sourcePath (path : String)
  | externalSources (enabled : Bool)
  | extendedAnalysis (enabled : Bool)
  deriving Repr, BEq, Inhabited

/-- The inner content of a token, parameterized by the recursive token type -/
inductive InnerToken (t : Type) where
  -- Arithmetic expressions (TA_*)
  | TA_Binary (op : String) (left right : t)
  | TA_Assignment (op : String) (lhs rhs : t)
  | TA_Variable (name : String) (indices : List t)
  | TA_Expansion (parts : List t)
  | TA_Sequence (exprs : List t)
  | TA_Parenthesis (expr : t)
  | TA_Trinary (cond thenExpr elseExpr : t)
  | TA_Unary (op : String) (expr : t)

  -- Test/condition expressions (TC_*)
  | TC_And (condType : ConditionType) (op : String) (left right : t)
  | TC_Binary (condType : ConditionType) (op : String) (left right : t)
  | TC_Group (condType : ConditionType) (expr : t)
  | TC_Nullary (condType : ConditionType) (expr : t)
  | TC_Or (condType : ConditionType) (op : String) (left right : t)
  | TC_Unary (condType : ConditionType) (op : String) (expr : t)
  | TC_Empty (condType : ConditionType)

  -- Keywords and operators (nullary tokens)
  | T_AND_IF       -- &&
  | T_Bang         -- !
  | T_Case         -- case
  | T_CLOBBER      -- >|
  | T_DGREAT       -- >>
  | T_DLESS        -- <<
  | T_DLESSDASH    -- <<-
  | T_Do           -- do
  | T_Done         -- done
  | T_DSEMI        -- ;;
  | T_Elif         -- elif
  | T_Else         -- else
  | T_EOF          -- end of file
  | T_Esac         -- esac
  | T_Fi           -- fi
  | T_For          -- for
  | T_GREATAND     -- >&
  | T_Greater      -- >
  | T_If           -- if
  | T_In           -- in
  | T_Lbrace       -- {
  | T_Less         -- <
  | T_LESSAND      -- <&
  | T_LESSGREAT    -- <>
  | T_Lparen       -- (
  | T_NEWLINE      -- newline
  | T_OR_IF        -- ||
  | T_Rbrace       -- }
  | T_Rparen       -- )
  | T_Select       -- select
  | T_Semi         -- ;
  | T_Then         -- then
  | T_Until        -- until
  | T_While        -- while

  -- Tokens with simple string content
  | T_Glob (pattern : String)
  | T_Literal (value : String)
  | T_SingleQuoted (value : String)
  | T_DollarSingleQuoted (value : String)
  | T_ParamSubSpecialChar (char : String)  -- e.g. '%' in ${foo%bar}
  | T_Pipe (pipeSym : String)              -- | or |&
  | T_UnparsedIndex (pos : SourcePos) (content : String)

  -- Complex tokens with children
  | T_AndIf (left right : t)
  | T_OrIf (left right : t)
  | T_Arithmetic (expr : t)
  | T_Array (elements : List t)
  | T_IndexedElement (indices : List t) (value : t)
  | T_Assignment (mode : AssignmentMode) (name : String) (indices : List t) (value : t)
  | T_Backgrounded (cmd : t)
  | T_Backticked (content : List t)
  | T_Banged (cmd : t)
  | T_BraceExpansion (parts : List t)
  | T_BraceGroup (cmds : List t)
  | T_CaseExpression (word : t) (cases : List (CaseType × List t × List t))
  | T_Condition (condType : ConditionType) (expr : t)
  | T_DollarArithmetic (expr : t)
  | T_DollarBraced (braced : Bool) (content : t)
  | T_DollarBracket (expr : t)
  | T_DollarDoubleQuoted (parts : List t)
  | T_DollarExpansion (cmds : List t)
  | T_DollarBraceCommandExpansion (isPiped : Piped) (cmds : List t)
  | T_DoubleQuoted (parts : List t)
  | T_Extglob (pattern : String) (parts : List t)
  | T_FdRedirect (fd : String) (target : t)
  | T_ForArithmetic (init cond incr : t) (body : List t)
  | T_ForIn (var : String) (words : List t) (body : List t)
  | T_Function (keyword : FunctionKeyword) (parens : FunctionParentheses) (name : String) (body : t)
  | T_HereDoc (isDashed : Dashed) (isQuoted : Quoted) (delimiter : String) (content : List t)
  | T_HereString (word : t)
  | T_IfExpression (conditions : List (List t × List t)) (elseBody : List t)
  | T_IoFile (op : t) (file : t)
  | T_IoDuplicate (op : t) (fd : String)
  | T_NormalWord (parts : List t)
  | T_Pipeline (separators : List t) (commands : List t)
  | T_ProcSub (direction : String) (cmds : List t)  -- direction is "<" or ">"
  | T_Redirecting (redirects : List t) (cmd : t)
  | T_Script (shebang : t) (commands : List t)
  | T_SelectIn (var : String) (words : List t) (body : List t)
  | T_SimpleCommand (assignments : List t) (words : List t)
  | T_Subshell (cmds : List t)
  | T_UntilExpression (cond : List t) (body : List t)
  | T_WhileExpression (cond : List t) (body : List t)
  | T_Annotation (annotations : List Annotation) (cmd : t)
  | T_CoProc (name : Option t) (body : t)
  | T_CoProcBody (body : t)
  | T_Include (script : t)
  | T_SourceCommand (source : t) (script : t)
  | T_BatsTest (name : String) (body : t)
  deriving Repr, BEq, Inhabited

/-- A token with an ID and inner content.
    Note: We use a structure rather than mutual inductive to simplify things.
    The inner token is parameterized to allow recursive definitions. -/
structure Token where
  id : Id
  inner : InnerToken Token
  deriving Repr, Inhabited

/-- Root of a shell script AST -/
structure Root where
  token : Token
  deriving Repr, Inhabited

-- Note: BEq Token is intentionally left out for now due to recursive type complexity.
-- Token equality can be checked by comparing IDs: t1.id == t2.id

/-- Get the ID of a token -/
def getId (t : Token) : Id := t.id

/-- Create a token with given ID and inner content -/
def mkToken (id : Id) (inner : InnerToken Token) : Token := ⟨id, inner⟩

-- Smart constructors for common patterns
def T_Literal' (id : Id) (s : String) : Token := mkToken id (.T_Literal s)
def T_SingleQuoted' (id : Id) (s : String) : Token := mkToken id (.T_SingleQuoted s)
def T_Glob' (id : Id) (s : String) : Token := mkToken id (.T_Glob s)

-- Analysis functions

/-- Do nothing -/
def blank [Monad m] (_ : Token) : m Unit := pure ()

/-- Analyze a token tree, calling f before recursing, g after, and i to transform -/
partial def analyze [Monad m]
    (f : Token → m Unit)
    (g : Token → m Unit)
    (transform : Token → m Token)
    (t : Token) : m Token := do
  f t
  let newInner ← traverseInner t.inner
  g t
  transform (mkToken t.id newInner)
where
  traverseInner (inner : InnerToken Token) : m (InnerToken Token) := do
    match inner with
    | .TA_Binary op l r => return .TA_Binary op (← analyze f g transform l) (← analyze f g transform r)
    | .TA_Assignment op l r => return .TA_Assignment op (← analyze f g transform l) (← analyze f g transform r)
    | .TA_Variable n is => return .TA_Variable n (← is.mapM (analyze f g transform))
    | .TA_Expansion ps => return .TA_Expansion (← ps.mapM (analyze f g transform))
    | .TA_Sequence es => return .TA_Sequence (← es.mapM (analyze f g transform))
    | .TA_Parenthesis e => return .TA_Parenthesis (← analyze f g transform e)
    | .TA_Trinary c t e => return .TA_Trinary (← analyze f g transform c) (← analyze f g transform t) (← analyze f g transform e)
    | .TA_Unary op e => return .TA_Unary op (← analyze f g transform e)
    | .TC_And ct op l r => return .TC_And ct op (← analyze f g transform l) (← analyze f g transform r)
    | .TC_Binary ct op l r => return .TC_Binary ct op (← analyze f g transform l) (← analyze f g transform r)
    | .TC_Group ct e => return .TC_Group ct (← analyze f g transform e)
    | .TC_Nullary ct e => return .TC_Nullary ct (← analyze f g transform e)
    | .TC_Or ct op l r => return .TC_Or ct op (← analyze f g transform l) (← analyze f g transform r)
    | .TC_Unary ct op e => return .TC_Unary ct op (← analyze f g transform e)
    | .TC_Empty ct => return .TC_Empty ct
    | .T_AND_IF => return .T_AND_IF
    | .T_Bang => return .T_Bang
    | .T_Case => return .T_Case
    | .T_CLOBBER => return .T_CLOBBER
    | .T_DGREAT => return .T_DGREAT
    | .T_DLESS => return .T_DLESS
    | .T_DLESSDASH => return .T_DLESSDASH
    | .T_Do => return .T_Do
    | .T_Done => return .T_Done
    | .T_DSEMI => return .T_DSEMI
    | .T_Elif => return .T_Elif
    | .T_Else => return .T_Else
    | .T_EOF => return .T_EOF
    | .T_Esac => return .T_Esac
    | .T_Fi => return .T_Fi
    | .T_For => return .T_For
    | .T_GREATAND => return .T_GREATAND
    | .T_Greater => return .T_Greater
    | .T_If => return .T_If
    | .T_In => return .T_In
    | .T_Lbrace => return .T_Lbrace
    | .T_Less => return .T_Less
    | .T_LESSAND => return .T_LESSAND
    | .T_LESSGREAT => return .T_LESSGREAT
    | .T_Lparen => return .T_Lparen
    | .T_NEWLINE => return .T_NEWLINE
    | .T_OR_IF => return .T_OR_IF
    | .T_Rbrace => return .T_Rbrace
    | .T_Rparen => return .T_Rparen
    | .T_Select => return .T_Select
    | .T_Semi => return .T_Semi
    | .T_Then => return .T_Then
    | .T_Until => return .T_Until
    | .T_While => return .T_While
    | .T_Glob p => return .T_Glob p
    | .T_Literal v => return .T_Literal v
    | .T_SingleQuoted v => return .T_SingleQuoted v
    | .T_DollarSingleQuoted v => return .T_DollarSingleQuoted v
    | .T_ParamSubSpecialChar c => return .T_ParamSubSpecialChar c
    | .T_Pipe s => return .T_Pipe s
    | .T_UnparsedIndex p c => return .T_UnparsedIndex p c
    | .T_AndIf l r => return .T_AndIf (← analyze f g transform l) (← analyze f g transform r)
    | .T_OrIf l r => return .T_OrIf (← analyze f g transform l) (← analyze f g transform r)
    | .T_Arithmetic e => return .T_Arithmetic (← analyze f g transform e)
    | .T_Array es => return .T_Array (← es.mapM (analyze f g transform))
    | .T_IndexedElement is v => return .T_IndexedElement (← is.mapM (analyze f g transform)) (← analyze f g transform v)
    | .T_Assignment m n is v => return .T_Assignment m n (← is.mapM (analyze f g transform)) (← analyze f g transform v)
    | .T_Backgrounded c => return .T_Backgrounded (← analyze f g transform c)
    | .T_Backticked cs => return .T_Backticked (← cs.mapM (analyze f g transform))
    | .T_Banged c => return .T_Banged (← analyze f g transform c)
    | .T_BraceExpansion ps => return .T_BraceExpansion (← ps.mapM (analyze f g transform))
    | .T_BraceGroup cs => return .T_BraceGroup (← cs.mapM (analyze f g transform))
    | .T_CaseExpression w cases => do
        let w' ← analyze f g transform w
        let cases' ← cases.mapM fun (ct, pats, body) => do
          let pats' ← pats.mapM (analyze f g transform)
          let body' ← body.mapM (analyze f g transform)
          return (ct, pats', body')
        return .T_CaseExpression w' cases'
    | .T_Condition ct e => return .T_Condition ct (← analyze f g transform e)
    | .T_DollarArithmetic e => return .T_DollarArithmetic (← analyze f g transform e)
    | .T_DollarBraced b c => return .T_DollarBraced b (← analyze f g transform c)
    | .T_DollarBracket e => return .T_DollarBracket (← analyze f g transform e)
    | .T_DollarDoubleQuoted ps => return .T_DollarDoubleQuoted (← ps.mapM (analyze f g transform))
    | .T_DollarExpansion cs => return .T_DollarExpansion (← cs.mapM (analyze f g transform))
    | .T_DollarBraceCommandExpansion p cs => return .T_DollarBraceCommandExpansion p (← cs.mapM (analyze f g transform))
    | .T_DoubleQuoted ps => return .T_DoubleQuoted (← ps.mapM (analyze f g transform))
    | .T_Extglob p ps => return .T_Extglob p (← ps.mapM (analyze f g transform))
    | .T_FdRedirect fd t => return .T_FdRedirect fd (← analyze f g transform t)
    | .T_ForArithmetic i c inc body => return .T_ForArithmetic (← analyze f g transform i) (← analyze f g transform c) (← analyze f g transform inc) (← body.mapM (analyze f g transform))
    | .T_ForIn v ws body => return .T_ForIn v (← ws.mapM (analyze f g transform)) (← body.mapM (analyze f g transform))
    | .T_Function kw par n body => return .T_Function kw par n (← analyze f g transform body)
    | .T_HereDoc d q del cs => return .T_HereDoc d q del (← cs.mapM (analyze f g transform))
    | .T_HereString w => return .T_HereString (← analyze f g transform w)
    | .T_IfExpression conds els => do
        let conds' ← conds.mapM fun (c, b) => do
          let c' ← c.mapM (analyze f g transform)
          let b' ← b.mapM (analyze f g transform)
          return (c', b')
        let els' ← els.mapM (analyze f g transform)
        return .T_IfExpression conds' els'
    | .T_IoFile op file => return .T_IoFile (← analyze f g transform op) (← analyze f g transform file)
    | .T_IoDuplicate op fd => return .T_IoDuplicate (← analyze f g transform op) fd
    | .T_NormalWord ps => return .T_NormalWord (← ps.mapM (analyze f g transform))
    | .T_Pipeline seps cmds => return .T_Pipeline (← seps.mapM (analyze f g transform)) (← cmds.mapM (analyze f g transform))
    | .T_ProcSub dir cs => return .T_ProcSub dir (← cs.mapM (analyze f g transform))
    | .T_Redirecting rs c => return .T_Redirecting (← rs.mapM (analyze f g transform)) (← analyze f g transform c)
    | .T_Script sh cs => return .T_Script (← analyze f g transform sh) (← cs.mapM (analyze f g transform))
    | .T_SelectIn v ws body => return .T_SelectIn v (← ws.mapM (analyze f g transform)) (← body.mapM (analyze f g transform))
    | .T_SimpleCommand as ws => return .T_SimpleCommand (← as.mapM (analyze f g transform)) (← ws.mapM (analyze f g transform))
    | .T_Subshell cs => return .T_Subshell (← cs.mapM (analyze f g transform))
    | .T_UntilExpression c body => return .T_UntilExpression (← c.mapM (analyze f g transform)) (← body.mapM (analyze f g transform))
    | .T_WhileExpression c body => return .T_WhileExpression (← c.mapM (analyze f g transform)) (← body.mapM (analyze f g transform))
    | .T_Annotation anns c => return .T_Annotation anns (← analyze f g transform c)
    | .T_CoProc n body => do
        let n' ← match n with
          | some t => some <$> analyze f g transform t
          | none => pure none
        return .T_CoProc n' (← analyze f g transform body)
    | .T_CoProcBody body => return .T_CoProcBody (← analyze f g transform body)
    | .T_Include s => return .T_Include (← analyze f g transform s)
    | .T_SourceCommand src scr => return .T_SourceCommand (← analyze f g transform src) (← analyze f g transform scr)
    | .T_BatsTest n body => return .T_BatsTest n (← analyze f g transform body)

/-- Analyze a token tree, calling f on each node before recursing -/
def doAnalysis [Monad m] (f : Token → m Unit) : Token → m Token :=
  analyze f blank pure

/-- Analyze a token tree, calling startToken before and endToken after recursing -/
def doStackAnalysis [Monad m] (startToken endToken : Token → m Unit) : Token → m Token :=
  analyze startToken endToken pure

/-- Transform each token in the tree -/
def doTransform (transform : Token → Token) (t : Token) : Token :=
  Id.run <| analyze blank blank (pure ∘ transform) t

-- Theorems (stubs)
theorem getId_mkToken (id : Id) (inner : InnerToken Token) :
    getId (mkToken id inner) = id := rfl

/-- Tokens with the same inner content are semantically equal -/
theorem inner_eq_implies_semantic_eq (t1 t2 : Token) (h : t1.inner = t2.inner) :
    t1.id = t2.id → t1 = t2 := by
  intro hid
  cases t1; cases t2
  simp_all

/-- doTransform applies transform to leaves -/
theorem doTransform_applies (_transform : Token → Token) (_t : Token) :
    True := trivial  -- Placeholder for actual property

end ShellCheck.AST
