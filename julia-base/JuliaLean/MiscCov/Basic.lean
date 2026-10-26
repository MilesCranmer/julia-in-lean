import JuliaLean.Core

/-!
Shared definitions of the `MiscCov` area: the Julia exceptions the modelled
methods throw and a small Julia syntax tree for the macros of
`base/deprecated.jl`, `base/experimental.jl`, `base/c.jl`, `base/osutils.jl`
and `base/opaque_closure.jl` (master `bbfa0ce4150`).
-/

namespace JuliaLean.MiscCov

/-- The exception types thrown by the modelled methods. Messages are kept only
where a property is about them. -/
inductive Err where
  | errorException (msg : String)
  | argumentError (msg : String)
  | typeError
  | methodError
  | inexactError
  | overflowError
  | boundsError
  | undefRefError
  | assertionError
  | fieldError
  | other (name : String)
  deriving Repr, DecidableEq, Inhabited

deriving instance DecidableEq for Except

/-- A Julia computation that returns a value or throws. -/
abbrev M (α : Type) := Except Err α

/-- Julia syntax values: `Symbol`s, literals, `QuoteNode`, `GlobalRef`,
`LineNumberNode`, other runtime values (by a descriptive tag) and `Expr`. -/
inductive Ex where
  | sym (name : String)
  | str (value : String)
  | int (value : Int)
  | bool (value : Bool)
  | nothing
  | qn (value : Ex)
  | gref (mod name : String)
  | lnn
  | val (tag : String)
  | expr (head : String) (args : List Ex)
  deriving Repr, Inhabited

namespace Ex

/-- `Meta.isexpr(ex, head)`. -/
def isExpr (ex : Ex) (head : String) : Bool :=
  match ex with
  | .expr h _ => h == head
  | _ => false

/-- `ex.args` of an `Expr`; `none` for other values (a `FieldError` in Julia). -/
def args? : Ex → Option (List Ex)
  | .expr _ a => some a
  | _ => none

/-- `ex isa LineNumberNode`. -/
def isLnn : Ex → Bool
  | .lnn => true
  | _ => false

/-- `ex === :name`. -/
def isSym (name : String) : Ex → Bool
  | .sym s => s == name
  | _ => false

/-- `esc(ex)`, `base/essentials.jl`. -/
def esc (ex : Ex) : Ex := .expr "escape" [ex]

end Ex

end JuliaLean.MiscCov
