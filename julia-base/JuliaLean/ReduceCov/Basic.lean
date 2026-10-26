import JuliaLean.Core

/-!
Shared definitions of the `ReduceCov` area: the exceptions thrown by the modelled
methods of `base/reduce.jl`, `base/reducedim.jl`, `base/indices.jl`, `base/some.jl`
and `base/missing.jl` (master `bbfa0ce4150`).
-/

namespace JuliaLean.ReduceCov

/-- Julia exceptions of this area: the shared `JlError`s and the exception types
`JlError` does not have. -/
inductive Err where
  | jl (e : JlError)
  | dimensionMismatch (msg : String)
  | missingException (msg : String)
  | errorException (msg : String)
  | typeError
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call of this area that may throw. -/
abbrev RJ (α : Type) := Except Err α

instance instDecidableEqRJ {α : Type} [DecidableEq α] : DecidableEq (RJ α) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .error x, .error y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => isFalse (by intro e; cases e)
  | .error _, .ok _ => isFalse (by intro e; cases e)

/-- `ArgumentError(msg)`. -/
def argErr (msg : String) : Err := .jl (.argumentError msg)

/-- `BoundsError`. -/
def boundsErr : Err := .jl .boundsError

abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

end JuliaLean.ReduceCov
