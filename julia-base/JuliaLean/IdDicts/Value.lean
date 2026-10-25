import JuliaLean.Core

/-!
# Values, `===`, `isequal` and types for the identity collections

`IdDict`, `IdSet` and `WeakValueIdDict` compare keys with `===` (`egal`);
`Set`, `Dict` and `WeakKeyDict` compare with `isequal`. The bugs of this area
live in the gap between the two, so the value universe has `===`-distinct
values that are `isequal`:

* `int n` (`Int64`) and `flt n` (the `Float64` with integral value `n`):
  `isequal(1, 1.0)`, `1 !== 1.0`;
* `vec id c` (`Vector{Int}` holding `[c]`) and `fvec id c` (`Vector{Float64}`
  holding `[c.0]`): mutable, so `===` compares the object identity `id`
  (together with the constructor), while `isequal` compares contents;
* `sym s` (`Symbol`) and `str s` (`String`): `===` and `isequal` both
  compare contents (Julia's egal compares `String` bytes);
* `nothing`.

No arithmetic is performed on `int n` or `flt n`; they are opaque Julia
values, so `Int` is enough to name them. `==` (used by `in` on vectors)
coincides with `isequal` on this universe: it has no `NaN`, `-0.0` or
`missing`.
-/

namespace JuliaLean.IdDicts

/-- Julia values used as keys, values and elements. -/
inductive JVal where
  | int (n : Int)
  | flt (n : Int)
  | sym (s : String)
  | str (s : String)
  | vec (id : Nat) (c : Int)
  | fvec (id : Nat) (c : Int)
  | nothing
  deriving Repr, DecidableEq

/-- `===` (`jl_egal`): every constructor argument is part of the identity. -/
def egal (a b : JVal) : Bool := a == b

/-- `isequal` on the universe (base/operators.jl; `isequal(1, 1.0)`,
`isequal([1], [1.0])`). -/
def isequal : JVal → JVal → Bool
  | .int a, .int b => a == b
  | .int a, .flt b => a == b
  | .flt a, .int b => a == b
  | .flt a, .flt b => a == b
  | .sym a, .sym b => a == b
  | .str a, .str b => a == b
  | .vec _ a, .vec _ b => a == b
  | .vec _ a, .fvec _ b => a == b
  | .fvec _ a, .vec _ b => a == b
  | .fvec _ a, .fvec _ b => a == b
  | .nothing, .nothing => true
  | _, _ => false

/-- `Base.secret_table_token`, base/abstractdict.jl:17: an ordinary interned
`Symbol` that any program can construct with `Symbol("...")`. -/
def token : JVal := .sym "__c782dbf1cf4d6a2e5e3865d7e95634f2e09b5902__"

/-- Julia types used as type parameters. -/
inductive JTy where
  | any | int | flt | sym | str | vec | fvec | nothing
  deriving Repr, DecidableEq

/-- `isa(x, T)`. -/
def isa : JVal → JTy → Bool
  | _, .any => true
  | .int _, .int => true
  | .flt _, .flt => true
  | .sym _, .sym => true
  | .str _, .str => true
  | .vec _ _, .vec => true
  | .fvec _ _, .fvec => true
  | .nothing, .nothing => true
  | _, _ => false

/-- Exceptions of the modelled calls (types only). -/
inductive IErr where
  | keyError
  /-- `TypeError`: `KeyTypeError` (base/abstractdict.jl:15) or a failed `::T` -/
  | typeError
  /-- `MethodError` from `convert` -/
  | methodError
  | argumentError
  /-- `ErrorException`, e.g. from `finalizer` on an immutable (base/gcutils.jl:44) -/
  | errorException
  /-- a failed `@assert` -/
  | assertionError
  deriving Repr, DecidableEq

/-- `convert(T, x)` on the universe: identity when `isa(x, T)`, the numeric
conversions `Int64 ↔ Float64` of integral values, and `Vector{Int} ↔
Vector{Float64}`, which allocates a new array (modelled as the object with the
other constructor and the same `id`, `===`-distinct from `x`). Every other
pair is a `MethodError`. -/
def convert (T : JTy) (x : JVal) : Except IErr JVal :=
  if isa x T then .ok x else
  match T, x with
  | .int, .flt n => .ok (.int n)
  | .flt, .int n => .ok (.flt n)
  | .vec, .fvec i c => .ok (.vec i c)
  | .fvec, .vec i c => .ok (.fvec i c)
  | _, _ => .error .methodError

/-- Objects that `finalizer` accepts (mutable types; base/gcutils.jl:42-45). -/
def finalizable : JVal → Bool
  | .str _ | .vec _ _ | .fvec _ _ => true
  | _ => false

/-- A call's final state together with its result: Julia mutates in place,
so a call that throws after a mutation leaves the mutated state. -/
abbrev Out (σ α : Type) := σ × Except IErr α

/-- `decide` on call results. -/
instance instDecidableEqExceptIErr {α} [DecidableEq α] : DecidableEq (Except IErr α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

theorem egal_iff (a b : JVal) : egal a b = true ↔ a = b := by
  simp [egal]

theorem convert_isa {T : JTy} {x w : JVal} (h : convert T x = .ok w) : isa w T = true := by
  unfold convert at h
  split at h
  · cases h; assumption
  · split at h <;> first | (cases h; rfl) | cases h

end JuliaLean.IdDicts
