import JuliaLean.BitArrays.Vector

/-!
# `Vector{Bool}` reference semantics and exception kinds

The properties compare each `BitVector` method with the same method on a
`Vector{Bool}` holding the same elements (`base/array.jl`, master
`bbfa0ce4150`). Element lists are `List Bool`; positions are 1-based as in Julia.

`JlError` (Core) has no `DimensionMismatch`; this area encodes it as
`.argumentError "DimensionMismatch"`. Properties compare exception *types*
(`ExcType`), not messages, since the two implementations word their messages
differently (`pop!` says "argument must not be empty" for `BitVector` and
"array must be non-empty" for `Vector`).
-/

namespace JuliaLean.BitArrays

/-- Julia exception types that occur in this area. -/
inductive ExcType where
  | argument | bounds | dimensionMismatch | divide | inexact | other
  deriving DecidableEq, Repr

def dimMismatch : JlError := .argumentError "DimensionMismatch"

def excType : JlError → ExcType
  | .argumentError m => if m = "DimensionMismatch" then .dimensionMismatch else .argument
  | .boundsError => .bounds
  | .divideError => .divide
  | .inexactError _ => .inexact
  | _ => .other

/-- A Julia result up to the exception message. -/
def kindOf {α : Type} : Jl α → Except ExcType α
  | .ok a => .ok a
  | .error e => .error (excType e)

/-- Product of a size tuple. -/
def dimsProd (dims : List Nat) : Nat := dims.foldl (· * ·) 1

namespace Ref

/-- `deleteat!(a::Vector, r::AbstractUnitRange{<:Integer})`, `base/array.jl:1905-1914`,
with `_deleteat!(a, i, delta)`'s checks at `base/array.jl:1312-1318`: an empty
range deletes nothing; otherwise `1 ≤ first(r)` and `last(r) ≤ length(a)`. -/
def deleteatRange (l : List Bool) (r : URange) : Jl (List Bool) :=
  if r.length = 0 then .ok l else
  if ¬ (1 ≤ r.first.val ∧ r.first.val ≤ l.length) then .error .boundsError else
  if ¬ (r.first.val + r.length ≤ l.length + 1) then .error .boundsError else
  let f := r.first.val.toNat
  .ok (l.take (f - 1) ++ l.drop (f - 1 + r.length.toNat))

/-- `circshift!(a::AbstractVector, shift::Integer)`, `base/abstractarray.jl:3756-3766`:
empty vectors are returned unchanged; otherwise element `k` moves to
`mod1(k + shift, n)`. -/
def circshift (l : List Bool) (k : JInt64) : List Bool :=
  let n := l.length
  if n = 0 then l else
  let s := (k.val % n).toNat
  l.drop (n - s) ++ l.take (n - s)

/-- Small integer types whose `add_sum` with a `Bool` promotes to `Int`,
`base/reduce.jl:17` (`Union{Bool,BitIntegerSmall}`). -/
def smallInt : IntTy → Bool
  | .i8 | .i16 | .i32 | .u8 | .u16 | .u32 => true
  | _ => false

/-- `count(a::Vector{Bool}; init)` as an `Int`-valued result:
`_simple_count(identity, ::Array{Bool}, init)`, `base/reduce.jl:1097-1113`, starts
from `v0 = add_sum(init, false)`, an `Int` for small `init` types (since #58374),
and accumulates `(n + c) % typeof(v0)`. -/
def count (t : IntTy) (init : JInt t) (l : List Bool) : Int :=
  let c := (l.filter id).length
  if smallInt t then wrapInt .i64 (init.val + c) else wrapInt t (init.val + c)

/-- `A[I] = X` for `A::Vector{Bool}` and a logical mask `I` of the same length:
`setindex_shape_check(X, count(I))` (`base/indices.jl`) throws
`DimensionMismatch` before any element is written. -/
def setindexMask (l : List Bool) (X : List Bool) (I : List Bool) : List Bool × Option JlError :=
  if l.length ≠ I.length then (l, some .boundsError) else
  if X.length ≠ (I.filter id).length then (l, some dimMismatch) else
  let rec go : List Bool → List Bool → List Bool → List Bool
    | _ :: as, true :: is, x :: xs => x :: go as is xs
    | a :: as, true :: is, [] => a :: go as is []
    | a :: as, false :: is, xs => a :: go as is xs
    | as, _, _ => as
  (go l I X, none)

/-- `reverse(A; dims=d)` for `A::Array{Bool}` of size `dims` (column-major
element list `l`): the element with coordinate `c` along dimension `d` moves to
coordinate `size(A, d) - 1 - c` (0-based), the others stay. -/
def reverseDims (l : List Bool) (dims : List Nat) (d : Nat) : List Bool :=
  let M := dimsProd (dims.take (d - 1))
  let sd := dims.getD (d - 1) 0
  (List.range l.length).map (fun t =>
    let c := (t / M) % sd
    l.getD (t - c * M + (sd - 1 - c) * M) false)

end Ref

end JuliaLean.BitArrays
