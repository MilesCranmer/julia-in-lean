import JuliaLean.BroadcastViews.Shape

/-!
View-of-view index composition, `reindex` (`base/subarray.jl:292-312`) as used by
`unsafe_view(V::SubArray, I...)` → `_maybe_reindex` (lines 267-280) and by
`getindex(V::SubArray, I::Vararg{Int})` (lines 316-321), master `bbfa0ce4150`.

A stored index (after `to_indices`) is a `VIdx`: an `Int`, `Slice(OneTo(n))` (from `:`), or a
one-based `AbstractVector{Int}` given by its elements (`UnitRange`, `StepRange`, `OneTo`,
`Vector{Int}`, a `LogicalIndex` of a `Bool` vector, an array of `CartesianIndex{1}`, which
`_maybe_reindex` treats like `Int`s, line 273). Indices with offset axes
(`IdentityUnitRange`, #62906) and arrays of `CartesianIndex{N}`, `N ≥ 2` (which keep two view
layers) are outside the model.
-/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- A view index after `to_indices`. -/
inductive VIdx where
  | scalar (i : Int)
  | slice (n : Nat)
  | vec (xs : List Int)
  deriving DecidableEq, Repr

/-- `xs[k]` for a one-based vector index. -/
def at1 (xs : List Int) (k : Int) : Int := xs.getD (k - 1).toNat 0

/-- `idxs[1][subidxs[1]]` for a vector parent index (`base/subarray.jl:304`): indexing a vector
with an `Int`, a `Slice(OneTo(m))` or a vector. -/
def index1 (xs : List Int) : VIdx → VIdx
  | .scalar k => .scalar (at1 xs k)
  | .slice m => .vec ((List.range m).map (fun k : Nat => at1 xs ((k : Int) + 1)))
  | .vec ks => .vec (ks.map (at1 xs))

/-- `reindex(idxs, subidxs)`, `base/subarray.jl:292-304`: scalars are kept and consume no
sub-index (295-296), a `Slice` passes its sub-index through (299-300), a vector index is indexed by
its sub-index (303-304). -/
def reindex : List VIdx → List VIdx → List VIdx
  | [], _ => []
  | .scalar i :: is, js => .scalar i :: reindex is js
  | .slice _ :: is, j :: js => j :: reindex is js
  | .vec xs :: is, j :: js => index1 xs j :: reindex is js
  | _ :: _, [] => []

/-- The parent subscripts read by `V[K...]` for a view with stored indices `I` and `Int`
subscripts `K` (`getindex(V::SubArray, I::Vararg{Int,N})`, line 319). -/
def readSubs (I : List VIdx) (K : List Int) : List VIdx := reindex I (K.map .scalar)

/-- `K` lies inside the axes of the view with stored indices `J` (one subscript per non-scalar
index). -/
def KInBounds : List VIdx → List Int → Prop
  | [], _ => True
  | .scalar _ :: js, K => KInBounds js K
  | .slice m :: js, k :: K => 1 ≤ k ∧ k ≤ m ∧ KInBounds js K
  | .vec ks :: js, k :: K => 1 ≤ k ∧ k ≤ ks.length ∧ KInBounds js K
  | _ :: _, [] => True

end JuliaLean.BroadcastViews
