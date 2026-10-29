import JuliaLean.MultidimCov.ArrayV2Find

/-!
`indcopy(sz, I)` (master `base/array.jl:2970-2992`), called by
`get!(X, A, I::RangeVecIntList, default)` (`base/abstractarray.jl:1664-1669`).
An index collection for one dimension is its list of indices in order.
-/

namespace JuliaLean.MultidimCov.ArrayV2

/-- One entry of a tuple `I`: an `Int`, an `AbstractRange{Int}` or an `AbstractVector{Int}`. -/
inductive IdxArg where
  | int (i : Int)
  | range (xs : List Int)
  | vec (xs : List Int)

/-- `_findin(a, 1:k)` (base/array.jl:2910, 2903): the positions `i` with `a[i] in 1:k`. -/
def findinRange (a : List Int) (k : Int) : List Int :=
  ((pairsV a).filter fun p => decide (1 ≤ p.2 ∧ p.2 ≤ k)).map Prod.fst

/-- The comprehensions of base/array.jl:2970 `indcopy(sz::Dims, I::Vector)`: `s` is the
product of `sz[n:end]`; for each `i`, `dst[i] = _findin(I[i], i < n ? (1:sz[i]) : (1:s))` and
`src[i] = I[i][dst[i]]`. -/
def indcopyVec (sz : List Int) (I : List (List Int)) : List (List Int) × List (List Int) :=
  let n := I.length
  let s := (sz.drop (n - 1)).foldr (· * ·) 1
  let bound := fun (i : Nat) => if i + 1 < n then sz.getD i 0 else s
  let dst := (List.range n).map fun i => findinRange (I.getD i []) (bound i)
  let src := (List.range n).map fun i => (findinRange (I.getD i []) (bound i)).map fun k => (I.getD i []).getD (k - 1).toNat 0
  (dst, src)

/-- Dispatch of `indcopy(size(A), I)` for a tuple `I`: the method at base/array.jl:2981 takes
only `Tuple{Vararg{RangeIndex}}` (each entry an `Int` or a range), and `_findin` has no method
for an `Int` entry; any other tuple is a `MethodError`. -/
def indcopyTup (sz : List Int) (I : List IdxArg) : R (List (List Int) × List (List Int)) :=
  let elems := I.filterMap fun a => match a with
    | .range xs => some xs
    | _ => none
  if elems.length = I.length then .ok (indcopyVec sz elems) else .error .method

/-- `get(A, I, default)` for a tuple `I` of index ranges and index vectors (every
`RangeVecIntList`, `base/abstractarray.jl:1634-1671`) copies the in-bounds part exactly as for
the same indices given as a vector of index vectors. -/
def PIndcopy : Prop := ∀ (sz : List Int) (I : List IdxArg),
    (∀ a ∈ I, ∃ xs, a = .range xs ∨ a = .vec xs) →
    indcopyTup sz I = .ok (indcopyVec sz (I.map fun a => match a with
      | .range xs => xs
      | .vec xs => xs
      | .int i => [i]))

/-- `get(A, ([1, 2],), d)`: the tuple holds an index vector, and `indcopy` has no method. -/
theorem pIndcopy_refuted : ¬ PIndcopy := by
  intro h
  have := h [3] [.vec [1, 2]] (by simp)
  simp [indcopyTup] at this

end JuliaLean.MultidimCov.ArrayV2
