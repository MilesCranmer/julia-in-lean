import JuliaLean.ReinterpretArrays.Views

/-!
`view(view(M, r, c), :)` for a matrix `M`, an `IdentityUnitRange` row index `r` and a scalar column
`c` (`base/subarray.jl`, `base/indices.jl`, master). Values are exact integers: every quantity below
is a small in-range `Int`.
-/

namespace JuliaLean.ReinterpretArrays

/-- First-dimension view indices: `Base.Slice(IdentityUnitRange(lo:hi))` or `IdentityUnitRange(lo:hi)`. -/
inductive RowIndex where
  | slice (lo hi : Int)
  | iur (lo hi : Int)
  deriving DecidableEq, Repr

/-- `first` and `last` of a row index. -/
def RowIndex.lo : RowIndex → Int | .slice lo _ => lo | .iur lo _ => lo
def RowIndex.hi : RowIndex → Int | .slice _ hi => hi | .iur _ hi => hi

/-- `offset1` of `SubArray(M, (I1, c))` for an `s1 × s2` matrix, `base/subarray.jl:34-44,478-490`:
`stride1 = 1` (`compute_stride1`, lines 448-455); a `Slice` first index takes the index-preserving
branch `compute_linindex(parent, I) - stride1*first(axes(parent, 1))` (line 481), any other range
`compute_linindex(parent, I) - stride1*first(axes1(I1))` (line 483). `compute_linindex` is
`1 + (first(I1) - 1) + (c - 1) * s1` (lines 486-500). -/
def offset1 (s1 : Int) (I1 : RowIndex) (c : Int) : Int :=
  let lin := 1 + (I1.lo - 1) + (c - 1) * s1
  match I1 with
  | .slice _ _ => lin - 1
  | .iur lo _ => lin - lo

/-- `view(view(M, IdentityUnitRange(lo:hi), c), :)`: `to_indices` turns `:` into
`Slice(axes(V, 1)) = Slice(IdentityUnitRange(lo:hi))`; `_maybe_reindex` (`base/subarray.jl:276-280`)
builds `SubArray(M, reindex(V.indices, I))`, and `reindex` (line 303) indexes
`IdentityUnitRange(lo:hi)[Slice(IdentityUnitRange(lo:hi))]`, which
`getindex(::IdentityUnitRange, ::AbstractUnitRange)` (`base/indices.jl`) returns as the `Slice`
itself. Returns the parent linear index read by `W[i]` (`_reindexlinear`, line 327). -/
def nestedColonParentIndex (s1 lo hi c i : Int) : Int :=
  offset1 s1 (.slice lo hi) c + 1 * i

/-- For every in-bounds `IdentityUnitRange(lo:hi)` row range, column `c` and `i ∈ lo:hi`,
`view(view(M, IdentityUnitRange(lo:hi), c), :)[i]` reads `M[i, c]` (linear index `i + (c-1)*s1`),
the same element as `view(M, IdentityUnitRange(lo:hi), c)[i]`. -/
def NestedColonViewCorrect : Prop :=
  ∀ (s1 s2 lo hi c i : Int), 1 ≤ lo → lo ≤ hi → hi ≤ s1 → 1 ≤ c → c ≤ s2 → lo ≤ i → i ≤ hi →
    nestedColonParentIndex s1 lo hi c i = i + (c - 1) * s1

/-- The single view reads the right element: `view(M, IdentityUnitRange(lo:hi), c)[i]` is `M[i, c]`. -/
theorem single_view_correct (s1 lo c i : Int) : offset1 s1 (.iur lo lo) c + 1 * i = i + (c - 1) * s1 := by
  simp only [offset1, RowIndex.lo]; omega

/-- `view(view(M, IdentityUnitRange(2:3), 2), :)[2]` for a `4 × 5` matrix reads `M[3, 2]`. -/
theorem nestedColonViewCorrect_refuted : ¬ NestedColonViewCorrect := by
  intro h
  have e := h 4 5 2 3 2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert e
  decide

end JuliaLean.ReinterpretArrays
