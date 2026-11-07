import JuliaLean.base.abstractarraymath
import JuliaLean.Proofs.base.subarray.cartesian_views

namespace JuliaLean.Multidim

/-- The documented result of `circshift`: `circshift(A, s)[J] == A[mod.(J .- 1 .- s, n) .+ 1]`
for each dimension (missing shifts are zero), for every `Array` and every tuple of
integer shift amounts no longer than `ndims(A)`. -/
def CircshiftFormula : Prop :=
  ∀ (sz : List Nat) (shifts : List Int) (src : List Int → Int),
    (∀ n ∈ sz, n < 2 ^ 62) → shifts.length ≤ sz.length →
    ∃ dest, circshift sz src shifts = .ok dest ∧
      ∀ J : List Int, inAxes (oneAxes sz) J = true →
        dest J = some (src ((J.zip (sz.zip (shifts ++ List.replicate (sz.length - shifts.length) 0))).map
          fun (j, n, s) => (j - 1 - s) % (n : Int) + 1))

/-- The size of `repeat(A; inner, outer)` is `size(A) .* inner .* outer` after padding all
three with ones to a common length; negative counts, and too few `inner` counts (or too few
`outer` counts when `inner` is given), are an `ArgumentError`. -/
def RepeatShape : Prop :=
  ∀ (sz : List Int) (inner outer : Option (List Int)),
    (∀ n ∈ sz, 0 ≤ n ∧ n < 2 ^ 20) →
    (∀ i, inner = some i → ∀ x ∈ i, x < 2 ^ 20 ∧ -2 ^ 20 < x) →
    (∀ o, outer = some o → ∀ x ∈ o, x < 2 ^ 20 ∧ -2 ^ 20 < x) →
    let N := max sz.length (max ((inner.map List.length).getD 0) ((outer.map List.length).getD 0))
    let ii := (inner.map (padOnes · N)).getD (List.replicate N 1)
    let oo := (outer.map (padOnes · N)).getD (List.replicate N 1)
    repeatSize sz inner outer =
      if (∀ i, inner = some i → (∀ x ∈ i, 0 ≤ x) ∧ sz.length ≤ i.length) ∧
          (∀ o, outer = some o → (∀ x ∈ o, 0 ≤ x) ∧ (sz.length ≤ o.length ∨ inner = none))
      then .ok ((List.range N).map fun d => (padOnes sz N).getD d 1 * ii.getD d 1 * oo.getD d 1)
      else .error .argumentError

/-- For `1 ≤ d ≤ ndims(A)` and a one-dimensional index `i`, `selectdim(A, d, i)` is
`view(A, :, ..., :, i, :, ..., :)` with `i` in position `d` (same size or same exception). -/
def SelectdimInRange : Prop :=
  ∀ (sz : List Nat) (d : Nat) (i : Idx), 1 ≤ d → d ≤ sz.length → i.ndims = 1 → (∀ n, i ≠ .slice n) →
    (selectdim sz d i >>= view sz) =
      view sz (List.replicate (d - 1) .colon ++ [i] ++ List.replicate (sz.length - d) .colon)

/-- A view returned by `selectdim(A, d, i)` addresses only positions inside `A`. -/
def SelectdimInBounds : Prop :=
  ∀ (sz : List Nat) (d : Int) (i : Idx), i ≠ .cart [] → (∀ n, i ≠ .slice n) →
    match selectdim sz d i with
    | .ok I => viewInBounds sz I = true
    | .error _ => True

/-- `selectdim(A, d, i)` is `view(A, :, ..., :, i, :, ..., :)` with `i` in position `d`
(same size, or the same exception), for every `d ≥ 1` and every one-dimensional index. -/
def SelectdimViewAgrees : Prop :=
  ∀ (sz : List Nat) (d : Nat) (i : Idx), 1 ≤ d → i.ndims = 1 → (∀ n, i ≠ .slice n) →
    (selectdim sz d i >>= view sz) =
      view sz (List.replicate (d - 1) .colon ++ [i] ++ List.replicate (sz.length - d) .colon)

end JuliaLean.Multidim
