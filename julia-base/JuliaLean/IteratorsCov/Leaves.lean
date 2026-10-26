import JuliaLean.IteratorsCov.Base

/-!
# Leaf iterators: vectors and tuples

`iterate(A::AbstractArray, i = firstindex(A))` for `IndexLinear` arrays
(base/abstractarray.jl:1250-1260) and `iterate(t::Tuple, i = 1)`
(base/tuple.jl:69-73) both use the next index as state:
`checkbounds(Bool, A, i) ? (A[i], i + 1) : nothing`.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `A[i]` for `1 ≤ i ≤ length(A)` (Julia indices are 1-based here). -/
def getIdx (xs : List V) (i : Int) : V := xs.getD (i - 1).toNat .nothing

/-- One indexed iteration step from index `i`. -/
def idxStep (xs : List V) (i : Int) : Step :=
  if 1 ≤ i ∧ i ≤ xs.length then .ok (some (getIdx xs i, .int (i + 1))) else .ok none

/-- `iterate(A, s)` for an indexed collection; a non-integer state is a
`MethodError`. -/
def idxNext (xs : List V) : V → Step
  | .int i => idxStep xs i
  | _ => jthrow (.methodError "iterate")

/-- A `Vector{et}` with elements `xs`: `IteratorSize` `HasShape{1}`
(base/generator.jl:101), `length`, `size`, `eltype`. -/
def vecIt (et : Ty) (xs : List V) : It where
  first := idxStep xs 1
  next := idxNext xs
  isz := .hasShape 1
  elt := et
  len := .ok (i64 xs.length)
  size := .ok [i64 xs.length]

/-- A tuple with elements `xs` and type `Tuple{ts...}`: `IteratorSize`
`HasLength` (base/generator.jl:100). -/
def tupIt (ts : List Ty) (xs : List V) : It where
  first := idxStep xs 1
  next := idxNext xs
  isz := .hasLength
  elt := ts.foldr .union .bottom
  len := .ok (i64 xs.length)

theorem idxStep_YF (xs : List V) : ∀ (k : Nat) (i : Int), i = xs.length - k + 1 → 1 ≤ i →
    YF (idxNext xs) (idxStep xs i) (xs.drop (i - 1).toNat) := by
  intro k
  induction k with
  | zero =>
    intro i hi _
    have : ¬ (1 ≤ i ∧ i ≤ xs.length) := by omega
    simp only [idxStep, this, if_false]
    have : xs.drop (i - 1).toNat = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; exact .nil
  | succ k ih =>
    intro i hi h1
    by_cases hk : k + 1 ≤ xs.length
    · have hc : 1 ≤ i ∧ i ≤ xs.length := by omega
      simp only [idxStep, hc, and_self, if_true]
      have hd : xs.drop (i - 1).toNat = getIdx xs i :: xs.drop (i + 1 - 1).toNat := by
        have hlt : (i - 1).toNat < xs.length := by omega
        rw [List.drop_eq_getElem_cons hlt]
        simp only [getIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        congr 2; omega
      rw [hd]
      exact .cons (ih (i + 1) (by omega) (by omega))
    · have : ¬ (1 ≤ i ∧ i ≤ xs.length) := by omega
      simp only [idxStep, this, if_false]
      have : xs.drop (i - 1).toNat = [] := List.drop_eq_nil_of_le (by omega)
      rw [this]; exact .nil

/-- Iterating an indexed collection yields its elements. -/
theorem idx_yields (xs : List V) : YF (idxNext xs) (idxStep xs 1) xs := by
  have := idxStep_YF xs xs.length 1 (by omega) (Int.le_refl _)
  simpa using this

theorem vecIt_yields (et : Ty) (xs : List V) : (vecIt et xs).Yields xs := idx_yields xs

theorem tupIt_yields (ts : List Ty) (xs : List V) : (tupIt ts xs).Yields xs := idx_yields xs

end JuliaLean.IteratorsCov
