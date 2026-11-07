import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.entries
/-!
Executable control-flow models for the `base/sort.jl` findings catalogued by
the `SortTuplesCov` area. The public Julia reproducers exercise the complete methods.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean

def InsortedRangeAgrees : Prop :=
  ∀ x r, insortedRange x r = some (insortedVector x r)

theorem insortedRangeAgrees_refuted : ¬ InsortedRangeAgrees := by
  intro h
  have hne : insortedRange .negZero [.posZero, .one] ≠
      some (insortedVector .negZero [.posZero, .one]) := by decide
  exact hne (h .negZero [.posZero, .one])

/-- Supplying an accepted scratch vector must not make a supported legacy sort
entry throw on a valid window. -/
def LegacySortScratch : Prop :=
  ∀ (n lo hi : Int) (a : LegacyAlg), 1 ≤ lo → hi ≤ n →
    legacySortWithoutScratch n lo hi a = .ok () →
    legacySortWithScratch n lo hi a = .ok ()

theorem legacySortScratch_refuted : ¬ LegacySortScratch := by
  intro h
  have hne : legacySortWithScratch 5 2 4 .quick ≠ .ok () := by
    simp [legacySortWithScratch, legacySortFallback]
  exact hne (h 5 2 4 .quick (by decide) (by decide)
    (by simp [legacySortWithoutScratch]))

/-- A partial quicksort branch must not discard a side containing a requested
target position.  This is the local invariant required by the
`PartialQuickSort(k)` docstring. -/
def PartialQuickSortCorrect : Prop :=
  ∀ (lo hi firstTarget lastTarget : Int) (targets : List Int) (pivot : Int),
    targets.getLast? = some lastTarget →
    lo ≤ pivot → pivot ≤ hi →
    (targets.any fun k => k < pivot) →
    (targets.any fun k => pivot < k) →
    partialQuickAction lo hi firstTarget lastTarget pivot ≠ .skipLower ∧
      partialQuickAction lo hi firstTarget lastTarget pivot ≠ .skipUpper

theorem partialQuickSortCorrect_refuted : ¬ PartialQuickSortCorrect := by
  intro h
  have := h 1 22 5 3 [5, 4, 3] 4 (by simp) (by decide) (by decide)
    (by decide) (by decide)
  exact this.1 (by simp [partialQuickAction])

/-- `sort(x::NTuple; alg=...)`, `base/sort.jl:1785-1795`, promises a sorted
tuple for each built-in `Algorithm` accepted by its signature. -/
def SortNTupleAlgs : Prop := ∀ a : TupleAlg, ∃ r, sortTupleDispatch a = .ok r

theorem sortNTupleAlgs_refuted : ¬ SortNTupleAlgs := by
  intro h
  obtain ⟨r, hr⟩ := h .quick
  simp [sortTupleDispatch] at hr

def SortDimsChecked : Prop :=
  ∀ nd dims, (dims < 1 ∨ nd < dims) →
    sortDimsDefault nd dims = .error (.argumentError "dimension out of range")

theorem sortDimsChecked_refuted : ¬ SortDimsChecked := by
  intro h
  have hne : sortDimsDefault 2 0 ≠ .error (.argumentError "dimension out of range") := by
    intro hbad
    change Except.error JlError.boundsError =
      Except.error (JlError.argumentError "dimension out of range") at hbad
    cases hbad
  exact hne (h 2 0 (by decide))

/-- The keyword signature accepts `Vector{eltype(v)}` as scratch, so the sort
must succeed for a valid `Vector{Union{Missing,Int32}}` input. -/
def SortScratchAccepted : Prop :=
  ∀ scratchType, scratchType = .missingOrInt32 →
    sortMissingWithScratch scratchType = .ok ()

theorem sortScratchAccepted_refuted : ¬ SortScratchAccepted := by
  intro h
  have hne : sortMissingWithScratch .missingOrInt32 ≠ .ok () := by
    simp [sortMissingWithScratch, makeScratch]
  exact hne (h .missingOrInt32 rfl)

end JuliaLean.SortTuplesCov
