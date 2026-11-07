import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.compatibility_kernels
/-! Remaining behavioral methods in `base/sort.jl` (master `bbfa0ce4150`):
BracketedSort helpers, the RadixSort wrapper, the integer-range permutation
fast path, and the legacy entry-point wrappers. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

def BracketedSortCorrect : Prop :=
  (∀ (V : Type) lt (xs : List V) lo hi,
    (bracketKernel lt xs lo hi).selected = xs.map fun x =>
      (lo.any fun s => lt x s) != (hi.elim true fun s => !lt s x)) ∧
  (∀ n single disjoint ordered, moveRoute n n single disjoint ordered =
    if single || disjoint then .pairSwaps
    else if ordered then .overlappingReversals else .rangeError) ∧
  (∀ lo hi len h t, ¬ lo < hi →
    bracketedSortRoute lo hi len h t = .emptyWindow) ∧
  (∀ lo hi len h t, lo < hi → len < 260 →
    bracketedSortRoute lo hi len h t = .smallFallback)

theorem bracketedSortCorrect : BracketedSortCorrect := by
  refine ⟨by intros; rfl, ?_, ?_, ?_⟩
  · intro n single disjoint ordered
    simp [moveRoute]
  · intro lo hi len h t hn
    simp [bracketedSortRoute, hn]
  · intro lo hi len h t hlt hlen
    simp [bracketedSortRoute, hlt, hlen]

def RadixSortWrapperCorrect : Prop :=
  ∀ bits, radixSortWrapper bits = ⟨true, true, true, true, true⟩

theorem radixSortWrapperCorrect : RadixSortWrapperCorrect := by
  intro bits
  rfl

def SortpermIntRangeCorrect : Prop :=
  ∀ x rangeLength minValue, sortpermIntRange x rangeLength minValue =
    (List.range rangeLength).flatMap fun label =>
      ((List.range x.length).zip x).filterMap fun (i, value) =>
        if value - minValue = (label : Int) then some (i + 1) else none

theorem sortpermIntRangeCorrect : SortpermIntRangeCorrect := by
  unfold SortpermIntRangeCorrect
  intros
  rfl

def LegacyEntriesCorrect : Prop :=
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    quickSortEntry true lt v lo hi = .ok (quickSort lt v lo hi)) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    mergeSortVectorEntry true lt v lo hi = mergeSortEntry true lt v lo hi) ∧
  (∀ (V : Type) [Inhabited V] lt f l (v : Array V) lo hi,
    partialQuickSortEntry true lt f l v lo hi = .ok (partialQuickSort lt f l v lo hi)) ∧
  (∀ (V A O S : Type) five (v : Array V) lo hi (a : A) (o : O) (s : S),
    legacyIgnoredScratch five v lo hi a o s = five v lo hi a o)

theorem legacyEntriesCorrect : LegacyEntriesCorrect := by
  exact ⟨by simp [quickSortEntry, checkedLegacyEntry],
    by simp [mergeSortVectorEntry],
    by simp [partialQuickSortEntry, checkedLegacyEntry],
    by intros; rfl⟩

end JuliaLean.SortTuplesCov
