import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.buckets
/-! Public sorting wrappers, tuple merge sort, permutation wrappers, and
multidimensional routing from `base/sort.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

def TopLevelSortCorrect : Prop :=
  (∀ (V : Type) core (v : List V), sortVectorBang core v = core v) ∧
  (∀ (V : Type) core (v : List V), (sortVectorCopy core v).1 = v ∧
    (sortVectorCopy core v).2 = core v) ∧
  (∀ (V : Type) lt (xs : List V), mergeSorted lt xs [] = xs) ∧
  (∀ (V : Type) lt (ys : List V), mergeSorted lt [] ys = ys) ∧
  (∀ (V : Type) core lt (xs : List V), xs.length > 9 →
    sortTupleDefault core lt xs = core xs)

theorem topLevelSortCorrect : TopLevelSortCorrect := by
  refine ⟨by simp [sortVectorBang], by simp [sortVectorCopy], by simp [mergeSorted],
    by intro V lt ys; cases ys <;> simp [mergeSorted], ?_⟩
  intro V core lt xs h
  simp [sortTupleDefault, h]

def SortpermWrappersCorrect : Prop :=
  sortpermOrderingChoice .true_ = true ∧ sortpermOrderingChoice .false_ = false ∧
  (∀ f v i n o r, f && v && i && n && o && r = true →
    sortpermRoute f v i n o r = .integerRangeFastPath) ∧
  (∀ n, sortpermBang true false n = .ok ((List.range n).map (.+1))) ∧
  (∀ n initialized, partialsortpermBang true initialized n =
    .ok ((List.range n).map (.+1)))

theorem sortpermWrappersCorrect : SortpermWrappersCorrect := by
  refine ⟨by decide, by decide, ?_, by simp [sortpermBang], by simp [partialsortpermBang]⟩
  intro f v i n o r h
  cases f <;> cases v <;> cases i <;> cases n <;> cases o <;> cases r <;>
    simp_all [sortpermRoute]

def MultidimensionalSortCorrect : Prop :=
  arraySortRoute 1 = .firstDimension ∧
  (∀ d, d ≠ 1 → arraySortRoute d = .permutedDimension) ∧
  sortChunksRoute true false = .reusedScratch ∧
  sortChunksRoute false true = .acquiredScratch ∧
  sortChunksRoute false false = .noScratch ∧
  (∀ x, getValue x = x) ∧
  (∀ d idx n, (getViewIndices d idx n).length = n)

theorem multidimensionalSortCorrect : MultidimensionalSortCorrect := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, by simp [getValue], ?_⟩
  · intro d h
    simp [arraySortRoute, h]
  · intro d idx n
    simp [getViewIndices]

end JuliaLean.SortTuplesCov
