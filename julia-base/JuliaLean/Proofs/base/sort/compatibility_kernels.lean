import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.unsigned_mapping
/-! Legacy QuickSort, MergeSort, and PartialQuickSort kernels from
`base/sort.jl:2401-2595` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

section

variable {V : Type} [Inhabited V]

def LegacySortKernelsCorrect : Prop :=
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    (selectPivot lt v lo hi).2 = JuliaLean.Sort.rd (selectPivot lt v lo hi).1 lo) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi, hi ≤ lo →
    quickSort lt v lo hi = v) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    lo < hi → hi - lo ≤ 20 → quickSort lt v lo hi =
      JuliaLean.Sort.insertionSort lt v lo hi) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    lo < hi → hi - lo ≤ 20 → mergeSort lt v lo hi =
      JuliaLean.Sort.insertionSort lt v lo hi) ∧
  (∀ (V : Type) [Inhabited V] lt f l (v : Array V) lo hi,
    lo < hi → hi - lo ≤ 20 → partialQuickSort lt f l v lo hi =
      JuliaLean.Sort.insertionSort lt v lo hi)

/- The size proofs for the recursive kernels follow because every mutation is
an Array modification.  They are kept together so the registry property uses
all three method bodies. -/
theorem legacySortKernelsCorrect : LegacySortKernelsCorrect := by
  refine ⟨by intros; simp [selectPivot], ?_, ?_, ?_, ?_⟩
  · intro V inst lt v lo hi
    intro h
    unfold quickSort
    generalize (hi - lo + 2).toNat = fuel
    cases fuel <;> simp [quickSortLoop, show ¬ lo < hi by omega]
  · intro V inst lt v lo hi hlo hsmall
    have hfuel : 0 < (hi - lo + 2).toNat := by omega
    cases hfuelEq : (hi - lo + 2).toNat with
    | zero => simp_all
    | succ fuel => simp [quickSort, hfuelEq, quickSortLoop, hlo, hsmall]
  · intro V inst lt v lo hi hlo hsmall
    have hfuel : 0 < (hi - lo + 2).toNat := by omega
    cases hfuelEq : (hi - lo + 2).toNat with
    | zero => simp_all
    | succ fuel => simp [mergeSort, hfuelEq, mergeSortLoop, hlo, hsmall]
  · intro V inst lt f l v lo hi hlo hsmall
    have hfuel : 0 < (hi - lo + 2).toNat := by omega
    cases hfuelEq : (hi - lo + 2).toNat with
    | zero => simp_all
    | succ fuel => simp [partialQuickSort, hfuelEq, partialQuickSortLoop, hlo, hsmall]

end

end JuliaLean.SortTuplesCov
