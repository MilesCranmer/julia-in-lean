import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.pipeline
/-! Algorithm-selection methods from `base/sort.jl` (master
`bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

def SortDispatchCorrect : Prop :=
  (∀ (R : Type) (yes no : R),
    isUIntMappableDispatch true yes no = yes ∧ isUIntMappableDispatch false yes no = no) ∧
  (∀ (R : Type) n (s b : R), smallExplicit n s b = ⟨n, s, b⟩ ∧
    smallDefault n s b = ⟨n, s, b⟩) ∧
  (∀ (R : Type) (a : SmallAlgorithm R) lo hi,
    smallDispatch a lo hi = if hi - lo < a.threshold then a.small else a.big) ∧
  (∀ rs lo hi, checkSortedDispatch true rs lo hi = .alreadySorted) ∧
  (∀ rs, stableCheckDispatch true rs = .alreadySorted) ∧
  (∀ (V : Type) lt (v : Array V), v.size = 0 → computeExtrema lt v = none) ∧
  (∀ bytes range span, (considerCounting bytes range span).useCounting =
    decide (range < if bytes > 8 then 5 * span - 100 else span / 2)) ∧
  (∀ (V : Type) (xs : List V), maybeReverse false xs = xs ∧
    maybeReverse true xs = xs.reverse) ∧
  (∀ bytes bits log, (considerRadix bytes bits log).useRadix =
    (bytes ≤ 8 && bits + 70 < log))

theorem sortDispatchCorrect : SortDispatchCorrect := by
  refine ⟨by simp [isUIntMappableDispatch], by simp [smallExplicit, smallDefault],
    by simp [smallDispatch], by simp [checkSortedDispatch], by simp [stableCheckDispatch],
    ?_, by simp [considerCounting], by simp [maybeReverse], by simp [considerRadix]⟩
  intro V lt v h
  simp [computeExtrema, Array.size_eq_zero_iff.mp h]

def InitialPipelineCorrect : Prop :=
  (∀ next, initialOptimizationStages next =
    [.subarray, .missing, .bool_, .small 10, .ieee] ++ next) ∧
  defaultSortDispatch true = defaultVectorStages ∧
  defaultSortDispatch false = defaultVectorStages ∧
  defalg .numericArray = .unstable ∧ defalg .missingArray = .unstable ∧
  defalg .bottomArray = .unstable ∧ defalg .otherArray = .stable ∧ defalg .other = .stable

theorem initialPipelineCorrect : InitialPipelineCorrect := by
  exact ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def AlgorithmShowCorrect : Prop :=
  (∀ alg, showAlgorithm alg = printAlgorithmTree (alg.depth + 1) alg 0) ∧
  (∀ name, showAlgorithmType none name = name) ∧
  (∀ n name, showAlgorithmType (some n) name = "Base.Sort.Small{" ++ toString n ++ "}")

theorem algorithmShowCorrect : AlgorithmShowCorrect := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end JuliaLean.SortTuplesCov
