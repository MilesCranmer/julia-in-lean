import JuliaLean.base.sort
import JuliaLean.Proofs.base.sort.keyword_wrappers
/-! Executable branch and mutation models for the optimization pipeline in
`base/sort.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

def SubarrayOptimizationCorrect : Prop :=
  (∀ (R : Type) (next : R), subarrayOptimization next = next) ∧
  (∀ pa pv hi lo off, ((pa && !pv && decide (hi - lo < 100)) || decide (off ≠ 0)) = true →
    unwrappableSubarrayOptimization pa pv hi lo off = .view) ∧
  (∀ pa pv hi lo off, ((pa && !pv && decide (hi - lo < 100)) || decide (off ≠ 0)) = false →
    unwrappableSubarrayOptimization pa pv hi lo off = .parentVector)

theorem subarrayOptimizationCorrect : SubarrayOptimizationCorrect := by
  refine ⟨by simp [subarrayOptimization], ?_, ?_⟩ <;>
    intro pa pv hi lo off h <;>
    cases pa <;> cases pv <;> simp_all [unwrappableSubarrayOptimization]

def WithoutMissingVectorCorrect : Prop :=
  (∀ (V : Type) (data : Array (Option V)), data.any (fun x => x.isNone) = true →
    withoutMissingVector data false =
      .error (.argumentError "data must not contain missing values")) ∧
  (∀ (V : Type) (data : Array (Option V)), withoutMissingVector data true = .ok data) ∧
  (∀ (V : Type) (data : Array (Option V)) x i,
    withoutMissingSet data x i = JuliaLean.Sort.wr data i (some x)) ∧
  (∀ (V : Type) (data : Array (Option V)),
    withoutMissingSize data = data.size ∧ withoutMissingAxes data = (1, data.size))

theorem withoutMissingVectorCorrect : WithoutMissingVectorCorrect := by
  refine ⟨?_, by simp [withoutMissingVector], ?_, by simp [withoutMissingSize, withoutMissingAxes]⟩
  · intro V data h
    simp [withoutMissingVector, h]
  · intro V data x i
    rfl

/-! ### send_to_end! -/

section SendToEnd

variable {V : Type} [Inhabited V]

def SendToEndCorrect : Prop :=
  (∀ (V : Type) [Inhabited V] f (v : Array V) lo hi,
    sendToEnd f v lo hi =
      let first := sendScan f hi (hi - lo + 2).toNat v lo
      let out := sendLoop f hi (hi - first.2 + 1).toNat first.1 first.2 (first.2 + 1)
      (out.1, out.2 - 1)) ∧
  sendToEndRoute false false = .forward false false ∧
  sendToEndRoute false true = .forward true true ∧
  sendToEndRoute true false = .reverse false true ∧
  sendToEndRoute true true = .reverse true false

theorem sendToEndCorrect : SendToEndCorrect := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  intro V inst f v lo hi
  rfl

end SendToEnd

def MissingOptimizationCorrect : Prop :=
  (∀ d hm p pd ii dh id,
    d && hm = true → missingOptimizationRoute d hm p pd ii dh id = .direct) ∧
  (∀ p pd ii dh id,
    p && pd && ii && dh && id = true →
      missingOptimizationRoute false false p pd ii dh id = .permutation) ∧
  missingOptimizationRoute false false false false false false false = .pass

theorem missingOptimizationCorrect : MissingOptimizationCorrect := by
  refine ⟨?_, ?_, by decide⟩
  · intro d hm p pd ii dh id h
    cases d <;> cases hm <;> simp_all [missingOptimizationRoute]
  · intro p pd ii dh id h
    cases p <;> cases pd <;> cases ii <;> cases dh <;> cases id <;>
      simp_all [missingOptimizationRoute]

def IEEEOptimizationCorrect : Prop :=
  (∀ s, afterZero false s = !s ∧ afterZero true s = s) ∧
  (∀ i c, isConcreteIEEEFloat i c = (i && c)) ∧
  (∀ vi d ii p pd di, vi && d = true →
    ieeeOptimizationRoute vi d ii p pd di = .values) ∧
  (∀ ii p pd di, ii && p && pd && di = true →
    ieeeOptimizationRoute false false ii p pd di = .permutation) ∧
  ieeeOptimizationRoute false false false false false false = .pass

theorem ieeeOptimizationCorrect : IEEEOptimizationCorrect := by
  refine ⟨by intro s; cases s <;> decide, by simp [isConcreteIEEEFloat], ?_, ?_, by decide⟩
  · intro vi d ii p pd di h
    cases vi <;> cases d <;> simp_all [ieeeOptimizationRoute]
  · intro ii p pd di h
    cases ii <;> cases p <;> cases pd <;> cases di <;> simp_all [ieeeOptimizationRoute]

def BoolOptimizationCorrect : Prop :=
  (∀ (R : Type) (next : R), boolOptimizationGeneric next = next) ∧
  (∀ lt v lo hi, boolOptimization lt v lo hi =
    let first := if lt false true then some false else if lt true false then some true else none
    match first with
    | none => v
    | some x =>
      let count := (List.range (hi - lo + 1).toNat).foldl
        (fun n (k : Nat) => if JuliaLean.Sort.rd v (lo + (k : Int)) = x then n + 1 else n) 0
      fillBoolRange (fillBoolRange v lo (lo + count - 1) x) (lo + count) hi (!x)) ∧
  (∀ v lo hi, boolOptimization (fun _ _ => false) v lo hi = v)

theorem boolOptimizationCorrect : BoolOptimizationCorrect := by
  exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, by simp [boolOptimization]⟩

end JuliaLean.SortTuplesCov
