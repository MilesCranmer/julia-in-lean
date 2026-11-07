import JuliaLean.base.set

namespace JuliaLean.Proofs.base.set.ReplacementKeySwap

open JuliaLean.base.set

/-- The replacement swaps two different keys without changing either value. -/
def swapPair (a b : Nat) (pair : Nat × Nat) : Result (Nat × Nat) :=
  .ok (if pair.1 = a then b else a, pair.2)

/-- The generic nonmutating dictionary branch necessarily deletes the first
replacement when the second original key is replaced. The hypotheses are the
ordinary public contracts of successful dictionary pop! and push!: pop! removes
only the queried key, and push! changes only the supplied key's value.

No dictionary implementation is selected or assumed to have the bad result.
The theorem holds for every implementation satisfying those operation laws.
The concrete IdDict manifestation is checked by
repro/set-replace-iddict-key-swap.jl.

Source: base/set.jl:909-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Promise: base/set.jl:869-873 replaces each original pair with its mapped pair. -/
theorem nonmutating_key_swap_loses_first
    {C : Type}
    (isDict isSet : C → Bool) (same : C → C → Bool)
    (elements : C → Result (List (Nat × Nat)))
    (lookup : C → Nat → Option Nat)
    (pop : Nat → C → Result (Nat × C))
    (push : (Nat × Nat) → C → Result C)
    (popLaw : ∀ c key value, lookup c key = some value →
      ∃ next, pop key c = .ok (value, next) ∧
        ∀ query, lookup next query = if query = key then none else lookup c query)
    (pushLaw : ∀ c pair, ∃ next, push pair c = .ok next ∧
      ∀ query, lookup next query =
        if query = pair.1 then some pair.2 else lookup c query)
    (source result : C) (a b va vb count : Nat)
    (budget : 2 ≤ count)
    (different : a ≠ b)
    (sourceIsDict : isDict source = true)
    (resultIsDict : isDict result = true)
    (distinctCopy : same result source = false)
    (originalPairs : elements source = .ok [(a, va), (b, vb)])
    (copiedFirst : lookup result a = some va) :
    ∃ out,
      replaceAbstractCollectionsMethod isDict isSet same elements (swapPair a b)
        (fun left right => decide (left = right)) asKeyDict pop push result source count = .ok out ∧
      lookup out b = none ∧
      ¬ (lookup out b = some va ∧ lookup out a = some vb) := by
  have zeroBudget : count ≠ 0 := by omega
  have oneBudget : count ≠ 1 := by omega
  obtain ⟨afterPopA, popA, lookupPopA⟩ := popLaw result a va copiedFirst
  obtain ⟨afterPushB, pushB, lookupPushB⟩ := pushLaw afterPopA (b, va)
  have presentB : lookup afterPushB b = some va := by
    rw [lookupPushB]
    simp
  obtain ⟨afterPopB, popB, lookupPopB⟩ := popLaw afterPushB b va presentB
  obtain ⟨out, pushA, lookupPushA⟩ := pushLaw afterPopB (a, vb)
  have missingB : lookup out b = none := by
    rw [lookupPushA]
    simp [Ne.symm different, lookupPopB]
  refine ⟨out, ?_, missingB, ?_⟩
  · simp [replaceAbstractCollectionsMethod,
      replaceAbstractCollectionsMethod.replaceLoop, sourceIsDict, resultIsDict,
      distinctCopy, originalPairs, swapPair, asKeyDict, popA, pushB, popB, pushA,
      different, Ne.symm different, zeroBudget, oneBudget,
      Ne.symm zeroBudget, Ne.symm oneBudget, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro expected
    rw [missingB] at expected
    cases expected.1

end JuliaLean.Proofs.base.set.ReplacementKeySwap
