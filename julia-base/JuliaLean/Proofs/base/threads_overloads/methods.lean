import JuliaLean.base.threads_overloads
import JuliaLean.Proofs.base.locks_mt.common

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

def ThreadsForeachProp : Prop := ∀ apply ntasks assignments outcomes,
  assignments.length = ntasks →
  threadsForeach apply ntasks assignments = .ok outcomes →
  outcomes = assignments.map (foreachWorker apply)

theorem threadsForeach_proven : ThreadsForeachProp := by
  intro apply ntasks assignments outcomes hlen h
  simp [threadsForeach, hlen] at h
  exact h.symm

def ApplyStaticProp : Prop := ∀ f x, applyStatic f x = (f x, [.called])

theorem applyStatic_proven : ApplyStaticProp := by
  unfold ApplyStaticProp
  intros
  rfl

def ApplyFairProp : Prop := ∀ f x, applyFair f x = (f x, [.spawned, .called, .waited])

theorem applyFair_proven : ApplyFairProp := by
  unfold ApplyFairProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulSmall
