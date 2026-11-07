import JuliaLean.base.cancellation
import JuliaLean.Proofs.base.task.interleavings

namespace JuliaLean.Tasks



private theorem raiseCancellation_mono (old requested : Nat) :
    old ≤ (raiseCancellation old requested).2 := by
  unfold raiseCancellation
  split <;> omega

/-- Cancellation is level-triggered and severities only escalate, under every
interleaving of requests (`base/cancellation.jl:3-12,662-700`). -/
def CancellationSeverityMonotone : Prop :=
  ∀ (initial : Nat) (requests : List Nat), initial ≤ cancellationRun requests initial

theorem cancellationSeverityMonotone_proven : CancellationSeverityMonotone := by
  intro initial requests
  induction requests generalizing initial with
  | nil => simp [cancellationRun]
  | cons requested requests ih =>
      rw [cancellationRun]
      exact Nat.le_trans (raiseCancellation_mono initial requested)
        (ih (raiseCancellation initial requested).2)

end JuliaLean.Tasks
