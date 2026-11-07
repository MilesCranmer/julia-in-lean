import JuliaLean.base.threadcall
import JuliaLean.Proofs.base.locks_mt.common

/-! Source-body models and properties for `base/threadcall.jl`. -/

namespace JuliaLean.ConcurrencyCov.Threadcall

open JuliaLean.ConcurrencyCov








/-- The four method bodies preserve validation order, callback effects, and
semaphore accounting (`base/threadcall.jl:18-109`). -/
def ThreadcallBodies : Prop :=
  (∀ n, threadcallMacro false n n =
    .error (.errorException "threadcall: argument types must be a tuple")) ∧
  (∀ nt nv, nt != nv → threadcallMacro true nt nv =
    .error (.errorException "threadcall: wrong number of arguments to C function")) ∧
  (∀ n, threadcallMacro true n n = .ok ⟨n, n, n, n != 0⟩) ∧
  (∀ f, threadcallRun f = f) ∧
  (∀ s, (threadcallNotify s).scheduled = true ∧
    (threadcallNotify s).taskPreserved = false ∧
    (threadcallNotify s).contextPreserved = false) ∧
  (∀ result s out, doThreadcall result s = some out →
    0 < s.permits ∧ out.1 = result ∧ out.2.permits = s.permits ∧
    out.2.queued = s.queued + 1 ∧ out.2.waited = true)

theorem threadcallBodies_proven : ThreadcallBodies := by
  refine ⟨fun _ => rfl, ?_, fun _ => by simp [threadcallMacro], fun _ => rfl,
    fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
  · intro nt nv h
    simp [threadcallMacro, h]
  · intro result s out h
    by_cases hz : s.permits = 0
    · simp [doThreadcall, hz] at h
    · simp [doThreadcall, hz] at h
      cases h
      exact ⟨Nat.pos_of_ne_zero hz, rfl, rfl, rfl, rfl⟩


def ThreadcallPoolFollowsEnvironment : Prop :=
  ∀ sysimageValue processEnvironment, 1 ≤ processEnvironment →
    limiterSize sysimageValue processEnvironment = processEnvironment

theorem threadcallPoolFollowsEnvironment_refuted : ¬ ThreadcallPoolFollowsEnvironment := by
  intro h
  have bad := h 4 8 (by omega)
  contradiction

end JuliaLean.ConcurrencyCov.Threadcall
