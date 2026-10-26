import JuliaLean.ConcurrencyCov.Common

/-! Source-body models and properties for `base/threadcall.jl`. -/

namespace JuliaLean.ConcurrencyCov.Threadcall

open JuliaLean.ConcurrencyCov

structure MacroPlan where
  roots : Nat
  converted : Nat
  unsafeConverted : Nat
  preservesRoots : Bool
  deriving DecidableEq, Repr

/-- `@threadcall` validates tuple syntax and arity before building one conversion
and one root per argument (`base/threadcall.jl:18-59`). -/
def threadcallMacro (tupleSyntax : Bool) (argTypes argValues : Nat) : R MacroPlan :=
  if !tupleSyntax then .error (.errorException "threadcall: argument types must be a tuple")
  else if argTypes != argValues then
    .error (.errorException "threadcall: wrong number of arguments to C function")
  else .ok ⟨argValues, argValues, argValues, argValues != 0⟩

def threadcallRun (f : Outcome) : Outcome := f

structure NotifyState where
  scheduled : Bool := false
  taskPreserved : Bool := true
  contextPreserved : Bool := true
  deriving DecidableEq, Repr

def threadcallNotify (s : NotifyState) : NotifyState :=
  { s with scheduled := true, taskPreserved := false, contextPreserved := false }

structure CallState where
  permits : Nat
  queued : Nat := 0
  taskPreserved : Bool := false
  contextPreserved : Bool := false
  waited : Bool := false
  deriving DecidableEq, Repr

/-- `do_threadcall` acquires one semaphore permit, preserves the task and closure,
queues and waits, then releases the permit in `finally` and returns `result[]`
(`base/threadcall.jl:78-109`). -/
def doThreadcall (result : Nat) (s : CallState) : Option (Nat × CallState) :=
  if s.permits = 0 then none
  else some (result, ⟨s.permits, s.queued + 1, true, true, true⟩)

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

/-- The limiter is serialized in the system image, so a restarted process should
honor its current `UV_THREADPOOL_SIZE` value as the docstring promises. -/
def limiterSize (sysimageValue processEnvironment : Nat) : Nat := sysimageValue

def ThreadcallPoolFollowsEnvironment : Prop :=
  ∀ sysimageValue processEnvironment, 1 ≤ processEnvironment →
    limiterSize sysimageValue processEnvironment = processEnvironment

theorem threadcallPoolFollowsEnvironment_refuted : ¬ ThreadcallPoolFollowsEnvironment := by
  intro h
  have bad := h 4 8 (by omega)
  contradiction

end JuliaLean.ConcurrencyCov.Threadcall
