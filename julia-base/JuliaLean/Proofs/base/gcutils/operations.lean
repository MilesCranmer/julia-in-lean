import JuliaLean.base.gcutils

namespace JuliaLean.ConcurrencyCov.GcUtils

open JuliaLean.ConcurrencyCov

/-- Weak-reference comparison delegates to `isequal`; finalizer registration
checks mutability before registering and returns its object
(`base/gcutils.jl:37-106`). -/
def FinalizerSpec : Prop :=
  (∀ a b, weakEq a b = (a.value == b.value)) ∧
  (∀ a b, weakEqValue a b = (a.value == b)) ∧
  (∀ a b, valueEqWeak a b = (a == b.value)) ∧
  (∀ o s out, addFinalizer true o s = .ok out → out.1 = o ∧ out.2.registered = s.registered + 1) ∧
  (∀ o s, addFinalizer false o s =
    .error (.errorException "object cannot be finalized because it is not mutable")) ∧
  (∀ mutable o s, addPointerFinalizer mutable o s = addFinalizer mutable o s) ∧
  (∀ o, finalize o = o)

theorem finalizerSpec_proven : FinalizerSpec := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl⟩
  intro o s out h
  cases h
  exact ⟨rfl, rfl⟩

/-- GC wrappers select full versus incremental collection, return the previous
enable state, balance the task-local finalizer counter, preserve expression
results, and expose the runtime logging and implementation values
(`base/gcutils.jl:136-295`). -/
def GcWrapperSpec : Prop :=
  gc true = .full ∧ gc false = .incremental ∧
  (∀ on rt, (enable on rt).1 = rt.gcEnabled ∧ (enable on rt).2.gcEnabled = on) ∧
  (∀ rt, (disableFinalizers rt).finalizerDepth = rt.finalizerDepth + 1) ∧
  (∀ rt, 0 < rt.finalizerDepth →
    (enableFinalizers rt).finalizerDepth = rt.finalizerDepth - 1 ∧
    (enableFinalizers rt).pendingFinalizers = false) ∧
  (∀ on rt, setFinalizers on rt = if on then enableFinalizers rt else disableFinalizers rt) ∧
  (∀ rt, inFinalizer rt = rt.inFinalizer) ∧
  (∀ syms out, syms.all (· != "") = true → preserve syms out = out) ∧
  (∀ rt, (safepoint rt).safepoints = rt.safepoints + 1) ∧
  (∀ on rt, (enableLogging on rt).logging = on) ∧
  (∀ rt, loggingEnabled rt = rt.logging ∧ gcActiveImpl rt = rt.activeImpl)

theorem gcWrapperSpec_proven : GcWrapperSpec := by
  refine ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_, fun _ _ => rfl,
    fun _ => rfl, ?_, fun _ => rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  · intro rt h
    exact ⟨rfl, rfl⟩
  · intro syms out h
    simp [preserve, h]
end JuliaLean.ConcurrencyCov.GcUtils
