import JuliaLean.ConcurrencyCov.Common

/-! Source-body models and properties for `base/gcutils.jl`. -/

namespace JuliaLean.ConcurrencyCov.GcUtils

open JuliaLean.ConcurrencyCov

structure Weak where value : Option Nat
  deriving DecidableEq, Repr

def weakEq (a b : Weak) : Bool := a.value == b.value
def weakEqValue (a : Weak) (b : Option Nat) : Bool := a.value == b
def valueEqWeak (a : Option Nat) (b : Weak) : Bool := a == b.value

def checkMutable (mutable : Bool) : R Unit :=
  if mutable then .ok () else .error (.errorException "object cannot be finalized because it is not mutable")

structure FinalizerState where registered : Nat := 0
  deriving DecidableEq, Repr

def addFinalizer (mutable : Bool) (object : Nat) (s : FinalizerState) : R (Nat × FinalizerState) := do
  checkMutable mutable
  return (object, { registered := s.registered + 1 })

def addPointerFinalizer := addFinalizer
def finalize (object : Nat) : Nat := object

inductive CollectionKind where | full | incremental
  deriving DecidableEq, Repr
def gc (full : Bool := true) : CollectionKind := if full then .full else .incremental

structure Runtime where
  gcEnabled : Bool
  finalizerDepth : Nat
  pendingFinalizers : Bool
  inFinalizer : Bool
  logging : Bool
  activeImpl : String
  safepoints : Nat := 0
  deriving DecidableEq, Repr

def enable (on : Bool) (rt : Runtime) : Bool × Runtime :=
  (rt.gcEnabled, { rt with gcEnabled := on })

def enableFinalizers (rt : Runtime) : Runtime :=
  { rt with finalizerDepth := rt.finalizerDepth - 1, pendingFinalizers := false }
def disableFinalizers (rt : Runtime) : Runtime :=
  { rt with finalizerDepth := rt.finalizerDepth + 1 }
def setFinalizers (on : Bool) (rt : Runtime) : Runtime :=
  if on then enableFinalizers rt else disableFinalizers rt

def inFinalizer (rt : Runtime) : Bool := rt.inFinalizer
def preserve (symbols : List String) (outcome : Outcome) : R Nat :=
  if symbols.all (· != "") then outcome else .error (.errorException "Preserved variable must be a symbol")
def safepoint (rt : Runtime) : Runtime := { rt with safepoints := rt.safepoints + 1 }
def enableLogging (on : Bool) (rt : Runtime) : Runtime := { rt with logging := on }
def loggingEnabled (rt : Runtime) : Bool := rt.logging
def gcActiveImpl (rt : Runtime) : String := rt.activeImpl

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
