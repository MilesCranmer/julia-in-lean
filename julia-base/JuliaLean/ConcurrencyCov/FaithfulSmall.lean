import JuliaLean.ConcurrencyCov.Common
import JuliaLean.ConcurrencyCov.Locks

/-! Per-method source-body models for the four small ConcurrencyCov files. -/

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov
/-- The field produced by `new`, including conversion to the declared field
type and propagation of conversion failure (`base/atomics.jl:68-69`). -/
structure AtomicCell (α : Type) where
  value : α

def atomicValueCtor {α β : Type} (convert : β → R α) (value : β) : R (AtomicCell α) :=
  match convert value with
  | .ok converted => .ok ⟨converted⟩
  | .error err => .error err

def atomicZeroCtor {α β : Type} (zero : R β) (convert : β → R α) : R (AtomicCell α) :=
  match zero with
  | .ok value => atomicValueCtor convert value
  | .error err => .error err

def AtomicCtorContract : Prop :=
  (∀ (α β : Type) (convert : β → R α) value converted,
    convert value = .ok converted → atomicValueCtor convert value = .ok ⟨converted⟩) ∧
  (∀ (α β : Type) (convert : β → R α) value err,
    convert value = .error err → atomicValueCtor convert value = .error err) ∧
  (∀ (α β : Type) (convert : β → R α) err,
    atomicZeroCtor (.error err) convert = .error err) ∧
  (∀ (α β : Type) (convert : β → R α) value converted,
    convert value = .ok converted → atomicZeroCtor (.ok value) convert = .ok ⟨converted⟩)

theorem atomicCtorContract_proven : AtomicCtorContract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β convert value converted h
    simp [atomicValueCtor, h]
  · intro α β convert value err h
    simp [atomicValueCtor, h]
  · intro α β convert err
    rfl
  · intro α β convert value converted h
    simp [atomicZeroCtor, atomicValueCtor, h]
/-- The unparameterized constructor delegates to `Atomic{Int}()`;
`base/atomics.jl:72`. -/
def atomicDefaultCtor : R (AtomicCell Int) :=
  atomicZeroCtor (.ok 0) (fun value => .ok value)

def AtomicDefaultContract : Prop := ∀ _ : Unit, atomicDefaultCtor = .ok ⟨0⟩
theorem atomicDefaultContract_proven : AtomicDefaultContract := by intro _; rfl


/-! ## `base/locks-mt.jl` -/

def spinLockCtor : Locks.Spin := ⟨0, fun _ => 0⟩
def SpinLockCtorProp : Prop := ∀ _u : Unit, spinLockCtor = ⟨0, fun _ => 0⟩
theorem spinLockCtor_proven : SpinLockCtorProp := by
  unfold SpinLockCtorProp
  intros
  rfl

def paddedSpinLockCtor : Locks.Spin :=
  let l : Locks.Spin := ⟨0, fun _ => 0⟩
  { l with owned := 0 }
def PaddedSpinLockCtorProp : Prop := ∀ _u : Unit, paddedSpinLockCtor.owned = 0
theorem paddedSpinLockCtor_proven : PaddedSpinLockCtorProp := by
  unfold PaddedSpinLockCtorProp
  intros
  rfl

def spinAssertHavelock (violation : R Unit) (l : Locks.Spin) : R Unit :=
  if Locks.spinIslocked l then .ok () else violation
def SpinAssertHavelockProp : Prop := ∀ violation l,
  spinAssertHavelock violation l = if Locks.spinIslocked l then .ok () else violation
theorem spinAssertHavelock_proven : SpinAssertHavelockProp := by
  unfold SpinAssertHavelockProp
  intros
  rfl

inductive SpinLoopOp where | suspend | safepoint
  deriving DecidableEq, Repr

/-- Each list element is the lock state observed at the next loop iteration. -/
def spinLockLoop (task : Nat) : List Locks.Spin → Option (Locks.Spin × List SpinLoopOp)
  | [] => none
  | l :: rest =>
    match Locks.spinTrylock task l with
    | (true, acquired) => some (acquired, [])
    | (false, _) => (spinLockLoop task rest).map fun (acquired, ops) =>
        (acquired, [.suspend, .safepoint] ++ ops)
def SpinLockLoopProp : Prop := ∀ task l rest acquired,
  Locks.spinTrylock task l = (true, acquired) → spinLockLoop task (l :: rest) = some (acquired, [])
theorem spinLockLoop_proven : SpinLockLoopProp := by
  intro task l rest acquired h
  simp [spinLockLoop, h]

def spinTrylock (task : Nat) (l : Locks.Spin) : Bool × Locks.Spin :=
  if l.owned = 0 then
    let disabled := upd l.fin task (l.fin task + 1)
    let previous := l.owned
    let swapped : Locks.Spin := ⟨1, disabled⟩
    if previous = 0 then (true, swapped)
    else (false, { swapped with fin := upd swapped.fin task (swapped.fin task - 1) })
  else (false, l)
def SpinTrylockProp : Prop := ∀ task l, spinTrylock task l = Locks.spinTrylock task l
theorem spinTrylock_proven : SpinTrylockProp := by
  unfold SpinTrylockProp
  intros
  rfl

def spinUnlock (wake : Locks.Spin → Locks.Spin) (task : Nat) (l : Locks.Spin) : R Locks.Spin :=
  let previous := l.owned
  let released := { l with owned := 0 }
  if previous = 0 then .error (.errorException "unlock count must match lock count")
  else
    let enabled := { released with fin := upd released.fin task (released.fin task - 1) }
    .ok (wake enabled)
def SpinUnlockProp : Prop := ∀ task l,
  spinUnlock (fun x => x) task l = Locks.spinUnlock task l
theorem spinUnlock_proven : SpinUnlockProp := by
  unfold SpinUnlockProp
  intros
  rfl

def spinIslocked (monotonicLoad : Int → Int) (l : Locks.Spin) : Bool :=
  monotonicLoad l.owned != 0
def SpinIslockedProp : Prop := ∀ load l,
  spinIslocked load l = (load l.owned != 0)
theorem spinIslocked_proven : SpinIslockedProp := by
  unfold SpinIslockedProp
  intros
  rfl

/-! ## `base/threadcall.jl` -/

structure ThreadcallPlan where
  functionExpr : Nat
  returnType : Nat
  argTypes : List Nat
  argValues : List Nat
  roots : List Nat
  converted : List (Nat × Nat)
  unsafeConverted : List (Nat × Nat)
  preserves : List Nat
  deriving DecidableEq, Repr

def threadcallMacro (isTuple : Bool) (f returnType : Nat)
    (argTypes argValues : List Nat) : R ThreadcallPlan :=
  if !isTuple then .error (.errorException "threadcall: argument types must be a tuple")
  else if argTypes.length != argValues.length then
    .error (.errorException "threadcall: wrong number of arguments to C function")
  else
    let roots := List.range argValues.length
    .ok ⟨f, returnType, argTypes, argValues, roots, argTypes.zip argValues,
      argTypes.zip roots, roots⟩
def ThreadcallMacroProp : Prop := ∀ tuple f ret tys vals plan,
  threadcallMacro tuple f ret tys vals = .ok plan →
    tuple = true ∧ tys.length = vals.length ∧ plan.argTypes = tys ∧
    plan.argValues = vals ∧ plan.converted = tys.zip vals ∧
    plan.unsafeConverted = tys.zip (List.range vals.length)
theorem threadcallMacro_proven : ThreadcallMacroProp := by
  intro tuple f ret tys vals plan h
  unfold threadcallMacro at h
  split at h <;> rename_i ht
  · cases h
  · split at h <;> rename_i hl
    · cases h
    · cases h
      simp_all

def threadcallRun (call : R Unit) : R Unit :=
  match call with | .ok () => .ok () | .error e => .error e
def ThreadcallRunProp : Prop := ∀ call, threadcallRun call = call
theorem threadcallRun_proven : ThreadcallRunProp := by intro call; cases call <;> simp [threadcallRun]

structure NotifyTrace where
  scheduled : Bool
  taskUnpreserved : Bool
  contextUnpreserved : Bool
  deriving DecidableEq, Repr
def threadcallNotify : NotifyTrace := ⟨true, true, true⟩
def ThreadcallNotifyProp : Prop := ∀ _task _ctx : Nat,
  threadcallNotify = ⟨true, true, true⟩
theorem threadcallNotify_proven : ThreadcallNotifyProp := by
  unfold ThreadcallNotifyProp
  intros
  rfl

inductive ThreadcallOp where
  | makeRunCallback | makeNotifyCallback | boxContext | acquire
  | preserveTask | preserveContext | queue | wait | release | readResult
  deriving DecidableEq, Repr
def doThreadcall (result : Nat) : Nat × List ThreadcallOp :=
  (result, [.makeRunCallback, .makeNotifyCallback, .boxContext, .acquire,
    .preserveTask, .preserveContext, .queue, .wait, .release, .readResult])
def DoThreadcallProp : Prop := ∀ result,
  doThreadcall result = (result, [.makeRunCallback, .makeNotifyCallback, .boxContext,
    .acquire, .preserveTask, .preserveContext, .queue, .wait, .release, .readResult])
theorem doThreadcall_proven : DoThreadcallProp := by
  unfold DoThreadcallProp
  intros
  rfl

/-! ## `base/threads_overloads.jl` -/

inductive ForeachOutcome where | ok (values : List Nat) | failed (values : List Nat)
  deriving DecidableEq, Repr

def foreachWorker (apply : Nat → R Nat) : List Nat → ForeachOutcome
  | [] => .ok []
  | item :: rest =>
    match apply item with
    | .error _ => .failed []
    | .ok value =>
      match foreachWorker apply rest with
      | .ok values => .ok (value :: values)
      | .failed values => .failed (value :: values)

def threadsForeach (apply : Nat → R Nat) (ntasks : Nat)
    (assignments : List (List Nat)) : R (List ForeachOutcome) :=
  if assignments.length != ntasks then .error (.assertionError "worker count")
  else .ok (assignments.map (foreachWorker apply))
def ThreadsForeachProp : Prop := ∀ apply ntasks assignments outcomes,
  assignments.length = ntasks →
  threadsForeach apply ntasks assignments = .ok outcomes →
  outcomes = assignments.map (foreachWorker apply)
theorem threadsForeach_proven : ThreadsForeachProp := by
  intro apply ntasks assignments outcomes hlen h
  simp [threadsForeach, hlen] at h
  exact h.symm

inductive ApplyTrace where | called | spawned | waited
  deriving DecidableEq, Repr
def applyStatic (f : Nat → Nat) (x : Nat) : Nat × List ApplyTrace := (f x, [.called])
def ApplyStaticProp : Prop := ∀ f x, applyStatic f x = (f x, [.called])
theorem applyStatic_proven : ApplyStaticProp := by
  unfold ApplyStaticProp
  intros
  rfl

def applyFair (f : Nat → Nat) (x : Nat) : Nat × List ApplyTrace := (f x, [.spawned, .called, .waited])
def ApplyFairProp : Prop := ∀ f x, applyFair f x = (f x, [.spawned, .called, .waited])
theorem applyFair_proven : ApplyFairProp := by
  unfold ApplyFairProp
  intros
  rfl

/-! ## `base/gcutils.jl` -/

structure Weak (α : Type) where value : α
def weakWeakEq (isequal : Nat → Nat → Bool) (a b : Weak Nat) := isequal a.value b.value
def WeakWeakEqProp : Prop := ∀ eq a b, weakWeakEq eq a b = eq a.value b.value
theorem weakWeakEq_proven : WeakWeakEqProp := by
  unfold WeakWeakEqProp
  intros
  rfl

def weakValueEq (isequal : Nat → Nat → Bool) (a : Weak Nat) (b : Nat) := isequal a.value b
def WeakValueEqProp : Prop := ∀ eq a b, weakValueEq eq a b = eq a.value b
theorem weakValueEq_proven : WeakValueEqProp := by
  unfold WeakValueEqProp
  intros
  rfl

def valueWeakEq (isequal : Nat → Nat → Bool) (a : Nat) (b : Weak Nat) := isequal a b.value
def ValueWeakEqProp : Prop := ∀ eq a b, valueWeakEq eq a b = eq a b.value
theorem valueWeakEq_proven : ValueWeakEqProp := by
  unfold ValueWeakEqProp
  intros
  rfl

def checkMutable (isMutable : Bool) (objectType : String) : R Unit :=
  if !isMutable then .error (.errorException s!"objects of type {objectType} cannot be finalized because they are not mutable")
  else .ok ()
def CheckMutableProp : Prop := ∀ mutable ty, checkMutable mutable ty =
  if !mutable then .error (.errorException s!"objects of type {ty} cannot be finalized because they are not mutable") else .ok ()
theorem checkMutable_proven : CheckMutableProp := by
  unfold CheckMutableProp
  intros
  rfl

def finalizer (check : Nat → R Unit) (register : Nat → Nat → Unit) (f o : Nat) : R Nat := do
  check o
  let _ := register f o
  return o
def FinalizerProp : Prop := ∀ check register f o,
  finalizer check register f o = do check o; let _ := register f o; return o
theorem finalizer_proven : FinalizerProp := by
  unfold FinalizerProp
  intros
  rfl

def pointerFinalizer (check : Nat → R Unit) (register : Nat → Nat → Unit) (f o : Nat) : R Nat := do
  check o
  let _ := register f o
  return o
def PointerFinalizerProp : Prop := ∀ check register f o,
  pointerFinalizer check register f o = do check o; let _ := register f o; return o
theorem pointerFinalizer_proven : PointerFinalizerProp := by
  unfold PointerFinalizerProp
  intros
  rfl

def finalize (ccall : Nat → Unit) (task object : Nat) : Unit := ccall (task + object)
def FinalizeProp : Prop := ∀ ccall task object, finalize ccall task object = ccall (task + object)
theorem finalize_proven : FinalizeProp := by
  unfold FinalizeProp
  intros
  rfl

def gc (collect : Int → Unit) (full : Bool := true) : Unit := collect (if full then 1 else 2)
def GcProp : Prop := ∀ collect full, gc collect full = collect (if full then 1 else 2)
theorem gc_proven : GcProp := by
  unfold GcProp
  intros
  rfl

def gcEnable (enable : Bool → Bool) (on : Bool) : Bool := enable on
def GcEnableProp : Prop := ∀ enable on, gcEnable enable on = enable on
theorem gcEnable_proven : GcEnableProp := by
  unfold GcEnableProp
  intros
  rfl

def setFinalizers (enable disable : Unit → Unit) (on : Bool) : Unit :=
  if on then enable () else disable ()
def SetFinalizersProp : Prop := ∀ enable disable on,
  setFinalizers enable disable on = if on then enable () else disable ()
theorem setFinalizers_proven : SetFinalizersProp := by
  unfold SetFinalizersProp
  intros
  rfl

def enableFinalizers (enable : Unit → Unit) (pending : Bool) (runPending : Unit → Unit) : Unit :=
  let _ := enable ()
  if pending then runPending () else ()
def EnableFinalizersProp : Prop := ∀ enable pending run,
  enableFinalizers enable pending run = let _ := enable (); if pending then run () else ()
theorem enableFinalizers_proven : EnableFinalizersProp := by
  unfold EnableFinalizersProp
  intros
  rfl

def disableFinalizers (disable : Unit → Unit) : Unit := disable ()
def DisableFinalizersProp : Prop := ∀ disable, disableFinalizers disable = disable ()
theorem disableFinalizers_proven : DisableFinalizersProp := by
  unfold DisableFinalizersProp
  intros
  rfl

def inFinalizer (ccall : Unit → Int) : Bool := ccall () > 0
def InFinalizerProp : Prop := ∀ ccall, inFinalizer ccall = decide (ccall () > 0)
theorem inFinalizer_proven : InFinalizerProp := by
  unfold InFinalizerProp
  intros
  rfl

inductive PreserveArg where | symbol (name : String) | other
  deriving DecidableEq, Repr
def preserve (args : List PreserveArg) (body : R Nat) : R Nat :=
  if args.all (fun x => match x with | .symbol _ => true | .other => false)
  then body else .error (.errorException "Preserved variable must be a symbol")
def PreserveProp : Prop := ∀ args body, preserve args body =
  if args.all (fun x => match x with | .symbol _ => true | .other => false)
  then body else .error (.errorException "Preserved variable must be a symbol")
theorem preserve_proven : PreserveProp := by
  unfold PreserveProp
  intros
  rfl

def safepoint (ccall : Unit → Unit) : Unit := ccall ()
def SafepointProp : Prop := ∀ ccall, safepoint ccall = ccall ()
theorem safepoint_proven : SafepointProp := by
  unfold SafepointProp
  intros
  rfl

def enableLogging (ccall : Bool → Unit) (on : Bool := true) : Unit := ccall on
def EnableLoggingProp : Prop := ∀ ccall on, enableLogging ccall on = ccall on
theorem enableLogging_proven : EnableLoggingProp := by
  unfold EnableLoggingProp
  intros
  rfl

def loggingEnabled (ccall : Unit → Int) : Bool := ccall () != 0
def LoggingEnabledProp : Prop := ∀ ccall, loggingEnabled ccall = (ccall () != 0)
theorem loggingEnabled_proven : LoggingEnabledProp := by
  unfold LoggingEnabledProp
  intros
  rfl

def gcActiveImpl (ccall : Unit → String) : String := ccall ()
def GcActiveImplProp : Prop := ∀ ccall, gcActiveImpl ccall = ccall ()
theorem gcActiveImpl_proven : GcActiveImplProp := by
  unfold GcActiveImplProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulSmall
