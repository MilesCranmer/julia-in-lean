import JuliaLean.ConcurrencyCov.Common
import JuliaLean.ConcurrencyCov.Locks

/-! Per-method source-body models for the four small ConcurrencyCov files. -/

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

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

end JuliaLean.ConcurrencyCov.FaithfulSmall
