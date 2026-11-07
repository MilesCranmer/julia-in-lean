import JuliaLean.base.gcutils
import JuliaLean.Proofs.base.locks_mt.common

namespace JuliaLean.ConcurrencyCov.FaithfulSmall

open JuliaLean.ConcurrencyCov

def WeakWeakEqProp : Prop := ∀ eq a b, weakWeakEq eq a b = eq a.value b.value

theorem weakWeakEq_proven : WeakWeakEqProp := by
  unfold WeakWeakEqProp
  intros
  rfl

def WeakValueEqProp : Prop := ∀ eq a b, weakValueEq eq a b = eq a.value b

theorem weakValueEq_proven : WeakValueEqProp := by
  unfold WeakValueEqProp
  intros
  rfl

def ValueWeakEqProp : Prop := ∀ eq a b, valueWeakEq eq a b = eq a b.value

theorem valueWeakEq_proven : ValueWeakEqProp := by
  unfold ValueWeakEqProp
  intros
  rfl

def CheckMutableProp : Prop := ∀ mutable ty, checkMutable mutable ty =
  if !mutable then .error (.errorException s!"objects of type {ty} cannot be finalized because they are not mutable") else .ok ()

theorem checkMutable_proven : CheckMutableProp := by
  unfold CheckMutableProp
  intros
  rfl

def FinalizerProp : Prop := ∀ check register f o,
  finalizer check register f o = do check o; let _ := register f o; return o

theorem finalizer_proven : FinalizerProp := by
  unfold FinalizerProp
  intros
  rfl

def PointerFinalizerProp : Prop := ∀ check register f o,
  pointerFinalizer check register f o = do check o; let _ := register f o; return o

theorem pointerFinalizer_proven : PointerFinalizerProp := by
  unfold PointerFinalizerProp
  intros
  rfl

def FinalizeProp : Prop := ∀ ccall task object, finalize ccall task object = ccall (task + object)

theorem finalize_proven : FinalizeProp := by
  unfold FinalizeProp
  intros
  rfl

def GcProp : Prop := ∀ collect full, gc collect full = collect (if full then 1 else 2)

theorem gc_proven : GcProp := by
  unfold GcProp
  intros
  rfl

def GcEnableProp : Prop := ∀ enable on, gcEnable enable on = enable on

theorem gcEnable_proven : GcEnableProp := by
  unfold GcEnableProp
  intros
  rfl

def SetFinalizersProp : Prop := ∀ enable disable on,
  setFinalizers enable disable on = if on then enable () else disable ()

theorem setFinalizers_proven : SetFinalizersProp := by
  unfold SetFinalizersProp
  intros
  rfl

def EnableFinalizersProp : Prop := ∀ enable pending run,
  enableFinalizers enable pending run = let _ := enable (); if pending then run () else ()

theorem enableFinalizers_proven : EnableFinalizersProp := by
  unfold EnableFinalizersProp
  intros
  rfl

def DisableFinalizersProp : Prop := ∀ disable, disableFinalizers disable = disable ()

theorem disableFinalizers_proven : DisableFinalizersProp := by
  unfold DisableFinalizersProp
  intros
  rfl

def InFinalizerProp : Prop := ∀ ccall, inFinalizer ccall = decide (ccall () > 0)

theorem inFinalizer_proven : InFinalizerProp := by
  unfold InFinalizerProp
  intros
  rfl

def PreserveProp : Prop := ∀ args body, preserve args body =
  if args.all (fun x => match x with | .symbol _ => true | .other => false)
  then body else .error (.errorException "Preserved variable must be a symbol")

theorem preserve_proven : PreserveProp := by
  unfold PreserveProp
  intros
  rfl

def SafepointProp : Prop := ∀ ccall, safepoint ccall = ccall ()

theorem safepoint_proven : SafepointProp := by
  unfold SafepointProp
  intros
  rfl

def EnableLoggingProp : Prop := ∀ ccall on, enableLogging ccall on = ccall on

theorem enableLogging_proven : EnableLoggingProp := by
  unfold EnableLoggingProp
  intros
  rfl

def LoggingEnabledProp : Prop := ∀ ccall, loggingEnabled ccall = (ccall () != 0)

theorem loggingEnabled_proven : LoggingEnabledProp := by
  unfold LoggingEnabledProp
  intros
  rfl

def GcActiveImplProp : Prop := ∀ ccall, gcActiveImpl ccall = ccall ()

theorem gcActiveImpl_proven : GcActiveImplProp := by
  unfold GcActiveImplProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulSmall
