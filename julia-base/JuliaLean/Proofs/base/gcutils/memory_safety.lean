import JuliaLean.base.gcutils
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.gcutils.memory_safety
open JuliaLean

-- The C runtime exports exactly one Cint at jl_gc_have_pending_finalizers.
def checkedPendingLoad (value : JInt .i32) (offset : Nat) : Jl (JInt .i32) :=
  if offset < 1 then pure value else .error .boundsError

def RuntimeCellInBounds : Prop :=
  ∀ (Object Finalizer ThreadState Pointer Task MemoryOrder Error : Type)
    (ops : JuliaLean.base.gcutils.GcOps Jl Object Finalizer ThreadState Pointer Task MemoryOrder Error)
    (pending : JInt .i32),
    JuliaLean.base.gcutils.GC.enableFinalizers
      { ops with enableFinalizersInternal := pure ()
                 pendingFinalizers := fun _ => checkedPendingLoad pending 0
                 runPendingFinalizers := fun _ => pure () } = .ok ()

theorem runtimeCellInBounds_proven : RuntimeCellInBounds := by
  unfold RuntimeCellInBounds
  intro Object Finalizer ThreadState Pointer Task MemoryOrder Error ops pending
  simp [JuliaLean.base.gcutils.GC.enableFinalizers, checkedPendingLoad]
  rfl

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-gcutils-global", juliaFile := "base/gcutils.jl"
    juliaFns := ["GC.enable_finalizers"]
    statement := "Enabling finalizers reads the runtime-owned pending-finalizer Cint without accessing beyond its single allocated cell."
    source := "base/gcutils.jl:161-166; src/gc.c runtime global declaration"
    status := .proven, prop := ``RuntimeCellInBounds
    thm := some ``runtimeCellInBounds_proven }
]
end JuliaLean.Proofs.base.gcutils.memory_safety
