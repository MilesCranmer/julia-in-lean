import JuliaLean.base.precompilation
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.precompilation.LegacyRuntime
open JuliaLean JuliaLean.base.precompilation JuliaLean.Registry

/-- Background-state locking uses the state's lock and keeps the callback's result. -/
def LockDelegateBodies : Prop :=
  (∀ (T : Rt) (o : Ops (Except PError) T) (bg : BackgroundPrecompileState T)
      (A : Type) (f : Except PError A), o.bgget = .ok bg →
      lock_BG o f = o.withLock bg.lock f) ∧
  (∀ (T : Rt) (o : Ops (Except PError) T) (bg : BackgroundPrecompileState T),
      o.bgget = .ok bg → lock_BG_ o = o.lock bg.lock) ∧
  (∀ (T : Rt) (o : Ops (Except PError) T) (bg : BackgroundPrecompileState T),
      o.bgget = .ok bg → unlock_BG o = o.unlock bg.lock)

theorem lockDelegateBodies_proven : LockDelegateBodies := by
  refine ⟨?_, ?_, ?_⟩
  · intro T o bg A f h
    simp [lock_BG, h, bind, Except.bind]
  · intro T o bg h
    simp [lock_BG_, h, bind, Except.bind]
  · intro T o bg h
    simp [unlock_BG, h, bind, Except.bind]

def entries : List Entry := [
  { id := "runtimecov-precomp-background-lock", juliaFile := "base/precompilation.jl"
    juliaFns := ["Base.lock(::Any, ::BackgroundPrecompileState)",
      "Base.lock(::BackgroundPrecompileState)", "Base.unlock(::BackgroundPrecompileState)"]
    statement := "Background-state lock methods delegate to the contained lock with the same callback or unit argument."
    source := "base/precompilation.jl:336-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .proven, prop := ``LockDelegateBodies, thm := some ``lockDelegateBodies_proven }
]

end JuliaLean.Proofs.base.precompilation.LegacyRuntime
