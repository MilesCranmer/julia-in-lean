import JuliaLean.Proofs.base.array.common.index_bounds

namespace JuliaLean.MemSafety.G5

/-! ## `base/stream.jl` -/

inductive RedirectGlobal where
  | stdin
  | stdout
  | stderr
  deriving DecidableEq

/-- The nested conditional at stream.jl:1949-1954, including the null branch. -/
def redirectTarget (fd : Int) : Option RedirectGlobal :=
  if fd = 0 then some .stdin
  else if fd = 1 then some .stdout
  else if fd = 2 then some .stderr
  else none

/-- `unsafe_store!(c_sym, value)` uses the implicit pointer offset one. -/
def redirectStoreOffset (fd : Int) : Option Nat := (redirectTarget fd).map (fun _ => 1)

/-- Every non-null target selected by `_redirect_io_cglobal` is a scalar C
global, and the actual implicit store offset is one. -/
def StreamRedirectAccessesInBounds : Prop :=
  ∀ fd offset, redirectStoreOffset fd = some offset → OneBasedInBounds 1 offset

theorem streamRedirectAccessesInBounds : StreamRedirectAccessesInBounds := by
  intro fd offset h
  unfold redirectStoreOffset redirectTarget at h
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst offset
    simp [OneBasedInBounds]
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst offset
    simp [OneBasedInBounds]
  split at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst offset
    simp [OneBasedInBounds]
  · simp at h


end JuliaLean.MemSafety.G5
