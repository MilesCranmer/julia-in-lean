import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- libuv returns `count` initialized records and the loop is `1:count`,
`base/sysinfo.jl:309-323`. -/
def cpuInfoIndex (count i : Nat) : Option Int := if i < count then some (i + 1) else none

def CpuInfoInBounds : Prop :=
  ∀ (count i : Nat) (j : Int), cpuInfoIndex count i = some j → InBounds count j


theorem cpuInfoInBounds : CpuInfoInBounds := by
  intro count i j h
  unfold cpuInfoIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst j
    unfold InBounds
    omega
  · contradiction

end JuliaLean.MemSafety.G4
