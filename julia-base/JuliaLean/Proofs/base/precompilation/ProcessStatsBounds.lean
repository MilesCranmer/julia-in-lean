import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- The three fixed reads from the 96-byte `proc_taskinfo` allocation,
`base/precompilation.jl:2102-2111`. -/
inductive ProcessStatSite where
  | rss
  | user
  | system

def processStatsRead (apple : Bool) (ret : Int) (site : ProcessStatSite) : Option ByteSpan :=
  if apple ∧ ret > 0 then
    some <| match site with
      | .rss => ⟨96, 8, 8⟩
      | .user => ⟨96, 16, 8⟩
      | .system => ⟨96, 24, 8⟩
  else none

def ProcessStatsReadsInBounds : Prop :=
  ∀ apple ret site span, processStatsRead apple ret site = some span → span.safe


theorem processStatsReadsInBounds : ProcessStatsReadsInBounds := by
  intro apple ret site span h
  cases apple <;> cases site <;> by_cases hr : 0 < ret <;>
    simp_all [processStatsRead] <;> subst span <;> simp [ByteSpan.safe]

end JuliaLean.MemSafety.G4
