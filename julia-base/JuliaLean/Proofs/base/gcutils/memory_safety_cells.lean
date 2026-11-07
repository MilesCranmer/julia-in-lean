import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- The `cglobal` objects loaded or stored at `base/gcutils.jl:163` and
`base/libdl.jl:517` are declared C globals of exactly the requested scalar
type, so `cglobal` computes offset zero in a one-cell object. -/
def runtimeCellAccesses (perform : Bool) : List Access :=
  if perform then [at0 1 0] else []

def RuntimeCellInBounds : Prop := ∀ perform,
  accessesSafe (runtimeCellAccesses perform)

theorem runtimeCellInBounds_proven : RuntimeCellInBounds := by
  intro perform
  cases perform <;> simp [runtimeCellAccesses, accessesSafe, Access.safe, at0]

end JuliaLean.MemSafety.G1
