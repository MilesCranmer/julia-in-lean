import JuliaLean.Proofs.base.array.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- Swap operations combine checked row or column indices with traversal of the other
axis; `base/combinatorics.jl:103-123,286-296`. -/
def CombinatoricsBounds : Prop := GuardedBounds ∧ IteratorBounds

theorem combinatoricsBounds_proven : CombinatoricsBounds :=
  ⟨guardedBounds_proven, iteratorBounds_proven⟩

end JuliaLean.MemSafety.G1
