import JuliaLean.Proofs.base.array.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- Set operations combine a checked Dict-table index with indices yielded by an array
axis; `base/set.jl:139-157,373-405,579-592,947-1005`. -/
def SetBounds : Prop := GuardedBounds ∧ IteratorBounds

theorem setBounds_proven : SetBounds := ⟨guardedBounds_proven, iteratorBounds_proven⟩

end JuliaLean.MemSafety.G1
