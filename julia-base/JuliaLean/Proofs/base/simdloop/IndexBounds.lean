import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- `@simd` creates `i=0; while i<length(r)` and reads
`r[i+firstindex(r)]`, `base/simdloop.jl:47-85`. -/
def simdIndex (indices : List Int) (i : Nat) : Option Int := indices[i]?

def SimdIndexInBounds : Prop :=
  ∀ (indices : List Int) (i : Nat) (j : Int), simdIndex indices i = some j → j ∈ indices


theorem simdIndexInBounds : SimdIndexInBounds := by
  intro indices i j h
  have hi : i < indices.length := List.getElem?_eq_some_iff.mp h |>.1
  have hj : indices[i] = j := by simpa [simdIndex, List.getElem?_eq_getElem hi] using h
  rw [← hj]
  exact List.getElem_mem hi

end JuliaLean.MemSafety.G4
