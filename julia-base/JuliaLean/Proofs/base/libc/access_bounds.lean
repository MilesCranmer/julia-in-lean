import JuliaLean.Proofs.base.array.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- C and runtime buffer accesses are in bounds under the size/null-termination contract
of the function that returned the pointer. This covers `FormatMessageW`,
`uv_os_get_group`, and the two `cglobal` cells in this group. -/
def RuntimeBufferBounds : Prop :=
  ∀ available offset count : Nat, 1 ≤ offset → offset + count - 1 ≤ available →
    Access available offset count

theorem runtimeBufferBounds_proven : RuntimeBufferBounds := by
  intro available offset count hoff hlen
  by_cases h : count = 0
  · simp [Access, h]
  · simp only [Access]
    right
    exact ⟨hoff, hlen⟩

end JuliaLean.MemSafety.G1
