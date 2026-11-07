import JuliaLean.Core

namespace JuliaLean.MemSafety.G5

def OneBasedInBounds (len index : Nat) : Prop := 1 ≤ index ∧ index ≤ len

/-- Julia's `1:n` loop, represented as one-based indices. -/
def oneBasedLoop (n : Nat) : List Nat := (List.range n).map Nat.succ

theorem oneBasedLoop_safe (n index : Nat) :
    index ∈ oneBasedLoop n → OneBasedInBounds n index := by
  intro h
  simp only [oneBasedLoop, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨by omega, by omega⟩

end JuliaLean.MemSafety.G5
