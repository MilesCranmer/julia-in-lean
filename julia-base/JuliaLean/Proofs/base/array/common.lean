import JuliaLean.Proofs.base.array.common.convert
import JuliaLean.Proofs.base.array.common.copy
import JuliaLean.Proofs.base.array.common.grow

namespace JuliaLean.MemSafety.G6

open JuliaLean

def inBounds (len : Nat) (i : Int) : Prop := 1 ≤ i ∧ i ≤ len

def checkedIndex (len : Nat) (i : Int) : Option Int :=
  if 1 ≤ i ∧ i ≤ len then some i else none

def span (first count : Nat) : List Int :=
  (List.range count).map fun k => (first + k : Nat)

theorem mem_span {first count : Nat} {i : Int} (h : i ∈ span first count) :
    ∃ k < count, i = first + k := by
  unfold span at h
  rw [List.mem_map] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, List.mem_range.mp hk, by omega⟩

end JuliaLean.MemSafety.G6
