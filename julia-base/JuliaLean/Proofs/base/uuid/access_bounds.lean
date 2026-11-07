import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## UUID formatting -/

def uuidHyphens : List Nat := [9, 14, 19, 24]

def uuidHexIndex (value : Nat) (digit : Nat) : Nat :=
  1 + (value / (16 ^ digit)) % 16

def uuidDestination (digit : Nat) : Nat :=
  if digit < 12 then 36 - digit
  else if digit < 16 then 35 - digit
  else if digit < 20 then 34 - digit
  else if digit < 24 then 33 - digit
  else 32 - digit

def uuidWrites (value : Nat) : List (Nat × Nat) :=
  (List.range 32).map fun digit =>
    (uuidDestination digit, uuidHexIndex value digit)

def UuidWritesInBounds : Prop :=
  (∀ value destination hexIndex, (destination, hexIndex) ∈ uuidWrites value →
    1 ≤ destination ∧ destination ≤ 36 ∧ 1 ≤ hexIndex ∧ hexIndex ≤ 16) ∧
  (∀ destination ∈ uuidHyphens, 1 ≤ destination ∧ destination ≤ 36)

theorem uuidWritesInBounds_proven : UuidWritesInBounds := by
  constructor
  · intro value destination hexIndex h
    unfold uuidWrites at h
    rw [List.mem_map] at h
    obtain ⟨digit, hd, h⟩ := h
    have hd' := List.mem_range.mp hd
    cases h
    have hm := Nat.mod_lt (value / 16 ^ digit) (by decide : 0 < 16)
    have hdest : 1 ≤ uuidDestination digit ∧ uuidDestination digit ≤ 36 := by
      unfold uuidDestination
      split
      · omega
      · split
        · omega
        · split
          · omega
          · split <;> omega
    exact ⟨hdest.1, hdest.2, by simp [uuidHexIndex], by simp [uuidHexIndex]; omega⟩
  · intro destination h
    simp [uuidHyphens] at h
    rcases h with rfl | rfl | rfl | rfl <;> omega
end JuliaLean.MemSafety.G6
end
