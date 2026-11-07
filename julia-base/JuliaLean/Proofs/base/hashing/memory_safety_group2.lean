import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/hashing.jl:378-466`: array hash windows -/

def window (start width : Nat) : List Nat :=
  (List.range width).map (start + ·)

def hashLoop : Nat → Nat → List Nat
  | i, pos =>
      if h : 48 < i then
        window pos 48 ++ hashLoop (i - 48) (pos + 48)
      else
        (if 16 < i then window pos 16 else []) ++
        (if 32 < i then window (pos + 16) 16 else [])
termination_by i pos => i
decreasing_by omega

def hashByteOffsets (n : Nat) : List Nat :=
  if n ≤ 16 then
    if 8 ≤ n then window 0 8 ++ window (n - 8) 8
    else if 4 ≤ n then window 0 4 ++ window (n - 4) 4
    else if 0 < n then [0, n - 1, n / 2]
    else []
  else hashLoop n 0 ++ window (n - 16) 8 ++ window (n - 8) 8

def hashArrayAccesses (a : Axis) : List Access :=
  (hashByteOffsets a.len).map fun (k : Nat) => ⟨a.len, (k : Int) + 1⟩

def HashArrayInBounds : Prop := ∀ a, AllInBounds (hashArrayAccesses a)





private theorem window_mem {start width k : Nat} (h : k ∈ window start width) :
    start ≤ k ∧ k < start + width := by
  simp [window] at h
  omega

private theorem hashLoop_mem : ∀ i pos k,
    k ∈ hashLoop i pos → pos ≤ k ∧ k < pos + i
  := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro pos k hk
      rw [hashLoop] at hk
      split at hk
      · rw [List.mem_append] at hk
        rcases hk with hk | hk
        · have hw := window_mem hk
          omega
        · have hr := ih (i - 48) (by omega) (pos + 48) k hk
          omega
      · rw [List.mem_append] at hk
        rcases hk with hk | hk
        · split at hk
          · have hw := window_mem hk
            omega
          · simp at hk
        · split at hk
          · have hw := window_mem hk
            omega
          · simp at hk

theorem hashByteOffsets_mem {n k : Nat} (h : k ∈ hashByteOffsets n) : k < n := by
  simp only [hashByteOffsets] at h
  split at h
  · split at h
    · rcases List.mem_append.mp h with h | h <;> have hw := window_mem h <;> omega
    · split at h
      · rcases List.mem_append.mp h with h | h <;> have hw := window_mem h <;> omega
      · split at h
        · simp at h
          rcases h with rfl | rfl | rfl <;> omega
        · simp at h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · have hh := hashLoop_mem n 0 k h
        omega
      · have hw := window_mem h
        omega
    · have hw := window_mem h
      omega

theorem hashArrayInBounds : HashArrayInBounds := by
  intro a access ha
  simp only [hashArrayAccesses, List.mem_map] at ha
  obtain ⟨k, hk, rfl⟩ := ha
  have hb := hashByteOffsets_mem hk
  simp only [Access.inBounds]
  omega

end JuliaLean.MemSafety.G2
