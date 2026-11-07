import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/summarysize.jl:45-190` -/

def frontierIndices (nf : Nat) : List Nat := (List.range nf).map (· + 1)

def summaryInlineAccesses (length np : Nat) : List Access :=
  if length = 0 || np = 0 then [] else
    (frontierIndices (length * np)).map fun (i : Nat) =>
      ⟨length, (((i - 1) / np + 1 : Nat) : Int)⟩

def summaryOutlineAccesses (length : Nat) : List Access :=
  (frontierIndices length).map fun (i : Nat) => ⟨length, (i : Int)⟩

def SummarySizeInBounds : Prop :=
  (∀ length np, AllInBounds (summaryInlineAccesses length np)) ∧
  (∀ length, AllInBounds (summaryOutlineAccesses length))





theorem summarySizeInBounds : SummarySizeInBounds := by
  constructor
  · intro length np access ha
    simp only [summaryInlineAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      simp only [frontierIndices, List.mem_map] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      simp only [List.mem_range] at hk
      rename_i hnonzero
      have hp : 0 < np := by
        simp at hnonzero
        omega
      have hk' : k < length * np := hk
      have hd : k / np < length := by
        exact (Nat.div_lt_iff_lt_mul hp).2 hk'
      simp only [Access.inBounds]
      simp
      constructor
      · exact_mod_cast Nat.succ_pos (k / np)
      · exact_mod_cast Nat.succ_le_of_lt hd
  · intro length access ha
    simp only [summaryOutlineAccesses, List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    simp only [frontierIndices, List.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [List.mem_range] at hk
    simp only [Access.inBounds]
    omega

end JuliaLean.MemSafety.G2
