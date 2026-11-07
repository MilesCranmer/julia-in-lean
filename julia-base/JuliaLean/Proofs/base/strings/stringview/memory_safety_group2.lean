import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/strings/stringview.jl:126-150` -/

def stringRangeAccesses (bytes : List UInt8) (first last : Int) : List Access :=
  if first ≤ last && 1 ≤ first && last ≤ bytes.length then
    [⟨bytes.length, first⟩, ⟨bytes.length, last⟩]
  else []

def chompLength (bytes : List UInt8) : Nat :=
  let n := bytes.length
  if n = 0 then 0 else
    let hasLf := bytes.getD (n - 1) 0 == 0x0a
    let twoBytes := 1 < n
    let crIndex := if twoBytes then n - 2 else n - 1
    let hasCr := hasLf && bytes.getD crIndex 0 == 0x0d
    n - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)

def chompAccesses (bytes : List UInt8) : List Access :=
  let len := chompLength bytes
  if len = 0 then [] else (oneBased len).map fun i => ⟨bytes.length, i⟩

def StringViewInBounds : Prop := ∀ bytes first last,
  AllInBounds (stringRangeAccesses bytes first last) ∧
  AllInBounds (chompAccesses bytes)





private theorem chompLength_le (bytes : List UInt8) : chompLength bytes ≤ bytes.length := by
  rw [chompLength]
  split
  · omega
  · dsimp only
    exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem stringViewInBounds : StringViewInBounds := by
  intro bytes first last
  constructor
  · intro access ha
    simp only [stringRangeAccesses] at ha
    split at ha
    · simp_all only [Bool.and_eq_true, decide_eq_true_eq]
      simp at ha
      rcases ha with rfl | rfl
      · simp only [Access.inBounds]
        omega
      · simp only [Access.inBounds]
        omega
    · simp at ha
  · intro access ha
    simp only [chompAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      have hb := oneBased_mem hi
      have hl := chompLength_le bytes
      simp only [Access.inBounds]
      omega

end JuliaLean.MemSafety.G2
