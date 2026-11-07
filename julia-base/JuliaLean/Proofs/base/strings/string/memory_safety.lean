import JuliaLean.Proofs.base.abstractarray.memory_safety_access

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- Every byte position that `isvalid(s, i)` can inspect.  `_thisind_str` first
reads `i`, then its continuation-byte slow path reads at most the three
preceding code units (`base/strings/string.jl:252-271`). -/
def stringIsvalidAccesses (length : Nat) (i : Int) : List Access :=
  if 1 ≤ i ∧ i ≤ length then
    (List.range (min 4 i.toNat)).map fun k => at0 length (i.toNat - 1 - k)
  else []

def StringIsvalidInBounds : Prop :=
  ∀ length i, accessesSafe (stringIsvalidAccesses length i)

theorem stringIsvalidInBounds_proven : StringIsvalidInBounds := by
  intro length i a ha
  simp only [stringIsvalidAccesses] at ha
  split at ha
  · simp only [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    simp only [List.mem_range] at hk
    simp [Access.safe, at0]
    have hi : i.toNat ≤ length := by
      have hic : (i.toNat : Int) = i := Int.toNat_of_nonneg (by omega)
      omega
    omega
  · simp at ha

end JuliaLean.MemSafety.G1
