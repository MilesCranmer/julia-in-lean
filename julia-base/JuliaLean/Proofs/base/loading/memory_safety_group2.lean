import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/loading.jl:46-65`: macOS `getattrlist` header -/

def headerAccess (n : Nat) : List Access :=
  [⟨n, 9⟩, ⟨n, 10⟩, ⟨n, 11⟩, ⟨n, 12⟩]

def loadingHeaderAccess (basenameLength returnedLength : Nat) : List Access :=
  let initial := basenameLength + 12 + 1
  headerAccess initial ++
    if initial < returnedLength + 12 then headerAccess (returnedLength + 12) else []

def LoadingHeaderInBounds : Prop := ∀ basenameLength returnedLength,
  AllInBounds (loadingHeaderAccess basenameLength returnedLength)





theorem loadingHeaderInBounds : LoadingHeaderInBounds := by
  have headerSafe : ∀ n, 12 ≤ n → AllInBounds (headerAccess n) := by
    intro n hn access ha
    simp [headerAccess] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [Access.inBounds] <;> omega
  intro basename returned access ha
  simp only [loadingHeaderAccess, List.mem_append] at ha
  rcases ha with ha | ha
  · exact headerSafe _ (by omega) access ha
  · split at ha
    · exact headerSafe _ (by omega) access ha
    · simp at ha

end JuliaLean.MemSafety.G2
