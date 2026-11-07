import JuliaLean.Proofs.base.array.common
import JuliaLean.Proofs.base.strings.basic.access_bounds


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-- `SubString` construction checks a one-based byte span. `unannotate` forwards that stored
span to `raw_substring`; AnnotatedString indexing first checks its index and then uses the same
underlying String index (`base/strings/annotated.jl:184-199`). -/
def annotatedSubstringAccesses (parentLen start count : Nat) : List Int :=
  if 1 ≤ start ∧ start + count ≤ parentLen + 1 then span start count else []

def AnnotatedStringAccessesInBounds : Prop :=
  (∀ parentLen start count i, i ∈ annotatedSubstringAccesses parentLen start count →
    inBounds parentLen i) ∧
  (∀ s index i, i ∈ checkedStringAccesses s index → inBounds s.bytes.length i)

theorem annotatedStringAccessesInBounds_proven : AnnotatedStringAccessesInBounds := by
  constructor
  · intro parentLen start count i hi
    unfold annotatedSubstringAccesses at hi
    split at hi
    · rename_i hspan
      obtain ⟨k, hk, rfl⟩ := mem_span hi
      simp [inBounds]
      omega
    · simp_all
  · intro s index i hi
    exact getindexStringAccesses_safe s index i hi
end JuliaLean.MemSafety.G6
end
