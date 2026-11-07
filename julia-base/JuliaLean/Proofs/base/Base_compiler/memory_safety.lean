import JuliaLean.Proofs.base.array.memory_safety

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

def strcatAccesses (xBytes yBytes : Nat) : List Access :=
  [span0 (xBytes + yBytes) 0 xBytes,
   span0 (xBytes + yBytes) xBytes yBytes]

def BootstrapStrcatInBounds : Prop := ∀ xBytes yBytes,
  accessesSafe (strcatAccesses xBytes yBytes)

theorem bootstrapStrcatInBounds_proven : BootstrapStrcatInBounds := by
  intro xBytes yBytes
  simp [strcatAccesses, accessesSafe, Access.safe, span0]

/-- Bootstrap `include`, `base/Base_compiler.jl:13-25`: the global vector has
offset one; the equality branch calls the full `_growend!` model with delta
one, and the other branch updates size before writing `len+1`. -/
def bootstrapIncludeAccesses (length capacity : Nat) : List Access :=
  if length ≤ capacity then
    if length = capacity then
      endGrowthAccesses ⟨capacity, 1, length⟩ 1 ++ [at0 (length + 1) length]
    else [at0 capacity length]
  else []

def BootstrapIncludeInBounds : Prop := ∀ length capacity,
  accessesSafe (bootstrapIncludeAccesses length capacity)

theorem bootstrapIncludeInBounds_proven : BootstrapIncludeInBounds := by
  intro length capacity a ha
  simp only [bootstrapIncludeAccesses] at ha
  split at ha
  · split at ha
    · simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact endGrowthInBounds_proven ⟨capacity, 1, length⟩ (by
          simp [VectorState.valid]; omega) 1 a ha
      · simp [Access.safe, at0]
    · simp only [List.mem_singleton] at ha
      subst a
      simp [Access.safe, at0]
      omega
  · simp at ha

def BootstrapInBounds : Prop := BootstrapIncludeInBounds ∧ BootstrapStrcatInBounds

theorem bootstrapInBounds_proven : BootstrapInBounds :=
  ⟨bootstrapIncludeInBounds_proven, bootstrapStrcatInBounds_proven⟩

end JuliaLean.MemSafety.G1
