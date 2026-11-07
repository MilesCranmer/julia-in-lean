import JuliaLean.Proofs.base.array.access_bounds

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- `Base.include` grows `_included_files` when its next index reaches capacity, and
`strcat` allocates exactly the sum of its input byte lengths; `base/Base_compiler.jl:16-25,
194-205`. -/
def BootstrapBounds : Prop :=
  (∀ length capacity : Nat, length ≤ capacity → 0 < capacity →
    let grown := if length = capacity then capacity + 1 else capacity
    Access grown (length + 1) 1) ∧
  (∀ nx ny : Nat,
    Access (nx + ny) 1 nx ∧ Access (nx + ny) (nx + 1) ny)

theorem bootstrapBounds_proven : BootstrapBounds := by
  constructor
  · intro length capacity hlen hcap
    dsimp
    split
    · simp only [Access]
      right
      omega
    · simp only [Access]
      right
      omega
  · intro nx ny
    constructor
    · by_cases h : nx = 0
      · simp [Access, h]
      · simp only [Access]
        right
        omega
    · by_cases h : ny = 0
      · simp [Access, h]
      · simp only [Access]
        right
        omega

end JuliaLean.MemSafety.G1
