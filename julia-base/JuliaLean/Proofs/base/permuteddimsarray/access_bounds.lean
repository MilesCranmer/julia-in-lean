import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## Permuted-dimension tiled loops -/

/-- The two tiled `_permutedims!` kernels visit an axis in blocks of eight. -/
def tiledAxis (first len : Nat) : List Int :=
  (List.range ((len + 7) / 8)).flatMap fun block =>
    (List.range (min 8 (len - 8 * block))).map fun lane =>
      (first + 8 * block + lane : Nat)

def PermutedTileLoopsInBounds : Prop :=
  ∀ first len i, i ∈ tiledAxis first len → first ≤ i ∧ i < first + len

theorem permutedTileLoopsInBounds_proven : PermutedTileLoopsInBounds := by
  intro first len i hi
  unfold tiledAxis at hi
  rw [List.mem_flatMap] at hi
  obtain ⟨block, hxs, hix⟩ := hi
  rw [List.mem_map] at hix
  obtain ⟨lane, hl, rfl⟩ := hix
  have hbm := List.mem_range.mp hxs
  have hlm := List.mem_range.mp hl
  constructor <;> omega
end JuliaLean.MemSafety.G6
end
