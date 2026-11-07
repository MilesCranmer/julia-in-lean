import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Number of set bits below `n`, matching the mask and `count_ones` in
`HAMT.entry_index`, `base/hamt.jl:138-141`. -/
def bitCountPrefix (bitmap : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bitCountPrefix bitmap n + if bitmap.testBit n then 1 else 0

/-- `HAMT.path` reads the entry whose zero-based position is the count of set
bits below `bi`. The representation invariant says the data length is the
number of set bits in the 32-bit bitmap. -/
def PersistentDictPathSafe : Prop :=
  ∀ (bitmap dataLength bi : Nat), bi < 32 → bitmap.testBit bi = true →
    dataLength = bitCountPrefix bitmap 32 →
      inOneBased dataLength (bitCountPrefix bitmap bi + 1)

private theorem bitCountPrefix_mono (bitmap : Nat) :
    ∀ {a b : Nat}, a ≤ b → bitCountPrefix bitmap a ≤ bitCountPrefix bitmap b
  | _, 0, h => by simp at h; subst h; exact Nat.le_refl _
  | a, b + 1, h => by
      by_cases hab : a = b + 1
      · subst hab; exact Nat.le_refl _
      · have ha : a ≤ b := by omega
        have ih := bitCountPrefix_mono bitmap ha
        simp only [bitCountPrefix]
        split <;> omega

theorem persistentDictPathSafe_proven : PersistentDictPathSafe := by
  intro bitmap dataLength bi hbi hset hlen
  have hstep : bitCountPrefix bitmap (bi + 1) = bitCountPrefix bitmap bi + 1 := by
    simp [bitCountPrefix, hset]
  have hmono := bitCountPrefix_mono bitmap (show bi + 1 ≤ 32 by omega)
  unfold inOneBased
  rw [hlen]
  omega

end JuliaLean.MemSafety.G3
