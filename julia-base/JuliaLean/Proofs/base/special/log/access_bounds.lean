import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## Log table indices -/

def roundTiesEven (numerator denominator : Nat) : Nat :=
  let q := numerator / denominator
  let r := numerator % denominator
  q + if denominator < 2 * r ∨ (denominator = 2 * r ∧ q % 2 = 1) then 1 else 0

/-- The `F = (y+C)-C` operation rounds the normalized mantissa to seven fraction bits. -/
def logProc1Index (fractionBits fractionWidth : Nat) : Nat :=
  let dropped := 2 ^ (fractionWidth - 7)
  128 + roundTiesEven fractionBits dropped - 127

/-- `_log_ext`: wrapping subtraction, arithmetic shift and `& (128-1)`, followed by `+1`.
Using the unsigned bit pattern gives the same low seven selected bits. -/
def logExtIndex (xu : Nat) : Nat :=
  ((((xu + 2 ^ 64 - 0x3fe6955500000000) % (2 ^ 64)) / (2 ^ 45)) % 128) + 1

def LogTableAccessesInBounds : Prop :=
  (∀ fraction : Fin (2 ^ 52), 1 ≤ logProc1Index fraction 52 ∧
      logProc1Index fraction 52 ≤ 129) ∧
  (∀ fraction : Fin (2 ^ 23), 1 ≤ logProc1Index fraction 23 ∧
      logProc1Index fraction 23 ≤ 129) ∧
  (∀ xu : Nat, 1 ≤ logExtIndex xu ∧ logExtIndex xu ≤ 128)

theorem logTableAccessesInBounds_proven : LogTableAccessesInBounds := by
  constructor
  · intro fraction
    unfold logProc1Index roundTiesEven
    have hf := fraction.isLt
    simp only [Nat.reduceSubDiff, Nat.reducePow]
    split <;> omega
  constructor
  · intro fraction
    unfold logProc1Index roundTiesEven
    have hf := fraction.isLt
    simp only [Nat.reduceSubDiff, Nat.reducePow]
    split <;> omega
  · intro xu
    unfold logExtIndex
    have hm := Nat.mod_lt (((xu + 2 ^ 64 - 0x3fe6955500000000) % 2 ^ 64) / 2 ^ 45)
      (by decide : 0 < 128)
    omega
end JuliaLean.MemSafety.G6
end
