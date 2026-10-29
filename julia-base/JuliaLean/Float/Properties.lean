import JuliaLean.Float.Extras
import JuliaLean.Registry.Types

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.Float

/-- `isless` places any pair in exactly one order or the same `isequal` class. -/
def islessPartition : Prop := ∀ x y : F64,
  (F64.isless x y = true ∨ F64.isless y x = true ∨ F64.isequal x y = true) ∧
  (F64.isequal x y = true ↔ F64.isless x y = false ∧ F64.isless y x = false)

theorem islessPartition_proven : islessPartition := by
  intro x y
  have hnan : F64.toBits x = F64.toBits y → F64.isnan x = F64.isnan y := by
    intro h
    simp only [F64.isnan, F64.exponentField, F64.fraction, h]
  have hsign : F64.toBits x = F64.toBits y → F64.signbit x = F64.signbit y := by
    intro h
    simp only [F64.signbit, h]
  cases hx : F64.isnan x <;> cases hy : F64.isnan y <;>
    cases sx : F64.signbit x <;> cases sy : F64.signbit y <;>
    simp only [F64.isless, F64.isequal, hx, hy, sx, sy] <;>
    simp_all <;> omega

/-- The strict order used for sorting is transitive, including NaNs and signed zero. -/
def islessTransitive : Prop := ∀ x y z : F64,
  F64.isless x y = true → F64.isless y z = true → F64.isless x z = true

theorem islessTransitive_proven : islessTransitive := by
  intro x y z hxy hyz
  cases hx : F64.isnan x <;> cases hy : F64.isnan y <;> cases hz : F64.isnan z <;>
    cases sx : F64.signbit x <;> cases sy : F64.signbit y <;> cases sz : F64.signbit z <;>
    simp only [F64.isless, hx, hy, hz, sx, sy, sz] at hxy hyz ⊢ <;>
    simp_all <;> omega

/-- Every signed and unsigned 8-bit integer converts without losing its exact value. -/
def smallIntegerExact : Prop := ∀ n : Fin 256, ∀ signed : Bool,
  let t := if signed then IntTy.i8 else IntTy.u8
  let x := JInt.wrap t (Int.ofNat n.val)
  let r := F64.toRat (F64.ofJInt x)
  r.2 > 0 ∧ r.1 = x.val * Int.ofNat r.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallIntegerExact_proven : smallIntegerExact := by
  unfold smallIntegerExact
  decide

/-- The strict RoundDown remainder interval promised by `base/div.jl:95-97`. -/
def remDownBound : Prop := ∀ x y : F64,
  F64.isfinite x = true → F64.isfinite y = true → F64.lt (F64.zero false) y = true →
  F64.le (F64.zero false) (F64.remMode x y .RoundDown) = true ∧
  F64.lt (F64.remMode x y .RoundDown) y = true

theorem remDownBound_refuted : ¬ remDownBound := by
  intro h
  have hh := h (F64.ofBits 0x8000000000000001) F64.one
    (by decide) (by decide) (by decide)
  have bad : F64.lt
    (F64.remMode (F64.ofBits 0x8000000000000001) F64.one .RoundDown) F64.one = false := by decide
  rw [bad] at hh
  exact Bool.false_ne_true hh.2

open JuliaLean.Registry

def propertyEntries : List Entry := []

end JuliaLean.Float
