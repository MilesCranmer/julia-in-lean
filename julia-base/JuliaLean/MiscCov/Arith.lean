import JuliaLean.Core
import JuliaLean.ParsePrint.Bits

/-!
Value lemmas for the wrapping `JInt` operations and the `ParsePrint` bit
helpers, used by the `MiscCov` proofs.
-/

namespace JuliaLean.MiscCov

open JuliaLean JuliaLean.ParsePrint

theorem val_bounds {t : IntTy} (x : JInt t) : t.min ≤ x.val ∧ x.val ≤ t.max := x.property

/-- The value of an unsigned `JInt` is in `0 : 2^bits - 1`. -/
theorem uval_bounds {t : IntTy} (h : t.signed = false) (x : JInt t) :
    0 ≤ x.val ∧ x.val < 2 ^ t.bits := by
  have := x.property
  simp [IntTy.min, IntTy.max, h] at this
  omega

/-- `x % T` for unsigned `T` is reduction modulo `2^bits`. -/
theorem wrap_val_u {t : IntTy} (h : t.signed = false) (x : Int) :
    (JInt.wrap t x).val = x % 2 ^ t.bits := by
  simp [JInt.wrap, wrapInt, h]

theorem wrap_val_of_range {t : IntTy} (x : Int) (h : t.min ≤ x ∧ x ≤ t.max) :
    (JInt.wrap t x).val = x := by
  simp [JInt.wrap, wrapInt_of_inRange t x h]

theorem add_val (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
theorem mul_val (a b : JInt t) : (a * b).val = wrapInt t (a.val * b.val) := rfl
theorem sub_val (a b : JInt t) : (a - b).val = wrapInt t (a.val - b.val) := rfl
theorem rem_val (t' : IntTy) (a : JInt t) : (JInt.rem t' a).val = wrapInt t' a.val := rfl
theorem lit_val (t : IntTy) (x : Int) : (JInt.lit t x).val = wrapInt t x := rfl
theorem shr_val (x : JInt t) (k : Nat) : (shr x k).val = wrapInt t ((x.val.toNat / 2 ^ k : Nat) : Int) := rfl
theorem shl_val (x : JInt t) (k : Nat) : (shl x k).val = wrapInt t ((x.val.toNat * 2 ^ k : Nat) : Int) := rfl
theorem band_val (x y : JInt t) : (band x y).val = wrapInt t ((Nat.land x.val.toNat y.val.toNat : Nat) : Int) := rfl
theorem bor_val (x y : JInt t) : (bor x y).val = wrapInt t ((Nat.lor x.val.toNat y.val.toNat : Nat) : Int) := rfl

end JuliaLean.MiscCov
