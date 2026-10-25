import JuliaLean.Core

/-!
Lemmas on two's-complement wrapping (`JuliaLean.wrapInt`) used by this area's proofs.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

theorem wrapInt_emod (t : IntTy) (x : Int) : wrapInt t x = wrapInt t (x % 2 ^ t.bits) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_emod_self (t : IntTy) (x : Int) : wrapInt t x % 2 ^ t.bits = x % 2 ^ t.bits := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_wrapInt (t : IntTy) (x : Int) : wrapInt t (wrapInt t x) = wrapInt t x :=
  wrapInt_of_inRange t _ (wrapInt_bounds t x)

theorem wrapInt_add (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a + wrapInt t b) = wrapInt t (a + b) := by
  rw [wrapInt_emod t (wrapInt t a + wrapInt t b), Int.add_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.add_emod, ← wrapInt_emod]

theorem wrapInt_mul (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a * wrapInt t b) = wrapInt t (a * b) := by
  rw [wrapInt_emod t (wrapInt t a * wrapInt t b), Int.mul_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.mul_emod, ← wrapInt_emod]

theorem wrapInt_sub (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a - wrapInt t b) = wrapInt t (a - b) := by
  rw [wrapInt_emod t (wrapInt t a - wrapInt t b), wrapInt_emod t (a - b), Int.sub_emod,
    wrapInt_emod_self, wrapInt_emod_self, ← Int.sub_emod]

theorem wrapInt_zero (t : IntTy) : wrapInt t 0 = 0 :=
  wrapInt_of_inRange t 0 (by cases t <;> decide)

theorem wrapInt_neg (t : IntTy) (a : Int) : wrapInt t (-wrapInt t a) = wrapInt t (-a) := by
  have h := wrapInt_sub t 0 a
  rw [wrapInt_zero] at h
  simpa using h

theorem val_add {t : IntTy} (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
theorem val_sub {t : IntTy} (a b : JInt t) : (a - b).val = wrapInt t (a.val - b.val) := rfl
theorem val_mul {t : IntTy} (a b : JInt t) : (a * b).val = wrapInt t (a.val * b.val) := rfl
theorem val_neg {t : IntTy} (a : JInt t) : (-a).val = wrapInt t (-a.val) := rfl
theorem val_lit (t : IntTy) (x : Int) : (JInt.lit t x).val = wrapInt t x := rfl

theorem val_eq_wrap {t : IntTy} (a : JInt t) : a.val = wrapInt t a.val :=
  (wrapInt_of_inRange t a.val a.property).symm

end JuliaLean.ReinterpretArrays
