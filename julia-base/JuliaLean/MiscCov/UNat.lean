import JuliaLean.MiscCov.Arith

/-!
The natural-number value `nv x` of an unsigned `JInt`, and how the wrapping
operations act on it. Used to reduce unsigned Julia arithmetic to `Nat`
arithmetic modulo `2^bits`.
-/

namespace JuliaLean.MiscCov

open JuliaLean JuliaLean.ParsePrint

/-- The value of an unsigned Julia integer as a natural number. -/
def nv {t : IntTy} (x : JInt t) : Nat := x.val.toNat

section
variable {t : IntTy} (h : t.signed = false)
include h

theorem val_nv (x : JInt t) : x.val = (nv x : Int) := by
  have := (uval_bounds h x).1
  rw [nv, Int.toNat_of_nonneg this]

theorem nv_lt (x : JInt t) : nv x < 2 ^ t.bits := by
  have ⟨h0, h1⟩ := uval_bounds h x
  rw [nv, Int.toNat_lt h0]
  exact_mod_cast h1

theorem wrapInt_nat (x : Nat) : wrapInt t x = ((x % 2 ^ t.bits : Nat) : Int) := by
  simp only [wrapInt, h, Bool.false_eq_true, ↓reduceIte]
  push_cast
  rfl

theorem nv_wrap (x : Nat) : nv (JInt.wrap t x) = x % 2 ^ t.bits := by
  show (wrapInt t x).toNat = _
  rw [wrapInt_nat h, Int.toNat_natCast]

theorem nv_mul (a b : JInt t) : nv (a * b) = (nv a * nv b) % 2 ^ t.bits := by
  show (wrapInt t (a.val * b.val)).toNat = _
  rw [val_nv h a, val_nv h b, ← Int.natCast_mul, wrapInt_nat h, Int.toNat_natCast]

theorem nv_add (a b : JInt t) : nv (a + b) = (nv a + nv b) % 2 ^ t.bits := by
  show (wrapInt t (a.val + b.val)).toNat = _
  rw [val_nv h a, val_nv h b, ← Int.natCast_add, wrapInt_nat h, Int.toNat_natCast]

theorem nv_shr (x : JInt t) (k : Nat) : nv (shr x k) = nv x / 2 ^ k := by
  show (wrapInt t ((x.val.toNat / 2 ^ k : Nat) : Int)).toNat = _
  rw [wrapInt_nat h, Int.toNat_natCast]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (nv_lt h x)

theorem nv_shl (x : JInt t) (k : Nat) : nv (shl x k) = (nv x * 2 ^ k) % 2 ^ t.bits := by
  show (wrapInt t ((x.val.toNat * 2 ^ k : Nat) : Int)).toNat = _
  rw [wrapInt_nat h, Int.toNat_natCast]
  rfl

theorem nv_bor (x y : JInt t) : nv (bor x y) = nv x ||| nv y := by
  show (wrapInt t ((Nat.lor x.val.toNat y.val.toNat : Nat) : Int)).toNat = _
  rw [wrapInt_nat h, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (nv_lt h x) (nv_lt h y))

theorem nv_band (x y : JInt t) : nv (band x y) = nv x &&& nv y := by
  show (wrapInt t ((Nat.land x.val.toNat y.val.toNat : Nat) : Int)).toNat = _
  rw [wrapInt_nat h, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (nv_lt h y))

theorem nv_lit (x : Nat) : nv (JInt.lit t x) = x % 2 ^ t.bits := nv_wrap h x

end

theorem nv_rem {t t' : IntTy} (h : t.signed = false) (h' : t'.signed = false) (a : JInt t) :
    nv (JInt.rem t' a) = nv a % 2 ^ t'.bits := by
  show (wrapInt t' a.val).toNat = _
  rw [val_nv h a, wrapInt_nat h', Int.toNat_natCast]

theorem nv_sub32 (a b : JInt .u32) : nv (a - b) = (nv a + (4294967296 - nv b)) % 4294967296 := by
  have hb := nv_lt (t := .u32) rfl b
  simp only [IntTy.bits, Nat.reducePow] at hb
  show (wrapInt .u32 (a.val - b.val)).toNat = _
  rw [val_nv (t := .u32) rfl a, val_nv (t := .u32) rfl b]
  have : wrapInt .u32 ((nv a : Int) - nv b) = (((nv a + (4294967296 - nv b)) % 4294967296 : Nat) : Int) := by
    simp only [wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true, ↓reduceIte, Int.reducePow]
    omega
  rw [this, Int.toNat_natCast]

theorem val_of_nv {t : IntTy} (h : t.signed = false) (x : JInt t) (n : Nat) (hx : nv x = n) :
    x.val = n := by rw [val_nv h x, hx]

end JuliaLean.MiscCov
