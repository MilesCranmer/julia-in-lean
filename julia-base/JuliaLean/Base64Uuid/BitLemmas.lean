import JuliaLean.Base64Uuid.Basic

/-!
Lemmas translating the unsigned bit operations of `JuliaLean.ParsePrint.Bits` into
`Nat` arithmetic on the values.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- The value of an unsigned integer as a natural number. -/
def vn {t : IntTy} (x : JInt t) : Nat := x.val.toNat

/-- The unsigned integer types. -/
def Uns (t : IntTy) : Prop := t.signed = false

theorem uns_u8 : Uns .u8 := rfl
theorem uns_u32 : Uns .u32 := rfl
theorem uns_u64 : Uns .u64 := rfl
theorem uns_u128 : Uns .u128 := rfl

theorem vn_wrap {t : IntTy} (hu : Uns t) (n : Nat) : vn (JInt.wrap t (n : Int)) = n % 2 ^ t.bits := by
  unfold Uns at hu
  simp only [vn, JInt.wrap, wrapInt, hu, Bool.false_eq_true, ite_false]
  exact Int.toNat_natCast _

theorem val_nonneg {t : IntTy} (hu : Uns t) (x : JInt t) : 0 ≤ x.val := by
  have h := x.property.1
  unfold Uns at hu
  cases t <;> simp_all [IntTy.min, IntTy.signed]

theorem val_eq_vn {t : IntTy} (hu : Uns t) (x : JInt t) : x.val = (vn x : Int) := by
  simp only [vn]; exact (Int.toNat_of_nonneg (val_nonneg hu x)).symm

theorem vn_lt {t : IntTy} (hu : Uns t) (x : JInt t) : vn x < 2 ^ t.bits := by
  have h := x.property.2
  have h0 := val_nonneg hu x
  unfold Uns at hu
  simp only [vn]
  cases t <;> simp_all [IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem vn_inj {t : IntTy} (hu : Uns t) {x y : JInt t} (h : vn x = vn y) : x = y := by
  apply Subtype.ext
  rw [val_eq_vn hu x, val_eq_vn hu y, h]

theorem vn_band {t : IntTy} (hu : Uns t) (x y : JInt t) : vn (band x y) = vn x &&& vn y := by
  simp only [band]
  rw [vn_wrap hu]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (vn_lt hu y))

theorem vn_bor {t : IntTy} (hu : Uns t) (x y : JInt t) : vn (bor x y) = vn x ||| vn y := by
  simp only [bor]
  rw [vn_wrap hu]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (vn_lt hu x) (vn_lt hu y))

theorem xor_lt_pow {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) : x ^^^ y < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi)),
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))]
  rfl

theorem vn_bxor {t : IntTy} (hu : Uns t) (x y : JInt t) : vn (bxor x y) = vn x ^^^ vn y := by
  simp only [bxor]
  rw [vn_wrap hu]
  exact Nat.mod_eq_of_lt (xor_lt_pow (vn_lt hu x) (vn_lt hu y))

theorem vn_shr {t : IntTy} (hu : Uns t) (x : JInt t) (k : Nat) : vn (shr x k) = vn x / 2 ^ k := by
  simp only [shr]
  change vn (JInt.wrap t ((x.val.toNat / 2 ^ k : Nat) : Int)) = _
  rw [vn_wrap hu]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (vn_lt hu x))

theorem vn_shl {t : IntTy} (hu : Uns t) (x : JInt t) (k : Nat) :
    vn (shl x k) = vn x * 2 ^ k % 2 ^ t.bits := by
  simp only [shl]
  change vn (JInt.wrap t ((x.val.toNat * 2 ^ k : Nat) : Int)) = _
  rw [vn_wrap hu]; rfl

theorem vn_rem {t t' : IntTy} (hu : Uns t) (hu' : Uns t') (x : JInt t) :
    vn (JInt.rem t' x) = vn x % 2 ^ t'.bits := by
  simp only [JInt.rem]
  rw [val_eq_vn hu x, vn_wrap hu']

theorem bn_eq_vn (x : Byte) : bn x = vn x := rfl

end JuliaLean.Base64Uuid
