import JuliaLean.base.float
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.int

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.Promotion

theorem Fmt.width_pow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega, Nat.pow_succ, Nat.mul_comm]

namespace Fl

theorem toBits_ofBits {f : Fmt} (v : Nat) : (Fl.ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem ofBits_toBits {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hv]

theorem ext_toBits {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  rw [← Fl.ofBits_toBits x, ← Fl.ofBits_toBits y, h]

theorem bits_split {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := Fmt.width_pow f
    have h3 : x.toBits = x.bits.val := rfl
    omega
  have hW := Nat.two_pow_pos (f.eb + f.sb)
  refine ⟨?_, Nat.mod_lt _ hW⟩
  unfold Fl.signbit Fl.magnitude
  by_cases hs : x.toBits ≥ 2 ^ (f.eb + f.sb)
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_true, ↓reduceIte]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [hs]

theorem expField_eq {f : Fmt} (x : Fl f) : x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem frac_eq {f : Fmt} (x : Fl f) : x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

end Fl
end JuliaLean.Promotion

namespace JuliaLean.Proofs.base.float

open JuliaLean JuliaLean.C JuliaLean.Registry JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion

/-! ## Basic integer and bit-pattern lemmas -/

theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2); omega

theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp at h ⊢ <;> omega

theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem wrapInt_val {t : IntTy} (x : JInt t) : wrapInt t x.val = x.val :=
  wrapInt_of_inRange t x.val x.property

theorem jint_eq {t : IntTy} {x y : JInt t} (h : x.val = y.val) : x = y := Subtype.ext h

theorem fromJInt_toNat {t : IntTy} (x : JInt t) :
    ((fromJInt x).toNat : Int) = x.val % ((2 ^ t.bits : Nat) : Int) := by
  simp only [fromJInt, BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := two_pow_pos_int t.bits; omega))

theorem fromJInt_toInt {t : IntTy} (x : JInt t) (h : t.signed = true) : (fromJInt x).toInt = x.val := by
  have hx := x.property
  simp only [fromJInt, BitVec.toInt_ofInt]
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, Int.bmod_def] <;> split <;> omega

theorem fromJInt_toNat_unsigned {t : IntTy} (x : JInt t) (h : t.signed = false) :
    ((fromJInt x).toNat : Int) = x.val := by
  have hx := x.property
  rw [fromJInt_toNat]
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

theorem toJInt_val (t : IntTy) (b : BitVec t.bits) :
    (toJInt t b).val = wrapInt t (if t.signed then b.toInt else (b.toNat : Int)) := rfl

theorem toJInt_ofInt_val (t : IntTy) (z : Int) : (toJInt t (BitVec.ofInt t.bits z)).val = wrapInt t z := by
  rw [toJInt_val]
  apply wrapInt_congr
  split
  · rw [BitVec.toInt_ofInt]
    exact Int.bmod_emod
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := two_pow_pos_int t.bits; omega)), Int.emod_emod]

theorem toJInt_ofNat_val (t : IntTy) (n : Nat) : (toJInt t (BitVec.ofNat t.bits n)).val = wrapInt t n := by
  rw [← BitVec.ofInt_natCast, toJInt_ofInt_val]

theorem toJInt_congr {t : IntTy} (b : BitVec t.bits) (z : Int)
    (h : (b.toNat : Int) = z % ((2 ^ t.bits : Nat) : Int)) : (toJInt t b).val = wrapInt t z := by
  have hb : b = BitVec.ofInt t.bits z := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    omega
  rw [hb, toJInt_ofInt_val]

theorem bitcast_val (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits = T.bits) :
    (int.bitcast T x h).val = wrapInt T x.val := by
  unfold int.bitcast
  apply toJInt_congr
  simp only [jlBitcast, BitVec.toNat_cast]
  rw [fromJInt_toNat, h]

theorem slt_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    int.slt_int x y = decide (x.val < y.val) := by
  simp only [int.slt_int, jlSltInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem sle_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    int.sle_int x y = decide (x.val ≤ y.val) := by
  simp only [int.sle_int, jlSleInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem ult_int_eq {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    int.ult_int x y = decide (x.val < y.val) := by
  have hx := fromJInt_toNat_unsigned x h
  have hy := fromJInt_toNat_unsigned y h
  simp only [int.ult_int, jlUltInt]
  by_cases hl : x.val < y.val <;> simp [hl] <;> omega

theorem ule_int_eq {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    int.ule_int x y = decide (x.val ≤ y.val) := by
  have hx := fromJInt_toNat_unsigned x h
  have hy := fromJInt_toNat_unsigned y h
  simp only [int.ule_int, jlUleInt]
  by_cases hl : x.val ≤ y.val <;> simp [hl] <;> omega

theorem eq_int_eq {t : IntTy} (x y : JInt t) : int.eq_int x y = decide (x.val = y.val) := by
  simp only [int.eq_int, jlEqInt]
  by_cases h : x.val = y.val
  · simp [fromJInt, show x = y from jint_eq h]
  · have : fromJInt x ≠ fromJInt y := by
      intro hb; apply h
      rw [← wrapInt_val x, ← wrapInt_val y, ← toJInt_ofInt_val, ← toJInt_ofInt_val]
      exact congrArg (fun b => (toJInt t b).val) hb
    simp [h, this]

/-! ## IEEEFloat format and intrinsic bridge lemmas -/

theorem fty_intTy_bits (T : FTy) : T.intTy.bits = T.fmt.width := by cases T <;> rfl
theorem fty_uintTy_bits (T : FTy) : T.uintTy.bits = T.fmt.width := by cases T <;> rfl
theorem fty_intTy_signed (T : FTy) : T.intTy.signed = true := by cases T <;> rfl
theorem fty_uintTy_signed (T : FTy) : T.uintTy.signed = false := by cases T <;> rfl



theorem isnan_IEEEFloat_eq {T : FTy} (x : FV T) : isnan_IEEEFloat x = x.isnan := by
  unfold isnan_IEEEFloat isnan_AbstractFloat eq_IEEEFloat eq_float jlEqFloat Fl.eq
  cases hx : x.isnan <;> simp [Fl.iszero, hx]

theorem isnan_callee_eq {T : FTy} (x : FV T) : isnan_callee x = x.isnan :=
  isnan_IEEEFloat_eq x

theorem isequal_IEEEFloat_eq {T : FTy} (x y : FV T) : isequal_IEEEFloat x y = Fl.isequal x y := rfl
theorem eq_IEEEFloat_eq {T : FTy} (x y : FV T) : eq_IEEEFloat x y = Fl.eq x y := rfl
theorem lt_IEEEFloat_eq {T : FTy} (x y : FV T) : lt_IEEEFloat x y = Fl.lt x y := rfl
theorem le_IEEEFloat_eq {T : FTy} (x y : FV T) : le_IEEEFloat x y = Fl.le x y := rfl

theorem iszero_float_eq {T : FTy} (x : FV T) : iszero_float x = x.iszero := by
  unfold iszero_float zero_float eq_float jlEqFloat Fl.eq
  have h0n : (Fl.zero false : FV T).isnan = false := by cases T <;> decide
  have h0z : (Fl.zero false : FV T).iszero = true := by cases T <;> decide
  have h0b : (Fl.zero false : FV T).toBits = 0 := by cases T <;> decide
  rw [h0n, h0z, h0b]
  obtain ⟨hs, hm⟩ := Fl.bits_split x
  cases hx : x.isnan
  · simp only [Bool.not_false, Bool.true_and, Bool.and_true]
    by_cases hz : x.iszero = true
    · simp [hz]
    · have hm0 : x.magnitude ≠ 0 := by simpa [Fl.iszero] using hz
      have htb0 : x.toBits ≠ 0 := by cases x.signbit <;> omega
      simp [hz, htb0]
  · simp only [Bool.not_true, Bool.false_and]
    unfold Fl.isnan at hx
    rw [Fl.expField_eq, Fl.frac_eq] at hx
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hx
    have hm0 : x.magnitude ≠ 0 := by intro h0; exact hx.2 (by simp [h0])
    simp [Fl.iszero, hm0]

theorem reinterpret_Unsigned_val {T : FTy} (x : FV T) :
    (reinterpret_Unsigned x).val = (x.toBits : Int) := by
  have hlt := x.bits.isLt
  have hbits : x.toBits = x.bits.val := rfl
  cases T
  · change (toJInt IntTy.u16 (BitVec.ofNat IntTy.u16.bits x.toBits)).val = _
    rw [toJInt_ofNat_val]; simp [FTy.fmt, half, Fmt.width] at hlt; simp [wrapInt, IntTy.signed, IntTy.bits]; omega
  · change (toJInt IntTy.u32 (BitVec.ofNat IntTy.u32.bits x.toBits)).val = _
    rw [toJInt_ofNat_val]; simp [FTy.fmt, single, Fmt.width] at hlt; simp [wrapInt, IntTy.signed, IntTy.bits]; omega
  · change (toJInt IntTy.u64 (BitVec.ofNat IntTy.u64.bits x.toBits)).val = _
    rw [toJInt_ofNat_val]; simp [FTy.fmt, double, Fmt.width] at hlt; simp [wrapInt, IntTy.signed, IntTy.bits]; omega

theorem reinterpret_Signed_val {T : FTy} (x : FV T) :
    (reinterpret_Signed x).val =
      if x.signbit then (x.magnitude : Int) - ((2 ^ (T.fmt.eb + T.fmt.sb) : Nat) : Int) else (x.magnitude : Int) := by
  obtain ⟨hsplit, hmag⟩ := Fl.bits_split x
  cases T
  · change (toJInt IntTy.i16 (BitVec.ofNat IntTy.i16.bits x.toBits)).val = _
    rw [toJInt_ofNat_val, hsplit]
    cases x.signbit <;> simp [FTy.fmt, half, wrapInt, IntTy.signed, IntTy.bits] at hmag ⊢ <;> omega
  · change (toJInt IntTy.i32 (BitVec.ofNat IntTy.i32.bits x.toBits)).val = _
    rw [toJInt_ofNat_val, hsplit]
    cases x.signbit <;> simp [FTy.fmt, single, wrapInt, IntTy.signed, IntTy.bits] at hmag ⊢ <;> omega
  · change (toJInt IntTy.i64 (BitVec.ofNat IntTy.i64.bits x.toBits)).val = _
    rw [toJInt_ofNat_val, hsplit]
    cases x.signbit <;> simp [FTy.fmt, double, wrapInt, IntTy.signed, IntTy.bits] at hmag ⊢ <;> omega

theorem signbit_float_eq {T : FTy} (x : FV T) : signbit_float x = x.signbit := by
  have hval : (reinterpret_Int_Float T.intTy x).val = (reinterpret_Signed x).val := by
    cases T <;> rfl
  have hmag := (Fl.bits_split x).2
  have hp := (reinterpret_Signed x).property
  have hmin : IntTy.i64.min ≤ T.intTy.min := by cases T <;> decide
  have hmax : T.intTy.max ≤ IntTy.i64.max := by cases T <;> decide
  have hw : wrapInt .i64 (reinterpret_Signed x).val = (reinterpret_Signed x).val :=
    wrapInt_of_inRange .i64 _ ⟨Int.le_trans hmin hp.1, Int.le_trans hp.2 hmax⟩
  have hw0 : wrapInt .i64 0 = 0 := by decide
  have hlt : int.lt (reinterpret_Int_Float T.intTy x) (int.lit .i64 0) =
      decide ((reinterpret_Signed x).val < 0) := by
    cases T <;>
      change int.slt_int (int.widenTo .i64 (reinterpret_Int_Float _ x)) (int.widenTo .i64 (int.lit .i64 0)) = _ <;>
      rw [slt_int_eq rfl] <;>
      simp only [int.widenTo, int.lit, JInt.wrap, hval, hw, hw0]
  simp only [signbit_float, int.signbit, fty_intTy_signed, ↓reduceIte, int.signbit_Integer,
    int.Generic.signbit_Integer, hlt, reinterpret_Signed_val]
  cases x.signbit <;> simp only [↓reduceIte, Bool.false_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not] <;> omega

theorem bitvec_xor_sign_typemax (w m : Nat) (hm : m < 2 ^ (w - 1)) (hw : 1 ≤ w) :
    BitVec.ofNat w (2 ^ (w - 1) + m) ^^^ BitVec.ofNat w (2 ^ (w - 1) - 1) =
      ~~~(BitVec.ofNat w m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_xor, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i (w - 1) with hlti | hgei
  · have h1 : (2 ^ (w - 1) - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hlti
    have h2 : (2 ^ (w - 1) + m).testBit i = m.testBit i := by
      have hm_mod : (2 ^ (w - 1) + m) % 2 ^ (w - 1) = m := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm]
      have htb := Nat.testBit_mod_two_pow (2 ^ (w - 1) + m) (w - 1) i
      rw [hm_mod, decide_eq_true hlti, Bool.true_and] at htb
      exact htb.symm
    rw [h1, h2]
    cases m.testBit i <;> rfl
  · have hi_eq : i = w - 1 := by omega
    subst hi_eq
    have h1 : (2 ^ (w - 1) - 1).testBit (w - 1) = false :=
      Nat.testBit_lt_two_pow (by have := Nat.two_pow_pos (w - 1); omega)
    have h2 : m.testBit (w - 1) = false := Nat.testBit_lt_two_pow hm
    have h3 : (2 ^ (w - 1) + m).testBit (w - 1) = true := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hdiv : (2 ^ (w - 1) + m) / 2 ^ (w - 1) = 1 := by
        rw [Nat.add_div_left _ (Nat.two_pow_pos (w - 1)), Nat.div_eq_of_lt hm]
      rw [hdiv]
      rfl
    simp [h1, h2, h3]

theorem fpint_val {T : FTy} (x : FV T) :
    (_fpint x).val = if x.signbit then -((x.magnitude : Int) + 1) else (x.magnitude : Int) := by
  obtain ⟨hsplit, hmag⟩ := Fl.bits_split x
  have heb_sb : T.fmt.eb + T.fmt.sb = T.intTy.bits - 1 := by cases T <;> rfl
  have hmag' : x.magnitude < 2 ^ (T.intTy.bits - 1) := heb_sb ▸ hmag
  have hzero : (int.zero (reinterpret_Signed x)).val = 0 := by cases T <;> rfl
  have hlt : int.lt_BitSigned (reinterpret_Signed x) (int.zero (reinterpret_Signed x)) = x.signbit := by
    rw [int.lt_BitSigned, slt_int_eq (fty_intTy_signed T), hzero, reinterpret_Signed_val]
    cases x.signbit <;> simp only [↓reduceIte, Bool.false_eq_true, decide_eq_true_eq,
      decide_eq_false_iff_not] <;> omega
  dsimp only [_fpint]
  rw [hlt]
  cases hs : x.signbit
  · simp only [Bool.false_eq_true, ↓reduceIte, int.ifelse, reinterpret_Signed_val, hs]
  · simp only [↓reduceIte, int.ifelse]
    have h1 : fromJInt (reinterpret_Signed x) =
        BitVec.ofNat T.intTy.bits (2 ^ (T.intTy.bits - 1) + x.magnitude) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      have hval := reinterpret_Signed_val x
      rw [hs, heb_sb] at hval
      simp only [↓reduceIte] at hval
      simp only [fromJInt, hval, BitVec.toNat_ofInt]
      cases T <;> simp only [FTy.intTy, IntTy.bits, Nat.reduceSub, Nat.reducePow] at hmag' ⊢ <;> omega
    have h2 : fromJInt (int.typemax T.intTy) = BitVec.ofNat T.intTy.bits (2 ^ (T.intTy.bits - 1) - 1) := by
      cases T <;> decide
    have hxor : fromJInt (reinterpret_Signed x) ^^^ fromJInt (int.typemax T.intTy) =
        ~~~(BitVec.ofNat T.intTy.bits x.magnitude) := by
      rw [h1, h2]
      exact bitvec_xor_sign_typemax T.intTy.bits x.magnitude hmag' (by cases T <;> decide)
    have hnot : ~~~(BitVec.ofNat T.intTy.bits x.magnitude) =
        BitVec.ofInt T.intTy.bits (-((x.magnitude : Int) + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
      cases T <;> simp only [FTy.intTy, IntTy.bits, Nat.reduceSub, Nat.reducePow] at hmag' ⊢ <;> omega
    simp only [int.bxor, int.xor_int, jlXorInt, hxor, hnot, toJInt_ofInt_val]
    have hmin : T.intTy.min = -((2 ^ (T.intTy.bits - 1) : Nat) : Int) := by cases T <;> decide
    have hmax : (0 : Int) ≤ T.intTy.max := by cases T <;> decide
    apply wrapInt_of_inRange
    rw [hmin]
    omega
theorem isless_IEEEFloat_eq {T : FTy} (a b : FV T) : isless_IEEEFloat a b = Fl.isless a b := by
  unfold isless_IEEEFloat Fl.isless
  rw [isnan_callee_eq, isnan_callee_eq]
  by_cases hnan : (a.isnan || b.isnan) = true
  · simp [hnan]
  · simp only [hnan, Bool.false_eq_true, ↓reduceIte, int.lt_BitSigned,
      slt_int_eq (fty_intTy_signed T), fpint_val]
    obtain ⟨ha, hma⟩ := Fl.bits_split a
    obtain ⟨hb, hmb⟩ := Fl.bits_split b
    rw [ha, hb]
    cases a.signbit <;> cases b.signbit <;> simp <;> omega

/-! ## Proof-internal reference lemmas for IEEE rational keys and exact conversions -/

/-- Exact mathematical comparison of a float with an integer: `-1`, `0`, `1` for less, equal,
greater; NaN gives `none`. -/
def exactOrder {f : Fmt} (x : Fl f) (y : Int) : Option Int :=
  if x.isnan then none
  else if x.isinf then some (if x.signbit then -1 else 1)
  else
    let r := x.toRat
    some (if r.1 < y * r.2 then -1 else if r.1 = y * r.2 then 0 else 1)


end JuliaLean.Proofs.base.float

namespace JuliaLean.Promotion

/-- Shape facts shared by `half`, `single` and `double`. -/
structure Fmt.Good (f : Fmt) : Prop where
  emax_eq : f.emax = 2 * f.bias + 1
  emax_succ : f.emax + 1 = 2 ^ f.eb
  bias_pos : 1 ≤ f.bias
  sb_pos : 1 ≤ f.sb
  sb_le : f.sb ≤ f.bias

theorem good_half : half.Good := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem good_single : single.Good := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem good_double : double.Good := ⟨by decide, by decide, by decide, by decide, by decide⟩

def Fmt.den (f : Fmt) : Nat := 2 ^ (f.bias + f.sb - 1)
theorem Fmt.den_pos (f : Fmt) : 0 < f.den := Nat.two_pow_pos _

end JuliaLean.Promotion

namespace JuliaLean.Proofs.base.float
open JuliaLean JuliaLean.C JuliaLean.Registry JuliaLean.base JuliaLean.base.float JuliaLean.Promotion

theorem good_fty (T : FTy) : T.fmt.Good := by
  cases T
  · exact good_half
  · exact good_single
  · exact good_double

theorem pow_mul_eq (m a b c d : Nat) (h : a + b = c + d) : m * 2 ^ a * 2 ^ b = m * 2 ^ c * 2 ^ d := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, h]

def magKey (f : Fmt) (M : Nat) : Nat :=
  (M % 2 ^ f.sb + if M / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) * 2 ^ (M / 2 ^ f.sb - 1)

theorem magKey_zero (f : Fmt) : magKey f 0 = 0 := by simp [magKey]

theorem magKey_lt (f : Fmt) (M : Nat) : magKey f M < 2 ^ f.sb * 2 ^ (M / 2 ^ f.sb) := by
  have hr := Nat.mod_lt M (Nat.two_pow_pos f.sb)
  unfold magKey
  generalize M / 2 ^ f.sb = e
  generalize M % 2 ^ f.sb = r at hr
  generalize 2 ^ f.sb = P at *
  cases e with
  | zero => simpa using hr
  | succ e =>
    have hq := Nat.two_pow_pos e
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.pow_succ]
    have h1 : (r + P) * 2 ^ e < (P + P) * 2 ^ e := (Nat.mul_lt_mul_right hq).2 (by omega)
    have h2 : (P + P) * 2 ^ e = P * (2 ^ e * 2) := by
      rw [← Nat.two_mul, Nat.mul_comm 2 P, Nat.mul_assoc, Nat.mul_comm 2]
    omega

theorem magKey_ge (f : Fmt) (M : Nat) (h : M / 2 ^ f.sb ≠ 0) :
    2 ^ f.sb * 2 ^ (M / 2 ^ f.sb - 1) ≤ magKey f M := by
  unfold magKey
  rw [ite_eq_right_iff.mpr fun h0 => absurd h0 h]
  exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

theorem magKey_strictMono (f : Fmt) {a b : Nat} (h : a < b) : magKey f a < magKey f b := by
  have hab : a / 2 ^ f.sb ≤ b / 2 ^ f.sb := Nat.div_le_div_right (Nat.le_of_lt h)
  rcases Nat.lt_or_eq_of_le hab with hlt | heq
  · have h1 := magKey_lt f a
    have h2 := magKey_ge f b (Nat.pos_iff_ne_zero.1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt))
    have h3 : 2 ^ (a / 2 ^ f.sb) ≤ 2 ^ (b / 2 ^ f.sb - 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_sub_one_of_lt hlt)
    have h4 := Nat.mul_le_mul_left (2 ^ f.sb) h3
    exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h4 h2)
  · have ha := Nat.div_add_mod a (2 ^ f.sb)
    have hb := Nat.div_add_mod b (2 ^ f.sb)
    rw [heq] at ha
    have hr : a % 2 ^ f.sb < b % 2 ^ f.sb := by omega
    unfold magKey
    rw [heq]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 (by omega)

theorem magKey_cases (f : Fmt) (a : Nat) :
    (a = 0 ∧ magKey f a = 0) ∨ (0 < a ∧ 0 < magKey f a) := by
  rcases Nat.eq_zero_or_pos a with h | h
  · exact Or.inl ⟨h, h ▸ magKey_zero f⟩
  · exact Or.inr ⟨h, magKey_zero f ▸ magKey_strictMono f h⟩

def cmpInt (a b : Int) : Int :=
  if a < b then -1 else if a = b then 0 else 1


end JuliaLean.Proofs.base.float

namespace JuliaLean.Promotion.Fl
open JuliaLean JuliaLean.Promotion JuliaLean.Proofs.base.float

variable {f g : Fmt}

def pack (neg : Bool) (B r : Nat) : Fl f :=
  ofBits ((if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r))

theorem pack_parts (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (pack neg B r : Fl f).signbit = neg ∧ (pack neg B r : Fl f).expField = B ∧
    (pack neg B r : Fl f).frac = r ∧ (pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
  have hP := Nat.two_pow_pos f.sb
  have hM : B * 2 ^ f.sb + r < 2 ^ (f.eb + f.sb) := by
    rw [Nat.pow_add]
    have : (B + 1) * 2 ^ f.sb ≤ 2 ^ f.eb * 2 ^ f.sb := Nat.mul_le_mul_right _ hB
    rw [Nat.succ_mul] at this
    omega
  have hw := Fmt.width_pow f
  have ht : (pack neg B r : Fl f).toBits =
      (if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r) := by
    unfold pack
    rw [toBits_ofBits, Nat.mod_eq_of_lt]
    rw [hw]
    cases neg <;> simp <;> omega
  have hm : (pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
    unfold magnitude
    rw [ht]
    cases neg <;> simp [Nat.mod_eq_of_lt hM]
  refine ⟨?_, ?_, ?_, hm⟩
  · unfold signbit
    rw [ht]
    cases neg <;> simp <;> omega
  · rw [expField_eq, hm, Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [frac_eq, hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

def key (x : Fl f) : Int :=
  if x.signbit then -((magKey f x.magnitude : Nat) : Int) else ((magKey f x.magnitude : Nat) : Int)

theorem lt_key {x y : Fl f} (hx : x.isnan = false) (hy : y.isnan = false) :
    Fl.lt x y = decide (x.key < y.key) := by
  obtain ⟨bx, mx⟩ := bits_split x
  obtain ⟨by', my⟩ := bits_split y
  unfold Fl.lt key iszero
  rw [hx, hy, bx, by']
  generalize x.magnitude = a at *
  generalize y.magnitude = b at *
  generalize x.signbit = s
  generalize y.signbit = t
  have pa := magKey_cases f a
  have pb := magKey_cases f b
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · subst h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem eq_key {x y : Fl f} (hx : x.isnan = false) (hy : y.isnan = false) :
    Fl.eq x y = decide (x.key = y.key) := by
  obtain ⟨bx, mx⟩ := bits_split x
  obtain ⟨by', my⟩ := bits_split y
  unfold Fl.eq key iszero
  rw [hx, hy, bx, by']
  generalize x.magnitude = a at *
  generalize y.magnitude = b at *
  generalize x.signbit = s
  generalize y.signbit = t
  have pa := magKey_cases f a
  have pb := magKey_cases f b
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · subst h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem eq_symm (x y : Fl f) : Fl.eq x y = Fl.eq y x := by
  unfold Fl.eq
  cases x.isnan <;> cases y.isnan <;> cases x.iszero <;> cases y.iszero <;> simp [BEq.comm]

theorem isnan_of_finite {x : Fl f} (h : x.isfinite = true) : x.isnan = false := by
  simp_all [isfinite, isnan]

theorem isinf_of_finite {x : Fl f} (h : x.isfinite = true) : x.isinf = false := by
  simp_all [isfinite, isinf]

theorem toRat_cases (hf : f.Good) (x : Fl f) (hx : x.isfinite = true) : ∃ m i j : Nat,
    x.toRat = ((if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int)),
      2 ^ j) ∧
    magKey f x.magnitude * 2 ^ j = m * 2 ^ i * f.den ∧ m < 2 ^ (f.sb + 1) ∧
    (m ≠ 0 → j + 1 ≤ m.log2 + i + f.bias + f.sb ∧ m.log2 + i ≤ j + f.bias) := by
  have hP := Nat.two_pow_pos f.sb
  have hb := hf.bias_pos
  have hs := hf.sb_pos
  have hE := hf.emax_eq
  have hS := hf.emax_succ
  have hM := (bits_split x).2
  have hfin : x.magnitude / 2 ^ f.sb ≠ f.emax := by
    have := hx
    simp only [isfinite, bne_iff_ne, ne_eq] at this
    rw [expField_eq] at this
    exact this
  have hdiv : x.magnitude / 2 ^ f.sb < 2 ^ f.eb := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hr := Nat.mod_lt x.magnitude hP
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold toRat magKey Fmt.den
  rw [expField_eq, frac_eq]
  simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  generalize x.signbit = s
  generalize x.magnitude / 2 ^ f.sb = e at *
  generalize x.magnitude % 2 ^ f.sb = r at *
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨r, 0, f.bias + f.sb - 1, ?_, ?_, by omega, ?_⟩
    · simp only [↓reduceIte, Nat.add_zero]
      split
      · exfalso; omega
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
    · simp
    · intro hr0
      have : r.log2 < f.sb := (Nat.log2_lt hr0).2 hr
      omega
  · have he0 : e ≠ 0 := by omega
    have hne : r + 2 ^ f.sb ≠ 0 := by omega
    have hl1 : (r + 2 ^ f.sb).log2 < f.sb + 1 := (Nat.log2_lt hne).2 (by omega)
    have hl2 : f.sb ≤ (r + 2 ^ f.sb).log2 := (Nat.le_log2 hne).2 (by omega)
    simp only [he0, ↓reduceIte]
    split
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, e - f.bias - f.sb, 0, ?_, ?_, by omega, fun _ => by omega⟩
      · have ht : ((e : Int) - f.bias - f.sb).toNat = e - f.bias - f.sb := by omega
        rw [ht]
        refine Prod.ext ?_ rfl
        cases s <;> simp [Int.natCast_mul, Int.neg_mul]
      · rw [Nat.mul_one]
        conv => lhs; rw [← Nat.mul_one ((r + 2 ^ f.sb) * 2 ^ (e - 1))]
        rw [show (1 : Nat) = 2 ^ 0 from rfl]
        exact pow_mul_eq _ _ _ _ _ (by omega)
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, 0, f.bias + f.sb - e, ?_, ?_, by omega, fun _ => by omega⟩
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
      · exact pow_mul_eq _ _ _ _ _ (by omega)

theorem toRat_key (hf : f.Good) (x : Fl f) (hx : x.isfinite = true) :
    0 < x.toRat.2 ∧ x.toRat.1 * (f.den : Int) = x.key * (x.toRat.2 : Int) := by
  obtain ⟨m, i, j, hr, hk, -, -⟩ := toRat_cases hf x hx
  rw [hr]
  refine ⟨Nat.two_pow_pos j, ?_⟩
  unfold key
  dsimp only
  cases x.signbit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul, ← Int.natCast_mul, hk]

theorem cmpInt_scale {a b c d : Int} (hc : 0 < c) (hd : 0 < d) (h : a * c = b * d) (y : Int) :
    cmpInt a (y * d) = cmpInt b (y * c) := by
  have h1 : a < y * d ↔ b < y * c := by
    rw [← Int.mul_lt_mul_right hc, h, Int.mul_right_comm y d c, Int.mul_lt_mul_right hd]
  have h2 : a = y * d ↔ b = y * c := by
    rw [← Int.mul_eq_mul_right_iff (by omega : c ≠ 0), h, Int.mul_right_comm y d c,
      Int.mul_eq_mul_right_iff (by omega : d ≠ 0)]
  unfold cmpInt
  simp only [h1, h2]

theorem exactOrder_finite (hf : f.Good) (x : Fl f) (hx : x.isfinite = true) (y : Int) :
    exactOrder x y = some (cmpInt x.key (y * f.den)) := by
  obtain ⟨h0, h1⟩ := toRat_key hf x hx
  unfold exactOrder
  simp only [isnan_of_finite hx, isinf_of_finite hx, Bool.false_eq_true, ↓reduceIte]
  rw [← cmpInt_scale (by exact_mod_cast f.den_pos) (by exact_mod_cast h0) h1 y]
  rfl

theorem exactOrder_key (hf : f.Good) (x : Fl f) (hx : x.isnan = false) (y : Int)
    (hy : y.natAbs < 2 ^ (f.bias + 1)) : exactOrder x y = some (cmpInt x.key (y * f.den)) := by
  cases hfin : x.isfinite
  · have he : x.expField = f.emax := by simpa [isfinite] using hfin
    have hr : x.frac = 0 := by simpa [isnan, he] using hx
    have hinf : x.isinf = true := by simp [isinf, he, hr]
    have hK : magKey f x.magnitude = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
      unfold magKey
      rw [← expField_eq, ← frac_eq, he, hr,
        ite_eq_right_iff.mpr (by have := hf.emax_eq; omega), Nat.zero_add]
    have hbound : y.natAbs * f.den < 2 ^ f.sb * 2 ^ (f.emax - 1) := by
      calc y.natAbs * f.den < 2 ^ (f.bias + 1) * f.den :=
            (Nat.mul_lt_mul_right f.den_pos).2 hy
        _ = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
          unfold Fmt.den
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1
          have := hf.emax_eq
          have := hf.sb_pos
          omega
    have hyD : (y * (f.den : Int)).natAbs < 2 ^ f.sb * 2 ^ (f.emax - 1) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact hbound
    unfold exactOrder key cmpInt
    rw [hK]
    simp only [hx, hinf, Bool.false_eq_true, ↓reduceIte]
    generalize y * (f.den : Int) = w at hyD
    generalize 2 ^ f.sb * 2 ^ (f.emax - 1) = K at hyD
    cases x.signbit <;> simp <;> omega
  · exact exactOrder_finite hf x hfin y

theorem log2_mul_pow (c i : Nat) (hc : c ≠ 0) : (c * 2 ^ i).log2 = c.log2 + i := by
  have hne : c * 2 ^ i ≠ 0 := Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  apply Nat.le_antisymm
  · have : c * 2 ^ i < 2 ^ (c.log2 + i + 1) := by
      rw [show c.log2 + i + 1 = (c.log2 + 1) + i by omega, Nat.pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos i)).2 Nat.lt_log2_self
    have := (Nat.log2_lt hne).2 this
    omega
  · apply (Nat.le_log2 hne).2
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hc)

theorem floorLog2Rat_pow (a j : Nat) (ha : a ≠ 0) :
    floorLog2Rat a (2 ^ j) = (a.log2 : Int) - j := by
  have h1 := Nat.log2_self_le ha
  unfold floorLog2Rat
  simp only [Nat.log2_two_pow]
  split
  · rename_i hge
    have : 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat = 2 ^ a.log2 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hc : ¬ a < 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat := by omega
    split
    · contradiction
    · rfl
  · rename_i hlt
    have : 2 ^ a.log2 * 2 ^ (-((a.log2 : Int) - j)).toNat = 2 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have := Nat.mul_le_mul_right (2 ^ (-((a.log2 : Int) - j)).toNat) h1
    have hc : ¬ a * 2 ^ (-((a.log2 : Int) - j)).toNat < 2 ^ j := by omega
    split
    · contradiction
    · rfl

theorem roundQuotient_exact (q d : Nat) (hd : 0 < d) : roundQuotient (q * d) d = q := by
  unfold roundQuotient
  rw [Nat.mul_div_cancel _ hd, Nat.mul_mod_left]
  dsimp only
  split
  · rename_i h
    simp at h <;> omega
  · rfl

theorem packRounded_normal (neg : Bool) (q : Nat) (k : Int) (h1 : 2 ^ f.sb ≤ q)
    (h2 : q < 2 ^ (f.sb + 1)) (hk2 : k + f.bias + f.sb < f.emax) :
    (packRounded neg q k : Fl f) = pack neg (k + f.bias + f.sb).toNat (q - 2 ^ f.sb) := by
  have hP := Nat.two_pow_pos f.sb
  have hq0 : (q == 0) = false := by simp; omega
  have hc : ¬ q ≥ 2 ^ (f.sb + 1) := by omega
  have he : ¬ k + f.bias + f.sb ≥ (f.emax : Int) := by omega
  have hm : ¬ q < 2 ^ f.sb := by omega
  unfold packRounded pack
  simp only [hq0, hc, he, hm, Bool.false_eq_true, ↓reduceIte]

theorem sig_bounds (c : Nat) (hc : c ≠ 0) (hc1 : c < 2 ^ (f.sb + 1)) :
    c.log2 ≤ f.sb ∧ 2 ^ f.sb ≤ c * 2 ^ (f.sb - c.log2) ∧
    c * 2 ^ (f.sb - c.log2) < 2 ^ (f.sb + 1) := by
  have hlc : c.log2 ≤ f.sb := by have := (Nat.log2_lt hc).2 hc1; omega
  refine ⟨hlc, ?_, ?_⟩
  · calc 2 ^ f.sb = 2 ^ c.log2 * 2 ^ (f.sb - c.log2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.log2_self_le hc)
  · calc c * 2 ^ (f.sb - c.log2) < 2 ^ (c.log2 + 1) * 2 ^ (f.sb - c.log2) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 Nat.lt_log2_self
      _ = 2 ^ (f.sb + 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega

theorem roundRat_normal (hf : f.Good) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f) =
      pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := sig_bounds (f := f) c hc hc1
  have ha : n.natAbs ≠ 0 := by
    rw [hn]
    exact Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  have hn0 : (n == 0) = false := by simp; omega
  have hd : (2 ^ j == 0) = false := by simp
  have hE : floorLog2Rat n.natAbs (2 ^ j) = ((c.log2 + i : Nat) : Int) - j := by
    rw [floorLog2Rat_pow _ _ ha, hn, log2_mul_pow c i hc]
  have hb := hf.bias_pos
  have hem := hf.emax_eq
  have hs := hf.sb_pos
  unfold roundRat
  simp only [hd, hn0, Bool.false_eq_true, ↓reduceIte]
  generalize floorLog2Rat n.natAbs (2 ^ j) = e at hE
  split
  · exfalso; omega
  split
  · exfalso; omega
  have hk : max (e - f.sb) (1 - (f.bias : Int) - f.sb) = e - f.sb := by omega
  rw [hk]
  have hpack : ∀ q : Nat, q = c * 2 ^ (f.sb - c.log2) →
      (packRounded (decide (n < 0)) q (e - f.sb) : Fl f) =
        pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
    intro q hq
    subst hq
    rw [packRounded_normal _ _ _ hq1 hq2 (by omega)]
    congr 1
    omega
  apply hpack
  by_cases hk0 : e - (f.sb : Int) ≥ 0
  · rw [ite_eq_left_iff.mpr fun h => absurd hk0 h]
    dsimp only
    have h1 : n.natAbs = c * 2 ^ (f.sb - c.log2) * (2 ^ j * 2 ^ (e - f.sb).toNat) := by
      rw [hn, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
      congr 2
      omega
    rw [h1, roundQuotient_exact _ _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))]
  · rw [ite_eq_right_iff.mpr fun h => absurd h hk0]
    dsimp only
    have h1 : n.natAbs * 2 ^ (-(e - f.sb)).toNat = c * 2 ^ (f.sb - c.log2) * 2 ^ j := by
      rw [hn]
      exact pow_mul_eq _ _ _ _ _ (by omega)
    rw [h1, roundQuotient_exact _ _ (Nat.two_pow_pos _)]

theorem pack_key (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (pack neg B r : Fl f).key = if neg then
      -(((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int)
      else (((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int) := by
  obtain ⟨hs, he, hfr, -⟩ := pack_parts (f := f) neg B r hB hr
  unfold key magKey
  rw [← expField_eq, ← frac_eq, hs, he, hfr]

theorem roundRat_key (hf : f.Good) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f).isfinite = true ∧
    (roundRat n (2 ^ j) z : Fl f).key * ((2 ^ j : Nat) : Int) = n * (f.den : Int) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := sig_bounds (f := f) c hc hc1
  have hem := hf.emax_eq
  have hS := hf.emax_succ
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  have hB : c.log2 + i + f.bias - j < 2 ^ f.eb := by omega
  have hr : c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb < 2 ^ f.sb := by
    generalize c * 2 ^ (f.sb - c.log2) = q at hq1 hq2 ⊢
    omega
  rw [roundRat_normal hf n c i j z hn hc0 hc1 hlo hhi]
  obtain ⟨-, he, -, -⟩ := pack_parts (f := f) (decide (n < 0)) _ _ hB hr
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  have hnz : (if c.log2 + i + f.bias - j = 0 then 0 else 2 ^ f.sb) = 2 ^ f.sb :=
    ite_eq_right_iff.mpr (by omega)
  rw [pack_key _ _ _ hB hr, hnz, Nat.sub_add_cancel hq1]
  have hpow : c * 2 ^ (f.sb - c.log2) * 2 ^ (c.log2 + i + f.bias - j - 1) * 2 ^ j =
      c * 2 ^ i * f.den := by
    unfold Fmt.den
    simp only [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rcases Int.lt_or_le n 0 with hneg | hpos
  · have hn' : n = -((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_true hneg, ↓reduceIte]
    rw [hn', Int.neg_mul, Int.neg_mul, ← Int.natCast_mul, ← Int.natCast_mul, hpow]
  · have hn' : n = ((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_false (Int.not_lt.2 hpos), Bool.false_eq_true, ↓reduceIte]
    rw [hn', ← Int.natCast_mul, ← Int.natCast_mul, hpow]

theorem zero_spec (hf : f.Good) (s : Bool) :
    (zero s : Fl f).isfinite = true ∧ (zero s : Fl f).key = 0 := by
  have hz : (zero s : Fl f) = pack s 0 0 := by simp [zero, pack]
  have hS := hf.emax_succ
  have hE := hf.emax_eq
  obtain ⟨-, he, -, -⟩ := pack_parts (f := f) s 0 0 (by omega) (Nat.two_pow_pos _)
  rw [hz]
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  rw [pack_key _ _ _ (by omega) (Nat.two_pow_pos _)]
  cases s <;> simp

theorem ofInt_key (hf : f.Good) (n : Int) (hn : n.natAbs < 2 ^ (f.sb + 1)) :
    (ofInt n : Fl f).isfinite = true ∧ (ofInt n : Fl f).key = n * (f.den : Int) := by
  by_cases h0 : n = 0
  · subst h0
    have : (ofInt 0 : Fl f) = zero false := by simp [ofInt, roundRat]
    rw [this]
    obtain ⟨h1, h2⟩ := zero_spec hf false
    exact ⟨h1, by rw [h2]; simp⟩
  · have hc : n.natAbs ≠ 0 := by omega
    have hlc := (sig_bounds (f := f) n.natAbs hc hn).1
    have := hf.sb_le
    have := hf.emax_eq
    have := hf.bias_pos
    obtain ⟨h1, h2⟩ := roundRat_key hf n n.natAbs 0 0 false (by simp) (by omega) hn
      (by omega) (by omega)
    refine ⟨h1, ?_⟩
    simpa [ofInt] using h2

theorem ofInt_exact (hf : f.Good) (n : Int) (hn : n.natAbs < 2 ^ (f.sb + 1)) :
    (ofInt n : Fl f).isfinite = true ∧ 0 < (ofInt n : Fl f).toRat.2 ∧
    (ofInt n : Fl f).toRat.1 = n * ((ofInt n : Fl f).toRat.2 : Int) := by
  obtain ⟨hfin, hk⟩ := ofInt_key hf n hn
  obtain ⟨hd, hr⟩ := toRat_key hf (ofInt n) hfin
  have hden : (0 : Int) < f.den := by exact_mod_cast f.den_pos
  refine ⟨hfin, hd, ?_⟩
  apply Int.eq_of_mul_eq_mul_right (by omega : (f.den : Int) ≠ 0)
  rw [hr, hk, Int.mul_right_comm]

theorem convert_exactOrder (hf : f.Good) (hg : g.Good) (hne : (g == f) = false)
    (hsb : f.sb ≤ g.sb) (hbias : f.bias + f.sb ≤ g.bias) (x : Fl f) (y : Int) :
    exactOrder (convert x : Fl g) y = exactOrder x y := by
  have hgS := hg.emax_succ
  have hgE := hg.emax_eq
  have hfE := hf.emax_eq
  have hPg := Nat.two_pow_pos g.sb
  unfold convert
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hn : x.isnan
  · cases hi : x.isinf
    · have hfin : x.isfinite = true := by
        simp_all [isnan, isinf, isfinite]
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨m, i, j, hr, hk, hm, hrange⟩ := toRat_cases hf x hfin
      have hkey := (toRat_key hf x hfin).2
      rw [exactOrder_finite hf x hfin]
      rw [hr]
      dsimp only
      rw [hr] at hkey
      dsimp only at hkey
      by_cases hm0 : m = 0
      · subst hm0
        have hz : (roundRat (if x.signbit then -((0 * 2 ^ i : Nat) : Int)
            else ((0 * 2 ^ i : Nat) : Int)) (2 ^ j) x.signbit : Fl g) = zero x.signbit := by
          cases x.signbit <;> simp [roundRat]
        rw [hz]
        obtain ⟨hz1, hz2⟩ := zero_spec hg x.signbit
        rw [exactOrder_finite hg _ hz1, hz2]
        have hkx : x.key = 0 := by
          have h2 : ((2 ^ j : Nat) : Int) ≠ 0 := by have := Nat.two_pow_pos j; omega
          have h3 : x.key * ((2 ^ j : Nat) : Int) = 0 := by
            rw [← hkey]
            cases x.signbit <;> simp
          exact (Int.mul_eq_zero.1 h3).resolve_right h2
        rw [hkx]
        congr 1
        unfold cmpInt
        have hDf : (0 : Int) < f.den := by exact_mod_cast f.den_pos
        have hDg : (0 : Int) < g.den := by exact_mod_cast g.den_pos
        rcases Int.lt_trichotomy y 0 with hy | hy | hy
        · have h1 : y * (g.den : Int) < 0 := Int.mul_neg_of_neg_of_pos hy hDg
          have h2 : y * (f.den : Int) < 0 := Int.mul_neg_of_neg_of_pos hy hDf
          simp only [show ¬ (0 : Int) < y * g.den by omega, show ¬ (0 : Int) < y * f.den by omega,
            show ¬ (0 : Int) = y * g.den by omega, show ¬ (0 : Int) = y * f.den by omega,
            ↓reduceIte]
        · subst hy
          simp
        · have h1 : 0 < y * (g.den : Int) := Int.mul_pos hy hDg
          have h2 : 0 < y * (f.den : Int) := Int.mul_pos hy hDf
          simp only [h1, h2, ↓reduceIte]
      · obtain ⟨hlo, hhi⟩ := hrange hm0
        have hn' : (if x.signbit then -((m * 2 ^ i : Nat) : Int)
            else ((m * 2 ^ i : Nat) : Int)).natAbs = m * 2 ^ i := by
          cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg,
            Int.natAbs_natCast]
        have hm1 : m < 2 ^ (g.sb + 1) :=
          Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
        obtain ⟨h1, h2⟩ := roundRat_key (f := g) hg _ m i j x.signbit hn' (by omega) hm1
          (by omega) (by omega)
        rw [exactOrder_finite hg _ h1]
        congr 1
        have hj : (0 : Int) < ((2 ^ j : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos j
        have hDf : (0 : Int) < f.den := by exact_mod_cast f.den_pos
        have hDg : (0 : Int) < g.den := by exact_mod_cast g.den_pos
        generalize (if x.signbit then -((m * 2 ^ i : Nat) : Int)
            else ((m * 2 ^ i : Nat) : Int)) = N at h2 hkey
        generalize (roundRat N (2 ^ j) x.signbit : Fl g).key = K at h2
        have hscale : K * f.den = x.key * g.den := by
          apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hj)
          calc K * f.den * ((2 ^ j : Nat) : Int) = K * ((2 ^ j : Nat) : Int) * f.den := by
                rw [Int.mul_right_comm]
            _ = N * g.den * f.den := by rw [h2]
            _ = N * f.den * g.den := by rw [Int.mul_right_comm]
            _ = x.key * ((2 ^ j : Nat) : Int) * g.den := by rw [hkey]
            _ = x.key * g.den * ((2 ^ j : Nat) : Int) := by rw [Int.mul_right_comm]
        exact cmpInt_scale hDf hDg hscale y
    · have hinf : (inf x.signbit : Fl g) = pack x.signbit g.emax 0 := by simp [inf, pack]
      obtain ⟨hs, he, hfr, -⟩ := pack_parts (f := g) x.signbit g.emax 0 (by omega) hPg
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hinf]
      unfold exactOrder
      have hpn : (pack x.signbit g.emax 0 : Fl g).isnan = false := by
        unfold isnan; rw [he, hfr]; simp
      have hpi : (pack x.signbit g.emax 0 : Fl g).isinf = true := by
        unfold isinf; rw [he, hfr]; simp
      simp only [hpn, hpi, hs, hn, hi, Bool.false_eq_true, ↓reduceIte]
  · have hfr : x.frac < 2 ^ f.sb := by rw [frac_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpay : x.frac * 2 ^ (g.sb - f.sb) < 2 ^ g.sb := by
      calc x.frac * 2 ^ (g.sb - f.sb) < 2 ^ f.sb * 2 ^ (g.sb - f.sb) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hfr
        _ = 2 ^ g.sb := by rw [← Nat.pow_add]; congr 1; omega
    have hhalf : 2 ^ (g.sb - 1) < 2 ^ g.sb :=
      Nat.pow_lt_pow_right (by decide) (by have := hg.sb_pos; omega)
    have hL : Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1)) < 2 ^ g.sb :=
      Nat.or_lt_two_pow hpay hhalf
    have hpk : (ofBits ((if x.signbit then 2 ^ (g.eb + g.sb) else 0) + g.emax * 2 ^ g.sb +
        Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) : Fl g) =
        pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) := by
      unfold pack; rw [Nat.add_assoc]
    obtain ⟨-, he, hfr', -⟩ := pack_parts (f := g) x.signbit g.emax _ (by omega) hL
    simp only [↓reduceIte, ite_eq_left_iff.mpr fun h => absurd hsb h]
    rw [hpk]
    unfold exactOrder
    have hpn : (pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isnan = true := by
      unfold isnan; rw [he, hfr']; simp
    simp only [hpn, hn, ↓reduceIte]

theorem compare_core (hg : g.Good) (a z : Fl g) (y : Int) (hz : z.isfinite = true)
    (hkz : z.key = y * (g.den : Int)) (hy : y.natAbs < 2 ^ (g.bias + 1)) :
    Fl.eq a z = (exactOrder a y == some 0) ∧ Fl.lt a z = (exactOrder a y == some (-1)) ∧
    Fl.le a z = (exactOrder a y == some (-1) || exactOrder a y == some 0) ∧
    Fl.eq z a = (exactOrder a y == some 0) ∧
    Fl.lt z a = (exactOrder a y == some 1) ∧
    Fl.le z a = (exactOrder a y == some 1 || exactOrder a y == some 0) := by
  have hzn := isnan_of_finite hz
  cases ha : a.isnan
  · rw [exactOrder_key hg a ha y hy]
    simp only [Fl.le, lt_key ha hzn, lt_key hzn ha, eq_key ha hzn, eq_key hzn ha, hkz]
    unfold cmpInt
    generalize a.key = k
    generalize y * (g.den : Int) = w
    by_cases h1 : k < w <;> by_cases h2 : k = w <;> simp [h1, h2] <;> omega
  · have hnone : exactOrder a y = none := by simp [exactOrder, ha]
    simp [hnone, Fl.le, Fl.lt, Fl.eq, ha, hzn]

theorem cmp_promote (hg : g.Good) (x : Fl g) (y : Int) (h1 : y.natAbs < 2 ^ (g.sb + 1))
    (h2 : y.natAbs < 2 ^ (g.bias + 1)) :
    Fl.eq x (ofInt y) = (exactOrder x y == some 0) ∧
    Fl.lt x (ofInt y) = (exactOrder x y == some (-1)) ∧
    Fl.le x (ofInt y) = (exactOrder x y == some (-1) || exactOrder x y == some 0) ∧
    Fl.eq (ofInt y) x = (exactOrder x y == some 0) ∧
    Fl.lt (ofInt y) x = (exactOrder x y == some 1) ∧
    Fl.le (ofInt y) x = (exactOrder x y == some 1 || exactOrder x y == some 0) := by
  obtain ⟨hz, hk⟩ := ofInt_key hg y h1
  exact compare_core hg x _ y hz hk h2

theorem cmp_via (hf : f.Good) (hg : g.Good) (hne : (g == f) = false) (hsb : f.sb ≤ g.sb)
    (hbias : f.bias + f.sb ≤ g.bias) (x : Fl f) (y : Int) (h1 : y.natAbs < 2 ^ (g.sb + 1))
    (h2 : y.natAbs < 2 ^ (g.bias + 1)) :
    Fl.eq (convert x : Fl g) (ofInt y) = (exactOrder x y == some 0) ∧
    Fl.lt (convert x : Fl g) (ofInt y) = (exactOrder x y == some (-1)) ∧
    Fl.le (convert x : Fl g) (ofInt y) = (exactOrder x y == some (-1) || exactOrder x y == some 0) ∧
    Fl.eq (ofInt y) (convert x : Fl g) = (exactOrder x y == some 0) ∧
    Fl.lt (ofInt y) (convert x : Fl g) = (exactOrder x y == some 1) ∧
    Fl.le (ofInt y) (convert x : Fl g) = (exactOrder x y == some 1 || exactOrder x y == some 0) := by
  rw [← convert_exactOrder hf hg hne hsb hbias x y]
  exact cmp_promote hg _ y h1 h2

end JuliaLean.Promotion.Fl

namespace JuliaLean.Proofs.base.float
open JuliaLean JuliaLean.C JuliaLean.Registry JuliaLean.base JuliaLean.base.float JuliaLean.Promotion

theorem exactOrder_cases {f : Fmt} (x : Fl f) (hx : x.isnan = false) (y : Int) :
    exactOrder x y = some (-1) ∨ exactOrder x y = some 0 ∨ exactOrder x y = some 1 := by
  unfold exactOrder
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  split
  · split <;> simp
  · split
    · simp
    · split <;> simp

theorem exactOrder_sign (T : FTy) (x : FV T) (hx : x.isnan = false) (y : Int) :
    (x.signbit = true → 0 ≤ y → exactOrder x y ≠ some 1) ∧
    (x.signbit = false → y < 0 → exactOrder x y = some 1) := by
  have hf := good_fty T
  cases hfin : x.isfinite
  · have he : x.expField = T.fmt.emax := by simpa [Fl.isfinite] using hfin
    have hr : x.frac = 0 := by simpa [Fl.isnan, he] using hx
    have hinf : x.isinf = true := by simp [Fl.isinf, he, hr]
    unfold exactOrder
    simp only [hx, hinf, Bool.false_eq_true, ↓reduceIte]
    cases x.signbit <;> simp
  · obtain ⟨m, i, j, hr, -, -, -⟩ := Fl.toRat_cases hf x hfin
    have hP : (0 : Int) < ((2 ^ j : Nat) : Int) := by have := Nat.two_pow_pos j; omega
    unfold exactOrder
    simp only [Fl.isnan_of_finite hfin, Fl.isinf_of_finite hfin, Bool.false_eq_true,
      ↓reduceIte]
    rw [hr]
    dsimp only
    generalize ((2 ^ j : Nat) : Int) = P at hP ⊢
    generalize hA : ((m * 2 ^ i : Nat) : Int) = A
    have hA0 : 0 ≤ A := by omega
    constructor
    · intro hs hy
      have : 0 ≤ y * P := Int.mul_nonneg hy (Int.le_of_lt hP)
      rw [hs]
      simp only [↓reduceIte]
      split
      · simp
      · split
        · simp
        · exfalso; omega
    · intro hs hy
      have : y * P < 0 := Int.mul_neg_of_neg_of_pos hy hP
      rw [hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · exfalso; omega
      · split
        · exfalso; omega
        · rfl

theorem okOf_eq {ε α : Type} {r : Except ε α} {h : ∀ e, r ≠ .error e} {a : α} (hr : r = .ok a) :
    int.okOf r h = a := by
  subst hr; rfl

theorem floatOfInt_eq_ofInt {t : IntTy} (ht : t.bits ≤ 64) (T : FTy) (y : JInt t) :
    floatOfInt T y = Fl.ofInt y.val := by
  cases t <;> try (exfalso; revert ht; decide)
  all_goals
    first
    | (simp only [floatOfInt, float_BitSigned64, sitofp, jlSitofp]
       rw [fromJInt_toInt y rfl])
    | (simp only [floatOfInt, float_BitUnsigned64, uitofp, jlUitofp]
       rw [fromJInt_toNat_unsigned y rfl])

theorem convertFloat_eq (T : FTy) {S : FTy} (x : FV S) :
    convertFloat T x = Fl.convert x := by
  cases T <;> cases S
  · simp [convertFloat, Fl.convert, Fl.ofBits_toBits]
  · simp only [convertFloat, Float16_Float32, fptrunc]
    exact okOf_eq rfl
  · simp only [convertFloat, Float16_Float64, fptrunc]
    exact okOf_eq rfl
  · simp only [convertFloat, Float32_Float16, fpext]
    exact okOf_eq rfl
  · simp [convertFloat, Fl.convert, Fl.ofBits_toBits]
  · simp only [convertFloat, Float32_Float64, fptrunc]
    exact okOf_eq rfl
  · simp only [convertFloat, Float64_Float16, fpext]
    exact okOf_eq rfl
  · simp only [convertFloat, Float64_Float32, fpext]
    exact okOf_eq rfl
  · simp [convertFloat, Fl.convert, Fl.ofBits_toBits]

theorem natAbs_le_bits {t : IntTy} (y : JInt t) : y.val.natAbs ≤ 2 ^ t.bits := by
  obtain ⟨v, h1, h2⟩ := y
  cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h1 h2 ⊢ <;> omega

theorem natAbs_lt {t : IntTy} (y : JInt t) {k : Nat} (h : 2 ^ t.bits < 2 ^ k) :
    y.val.natAbs < 2 ^ k :=
  Nat.lt_of_le_of_lt (natAbs_le_bits y) h

/-! ## Properties 1 & 2: `isless` and `isequal` total order (`float-isless-partition`, `float-isless-transitive`) -/

/-- `isless` and `isequal` partition every pair of `IEEEFloat` values of type `T` into a strict
total order on `isequal` classes, with `-0.0` strictly before `+0.0` and all `NaN` bit patterns
in one `isequal` class at the top (`base/float.jl:619-634`). -/
def IslessPartition : Prop := ∀ (T : FTy) (x y : FV T),
  (isless_IEEEFloat x y = true ∨ isless_IEEEFloat y x = true ∨ isequal_IEEEFloat x y = true) ∧
  (isequal_IEEEFloat x y = true ↔ isless_IEEEFloat x y = false ∧ isless_IEEEFloat y x = false)

theorem islessPartition_proven : IslessPartition := by
  intro T x y
  rw [isless_IEEEFloat_eq, isless_IEEEFloat_eq, isequal_IEEEFloat_eq]
  have hnan : x.toBits = y.toBits → x.isnan = y.isnan := by
    intro h; simp only [Fl.isnan, Fl.expField, Fl.frac, h]
  have hsign : x.toBits = y.toBits → x.signbit = y.signbit := by
    intro h; simp only [Fl.signbit, h]
  cases hx : x.isnan <;> cases hy : y.isnan <;>
    cases sx : x.signbit <;> cases sy : y.signbit <;>
    simp only [Fl.isless, Fl.isequal, hx, hy, sx, sy] <;>
    simp_all <;> omega

/-- `isless` is transitive across all bit patterns of every `IEEEFloat` format `T`, including
`NaN` payloads and signed zeros (`base/float.jl:621-634`). -/
def IslessTransitive : Prop := ∀ (T : FTy) (x y z : FV T),
  isless_IEEEFloat x y = true → isless_IEEEFloat y z = true → isless_IEEEFloat x z = true

theorem islessTransitive_proven : IslessTransitive := by
  intro T x y z hxy hyz
  rw [isless_IEEEFloat_eq] at hxy hyz ⊢
  cases hx : x.isnan <;> cases hy : y.isnan <;> cases hz : z.isnan <;>
    cases sx : x.signbit <;> cases sy : y.signbit <;> cases sz : z.signbit <;>
    simp only [Fl.isless, hx, hy, hz, sx, sy, sz] at hxy hyz ⊢ <;>
    simp_all <;> omega

/-! ## Property 3: `Base.uabs` (`intarith-division-uabs-typemin`) -/

/-- `Base.uabs(x)` returns the exact non-negative magnitude `|x|` as an unsigned integer of the
same width for every fixed-width integer `x`, avoiding signed overflow at `typemin(T)`
(`base/float.jl:225-236`). -/
def UabsExact : Prop := ∀ (t : IntTy) (x : JInt t),
  (uabs x).val = (x.val.natAbs : Int) ∧
  (t.signed = true → (uabs_BitSigned x).val = if x.val < 0 then -x.val else x.val) ∧
  (t.signed = false → uabs_Integer int.abs x = x)

theorem uabsExact_proven : UabsExact := by
  intro t x
  have hx := x.property
  have hflipsign : ∀ (s : IntTy), s.signed = true → ∀ a : JInt s,
      (int.abs_Signed a).val = wrapInt s (if a.val < 0 then -a.val else a.val) := by
    intro s hs a
    simp only [int.abs_Signed, int.Generic.abs_Signed, int.flipsign_same, int.flipsign_int, jlFlipsignInt, fromJInt_toInt a hs]
    split
    · simp only [fromJInt]; rw [← BitVec.ofInt_neg, toJInt_ofInt_val]
    · rw [fromJInt, toJInt_ofInt_val, wrapInt_val]
  have hunsigned : ∀ (s : IntTy) (a : JInt s), (int.unsigned a).val = wrapInt s.toUnsigned a.val := by
    intro s a
    cases s
    · exact bitcast_val .u8 a rfl
    · exact bitcast_val .u16 a rfl
    · exact bitcast_val .u32 a rfl
    · exact bitcast_val .u64 a rfl
    · exact bitcast_val .u128 a rfl
    · exact (wrapInt_val a).symm
    · exact (wrapInt_val a).symm
    · exact (wrapInt_val a).symm
    · exact (wrapInt_val a).symm
    · exact (wrapInt_val a).symm
  refine ⟨?_, ?_, ?_⟩
  · unfold uabs uabs_BitSigned uabs_Integer int.abs
    by_cases hs : t.signed = true
    · simp only [hs, ↓reduceIte, hunsigned, hflipsign t hs x]
      cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;>
        split <;> omega
    · have hs' : t.signed = false := Bool.eq_false_iff.mpr hs
      simp only [hs', Bool.false_eq_true, ↓reduceIte, int.abs_Unsigned, int.Generic.abs_Unsigned]
      cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned, IntTy.min, IntTy.max, int.remT, int.rem_same] <;>
        omega
  · intro hs
    simp only [uabs_BitSigned, int.abs, hs, ↓reduceIte, hunsigned, hflipsign t hs x]
    cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;>
      split <;> omega
  · intro hs
    simp [uabs_Integer, int.abs, hs, int.abs_Unsigned, int.Generic.abs_Unsigned]

/-! ## Property 4: Exact conversion of small integers to `IEEEFloat` (`float-small-integer-exact`) -/

/-- Every integer of a fixed-width integer type whose bit width does not exceed the target format's
significand precision (all 8-bit integers in `Float16`/`Float32`/`Float64`, all 16-bit integers in
`Float32`/`Float64`, and all 32-bit integers in `Float64`), as well as `Bool`, converts via
`sitofp`/`uitofp` to a finite float whose rational value is exactly that integer
(`base/float.jl:241-256,350`). -/
def SmallIntegerExact : Prop :=
  (∀ (T : FTy) (t : IntTy) (x : JInt t), t.bits ≤ T.fmt.sb →
    let f := floatOfInt T x
    f.isfinite = true ∧ 0 < f.toRat.2 ∧ f.toRat.1 = x.val * (f.toRat.2 : Int)) ∧
  (∀ (t : IntTy) (x : JInt t), t.bits ≤ 8 →
    Float16_Integer (floatOfInt .f32) Float16_Float32 x = floatOfInt .f16 x) ∧
  (∀ (t : IntTy) (x : JInt t), AbstractFloat_BitInteger x = floatOfInt .f64 x) ∧
  (∀ (T : FTy) (b : Bool),
    float_Bool T b = (if b then one_float T else zero_float T) ∧
    AbstractFloat_Bool b = float_Bool .f64 b)

theorem smallIntegerExact_proven : SmallIntegerExact := by
  refine ⟨?_, ?_, fun _ _ => rfl, ?_⟩
  · intro T t x hbits
    have ht64 : t.bits ≤ 64 := by cases T <;> simp [FTy.fmt, half, single, double] at hbits <;> omega
    rw [floatOfInt_eq_ofInt ht64 T x]
    apply Fl.ofInt_exact (good_fty T) x.val
    have hpow : 2 ^ t.bits < 2 ^ (T.fmt.sb + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    exact natAbs_lt x hpow
  · intro t x ht8
    have hfin256 : ∀ (s : Bool) (k : Fin 256),
        let t0 := if s then IntTy.i8 else IntTy.u8
        let y := JInt.wrap t0 (k.val : Int)
        Float16_Integer (floatOfInt .f32) Float16_Float32 y = floatOfInt .f16 y := by decide
    have hk : (x.val % 256).toNat < 256 := by omega
    cases t <;> try (exfalso; revert ht8; decide)
    · have hx : x = JInt.wrap .i8 ((⟨(x.val % 256).toNat, hk⟩ : Fin 256).val : Int) := by
        apply jint_eq; have := x.property
        simp [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at this ⊢; omega
      rw [hx]; exact hfin256 true ⟨(x.val % 256).toNat, hk⟩
    · have hx : x = JInt.wrap .u8 ((⟨(x.val % 256).toNat, hk⟩ : Fin 256).val : Int) := by
        apply jint_eq; have := x.property
        simp [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at this ⊢; omega
      rw [hx]; exact hfin256 false ⟨(x.val % 256).toNat, hk⟩
  · intro T b
    cases T <;> cases b <;> decide

/-! ## Property 5: Exact mixed float/integer comparisons (`promotion-mixed-compare-small`) -/

/-- `==`, `<` and `<=` between `Float16`/`Float32`/`Float64` and every integer type of at most 32
bits, in both argument orders, compare the exact mathematical values; `NaN` compares `false`
(`base/float.jl:678-690`). -/
def MixedCompareSmall : Prop := ∀ (T : FTy) (t : IntTy) (x : FV T) (y : JInt t), t.bits ≤ 32 →
  eq_FI x y = (exactOrder x y.val == some 0) ∧
  lt_FI x y = (exactOrder x y.val == some (-1)) ∧
  le_FI x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
  eq_IF y x = (exactOrder x y.val == some 0) ∧
  lt_IF y x = (exactOrder x y.val == some 1) ∧
  le_IF y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)

theorem mixedCompareSmall_proven : MixedCompareSmall := by
  intro T t x y ht
  have hf32 : Float32_Float16 = (Fl.convert : FV .f16 → FV .f32) := by
    funext a; exact convertFloat_eq .f32 a
  have hf64_16 : Float64_Float16 = (Fl.convert : FV .f16 → FV .f64) := by
    funext a; exact convertFloat_eq .f64 a
  have hfi : ∀ (S : FTy), floatOfInt S y = Fl.ofInt y.val :=
    fun S => floatOfInt_eq_ofInt (Nat.le_trans ht (by decide)) S y
  cases T <;> cases t <;> try (exfalso; revert ht; decide)
  all_goals
    simp only [eq_FI, lt_FI, le_FI, eq_IF, lt_IF, le_IF,
      op_Float16_Int16, op_Int16_Float16, op_SmallFloat_Int32, op_Int32_SmallFloat,
      eq_IEEEFloat_eq, lt_IEEEFloat_eq, le_IEEEFloat_eq,
      hf32, convertFloat_eq, hfi]
  · exact Fl.cmp_promote good_half x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_half good_single (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_half good_double (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_half x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_half good_single (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_half good_double (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_single good_double (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_single good_double (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_double x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_double x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_double x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_double x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_double x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_double x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))


/-! ## Proof-internal lemmas for `unsafe_trunc`, `round(Ti, x, RoundToZero)`, and `Ti(x)` -/

namespace TruncProofs

def mantissaNat {T : FTy} (x : FV T) : Nat :=
  x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb

def numerator {T : FTy} (x : FV T) : Nat :=
  mantissaNat x * 2 ^ (x.expField - (T.fmt.bias + T.fmt.sb))

def denominator {T : FTy} (x : FV T) : Nat :=
  2 ^ (if x.expField = 0 then T.fmt.bias + T.fmt.sb - 1 else T.fmt.bias + T.fmt.sb - x.expField)

def quotient {T : FTy} (x : FV T) : Nat := numerator x / denominator x

theorem rat_parts {T : FTy} (x : FV T) (hfin : x.isfinite = true) :
    x.toRat = (if x.signbit then -(numerator x : Int) else (numerator x : Int), denominator x) := by
  unfold Fl.toRat numerator mantissaNat denominator
  simp only [hfin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rcases Nat.eq_zero_or_pos x.expField with hz | hpos
  · rw [hz]
    simp only [↓reduceIte, Nat.add_zero]
    have hlt : (1 : Int) - (T.fmt.bias : Int) - T.fmt.sb < 0 := by cases T <;> decide
    rw [ite_eq_right_iff.mpr fun h => absurd h (Int.not_le.mpr hlt)]
    have hsub : 0 - (T.fmt.bias + T.fmt.sb) = 0 := Nat.zero_sub _
    have hpow : (-(1 - (T.fmt.bias : Int) - T.fmt.sb)).toNat = T.fmt.bias + T.fmt.sb - 1 := by
      cases T <;> decide
    rw [hsub, hpow, Nat.pow_zero, Nat.mul_one]
  · have hnz : x.expField ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    simp only [hnz, ↓reduceIte]
    by_cases hge : ((x.expField : Int) - T.fmt.bias - T.fmt.sb) ≥ 0
    · rw [ite_eq_left_iff.mpr fun h => absurd hge h]
      have h1 : ((x.expField : Int) - T.fmt.bias - T.fmt.sb).toNat =
          x.expField - (T.fmt.bias + T.fmt.sb) := by omega
      have h2 : T.fmt.bias + T.fmt.sb - x.expField = 0 := by omega
      rw [h1, h2, Nat.pow_zero]
      refine Prod.ext ?_ rfl
      cases x.signbit <;> simp [Int.natCast_mul, Int.neg_mul]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hge]
      have h1 : x.expField - (T.fmt.bias + T.fmt.sb) = 0 := by omega
      have h2 : (-((x.expField : Int) - T.fmt.bias - T.fmt.sb)).toNat =
          T.fmt.bias + T.fmt.sb - x.expField := by omega
      rw [h1, h2, Nat.pow_zero, Nat.mul_one]

theorem truncVal_parts {T : FTy} (x : FV T) (hfin : x.isfinite = true) :
    x.truncVal = if x.signbit then -(quotient x : Int) else (quotient x : Int) := by
  unfold Fl.truncVal
  rw [rat_parts x hfin]
  cases x.signbit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_tdiv, ← Int.ofNat_tdiv, quotient]

theorem quotient_small {T : FTy} (x : FV T) (he : x.expField < T.fmt.bias) :
    quotient x = 0 := by
  have hf : x.frac < 2 ^ T.fmt.sb := by rw [Fl.frac_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hshift : x.expField - (T.fmt.bias + T.fmt.sb) = 0 := by omega
  have hpow : 2 ^ (T.fmt.sb + 1) = 2 * 2 ^ T.fmt.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  have hm : mantissaNat x < 2 ^ (T.fmt.sb + 1) := by
    unfold mantissaNat; split <;> omega
  have hd : 2 ^ (T.fmt.sb + 1) ≤ denominator x := by
    unfold denominator
    apply Nat.pow_le_pow_right (by decide)
    have : 2 ≤ T.fmt.bias := by cases T <;> decide
    split <;> omega
  unfold quotient numerator
  rw [hshift, Nat.pow_zero, Nat.mul_one]
  exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hm hd)

theorem quotient_binade {T : FTy} (x : FV T) (he : T.fmt.bias ≤ x.expField) :
    2 ^ (x.expField - T.fmt.bias) ≤ quotient x ∧
      quotient x < 2 ^ (x.expField - T.fmt.bias + 1) := by
  have hf : x.frac < 2 ^ T.fmt.sb := by rw [Fl.frac_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbias : 1 ≤ T.fmt.bias := (good_fty T).bias_pos
  have hz : x.expField ≠ 0 := by omega
  have hpow : 2 ^ (T.fmt.sb + 1) = 2 * 2 ^ T.fmt.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  have hm1 : 2 ^ T.fmt.sb ≤ mantissaNat x := by simp [mantissaNat, hz]
  have hm2 : mantissaNat x < 2 ^ (T.fmt.sb + 1) := by simp only [mantissaNat, hz, ↓reduceIte]; omega
  by_cases hs : x.expField ≤ T.fmt.bias + T.fmt.sb
  · have hd : 0 < 2 ^ (T.fmt.bias + T.fmt.sb - x.expField) := Nat.two_pow_pos _
    have h1 : 2 ^ (x.expField - T.fmt.bias) * 2 ^ (T.fmt.bias + T.fmt.sb - x.expField) = 2 ^ T.fmt.sb := by
      rw [← Nat.pow_add]; congr 1; omega
    have h2 : 2 ^ (x.expField - T.fmt.bias + 1) * 2 ^ (T.fmt.bias + T.fmt.sb - x.expField) = 2 ^ (T.fmt.sb + 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    simp only [quotient, numerator, denominator, hz, ↓reduceIte,
      Nat.sub_eq_zero_of_le hs, Nat.pow_zero, Nat.mul_one]
    exact ⟨(Nat.le_div_iff_mul_le hd).mpr (by rw [h1]; exact hm1),
      (Nat.div_lt_iff_lt_mul hd).mpr (by rw [h2]; exact hm2)⟩
  · have h1 : 2 ^ T.fmt.sb * 2 ^ (x.expField - (T.fmt.bias + T.fmt.sb)) = 2 ^ (x.expField - T.fmt.bias) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h2 : 2 ^ (T.fmt.sb + 1) * 2 ^ (x.expField - (T.fmt.bias + T.fmt.sb)) = 2 ^ (x.expField - T.fmt.bias + 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    simp only [quotient, numerator, denominator, hz, ↓reduceIte,
      Nat.sub_eq_zero_of_le (by omega : T.fmt.bias + T.fmt.sb ≤ x.expField),
      Nat.pow_zero, Nat.div_one]
    exact ⟨by rw [← h1]; exact Nat.mul_le_mul_right _ hm1,
      by rw [← h2]; exact Nat.mul_lt_mul_of_pos_right hm2 (Nat.two_pow_pos _)⟩

theorem quotient_lt_pow {T : FTy} (x : FV T) (b : Nat) :
    quotient x < 2 ^ b ↔ x.expField < T.fmt.bias + b := by
  by_cases he : x.expField < T.fmt.bias
  · rw [quotient_small x he]
    exact iff_of_true (Nat.two_pow_pos _) (by omega)
  · obtain ⟨h1, h2⟩ := quotient_binade x (by omega)
    constructor
    · intro h
      have hp : 2 ^ (x.expField - T.fmt.bias) < 2 ^ b := by omega
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
      omega
    · intro h
      have hp : 2 ^ (x.expField - T.fmt.bias + 1) ≤ 2 ^ b :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega

theorem mag_decomp {T : FTy} (x : FV T) :
    x.magnitude = x.expField * 2 ^ T.fmt.sb + x.frac ∧ x.frac < 2 ^ T.fmt.sb := by
  rw [Fl.expField_eq, Fl.frac_eq]
  have h := Nat.div_add_mod x.magnitude (2 ^ T.fmt.sb)
  exact ⟨by rw [Nat.mul_comm]; exact h.symm, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem quotient_lt_pow_bits {T : FTy} (x : FV T) (b : Nat) :
    quotient x < 2 ^ b ↔ x.magnitude < (T.fmt.bias + b) * 2 ^ T.fmt.sb := by
  rw [quotient_lt_pow]
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hP := Nat.two_pow_pos T.fmt.sb
  constructor
  · intro h
    have : (x.expField + 1) * 2 ^ T.fmt.sb ≤ (T.fmt.bias + b) * 2 ^ T.fmt.sb :=
      Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega
  · intro h
    rcases Nat.lt_or_ge x.expField (T.fmt.bias + b) with hlt | hge
    · exact hlt
    · have : (T.fmt.bias + b) * 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb :=
        Nat.mul_le_mul_right _ hge
      omega

theorem quotient_zero_bits {T : FTy} (x : FV T) :
    quotient x = 0 ↔ x.magnitude < T.fmt.bias * 2 ^ T.fmt.sb := by
  have h := quotient_lt_pow_bits x 0
  simp only [Nat.pow_zero, Nat.add_zero] at h
  omega

theorem quotient_le_pow_small {T : FTy} (x : FV T) (b : Nat) (hb : b < T.fmt.sb) :
    quotient x ≤ 2 ^ b ↔
      x.magnitude < (T.fmt.bias + b) * 2 ^ T.fmt.sb + 2 ^ (T.fmt.sb - b) := by
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hbias : 1 ≤ T.fmt.bias := (good_fty T).bias_pos
  by_cases hc : x.expField = T.fmt.bias + b
  · have hz : x.expField ≠ 0 := by omega
    have hs : x.expField - (T.fmt.bias + T.fmt.sb) = 0 := by omega
    have hd : T.fmt.bias + T.fmt.sb - x.expField = T.fmt.sb - b := by omega
    have hp : 2 ^ b * 2 ^ (T.fmt.sb - b) = 2 ^ T.fmt.sb := by
      rw [← Nat.pow_add]; congr 1; omega
    have hd0 := Nat.two_pow_pos (T.fmt.sb - b)
    have hn : quotient x ≤ 2 ^ b ↔ x.frac < 2 ^ (T.fmt.sb - b) := by
      simp only [quotient, numerator, denominator, mantissaNat, hz, ↓reduceIte,
        hs, hd, Nat.pow_zero, Nat.mul_one]
      rw [Nat.lt_succ_iff.symm, Nat.div_lt_iff_lt_mul hd0, Nat.succ_mul, hp]
      omega
    rw [hn, hm, hc]; omega
  · have hl := quotient_lt_pow_bits x b
    by_cases hlow : x.expField < T.fmt.bias + b
    · have hq := (quotient_lt_pow x b).mpr hlow
      have hr := hl.mp hq
      exact iff_of_true (Nat.le_of_lt hq) (Nat.lt_of_lt_of_le hr (Nat.le_add_right _ _))
    · obtain ⟨h1, -⟩ := quotient_binade x (by omega)
      have hp : 2 ^ b < 2 ^ (x.expField - T.fmt.bias) :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      have hd : 2 ^ (T.fmt.sb - b) ≤ 2 ^ T.fmt.sb :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hr : (T.fmt.bias + b + 1) * 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at hr
      exact iff_of_false (by omega) (by omega)

theorem quotient_le_pow_big {T : FTy} (x : FV T) (b : Nat) (hb : T.fmt.sb ≤ b) :
    quotient x ≤ 2 ^ b ↔ x.magnitude ≤ (T.fmt.bias + b) * 2 ^ T.fmt.sb := by
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hbias : 1 ≤ T.fmt.bias := (good_fty T).bias_pos
  by_cases hc : x.expField = T.fmt.bias + b
  · have hz : x.expField ≠ 0 := by omega
    have hs : T.fmt.bias + T.fmt.sb - x.expField = 0 := by omega
    have hd : x.expField - (T.fmt.bias + T.fmt.sb) = b - T.fmt.sb := by omega
    have hp : 2 ^ T.fmt.sb * 2 ^ (b - T.fmt.sb) = 2 ^ b := by
      rw [← Nat.pow_add]; congr 1; omega
    have hd0 := Nat.two_pow_pos (b - T.fmt.sb)
    have hn : quotient x ≤ 2 ^ b ↔ x.frac = 0 := by
      simp only [quotient, numerator, denominator, mantissaNat, hz, ↓reduceIte,
        hs, hd, Nat.pow_zero, Nat.div_one, Nat.add_mul, hp]
      constructor
      · intro h
        have hmul : x.frac * 2 ^ (b - T.fmt.sb) = 0 := by omega
        exact (Nat.mul_eq_zero.mp hmul).resolve_right (by omega)
      · intro h; simp [h]
    rw [hn, hm, hc]; omega
  · have hl := quotient_lt_pow_bits x b
    by_cases hlow : x.expField < T.fmt.bias + b
    · have hq := (quotient_lt_pow x b).mpr hlow
      have hr := hl.mp hq
      exact iff_of_true (by omega) (by omega)
    · obtain ⟨h1, -⟩ := quotient_binade x (by omega)
      have hp : 2 ^ b < 2 ^ (x.expField - T.fmt.bias) :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      have hr : (T.fmt.bias + b + 1) * 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb :=
        Nat.mul_le_mul_right _ (by omega)
      have hP := Nat.two_pow_pos T.fmt.sb
      rw [Nat.succ_mul] at hr
      exact iff_of_false (by omega) (by omega)

theorem signed_mod_zero (a d : Nat) (s : Bool) (hd : 0 < d) :
    ((if s then -(a : Int) else (a : Int)) % (d : Int) == 0) = (a % d == 0) := by
  have hr := Nat.mod_lt a hd
  apply Bool.eq_iff_iff.mpr
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, ← Int.natCast_emod,
      Int.natCast_eq_zero]
  · simp only [↓reduceIte, beq_iff_eq, Int.neg_emod, ← Int.natCast_emod]
    omega

theorem integral_parts {T : FTy} (x : FV T) (hfin : x.isfinite = true) :
    x.toRat.1 % (x.toRat.2 : Int) = 0 ↔ numerator x % denominator x = 0 := by
  rw [rat_parts x hfin]
  have h := Bool.eq_iff_iff.mp
    (signed_mod_zero (numerator x) (denominator x) x.signbit (Nat.two_pow_pos _))
  simpa only [beq_iff_eq] using h

theorem numerator_exact {T : FTy} (x : FV T) (hi : numerator x % denominator x = 0) :
    numerator x = quotient x * denominator x := by
  have h := Nat.mod_add_div (numerator x) (denominator x)
  rw [hi, Nat.zero_add] at h
  simpa only [quotient, Nat.mul_comm] using h.symm

theorem quotient_zero_integral {T : FTy} (x : FV T) (hi : numerator x % denominator x = 0) :
    quotient x = 0 ↔ x.magnitude = 0 := by
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hP := Nat.two_pow_pos T.fmt.sb
  constructor
  · intro hq
    have hn := numerator_exact x hi
    rw [hq, Nat.zero_mul] at hn
    have hm0 : mantissaNat x = 0 :=
      (Nat.mul_eq_zero.mp hn).resolve_right (Nat.ne_of_gt (Nat.two_pow_pos _))
    unfold mantissaNat at hm0
    have he : x.expField = 0 := by
      by_cases h : x.expField = 0
      · exact h
      · simp only [h, ↓reduceIte] at hm0; omega
    simp only [he, ↓reduceIte, Nat.add_zero] at hm0
    rw [hm, he, hm0]; simp
  · intro h
    apply (quotient_zero_bits x).mpr
    have : 1 ≤ T.fmt.bias := (good_fty T).bias_pos
    have : 1 * 2 ^ T.fmt.sb ≤ T.fmt.bias * 2 ^ T.fmt.sb := Nat.mul_le_mul_right _ this
    omega

theorem quotient_le_pow_integral {T : FTy} (x : FV T) (b : Nat)
    (hi : numerator x % denominator x = 0) :
    quotient x ≤ 2 ^ b ↔ x.magnitude ≤ (T.fmt.bias + b) * 2 ^ T.fmt.sb := by
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hbias : 1 ≤ T.fmt.bias := (good_fty T).bias_pos
  have hP := Nat.two_pow_pos T.fmt.sb
  have hlt := quotient_lt_pow_bits x b
  constructor
  · intro hq
    by_cases hstrict : quotient x < 2 ^ b
    · have := hlt.mp hstrict; omega
    have hqe : quotient x = 2 ^ b := by omega
    have hnext := quotient_lt_pow x (b + 1)
    have hprev := quotient_lt_pow x b
    have hp : 2 ^ b < 2 ^ (b + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
    have he : x.expField = T.fmt.bias + b := by
      have := hnext.mp (by omega)
      omega
    have hz : x.expField ≠ 0 := by omega
    have hn := numerator_exact x hi
    have hfrac : x.frac = 0 := by
      by_cases hs : b < T.fmt.sb
      · have hp' : 2 ^ b * 2 ^ (T.fmt.sb - b) = 2 ^ T.fmt.sb := by
          rw [← Nat.pow_add]; congr 1; omega
        simp only [numerator, mantissaNat, denominator, hz, ↓reduceIte,
          Nat.sub_eq_zero_of_le (by omega : x.expField ≤ T.fmt.bias + T.fmt.sb),
          Nat.pow_zero, Nat.mul_one, hqe,
          show T.fmt.bias + T.fmt.sb - x.expField = T.fmt.sb - b by omega, hp'] at hn
        omega
      · have hp' : 2 ^ T.fmt.sb * 2 ^ (b - T.fmt.sb) = 2 ^ b := by
          rw [← Nat.pow_add]; congr 1; omega
        simp only [numerator, mantissaNat, denominator, hz, ↓reduceIte,
          Nat.sub_eq_zero_of_le (by omega : T.fmt.bias + T.fmt.sb ≤ x.expField),
          Nat.pow_zero, Nat.mul_one, hqe,
          show x.expField - (T.fmt.bias + T.fmt.sb) = b - T.fmt.sb by omega,
          Nat.add_mul, hp'] at hn
        have hmul : x.frac * 2 ^ (b - T.fmt.sb) = 0 := by omega
        exact (Nat.mul_eq_zero.mp hmul).resolve_right (Nat.ne_of_gt (Nat.two_pow_pos _))
    rw [hm, he, hfrac]; omega
  · intro h
    by_cases hs : b < T.fmt.sb
    · apply (quotient_le_pow_small x b hs).mpr
      have := Nat.two_pow_pos (T.fmt.sb - b)
      omega
    · exact (quotient_le_pow_big x b (by omega)).mpr h


theorem bitvec_and_mask (w a b : Nat) :
    BitVec.ofNat w a &&& BitVec.ofNat w (2 ^ b - 1) = BitVec.ofNat w (a % 2 ^ b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_and, hi, decide_true, Bool.true_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem bitvec_or_pow (w r b : Nat) (hr : r < 2 ^ b) :
    BitVec.ofNat w r ||| BitVec.ofNat w (2 ^ b) = BitVec.ofNat w (r + 2 ^ b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_or, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i b with hlt | hge
  · have h1 : (2 ^ b).testBit i = false := by rw [Nat.testBit_two_pow]; simp [Nat.ne_of_gt hlt]
    have hm_mod : (r + 2 ^ b) % 2 ^ b = r := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    have htb := Nat.testBit_mod_two_pow (r + 2 ^ b) b i
    rw [hm_mod, decide_eq_true hlt, Bool.true_and] at htb
    rw [h1, ← htb, Bool.or_false]
  · rcases Nat.eq_or_lt_of_le hge with h_eq | hgt
    · rw [← h_eq]
      have h1 : (2 ^ b).testBit b = true := by rw [Nat.testBit_two_pow]; simp
      have h2 : (r + 2 ^ b).testBit b = true := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rw [Nat.add_div_right _ (Nat.two_pow_pos b), Nat.div_eq_of_lt hr]; rfl
      rw [h1, h2, Bool.or_true]
    · have hpow : r + 2 ^ b < 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
      have hle : 2 ^ (b + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega),
        Nat.testBit_lt_two_pow (by omega)]; rfl

def pattern {t : IntTy} (x : JInt t) : Nat := (x.val % ((2 ^ t.bits : Nat) : Int)).toNat

theorem pattern_cast {t : IntTy} (x : JInt t) : (pattern x : Int) = x.val % ((2 ^ t.bits : Nat) : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := two_pow_pos_int t.bits; omega))

theorem pattern_lt {t : IntTy} (x : JInt t) : pattern x < 2 ^ t.bits := by
  have h := pattern_cast x
  have h2 := Int.emod_lt_of_pos x.val (two_pow_pos_int t.bits)
  generalize 2 ^ t.bits = M at *
  omega

theorem pattern_fromJInt {t : IntTy} (x : JInt t) : pattern x = (fromJInt x).toNat := by
  have h1 := pattern_cast x
  have h2 := fromJInt_toNat x
  omega

theorem pattern_toJInt (t : IntTy) (b : BitVec t.bits) : pattern (toJInt t b) = b.toNat := by
  have hc := pattern_cast (toJInt t b)
  rw [toJInt_val, wrapInt_emod_self] at hc
  have hb := b.isLt
  have hm : (b.toNat : Int) % ((2 ^ t.bits : Nat) : Int) = b.toNat :=
    Int.emod_eq_of_lt (by omega) (by omega)
  split at hc
  · rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_emod, hm] at hc; omega
  · rw [hm] at hc; omega

theorem val_eq_wrap_pattern {t : IntTy} (x : JInt t) : x.val = wrapInt t (pattern x) := by
  rw [← wrapInt_val x]
  apply wrapInt_congr
  rw [pattern_cast, Int.emod_emod]

theorem val_bounds {t : IntTy} (x : JInt t) :
    -((2 ^ t.bits : Nat) : Int) < x.val ∧ x.val < ((2 ^ t.bits : Nat) : Int) := by
  have hx := x.property
  cases t <;> simp_all [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem pattern_of_nonneg {t : IntTy} (x : JInt t) (h : 0 ≤ x.val) : pattern x = x.val.toNat := by
  have hc := pattern_cast x
  rw [Int.emod_eq_of_lt h (val_bounds x).2] at hc
  omega

theorem val_of_unsigned_pattern {t : IntTy} (h : t.signed = false) (x : JInt t) : (pattern x : Int) = x.val := by
  have hx := x.property
  have h0 : 0 ≤ x.val := by
    have := hx.1
    cases t <;> simp_all [IntTy.signed, IntTy.min]
  rw [pattern_of_nonneg x h0]
  exact Int.toNat_of_nonneg h0

theorem val_of_signed_small_pattern {t : IntTy} (x : JInt t) (h : pattern x < 2 ^ (t.bits - 1)) :
    x.val = (pattern x : Int) := by
  rw [val_eq_wrap_pattern x]
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits, Nat.reduceSub, Nat.reducePow] at h ⊢ <;> omega

theorem pattern_band {t : IntTy} (x y : JInt t) : pattern (int.band x y) = pattern x &&& pattern y := by
  simp only [int.band, int.and_int, jlAndInt, pattern_toJInt, BitVec.toNat_and, ← pattern_fromJInt]

theorem pattern_bor {t : IntTy} (x y : JInt t) : pattern (int.bor x y) = pattern x ||| pattern y := by
  simp only [int.bor, int.or_int, jlOrInt, pattern_toJInt, BitVec.toNat_or, ← pattern_fromJInt]

theorem pattern_bxor {t : IntTy} (x y : JInt t) : pattern (int.bxor x y) = pattern x ^^^ pattern y := by
  simp only [int.bxor, int.xor_int, jlXorInt, pattern_toJInt, BitVec.toNat_xor, ← pattern_fromJInt]

theorem sub_int_val {t : IntTy} (x y : JInt t) : (int.sub x y).val = wrapInt t (x.val - y.val) := by
  simp only [int.sub, int.sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, toJInt_ofInt_val, Int.sub_eq_add_neg]

theorem add_int_val {t : IntTy} (x y : JInt t) : (int.add x y).val = wrapInt t (x.val + y.val) := by
  simp only [int.add, int.add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add, toJInt_ofInt_val]

theorem neg_int_val {t : IntTy} (x : JInt t) : (int.neg x).val = wrapInt t (-x.val) := by
  simp only [int.neg, int.neg_int, jlNegInt, fromJInt]
  rw [← BitVec.ofInt_neg, toJInt_ofInt_val]

theorem rem_BitInteger_Type_val (to : IntTy) {fr : IntTy} (x : JInt fr) :
    (int.rem_BitInteger_Type to x).val = wrapInt to x.val := by
  unfold int.rem_BitInteger_Type
  split
  · rename_i h
    have hlt := int.bits_lt_of_sizeofT_lt h
    unfold int.Generated.rem_trunc int.trunc_int
    rw [okOf_eq (a := BitVec.ofInt to.bits ((fromJInt x).toNat : Int))
      (by simp [jlTruncInt, Nat.not_le.mpr hlt, pure, Except.pure])]
    rw [toJInt_ofInt_val]
    apply wrapInt_congr
    rw [fromJInt_toNat]
    have hd : ((2 ^ to.bits : Nat) : Int) ∣ ((2 ^ fr.bits : Nat) : Int) :=
      Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (Nat.le_of_lt hlt))
    exact Int.emod_emod_of_dvd _ hd
  · split
    · rename_i h h2
      have hlt := int.bits_lt_of_sizeofT_lt h2
      split
      · rename_i hs
        unfold int.Generated.rem_sext int.sext_int
        rw [okOf_eq (a := BitVec.ofInt to.bits (fromJInt x).toInt)
          (by simp [jlSextInt, Nat.not_le.mpr hlt, pure, Except.pure])]
        rw [toJInt_ofInt_val, fromJInt_toInt x (by simpa using hs)]
      · rfl
    · rename_i h h2
      exact bitcast_val to x (int.bits_eq_of_sizeofT h h2)

theorem remT_val (to : IntTy) {fr : IntTy} (x : JInt fr) : (int.remT to x).val = wrapInt to x.val := by
  unfold int.remT
  split
  · rename_i h; subst h; simp [int.rem_same, wrapInt_val]
  · exact rem_BitInteger_Type_val to x

theorem pattern_of_cong {t : IntTy} (x : JInt t) (z : Int) (h : x.val = wrapInt t z) :
    pattern x = (z % ((2 ^ t.bits : Nat) : Int)).toNat := by
  unfold pattern
  rw [h, wrapInt_emod_self]

theorem pattern_remT_same_bits (to : IntTy) {fr : IntTy} (x : JInt fr) (hb : to.bits = fr.bits) :
    pattern (int.remT to x) = pattern x := by
  rw [pattern_of_cong _ x.val (remT_val to x), hb]
  rfl

theorem unsigned_val {t : IntTy} (x : JInt t) : (int.unsigned x).val = wrapInt t.toUnsigned x.val := by
  unfold int.unsigned
  split
  · exact bitcast_val _ x _
  · exact remT_val _ x

theorem toUnsigned_bits (t : IntTy) : t.toUnsigned.bits = t.bits := by cases t <;> rfl

theorem pattern_unsigned {t : IntTy} (x : JInt t) : pattern (int.unsigned x) = pattern x := by
  rw [pattern_of_cong _ x.val (unsigned_val x), toUnsigned_bits]; rfl

theorem pattern_shl_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (int.shl_int x y) = pattern x * 2 ^ pattern y % 2 ^ t.bits := by
  simp only [int.shl_int, jlShlInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 h) _)).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]

theorem pattern_lshr_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (int.lshr_int x y) = pattern x / 2 ^ pattern y := by
  simp only [int.lshr_int, jlLshrInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (pattern_lt x) (Nat.pow_le_pow_right (by decide) h))).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (pattern_lt x))

theorem le_zero_eq (y : JInt .i64) : int.le_BitSigned (int.lit .i64 0) y = decide (0 ≤ y.val) := by
  have h0 : (int.lit IntTy.i64 0).val = 0 := by decide
  rw [int.le_BitSigned, sle_int_eq rfl, h0]

theorem pattern_unsigned_count (y : JInt .i64) (h : 0 ≤ y.val) : pattern (int.unsigned y) = y.val.toNat := by
  rw [pattern_unsigned, pattern_of_nonneg y h]

theorem pattern_shl_Int {t : IntTy} (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (int.shl_Int x c) = pattern x * 2 ^ c.val.toNat % 2 ^ t.bits := by
  simp only [int.shl_Int, int.ifelse, le_zero_eq, decide_eq_true_iff, h, ↓reduceIte,
    int.shl_BitInteger_BitUnsigned, pattern_shl_int, pattern_unsigned_count c h]

theorem pattern_shr_Int_unsigned {t : IntTy} (hu : t.signed = false) (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (int.shr_Int x c) = pattern x / 2 ^ c.val.toNat := by
  simp only [int.shr_Int, int.ifelse, le_zero_eq, decide_eq_true_iff, h, ↓reduceIte,
    int.shrU, hu, Bool.false_eq_true, int.shr_BitUnsigned_BitUnsigned,
    pattern_lshr_int, pattern_unsigned_count c h]

theorem nat_and_mask (a b : Nat) : a &&& (2 ^ b - 1) = a % 2 ^ b := by
  have h := congrArg BitVec.toNat (bitvec_and_mask (max a.log2 b + 2) a b)
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at h
  have hlt1 : (a &&& (2 ^ b - 1)) < 2 ^ (max a.log2 b + 2) := by
    have : a &&& (2 ^ b - 1) ≤ 2 ^ b - 1 := Nat.and_le_right
    have : 2 ^ b < 2 ^ (max a.log2 b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hlt2 : a % 2 ^ b < 2 ^ (max a.log2 b + 2) := by
    have := Nat.mod_lt a (Nat.two_pow_pos b)
    have : 2 ^ b < 2 ^ (max a.log2 b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have h1 : (a % 2 ^ (max a.log2 b + 2)) &&& ((2 ^ b - 1) % 2 ^ (max a.log2 b + 2)) =
      a &&& (2 ^ b - 1) := by
    have ha : a < 2 ^ (max a.log2 b + 2) := by
      by_cases h0 : a = 0
      · subst h0; exact Nat.two_pow_pos _
      · calc a < 2 ^ (a.log2 + 1) := Nat.lt_log2_self
          _ ≤ 2 ^ (max a.log2 b + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    have hb : 2 ^ b - 1 < 2 ^ (max a.log2 b + 2) := by
      have : 2 ^ b < 2 ^ (max a.log2 b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [h1, Nat.mod_eq_of_lt hlt2] at h
  exact h

theorem nat_or_pow (r b : Nat) (hr : r < 2 ^ b) : (r ||| 2 ^ b) = r + 2 ^ b := by
  have h := congrArg BitVec.toNat (bitvec_or_pow (b + 2) r b hr)
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat] at h
  have hp : 2 ^ b < 2 ^ (b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsum : r + 2 ^ b < 2 ^ (b + 2) := by
    calc r + 2 ^ b < 2 ^ b + 2 ^ b := by omega
      _ = 2 ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_two]
      _ < 2 ^ (b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hsum] at h
  exact h

theorem pattern_reinterpret_Unsigned {T : FTy} (x : FV T) :
    pattern (reinterpret_Unsigned x) = x.toBits := by
  have hv := reinterpret_Unsigned_val x
  have hlt := x.bits.isLt
  have hbits : x.toBits = x.bits.val := rfl
  rw [← val_of_unsigned_pattern (fty_uintTy_signed T)] at hv
  omega

theorem unsafe_trunc_u128_f64_val (x : FV .f64) (he : x.expField < 1023 + 128) :
    (unsafe_trunc_UInt128_Float64 x).val = (quotient x : Int) := by
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hexp : x.expField < 2048 := Nat.mod_lt _ (by decide)
  have hpat_xu0 : pattern (reinterpret_Unsigned_Float64 x) = x.toBits :=
    pattern_reinterpret_Unsigned (T := .f64) x
  have hpat_exp : pattern (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float64 x) (int.lit .i64 52))) (int.lit .i64 0x07ff)) = x.expField := by
    rw [pattern_band, pattern_remT_same_bits .i64 (int.shr_Int (reinterpret_Unsigned_Float64 x) (int.lit .i64 52)) rfl,
      pattern_shr_Int_unsigned rfl _ _ (by decide), hpat_xu0]
    have h1 : (int.lit .i64 52).val.toNat = 52 := rfl
    have h2 : pattern (int.lit .i64 0x07ff) = 2 ^ 11 - 1 := rfl
    rw [h1, h2, nat_and_mask]
    rfl
  have hexp_val : (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float64 x) (int.lit .i64 52))) (int.lit .i64 0x07ff)).val = (x.expField : Int) := by
    have hlt_exp : pattern (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float64 x) (int.lit .i64 52))) (int.lit .i64 0x07ff)) < 2 ^ (IntTy.i64.bits - 1) := by
      rw [hpat_exp]; dsimp [IntTy.bits]; omega
    rw [val_of_signed_small_pattern _ hlt_exp, hpat_exp]
  have hk_val : (int.sub (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float64 x) (int.lit .i64 52))) (int.lit .i64 0x07ff)) (int.lit .i64 1075)).val =
      (x.expField : Int) - 1075 := by
    rw [sub_int_val, hexp_val]
    have : (int.lit .i64 1075).val = 1075 := rfl
    rw [this]
    simp [wrapInt, IntTy.signed, IntTy.bits]; omega
  have hpat_mant : pattern (int.bor (int.band (reinterpret_Unsigned_Float64 x) (int.lit .u64 0x000f_ffff_ffff_ffff)) (int.lit .u64 0x0010_0000_0000_0000)) =
      x.frac + 2 ^ 52 := by
    rw [pattern_bor, pattern_band, hpat_xu0]
    have h1 : pattern (int.lit .u64 0x000f_ffff_ffff_ffff) = 2 ^ 52 - 1 := rfl
    have h2 : pattern (int.lit .u64 0x0010_0000_0000_0000) = 2 ^ 52 := rfl
    rw [h1, h2, nat_and_mask, show x.toBits % 2 ^ 52 = x.frac from rfl, nat_or_pow _ 52 hf]
  dsimp only [unsafe_trunc_UInt128_Float64]
  generalize hk_def : int.sub (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float64 x) (int.lit .i64 52))) (int.lit .i64 0x07ff)) (int.lit .i64 1075) = k at hk_val
  generalize hxu_def : int.bor (int.band (reinterpret_Unsigned_Float64 x) (int.lit .u64 0x000f_ffff_ffff_ffff)) (int.lit .u64 0x0010_0000_0000_0000) = xu at hpat_mant
  have hle_k : int.le_BitSigned k (int.lit .i64 0) = decide (x.expField ≤ 1075) := by
    rw [int.le_BitSigned, sle_int_eq rfl, hk_val]
    have : (int.lit .i64 0).val = 0 := by decide
    rw [this]; apply decide_eq_decide.mpr; omega
  rw [hle_k]
  by_cases hle : x.expField ≤ 1075
  · simp only [decide_eq_true hle, ↓reduceIte]
    have hneg_k : (int.neg k).val = (1075 - x.expField : Nat) := by
      rw [neg_int_val, hk_val]
      simp [wrapInt, IntTy.signed, IntTy.bits]; omega
    have hpat_shr : pattern (int.shr_Int xu (int.neg k)) = (x.frac + 2 ^ 52) / 2 ^ (1075 - x.expField) := by
      rw [pattern_shr_Int_unsigned rfl xu (int.neg k) (by rw [hneg_k]; omega), hpat_mant, hneg_k]
      rfl
    have hval_shr : (int.shr_Int xu (int.neg k)).val = ((x.frac + 2 ^ 52) / 2 ^ (1075 - x.expField) : Nat) := by
      rw [← val_of_unsigned_pattern rfl, hpat_shr]
    have hwiden : (int.widenTo .u128 (int.shr_Int xu (int.neg k))).val =
        ((x.frac + 2 ^ 52) / 2 ^ (1075 - x.expField) : Nat) := by
      simp only [int.widenTo, int.lit, JInt.wrap, hval_shr]
      have hdiv_lt : (x.frac + 2 ^ 52) / 2 ^ (1075 - x.expField) < 2 ^ 53 := by
        have := Nat.div_le_self (x.frac + 2 ^ 52) (2 ^ (1075 - x.expField))
        omega
      apply wrapInt_of_inRange
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true, ↓reduceIte]
      omega
    rw [hwiden]
    by_cases hlt1023 : x.expField < 1023
    · rw [quotient_small x hlt1023]
      have hdiv0 : (x.frac + 2 ^ 52) / 2 ^ (1075 - x.expField) = 0 := by
        apply Nat.div_eq_of_lt
        calc x.frac + 2 ^ 52 < 2 ^ 53 := by omega
          _ ≤ 2 ^ (1075 - x.expField) := Nat.pow_le_pow_right (by decide) (by omega)
      simp [hdiv0]
    · have hnz : x.expField ≠ 0 := by omega
      have hq : quotient x = (x.frac + 2 ^ 52) / 2 ^ (1075 - x.expField) := by
        have hb1 : FTy.f64.fmt.bias + FTy.f64.fmt.sb = 1075 := rfl
        have hb2 : 2 ^ FTy.f64.fmt.sb = 2 ^ 52 := rfl
        simp only [quotient, numerator, denominator, mantissaNat, hnz, ↓reduceIte, hb1, hb2,
          Nat.sub_eq_zero_of_le hle, Nat.pow_zero, Nat.mul_one]
      rw [hq]
  · simp only [decide_eq_false hle, Bool.false_eq_true, ↓reduceIte]
    have hgt : 1075 < x.expField := by omega
    have hnz : x.expField ≠ 0 := by omega
    have hxu_val : xu.val = ((x.frac + 2 ^ 52 : Nat) : Int) := by
      rw [← val_of_unsigned_pattern rfl, hpat_mant]
    have hwiden_pat' : pattern (int.widenTo .u128 xu) = x.frac + 2 ^ 52 := by
      rw [pattern_of_cong _ xu.val rfl, hxu_val]
      have : ((x.frac + 2 ^ 52 : Nat) : Int) % ((2 ^ 128 : Nat) : Int) = (x.frac + 2 ^ 52 : Nat) := by
        apply Int.emod_eq_of_lt (by omega) (by omega)
      change (((x.frac + 2 ^ 52 : Nat) : Int) % ((2 ^ 128 : Nat) : Int)).toNat = _
      rw [this]; rfl
    have hk_toNat : k.val.toNat = x.expField - 1075 := by omega
    have hprod_lt : (x.frac + 2 ^ 52) * 2 ^ (x.expField - 1075) < 2 ^ 128 := by
      calc (x.frac + 2 ^ 52) * 2 ^ (x.expField - 1075)
          < 2 ^ 53 * 2 ^ (x.expField - 1075) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 (by omega)
        _ = 2 ^ (53 + (x.expField - 1075)) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
    have hpat_shl : pattern (int.shl_Int (int.widenTo .u128 xu) k) =
        (x.frac + 2 ^ 52) * 2 ^ (x.expField - 1075) := by
      rw [pattern_shl_Int _ _ (by omega), hwiden_pat', hk_toNat]
      exact Nat.mod_eq_of_lt hprod_lt
    rw [← val_of_unsigned_pattern rfl, hpat_shl]
    have hq : quotient x = (x.frac + 2 ^ 52) * 2 ^ (x.expField - 1075) := by
      have hb1 : FTy.f64.fmt.bias + FTy.f64.fmt.sb = 1075 := rfl
      have hb2 : 2 ^ FTy.f64.fmt.sb = 2 ^ 52 := rfl
      simp only [quotient, numerator, denominator, mantissaNat, hnz, ↓reduceIte, hb1, hb2,
        Nat.sub_eq_zero_of_le (by omega : 1075 ≤ x.expField), Nat.pow_zero, Nat.div_one]
    rw [hq]

theorem toJInt_fromJInt {t : IntTy} (x : JInt t) : toJInt t (fromJInt x) = x :=
  jint_eq (by rw [fromJInt, toJInt_ofInt_val, wrapInt_val])

theorem flipsign_int_val {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    (int.flipsign_int x y).val = wrapInt t (if y.val < 0 then -x.val else x.val) := by
  simp only [int.flipsign_int, jlFlipsignInt, fromJInt_toInt y h]
  split
  · simp only [fromJInt]; rw [← BitVec.ofInt_neg, toJInt_ofInt_val]
  · rw [toJInt_fromJInt, wrapInt_val]

theorem wrapInt_narrow {t P : IntTy} (h : t.bits ≤ P.bits) (z : Int) :
    wrapInt t (wrapInt P z) = wrapInt t z := by
  apply wrapInt_congr
  have hd : ((2 ^ t.bits : Nat) : Int) ∣ ((2 ^ P.bits : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
  rw [← Int.emod_emod_of_dvd (wrapInt P z) hd, wrapInt_emod_self, Int.emod_emod_of_dvd _ hd]

theorem promote_signed {s t : IntTy} (hs : s.signed = true) (ht : t.signed = true) :
    (s.promote t).signed = true := by
  cases s <;> cases t <;> simp_all [IntTy.signed, IntTy.promote, IntTy.bits]

theorem bits_le_promote_left (s t : IntTy) : s.bits ≤ (s.promote t).bits := by
  cases s <;> cases t <;> decide

theorem widenTo_val (T : IntTy) {S : IntTy} (x : JInt S) : (int.widenTo T x).val = wrapInt T x.val := rfl

theorem widen_promote_left {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) :
    wrapInt (s.promote t) x.val = x.val := by
  have hx := x.property
  cases s <;> cases t <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
    omega

theorem widen_promote_right {s t : IntTy} (h : s.signed = t.signed) (y : JInt t) :
    wrapInt (s.promote t) y.val = y.val := by
  have hy := y.property
  cases s <;> cases t <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
    omega

theorem binop_eq (op : {r : IntTy} → JInt r → JInt r → JInt r) {s t : IntTy} (x : JInt s) (y : JInt t) :
    int.binop op x y = op (int.remT (s.promote t) x) (int.remT (s.promote t) y) := by
  unfold int.binop int.op_Integer
  split <;> rfl

theorem neg_iff_top {t : IntTy} (h : t.signed = true) (x : JInt t) :
    x.val < 0 ↔ (pattern x).testBit (t.bits - 1) = true := by
  have hx := x.property
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  unfold pattern
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

theorem bxor_neg_iff {t : IntTy} (h : t.signed = true) (a b : JInt t) :
    (int.bxor a b).val < 0 ↔ ¬ (a.val < 0 ↔ b.val < 0) := by
  rw [neg_iff_top h, neg_iff_top h, neg_iff_top h, pattern_bxor, Nat.testBit_xor]
  cases (pattern a).testBit (t.bits - 1) <;> cases (pattern b).testBit (t.bits - 1) <;> simp

theorem flipsign_val {s t : IntTy} (hs : s.signed = true) (ht : t.signed = true) (x : JInt s)
    (y : JInt t) : (int.flipsign x y).val = wrapInt s (if y.val < 0 then -x.val else x.val) := by
  unfold int.flipsign
  rw [ite_eq_left_iff.mpr fun h => absurd ht h]
  split
  · rename_i h
    subst h
    rw [int.flipsign_same, flipsign_int_val hs, remT_val, wrapInt_val]
  · simp only [int.flipsign_BitSigned, int.promoteSameSign, remT_val]
    rw [flipsign_int_val (promote_signed hs ht), widenTo_val, widenTo_val,
      widen_promote_left (by rw [hs, ht]) x, widen_promote_right (by rw [hs, ht]) y]
    exact wrapInt_narrow (bits_le_promote_left s t) _

theorem copysign_Signed_val {s t : IntTy} (hs : s.signed = true) (ht : t.signed = true) (x : JInt s)
    (y : JInt t) : (int.copysign_Signed x y).val =
      wrapInt s (if y.val < 0 then -(x.val.natAbs : Int) else x.val.natAbs) := by
  have hP := promote_signed hs ht
  simp only [int.copysign_Signed, flipsign_val hs hP, binop_eq, bxor_neg_iff hP, remT_val,
    widen_promote_left (show s.signed = t.signed by rw [hs, ht]) x,
    widen_promote_right (show s.signed = t.signed by rw [hs, ht]) y]
  by_cases hx : x.val < 0 <;> by_cases hy : y.val < 0 <;> simp [hx, hy] <;> congr 1 <;> omega

theorem bitcastFloat_neg (T : IntTy) {f : Fmt} (y : Fl f) (hw : f.width = T.bits)
    (hT : T.signed = true) : (int.bitcastFloat T y).val < 0 ↔ y.signbit = true := by
  have hy : y.toBits < 2 ^ T.bits := by rw [← hw]; exact y.bits.isLt
  have hweq : f.eb + f.sb = T.bits - 1 := by rw [← hw, Fmt.width]; omega
  unfold Fl.signbit
  rw [hweq, decide_eq_true_iff, int.bitcastFloat, jlBitcast, toJInt_ofNat_val]
  cases T <;> simp_all [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem copysign_Float64_val {s : IntTy} (hs : s.signed = true) (x : JInt s) (c : FV .f64) :
    (int.copysign_Float64 x c).val =
      wrapInt s (if c.signbit then -(x.val.natAbs : Int) else x.val.natAbs) := by
  change (int.copysign_Signed x (int.bitcastFloat .i64 c)).val = _
  rw [copysign_Signed_val hs rfl]
  simp only [bitcastFloat_neg .i64 c (by decide) rfl]

theorem copysign_Float32_val {s : IntTy} (hs : s.signed = true) (x : JInt s) (b : FV .f32) :
    (int.copysign_Float32 x b).val =
      wrapInt s (if b.signbit then -(x.val.natAbs : Int) else x.val.natAbs) := by
  change (int.copysign_Signed x (int.bitcastFloat .i32 b)).val = _
  rw [copysign_Signed_val hs rfl]
  simp only [bitcastFloat_neg .i32 b (by decide) rfl]

theorem unsafe_trunc_i128_f64_val (x : FV .f64)
    (h : if x.signbit then quotient x ≤ 2 ^ 127 else quotient x < 2 ^ 127) :
    (unsafe_trunc_Int128_Float64 x).val = if x.signbit then -(quotient x : Int) else (quotient x : Int) := by
  have hq_le : quotient x ≤ 2 ^ 127 := by revert h; cases x.signbit <;> simp <;> omega
  have hlt128 : quotient x < 2 ^ 128 := by omega
  have he : x.expField < 1023 + 128 := (quotient_lt_pow x 128).mp hlt128
  have hu := unsafe_trunc_u128_f64_val x he
  have hrem_abs : (int.remT .i128 (unsafe_trunc_UInt128_Float64 x)).val.natAbs = quotient x := by
    rw [remT_val, hu]
    simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
    omega
  unfold unsafe_trunc_Int128_Float64
  rw [copysign_Float64_val rfl, hrem_abs]
  apply wrapInt_of_inRange
  revert h
  cases hs : x.signbit <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega


def width (t : IntTy) : Nat := if t.signed then t.bits - 1 else t.bits

def upperExp (T : FTy) (t : IntTy) : Nat := min (T.fmt.bias + width t) T.fmt.emax

def upperBits (T : FTy) (t : IntTy) : Nat := upperExp T t * 2 ^ T.fmt.sb

def lowerBits (T : FTy) (t : IntTy) : Nat :=
  if t.signed then
    2 ^ (T.fmt.eb + T.fmt.sb) + upperBits T t +
      if t.bits / 8 < T.bytes then 2 ^ (T.fmt.sb - width t) else 0
  else 2 ^ (T.fmt.eb + T.fmt.sb) + T.fmt.bias * 2 ^ T.fmt.sb

def bitTruncValid (T : FTy) (t : IntTy) (x : FV T) : Prop :=
  if x.signbit then
    if t.signed then
      if t.bits / 8 < T.bytes then x.magnitude < upperBits T t + 2 ^ (T.fmt.sb - width t)
      else if T.fmt.bias + width t ≥ T.fmt.emax then x.magnitude < upperBits T t
      else x.magnitude ≤ upperBits T t
    else x.magnitude < T.fmt.bias * 2 ^ T.fmt.sb
  else x.magnitude < upperBits T t

def bitIntValid (T : FTy) (t : IntTy) (x : FV T) : Prop :=
  if x.signbit then
    if t.signed then x.magnitude ≤ upperBits T t
    else x.magnitude = 0
  else x.magnitude < upperBits T t

instance (T : FTy) (t : IntTy) (x : FV T) : Decidable (bitTruncValid T t x) := by
  unfold bitTruncValid; infer_instance

instance (T : FTy) (t : IntTy) (x : FV T) : Decidable (bitIntValid T t x) := by
  unfold bitIntValid; infer_instance

theorem min_eq (t : IntTy) :
    t.min = if t.signed then -((2 ^ (width t) : Nat) : Int) else 0 := by
  cases t <;> decide

theorem max_eq (t : IntTy) : t.max = ((2 ^ (width t) : Nat) : Int) - 1 := by
  cases t <;> decide

theorem isfinite_iff_mag {T : FTy} (x : FV T) :
    x.isfinite = true ↔ x.magnitude < T.fmt.emax * 2 ^ T.fmt.sb := by
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hP := Nat.two_pow_pos T.fmt.sb
  have hM := (Fl.bits_split x).2
  have hS := (good_fty T).emax_succ
  have hdiv : x.expField < 2 ^ T.fmt.eb := by
    rw [Fl.expField_eq]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  simp only [Fl.isfinite, bne_iff_ne]
  constructor
  · intro hne
    have hlt : x.expField < T.fmt.emax := by omega
    have : (x.expField + 1) * 2 ^ T.fmt.sb ≤ T.fmt.emax * 2 ^ T.fmt.sb :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at this
    omega
  · intro hlt h_eq
    rw [h_eq] at hm
    omega

theorem isnan_iff_mag {T : FTy} (x : FV T) :
    x.isnan = true ↔ T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude := by
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hP := Nat.two_pow_pos T.fmt.sb
  have hM := (Fl.bits_split x).2
  have hS := (good_fty T).emax_succ
  have hdiv : x.expField < 2 ^ T.fmt.eb := by
    rw [Fl.expField_eq]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  constructor
  · rintro ⟨he, hfr⟩
    rw [hm, he]; omega
  · intro hgt
    have he : x.expField = T.fmt.emax := by
      rcases Nat.lt_or_ge x.expField T.fmt.emax with hlt | hge
      · have : (x.expField + 1) * 2 ^ T.fmt.sb ≤ T.fmt.emax * 2 ^ T.fmt.sb :=
          Nat.mul_le_mul_right _ hlt
        rw [Nat.succ_mul] at this
        omega
      · omega
    exact ⟨he, by rw [hm, he] at hgt; omega⟩

theorem lower_trunc_constant (T : FTy) (t : IntTy) :
    (if !t.signed || int.sizeofT t < T.bytes then
      sub_IEEEFloat (floatOfInt T (int.typemin t)) (one_float T)
     else floatOfInt T (int.typemin t)) = Fl.ofBits (lowerBits T t) := by
  cases T <;> cases t <;> decide

theorem upper_trunc_constant (T : FTy) (t : IntTy) :
    (if !t.signed || int.sizeofT t < T.bytes then
      add_IEEEFloat (floatOfInt T (int.typemax t)) (one_float T)
     else floatOfInt T (int.typemax t)) = Fl.ofBits (upperBits T t) := by
  cases T <;> cases t <;> decide

theorem min_int_constant (T : FTy) (t : IntTy) :
    floatOfInt T (int.typemin t) =
      Fl.ofBits (if t.signed then 2 ^ (T.fmt.eb + T.fmt.sb) + upperBits T t else 0) := by
  cases T <;> cases t <;> decide

theorem lo_egal_neg_inf (T : FTy) (t : IntTy) :
    egal_float (floatOfInt T (int.typemin t)) (neg_IEEEFloat (inf_float T)) =
      decide (t.signed && T.fmt.bias + width t ≥ T.fmt.emax) := by
  cases T <;> cases t <;> decide

theorem fl_lt_pos_const {T : FTy} (x : FV T) (M : Nat)
    (h0 : 0 < M) (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) :
    Fl.lt x (Fl.ofBits M) = decide (if x.signbit then x.magnitude ≤ T.fmt.emax * 2 ^ T.fmt.sb
      else x.magnitude < M) := by
  obtain ⟨hx_split, hx_mag⟩ := Fl.bits_split x
  have hnan_x : x.isnan = decide (T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude) :=
    Bool.eq_iff_iff.mpr (by rw [isnan_iff_mag, decide_eq_true_iff])
  have hW : M < 2 ^ T.fmt.width := by
    have := Fmt.width_pow T.fmt
    have : T.fmt.emax * 2 ^ T.fmt.sb < 2 ^ (T.fmt.eb + T.fmt.sb) := by
      cases T <;> decide
    omega
  have hc_bits : (Fl.ofBits M : FV T).toBits = M := by
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt hW]
  have hc_sign : (Fl.ofBits M : FV T).signbit = false := by
    unfold Fl.signbit; rw [hc_bits]
    have : T.fmt.emax * 2 ^ T.fmt.sb < 2 ^ (T.fmt.eb + T.fmt.sb) := by cases T <;> decide
    simp; omega
  have hc_mag : (Fl.ofBits M : FV T).magnitude = M := by
    unfold Fl.magnitude; rw [hc_bits]
    have : T.fmt.emax * 2 ^ T.fmt.sb < 2 ^ (T.fmt.eb + T.fmt.sb) := by cases T <;> decide
    exact Nat.mod_eq_of_lt (by omega)
  have hc_nan : (Fl.ofBits M : FV T).isnan = false := by
    rw [Bool.eq_false_iff, ne_eq, isnan_iff_mag, hc_mag]; omega
  have hc_zero : (Fl.ofBits M : FV T).iszero = false := by
    unfold Fl.iszero; rw [hc_mag]; simp; omega
  have hx_zero : x.iszero = (x.magnitude == 0) := rfl
  unfold Fl.lt
  rw [hnan_x, hc_nan, hc_zero, hc_sign, hc_bits, hx_zero, hx_split]
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  cases x.signbit <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

theorem fl_lt_neg_const {T : FTy} (x : FV T) (M : Nat)
    (h0 : 0 < M) (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) :
    Fl.lt (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M)) x =
      decide (if x.signbit then x.magnitude < M
       else x.magnitude ≤ T.fmt.emax * 2 ^ T.fmt.sb) := by
  obtain ⟨hx_split, hx_mag⟩ := Fl.bits_split x
  have hnan_x : x.isnan = decide (T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude) :=
    Bool.eq_iff_iff.mpr (by rw [isnan_iff_mag, decide_eq_true_iff])
  have hlt_pow : T.fmt.emax * 2 ^ T.fmt.sb < 2 ^ (T.fmt.eb + T.fmt.sb) := by cases T <;> decide
  have hW : 2 ^ (T.fmt.eb + T.fmt.sb) + M < 2 ^ T.fmt.width := by
    rw [Fmt.width_pow]; omega
  have hc_bits : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).toBits =
      2 ^ (T.fmt.eb + T.fmt.sb) + M := by
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt hW]
  have hc_sign : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).signbit = true := by
    unfold Fl.signbit; rw [hc_bits]; simp
  have hc_mag : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).magnitude = M := by
    unfold Fl.magnitude; rw [hc_bits, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hc_nan : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).isnan = false := by
    rw [Bool.eq_false_iff, ne_eq, isnan_iff_mag, hc_mag]; omega
  have hc_zero : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).iszero = false := by
    unfold Fl.iszero; rw [hc_mag]; simp; omega
  have hx_zero : x.iszero = (x.magnitude == 0) := rfl
  unfold Fl.lt
  rw [hnan_x, hc_nan, hc_zero, hc_sign, hc_bits, hx_zero, hx_split]
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  cases x.signbit <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

theorem fl_le_neg_const {T : FTy} (x : FV T) (M : Nat)
    (h0 : 0 < M) (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) :
    Fl.le (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M)) x =
      decide (if x.signbit then x.magnitude ≤ M
       else x.magnitude ≤ T.fmt.emax * 2 ^ T.fmt.sb) := by
  obtain ⟨hx_split, hx_mag⟩ := Fl.bits_split x
  have hnan_x : x.isnan = decide (T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude) :=
    Bool.eq_iff_iff.mpr (by rw [isnan_iff_mag, decide_eq_true_iff])
  have hlt_pow : T.fmt.emax * 2 ^ T.fmt.sb < 2 ^ (T.fmt.eb + T.fmt.sb) := by cases T <;> decide
  have hW : 2 ^ (T.fmt.eb + T.fmt.sb) + M < 2 ^ T.fmt.width := by
    rw [Fmt.width_pow]; omega
  have hc_bits : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).toBits =
      2 ^ (T.fmt.eb + T.fmt.sb) + M := by
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt hW]
  have hc_mag : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).magnitude = M := by
    unfold Fl.magnitude; rw [hc_bits, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hc_nan : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).isnan = false := by
    rw [Bool.eq_false_iff, ne_eq, isnan_iff_mag, hc_mag]; omega
  have hc_zero : (Fl.ofBits (2 ^ (T.fmt.eb + T.fmt.sb) + M) : FV T).iszero = false := by
    unfold Fl.iszero; rw [hc_mag]; simp; omega
  have hx_zero : x.iszero = (x.magnitude == 0) := rfl
  unfold Fl.le
  rw [fl_lt_neg_const x M h0 hM]
  unfold Fl.eq
  rw [hnan_x, hc_nan, hc_zero, hc_bits, hx_zero, hx_split]
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  cases x.signbit <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega

theorem fl_le_zero_const {T : FTy} (x : FV T) :
    Fl.le (Fl.ofBits 0) x =
      decide (if x.signbit then x.magnitude = 0
       else x.magnitude ≤ T.fmt.emax * 2 ^ T.fmt.sb) := by
  obtain ⟨hx_split, hx_mag⟩ := Fl.bits_split x
  have hnan_x : x.isnan = decide (T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude) :=
    Bool.eq_iff_iff.mpr (by rw [isnan_iff_mag, decide_eq_true_iff])
  have hc_bits : (Fl.ofBits 0 : FV T).toBits = 0 := rfl
  have hc_sign : (Fl.ofBits 0 : FV T).signbit = false := by cases T <;> decide
  have hc_nan : (Fl.ofBits 0 : FV T).isnan = false := by cases T <;> decide
  have hc_zero : (Fl.ofBits 0 : FV T).iszero = true := by cases T <;> decide
  have hx_zero : x.iszero = (x.magnitude == 0) := rfl
  unfold Fl.le Fl.lt Fl.eq
  rw [hnan_x, hc_nan, hc_zero, hc_sign, hc_bits, hx_zero, hx_split]
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  cases x.signbit <;> apply Bool.eq_iff_iff.mpr <;> simp <;> omega


@[simp] theorem f16_eb : FTy.f16.fmt.eb = 5 := rfl
@[simp] theorem f16_sb : FTy.f16.fmt.sb = 10 := rfl
@[simp] theorem f16_bias : FTy.f16.fmt.bias = 15 := rfl
@[simp] theorem f16_emax : FTy.f16.fmt.emax = 31 := rfl
@[simp] theorem f32_eb : FTy.f32.fmt.eb = 8 := rfl
@[simp] theorem f32_sb : FTy.f32.fmt.sb = 23 := rfl
@[simp] theorem f32_bias : FTy.f32.fmt.bias = 127 := rfl
@[simp] theorem f32_emax : FTy.f32.fmt.emax = 255 := rfl
@[simp] theorem f64_eb : FTy.f64.fmt.eb = 11 := rfl
@[simp] theorem f64_sb : FTy.f64.fmt.sb = 52 := rfl
@[simp] theorem f64_bias : FTy.f64.fmt.bias = 1023 := rfl
@[simp] theorem f64_emax : FTy.f64.fmt.emax = 2047 := rfl

theorem trunc_checks (T : FTy) (t : IntTy) (x : FV T) :
    (if !t.signed || int.sizeofT t < T.bytes then
      lt_IEEEFloat (sub_IEEEFloat (floatOfInt T (int.typemin t)) (one_float T)) x &&
        lt_IEEEFloat x (add_IEEEFloat (floatOfInt T (int.typemax t)) (one_float T))
     else
      let lo := floatOfInt T (int.typemin t)
      let hi := floatOfInt T (int.typemax t)
      (if egal_float lo (neg_IEEEFloat (inf_float T)) then lt_IEEEFloat lo x else le_IEEEFloat lo x) &&
        lt_IEEEFloat x hi) = decide (bitTruncValid T t x) := by
  have hl := lower_trunc_constant T t
  have hu := upper_trunc_constant T t
  have hegal := lo_egal_neg_inf T t
  have hlt_eq : ∀ a b : FV T, lt_IEEEFloat a b = Fl.lt a b := fun _ _ => rfl
  have hle_eq : ∀ a b : FV T, le_IEEEFloat a b = Fl.le a b := fun _ _ => rfl
  have hM2_0 : 0 < upperBits T t := by cases T <;> cases t <;> decide
  have hM2_le : upperBits T t ≤ T.fmt.emax * 2 ^ T.fmt.sb := by cases T <;> cases t <;> decide
  by_cases hc : (!t.signed || int.sizeofT t < T.bytes) = true
  · simp only [hc, ↓reduceIte, hlt_eq] at hl hu ⊢
    rw [hl, hu]
    let M1 := if t.signed then upperBits T t + (if t.bits / 8 < T.bytes then 2 ^ (T.fmt.sb - width t) else 0)
      else T.fmt.bias * 2 ^ T.fmt.sb
    have hlow_split : lowerBits T t = 2 ^ (T.fmt.eb + T.fmt.sb) + M1 := by
      unfold lowerBits M1; cases t.signed <;> simp [Nat.add_assoc]
    have hM1_0 : 0 < M1 := by revert hc; cases T <;> cases t <;> decide
    have hM1_le : M1 ≤ T.fmt.emax * 2 ^ T.fmt.sb := by revert hc; cases T <;> cases t <;> decide
    rw [hlow_split, fl_lt_neg_const x M1 hM1_0 hM1_le, fl_lt_pos_const x (upperBits T t) hM2_0 hM2_le]
    clear hl hu hegal hM2_0 hM2_le hlow_split hM1_0 hM1_le
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    unfold bitTruncValid M1
    revert hc
    cases T <;> cases t <;> intro hc <;> (try contradiction) <;>
      cases x.signbit <;>
      simp [upperBits, upperExp, width, FTy.bytes, IntTy.signed, IntTy.bits] <;> omega
  · have hc' : (!t.signed || int.sizeofT t < T.bytes) = false := Bool.eq_false_iff.mpr hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte, hlt_eq, hle_eq, hegal] at hl hu ⊢
    rw [hl, hu]
    have hlow_split : lowerBits T t = 2 ^ (T.fmt.eb + T.fmt.sb) + upperBits T t := by
      revert hc'; cases T <;> cases t <;> decide
    rw [hlow_split, fl_lt_pos_const x (upperBits T t) hM2_0 hM2_le]
    by_cases hinf : decide (t.signed && T.fmt.bias + width t ≥ T.fmt.emax) = true
    · simp only [hinf, ↓reduceIte]
      rw [fl_lt_neg_const x (upperBits T t) hM2_0 hM2_le]
      clear hl hu hegal hM2_0 hM2_le hlow_split hc
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      unfold bitTruncValid
      revert hc' hinf
      cases T <;> cases t <;> intro hc' hinf <;> (try contradiction) <;>
        cases x.signbit <;>
        simp [upperBits, upperExp, width, FTy.bytes, IntTy.signed, IntTy.bits] <;> omega
    · have hinf' : decide (t.signed && T.fmt.bias + width t ≥ T.fmt.emax) = false :=
        Bool.eq_false_iff.mpr hinf
      simp only [hinf', Bool.false_eq_true, ↓reduceIte]
      rw [fl_le_neg_const x (upperBits T t) hM2_0 hM2_le]
      clear hl hu hegal hM2_0 hM2_le hlow_split hc hinf
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      unfold bitTruncValid
      revert hc' hinf'
      cases T <;> cases t <;> intro hc' hinf' <;> (try contradiction) <;>
        cases x.signbit <;>
        simp [upperBits, upperExp, width, FTy.bytes, IntTy.signed, IntTy.bits] <;> omega

theorem int_checks (T : FTy) (t : IntTy) (x : FV T) :
    (le_IEEEFloat (floatOfInt T (int.typemin t)) x &&
      lt_IEEEFloat x (if !t.signed || int.sizeofT t < T.bytes then
        add_IEEEFloat (floatOfInt T (int.typemax t)) (one_float T)
      else floatOfInt T (int.typemax t))) = decide (bitIntValid T t x) := by
  have hl := min_int_constant T t
  have hu := upper_trunc_constant T t
  have hlt_eq : ∀ a b : FV T, lt_IEEEFloat a b = Fl.lt a b := fun _ _ => rfl
  have hle_eq : ∀ a b : FV T, le_IEEEFloat a b = Fl.le a b := fun _ _ => rfl
  rw [hlt_eq, hle_eq, hl, hu]
  have hM2_0 : 0 < upperBits T t := by cases T <;> cases t <;> decide
  have hM2_le : upperBits T t ≤ T.fmt.emax * 2 ^ T.fmt.sb := by cases T <;> cases t <;> decide
  rw [fl_lt_pos_const x (upperBits T t) hM2_0 hM2_le]
  cases ht : t.signed
  · simp only [Bool.false_eq_true, ↓reduceIte, fl_le_zero_const]
    clear hl hu hM2_0 hM2_le
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    unfold bitIntValid
    revert ht
    cases T <;> cases t <;> intro ht <;> (try contradiction) <;>
      cases x.signbit <;>
      simp [upperBits, upperExp, width, IntTy.signed, IntTy.bits] <;> omega
  · simp only [↓reduceIte, fl_le_neg_const x (upperBits T t) hM2_0 hM2_le]
    clear hl hu hM2_0 hM2_le
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_iff]
    unfold bitIntValid
    revert ht
    cases T <;> cases t <;> intro ht <;> (try contradiction) <;>
      cases x.signbit <;>
      simp [upperBits, upperExp, width, IntTy.signed, IntTy.bits] <;> omega

theorem unsafe_trunc_u128_f32_val (x : FV .f32) (he : x.expField < 127 + 128) :
    (unsafe_trunc_UInt128_Float32 x).val = (quotient x : Int) := by
  have hf : x.frac < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have hexp : x.expField < 256 := Nat.mod_lt _ (by decide)
  have hpat_xu0 : pattern (reinterpret_Unsigned_Float32 x) = x.toBits :=
    pattern_reinterpret_Unsigned (T := .f32) x
  have hpat_exp : pattern (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float32 x) (int.lit .i64 23))) (int.lit .i64 0x00ff)) = x.expField := by
    rw [pattern_band]
    have hshr : (int.shr_Int (reinterpret_Unsigned_Float32 x) (int.lit .i64 23)).val = (x.toBits / 2 ^ 23 : Nat) := by
      rw [← val_of_unsigned_pattern rfl, pattern_shr_Int_unsigned rfl _ _ (by decide), hpat_xu0]
      rfl
    have hrem : pattern (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float32 x) (int.lit .i64 23))) = x.toBits / 2 ^ 23 := by
      have hlt32 : x.toBits < 2 ^ 32 := x.bits.isLt
      rw [pattern_of_cong _ _ (remT_val .i64 _), hshr]
      have : ((x.toBits / 2 ^ 23 : Nat) : Int) % ((2 ^ 64 : Nat) : Int) = (x.toBits / 2 ^ 23 : Nat) :=
        Int.emod_eq_of_lt (by omega) (by omega)
      change (((x.toBits / 2 ^ 23 : Nat) : Int) % ((2 ^ 64 : Nat) : Int)).toNat = _
      rw [this]; rfl
    have h2 : pattern (int.lit .i64 0x00ff) = 2 ^ 8 - 1 := rfl
    rw [hrem, h2, nat_and_mask]
    rfl
  have hexp_val : (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float32 x) (int.lit .i64 23))) (int.lit .i64 0x00ff)).val = (x.expField : Int) := by
    have hlt_exp : pattern (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float32 x) (int.lit .i64 23))) (int.lit .i64 0x00ff)) < 2 ^ (IntTy.i64.bits - 1) := by
      rw [hpat_exp]; dsimp [IntTy.bits]; omega
    rw [val_of_signed_small_pattern _ hlt_exp, hpat_exp]
  have hk_val : (int.sub (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float32 x) (int.lit .i64 23))) (int.lit .i64 0x00ff)) (int.lit .i64 150)).val =
      (x.expField : Int) - 150 := by
    rw [sub_int_val, hexp_val]
    have : (int.lit .i64 150).val = 150 := rfl
    rw [this]
    simp [wrapInt, IntTy.signed, IntTy.bits]; omega
  have hpat_mant : pattern (int.bor (int.band (reinterpret_Unsigned_Float32 x) (int.lit .u32 0x007f_ffff)) (int.lit .u32 0x0080_0000)) =
      x.frac + 2 ^ 23 := by
    rw [pattern_bor, pattern_band, hpat_xu0]
    have h1 : pattern (int.lit .u32 0x007f_ffff) = 2 ^ 23 - 1 := rfl
    have h2 : pattern (int.lit .u32 0x0080_0000) = 2 ^ 23 := rfl
    rw [h1, h2, nat_and_mask, show x.toBits % 2 ^ 23 = x.frac from rfl, nat_or_pow _ 23 hf]
  dsimp only [unsafe_trunc_UInt128_Float32]
  generalize hk_def : int.sub (int.band (int.remT .i64 (int.shr_Int (reinterpret_Unsigned_Float32 x) (int.lit .i64 23))) (int.lit .i64 0x00ff)) (int.lit .i64 150) = k at hk_val
  generalize hxu_def : int.bor (int.band (reinterpret_Unsigned_Float32 x) (int.lit .u32 0x007f_ffff)) (int.lit .u32 0x0080_0000) = xu at hpat_mant
  have hle_k : int.le_BitSigned k (int.lit .i64 0) = decide (x.expField ≤ 150) := by
    rw [int.le_BitSigned, sle_int_eq rfl, hk_val]
    have : (int.lit .i64 0).val = 0 := by decide
    rw [this]; apply decide_eq_decide.mpr; omega
  rw [hle_k]
  by_cases hle : x.expField ≤ 150
  · simp only [decide_eq_true hle, ↓reduceIte]
    have hneg_k : (int.neg k).val = (150 - x.expField : Nat) := by
      rw [neg_int_val, hk_val]
      simp [wrapInt, IntTy.signed, IntTy.bits]; omega
    have hpat_shr : pattern (int.shr_Int xu (int.neg k)) = (x.frac + 2 ^ 23) / 2 ^ (150 - x.expField) := by
      rw [pattern_shr_Int_unsigned rfl xu (int.neg k) (by rw [hneg_k]; omega), hpat_mant, hneg_k]
      rfl
    have hval_shr : (int.shr_Int xu (int.neg k)).val = ((x.frac + 2 ^ 23) / 2 ^ (150 - x.expField) : Nat) := by
      rw [← val_of_unsigned_pattern rfl, hpat_shr]
    have hwiden : (int.widenTo .u128 (int.shr_Int xu (int.neg k))).val =
        ((x.frac + 2 ^ 23) / 2 ^ (150 - x.expField) : Nat) := by
      simp only [int.widenTo, int.lit, JInt.wrap, hval_shr]
      have hdiv_lt : (x.frac + 2 ^ 23) / 2 ^ (150 - x.expField) < 2 ^ 24 := by
        have := Nat.div_le_self (x.frac + 2 ^ 23) (2 ^ (150 - x.expField))
        omega
      apply wrapInt_of_inRange
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true, ↓reduceIte]
      omega
    rw [hwiden]
    by_cases hlt127 : x.expField < 127
    · rw [quotient_small x hlt127]
      have hdiv0 : (x.frac + 2 ^ 23) / 2 ^ (150 - x.expField) = 0 := by
        apply Nat.div_eq_of_lt
        calc x.frac + 2 ^ 23 < 2 ^ 24 := by omega
          _ ≤ 2 ^ (150 - x.expField) := Nat.pow_le_pow_right (by decide) (by omega)
      simp [hdiv0]
    · have hnz : x.expField ≠ 0 := by omega
      have hq : quotient x = (x.frac + 2 ^ 23) / 2 ^ (150 - x.expField) := by
        have hb1 : FTy.f32.fmt.bias + FTy.f32.fmt.sb = 150 := rfl
        have hb2 : 2 ^ FTy.f32.fmt.sb = 2 ^ 23 := rfl
        simp only [quotient, numerator, denominator, mantissaNat, hnz, ↓reduceIte, hb1, hb2,
          Nat.sub_eq_zero_of_le hle, Nat.pow_zero, Nat.mul_one]
      rw [hq]
  · simp only [decide_eq_false hle, Bool.false_eq_true, ↓reduceIte]
    have hgt : 150 < x.expField := by omega
    have hnz : x.expField ≠ 0 := by omega
    have hxu_val : xu.val = ((x.frac + 2 ^ 23 : Nat) : Int) := by
      rw [← val_of_unsigned_pattern rfl, hpat_mant]
    have hwiden_pat' : pattern (int.widenTo .u128 xu) = x.frac + 2 ^ 23 := by
      rw [pattern_of_cong _ xu.val rfl, hxu_val]
      have : ((x.frac + 2 ^ 23 : Nat) : Int) % ((2 ^ 128 : Nat) : Int) = (x.frac + 2 ^ 23 : Nat) := by
        apply Int.emod_eq_of_lt (by omega) (by omega)
      change (((x.frac + 2 ^ 23 : Nat) : Int) % ((2 ^ 128 : Nat) : Int)).toNat = _
      rw [this]; rfl
    have hk_toNat : k.val.toNat = x.expField - 150 := by omega
    have hprod_lt : (x.frac + 2 ^ 23) * 2 ^ (x.expField - 150) < 2 ^ 128 := by
      calc (x.frac + 2 ^ 23) * 2 ^ (x.expField - 150)
          < 2 ^ 24 * 2 ^ (x.expField - 150) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 (by omega)
        _ = 2 ^ (24 + (x.expField - 150)) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide) (by omega)
    have hpat_shl : pattern (int.shl_Int (int.widenTo .u128 xu) k) =
        (x.frac + 2 ^ 23) * 2 ^ (x.expField - 150) := by
      rw [pattern_shl_Int _ _ (by omega), hwiden_pat', hk_toNat]
      exact Nat.mod_eq_of_lt hprod_lt
    rw [← val_of_unsigned_pattern rfl, hpat_shl]
    have hq : quotient x = (x.frac + 2 ^ 23) * 2 ^ (x.expField - 150) := by
      have hb1 : FTy.f32.fmt.bias + FTy.f32.fmt.sb = 150 := rfl
      have hb2 : 2 ^ FTy.f32.fmt.sb = 2 ^ 23 := rfl
      simp only [quotient, numerator, denominator, mantissaNat, hnz, ↓reduceIte, hb1, hb2,
        Nat.sub_eq_zero_of_le (by omega : 150 ≤ x.expField), Nat.pow_zero, Nat.div_one]
    rw [hq]

theorem unsafe_trunc_i128_f32_val (x : FV .f32)
    (h : if x.signbit then quotient x ≤ 2 ^ 127 else quotient x < 2 ^ 127) :
    (unsafe_trunc_Int128_Float32 x).val = if x.signbit then -(quotient x : Int) else (quotient x : Int) := by
  have hq_le : quotient x ≤ 2 ^ 127 := by revert h; cases x.signbit <;> simp <;> omega
  have hlt128 : quotient x < 2 ^ 128 := by omega
  have he : x.expField < 127 + 128 := (quotient_lt_pow x 128).mp hlt128
  have hu := unsafe_trunc_u128_f32_val x he
  have hrem_abs : (int.remT .i128 (unsafe_trunc_UInt128_Float32 x)).val.natAbs = quotient x := by
    rw [remT_val, hu]
    simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
    omega
  unfold unsafe_trunc_Int128_Float32
  rw [copysign_Float32_val rfl, hrem_abs]
  apply wrapInt_of_inRange
  revert h
  cases hs : x.signbit <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem f32_of_f16_quotient (x : FV .f16) (hfin : x.isfinite = true) :
    (Float32_Float16 x).isfinite = true ∧
    (Float32_Float16 x).signbit = x.signbit ∧
    quotient (Float32_Float16 x) = quotient x := by
  have hconv : Float32_Float16 x = (Fl.convert x : FV .f32) := convertFloat_eq .f32 x
  have hord : ∀ y : Int, exactOrder (Float32_Float16 x) y = exactOrder x y := by
    intro y; rw [hconv]
    exact Fl.convert_exactOrder (good_fty .f16) (good_fty .f32) (by decide) (by decide) (by decide) x y
  have hfin_sign : (Float32_Float16 x).isfinite = true ∧ (Float32_Float16 x).signbit = x.signbit := by
    rw [hconv]
    dsimp only [Fl.convert]
    have hne : (FTy.f32.fmt == FTy.f16.fmt) = false := by decide
    simp only [hne, Fl.isnan_of_finite hfin, Fl.isinf_of_finite hfin, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨m, i, j, hr, -, hm, hrange⟩ := Fl.toRat_cases (good_fty .f16) x hfin
    rw [hr]
    dsimp only
    by_cases hm0 : m = 0
    · subst hm0
      have hz : (Fl.roundRat (if x.signbit then -((0 * 2 ^ i : Nat) : Int)
          else ((0 * 2 ^ i : Nat) : Int)) (2 ^ j) x.signbit : FV .f32) = Fl.zero x.signbit := by
        cases x.signbit <;> simp [Fl.roundRat]
      rw [hz]
      refine ⟨(Fl.zero_spec (good_fty .f32) x.signbit).1, ?_⟩
      cases x.signbit <;> decide
    · obtain ⟨hlo, hhi⟩ := hrange hm0
      have hn' : (if x.signbit then -((m * 2 ^ i : Nat) : Int)
          else ((m * 2 ^ i : Nat) : Int)).natAbs = m * 2 ^ i := by
        cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
      have hm1 : m < 2 ^ (FTy.f32.fmt.sb + 1) :=
        Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by decide))
      have hlo32 : j + 1 ≤ m.log2 + i + FTy.f32.fmt.bias := by simp at hlo ⊢; omega
      have hhi32 : m.log2 + i + FTy.f32.fmt.bias < j + FTy.f32.fmt.emax := by simp at hhi ⊢; omega
      have hfin32 := (Fl.roundRat_key (f := FTy.f32.fmt) (good_fty .f32) _ m i j x.signbit hn'
        (by omega) hm1 hlo32 hhi32).1
      refine ⟨hfin32, ?_⟩
      have hnorm := Fl.roundRat_normal (f := FTy.f32.fmt) (good_fty .f32) _ m i j x.signbit hn'
        (by omega) hm1 hlo32 hhi32
      rw [hnorm]
      have hpos : 0 < m * 2 ^ i := Nat.mul_pos (by omega) (Nat.two_pow_pos i)
      have hneg : decide ((if x.signbit then -((m * 2 ^ i : Nat) : Int)
          else ((m * 2 ^ i : Nat) : Int)) < 0) = x.signbit := by
        generalize m * 2 ^ i = p at hpos ⊢
        cases x.signbit <;> simp <;> omega
      rw [hneg]
      have hq1 := (Fl.sig_bounds (f := FTy.f32.fmt) m hm0 hm1).2.1
      have hq2 := (Fl.sig_bounds (f := FTy.f32.fmt) m hm0 hm1).2.2
      have hB : m.log2 + i + FTy.f32.fmt.bias - j < 2 ^ FTy.f32.fmt.eb := by simp at hhi ⊢; omega
      have hr' : m * 2 ^ (FTy.f32.fmt.sb - m.log2) - 2 ^ FTy.f32.fmt.sb < 2 ^ FTy.f32.fmt.sb := by
        simp at hq1 hq2 ⊢; omega
      exact (Fl.pack_parts (f := FTy.f32.fmt) x.signbit _ _ hB hr').1
  obtain ⟨hfin32, hsign⟩ := hfin_sign
  refine ⟨hfin32, hsign, ?_⟩
  have htr : (Float32_Float16 x).truncVal = x.truncVal := by
    have h_le : ∀ (T : FTy) (z : FV T) (hz : z.isfinite = true) (y : Int),
        (z.signbit = false → (y ≤ z.truncVal ↔ exactOrder z y ≠ some (-1))) ∧
        (z.signbit = true → (z.truncVal ≤ y ↔ exactOrder z y ≠ some 1)) := by
      intro T z hz y
      have hd_pos : 0 < denominator z := by unfold denominator; exact Nat.two_pow_pos _
      have htr_z := truncVal_parts z hz
      have hrat_z := rat_parts z hz
      unfold exactOrder
      simp only [Fl.isnan_of_finite hz, Fl.isinf_of_finite hz, Bool.false_eq_true, ↓reduceIte]
      rw [hrat_z, htr_z]
      dsimp only
      have hquot_eq : ((quotient z : Nat) : Int) = (numerator z : Int) / (denominator z : Int) := by
        simp [quotient]
      constructor
      · intro hs
        simp only [hs, Bool.false_eq_true, ↓reduceIte, hquot_eq]
        rw [Int.le_ediv_iff_mul_le (by omega)]
        split <;> simp <;> omega
      · intro hs
        simp only [hs, ↓reduceIte, hquot_eq]
        have hmul : -((numerator z : Int) / (denominator z : Int)) ≤ y ↔
            -(numerator z : Int) ≤ y * (denominator z : Int) := by
          have h1 : -((numerator z : Int) / (denominator z : Int)) ≤ y ↔
              -y ≤ (numerator z : Int) / (denominator z : Int) := by omega
          rw [h1, Int.le_ediv_iff_mul_le (by omega), Int.neg_mul]
          omega
        rw [hmul]
        split
        · simp; omega
        · split <;> simp <;> omega
    cases hs : x.signbit
    · have hs32 : (Float32_Float16 x).signbit = false := by rw [hsign, hs]
      have ha := (h_le .f32 (Float32_Float16 x) hfin32 x.truncVal).1 hs32
      have hb := (h_le .f16 x hfin x.truncVal).1 hs
      have hc := (h_le .f32 (Float32_Float16 x) hfin32 (Float32_Float16 x).truncVal).1 hs32
      have hd := (h_le .f16 x hfin (Float32_Float16 x).truncVal).1 hs
      rw [hord, ← hb] at ha
      rw [hord, ← hd] at hc
      omega
    · have hs32 : (Float32_Float16 x).signbit = true := by rw [hsign, hs]
      have ha := (h_le .f32 (Float32_Float16 x) hfin32 x.truncVal).2 hs32
      have hb := (h_le .f16 x hfin x.truncVal).2 hs
      have hc := (h_le .f32 (Float32_Float16 x) hfin32 (Float32_Float16 x).truncVal).2 hs32
      have hd := (h_le .f16 x hfin (Float32_Float16 x).truncVal).2 hs
      rw [hord, ← hb] at ha
      rw [hord, ← hd] at hc
      omega
  rw [truncVal_parts (Float32_Float16 x) hfin32, truncVal_parts x hfin, hsign] at htr
  revert htr
  cases x.signbit <;> simp <;> omega

theorem trunc_range (T : FTy) (t : IntTy) (x : FV T) :
    bitTruncValid T t x ↔ x.isfinite = true ∧ t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max := by
  have hfin_iff := isfinite_iff_mag x
  have hmin := min_eq t
  have hmax := max_eq t
  have h0 : 0 < 2 ^ (width t) := Nat.two_pow_pos (width t)
  have hbias_lt : T.fmt.bias * 2 ^ T.fmt.sb < T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> decide
  have hub_le : upperBits T t ≤ T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> cases t <;> decide
  by_cases hfin : x.isfinite = true
  · have hmag_fin : x.magnitude < T.fmt.emax * 2 ^ T.fmt.sb := hfin_iff.mp hfin
    have htr := truncVal_parts x hfin
    simp only [hfin, true_and, htr, hmin, hmax]
    unfold bitTruncValid
    by_cases hbig_exp : T.fmt.bias + width t ≥ T.fmt.emax
    · have hub_eq : upperBits T t = T.fmt.emax * 2 ^ T.fmt.sb := by
        revert hbig_exp; cases T <;> cases t <;> decide
      have hnot_small : ¬(t.bits / 8 < T.bytes) := by
        revert hbig_exp; cases T <;> cases t <;> decide
      have hexp_lt : x.expField < T.fmt.bias + width t := by
        obtain ⟨hm, _⟩ := mag_decomp x
        have hP := Nat.two_pow_pos T.fmt.sb
        have : x.expField < T.fmt.emax :=
          Classical.byContradiction fun hge => by
            have : T.fmt.emax * 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb :=
              Nat.mul_le_mul_right _ (by omega)
            omega
        omega
      have hq_lt : quotient x < 2 ^ (width t) := (quotient_lt_pow x (width t)).mpr hexp_lt
      simp only [hnot_small, hbig_exp, ↓reduceIte, hub_eq]
      cases hs : x.signbit <;> cases ht : t.signed <;> simp only [↓reduceIte, Bool.false_eq_true]
      · omega
      · omega
      · rw [← quotient_zero_bits x]
        omega
      · omega
    · have hub_eq : upperBits T t = (T.fmt.bias + width t) * 2 ^ T.fmt.sb := by
        revert hbig_exp; cases T <;> cases t <;> decide
      have hlt_exp : width t ≤ T.fmt.emax - 1 - T.fmt.bias := by
        revert hbig_exp; cases T <;> cases t <;> decide
      have hq_lt := quotient_lt_pow_bits x (width t)
      rw [← hub_eq] at hq_lt
      simp only [hbig_exp, ↓reduceIte]
      cases hs : x.signbit
      · simp only [Bool.false_eq_true, ↓reduceIte, ← hq_lt]
        cases t.signed <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
      · simp only [↓reduceIte]
        cases ht : t.signed
        · simp only [Bool.false_eq_true, ↓reduceIte, ← quotient_zero_bits x]
          omega
        · simp only [↓reduceIte]
          by_cases hsmall : t.bits / 8 < T.bytes
          · have hwsb : width t < T.fmt.sb := by
              revert hsmall ht; cases T <;> cases t <;> decide
            have hq_le := quotient_le_pow_small x (width t) hwsb
            rw [← hub_eq] at hq_le
            simp only [hsmall, ↓reduceIte, ← hq_le]
            omega
          · have hsbw : T.fmt.sb ≤ width t := by
              revert hsmall ht; cases T <;> cases t <;> decide
            have hq_le := quotient_le_pow_big x (width t) hsbw
            rw [← hub_eq] at hq_le
            simp only [hsmall, ↓reduceIte, ← hq_le]
            omega
  · have hnf : x.isfinite = false := Bool.eq_false_iff.mpr hfin
    simp only [hnf, Bool.false_eq_true, false_and, iff_false]
    rw [hfin_iff] at hfin
    have hmag_ge : T.fmt.emax * 2 ^ T.fmt.sb ≤ x.magnitude := by omega
    unfold bitTruncValid
    by_cases h1 : t.bits / 8 < T.bytes
    · have : upperBits T t + 2 ^ (T.fmt.sb - width t) ≤ T.fmt.emax * 2 ^ T.fmt.sb := by
        revert h1; cases T <;> cases t <;> decide
      cases x.signbit <;> cases t.signed <;> simp only [h1, ↓reduceIte, Bool.false_eq_true] <;> omega
    · by_cases h2 : T.fmt.bias + width t ≥ T.fmt.emax
      · cases x.signbit <;> cases t.signed <;> simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] <;> omega
      · have : upperBits T t < T.fmt.emax * 2 ^ T.fmt.sb := by
          revert h1 h2; cases T <;> cases t <;> decide
        cases x.signbit <;> cases t.signed <;> simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] <;> omega

theorem int_range (T : FTy) (t : IntTy) (x : FV T) (hi : x.isinteger = true) :
    bitIntValid T t x ↔ x.isfinite = true ∧ t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max := by
  have hfin : x.isfinite = true := by
    unfold Fl.isinteger at hi; revert hi; cases x.isfinite <;> simp
  have hmod : numerator x % denominator x = 0 := by
    unfold Fl.isinteger at hi
    simp only [hfin, Bool.true_and, beq_iff_eq] at hi
    exact (integral_parts x hfin).mp hi
  have hmag_fin : x.magnitude < T.fmt.emax * 2 ^ T.fmt.sb := (isfinite_iff_mag x).mp hfin
  have htr := truncVal_parts x hfin
  have hmin := min_eq t
  have hmax := max_eq t
  have h0 : 0 < 2 ^ (width t) := Nat.two_pow_pos (width t)
  simp only [hfin, true_and, htr, hmin, hmax]
  unfold bitIntValid
  by_cases hbig_exp : T.fmt.bias + width t ≥ T.fmt.emax
  · have hub_eq : upperBits T t = T.fmt.emax * 2 ^ T.fmt.sb := by
      revert hbig_exp; cases T <;> cases t <;> decide
    have hexp_lt : x.expField < T.fmt.bias + width t := by
      obtain ⟨hm, _⟩ := mag_decomp x
      have hP := Nat.two_pow_pos T.fmt.sb
      have : x.expField < T.fmt.emax :=
        Classical.byContradiction fun hge => by
          have : T.fmt.emax * 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb :=
            Nat.mul_le_mul_right _ (by omega)
          omega
      omega
    have hq_lt : quotient x < 2 ^ (width t) := (quotient_lt_pow x (width t)).mpr hexp_lt
    simp only [hub_eq]
    cases hs : x.signbit <;> cases ht : t.signed <;> simp only [↓reduceIte, Bool.false_eq_true]
    · omega
    · omega
    · rw [← quotient_zero_integral x hmod]
      omega
    · omega
  · have hub_eq : upperBits T t = (T.fmt.bias + width t) * 2 ^ T.fmt.sb := by
      revert hbig_exp; cases T <;> cases t <;> decide
    have hlt_exp : width t ≤ T.fmt.emax - 1 - T.fmt.bias := by
      revert hbig_exp; cases T <;> cases t <;> decide
    have hq_lt := quotient_lt_pow_bits x (width t)
    have hq_le := quotient_le_pow_integral x (width t) hmod
    rw [← hub_eq] at hq_lt hq_le
    cases hs : x.signbit <;> cases ht : t.signed <;> simp only [↓reduceIte, Bool.false_eq_true]
    · rw [← hq_lt]; omega
    · rw [← hq_lt]; omega
    · rw [← quotient_zero_integral x hmod]; omega
    · rw [← hq_le]; omega

theorem toJInt_ofNat_natAbs (t : IntTy) (z : Int) (hz : 0 ≤ z) :
    (toJInt t (BitVec.ofNat t.bits z.natAbs)).val = wrapInt t z := by
  have : BitVec.ofNat t.bits z.natAbs = BitVec.ofInt t.bits z := by
    rw [← BitVec.ofInt_natCast, Int.natAbs_of_nonneg hz]
  rw [this, toJInt_ofInt_val]

theorem unsafe_trunc_eq_wrap (T : FTy) (t : IntTy) (x : FV T) (hfin : x.isfinite = true)
    (hin : t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max) :
    (unsafe_trunc t x).val = wrapInt t x.truncVal := by
  have htr := truncVal_parts x hfin
  cases t
  · simp [unsafe_trunc, unsafe_trunc_BitSigned64, fptosi, jlFptosi, hfin, toJInt_ofInt_val]
  · simp [unsafe_trunc, unsafe_trunc_BitSigned64, fptosi, jlFptosi, hfin, toJInt_ofInt_val]
  · simp [unsafe_trunc, unsafe_trunc_BitSigned64, fptosi, jlFptosi, hfin, toJInt_ofInt_val]
  · simp [unsafe_trunc, unsafe_trunc_BitSigned64, fptosi, jlFptosi, hfin, toJInt_ofInt_val]
  · -- .i128
    have hq : if x.signbit then quotient x ≤ 2 ^ 127 else quotient x < 2 ^ 127 := by
      revert hin; rw [htr]; cases x.signbit <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    have hwrap : wrapInt .i128 x.truncVal = x.truncVal :=
      wrapInt_of_inRange .i128 x.truncVal hin
    rw [hwrap, htr]
    cases T
    · obtain ⟨hfin32, hsign32, hq32⟩ := f32_of_f16_quotient x hfin
      have hq32' : if (Float32_Float16 x).signbit then quotient (Float32_Float16 x) ≤ 2 ^ 127
          else quotient (Float32_Float16 x) < 2 ^ 127 := by
        rw [hsign32, hq32]; exact hq
      change (unsafe_trunc_Int128_Float32 (Float32_Float16 x)).val = _
      rw [unsafe_trunc_i128_f32_val (Float32_Float16 x) hq32', hsign32, hq32]
    · exact unsafe_trunc_i128_f32_val x hq
    · exact unsafe_trunc_i128_f64_val x hq
  · simp only [unsafe_trunc, unsafe_trunc_BitUnsigned64, fptoui, jlFptoui, hfin, ↓reduceIte]
    exact toJInt_ofNat_natAbs .u8 x.truncVal hin.1
  · simp only [unsafe_trunc, unsafe_trunc_BitUnsigned64, fptoui, jlFptoui, hfin, ↓reduceIte]
    exact toJInt_ofNat_natAbs .u16 x.truncVal hin.1
  · simp only [unsafe_trunc, unsafe_trunc_BitUnsigned64, fptoui, jlFptoui, hfin, ↓reduceIte]
    exact toJInt_ofNat_natAbs .u32 x.truncVal hin.1
  · simp only [unsafe_trunc, unsafe_trunc_BitUnsigned64, fptoui, jlFptoui, hfin, ↓reduceIte]
    exact toJInt_ofNat_natAbs .u64 x.truncVal hin.1
  · -- .u128
    have hwrap : wrapInt .u128 x.truncVal = x.truncVal :=
      wrapInt_of_inRange .u128 x.truncVal hin
    have hq_eq : (quotient x : Int) = x.truncVal := by
      revert hin; rw [htr]; cases x.signbit <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    have hq_lt : quotient x < 2 ^ 128 := by
      revert hin; rw [htr]; cases x.signbit <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    rw [hwrap, ← hq_eq]
    cases T
    · obtain ⟨hfin32, -, hq32⟩ := f32_of_f16_quotient x hfin
      have he32 : (Float32_Float16 x).expField < 127 + 128 :=
        (quotient_lt_pow (Float32_Float16 x) 128).mp (by rw [hq32]; exact hq_lt)
      change (unsafe_trunc_UInt128_Float32 (Float32_Float16 x)).val = _
      rw [unsafe_trunc_u128_f32_val (Float32_Float16 x) he32, hq32]
    · have he32 : x.expField < 127 + 128 := (quotient_lt_pow x 128).mp hq_lt
      exact unsafe_trunc_u128_f32_val x he32
    · have he64 : x.expField < 1023 + 128 := (quotient_lt_pow x 128).mp hq_lt
      exact unsafe_trunc_u128_f64_val x he64

theorem round_ToZero_eq (T : FTy) (t : IntTy) (x : FV T) :
    round_ToZero t x =
      if x.isfinite && decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max) then
        .ok (JInt.wrap t x.truncVal)
      else .error (.inexactError "round") := by
  have hchk := trunc_checks T t x
  have hrng := trunc_range T t x
  unfold round_ToZero round_ToZero_small round_ToZero_large
  by_cases hc : (!t.signed || int.sizeofT t < T.bytes) = true
  · simp only [hc, ↓reduceIte] at hchk ⊢
    rw [hchk]
    by_cases hb : bitTruncValid T t x
    · obtain ⟨hfin, hin⟩ := hrng.mp hb
      simp only [decide_eq_true hb, hfin, decide_eq_true hin, Bool.true_and, ↓reduceIte]
      congr 1; apply Subtype.ext
      exact unsafe_trunc_eq_wrap T t x hfin hin
    · have hnot : (x.isfinite && decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max)) = false := by
        rw [Bool.and_eq_false_iff]
        by_cases hf : x.isfinite = true
        · right; rw [decide_eq_false_iff_not]; intro hin; exact hb (hrng.mpr ⟨hf, hin⟩)
        · left; exact Bool.eq_false_iff.mpr hf
      rw [hnot]; simp [decide_eq_false hb]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hchk ⊢
    rw [hchk]
    by_cases hb : bitTruncValid T t x
    · obtain ⟨hfin, hin⟩ := hrng.mp hb
      simp only [decide_eq_true hb, hfin, decide_eq_true hin, Bool.true_and, ↓reduceIte]
      congr 1; apply Subtype.ext
      exact unsafe_trunc_eq_wrap T t x hfin hin
    · have hnot : (x.isfinite && decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max)) = false := by
        rw [Bool.and_eq_false_iff]
        by_cases hf : x.isfinite = true
        · right; rw [decide_eq_false_iff_not]; intro hin; exact hb (hrng.mpr ⟨hf, hin⟩)
        · left; exact Bool.eq_false_iff.mpr hf
      rw [hnot]; simp [decide_eq_false hb]

theorem intOfFloat_eq (T : FTy) (t : IntTy) (x : FV T) :
    intOfFloat t x =
      if x.isinteger && decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max) then
        .ok (JInt.wrap t x.truncVal)
      else .error (.inexactError t.name) := by
  have hchk := int_checks T t x
  unfold intOfFloat intOfFloat_small intOfFloat_large isinteger_callee
  by_cases hc : (!t.signed || int.sizeofT t < T.bytes) = true
  · simp only [hc, ↓reduceIte] at hchk ⊢
    rw [hchk]
    cases hi : x.isinteger
    · simp
    · have hrng := int_range T t x hi
      have hfin : x.isfinite = true := by
        unfold Fl.isinteger at hi; revert hi; cases x.isfinite <;> simp
      by_cases hb : bitIntValid T t x
      · obtain ⟨-, hin⟩ := hrng.mp hb
        simp only [decide_eq_true hb, decide_eq_true hin, Bool.and_self, ↓reduceIte]
        congr 1; apply Subtype.ext
        exact unsafe_trunc_eq_wrap T t x hfin hin
      · have hnot : decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max) = false := by
          rw [decide_eq_false_iff_not]; intro hin; exact hb (hrng.mpr ⟨hfin, hin⟩)
        rw [hnot]; simp [decide_eq_false hb]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hchk ⊢
    rw [hchk]
    cases hi : x.isinteger
    · simp
    · have hrng := int_range T t x hi
      have hfin : x.isfinite = true := by
        unfold Fl.isinteger at hi; revert hi; cases x.isfinite <;> simp
      by_cases hb : bitIntValid T t x
      · obtain ⟨-, hin⟩ := hrng.mp hb
        simp only [decide_eq_true hb, decide_eq_true hin, Bool.and_self, ↓reduceIte]
        congr 1; apply Subtype.ext
        exact unsafe_trunc_eq_wrap T t x hfin hin
      · have hnot : decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max) = false := by
          rw [decide_eq_false_iff_not]; intro hin; exact hb (hrng.mpr ⟨hfin, hin⟩)
        rw [hnot]; simp [decide_eq_false hb]

end TruncProofs


/-! ## Proof-internal lemmas for `_nextfloat`, `nextfloat`, and `prevfloat` -/

open JuliaLean.base TruncProofs

namespace NextProofs

theorem ltSame_eq {t : IntTy} (x y : JInt t) : int.ltSame x y = decide (x.val < y.val) := by
  unfold int.ltSame
  cases h : t.signed
  · simp [int.lt_BitUnsigned, ult_int_eq h]
  · simp [int.lt_BitSigned, slt_int_eq h]

theorem leSame_eq {t : IntTy} (x y : JInt t) : int.leSame x y = decide (x.val ≤ y.val) := by
  unfold int.leSame
  cases h : t.signed
  · simp [int.le_BitUnsigned, ule_int_eq h]
  · simp [int.le_BitSigned, sle_int_eq h]

theorem ltPromote_eq {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) (y : JInt t) :
    int.ltPromote x y = decide (x.val < y.val) := by
  simp only [int.ltPromote, int.promoteSameSign, ltSame_eq, widenTo_val, widen_promote_left h,
    widen_promote_right h]

theorem lePromote_eq {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) (y : JInt t) :
    int.lePromote x y = decide (x.val ≤ y.val) := by
  simp only [int.lePromote, int.promoteSameSign, leSame_eq, widenTo_val, widen_promote_left h,
    widen_promote_right h]

theorem cmp_eq (op : {r : IntTy} → JInt r → JInt r → Bool) (R : Int → Int → Prop)
    [DecidableRel R] (hop : ∀ {r : IntTy} (a b : JInt r), op a b = decide (R a.val b.val))
    (hR : ∀ a b : Int, 0 ≤ a → b < 0 → ¬ R a b) {u s : IntTy} (hu : u.signed = false)
    (hs : s.signed = true) (x : JInt u) (y : JInt s) :
    int.cmp_BitUnsigned_BitSigned op x y = decide (R x.val y.val) := by
  have hx := x.property
  have hy := y.property
  unfold int.cmp_BitUnsigned_BitSigned
  split
  · rename_i h
    dsimp only
    have hr : s.min ≤ u.min ∧ u.max ≤ s.max := by
      revert h hu hs; cases u <;> cases s <;> decide
    rw [hop, widenTo_val, wrapInt_of_inRange s x.val ⟨by omega, by omega⟩]
  · rename_i h
    dsimp only
    have hr : s.max ≤ u.max ∧ s.max ≤ s.toUnsigned.max ∧ u.min = 0 ∧ s.toUnsigned.min = 0 := by
      revert h hu hs; cases u <;> cases s <;> decide
    rw [lePromote_eq (by cases s <;> simp_all [IntTy.signed]), hop, remT_val, unsigned_val]
    have h0 : (int.lit IntTy.i64 0).val = 0 := by decide
    rw [h0]
    by_cases hy0 : 0 ≤ y.val
    · rw [wrapInt_of_inRange s.toUnsigned y.val ⟨by omega, by omega⟩,
        wrapInt_of_inRange u y.val ⟨by omega, by omega⟩]
      simp [hy0]
    · have hu0 : 0 ≤ x.val := by omega
      simp [hy0, hR x.val y.val hu0 (by omega)]

theorem ltUnsignedSigned_eq {u s : IntTy} (hu : u.signed = false) (hs : s.signed = true)
    (x : JInt u) (y : JInt s) :
    int.lt_BitUnsigned_BitSigned x y = decide (x.val < y.val) :=
  cmp_eq int.ltSame (· < ·) ltSame_eq (by intros; omega) hu hs x y

theorem leUnsignedSigned_eq {u s : IntTy} (hu : u.signed = false) (hs : s.signed = true)
    (x : JInt u) (y : JInt s) :
    int.le_BitUnsigned_BitSigned x y = decide (x.val ≤ y.val) :=
  cmp_eq int.leSame (· ≤ ·) leSame_eq (by intros; omega) hu hs x y

theorem lt_int_eq {s t : IntTy} (x : JInt s) (y : JInt t) :
    int.lt x y = decide (x.val < y.val) := by
  unfold int.lt
  split
  · exact ltPromote_eq (by assumption) x y
  · split
    · rename_i h1 h2
      have hu : t.signed = false := by cases s <;> cases t <;> simp_all [IntTy.signed]
      rw [int.lt_BitSigned_BitUnsigned, leUnsignedSigned_eq hu h2]
      by_cases h : x.val < y.val <;> simp [h] <;> omega
    · exact ltUnsignedSigned_eq
        (by cases s <;> simp_all [IntTy.signed]) (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y

theorem isnegative_int_eq {t : IntTy} (d : JInt t) :
    isnegative_int d = decide (d.val < 0) := by
  unfold isnegative_int
  by_cases ht : t.signed = true
  · simp only [ht, ↓reduceIte]
    rw [lt_int_eq]
    rfl
  · have htu : t.signed = false := Bool.eq_false_iff.mpr ht
    have hd := d.property.1
    simp only [htu, Bool.false_eq_true, ↓reduceIte]
    symm; rw [decide_eq_false_iff_not]
    revert htu hd; cases t <;> simp [IntTy.signed, IntTy.min] <;> omega

theorem ispositive_int_eq {t : IntTy} (d : JInt t) :
    ispositive_int d = decide (0 < d.val) := by
  unfold ispositive_int
  rw [lt_int_eq]
  rfl

def infMag (F : FTy) : Nat := F.fmt.emax * 2 ^ F.fmt.sb
def signMask (F : FTy) : Nat := 2 ^ (F.fmt.eb + F.fmt.sb)

def encode (F : FTy) (s : Bool) (m : Nat) : FV F :=
  Fl.ofBits ((if s then signMask F else 0) + m)

def walk (F : FTy) (s d : Bool) (m n : Nat) : FV F :=
  if s != d then
    if m < n then encode F (!s) (min (n - m) (infMag F))
    else encode F s (m - n)
  else encode F s (min (m + n) (infMag F))

def nextSpec {F : FTy} (x : FV F) (d : Bool) (n : Nat) : FV F :=
  if x.isnan then x
  else walk F x.signbit d x.magnitude n

def iter {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iter f n (f x)

theorem infMag_lt_signMask (F : FTy) : infMag F < signMask F := by
  cases F <;> decide

theorem signMask_mul_two (F : FTy) : 2 * signMask F = 2 ^ F.fmt.width := by
  cases F <;> decide

theorem not_nan_mag {F : FTy} {x : FV F} (h : x.isnan = false) :
    x.magnitude ≤ infMag F := by
  have hn : ¬(F.fmt.emax * 2 ^ F.fmt.sb < x.magnitude) := by
    rw [← isnan_iff_mag]; simp [h]
  unfold infMag; omega

theorem tb_encode (F : FTy) (s : Bool) {m : Nat} (hm : m < signMask F) :
    (encode F s m).toBits = (if s then signMask F else 0) + m := by
  unfold encode
  rw [Fl.toBits_ofBits]
  have h2 := signMask_mul_two F
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> apply Nat.mod_eq_of_lt <;> omega

theorem mag_encode (F : FTy) (s : Bool) {m : Nat} (hm : m < signMask F) :
    (encode F s m).magnitude = m := by
  unfold Fl.magnitude
  rw [tb_encode F s hm]
  unfold signMask at hm ⊢
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_mod_left, Nat.mod_eq_of_lt hm]

theorem sign_encode (F : FTy) (s : Bool) {m : Nat} (hm : m < signMask F) :
    (encode F s m).signbit = s := by
  unfold Fl.signbit
  rw [tb_encode F s hm]
  have hpos : 0 < signMask F := by unfold signMask; exact Nat.two_pow_pos _
  unfold signMask at hm hpos ⊢
  cases s <;> simp [hm] <;> omega

theorem not_nan_encode (F : FTy) (s : Bool) {m : Nat} (hm : m ≤ infMag F) :
    (encode F s m).isnan = false := by
  have hlt : m < signMask F := Nat.lt_of_le_of_lt hm (infMag_lt_signMask F)
  rw [Bool.eq_false_iff, ne_eq, isnan_iff_mag, mag_encode F s hlt]
  unfold infMag at hm; omega

theorem encode_input {F : FTy} (x : FV F) :
    encode F x.signbit x.magnitude = x := by
  unfold encode signMask
  rw [← (Fl.bits_split x).1, Fl.ofBits_toBits]

theorem walk_large (F : FTy) (s d : Bool) {m n : Nat} (hm : m ≤ infMag F)
    (hn : 2 ^ F.fmt.width ≤ n) : walk F s d m n = encode F d (infMag F) := by
  have h1 := infMag_lt_signMask F
  have h2 := signMask_mul_two F
  have hmn : m < n := by omega
  have hleft : infMag F ≤ n - m := by omega
  have hright : infMag F ≤ m + n := by omega
  cases s <;> cases d <;>
    simp [walk, hmn, Nat.min_eq_right hleft, Nat.min_eq_right hright]

theorem fumax_val (F : FTy) :
    (reinterpret_Unsigned (inf_float F)).val = (infMag F : Int) := by
  cases F <;> decide

theorem fneg_eq {F : FTy} (f : FV F) :
    int.lt (reinterpret_Signed f) (int.lit .i64 0) = f.signbit := by
  rw [lt_int_eq, reinterpret_Signed_val]
  have hm : f.magnitude < 2 ^ (F.fmt.eb + F.fmt.sb) := (Fl.bits_split f).2
  have h0 : (int.lit .i64 0).val = 0 := rfl
  rw [h0]
  cases f.signbit <;>
    simp only [↓reduceIte, Bool.false_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] <;>
    omega

theorem fu_init_val {F : FTy} (f : FV F) :
    (int.remT F.uintTy (int.unsigned (int.band (reinterpret_Signed f) (int.typemax F.intTy)))).val =
      (f.magnitude : Int) := by
  have hpat_fi : pattern (reinterpret_Signed f) = f.toBits := by
    have hlt : f.toBits < 2 ^ F.intTy.bits := by
      have hw : F.intTy.bits = F.fmt.width := by cases F <;> rfl
      rw [hw]; exact f.bits.isLt
    have h_eq : reinterpret_Signed f = toJInt F.intTy (BitVec.ofNat F.intTy.bits f.toBits) := by
      cases F <;> rfl
    rw [h_eq, pattern_toJInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpat_max : pattern (int.typemax F.intTy) = 2 ^ (F.fmt.eb + F.fmt.sb) - 1 := by
    cases F <;> rfl
  have hpat_band : pattern (int.band (reinterpret_Signed f) (int.typemax F.intTy)) = f.magnitude := by
    rw [pattern_band, hpat_fi, hpat_max, nat_and_mask]
    rfl
  have hpat_rem : pattern (int.remT F.uintTy (int.unsigned (int.band (reinterpret_Signed f) (int.typemax F.intTy)))) =
      f.magnitude := by
    have hbits : F.uintTy.bits = F.intTy.toUnsigned.bits := by cases F <;> rfl
    rw [pattern_of_cong _ _ (remT_val F.uintTy _)]
    change ((int.unsigned (int.band (reinterpret_Signed f) (int.typemax F.intTy))).val %
      ((2 ^ F.uintTy.bits : Nat) : Int)).toNat = f.magnitude
    rw [hbits, ← pattern_cast, pattern_unsigned, hpat_band]; rfl
  have huns : F.uintTy.signed = false := by cases F <;> rfl
  rw [← val_of_unsigned_pattern huns, hpat_rem]

theorem reinterpret_bor_sign {F : FTy} (fneg : Bool) (fu : JInt F.uintTy) {m : Nat}
    (hfu : fu.val = (m : Int)) (hm : m < signMask F) :
    reinterpret_Float_Int F (if fneg then int.bor fu (sign_mask F) else fu) = encode F fneg m := by
  have huns : F.uintTy.signed = false := by cases F <;> rfl
  have hpat_fu : pattern fu = m := by
    have := val_of_unsigned_pattern huns fu
    omega
  have hpat_sm : pattern (sign_mask F) = 2 ^ (F.fmt.eb + F.fmt.sb) := by
    cases F <;> rfl
  have hpat_if : pattern (if fneg then int.bor fu (sign_mask F) else fu) =
      (if fneg then signMask F else 0) + m := by
    cases fneg
    · simp [hpat_fu]
    · simp only [↓reduceIte, pattern_bor, hpat_sm]; rw [hpat_fu]
      unfold signMask at hm ⊢
      rw [nat_or_pow m (F.fmt.eb + F.fmt.sb) hm, Nat.add_comm]
  have h_reinterpret : ∀ u : JInt F.uintTy, reinterpret_Float_Int F u = Fl.ofBits (pattern u) := by
    intro u
    unfold reinterpret_Float_Int bitcast_to_float jlBitcast
    rw [← pattern_fromJInt]
  rw [h_reinterpret, hpat_if]
  rfl

theorem nextfloat_core_eq {F : FTy} {t : IntTy} (f : FV F) (dneg : Bool) (da : JInt t)
    (hda : 0 ≤ da.val) :
    _nextfloat f dneg da = nextSpec f dneg da.val.toNat := by
  unfold _nextfloat nextSpec
  rw [isnan_IEEEFloat_eq]
  by_cases hnan : f.isnan = true
  · simp [hnan]
  have hnan' : f.isnan = false := Bool.eq_false_iff.mpr hnan
  simp only [hnan', Bool.false_eq_true, ↓reduceIte]
  rw [fneg_eq f]
  have hfu_init := fu_init_val f
  have hfumax := fumax_val F
  have hm_le : f.magnitude ≤ infMag F := not_nan_mag hnan'
  have hinf_lt : infMag F < signMask F := infMag_lt_signMask F
  have h2w : 2 * signMask F = 2 ^ F.fmt.width := signMask_mul_two F
  have hbits_w : F.uintTy.bits = F.fmt.width := by cases F <;> rfl
  have huns : F.uintTy.signed = false := by cases F <;> rfl
  have htypemax : (int.typemax F.uintTy).val = (2 ^ F.fmt.width - 1 : Nat) := by
    cases F <;> decide
  have hlt_max : int.lt (int.typemax F.uintTy) da = decide (2 ^ F.fmt.width ≤ da.val.toNat) := by
    rw [lt_int_eq, htypemax]
    have hpos_w : 0 < 2 ^ F.fmt.width := Nat.two_pow_pos _
    apply decide_eq_decide.mpr; omega
  rw [hlt_max]
  generalize hfu0 : int.remT F.uintTy (int.unsigned (int.band (reinterpret_Signed f) (int.typemax F.intTy))) = fu0 at hfu_init
  generalize hfumax0 : reinterpret_Unsigned (inf_float F) = fumax at hfumax
  by_cases hlarge : 2 ^ F.fmt.width ≤ da.val.toNat
  · simp only [decide_eq_true hlarge, ↓reduceIte]
    rw [walk_large F f.signbit dneg hm_le hlarge]
    exact reinterpret_bor_sign dneg fumax hfumax hinf_lt
  · simp only [decide_eq_false hlarge, Bool.false_eq_true, ↓reduceIte]
    have hda_lt : da.val.toNat < 2 ^ F.fmt.width := by omega
    let n := da.val.toNat
    let m := f.magnitude
    have hda_eq : da.val = (n : Int) := by omega
    have hdu_val : (int.remT F.uintTy da).val = (n : Int) := by
      rw [remT_val, hda_eq]
      apply wrapInt_of_inRange
      revert hda_lt
      cases F <;> simp [FTy.uintTy, FTy.fmt, half, single, double, Fmt.width,
        IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    generalize hdu0 : int.remT F.uintTy da = du at hdu_val
    have hxor : xor f.signbit dneg = (f.signbit != dneg) := by
      cases f.signbit <;> cases dneg <;> rfl
    rw [hxor]
    have h_sub : ∀ (a b : JInt F.uintTy) (A B : Nat),
        a.val = (A : Int) → b.val = (B : Int) → B ≤ A → A < 2 ^ F.fmt.width →
        (int.sub a b).val = ((A - B : Nat) : Int) := by
      intro a b A B ha hb hle hA
      rw [sub_int_val, ha, hb, ← Int.natCast_sub hle]
      apply wrapInt_of_inRange
      revert hle hA
      cases F <;> simp [FTy.uintTy, FTy.fmt, half, single, double, Fmt.width,
        IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    have h_add : ∀ (a b : JInt F.uintTy) (A B : Nat),
        a.val = (A : Int) → b.val = (B : Int) → A + B < 2 ^ F.fmt.width →
        (int.add a b).val = ((A + B : Nat) : Int) := by
      intro a b A B ha hb hAB
      rw [add_int_val, ha, hb, ← Int.natCast_add]
      apply wrapInt_of_inRange
      revert hAB
      cases F <;> simp [FTy.uintTy, FTy.fmt, half, single, double, Fmt.width,
        IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    unfold walk
    by_cases hdir : (f.signbit != dneg) = true
    · simp only [hdir, ↓reduceIte]
      have hcmp1 : int.lt_BitUnsigned fu0 du = decide (m < n) := by
        rw [int.lt_BitUnsigned, ult_int_eq huns, hfu_init, hdu_val]
        apply decide_eq_decide.mpr; omega
      rw [hcmp1]
      by_cases hmn : m < n
      · have hmn' : f.magnitude < da.val.toNat := hmn
        simp only [decide_eq_true hmn, hmn', ↓reduceIte]
        have hdiff := h_sub du fu0 n m hdu_val hfu_init (by omega) hda_lt
        have hcmp2 : int.lt_BitUnsigned (int.sub du fu0) fumax = decide (n - m < infMag F) := by
          rw [int.lt_BitUnsigned, ult_int_eq huns, hdiff, hfumax]
          apply decide_eq_decide.mpr; omega
        rw [hcmp2, int.ifelse]
        by_cases hsat : n - m < infMag F
        · simp only [decide_eq_true hsat, ↓reduceIte]
          rw [show da.val.toNat - f.magnitude = n - m from rfl, Nat.min_eq_left (Nat.le_of_lt hsat)]
          exact reinterpret_bor_sign (!f.signbit) (int.sub du fu0) hdiff (by omega)
        · simp only [decide_eq_false hsat, Bool.false_eq_true, ↓reduceIte]
          rw [show da.val.toNat - f.magnitude = n - m from rfl, Nat.min_eq_right (by omega : infMag F ≤ n - m)]
          exact reinterpret_bor_sign (!f.signbit) fumax hfumax hinf_lt
      · have hmn' : ¬(f.magnitude < da.val.toNat) := hmn
        simp only [decide_eq_false hmn, hmn', Bool.false_eq_true, ↓reduceIte]
        have hdiff := h_sub fu0 du m n hfu_init hdu_val (by omega) (by omega)
        exact reinterpret_bor_sign f.signbit (int.sub fu0 du) hdiff (by omega)
    · simp only [hdir, Bool.false_eq_true, ↓reduceIte]
      have hdiff := h_sub fumax fu0 (infMag F) m hfumax hfu_init hm_le (by omega)
      have hcmp : int.lt_BitUnsigned (int.sub fumax fu0) du = decide (infMag F - m < n) := by
        rw [int.lt_BitUnsigned, ult_int_eq huns, hdiff, hdu_val]
        apply decide_eq_decide.mpr; omega
      rw [hcmp]
      by_cases hsat : infMag F - m < n
      · simp only [decide_eq_true hsat, ↓reduceIte]
        rw [Nat.min_eq_right (by omega : infMag F ≤ m + n)]
        exact reinterpret_bor_sign f.signbit fumax hfumax hinf_lt
      · simp only [decide_eq_false hsat, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.min_eq_left (by omega : m + n ≤ infMag F)]
        have hsum := h_add fu0 du m n hfu_init hdu_val (by omega)
        exact reinterpret_bor_sign f.signbit (int.add fu0 du) hsum (by omega)

theorem spec_encode (F : FTy) (s d : Bool) {m : Nat} (n : Nat) (hm : m ≤ infMag F) :
    nextSpec (encode F s m) d n = walk F s d m n := by
  have hlt : m < signMask F := Nat.lt_of_le_of_lt hm (infMag_lt_signMask F)
  simp only [nextSpec, not_nan_encode F s hm, Bool.false_eq_true, ↓reduceIte,
    sign_encode F s hlt, mag_encode F s hlt]

theorem min_add (F : FTy) (m n : Nat) :
    min (min (m + 1) (infMag F) + n) (infMag F) = min (m + (n + 1)) (infMag F) := by
  simp only [Nat.min_def]
  split <;> split <;> split <;> omega

theorem walk_step (F : FTy) (s d : Bool) {m : Nat} (n : Nat) (hm : m ≤ infMag F) :
    nextSpec (walk F s d m 1) d n = walk F s d m (n + 1) := by
  have h1_le : 1 ≤ infMag F := by cases F <;> decide
  by_cases hdir : s = d
  · subst d
    have heq : walk F s s m 1 = encode F s (min (m + 1) (infMag F)) := by simp [walk]
    rw [heq, spec_encode F s s n (Nat.min_le_right _ _)]
    simpa only [walk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using
      congrArg (encode F s) (min_add F m n)
  · have hdiff : (s != d) = true := by simp [hdir]
    have hneg : (!s) = d := by cases s <;> cases d <;> simp_all
    by_cases hz : m = 0
    · subst m
      have heq : walk F s d 0 1 = encode F d 1 := by
        simp [walk, hdiff, hneg, Nat.min_eq_left h1_le]
      rw [heq, spec_encode F d d n h1_le]
      simp [walk, hdiff, hneg, Nat.add_comm]
    · have heq : walk F s d m 1 = encode F s (m - 1) := by
        simp [walk, hdiff, show ¬(m < 1) by omega]
      rw [heq, spec_encode F s d n (by omega)]
      simp only [walk, hdiff, ↓reduceIte]
      by_cases hc : m - 1 < n
      · have hc' : m < n + 1 := by omega
        simp only [hc, hc', ↓reduceIte]
        have he : n - (m - 1) = n + 1 - m := by omega
        rw [he]
      · have hc' : ¬(m < n + 1) := by omega
        simp only [hc, hc', ↓reduceIte]
        have he : m - 1 - n = m - (n + 1) := by omega
        rw [he]

theorem spec_zero {F : FTy} (x : FV F) (d : Bool) : nextSpec x d 0 = x := by
  by_cases hx : x.isnan = true
  · simp [nextSpec, hx]
  have hx' : x.isnan = false := Bool.eq_false_iff.mpr hx
  have hm := not_nan_mag hx'
  have hw : walk F x.signbit d x.magnitude 0 = encode F x.signbit x.magnitude := by
    cases x.signbit <;> cases d <;> simp [walk, Nat.min_eq_left hm]
  simp only [nextSpec, hx', Bool.false_eq_true, ↓reduceIte, hw, encode_input]

theorem spec_step {F : FTy} (x : FV F) (d : Bool) (n : Nat) :
    nextSpec (nextSpec x d 1) d n = nextSpec x d (n + 1) := by
  by_cases hx : x.isnan = true
  · simp [nextSpec, hx]
  have hx' : x.isnan = false := Bool.eq_false_iff.mpr hx
  simp only [nextSpec, hx', Bool.false_eq_true, ↓reduceIte]
  exact walk_step F _ _ n (not_nan_mag hx')

theorem spec_iter {F : FTy} (d : Bool) (n : Nat) (x : FV F) :
    nextSpec x d n = iter (fun y => nextSpec y d 1) n x := by
  induction n generalizing x with
  | zero => exact spec_zero x d
  | succ n ih =>
    change nextSpec x d (n + 1) = iter (fun y => nextSpec y d 1) n (nextSpec x d 1)
    rw [← ih]
    exact (spec_step x d n).symm

theorem nextfloat_step_eq {F : FTy} {t : IntTy} (x : FV F) (d : JInt t) :
    nextfloat_step x d = nextSpec x (decide (d.val < 0)) d.val.natAbs := by
  unfold nextfloat_step nextfloat_AbstractFloat
  have hu : (uabs d).val = (d.val.natAbs : Int) := (uabsExact_proven t d).1
  rw [isnegative_int_eq, nextfloat_core_eq x _ (uabs d) (by omega), hu]
  simp

theorem prevfloat_step_eq {F : FTy} {t : IntTy} (x : FV F) (d : JInt t) :
    prevfloat_step x d = nextSpec x (decide (0 < d.val)) d.val.natAbs := by
  unfold prevfloat_step prevfloat_AbstractFloat
  have hu : (uabs d).val = (d.val.natAbs : Int) := (uabsExact_proven t d).1
  rw [ispositive_int_eq, nextfloat_core_eq x _ (uabs d) (by omega), hu]
  simp

theorem nextfloat_eq {F : FTy} (x : FV F) :
    nextfloat x = nextSpec x false 1 := by
  unfold nextfloat nextfloat_AbstractFloat_one
  rw [nextfloat_step_eq]
  rfl

theorem prevfloat_eq {F : FTy} (x : FV F) :
    prevfloat x = nextSpec x true 1 := by
  unfold prevfloat prevfloat_AbstractFloat_one
  rw [nextfloat_step_eq]
  rfl

theorem nextfloat_step_iter {F : FTy} {t : IntTy} (x : FV F) (d : JInt t) :
    nextfloat_step x d =
      if 0 ≤ d.val then iter nextfloat d.val.natAbs x
      else iter prevfloat d.val.natAbs x := by
  rw [nextfloat_step_eq]
  have hnext : (nextfloat : FV F → FV F) = (fun y => nextSpec y false 1) :=
    funext nextfloat_eq
  have hprev : (prevfloat : FV F → FV F) = (fun y => nextSpec y true 1) :=
    funext prevfloat_eq
  by_cases hd : 0 ≤ d.val
  · have hlt : decide (d.val < 0) = false := decide_eq_false (by omega)
    simp only [hlt, hd, ↓reduceIte, hnext, spec_iter false d.val.natAbs x]
  · have hlt : decide (d.val < 0) = true := decide_eq_true (by omega)
    simp only [hlt, hd, ↓reduceIte, hprev, spec_iter true d.val.natAbs x]

theorem prevfloat_step_iter {F : FTy} {t : IntTy} (x : FV F) (d : JInt t) :
    prevfloat_step x d =
      if 0 ≤ d.val then iter prevfloat d.val.natAbs x
      else iter nextfloat d.val.natAbs x := by
  rw [prevfloat_step_eq]
  have hnext : (nextfloat : FV F → FV F) = (fun y => nextSpec y false 1) :=
    funext nextfloat_eq
  have hprev : (prevfloat : FV F → FV F) = (fun y => nextSpec y true 1) :=
    funext prevfloat_eq
  by_cases hd : 0 ≤ d.val
  · by_cases h0 : d.val = 0
    · simp [h0, iter, spec_zero]
    · have hgt : decide (0 < d.val) = true := decide_eq_true (by omega)
      simp only [hgt, hd, ↓reduceIte, hprev, spec_iter true d.val.natAbs x]
  · have hgt : decide (0 < d.val) = false := decide_eq_false (by omega)
    simp only [hgt, hd, ↓reduceIte, hnext, spec_iter false d.val.natAbs x]

theorem fl_lt_parts {F : FTy} (x y : FV F) (hx : x.isnan = false) (hy : y.isnan = false) :
    lt_IEEEFloat x y =
      if x.magnitude == 0 && y.magnitude == 0 then false
      else if x.signbit != y.signbit then x.signbit
      else if x.signbit then decide (y.magnitude < x.magnitude)
      else decide (x.magnitude < y.magnitude) := by
  rw [lt_IEEEFloat_eq]
  obtain ⟨hbx, _⟩ := Fl.bits_split x
  obtain ⟨hby, _⟩ := Fl.bits_split y
  have hzx : x.iszero = (x.magnitude == 0) := rfl
  have hzy : y.iszero = (y.magnitude == 0) := rfl
  unfold Fl.lt
  rw [hx, hy, hzx, hzy, hbx, hby]
  cases x.signbit <;> cases y.signbit <;> cases (x.magnitude == 0) <;> cases (y.magnitude == 0) <;>
    simp <;> omega

theorem nextfloat_order_adj {F : FTy} (x : FV F) (hx : x.isnan = false)
    (hmax : ¬(x.signbit = false ∧ x.magnitude = infMag F)) :
    lt_IEEEFloat x (nextfloat x) = true ∧
    ∀ y : FV F, ¬(lt_IEEEFloat x y = true ∧ lt_IEEEFloat y (nextfloat x) = true) := by
  have hm : x.magnitude ≤ infMag F := not_nan_mag hx
  have hinf_lt : infMag F < signMask F := infMag_lt_signMask F
  have h1_le : 1 ≤ infMag F := by cases F <;> decide
  rw [nextfloat_eq]
  simp only [nextSpec, hx, Bool.false_eq_true, ↓reduceIte, walk]
  cases hs : x.signbit
  · have hlt_inf : x.magnitude < infMag F := by simp [hs] at hmax; omega
    simp only [Bool.false_bne, Bool.false_eq_true, ↓reduceIte,
      Nat.min_eq_left (by omega : x.magnitude + 1 ≤ infMag F)]
    have hm1_lt : x.magnitude + 1 < signMask F := by omega
    have hnan_n : (encode F false (x.magnitude + 1)).isnan = false :=
      not_nan_encode F false (by omega)
    have hsign_n : (encode F false (x.magnitude + 1)).signbit = false :=
      sign_encode F false hm1_lt
    have hmag_n : (encode F false (x.magnitude + 1)).magnitude = x.magnitude + 1 :=
      mag_encode F false hm1_lt
    have hz1 : (x.magnitude + 1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    refine ⟨?_, ?_⟩
    · rw [fl_lt_parts x _ hx hnan_n, hs, hsign_n, hmag_n, hz1]
      simp
    · intro y ⟨h1, h2⟩
      by_cases hyn : y.isnan = true
      · rw [lt_IEEEFloat_eq] at h1; unfold Fl.lt at h1; simp [hyn] at h1
      · have hyn' : y.isnan = false := Bool.eq_false_iff.mpr hyn
        rw [fl_lt_parts x y hx hyn', hs] at h1
        rw [fl_lt_parts y _ hyn' hnan_n, hsign_n, hmag_n, hz1] at h2
        revert h1 h2
        cases y.signbit <;>
          simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.and_false] <;>
          split <;> simp <;> omega
  · simp only [Bool.true_bne, Bool.not_false, ↓reduceIte]
    by_cases hz : x.magnitude = 0
    · simp only [hz, Nat.zero_lt_one, ↓reduceIte, Nat.sub_zero, Bool.not_true,
        Nat.min_eq_left h1_le]
      have h1_lt : 1 < signMask F := by omega
      have hnan_n : (encode F false 1).isnan = false := not_nan_encode F false h1_le
      have hsign_n : (encode F false 1).signbit = false := sign_encode F false h1_lt
      have hmag_n : (encode F false 1).magnitude = 1 := mag_encode F false h1_lt
      refine ⟨?_, ?_⟩
      · rw [fl_lt_parts x _ hx hnan_n, hs, hz, hsign_n, hmag_n]; decide
      · intro y ⟨h1, h2⟩
        by_cases hyn : y.isnan = true
        · rw [lt_IEEEFloat_eq] at h1; unfold Fl.lt at h1; simp [hyn] at h1
        · have hyn' : y.isnan = false := Bool.eq_false_iff.mpr hyn
          rw [fl_lt_parts x y hx hyn', hs, hz] at h1
          rw [fl_lt_parts y _ hyn' hnan_n, hsign_n, hmag_n] at h2
          revert h1 h2
          cases y.signbit <;>
            simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, beq_self_eq_true,
              show (1 == 0) = false by decide, Bool.and_false, Bool.true_and, beq_iff_eq] <;>
            split <;> simp <;> omega
    · have hnot_lt : ¬(x.magnitude < 1) := by omega
      simp only [hnot_lt, ↓reduceIte]
      have hm1_lt : x.magnitude - 1 < signMask F := by omega
      have hnan_n : (encode F true (x.magnitude - 1)).isnan = false :=
        not_nan_encode F true (by omega)
      have hsign_n : (encode F true (x.magnitude - 1)).signbit = true :=
        sign_encode F true hm1_lt
      have hmag_n : (encode F true (x.magnitude - 1)).magnitude = x.magnitude - 1 :=
        mag_encode F true hm1_lt
      have hzx : (x.magnitude == 0) = false := beq_eq_false_iff_ne.mpr hz
      refine ⟨?_, ?_⟩
      · rw [fl_lt_parts x _ hx hnan_n, hs, hsign_n, hmag_n, hzx]
        simp; omega
      · intro y ⟨h1, h2⟩
        by_cases hyn : y.isnan = true
        · rw [lt_IEEEFloat_eq] at h1; unfold Fl.lt at h1; simp [hyn] at h1
        · have hyn' : y.isnan = false := Bool.eq_false_iff.mpr hyn
          rw [fl_lt_parts x y hx hyn', hs, hzx] at h1
          rw [fl_lt_parts y _ hyn' hnan_n, hsign_n, hmag_n] at h2
          revert h1 h2
          cases y.signbit <;>
            simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.false_and] <;>
            split <;> simp <;> omega

theorem prevfloat_order_adj {F : FTy} (x : FV F) (hx : x.isnan = false)
    (hmin : ¬(x.signbit = true ∧ x.magnitude = infMag F)) :
    lt_IEEEFloat (prevfloat x) x = true ∧
    ∀ y : FV F, ¬(lt_IEEEFloat (prevfloat x) y = true ∧ lt_IEEEFloat y x = true) := by
  have hm : x.magnitude ≤ infMag F := not_nan_mag hx
  have hinf_lt : infMag F < signMask F := infMag_lt_signMask F
  have h1_le : 1 ≤ infMag F := by cases F <;> decide
  rw [prevfloat_eq]
  simp only [nextSpec, hx, Bool.false_eq_true, ↓reduceIte, walk]
  cases hs : x.signbit
  · simp only [Bool.false_bne, ↓reduceIte]
    by_cases hz : x.magnitude = 0
    · simp only [hz, Nat.zero_lt_one, ↓reduceIte, Nat.sub_zero, Bool.not_false,
        Nat.min_eq_left h1_le]
      have h1_lt : 1 < signMask F := by omega
      have hnan_n : (encode F true 1).isnan = false := not_nan_encode F true h1_le
      have hsign_n : (encode F true 1).signbit = true := sign_encode F true h1_lt
      have hmag_n : (encode F true 1).magnitude = 1 := mag_encode F true h1_lt
      refine ⟨?_, ?_⟩
      · rw [fl_lt_parts _ x hnan_n hx, hs, hz, hsign_n, hmag_n]; decide
      · intro y ⟨h1, h2⟩
        by_cases hyn : y.isnan = true
        · rw [lt_IEEEFloat_eq] at h1; unfold Fl.lt at h1; simp [hyn] at h1
        · have hyn' : y.isnan = false := Bool.eq_false_iff.mpr hyn
          rw [fl_lt_parts _ y hnan_n hyn', hsign_n, hmag_n] at h1
          rw [fl_lt_parts y x hyn' hx, hs, hz] at h2
          revert h1 h2
          cases y.signbit <;>
            simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, beq_self_eq_true,
              show (1 == 0) = false by decide, Bool.false_and, Bool.and_true, beq_iff_eq] <;>
            split <;> simp <;> omega
    · have hnot_lt : ¬(x.magnitude < 1) := by omega
      simp only [hnot_lt, ↓reduceIte]
      have hm1_lt : x.magnitude - 1 < signMask F := by omega
      have hnan_n : (encode F false (x.magnitude - 1)).isnan = false :=
        not_nan_encode F false (by omega)
      have hsign_n : (encode F false (x.magnitude - 1)).signbit = false :=
        sign_encode F false hm1_lt
      have hmag_n : (encode F false (x.magnitude - 1)).magnitude = x.magnitude - 1 :=
        mag_encode F false hm1_lt
      have hzx : (x.magnitude == 0) = false := beq_eq_false_iff_ne.mpr hz
      refine ⟨?_, ?_⟩
      · rw [fl_lt_parts _ x hnan_n hx, hs, hsign_n, hmag_n, hzx]
        simp [Bool.and_false]; omega
      · intro y ⟨h1, h2⟩
        by_cases hyn : y.isnan = true
        · rw [lt_IEEEFloat_eq] at h1; unfold Fl.lt at h1; simp [hyn] at h1
        · have hyn' : y.isnan = false := Bool.eq_false_iff.mpr hyn
          rw [fl_lt_parts _ y hnan_n hyn', hsign_n, hmag_n] at h1
          rw [fl_lt_parts y x hyn' hx, hs, hzx] at h2
          revert h1 h2
          cases y.signbit <;>
            simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.and_false] <;>
            split <;> simp <;> omega
  · have hlt_inf : x.magnitude < infMag F := by simp [hs] at hmin; omega
    simp only [Bool.true_bne, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Nat.min_eq_left (by omega : x.magnitude + 1 ≤ infMag F)]
    have hm1_lt : x.magnitude + 1 < signMask F := by omega
    have hnan_n : (encode F true (x.magnitude + 1)).isnan = false :=
      not_nan_encode F true (by omega)
    have hsign_n : (encode F true (x.magnitude + 1)).signbit = true :=
      sign_encode F true hm1_lt
    have hmag_n : (encode F true (x.magnitude + 1)).magnitude = x.magnitude + 1 :=
      mag_encode F true hm1_lt
    have hz1 : (x.magnitude + 1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
    refine ⟨?_, ?_⟩
    · rw [fl_lt_parts _ x hnan_n hx, hs, hsign_n, hmag_n, hz1]
      simp
    · intro y ⟨h1, h2⟩
      by_cases hyn : y.isnan = true
      · rw [lt_IEEEFloat_eq] at h1; unfold Fl.lt at h1; simp [hyn] at h1
      · have hyn' : y.isnan = false := Bool.eq_false_iff.mpr hyn
        rw [fl_lt_parts _ y hnan_n hyn', hsign_n, hmag_n, hz1] at h1
        rw [fl_lt_parts y x hyn' hx, hs] at h2
        revert h1 h2
        cases y.signbit <;>
          simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.false_and] <;>
          split <;> simp <;> omega

end NextProofs


theorem nat_or_mul_pow (a b k : Nat) (hr : a < 2 ^ k) :
    a ||| b * 2 ^ k = a + b * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  rcases Nat.lt_or_ge i k with hlt | hge
  · have h1 : (b * 2 ^ k).testBit i = false := by
      have hm : (b * 2 ^ k) % 2 ^ k = 0 := Nat.mul_mod_left b (2 ^ k)
      have htb := Nat.testBit_mod_two_pow (b * 2 ^ k) k i
      rw [hm, decide_eq_true hlt, Bool.true_and, Nat.zero_testBit] at htb
      exact htb.symm
    have h2 : (a + b * 2 ^ k).testBit i = a.testBit i := by
      have hm : (a + b * 2 ^ k) % 2 ^ k = a := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      have htb := Nat.testBit_mod_two_pow (a + b * 2 ^ k) k i
      rw [hm, decide_eq_true hlt, Bool.true_and] at htb
      exact htb.symm
    rw [h1, h2, Bool.or_false]
  · have h1 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hge))
    have hi : i = (i - k) + k := (Nat.sub_add_cancel hge).symm
    rw [h1, Bool.false_or, hi, Nat.testBit_add, Nat.testBit_add,
      Nat.mul_div_cancel _ (Nat.two_pow_pos k),
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hr, Nat.zero_add]

theorem nat_and_shiftRight (a b k : Nat) :
    (a &&& b) / 2 ^ k = (a / 2 ^ k) &&& (b / 2 ^ k) := by
  simp only [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib]

theorem binop_bor_same (t : IntTy) (a b : JInt t) :
    int.remT t (int.binop int.bor a b) = int.bor a b := by
  cases t <;>
    simp [int.remT, int.rem_same, int.binop, IntTy.promote, IntTy.signed]

theorem ieee754_representation_pack (F : FTy) (s : Bool)
    (e m : JInt F.uintTy)
    (he : e.val.toNat < 2 ^ F.fmt.eb)
    (hm : m.val.toNat < 2 ^ F.fmt.sb) :
    reinterpret_Float_Int F (ieee754_representation F s e m) =
      Fl.pack s e.val.toNat m.val.toNat := by
  have huns : F.uintTy.signed = false := by cases F <;> rfl
  have hbw : F.uintTy.bits = F.fmt.width := by cases F <;> rfl
  have hpat_e : pattern e = e.val.toNat := by
    have := val_of_unsigned_pattern huns e; omega
  have hpat_m : pattern m = m.val.toNat := by
    have := val_of_unsigned_pattern huns m; omega
  have hpat_s_eb : pattern (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) =
      (if s then 1 else 0) * 2 ^ F.fmt.eb := by
    cases F <;> cases s <;> decide
  have hpat_se : pattern (int.bor (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) e) =
      e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb := by
    rw [pattern_bor, hpat_s_eb, hpat_e, Nat.or_comm, nat_or_mul_pow _ _ _ he]
  have hsb_val : (significand_bits F).val = (F.fmt.sb : Int) ∧ (significand_bits F).val.toNat = F.fmt.sb := by
    cases F <;> decide
  have hse_lt : (e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb) * 2 ^ F.fmt.sb < 2 ^ F.uintTy.bits := by
    rw [hbw, Fmt.width_pow, Nat.pow_add]
    cases s <;> simp [Nat.add_mul] <;>
      have := Nat.mul_lt_mul_of_pos_right he (Nat.two_pow_pos F.fmt.sb) <;> omega
  have hpat_shl : pattern (int.shl_Int (int.bor (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) e)
      (significand_bits F)) =
      (e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb) * 2 ^ F.fmt.sb := by
    rw [pattern_shl_Int _ _ (by omega), hpat_se, hsb_val.2, Nat.mod_eq_of_lt hse_lt]
  have hpat_all : pattern (ieee754_representation F s e m) =
      (if s then 2 ^ (F.fmt.eb + F.fmt.sb) else 0) + (e.val.toNat * 2 ^ F.fmt.sb + m.val.toNat) := by
    dsimp only [ieee754_representation]
    rw [binop_bor_same, binop_bor_same, pattern_bor, hpat_shl, hpat_m, Nat.or_comm, nat_or_mul_pow _ _ _ hm]
    rw [Nat.pow_add]
    cases s <;> simp [Nat.add_mul] <;> omega
  unfold reinterpret_Float_Int bitcast_to_float jlBitcast Fl.pack
  rw [← pattern_fromJInt, hpat_all]

theorem finishFloat_eq {T : FTy} (v : FV T) : finishFloat v = v := by
  unfold finishFloat
  have : (T.fmt == bfloat) = false := by cases T <;> decide
  rw [this]; rfl

theorem quietFloat_isnan {T : FTy} (x : FV T) (hx : x.isnan = true) :
    (quietFloat x).isnan = true := by
  have hmag_gt : T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude := (isnan_iff_mag x).mp hx
  rw [isnan_iff_mag]
  unfold quietFloat Fl.magnitude
  change ((x.toBits ||| 2 ^ (T.fmt.sb - 1)) % 2 ^ T.fmt.width) % 2 ^ (T.fmt.eb + T.fmt.sb) > _
  have h1 := x.bits.isLt
  have h2 : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.width := by
    apply Nat.pow_lt_pow_right (by decide); unfold Fmt.width; omega
  have hor_lt : (x.toBits ||| 2 ^ (T.fmt.sb - 1)) < 2 ^ T.fmt.width :=
    Nat.or_lt_two_pow h1 h2
  rw [Nat.mod_eq_of_lt hor_lt]
  have hmod_or : (x.toBits ||| 2 ^ (T.fmt.sb - 1)) % 2 ^ (T.fmt.eb + T.fmt.sb) =
      x.magnitude ||| 2 ^ (T.fmt.sb - 1) := by
    apply Nat.eq_of_testBit_eq; intro i
    have hlt_sb : T.fmt.sb - 1 < T.fmt.eb + T.fmt.sb := by
      have : 0 < T.fmt.sb := by cases T <;> decide
      omega
    have hpow_lt : 2 ^ (T.fmt.sb - 1) < 2 ^ (T.fmt.eb + T.fmt.sb) :=
      Nat.pow_lt_pow_right (by decide) hlt_sb
    rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_or]
    unfold Fl.magnitude
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < T.fmt.eb + T.fmt.sb
    · simp [hi]
    · have : (2 ^ (T.fmt.sb - 1)).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hpow_lt (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, this]
  rw [hmod_or]
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hP := Nat.two_pow_pos T.fmt.sb
  have hexp : x.expField = T.fmt.emax := by
    unfold Fl.isnan at hx; simp only [Bool.and_eq_true, beq_iff_eq] at hx; exact hx.1
  have hpow_sb : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.sb := by cases T <;> decide
  have hor_split : (x.magnitude ||| 2 ^ (T.fmt.sb - 1)) =
      (x.frac ||| 2 ^ (T.fmt.sb - 1)) + T.fmt.emax * 2 ^ T.fmt.sb := by
    rw [hm, hexp, Nat.add_comm, ← nat_or_mul_pow _ _ _ hf, Nat.or_assoc,
      Nat.or_comm (T.fmt.emax * 2 ^ T.fmt.sb), ← Nat.or_assoc,
      nat_or_mul_pow _ _ _ (Nat.or_lt_two_pow hf hpow_sb)]
  have hpos_or : 0 < (x.frac ||| 2 ^ (T.fmt.sb - 1)) := by
    apply Classical.byContradiction; intro hle
    have h0 : (x.frac ||| 2 ^ (T.fmt.sb - 1)) = 0 := by omega
    have htb := congrArg (fun n : Nat => n.testBit (T.fmt.sb - 1)) h0
    simp [Nat.testBit_or] at htb
  omega

theorem isinf_IEEEFloat_eq {T : FTy} (x : FV T) :
    isinf_IEEEFloat x = x.isinf := by
  unfold isinf_IEEEFloat egal_float abs_IEEEFloat abs_float jlAbsFloat unaryFloat oftype_float inf_float
  rw [finishFloat_eq]
  have hinf_bits : (Fl.inf false : FV T).toBits = T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> decide
  have habs_bits : ∀ y : FV T, (Fl.ofBits y.magnitude : FV T).toBits = y.magnitude := by
    intro y
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt (by have := (Fl.bits_split y).2; rw [Fmt.width_pow]; omega)]
  rw [hinf_bits, habs_bits]
  by_cases hnan : x.isnan = true
  · have hnot_inf : x.isinf = false := by
      unfold Fl.isnan at hnan; unfold Fl.isinf
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hnan
      simp [hnan.1, hnan.2]
    rw [hnot_inf]
    have hq_nan : (if T.fmt == half && x.isnan then quietFloat x else x).isnan = true := by
      split
      · exact quietFloat_isnan x hnan
      · exact hnan
    have hm_gt : T.fmt.emax * 2 ^ T.fmt.sb < (if T.fmt == half && x.isnan then quietFloat x else x).magnitude :=
      (isnan_iff_mag _).mp hq_nan
    rw [beq_eq_false_iff_ne]; omega
  · have hnan' : x.isnan = false := Bool.eq_false_iff.mpr hnan
    simp only [hnan', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hm, hf⟩ := mag_decomp x
    have hP := Nat.two_pow_pos T.fmt.sb
    rw [hm]
    unfold Fl.isinf
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h
      have he : x.expField = T.fmt.emax := by
        rcases Nat.lt_trichotomy x.expField T.fmt.emax with hlt | h_eq | hgt
        · have : (x.expField + 1) * 2 ^ T.fmt.sb ≤ T.fmt.emax * 2 ^ T.fmt.sb :=
            Nat.mul_le_mul_right _ hlt
          rw [Nat.succ_mul] at this; omega
        · exact h_eq
        · have : (T.fmt.emax + 1) * 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb :=
            Nat.mul_le_mul_right _ hgt
          rw [Nat.succ_mul] at this; omega
      exact ⟨he, by rw [he] at h; omega⟩
    · rintro ⟨h_eq, h0⟩; rw [h_eq, h0]; omega

theorem fl_neg_parts {T : FTy} (x : FV T) :
    (Fl.neg x).magnitude = x.magnitude ∧ (Fl.neg x).signbit = !x.signbit := by
  obtain ⟨hbx, hmx⟩ := Fl.bits_split x
  have h2 := Fmt.width_pow T.fmt
  have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
  unfold Fl.neg
  cases hs : x.signbit
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [hs] at hbx; simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hbx
    have hlt : x.toBits + 2 ^ (T.fmt.eb + T.fmt.sb) < 2 ^ T.fmt.width := by omega
    unfold Fl.magnitude Fl.signbit
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt hlt]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mod_left]
    · rw [decide_eq_true_iff]; omega
  · simp only [↓reduceIte, Bool.not_true]
    rw [hs] at hbx; simp only [↓reduceIte] at hbx
    have hlt : x.toBits - 2 ^ (T.fmt.eb + T.fmt.sb) < 2 ^ T.fmt.width := by omega
    have hsub : x.toBits - 2 ^ (T.fmt.eb + T.fmt.sb) = x.magnitude := by omega
    unfold Fl.magnitude Fl.signbit
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt hlt, hsub]
    refine ⟨Nat.mod_eq_of_lt hmx, ?_⟩
    rw [decide_eq_false_iff_not]; omega

theorem isfinite_IEEEFloat_eq {T : FTy} (x : FV T) :
    isfinite_IEEEFloat x = x.isfinite := by
  unfold isfinite_IEEEFloat isfinite_AbstractFloat sub_IEEEFloat sub_float jlSubFloat
  rw [isnan_IEEEFloat_eq, finishFloat_eq]
  unfold floatSub floatAdd
  obtain ⟨hneg_mag, hneg_sign⟩ := fl_neg_parts x
  have hneg_exp : (Fl.neg x).expField = x.expField := by
    rw [Fl.expField_eq, Fl.expField_eq, hneg_mag]
  have hneg_frac : (Fl.neg x).frac = x.frac := by
    rw [Fl.frac_eq, Fl.frac_eq, hneg_mag]
  have hneg_nan : (Fl.neg x).isnan = x.isnan := by
    unfold Fl.isnan; rw [hneg_exp, hneg_frac]
  have hneg_inf : (Fl.neg x).isinf = x.isinf := by
    unfold Fl.isinf; rw [hneg_exp, hneg_frac]
  have hneg_fin : (Fl.neg x).isfinite = x.isfinite := by
    unfold Fl.isfinite; rw [hneg_exp]
  have hneg_rat : (Fl.neg x).toRat = (-x.toRat.1, x.toRat.2) := by
    unfold Fl.toRat; rw [hneg_fin, hneg_exp, hneg_frac, hneg_sign]
    dsimp only
    generalize x.frac + (if (x.expField == 0) = true then 0 else 2 ^ T.fmt.sb) = m
    generalize (if (x.expField == 0) = true then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
      else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) = p
    cases x.isfinite
    · simp
    · cases x.signbit <;>
        simp only [Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;>
        split <;> simp [Int.neg_mul]
  rw [hneg_nan, hneg_inf, hneg_sign, hneg_rat]
  have hinv_nan : (invalidFloat T.fmt).isnan = true := by cases T <;> decide
  have hzero_nan : (Fl.zero false : FV T).isnan = false := by cases T <;> decide
  by_cases hfin : x.isfinite = true
  · simp only [hfin, Fl.isnan_of_finite hfin, Fl.isinf_of_finite hfin, Bool.false_eq_true, ↓reduceIte]
    have hd_pos : 0 < x.toRat.2 := (Fl.toRat_key (good_fty T) x hfin).1
    have hd_ne : (x.toRat.2 * x.toRat.2 == 0) = false :=
      beq_eq_false_iff_ne.mpr (by have := Nat.mul_pos hd_pos hd_pos; omega)
    have h0 : x.toRat.1 * (x.toRat.2 : Int) + -x.toRat.1 * (x.toRat.2 : Int) = 0 := by
      rw [Int.neg_mul, Int.add_right_neg]
    have hs : (x.signbit && !x.signbit) = false := by cases x.signbit <;> rfl
    rw [h0, hs]
    unfold Fl.roundRat
    simp [hd_ne, hzero_nan]
  · have hnf : x.isfinite = false := Bool.eq_false_iff.mpr hfin
    rw [hnf]
    cases hn : x.isnan
    · have hi : x.isinf = true := by
        unfold Fl.isfinite at hnf; unfold Fl.isnan at hn; unfold Fl.isinf
        simp only [bne_eq_false_iff_eq] at hnf
        simp [hnf] at hn ⊢; exact hn
      have hne_s : (x.signbit != !x.signbit) = true := by cases x.signbit <;> rfl
      simp [hi, hne_s, hinv_nan]
    · simp [quietFloat_isnan x hn]

theorem eq_int_same_eq {t : IntTy} (x y : JInt t) :
    int.eq x y = decide (x.val = y.val) := by
  simp [int.eq, int.eqPromote, int.promoteSameSign, int.eqSame, eq_int_eq,
    widenTo_val, widen_promote_left rfl]

theorem decompose_spec (T : FTy) (x : FV T) :
    (x.isnan = true →
      (decompose x).1.val = 0 ∧ (decompose x).2.1.val = 0 ∧ (decompose x).2.2.val = 0) ∧
    (x.isinf = true →
      (decompose x).1.val = (if x.signbit then -1 else 1) ∧
      (decompose x).2.1.val = 0 ∧ (decompose x).2.2.val = 0) ∧
    (x.isfinite = true →
      (decompose x).1.val = (mantissaNat x : Int) ∧
      (decompose x).2.1.val = (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
                               else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) ∧
      (decompose x).2.2.val = (if x.signbit then -1 else 1) ∧
      x.toRat = ((decompose x).2.2.val * (decompose x).1.val *
                   (if 0 ≤ (decompose x).2.1.val then (2 ^ (decompose x).2.1.val.toNat : Nat) else 1),
                 if 0 ≤ (decompose x).2.1.val then 1 else 2 ^ (-(decompose x).2.1.val).toNat)) := by
  have hnan_eq := isnan_IEEEFloat_eq x
  have hinf_eq := isinf_IEEEFloat_eq x
  have hsign_eq := signbit_float_eq x
  refine ⟨?_, ?_, ?_⟩
  · intro hnan
    cases T <;>
      simp only [decompose, decompose_Float16, decompose_Float32, decompose_Float64,
        hnan_eq, hnan, ↓reduceIte] <;> decide
  · intro hinf
    have hnan : x.isnan = false := by
      unfold Fl.isinf at hinf; unfold Fl.isnan
      simp only [Bool.and_eq_true, beq_iff_eq] at hinf
      simp [hinf.1, hinf.2]
    have hx_eq : x = Fl.inf x.signbit := by
      generalize hs : x.signbit = s
      rw [← Fl.ofBits_toBits x, (Fl.bits_split x).1, hs]
      obtain ⟨hm, _⟩ := mag_decomp x
      unfold Fl.isinf at hinf
      simp only [Bool.and_eq_true, beq_iff_eq] at hinf
      rw [hm, hinf.1, hinf.2]
      rfl
    have hlt0 : lt_FI (Fl.inf x.signbit : FV T) (int.lit .i64 0) = x.signbit := by
      cases T <;> cases x.signbit <;> decide
    cases T <;>
      simp only [decompose, decompose_Float16, decompose_Float32, decompose_Float64,
        hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte] <;>
      rw [hx_eq, hlt0] <;>
      cases x.signbit <;> decide
  · intro hfin
    have hnan : x.isnan = false := Fl.isnan_of_finite hfin
    have hinf : x.isinf = false := Fl.isinf_of_finite hfin
    have hpat_n : pattern (reinterpret_Unsigned x) = x.toBits :=
      pattern_reinterpret_Unsigned x
    have hf : x.frac < 2 ^ T.fmt.sb := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hexp_lt : x.expField < 2 ^ T.fmt.eb := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hT_facts :
        T.uintTy.signed = false ∧
        T.intTy.bits = T.uintTy.bits ∧
        T.fmt.sb < T.uintTy.bits ∧
        T.fmt.sb + 1 ≤ T.intTy.bits - 1 ∧
        T.intTy.bits - 1 ≤ 63 ∧
        2 ^ T.fmt.eb ≤ 2048 ∧
        T.fmt.bias + T.fmt.sb ≤ 1075 ∧
        pattern (int.ofBool T.intTy false) = 0 ∧
        pattern (int.ofBool T.intTy true) = 1 := by
      clear hnan_eq hinf_eq hsign_eq hfin hnan hinf hpat_n hf hexp_lt x
      cases T <;> decide
    obtain ⟨huns, hbits_eq, hsb_lt_u, hsb_le_i, hi_le_63, heb_2048, hbs_1075, hpat_b_false, hpat_b_true⟩ := hT_facts
    have h_exp : ∀ (mask : JInt T.uintTy) (sb : JInt .i64),
        pattern mask = (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb →
        sb.val = (T.fmt.sb : Int) →
        (int.remT .i64 (int.shr_Int (int.band (reinterpret_Unsigned x) mask) sb)).val =
          (x.expField : Int) := by
      intro mask sb hmask hsb
      have hsb0 : 0 ≤ sb.val := by omega
      have hpat_shr : pattern (int.shr_Int (int.band (reinterpret_Unsigned x) mask) sb) = x.expField := by
        rw [pattern_shr_Int_unsigned huns _ _ hsb0, pattern_band, hpat_n, hmask, hsb]
        change (x.toBits &&& (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) / 2 ^ T.fmt.sb = x.expField
        rw [nat_and_shiftRight, Nat.mul_div_cancel _ (Nat.two_pow_pos _), nat_and_mask]
        rfl
      have hval_shr : (int.shr_Int (int.band (reinterpret_Unsigned x) mask) sb).val = (x.expField : Int) := by
        rw [← val_of_unsigned_pattern huns, hpat_shr]
      rw [remT_val, hval_shr]
      apply wrapInt_of_inRange
      simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
    have h_s : ∀ (smask : JInt T.uintTy) (sb bias_sb e : JInt .i64),
        pattern smask = 2 ^ T.fmt.sb - 1 →
        sb.val = (T.fmt.sb : Int) →
        bias_sb.val = (T.fmt.bias + T.fmt.sb : Nat) →
        e.val = (x.expField : Int) →
        (int.remT .i64 (int.bor (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask))
          (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb))).val =
          (mantissaNat x : Int) ∧
        (int.add (int.sub e bias_sb)
          (int.ofBool .i64 (int.eq e (int.lit .i64 0)))).val =
          (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
           else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) := by
      intro smask sb bias_sb e hsm hsb hbs he
      have heq0 : int.eq e (int.lit .i64 0) = decide (x.expField = 0) := by
        rw [eq_int_same_eq, he]
        have : (int.lit .i64 0).val = 0 := rfl
        rw [this]; apply decide_eq_decide.mpr; omega
      have hpat_s0 : pattern (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask)) = x.frac := by
        rw [pattern_of_cong _ _ (remT_val T.intTy _)]
        change ((int.band (reinterpret_Unsigned x) smask).val % ((2 ^ T.intTy.bits : Nat) : Int)).toNat = x.frac
        rw [hbits_eq, ← pattern_cast, pattern_band, hpat_n, hsm, nat_and_mask]
        rfl
      have hpat_shl : pattern (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb) =
          if x.expField = 0 then 0 else 2 ^ T.fmt.sb := by
        rw [heq0, pattern_shl_Int _ _ (by omega)]
        have hsb_nat : sb.val.toNat = T.fmt.sb := by omega
        rw [hsb_nat]
        by_cases hx0 : x.expField = 0
        · simp only [hx0, decide_true, Bool.not_true, ↓reduceIte]
          rw [hpat_b_false, Nat.zero_mul, Nat.zero_mod]
        · simp only [hx0, decide_false, Bool.not_false, ↓reduceIte]
          have hpow_lt : 2 ^ T.fmt.sb < 2 ^ T.intTy.bits :=
            Nat.pow_lt_pow_right (by decide) (by omega)
          rw [hpat_b_true, Nat.one_mul, Nat.mod_eq_of_lt hpow_lt]
      have hpat_bor : pattern (int.bor (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask))
          (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb)) = mantissaNat x := by
        rw [pattern_bor, hpat_s0, hpat_shl]
        unfold mantissaNat
        by_cases hx0 : x.expField = 0
        · simp [hx0]
        · simp only [hx0, ↓reduceIte]
          exact nat_or_pow x.frac T.fmt.sb hf
      have hm_lt : mantissaNat x < 2 ^ (T.intTy.bits - 1) := by
        unfold mantissaNat
        have h1 : 2 ^ (T.fmt.sb + 1) ≤ 2 ^ (T.intTy.bits - 1) :=
          Nat.pow_le_pow_right (by decide) hsb_le_i
        rw [Nat.pow_succ] at h1
        split <;> omega
      have hs_val : (int.bor (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask))
          (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb)).val = (mantissaNat x : Int) := by
        rw [val_of_signed_small_pattern _ (by rw [hpat_bor]; exact hm_lt), hpat_bor]
      refine ⟨?_, ?_⟩
      · rw [remT_val, hs_val]
        apply wrapInt_of_inRange
        have hm_63 : mantissaNat x < 2 ^ 63 :=
          Nat.lt_of_lt_of_le hm_lt (Nat.pow_le_pow_right (by decide) hi_le_63)
        simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
      · rw [add_int_val, sub_int_val, he, hbs, heq0]
        have hofb : ∀ b : Bool, (int.ofBool .i64 b).val = if b then 1 else 0 := by intro b; cases b <;> rfl
        rw [hofb]
        have hsub_val : wrapInt .i64 ((x.expField : Int) - (T.fmt.bias + T.fmt.sb : Nat)) =
            (x.expField : Int) - (T.fmt.bias + T.fmt.sb : Nat) := by
          apply wrapInt_of_inRange; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
        rw [hsub_val]
        by_cases hx0 : x.expField = 0
        · simp only [hx0, decide_true, ↓reduceIte]
          rw [wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
          omega
        · simp only [hx0, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
          omega
    have hnum_pow_den :
        (decompose x).1.val = (mantissaNat x : Int) ∧
        (decompose x).2.1.val = (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
                                 else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) ∧
        (decompose x).2.2.val = (if x.signbit then -1 else 1) := by
      clear huns hbits_eq hsb_lt_u hsb_le_i hi_le_63 heb_2048 hbs_1075 hpat_b_false hpat_b_true hpat_n hf hexp_lt hfin
      cases T
      · have he16 := h_exp (int.lit .u16 0x7c00) (int.lit .i64 10) rfl rfl
        obtain ⟨hs16, hp16⟩ := h_s (int.lit .u16 0x03ff) (int.lit .i64 10) (int.lit .i64 25) _ rfl rfl rfl he16
        dsimp only [decompose, decompose_Float16, reinterpret_Unsigned] at hs16 hp16 ⊢
        simp only [hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs16, hp16, ?_⟩
        rw [hsign_eq]; cases x.signbit <;> rfl
      · have he32 := h_exp (int.lit .u32 0x7f800000) (int.lit .i64 23) rfl rfl
        obtain ⟨hs32, hp32⟩ := h_s (int.lit .u32 0x007fffff) (int.lit .i64 23) (int.lit .i64 150) _ rfl rfl rfl he32
        dsimp only [decompose, decompose_Float32, reinterpret_Unsigned] at hs32 hp32 ⊢
        simp only [hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs32, hp32, ?_⟩
        rw [hsign_eq]; cases x.signbit <;> rfl
      · have he64 := h_exp (int.lit .u64 0x7ff0000000000000) (int.lit .i64 52) rfl rfl
        obtain ⟨hs64, hp64⟩ := h_s (int.lit .u64 0x000fffffffffffff) (int.lit .i64 52) (int.lit .i64 1075) _ rfl rfl rfl he64
        dsimp only [decompose, decompose_Float64, reinterpret_Unsigned] at hs64 hp64 ⊢
        simp only [hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte]
        have hs64' : (int.bor (int.remT .i64 (int.band (reinterpret_Unsigned_Float64 x) (int.lit .u64 0x000fffffffffffff)))
            (int.shl_Int (int.ofBool .i64 (!(int.eq (int.remT .i64 (int.shr_Int (int.band (reinterpret_Unsigned_Float64 x) (int.lit .u64 0x7ff0000000000000)) (int.lit .i64 52))) (int.lit .i64 0)))) (int.lit .i64 52))).val =
            (mantissaNat x : Int) := by
          dsimp [FTy.intTy, FTy.uintTy, int.remT, int.rem_same] at hs64 ⊢; exact hs64
        refine ⟨hs64', hp64, ?_⟩
        rw [hsign_eq]; cases x.signbit <;> rfl
    obtain ⟨h1, h2, h3⟩ := hnum_pow_den
    refine ⟨h1, h2, h3, ?_⟩
    rw [h1, h2, h3]
    unfold Fl.toRat mantissaNat
    simp only [hfin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
    generalize (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
      else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) = p
    generalize x.frac + (if x.expField = 0 then 0 else 2 ^ T.fmt.sb) = m
    cases x.signbit <;> split <;> simp



open NextProofs

def TruncIntExact : Prop :=
  (∀ (T : FTy) (t : IntTy) (x : FV T),
    round_ToZero t x =
      if x.isfinite && decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max) then
        .ok (JInt.wrap t x.truncVal)
      else .error (.inexactError "round")) ∧
  (∀ (T : FTy) (t : IntTy) (x : FV T),
    x.isfinite = true → t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max →
    unsafe_trunc t x = JInt.wrap t x.truncVal) ∧
  (∀ (T : FTy) (x : FV T),
    round_Signed (fun y _ => round_ToZero .i64 y) x .ToZero = round_ToZero .i64 x ∧
    round_Unsigned (fun y _ => round_ToZero .u64 y) x .ToZero = round_ToZero .u64 x ∧
    round_Integer (fun y _ => round_ToZero .i64 y) x .ToZero = round_ToZero .i64 x)

theorem truncIntExact_proven : TruncIntExact := by
  refine ⟨round_ToZero_eq, ?_, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  intro T t x hfin hin
  apply Subtype.ext
  exact unsafe_trunc_eq_wrap T t x hfin hin

def IntConvertExact : Prop :=
  (∀ (T : FTy) (t : IntTy) (x : FV T),
    intOfFloat t x =
      if x.isinteger && decide (t.min ≤ x.truncVal ∧ x.truncVal ≤ t.max) then
        .ok (JInt.wrap t x.truncVal)
      else .error (.inexactError t.name)) ∧
  (∀ (x : FV .f16),
    Bool_Float16 x =
      if eq_IEEEFloat x (zero_float .f16) then .ok false
      else if eq_IEEEFloat x (one_float .f16) then .ok true
      else .error (.inexactError "Bool")) ∧
  Bool_Float16 (zero_float .f16) = .ok false ∧
  Bool_Float16 (neg_IEEEFloat (zero_float .f16)) = .ok false ∧
  Bool_Float16 (one_float .f16) = .ok true ∧
  Bool_Float16 (neg_IEEEFloat (one_float .f16)) = .error (.inexactError "Bool") ∧
  Bool_Float16 (nan_float .f16) = .error (.inexactError "Bool")

theorem intConvertExact_proven : IntConvertExact :=
  ⟨intOfFloat_eq, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

def NextfloatIterate : Prop :=
  (∀ (F : FTy) (t : IntTy) (x : FV F) (d : JInt t),
    (0 ≤ d.val →
      _nextfloat x false (uabs d) = iter nextfloat d.val.natAbs x ∧
      _nextfloat x true (uabs d) = iter prevfloat d.val.natAbs x) ∧
    nextfloat_step x d =
      (if 0 ≤ d.val then iter nextfloat d.val.natAbs x
       else iter prevfloat d.val.natAbs x) ∧
    prevfloat_step x d =
      (if 0 ≤ d.val then iter prevfloat d.val.natAbs x
       else iter nextfloat d.val.natAbs x)) ∧
  (∀ (F : FTy) (x : FV F),
    (x.isnan = true → nextfloat x = x ∧ prevfloat x = x) ∧
    nextfloat (inf_float F) = inf_float F ∧
    prevfloat (neg_IEEEFloat (inf_float F)) = neg_IEEEFloat (inf_float F) ∧
    (x.isnan = false → ¬(x.signbit = false ∧ x.magnitude = infMag F) →
      lt_IEEEFloat x (nextfloat x) = true ∧
      ∀ y : FV F, ¬(lt_IEEEFloat x y = true ∧ lt_IEEEFloat y (nextfloat x) = true)) ∧
    (x.isnan = false → ¬(x.signbit = true ∧ x.magnitude = infMag F) →
      lt_IEEEFloat (prevfloat x) x = true ∧
      ∀ y : FV F, ¬(lt_IEEEFloat (prevfloat x) y = true ∧ lt_IEEEFloat y x = true)))

theorem nextfloatIterate_proven : NextfloatIterate := by
  refine ⟨?_, ?_⟩
  · intro F t x d
    have hu : (uabs d).val = (d.val.natAbs : Int) := (uabsExact_proven t d).1
    have hnext : (nextfloat : FV F → FV F) = (fun y => nextSpec y false 1) :=
      funext nextfloat_eq
    have hprev : (prevfloat : FV F → FV F) = (fun y => nextSpec y true 1) :=
      funext prevfloat_eq
    refine ⟨?_, nextfloat_step_iter x d, prevfloat_step_iter x d⟩
    intro _
    rw [nextfloat_core_eq x false (uabs d) (by omega),
      nextfloat_core_eq x true (uabs d) (by omega), hu, Int.toNat_natCast,
      hnext, hprev, ← spec_iter false d.val.natAbs x, ← spec_iter true d.val.natAbs x]
    exact ⟨rfl, rfl⟩
  · intro F x
    have hinf_eq : nextfloat (inf_float F) = inf_float F ∧
        prevfloat (neg_IEEEFloat (inf_float F)) = neg_IEEEFloat (inf_float F) := by
      clear x; cases F <;> decide
    refine ⟨?_, hinf_eq.1, hinf_eq.2, nextfloat_order_adj x, prevfloat_order_adj x⟩
    intro hx
    rw [nextfloat_eq, prevfloat_eq]
    simp [nextSpec, hx]

def FloatBitLayoutInvariants : Prop :=
  (∀ T : FTy,
    IEEEFloat T = true ∧
    (int.band (sign_mask T) (exponent_mask T)).val = 0 ∧
    (int.band (sign_mask T) (significand_mask T)).val = 0 ∧
    (int.band (exponent_mask T) (significand_mask T)).val = 0 ∧
    int.bor (int.bor (sign_mask T) (exponent_mask T)) (significand_mask T) = int.typemax T.uintTy ∧
    (significand_bits T).val = (T.fmt.sb : Int) ∧
    (exponent_bits T).val = (T.fmt.eb : Int) ∧
    (exponent_bias T).val = (T.fmt.bias : Int) ∧
    (exponent_raw_max T).val = (T.fmt.emax : Int) ∧
    (exponent_max T).val = (T.fmt.bias : Int) ∧
    (exponent_min T).val = 1 - (T.fmt.bias : Int) ∧
    ieee754_exponent_min T = exponent_min T ∧
    (exponent_one T).val = (T.fmt.bias * 2 ^ T.fmt.sb : Nat) ∧
    (exponent_half T).val = ((T.fmt.bias - 1) * 2 ^ T.fmt.sb : Nat)) ∧
  (Inf16 = inf_float .f16 ∧ Inf32 = inf_float .f32 ∧ Inf64 = inf_float .f64 ∧ Inf = Inf64 ∧
    NaN16.isnan = true ∧ NaN32.isnan = true ∧ NaN64.isnan = true ∧ NaN = NaN64) ∧
  (uinttype_Float16 = .u16 ∧ uinttype_Float32 = .u32 ∧ uinttype_Float64 = .u64 ∧
    inttype_Float16 = .i16 ∧ inttype_Float32 = .i32 ∧ inttype_Float64 = .i64 ∧
    floattype_UInt16 = .f16 ∧ floattype_UInt32 = .f32 ∧ floattype_UInt64 = .f64 ∧
    floattype_Int16 = .f16 ∧ floattype_Int32 = .f32 ∧ floattype_Int64 = .f64 ∧
    (∀ T : FTy, floattype T.uintTy = some T ∧ floattype T.intTy = some T)) ∧
  (∀ (T : FTy) (x : FV T),
    (reinterpret_Unsigned x).val = (x.toBits : Int) ∧
    pattern (reinterpret_Signed x) = x.toBits ∧
    reinterpret_Float_Int T (reinterpret_Unsigned x) = x ∧
    reinterpret_Float_Int T (reinterpret_Signed x) = x ∧
    (mantissa x).val = (x.frac : Int))

theorem floatBitLayoutInvariants_proven : FloatBitLayoutInvariants := by
  refine ⟨?_, by decide, ?_, ?_⟩
  · intro T; cases T <;> decide
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro T; cases T <;> decide
  · intro T x
    have hT_mask : T.uintTy.signed = false ∧ pattern (significand_mask T) = 2 ^ T.fmt.sb - 1 := by
      clear x; cases T <;> decide
    have hu := reinterpret_Unsigned_val x
    have hpat_s : pattern (reinterpret_Signed x) = x.toBits := by
      have hlt : x.toBits < 2 ^ T.intTy.bits := by
        have hw : T.intTy.bits = T.fmt.width := by clear hu x; cases T <;> rfl
        rw [hw]; exact x.bits.isLt
      have h_eq : reinterpret_Signed x = toJInt T.intTy (BitVec.ofNat T.intTy.bits x.toBits) := by
        clear hu hlt; cases T <;> rfl
      rw [h_eq, pattern_toJInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hpat_u : pattern (reinterpret_Unsigned x) = x.toBits :=
      pattern_reinterpret_Unsigned x
    have h_re_u : reinterpret_Float_Int T (reinterpret_Unsigned x) = x := by
      unfold reinterpret_Float_Int bitcast_to_float jlBitcast
      rw [← pattern_fromJInt, hpat_u, Fl.ofBits_toBits]
    have h_re_s : reinterpret_Float_Int T (reinterpret_Signed x) = x := by
      unfold reinterpret_Float_Int bitcast_to_float jlBitcast
      rw [← pattern_fromJInt, hpat_s, Fl.ofBits_toBits]
    have hmant : (mantissa x).val = (x.frac : Int) := by
      rw [← val_of_unsigned_pattern hT_mask.1]
      unfold mantissa
      rw [pattern_band, hpat_u, hT_mask.2, nat_and_mask]
      rfl
    exact ⟨hu, hpat_s, h_re_u, h_re_s, hmant⟩

def FloatIeee754RepresentationSpec : Prop := ∀ (F : FTy) (s : Bool),
  (∀ (e m : JInt F.uintTy), e.val.toNat < 2 ^ F.fmt.eb → m.val.toNat < 2 ^ F.fmt.sb →
    reinterpret_Float_Int F (ieee754_representation F s e m) =
      Fl.pack s e.val.toNat m.val.toNat) ∧
  reinterpret_Float_Int F (ieee754_representation_zero F s) = Fl.zero s ∧
  reinterpret_Float_Int F (ieee754_representation_inf F s) = Fl.inf s ∧
  (reinterpret_Float_Int F (ieee754_representation_nan F s)).isnan = true ∧
  (reinterpret_Float_Int F (ieee754_representation_nan F s)).signbit = s ∧
  reinterpret_Float_Int F (ieee754_representation_omega F false) = floatmax_float F ∧
  reinterpret_Float_Int F (ieee754_representation_omega F true) = neg_IEEEFloat (floatmax_float F) ∧
  (∀ (m : JInt F.uintTy), m.val.toNat < 2 ^ F.fmt.sb →
    reinterpret_Float_Int F (ieee754_representation_subnormal F s m) =
      Fl.pack s 0 m.val.toNat) ∧
  (∀ (m : JInt F.uintTy), m.val.toNat < 2 ^ F.fmt.sb →
    reinterpret_Float_Int F (ieee754_representation_nan_payload F s m) =
      Fl.pack s F.fmt.emax m.val.toNat)

theorem floatIeee754RepresentationSpec_proven : FloatIeee754RepresentationSpec := by
  intro F s
  have hfixed :
      reinterpret_Float_Int F (ieee754_representation_zero F s) = Fl.zero s ∧
      reinterpret_Float_Int F (ieee754_representation_inf F s) = Fl.inf s ∧
      (reinterpret_Float_Int F (ieee754_representation_nan F s)).isnan = true ∧
      (reinterpret_Float_Int F (ieee754_representation_nan F s)).signbit = s ∧
      reinterpret_Float_Int F (ieee754_representation_omega F false) = floatmax_float F ∧
      reinterpret_Float_Int F (ieee754_representation_omega F true) = neg_IEEEFloat (floatmax_float F) ∧
      int.remT F.uintTy (int.binop int.bor
        (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) (int.ofBool .u8 false)) =
      int.remT F.uintTy (int.binop int.bor
        (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) (int.lit F.uintTy 0)) ∧
      (int.lit F.uintTy 0).val.toNat = 0 ∧
      int.remT F.uintTy (int.binop int.bor
        (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) (exponent_raw_max F)) =
      int.remT F.uintTy (int.binop int.bor
        (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) (int.remT F.uintTy (exponent_raw_max F))) ∧
      (int.remT F.uintTy (exponent_raw_max F)).val.toNat = F.fmt.emax ∧
      F.fmt.emax < 2 ^ F.fmt.eb := by
    cases F <;> cases s <;> decide
  obtain ⟨hz, hinf, hnan1, hnan2, hom1, hom2, hsub_e, he0, hnan_e, he_max, hem_lt⟩ := hfixed
  refine ⟨ieee754_representation_pack F s, hz, hinf, hnan1, hnan2, hom1, hom2, ?_, ?_⟩
  · intro m hm
    have heq : ieee754_representation_subnormal F s m =
        ieee754_representation F s (int.lit F.uintTy 0) m := by
      dsimp only [ieee754_representation_subnormal, ieee754_representation]
      rw [hsub_e]
    have heb : (int.lit F.uintTy 0).val.toNat < 2 ^ F.fmt.eb := by
      rw [he0]; exact Nat.two_pow_pos _
    rw [heq, ieee754_representation_pack F s (int.lit F.uintTy 0) m heb hm, he0]
  · intro m hm
    have heq : ieee754_representation_nan_payload F s m =
        ieee754_representation F s (int.remT F.uintTy (exponent_raw_max F)) m := by
      dsimp only [ieee754_representation_nan_payload, ieee754_representation]
      rw [hnan_e]
    have heb : (int.remT F.uintTy (exponent_raw_max F)).val.toNat < 2 ^ F.fmt.eb := by
      rw [he_max]; exact hem_lt
    rw [heq, ieee754_representation_pack F s _ m heb hm, he_max]

def FloatClassificationAndDecompose : Prop := ∀ (T : FTy) (x : FV T),
  isnan_IEEEFloat x = x.isnan ∧
  isinf_IEEEFloat x = x.isinf ∧
  isfinite_IEEEFloat x = x.isfinite ∧
  (∀ {N : Type} (n : N), isnan_Number n = false) ∧
  (∀ n : Int, isfinite_Integer n = true) ∧
  isinf_Real isnan_IEEEFloat isfinite_IEEEFloat x = isinf_IEEEFloat x ∧
  isfinite_Real decompose x = isfinite_IEEEFloat x ∧
  (∀ (t : IntTy) (n : JInt t), decompose_Integer n = (n, int.lit .i64 0, int.lit .i64 1)) ∧
  (x.isnan = true →
    (decompose x).1.val = 0 ∧ (decompose x).2.1.val = 0 ∧ (decompose x).2.2.val = 0) ∧
  (x.isinf = true →
    (decompose x).1.val = (if x.signbit then -1 else 1) ∧
    (decompose x).2.1.val = 0 ∧ (decompose x).2.2.val = 0) ∧
  (x.isfinite = true →
    (decompose x).1.val = (mantissaNat x : Int) ∧
    (decompose x).2.1.val = (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
                             else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) ∧
    (decompose x).2.2.val = (if x.signbit then -1 else 1) ∧
    x.toRat = ((decompose x).2.2.val * (decompose x).1.val *
                 (if 0 ≤ (decompose x).2.1.val then (2 ^ (decompose x).2.1.val.toNat : Nat) else 1),
               if 0 ≤ (decompose x).2.1.val then 1 else 2 ^ (-(decompose x).2.1.val).toNat))

theorem floatClassificationAndDecompose_proven : FloatClassificationAndDecompose := by
  intro T x
  obtain ⟨hd_nan, hd_inf, hd_fin⟩ := decompose_spec T x
  have hreal_inf : isinf_Real isnan_IEEEFloat isfinite_IEEEFloat x = isinf_IEEEFloat x := by
    unfold isinf_Real
    rw [isnan_IEEEFloat_eq, isfinite_IEEEFloat_eq, isinf_IEEEFloat_eq]
    unfold Fl.isnan Fl.isfinite Fl.isinf bne
    cases (x.expField == T.fmt.emax) <;> cases (x.frac == 0) <;> rfl
  have hreal_fin : isfinite_Real decompose x = isfinite_IEEEFloat x := by
    unfold isfinite_Real
    rw [isfinite_IEEEFloat_eq, eq_int_same_eq]
    have h0 : (int.lit .i64 0).val = 0 := rfl
    rw [h0]
    by_cases hf : x.isfinite = true
    · obtain ⟨-, -, hden, -⟩ := hd_fin hf
      rw [hf, hden]; cases x.signbit <;> decide
    · have hnf : x.isfinite = false := Bool.eq_false_iff.mpr hf
      rw [hnf]
      cases hn : x.isnan
      · have hi : x.isinf = true := by
          unfold Fl.isfinite at hnf; unfold Fl.isnan at hn; unfold Fl.isinf
          simp only [bne_eq_false_iff_eq] at hnf
          simp [hnf] at hn ⊢; exact hn
        obtain ⟨-, -, hden⟩ := hd_inf hi
        rw [hden]; decide
      · obtain ⟨-, -, hden⟩ := hd_nan hn
        rw [hden]; decide
  exact ⟨isnan_IEEEFloat_eq x, isinf_IEEEFloat_eq x, isfinite_IEEEFloat_eq x,
    (fun {_} _ => rfl), (fun _ => rfl), hreal_inf, hreal_fin, fun _ _ => rfl, hd_nan, hd_inf, hd_fin⟩

/-! ## Property 12: Float conversions, promotion rules, and `widen` (`float-widen-convert-roundtrip`) -/

def FloatWidenConvertRoundtrip : Prop :=
  (∀ (T : FTy) (t : IntTy),
    (t.bits ≤ 64 ∧ t.signed = true → promote_rule_float_int T t = promote_rule_float_BitSigned64 T t) ∧
    (t.bits ≤ 64 ∧ t.signed = false → promote_rule_float_int T t = promote_rule_float_BitUnsigned64 T t) ∧
    promote_rule_float_int T t = T ∧
    promote_rule_float_Bool T = T ∧
    float_Type_Number (fun _ => int.lit t 0) float_BitInteger (fun _ => FTy.f64) = .f64 ∧
    float_Type_AbstractFloat T = T) ∧
  (float_Type_Bottom = none ∧ float_Type_Bottom_slurp (α := FTy) = .error (.methodError "float") ∧
    promote_rule_float .f32 .f16 = some .f32 ∧
    promote_rule_float .f64 .f16 = some .f64 ∧
    promote_rule_float .f64 .f32 = some .f64 ∧
    widen_float .f16 = some .f32 ∧
    widen_float .f32 = some .f64 ∧
    widen_float .f64 = none) ∧
  (∀ (x : FV .f16) (y : Int),
    exactOrder (Float32_Float16 x) y = exactOrder x y ∧
    exactOrder (Float64_Float16 x) y = exactOrder x y) ∧
  (∀ (x : FV .f32) (y : Int),
    exactOrder (Float64_Float32 x) y = exactOrder x y) ∧
  (∀ (T : FTy),
    Float16_Float32 (zero_float .f32) = zero_float .f16 ∧
    Float16_Float32 (one_float .f32) = one_float .f16 ∧
    Float16_Float64 (zero_float .f64) = zero_float .f16 ∧
    Float16_Float64 (one_float .f64) = one_float .f16 ∧
    Float32_Float64 (zero_float .f64) = zero_float .f32 ∧
    Float32_Float64 (one_float .f64) = one_float .f32 ∧
    (∀ x : FV T, convertFloat T x = x)) ∧
  (∀ (t : IntTy) (x : JInt t), float_BitInteger x = floatOfInt .f64 x) ∧
  (∀ (x : JInt .u128), Float16_UInt128 Float16_Float64 x = Float16_Float64 (Float64_UInt128 x)) ∧
  (∀ (x : JInt .i128), Float16_Int128 Float16_Float64 x = Float16_Float64 (Float64_Int128 x)) ∧
  (Float64_UInt128 (int.lit .u128 0) = zero_float .f64 ∧
    Float64_UInt128 (int.lit .u128 1) = one_float .f64 ∧
    Float64_UInt128 (int.shl_Int (int.lit .u128 1) (int.lit .i64 104)) = Fl.pack false (1023 + 104) 0 ∧
    Float64_Int128 (int.lit .i128 0) = zero_float .f64 ∧
    Float64_Int128 (int.lit .i128 (-1)) = neg_IEEEFloat (one_float .f64) ∧
    Float64_Int128 (int.typemin .i128) = neg_IEEEFloat (Float64_UInt128 (uabs_BitSigned (int.typemin .i128))) ∧
    Float32_UInt128 (int.lit .u128 0) = zero_float .f32 ∧
    Float32_UInt128 (int.lit .u128 1) = one_float .f32 ∧
    Float32_UInt128 (int.shl_Int (int.lit .u128 1) (int.lit .i64 100)) = Fl.pack false (127 + 100) 0 ∧
    Float32_Int128 (int.lit .i128 0) = zero_float .f32 ∧
    Float32_Int128 (int.lit .i128 (-1)) = neg_IEEEFloat (one_float .f32) ∧
    Float32_Int128 (int.typemin .i128) = neg_IEEEFloat (Float32_UInt128 (uabs_BitSigned (int.typemin .i128))))

theorem floatWidenConvertRoundtrip_proven : FloatWidenConvertRoundtrip := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, by decide⟩
  · intro T t; cases T <;> cases t <;> decide
  · intro x y
    have h1 : Float32_Float16 x = (Fl.convert x : FV .f32) := convertFloat_eq .f32 x
    have h2 : Float64_Float16 x = (Fl.convert x : FV .f64) := convertFloat_eq .f64 x
    refine ⟨?_, ?_⟩
    · rw [h1]; exact Fl.convert_exactOrder (good_fty .f16) (good_fty .f32) (by decide) (by decide) (by decide) x y
    · rw [h2]; exact Fl.convert_exactOrder (good_fty .f16) (good_fty .f64) (by decide) (by decide) (by decide) x y
  · intro x y
    have h1 : Float64_Float32 x = (Fl.convert x : FV .f64) := convertFloat_eq .f64 x
    rw [h1]; exact Fl.convert_exactOrder (good_fty .f32) (good_fty .f64) (by decide) (by decide) (by decide) x y
  · intro T
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
    intro x; cases T <;> rfl

/-! ## Property 13: IEEE 754 `==`, `<`, and `<=` on `IEEEFloat` (`float-ieee-eq-lt-le`) -/

theorem fl_eq_parts {F : FTy} (x y : FV F) (hx : x.isnan = false) (hy : y.isnan = false) :
    eq_IEEEFloat x y =
      if x.magnitude == 0 && y.magnitude == 0 then true
      else (x.signbit == y.signbit && x.magnitude == y.magnitude) := by
  rw [eq_IEEEFloat_eq]
  obtain ⟨hbx, _⟩ := Fl.bits_split x
  obtain ⟨hby, _⟩ := Fl.bits_split y
  have hzx : x.iszero = (x.magnitude == 0) := rfl
  have hzy : y.iszero = (y.magnitude == 0) := rfl
  unfold Fl.eq
  rw [hx, hy, hzx, hzy, hbx, hby]
  cases x.signbit <;> cases y.signbit <;> cases (x.magnitude == 0) <;> cases (y.magnitude == 0) <;>
    apply Bool.eq_iff_iff.mpr <;> simp <;> omega

def FloatIeeeEqLtLe : Prop := ∀ (T : FTy) (x y z : FV T),
  eq_IEEEFloat x y = Fl.eq x y ∧
  lt_IEEEFloat x y = Fl.lt x y ∧
  le_IEEEFloat x y = Fl.le x y ∧
  (x.isnan = true ∨ y.isnan = true →
    eq_IEEEFloat x y = false ∧ lt_IEEEFloat x y = false ∧ le_IEEEFloat x y = false) ∧
  eq_IEEEFloat (Fl.zero false : FV T) (Fl.zero true) = true ∧
  lt_IEEEFloat (Fl.zero true : FV T) (Fl.zero false) = false ∧
  le_IEEEFloat (Fl.zero true : FV T) (Fl.zero false) = true ∧
  (x.isnan = false → eq_IEEEFloat x x = true ∧ lt_IEEEFloat x x = false ∧ le_IEEEFloat x x = true) ∧
  eq_IEEEFloat x y = eq_IEEEFloat y x ∧
  le_IEEEFloat x y = (lt_IEEEFloat x y || eq_IEEEFloat x y) ∧
  (x.isnan = false → y.isnan = false →
    (lt_IEEEFloat x y = true ∨ eq_IEEEFloat x y = true ∨ lt_IEEEFloat y x = true) ∧
    ¬(lt_IEEEFloat x y = true ∧ lt_IEEEFloat y x = true)) ∧
  (lt_IEEEFloat x y = true → lt_IEEEFloat y z = true → lt_IEEEFloat x z = true) ∧
  (∀ (t : IntTy) (u : JInt t), eq_Ti_Tf_exact u x = eq_Tf_Ti_exact x u)

theorem floatIeeeEqLtLe_proven : FloatIeeeEqLtLe := by
  intro T x y z
  have hz_eq : eq_IEEEFloat (Fl.zero false : FV T) (Fl.zero true) = true ∧
      lt_IEEEFloat (Fl.zero true : FV T) (Fl.zero false) = false ∧
      le_IEEEFloat (Fl.zero true : FV T) (Fl.zero false) = true := by
    clear x y z; cases T <;> decide
  refine ⟨rfl, rfl, rfl, ?_, hz_eq.1, hz_eq.2.1, hz_eq.2.2, ?_, ?_, rfl, ?_, ?_, fun _ _ => rfl⟩
  · intro hnan
    rcases hnan with hx | hy
    · simp [eq_IEEEFloat, lt_IEEEFloat, le_IEEEFloat, eq_float, lt_float, le_float,
        jlEqFloat, jlLtFloat, jlLeFloat, Fl.eq, Fl.lt, Fl.le, hx]
    · simp [eq_IEEEFloat, lt_IEEEFloat, le_IEEEFloat, eq_float, lt_float, le_float,
        jlEqFloat, jlLtFloat, jlLeFloat, Fl.eq, Fl.lt, Fl.le, hy]
  · intro hx
    rw [le_IEEEFloat_eq, Fl.le, ← lt_IEEEFloat_eq, ← eq_IEEEFloat_eq,
      fl_eq_parts x x hx hx, fl_lt_parts x x hx hx]
    cases x.signbit <;> cases (x.magnitude == 0) <;> simp
  · by_cases hx : x.isnan = true
    · simp [eq_IEEEFloat, eq_float, jlEqFloat, Fl.eq, hx]
    · by_cases hy : y.isnan = true
      · simp [eq_IEEEFloat, eq_float, jlEqFloat, Fl.eq, hy]
      · have hx' : x.isnan = false := Bool.eq_false_iff.mpr hx
        have hy' : y.isnan = false := Bool.eq_false_iff.mpr hy
        rw [fl_eq_parts x y hx' hy', fl_eq_parts y x hy' hx']
        cases x.signbit <;> cases y.signbit <;>
          cases h0x : (x.magnitude == 0) <;> cases h0y : (y.magnitude == 0) <;>
          apply Bool.eq_iff_iff.mpr <;> simp <;> omega
  · intro hx hy
    rw [fl_eq_parts x y hx hy, fl_lt_parts x y hx hy, fl_lt_parts y x hy hx]
    cases x.signbit <;> cases y.signbit <;>
      cases h0x : (x.magnitude == 0) <;> cases h0y : (y.magnitude == 0) <;>
      simp only [beq_iff_eq, beq_eq_false_iff_ne] at h0x h0y <;>
      simp [h0x, h0y] <;> omega
  · intro hxy hyz
    by_cases hx : x.isnan = true
    · simp [lt_IEEEFloat, lt_float, jlLtFloat, Fl.lt, hx] at hxy
    · by_cases hy : y.isnan = true
      · simp [lt_IEEEFloat, lt_float, jlLtFloat, Fl.lt, hy] at hxy
      · by_cases hz : z.isnan = true
        · simp [lt_IEEEFloat, lt_float, jlLtFloat, Fl.lt, hz] at hyz
        · have hx' : x.isnan = false := Bool.eq_false_iff.mpr hx
          have hy' : y.isnan = false := Bool.eq_false_iff.mpr hy
          have hz' : z.isnan = false := Bool.eq_false_iff.mpr hz
          rw [fl_lt_parts x y hx' hy'] at hxy
          rw [fl_lt_parts y z hy' hz'] at hyz
          rw [fl_lt_parts x z hx' hz']
          revert hxy hyz
          cases x.signbit <;> cases y.signbit <;> cases z.signbit <;>
            cases h0x : (x.magnitude == 0) <;> cases h0y : (y.magnitude == 0) <;> cases h0z : (z.magnitude == 0) <;>
            simp only [beq_iff_eq, beq_eq_false_iff_ne] at h0x h0y h0z <;>
            simp [h0x, h0y, h0z] <;> omega

/-! ## Property 14: LLVM rounding intrinsics, `rounds_up`, and `_round_convert` (`float-round-llvm-and-convert`) -/

def FloatRoundLlvmAndConvert : Prop := ∀ (T : FTy) (x : FV T),
  (x.isnan = false → (!x.isfinite || x.iszero) = true →
    round_ToZero_llvm x = x ∧ round_Down_llvm x = x ∧
    round_Up_llvm x = x ∧ round_Nearest_llvm x = x) ∧
  (x.isfinite = true → x.iszero = false →
    round_ToZero_llvm x = Fl.roundRat x.truncVal 1 x.signbit ∧
    round_Down_llvm x = Fl.roundRat (x.toRat.1 / x.toRat.2) 1 x.signbit ∧
    round_Up_llvm x = Fl.roundRat (-((-x.toRat.1) / x.toRat.2)) 1 x.signbit ∧
    round_Nearest_llvm x = Fl.roundRat
      (if x.toRat.1 < 0 then -(Fl.roundQuotient x.toRat.1.natAbs x.toRat.2 : Int)
       else (Fl.roundQuotient x.toRat.1.natAbs x.toRat.2 : Int)) 1 x.signbit) ∧
  rounds_up signbit_float x .Down = false ∧
  rounds_up signbit_float x .Up = true ∧
  rounds_up signbit_float x .ToZero = x.signbit ∧
  rounds_up signbit_float x .FromZero = !x.signbit ∧
  (∀ (t : IntTy) (n : JInt t),
    _round_convert (floatOfInt T) signbit_float lt_IEEEFloat (fun a b => lt_IEEEFloat b a)
        nextfloat prevfloat n x .Down =
      (let xt := floatOfInt T n; if lt_IEEEFloat x xt then prevfloat xt else xt) ∧
    _round_convert (floatOfInt T) signbit_float lt_IEEEFloat (fun a b => lt_IEEEFloat b a)
        nextfloat prevfloat n x .Up =
      (let xt := floatOfInt T n; if lt_IEEEFloat xt x then nextfloat xt else xt) ∧
    _round_convert (floatOfInt T) signbit_float lt_IEEEFloat (fun a b => lt_IEEEFloat b a)
        nextfloat prevfloat n x .ToZero =
      (let xt := floatOfInt T n
       if x.signbit then (if lt_IEEEFloat xt x then nextfloat xt else xt)
       else (if lt_IEEEFloat x xt then prevfloat xt else xt)) ∧
    _round_convert (floatOfInt T) signbit_float lt_IEEEFloat (fun a b => lt_IEEEFloat b a)
        nextfloat prevfloat n x .FromZero =
      (let xt := floatOfInt T n
       if x.signbit then (if lt_IEEEFloat x xt then prevfloat xt else xt)
       else (if lt_IEEEFloat xt x then nextfloat xt else xt)))

theorem roundConvertToZero {I F X : Type} (cv : I → F) (sb : X → Bool)
    (lt gt : F → X → Bool) (nf pf : F → F) (n : I) (x : X) :
    _round_convert cv sb lt gt nf pf n x .ToZero =
      (let f := cv n; if sb x then (if lt f x then nf f else f)
       else (if gt f x then pf f else f)) := rfl

theorem roundConvertFromZero {I F X : Type} (cv : I → F) (sb : X → Bool)
    (lt gt : F → X → Bool) (nf pf : F → F) (n : I) (x : X) :
    _round_convert cv sb lt gt nf pf n x .FromZero =
      (let f := cv n; if sb x then (if gt f x then pf f else f)
       else (if lt f x then nf f else f)) := by
  unfold _round_convert rounds_up rounds_up_FromZero
  cases sb x <;> rfl

theorem floatRoundLlvmAndConvert_proven : FloatRoundLlvmAndConvert := by
  intro T x
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro hnan hcond
    simp [round_ToZero_llvm, round_Down_llvm, round_Up_llvm, round_Nearest_llvm,
      trunc_llvm, floor_llvm, ceil_llvm, rint_llvm,
      jlTruncLlvm, jlFloorLlvm, jlCeilLlvm, jlRintLlvm,
      unaryFloat, finishFloat_eq, roundFloat, hnan, hcond]
  · intro hfin hnz
    have hnan : x.isnan = false := Fl.isnan_of_finite hfin
    simp [round_ToZero_llvm, round_Down_llvm, round_Up_llvm, round_Nearest_llvm,
      trunc_llvm, floor_llvm, ceil_llvm, rint_llvm,
      jlTruncLlvm, jlFloorLlvm, jlCeilLlvm, jlRintLlvm,
      unaryFloat, finishFloat_eq, roundFloat, hnan, hfin, hnz, Fl.truncVal]
  · simp [rounds_up, rounds_up_ToZero, signbit_float_eq]
  · simp [rounds_up, rounds_up_FromZero, signbit_float_eq]
  · intro t n
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa only [signbit_float_eq] using
        roundConvertToZero (floatOfInt T) signbit_float lt_IEEEFloat
          (fun a b => lt_IEEEFloat b a) nextfloat prevfloat n x
    · simpa only [signbit_float_eq] using
        roundConvertFromZero (floatOfInt T) signbit_float lt_IEEEFloat
          (fun a b => lt_IEEEFloat b a) nextfloat prevfloat n x

/-! ## Property 15: IEEE 754 arithmetic, negation, `abs`, and NaN propagation (`float-arithmetic-and-nan-propagation`) -/

def FloatArithmeticAndNanPropagation : Prop := ∀ (T : FTy) (x y z : FV T),
  (x.isnan = false →
    (neg_IEEEFloat x).signbit = !x.signbit ∧
    (neg_IEEEFloat x).magnitude = x.magnitude ∧
    (abs_IEEEFloat x).signbit = false ∧
    (abs_IEEEFloat x).magnitude = x.magnitude) ∧
  (x.isnan = true ∨ y.isnan = true →
    (add_IEEEFloat x y).isnan = true ∧
    (sub_IEEEFloat x y).isnan = true ∧
    (mul_IEEEFloat x y).isnan = true ∧
    (div_IEEEFloat x y).isnan = true ∧
    (muladd_IEEEFloat x y z).isnan = true) ∧
  (add_IEEEFloat (inf_float T) (neg_IEEEFloat (inf_float T))).isnan = true ∧
  (sub_IEEEFloat (inf_float T) (inf_float T)).isnan = true ∧
  (mul_IEEEFloat (inf_float T) (zero_float T)).isnan = true ∧
  (div_IEEEFloat (zero_float T) (zero_float T)).isnan = true ∧
  (div_IEEEFloat (inf_float T) (inf_float T)).isnan = true ∧
  (x.isnan = false → y.isnan = false → sub_IEEEFloat x y = add_IEEEFloat x (Fl.neg y))

theorem floatArithmeticAndNanPropagation_proven : FloatArithmeticAndNanPropagation := by
  intro T x y z
  have hinv_ops :
      (add_IEEEFloat (inf_float T) (neg_IEEEFloat (inf_float T))).isnan = true ∧
      (sub_IEEEFloat (inf_float T) (inf_float T)).isnan = true ∧
      (mul_IEEEFloat (inf_float T) (zero_float T)).isnan = true ∧
      (div_IEEEFloat (zero_float T) (zero_float T)).isnan = true ∧
      (div_IEEEFloat (inf_float T) (inf_float T)).isnan = true := by
    clear x y z; cases T <;> decide
  refine ⟨?_, ?_, hinv_ops.1, hinv_ops.2.1, hinv_ops.2.2.1, hinv_ops.2.2.2.1, hinv_ops.2.2.2.2, ?_⟩
  · intro hx
    obtain ⟨hneg_mag, hneg_sign⟩ := fl_neg_parts x
    have hm_lt : x.magnitude < 2 ^ T.fmt.width := by
      have := (Fl.bits_split x).2; rw [Fmt.width_pow]; omega
    have hpos : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
    have hm_bound := (Fl.bits_split x).2
    simp only [neg_IEEEFloat, neg_float, jlNegFloat, abs_IEEEFloat, abs_float, jlAbsFloat,
      unaryFloat, finishFloat_eq, hx, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      hneg_sign, hneg_mag, true_and]
    unfold Fl.signbit Fl.magnitude at hm_lt hm_bound ⊢
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hm_bound]
    refine ⟨?_, rfl⟩
    rw [decide_eq_false_iff_not]; omega
  · intro hnan
    have hq2 : ∀ w : FV T, w.isnan = true →
        (if 32 ≤ T.fmt.width then quietFloat w else quietFloat (quietFloat w)).isnan = true := by
      intro w hw; split
      · exact quietFloat_isnan w hw
      · exact quietFloat_isnan _ (quietFloat_isnan w hw)
    rcases hnan with hx | hy
    · simp [add_IEEEFloat, sub_IEEEFloat, mul_IEEEFloat, div_IEEEFloat, muladd_IEEEFloat,
        add_float, sub_float, mul_float, div_float, muladd_float,
        jlAddFloat, jlSubFloat, jlMulFloat, jlDivFloat, jlMuladdFloat,
        finishFloat_eq, floatAdd, floatSub, floatMul, floatDiv, floatFma,
        hx, quietFloat_isnan x hx, hq2 x hx]
    · by_cases hx : x.isnan = true
      · simp [add_IEEEFloat, sub_IEEEFloat, mul_IEEEFloat, div_IEEEFloat, muladd_IEEEFloat,
          add_float, sub_float, mul_float, div_float, muladd_float,
          jlAddFloat, jlSubFloat, jlMulFloat, jlDivFloat, jlMuladdFloat,
          finishFloat_eq, floatAdd, floatSub, floatMul, floatDiv, floatFma,
          hx, quietFloat_isnan x hx, hq2 x hx]
      · have hx' : x.isnan = false := Bool.eq_false_iff.mpr hx
        simp [add_IEEEFloat, sub_IEEEFloat, mul_IEEEFloat, div_IEEEFloat, muladd_IEEEFloat,
          add_float, sub_float, mul_float, div_float, muladd_float,
          jlAddFloat, jlSubFloat, jlMulFloat, jlDivFloat, jlMuladdFloat,
          finishFloat_eq, floatAdd, floatSub, floatMul, floatDiv, floatFma,
          hx', hy, quietFloat_isnan y hy, hq2 y hy]
  · intro hx hy
    simp [sub_IEEEFloat, add_IEEEFloat, sub_float, add_float, jlSubFloat, jlAddFloat,
      finishFloat_eq, floatSub, hx, hy]

/-! ## Property 16: `unbiased_exponent`, `explicit_mantissa_noinfnan`, `_to_float`, `rem`, and `mod` (`float-fields-and-rem-mod-spec`) -/

def FloatFieldsAndRemModCore : Prop := ∀ (T : FTy) (x y : FV T),
  (unbiased_exponent x).val = (x.expField : Int) ∧
  (explicit_mantissa_noinfnan x).val =
    (if x.expField = 0 ∧ x.frac ≠ 0 then x.frac else x.frac + 2 ^ T.fmt.sb : Nat) ∧
  _to_float (int.lit T.uintTy 0) (int.lit .i64 0) = zero_float T ∧
  _to_float (int.add (significand_mask T) (int.lit T.uintTy 1)) (int.sub (exponent_bias T) (int.lit .i64 1)) = one_float T ∧
  rem_internal (one_float T) (one_float T) = zero_float T ∧
  rem_IEEEFloat (one_float T) (one_float T) = zero_float T ∧
  mod_AbstractFloat (one_float T) (one_float T) = zero_float T ∧
  (x.isnan = true ∨ y.isnan = true ∨ x.isinf = true ∨ iszero_float y = true →
    (rem_IEEEFloat x y).isnan = true ∧ (mod_AbstractFloat x y).isnan = true)

theorem floatFieldsAndRemModCore_proven : FloatFieldsAndRemModCore := by
  intro T x y
  have hT_facts :
      T.uintTy.signed = false ∧
      0 ≤ (significand_bits T).val ∧
      (significand_bits T).val.toNat = T.fmt.sb ∧
      pattern (exponent_mask T) = (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb ∧
      pattern (significand_mask T) = 2 ^ T.fmt.sb - 1 ∧
      pattern (int.add (significand_mask T) (int.lit T.uintTy 1)) = 2 ^ T.fmt.sb ∧
      _to_float (int.lit T.uintTy 0) (int.lit .i64 0) = zero_float T ∧
      _to_float (int.add (significand_mask T) (int.lit T.uintTy 1)) (int.sub (exponent_bias T) (int.lit .i64 1)) = one_float T ∧
      rem_internal (one_float T) (one_float T) = zero_float T ∧
      rem_IEEEFloat (one_float T) (one_float T) = zero_float T ∧
      mod_AbstractFloat (one_float T) (one_float T) = zero_float T ∧
      (nan_float T : FV T).isnan = true ∧
      0 < T.fmt.emax * 2 ^ T.fmt.sb := by
    clear x y; cases T <;> decide
  obtain ⟨huns, hsb0, hsb_nat, hmask_e, hmask_s, hadd_s, hto0, hto1, hrem1, hrem2, hmod1, hnan_t, hem_pos⟩ := hT_facts
  have hpat_x : pattern (reinterpret_Unsigned x) = x.toBits := pattern_reinterpret_Unsigned x
  have hf : x.frac < 2 ^ T.fmt.sb := Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨?_, ?_, hto0, hto1, hrem1, hrem2, hmod1, ?_⟩
  · rw [← val_of_unsigned_pattern huns]
    unfold unbiased_exponent
    rw [pattern_shr_Int_unsigned huns _ _ hsb0, pattern_band, hpat_x, hmask_e, hsb_nat]
    change ((x.toBits &&& (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) / 2 ^ T.fmt.sb : Nat) = (x.expField : Int)
    rw [nat_and_shiftRight, Nat.mul_div_cancel _ (Nat.two_pow_pos _), nat_and_mask]
    rfl
  · rw [← val_of_unsigned_pattern huns]
    unfold explicit_mantissa_noinfnan issubnormal_callee mantissa
    have hpat_m : pattern (int.band (reinterpret_Unsigned x) (significand_mask T)) = x.frac := by
      rw [pattern_band, hpat_x, hmask_s, nat_and_mask]; rfl
    by_cases hsub : x.expField = 0 ∧ x.frac ≠ 0
    · have hsub_b : (x.expField == 0 && x.frac != 0) = true := by
        simp [hsub.1, hsub.2]
      simp [hsub.1, hsub.2, hpat_m]
    · have hsub_b : (x.expField == 0 && x.frac != 0) = false := by
        rw [Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq]; omega
      simp only [hsub, hsub_b, Bool.false_eq_true, ↓reduceIte]
      rw [pattern_bor, hpat_m, hadd_s, nat_or_pow x.frac T.fmt.sb hf]
  · intro hcond
    have h_nan_x : isnan_callee x = x.isnan := isnan_IEEEFloat_eq x
    have h_nan_y : isnan_callee y = y.isnan := isnan_IEEEFloat_eq y
    have h_fin_x : isfinite_callee x = x.isfinite := isfinite_IEEEFloat_eq x
    have h_fin_y : isfinite_callee y = y.isfinite := isfinite_IEEEFloat_eq y
    have h_inf_x : isinf_callee x = x.isinf := isinf_IEEEFloat_eq x
    have h_inf_y : isinf_callee y = y.isinf := isinf_IEEEFloat_eq y
    have hrem_nan : (rem_IEEEFloat x y).isnan = true := by
      unfold rem_IEEEFloat
      rw [h_fin_x, h_fin_y, h_inf_x, h_nan_y]
      rcases hcond with hx | hy | hix | hzy
      · have hfx : x.isfinite = false := by
          unfold Fl.isnan at hx; unfold Fl.isfinite
          simp only [Bool.and_eq_true, beq_iff_eq] at hx; simp [hx.1]
        have hix' : x.isinf = false := by
          unfold Fl.isnan at hx; unfold Fl.isinf
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hx; simp [hx.1, hx.2]
        simp only [hfx, hix', Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        split <;> simp [hnan_t, hx]
      · have hfy : y.isfinite = false := by
          unfold Fl.isnan at hy; unfold Fl.isfinite
          simp only [Bool.and_eq_true, beq_iff_eq] at hy; simp [hy.1]
        simp [hy, hfy, hnan_t]
      · have hfx : x.isfinite = false := by
          unfold Fl.isinf at hix; unfold Fl.isfinite
          simp only [Bool.and_eq_true, beq_iff_eq] at hix; simp [hix.1]
        simp [hix, hfx, hnan_t]
      · simp [hzy, hnan_t]
    refine ⟨hrem_nan, ?_⟩
    unfold mod_AbstractFloat mod_generic
    rw [h_inf_y, h_fin_x]
    by_cases h_if : (y.isinf && x.isfinite) = true
    · simp only [Bool.and_eq_true] at h_if
      rcases hcond with hx | hy | hix | hzy
      · rw [Fl.isnan_of_finite h_if.2] at hx; contradiction
      · have : y.isinf = false := by
          unfold Fl.isnan at hy; unfold Fl.isinf
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hy; simp [hy.1, hy.2]
        rw [this] at h_if; exact Bool.noConfusion h_if.1
      · have : x.isfinite = false := by
          unfold Fl.isinf at hix; unfold Fl.isfinite
          simp only [Bool.and_eq_true, beq_iff_eq] at hix; simp [hix.1]
        rw [this] at h_if; exact Bool.noConfusion h_if.2
      · have hy_inf : y = Fl.inf y.signbit := by
          generalize hs : y.signbit = s
          rw [← Fl.ofBits_toBits y, (Fl.bits_split y).1, hs]
          obtain ⟨hm, _⟩ := mag_decomp y
          have hiy := h_if.1
          unfold Fl.isinf at hiy
          simp only [Bool.and_eq_true, beq_iff_eq] at hiy
          rw [hm, hiy.1, hiy.2]; rfl
        have hnz : iszero_float (Fl.inf y.signbit : FV T) = false := by
          clear huns hsb0 hsb_nat hmask_e hmask_s hadd_s hto0 hto1 hrem1 hrem2 hmod1 hnan_t hem_pos
            hpat_x hf h_nan_x h_nan_y h_fin_x h_fin_y h_inf_x h_inf_y hrem_nan h_if hzy hy_inf x
          generalize y.signbit = s; clear y
          cases T <;> cases s <;> decide
        rw [hy_inf, hnz] at hzy; contradiction
    · simp only [h_if, Bool.false_eq_true, ↓reduceIte]
      have h_isz : eq_float (rem_IEEEFloat x y) (zero_float T) = false := by
        unfold eq_float jlEqFloat Fl.eq
        simp [hrem_nan]
      rw [h_isz]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split <;> simp [add_float, jlAddFloat,
        finishFloat_eq, floatAdd, hrem_nan, quietFloat_isnan _ hrem_nan]

def FloatBoundsAndEpsCore : Prop := ∀ (T : FTy) (x : FV T),
  (precision_Type_default .f16).val = 11 ∧
  (precision_Type_default .f32).val = 24 ∧
  (precision_Type_default .f64).val = 53 ∧
  precision_val_default x = precision_Type_default T ∧
  (∀ (b : JInt .i64) (f : JInt .i64 → JInt .i64 → Jl (JInt .i64)), b.val ≤ 1 →
    precision_Type _precision_with_base_2 f T b = .error (.domainError "`base` cannot be less than 2.") ∧
    precision_val f x b = .error (.domainError "`base` cannot be less than 2.")) ∧
  issubnormal (zero_float T) = false ∧
  issubnormal (floatmin_float T) = false ∧
  issubnormal (nextfloat (zero_float T)) = true ∧
  ispow2_AbstractFloat (fun y => (y, (0 : Int))) (reinterpret_Float_Int T (exponent_half T)) = true ∧
  ispow2_AbstractFloat (fun y => (y, (0 : Int))) (zero_float T) = false ∧
  iseven_AbstractFloat floatmax_val (unsafe_trunc .i64)
    (fun n => int.eq (int.band n (int.lit .i64 1)) (int.lit .i64 0)) (zero_float T) = true ∧
  isodd_AbstractFloat floatmax_val (unsafe_trunc .i64)
    (fun n => !(int.eq (int.band n (int.lit .i64 1)) (int.lit .i64 0))) (one_float T) = true ∧
  typemin_float T = neg_IEEEFloat (inf_float T) ∧
  typemax_float T = inf_float T ∧
  typemin_Real typemin_float T x = typemin_float T ∧
  typemax_Real typemax_float T x = typemax_float T ∧
  floatmin_val x = floatmin_float T ∧
  floatmax_val x = floatmax_float T ∧
  floatmin_default = floatmin_Float64 ∧
  floatmax_default = floatmax_Float64 ∧
  eps_default = eps_Float64 ∧
  eps_IEEEFloat (one_float T) = eps_float T ∧
  (eps_IEEEFloat (inf_float T)).isnan = true ∧
  (eps_IEEEFloat (nan_float T)).isnan = true ∧
  eps_AbstractFloat isfinite_IEEEFloat abs_IEEEFloat le_IEEEFloat floatmin_val (eps_float T)
    unbiased_exponent (fun _ _ => eps_float T) nextfloat (fun _ => zero_float T) (nan_float T) (zero_float T) =
    nextfloat (zero_float T)

theorem floatBoundsAndEpsCore_proven : FloatBoundsAndEpsCore := by
  intro T x
  have hfixed :
      issubnormal (zero_float T) = false ∧
      issubnormal (floatmin_float T) = false ∧
      issubnormal (nextfloat (zero_float T)) = true ∧
      ispow2_AbstractFloat (fun y => (y, (0 : Int))) (reinterpret_Float_Int T (exponent_half T)) = true ∧
      ispow2_AbstractFloat (fun y => (y, (0 : Int))) (zero_float T) = false ∧
      iseven_AbstractFloat floatmax_val (unsafe_trunc .i64)
        (fun n => int.eq (int.band n (int.lit .i64 1)) (int.lit .i64 0)) (zero_float T) = true ∧
      isodd_AbstractFloat floatmax_val (unsafe_trunc .i64)
        (fun n => !(int.eq (int.band n (int.lit .i64 1)) (int.lit .i64 0))) (one_float T) = true ∧
      typemin_float T = neg_IEEEFloat (inf_float T) ∧
      typemax_float T = inf_float T ∧
      eps_IEEEFloat (one_float T) = eps_float T ∧
      (eps_IEEEFloat (inf_float T)).isnan = true ∧
      (eps_IEEEFloat (nan_float T)).isnan = true ∧
      eps_AbstractFloat isfinite_IEEEFloat abs_IEEEFloat le_IEEEFloat floatmin_val (eps_float T)
        unbiased_exponent (fun _ _ => eps_float T) nextfloat (fun _ => zero_float T) (nan_float T) (zero_float T) =
        nextfloat (zero_float T) := by
    clear x; cases T <;> decide
  refine ⟨rfl, rfl, rfl, rfl, ?_, hfixed.1, hfixed.2.1, hfixed.2.2.1,
    hfixed.2.2.2.1, hfixed.2.2.2.2.1, hfixed.2.2.2.2.2.1, hfixed.2.2.2.2.2.2.1,
    hfixed.2.2.2.2.2.2.2.1, hfixed.2.2.2.2.2.2.2.2.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hfixed.2.2.2.2.2.2.2.2.2.1, hfixed.2.2.2.2.2.2.2.2.2.2.1, hfixed.2.2.2.2.2.2.2.2.2.2.2.1,
    hfixed.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro b f hb
  unfold precision_val precision_AbstractFloat precision_Type _precision
  rw [lt_int_eq]
  have h1 : (int.lit .i64 1).val = 1 := rfl
  rw [h1, decide_eq_false (by omega)]
  exact ⟨rfl, rfl⟩

/-! ## Property 18: `bswap` on `IEEEFloat` and `float` on arrays and ranges (`float-bswap-and-collections`) -/

def FloatBswapAndCollections : Prop := ∀ (T : FTy) (x : FV T),
  bswap_IEEEFloat (zero_float T) = zero_float T ∧
  bswap_IEEEFloat (bswap_IEEEFloat (one_float T)) = one_float T ∧
  reinterpret_Unsigned (bswap_IEEEFloat x) = int.bswap (reinterpret_Unsigned x) ∧
  (∀ (arr : Array (FV T)), float_AbstractArray_AbstractFloat arr = arr) ∧
  (∀ {α : Type} (z : α) (toF : α → FV T) (arr : Array α),
    float_AbstractArray (fun _ => false) (fun _ => z) toF (fun _ => T) (fun _ a => .ok (a.map toF)) arr =
      .error (.errorException "`float` not defined on abstractly-typed arrays; please convert to a more specific type") ∧
    float_AbstractArray (fun _ => true) (fun _ => z) toF (fun _ => T) (fun _ a => .ok (a.map toF)) arr =
      .ok (arr.map toF)) ∧
  (∀ {α S R L : Type} (toF : α → FV T) (toS : S → FV T) (toR : R → FV T) (toT : R → α)
      (lastStep : JuliaLean.base.range.StepRange α S → α)
      (lastUnit : JuliaLean.base.range.UnitRange α → α)
      (lenStepLen : JuliaLean.base.range.StepRangeLen α R S L → L)
      (lenLin : JuliaLean.base.range.LinRange α L → L)
      (sr : JuliaLean.base.range.StepRange α S)
      (ur : JuliaLean.base.range.UnitRange α)
      (srl : JuliaLean.base.range.StepRangeLen α R S L)
      (lr : JuliaLean.base.range.LinRange α L),
    float_StepRange toF toS lastStep (fun a s b => (a, s, b)) sr =
      (toF sr.start, toS sr.step, toF (lastStep sr)) ∧
    float_UnitRange toF lastUnit (fun a b => JuliaLean.base.range.UnitRange.mk a b) ur =
      JuliaLean.base.range.UnitRange.mk (toF ur.start) (toF (lastUnit ur)) ∧
    float_StepRangeLen toT toF (fun _ => T) toR toS lenStepLen
      (fun _ ref step len off => @JuliaLean.base.range.StepRangeLen.mk (FV T) (FV T) (FV T) L ref step len off) srl =
      @JuliaLean.base.range.StepRangeLen.mk (FV T) (FV T) (FV T) L (toR srl.ref) (toS srl.step) (lenStepLen srl) srl.offset ∧
    float_LinRange toF lenLin (fun a b n => JuliaLean.base.range.LinRange.mk a b n n) lr =
      JuliaLean.base.range.LinRange.mk (toF lr.start) (toF lr.stop) (lenLin lr) (lenLin lr))

theorem floatBswapAndCollections_proven : FloatBswapAndCollections := by
  intro T x
  have hfixed :
      bswap_IEEEFloat (zero_float T) = zero_float T ∧
      bswap_IEEEFloat (bswap_IEEEFloat (one_float T)) = one_float T := by
    clear x; cases T <;> decide
  refine ⟨hfixed.1, hfixed.2, ?_, fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  apply jint_eq
  have huns : T.uintTy.signed = false := by clear x hfixed; cases T <;> rfl
  have hbw : T.uintTy.bits = T.fmt.width := by clear x hfixed; cases T <;> rfl
  rw [← val_of_unsigned_pattern huns, ← val_of_unsigned_pattern huns]
  congr 1
  rw [pattern_reinterpret_Unsigned]
  have htoNat : (fromJInt (reinterpret_Unsigned x)).toNat = x.toBits := by
    rw [← pattern_fromJInt, pattern_reinterpret_Unsigned]
  have h_ok : ∀ (w : Nat) (hm : w % 16 = 0) (b : BitVec w) (hp),
      int.okOf (jlBswapInt b) hp =
        BitVec.ofNat w ((List.range (w / 8)).foldl (fun r i => r * 256 + b.toNat / 2 ^ (8 * i) % 256) 0) := by
    intro w hm b hp
    apply okOf_eq
    simp [jlBswapInt, hm, pure, Except.pure]
  unfold bswap_IEEEFloat bswap_int_float int.bswap int.bswap_wide int.bswap_int
  have hmod16 : T.uintTy.bits % 16 = 0 := by clear x hfixed huns hbw htoNat h_ok; cases T <;> decide
  simp only [hmod16, ↓reduceDIte]
  rw [pattern_toJInt, h_ok T.uintTy.bits hmod16, h_ok T.fmt.width (by rw [← hbw]; exact hmod16)]
  have hlt : x.toBits < 2 ^ T.fmt.width := x.bits.isLt
  simp only [hbw, htoNat, BitVec.toNat_ofNat, Fl.toBits_ofBits, Nat.mod_eq_of_lt hlt, Nat.mod_mod]

/-! ## Nothing to promise

- `float@387`: `float(::Type{Union{}}, slurp...)` — `Union{}` ambiguity breaker (also covered in `FloatWidenConvertRoundtrip`)
- `unsafe_trunc@406`: `function unsafe_trunc end` — empty generic function declaration
- `precision@795`: `function precision end` — empty generic function declaration
- `precision@807`: `precision(::Type{Union{}}; kwargs...)` — `Union{}` ambiguity breaker
- `eps@996`: `eps(::Type{Union{}})` — `Union{}` ambiguity breaker
- `floatmin@1049`: `floatmin(::Type{Union{}})` — `Union{}` ambiguity breaker
- `floatmax@1050`: `floatmax(::Type{Union{}})` — `Union{}` ambiguity breaker
-/


/-! ## Remainder, subnormal and epsilon specifications -/

open NextProofs TruncProofs

theorem rem_internal_le {T : FTy} (x y : FV T) (hle : x.toBits ≤ y.toBits) :
    rem_internal x y = if x.toBits < y.toBits then x else zero_float T := by
  unfold rem_internal
  have huns : T.uintTy.signed = false := by clear x y hle; cases T <;> rfl
  have hx : (reinterpret_Unsigned x).val = (x.toBits : Int) := reinterpret_Unsigned_val x
  have hy : (reinterpret_Unsigned y).val = (y.toBits : Int) := reinterpret_Unsigned_val y
  have hle_b : int.le_BitUnsigned (reinterpret_Unsigned x) (reinterpret_Unsigned y) = true := by
    unfold int.le_BitUnsigned; rw [ule_int_eq huns, hx, hy]
    exact decide_eq_true (by omega)
  have hlt_b : int.lt_BitUnsigned (reinterpret_Unsigned x) (reinterpret_Unsigned y) =
      decide (x.toBits < y.toBits) := by
    unfold int.lt_BitUnsigned; rw [ult_int_eq huns, hx, hy]
    apply decide_eq_decide.mpr; omega
  dsimp only
  rw [hle_b, hlt_b]
  by_cases hlt : x.toBits < y.toBits <;> simp [hlt]

theorem rem_IEEEFloat_small_and_diag {T : FTy} (x y : FV T) :
    (x.isfinite = true → y.isfinite = true →
      iszero_float x = false → iszero_float y = false →
      (x.magnitude < y.magnitude → rem_IEEEFloat x y = x) ∧
      (x.magnitude = y.magnitude → rem_IEEEFloat x y = Fl.zero x.signbit)) ∧
    (x.isfinite = true → iszero_float x = true →
      y.isnan = false → iszero_float y = false →
      rem_IEEEFloat x y = x) ∧
    (x.isfinite = true → y.isinf = true →
      rem_IEEEFloat x y = x ∧ mod_AbstractFloat x y = x) := by
  have h_fin_x : isfinite_callee x = x.isfinite := isfinite_IEEEFloat_eq x
  have h_fin_y : isfinite_callee y = y.isfinite := isfinite_IEEEFloat_eq y
  have h_inf_x : isinf_callee x = x.isinf := isinf_IEEEFloat_eq x
  have h_inf_y : isinf_callee y = y.isinf := isinf_IEEEFloat_eq y
  have h_nan_y : isnan_callee y = y.isnan := isnan_IEEEFloat_eq y
  refine ⟨?_, ?_, ?_⟩
  · intro hfx hfy hzx hzy
    have hnx : x.isnan = false := Fl.isnan_of_finite hfx
    have hny : y.isnan = false := Fl.isnan_of_finite hfy
    have h_abs_bits : ∀ z : FV T, z.isnan = false → (abs_float z).toBits = z.magnitude := by
      intro z hnz
      unfold abs_float jlAbsFloat unaryFloat
      rw [finishFloat_eq]
      simp only [hnz, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Fl.toBits_ofBits]
      have hm_lt : z.magnitude < 2 ^ T.fmt.width := by
        have := (Fl.bits_split z).2; rw [Fmt.width_pow]; omega
      exact Nat.mod_eq_of_lt hm_lt
    have habs_x := h_abs_bits x hnx
    have habs_y := h_abs_bits y hny
    unfold rem_IEEEFloat
    rw [h_fin_x, h_fin_y, hzx, hzy]
    simp only [hfx, hfy, Bool.not_false, Bool.and_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · intro hlt
      rw [rem_internal_le (abs_float x) (abs_float y) (by omega)]
      have hlt' : (abs_float x).toBits < (abs_float y).toBits := by omega
      simp only [hlt', ↓reduceIte]
      unfold copysign_float jlCopysignFloat
      rw [finishFloat_eq]
      have hmag_abs : (abs_float x).magnitude = x.magnitude :=
        (floatArithmeticAndNanPropagation_proven T x x x).1 hnx |>.2.2.2
      rw [hmag_abs, Nat.add_comm, ← (Fl.bits_split x).1, Fl.ofBits_toBits]
    · intro heq
      rw [rem_internal_le (abs_float x) (abs_float y) (by omega)]
      have hlt' : ¬((abs_float x).toBits < (abs_float y).toBits) := by omega
      simp only [hlt', ↓reduceIte]
      unfold copysign_float jlCopysignFloat
      rw [finishFloat_eq]
      have hz_mag : (zero_float T).magnitude = 0 := by clear h_fin_x h_fin_y h_inf_x h_inf_y h_nan_y hfx hfy hzx hzy hnx hny habs_x habs_y heq hlt' x y; cases T <;> decide
      rw [hz_mag]
      simp only [Nat.zero_add, Fl.zero]
  · intro hfx hzx hny hzy
    have hix : x.isinf = false := Fl.isinf_of_finite hfx
    unfold rem_IEEEFloat
    simp [h_fin_x, h_inf_x, h_nan_y, hfx, hzx, hix, hny, hzy]
  · intro hfx hiy
    have hix : x.isinf = false := Fl.isinf_of_finite hfx
    have hfy : y.isfinite = false := by
      unfold Fl.isinf at hiy; unfold Fl.isfinite
      simp only [Bool.and_eq_true, beq_iff_eq] at hiy; simp [hiy.1]
    have hny : y.isnan = false := by
      unfold Fl.isinf at hiy; unfold Fl.isnan
      simp only [Bool.and_eq_true, beq_iff_eq] at hiy; simp [hiy.1, hiy.2]
    have hy_inf : y = Fl.inf y.signbit := by
      generalize hs : y.signbit = s
      rw [← Fl.ofBits_toBits y, (Fl.bits_split y).1, hs]
      obtain ⟨hm, _⟩ := mag_decomp y
      unfold Fl.isinf at hiy
      simp only [Bool.and_eq_true, beq_iff_eq] at hiy
      rw [hm, hiy.1, hiy.2]; rfl
    have hzy : iszero_float y = false := by
      rw [hy_inf]
      clear h_fin_x h_fin_y h_inf_x h_inf_y h_nan_y hfx hiy hix hfy hny hy_inf x
      generalize y.signbit = s; clear y
      cases T <;> cases s <;> decide
    refine ⟨?_, ?_⟩
    · unfold rem_IEEEFloat
      simp [h_fin_x, h_fin_y, h_inf_x, h_nan_y, hfx, hfy, hix, hny, hzy]
    · unfold mod_AbstractFloat mod_generic
      simp [h_inf_y, h_fin_x, hiy, hfx]

theorem abs_preserves_nan {T : FTy} (x : FV T) (hx : x.isnan = true) :
    (abs_IEEEFloat x).isnan = true := by
  have hm : ∀ y : FV T, (Fl.ofBits y.magnitude : FV T).isnan = y.isnan := by
    intro y
    have hy := (Fl.bits_split y).2
    have hw : y.magnitude < 2 ^ T.fmt.width := by rw [Fmt.width_pow]; omega
    have hmag : (Fl.ofBits y.magnitude : FV T).magnitude = y.magnitude := by
      change (y.magnitude % 2 ^ T.fmt.width) % 2 ^ (T.fmt.eb + T.fmt.sb) = y.magnitude
      rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hy]
    simp only [Fl.isnan, Fl.expField_eq, Fl.frac_eq, hmag]
  unfold abs_IEEEFloat abs_float jlAbsFloat unaryFloat
  rw [finishFloat_eq]
  simp only [hx]
  split
  · rw [hm]; exact quietFloat_isnan x hx
  · rw [hm]; exact hx

theorem eps_IEEEFloat_nonfinite_and_sign {T : FTy} (x : FV T) :
    (x.isfinite = false → (eps_IEEEFloat x).isnan = true) ∧
    ((eps_IEEEFloat x).isnan = false → (eps_IEEEFloat x).signbit = false) := by
  refine ⟨?_, ?_⟩
  · intro hnf
    by_cases hx : x.isnan = true
    · unfold eps_IEEEFloat
      dsimp only
      have hsub_nan : (sub_IEEEFloat x (reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true)))).isnan = true :=
        ((floatArithmeticAndNanPropagation_proven T x _ x).2.1 (Or.inl hx)).2.1
      exact abs_preserves_nan _ hsub_nan
    · have hx' : x.isnan = false := Bool.eq_false_iff.mpr hx
      have hix : x.isinf = true := by
        unfold Fl.isfinite at hnf; unfold Fl.isnan at hx'; unfold Fl.isinf
        simp only [bne_eq_false_iff_eq] at hnf
        simp [hnf] at hx' ⊢; exact hx'
      have hx_inf : x = Fl.inf x.signbit := by
        generalize hs : x.signbit = s
        rw [← Fl.ofBits_toBits x, (Fl.bits_split x).1, hs]
        obtain ⟨hm, _⟩ := mag_decomp x
        unfold Fl.isinf at hix
        simp only [Bool.and_eq_true, beq_iff_eq] at hix
        rw [hm, hix.1, hix.2]; rfl
      rw [hx_inf]
      clear hnf hx hx' hix hx_inf
      generalize x.signbit = s; clear x
      cases T <;> cases s <;> decide
  · intro hnot_nan
    unfold eps_IEEEFloat at hnot_nan ⊢
    dsimp only at hnot_nan ⊢
    generalize sub_IEEEFloat x (reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))) = d at hnot_nan ⊢
    by_cases hd : d.isnan = true
    · exfalso
      have h_abs_nan := abs_preserves_nan d hd
      rw [h_abs_nan] at hnot_nan; contradiction
    · exact (floatArithmeticAndNanPropagation_proven T d d d).1 (Bool.eq_false_iff.mpr hd) |>.2.2.1

theorem issubnormal_eq {T : FTy} (x : FV T) :
    issubnormal x = (x.expField == 0 && x.frac != 0) := by
  have hT :
      T.uintTy.signed = false ∧
      pattern (exponent_mask T) = (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb ∧
      pattern (significand_mask T) = 2 ^ T.fmt.sb - 1 := by
    clear x; cases T <;> decide
  obtain ⟨huns, hme, hms⟩ := hT
  have hpat_x : pattern (reinterpret_Unsigned x) = x.toBits := pattern_reinterpret_Unsigned x
  have h_eq0 : ∀ u : JInt T.uintTy, int.eq u (int.lit .i64 0) = (pattern u == 0) := by
    intro u
    have hval := val_of_unsigned_pattern huns u
    have hcmp := cmp_eq int.eqSame (· = ·) (fun a b => eq_int_eq a b) (by intros; omega)
      huns rfl u (int.lit .i64 0)
    have hne : (T.uintTy.signed == IntTy.i64.signed) = false := by rw [huns]; rfl
    unfold int.eq
    simp only [huns, Bool.false_eq_true, ↓reduceIte]
    change int.cmp_BitUnsigned_BitSigned int.eqSame u (int.lit .i64 0) = _
    rw [hcmp, ← hval]
    have h0 : (int.lit .i64 0).val = 0 := rfl
    rw [h0]
    cases pattern u <;> rfl
  unfold issubnormal
  dsimp only
  rw [h_eq0, h_eq0, pattern_band, pattern_band, hpat_x, hme, hms, nat_and_mask]
  clear hme hms h_eq0 hpat_x
  have hfrac : x.toBits % 2 ^ T.fmt.sb = x.frac := rfl
  have hexp_and : (x.toBits &&& (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb == 0) = (x.expField == 0) := by
    have hdiv : (x.toBits &&& (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) / 2 ^ T.fmt.sb = x.expField := by
      rw [nat_and_shiftRight, Nat.mul_div_cancel _ (Nat.two_pow_pos _), nat_and_mask]
      rfl
    have hmod : (x.toBits &&& (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) % 2 ^ T.fmt.sb = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.zero_testBit]
      by_cases hi : i < T.fmt.sb
      · have hm0 : ((2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) % 2 ^ T.fmt.sb = 0 :=
          Nat.mul_mod_left _ _
        have htb := Nat.testBit_mod_two_pow ((2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) T.fmt.sb i
        rw [hm0, decide_eq_true hi, Bool.true_and, Nat.zero_testBit] at htb
        simp [hi, htb.symm]
      · simp [hi]
    have hfull := (Nat.div_add_mod (x.toBits &&& (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) (2 ^ T.fmt.sb)).symm
    rw [hdiv, hmod, Nat.add_zero] at hfull
    rw [hfull]
    have hP := Nat.two_pow_pos T.fmt.sb
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Nat.mul_eq_zero]
    omega
  rw [hexp_and, hfrac]
  rfl



/-- A finite nonzero dividend smaller in magnitude than its divisor is unchanged by
`rem`; equal magnitudes give zero with the dividend's sign. Infinite divisors preserve
finite dividends under both `rem` and `mod`. -/
def FloatFieldsAndRemModSpec : Prop := FloatFieldsAndRemModCore ∧
  ∀ (T : FTy) (x y : FV T),
    (x.isfinite = true → y.isfinite = true →
      iszero_float x = false → iszero_float y = false →
      (x.magnitude < y.magnitude → rem_IEEEFloat x y = x) ∧
      (x.magnitude = y.magnitude → rem_IEEEFloat x y = Fl.zero x.signbit)) ∧
    (x.isfinite = true → iszero_float x = true →
      y.isnan = false → iszero_float y = false → rem_IEEEFloat x y = x) ∧
    (x.isfinite = true → y.isinf = true →
      rem_IEEEFloat x y = x ∧ mod_AbstractFloat x y = x)

theorem floatFieldsAndRemModSpec_proven : FloatFieldsAndRemModSpec :=
  ⟨floatFieldsAndRemModCore_proven, fun _ x y => rem_IEEEFloat_small_and_diag x y⟩

/-- Subnormal floats have a zero exponent field and a nonzero stored fraction.
`eps` is NaN on every nonfinite input; every non-NaN epsilon has a positive sign. -/
def FloatBoundsAndEps : Prop := FloatBoundsAndEpsCore ∧
  ∀ (T : FTy) (x : FV T),
    issubnormal x = (x.expField == 0 && x.frac != 0) ∧
    (x.isfinite = false → (eps_IEEEFloat x).isnan = true) ∧
    ((eps_IEEEFloat x).isnan = false → (eps_IEEEFloat x).signbit = false)

theorem floatBoundsAndEps_proven : FloatBoundsAndEps :=
  ⟨floatBoundsAndEpsCore_proven, fun _ x => ⟨issubnormal_eq x, eps_IEEEFloat_nonfinite_and_sign x⟩⟩

theorem eq_u128_zero (u : JInt .u128) :
    int.eq u (int.lit .i64 0) = decide (u.val = 0) := by
  have hc := cmp_eq int.eqSame (· = ·) (fun a b => eq_int_eq a b)
    (by intros; omega) (by rfl) (by rfl) u (int.lit .i64 0)
  unfold int.eq
  simp only [IntTy.signed, Bool.false_eq_true, ↓reduceIte]
  change int.cmp_BitUnsigned_BitSigned int.eqSame u (int.lit .i64 0) = _
  exact hc

theorem pattern_add_u32 (a b : JInt .u32) :
    pattern (int.add a b) = (pattern a + pattern b) % 2 ^ 32 := by
  have ha := val_of_unsigned_pattern (by rfl) a
  have hb := val_of_unsigned_pattern (by rfl) b
  rw [pattern_of_cong _ _ (add_int_val a b)]
  change ((a.val + b.val) % (2 ^ 32 : Nat)).toNat = _
  rw [← ha, ← hb, ← Int.natCast_add, ← Int.natCast_emod, Int.toNat_natCast]

theorem top_set_bit_bounds (x : JInt .u128) :
    0 ≤ (int.top_set_bit x).val ∧ (int.top_set_bit x).val ≤ 128 ∧
    (x.val = 0 ↔ (int.top_set_bit x).val = 0) ∧
    (0 < (int.top_set_bit x).val →
      2 ^ ((int.top_set_bit x).val.toNat - 1) ≤ pattern x ∧
      pattern x < 2 ^ (int.top_set_bit x).val.toNat) := by
  unfold int.top_set_bit int.sizeof int.sizeofT int.leading_zeros int.ctlz_int jlCtlzInt
  have h1 : (int.mul (int.lit .i64 8) (int.lit .i64 ↑(IntTy.u128.bits / 8))).val = 128 := by decide
  have h2 : (fromJInt x).toNat < 2 ^ 128 := (fromJInt x).isLt
  have h3 : (if (fromJInt x).toNat == 0 then IntTy.u128.bits else IntTy.u128.bits - (fromJInt x).toNat.log2 - 1) ≤ 128 := by
    dsimp [IntTy.bits]; split <;> omega
  generalize h_lz : (if (fromJInt x).toNat == 0 then IntTy.u128.bits else IntTy.u128.bits - (fromJInt x).toNat.log2 - 1) = lz at h3 ⊢
  have hpat_lz : pattern (toJInt .u128 (BitVec.ofNat IntTy.u128.bits lz)) = lz := by
    rw [pattern_toJInt, BitVec.toNat_ofNat]; dsimp [IntTy.bits]; omega
  have hrem_lz : (int.remT .i64 (toJInt .u128 (BitVec.ofNat IntTy.u128.bits lz))).val = (lz : Int) := by
    rw [remT_val, ← val_of_unsigned_pattern (by rfl), hpat_lz]
    apply wrapInt_of_inRange; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  rw [sub_int_val, h1, hrem_lz, wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
  have hpat_x : (fromJInt x).toNat = pattern x := (pattern_fromJInt x).symm
  have hx_val : x.val = (pattern x : Int) := (val_of_unsigned_pattern (by rfl) x).symm
  rw [hpat_x] at h_lz h2
  dsimp [IntTy.bits] at h_lz
  by_cases hx0 : pattern x = 0
  · subst h_lz; simp [hx0, hx_val]
  · have hlog_lt : (pattern x).log2 < 128 := (Nat.log2_lt hx0).mpr h2
    have hlog_bounds := Nat.log2_self_le hx0
    have hlog_upper : pattern x < 2 ^ ((pattern x).log2 + 1) :=
      Nat.lt_log2_self
    subst h_lz
    simp only [beq_iff_eq, hx0, ↓reduceIte]
    have h_tsb : (128 - (128 - (pattern x).log2 - 1 : Nat) : Int).toNat = (pattern x).log2 + 1 := by omega
    refine ⟨by omega, by omega, ⟨by omega, by omega⟩, fun _ => ?_⟩
    rw [h_tsb]
    exact ⟨hlog_bounds, hlog_upper⟩

theorem float32_uint128_spec (x : JInt .u128) :
    Float32_UInt128 x =
      if x.val = 0 then zero_float .f32
      else
        let n := (int.top_set_bit x).val.toNat
        if n ≤ 24 then
          Fl.pack false (n + 126) (((pattern x % 2 ^ 32) * 2 ^ (24 - n)) % 2 ^ 23)
        else
          let y0 := (pattern x / 2 ^ (n - 25)) % 2 ^ 24
          let y1 := (y0 + 1) / 2
          let y2 := if (int.trailing_zeros x).val = (n : Int) - 25 then y1 &&& (2 ^ 32 - 2) else y1
          Fl.ofBits (((n + 126) * 2 ^ 23 + y2) % 2 ^ 32) := by
  unfold Float32_UInt128
  have heq0 : int.eq x (int.lit .i64 0) = decide (x.val = 0) :=
    eq_u128_zero x
  rw [heq0]
  by_cases hx0 : x.val = 0
  · simp [hx0]
  · simp only [hx0, decide_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hn0, hn128, _, _⟩ := top_set_bit_bounds x
    generalize int.top_set_bit x = n_int at hn0 hn128 ⊢
    generalize int.trailing_zeros x = tz_int
    have hle24 : int.le_BitSigned n_int (int.lit .i64 24) = decide (n_int.val.toNat ≤ 24) := by
      unfold int.le_BitSigned; rw [sle_int_eq rfl]
      have : (int.lit .i64 24).val = 24 := rfl
      rw [this]; apply decide_eq_decide.mpr; omega
    have hre : ∀ u : JInt .u32, reinterpret_Float_Int .f32 u = Fl.ofBits (pattern u) := by
      intro u; unfold reinterpret_Float_Int bitcast_to_float jlBitcast
      rw [← pattern_fromJInt]
    have h_rem32 : ∀ u : JInt .u128, pattern (int.remT .u32 u) = pattern u % 2 ^ 32 := by
      intro u; unfold pattern; rw [remT_val]
      simp only [wrapInt, IntTy.signed, Bool.false_eq_true, ↓reduceIte, IntTy.bits, Int.emod_emod]
      rw [← val_of_unsigned_pattern (by rfl) u]
      have : (0 : Int) ≤ (pattern u : Int) % (2 ^ 32 : Nat) :=
        Int.emod_nonneg _ (by decide)
      omega
    have h23 : (int.lit .i64 23).val.toNat = 23 := rfl
    have hadd126 : 0 ≤ (int.add n_int (int.lit .i64 126)).val ∧
        pattern (int.remT .u32 (int.add n_int (int.lit .i64 126))) = n_int.val.toNat + 126 := by
      have hadd : (int.add n_int (int.lit .i64 126)).val = (n_int.val.toNat + 126 : Nat) := by
        rw [add_int_val]
        have : (int.lit .i64 126).val = 126 := rfl
        rw [this, wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
        omega
      refine ⟨by omega, ?_⟩
      unfold pattern; rw [remT_val, hadd]
      have hw : wrapInt .u32 (n_int.val.toNat + 126 : Nat) = (n_int.val.toNat + 126 : Nat) := by
        apply wrapInt_of_inRange; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
      rw [hw]; dsimp [IntTy.bits]; omega
    have hexp_pat : pattern (int.shl_Int (int.remT .u32 (int.add n_int (int.lit .i64 126))) (int.lit .i64 23)) =
        (n_int.val.toNat + 126) * 2 ^ 23 := by
      rw [pattern_shl_Int _ _ (by decide), hadd126.2, h23]
      dsimp [IntTy.bits]; omega
    rw [hle24]
    by_cases hn24 : n_int.val.toNat ≤ 24
    · simp only [hn24, decide_true, ↓reduceIte]
      have hsub24 : 0 ≤ (int.sub (int.lit .i64 24) n_int).val ∧
          (int.sub (int.lit .i64 24) n_int).val.toNat = 24 - n_int.val.toNat := by
        rw [sub_int_val]
        have : (int.lit .i64 24).val = 24 := rfl
        rw [this, wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
        omega
      have hy_pat : pattern (int.band (int.shl_Int (int.remT .u32 x) (int.sub (int.lit .i64 24) n_int))
          (int.lit .u32 0x007fffff)) = ((pattern x % 2 ^ 32) * 2 ^ (24 - n_int.val.toNat)) % 2 ^ 23 := by
        rw [pattern_band, pattern_shl_Int _ _ hsub24.1, h_rem32, hsub24.2]
        have hm23 : pattern (int.lit .u32 0x007fffff) = 2 ^ 23 - 1 := rfl
        rw [hm23, nat_and_mask]
        exact Nat.mod_mod_of_dvd _ (by decide : 2 ^ 23 ∣ 2 ^ 32)
      have hy_lt : ((pattern x % 2 ^ 32) * 2 ^ (24 - n_int.val.toNat)) % 2 ^ 23 < 2 ^ 23 :=
        Nat.mod_lt _ (Nat.two_pow_pos 23)
      generalize ((pattern x % 2 ^ 32) * 2 ^ (24 - n_int.val.toNat)) % 2 ^ 23 = ym at hy_pat hy_lt ⊢
      rw [hre]
      have hadd_pat : pattern (int.add (int.shl_Int (int.remT .u32 (int.add n_int (int.lit .i64 126))) (int.lit .i64 23))
          (int.band (int.shl_Int (int.remT .u32 x) (int.sub (int.lit .i64 24) n_int)) (int.lit .u32 0x007fffff))) =
          (n_int.val.toNat + 126) * 2 ^ 23 + ym := by
        rw [pattern_add_u32, hexp_pat, hy_pat]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hadd_pat]
      unfold Fl.pack
      have h_eb : 2 ^ FTy.f32.fmt.eb = 256 := rfl
      have h_sb : FTy.f32.fmt.sb = 23 := rfl
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, h_eb, h_sb]
    · simp only [hn24, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hsub25 : 0 ≤ (int.sub n_int (int.lit .i64 25)).val ∧
          (int.sub n_int (int.lit .i64 25)).val = (n_int.val.toNat : Int) - 25 ∧
          (int.sub n_int (int.lit .i64 25)).val.toNat = n_int.val.toNat - 25 := by
        rw [sub_int_val]
        have : (int.lit .i64 25).val = 25 := rfl
        rw [this, wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
        omega
      have hy0_pat : pattern (int.band (int.remT .u32 (int.shr_Int x (int.sub n_int (int.lit .i64 25))))
          (int.lit .u32 0x00ffffff)) = (pattern x / 2 ^ (n_int.val.toNat - 25)) % 2 ^ 24 := by
        rw [pattern_band, h_rem32, pattern_shr_Int_unsigned (by rfl) x _ hsub25.1, hsub25.2.2]
        have hm24 : pattern (int.lit .u32 0x00ffffff) = 2 ^ 24 - 1 := rfl
        rw [hm24, nat_and_mask]
        exact Nat.mod_mod_of_dvd _ (by decide : 2 ^ 24 ∣ 2 ^ 32)
      have hy0_lt : (pattern x / 2 ^ (n_int.val.toNat - 25)) % 2 ^ 24 < 2 ^ 24 :=
        Nat.mod_lt _ (Nat.two_pow_pos 24)
      generalize int.band (int.remT .u32 (int.shr_Int x (int.sub n_int (int.lit .i64 25))))
          (int.lit .u32 0x00ffffff) = y0_int at hy0_pat ⊢
      have hy1_pat : pattern (int.shr_Int (int.add y0_int (int.lit .u32 1)) (int.lit .i64 1)) =
          (pattern y0_int + 1) / 2 := by
        rw [pattern_shr_Int_unsigned (by rfl) _ _ (by decide)]
        have h1 : (int.lit .i64 1).val.toNat = 1 := rfl
        have h_add_u32 : pattern (int.add y0_int (int.lit .u32 1)) = pattern y0_int + 1 := by
          rw [pattern_add_u32]
          have h1u : pattern (int.lit .u32 1) = 1 := rfl
          rw [h1u]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h_add_u32, h1]
      have heq_tz : int.eq_int tz_int (int.sub n_int (int.lit .i64 25)) =
          decide (tz_int.val = (n_int.val.toNat : Int) - 25) := by
        rw [eq_int_eq, hsub25.2.1]
      have hpat_bnot : ∀ b : Bool, pattern (int.bnot (int.ofBool .u32 b)) =
          if b then 2 ^ 32 - 2 else 2 ^ 32 - 1 := by
        intro b; cases b <;> rfl
      generalize int.shr_Int (int.add y0_int (int.lit .u32 1)) (int.lit .i64 1) = y1_int at hy1_pat ⊢
      have hy2_pat : pattern (int.band y1_int (int.bnot (int.ofBool .u32 (int.eq_int tz_int (int.sub n_int (int.lit .i64 25)))))) =
          if tz_int.val = (n_int.val.toNat : Int) - 25 then pattern y1_int &&& (2 ^ 32 - 2)
          else pattern y1_int := by
        rw [pattern_band, heq_tz, hpat_bnot]
        by_cases htz : tz_int.val = (n_int.val.toNat : Int) - 25
        · simp [htz]
        · simp only [htz, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [nat_and_mask, Nat.mod_eq_of_lt (by omega)]
      rw [hre]
      rw [pattern_add_u32, hexp_pat, hy2_pat, hy1_pat, hy0_pat]


theorem roundRat_nat32_normal (n : Nat) (hn : 0 < n) (hlog : n.log2 ≤ 127) :
    (Fl.roundRat (n : Int) 1 false : FV .f32) =
      Fl.packRounded false
        (if 23 ≤ n.log2 then Fl.roundQuotient n (2 ^ (n.log2 - 23))
         else n * 2 ^ (23 - n.log2))
        ((n.log2 : Int) - 23) := by
  have hn0 : n ≠ 0 := by omega
  have hnI : (n : Int) ≠ 0 := by omega
  have hneg : decide ((n : Int) < 0) = false := by simp
  have hfloor : Fl.floorLog2Rat n 1 = (n.log2 : Int) := by
    simpa using Fl.floorLog2Rat_pow n 0 hn0
  unfold Fl.roundRat
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    beq_eq_false_iff_ne.mpr hnI, hneg, Int.natAbs_natCast, hfloor]
  have hupper : ¬((n.log2 : Int) ≥ (FTy.f32.fmt.emax : Int) - FTy.f32.fmt.bias) := by
    change ¬((n.log2 : Int) ≥ 128)
    omega
  have hlower : ¬((n.log2 : Int) < -((FTy.f32.fmt.bias : Int) + FTy.f32.fmt.sb) - 1) := by
    change ¬((n.log2 : Int) < -151)
    omega
  rw [if_neg hupper, if_neg hlower]
  have hk : max ((n.log2 : Int) - FTy.f32.fmt.sb)
      (1 - (FTy.f32.fmt.bias : Int) - FTy.f32.fmt.sb) = (n.log2 : Int) - 23 := by
    change max ((n.log2 : Int) - 23) (-149) = (n.log2 : Int) - 23
    omega
  rw [hk]
  by_cases he : 23 ≤ n.log2
  · have heI : 0 ≤ (n.log2 : Int) - 23 := by omega
    have hcast : ((n.log2 : Int) - 23).toNat = n.log2 - 23 := by omega
    simp only [he, ↓reduceIte, heI, hcast, Nat.one_mul]
  · have heI : ¬(0 ≤ (n.log2 : Int) - 23) := by omega
    have hcast : (-((n.log2 : Int) - 23)).toNat = 23 - n.log2 := by omega
    simp only [he, ↓reduceIte, heI, hcast]
    rw [show n * 2 ^ (23 - n.log2) = (n * 2 ^ (23 - n.log2)) * 1 by omega,
      Fl.roundQuotient_exact _ 1 (by decide)]

    simp only [Nat.mul_one]

theorem roundQuotient_guard (a d : Nat) (hd : 0 < d) :
    Fl.roundQuotient a (d * 2) =
      let y := (a / d + 1) / 2
      if a % d = 0 ∧ a / d % 2 = 1 then y - y % 2 else y := by
  have hrem : a % d < d := Nat.mod_lt a hd
  have hbit : a / d % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsplit : a % (d * 2) = d * (a / d % 2) + a % d := by
    calc
      a % (d * 2) = d * (a % (d * 2) / d) + a % (d * 2) % d := by
        simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div (a % (d * 2)) d).symm
      _ = d * (a / d % 2) + a % d := by
        rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  have hdiv : a / (d * 2) = a / d / 2 := by
    rw [Nat.div_div_eq_div_mul]
  unfold Fl.roundQuotient
  rw [hsplit, hdiv]
  dsimp only
  clear hsplit hdiv
  generalize a / d = b at *
  generalize a % d = r at *
  by_cases hb : b % 2 = 0
  · have hy : (b + 1) / 2 = b / 2 := by omega
    have hc : ¬(2 * r > d * 2) := by omega
    have ht : 2 * r ≠ d * 2 := by omega
    simp [hb, hc, ht, hy]
  · have hb1 : b % 2 = 1 := by omega
    have hy : (b + 1) / 2 = b / 2 + 1 := by omega
    rw [hb1, Nat.mul_one, hy]
    by_cases hz : r = 0
    · simp only [hz, Nat.add_zero, Nat.mul_comm d 2, Nat.lt_irrefl, decide_false,
        beq_self_eq_true, Bool.false_or, Bool.true_and, true_and, ↓reduceIte]
      generalize b / 2 = q
      have hpar : q % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases hp : q % 2 = 1 <;> simp [hp] <;> omega
    · have hstrict : 2 * (d + r) > d * 2 := by omega
      simp [hz, hstrict]


theorem trailing_zeros_tie (x : JInt .u128) (k : Nat) (hk : k < 128) :
    (int.trailing_zeros x).val = (k : Int) ↔
      pattern x % 2 ^ k = 0 ∧ (pattern x).testBit k = true := by
  obtain ⟨hr0, hr128, hbefore, hat⟩ := JuliaLean.Proofs.base.int.trailingZeros_proven .u128 x
  have hbefore' : ∀ i : Nat, (i : Int) < (int.trailing_zeros x).val →
      (pattern x).testBit i = false := by
    intro i hi
    simpa only [JuliaLean.Proofs.base.int.bitOf_eq, JuliaLean.Proofs.base.int.pattern, pattern] using hbefore i hi
  have hat' : (int.trailing_zeros x).val < 128 →
      (pattern x).testBit (int.trailing_zeros x).val.toNat = true := by
    intro h
    simpa only [JuliaLean.Proofs.base.int.bitOf_eq, JuliaLean.Proofs.base.int.pattern, pattern] using hat h
  constructor
  · intro heq
    refine ⟨?_, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
      by_cases hi : i < k
      · rw [hbefore' i (by omega)]
        simp
      · simp [hi]
    · have h := hat' (by omega)
      simpa only [heq, Int.toNat_natCast] using h
  · rintro ⟨hmod, hbit⟩
    have low : ∀ i : Nat, i < k → (pattern x).testBit i = false := by
      intro i hi
      have h := congrArg (fun n : Nat => n.testBit i) hmod
      simpa [Nat.testBit_mod_two_pow, hi] using h
    have hnotlt : ¬((int.trailing_zeros x).val < (k : Int)) := by
      intro h
      have h1 := hat' (by omega)
      have h2 := low (int.trailing_zeros x).val.toNat (by omega)
      rw [h1] at h2
      contradiction
    have hnotgt : ¬((k : Int) < (int.trailing_zeros x).val) := by
      intro h
      have h := hbefore' k h
      rw [hbit] at h
      contradiction
    omega

/-- The unsigned 32-bit tie mask clears precisely the low bit. -/
theorem clear_low_bit32 (a : Nat) (ha : a < 2 ^ 32) :
    a &&& (2 ^ 32 - 2) = a - a % 2 := by
  have hm : ∀ i : Fin 32, (2 ^ 32 - 2 : Nat).testBit i.val = decide (0 < i.val) := by decide
  have hlow : a - a % 2 = a / 2 * 2 ^ 1 := by omega
  rw [hlow]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow]
  change _ = (decide (1 ≤ i) && (a / 2 ^ 1).testBit (i - 1))
  rw [Nat.testBit_div_two_pow]
  by_cases hi : i < 32
  · rw [hm ⟨i, hi⟩]
    by_cases h0 : i = 0
    · subst i; simp
    · have hsum : i - 1 + 1 = i := by omega
      simp [show 1 ≤ i by omega, hsum, show 0 < i by omega]
  · have ha' : a < 2 ^ i := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow ha']
    by_cases h0 : i = 0
    · omega
    · have hsum : i - 1 + 1 = i := by omega
      simp [show 1 ≤ i by omega, hsum, Nat.testBit_lt_two_pow ha']


theorem packRounded32_guard (l y : Nat) (hl : l ≤ 127) (hy : y ≤ 2 ^ 23) :
    (Fl.packRounded false (2 ^ 23 + y) ((l : Int) - 23) : FV .f32) =
      Fl.ofBits ((l + 127) * 2 ^ 23 + y) := by
  have hq0 : ¬((2 ^ 23 + y : Nat) == 0) = true := by simp
  have he : (l : Int) - 23 + (FTy.f32.fmt.bias : Int) + FTy.f32.fmt.sb = (l + 127 : Nat) := by
    change (l : Int) - 23 + 127 + 23 = (l + 127 : Nat)
    omega
  have hec : ((l : Int) - 23 + 1) + (FTy.f32.fmt.bias : Int) + FTy.f32.fmt.sb = (l + 128 : Nat) := by
    change ((l : Int) - 23 + 1) + 127 + 23 = (l + 128 : Nat)
    omega
  unfold Fl.packRounded
  rw [if_neg hq0]
  by_cases hc : y = 2 ^ 23
  · have hcarry : 2 ^ 23 + y ≥ 2 ^ (FTy.f32.fmt.sb + 1) := by
      change 2 ^ 23 + y ≥ 2 ^ 24
      omega
    simp only [hcarry, ↓reduceIte, hec, Bool.false_eq_true, Nat.zero_add]
    have hm : (2 ^ 23 + y) / 2 = 2 ^ FTy.f32.fmt.sb := by
      change (2 ^ 23 + y) / 2 = 2 ^ 23
      omega
    rw [hm]
    have hm0 : ¬(2 ^ FTy.f32.fmt.sb < 2 ^ FTy.f32.fmt.sb) := by omega
    simp only [hm0, ↓reduceIte, Nat.sub_self, Nat.add_zero, Int.toNat_natCast]
    by_cases htop : l = 127
    · subst l
      simp only [show ((127 + 128 : Nat) : Int) ≥ (FTy.f32.fmt.emax : Int) by decide, ↓reduceIte]
      subst y
      rfl
    · have hemax : ¬((l + 128 : Nat) : Int) ≥ (FTy.f32.fmt.emax : Int) := by
        change ¬((l + 128 : Nat) : Int) ≥ 255
        omega
      rw [if_neg hemax]
      apply congrArg (Fl.ofBits (f := FTy.f32.fmt))
      change (l + 128) * 2 ^ 23 = (l + 127) * 2 ^ 23 + y
      omega
  · have hcarry : ¬(2 ^ 23 + y ≥ 2 ^ (FTy.f32.fmt.sb + 1)) := by
      change ¬(2 ^ 23 + y ≥ 2 ^ 24)
      omega
    simp only [hcarry, ↓reduceIte, he, Bool.false_eq_true, Nat.zero_add]
    have hemax : ¬((l + 127 : Nat) : Int) ≥ (FTy.f32.fmt.emax : Int) := by
      change ¬((l + 127 : Nat) : Int) ≥ 255
      omega
    rw [if_neg hemax]
    have hm : ¬(2 ^ 23 + y < 2 ^ FTy.f32.fmt.sb) := by
      change ¬(2 ^ 23 + y < 2 ^ 23)
      omega
    simp only [hm, ↓reduceIte, Int.toNat_natCast]
    apply congrArg (Fl.ofBits (f := FTy.f32.fmt))
    change (l + 127) * 2 ^ 23 + (2 ^ 23 + y - 2 ^ 23) = (l + 127) * 2 ^ 23 + y
    omega


theorem top_set_bit_log2 (x : JInt .u128) (hx : x.val ≠ 0) :
    (int.top_set_bit x).val.toNat = (pattern x).log2 + 1 := by
  obtain ⟨hn0, hn128, hnzero, hbounds⟩ := top_set_bit_bounds x
  have hnp : 0 < (int.top_set_bit x).val := by omega
  have hp : pattern x ≠ 0 := by
    have hv := val_of_unsigned_pattern (by rfl) x
    omega
  obtain ⟨hlo, hhi⟩ := hbounds hnp
  have h1 := (Nat.le_log2 hp).mpr hlo
  have h2 := (Nat.log2_lt hp).mpr hhi
  omega

theorem nat32_small_rounded (n : Nat) (hn : 0 < n) (hsmall : n.log2 + 1 ≤ 24) :
    (Fl.pack false (n.log2 + 1 + 126) (((n % 2 ^ 32) * 2 ^ (24 - (n.log2 + 1))) % 2 ^ 23) : FV .f32) =
      Fl.roundRat (n : Int) 1 false := by
  have hn0 : n ≠ 0 := by omega
  have hn24 : n < 2 ^ 24 := (Nat.log2_lt hn0).mp (by omega)
  have hn32 : n < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hn32]
  have he : 24 - (n.log2 + 1) = 23 - n.log2 := by omega
  rw [he]
  have hnorm := Fl.roundRat_normal (good_fty .f32) (n : Int) n 0 0 false
    (by simp) (by omega) hn24 (by change 1 ≤ n.log2 + 0 + 127; omega)
    (by change n.log2 + 0 + 127 < 0 + 255; omega)
  have hq := Fl.sig_bounds (f := FTy.f32.fmt) n hn0 hn24
  have hmod : n * 2 ^ (23 - n.log2) % 2 ^ 23 = n * 2 ^ (23 - n.log2) - 2 ^ 23 := by
    change n.log2 ≤ 23 ∧ 2 ^ 23 ≤ n * 2 ^ (23 - n.log2) ∧
      n * 2 ^ (23 - n.log2) < 2 ^ 24 at hq
    omega
  rw [hmod, hnorm]
  have hfalse : decide ((n : Int) < 0) = false := by simp
  simp only [hfalse, Nat.add_zero, Nat.sub_zero]
  rfl

theorem ofBits_mod_pattern {f : Fmt} (a : Nat) :
    (Fl.ofBits (a % 2 ^ f.width) : Fl f) = Fl.ofBits a := by
  apply Fl.ext_toBits
  exact Nat.mod_mod a (2 ^ f.width)

theorem packRounded32_mod (l : Nat) (hl : l ≤ 127) : ∀ z : Nat, z ≤ 2 ^ 23 →
      (Fl.packRounded false (2 ^ 23 + z) ((l : Int) - 23) : FV .f32) =
        Fl.ofBits (((l + 1 + 126) * 2 ^ 23 + z) % 2 ^ 32) := by
    have he : l + 1 + 126 = l + 127 := by omega
    intro z hz
    rw [he]
    exact (packRounded32_guard l z hl hz).trans (ofBits_mod_pattern (f := FTy.f32.fmt) _).symm

theorem packRounded32_tie (l y : Nat) (b : Prop) [Decidable b]
    (hl : l ≤ 127) (hy : y ≤ 2 ^ 23) :
    (Fl.packRounded false
      (if b then (2 ^ 23 + y) - (2 ^ 23 + y) % 2 else 2 ^ 23 + y)
      ((l : Int) - 23) : FV .f32) =
    Fl.ofBits (((l + 1 + 126) * 2 ^ 23 +
      if b then y &&& (2 ^ 32 - 2) else y) % 2 ^ 32) := by
  have hp : ∀ z : Nat, z ≤ 2 ^ 23 →
      (Fl.packRounded false (2 ^ 23 + z) ((l : Int) - 23) : FV .f32) =
        Fl.ofBits (((l + 1 + 126) * 2 ^ 23 + z) % 2 ^ 32) := packRounded32_mod l hl
  have hclear : (2 ^ 23 + y) - (2 ^ 23 + y) % 2 = 2 ^ 23 + (y - y % 2) := by omega
  have hlow := clear_low_bit32 y (by omega)
  have ht : (Fl.packRounded false ((2 ^ 23 + y) - (2 ^ 23 + y) % 2) ((l : Int) - 23) : FV .f32) =
      Fl.ofBits (((l + 1 + 126) * 2 ^ 23 + (y &&& (2 ^ 32 - 2))) % 2 ^ 32) := by
    calc
      _ = Fl.packRounded false (2 ^ 23 + (y - y % 2)) ((l : Int) - 23) :=
        congrArg (fun q => (Fl.packRounded false q ((l : Int) - 23) : FV .f32)) hclear
      _ = _ := by rw [hlow]; exact hp _ (by omega)
  rw [apply_ite (fun q => (Fl.packRounded false q ((l : Int) - 23) : FV .f32)),
    apply_ite (fun z => (Fl.ofBits (((l + 1 + 126) * 2 ^ 23 + z) % 2 ^ 32) : FV .f32))]
  by_cases hb : b
  · simpa only [hb, ↓reduceIte] using ht
  · simpa only [hb, ↓reduceIte] using hp y hy

theorem nat32_large_rounded (n : Nat) (hn : 0 < n) (hn128 : n < 2 ^ 128) (tz : Int)
    (htie : tz = ((n.log2 - 24 : Nat) : Int) ↔ n % 2 ^ (n.log2 - 24) = 0 ∧ n / 2 ^ (n.log2 - 24) % 2 = 1)
    (hsmall : ¬ n.log2 + 1 ≤ 24) :
    (let y0 := (n / 2 ^ (n.log2 + 1 - 25)) % 2 ^ 24
     let y1 := (y0 + 1) / 2
     let y2 := if tz = ((n.log2 + 1 : Nat) : Int) - 25 then y1 &&& (2 ^ 32 - 2) else y1
     Fl.ofBits (((n.log2 + 1 + 126) * 2 ^ 23 + y2) % 2 ^ 32) : FV .f32) =
      Fl.roundRat (n : Int) 1 false := by
  have hn0 : n ≠ 0 := by omega
  have hl : n.log2 ≤ 127 := by
    have h := (Nat.log2_lt hn0).mpr hn128
    omega
  have hl24 : 24 ≤ n.log2 := by omega
  let d := 2 ^ (n.log2 - 24)
  have hd : 0 < d := Nat.two_pow_pos _
  have hpow : 2 ^ (n.log2 - 23) = d * 2 := by
    dsimp [d]
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hpLo : 2 ^ n.log2 = 2 ^ 24 * d := by
    change 2 ^ n.log2 = 2 ^ 24 * 2 ^ (n.log2 - 24)
    rw [← Nat.pow_add]
    congr 1
    omega
  have hpHi : 2 ^ (n.log2 + 1) = 2 ^ 25 * d := by
    change 2 ^ (n.log2 + 1) = 2 ^ 25 * 2 ^ (n.log2 - 24)
    rw [← Nat.pow_add]
    congr 1
    omega
  have hgLo : 2 ^ 24 ≤ n / d := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    rw [← hpLo]
    exact Nat.log2_self_le hn0
  have hgHi : n / d < 2 ^ 25 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    rw [← hpHi]
    exact Nat.lt_log2_self
  have hg : n / d = 2 ^ 24 + n / d % 2 ^ 24 := by omega
  have he : (((n.log2 + 1 : Nat) : Int) - 25) = ((n.log2 - 24 : Nat) : Int) := by omega
  have hshift : n.log2 + 1 - 25 = n.log2 - 24 := by omega
  rw [he, hshift]
  simp only [htie]
  change Fl.ofBits (((n.log2 + 1 + 126) * 2 ^ 23 +
    (if n % d = 0 ∧ n / d % 2 = 1 then
      ((n / d % 2 ^ 24 + 1) / 2) &&& (2 ^ 32 - 2)
     else (n / d % 2 ^ 24 + 1) / 2)) % 2 ^ 32) =
    (Fl.roundRat (n : Int) 1 false : FV .f32)
  have hr := roundRat_nat32_normal n hn hl
  simp only [show 23 ≤ n.log2 by omega, ↓reduceIte, hpow] at hr
  rw [hr, roundQuotient_guard n d hd]
  let y := (n / d % 2 ^ 24 + 1) / 2
  have hy : y ≤ 2 ^ 23 := by
    have h := Nat.mod_lt (n / d) (by decide : 0 < 2 ^ 24)
    dsimp [y]
    omega
  have hyhalf : (n / d + 1) / 2 = 2 ^ 23 + y := by
    dsimp [y]
    omega
  rw [hyhalf]
  dsimp only
  exact (packRounded32_tie n.log2 y (n % d = 0 ∧ n / d % 2 = 1) hl hy).symm


theorem nat32_source_rounded (n : Nat) (hn : 0 < n) (hn128 : n < 2 ^ 128) (tz : Int)
    (htie : tz = ((n.log2 - 24 : Nat) : Int) ↔ n % 2 ^ (n.log2 - 24) = 0 ∧ n / 2 ^ (n.log2 - 24) % 2 = 1) :
    (if n.log2 + 1 ≤ 24 then
      Fl.pack false (n.log2 + 1 + 126) (((n % 2 ^ 32) * 2 ^ (24 - (n.log2 + 1))) % 2 ^ 23)
     else
      let y0 := (n / 2 ^ (n.log2 + 1 - 25)) % 2 ^ 24
      let y1 := (y0 + 1) / 2
      let y2 := if tz = ((n.log2 + 1 : Nat) : Int) - 25 then y1 &&& (2 ^ 32 - 2) else y1
      Fl.ofBits (((n.log2 + 1 + 126) * 2 ^ 23 + y2) % 2 ^ 32) : FV .f32) =
      Fl.roundRat (n : Int) 1 false := by
  by_cases hsmall : n.log2 + 1 ≤ 24
  · simp only [hsmall, ↓reduceIte]
    exact nat32_small_rounded n hn hsmall
  · simp only [hsmall, ↓reduceIte]
    exact nat32_large_rounded n hn hn128 tz htie hsmall

theorem float32_uint128_rounded (x : JInt .u128) :
    Float32_UInt128 x = (Fl.roundRat x.val 1 false : FV .f32) := by
  rw [float32_uint128_spec]
  by_cases hx : x.val = 0
  · simp [hx, Fl.roundRat]
    rfl
  · simp only [hx, ↓reduceIte]
    have hv := val_of_unsigned_pattern (by rfl) x
    have hn0 : pattern x ≠ 0 := by omega
    have hn128 : pattern x < 2 ^ 128 := pattern_lt x
    have hl : (pattern x).log2 < 128 := (Nat.log2_lt hn0).mpr hn128
    have htie := trailing_zeros_tie x ((pattern x).log2 - 24) (by omega)
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at htie
    rw [top_set_bit_log2 x hx, ← hv]
    exact nat32_source_rounded (pattern x) (by omega) hn128 (int.trailing_zeros x).val htie


/-- Full-domain UInt128 conversion to binary32 uses nearest-even IEEE rounding. -/
def Unsigned128Float32Rounded : Prop := ∀ x : JInt .u128,
  Float32_UInt128 x = (Fl.roundRat x.val 1 false : FV .f32)

theorem unsigned128Float32Rounded_proven : Unsigned128Float32Rounded := float32_uint128_rounded

theorem signed128_magnitude_arg (x : JInt .i128) :
    int.remT .u128 (int.abs_Signed x) = uabs_BitSigned x := by
  apply jint_eq
  rw [remT_val]
  change wrapInt .u128 (int.abs_Signed x).val = (int.unsigned (int.abs x)).val
  rw [unsigned_val]
  rfl

theorem signed128_zero_test (x : JInt .i128) :
    int.eq x (int.lit .i64 0) = decide (x.val = 0) := by
  exact JuliaLean.Proofs.base.int.eq_eq x (int.lit .i64 0)

theorem sign_pattern32 (x : JInt .i128) :
    pattern (int.band (int.remT .u32 (int.lshr_Int x (int.lit .i64 96))) (int.lit .u32 0x80000000)) =
      if x.val < 0 then 2 ^ 31 else 0 := by
  have hx := x.property
  change -(2 ^ 127 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 127 - 1 at hx
  have hpat : pattern x = if x.val < 0 then (x.val + 2 ^ 128).toNat else x.val.toNat := by
    unfold pattern
    change (x.val % (2 ^ 128 : Nat)).toNat = _
    by_cases hz : x.val < 0 <;> simp only [hz, ↓reduceIte] <;> omega
  have hshift : pattern (int.lshr_Int x (int.lit .i64 96)) = pattern x / 2 ^ 96 := by
    have h := JuliaLean.Proofs.base.int.pattern_lshr_Int x (int.lit .i64 96) (by decide)
    change pattern (int.lshr_Int x (int.lit .i64 96)) = pattern x / 2 ^ 96 at h
    exact h
  have hlt : pattern (int.lshr_Int x (int.lit .i64 96)) < 2 ^ 32 := by
    rw [hshift]
    have := pattern_lt x
    change pattern x < 2 ^ 128 at this
    omega
  have hval : (int.lshr_Int x (int.lit .i64 96)).val = (pattern x / 2 ^ 96 : Nat) := by
    rw [val_of_signed_small_pattern _ (by change _ < 2 ^ 127; omega), hshift]
  have hrem : pattern (int.remT .u32 (int.lshr_Int x (int.lit .i64 96))) = pattern x / 2 ^ 96 := by
    unfold pattern
    rw [remT_val, hval]
    have hw : wrapInt .u32 (pattern x / 2 ^ 96 : Nat) = (pattern x / 2 ^ 96 : Nat) := by
      apply wrapInt_of_inRange
      simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      rw [hshift] at hlt
      omega
    rw [hw]
    change (((pattern x / 2 ^ 96 : Nat) : Int) % (2 ^ 32 : Nat)).toNat = _
    rw [← Int.natCast_emod, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt (by rw [hshift] at hlt; exact hlt)
  rw [pattern_band, hrem]
  have hm : pattern (int.lit .u32 0x80000000) = 2 ^ 31 := rfl
  rw [hm]
  have hbits : ∀ n : Nat, n < 2 ^ 32 → n &&& 2 ^ 31 =
      if 2 ^ 31 ≤ n then 2 ^ 31 else 0 := by
    intro n hn
    have he : (n &&& 2 ^ 31).testBit 31 = n.testBit 31 := by
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.and_true]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i = 31
    · subst i
      rw [he, Nat.testBit_eq_decide_div_mod_eq]
      by_cases hb : 2 ^ 31 ≤ n
      · simp only [hb, ↓reduceIte]
        rw [show (2 ^ 31 : Nat).testBit 31 = true by decide]
        apply decide_eq_true
        omega
      · simp only [hb, ↓reduceIte, Nat.zero_testBit]
        apply decide_eq_false
        omega
    · rw [Nat.testBit_and, Nat.testBit_two_pow]
      have hne : decide (31 = i) = false := decide_eq_false (Ne.symm hi)
      simp only [hne, Bool.and_false]
      by_cases hb : 2 ^ 31 ≤ n <;>
        simp only [hb, ↓reduceIte, Nat.testBit_two_pow, hne, Nat.zero_testBit]
  rw [hbits _ (by rw [hshift] at hlt; exact hlt), hpat]
  by_cases hn : x.val < 0 <;> simp [hn] <;> omega

theorem signed32_source_bits (x : JInt .i128) :
    let u : JInt .u128 := uabs_BitSigned x
    Float32_Int128 x = Fl.ofBits ((if x.val < 0 then 2 ^ 31 else 0) ||| (Float32_UInt128 u).toBits) := by
  let u : JInt .u128 := uabs_BitSigned x
  change Float32_Int128 x = Fl.ofBits ((if x.val < 0 then 2 ^ 31 else 0) ||| (Float32_UInt128 u).toBits)
  have huval : u.val = if x.val < 0 then -x.val else x.val := (uabsExact_proven .i128 x).2.1 rfl
  have harg : int.remT .u128 (int.abs_Signed x) = u := signed128_magnitude_arg x
  have hzero : int.eq u (int.lit .i64 0) = decide (x.val = 0) := by
    rw [eq_u128_zero, huval]
    apply decide_eq_decide.mpr
    by_cases hs : x.val < 0 <;> simp only [hs, ↓reduceIte] <;> omega
  by_cases hx : x.val = 0
  · rw [Float32_Int128, signed128_zero_test, if_pos (decide_eq_true hx)]
    have hu : u = int.lit .u128 0 := by
      apply jint_eq
      change u.val = 0
      simp only [hx, Int.lt_irrefl, ↓reduceIte] at huval
      exact huval
    rw [hu]
    simp only [hx, Int.lt_irrefl, ↓reduceIte, Nat.zero_or]
    rfl
  · have hre : ∀ a : JInt .u32, reinterpret_Float_Int .f32 a = Fl.ofBits (pattern a) := by
      intro a
      unfold reinterpret_Float_Int bitcast_to_float jlBitcast
      rw [← pattern_fromJInt]
    unfold Float32_Int128 Float32_UInt128
    rw [signed128_zero_test, hzero]
    simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [harg]
    rw [hre, hre, pattern_bor, sign_pattern32]
    generalize ha : pattern (int.add (int.shl_Int
      (int.remT .u32 (int.add (int.top_set_bit u) (int.lit .i64 126)))
      (int.lit .i64 23)) _) = a
    have hlt : a < 2 ^ 32 := by
      rw [← ha]
      exact pattern_lt _
    rw [Fl.toBits_ofBits]
    have hw : FTy.f32.fmt.width = 32 := rfl
    rw [hw, Nat.mod_eq_of_lt hlt]

theorem packRounded_sign32 (s : Bool) (q : Nat) (k : Int)
    (hq : 2 ^ 23 ≤ q ∧ q ≤ 2 ^ 24) (hk : -23 ≤ k ∧ k ≤ 104) :
    (Fl.packRounded s q k : FV .f32) =
      Fl.ofBits ((if s then 2 ^ 31 else 0) ||| (Fl.packRounded false q k : FV .f32).toBits) := by
  have hq0 : (q == 0) = false := by simp; omega
  unfold Fl.packRounded
  simp only [hq0, Bool.false_eq_true, ↓reduceIte, Fl.toBits_ofBits]
  generalize hm : (if q ≥ 2 ^ (FTy.f32.fmt.sb + 1) then q / 2 else q) = m
  generalize hp : (if q ≥ 2 ^ (FTy.f32.fmt.sb + 1) then k + 1 else k) = p
  have hmb : 2 ^ 23 ≤ m ∧ m < 2 ^ 24 := by
    change (if q ≥ 2 ^ 24 then q / 2 else q) = m at hm
    split at hm <;> omega
  have hpb : -23 ≤ p ∧ p ≤ 105 := by split at hp <;> omega
  have hs : FTy.f32.fmt.sb = 23 := rfl
  have hb : FTy.f32.fmt.bias = 127 := rfl
  have he : FTy.f32.fmt.emax = 255 := rfl
  have hw : FTy.f32.fmt.width = 32 := rfl
  have hsign : FTy.f32.fmt.eb + FTy.f32.fmt.sb = 31 := rfl
  simp only [hs, hb, he, hw, hsign, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  simp only [show ((127 : Nat) : Int) = 127 from rfl,
    show ((23 : Nat) : Int) = 23 from rfl, show ((255 : Nat) : Int) = 255 from rfl,
    show FTy.f32.fmt.eb + 23 = 31 from rfl]
  by_cases hov : p + 127 + 23 ≥ 255
  · simp only [hov, ↓reduceIte]
    cases s <;> decide
  · simp only [hov, ↓reduceIte]
    have hmlo : ¬m < 2 ^ 23 := by omega
    simp only [hmlo, ↓reduceIte]
    rw [Fl.toBits_ofBits, hw]
    have hmag : (p + 127 + 23).toNat * 2 ^ 23 + (m - 2 ^ 23) < 2 ^ 31 := by omega
    generalize (p + 127 + 23).toNat * 2 ^ 23 + (m - 2 ^ 23) = mag at hmag ⊢
    rw [Nat.mod_eq_of_lt (by omega : mag < 2 ^ 32)]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.zero_or]
    · simp only [↓reduceIte]
      rw [Nat.or_comm, nat_or_pow mag 31 hmag, Nat.add_comm]

theorem roundRat_int32_normal (n : Int) (hn : n ≠ 0) (hlog : n.natAbs.log2 ≤ 127) :
    (Fl.roundRat n 1 false : FV .f32) =
      Fl.packRounded (decide (n < 0))
        (if 23 ≤ n.natAbs.log2 then Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - 23))
         else n.natAbs * 2 ^ (23 - n.natAbs.log2))
        ((n.natAbs.log2 : Int) - 23) := by
  have hn0 : n.natAbs ≠ 0 := by omega
  have hfloor : Fl.floorLog2Rat n.natAbs 1 = (n.natAbs.log2 : Int) := by
    simpa using Fl.floorLog2Rat_pow n.natAbs 0 hn0
  unfold Fl.roundRat
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    beq_eq_false_iff_ne.mpr hn, hfloor]
  have hupper : ¬((n.natAbs.log2 : Int) ≥ (FTy.f32.fmt.emax : Int) - FTy.f32.fmt.bias) := by
    change ¬((n.natAbs.log2 : Int) ≥ 128)
    omega
  have hlower : ¬((n.natAbs.log2 : Int) < -((FTy.f32.fmt.bias : Int) + FTy.f32.fmt.sb) - 1) := by
    change ¬((n.natAbs.log2 : Int) < -151)
    omega
  rw [if_neg hupper, if_neg hlower]
  have hk : max ((n.natAbs.log2 : Int) - FTy.f32.fmt.sb)
      (1 - (FTy.f32.fmt.bias : Int) - FTy.f32.fmt.sb) = (n.natAbs.log2 : Int) - 23 := by
    change max ((n.natAbs.log2 : Int) - 23) (-149) = (n.natAbs.log2 : Int) - 23
    omega
  rw [hk]
  by_cases he : 23 ≤ n.natAbs.log2
  · have heI : 0 ≤ (n.natAbs.log2 : Int) - 23 := by omega
    have hcast : ((n.natAbs.log2 : Int) - 23).toNat = n.natAbs.log2 - 23 := by omega
    simp only [he, ↓reduceIte, heI, hcast, Nat.one_mul]
  · have heI : ¬(0 ≤ (n.natAbs.log2 : Int) - 23) := by omega
    have hcast : (-((n.natAbs.log2 : Int) - 23)).toNat = 23 - n.natAbs.log2 := by omega
    simp only [he, ↓reduceIte, heI, hcast]
    rw [show n.natAbs * 2 ^ (23 - n.natAbs.log2) = (n.natAbs * 2 ^ (23 - n.natAbs.log2)) * 1 by omega,
      Fl.roundQuotient_exact _ 1 (by decide)]
    simp only [Nat.mul_one]

theorem roundRat_sign32 (n : Int) (hn : n ≠ 0) (hbound : n.natAbs < 2 ^ 128) :
    (Fl.roundRat n 1 false : FV .f32) =
      Fl.ofBits ((if n < 0 then 2 ^ 31 else 0) ||| (Fl.roundRat (n.natAbs : Int) 1 false : FV .f32).toBits) := by
  have ha : n.natAbs ≠ 0 := by omega
  have hl : n.natAbs.log2 ≤ 127 := by
    have h := (Nat.log2_lt ha).mpr hbound
    omega
  rw [roundRat_int32_normal n hn hl,
    roundRat_int32_normal (n.natAbs : Int) (by omega) (by simpa only [Int.natAbs_natCast] using hl)]
  have hfalse : decide ((n.natAbs : Int) < 0) = false := by simp
  simp only [Int.natAbs_natCast, hfalse]
  have hq : 2 ^ 23 ≤ (if 23 ≤ n.natAbs.log2 then Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - 23))
      else n.natAbs * 2 ^ (23 - n.natAbs.log2)) ∧
      (if 23 ≤ n.natAbs.log2 then Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - 23))
      else n.natAbs * 2 ^ (23 - n.natAbs.log2)) ≤ 2 ^ 24 := by
    by_cases he : 23 ≤ n.natAbs.log2
    · simp only [he, ↓reduceIte]
      have hd := Nat.two_pow_pos (n.natAbs.log2 - 23)
      have hp1 : 2 ^ n.natAbs.log2 = 2 ^ 23 * 2 ^ (n.natAbs.log2 - 23) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hp2 : 2 ^ (n.natAbs.log2 + 1) = 2 ^ 24 * 2 ^ (n.natAbs.log2 - 23) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hlow : 2 ^ 23 ≤ n.natAbs / 2 ^ (n.natAbs.log2 - 23) := by
        apply (Nat.le_div_iff_mul_le hd).mpr
        rw [← hp1]
        exact Nat.log2_self_le ha
      have hhi : n.natAbs / 2 ^ (n.natAbs.log2 - 23) < 2 ^ 24 := by
        apply (Nat.div_lt_iff_lt_mul hd).mpr
        rw [← hp2]
        exact Nat.lt_log2_self
      unfold Fl.roundQuotient
      dsimp only
      split <;> omega
    · simp only [he, ↓reduceIte]
      have hn24 : n.natAbs < 2 ^ 24 := (Nat.log2_lt ha).mp (by omega)
      have h := Fl.sig_bounds (f := FTy.f32.fmt) n.natAbs ha hn24
      change n.natAbs.log2 ≤ 23 ∧ 2 ^ 23 ≤ n.natAbs * 2 ^ (23 - n.natAbs.log2) ∧
        n.natAbs * 2 ^ (23 - n.natAbs.log2) < 2 ^ 24 at h
      exact ⟨h.2.1, Nat.le_of_lt h.2.2⟩
  simpa only [decide_eq_true_eq] using
    packRounded_sign32 (decide (n < 0)) _ ((n.natAbs.log2 : Int) - 23) hq ⟨by omega, by omega⟩

theorem float32_int128_rounded (x : JInt .i128) :
    Float32_Int128 x = (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f32) := by
  by_cases hx : x.val = 0
  · rw [Float32_Int128, signed128_zero_test]
    simp only [hx, decide_true, ↓reduceIte]
    rfl
  · have hbound : x.val.natAbs < 2 ^ 128 := by
      have h := x.property
      change -(2 ^ 127 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 127 - 1 at h
      omega
    let u : JInt .u128 := uabs_BitSigned x
    have hu : u.val = (x.val.natAbs : Int) := by
      have h := (uabsExact_proven .i128 x).2.1 rfl
      change u.val = _ at h
      by_cases hs : x.val < 0 <;> simp only [hs, ↓reduceIte] at h <;> omega
    have hsrc := signed32_source_bits x
    change Float32_Int128 x = Fl.ofBits ((if x.val < 0 then 2 ^ 31 else 0) ||| (Float32_UInt128 u).toBits) at hsrc
    rw [hsrc, float32_uint128_rounded u, hu]
    have hz : (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f32) = Fl.roundRat x.val 1 false := by
      unfold Fl.roundRat
      simp only [show ((1 : Nat) == 0) = false from rfl, beq_eq_false_iff_ne.mpr hx,
        Bool.false_eq_true, ↓reduceIte]
    rw [hz]
    exact (roundRat_sign32 x.val hx hbound).symm


/-- Full-domain Int128 conversion to binary32 uses nearest-even IEEE rounding. -/
def Signed128Float32Rounded : Prop := ∀ x : JInt .i128,
  Float32_Int128 x = (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f32)

theorem signed128Float32Rounded_proven : Signed128Float32Rounded := float32_int128_rounded

theorem roundQuotient_scale (a b k : Nat) (hk : 0 < k) :
    Fl.roundQuotient (a * k) (b * k) = Fl.roundQuotient a b := by
  unfold Fl.roundQuotient
  rw [Nat.mul_div_mul_right a b hk, Nat.mul_mod_mul_right]
  dsimp only
  have hgt : 2 * (a % b * k) > b * k ↔ 2 * (a % b) > b := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_lt_mul_right hk
  have heq : 2 * (a % b * k) = b * k ↔ 2 * (a % b) = b := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_right_cancel_iff (by omega)
  have hbeq : (2 * (a % b * k) == b * k) = (2 * (a % b) == b) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq] using heq
  simp only [hgt, hbeq]

theorem roundRat_scale_pow {f : Fmt} (n j : Nat) (s : Bool) :
    (Fl.roundRat ((n * 2 ^ j : Nat) : Int) (2 ^ j) s : Fl f) = Fl.roundRat (n : Int) 1 s := by
  have hp : 2 ^ j ≠ 0 := by have := Nat.two_pow_pos j; omega
  by_cases hn : n = 0
  · subst n
    simp [Fl.roundRat, hp]
  · have hnp : n * 2 ^ j ≠ 0 := Nat.mul_ne_zero hn hp
    have hnneg : decide ((n : Int) < 0) = false := by simp
    have hnpneg : decide (((n * 2 ^ j : Nat) : Int) < 0) = false :=
      decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg _))
    simp only [Fl.roundRat, beq_iff_eq, hp, hn, hnp, Int.natCast_eq_zero,
      Bool.false_eq_true, ↓reduceIte, Int.natAbs_natCast, hnpneg, hnneg]
    rw [Fl.floorLog2Rat_pow (n * 2 ^ j) j hnp, Fl.log2_mul_pow n j hn,
      Fl.floorLog2Rat_pow n 0 hn]
    rw [show ((n.log2 + j : Nat) : Int) - j = (n.log2 : Int) by omega]
    simp only [show ((0 : Nat) : Int) = 0 from rfl, Int.sub_zero,
      show ¬ (1 : Nat) = 0 from by decide, ↓reduceIte]
    split
    · rfl
    · split
      · rfl
      · generalize max ((n.log2 : Int) - f.sb) (1 - (f.bias : Int) - f.sb) = k
        by_cases hk : k ≥ 0
        · simp only [hk, ↓reduceIte, Nat.one_mul]
          rw [Nat.mul_comm (2 ^ j) (2 ^ k.toNat), roundQuotient_scale _ _ _ (Nat.two_pow_pos j)]
        · simp only [hk, ↓reduceIte]
          rw [Nat.mul_right_comm n (2 ^ j) _]
          congr 1
          simpa only [Nat.one_mul] using
            roundQuotient_scale (n * 2 ^ (-k).toNat) 1 (2 ^ j) (Nat.two_pow_pos j)

theorem re_bor_exp64 (e : Nat) (he : e < 2048) (exp_fl : FV .f64)
    (b : JInt .u64) (hexp : exp_fl = Fl.ofBits (e * 2 ^ 52)) (hb : pattern b < 2 ^ 52) :
    reinterpret_Float_Int .f64 (int.bor (reinterpret_Unsigned_Float64 exp_fl) b) =
      Fl.pack false e (pattern b) := by
  have hre : ∀ u : JInt .u64, reinterpret_Float_Int .f64 u = Fl.ofBits (pattern u) := by
    intro u; unfold reinterpret_Float_Int bitcast_to_float jlBitcast
    rw [← pattern_fromJInt]
  have hpat_exp : pattern (reinterpret_Unsigned_Float64 exp_fl) = e * 2 ^ 52 := by
    change pattern (reinterpret_Unsigned exp_fl) = e * 2 ^ 52
    rw [pattern_reinterpret_Unsigned, hexp, Fl.toBits_ofBits]
    have hw : FTy.f64.fmt.width = 64 := rfl
    rw [hw]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hre, pattern_bor, hpat_exp, Nat.or_comm, nat_or_mul_pow (pattern b) e 52 hb]
  unfold Fl.pack; simp [Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hb, Nat.add_comm]

theorem float64_uint128_spec (x : JInt .u128) :
    Float64_UInt128 x =
      if pattern x < 2 ^ 104 then
        let low_val := floatSub (Fl.pack false 1075 (pattern x % 2 ^ 52)) (Fl.pack false 1075 0)
        let high_val := floatSub (Fl.pack false 1127 ((pattern x / 2 ^ 52) % 2 ^ 52)) (Fl.pack false 1127 0)
        floatAdd low_val high_val
      else
        let low_bits := (((pattern x / 2 ^ 12) % 2 ^ 64) / 2 ^ 12) ||| ((pattern x % 2 ^ 64) &&& 0xFFFFFF)
        let low_val := floatSub (Fl.pack false 1099 low_bits) (Fl.pack false 1099 0)
        let high_val := floatSub (Fl.pack false 1151 ((pattern x / 2 ^ 76) % 2 ^ 52)) (Fl.pack false 1151 0)
        floatAdd low_val high_val := by
  unfold Float64_UInt128
  simp only [significand_mask]
  have hx_lt : pattern x < 2 ^ 128 := pattern_lt x
  have h_rem64 : ∀ u : JInt .u128, pattern (int.remT .u64 u) = pattern u % 2 ^ 64 := by
    intro u
    rw [pattern_of_cong _ _ (remT_val .u64 u), ← val_of_unsigned_pattern (by rfl) u]
    change (((pattern u : Int) % (2 ^ 64 : Nat)).toNat) = _
    rw [← Int.natCast_emod, Int.toNat_natCast]
  have h_shr : ∀ (k : JInt .i64), 0 ≤ k.val →
      pattern (int.shr_Int x k) = pattern x / 2 ^ k.val.toNat :=
    fun k hk => pattern_shr_Int_unsigned (by rfl) x k hk
  have hcond : int.lt_BitUnsigned x (int.shl_Int (int.lit .u128 1) (int.lit .i64 104)) =
      decide (pattern x < 2 ^ 104) := by
    unfold int.lt_BitUnsigned
    rw [ult_int_eq rfl]
    have hx_val : x.val = (pattern x : Int) := (val_of_unsigned_pattern (by rfl) x).symm
    have h104 : (int.shl_Int (int.lit .u128 1) (int.lit .i64 104)).val = (2 ^ 104 : Int) := by decide
    rw [hx_val, h104]; apply decide_eq_decide.mpr; omega
  have h_add : ∀ a b : FV .f64, add_float a b = floatAdd a b := by
    intro a b
    unfold add_float jlAddFloat
    exact @finishFloat_eq .f64 _
  have h_sub : ∀ a b : FV .f64, sub_float a b = floatSub a b := by
    intro a b
    unfold sub_float jlSubFloat
    exact @finishFloat_eq .f64 _
  have hsm : pattern significand_mask_Float64 = 2 ^ 52 - 1 := by decide
  rw [hcond]
  by_cases hlt : pattern x < 2 ^ 104
  · simp only [hlt, decide_true, ↓reduceIte]
    have hlow : pattern (int.band (int.remT .u64 x) significand_mask_Float64) = pattern x % 2 ^ 52 := by
      rw [pattern_band]
      change pattern (int.remT .u64 x) &&& pattern significand_mask_Float64 = _
      rw [h_rem64, hsm, nat_and_mask]
      exact Nat.mod_mod_of_dvd (pattern x) (by decide : 2 ^ 52 ∣ 2 ^ 64)
    have hhigh_lt : pattern x / 2 ^ 52 < 2 ^ 52 := by omega
    have hhigh : pattern (int.remT .u64 (int.shr_Int x (int.lit .i64 52))) =
        (pattern x / 2 ^ 52) % 2 ^ 52 := by
      rw [h_rem64, h_shr (int.lit .i64 52) (by decide)]
      have h52 : (int.lit .i64 52).val.toNat = 52 := rfl
      rw [h52, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hhigh_lt]
    have h1 := re_bor_exp64 1075 (by decide) (Fl.ofBits 0x4330000000000000)
      (int.band (int.remT .u64 x) significand_mask_Float64) (by decide) (by rw [hlow]; omega)
    have h2 := re_bor_exp64 1127 (by decide) (Fl.ofBits 0x4670000000000000)
      (int.remT .u64 (int.shr_Int x (int.lit .i64 52))) (by decide) (by rw [hhigh]; omega)
    have hc1 : (Fl.ofBits 0x4330000000000000 : FV .f64) = Fl.pack false 1075 0 := by decide
    have hc2 : (Fl.ofBits 0x4670000000000000 : FV .f64) = Fl.pack false 1127 0 := by decide
    rw [h1, h2, hlow, hhigh, h_add, h_sub, h_sub, hc1, hc2]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hlow_pat : pattern (int.bor (int.shr_Int (int.remT .u64 (int.shr_Int x (int.lit .i64 12))) (int.lit .i64 12))
        (int.band (int.remT .u64 x) (int.lit .u64 0xFFFFFF))) =
        (((pattern x / 2 ^ 12) % 2 ^ 64) / 2 ^ 12) ||| ((pattern x % 2 ^ 64) &&& 0xFFFFFF) := by
      rw [pattern_bor, pattern_shr_Int_unsigned (by rfl) _ _ (by decide),
        h_rem64, h_shr (int.lit .i64 12) (by decide), pattern_band, h_rem64]
      rfl
    have hlow_lt : (((pattern x / 2 ^ 12) % 2 ^ 64) / 2 ^ 12) ||| ((pattern x % 2 ^ 64) &&& 0xFFFFFF) < 2 ^ 52 := by
      have ha : ((pattern x / 2 ^ 12) % 2 ^ 64) / 2 ^ 12 < 2 ^ 52 := by omega
      have hb : (pattern x % 2 ^ 64) &&& 0xFFFFFF < 2 ^ 52 := by
        have : 0xFFFFFF = 2 ^ 24 - 1 := rfl
        rw [this, nat_and_mask]; omega
      exact Nat.or_lt_two_pow ha hb
    have hhigh_lt : pattern x / 2 ^ 76 < 2 ^ 52 := by omega
    have hhigh : pattern (int.remT .u64 (int.shr_Int x (int.lit .i64 76))) =
        (pattern x / 2 ^ 76) % 2 ^ 52 := by
      rw [h_rem64, h_shr (int.lit .i64 76) (by decide)]
      have h76 : (int.lit .i64 76).val.toNat = 76 := rfl
      rw [h76, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hhigh_lt]
    have h1 := re_bor_exp64 1099 (by decide) (Fl.ofBits 0x44b0000000000000)
      (int.bor (int.shr_Int (int.remT .u64 (int.shr_Int x (int.lit .i64 12))) (int.lit .i64 12))
        (int.band (int.remT .u64 x) (int.lit .u64 0xFFFFFF))) (by decide) (by rw [hlow_pat]; exact hlow_lt)
    have h2 := re_bor_exp64 1151 (by decide) (Fl.ofBits 0x47f0000000000000)
      (int.remT .u64 (int.shr_Int x (int.lit .i64 76))) (by decide) (by rw [hhigh]; omega)
    have hc1 : (Fl.ofBits 0x44b0000000000000 : FV .f64) = Fl.pack false 1099 0 := by decide
    have hc2 : (Fl.ofBits 0x47f0000000000000 : FV .f64) = Fl.pack false 1151 0 := by decide
    rw [h1, h2, hlow_pat, hhigh, h_add, h_sub, h_sub, hc1, hc2]


theorem roundRat_exact_nat64 (c p : Nat) (hc : c < 2 ^ 53) (hp : p ≤ 76) :
    let x : FV .f64 := Fl.roundRat ((c * 2 ^ p : Nat) : Int) 1 false
    x.isfinite = true ∧ x.signbit = false ∧ x.toRat.1 = ((c * 2 ^ p : Nat) : Int) * (x.toRat.2 : Int) := by
  dsimp only
  by_cases hc0 : c = 0
  · subst c
    simp only [Nat.zero_mul, Int.natCast_zero, Fl.roundRat, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, by decide⟩
  · have hl : c.log2 ≤ 52 := by have := (Nat.log2_lt hc0).mpr hc; omega
    have hn : ((c * 2 ^ p : Nat) : Int).natAbs = c * 2 ^ p := Int.natAbs_natCast _
    have hlo : 0 + 1 ≤ c.log2 + p + FTy.f64.fmt.bias := by change 1 ≤ c.log2 + p + 1023; omega
    have hhi : c.log2 + p + FTy.f64.fmt.bias < 0 + FTy.f64.fmt.emax := by change c.log2 + p + 1023 < 2047; omega
    have he := Fl.roundRat_key (good_fty .f64) _ c p 0 false hn (by omega) hc hlo hhi
    simp only [Nat.pow_zero, Nat.one_mul, Int.natCast_one, Int.mul_one] at he
    refine ⟨he.1, ?_, ?_⟩
    · rw [Fl.roundRat_normal (good_fty .f64) _ c p 0 false hn (by omega) hc hlo hhi]
      have hq := Fl.sig_bounds (f := FTy.f64.fmt) c hc0 hc
      have hb : c.log2 + p + FTy.f64.fmt.bias - 0 < 2 ^ FTy.f64.fmt.eb := by change c.log2 + p + 1023 < 2048; omega
      have hr : c * 2 ^ (FTy.f64.fmt.sb - c.log2) - 2 ^ FTy.f64.fmt.sb < 2 ^ FTy.f64.fmt.sb := by
        have hpw : 2 ^ (FTy.f64.fmt.sb + 1) = 2 * 2 ^ FTy.f64.fmt.sb := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      simpa only [show decide (((c * 2 ^ p : Nat) : Int) < 0) = false from
        decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg _))] using
        (Fl.pack_parts (f := FTy.f64.fmt) (decide (((c * 2 ^ p : Nat) : Int) < 0)) _ _ hb hr).1
    · have hrat := (Fl.toRat_key (good_fty .f64) _ he.1).2
      apply Int.eq_of_mul_eq_mul_right (a := (FTy.f64.fmt.den : Int)) (by have := FTy.f64.fmt.den_pos; omega)
      rw [hrat, he.2]
      simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

theorem floatAdd_exact_naturals64 (x y : FV .f64) (a b : Nat)
    (hx : x.isfinite = true ∧ x.signbit = false ∧ x.toRat.1 = (a : Int) * (x.toRat.2 : Int))
    (hy : y.isfinite = true ∧ y.signbit = false ∧ y.toRat.1 = (b : Int) * (y.toRat.2 : Int)) :
    floatAdd x y = Fl.roundRat ((a + b : Nat) : Int) 1 false := by
  obtain ⟨_, _, jx, hxr, _, _, _⟩ := Fl.toRat_cases (good_fty .f64) x hx.1
  obtain ⟨_, _, jy, hyr, _, _, _⟩ := Fl.toRat_cases (good_fty .f64) y hy.1
  have hxd : x.toRat.2 = 2 ^ jx := congrArg Prod.snd hxr
  have hyd : y.toRat.2 = 2 ^ jy := congrArg Prod.snd hyr
  unfold floatAdd
  simp only [Fl.isnan_of_finite hx.1, Fl.isnan_of_finite hy.1, Fl.isinf_of_finite hx.1,
    Fl.isinf_of_finite hy.1, Bool.false_eq_true, ↓reduceIte, hx.2.1, hy.2.1, Bool.false_and]
  rw [hx.2.2, hy.2.2]
  have hn : (a : Int) * (x.toRat.2 : Int) * (y.toRat.2 : Int) +
      (b : Int) * (y.toRat.2 : Int) * (x.toRat.2 : Int) =
      ((a + b : Nat) : Int) * ((x.toRat.2 * y.toRat.2 : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hn, hxd, hyd, ← Nat.pow_add, ← Int.natCast_mul]
  exact roundRat_scale_pow (a + b) (jx + jy) false


theorem pack64_integer_rat (s : Bool) (e m : Nat) (he : 1075 ≤ e ∧ e ≤ 1151) (hm : m < 2 ^ 52) :
    let x : FV .f64 := Fl.pack s e m
    x.isfinite = true ∧ x.signbit = s ∧
    x.toRat = ((if s then -(((2 ^ 52 + m) * 2 ^ (e - 1075) : Nat) : Int)
      else (((2 ^ 52 + m) * 2 ^ (e - 1075) : Nat) : Int)), 1) := by
  dsimp only
  have hp := Fl.pack_parts (f := FTy.f64.fmt) s e m (by change e < 2048; omega) hm
  refine ⟨?_, hp.1, ?_⟩
  · simp only [Fl.isfinite, hp.2.1]
    change (e != 2047) = true
    simp; omega
  · unfold Fl.toRat
    have hf : (Fl.pack s e m : FV .f64).isfinite = true := by
      simp only [Fl.isfinite, hp.2.1]
      change (e != 2047) = true
      simp; omega
    simp only [hf, Bool.true_eq_false, ↓reduceIte, hp.1, hp.2.1, hp.2.2.1]
    have he0 : e ≠ 0 := by omega
    simp only [Bool.not_true, Bool.false_eq_true, beq_eq_false_iff_ne.mpr he0, ↓reduceIte]
    have hpower : (e : Int) - (FTy.f64.fmt.bias : Int) - FTy.f64.fmt.sb = (e - 1075 : Nat) := by
      change (e : Int) - 1023 - 52 = (e - 1075 : Nat); omega
    rw [hpower]
    simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
    congr 1
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_comm,
      show FTy.f64.fmt.sb = 52 from rfl, Int.natCast_mul, Int.neg_mul]

theorem neg_pack64_zero (e : Nat) (he : e ≤ 1151) :
    Fl.neg (Fl.pack false e 0 : FV .f64) = Fl.pack true e 0 := by
  have hp := Fl.pack_parts (f := FTy.f64.fmt) false e 0 (by change e < 2048; omega) (Nat.two_pow_pos 52)
  unfold Fl.neg
  rw [hp.1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold Fl.pack
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
  rw [Fl.toBits_ofBits]
  have hw : FTy.f64.fmt.width = 64 := rfl
  have hs : FTy.f64.fmt.eb + FTy.f64.fmt.sb = 63 := rfl
  have hm : e * 2 ^ FTy.f64.fmt.sb < 2 ^ 64 := by change e * 2 ^ 52 < 2 ^ 64; omega
  rw [hw, Nat.mod_eq_of_lt hm]
  congr 1
  rw [hs, Nat.add_comm]

theorem floatSub_pack64_exact (m p : Nat) (hm : m < 2 ^ 52) (hp : p ≤ 76) :
    floatSub (Fl.pack false (1075 + p) m : FV .f64) (Fl.pack false (1075 + p) 0) =
      Fl.roundRat ((m * 2 ^ p : Nat) : Int) 1 false := by
  have hx := pack64_integer_rat false (1075 + p) m (by omega) hm
  have hy := pack64_integer_rat true (1075 + p) 0 (by omega) (Nat.two_pow_pos 52)
  have hz := pack64_integer_rat false (1075 + p) 0 (by omega) (Nat.two_pow_pos 52)
  unfold floatSub
  rw [neg_pack64_zero _ (by omega)]
  unfold floatAdd
  simp only [Fl.isnan_of_finite hx.1, Fl.isnan_of_finite hy.1, Fl.isnan_of_finite hz.1,
    Fl.isinf_of_finite hx.1, Fl.isinf_of_finite hy.1, Bool.false_eq_true, ↓reduceIte,
    hx.2.1, hy.2.1, Bool.false_and, hx.2.2, hy.2.2, Nat.add_sub_cancel_left,
    Nat.add_zero, show ((1 : Nat) : Int) = 1 from rfl, Int.mul_one, Nat.one_mul]
  congr 1
  simp only [Int.natCast_mul, Int.natCast_add, Int.add_mul]
  omega


theorem float64_uint128_intermediate (x : JInt .u128) :
    Float64_UInt128 x =
      Fl.roundRat ((if pattern x < 2 ^ 104 then pattern x else
        (((pattern x / 2 ^ 24) % 2 ^ 52) ||| (pattern x % 2 ^ 24)) * 2 ^ 24 +
        (pattern x / 2 ^ 76) * 2 ^ 76 : Nat) : Int) 1 false := by
  rw [float64_uint128_spec]
  have hn : pattern x < 2 ^ 128 := pattern_lt x
  by_cases hs : pattern x < 2 ^ 104
  · simp only [hs, ↓reduceIte]
    have hm := Nat.mod_lt (pattern x) (Nat.two_pow_pos 52)
    have hh : pattern x / 2 ^ 52 < 2 ^ 52 := by omega
    rw [Nat.mod_eq_of_lt hh]
    rw [floatSub_pack64_exact _ 0 hm (by decide), floatSub_pack64_exact _ 52 hh (by decide)]
    rw [floatAdd_exact_naturals64 _ _ _ _
      (roundRat_exact_nat64 _ 0 (by omega) (by decide))
      (roundRat_exact_nat64 _ 52 (by omega) (by decide))]
    congr 1
    simp only [Nat.pow_zero, Nat.mul_one]
    congr 1
    omega
  · simp only [hs, ↓reduceIte]
    have hl1 : ((pattern x / 2 ^ 12) % 2 ^ 64) / 2 ^ 12 = (pattern x / 2 ^ 24) % 2 ^ 52 := by omega
    have hl2 : (pattern x % 2 ^ 64) &&& 0xFFFFFF = pattern x % 2 ^ 24 := by
      rw [show 0xFFFFFF = 2 ^ 24 - 1 from rfl, nat_and_mask]
      exact Nat.mod_mod_of_dvd _ (by decide)
    rw [hl1, hl2]
    have hl : ((pattern x / 2 ^ 24) % 2 ^ 52 ||| pattern x % 2 ^ 24) < 2 ^ 52 :=
      Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos 52)) (by have := Nat.mod_lt (pattern x) (Nat.two_pow_pos 24); omega)
    have hh : pattern x / 2 ^ 76 < 2 ^ 52 := by omega
    rw [Nat.mod_eq_of_lt hh]
    rw [floatSub_pack64_exact _ 24 hl (by decide), floatSub_pack64_exact _ 76 hh (by decide)]
    exact floatAdd_exact_naturals64 _ _ _ _
      (roundRat_exact_nat64 _ 24 (by omega) (by decide))
      (roundRat_exact_nat64 _ 76 (by omega) (by decide))

theorem nat_or_div_pow (a b r : Nat) (hb : b < 2 ^ r) :
    (a ||| b) / 2 ^ r = a / 2 ^ r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_or, Nat.testBit_div_two_pow]
  have hbit : b.testBit (i + r) = false := by
    have ht := congrArg (fun z : Nat => z.testBit i) (Nat.div_eq_of_lt hb)
    simpa only [Nat.testBit_div_two_pow, Nat.zero_testBit] using ht
  simp only [hbit, Bool.or_false]

theorem nat_or_mod_pow (a b r : Nat) :
    (a ||| b) % 2 ^ r = (a % 2 ^ r) ||| (b % 2 ^ r) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases hi : i < r <;> simp [hi]

theorem nat_or_zero (a b : Nat) : (a ||| b) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha : a = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      have hz := congrArg (fun n : Nat => n.testBit i) h
      simp only [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at hz
      simpa only [Nat.zero_testBit] using hz.1
    have hb : b = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      have hz := congrArg (fun n : Nat => n.testBit i) h
      simp only [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at hz
      simpa only [Nat.zero_testBit] using hz.2
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sticky24_div_guard (n k : Nat) (hk : 49 ≤ k) :
    (((n / 2 ^ 24) ||| (n % 2 ^ 24)) * 2 ^ 24) / 2 ^ (k - 1) = n / 2 ^ (k - 1) := by
  have hb : n % 2 ^ 24 < 2 ^ (k - 25) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt n (Nat.two_pow_pos 24)) (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : 2 ^ (k - 1) = 2 ^ (k - 25) * 2 ^ 24 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hd, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 24), nat_or_div_pow _ _ _ hb]
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ 24)]

theorem sticky24_zero_guard (n k : Nat) (hk : 49 ≤ k) :
    (((n / 2 ^ 24) ||| (n % 2 ^ 24)) * 2 ^ 24) % 2 ^ (k - 1) = 0 ↔ n % 2 ^ (k - 1) = 0 := by
  have hb : n % 2 ^ 24 < 2 ^ (k - 25) :=
    Nat.lt_of_lt_of_le (Nat.mod_lt n (Nat.two_pow_pos 24)) (Nat.pow_le_pow_right (by decide) (by omega))
  have hd : 2 ^ (k - 1) = 2 ^ (k - 25) * 2 ^ 24 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hd, Nat.mul_mod_mul_right, nat_or_mod_pow, Nat.mod_eq_of_lt hb]
  have hz : ∀ a : Nat, a * 2 ^ 24 = 0 ↔ a = 0 := by intro a; omega
  rw [hz, nat_or_zero]
  have hdiv : n % (2 ^ (k - 25) * 2 ^ 24) / 2 ^ 24 = n / 2 ^ 24 % 2 ^ (k - 25) := by
    rw [Nat.mul_comm (2 ^ (k - 25)), Nat.mod_mul_right_div_self]
  have hmod : n % (2 ^ (k - 25) * 2 ^ 24) % 2 ^ 24 = n % 2 ^ 24 := by
    rw [Nat.mul_comm (2 ^ (k - 25)), Nat.mod_mul_right_mod]
  constructor
  · rintro ⟨ha, hb0⟩
    rw [ha] at hdiv
    rw [hb0] at hmod
    omega
  · intro hn
    rw [hn] at hdiv hmod
    simp only [Nat.zero_div, Nat.zero_mod] at hdiv hmod
    exact ⟨hdiv.symm, hmod.symm⟩

theorem roundQuotient_sticky24 (n k : Nat) (hk : 49 ≤ k) :
    Fl.roundQuotient (((n / 2 ^ 24) ||| (n % 2 ^ 24)) * 2 ^ 24) (2 ^ k) =
      Fl.roundQuotient n (2 ^ k) := by
  have hd : 2 ^ k = 2 ^ (k - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  rw [hd, roundQuotient_guard _ _ (Nat.two_pow_pos _), roundQuotient_guard _ _ (Nat.two_pow_pos _)]
  simp only [sticky24_div_guard n k hk, sticky24_zero_guard n k hk]

theorem roundRat_nat64_normal (n : Nat) (hn : 0 < n) (hlog : n.log2 ≤ 1023) :
    (Fl.roundRat (n : Int) 1 false : FV .f64) =
      Fl.packRounded false
        (if 52 ≤ n.log2 then Fl.roundQuotient n (2 ^ (n.log2 - 52))
         else n * 2 ^ (52 - n.log2))
        ((n.log2 : Int) - 52) := by
  have hn0 : n ≠ 0 := by omega
  have hnI : (n : Int) ≠ 0 := by omega
  have hneg : decide ((n : Int) < 0) = false := by simp
  have hfloor : Fl.floorLog2Rat n 1 = (n.log2 : Int) := by
    simpa using Fl.floorLog2Rat_pow n 0 hn0
  unfold Fl.roundRat
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    beq_eq_false_iff_ne.mpr hnI, hneg, Int.natAbs_natCast, hfloor]
  have hupper : ¬((n.log2 : Int) ≥ (FTy.f64.fmt.emax : Int) - FTy.f64.fmt.bias) := by
    change ¬((n.log2 : Int) ≥ 1024)
    omega
  have hlower : ¬((n.log2 : Int) < -((FTy.f64.fmt.bias : Int) + FTy.f64.fmt.sb) - 1) := by
    change ¬((n.log2 : Int) < -1076)
    omega
  rw [if_neg hupper, if_neg hlower]
  have hk : max ((n.log2 : Int) - FTy.f64.fmt.sb)
      (1 - (FTy.f64.fmt.bias : Int) - FTy.f64.fmt.sb) = (n.log2 : Int) - 52 := by
    change max ((n.log2 : Int) - 52) (-1074) = (n.log2 : Int) - 52
    omega
  rw [hk]
  by_cases he : 52 ≤ n.log2
  · have heI : 0 ≤ (n.log2 : Int) - 52 := by omega
    have hcast : ((n.log2 : Int) - 52).toNat = n.log2 - 52 := by omega
    simp only [he, ↓reduceIte, heI, hcast, Nat.one_mul]
  · have heI : ¬(0 ≤ (n.log2 : Int) - 52) := by omega
    have hcast : (-((n.log2 : Int) - 52)).toNat = 52 - n.log2 := by omega
    simp only [he, ↓reduceIte, heI, hcast]
    rw [show n * 2 ^ (52 - n.log2) = (n * 2 ^ (52 - n.log2)) * 1 by omega,
      Fl.roundQuotient_exact _ 1 (by decide)]

    simp only [Nat.mul_one]

theorem roundRat_sticky24_64 (n : Nat) (hlo : 2 ^ 104 ≤ n) (hhi : n < 2 ^ 128) :
    (Fl.roundRat ((((n / 2 ^ 24) ||| (n % 2 ^ 24)) * 2 ^ 24 : Nat) : Int) 1 false : FV .f64) =
      Fl.roundRat (n : Int) 1 false := by
  let m := ((n / 2 ^ 24) ||| (n % 2 ^ 24)) * 2 ^ 24
  have hn0 : n ≠ 0 := by omega
  have hl : 104 ≤ n.log2 := (Nat.le_log2 hn0).mpr hlo
  have hh : n.log2 ≤ 127 := by have := (Nat.log2_lt hn0).mpr hhi; omega
  have hd := Nat.two_pow_pos n.log2
  have hnlow := Nat.log2_self_le hn0
  have hnhigh : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hnqlo : 1 ≤ n / 2 ^ n.log2 := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hnlow)
  have hnqhi : n / 2 ^ n.log2 < 2 := (Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [Nat.pow_succ, Nat.mul_comm] using hnhigh)
  have hnq : n / 2 ^ n.log2 = 1 := by omega
  have hmq := sticky24_div_guard n (n.log2 + 1) (by omega)
  change m / 2 ^ (n.log2 + 1 - 1) = _ at hmq
  rw [show n.log2 + 1 - 1 = n.log2 by omega, hnq] at hmq
  have hmlow : 2 ^ n.log2 ≤ m := by
    simpa only [Nat.one_mul] using
      (Nat.le_div_iff_mul_le hd).mp (show 1 ≤ m / 2 ^ n.log2 by omega)
  have hmhi : m < 2 ^ (n.log2 + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hd).mp (show m / 2 ^ n.log2 < 2 by omega)
    simpa only [Nat.pow_succ, Nat.mul_comm] using h
  have hm0 : m ≠ 0 := by omega
  have hml : m.log2 = n.log2 := by
    have h1 := (Nat.le_log2 hm0).mpr hmlow
    have h2 := (Nat.log2_lt hm0).mpr hmhi
    omega
  change (Fl.roundRat (m : Int) 1 false : FV .f64) = _
  rw [roundRat_nat64_normal m (by omega) (by omega), roundRat_nat64_normal n (by omega) (by omega), hml]
  simp only [show 52 ≤ n.log2 by omega, ↓reduceIte]
  congr 1
  exact roundQuotient_sticky24 n (n.log2 - 52) (by omega)

theorem float64_uint128_rounded (x : JInt .u128) :
    Float64_UInt128 x = (Fl.roundRat x.val 1 false : FV .f64) := by
  rw [float64_uint128_intermediate, ← val_of_unsigned_pattern (by rfl) x]
  by_cases hs : pattern x < 2 ^ 104
  · simp only [hs, ↓reduceIte]
  · simp only [hs, ↓reduceIte]
    have hb : pattern x % 2 ^ 24 < 2 ^ 52 := by have := Nat.mod_lt (pattern x) (Nat.two_pow_pos 24); omega
    have ha := Nat.mod_lt (pattern x / 2 ^ 24) (Nat.two_pow_pos 52)
    have hl : ((pattern x / 2 ^ 24) % 2 ^ 52 ||| pattern x % 2 ^ 24) < 2 ^ 52 := Nat.or_lt_two_pow ha hb
    have hdiv : pattern x / 2 ^ 24 = (pattern x / 2 ^ 24) % 2 ^ 52 + (pattern x / 2 ^ 76) * 2 ^ 52 := by omega
    have hor : (pattern x / 2 ^ 24 ||| pattern x % 2 ^ 24) =
        ((pattern x / 2 ^ 24) % 2 ^ 52 ||| pattern x % 2 ^ 24) + (pattern x / 2 ^ 76) * 2 ^ 52 := by
      conv => lhs; rw [hdiv]
      rw [← nat_or_mul_pow _ _ 52 ha, Nat.or_assoc,
        Nat.or_comm ((pattern x / 2 ^ 76) * 2 ^ 52), ← Nat.or_assoc, nat_or_mul_pow _ _ 52 hl]
    have hnum : ((pattern x / 2 ^ 24) % 2 ^ 52 ||| pattern x % 2 ^ 24) * 2 ^ 24 +
        pattern x / 2 ^ 76 * 2 ^ 76 = (pattern x / 2 ^ 24 ||| pattern x % 2 ^ 24) * 2 ^ 24 := by
      rw [hor, Nat.add_mul]
      omega
    rw [hnum]
    exact roundRat_sticky24_64 (pattern x) (by omega) (pattern_lt x)

theorem sign_pattern64 (x : JInt .i128) :
    pattern (int.shl_Int (int.remT .u64 (int.shr_Int x (int.lit .i64 127))) (int.lit .i64 63)) =
      if x.val < 0 then 2 ^ 63 else 0 := by
  rw [pattern_shl_Int _ _ (by decide), pattern_of_cong _ _ (remT_val .u64 _), JuliaLean.Proofs.base.int.shr127_val]
  have h63 : (int.lit .i64 63).val.toNat = 63 := rfl
  rw [h63]
  by_cases hs : x.val < 0 <;> simp only [hs, ↓reduceIte] <;> rfl

theorem signed64_source_bits (x : JInt .i128) :
    let u : JInt .u128 := uabs_BitSigned x
    Float64_Int128 x = Fl.ofBits ((if x.val < 0 then 2 ^ 63 else 0) ||| (Float64_UInt128 u).toBits) := by
  dsimp only
  have hf_eq : Float64_Int128 x =
      reinterpret_Float_Int .f64 (int.bor
        (int.shl_Int (int.remT .u64 (int.shr_Int x (int.lit .i64 127))) (int.lit .i64 63))
        (reinterpret_Unsigned_Float64 (Float64_UInt128 (uabs_BitSigned x)))) := by
    unfold Float64_Int128 Float64_UInt128
    dsimp only
    exact (apply_ite (fun v => reinterpret_Float_Int .f64 (int.bor
      (int.shl_Int (int.remT .u64 (int.shr_Int x (int.lit .i64 127))) (int.lit .i64 63))
      (reinterpret_Unsigned_Float64 v))) _ _ _).symm
  rw [hf_eq]
  have hre : ∀ a : JInt .u64, reinterpret_Float_Int .f64 a = Fl.ofBits (pattern a) := by
    intro a
    unfold reinterpret_Float_Int bitcast_to_float jlBitcast
    rw [← pattern_fromJInt]
  rw [hre, pattern_bor, sign_pattern64]
  have hp : pattern (reinterpret_Unsigned_Float64 (Float64_UInt128 (uabs_BitSigned x))) =
      (Float64_UInt128 (uabs_BitSigned x)).toBits :=
    @pattern_reinterpret_Unsigned .f64 (Float64_UInt128 (uabs_BitSigned x))
  rw [hp]

theorem packRounded_sign64 (s : Bool) (q : Nat) (k : Int)
    (hq : 2 ^ 52 ≤ q ∧ q ≤ 2 ^ 53) (hk : -52 ≤ k ∧ k ≤ 75) :
    (Fl.packRounded s q k : FV .f64) =
      Fl.ofBits ((if s then 2 ^ 63 else 0) ||| (Fl.packRounded false q k : FV .f64).toBits) := by
  have hq0 : (q == 0) = false := by simp; omega
  unfold Fl.packRounded
  simp only [hq0, Bool.false_eq_true, ↓reduceIte, Fl.toBits_ofBits]
  generalize hm : (if q ≥ 2 ^ (FTy.f64.fmt.sb + 1) then q / 2 else q) = m
  generalize hp : (if q ≥ 2 ^ (FTy.f64.fmt.sb + 1) then k + 1 else k) = p
  have hmb : 2 ^ 52 ≤ m ∧ m < 2 ^ 53 := by
    change (if q ≥ 2 ^ 53 then q / 2 else q) = m at hm
    split at hm <;> omega
  have hpb : -52 ≤ p ∧ p ≤ 76 := by split at hp <;> omega
  have hs : FTy.f64.fmt.sb = 52 := rfl
  have hb : FTy.f64.fmt.bias = 1023 := rfl
  have he : FTy.f64.fmt.emax = 2047 := rfl
  have hw : FTy.f64.fmt.width = 64 := rfl
  have hsign : FTy.f64.fmt.eb + FTy.f64.fmt.sb = 63 := rfl
  simp only [hs, hb, he, hw, hsign, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  simp only [show ((1023 : Nat) : Int) = 1023 from rfl,
    show ((52 : Nat) : Int) = 52 from rfl, show ((2047 : Nat) : Int) = 2047 from rfl,
    show FTy.f64.fmt.eb + 52 = 63 from rfl]
  by_cases hov : p + 1023 + 52 ≥ 2047
  · simp only [hov, ↓reduceIte]
    cases s <;> decide
  · simp only [hov, ↓reduceIte]
    have hmlo : ¬m < 2 ^ 52 := by omega
    simp only [hmlo, ↓reduceIte]
    rw [Fl.toBits_ofBits, hw]
    have hmag : (p + 1023 + 52).toNat * 2 ^ 52 + (m - 2 ^ 52) < 2 ^ 63 := by omega
    generalize (p + 1023 + 52).toNat * 2 ^ 52 + (m - 2 ^ 52) = mag at hmag ⊢
    rw [Nat.mod_eq_of_lt (by omega : mag < 2 ^ 64)]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.zero_or]
    · simp only [↓reduceIte]
      rw [Nat.or_comm, nat_or_pow mag 63 hmag, Nat.add_comm]

theorem roundRat_int64_normal (n : Int) (hn : n ≠ 0) (hlog : n.natAbs.log2 ≤ 127) :
    (Fl.roundRat n 1 false : FV .f64) =
      Fl.packRounded (decide (n < 0))
        (if 52 ≤ n.natAbs.log2 then Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - 52))
         else n.natAbs * 2 ^ (52 - n.natAbs.log2))
        ((n.natAbs.log2 : Int) - 52) := by
  have hn0 : n.natAbs ≠ 0 := by omega
  have hfloor : Fl.floorLog2Rat n.natAbs 1 = (n.natAbs.log2 : Int) := by
    simpa using Fl.floorLog2Rat_pow n.natAbs 0 hn0
  unfold Fl.roundRat
  simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    beq_eq_false_iff_ne.mpr hn, hfloor]
  have hupper : ¬((n.natAbs.log2 : Int) ≥ (FTy.f64.fmt.emax : Int) - FTy.f64.fmt.bias) := by
    change ¬((n.natAbs.log2 : Int) ≥ 1024)
    omega
  have hlower : ¬((n.natAbs.log2 : Int) < -((FTy.f64.fmt.bias : Int) + FTy.f64.fmt.sb) - 1) := by
    change ¬((n.natAbs.log2 : Int) < -1076)
    omega
  rw [if_neg hupper, if_neg hlower]
  have hk : max ((n.natAbs.log2 : Int) - FTy.f64.fmt.sb)
      (1 - (FTy.f64.fmt.bias : Int) - FTy.f64.fmt.sb) = (n.natAbs.log2 : Int) - 52 := by
    change max ((n.natAbs.log2 : Int) - 52) (-1074) = (n.natAbs.log2 : Int) - 52
    omega
  rw [hk]
  by_cases he : 52 ≤ n.natAbs.log2
  · have heI : 0 ≤ (n.natAbs.log2 : Int) - 52 := by omega
    have hcast : ((n.natAbs.log2 : Int) - 52).toNat = n.natAbs.log2 - 52 := by omega
    simp only [he, ↓reduceIte, heI, hcast, Nat.one_mul]
  · have heI : ¬(0 ≤ (n.natAbs.log2 : Int) - 52) := by omega
    have hcast : (-((n.natAbs.log2 : Int) - 52)).toNat = 52 - n.natAbs.log2 := by omega
    simp only [he, ↓reduceIte, heI, hcast]
    rw [show n.natAbs * 2 ^ (52 - n.natAbs.log2) = (n.natAbs * 2 ^ (52 - n.natAbs.log2)) * 1 by omega,
      Fl.roundQuotient_exact _ 1 (by decide)]
    simp only [Nat.mul_one]

theorem roundRat_sign64 (n : Int) (hn : n ≠ 0) (hbound : n.natAbs < 2 ^ 128) :
    (Fl.roundRat n 1 false : FV .f64) =
      Fl.ofBits ((if n < 0 then 2 ^ 63 else 0) ||| (Fl.roundRat (n.natAbs : Int) 1 false : FV .f64).toBits) := by
  have ha : n.natAbs ≠ 0 := by omega
  have hl : n.natAbs.log2 ≤ 127 := by
    have h := (Nat.log2_lt ha).mpr hbound
    omega
  rw [roundRat_int64_normal n hn hl,
    roundRat_int64_normal (n.natAbs : Int) (by omega) (by simpa only [Int.natAbs_natCast] using hl)]
  have hfalse : decide ((n.natAbs : Int) < 0) = false := by simp
  simp only [Int.natAbs_natCast, hfalse]
  have hq : 2 ^ 52 ≤ (if 52 ≤ n.natAbs.log2 then Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - 52))
      else n.natAbs * 2 ^ (52 - n.natAbs.log2)) ∧
      (if 52 ≤ n.natAbs.log2 then Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - 52))
      else n.natAbs * 2 ^ (52 - n.natAbs.log2)) ≤ 2 ^ 53 := by
    by_cases he : 52 ≤ n.natAbs.log2
    · simp only [he, ↓reduceIte]
      have hd := Nat.two_pow_pos (n.natAbs.log2 - 52)
      have hp1 : 2 ^ n.natAbs.log2 = 2 ^ 52 * 2 ^ (n.natAbs.log2 - 52) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hp2 : 2 ^ (n.natAbs.log2 + 1) = 2 ^ 53 * 2 ^ (n.natAbs.log2 - 52) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hlow : 2 ^ 52 ≤ n.natAbs / 2 ^ (n.natAbs.log2 - 52) := by
        apply (Nat.le_div_iff_mul_le hd).mpr
        rw [← hp1]
        exact Nat.log2_self_le ha
      have hhi : n.natAbs / 2 ^ (n.natAbs.log2 - 52) < 2 ^ 53 := by
        apply (Nat.div_lt_iff_lt_mul hd).mpr
        rw [← hp2]
        exact Nat.lt_log2_self
      unfold Fl.roundQuotient
      dsimp only
      split <;> omega
    · simp only [he, ↓reduceIte]
      have hn53 : n.natAbs < 2 ^ 53 := (Nat.log2_lt ha).mp (by omega)
      have h := Fl.sig_bounds (f := FTy.f64.fmt) n.natAbs ha hn53
      change n.natAbs.log2 ≤ 52 ∧ 2 ^ 52 ≤ n.natAbs * 2 ^ (52 - n.natAbs.log2) ∧
        n.natAbs * 2 ^ (52 - n.natAbs.log2) < 2 ^ 53 at h
      exact ⟨h.2.1, Nat.le_of_lt h.2.2⟩
  simpa only [decide_eq_true_eq] using
    packRounded_sign64 (decide (n < 0)) _ ((n.natAbs.log2 : Int) - 52) hq ⟨by omega, by omega⟩

theorem float64_int128_rounded (x : JInt .i128) :
    Float64_Int128 x = (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f64) := by
  by_cases hx : x.val = 0
  · rw [signed64_source_bits]
    have hu : (uabs_BitSigned x : JInt .u128) = int.lit .u128 0 := by
      apply jint_eq
      change (uabs_BitSigned x).val = 0
      have h := (uabsExact_proven .i128 x).2.1 rfl
      simpa only [hx, Int.lt_irrefl, ↓reduceIte] using h
    rw [hu, float64_uint128_rounded]
    simp only [hx, Int.lt_irrefl, ↓reduceIte, Nat.zero_or]
    rfl
  · have hbound : x.val.natAbs < 2 ^ 128 := by
      have h := x.property
      change -(2 ^ 127 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 127 - 1 at h
      omega
    let u : JInt .u128 := uabs_BitSigned x
    have hu : u.val = (x.val.natAbs : Int) := by
      have h := (uabsExact_proven .i128 x).2.1 rfl
      change u.val = _ at h
      by_cases hs : x.val < 0 <;> simp only [hs, ↓reduceIte] at h <;> omega
    have hsrc := signed64_source_bits x
    change Float64_Int128 x = Fl.ofBits ((if x.val < 0 then 2 ^ 63 else 0) ||| (Float64_UInt128 u).toBits) at hsrc
    rw [hsrc, float64_uint128_rounded u, hu]
    have hz : (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f64) = Fl.roundRat x.val 1 false := by
      unfold Fl.roundRat
      simp only [show ((1 : Nat) == 0) = false from rfl, beq_eq_false_iff_ne.mpr hx,
        Bool.false_eq_true, ↓reduceIte]
    rw [hz]
    exact (roundRat_sign64 x.val hx hbound).symm


/-- Full-domain UInt128 conversion to binary64 uses nearest-even IEEE rounding. -/
def Unsigned128Float64Rounded : Prop := ∀ x : JInt .u128,
  Float64_UInt128 x = (Fl.roundRat x.val 1 false : FV .f64)

theorem unsigned128Float64Rounded_proven : Unsigned128Float64Rounded := float64_uint128_rounded

/-- Full-domain Int128 conversion to binary64 uses nearest-even IEEE rounding. -/
def Signed128Float64Rounded : Prop := ∀ x : JInt .i128,
  Float64_Int128 x = (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f64)

theorem signed128Float64Rounded_proven : Signed128Float64Rounded := float64_int128_rounded

theorem nat64_q_bounds (n : Nat) (hn0 : n ≠ 0) : 2 ^ 52 ≤ (if 52 ≤ n.log2 then Fl.roundQuotient n (2 ^ (n.log2 - 52))
    else n * 2 ^ (52 - n.log2)) ∧
    (if 52 ≤ n.log2 then Fl.roundQuotient n (2 ^ (n.log2 - 52))
    else n * 2 ^ (52 - n.log2)) ≤ 2 ^ 53 := by
  by_cases he : 52 ≤ n.log2
  · simp only [he, ↓reduceIte]
    have hd := Nat.two_pow_pos (n.log2 - 52)
    have hp1 : 2 ^ n.log2 = 2 ^ 52 * 2 ^ (n.log2 - 52) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hp2 : 2 ^ (n.log2 + 1) = 2 ^ 53 * 2 ^ (n.log2 - 52) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hlow : 2 ^ 52 ≤ n / 2 ^ (n.log2 - 52) := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      rw [← hp1]
      exact Nat.log2_self_le hn0
    have hhi : n / 2 ^ (n.log2 - 52) < 2 ^ 53 := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      rw [← hp2]
      exact Nat.lt_log2_self
    unfold Fl.roundQuotient
    dsimp only
    split <;> omega
  · simp only [he, ↓reduceIte]
    have hn53 : n < 2 ^ 53 := (Nat.log2_lt hn0).mp (by omega)
    have h := Fl.sig_bounds (f := FTy.f64.fmt) n hn0 hn53
    change n.log2 ≤ 52 ∧ 2 ^ 52 ≤ n * 2 ^ (52 - n.log2) ∧
      n * 2 ^ (52 - n.log2) < 2 ^ 53 at h
    exact ⟨h.2.1, Nat.le_of_lt h.2.2⟩


theorem nat64_large_pack (n : Nat) (hn : 2 ^ 16 ≤ n) (hb : n < 2 ^ 128) :
    ∃ e m : Nat, 1039 ≤ e ∧ e ≤ 1151 ∧ m < 2 ^ 52 ∧
      (Fl.roundRat (n : Int) 1 false : FV .f64) = Fl.pack false e m := by
  have hn0 : n ≠ 0 := by omega
  have hl : 16 ≤ n.log2 := (Nat.le_log2 hn0).mpr hn
  have hh : n.log2 ≤ 127 := by have := (Nat.log2_lt hn0).mpr hb; omega
  rw [roundRat_nat64_normal n (by omega) (by omega)]
  have hq := nat64_q_bounds n hn0
  generalize (if 52 ≤ n.log2 then Fl.roundQuotient n (2 ^ (n.log2 - 52)) else n * 2 ^ (52 - n.log2)) = q at hq ⊢
  by_cases hc : q < 2 ^ 53
  · rw [Fl.packRounded_normal false q ((n.log2 : Int) - 52) hq.1 hc (by change (n.log2 : Int) - 52 + 1023 + 52 < 2047; omega)]
    refine ⟨n.log2 + 1023, q - 2 ^ 52, by omega, by omega, by omega, ?_⟩
    congr 1
    change ((n.log2 : Int) - 52 + 1023 + 52).toNat = n.log2 + 1023
    omega
  · have heq : q = 2 ^ 53 := by omega
    subst q
    refine ⟨n.log2 + 1024, 0, by omega, by omega, Nat.two_pow_pos 52, ?_⟩
    unfold Fl.packRounded Fl.pack
    have hs : FTy.f64.fmt.sb = 52 := rfl
    have hbi : FTy.f64.fmt.bias = 1023 := rfl
    have hem : FTy.f64.fmt.emax = 2047 := rfl
    have heb : FTy.f64.fmt.eb = 11 := rfl
    simp only [hs, hbi, hem, heb, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    have ho : ¬((n.log2 : Int) - 52 + 1 + (1023 : Nat) + (52 : Nat) ≥ (2047 : Nat)) := by omega
    simp only [show ((2 ^ 53 : Nat) == 0) = false from by decide,
      show (2 ^ 53 : Nat) ≥ 2 ^ (52 + 1) from by decide,
      show (2 ^ 53 : Nat) / 2 = 2 ^ 52 from rfl,
      Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl, ho, Nat.sub_self, Nat.add_zero]
    apply congrArg (fun v => (Fl.ofBits v : FV .f64))
    have he : ((n.log2 : Int) - 52 + 1 + (1023 : Nat) + (52 : Nat)).toNat = n.log2 + 1024 := by omega
    rw [he]


theorem roundRat16_overflow_dyadic (c i j : Nat) (s z : Bool) (hc : c ≠ 0)
    (hlarge : j + 16 ≤ c.log2 + i) :
    (Fl.roundRat (if s then -((c * 2 ^ i : Nat) : Int) else ((c * 2 ^ i : Nat) : Int))
      (2 ^ j) z : FV .f16) = Fl.inf s := by
  have hp : 2 ^ j ≠ 0 := by have := Nat.two_pow_pos j; omega
  have hcp : 0 < c * 2 ^ i := Nat.mul_pos (by omega) (Nat.two_pow_pos i)
  have habs : (if s then -((c * 2 ^ i : Nat) : Int) else ((c * 2 ^ i : Nat) : Int)).natAbs = c * 2 ^ i := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
  have hn0 : (if s then -((c * 2 ^ i : Nat) : Int) else ((c * 2 ^ i : Nat) : Int)) ≠ 0 := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hsign : decide ((if s then -((c * 2 ^ i : Nat) : Int) else ((c * 2 ^ i : Nat) : Int)) < 0) = s := by
    cases s
    · exact decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg _))
    · change decide (-((c * 2 ^ i : Nat) : Int) < 0) = true
      exact decide_eq_true (by omega)
  unfold Fl.roundRat
  simp only [beq_iff_eq, hp, hn0, ↓reduceIte, habs, hsign]
  rw [Fl.floorLog2Rat_pow _ _ (by omega), Fl.log2_mul_pow c i hc]
  have he : ((c.log2 + i : Nat) : Int) - j ≥ (FTy.f16.fmt.emax : Int) - FTy.f16.fmt.bias := by
    change ((c.log2 + i : Nat) : Int) - j ≥ 16
    omega
  simp only [he, ↓reduceIte]

theorem convert64_half_overflow_pack (s : Bool) (e m : Nat)
    (he : 1039 ≤ e ∧ e ≤ 1151) (hm : m < 2 ^ 52) :
    (Fl.convert (Fl.pack s e m : FV .f64) : FV .f16) = Fl.inf s := by
  have hp := Fl.pack_parts (f := FTy.f64.fmt) s e m (by change e < 2048; omega) hm
  have hfin : (Fl.pack s e m : FV .f64).isfinite = true := by
    simp only [Fl.isfinite, hp.2.1]
    change (e != 2047) = true
    simp; omega
  have hM : (m + 2 ^ 52).log2 = 52 := by
    have hn0 : m + 2 ^ 52 ≠ 0 := by omega
    have hl := (Nat.le_log2 hn0).mpr (show 2 ^ 52 ≤ m + 2 ^ 52 by omega)
    have hh := (Nat.log2_lt hn0).mpr (show m + 2 ^ 52 < 2 ^ 53 by omega)
    omega
  unfold Fl.convert
  simp only [show (FTy.f16.fmt == FTy.f64.fmt) = false from by decide,
    Bool.false_eq_true, ↓reduceIte, Fl.isnan_of_finite hfin, Fl.isinf_of_finite hfin]
  unfold Fl.toRat
  simp only [hfin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp.1, hp.2.1, hp.2.2.1,
    show (e == 0) = false from beq_eq_false_iff_ne.mpr (by omega), show FTy.f64.fmt.sb = 52 from rfl,
    show ((52 : Nat) : Int) = 52 from rfl]
  by_cases hge : 0 ≤ (e : Int) - FTy.f64.fmt.bias - 52
  · simp only [hge, ↓reduceIte]
    have hnum : (if s then -((m + 2 ^ 52 : Nat) : Int) else ((m + 2 ^ 52 : Nat) : Int)) *
        ((2 ^ ((e : Int) - FTy.f64.fmt.bias - 52).toNat : Nat) : Int) =
        if s then -(((m + 2 ^ 52) * 2 ^ ((e : Int) - FTy.f64.fmt.bias - 52).toNat : Nat) : Int)
        else (((m + 2 ^ 52) * 2 ^ ((e : Int) - FTy.f64.fmt.bias - 52).toNat : Nat) : Int) := by
      cases s <;> simp [Int.neg_mul]
    rw [hnum]
    exact roundRat16_overflow_dyadic (m + 2 ^ 52) _ 0 s s (by omega) (by rw [hM]; omega)
  · have hlt : ¬(0 ≤ (e : Int) - FTy.f64.fmt.bias - 52) := hge
    simp only [hlt, ↓reduceIte]
    change (Fl.roundRat (if s then -((m + 2 ^ 52 : Nat) : Int) else ((m + 2 ^ 52 : Nat) : Int))
      (2 ^ (-((e : Int) - FTy.f64.fmt.bias - 52)).toNat) s : FV .f16) = _
    have h0 : (if s then -(((m + 2 ^ 52) * 2 ^ 0 : Nat) : Int) else (((m + 2 ^ 52) * 2 ^ 0 : Nat) : Int)) =
        (if s then -((m + 2 ^ 52 : Nat) : Int) else ((m + 2 ^ 52 : Nat) : Int)) := by simp
    rw [← h0]
    apply roundRat16_overflow_dyadic
    · omega
    · rw [hM]
      change (-((e : Int) - 1023 - 52)).toNat + 16 ≤ 52 + 0
      change ¬ (0 ≤ (e : Int) - 1023 - 52) at hge
      omega


theorem convert64_nat_half (n : Nat) (hb : n < 2 ^ 128) :
    (Fl.convert (Fl.roundRat (n : Int) 1 false : FV .f64) : FV .f16) = Fl.roundRat (n : Int) 1 false := by
  by_cases hs : n < 2 ^ 16
  · have hx := roundRat_exact_nat64 n 0 (by omega) (by decide)
    simp only [Nat.pow_zero, Nat.mul_one] at hx
    obtain ⟨_, _, j, hr, _, _, _⟩ := Fl.toRat_cases (good_fty .f64) (Fl.roundRat (n : Int) 1 false) hx.1
    have hd : (Fl.roundRat (n : Int) 1 false : FV .f64).toRat.2 = 2 ^ j := congrArg Prod.snd hr
    unfold Fl.convert
    simp only [show (FTy.f16.fmt == FTy.f64.fmt) = false from by decide,
      Bool.false_eq_true, ↓reduceIte, Fl.isnan_of_finite hx.1, Fl.isinf_of_finite hx.1, hx.2.1]
    rw [hx.2.2, hd, ← Int.natCast_mul]
    exact roundRat_scale_pow n j false
  · obtain ⟨e, m, helo, hehi, hm, he⟩ := nat64_large_pack n (by omega) hb
    rw [he, convert64_half_overflow_pack false e m ⟨helo, hehi⟩ hm]
    have hn0 : n ≠ 0 := by omega
    have hl : 16 ≤ n.log2 := (Nat.le_log2 hn0).mpr (by omega)
    have hround : (Fl.roundRat (n : Int) 1 false : FV .f16) = Fl.inf false := by
      simpa only [Bool.false_eq_true, ↓reduceIte, Nat.pow_zero, Nat.mul_one] using
        roundRat16_overflow_dyadic n 0 0 false false hn0 (by omega)
    exact hround.symm

theorem float16_uint128_rounded (x : JInt .u128) :
    Float16_UInt128 Float16_Float64 x = (Fl.roundRat x.val 1 false : FV .f16) := by
  have hc : ∀ v : FV .f64, fptrunc .f16 v = (Fl.convert v : FV .f16) :=
    fun v => @convertFloat_eq .f16 .f64 v
  unfold Float16_UInt128 Float16_Float64
  rw [hc, float64_uint128_rounded, ← val_of_unsigned_pattern (by rfl) x]
  exact convert64_nat_half (pattern x) (pattern_lt x)

theorem roundRat_signed_scale_pow {f : Fmt} (n j : Nat) (s z : Bool) :
    (Fl.roundRat (if s then -((n * 2 ^ j : Nat) : Int) else ((n * 2 ^ j : Nat) : Int)) (2 ^ j) z : Fl f) =
      Fl.roundRat (if s then -(n : Int) else (n : Int)) 1 z := by
  have hp : 2 ^ j ≠ 0 := by have := Nat.two_pow_pos j; omega
  by_cases hn : n = 0
  · subst n
    cases s <;> simp [Fl.roundRat]
  · have hnp : n * 2 ^ j ≠ 0 := Nat.mul_ne_zero hn hp
    have hpos : 0 < n * 2 ^ j := by omega
    have hnum0 : (if s then -((n * 2 ^ j : Nat) : Int) else ((n * 2 ^ j : Nat) : Int)) ≠ 0 := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hn0 : (if s then -(n : Int) else (n : Int)) ≠ 0 := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hnpabs : (if s then -((n * 2 ^ j : Nat) : Int) else ((n * 2 ^ j : Nat) : Int)).natAbs = n * 2 ^ j := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    have hnabs : (if s then -(n : Int) else (n : Int)).natAbs = n := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    have hsn : decide ((if s then -(n : Int) else (n : Int)) < 0) = s := by
      cases s
      · exact decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg _))
      · change decide (-(n : Int) < 0) = true
        exact decide_eq_true (by omega)
    have hsnp : decide ((if s then -((n * 2 ^ j : Nat) : Int) else ((n * 2 ^ j : Nat) : Int)) < 0) = s := by
      cases s
      · exact decide_eq_false (Int.not_lt.mpr (Int.natCast_nonneg _))
      · change decide (-((n * 2 ^ j : Nat) : Int) < 0) = true
        exact decide_eq_true (by omega)
    simp only [Fl.roundRat, beq_iff_eq, hp, hnum0, hn0, ↓reduceIte, hnpabs, hnabs, hsn, hsnp]
    rw [Fl.floorLog2Rat_pow (n * 2 ^ j) j hnp, Fl.log2_mul_pow n j hn,
      Fl.floorLog2Rat_pow n 0 hn]
    rw [show ((n.log2 + j : Nat) : Int) - j = (n.log2 : Int) by omega]
    simp only [show ((0 : Nat) : Int) = 0 from rfl, Int.sub_zero,
      show ¬ (1 : Nat) = 0 from by decide, ↓reduceIte]
    split
    · rfl
    · split
      · rfl
      · generalize max ((n.log2 : Int) - f.sb) (1 - (f.bias : Int) - f.sb) = k
        by_cases hk : k ≥ 0
        · simp only [hk, ↓reduceIte, Nat.one_mul]
          rw [Nat.mul_comm (2 ^ j) (2 ^ k.toNat), roundQuotient_scale _ _ _ (Nat.two_pow_pos j)]
        · simp only [hk, ↓reduceIte]
          rw [Nat.mul_right_comm n (2 ^ j) _]
          congr 1
          simpa only [Nat.one_mul] using
            roundQuotient_scale (n * 2 ^ (-k).toNat) 1 (2 ^ j) (Nat.two_pow_pos j)

theorem roundRat_zeroSign_irrel {f : Fmt} (n : Int) (d : Nat) (a b : Bool) (hn : n ≠ 0) :
    (Fl.roundRat n d a : Fl f) = Fl.roundRat n d b := by
  unfold Fl.roundRat
  simp only [beq_eq_false_iff_ne.mpr hn, Bool.false_eq_true, ↓reduceIte]

theorem roundRat_exact_int64 (n : Int) (hn : n.natAbs < 2 ^ 53) :
    let x : FV .f64 := Fl.roundRat n 1 false
    x.isfinite = true ∧ x.toRat.1 = n * (x.toRat.2 : Int) := by
  dsimp only
  by_cases hn0 : n = 0
  · subst n
    exact ⟨by decide, by decide⟩
  · have hc0 : n.natAbs ≠ 0 := by omega
    have hl : n.natAbs.log2 ≤ 52 := by have := (Nat.log2_lt hc0).mpr hn; omega
    have he := Fl.roundRat_key (good_fty .f64) n n.natAbs 0 0 false (by simp) (by omega) hn
      (by change 1 ≤ n.natAbs.log2 + 0 + 1023; omega)
      (by change n.natAbs.log2 + 0 + 1023 < 0 + 2047; omega)
    simp only [Nat.pow_zero, Int.natCast_one, Int.mul_one] at he
    refine ⟨he.1, ?_⟩
    have hr := (Fl.toRat_key (good_fty .f64) _ he.1).2
    apply Int.eq_of_mul_eq_mul_right (a := (FTy.f64.fmt.den : Int)) (by have := FTy.f64.fmt.den_pos; omega)
    rw [hr, he.2]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem pack64_add_sign (s : Bool) (e m : Nat) (he : e ≤ 1151) (hm : m < 2 ^ 52) :
    (Fl.ofBits ((if s then 2 ^ 63 else 0) ||| (Fl.pack false e m : FV .f64).toBits) : FV .f64) = Fl.pack s e m := by
  unfold Fl.pack
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  rw [Fl.toBits_ofBits]
  have hw : FTy.f64.fmt.width = 64 := rfl
  have hs : FTy.f64.fmt.eb + FTy.f64.fmt.sb = 63 := rfl
  have hf : FTy.f64.fmt.sb = 52 := rfl
  have hmag : e * 2 ^ 52 + m < 2 ^ 63 := by omega
  rw [hw, hs, hf, Nat.mod_eq_of_lt (by omega)]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_or, Nat.zero_add]
  · simp only [↓reduceIte]
    rw [Nat.or_comm, nat_or_pow _ _ hmag]
    apply congrArg (fun a => (Fl.ofBits a : FV .f64))
    omega

theorem convert64_signed_int_half (n : Int) (hb : n.natAbs < 2 ^ 128) :
    (Fl.convert (Fl.roundRat n 1 false : FV .f64) : FV .f16) = Fl.roundRat n 1 false := by
  by_cases hn0 : n = 0
  · subst n
    exact convert64_nat_half 0 (by decide)
  · have hnrepr : n = if n < 0 then -(n.natAbs : Int) else (n.natAbs : Int) := by
      by_cases hs : n < 0 <;> simp only [hs, ↓reduceIte] <;> omega
    by_cases hs : n.natAbs < 2 ^ 16
    · have hx := roundRat_exact_int64 n (by omega)
      obtain ⟨_, _, j, hr, _, _, _⟩ := Fl.toRat_cases (good_fty .f64) (Fl.roundRat n 1 false) hx.1
      have hd : (Fl.roundRat n 1 false : FV .f64).toRat.2 = 2 ^ j := congrArg Prod.snd hr
      unfold Fl.convert
      simp only [show (FTy.f16.fmt == FTy.f64.fmt) = false from by decide,
        Bool.false_eq_true, ↓reduceIte, Fl.isnan_of_finite hx.1, Fl.isinf_of_finite hx.1]
      rw [hx.2, hd]
      have hnum : n * ((2 ^ j : Nat) : Int) =
          if n < 0 then -((n.natAbs * 2 ^ j : Nat) : Int) else ((n.natAbs * 2 ^ j : Nat) : Int) := by
        by_cases hneg : n < 0
        · have hv : n = -(n.natAbs : Int) := by omega
          simp only [hneg, ↓reduceIte, Int.natCast_mul]
          calc n * ((2 ^ j : Nat) : Int) = -(n.natAbs : Int) * ((2 ^ j : Nat) : Int) :=
              congrArg (fun a => a * ((2 ^ j : Nat) : Int)) hv
            _ = _ := Int.neg_mul _ _
        · have hv : n = (n.natAbs : Int) := by omega
          simp only [hneg, ↓reduceIte, Int.natCast_mul]
          exact congrArg (fun a => a * ((2 ^ j : Nat) : Int)) hv
      rw [hnum]
      have hscale := roundRat_signed_scale_pow (f := FTy.f16.fmt) n.natAbs j (decide (n < 0)) (Fl.roundRat n 1 false : FV .f64).signbit
      simp only [decide_eq_true_eq, ← hnrepr] at hscale
      rw [hscale]
      exact roundRat_zeroSign_irrel n 1 _ false hn0
    · have hc0 : n.natAbs ≠ 0 := by omega
      have hl : 16 ≤ n.natAbs.log2 := (Nat.le_log2 hc0).mpr (by omega)
      rw [roundRat_sign64 n hn0 hb]
      obtain ⟨e, m, helo, hehi, hm, he⟩ := nat64_large_pack n.natAbs (by omega) hb
      rw [he]
      have hsgn : (Fl.ofBits ((if n < 0 then 2 ^ 63 else 0) ||| (Fl.pack false e m : FV .f64).toBits) : FV .f64) =
          Fl.pack (decide (n < 0)) e m := by
        simpa only [decide_eq_true_eq] using pack64_add_sign (decide (n < 0)) e m hehi hm
      rw [hsgn, convert64_half_overflow_pack _ e m ⟨helo, hehi⟩ hm]
      have hr := roundRat16_overflow_dyadic n.natAbs 0 0 (decide (n < 0)) false hc0 (by omega)
      simp only [Nat.pow_zero, Nat.mul_one, decide_eq_true_eq, ← hnrepr] at hr
      exact hr.symm

theorem float16_int128_rounded (x : JInt .i128) :
    Float16_Int128 Float16_Float64 x = (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f16) := by
  have hc : ∀ v : FV .f64, fptrunc .f16 v = (Fl.convert v : FV .f16) :=
    fun v => @convertFloat_eq .f16 .f64 v
  have hb : x.val.natAbs < 2 ^ 128 := by
    have h := x.property
    change -(2 ^ 127 : Int) ≤ x.val ∧ x.val ≤ 2 ^ 127 - 1 at h
    omega
  have hz : (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV .f64) = Fl.roundRat x.val 1 false := by
    by_cases hx : x.val = 0
    · simp only [hx, Int.lt_irrefl, decide_false]
    · exact roundRat_zeroSign_irrel x.val 1 _ false hx
  unfold Float16_Int128 Float16_Float64
  rw [hc, float64_int128_rounded, hz, convert64_signed_int_half x.val hb]
  by_cases hx : x.val = 0
  · simp only [hx, Int.lt_irrefl, decide_false]
  · exact roundRat_zeroSign_irrel x.val 1 false _ hx


/-- Every 128-bit integer conversion uses nearest-even rounding in every IEEE format. -/
def Integer128AllFormatsRounded : Prop :=
  (∀ (T : FTy) (x : JInt .u128), floatOfInt T x = (Fl.roundRat x.val 1 false : FV T)) ∧
  (∀ (T : FTy) (x : JInt .i128), floatOfInt T x = (Fl.roundRat x.val 1 (decide (x.val < 0)) : FV T))

theorem integer128AllFormatsRounded_proven : Integer128AllFormatsRounded := by
  constructor
  · intro T x
    cases T
    · exact float16_uint128_rounded x
    · exact float32_uint128_rounded x
    · exact float64_uint128_rounded x
  · intro T x
    cases T
    · exact float16_int128_rounded x
    · exact float32_int128_rounded x
    · exact float64_int128_rounded x

theorem magKey_grid_of_ge (f : Fmt) (E M : Nat) (h : 2 ^ f.sb * 2 ^ E ≤ magKey f M) :
    ∃ a : Nat, magKey f M = a * 2 ^ E := by
  have he : E + 1 ≤ M / 2 ^ f.sb := by
    apply Classical.byContradiction
    intro hn
    have hexp : M / 2 ^ f.sb ≤ E := by omega
    have hp : 2 ^ (M / 2 ^ f.sb) ≤ 2 ^ E := Nat.pow_le_pow_right (by decide) hexp
    have hu := magKey_lt f M
    have hupper : 2 ^ f.sb * 2 ^ (M / 2 ^ f.sb) ≤ 2 ^ f.sb * 2 ^ E := Nat.mul_le_mul_left _ hp
    omega
  refine ⟨(M % 2 ^ f.sb + if M / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) *
    2 ^ (M / 2 ^ f.sb - 1 - E), ?_⟩
  unfold magKey
  rw [Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  omega

theorem roundQuotient_floor_bounds (N G : Nat) :
    N / G ≤ Fl.roundQuotient N G ∧ Fl.roundQuotient N G ≤ N / G + 1 ∧
      (N % G = 0 → Fl.roundQuotient N G = N / G) := by
  unfold Fl.roundQuotient
  dsimp only
  constructor
  · split <;> omega
  constructor
  · split <;> omega
  intro hz
  by_cases hG : G = 0
  · subst G
    simp only [hz, Nat.zero_mul, Nat.lt_irrefl, decide_false, beq_self_eq_true, Bool.false_or, Bool.true_and]
    simp
  · have hgt : ¬ 2 * (N % G) > G := by omega
    have hne : 2 * (N % G) ≠ G := by omega
    simp only [hgt, beq_eq_false_iff_ne.mpr hne, Bool.false_and, Bool.or_false, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem rounding_projection_grid (N G P X : Nat) (hG : 0 < G) (hN : P * G ≤ N)
    (hgrid : P * G ≤ X → ∃ a : Nat, X = a * G) :
    (X < Fl.roundQuotient N G * G → X < N) ∧
    (Fl.roundQuotient N G * G < X → N < X) := by
  obtain ⟨hqlo, hqhi, hqexact⟩ := roundQuotient_floor_bounds N G
  constructor
  · intro hlt
    by_cases hX : P * G ≤ X
    · obtain ⟨a, rfl⟩ := hgrid hX
      have haq : a < Fl.roundQuotient N G := (Nat.mul_lt_mul_right hG).mp hlt
      have ha : a ≤ N / G := by omega
      have hle : a * G ≤ N := (Nat.le_div_iff_mul_le hG).mp ha
      have hne : a * G ≠ N := by
        intro he
        have hz : N % G = 0 := by rw [← he, Nat.mul_mod_left]
        have hd : N / G = a := by rw [← he, Nat.mul_div_cancel _ hG]
        have hq := hqexact hz
        omega
      omega
    · omega
  · intro hlt
    have hqbase : P ≤ Fl.roundQuotient N G := by
      have hp : P ≤ N / G := (Nat.le_div_iff_mul_le hG).mpr hN
      omega
    have hX : P * G ≤ X := Nat.le_trans (Nat.mul_le_mul_right G hqbase) (Nat.le_of_lt hlt)
    obtain ⟨a, rfl⟩ := hgrid hX
    have haq : Fl.roundQuotient N G < a := (Nat.mul_lt_mul_right hG).mp hlt
    have ha : N / G < a := by omega
    exact (Nat.div_lt_iff_lt_mul hG).mp ha

theorem packRounded_carry_pack {f : Fmt} (s : Bool) (k : Nat)
    (hk : k + f.bias + f.sb < f.emax) :
    (Fl.packRounded s (2 ^ (f.sb + 1)) (k : Int) : Fl f) = Fl.pack s (k + f.bias + f.sb + 1) 0 := by
  have hp : 0 < 2 ^ (f.sb + 1) := Nat.two_pow_pos _
  have hq0 : ((2 ^ (f.sb + 1) : Nat) == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hdiv : 2 ^ (f.sb + 1) / 2 = 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
  unfold Fl.packRounded
  simp only [hq0, Bool.false_eq_true, ↓reduceIte, Nat.le_refl, hdiv, Nat.lt_irrefl, Nat.sub_self, Nat.add_zero]
  by_cases ho : (k : Int) + 1 + f.bias + f.sb ≥ f.emax
  · simp only [ho, ↓reduceIte]
    have he : k + f.bias + f.sb + 1 = f.emax := by omega
    rw [he]
    rfl
  · simp only [ho, ↓reduceIte]
    unfold Fl.pack
    have he : ((k : Int) + 1 + f.bias + f.sb).toNat = k + f.bias + f.sb + 1 := by omega
    simp only [he, Nat.add_zero]

theorem packRounded_integer_key {f : Fmt} (hf : f.Good) (s : Bool) (q k : Nat)
    (hq : 2 ^ f.sb ≤ q ∧ q ≤ 2 ^ (f.sb + 1)) (hk : k + f.bias + f.sb < f.emax) :
    (Fl.packRounded s q (k : Int) : Fl f).key =
      if s then -((q * 2 ^ k * f.den : Nat) : Int) else ((q * 2 ^ k * f.den : Nat) : Int) := by
  have hP := Nat.two_pow_pos f.sb
  have hbase := hf.bias_pos
  have hmax := hf.emax_succ
  by_cases hc : q < 2 ^ (f.sb + 1)
  · have hB : k + f.bias + f.sb < 2 ^ f.eb := by omega
    have hr : q - 2 ^ f.sb < 2 ^ f.sb := by
      have he : 2 ^ (f.sb + 1) = 2 ^ f.sb * 2 := Nat.pow_succ _ _
      omega
    rw [Fl.packRounded_normal s q (k : Int) hq.1 hc (by omega)]
    have he : ((k : Int) + f.bias + f.sb).toNat = k + f.bias + f.sb := by omega
    rw [he, Fl.pack_key _ _ _ hB hr]
    have hz : k + f.bias + f.sb ≠ 0 := by omega
    simp only [hz, ↓reduceIte, Nat.sub_add_cancel hq.1]
    have hscale : q * 2 ^ (k + f.bias + f.sb - 1) = q * 2 ^ k * f.den := by
      unfold Fmt.den
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr 2
      omega
    rw [hscale]
  · have hqeq : q = 2 ^ (f.sb + 1) := by omega
    subst q
    rw [packRounded_carry_pack s k hk]
    have hB : k + f.bias + f.sb + 1 < 2 ^ f.eb := by omega
    rw [Fl.pack_key _ _ _ hB hP]
    have hz : k + f.bias + f.sb + 1 ≠ 0 := by omega
    simp only [hz, ↓reduceIte, Nat.zero_add]
    have hscale : 2 ^ f.sb * 2 ^ (k + f.bias + f.sb + 1 - 1) = 2 ^ (f.sb + 1) * 2 ^ k * f.den := by
      unfold Fmt.den
      simp only [← Nat.pow_add]
      congr 1
      omega
    rw [hscale]

theorem rounded_significand_bounds (f : Fmt) (n : Nat) (hn0 : n ≠ 0) : 2 ^ f.sb ≤ (if f.sb ≤ n.log2 then Fl.roundQuotient n (2 ^ (n.log2 - f.sb))
    else n * 2 ^ (f.sb - n.log2)) ∧
    (if f.sb ≤ n.log2 then Fl.roundQuotient n (2 ^ (n.log2 - f.sb))
    else n * 2 ^ (f.sb - n.log2)) ≤ 2 ^ (f.sb + 1) := by
  by_cases he : f.sb ≤ n.log2
  · simp only [he, ↓reduceIte]
    have hd := Nat.two_pow_pos (n.log2 - f.sb)
    have hp1 : 2 ^ n.log2 = 2 ^ f.sb * 2 ^ (n.log2 - f.sb) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hp2 : 2 ^ (n.log2 + 1) = 2 ^ (f.sb + 1) * 2 ^ (n.log2 - f.sb) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hlow : 2 ^ f.sb ≤ n / 2 ^ (n.log2 - f.sb) := by
      apply (Nat.le_div_iff_mul_le hd).mpr
      rw [← hp1]
      exact Nat.log2_self_le hn0
    have hhi : n / 2 ^ (n.log2 - f.sb) < 2 ^ (f.sb + 1) := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      rw [← hp2]
      exact Nat.lt_log2_self
    unfold Fl.roundQuotient
    dsimp only
    split <;> omega
  · simp only [he, ↓reduceIte]
    have hn53 : n < 2 ^ (f.sb + 1) := (Nat.log2_lt hn0).mp (by omega)
    have h := Fl.sig_bounds (f := f) n hn0 hn53
    change n.log2 ≤ f.sb ∧ 2 ^ f.sb ≤ n * 2 ^ (f.sb - n.log2) ∧
      n * 2 ^ (f.sb - n.log2) < 2 ^ (f.sb + 1) at h
    exact ⟨h.2.1, Nat.le_of_lt h.2.2⟩


theorem roundRat_wide_key (T : FTy) (hT : T = .f32 ∨ T = .f64) (n : Int)
    (hn : n ≠ 0) (hb : n.natAbs < 2 ^ 128) (hl : T.fmt.sb ≤ n.natAbs.log2) :
    (Fl.roundRat n 1 false : FV T).key =
      if n < 0 then -((Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - T.fmt.sb)) *
        2 ^ (n.natAbs.log2 - T.fmt.sb) * T.fmt.den : Nat) : Int)
      else ((Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - T.fmt.sb)) *
        2 ^ (n.natAbs.log2 - T.fmt.sb) * T.fmt.den : Nat) : Int) := by
  have hn0 : n.natAbs ≠ 0 := by omega
  have hh : n.natAbs.log2 ≤ 127 := by have := (Nat.log2_lt hn0).mpr hb; omega
  have hnorm : (Fl.roundRat n 1 false : FV T) = Fl.packRounded (decide (n < 0))
      (Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - T.fmt.sb))) ((n.natAbs.log2 - T.fmt.sb : Nat) : Int) := by
    rcases hT with rfl | rfl
    · rw [roundRat_int32_normal n hn hh]
      have hge : 23 ≤ n.natAbs.log2 := hl
      simp only [hge, ↓reduceIte]
      have hk : (n.natAbs.log2 : Int) - 23 = (n.natAbs.log2 - 23 : Nat) := by omega
      rw [hk]
      rfl
    · rw [roundRat_int64_normal n hn hh]
      have hge : 52 ≤ n.natAbs.log2 := hl
      simp only [hge, ↓reduceIte]
      have hk : (n.natAbs.log2 : Int) - 52 = (n.natAbs.log2 - 52 : Nat) := by omega
      rw [hk]
      rfl
  have hq := rounded_significand_bounds T.fmt n.natAbs hn0
  simp only [hl, ↓reduceIte] at hq
  have hk : n.natAbs.log2 - T.fmt.sb + T.fmt.bias + T.fmt.sb < T.fmt.emax := by
    rcases hT with rfl | rfl
    · change n.natAbs.log2 - 23 + 127 + 23 < 255
      change 23 ≤ n.natAbs.log2 at hl
      omega
    · change n.natAbs.log2 - 52 + 1023 + 52 < 2047
      change 52 ≤ n.natAbs.log2 at hl
      omega
  rw [hnorm, packRounded_integer_key (good_fty T) _ _ _ hq hk]
  simp only [decide_eq_true_eq]

theorem roundRat_wide_projection (T : FTy) (hT : T = .f32 ∨ T = .f64) (n : Int)
    (hb : n.natAbs < 2 ^ 128) (x : FV T) :
    (x.key < (Fl.roundRat n 1 false : FV T).key → x.key < n * (T.fmt.den : Int)) ∧
    ((Fl.roundRat n 1 false : FV T).key < x.key → n * (T.fmt.den : Int) < x.key) := by
  by_cases hs : n.natAbs < 2 ^ (T.fmt.sb + 1)
  · have hk := (Fl.ofInt_key (good_fty T) n hs).2
    change (Fl.roundRat n 1 false : FV T).key = _ at hk
    rw [hk]
    exact ⟨id, id⟩
  · have hn : n ≠ 0 := by intro hz; simp only [hz, Int.natAbs_zero] at hs; have := Nat.two_pow_pos (T.fmt.sb + 1); omega
    have hn0 : n.natAbs ≠ 0 := by omega
    have hnpos : 0 < n.natAbs := by omega
    have hnegval : n < 0 → n = -(n.natAbs : Int) := by intro h; omega
    have hposval : ¬ n < 0 → n = (n.natAbs : Int) := by intro h; omega
    have hl : T.fmt.sb ≤ n.natAbs.log2 := by
      have h := (Nat.le_log2 hn0).mpr (show 2 ^ (T.fmt.sb + 1) ≤ n.natAbs by omega)
      omega
    let k := n.natAbs.log2 - T.fmt.sb
    let G := 2 ^ k * T.fmt.den
    let N := n.natAbs * T.fmt.den
    let Q := Fl.roundQuotient n.natAbs (2 ^ k) * G
    have hd := T.fmt.den_pos
    have hG : 0 < G := Nat.mul_pos (Nat.two_pow_pos k) hd
    have hE : G = 2 ^ (k + T.fmt.bias + T.fmt.sb - 1) := by
      dsimp only [G]
      unfold Fmt.den
      rw [← Nat.pow_add]
      congr 1
      have := (good_fty T).bias_pos
      omega
    have hN : 2 ^ T.fmt.sb * G ≤ N := by
      have hpow : 2 ^ T.fmt.sb * 2 ^ k = 2 ^ n.natAbs.log2 := by
        rw [← Nat.pow_add]; congr 1; dsimp only [k]; omega
      dsimp only [G, N]
      rw [← Nat.mul_assoc, hpow]
      exact Nat.mul_le_mul_right _ (Nat.log2_self_le hn0)
    have hgrid : 2 ^ T.fmt.sb * G ≤ magKey T.fmt x.magnitude →
        ∃ a : Nat, magKey T.fmt x.magnitude = a * G := by
      intro hm
      rw [hE] at hm
      obtain ⟨a, ha⟩ := magKey_grid_of_ge T.fmt _ x.magnitude hm
      exact ⟨a, by rw [hE]; exact ha⟩
    have hprojection := rounding_projection_grid N G (2 ^ T.fmt.sb) (magKey T.fmt x.magnitude) hG hN hgrid
    have hq : Fl.roundQuotient N G * G = Q := by
      dsimp only [N, G, Q]
      rw [roundQuotient_scale _ _ _ hd]
    rw [hq] at hprojection
    have hqbound := rounded_significand_bounds T.fmt n.natAbs hn0
    simp only [hl, ↓reduceIte] at hqbound
    have hQ : 0 < Q := by
      have hqpos : 0 < Fl.roundQuotient n.natAbs (2 ^ k) := by
        have := Nat.two_pow_pos T.fmt.sb
        have hlo := hqbound.1
        change 2 ^ T.fmt.sb ≤ Fl.roundQuotient n.natAbs (2 ^ k) at hlo
        omega
      exact Nat.mul_pos hqpos hG
    have hNpos : 0 < N := Nat.mul_pos hnpos hd
    have hnD : n * (T.fmt.den : Int) = if n < 0 then -(N : Int) else (N : Int) := by
      by_cases hneg : n < 0
      · simp only [hneg, ↓reduceIte]
        have hv : n = -(n.natAbs : Int) := hnegval hneg
        calc n * (T.fmt.den : Int) = -(n.natAbs : Int) * (T.fmt.den : Int) := congrArg (fun a => a * (T.fmt.den : Int)) hv
          _ = -(N : Int) := by dsimp only [N]; rw [Int.neg_mul, Int.natCast_mul]
      · simp only [hneg, ↓reduceIte]
        have hv : n = (n.natAbs : Int) := hposval hneg
        calc n * (T.fmt.den : Int) = (n.natAbs : Int) * (T.fmt.den : Int) := congrArg (fun a => a * (T.fmt.den : Int)) hv
          _ = (N : Int) := by dsimp only [N]; rw [Int.natCast_mul]
    have hkey := roundRat_wide_key T hT n hn hb hl
    change (Fl.roundRat n 1 false : FV T).key =
      if n < 0 then -((Fl.roundQuotient n.natAbs (2 ^ k) * 2 ^ k * T.fmt.den : Nat) : Int)
      else ((Fl.roundQuotient n.natAbs (2 ^ k) * 2 ^ k * T.fmt.den : Nat) : Int) at hkey
    simp only [Nat.mul_assoc] at hkey
    change (Fl.roundRat n 1 false : FV T).key = if n < 0 then -(Q : Int) else (Q : Int) at hkey
    rw [hkey, hnD]
    unfold Fl.key
    cases hx : x.signbit <;> by_cases hneg : n < 0 <;> simp only [hx, hneg, Bool.false_eq_true, ↓reduceIte]
    all_goals constructor <;> intro h
    all_goals first
      | omega
      | (have hh := hprojection.1 (by omega); omega)
      | (have hh := hprojection.2 (by omega); omega)

theorem floatOfInt_roundRat (T : FTy) {t : IntTy} (x : JInt t) :
    floatOfInt T x = (Fl.roundRat x.val 1 false : FV T) := by
  by_cases ht : t.bits ≤ 64
  · exact floatOfInt_eq_ofInt ht T x
  · have h128 : t = .i128 ∨ t = .u128 := by cases t <;> simp_all [IntTy.bits]
    rcases h128 with rfl | rfl
    · have h := integer128AllFormatsRounded_proven.2 T x
      rw [h]
      by_cases hx : x.val = 0
      · simp only [hx, Int.lt_irrefl, decide_false]
      · exact roundRat_zeroSign_irrel x.val 1 _ false hx
    · exact integer128AllFormatsRounded_proven.1 T x

theorem packRounded_integer_notnan {f : Fmt} (hf : f.Good) (s : Bool) (q k : Nat)
    (hq : 2 ^ f.sb ≤ q ∧ q ≤ 2 ^ (f.sb + 1)) (hk : k + f.bias + f.sb < f.emax) :
    (Fl.packRounded s q (k : Int) : Fl f).isnan = false := by
  have hp := Nat.two_pow_pos f.sb
  have hm := hf.emax_succ
  by_cases hc : q < 2 ^ (f.sb + 1)
  · rw [Fl.packRounded_normal s q (k : Int) hq.1 hc (by omega)]
    have he : ((k : Int) + f.bias + f.sb).toNat = k + f.bias + f.sb := by omega
    rw [he]
    have hr : q - 2 ^ f.sb < 2 ^ f.sb := by
      have h2 : 2 ^ (f.sb + 1) = 2 ^ f.sb * 2 := Nat.pow_succ _ _
      omega
    have parts := Fl.pack_parts (f := f) s (k + f.bias + f.sb) (q - 2 ^ f.sb) (by omega) hr
    unfold Fl.isnan
    rw [parts.2.1]
    simp only [beq_eq_false_iff_ne.mpr (by omega : k + f.bias + f.sb ≠ f.emax), Bool.false_and]
  · have heq : q = 2 ^ (f.sb + 1) := by omega
    subst q
    rw [packRounded_carry_pack s k hk]
    have parts := Fl.pack_parts (f := f) s (k + f.bias + f.sb + 1) 0 (by omega) hp
    unfold Fl.isnan
    rw [parts.2.2.1]
    simp

theorem rounded_wide_integer (T : FTy) (hT : T = .f32 ∨ T = .f64) (n : Int) (hb : n.natAbs < 2 ^ 128) :
    (Fl.roundRat n 1 false : FV T).isnan = false ∧
      ∃ r : Int, (Fl.roundRat n 1 false : FV T).key = r * (T.fmt.den : Int) := by
  by_cases hs : n.natAbs < 2 ^ (T.fmt.sb + 1)
  · have h := Fl.ofInt_key (good_fty T) n hs
    exact ⟨Fl.isnan_of_finite h.1, n, h.2⟩
  · have hn : n ≠ 0 := by intro hz; simp only [hz, Int.natAbs_zero] at hs; have := Nat.two_pow_pos (T.fmt.sb + 1); omega
    have hn0 : n.natAbs ≠ 0 := by omega
    have hh : n.natAbs.log2 ≤ 127 := by have := (Nat.log2_lt hn0).mpr hb; omega
    have hl : T.fmt.sb ≤ n.natAbs.log2 := by
      have h := (Nat.le_log2 hn0).mpr (show 2 ^ (T.fmt.sb + 1) ≤ n.natAbs by omega)
      omega
    have hq := rounded_significand_bounds T.fmt n.natAbs hn0
    simp only [hl, ↓reduceIte] at hq
    have hk : n.natAbs.log2 - T.fmt.sb + T.fmt.bias + T.fmt.sb < T.fmt.emax := by
      rcases hT with rfl | rfl
      · change n.natAbs.log2 - 23 + 127 + 23 < 255
        change 23 ≤ n.natAbs.log2 at hl
        omega
      · change n.natAbs.log2 - 52 + 1023 + 52 < 2047
        change 52 ≤ n.natAbs.log2 at hl
        omega
    constructor
    · have hnorm : (Fl.roundRat n 1 false : FV T) = Fl.packRounded (decide (n < 0))
          (Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - T.fmt.sb))) ((n.natAbs.log2 - T.fmt.sb : Nat) : Int) := by
        rcases hT with rfl | rfl
        · rw [roundRat_int32_normal n hn hh]
          have hge : 23 ≤ n.natAbs.log2 := hl
          simp only [hge, ↓reduceIte]
          have he : (n.natAbs.log2 : Int) - 23 = (n.natAbs.log2 - 23 : Nat) := by omega
          rw [he]
          rfl
        · rw [roundRat_int64_normal n hn hh]
          have hge : 52 ≤ n.natAbs.log2 := hl
          simp only [hge, ↓reduceIte]
          have he : (n.natAbs.log2 : Int) - 52 = (n.natAbs.log2 - 52 : Nat) := by omega
          rw [he]
          rfl
      rw [hnorm]
      exact packRounded_integer_notnan (good_fty T) _ _ _ hq hk
    · refine ⟨if n < 0 then -((Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - T.fmt.sb)) *
          2 ^ (n.natAbs.log2 - T.fmt.sb) : Nat) : Int)
        else ((Fl.roundQuotient n.natAbs (2 ^ (n.natAbs.log2 - T.fmt.sb)) *
          2 ^ (n.natAbs.log2 - T.fmt.sb) : Nat) : Int), ?_⟩
      rw [roundRat_wide_key T hT n hn hb hl]
      by_cases hneg : n < 0 <;> simp only [hneg, ↓reduceIte, Int.natCast_mul, Int.neg_mul]

theorem wide_endpoint_keys (T : FTy) (hT : T = .f32 ∨ T = .f64) (t : IntTy)
    (ht : t = .i64 ∨ t = .u64 ∨ t = .i128 ∨ t = .u128) :
    (floatOfInt T (int.typemin t)).key = t.min * (T.fmt.den : Int) ∧
    (floatOfInt T (int.typemax t)).key = (t.max + 1) * (T.fmt.den : Int) ∧
    -(magKey T.fmt (infMag T) : Int) < t.min * (T.fmt.den : Int) ∧
    (t.max + 1) * (T.fmt.den : Int) ≤ (magKey T.fmt (infMag T) : Int) := by
  rw [floatOfInt_roundRat, floatOfInt_roundRat]
  rcases hT with rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;> decide

theorem bitInteger_abs_lt_128 {t : IntTy} (y : JInt t) : y.val.natAbs < 2 ^ 128 := by
  have h := y.property
  cases t <;> simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ↓reduceIte] at h <;> omega

theorem finite_of_key_interval (T : FTy) (x : FV T) (hnan : x.isnan = false)
    (hlo : -(magKey T.fmt (infMag T) : Int) < x.key)
    (hhi : x.key < (magKey T.fmt (infMag T) : Int)) : x.isfinite = true := by
  apply (isfinite_iff_mag x).mpr
  have hm : x.magnitude ≤ infMag T := by
    apply Classical.byContradiction
    intro h
    change ¬ x.magnitude ≤ T.fmt.emax * 2 ^ T.fmt.sb at h
    have hx : x.isnan = true := (isnan_iff_mag x).mpr (by change T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude; omega)
    rw [hnan] at hx
    contradiction
  apply Classical.byContradiction
  intro hfin
  change ¬ x.magnitude < infMag T at hfin
  have he : x.magnitude = infMag T := by omega
  unfold Fl.key at hlo hhi
  rw [he] at hlo hhi
  cases hx : x.signbit <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] at hlo hhi <;> omega

theorem integral_of_key (T : FTy) (x : FV T) (r : Int) (hf : x.isfinite = true)
    (hk : x.key = r * (T.fmt.den : Int)) :
    x.truncVal = r ∧ x.isinteger = true := by
  have hd : 0 < x.toRat.2 := (Fl.toRat_key (good_fty T) x hf).1
  have hr := (Fl.toRat_key (good_fty T) x hf).2
  have hn : x.toRat.1 = r * (x.toRat.2 : Int) := by
    apply Int.eq_of_mul_eq_mul_right (a := (T.fmt.den : Int)) (by have := T.fmt.den_pos; omega)
    rw [hr, hk]
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  constructor
  · unfold Fl.truncVal
    rw [hn, Int.mul_tdiv_cancel _ (by omega)]
  · simp only [Fl.isinteger, hf, hn, Int.mul_emod_left, beq_self_eq_true, Bool.true_and]

theorem rounded_wide_guard_valid (T : FTy) (hT : T = .f32 ∨ T = .f64) (t : IntTy)
    (ht : t = .i64 ∨ t = .u64 ∨ t = .i128 ∨ t = .u128) (y : JInt t)
    (hguard : eq_IEEEFloat (floatOfInt T y) (floatOfInt T (int.typemax t)) = false) :
    (floatOfInt T y).isfinite = true ∧
    (floatOfInt T y).isinteger = true ∧
    t.min ≤ (floatOfInt T y).truncVal ∧ (floatOfInt T y).truncVal ≤ t.max ∧
    (unsafe_trunc t (floatOfInt T y)).val = (floatOfInt T y).truncVal := by
  have hD : 0 < (T.fmt.den : Int) := by have := T.fmt.den_pos; omega
  have hfy := rounded_wide_integer T hT y.val (bitInteger_abs_lt_128 y)
  rw [← floatOfInt_roundRat T y] at hfy
  obtain ⟨hnan, r, hr⟩ := hfy
  have hmaxnan := (rounded_wide_integer T hT (int.typemax t).val (bitInteger_abs_lt_128 (int.typemax t))).1
  rw [← floatOfInt_roundRat T (int.typemax t)] at hmaxnan
  obtain ⟨hmin, hmax, hinflo, hinfhi⟩ := wide_endpoint_keys T hT t ht
  have hprojmin := roundRat_wide_projection T hT y.val (bitInteger_abs_lt_128 y) (floatOfInt T (int.typemin t))
  have hprojmax := roundRat_wide_projection T hT y.val (bitInteger_abs_lt_128 y) (floatOfInt T (int.typemax t))
  rw [← floatOfInt_roundRat T y] at hprojmin hprojmax
  have hymin : t.min * (T.fmt.den : Int) ≤ y.val * (T.fmt.den : Int) := (Int.mul_le_mul_right hD).mpr y.property.1
  have hymax : y.val * (T.fmt.den : Int) < (t.max + 1) * (T.fmt.den : Int) :=
    (Int.mul_lt_mul_right hD).mpr (by have := y.property; omega)
  have hlow : t.min * (T.fmt.den : Int) ≤ (floatOfInt T y).key := by
    apply Classical.byContradiction
    intro h
    have hp := hprojmin.2 (by rw [hmin]; omega)
    rw [hmin] at hp
    omega
  have hupp : (floatOfInt T y).key ≤ (t.max + 1) * (T.fmt.den : Int) := by
    apply Classical.byContradiction
    intro h
    have hp := hprojmax.1 (by rw [hmax]; omega)
    rw [hmax] at hp
    omega
  have hne : (floatOfInt T y).key ≠ (t.max + 1) * (T.fmt.den : Int) := by
    rw [eq_IEEEFloat_eq, Fl.eq_key hnan hmaxnan, hmax] at hguard
    exact of_decide_eq_false hguard
  have hupp' : (floatOfInt T y).key < (t.max + 1) * (T.fmt.den : Int) := by omega
  have hfin := finite_of_key_interval T (floatOfInt T y) hnan (by omega) (by omega)
  obtain ⟨htrunc, hint⟩ := integral_of_key T (floatOfInt T y) r hfin hr
  have hrmin : t.min ≤ r := (Int.mul_le_mul_right hD).mp (by rw [← hr]; exact hlow)
  have hrmax : r ≤ t.max := by
    have hlt : r < t.max + 1 := (Int.mul_lt_mul_right hD).mp (by rw [← hr]; exact hupp')
    omega
  refine ⟨hfin, hint, by omega, by omega, ?_⟩
  rw [unsafe_trunc_eq_wrap T t _ hfin ⟨by omega, by omega⟩, wrapInt_of_inRange t _ ⟨by omega, by omega⟩]

theorem mixed_comparison_assembly (a b c : Int)
    (hp : (a < b → a < c) ∧ (b < a → c < a)) :
    (decide (a = b) && decide (b = c)) = decide (a = c) ∧
    (decide (a < b) || (decide (a = b) && decide (b < c))) = decide (a < c) ∧
    (decide (a < b) || (decide (a = b) && decide (b ≤ c))) = decide (a ≤ c) ∧
    (decide (b < a) || (decide (b = a) && decide (c < b))) = decide (c < a) ∧
    (decide (b < a) || (decide (b = a) && decide (c ≤ b))) = decide (c ≤ a) := by
  rcases Int.lt_trichotomy a b with h | h | h
  · have hc := hp.1 h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    all_goals omega
  · subst b
    simp
  · have hc := hp.2 h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    all_goals omega

theorem mixed_comparison_overflow_assembly (a b c : Int)
    (hp : (a < b → a < c) ∧ (b < a → c < a)) (hbc : c < b) :
    false = decide (a = c) ∧
    decide (a < b) = decide (a < c) ∧
    decide (a < b) = decide (a ≤ c) ∧
    (decide (b < a) || decide (b = a)) = decide (c < a) ∧
    (decide (b < a) || decide (b = a)) = decide (c ≤ a) := by
  rcases Int.lt_trichotomy a b with h | h | h
  · have hc := hp.1 h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_iff, true_or, or_true, true_iff]
    all_goals omega
  · subst b
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_iff, true_or, or_true, true_iff]
    all_goals omega
  · have hc := hp.2 h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_iff, true_or, or_true, true_iff]
    all_goals omega

theorem wide_source_key_comparisons (T : FTy) (hT : T = .f32 ∨ T = .f64) (t : IntTy)
    (ht : t = .i64 ∨ t = .u64 ∨ t = .i128 ∨ t = .u128) (x : FV T) (y : JInt t) (hx : x.isnan = false) :
    eq_Tf_Ti_exact x y = decide (x.key = y.val * (T.fmt.den : Int)) ∧
    lt_Tf_Ti_exact x y = decide (x.key < y.val * (T.fmt.den : Int)) ∧
    le_Tf_Ti_exact x y = decide (x.key ≤ y.val * (T.fmt.den : Int)) ∧
    lt_Ti_Tf_exact y x = decide (y.val * (T.fmt.den : Int) < x.key) ∧
    le_Ti_Tf_exact y x = decide (y.val * (T.fmt.den : Int) ≤ x.key) := by
  have hD : 0 < (T.fmt.den : Int) := by have := T.fmt.den_pos; omega
  have hnan := (rounded_wide_integer T hT y.val (bitInteger_abs_lt_128 y)).1
  rw [← floatOfInt_roundRat T y] at hnan
  have hmaxnan := (rounded_wide_integer T hT (int.typemax t).val (bitInteger_abs_lt_128 (int.typemax t))).1
  rw [← floatOfInt_roundRat T (int.typemax t)] at hmaxnan
  have hproj := roundRat_wide_projection T hT y.val (bitInteger_abs_lt_128 y) x
  rw [← floatOfInt_roundRat T y] at hproj
  have hmax := (wide_endpoint_keys T hT t ht).2.1
  by_cases hguard : eq_IEEEFloat (floatOfInt T y) (floatOfInt T (int.typemax t)) = true
  · have heq : (floatOfInt T y).key = (floatOfInt T (int.typemax t)).key := by
      rw [eq_IEEEFloat_eq, Fl.eq_key hnan hmaxnan] at hguard
      exact of_decide_eq_true hguard
    have hmaxlt : lt_IEEEFloat (floatOfInt T y) (floatOfInt T (int.typemax t)) = false := by
      rw [lt_IEEEFloat_eq, Fl.lt_key hnan hmaxnan, heq]
      simp
    have hbc : y.val * (T.fmt.den : Int) < (floatOfInt T y).key := by
      rw [heq, hmax]
      exact (Int.mul_lt_mul_right hD).mpr (by have := y.property; omega)
    have h := mixed_comparison_overflow_assembly x.key (floatOfInt T y).key (y.val * (T.fmt.den : Int)) hproj hbc
    simpa only [eq_Tf_Ti_exact, lt_Tf_Ti_exact, le_Tf_Ti_exact, lt_Ti_Tf_exact, le_Ti_Tf_exact,
      hguard, hmaxlt, Bool.not_true, Bool.and_false, Bool.false_and, Bool.true_or, Bool.or_true,
      Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or,
      eq_IEEEFloat_eq, lt_IEEEFloat_eq, Fl.eq_key hx hnan, Fl.eq_key hnan hx,
      Fl.lt_key hx hnan, Fl.lt_key hnan hx] using h
  · have hg : eq_IEEEFloat (floatOfInt T y) (floatOfInt T (int.typemax t)) = false := Bool.eq_false_iff.mpr hguard
    obtain ⟨hfin, hint, hrlo, hrhi, hunsafe⟩ := rounded_wide_guard_valid T hT t ht y hg
    obtain ⟨_, r, hrkey⟩ := rounded_wide_integer T hT y.val (bitInteger_abs_lt_128 y)
    rw [← floatOfInt_roundRat T y] at hrkey
    have htr := (integral_of_key T (floatOfInt T y) r hfin hrkey).1
    have hR : (floatOfInt T y).key = (unsafe_trunc t (floatOfInt T y)).val * (T.fmt.den : Int) := by
      rw [hunsafe, htr]
      exact hrkey
    have hmaxlt : lt_IEEEFloat (floatOfInt T y) (floatOfInt T (int.typemax t)) = true := by
      rw [lt_IEEEFloat_eq, Fl.lt_key hnan hmaxnan, hmax, hR]
      apply decide_eq_true
      apply (Int.mul_lt_mul_right hD).mpr
      omega
    have heq : y.val = (unsafe_trunc t (floatOfInt T y)).val ↔
        (floatOfInt T y).key = y.val * (T.fmt.den : Int) := by
      rw [hR, Int.mul_eq_mul_right_iff (by omega : (T.fmt.den : Int) ≠ 0)]
      exact eq_comm
    have hult : (unsafe_trunc t (floatOfInt T y)).val < y.val ↔
        (floatOfInt T y).key < y.val * (T.fmt.den : Int) := by
      rw [hR, Int.mul_lt_mul_right hD]
    have hule : (unsafe_trunc t (floatOfInt T y)).val ≤ y.val ↔
        (floatOfInt T y).key ≤ y.val * (T.fmt.den : Int) := by
      rw [hR, Int.mul_le_mul_right hD]
    have hltu : y.val < (unsafe_trunc t (floatOfInt T y)).val ↔
        y.val * (T.fmt.den : Int) < (floatOfInt T y).key := by
      rw [hR, Int.mul_lt_mul_right hD]
    have hleu : y.val ≤ (unsafe_trunc t (floatOfInt T y)).val ↔
        y.val * (T.fmt.den : Int) ≤ (floatOfInt T y).key := by
      rw [hR, Int.mul_le_mul_right hD]
    have h := mixed_comparison_assembly x.key (floatOfInt T y).key (y.val * (T.fmt.den : Int)) hproj
    simpa only [eq_Tf_Ti_exact, lt_Tf_Ti_exact, le_Tf_Ti_exact, lt_Ti_Tf_exact, le_Ti_Tf_exact,
      hg, hmaxlt, Bool.not_false, Bool.and_false, Bool.false_and, Bool.true_or, Bool.or_true,
      Bool.and_true, Bool.true_and, Bool.or_false, Bool.false_or,
      eq_IEEEFloat_eq, lt_IEEEFloat_eq, Fl.eq_key hx hnan, Fl.eq_key hnan hx,
      Fl.lt_key hx hnan, Fl.lt_key hnan hx, JuliaLean.Proofs.base.int.eq_eq,
      JuliaLean.Proofs.base.int.lt_eq, JuliaLean.Proofs.base.int.le_eq, heq, hult, hule, hltu, hleu] using h

def WideMixedComparisons : Prop :=
  ∀ (T : FTy), T = .f32 ∨ T = .f64 → ∀ (t : IntTy),
  t = .i64 ∨ t = .u64 ∨ t = .i128 ∨ t = .u128 → ∀ (x : FV T) (y : JInt t),
  eq_Tf_Ti_exact x y = (exactOrder x y.val == some 0) ∧
  eq_Ti_Tf_exact y x = (exactOrder x y.val == some 0) ∧
  lt_Tf_Ti_exact x y = (exactOrder x y.val == some (-1)) ∧
  le_Tf_Ti_exact x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
  lt_Ti_Tf_exact y x = (exactOrder x y.val == some 1) ∧
  le_Ti_Tf_exact y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)

theorem wideMixedComparisons_proven : WideMixedComparisons := by
  intro T hT t ht x y
  by_cases hx : x.isnan = true
  · simp [eq_Tf_Ti_exact, eq_Ti_Tf_exact, lt_Tf_Ti_exact, le_Tf_Ti_exact, lt_Ti_Tf_exact, le_Ti_Tf_exact,
      eq_IEEEFloat_eq, lt_IEEEFloat_eq, Fl.eq, Fl.lt, hx, exactOrder]
  · have hn : x.isnan = false := Bool.eq_false_iff.mpr hx
    obtain ⟨heq, hlt, hle, hgt, hge⟩ := wide_source_key_comparisons T hT t ht x y hn
    have hbound : y.val.natAbs < 2 ^ (T.fmt.bias + 1) := by
      have hb := bitInteger_abs_lt_128 y
      rcases hT with rfl | rfl
      · exact hb
      · exact Nat.lt_of_lt_of_le hb (by decide)
    have heo := Fl.exactOrder_key (good_fty T) x hn y.val hbound
    simp only [eq_Ti_Tf_exact, heq, hlt, hle, hgt, hge, heo]
    rcases Int.lt_trichotomy x.key (y.val * (T.fmt.den : Int)) with hl | he | hg
    · simp [cmpInt, hl, show x.key ≠ y.val * (T.fmt.den : Int) by omega,
        show x.key ≤ y.val * (T.fmt.den : Int) by omega,
        show ¬ y.val * (T.fmt.den : Int) < x.key by omega,
        show ¬ y.val * (T.fmt.den : Int) ≤ x.key by omega]
    · simp [cmpInt, he]
    · simp [cmpInt, show ¬ x.key < y.val * (T.fmt.den : Int) by omega,
        show x.key ≠ y.val * (T.fmt.den : Int) by omega,
        show ¬ x.key ≤ y.val * (T.fmt.den : Int) by omega,
        hg, show y.val * (T.fmt.den : Int) ≤ x.key by omega]


theorem roundRat64_int_finite (n : Int) (hb : n.natAbs < 2 ^ 128) :
    (Fl.roundRat n 1 false : FV .f64).isfinite = true := by
  by_cases hs : n.natAbs < 2 ^ 16
  · exact (roundRat_exact_int64 n (by omega)).1
  · have hn : n ≠ 0 := by intro hz; simp only [hz, Int.natAbs_zero] at hs; omega
    rw [roundRat_sign64 n hn hb]
    obtain ⟨e, m, hlo, hhi, hm, he⟩ := nat64_large_pack n.natAbs (by omega) hb
    rw [he]
    have hsign : (Fl.ofBits ((if n < 0 then 2 ^ 63 else 0) ||| (Fl.pack false e m : FV .f64).toBits) : FV .f64) =
        Fl.pack (decide (n < 0)) e m := by
      simpa only [decide_eq_true_eq] using pack64_add_sign (decide (n < 0)) e m hhi hm
    rw [hsign]
    have hp := Fl.pack_parts (f := FTy.f64.fmt) (decide (n < 0)) e m (by change e < 2048; omega) hm
    simp only [Fl.isfinite, hp.2.1]
    change (e != 2047) = true
    simp; omega

theorem finite_key_interval {T : FTy} (x : FV T) (hf : x.isfinite = true) :
    -(magKey T.fmt (infMag T) : Int) < x.key ∧ x.key < (magKey T.fmt (infMag T) : Int) := by
  have hmag := (isfinite_iff_mag x).mp hf
  change x.magnitude < infMag T at hmag
  have hk := magKey_strictMono T.fmt hmag
  unfold Fl.key
  cases hx : x.signbit <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem exactOrder_none_iff {f : Fmt} (x : Fl f) (n : Int) : exactOrder x n = none ↔ x.isnan = true := by
  cases hx : x.isnan
  · simp only [exactOrder, hx, Bool.false_eq_true, ↓reduceIte, iff_false]
    split <;> simp
  · simp [exactOrder, hx]

theorem finite_half_key_bounds (x : FV .f16) (hf : x.isfinite = true) :
    (-65536 : Int) * (FTy.f16.fmt.den : Int) < x.key ∧ x.key < (65536 : Int) * (FTy.f16.fmt.den : Int) := by
  have hmag := (isfinite_iff_mag x).mp hf
  change x.magnitude < 31 * 2 ^ 10 at hmag
  have hexp : x.magnitude / 2 ^ 10 ≤ 30 := by omega
  have hpow : 2 ^ (x.magnitude / 2 ^ 10) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hexp
  have hm := magKey_lt FTy.f16.fmt x.magnitude
  change magKey FTy.f16.fmt x.magnitude < 2 ^ 10 * 2 ^ (x.magnitude / 2 ^ 10) at hm
  have hu : magKey FTy.f16.fmt x.magnitude < 2 ^ 40 := by
    have hmul := Nat.mul_le_mul_left (2 ^ 10) hpow
    omega
  have hden : FTy.f16.fmt.den = 2 ^ 24 := rfl
  rw [hden]
  unfold Fl.key
  cases hx : x.signbit <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem finite_half_exactOrder_bounds (x : FV .f16) (hf : x.isfinite = true) :
    exactOrder x 65536 = some (-1) ∧ exactOrder x (-65536) = some 1 := by
  obtain ⟨hlo, hhi⟩ := finite_half_key_bounds x hf
  rw [Fl.exactOrder_finite (good_fty .f16) x hf, Fl.exactOrder_finite (good_fty .f16) x hf]
  constructor
  · simp only [cmpInt, hhi, ↓reduceIte]
  · simp only [cmpInt, show ¬ x.key < (-65536 : Int) * (FTy.f16.fmt.den : Int) by omega,
      show x.key ≠ (-65536 : Int) * (FTy.f16.fmt.den : Int) by omega, ↓reduceIte]

theorem converted_half_finite_key_bounds (x : FV .f16) (hf : x.isfinite = true) :
    let c : FV .f64 := Fl.convert x
    c.isnan = false ∧ (-65536 : Int) * (FTy.f64.fmt.den : Int) < c.key ∧
      c.key < (65536 : Int) * (FTy.f64.fmt.den : Int) := by
  dsimp only
  have hc : ∀ n : Int, exactOrder (Fl.convert x : FV .f64) n = exactOrder x n :=
    Fl.convert_exactOrder (good_fty .f16) (good_fty .f64) (by decide) (by decide) (by decide) x
  obtain ⟨hhi, hlo⟩ := finite_half_exactOrder_bounds x hf
  have hhi' := (hc 65536).trans hhi
  have hlo' := (hc (-65536)).trans hlo
  have hnan : (Fl.convert x : FV .f64).isnan = false := by
    apply Bool.eq_false_iff.mpr
    intro hn
    have he := (exactOrder_none_iff (Fl.convert x : FV .f64) 65536).mpr hn
    rw [hhi'] at he
    contradiction
  refine ⟨hnan, ?_, ?_⟩
  · rw [Fl.exactOrder_key (good_fty .f64) _ hnan (-65536) (by decide)] at hlo'
    have hh : cmpInt (Fl.convert x : FV .f64).key ((-65536 : Int) * (FTy.f64.fmt.den : Int)) = 1 := Option.some.inj hlo'
    unfold cmpInt at hh
    split at hh
    · contradiction
    · split at hh
      · contradiction
      · omega
  · rw [Fl.exactOrder_key (good_fty .f64) _ hnan 65536 (by decide)] at hhi'
    have hh : cmpInt (Fl.convert x : FV .f64).key ((65536 : Int) * (FTy.f64.fmt.den : Int)) = -1 := Option.some.inj hhi'
    unfold cmpInt at hh
    split at hh
    · assumption
    · split at hh <;> contradiction

theorem nonfinite_notnan_eq_inf {T : FTy} (x : FV T) (hf : x.isfinite = false) (hn : x.isnan = false) :
    x = Fl.inf x.signbit := by
  have hupper : x.magnitude ≤ infMag T := by
    apply Classical.byContradiction
    intro h
    change ¬ x.magnitude ≤ T.fmt.emax * 2 ^ T.fmt.sb at h
    have hx : x.isnan = true := (isnan_iff_mag x).mpr (by omega)
    rw [hn] at hx
    contradiction
  have hlower : infMag T ≤ x.magnitude := by
    apply Classical.byContradiction
    intro h
    have hx : x.isfinite = true := (isfinite_iff_mag x).mpr (by change x.magnitude < infMag T; omega)
    rw [hf] at hx
    contradiction
  have hm : x.magnitude = infMag T := by omega
  calc x = Fl.ofBits x.toBits := (Fl.ofBits_toBits x).symm
    _ = Fl.inf x.signbit := by rw [(Fl.bits_split x).1, hm]; rfl

theorem converted_half_ne_large_integer (x : FV .f16) (n : Int) (hb : n.natAbs < 2 ^ 128)
    (hl : 2 ^ 53 ≤ n.natAbs) (hnan : x.isnan = false) :
    (Fl.convert x : FV .f64).key ≠ (Fl.roundRat n 1 false : FV .f64).key := by
  have hD : 0 < (FTy.f64.fmt.den : Int) := by have := FTy.f64.fmt.den_pos; omega
  have hpos : 0 ≤ n → 65536 ≤ n := by intro h; omega
  have hneg : n < 0 → n ≤ -65536 := by intro h; omega
  by_cases hf : x.isfinite = true
  · obtain ⟨_, hxlo, hxhi⟩ := converted_half_finite_key_bounds x hf
    by_cases hs : 0 ≤ n
    · have hn : (65536 : Int) * (FTy.f64.fmt.den : Int) ≤ n * (FTy.f64.fmt.den : Int) :=
        (Int.mul_le_mul_right hD).mpr (hpos hs)
      have hk : (Fl.roundRat 65536 1 false : FV .f64).key = (65536 : Int) * (FTy.f64.fmt.den : Int) :=
        (Fl.ofInt_key (good_fty .f64) 65536 (by decide)).2
      have hp := (roundRat_wide_projection .f64 (Or.inr rfl) n hb (Fl.roundRat 65536 1 false)).2
      have hy : (65536 : Int) * (FTy.f64.fmt.den : Int) ≤ (Fl.roundRat n 1 false : FV .f64).key := by
        apply Classical.byContradiction
        intro h
        have h' := hp (by rw [hk]; omega)
        rw [hk] at h'
        omega
      omega
    · have hn : n * (FTy.f64.fmt.den : Int) ≤ (-65536 : Int) * (FTy.f64.fmt.den : Int) :=
        (Int.mul_le_mul_right hD).mpr (hneg (by omega))
      have hk : (Fl.roundRat (-65536) 1 false : FV .f64).key = (-65536 : Int) * (FTy.f64.fmt.den : Int) :=
        (Fl.ofInt_key (good_fty .f64) (-65536) (by decide)).2
      have hp := (roundRat_wide_projection .f64 (Or.inr rfl) n hb (Fl.roundRat (-65536) 1 false)).1
      have hy : (Fl.roundRat n 1 false : FV .f64).key ≤ (-65536 : Int) * (FTy.f64.fmt.den : Int) := by
        apply Classical.byContradiction
        intro h
        have h' := hp (by rw [hk]; omega)
        rw [hk] at h'
        omega
      omega
  · have hfalse : x.isfinite = false := Bool.eq_false_iff.mpr hf
    have hInf := nonfinite_notnan_eq_inf x hfalse hnan
    have hi : x.isinf = true := by
      calc x.isinf = (Fl.inf x.signbit : FV .f16).isinf := congrArg Fl.isinf hInf
        _ = true := by cases x.signbit <;> decide
    have hc : (Fl.convert x : FV .f64) = Fl.inf x.signbit := by
      unfold Fl.convert
      simp only [show (FTy.f64.fmt == FTy.f16.fmt) = false from by decide,
        hnan, hi, Bool.false_eq_true, ↓reduceIte]
    have hy := finite_key_interval (Fl.roundRat n 1 false : FV .f64) (roundRat64_int_finite n hb)
    have hs : (Fl.inf x.signbit : FV .f64).signbit = x.signbit := by cases x.signbit <;> decide
    have hm : (Fl.inf x.signbit : FV .f64).magnitude = infMag .f64 := by cases x.signbit <;> decide
    have hk : (Fl.inf x.signbit : FV .f64).key =
        if x.signbit then -(magKey FTy.f64.fmt (infMag .f64) : Int) else (magKey FTy.f64.fmt (infMag .f64) : Int) := by
      unfold Fl.key
      rw [hs, hm]
    rw [hc, hk]
    cases hx : x.signbit <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem le_IEEEFloat_eq_lt_of_ne {T : FTy} (a b : FV T) (heq : eq_IEEEFloat a b = false) :
    le_IEEEFloat a b = lt_IEEEFloat a b := by
  rw [eq_IEEEFloat_eq] at heq
  rw [le_IEEEFloat_eq, lt_IEEEFloat_eq]
  unfold Fl.le
  rw [heq, Bool.or_false]

def HalfWideComparisons : Prop := ∀ (t : IntTy),
    t = .i64 ∨ t = .u64 ∨ t = .i128 ∨ t = .u128 → ∀ (x : FV .f16) (y : JInt t),
    op_Float16_WideInt eq_IEEEFloat x y = (exactOrder x y.val == some 0) ∧
    op_WideInt_Float16 eq_IEEEFloat y x = (exactOrder x y.val == some 0) ∧
    op_Float16_WideInt lt_IEEEFloat x y = (exactOrder x y.val == some (-1)) ∧
    op_Float16_WideInt le_IEEEFloat x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
    op_WideInt_Float16 lt_IEEEFloat y x = (exactOrder x y.val == some 1) ∧
    op_WideInt_Float16 le_IEEEFloat y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)

theorem halfWideComparisons_proven : HalfWideComparisons := by
  intro t ht x y
  have hcv : Float64_Float16 x = (Fl.convert x : FV .f64) := @convertFloat_eq .f64 .f16 x
  have hconv : ∀ n : Int, exactOrder (Fl.convert x : FV .f64) n = exactOrder x n :=
    Fl.convert_exactOrder (good_fty .f16) (good_fty .f64) (by decide) (by decide) (by decide) x
  by_cases hs : y.val.natAbs < 2 ^ 53
  · have h := Fl.cmp_via (good_fty .f16) (good_fty .f64) (by decide) (by decide) (by decide) x y.val hs
      (Nat.lt_of_lt_of_le hs (by decide))
    have hsym : Fl.eq (Fl.convert x : FV .f64) (Fl.ofInt y.val) = Fl.eq (Fl.ofInt y.val) (Fl.convert x : FV .f64) :=
      (floatIeeeEqLtLe_proven .f64 (Fl.convert x) (Fl.ofInt y.val) (Fl.convert x)).2.2.2.2.2.2.2.2.1
    simpa only [op_Float16_WideInt, op_WideInt_Float16, hcv, floatOfInt_roundRat,
      eq_IEEEFloat_eq, lt_IEEEFloat_eq, le_IEEEFloat_eq, Fl.ofInt] using
      (show Fl.eq (Fl.convert x : FV .f64) (Fl.ofInt y.val) = (exactOrder x y.val == some 0) ∧
        Fl.eq (Fl.ofInt y.val) (Fl.convert x : FV .f64) = (exactOrder x y.val == some 0) ∧
        Fl.lt (Fl.convert x : FV .f64) (Fl.ofInt y.val) = (exactOrder x y.val == some (-1)) ∧
        Fl.le (Fl.convert x : FV .f64) (Fl.ofInt y.val) = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
        Fl.lt (Fl.ofInt y.val) (Fl.convert x : FV .f64) = (exactOrder x y.val == some 1) ∧
        Fl.le (Fl.ofInt y.val) (Fl.convert x : FV .f64) = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0) from
        ⟨h.1, hsym.symm.trans h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩)
  · by_cases hx : x.isnan = true
    · have hc : (Fl.convert x : FV .f64).isnan = true := by
        apply (exactOrder_none_iff _ 0).mp
        rw [hconv]
        exact (exactOrder_none_iff x 0).mpr hx
      simp [op_Float16_WideInt, op_WideInt_Float16, hcv, eq_IEEEFloat_eq, lt_IEEEFloat_eq,
        le_IEEEFloat_eq, Fl.le, Fl.eq, Fl.lt, hx, hc, exactOrder]
    · have hxn : x.isnan = false := Bool.eq_false_iff.mpr hx
      have hc : (Fl.convert x : FV .f64).isnan = false := by
        apply Bool.eq_false_iff.mpr
        intro hn
        have he := (exactOrder_none_iff (Fl.convert x : FV .f64) 0).mpr hn
        rw [hconv] at he
        have hx' := (exactOrder_none_iff x 0).mp he
        rw [hxn] at hx'
        contradiction
      have hyn := (rounded_wide_integer .f64 (Or.inr rfl) y.val (bitInteger_abs_lt_128 y)).1
      rw [← floatOfInt_roundRat .f64 y] at hyn
      have hneq := converted_half_ne_large_integer x y.val (bitInteger_abs_lt_128 y) (by omega) hxn
      rw [← floatOfInt_roundRat .f64 y] at hneq
      have heq : eq_IEEEFloat (Fl.convert x : FV .f64) (floatOfInt .f64 y) = false := by
        rw [eq_IEEEFloat_eq, Fl.eq_key hc hyn]
        exact decide_eq_false hneq
      have hrev : eq_IEEEFloat (floatOfInt .f64 y) (Fl.convert x : FV .f64) = false := by
        rw [eq_IEEEFloat_eq, Fl.eq_key hyn hc]
        exact decide_eq_false (Ne.symm hneq)
      have hle := le_IEEEFloat_eq_lt_of_ne _ _ heq
      have hler := le_IEEEFloat_eq_lt_of_ne _ _ hrev
      have h := wideMixedComparisons_proven .f64 (Or.inr rfl) t ht (Fl.convert x) y
      simp only [eq_Tf_Ti_exact, eq_Ti_Tf_exact, lt_Tf_Ti_exact, le_Tf_Ti_exact, lt_Ti_Tf_exact, le_Ti_Tf_exact,
        heq, hrev, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, hconv] at h
      simpa only [op_Float16_WideInt, op_WideInt_Float16, hcv, hle, hler, heq, hrev] using h

def MixedCompareAll : Prop := ∀ (T : FTy) (t : IntTy) (x : FV T) (y : JInt t),
  eq_FI x y = (exactOrder x y.val == some 0) ∧
  lt_FI x y = (exactOrder x y.val == some (-1)) ∧
  le_FI x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
  eq_IF y x = (exactOrder x y.val == some 0) ∧
  lt_IF y x = (exactOrder x y.val == some 1) ∧
  le_IF y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)

theorem mixedCompareAll_proven : MixedCompareAll := by
  intro T t x y
  by_cases hs : t.bits ≤ 32
  · exact mixedCompareSmall_proven T t x y hs
  · have ht : t = .i64 ∨ t = .u64 ∨ t = .i128 ∨ t = .u128 := by cases t <;> simp_all [IntTy.bits]
    cases T
    · obtain ⟨heq, heqr, hlt, hle, hgt, hge⟩ := halfWideComparisons_proven t ht x y
      rcases ht with rfl | rfl | rfl | rfl
      all_goals simpa only [eq_FI, lt_FI, le_FI, eq_IF, lt_IF, le_IF] using
        (show op_Float16_WideInt eq_IEEEFloat x y = (exactOrder x y.val == some 0) ∧
          op_Float16_WideInt lt_IEEEFloat x y = (exactOrder x y.val == some (-1)) ∧
          op_Float16_WideInt le_IEEEFloat x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
          op_WideInt_Float16 eq_IEEEFloat y x = (exactOrder x y.val == some 0) ∧
          op_WideInt_Float16 lt_IEEEFloat y x = (exactOrder x y.val == some 1) ∧
          op_WideInt_Float16 le_IEEEFloat y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)
          from ⟨heq, hlt, hle, heqr, hgt, hge⟩)
    · obtain ⟨heq, heqr, hlt, hle, hgt, hge⟩ := wideMixedComparisons_proven .f32 (Or.inl rfl) t ht x y
      rcases ht with rfl | rfl | rfl | rfl
      all_goals simpa only [eq_FI, lt_FI, le_FI, eq_IF, lt_IF, le_IF] using
        (show eq_Tf_Ti_exact x y = (exactOrder x y.val == some 0) ∧
          lt_Tf_Ti_exact x y = (exactOrder x y.val == some (-1)) ∧
          le_Tf_Ti_exact x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
          eq_Ti_Tf_exact y x = (exactOrder x y.val == some 0) ∧
          lt_Ti_Tf_exact y x = (exactOrder x y.val == some 1) ∧
          le_Ti_Tf_exact y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)
          from ⟨heq, hlt, hle, heqr, hgt, hge⟩)
    · obtain ⟨heq, heqr, hlt, hle, hgt, hge⟩ := wideMixedComparisons_proven .f64 (Or.inr rfl) t ht x y
      rcases ht with rfl | rfl | rfl | rfl
      all_goals simpa only [eq_FI, lt_FI, le_FI, eq_IF, lt_IF, le_IF] using
        (show eq_Tf_Ti_exact x y = (exactOrder x y.val == some 0) ∧
          lt_Tf_Ti_exact x y = (exactOrder x y.val == some (-1)) ∧
          le_Tf_Ti_exact x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
          eq_Ti_Tf_exact y x = (exactOrder x y.val == some 0) ∧
          lt_Ti_Tf_exact y x = (exactOrder x y.val == some 1) ∧
          le_Ti_Tf_exact y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)
          from ⟨heq, hlt, hle, heqr, hgt, hge⟩)


def IntegerConversionsRounded : Prop :=
  (∀ (T : FTy) (t : IntTy) (x : JInt t), floatOfInt T x = (Fl.roundRat x.val 1 false : FV T)) ∧
  (∀ (T : FTy) (t : IntTy) (x : JInt t), t.signed = true → t.bits ≤ 64 →
    float_BitSigned64 T x = (Fl.roundRat x.val 1 false : FV T)) ∧
  (∀ (T : FTy) (t : IntTy) (x : JInt t), t.signed = false → t.bits ≤ 64 →
    float_BitUnsigned64 T x = (Fl.roundRat x.val 1 false : FV T)) ∧
  (∀ (t : IntTy) (x : JInt t), AbstractFloat_BitInteger x = (Fl.roundRat x.val 1 false : FV .f64))

theorem integerConversionsRounded_proven : IntegerConversionsRounded := by
  refine ⟨fun T _ x => floatOfInt_roundRat T x, ?_, ?_, ?_⟩
  · intro T t x hs _
    simp only [float_BitSigned64, sitofp, jlSitofp, fromJInt_toInt x hs, Fl.ofInt]
  · intro T t x hs _
    simp only [float_BitUnsigned64, uitofp, jlUitofp, fromJInt_toNat_unsigned x hs, Fl.ofInt]
  · intro t x
    exact floatOfInt_roundRat .f64 x

def NarrowFloatConversions : Prop := ∀ (T S : FTy) (x : FV S), T.fmt.width < S.fmt.width →
  (x.isfinite = true → convertFloat T x = (Fl.roundRat x.toRat.1 x.toRat.2 x.signbit : FV T)) ∧
  (x.isinf = true → convertFloat T x = (Fl.inf x.signbit : FV T)) ∧
  (x.isnan = true → (convertFloat T x).isnan = true)

theorem narrowFloatConversions_proven : NarrowFloatConversions := by
  intro T S x hwidth
  have hne : (T.fmt == S.fmt) = false := by
    revert hwidth
    cases T <;> cases S <;> decide
  rw [convertFloat_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro hf
    simp only [Fl.convert, hne, Fl.isnan_of_finite hf, Fl.isinf_of_finite hf, Bool.false_eq_true, ↓reduceIte]
  · intro hi
    have hn : x.isnan = false := by
      unfold Fl.isinf at hi
      unfold Fl.isnan
      simp only [Bool.and_eq_true, beq_iff_eq] at hi
      simp only [hi.1, hi.2, beq_self_eq_true, bne_self_eq_false, Bool.and_false]
    simp only [Fl.convert, hne, hn, hi, Bool.false_eq_true, ↓reduceIte]
  · intro hn
    have hsb : T.fmt.sb < S.fmt.sb := by
      revert hwidth
      cases T <;> cases S <;> decide
    have hspos : 0 < T.fmt.sb := by cases T <;> decide
    let pay := x.frac / 2 ^ (S.fmt.sb - T.fmt.sb)
    have hpay : pay < 2 ^ T.fmt.sb := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      have he : 2 ^ T.fmt.sb * 2 ^ (S.fmt.sb - T.fmt.sb) = 2 ^ S.fmt.sb := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [he]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hhalf : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.sb :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    have hor : (pay ||| 2 ^ (T.fmt.sb - 1)) < 2 ^ T.fmt.sb := Nat.or_lt_two_pow hpay hhalf
    have hnonzero : (pay ||| 2 ^ (T.fmt.sb - 1)) ≠ 0 := by
      intro hz
      have hb := congrArg (fun n : Nat => n.testBit (T.fmt.sb - 1)) hz
      simp [Nat.testBit_or] at hb
    have hB : T.fmt.emax < 2 ^ T.fmt.eb := by have := (good_fty T).emax_succ; omega
    have hp := Fl.pack_parts (f := T.fmt) x.signbit T.fmt.emax (pay ||| 2 ^ (T.fmt.sb - 1)) hB hor
    unfold Fl.convert
    simp only [hne, hn, Bool.false_eq_true, ↓reduceIte, show ¬ T.fmt.sb ≥ S.fmt.sb by omega]
    rw [Nat.add_assoc]
    change (Fl.pack x.signbit T.fmt.emax (pay ||| 2 ^ (T.fmt.sb - 1)) : FV T).isnan = true
    simp only [Fl.isnan, hp.2.1, hp.2.2.1, beq_self_eq_true,
      bne_iff_ne, hnonzero, Bool.true_and]
    exact hnonzero

def GenericIntegerDecomposition : Prop := ∀ (I : Type) (value : I → Int) (n : I),
  let d := decompose_Integer n
  d.2.2.val ≠ 0 ∧ (value d.1) * (2 ^ d.2.1.val.toNat : Nat) = (value n) * d.2.2.val

theorem genericIntegerDecomposition_proven : GenericIntegerDecomposition := by
  intro I value n
  simp only [decompose_Integer]
  change (1 : Int) ≠ 0 ∧ value n * (2 ^ (0 : Int).toNat : Nat) = value n * 1
  simp

def GenericArrayFloatConversion : Prop :=
  ∀ (T F Ty A B I : Type) (zero : Unit → T) (AbstractFloat : T → F) (typeof : F → Ty)
    (convert : Ty → A → JuliaLean.base.range.JlX B) (getA : A → I → T) (getB : B → I → F),
  (∀ (tag : Ty) (a : A) (b : B), convert tag a = .ok b → ∀ i, getB b i = float_any AbstractFloat (getA a i)) →
  ∀ (a : A),
  float_AbstractArray (fun _ => false) zero (float_any AbstractFloat) typeof convert a =
    .error (.errorException "`float` not defined on abstractly-typed arrays; please convert to a more specific type") ∧
  (∀ b, float_AbstractArray (fun _ => true) zero (float_any AbstractFloat) typeof convert a = .ok b →
    ∀ i, getB b i = float_any AbstractFloat (getA a i))

theorem genericArrayFloatConversion_proven : GenericArrayFloatConversion := by
  intro T F Ty A B I zero AbstractFloat typeof convert getA getB hconvert a
  refine ⟨rfl, ?_⟩
  intro b hb i
  exact hconvert _ a b hb i

/-! Nothing to promise:
`uabs(::Integer)@235`: forwards to the selected `abs` method; the magnitude arithmetic is in `int.jl` or the Integer subtype's own implementation.
`Float16(::Integer)@241`: forwards the Integer-to-Float32 result to the Float16 constructor; its callees implement the conversions.
`float(x)@367`: forwards to the selected AbstractFloat constructor or array method.
`float(::Type{T<:Number})@384`: queries the type returned by converting the type's zero; the selected constructor supplies the numeric result.
`float(::Type{T<:AbstractFloat})@385`: type-identity dispatch with no calculation.
`round(::Type{Signed},IEEEFloat,RoundingMode)@454`: forwards every rounding mode to the selected machine-signed-integer method.
`round(::Type{Unsigned},IEEEFloat,RoundingMode)@455`: forwards every rounding mode to the selected machine-unsigned-integer method.
`round(::Type{Integer},IEEEFloat,RoundingMode)@456`: forwards every rounding mode to the selected machine-integer method.
`precision(Type{T<:AbstractFloat})@805`: forwards to `_precision` without changing its arguments.
`precision(AbstractFloat)@806`: type-query forwarding to the precision method for that AbstractFloat subtype.
`nextfloat(AbstractFloat,Integer)@853`: forwards the sign and unsigned magnitude of the Integer step to the selected `_nextfloat` implementation.
`nextfloat(AbstractFloat)@863`: forwards a machine-integer step of one to the subtype's selected stepping implementation.
`prevfloat(AbstractFloat,Integer)@871`: forwards the reverse direction and unsigned magnitude of the Integer step to the selected `_nextfloat` implementation.
`prevfloat(AbstractFloat)@879`: forwards a machine-integer step of negative one to the subtype's selected stepping implementation.
`typemin(Real)@969`: forwards to the lower-bound method selected for the value's type.
`typemax(Real)@970`: forwards to the upper-bound method selected for the value's type.
`floatmin(AbstractFloat)@1019`: forwards to the type's smallest-normal-value method.
`floatmax(AbstractFloat)@1045`: forwards to the type's greatest-finite-value method.
`floatmin()@1047`: default-type forwarding to Float64; the Float64 extremum is specified below.
`floatmax()@1048`: default-type forwarding to Float64; the Float64 extremum is specified below.
`float(AbstractArray{<:AbstractFloat})@1166`: identity dispatch for an already-floating array, with no conversion or array traversal.
-/

theorem magKey_mono (f : Fmt) {a b : Nat} (h : a ≤ b) : magKey f a ≤ magKey f b := by
  rcases Nat.lt_or_eq_of_le h with hl | he
  · exact Nat.le_of_lt (magKey_strictMono f hl)
  · rw [he]
    exact Nat.le_refl _

def FloatExtrema : Prop := ∀ (T : FTy),
  (floatmin_float T).isfinite = true ∧ (floatmin_float T).signbit = false ∧
  (floatmin_float T).expField = 1 ∧ (floatmin_float T).frac = 0 ∧
  lt_IEEEFloat (zero_float T) (floatmin_float T) = true ∧
  (∀ x : FV T, x.isfinite = true → x.signbit = false → x.expField ≠ 0 →
    lt_IEEEFloat x (floatmin_float T) = false) ∧
  (floatmax_float T).isfinite = true ∧ (floatmax_float T).signbit = false ∧
  (∀ x : FV T, x.isfinite = true → lt_IEEEFloat (floatmax_float T) x = false)

theorem floatExtrema_proven : FloatExtrema := by
  intro T
  have hmin : (floatmin_float T).isfinite = true ∧ (floatmin_float T).signbit = false ∧
      (floatmin_float T).expField = 1 ∧ (floatmin_float T).frac = 0 ∧
      lt_IEEEFloat (zero_float T) (floatmin_float T) = true ∧ (floatmin_float T).magnitude = 2 ^ T.fmt.sb := by
    cases T <;> decide
  have hmax : (floatmax_float T).isfinite = true ∧ (floatmax_float T).signbit = false ∧
      (floatmax_float T).magnitude = infMag T - 1 := by cases T <;> decide
  refine ⟨hmin.1, hmin.2.1, hmin.2.2.1, hmin.2.2.2.1, hmin.2.2.2.2.1, ?_, hmax.1, hmax.2.1, ?_⟩
  · intro x hf hsign he
    have hparts := (mag_decomp x).1
    have hmul : 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb := by
      have h := Nat.mul_le_mul_right (2 ^ T.fmt.sb) (show 1 ≤ x.expField by omega)
      simpa only [Nat.one_mul] using h
    have hxm : 2 ^ T.fmt.sb ≤ x.magnitude := by omega
    have hkey := magKey_mono T.fmt hxm
    have hminKey : (floatmin_float T).key = (magKey T.fmt (2 ^ T.fmt.sb) : Int) := by
      unfold Fl.key
      rw [hmin.2.1, hmin.2.2.2.2.2]
      rfl
    have hxKey : x.key = (magKey T.fmt x.magnitude : Int) := by unfold Fl.key; rw [hsign]; rfl
    rw [lt_IEEEFloat_eq, Fl.lt_key (Fl.isnan_of_finite hf) (Fl.isnan_of_finite hmin.1), hxKey, hminKey]
    exact decide_eq_false (by omega)
  · intro x hf
    have hxmag := (isfinite_iff_mag x).mp hf
    change x.magnitude < infMag T at hxmag
    have hkey := magKey_mono T.fmt (show x.magnitude ≤ infMag T - 1 by omega)
    have hmaxKey : (floatmax_float T).key = (magKey T.fmt (infMag T - 1) : Int) := by
      unfold Fl.key
      rw [hmax.2.1, hmax.2.2]
      rfl
    rw [lt_IEEEFloat_eq, Fl.lt_key (Fl.isnan_of_finite hmax.1) (Fl.isnan_of_finite hf), hmaxKey]
    unfold Fl.key
    cases hx : x.signbit <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] <;> apply decide_eq_false <;> omega

theorem le_IEEEFloat_key {T : FTy} (x y : FV T) (hx : x.isnan = false) (hy : y.isnan = false) :
    le_IEEEFloat x y = decide (x.key ≤ y.key) := by
  rw [le_IEEEFloat_eq]
  unfold Fl.le
  rw [Fl.lt_key hx hy, Fl.eq_key hx hy]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  omega

def MachineEpsilonGap : Prop := ∀ (T : FTy),
  (eps_float T).isfinite = true ∧ (eps_float T).signbit = false ∧
  (eps_float T).toRat.1 * ((2 ^ T.fmt.sb : Nat) : Int) = ((eps_float T).toRat.2 : Int) ∧
  add_IEEEFloat (one_float T) (eps_float T) = nextfloat (one_float T) ∧
  lt_IEEEFloat (one_float T) (add_IEEEFloat (one_float T) (eps_float T)) = true ∧
  (∀ y : FV T, lt_IEEEFloat (one_float T) y = true →
    le_IEEEFloat (add_IEEEFloat (one_float T) (eps_float T)) y = true) ∧
  eps_default.isfinite = true ∧ eps_default.signbit = false ∧
  eps_default.toRat.1 * ((2 ^ 52 : Nat) : Int) = (eps_default.toRat.2 : Int)

theorem machineEpsilonGap_proven : MachineEpsilonGap := by
  intro T
  have hc : (eps_float T).isfinite = true ∧ (eps_float T).signbit = false ∧
      (eps_float T).toRat.1 * ((2 ^ T.fmt.sb : Nat) : Int) = ((eps_float T).toRat.2 : Int) ∧
      add_IEEEFloat (one_float T) (eps_float T) = nextfloat (one_float T) := by cases T <;> decide
  have hnan : (one_float T).isnan = false := by cases T <;> decide
  have hinf : ¬ ((one_float T).signbit = false ∧ (one_float T).magnitude = infMag T) := by cases T <;> decide
  have hn : (nextfloat (one_float T)).isnan = false := by cases T <;> decide
  have hadj := nextfloat_order_adj (one_float T) hnan hinf
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, by rw [hc.2.2.2]; exact hadj.1, ?_, by decide⟩
  intro y hy
  have hynan : y.isnan = false := by
    apply Bool.eq_false_iff.mpr
    intro hx
    have hz : lt_IEEEFloat (one_float T) y = false := by simp [lt_IEEEFloat_eq, Fl.lt, hx]
    rw [hz] at hy
    contradiction
  have hlt : lt_IEEEFloat y (nextfloat (one_float T)) = false :=
    Bool.eq_false_iff.mpr (fun h => hadj.2 y ⟨hy, h⟩)
  rw [lt_IEEEFloat_eq, Fl.lt_key hynan hn] at hlt
  have hge : (nextfloat (one_float T)).key ≤ y.key := by have := of_decide_eq_false hlt; omega
  rw [hc.2.2.2, le_IEEEFloat_key _ _ hn hynan]
  exact decide_eq_true hge


def GenericFloatClassification : Prop :=
  ∀ (F V : Type) [BEq V] [LawfulBEq V] (value : F → V)
    (nan finite : F → Bool) (ne : F → F → Bool) (sub : F → F → F),
  (∀ a b, ne a b = (nan a || nan b || !(value a == value b))) →
  (∀ x, nan (sub x x) = !finite x) →
  ∀ x, isnan_AbstractFloat ne x = nan x ∧
    isfinite_AbstractFloat sub (isnan_AbstractFloat ne) x = finite x ∧
    (isinf_Real (isnan_AbstractFloat ne) (isfinite_AbstractFloat sub (isnan_AbstractFloat ne)) x = true ↔
      nan x = false ∧ finite x = false)

theorem genericFloatClassification_proven : GenericFloatClassification := by
  intro F V _ _ value nan finite ne sub hne hsub x
  have hnan (y : F) : isnan_AbstractFloat ne y = nan y := by
    simp only [isnan_AbstractFloat, hne, beq_self_eq_true, Bool.not_true, Bool.or_false, Bool.or_self]
  have hfin : isfinite_AbstractFloat sub (isnan_AbstractFloat ne) x = finite x := by
    simp only [isfinite_AbstractFloat, hnan, hsub, Bool.not_not]
  refine ⟨hnan x, hfin, ?_⟩
  simp only [isinf_Real, hnan, hfin, Bool.and_eq_true, Bool.not_eq_true]
  cases nan x <;> cases finite x <;> decide

def GenericRealClassification : Prop :=
  ∀ (R N E : Type) (decompose : R → N × E × JInt .i64) (finite : R → Bool),
  (∀ x, (decompose x).2.2.val ≠ 0 ↔ finite x = true) →
  ∀ x, isfinite_Real decompose x = finite x ∧
    (isinf_Real isnan_Number (isfinite_Real decompose) x = true ↔ finite x = false)

theorem genericRealClassification_proven : GenericRealClassification := by
  intro R N E decompose finite hden x
  have hfin : isfinite_Real decompose x = finite x := by
    by_cases hz : (decompose x).2.2.val = 0
    · have hfalse : finite x = false := Bool.eq_false_iff.mpr (fun h => (hden x).mpr h hz)
      simp [isfinite_Real, eq_int_same_eq, hz, hfalse]
      rfl
    · have htrue := (hden x).mp hz
      simp [isfinite_Real, eq_int_same_eq, hz, htrue]
      exact hz
  refine ⟨hfin, ?_⟩
  simp only [isinf_Real, isnan_Number, Bool.not_false, Bool.true_and, hfin, Bool.not_eq_true]
  cases finite x <;> decide

def GenericIntegerFinite : Prop := ∀ (I : Type) (n : I),
  isfinite_Integer n = true ∧ isnan_Number n = false ∧
  isfinite_Real decompose_Integer n = true ∧
  isinf_Real isnan_Number (isfinite_Real decompose_Integer) n = false

theorem genericIntegerFinite_proven : GenericIntegerFinite := by
  intro I n
  change true = true ∧ false = false ∧ (!(int.eq (int.lit .i64 1) (int.lit .i64 0))) = true ∧
    Bool.and true (!(!(int.eq (int.lit .i64 1) (int.lit .i64 0)))) = false
  decide

def GenericFloatParity : Prop :=
  ∀ (F I : Type) (integer : F → Bool) (abs maxintfloat : F → F)
    (gt le : F → F → Bool) (toInteger : F → I) (value : I → Int)
    (even odd : I → Bool),
  (∀ a b, gt a b = !le a b) →
  (∀ i, even i = decide (value i % 2 = 0)) →
  (∀ i, odd i = decide (value i % 2 ≠ 0)) →
  (∀ x, integer x = true → le (abs x) (maxintfloat x) = false → value (toInteger x) % 2 = 0) →
  ∀ x,
    iseven_generic integer abs maxintfloat gt toInteger even x =
      (integer x && decide (value (toInteger x) % 2 = 0)) ∧
    isodd_generic integer abs maxintfloat le toInteger odd x =
      (integer x && decide (value (toInteger x) % 2 ≠ 0))

theorem genericFloatParity_proven : GenericFloatParity := by
  intro F I integer abs maxintfloat gt le toInteger value even odd hgt heven hodd hlarge x
  unfold iseven_generic isodd_generic
  rw [hgt, heven, hodd]
  cases hi : integer x
  · simp
  · cases hl : le (abs x) (maxintfloat x)
    · have hz := hlarge x hi hl
      simp [hz]
    · simp

def RadixPrecisionInterval : Prop :=
  ∀ (A : Type) (t : IntTy) (binaryPrecision : A → JInt .i64)
    (floorLog : JInt .i64 → JInt t → Jl (JInt .i64)),
  (∀ p b, 0 ≤ p.val → 1 < b.val → b.val ≠ 2 →
    ∃ q, floorLog p b = .ok q ∧ 0 ≤ q.val ∧
      b.val.toNat ^ q.val.toNat ≤ 2 ^ p.val.toNat ∧
      2 ^ p.val.toNat < b.val.toNat ^ (q.val.toNat + 1)) →
  ∀ x b, 0 ≤ (binaryPrecision x).val →
    (b.val ≤ 1 → _precision binaryPrecision floorLog x b = .error (.domainError "`base` cannot be less than 2.")) ∧
    (1 < b.val → ∃ q, _precision binaryPrecision floorLog x b = .ok q ∧ 0 ≤ q.val ∧
      b.val.toNat ^ q.val.toNat ≤ 2 ^ (binaryPrecision x).val.toNat ∧
      2 ^ (binaryPrecision x).val.toNat < b.val.toNat ^ (q.val.toNat + 1))

theorem radixPrecisionInterval_proven : RadixPrecisionInterval := by
  intro A t binaryPrecision floorLog hfloor x b hp
  have hlt : int.lt (int.lit .i64 1) b = decide (1 < b.val) := by
    have h := JuliaLean.Proofs.base.int.lt_eq (int.lit .i64 1) b
    change int.lt (int.lit .i64 1) b = decide ((1 : Int) < b.val) at h
    exact h
  have heq : int.eq b (int.lit .i64 2) = decide (b.val = 2) := by
    have h := JuliaLean.Proofs.base.int.eq_eq b (int.lit .i64 2)
    change int.eq b (int.lit .i64 2) = decide (b.val = (2 : Int)) at h
    exact h
  constructor
  · intro hb
    simp only [_precision, hlt, show ¬1 < b.val by omega, decide_false, Bool.not_false, ↓reduceIte]
  · intro hb
    by_cases htwo : b.val = 2
    · refine ⟨binaryPrecision x, ?_, hp, ?_, ?_⟩
      · simp [_precision, hlt, heq, hb, htwo]
      · rw [htwo]; exact Nat.le_refl _
      · rw [htwo]; change 2 ^ (binaryPrecision x).val.toNat < 2 ^ ((binaryPrecision x).val.toNat + 1)
        rw [Nat.pow_succ]
        have := Nat.two_pow_pos (binaryPrecision x).val.toNat
        omega
    · obtain ⟨q, hq, hnonneg, hlo, hhi⟩ := hfloor (binaryPrecision x) b hp hb htwo
      refine ⟨q, ?_, hnonneg, hlo, hhi⟩
      simp only [_precision, hlt, heq, hb, htwo, decide_true, decide_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, hq]


theorem nextSpec_saturated {F : FTy} (x : FV F) (d : Bool) (n : Nat)
    (hn : 2 ^ F.fmt.width ≤ n) :
    nextSpec x d n = if x.isnan then x else encode F d (infMag F) := by
  by_cases hx : x.isnan = true
  · simp [nextSpec, hx]
  have hxn : x.isnan = false := Bool.eq_false_iff.mpr hx
  have hm := not_nan_mag hxn
  have hcap : 2 * infMag F < 2 ^ F.fmt.width := by cases F <;> decide
  simp only [nextSpec, hxn, Bool.false_eq_true, ↓reduceIte]
  unfold walk
  cases hs : x.signbit <;> cases d <;>
    simp only [Bool.false_eq_true, Bool.false_bne, Bool.true_bne, Bool.not_false, Bool.not_true,
      ↓reduceIte, Nat.min_eq_right (by omega : infMag F ≤ x.magnitude + n),
      Nat.min_eq_right (by omega : infMag F ≤ n - x.magnitude)] <;>
    split <;> simp_all <;> omega

theorem generic_nextfloat_closed {F : FTy} {I : Type}
    (value : I → Nat) (gt : I → Bool) (remU : I → JInt F.uintTy)
    (hgt : ∀ a, gt a = decide (2 ^ F.fmt.width ≤ value a))
    (hrem : ∀ a, (remU a).val = ((value a % 2 ^ F.fmt.width : Nat) : Int))
    (x : FV F) (d : Bool) (a : I) :
    _nextfloat_generic gt remU x d a = nextSpec x d (value a) := by
  let n := value a
  let c := min n (2 ^ F.fmt.width)
  let du : JInt .u128 := int.lit .u128 c
  have hc : c ≤ 2 ^ F.fmt.width := Nat.min_le_right _ _
  have hcw : (2 ^ F.fmt.width : Nat) < 2 ^ 128 := by cases F <;> decide
  have hd : du.val = (c : Int) := by
    change wrapInt .u128 (c : Int) = (c : Int)
    apply wrapInt_of_inRange
    constructor
    · exact Int.natCast_nonneg _
    · change (c : Int) ≤ (2 ^ 128 : Nat) - 1
      omega
  have hmax : (int.typemax F.uintTy).val = ((2 ^ F.fmt.width : Nat) : Int) - 1 := by cases F <;> decide
  have hlt : int.lt (int.typemax F.uintTy) du = decide (2 ^ F.fmt.width ≤ n) := by
    rw [JuliaLean.Proofs.base.int.lt_eq, hmax, hd]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    change (((2 ^ F.fmt.width : Nat) : Int) - 1 < ((min n (2 ^ F.fmt.width) : Nat) : Int)) ↔ 2 ^ F.fmt.width ≤ n
    omega
  have heq : _nextfloat_generic gt remU x d a = _nextfloat x d du := by
    unfold _nextfloat_generic _nextfloat
    rw [hgt, hlt]
    change (if isnan_IEEEFloat x then x else _) = (if isnan_IEEEFloat x then x else _)
    split
    · rfl
    · by_cases hlarge : 2 ^ F.fmt.width ≤ n
      · simp only [show value a = n from rfl, hlarge, decide_true, ↓reduceIte]
      · have hcsmall : c = n := Nat.min_eq_left (by omega)
        have hdu : int.remT F.uintTy du = remU a := by
          apply jint_eq
          rw [remT_val, hd, hrem, hcsmall]
          change wrapInt F.uintTy (n : Int) = ((n % 2 ^ F.fmt.width : Nat) : Int)
          have hu : F.uintTy.signed = false := by cases F <;> decide
          have hw : F.uintTy.bits = F.fmt.width := by cases F <;> decide
          simp only [wrapInt, hu, Bool.false_eq_true, ↓reduceIte, hw, Int.natCast_emod,
            Int.natCast_pow]
          rfl
        simp only [show value a = n from rfl, hlarge, decide_false, Bool.false_eq_true, ↓reduceIte, hdu]
  rw [heq, nextfloat_core_eq x d du (by rw [hd]; exact Int.natCast_nonneg _), hd, Int.toNat_natCast]
  by_cases hsmall : n ≤ 2 ^ F.fmt.width
  · rw [show c = n from Nat.min_eq_left hsmall]
  · have hlarge : 2 ^ F.fmt.width ≤ n := by omega
    have hcfull : c = 2 ^ F.fmt.width := Nat.min_eq_right hlarge
    rw [hcfull, nextSpec_saturated x d _ (Nat.le_refl _), nextSpec_saturated x d _ hlarge]

def ArbitraryIntegerStepping : Prop :=
  ∀ (F : FTy) (I : Type) (value : I → Nat) (gt : I → Bool) (remU : I → JInt F.uintTy),
  (∀ a, gt a = decide (2 ^ F.fmt.width ≤ value a)) →
  (∀ a, (remU a).val = ((value a % 2 ^ F.fmt.width : Nat) : Int)) →
  ∀ (x : FV F) (a : I),
    _nextfloat_generic gt remU x false a = iter nextfloat (value a) x ∧
    _nextfloat_generic gt remU x true a = iter prevfloat (value a) x

theorem arbitraryIntegerStepping_proven : ArbitraryIntegerStepping := by
  intro F I value gt remU hgt hrem x a
  rw [generic_nextfloat_closed value gt remU hgt hrem x false a,
    generic_nextfloat_closed value gt remU hgt hrem x true a, spec_iter false, spec_iter true]
  have hn : (nextfloat : FV F → FV F) = (fun y => nextSpec y false 1) := funext nextfloat_eq
  have hp : (prevfloat : FV F → FV F) = (fun y => nextSpec y true 1) := funext prevfloat_eq
  rw [hn, hp]
  exact ⟨rfl, rfl⟩

theorem numerator_power_two (n : Int) :
    2 * n = ((2 ^ (n.natAbs.log2 + 1) : Nat) : Int) ↔ ∃ k : Nat, n = ((2 ^ k : Nat) : Int) := by
  constructor
  · intro h
    refine ⟨n.natAbs.log2, ?_⟩
    rw [Nat.pow_succ, Int.natCast_mul] at h
    omega
  · rintro ⟨k, rfl⟩
    have hl : (2 ^ k : Nat).log2 = k := by
      simpa only [Nat.one_mul, show (1 : Nat).log2 = 0 from rfl, Nat.zero_add] using Fl.log2_mul_pow 1 k (by decide)
    simp only [Int.natAbs_natCast, hl, Nat.pow_succ, Int.natCast_mul]
    omega

def GenericBinaryPowerOfTwo : Prop :=
  ∀ (F E : Type) (numerator : F → Int) (denominator : F → Nat) (frexp : F → F × E)
    (finite zero : F → Bool) (equalHalf : F → FV .f64 → Bool),
  (∀ x, finite x = true → 0 < denominator x) →
  (∀ x, finite x = true → zero x = decide (numerator x = 0)) →
  (∀ x, finite x = true → equalHalf x (reinterpret_Float_Int .f64 exponent_half_Float64) =
      decide (2 * numerator x = (denominator x : Int))) →
  (∀ x, finite x = false → equalHalf x (reinterpret_Float_Int .f64 exponent_half_Float64) = false) →
  (∀ x, finite (frexp x).1 = finite x) →
  (∀ x, finite x = true → numerator (frexp x).1 * ((2 ^ (numerator x).natAbs.log2.succ : Nat) : Int) =
      numerator x * (denominator (frexp x).1 : Int)) →
  ∀ x, ispow2_generic zero frexp equalHalf x = true ↔
    finite x = true ∧ ∃ k : Nat, numerator x = ((2 ^ k : Nat) : Int)

theorem genericBinaryPowerOfTwo_proven : GenericBinaryPowerOfTwo := by
  intro F E numerator denominator frexp finite zero equalHalf hden hzero hhalf hnonfinite hfm hfrac x
  by_cases hfinite : finite x = true
  case neg =>
    have hx : finite x = false := Bool.eq_false_iff.mpr hfinite
    have hm : finite (frexp x).1 = false := by rw [hfm, hx]
    simp only [ispow2_generic, hnonfinite _ hm, Bool.and_false, hfinite, Bool.false_eq_true, false_and]
  simp only [hfinite, true_and]
  let m := (frexp x).1
  let n := numerator x
  let d : Int := denominator m
  let p : Int := ((2 ^ (n.natAbs.log2 + 1) : Nat) : Int)
  have hmf : finite m = true := by rw [hfm, hfinite]
  have hd : 0 < d := Int.natCast_pos.mpr (hden m hmf)
  have hp : 0 < p := Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hf : numerator m * p = n * d := hfrac x hfinite
  have hhalf_iff : 2 * numerator m = d ↔ 2 * n = p := by
    constructor
    · intro hm
      apply Int.eq_of_mul_eq_mul_right (show d ≠ 0 by omega)
      calc
        (2 * n) * d = 2 * (n * d) := by rw [Int.mul_assoc]
        _ = 2 * (numerator m * p) := by rw [hf]
        _ = (2 * numerator m) * p := by rw [Int.mul_assoc]
        _ = p * d := by rw [hm, Int.mul_comm]
    · intro hn
      apply Int.eq_of_mul_eq_mul_right (show p ≠ 0 by omega)
      calc
        (2 * numerator m) * p = 2 * (numerator m * p) := by rw [Int.mul_assoc]
        _ = 2 * (n * d) := by rw [hf]
        _ = (2 * n) * d := by rw [Int.mul_assoc]
        _ = d * p := by rw [hn, Int.mul_comm]
  rw [← numerator_power_two]
  change ispow2_generic zero frexp equalHalf x = true ↔ 2 * n = p
  unfold ispow2_generic
  rw [hzero x hfinite, hhalf (frexp x).1 hmf]
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨_, he⟩
    exact hhalf_iff.mp (of_decide_eq_true he)
  · intro he
    have hn : n ≠ 0 := by omega
    refine ⟨?_, decide_eq_true (hhalf_iff.mpr he)⟩
    change (!decide (n = 0)) = true
    rw [show decide (n = 0) = false from decide_eq_false hn]
    rfl


def GenericEpsilonSpacing : Prop :=
  ∀ (F E : Type) (key : F → Int) (finite normal : F → Bool)
    (ne : F → F → Bool) (abs : F → F) (sub2 : F → F → F)
    (le : F → F → Bool) (minimum : Unit → F) (epsT nan : F)
    (exponent : F → E) (exponentValue : E → Int) (ldexp : F → E → F)
    (step : F → Bool → JInt .u64 → F) (zero : F → F)
    (precisionExponent maxExponent : Nat),
  (∀ x, isfinite_AbstractFloat sub2 (isnan_AbstractFloat ne) x = finite x) →
  (∀ x, le (floatmin_AbstractFloat minimum () x) (abs x) = normal x) →
  key epsT = ((2 ^ precisionExponent : Nat) : Int) →
  (∀ (v : F) (e : E) (p : Nat), key v = ((2 ^ p : Nat) : Int) →
    0 ≤ (p : Int) + exponentValue e → (p : Int) + exponentValue e ≤ maxExponent →
    key (ldexp v e) = ((2 ^ ((p : Int) + exponentValue e).toNat : Nat) : Int)) →
  (∀ x, finite x = true → normal x = true →
    0 ≤ (precisionExponent : Int) + exponentValue (exponent x) ∧
    (precisionExponent : Int) + exponentValue (exponent x) ≤ maxExponent) →
  (∀ x, key (nextfloat_AbstractFloat_one (nextfloat_AbstractFloat step isnegative_int uabs) (zero x)) = 1) →
  (∀ x, finite x = false → key nan = 0 ∧ isnan_AbstractFloat ne nan = true) →
  ∀ x,
    let result := eps_AbstractFloat (isfinite_AbstractFloat sub2 (isnan_AbstractFloat ne)) abs le
      (floatmin_AbstractFloat minimum ()) epsT exponent ldexp
      (nextfloat_AbstractFloat_one (nextfloat_AbstractFloat step isnegative_int uabs)) zero nan x
    (finite x = true →
      key result = ((2 ^ (if normal x then ((precisionExponent : Int) + exponentValue (exponent x)).toNat else 0) : Nat) : Int) ∧
      0 < key result) ∧
    (finite x = false → key result = 0 ∧ isnan_AbstractFloat ne result = true)

theorem genericEpsilonSpacing_proven : GenericEpsilonSpacing := by
  intro F E key finite normal ne abs sub2 le minimum epsT nan exponent exponentValue ldexp step zero
    precisionExponent maxExponent hfinite hnormal heps hldexp hrange hnext hnan x
  dsimp only
  constructor
  · intro hf
    cases hn : normal x
    · simp only [eps_AbstractFloat, hfinite, hf, hnormal, hn, Bool.false_eq_true, ↓reduceIte, hnext]
      decide
    · have hb := hrange x hf hn
      have hval := hldexp epsT (exponent x) precisionExponent heps hb.1 hb.2
      simp only [eps_AbstractFloat, hfinite, hf, hnormal, hn, ↓reduceIte, hval]
      exact ⟨True.intro, Int.natCast_pos.mpr (Nat.two_pow_pos _)⟩
  · intro hf
    simp only [eps_AbstractFloat, hfinite, hf, Bool.false_eq_true, ↓reduceIte]
    exact hnan x hf


theorem wrap_fty_signed_small (T : FTy) (z : Int) (hz : -4096 ≤ z ∧ z ≤ 4096) :
    wrapInt T.intTy z = z := by
  apply wrapInt_of_inRange
  have ht : T.intTy.min ≤ -4096 ∧ 4096 ≤ T.intTy.max := by cases T <;> decide
  omega

theorem wrap_fty_unsigned_small (T : FTy) (z : Int) (hz : 0 ≤ z ∧ z ≤ 4096) :
    wrapInt T.uintTy z = z := by
  apply wrapInt_of_inRange
  have ht : T.uintTy.min = 0 ∧ 4096 ≤ T.uintTy.max := by cases T <;> decide
  omega

theorem wrap_fty_unsigned (T : FTy) (z : Int) :
    wrapInt T.uintTy z = z % ((2 ^ T.fmt.width : Nat) : Int) := by cases T <;> rfl

theorem ctlz_fty_val (T : FTy) (x : JInt T.uintTy) :
    (int.ctlz_int x).val = ((if pattern x = 0 then T.fmt.width else T.fmt.width - (pattern x).log2 - 1 : Nat) : Int) := by
  have hw : T.uintTy.bits = T.fmt.width := by cases T <;> decide
  have hc : (if pattern x = 0 then T.fmt.width else T.fmt.width - (pattern x).log2 - 1 : Nat) ≤ 4096 := by
    have hwidth : T.fmt.width ≤ 4096 := by cases T <;> decide
    split <;> omega
  unfold int.ctlz_int jlCtlzInt
  rw [← pattern_fromJInt]
  simp only [beq_iff_eq]
  rw [toJInt_ofNat_val, hw]
  apply wrap_fty_unsigned_small
  exact ⟨Int.natCast_nonneg _, by omega⟩

theorem normalize_significand (T : FTy) (n : Nat) (hn : 0 < n) (hsmall : n < 2 ^ (T.fmt.sb + 1)) :
    n.log2 ≤ T.fmt.sb ∧
    2 ^ T.fmt.sb ≤ n * 2 ^ (T.fmt.sb - n.log2) ∧
    n * 2 ^ (T.fmt.sb - n.log2) < 2 ^ (T.fmt.sb + 1) := by
  have hlog : n.log2 ≤ T.fmt.sb := by
    have := (Nat.log2_lt (by omega : n ≠ 0)).mpr hsmall
    omega
  have hlo : 2 ^ n.log2 ≤ n := Nat.log2_self_le (by omega)
  have hhi : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  refine ⟨hlog, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_right (2 ^ (T.fmt.sb - n.log2)) hlo
    rw [← Nat.pow_add, Nat.add_sub_of_le hlog] at hmul
    exact hmul
  · have hmul := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos (T.fmt.sb - n.log2))
    rw [← Nat.pow_add] at hmul
    have he : n.log2 + 1 + (T.fmt.sb - n.log2) = T.fmt.sb + 1 := by omega
    rw [he] at hmul
    exact hmul

theorem reconstruct_prefix (T : FTy) {tep : IntTy} (number : JInt T.uintTy) (ep : JInt tep)
    (hn : 0 < pattern number) (hsmall : pattern number < 2 ^ (T.fmt.sb + 1))
    (hep : 0 ≤ ep.val ∧ ep.val ≤ 2099) :
    let lz := int.unsafe_trunc T.intTy (int.sub (int.ctlz_int number) (int.remT T.uintTy (exponent_bits T)))
    lz.val = ((T.fmt.sb - (pattern number).log2 : Nat) : Int) ∧
    pattern (int.shl_Int number (int.widenTo .i64 lz)) = pattern number * 2 ^ (T.fmt.sb - (pattern number).log2) ∧
    (int.unsafe_trunc T.intTy ep).val = ep.val ∧
    (int.sub (int.unsafe_trunc T.intTy ep) lz).val = ep.val - ((T.fmt.sb - (pattern number).log2 : Nat) : Int) := by
  let n := pattern number
  let L := T.fmt.sb - n.log2
  let lz := int.unsafe_trunc T.intTy (int.sub (int.ctlz_int number) (int.remT T.uintTy (exponent_bits T)))
  have hnorm := normalize_significand T n hn hsmall
  have hsb : T.fmt.sb ≤ 52 := by cases T <;> decide
  have hwidth : T.fmt.width = 1 + T.fmt.eb + T.fmt.sb := rfl
  have hw : T.uintTy.bits = T.fmt.width := by cases T <;> decide
  have hL : L ≤ 52 := by dsimp [L]; omega
  have heb : (int.remT T.uintTy (exponent_bits T)).val = (T.fmt.eb : Int) := by cases T <;> decide
  have hc : (int.sub (int.ctlz_int number) (int.remT T.uintTy (exponent_bits T))).val = (L : Int) := by
    rw [sub_int_val, ctlz_fty_val, heb]
    have hn0 : pattern number ≠ 0 := by omega
    simp only [hn0, ↓reduceIte]
    have hnlog : (pattern number).log2 ≤ T.fmt.sb := hnorm.1
    have hd : ((T.fmt.width - (pattern number).log2 - 1 : Nat) : Int) - T.fmt.eb = (L : Int) := by
      dsimp [L, n]
      omega
    rw [hd]
    apply wrap_fty_unsigned_small
    exact ⟨Int.natCast_nonneg _, by omega⟩
  have hlz : lz.val = (L : Int) := by
    change (int.remT T.intTy (int.sub (int.ctlz_int number) (int.remT T.uintTy (exponent_bits T)))).val = (L : Int)
    rw [remT_val, hc]
    apply wrap_fty_signed_small
    exact ⟨by omega, by omega⟩
  have hcount : (int.widenTo .i64 lz).val = (L : Int) := by
    rw [widenTo_val, hlz]
    exact wrap_fty_signed_small .f64 _ ⟨by omega, by omega⟩
  have hnormalized : pattern (int.shl_Int number (int.widenTo .i64 lz)) = n * 2 ^ L := by
    rw [pattern_shl_Int _ _ (by rw [hcount]; exact Int.natCast_nonneg _), hcount, Int.toNat_natCast, hw]
    have hfit : n * 2 ^ L < 2 ^ T.fmt.width := by
      have hpow : 2 ^ (T.fmt.sb + 1) ≤ 2 ^ T.fmt.width := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_lt_of_le hnorm.2.2 hpow
    exact Nat.mod_eq_of_lt hfit
  have he : (int.unsafe_trunc T.intTy ep).val = ep.val := by
    change (int.remT T.intTy ep).val = ep.val
    rw [remT_val]
    exact wrap_fty_signed_small T _ ⟨by omega, by omega⟩
  have heL : (int.sub (int.unsafe_trunc T.intTy ep) lz).val = ep.val - (L : Int) := by
    rw [sub_int_val, he, hlz]
    exact wrap_fty_signed_small T _ ⟨by omega, by omega⟩
  exact ⟨hlz, hnormalized, he, heL⟩

theorem reinterpret_fty_bits (T : FTy) {t : IntTy} (x : JInt t) :
    reinterpret_Float_Int T x = (Fl.ofBits (pattern x) : FV T) := by
  unfold reinterpret_Float_Int bitcast_to_float jlBitcast
  rw [← pattern_fromJInt]

theorem shifted_exponent_mask (T : FTy) (e : Nat) (he : e < 2 ^ T.fmt.eb) :
    e * 2 ^ T.fmt.sb &&& ((2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) = e * 2 ^ T.fmt.sb := by
  have hd := @Nat.shiftLeft_and_distrib T.fmt.sb e (2 ^ T.fmt.eb - 1)
  simp only [Nat.shiftLeft_eq] at hd
  rw [← hd, nat_and_mask, Nat.mod_eq_of_lt he]

theorem normalized_fraction (T : FTy) (n L : Nat)
    (hlo : 2 ^ T.fmt.sb ≤ n * 2 ^ L) (hhi : n * 2 ^ L < 2 ^ (T.fmt.sb + 1)) :
    n * 2 ^ L % 2 ^ T.fmt.sb + 2 ^ T.fmt.sb = n * 2 ^ L := by
  have hless : n * 2 ^ L - 2 ^ T.fmt.sb < 2 ^ T.fmt.sb := by
    rw [Nat.pow_succ] at hhi
    omega
  rw [Nat.mod_eq_sub_mod hlo, Nat.mod_eq_of_lt hless]
  omega

theorem reconstruct_normal_pack (T : FTy) {tep : IntTy} (number : JInt T.uintTy) (ep : JInt tep)
    (hn : 0 < pattern number) (hsmall : pattern number < 2 ^ (T.fmt.sb + 1))
    (hep : 0 ≤ ep.val ∧ ep.val ≤ 2099)
    (hbranch : ((T.fmt.sb - (pattern number).log2 : Nat) : Int) ≤ ep.val)
    (hfinite : ep.val - ((T.fmt.sb - (pattern number).log2 : Nat) : Int) + 1 < T.fmt.emax) :
    _to_float number ep = (Fl.pack false
      (ep.val - ((T.fmt.sb - (pattern number).log2 : Nat) : Int) + 1).toNat
      (pattern number * 2 ^ (T.fmt.sb - (pattern number).log2) % 2 ^ T.fmt.sb) : FV T) := by
  let n := pattern number
  let L := T.fmt.sb - n.log2
  let lz := int.unsafe_trunc T.intTy (int.sub (int.ctlz_int number) (int.remT T.uintTy (exponent_bits T)))
  let number' := int.shl_Int number (int.widenTo .i64 lz)
  let e := int.sub (int.unsafe_trunc T.intTy ep) lz
  let E := (ep.val - (L : Int) + 1).toNat
  change (L : Int) ≤ ep.val at hbranch
  change ep.val - (L : Int) + 1 < T.fmt.emax at hfinite
  have hp := reconstruct_prefix T number ep hn hsmall hep
  have hlz : lz.val = (L : Int) := hp.1
  have hnumber : pattern number' = n * 2 ^ L := hp.2.1
  have he : e.val = ep.val - (L : Int) := hp.2.2.2
  have hL : L ≤ 52 := by
    have hs : T.fmt.sb ≤ 52 := by
      have hsall : ∀ S : FTy, S.fmt.sb ≤ 52 := by intro S; cases S <;> decide
      exact hsall T
    dsimp [L]
    omega
  have hmeta : ∀ S : FTy, S.intTy.signed = true ∧ S.uintTy.bits = S.intTy.bits ∧
      S.intTy.bits = S.fmt.width ∧ S.fmt.width = 1 + S.fmt.eb + S.fmt.sb ∧
      (2 ^ S.fmt.eb : Nat) = S.fmt.emax + 1 ∧
      (significand_bits S).val = (S.fmt.sb : Int) ∧
      pattern (exponent_mask S) = (2 ^ S.fmt.eb - 1) * 2 ^ S.fmt.sb ∧
      pattern (significand_mask S) = 2 ^ S.fmt.sb - 1 ∧
      (int.lit S.intTy 1).val = 1 ∧ (int.lit S.intTy 0).val = 0 := by
    intro S; cases S <;> decide
  obtain ⟨hsgn, hubits, hibits, hwidth, hmaxbits, hsbval, hemask, hsmask, hone, hzero⟩ := hmeta T
  have he0 : 0 ≤ e.val := by rw [he]; exact Int.sub_nonneg.mpr hbranch
  have hcond : int.le_BitSigned (int.lit T.intTy 0) e = true := by
    rw [int.le_BitSigned, sle_int_eq hsgn, hzero]
    exact decide_eq_true he0
  have heplus : (int.add e (int.lit T.intTy 1)).val = ep.val - (L : Int) + 1 := by
    rw [add_int_val, he, hone]
    apply wrap_fty_signed_small
    constructor <;> omega
  have hepat : pattern (int.add e (int.lit T.intTy 1)) = E := by
    rw [pattern_of_nonneg _ (by rw [heplus]; omega), heplus]
  have hE : E < 2 ^ T.fmt.eb := by
    rw [hmaxbits]
    dsimp [E]
    omega
  have hfit : E * 2 ^ T.fmt.sb < 2 ^ T.fmt.width := by
    have hmul := Nat.mul_lt_mul_of_pos_right hE (Nat.two_pow_pos T.fmt.sb)
    rw [← Nat.pow_add] at hmul
    have hpow : 2 ^ (T.fmt.eb + T.fmt.sb) ≤ 2 ^ T.fmt.width :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.lt_of_lt_of_le hmul hpow
  have hshift : pattern (int.shl_Int (int.add e (int.lit T.intTy 1)) (significand_bits T)) =
      E * 2 ^ T.fmt.sb := by
    rw [pattern_shl_Int _ _ (by rw [hsbval]; exact Int.natCast_nonneg _), hepat,
      hsbval, Int.toNat_natCast, hibits, Nat.mod_eq_of_lt hfit]
  have hfrac : pattern (int.band number' (significand_mask T)) = n * 2 ^ L % 2 ^ T.fmt.sb := by
    rw [pattern_band, hnumber, hsmask, nat_and_mask]
  have hexp : pattern (int.band (int.remT T.uintTy (int.shl_Int
      (int.add e (int.lit T.intTy 1)) (significand_bits T))) (exponent_mask T)) = E * 2 ^ T.fmt.sb := by
    rw [pattern_band, pattern_remT_same_bits _ _ hubits, hshift, hemask, shifted_exponent_mask T E hE]
  change reinterpret_Float_Int T (if int.le_BitSigned (int.lit T.intTy 0) e then
      int.bor (int.band number' (significand_mask T))
        (int.band (int.remT T.uintTy (int.shl_Int (int.add e (int.lit T.intTy 1)) (significand_bits T))) (exponent_mask T))
    else _) = _
  rw [hcond]
  simp only [↓reduceIte]
  rw [reinterpret_fty_bits, pattern_bor, hfrac, hexp,
    nat_or_mul_pow _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  unfold Fl.pack
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_comm]
  rfl

theorem reconstruct_subnormal_pack (T : FTy) {tep : IntTy} (number : JInt T.uintTy) (ep : JInt tep)
    (hn : 0 < pattern number) (hsmall : pattern number < 2 ^ (T.fmt.sb + 1))
    (hep : 0 ≤ ep.val ∧ ep.val ≤ 2099)
    (hbranch : ep.val < ((T.fmt.sb - (pattern number).log2 : Nat) : Int)) :
    _to_float number ep = (Fl.pack false 0 (pattern number * 2 ^ ep.val.toNat) : FV T) ∧
    pattern number * 2 ^ ep.val.toNat < 2 ^ T.fmt.sb := by
  let n := pattern number
  let L := T.fmt.sb - n.log2
  let lz := int.unsafe_trunc T.intTy (int.sub (int.ctlz_int number) (int.remT T.uintTy (exponent_bits T)))
  let number' := int.shl_Int number (int.widenTo .i64 lz)
  let e := int.sub (int.unsafe_trunc T.intTy ep) lz
  let c := int.widenTo .i64 (int.neg e)
  change ep.val < (L : Int) at hbranch
  have hp := reconstruct_prefix T number ep hn hsmall hep
  have hnumber : pattern number' = n * 2 ^ L := hp.2.1
  have he : e.val = ep.val - (L : Int) := hp.2.2.2
  have hsall : ∀ S : FTy, S.fmt.sb ≤ 52 ∧ S.intTy.signed = true ∧ S.uintTy.signed = false ∧
      (int.lit S.intTy 0).val = 0 ∧ pattern (significand_mask S) = 2 ^ S.fmt.sb - 1 := by
    intro S; cases S <;> decide
  obtain ⟨hsb, hsgn, hu, hzero, hmask⟩ := hsall T
  have hL : L ≤ 52 := by dsimp [L]; omega
  have he0 : e.val < 0 := by rw [he]; omega
  have hcond : int.le_BitSigned (int.lit T.intTy 0) e = false := by
    rw [int.le_BitSigned, sle_int_eq hsgn, hzero]
    exact decide_eq_false (by omega)
  have hneg : (int.neg e).val = (L : Int) - ep.val := by
    rw [neg_int_val, he]
    have hv : -(ep.val - (L : Int)) = (L : Int) - ep.val := by omega
    rw [hv]
    exact wrap_fty_signed_small T _ ⟨by omega, by omega⟩
  have hc : c.val = (L : Int) - ep.val := by
    rw [widenTo_val, hneg]
    exact wrap_fty_signed_small .f64 _ ⟨by omega, by omega⟩
  have hcNat : c.val.toNat = L - ep.val.toNat := by rw [hc]; omega
  have hepL : ep.val.toNat ≤ L := by omega
  have hpowers : 2 ^ L = 2 ^ ep.val.toNat * 2 ^ (L - ep.val.toNat) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hepL]
  have hshift : pattern (int.shr_Int number' c) = n * 2 ^ ep.val.toNat := by
    rw [pattern_shr_Int_unsigned hu _ _ (by rw [hc]; omega), hnumber, hcNat, hpowers,
      ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hsmallResult : n * 2 ^ ep.val.toNat < 2 ^ T.fmt.sb := by
    have hlog : n.log2 ≤ T.fmt.sb := (normalize_significand T n hn hsmall).1
    have heL : n.log2 + 1 + ep.val.toNat ≤ T.fmt.sb := by dsimp [L] at hbranch; omega
    have hmul := Nat.mul_lt_mul_of_pos_right (show n < 2 ^ (n.log2 + 1) from Nat.lt_log2_self)
      (Nat.two_pow_pos ep.val.toNat)
    rw [← Nat.pow_add] at hmul
    exact Nat.lt_of_lt_of_le hmul (Nat.pow_le_pow_right (by decide) heL)
  refine ⟨?_, hsmallResult⟩
  change reinterpret_Float_Int T (if int.le_BitSigned (int.lit T.intTy 0) e then _
    else int.band (int.shr_Int number' c) (significand_mask T)) = _
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [reinterpret_fty_bits, pattern_band, hshift, hmask, nat_and_mask, Nat.mod_eq_of_lt hsmallResult]
  unfold Fl.pack
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.zero_mul]
  rfl

theorem to_float_exact_key (T : FTy) {tep : IntTy} (number : JInt T.uintTy) (ep : JInt tep)
    (hn : 0 < pattern number) (hsmall : pattern number < 2 ^ (T.fmt.sb + 1))
    (hep : 0 ≤ ep.val)
    (hfinite : ep.val.toNat + (pattern number).log2 + 1 < T.fmt.emax + T.fmt.sb) :
    (_to_float number ep).isfinite = true ∧ (_to_float number ep).signbit = false ∧
    (_to_float number ep).key = ((pattern number * 2 ^ ep.val.toNat : Nat) : Int) := by
  let n := pattern number
  let L := T.fmt.sb - n.log2
  have hnorm := normalize_significand T n hn hsmall
  change ep.val.toNat + n.log2 + 1 < T.fmt.emax + T.fmt.sb at hfinite
  have hmeta : ∀ S : FTy, 0 < S.fmt.emax ∧ S.fmt.emax + S.fmt.sb ≤ 2099 ∧
      (2 ^ S.fmt.eb : Nat) = S.fmt.emax + 1 := by
    intro S; cases S <;> decide
  obtain ⟨hmaxpos, hmaxsmall, hmaxbits⟩ := hmeta T
  have heps : ep.val ≤ 2099 := by omega
  by_cases hnormal : (L : Int) ≤ ep.val
  · let E := (ep.val - (L : Int) + 1).toNat
    have hEpos : 0 < E := by dsimp [E]; omega
    have hEmax : E < T.fmt.emax := by
      dsimp [E, L]
      have hnlog := hnorm.1
      omega
    have hEbits : E < 2 ^ T.fmt.eb := by rw [hmaxbits]; omega
    have hEf : ep.val - (L : Int) + 1 < T.fmt.emax := by
      dsimp [E] at hEmax
      omega
    rw [reconstruct_normal_pack T number ep hn hsmall ⟨hep, heps⟩ hnormal hEf]
    have hfrac : n * 2 ^ L % 2 ^ T.fmt.sb < 2 ^ T.fmt.sb := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hparts := Fl.pack_parts (f := T.fmt) false E (n * 2 ^ L % 2 ^ T.fmt.sb) hEbits hfrac
    refine ⟨?_, hparts.1, ?_⟩
    · unfold Fl.isfinite
      rw [hparts.2.1]
      simp only [bne_iff_ne]
      omega
    · rw [Fl.pack_key false E _ hEbits hfrac]
      simp only [Bool.false_eq_true, ↓reduceIte, show E ≠ 0 by omega]
      rw [normalized_fraction T n L hnorm.2.1 hnorm.2.2]
      have he : L + (E - 1) = ep.val.toNat := by dsimp [E]; omega
      rw [Nat.mul_assoc, ← Nat.pow_add, he]
  · have hsub : ep.val < (L : Int) := by omega
    have hpack := reconstruct_subnormal_pack T number ep hn hsmall ⟨hep, heps⟩ hsub
    rw [hpack.1]
    have hbits : (0 : Nat) < 2 ^ T.fmt.eb := Nat.two_pow_pos _
    have hparts := Fl.pack_parts (f := T.fmt) false 0 (n * 2 ^ ep.val.toNat) hbits hpack.2
    refine ⟨?_, hparts.1, ?_⟩
    · unfold Fl.isfinite
      rw [hparts.2.1]
      simp only [bne_iff_ne]
      omega
    · rw [Fl.pack_key false 0 _ hbits hpack.2]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_sub, Nat.pow_zero, Nat.add_zero, Nat.mul_one]

theorem uint_fty_lt (T : FTy) (x : JInt T.uintTy) : pattern x < 2 ^ T.fmt.width := by
  have hw : T.uintTy.bits = T.fmt.width := by cases T <;> decide
  simpa only [hw] using pattern_lt x

theorem uint_fty_wrap (T : FTy) (z : Int) :
    wrapInt T.uintTy z = z % ((2 ^ T.fmt.width : Nat) : Int) := by cases T <;> rfl

theorem uint_fty_compare (T : FTy) (x y : JInt T.uintTy) :
    int.lt_BitUnsigned x y = decide (pattern x < pattern y) := by
  have hu : T.uintTy.signed = false := by cases T <;> decide
  rw [int.lt_BitUnsigned, ult_int_eq hu, ← val_of_unsigned_pattern hu x, ← val_of_unsigned_pattern hu y]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem uint_fty_sub (T : FTy) (x y : JInt T.uintTy) (h : pattern y ≤ pattern x) :
    pattern (int.sub x y) = pattern x - pattern y := by
  have hu : T.uintTy.signed = false := by cases T <;> decide
  have hx := uint_fty_lt T x
  have hv : ((pattern (int.sub x y) : Nat) : Int) = ((pattern x - pattern y : Nat) : Int) := by
    rw [val_of_unsigned_pattern hu, sub_int_val, uint_fty_wrap,
      ← val_of_unsigned_pattern hu x, ← val_of_unsigned_pattern hu y, ← Int.natCast_sub h]
    apply Int.emod_eq_of_lt
    · exact Int.natCast_nonneg _
    · omega
  exact Int.ofNat_inj.mp hv

theorem urem_fty_val (T : FTy) (x y : JInt T.uintTy) (hy : 0 < y.val) :
    (urem_int x y).val = x.val % y.val := by
  have hu : T.uintTy.signed = false := by cases T <;> decide
  have hx := fromJInt_toNat_unsigned x hu
  have hyv := fromJInt_toNat_unsigned y hu
  have hx0 : 0 ≤ x.val := by rw [← val_of_unsigned_pattern hu x]; exact Int.natCast_nonneg _
  unfold urem_int jlUremInt integerDivide
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, hx, hyv,
    show (y.val == 0) = false from beq_eq_false_iff_ne.mpr (by omega), Bool.false_eq_true,
    pure, Except.pure, bind, Except.bind]
  rw [toJInt_ofInt_val, Int.tmod_eq_emod_of_nonneg hx0]
  apply wrapInt_of_inRange
  have ht : T.uintTy.min = 0 := by cases T <;> decide
  have hmod0 := Int.emod_nonneg x.val (Int.ne_of_gt hy)
  have hmodlt := Int.emod_lt_of_pos x.val hy
  have hym := y.property.2
  constructor <;> omega

theorem urem_fty_pattern (T : FTy) (x y : JInt T.uintTy) (hy : 0 < pattern y) :
    pattern (urem_int x y) = pattern x % pattern y := by
  have hu : T.uintTy.signed = false := by cases T <;> decide
  have hyv : 0 < y.val := by rw [← val_of_unsigned_pattern hu y]; omega
  have hv : ((pattern (urem_int x y) : Nat) : Int) = ((pattern x % pattern y : Nat) : Int) := by
    rw [val_of_unsigned_pattern hu, urem_fty_val T x y hyv,
      ← val_of_unsigned_pattern hu x, ← val_of_unsigned_pattern hu y, Int.natCast_emod]
  exact Int.ofNat_inj.mp hv

theorem uint_fty_shift (T : FTy) (x c : JInt T.uintTy) :
    pattern (int.shl_BitInteger_BitUnsigned x c) = pattern x * 2 ^ pattern c % 2 ^ T.fmt.width := by
  have hw : T.uintTy.bits = T.fmt.width := by cases T <;> decide
  rw [int.shl_BitInteger_BitUnsigned, pattern_shl_int, hw]

theorem rem_loop_remainder (T : FTy) (fuel : Nat)
    (d c m y : JInt T.uintTy) (hd : pattern d ≤ fuel)
    (hc : 0 < pattern c) (hy : 0 < pattern y)
    (hm : pattern m < pattern y)
    (hcapacity : pattern y * 2 ^ pattern c ≤ 2 ^ T.fmt.width) :
    let result := rem_internal_loop fuel d c m y
    pattern result.1 ≤ pattern c ∧ pattern result.2 < pattern y ∧
    (pattern result.2 * 2 ^ pattern result.1) % pattern y =
      (pattern m * 2 ^ pattern d) % pattern y := by
  induction fuel generalizing d m with
  | zero =>
    simp only [rem_internal_loop]
    exact ⟨by omega, hm, True.intro⟩
  | succ fuel ih =>
    unfold rem_internal_loop
    rw [uint_fty_compare]
    by_cases hstep : pattern c < pattern d
    · simp only [hstep, decide_true, ↓reduceIte]
      have hsub := uint_fty_sub T d c (by omega)
      have hshift : pattern (int.shl_BitInteger_BitUnsigned m c) = pattern m * 2 ^ pattern c := by
        rw [uint_fty_shift]
        apply Nat.mod_eq_of_lt
        have hmul := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos (pattern c))
        omega
      have hrem := urem_fty_pattern T (int.shl_BitInteger_BitUnsigned m c) y hy
      rw [hshift] at hrem
      have hbound : pattern (urem_int (int.shl_BitInteger_BitUnsigned m c) y) < pattern y := by
        rw [hrem]
        exact Nat.mod_lt _ hy
      have hrest := ih (int.sub d c) (urem_int (int.shl_BitInteger_BitUnsigned m c) y)
        (by rw [hsub]; omega) hbound
      dsimp only at hrest
      refine ⟨hrest.1, hrest.2.1, ?_⟩
      rw [hrest.2.2, hrem, hsub]
      calc
        ((pattern m * 2 ^ pattern c) % pattern y * 2 ^ (pattern d - pattern c)) % pattern y =
            (pattern m * 2 ^ pattern c * 2 ^ (pattern d - pattern c)) % pattern y := by
          exact Nat.mod_mul_mod _ _ _
        _ = (pattern m * 2 ^ pattern d) % pattern y := by
          rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le (by omega : pattern c ≤ pattern d)]
    · simp only [hstep, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨by omega, hm, True.intro⟩

theorem odd_mod_power_nonzero (m y c : Nat) (hodd : y % 2 = 1) (hm0 : 0 < m) (hm : m < y) :
    (m * 2 ^ c) % y ≠ 0 := by
  have hcop : Nat.Coprime y 2 := by
    change Nat.gcd y 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec 2 y, hodd, Nat.gcd_one_left]
  intro hzero
  have hdiv := Nat.dvd_of_mod_eq_zero hzero
  have hmdiv : y ∣ m := (hcop.pow_right c).dvd_of_dvd_mul_right hdiv
  have hmzero := Nat.mod_eq_zero_of_dvd hmdiv
  rw [Nat.mod_eq_of_lt hm] at hmzero
  omega

theorem rem_loop_final (T : FTy) (fuel : Nat)
    (d c m y : JInt T.uintTy) (hd : pattern d ≤ fuel)
    (hc : 0 < pattern c) (hy : 0 < pattern y)
    (hm : pattern m < pattern y)
    (hcapacity : pattern y * 2 ^ pattern c ≤ 2 ^ T.fmt.width) :
    let result := rem_internal_loop fuel d c m y
    let remainder := urem_int (int.shl_BitInteger_BitUnsigned result.2 result.1) y
    pattern remainder = (pattern m * 2 ^ pattern d) % pattern y ∧
    pattern remainder < pattern y ∧
    (pattern y % 2 = 1 → 0 < pattern m → 0 < pattern remainder) := by
  have hr := rem_loop_remainder T fuel d c m y hd hc hy hm hcapacity
  let result := rem_internal_loop fuel d c m y
  change pattern result.1 ≤ pattern c ∧ pattern result.2 < pattern y ∧
    (pattern result.2 * 2 ^ pattern result.1) % pattern y =
      (pattern m * 2 ^ pattern d) % pattern y at hr
  have hs : pattern (int.shl_BitInteger_BitUnsigned result.2 result.1) =
      pattern result.2 * 2 ^ pattern result.1 := by
    rw [uint_fty_shift]
    apply Nat.mod_eq_of_lt
    have hmul := Nat.mul_lt_mul_of_pos_right hr.2.1 (Nat.two_pow_pos (pattern result.1))
    have hpow : 2 ^ pattern result.1 ≤ 2 ^ pattern c := Nat.pow_le_pow_right (by decide) hr.1
    have hcap := Nat.mul_le_mul_left (pattern y) hpow
    omega
  have hv : pattern (urem_int (int.shl_BitInteger_BitUnsigned result.2 result.1) y) =
      (pattern m * 2 ^ pattern d) % pattern y := by
    rw [urem_fty_pattern T _ y hy, hs]
    exact hr.2.2
  dsimp only
  refine ⟨hv, ?_, ?_⟩
  · rw [hv]
    exact Nat.mod_lt _ hy
  · intro hodd hm0
    rw [hv]
    have hnonzero := odd_mod_power_nonzero (pattern m) (pattern y) (pattern d) hodd hm0 hm
    omega

theorem uint_fty_le (T : FTy) (x y : JInt T.uintTy) :
    int.le_BitUnsigned x y = decide (pattern x ≤ pattern y) := by
  have hu : T.uintTy.signed = false := by cases T <;> decide
  rw [int.le_BitUnsigned, ule_int_eq hu, ← val_of_unsigned_pattern hu x, ← val_of_unsigned_pattern hu y]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem positive_subnormal_pack {T : FTy} (x : FV T) (hs : x.signbit = false) (he : x.expField = 0) :
    x = (Fl.pack false 0 x.frac : FV T) := by
  have hm : x.magnitude = x.frac := by simpa only [he, Nat.zero_mul, Nat.zero_add] using (mag_decomp x).1
  have hb : x.toBits = x.frac := by
    rw [(Fl.bits_split x).1, hs, hm]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  calc
    x = Fl.ofBits x.toBits := (Fl.ofBits_toBits x).symm
    _ = Fl.pack false 0 x.frac := by rw [hb]; simp [Fl.pack]

theorem subnormal_remainder_pack {T : FTy} (x y : FV T)
    (hxs : x.signbit = false) (hys : y.signbit = false)
    (hxe : x.expField = 0) (hye : y.expField = 0) (hy : 0 < y.frac) :
    rem_internal x y = (Fl.pack false 0 (x.frac % y.frac) : FV T) := by
  have hxp := positive_subnormal_pack x hxs hxe
  have hyp := positive_subnormal_pack y hys hye
  have hxb : x.toBits = x.frac := by
    rw [(Fl.bits_split x).1, hxs]
    have hm := (mag_decomp x).1
    simp only [hxe, Nat.zero_mul, Nat.zero_add] at hm
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using hm
  have hyb : y.toBits = y.frac := by
    rw [(Fl.bits_split y).1, hys]
    have hm := (mag_decomp y).1
    simp only [hye, Nat.zero_mul, Nat.zero_add] at hm
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using hm
  have hex : (unbiased_exponent x).val = 0 := by
    rw [(floatFieldsAndRemModCore_proven T x y).1, hxe]
    rfl
  have hey : (unbiased_exponent y).val = 0 := by
    rw [(floatFieldsAndRemModCore_proven T y x).1, hye]
    rfl
  have hmasks : ∀ S : FTy, (significand_bits S).val = (S.fmt.sb : Int) ∧
      pattern (significand_mask S) = 2 ^ S.fmt.sb - 1 ∧
      (zero_float S) = (Fl.pack false 0 0 : FV S) := by
    intro S; cases S <;> decide
  obtain ⟨hsb, hmask, hzero⟩ := hmasks T
  have hfast : int.lt (significand_bits T) (unbiased_exponent y) = false := by
    rw [JuliaLean.Proofs.base.int.lt_eq, hsb, hey]
    exact decide_eq_false (by omega)
  have heqx : int.eq (unbiased_exponent x) (int.lit .i64 0) = true := by
    rw [JuliaLean.Proofs.base.int.eq_eq, hex]
    decide
  have heqy : int.eq (unbiased_exponent y) (int.lit .i64 0) = true := by
    rw [JuliaLean.Proofs.base.int.eq_eq, hey]
    decide
  unfold rem_internal
  dsimp only
  rw [uint_fty_le, uint_fty_compare, pattern_reinterpret_Unsigned, pattern_reinterpret_Unsigned, hxb, hyb]
  by_cases hle : x.frac ≤ y.frac
  · simp only [hle, decide_true, ↓reduceIte]
    by_cases hlt : x.frac < y.frac
    · simp only [hlt, decide_true, ↓reduceIte, Nat.mod_eq_of_lt hlt]
      exact hxp
    · have hequal : x.frac = y.frac := by omega
      simp only [hequal, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.mod_self, hzero]
  · simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte, hfast, Bool.false_and, heqx, heqy,
      Bool.true_and]
    have hrem : pattern (urem_int (reinterpret_Unsigned x) (reinterpret_Unsigned y)) = x.frac % y.frac := by
      rw [urem_fty_pattern T _ _ (by rw [pattern_reinterpret_Unsigned, hyb]; exact hy),
        pattern_reinterpret_Unsigned, pattern_reinterpret_Unsigned, hxb, hyb]
    have hfrac : x.frac % y.frac < 2 ^ T.fmt.sb :=
      Nat.lt_trans (Nat.mod_lt _ hy) (mag_decomp y).2
    unfold reinterpret_Float_Int bitcast_to_float jlBitcast
    rw [← pattern_fromJInt, pattern_band, hrem, hmask, nat_and_mask, Nat.mod_eq_of_lt hfrac]
    simp [Fl.pack]

theorem cttz_fty_val (T : FTy) (x : JInt T.uintTy) :
    (int.cttz_int x).val =
      (((List.range T.uintTy.bits).find? (fun i => (pattern x).testBit i)).getD T.uintTy.bits : Nat) := by
  let c := ((List.range T.uintTy.bits).find? (fun i => (pattern x).testBit i)).getD T.uintTy.bits
  have hs := JuliaLean.Proofs.base.int.trailing_spec x
  have hc : c ≤ T.uintTy.bits := hs.1
  have hmeta : ∀ S : FTy, S.uintTy.bits < 2 ^ S.fmt.width := by intro S; cases S <;> decide
  have hcap := hmeta T
  unfold int.cttz_int jlCttzInt
  rw [← pattern_fromJInt]
  have hf : (fun i => pattern x / 2 ^ i % 2 == 1) = (fun i => (pattern x).testBit i) := by
    funext i
    rw [Nat.testBit_eq_decide_div_mod_eq]
    cases h : (pattern x / 2 ^ i % 2 == 1) <;> simp_all
  rw [hf, toJInt_ofNat_val, uint_fty_wrap]
  apply Int.emod_eq_of_lt
  · exact Int.natCast_nonneg _
  · omega

theorem cttz_fty_factor (T : FTy) (x : JInt T.uintTy) (hx : 0 < pattern x) :
    let c := pattern (int.cttz_int x)
    c ≤ (pattern x).log2 ∧
    pattern x % 2 ^ c = 0 ∧
    (pattern x / 2 ^ c) % 2 = 1 := by
  let c := ((List.range T.uintTy.bits).find? (fun i => (pattern x).testBit i)).getD T.uintTy.bits
  have hu : T.uintTy.signed = false := by
    have hh : ∀ S : FTy, S.uintTy.signed = false := by intro S; cases S <;> decide
    exact hh T
  have hcount : pattern (int.cttz_int x) = c := by
    have hv := cttz_fty_val T x
    have hp := val_of_unsigned_pattern hu (int.cttz_int x)
    omega
  rw [hcount]
  have hs : c ≤ T.uintTy.bits ∧ (∀ i, i < c → (pattern x).testBit i = false) ∧
      (c < T.uintTy.bits → (pattern x).testBit c = true) :=
    JuliaLean.Proofs.base.int.trailing_spec x
  have hbelow (i : Nat) (hi : i < c) : (pattern x).testBit i = false := by
    exact hs.2.1 i hi
  have hlog : (pattern x).log2 < T.uintTy.bits :=
    (Nat.log2_lt (by omega : pattern x ≠ 0)).mpr (pattern_lt x)
  have hc : c ≤ (pattern x).log2 := by
    apply Nat.le_of_not_gt
    intro hh
    have hz := hbelow (pattern x).log2 hh
    rw [Nat.testBit_log2 (by omega : pattern x ≠ 0)] at hz
    contradiction
  have hbit : (pattern x).testBit c = true := hs.2.2 (by omega)
  refine ⟨hc, ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < c
    · simp only [hi, decide_true, Bool.true_and, hbelow i hi]
    · simp only [hi, decide_false, Bool.false_and]
  · rw [Nat.mod_two_eq_one_iff_testBit_zero, Nat.testBit_div_two_pow, Nat.zero_add]
    exact hbit

theorem uint_fty_eq_zero (T : FTy) (x : JInt T.uintTy) :
    int.eq x (int.lit T.uintTy 0) = decide (pattern x = 0) := by
  have hmeta : ∀ S : FTy, S.uintTy.signed = false ∧ (int.lit S.uintTy 0).val = 0 := by
    intro S; cases S <;> decide
  obtain ⟨hu, hzero⟩ := hmeta T
  rw [JuliaLean.Proofs.base.int.eq_eq, hzero, ← val_of_unsigned_pattern hu x]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem remainder_finish_key (T : FTy) (d c m y e : JInt T.uintTy)
    (hc : 0 < pattern c) (hy : 0 < pattern y) (hm : pattern m < pattern y)
    (hsmall : pattern y ≤ 2 ^ (T.fmt.sb + 1))
    (hcapacity : pattern y * 2 ^ pattern c ≤ 2 ^ T.fmt.width)
    (hodd : pattern d ≠ 0 → pattern y % 2 = 1)
    (hrange : ∀ q : Nat, 0 < q → q < pattern y → pattern e + q.log2 + 1 < T.fmt.emax + T.fmt.sb) :
    let result := if int.eq m (int.lit T.uintTy 0) then zero_float T
      else if int.eq d (int.lit T.uintTy 0) then _to_float m e
      else
        let z := rem_internal_loop d.val.toNat d c m y
        let r := urem_int (int.shl_BitInteger_BitUnsigned z.2 z.1) y
        _to_float r e
    (result.isfinite = true ∧ result.signbit = false ∧
      result.key = (((pattern m * 2 ^ pattern d % pattern y) * 2 ^ pattern e : Nat) : Int)) := by
  have huall : ∀ S : FTy, S.uintTy.signed = false ∧ (zero_float S).signbit = false := by
    intro S; cases S <;> decide
  obtain ⟨hu, hzsign⟩ := huall T
  have hE : e.val.toNat = pattern e := by have := val_of_unsigned_pattern hu e; omega
  have hD : d.val.toNat = pattern d := by have := val_of_unsigned_pattern hu d; omega
  have hz := Fl.zero_spec (good_fty T) false
  rw [uint_fty_eq_zero, uint_fty_eq_zero]
  by_cases hm0 : pattern m = 0
  · simp only [hm0, decide_true, ↓reduceIte, Nat.zero_mul, Nat.zero_mod]
    exact ⟨hz.1, hzsign, hz.2⟩
  · simp only [hm0, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hd0 : pattern d = 0
    · simp only [hd0, decide_true, ↓reduceIte, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hm]
      have hv := to_float_exact_key T m e (by omega) (Nat.lt_of_lt_of_le hm hsmall)
        (by rw [← val_of_unsigned_pattern hu e]; exact Int.natCast_nonneg _) (by rw [hE]; exact hrange _ (by omega) hm)
      simpa only [hE] using hv
    · simp only [hd0, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hlo := rem_loop_final T d.val.toNat d c m y (by rw [hD]; exact Nat.le_refl _) hc hy hm hcapacity
      let z := rem_internal_loop d.val.toNat d c m y
      let r := urem_int (int.shl_BitInteger_BitUnsigned z.2 z.1) y
      have hr : pattern r = (pattern m * 2 ^ pattern d) % pattern y := hlo.1
      have hrb : pattern r < pattern y := hlo.2.1
      have hr0 : 0 < pattern r := hlo.2.2 (hodd hd0) (by omega)
      have hv := to_float_exact_key T r e hr0 (Nat.lt_of_lt_of_le hrb hsmall)
        (by rw [← val_of_unsigned_pattern hu e]; exact Int.natCast_nonneg _) (by rw [hE]; exact hrange _ hr0 hrb)
      simpa only [hr, hE] using hv

theorem remainder_scaled_units (a b e d : Nat) :
    (a * 2 ^ (d + e)) % (b * 2 ^ e) = (a * 2 ^ d % b) * 2 ^ e := by
  rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_mod_mul_right]

theorem exact_power_factor (b s : Nat) (h : b % 2 ^ s = 0) :
    b = (b / 2 ^ s) * 2 ^ s := by
  have hdiv := Nat.mod_add_div b (2 ^ s)
  rw [h, Nat.zero_add] at hdiv
  exact hdiv.symm.trans (Nat.mul_comm _ _)

theorem preprocessing_remainder (mx my ex ey right left rest : Nat)
    (hdiv : my % 2 ^ right = 0) (hex : ex = left + rest + (ey + right)) :
    (mx * 2 ^ ex) % (my * 2 ^ ey) =
      (((mx * 2 ^ left) % (my / 2 ^ right) * 2 ^ rest) % (my / 2 ^ right)) * 2 ^ (ey + right) := by
  have hmy : my * 2 ^ ey = (my / 2 ^ right) * 2 ^ (ey + right) := by
    calc
      my * 2 ^ ey = ((my / 2 ^ right) * 2 ^ right) * 2 ^ ey := congrArg (fun v => v * 2 ^ ey) (exact_power_factor my right hdiv)
      _ = (my / 2 ^ right) * 2 ^ (ey + right) := by
        rw [Nat.mul_assoc, ← Nat.pow_add]
        congr 2
        omega
  have hmx : mx * 2 ^ ex = ((mx * 2 ^ left) * 2 ^ rest) * 2 ^ (ey + right) := by
    rw [hex, Nat.pow_add, Nat.pow_add]
    simp only [Nat.mul_assoc]
  rw [hmx, hmy, Nat.mul_mod_mul_right, Nat.mod_mul_mod]

theorem positive_float_key {T : FTy} (x : FV T) (hs : x.signbit = false) :
    x.key = (((x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb) *
      2 ^ (x.expField - 1) : Nat) : Int) := by
  unfold Fl.key
  rw [hs]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold magKey
  rw [← Fl.expField_eq, ← Fl.frac_eq]

def FloatReconstructionExact : Prop := ∀ (T : FTy) (tep : IntTy) (number : JInt T.uintTy) (ep : JInt tep),
  0 < pattern number → pattern number < 2 ^ (T.fmt.sb + 1) → 0 ≤ ep.val →
  ep.val.toNat + (pattern number).log2 + 1 < T.fmt.emax + T.fmt.sb →
  (_to_float number ep).isfinite = true ∧ (_to_float number ep).signbit = false ∧
  (_to_float number ep).key = ((pattern number * 2 ^ ep.val.toNat : Nat) : Int)

theorem floatReconstructionExact_proven : FloatReconstructionExact := by
  intro T tep number ep
  exact to_float_exact_key T number ep

def SubnormalRemainderExact : Prop := ∀ (T : FTy) (x y : FV T),
  x.signbit = false → y.signbit = false → x.expField = 0 → y.expField = 0 → 0 < y.frac →
  rem_internal x y = (Fl.pack false 0 (x.frac % y.frac) : FV T)

theorem subnormalRemainderExact_proven : SubnormalRemainderExact := by
  intro T x y
  exact subnormal_remainder_pack x y

def RemainderLoopExact : Prop := ∀ (T : FTy) (d c m y : JInt T.uintTy),
  0 < pattern c → 0 < pattern y → pattern m < pattern y →
  pattern y * 2 ^ pattern c ≤ 2 ^ T.fmt.width →
  let result := rem_internal_loop d.val.toNat d c m y
  pattern result.1 ≤ pattern c ∧ pattern result.2 < pattern y ∧
  (pattern result.2 * 2 ^ pattern result.1) % pattern y = (pattern m * 2 ^ pattern d) % pattern y

theorem remainderLoopExact_proven : RemainderLoopExact := by
  intro T d c m y hc hy hm hcapacity
  have hmeta : ∀ S : FTy, S.uintTy.signed = false := by intro S; cases S <;> decide
  have hv := val_of_unsigned_pattern (hmeta T) d
  exact rem_loop_remainder T d.val.toNat d c m y (by omega) hc hy hm hcapacity


namespace EpsilonProofs
open TruncProofs NextProofs

theorem roundRat_dyadic_pack (T : FTy) (i j k : Nat) (s z : Bool)
    (hscale : i + (T.fmt.bias + T.fmt.sb - 1) = j + k)
    (hfinite : k + 1 < T.fmt.emax + T.fmt.sb) :
    (Fl.roundRat (if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)) (2 ^ j) z : FV T) =
      Fl.pack s (if k < T.fmt.sb then 0 else k - T.fmt.sb + 1)
        (if k < T.fmt.sb then 2 ^ k else 0) := by
  have hg := good_fty T
  have hbias := hg.bias_pos
  have hsb := hg.sb_pos
  have hemax := hg.emax_eq
  have hposi : (0 : Int) < ((2 ^ i : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos i)
  have hposj : 0 < 2 ^ j := Nat.two_pow_pos j
  have hn0 : (if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)) ≠ 0 := by cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hnabs : (if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)).natAbs = 2 ^ i := by
    cases s <;> simp
  have hsign : decide ((if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)) < 0) = s := by
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact decide_eq_false (by omega)
    · simp only [↓reduceIte]
      exact decide_eq_true (by omega)
  have hfloor : Fl.floorLog2Rat (2 ^ i) (2 ^ j) = (i : Int) - j := by
    rw [Fl.floorLog2Rat_pow _ j (by omega), Nat.log2_two_pow]
  have he : (i : Int) - j = (k : Int) - (T.fmt.bias + T.fmt.sb - 1 : Nat) := by omega
  have hlarge : ¬ (i : Int) - j ≥ (T.fmt.emax : Int) - T.fmt.bias := by omega
  have htiny : ¬ (i : Int) - j < -((T.fmt.bias : Int) + T.fmt.sb) - 1 := by omega
  unfold Fl.roundRat
  simp only [beq_iff_eq, show ¬ (2 ^ j : Nat) = 0 by omega, hn0, Bool.false_eq_true, ↓reduceIte, hsign, hnabs,
    hfloor, hlarge, htiny]
  by_cases hs : k < T.fmt.sb
  · have hmax : max ((i : Int) - j - T.fmt.sb) (1 - (T.fmt.bias : Int) - T.fmt.sb) =
        1 - (T.fmt.bias : Int) - T.fmt.sb := by omega
    rw [hmax]
    have hneg : ¬0 ≤ 1 - (T.fmt.bias : Int) - T.fmt.sb := by omega
    simp only [hneg, ↓reduceIte]
    have hD : (-(1 - (T.fmt.bias : Int) - T.fmt.sb)).toNat = T.fmt.bias + T.fmt.sb - 1 := by omega
    rw [hD]
    have hnum : 2 ^ i * 2 ^ (T.fmt.bias + T.fmt.sb - 1) = 2 ^ k * 2 ^ j := by
      rw [← Nat.pow_add, ← Nat.pow_add, hscale, Nat.add_comm j k]
    rw [hnum, Fl.roundQuotient_exact _ _ hposj]
    have hq0 : ¬ (2 ^ k : Nat) = 0 := by have := Nat.two_pow_pos k; omega
    have hq : (2 ^ k : Nat) < 2 ^ T.fmt.sb := Nat.pow_lt_pow_right (by decide) hs
    have hq2 : ¬ (2 ^ k : Nat) ≥ 2 ^ (T.fmt.sb + 1) := by
      have hmore : 2 ^ T.fmt.sb < 2 ^ (T.fmt.sb + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    unfold Fl.packRounded
    simp only [beq_iff_eq, hq0, Bool.false_eq_true, ↓reduceIte, hq2]
    have hp : 1 - (T.fmt.bias : Int) - T.fmt.sb + T.fmt.bias + T.fmt.sb = 1 := by omega
    rw [hp]
    simp only [hs, ↓reduceIte, show ¬ (1 : Int) ≥ T.fmt.emax by omega, hq,
      beq_self_eq_true, decide_true, Bool.true_and, Int.toNat_one]
    unfold Fl.pack
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_assoc]
  · have hks : T.fmt.sb ≤ k := by omega
    have hmax : max ((i : Int) - j - T.fmt.sb) (1 - (T.fmt.bias : Int) - T.fmt.sb) =
        (i : Int) - j - T.fmt.sb := by omega
    rw [hmax]
    have hrounded : Fl.roundQuotient
        (if (i : Int) - j - T.fmt.sb ≥ 0 then (2 ^ i, 2 ^ j * 2 ^ ((i : Int) - j - T.fmt.sb).toNat)
          else (2 ^ i * 2 ^ (-((i : Int) - j - T.fmt.sb)).toNat, 2 ^ j)).1
        (if (i : Int) - j - T.fmt.sb ≥ 0 then (2 ^ i, 2 ^ j * 2 ^ ((i : Int) - j - T.fmt.sb).toNat)
          else (2 ^ i * 2 ^ (-((i : Int) - j - T.fmt.sb)).toNat, 2 ^ j)).2 = 2 ^ T.fmt.sb := by
      by_cases hk : 0 ≤ (i : Int) - j - T.fmt.sb
      · simp only [hk, ↓reduceIte]
        have hp : i = T.fmt.sb + (j + ((i : Int) - j - T.fmt.sb).toNat) := by omega
        have heq : 2 ^ i = 2 ^ T.fmt.sb * (2 ^ j * 2 ^ ((i : Int) - j - T.fmt.sb).toNat) := by
          rw [← Nat.pow_add, ← Nat.pow_add, ← hp]
        rw [heq, Fl.roundQuotient_exact _ _ (Nat.mul_pos hposj (Nat.two_pow_pos _))]
      · simp only [hk, ↓reduceIte]
        have hp : i + (-((i : Int) - j - T.fmt.sb)).toNat = T.fmt.sb + j := by omega
        have heq : 2 ^ i * 2 ^ (-((i : Int) - j - T.fmt.sb)).toNat = 2 ^ T.fmt.sb * 2 ^ j := by
          rw [← Nat.pow_add, ← Nat.pow_add, hp]
        rw [heq, Fl.roundQuotient_exact _ _ hposj]
    rw [hrounded]
    have hq0 : ¬ (2 ^ T.fmt.sb : Nat) = 0 := by have := Nat.two_pow_pos T.fmt.sb; omega
    have hq2 : ¬ (2 ^ T.fmt.sb : Nat) ≥ 2 ^ (T.fmt.sb + 1) := by
      exact Nat.not_le.mpr (Nat.pow_lt_pow_right (by decide) (by omega))
    unfold Fl.packRounded
    simp only [beq_iff_eq, hq0, Bool.false_eq_true, ↓reduceIte, hq2]
    have hp : (i : Int) - j - T.fmt.sb + T.fmt.bias + T.fmt.sb = (k - T.fmt.sb + 1 : Nat) := by omega
    rw [hp]
    have hpe : ¬ ((k - T.fmt.sb + 1 : Nat) : Int) ≥ T.fmt.emax := by omega
    simp only [hpe, hs, ↓reduceIte, Nat.lt_irrefl, decide_false, Bool.and_false,
      Int.toNat_natCast, Nat.sub_self, Nat.add_zero]
    rfl

theorem roundRat_dyadic_abs_key (T : FTy) (i j k : Nat) (s z : Bool)
    (hscale : i + (T.fmt.bias + T.fmt.sb - 1) = j + k)
    (hfinite : k + 1 < T.fmt.emax + T.fmt.sb) :
    let result := abs_IEEEFloat (Fl.roundRat (if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)) (2 ^ j) z : FV T)
    result.isfinite = true ∧ result.signbit = false ∧ result.key = ((2 ^ k : Nat) : Int) := by
  rw [roundRat_dyadic_pack T i j k s z hscale hfinite]
  let E := if k < T.fmt.sb then 0 else k - T.fmt.sb + 1
  let m := if k < T.fmt.sb then 2 ^ k else 0
  have hg := good_fty T
  have hbias := hg.bias_pos
  have hsb := hg.sb_pos
  have hemax := hg.emax_eq
  have hE : E < T.fmt.emax := by dsimp [E]; split <;> omega
  have hEbits : E < 2 ^ T.fmt.eb := by have he := hg.emax_succ; omega
  have hm : m < 2 ^ T.fmt.sb := by
    dsimp [m]
    split
    · exact Nat.pow_lt_pow_right (by decide) ‹k < T.fmt.sb›
    · exact Nat.two_pow_pos _
  have hp := Fl.pack_parts (f := T.fmt) s E m hEbits hm
  have hf : (Fl.pack s E m : FV T).isfinite = true := by
    simp only [Fl.isfinite, hp.2.1, bne_iff_ne]
    omega
  have hn := Fl.isnan_of_finite hf
  have habs : abs_IEEEFloat (Fl.pack s E m : FV T) = Fl.pack false E m := by
    unfold abs_IEEEFloat abs_float jlAbsFloat unaryFloat
    simp only [hn, Bool.and_false, Bool.false_eq_true, ↓reduceIte, finishFloat_eq]
    rw [hp.2.2.2]
    unfold Fl.pack
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_assoc]
  change (abs_IEEEFloat (Fl.pack s E m : FV T)).isfinite = true ∧ _
  rw [habs]
  have hp0 := Fl.pack_parts (f := T.fmt) false E m hEbits hm
  refine ⟨?_, hp0.1, ?_⟩
  · simp only [Fl.isfinite, hp0.2.1, bne_iff_ne]
    omega
  · rw [Fl.pack_key false E m hEbits hm]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [E, m]
    by_cases hk : k < T.fmt.sb
    · simp only [hk, ↓reduceIte, Nat.zero_sub, Nat.pow_zero, Nat.add_zero, Nat.mul_one]
    · simp only [hk, ↓reduceIte, show k - T.fmt.sb + 1 ≠ 0 by omega, Nat.zero_add,
        Nat.add_sub_cancel]
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega : T.fmt.sb ≤ k)]

theorem xor_one_difference (a : Nat) :
    ((a ^^^ 1 : Nat) : Int) - (a : Int) = if a % 2 = 0 then 1 else -1 := by
  have hd : (a ^^^ 1) / 2 = a / 2 := by rw [Nat.xor_div_two]; simp
  have hm : ((a ^^^ 1) % 2 = 1) ↔ a % 2 = 0 := by
    rw [Nat.xor_mod_two_eq_one]
    simp only [Nat.one_mod, Nat.reduceEqDiff, iff_true]
    have ha := Nat.mod_two_eq_zero_or_one a
    omega
  have h0 := Nat.mod_two_eq_zero_or_one a
  have h1 := Nat.mod_two_eq_zero_or_one (a ^^^ 1)
  have hv0 := Nat.mod_add_div a 2
  have hv1 := Nat.mod_add_div (a ^^^ 1) 2
  by_cases h : a % 2 = 0
  · simp only [h, ↓reduceIte]
    have hh := hm.mpr h
    omega
  · simp only [h, ↓reduceIte]
    have hh : (a ^^^ 1) % 2 = 0 := by omega
    omega

theorem epsilon_toggle_parts {T : FTy} (x : FV T) :
    let y := reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))
    y.signbit = x.signbit ∧ y.expField = x.expField ∧ y.frac = x.frac ^^^ 1 := by
  have hmeta : ∀ S : FTy, 0 < S.fmt.sb ∧ 0 < S.fmt.eb + S.fmt.sb ∧
      pattern (int.ofBool S.uintTy true) = 1 := by intro S; cases S <;> decide
  obtain ⟨hsb, hsignpos, hone⟩ := hmeta T
  let y := reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))
  have hy : y = (Fl.ofBits (x.toBits ^^^ 1) : FV T) := by
    dsimp only [y]
    rw [reinterpret_fty_bits, pattern_bxor, pattern_reinterpret_Unsigned, hone]
  have hsmall : x.toBits ^^^ 1 < 2 ^ T.fmt.width := Nat.xor_lt_two_pow x.bits.isLt (by
    have hp : 1 < 2 ^ T.fmt.width := by
      have hwidth : 0 < T.fmt.width := by
        have hh : ∀ S : FTy, 0 < S.fmt.width := by intro S; cases S <;> decide
        exact hh T
      exact Nat.one_lt_two_pow (by omega)
    exact hp)
  have hb : y.toBits = x.toBits ^^^ 1 := by rw [hy, Fl.toBits_ofBits, Nat.mod_eq_of_lt hsmall]
  have hsb1 : 1 < 2 ^ T.fmt.sb := Nat.one_lt_two_pow (by omega)
  have hs1 : 1 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.one_lt_two_pow (by omega)
  have hdivsb : y.toBits / 2 ^ T.fmt.sb = x.toBits / 2 ^ T.fmt.sb := by
    rw [hb, Nat.xor_div_two_pow, Nat.div_eq_of_lt hsb1, Nat.xor_zero]
  have hdivsg : y.toBits / 2 ^ (T.fmt.eb + T.fmt.sb) = x.toBits / 2 ^ (T.fmt.eb + T.fmt.sb) := by
    rw [hb, Nat.xor_div_two_pow, Nat.div_eq_of_lt hs1, Nat.xor_zero]
  refine ⟨?_, ?_, ?_⟩
  · change decide (y.toBits ≥ 2 ^ (T.fmt.eb + T.fmt.sb)) = decide (x.toBits ≥ 2 ^ (T.fmt.eb + T.fmt.sb))
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have hp := Nat.two_pow_pos (T.fmt.eb + T.fmt.sb)
    have he (n : Nat) : (2 ^ (T.fmt.eb + T.fmt.sb) ≤ n) ↔ 1 ≤ n / 2 ^ (T.fmt.eb + T.fmt.sb) := by
      rw [Nat.le_div_iff_mul_le hp, Nat.one_mul]
    change 2 ^ (T.fmt.eb + T.fmt.sb) ≤ y.toBits ↔ 2 ^ (T.fmt.eb + T.fmt.sb) ≤ x.toBits
    rw [he, he, hdivsg]
  · change y.toBits / 2 ^ T.fmt.sb % 2 ^ T.fmt.eb = x.toBits / 2 ^ T.fmt.sb % 2 ^ T.fmt.eb
    rw [hdivsb]
  · change y.toBits % 2 ^ T.fmt.sb = x.toBits % 2 ^ T.fmt.sb ^^^ 1
    rw [hb, Nat.xor_mod_two_pow, Nat.mod_eq_of_lt hsb1]

theorem neg_finite_rat {T : FTy} (x : FV T) (hf : x.isfinite = true) :
    (Fl.neg x).isfinite = true ∧ (Fl.neg x).toRat = (-x.toRat.1, x.toRat.2) := by
  obtain ⟨hm, hs⟩ := fl_neg_parts x
  have he : (Fl.neg x).expField = x.expField := by rw [Fl.expField_eq, hm, ← Fl.expField_eq]
  have hfr : (Fl.neg x).frac = x.frac := by rw [Fl.frac_eq, hm, ← Fl.frac_eq]
  have hfn : (Fl.neg x).isfinite = true := by simpa only [Fl.isfinite, he] using hf
  refine ⟨hfn, ?_⟩
  unfold Fl.toRat
  simp only [hf, hfn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, he, hfr, hs]
  cases hx : x.signbit <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals split <;> split <;> simp [Int.neg_mul]

theorem sub_finite_rational {T : FTy} (x y : FV T) (hx : x.isfinite = true) (hy : y.isfinite = true) :
    sub_IEEEFloat x y = Fl.roundRat
      (x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int))
      (x.toRat.2 * y.toRat.2) (x.signbit && !y.signbit) := by
  have hn := neg_finite_rat y hy
  have hsg := (fl_neg_parts y).2
  unfold sub_IEEEFloat sub_float jlSubFloat floatSub floatAdd
  simp only [finishFloat_eq, Fl.isnan_of_finite hx, Fl.isnan_of_finite hy,
    Fl.isnan_of_finite hn.1, Fl.isinf_of_finite hx, Fl.isinf_of_finite hy,
    Fl.isinf_of_finite hn.1, Bool.false_eq_true, ↓reduceIte, hn.2, hsg]
  congr 1
  simp only [Int.neg_mul, Int.sub_eq_add_neg]

theorem integer_dyadic_ratio (N : Int) (g j k : Nat) (s : Bool)
    (h : N * ((2 ^ g : Nat) : Int) = (if s then -((2 ^ k : Nat) : Int) else ((2 ^ k : Nat) : Int)) * ((2 ^ j : Nat) : Int)) :
    ∃ i : Nat, N = (if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)) ∧ i + g = j + k := by
  have ha : N.natAbs * 2 ^ g = 2 ^ (j + k) := by
    have hh := congrArg Int.natAbs h
    cases s <;> simpa only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Int.natAbs_mul,
      Int.natAbs_neg, Int.natAbs_natCast, ← Nat.pow_add, Nat.add_comm k j] using hh
  have hN : 0 < N.natAbs := by
    have hp := Nat.two_pow_pos (j + k)
    apply Classical.byContradiction
    intro hz
    have he : N.natAbs = 0 := by omega
    rw [he, Nat.zero_mul] at ha
    omega
  have hg : g ≤ j + k := by
    apply Classical.byContradiction
    intro hh
    have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) (show j + k < g by omega)
    have hm : 2 ^ g ≤ N.natAbs * 2 ^ g := by simpa using Nat.mul_le_mul_right (2 ^ g) (show 1 ≤ N.natAbs by omega)
    omega
  let i := j + k - g
  have hiscale : i + g = j + k := Nat.sub_add_cancel hg
  refine ⟨i, ?_, hiscale⟩
  apply Int.eq_of_mul_eq_mul_right (show ((2 ^ g : Nat) : Int) ≠ 0 by
    have hp : 0 < ((2 ^ g : Nat) : Int) := Int.natCast_pos.mpr (Nat.two_pow_pos g)
    omega)
  rw [h]
  cases s <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, Int.neg_mul, ← Int.natCast_mul]
  all_goals rw [← Nat.pow_add, ← Nat.pow_add, hiscale, Nat.add_comm k j]

theorem sub_dyadic_key {T : FTy} (x y : FV T) (hx : x.isfinite = true) (hy : y.isfinite = true)
    (k : Nat) (s : Bool)
    (hk : x.key - y.key = if s then -((2 ^ k : Nat) : Int) else ((2 ^ k : Nat) : Int))
    (hfin : k + 1 < T.fmt.emax + T.fmt.sb) :
    let r := abs_IEEEFloat (sub_IEEEFloat x y)
    r.isfinite = true ∧ r.signbit = false ∧ r.key = ((2 ^ k : Nat) : Int) := by
  obtain ⟨mx, ix, jx, hxr, -, -, -⟩ := Fl.toRat_cases (good_fty T) x hx
  obtain ⟨my, iy, jy, hyr, -, -, -⟩ := Fl.toRat_cases (good_fty T) y hy
  have hdx : x.toRat.2 = 2 ^ jx := congrArg Prod.snd hxr
  have hdy : y.toRat.2 = 2 ^ jy := congrArg Prod.snd hyr
  have hkeyx := (Fl.toRat_key (good_fty T) x hx).2
  have hkeyy := (Fl.toRat_key (good_fty T) y hy).2
  let N := x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int)
  have hscale : N * (T.fmt.den : Int) = (x.key - y.key) * ((x.toRat.2 * y.toRat.2 : Nat) : Int) := by
    calc
      N * (T.fmt.den : Int) = (x.toRat.1 * (T.fmt.den : Int)) * (y.toRat.2 : Int) -
          (y.toRat.1 * (T.fmt.den : Int)) * (x.toRat.2 : Int) := by
        dsimp only [N]
        simp only [Int.sub_mul, Int.mul_right_comm]
      _ = (x.key * (x.toRat.2 : Int)) * (y.toRat.2 : Int) -
          (y.key * (y.toRat.2 : Int)) * (x.toRat.2 : Int) := by rw [hkeyx, hkeyy]
      _ = (x.key - y.key) * ((x.toRat.2 * y.toRat.2 : Nat) : Int) := by
        simp only [Int.sub_mul, Int.natCast_mul, Int.mul_assoc, Int.mul_comm (y.toRat.2 : Int) (x.toRat.2 : Int)]
  have hdprod : x.toRat.2 * y.toRat.2 = 2 ^ (jx + jy) := by rw [hdx, hdy, Nat.pow_add]
  rw [Fmt.den, hk, hdprod] at hscale
  obtain ⟨i, hi, hsum⟩ := integer_dyadic_ratio N (T.fmt.bias + T.fmt.sb - 1) (jx + jy) k s hscale
  have hr : sub_IEEEFloat x y = Fl.roundRat
      (if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)) (2 ^ (jx + jy)) (x.signbit && !y.signbit) := by
    rw [sub_finite_rational x y hx hy, hdprod]
    change Fl.roundRat N _ _ = _
    rw [hi]
  rw [hr]
  exact roundRat_dyadic_abs_key T i (jx + jy) k s (x.signbit && !y.signbit) hsum hfin

theorem key_fields {T : FTy} (x : FV T) :
    x.key = if x.signbit then -(((x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb) * 2 ^ (x.expField - 1) : Nat) : Int)
      else (((x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb) * 2 ^ (x.expField - 1) : Nat) : Int) := by
  unfold Fl.key magKey
  rw [← Fl.expField_eq, ← Fl.frac_eq]

theorem signed_difference (a b p q : Int) (s e : Bool) (h : a - b = if e then -1 else 1) :
    (if s then -((a+p)*q) else (a+p)*q) - (if s then -((b+p)*q) else (b+p)*q) = if s ^^ e then -q else q := by
  have hd : (a+p)*q - (b+p)*q = (a-b)*q := by rw [← Int.sub_mul]; congr 1; omega
  cases s <;> cases e <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor, Bool.true_xor,
    Bool.not_false, Bool.not_true] at h ⊢
  all_goals rw [h] at hd
  all_goals simp only [Int.neg_one_mul, Int.one_mul] at hd
  all_goals omega

theorem epsilon_toggle_key {T : FTy} (x : FV T) :
    let y := reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))
    x.key - y.key = if x.signbit ^^ decide (x.frac % 2 = 0) then -((2 ^ (x.expField - 1) : Nat) : Int)
      else ((2 ^ (x.expField - 1) : Nat) : Int) := by
  let y := reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))
  obtain ⟨hsgn, hexp, hfrac⟩ := epsilon_toggle_parts x
  have hdiff : (x.frac : Int) - (y.frac : Int) = if x.frac % 2 = 0 then -1 else 1 := by
    change (x.frac : Int) - ((reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))).frac : Int) = _
    rw [hfrac]
    have hh := xor_one_difference x.frac
    by_cases he : x.frac % 2 = 0 <;> simp only [he, ↓reduceIte] at hh ⊢ <;> omega
  change x.key - y.key = _
  rw [key_fields x, key_fields y]
  change y.signbit = x.signbit at hsgn
  change y.expField = x.expField at hexp
  rw [hsgn, hexp]
  simp only [Int.natCast_mul, Int.natCast_add]
  exact signed_difference (x.frac : Int) (y.frac : Int) (if x.expField = 0 then 0 else 2 ^ T.fmt.sb : Nat)
    ((2 ^ (x.expField - 1) : Nat) : Int) x.signbit (decide (x.frac % 2 = 0)) (by simpa using hdiff)

def FiniteEpsilonBitSpacing : Prop := ∀ (T : FTy) (x : FV T), x.isfinite = true →
  (eps_IEEEFloat x).isfinite = true ∧ (eps_IEEEFloat x).signbit = false ∧
    (eps_IEEEFloat x).key = ((2 ^ (x.expField - 1) : Nat) : Int)

theorem finiteEpsilonBitSpacing_proven : FiniteEpsilonBitSpacing := by
  intro T x hx
  let y := reinterpret_Float_Int T (int.bxor (reinterpret_Unsigned x) (int.ofBool T.uintTy true))
  obtain ⟨-, he, -⟩ := epsilon_toggle_parts x
  have hy : y.isfinite = true := by
    change y.expField = x.expField at he
    simpa only [Fl.isfinite, he] using hx
  have hbound : x.expField < T.fmt.emax := by
    have hmag := (isfinite_iff_mag x).mp hx
    rw [Fl.expField_eq]
    exact Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hmag)
  have hsb := (good_fty T).sb_pos
  have hfin : x.expField - 1 + 1 < T.fmt.emax + T.fmt.sb := by omega
  exact sub_dyadic_key x y hx hy (x.expField - 1) (x.signbit ^^ decide (x.frac % 2 = 0))
    (epsilon_toggle_key x) hfin

end EpsilonProofs

namespace EpsilonNeighborProofs
open TruncProofs NextProofs EpsilonProofs

theorem sub_dyadic_sign {T : FTy} (x y : FV T) (hx : x.isfinite = true) (hy : y.isfinite = true)
    (k : Nat) (s : Bool)
    (hk : x.key - y.key = if s then -((2 ^ k : Nat) : Int) else ((2 ^ k : Nat) : Int))
    (hfin : k + 1 < T.fmt.emax + T.fmt.sb) :
    (sub_IEEEFloat x y).signbit = s := by
  obtain ⟨mx, ix, jx, hxr, -, -, -⟩ := Fl.toRat_cases (good_fty T) x hx
  obtain ⟨my, iy, jy, hyr, -, -, -⟩ := Fl.toRat_cases (good_fty T) y hy
  have hdx : x.toRat.2 = 2 ^ jx := congrArg Prod.snd hxr
  have hdy : y.toRat.2 = 2 ^ jy := congrArg Prod.snd hyr
  have hkeyx := (Fl.toRat_key (good_fty T) x hx).2
  have hkeyy := (Fl.toRat_key (good_fty T) y hy).2
  let N := x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int)
  have hscale : N * (T.fmt.den : Int) = (x.key - y.key) * ((x.toRat.2 * y.toRat.2 : Nat) : Int) := by
    calc
      N * (T.fmt.den : Int) = (x.toRat.1 * (T.fmt.den : Int)) * (y.toRat.2 : Int) -
          (y.toRat.1 * (T.fmt.den : Int)) * (x.toRat.2 : Int) := by
        dsimp only [N]
        simp only [Int.sub_mul, Int.mul_right_comm]
      _ = (x.key * (x.toRat.2 : Int)) * (y.toRat.2 : Int) -
          (y.key * (y.toRat.2 : Int)) * (x.toRat.2 : Int) := by rw [hkeyx, hkeyy]
      _ = (x.key - y.key) * ((x.toRat.2 * y.toRat.2 : Nat) : Int) := by
        simp only [Int.sub_mul, Int.natCast_mul, Int.mul_assoc, Int.mul_comm (y.toRat.2 : Int) (x.toRat.2 : Int)]
  have hdprod : x.toRat.2 * y.toRat.2 = 2 ^ (jx + jy) := by rw [hdx, hdy, Nat.pow_add]
  rw [Fmt.den, hk, hdprod] at hscale
  obtain ⟨i, hi, hsum⟩ := integer_dyadic_ratio N (T.fmt.bias + T.fmt.sb - 1) (jx + jy) k s hscale
  have hr : sub_IEEEFloat x y = Fl.roundRat
      (if s then -((2 ^ i : Nat) : Int) else ((2 ^ i : Nat) : Int)) (2 ^ (jx + jy)) (x.signbit && !y.signbit) := by
    rw [sub_finite_rational x y hx hy, hdprod]
    change Fl.roundRat N _ _ = _
    rw [hi]
  rw [hr]
  rw [roundRat_dyadic_pack T i (jx + jy) k s (x.signbit && !y.signbit) hsum hfin]
  let E := if k < T.fmt.sb then 0 else k - T.fmt.sb + 1
  let m := if k < T.fmt.sb then 2 ^ k else 0
  have hE : E < 2 ^ T.fmt.eb := by
    have he := (good_fty T).emax_succ
    dsimp only [E]
    split <;> omega
  have hm : m < 2 ^ T.fmt.sb := by
    dsimp only [m]
    split
    · exact Nat.pow_lt_pow_right (by decide) ‹k < T.fmt.sb›
    · exact Nat.two_pow_pos _
  exact (Fl.pack_parts (f := T.fmt) s E m hE hm).1

theorem magKey_next (f : Fmt) (M : Nat) :
    ((magKey f (M + 1) : Nat) : Int) - ((magKey f M : Nat) : Int) = ((2 ^ (M / 2 ^ f.sb - 1) : Nat) : Int) := by
  have hp := Nat.two_pow_pos f.sb
  have hr := Nat.mod_lt M hp
  have hs : M + 1 = (M % 2 ^ f.sb + 1) + 2 ^ f.sb * (M / 2 ^ f.sb) := by
    have hh := Nat.mod_add_div M (2 ^ f.sb)
    omega
  have hd : (M + 1) / 2 ^ f.sb = (M % 2 ^ f.sb + 1) / 2 ^ f.sb + M / 2 ^ f.sb := by
    rw [hs, Nat.add_mul_div_left _ _ hp]
  have hm : (M + 1) % 2 ^ f.sb = (M % 2 ^ f.sb + 1) % 2 ^ f.sb := by
    rw [hs, Nat.add_mul_mod_self_left]
  unfold magKey
  rw [hd, hm]
  generalize M / 2 ^ f.sb = E
  generalize M % 2 ^ f.sb = r at hr ⊢
  generalize 2 ^ f.sb = P at hp hr ⊢
  by_cases hsmall : r + 1 < P
  · rw [Nat.mod_eq_of_lt hsmall, Nat.div_eq_of_lt hsmall, Nat.zero_add]
    simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    omega
  · have he : r + 1 = P := by omega
    rw [he, Nat.mod_self, Nat.div_self (by omega), Nat.zero_add]
    cases E with
    | zero => simp; omega
    | succ e =>
      rw [show 1 + Nat.succ e - 1 = e + 1 by omega]
      simp only [Nat.succ_eq_add_one, show 1 + (e + 1) ≠ 0 by omega,
        show e + 1 ≠ 0 by omega, ↓reduceIte, Nat.zero_add, Nat.add_sub_cancel, Nat.pow_succ]
      rw [← he]
      simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one,
        Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, ← Int.mul_assoc]
      omega

theorem encode_finite (T : FTy) (s : Bool) (m : Nat) (hm : m < infMag T) :
    (encode T s m).isfinite = true := by
  rw [isfinite_iff_mag, mag_encode T s (Nat.lt_trans hm (infMag_lt_signMask T))]
  exact hm

theorem encode_key (T : FTy) (s : Bool) (m : Nat) (hm : m < signMask T) :
    (encode T s m).key = if s then -((magKey T.fmt m : Nat) : Int) else ((magKey T.fmt m : Nat) : Int) := by
  unfold Fl.key
  rw [sign_encode T s hm, mag_encode T s hm]

theorem abs_nonnegative {T : FTy} (x : FV T) (hn : x.isnan = false) (hs : x.signbit = false) :
    abs_IEEEFloat x = x := by
  have hb := (Fl.bits_split x).1
  simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hb
  unfold abs_IEEEFloat abs_float jlAbsFloat unaryFloat
  simp only [hn, Bool.and_false, Bool.false_eq_true, ↓reduceIte, finishFloat_eq]
  rw [← hb, Fl.ofBits_toBits]

theorem sub_positive_dyadic {T : FTy} (x y : FV T) (hx : x.isfinite = true) (hy : y.isfinite = true)
    (k : Nat) (hk : x.key - y.key = ((2 ^ k : Nat) : Int))
    (hfin : k + 1 < T.fmt.emax + T.fmt.sb) :
    (sub_IEEEFloat x y).isfinite = true ∧ (sub_IEEEFloat x y).signbit = false ∧
      (sub_IEEEFloat x y).key = ((2 ^ k : Nat) : Int) := by
  have ha := sub_dyadic_key x y hx hy k false hk hfin
  have hs := sub_dyadic_sign x y hx hy k false hk hfin
  have hn : (sub_IEEEFloat x y).isnan = false := by
    cases hz : (sub_IEEEFloat x y).isnan
    · rfl
    · have hh := abs_preserves_nan (sub_IEEEFloat x y) hz
      have hhf := Fl.isnan_of_finite ha.1
      rw [hhf] at hh
      contradiction
  rw [abs_nonnegative _ hn hs] at ha
  exact ha

def encodedGap (T : FTy) (s : Bool) (m : Nat) : FV T :=
  if s then sub_IEEEFloat (encode T s m) (encode T s (m + 1))
  else sub_IEEEFloat (encode T s (m + 1)) (encode T s m)

theorem encodedGap_finite (T : FTy) (s : Bool) (m : Nat) (hm : m + 1 < infMag T) :
    (encodedGap T s m).isfinite = true ∧ (encodedGap T s m).signbit = false ∧
      (encodedGap T s m).key = ((2 ^ (m / 2 ^ T.fmt.sb - 1) : Nat) : Int) := by
  have hm0 : m < infMag T := by omega
  have hs1 := Nat.lt_trans hm (infMag_lt_signMask T)
  have hs0 := Nat.lt_trans hm0 (infMag_lt_signMask T)
  have hf0 := encode_finite T s m hm0
  have hf1 := encode_finite T s (m + 1) hm
  have hk := magKey_next T.fmt m
  have hExp : m / 2 ^ T.fmt.sb < T.fmt.emax := by
    exact Nat.div_lt_of_lt_mul (by simpa only [infMag, Nat.mul_comm] using hm0)
  have hsb := (good_fty T).sb_pos
  have hbound (E EM SB : Nat) (hE : E < EM) (hSB : 0 < SB) : E - 1 + 1 < EM + SB := by omega
  have hfin := hbound _ _ _ hExp hsb
  cases s
  · apply sub_positive_dyadic _ _ hf1 hf0 _ ?_ hfin
    simpa only [encode_key T false _ hs1, encode_key T false _ hs0, Bool.false_eq_true, ↓reduceIte] using hk
  · apply sub_positive_dyadic _ _ hf0 hf1 _ ?_ hfin
    rw [encode_key T true _ hs0, encode_key T true _ hs1]
    simp only [↓reduceIte]
    omega

theorem encode_infinity (T : FTy) (s : Bool) : encode T s (infMag T) = (Fl.inf s : FV T) := by
  rfl

theorem encodedGap_infinite (T : FTy) (s : Bool) :
    encodedGap T s (infMag T - 1) = (Fl.inf false : FV T) := by
  have hI : 1 < infMag T := by
    have hall : ∀ S : FTy, 1 < infMag S := by intro S; cases S <;> decide
    exact hall T
  have hstep : infMag T - 1 + 1 = infMag T := by omega
  have hf := encode_finite T s (infMag T - 1) (by omega)
  have hnf := Fl.isnan_of_finite hf
  have hif := Fl.isinf_of_finite hf
  have hnegf := (neg_finite_rat (encode T s (infMag T - 1)) hf).1
  have hnnf := Fl.isnan_of_finite hnegf
  have hinf := Fl.isinf_of_finite hnegf
  have hmeta : ∀ S : FTy,
      (Fl.inf false : FV S).isnan = false ∧ (Fl.inf false : FV S).isinf = true ∧
      (Fl.inf false : FV S).signbit = false ∧ (Fl.inf true : FV S).isnan = false ∧
      Fl.neg (Fl.inf true : FV S) = Fl.inf false := by
    intro S; cases S <;> decide
  obtain ⟨hnp, hip, hsp, hnn, hneg⟩ := hmeta T
  unfold encodedGap
  rw [hstep, encode_infinity]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_IEEEFloat, sub_float, jlSubFloat,
    finishFloat_eq, floatSub, floatAdd, hnf, hnnf, hnp, hnn, Bool.false_eq_true, ↓reduceIte,
    hneg, hif, hinf, hip, hsp, Bool.true_and, Bool.false_and]

theorem finite_neighbors {T : FTy} (x : FV T) (hx : x.isfinite = true) (hm : 0 < x.magnitude) :
    nextfloat x = (if x.signbit then encode T true (x.magnitude - 1) else encode T false (x.magnitude + 1)) ∧
    prevfloat x = (if x.signbit then encode T true (x.magnitude + 1) else encode T false (x.magnitude - 1)) := by
  have hn := Fl.isnan_of_finite hx
  have hb : x.magnitude + 1 ≤ infMag T := by have hh := (isfinite_iff_mag x).mp hx; exact hh
  have hnot : ¬x.magnitude < 1 := by omega
  rw [nextfloat_eq, prevfloat_eq]
  cases hs : x.signbit <;> simp [nextSpec, walk, hn, hs, hnot, Nat.min_eq_left hb]

theorem zero_neighbors {T : FTy} (x : FV T) (hx : x.isfinite = true) (hm : x.magnitude = 0) :
    nextfloat x = encode T false 1 ∧ prevfloat x = encode T true 1 := by
  have hn := Fl.isnan_of_finite hx
  have hI : 1 ≤ infMag T := by
    have hall : ∀ S : FTy, 1 ≤ infMag S := by intro S; cases S <;> decide
    exact hall T
  rw [nextfloat_eq, prevfloat_eq]
  cases hs : x.signbit <;> simp [nextSpec, walk, hn, hs, hm, Nat.min_eq_left hI]

theorem finite_key_lt_infinity {T : FTy} (x : FV T) (hf : x.isfinite = true) (hs : x.signbit = false) :
    x.key < (Fl.inf false : FV T).key := by
  have hm := (isfinite_iff_mag x).mp hf
  have hi : (Fl.inf false : FV T).signbit = false := by
    have hall : ∀ S : FTy, (Fl.inf false : FV S).signbit = false := by intro S; cases S <;> decide
    exact hall T
  have hmag : (Fl.inf false : FV T).magnitude = infMag T := by
    rw [← encode_infinity T false, mag_encode T false (infMag_lt_signMask T)]
  unfold Fl.key
  rw [hs, hi, hmag]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact Int.ofNat_lt.mpr (magKey_strictMono T.fmt hm)

theorem neighbor_gap_pair {T : FTy} (x : FV T) (hx : x.isfinite = true) (hm : 0 < x.magnitude) :
    (sub_IEEEFloat x (prevfloat x), sub_IEEEFloat (nextfloat x) x) =
      if x.signbit then (encodedGap T true x.magnitude, encodedGap T true (x.magnitude - 1))
      else (encodedGap T false (x.magnitude - 1), encodedGap T false x.magnitude) := by
  obtain ⟨hn, hp⟩ := finite_neighbors x hx hm
  rw [hn, hp]
  cases hs : x.signbit <;>
    simp only [hs, Bool.false_eq_true, ↓reduceIte, encodedGap, Nat.sub_add_cancel (show 1 ≤ x.magnitude by omega)]
  all_goals have he := encode_input x
  all_goals rw [hs] at he
  all_goals rw [he]

theorem zero_gap_values {T : FTy} (x : FV T) (hx : x.isfinite = true) (hm : x.magnitude = 0) :
    ((sub_IEEEFloat x (prevfloat x)).isfinite = true ∧ (sub_IEEEFloat x (prevfloat x)).signbit = false ∧
      (sub_IEEEFloat x (prevfloat x)).key = 1) ∧
    ((sub_IEEEFloat (nextfloat x) x).isfinite = true ∧ (sub_IEEEFloat (nextfloat x) x).signbit = false ∧
      (sub_IEEEFloat (nextfloat x) x).key = 1) := by
  obtain ⟨hn, hp⟩ := zero_neighbors x hx hm
  have hI : 1 < infMag T := by
    have hall : ∀ S : FTy, 1 < infMag S := by intro S; cases S <;> decide
    exact hall T
  have hs : 1 < signMask T := Nat.lt_trans hI (infMag_lt_signMask T)
  have hleft := encode_finite T true 1 hI
  have hright := encode_finite T false 1 hI
  have hunit : ((magKey T.fmt 1 : Nat) : Int) = 1 := by
    simpa only [Nat.zero_add, Nat.zero_div, Nat.zero_sub, Nat.pow_zero, magKey_zero,
      Int.natCast_zero, Int.natCast_one, Int.sub_zero] using magKey_next T.fmt 0
  have hxkey : x.key = 0 := by
    unfold Fl.key
    rw [hm, magKey_zero]
    cases x.signbit <;> simp
  have hlkey : (encode T true 1).key = -1 := by rw [encode_key T true 1 hs]; simp [hunit]
  have hrkey : (encode T false 1).key = 1 := by rw [encode_key T false 1 hs]; simp [hunit]
  have hfin : 0 + 1 < T.fmt.emax + T.fmt.sb := by
    have hall : ∀ S : FTy, 0 + 1 < S.fmt.emax + S.fmt.sb := by intro S; cases S <;> decide
    exact hall T
  rw [hp, hn]
  constructor
  · exact sub_positive_dyadic x _ hx hleft 0 (by rw [hxkey, hlkey]; rfl) hfin
  · exact sub_positive_dyadic _ x hright hx 0 (by rw [hrkey, hxkey]; rfl) hfin

theorem eq_of_key {T : FTy} (a b : FV T) (ha : a.isnan = false) (hb : b.isnan = false)
    (hk : a.key = b.key) : eq_IEEEFloat a b = true := by
  rw [eq_IEEEFloat_eq, Fl.eq_key ha hb]
  exact decide_eq_true_eq.mpr hk

theorem selected_gap_eq {T : FTy} (z a b : FV T) (hz : z.isnan = false) (ha : a.isnan = false)
    (hb : b.isnan = false) (minimum : Bool)
    (hk : z.key = if minimum then (if a.key < b.key then a.key else b.key)
      else (if a.key < b.key then b.key else a.key)) :
    eq_IEEEFloat z (if minimum then (if lt_IEEEFloat a b then a else b)
      else (if lt_IEEEFloat a b then b else a)) = true := by
  rw [lt_IEEEFloat_eq, Fl.lt_key ha hb]
  cases minimum <;> by_cases hlt : a.key < b.key <;>
    simp only [Bool.false_eq_true, ↓reduceIte, hlt, decide_true, decide_false] at hk ⊢
  · exact eq_of_key z b hz hb hk
  · exact eq_of_key z a hz ha hk
  · exact eq_of_key z a hz ha hk
  · exact eq_of_key z b hz hb hk

def FiniteEpsilonNeighborMaxMin : Prop := ∀ (T : FTy) (x : FV T), x.isfinite = true →
  let left := sub_IEEEFloat x (prevfloat x)
  let right := sub_IEEEFloat (nextfloat x) x
  eq_IEEEFloat (eps_IEEEFloat x)
    (if x.magnitude + 1 = infMag T then
      (if lt_IEEEFloat left right then left else right)
    else (if lt_IEEEFloat left right then right else left)) = true

theorem finiteEpsilonNeighborMaxMin_proven : FiniteEpsilonNeighborMaxMin := by
  intro T x hx
  have heps := finiteEpsilonBitSpacing_proven T x hx
  have hepsN := Fl.isnan_of_finite heps.1
  have hI : 1 < infMag T := by
    have hall : ∀ S : FTy, 1 < infMag S := by intro S; cases S <;> decide
    exact hall T
  by_cases hz : x.magnitude = 0
  · obtain ⟨hl, hr⟩ := zero_gap_values x hx hz
    have he : x.expField = 0 := by rw [Fl.expField_eq, hz]; simp
    have hepkey : (eps_IEEEFloat x).key = 1 := by simpa only [he, Nat.zero_sub, Nat.pow_zero, Int.natCast_one] using heps.2.2
    have hend : ¬x.magnitude + 1 = infMag T := by omega
    simp only [hend, ↓reduceIte]
    apply selected_gap_eq _ _ _ hepsN (Fl.isnan_of_finite hl.1) (Fl.isnan_of_finite hr.1) false
    simp only [Bool.false_eq_true, ↓reduceIte, hl.2.2, hr.2.2, Int.lt_irrefl]
    exact hepkey
  · have hm : 0 < x.magnitude := by omega
    have hinner : (x.magnitude - 1) + 1 < infMag T := by
      have hh := (isfinite_iff_mag x).mp hx
      change x.magnitude < infMag T at hh
      omega
    have hin := encodedGap_finite T x.signbit (x.magnitude - 1) hinner
    have hpair := neighbor_gap_pair x hx hm
    have hleft := congrArg Prod.fst hpair
    have hright := congrArg Prod.snd hpair
    have hE : x.expField = x.magnitude / 2 ^ T.fmt.sb := Fl.expField_eq x
    have hporder : (2 ^ ((x.magnitude - 1) / 2 ^ T.fmt.sb - 1) : Nat) ≤ 2 ^ (x.expField - 1) := by
      rw [hE]
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.sub_le _ _)) 1
    by_cases hend : x.magnitude + 1 = infMag T
    · have hmend : x.magnitude = infMag T - 1 := by omega
      have hout : encodedGap T x.signbit x.magnitude = (Fl.inf false : FV T) := by rw [hmend]; exact encodedGap_infinite T x.signbit
      have hEnd : (x.magnitude - 1) / 2 ^ T.fmt.sb = x.expField := by
        rw [hE, hmend]
        have hall : ∀ S : FTy, (infMag S - 2) / 2 ^ S.fmt.sb = (infMag S - 1) / 2 ^ S.fmt.sb := by
          intro S; cases S <;> decide
        simpa only [Nat.sub_sub] using hall T
      have hik : (encodedGap T x.signbit (x.magnitude - 1)).key = (eps_IEEEFloat x).key := by
        rw [hin.2.2, hEnd, heps.2.2]
      have hInfN : (Fl.inf false : FV T).isnan = false := by
        have hall : ∀ S : FTy, (Fl.inf false : FV S).isnan = false := by intro S; cases S <;> decide
        exact hall T
      have hiLT := finite_key_lt_infinity _ hin.1 hin.2.1
      simp only [hend, ↓reduceIte]
      cases hs : x.signbit <;>
        simp only [hs, Bool.false_eq_true, ↓reduceIte, Prod.fst, Prod.snd] at hleft hright hin hik hout hiLT
      · rw [hleft, hright, hout]
        apply selected_gap_eq _ _ _ hepsN (Fl.isnan_of_finite hin.1) hInfN true
        simp only [↓reduceIte, hiLT]
        exact hik.symm
      · rw [hleft, hright, hout]
        apply selected_gap_eq _ _ _ hepsN hInfN (Fl.isnan_of_finite hin.1) true
        have hnot : ¬(Fl.inf false : FV T).key < (encodedGap T true (x.magnitude - 1)).key := by omega
        simp only [↓reduceIte, hnot]
        exact hik.symm
    · have houter : x.magnitude + 1 < infMag T := by
        have hh := (isfinite_iff_mag x).mp hx
        change x.magnitude < infMag T at hh
        omega
      have hout := encodedGap_finite T x.signbit x.magnitude houter
      have hok : (encodedGap T x.signbit x.magnitude).key = (eps_IEEEFloat x).key := by rw [hout.2.2, ← hE, heps.2.2]
      have hle : (encodedGap T x.signbit (x.magnitude - 1)).key ≤ (encodedGap T x.signbit x.magnitude).key := by
        rw [hin.2.2, hout.2.2, ← hE]
        exact Int.ofNat_le.mpr hporder
      simp only [hend, ↓reduceIte]
      cases hs : x.signbit <;>
        simp only [hs, Bool.false_eq_true, ↓reduceIte, Prod.fst, Prod.snd] at hleft hright hin hout hok hle
      · rw [hleft, hright]
        apply selected_gap_eq _ _ _ hepsN (Fl.isnan_of_finite hin.1) (Fl.isnan_of_finite hout.1) false
        simp only [Bool.false_eq_true, ↓reduceIte]
        split <;> omega
      · rw [hleft, hright]
        apply selected_gap_eq _ _ _ hepsN (Fl.isnan_of_finite hout.1) (Fl.isnan_of_finite hin.1) false
        simp only [Bool.false_eq_true, ↓reduceIte]
        split <;> omega

theorem extreme_neighbors (T : FTy) :
    nextfloat (Fl.inf true : FV T) = encode T true (infMag T - 1) ∧
    prevfloat (Fl.inf false : FV T) = encode T false (infMag T - 1) := by
  have hmeta : ∀ S : FTy,
      (Fl.inf true : FV S).isnan = false ∧ (Fl.inf true : FV S).signbit = true ∧
      (Fl.inf true : FV S).magnitude = infMag S ∧ (Fl.inf false : FV S).isnan = false ∧
      (Fl.inf false : FV S).signbit = false ∧ (Fl.inf false : FV S).magnitude = infMag S ∧
      1 < infMag S := by intro S; cases S <;> decide
  obtain ⟨hnt, hst, hmt, hnf, hsf, hmf, hi⟩ := hmeta T
  rw [nextfloat_eq, prevfloat_eq]
  simp [nextSpec, walk, hnt, hnf, hst, hsf, hmt, hmf, show ¬infMag T < 1 by omega]

theorem endpoint_characterization {T : FTy} (x : FV T) :
    (x = nextfloat (Fl.inf true : FV T) ∨ x = prevfloat (Fl.inf false : FV T)) ↔
      x.magnitude + 1 = infMag T := by
  have hI : 1 < infMag T := by
    have hall : ∀ S : FTy, 1 < infMag S := by intro S; cases S <;> decide
    exact hall T
  have hs : infMag T - 1 < signMask T := Nat.lt_trans (show infMag T - 1 < infMag T by omega) (infMag_lt_signMask T)
  rw [(extreme_neighbors T).1, (extreme_neighbors T).2]
  constructor
  · intro he
    rcases he with he | he
    · rw [he, mag_encode T true hs]
      omega
    · rw [he, mag_encode T false hs]
      omega
  · intro hend
    have hm : x.magnitude = infMag T - 1 := by omega
    have he := encode_input x
    rw [hm] at he
    cases hsx : x.signbit
    · rw [hsx] at he
      exact Or.inr he.symm
    · rw [hsx] at he
      exact Or.inl he.symm

def DocumentedEpsilonSpacing : Prop := ∀ (T : FTy) (x : FV T), x.isfinite = true →
  let left := sub_IEEEFloat x (prevfloat x)
  let right := sub_IEEEFloat (nextfloat x) x
  eq_IEEEFloat (eps_IEEEFloat x)
    (if x = nextfloat (Fl.inf true : FV T) ∨ x = prevfloat (Fl.inf false : FV T) then
      (if lt_IEEEFloat left right then left else right)
    else (if lt_IEEEFloat left right then right else left)) = true

theorem documentedEpsilonSpacing_proven : DocumentedEpsilonSpacing := by
  intro T x hx
  simpa only [endpoint_characterization x] using finiteEpsilonNeighborMaxMin_proven T x hx

end EpsilonNeighborProofs

structure AbstractFloatModOps (F : Type) where
  eq : F → F → Bool
  sub : F → F → F
  rem : F → F → F
  copysign : F → F → F
  add : F → F → F
  eqZero : F → Bool
  gtZero : F → Bool
  signbit : F → Bool
  magnitudeLt : F → F → Prop

def GenericModuloSign : Prop := ∀ (F : Type) (op : AbstractFloatModOps F),
  let nan := isnan_AbstractFloat op.eq
  let finite := isfinite_AbstractFloat op.sub nan
  let infinite := isinf_Real nan finite
  (∀ z, finite z = true → op.eqZero z = false → op.gtZero z = !op.signbit z) →
  (∀ x y, finite x = true → finite y = true → op.eqZero y = false →
    finite (op.rem x y) = true ∧
    (op.eqZero (op.rem x y) = false → op.magnitudeLt (op.rem x y) y)) →
  (∀ r y, finite r = true → op.eqZero r = true →
    finite (op.copysign r y) = true ∧ op.signbit (op.copysign r y) = op.signbit y) →
  (∀ r y, finite r = true → finite y = true → op.magnitudeLt r y →
    op.signbit r ≠ op.signbit y →
    finite (op.add r y) = true ∧ op.signbit (op.add r y) = op.signbit y) →
  ∀ x y, finite x = true → finite y = true → op.eqZero y = false →
    let r := mod_generic infinite finite op.rem op.eqZero op.copysign op.gtZero op.add x y
    finite r = true ∧ op.signbit r = op.signbit y

theorem genericModuloSign_proven : GenericModuloSign := by
  intro F op nan finite infinite hgt hrem hcopy hadd x y hx hy hy0
  have hi : infinite y = false := by
    change Bool.and (!(nan y)) (!(finite y)) = false
    simp only [hy, Bool.not_true, Bool.and_false]
  have hr := hrem x y hx hy hy0
  change finite (mod_generic infinite finite op.rem op.eqZero op.copysign op.gtZero op.add x y) = true ∧ _
  unfold mod_generic
  simp only [hi, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases hz : op.eqZero (op.rem x y)
  · have hmag := hr.2 hz
    have hgx := hgt (op.rem x y) hr.1 hz
    have hgy := hgt y hy hy0
    rw [hgx, hgy]
    cases hsx : op.signbit (op.rem x y) <;> cases hsy : op.signbit y <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_xor, Bool.true_xor,
        Bool.false_eq_true, ↓reduceIte]
    · exact ⟨hr.1, hsx⟩
    · simpa only [hsy] using hadd _ _ hr.1 hy hmag (by rw [hsx, hsy]; decide)
    · simpa only [hsy] using hadd _ _ hr.1 hy hmag (by rw [hsx, hsy]; decide)
    · exact ⟨hr.1, hsx⟩
  · exact hcopy _ _ hr.1 hz


namespace RemainderProofs
open TruncProofs NextProofs

theorem finite_exp_lt {T : FTy} (x : FV T) (hf : x.isfinite = true) : x.expField < T.fmt.emax := by
  have hne : x.expField ≠ T.fmt.emax := by simpa only [Fl.isfinite, bne_iff_ne] using hf
  have hb : x.expField < 2 ^ T.fmt.eb := Nat.mod_lt _ (Nat.two_pow_pos _)
  have he := (good_fty T).emax_succ
  omega

theorem positive_float_bits {T : FTy} (x : FV T) (hs : x.signbit = false) : x.toBits = x.magnitude := by
  rw [(Fl.bits_split x).1, hs]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]

theorem unbiased_pattern {T : FTy} (x : FV T) : pattern (unbiased_exponent x) = x.expField := by
  have hmeta : ∀ S : FTy, S.uintTy.signed = false := by intro S; cases S <;> decide
  have h := (floatFieldsAndRemModCore_proven T x x).1
  have hp := val_of_unsigned_pattern (hmeta T) (unbiased_exponent x)
  omega

theorem explicit_normal_pattern {T : FTy} (x : FV T) (he : x.expField ≠ 0) :
    pattern (explicit_mantissa_noinfnan x) = x.frac + 2 ^ T.fmt.sb := by
  have hmeta : ∀ S : FTy, S.uintTy.signed = false := by intro S; cases S <;> decide
  have h := (floatFieldsAndRemModCore_proven T x x).2.1
  simp only [he, false_and, ↓reduceIte] at h
  have hp := val_of_unsigned_pattern (hmeta T) (explicit_mantissa_noinfnan x)
  omega

theorem rem_internal_fast_key {T : FTy} (x y : FV T)
    (hxs : x.signbit = false) (hys : y.signbit = false) (hyf : y.isfinite = true)
    (hxy : y.magnitude < x.magnitude) (hey : T.fmt.sb < y.expField)
    (hdiff : x.expField - y.expField ≤ T.fmt.eb) :
    (rem_internal x y).isfinite = true ∧ (rem_internal x y).signbit = false ∧
    (rem_internal x y).key = x.key % y.key := by
  let ex := unbiased_exponent x
  let ey := unbiased_exponent y
  let delta := int.sub ex ey
  let mx := explicit_mantissa_noinfnan x
  let my := explicit_mantissa_noinfnan y
  let r := urem_int (int.shl_BitInteger_BitUnsigned mx delta) my
  let ep := int.sub ey (int.lit T.uintTy 1)
  let D := x.expField - y.expField
  let MX := x.frac + 2 ^ T.fmt.sb
  let MY := y.frac + 2 ^ T.fmt.sb
  let R := (MX * 2 ^ D) % MY
  have hmeta : ∀ S : FTy, S.uintTy.signed = false ∧ S.fmt.width = 1 + S.fmt.eb + S.fmt.sb ∧
      (significand_bits S).val = (S.fmt.sb : Int) ∧ (exponent_bits S).val = (S.fmt.eb : Int) ∧
      pattern (int.lit S.uintTy 1) = 1 ∧ (zero_float S).signbit = false := by
    intro S; cases S <;> decide
  obtain ⟨hu, hw, hsb, heb, hone, hzsign⟩ := hmeta T
  have hEx : y.expField ≤ x.expField := by
    rw [Fl.expField_eq, Fl.expField_eq]
    exact Nat.div_le_div_right (Nat.le_of_lt hxy)
  have hxe0 : x.expField ≠ 0 := by omega
  have hye0 : y.expField ≠ 0 := by omega
  have hEX : pattern ex = x.expField := unbiased_pattern x
  have hEY : pattern ey = y.expField := unbiased_pattern y
  have hD : pattern delta = D := by rw [uint_fty_sub T ex ey (by rw [hEX, hEY]; exact hEx), hEX, hEY]
  have hDv : delta.val = (D : Int) := by rw [← val_of_unsigned_pattern hu delta, hD]
  have hMX : pattern mx = MX := explicit_normal_pattern x hxe0
  have hMY : pattern my = MY := explicit_normal_pattern y hye0
  have hMYpos : 0 < MY := by dsimp [MY]; have := Nat.two_pow_pos T.fmt.sb; omega
  have hMXbound : MX < 2 ^ (T.fmt.sb + 1) := by
    have := (mag_decomp x).2
    dsimp [MX]
    rw [Nat.pow_succ]
    omega
  have hMYbound : MY < 2 ^ (T.fmt.sb + 1) := by
    have := (mag_decomp y).2
    dsimp [MY]
    rw [Nat.pow_succ]
    omega
  have hshiftfit : MX * 2 ^ D < 2 ^ T.fmt.width := by
    have hm := Nat.mul_lt_mul_of_pos_right hMXbound (Nat.two_pow_pos D)
    rw [← Nat.pow_add] at hm
    have hbound : ∀ (S : FTy) (d : Nat), d ≤ S.fmt.eb → S.fmt.sb + 1 + d ≤ S.fmt.width := by
      intro S d hd
      have hw : S.fmt.width = 1 + S.fmt.eb + S.fmt.sb := rfl
      omega
    have hp : 2 ^ (T.fmt.sb + 1 + D) ≤ 2 ^ T.fmt.width :=
      Nat.pow_le_pow_right (by decide) (hbound T D hdiff)
    exact Nat.lt_of_lt_of_le hm hp
  have hR : pattern r = R := by
    rw [urem_fty_pattern T _ my (by rw [hMY]; exact hMYpos), uint_fty_shift, hMX, hD, hMY,
      Nat.mod_eq_of_lt hshiftfit]
  have hRsmall : R < MY := Nat.mod_lt _ hMYpos
  have hEP : pattern ep = y.expField - 1 := by
    rw [uint_fty_sub T ey (int.lit T.uintTy 1) (by rw [hEY, hone]; omega), hEY, hone]
  have hEPv : ep.val = ((y.expField - 1 : Nat) : Int) := by rw [← val_of_unsigned_pattern hu ep, hEP]
  have hexv : ex.val = (x.expField : Int) := (floatFieldsAndRemModCore_proven T x y).1
  have heyv : ey.val = (y.expField : Int) := (floatFieldsAndRemModCore_proven T y x).1
  have hfast : (int.lt (significand_bits T) ey && int.le delta (exponent_bits T)) = true := by
    rw [JuliaLean.Proofs.base.int.lt_eq, JuliaLean.Proofs.base.int.le_eq, hsb, heyv, hDv, heb]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Int.ofNat_lt.mpr hey, Int.ofNat_le.mpr hdiff⟩
  have hfirst : int.le_BitUnsigned (reinterpret_Unsigned x) (reinterpret_Unsigned y) = false := by
    rw [uint_fty_le, pattern_reinterpret_Unsigned, pattern_reinterpret_Unsigned,
      positive_float_bits x hxs, positive_float_bits y hys]
    exact decide_eq_false (by omega)
  have hkey : x.key % y.key = ((R * 2 ^ (y.expField - 1) : Nat) : Int) := by
    rw [positive_float_key x hxs, positive_float_key y hys]
    simp only [hxe0, hye0, ↓reduceIte]
    rw [← Int.natCast_emod]
    have he : x.expField - 1 = D + (y.expField - 1) := by dsimp [D]; omega
    rw [he, remainder_scaled_units]
  unfold rem_internal
  dsimp only
  rw [hfirst]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if (int.lt (significand_bits T) ey && int.le delta (exponent_bits T)) then
    if int.eq r (int.lit T.uintTy 0) then zero_float T else _to_float r ep else _).isfinite = true ∧ _
  rw [hfast]
  simp only [↓reduceIte]
  rw [uint_fty_eq_zero, hR]
  by_cases hr0 : R = 0
  · simp only [hr0, decide_true, ↓reduceIte]
    have hz := Fl.zero_spec (good_fty T) false
    rw [hkey, hr0, Nat.zero_mul]
    exact ⟨hz.1, hzsign, hz.2⟩
  · simp only [hr0, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hefin := finite_exp_lt y hyf
    have hlog : R.log2 ≤ T.fmt.sb := by
      have hh := (Nat.log2_lt hr0).mpr (Nat.lt_trans hRsmall hMYbound)
      omega
    have hv := to_float_exact_key T r ep (by rw [hR]; omega)
      (by rw [hR]; exact Nat.lt_trans hRsmall hMYbound)
      (by rw [hEPv]; exact Int.natCast_nonneg _) (by rw [hEPv, Int.toNat_natCast, hR]; omega)
    rw [hkey]
    simpa only [hR, hEPv, Int.toNat_natCast] using hv


theorem uint_add_pattern (T : FTy) (a b : JInt T.uintTy)
    (h : pattern a + pattern b < 2 ^ T.fmt.width) :
    pattern (int.add a b) = pattern a + pattern b := by
  have hu : T.uintTy.signed = false := by cases T <;> rfl
  have hv : (int.add a b).val = ((pattern a + pattern b : Nat) : Int) := by
    rw [add_int_val, uint_fty_wrap, ← val_of_unsigned_pattern hu a, ← val_of_unsigned_pattern hu b,
      ← Int.natCast_add]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr h)
  have hp := val_of_unsigned_pattern hu (int.add a b)
  omega

theorem uint_min_pattern (T : FTy) (a b : JInt T.uintTy) :
    pattern (int.ifelse (int.lt_BitUnsigned a b) a b) = min (pattern a) (pattern b) := by
  rw [uint_fty_compare]
  unfold int.ifelse
  by_cases h : pattern a < pattern b
  · simp only [h, decide_true, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt h)]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_right (by omega : pattern b ≤ pattern a)]

theorem uint_shift_right_pattern (T : FTy) (a b : JInt T.uintTy) :
    pattern (int.shr_BitUnsigned_BitUnsigned a b) = pattern a / 2 ^ pattern b := by
  exact pattern_lshr_int a b

theorem mantissa_pattern {T : FTy} (x : FV T) : pattern (mantissa x) = x.frac := by
  have hv := (floatBitLayoutInvariants_proven.2.2.2 T x).2.2.2.2
  have hu : T.uintTy.signed = false := by cases T <;> rfl
  have hp := val_of_unsigned_pattern hu (mantissa x)
  omega

theorem preprocessing_bounds (T : FTy) (mx my ex ey t : Nat)
    (hmx : mx < 2 ^ (T.fmt.sb + 1)) (hmy : 0 < my) (hmyb : my < 2 ^ (T.fmt.sb + 1))
    (hex : ex < T.fmt.emax) (hey : ey ≤ ex)
    (ht : t ≤ my.log2) (hdiv : my % 2 ^ t = 0) (hodd : (my / 2 ^ t) % 2 = 1)
    (hrange : ey + my.log2 + 1 < T.fmt.emax + T.fmt.sb) :
    let r := min (ex - ey) t
    let b := my / 2 ^ r
    let l := min (ex - ey - r) T.fmt.eb
    let d := ex - ey - r - l
    let c := T.fmt.width - my.log2 - 1 + t
    let m := (mx * 2 ^ l) % b
    0 < b ∧ b ≤ 2 ^ (T.fmt.sb + 1) ∧ m < b ∧ 0 < c ∧ c < 2 ^ T.fmt.width ∧
    ey + r < 2 ^ T.fmt.width ∧ d < 2 ^ T.fmt.width ∧ mx * 2 ^ l < 2 ^ T.fmt.width ∧
    (d ≠ 0 → b % 2 = 1 ∧ b * 2 ^ c ≤ 2 ^ T.fmt.width) ∧
    (∀ q : Nat, 0 < q → q < b → ey + r + q.log2 + 1 < T.fmt.emax + T.fmt.sb) ∧
    (mx * 2 ^ ex) % (my * 2 ^ ey) = (m * 2 ^ d % b) * 2 ^ (ey + r) := by
  intro r b l d c m
  have hwidth : T.fmt.width = T.fmt.sb + 1 + T.fmt.eb := by unfold Fmt.width; omega
  have heb : 0 < T.fmt.eb := by
    have hall : ∀ S : FTy, 0 < S.fmt.eb := by intro S; cases S <;> decide
    exact hall T
  have hlog : my.log2 < T.fmt.sb + 1 := (Nat.log2_lt (by omega)).mpr hmyb
  have hlogW : my.log2 < T.fmt.width := by omega
  have hmeta : ∀ S : FTy, S.fmt.width < 2 ^ S.fmt.width ∧ S.fmt.emax < 2 ^ S.fmt.width := by
    intro S; cases S <;> decide
  obtain ⟨hwidthcap, hemaxcap⟩ := hmeta T
  have hr0 : r ≤ ex - ey := Nat.min_le_left _ _
  have hrt : r ≤ t := Nat.min_le_right _ _
  have hl0 : l ≤ ex - ey - r := Nat.min_le_left _ _
  have hle : l ≤ T.fmt.eb := Nat.min_le_right _ _
  have hexact : ex = l + d + (ey + r) := by dsimp only [d]; omega
  have hdivr : my % 2 ^ r = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hrt) (Nat.dvd_of_mod_eq_zero hdiv)
  have hpow : 2 ^ r ≤ my := Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_trans hrt ht)) (Nat.log2_self_le (by omega))
  have hb : 0 < b := Nat.div_pos hpow (Nat.two_pow_pos r)
  have hbmy : b ≤ my := Nat.div_le_self _ _
  have hbsmall : b ≤ 2 ^ (T.fmt.sb + 1) := by omega
  have hm : m < b := Nat.mod_lt _ hb
  have hfactor : my = b * 2 ^ r := exact_power_factor my r hdivr
  have hlogfactor : my.log2 = b.log2 + r := by rw [hfactor, Fl.log2_mul_pow b r (by omega)]
  have hcpos : 0 < c := by dsimp only [c]; omega
  have hcW : c < T.fmt.width := by dsimp only [c]; omega
  have hEY : ey + r ≤ ex := by omega
  have hD : d ≤ ex := by dsimp only [d]; omega
  have hshift : mx * 2 ^ l < 2 ^ T.fmt.width := by
    have hh := Nat.mul_lt_mul_of_pos_right hmx (Nat.two_pow_pos l)
    rw [← Nat.pow_add] at hh
    exact Nat.lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨hb, hbsmall, hm, hcpos, Nat.lt_trans hcW hwidthcap, Nat.lt_of_le_of_lt hEY (Nat.lt_trans hex hemaxcap),
    Nat.lt_of_le_of_lt hD (Nat.lt_trans hex hemaxcap), hshift, ?_, ?_, ?_⟩
  · intro hd
    have hrtEq : r = t := by
      dsimp only [r]
      by_cases hh : ex - ey ≤ t
      · have heq : r = ex - ey := Nat.min_eq_left hh
        have hd0 : d = 0 := by dsimp only [d]; omega
        contradiction
      · exact Nat.min_eq_right (by omega)
    refine ⟨?_, ?_⟩
    · simpa only [b, hrtEq] using hodd
    · have he : b.log2 + 1 + c = T.fmt.width := by dsimp only [c]; omega
      have hbound : b < 2 ^ (b.log2 + 1) := Nat.lt_log2_self
      have hh := Nat.mul_lt_mul_of_pos_right hbound (Nat.two_pow_pos c)
      rw [← Nat.pow_add, he] at hh
      exact Nat.le_of_lt hh
  · intro q hq hqb
    have hqlog : q.log2 < b.log2 + 1 := (Nat.log2_lt (by omega)).mpr (Nat.lt_trans hqb Nat.lt_log2_self)
    omega
  · exact preprocessing_remainder mx my ex ey r l d hdivr hexact

theorem finish_key_conditional (T : FTy) (d c m y e : JInt T.uintTy)
    (hy : 0 < pattern y) (hm : pattern m < pattern y)
    (hsmall : pattern y ≤ 2 ^ (T.fmt.sb + 1))
    (hc : pattern d ≠ 0 → 0 < pattern c)
    (hcapacity : pattern d ≠ 0 → pattern y * 2 ^ pattern c ≤ 2 ^ T.fmt.width)
    (hodd : pattern d ≠ 0 → pattern y % 2 = 1)
    (hrange : ∀ q : Nat, 0 < q → q < pattern y → pattern e + q.log2 + 1 < T.fmt.emax + T.fmt.sb) :
    let result := if int.eq m (int.lit T.uintTy 0) then zero_float T
      else if int.eq d (int.lit T.uintTy 0) then _to_float m e
      else
        let z := rem_internal_loop d.val.toNat d c m y
        let r := urem_int (int.shl_BitInteger_BitUnsigned z.2 z.1) y
        _to_float r e
    result.isfinite = true ∧ result.signbit = false ∧
      result.key = (((pattern m * 2 ^ pattern d % pattern y) * 2 ^ pattern e : Nat) : Int) := by
  by_cases hd : pattern d = 0
  · have hu : T.uintTy.signed = false := by cases T <;> rfl
    have hE : e.val.toNat = pattern e := by have := val_of_unsigned_pattern hu e; omega
    rw [uint_fty_eq_zero, uint_fty_eq_zero]
    simp only [hd, decide_true, ↓reduceIte, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hm]
    by_cases hm0 : pattern m = 0
    · simp only [hm0, decide_true, ↓reduceIte, Nat.zero_mul]
      have hz := Fl.zero_spec (good_fty T) false
      have hs : (zero_float T).signbit = false := by
        have hall : ∀ S : FTy, (zero_float S).signbit = false := by intro S; cases S <;> decide
        exact hall T
      exact ⟨hz.1, hs, hz.2⟩
    · simp only [hm0, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hv := to_float_exact_key T m e (by omega) (Nat.lt_of_lt_of_le hm hsmall)
        (by rw [← val_of_unsigned_pattern hu e]; exact Int.natCast_nonneg _)
        (by rw [hE]; exact hrange _ (by omega) hm)
      simpa only [hE] using hv
  · exact remainder_finish_key T d c m y e (hc hd) hy hm hsmall (hcapacity hd) hodd hrange

theorem slow_core_key (T : FTy) (mx my ex ey lz : JInt T.uintTy)
    (hmx : pattern mx < 2 ^ (T.fmt.sb + 1))
    (hmy : 0 < pattern my) (hmyb : pattern my < 2 ^ (T.fmt.sb + 1))
    (hex : pattern ex < T.fmt.emax) (hey : pattern ey ≤ pattern ex)
    (hlz : pattern lz = T.fmt.width - (pattern my).log2 - 1)
    (hrange : pattern ey + (pattern my).log2 + 1 < T.fmt.emax + T.fmt.sb) :
    let tz := int.cttz_int my
    let c := int.add lz tz
    let delta := int.sub ex ey
    let right := int.ifelse (int.lt_BitUnsigned tz delta) tz delta
    let y := int.shr_BitUnsigned_BitUnsigned my right
    let delta := int.sub delta right
    let e := int.add ey right
    let eb := int.remT T.uintTy (exponent_bits T)
    let left := int.ifelse (int.lt_BitUnsigned eb delta) eb delta
    let x := int.shl_BitInteger_BitUnsigned mx left
    let d := int.sub delta left
    let m := urem_int x y
    let result := if int.eq m (int.lit T.uintTy 0) then zero_float T
      else if int.eq d (int.lit T.uintTy 0) then _to_float m e
      else
        let z := rem_internal_loop d.val.toNat d c m y
        let r := urem_int (int.shl_BitInteger_BitUnsigned z.2 z.1) y
        _to_float r e
    result.isfinite = true ∧ result.signbit = false ∧
      result.key = ((((pattern mx * 2 ^ pattern ex) % (pattern my * 2 ^ pattern ey) : Nat) : Int)) := by
  intro tz c delta right y delta' e eb left x d m result
  let MX := pattern mx
  let MY := pattern my
  let EX := pattern ex
  let EY := pattern ey
  let TZ := pattern tz
  let R := min (EX - EY) TZ
  let B := MY / 2 ^ R
  let L := min (EX - EY - R) T.fmt.eb
  let D := EX - EY - R - L
  let C := T.fmt.width - MY.log2 - 1 + TZ
  let M := MX * 2 ^ L % B
  obtain ⟨ht, hdiv, hodd⟩ := cttz_fty_factor T my hmy
  have hn := preprocessing_bounds T MX MY EX EY TZ hmx hmy hmyb hex hey ht hdiv hodd hrange
  change 0 < B ∧ B ≤ 2 ^ (T.fmt.sb + 1) ∧ M < B ∧ 0 < C ∧ C < 2 ^ T.fmt.width ∧
    EY + R < 2 ^ T.fmt.width ∧ D < 2 ^ T.fmt.width ∧ MX * 2 ^ L < 2 ^ T.fmt.width ∧
    (D ≠ 0 → B % 2 = 1 ∧ B * 2 ^ C ≤ 2 ^ T.fmt.width) ∧
    (∀ q : Nat, 0 < q → q < B → EY + R + q.log2 + 1 < T.fmt.emax + T.fmt.sb) ∧
    (MX * 2 ^ EX) % (MY * 2 ^ EY) = (M * 2 ^ D % B) * 2 ^ (EY + R) at hn
  obtain ⟨hB, hBsmall, hM, hC, hCcap, hEcap, hDcap, hXcap, hRest, hRange, hResult⟩ := hn
  have hdelta : pattern delta = EX - EY := uint_fty_sub T ex ey hey
  have hright : pattern right = R := by
    rw [uint_min_pattern, hdelta, Nat.min_comm]
  have hy : pattern y = B := by rw [uint_shift_right_pattern, hright]
  have hrle : R ≤ EX - EY := Nat.min_le_left _ _
  have hdelta' : pattern delta' = EX - EY - R := by
    rw [uint_fty_sub T delta right (by rw [hdelta, hright]; exact hrle), hdelta, hright]
  have he : pattern e = EY + R := by
    rw [uint_add_pattern T ey right (by rw [hright]; exact hEcap), hright]
  have heb : pattern eb = T.fmt.eb := by
    have hall : ∀ S : FTy, pattern (int.remT S.uintTy (exponent_bits S)) = S.fmt.eb := by intro S; cases S <;> decide
    exact hall T
  have hleft : pattern left = L := by rw [uint_min_pattern, heb, hdelta', Nat.min_comm]
  have hlle : L ≤ EX - EY - R := Nat.min_le_left _ _
  have hd : pattern d = D := by
    rw [uint_fty_sub T delta' left (by rw [hdelta', hleft]; exact hlle), hdelta', hleft]
  have hx : pattern x = MX * 2 ^ L := by rw [uint_fty_shift, hleft, Nat.mod_eq_of_lt hXcap]
  have hm : pattern m = M := by rw [urem_fty_pattern T x y (by rw [hy]; exact hB), hx, hy]
  have hc : pattern c = C := by
    rw [uint_add_pattern T lz tz (by rw [hlz]; exact hCcap), hlz]
  have hf := finish_key_conditional T d c m y e (by rw [hy]; exact hB) (by rw [hm, hy]; exact hM)
    (by rw [hy]; exact hBsmall) (fun _ => by rw [hc]; exact hC)
    (fun h => by rw [hy, hc]; exact (hRest (by rw [hd] at h; exact h)).2)
    (fun h => by rw [hy]; exact (hRest (by rw [hd] at h; exact h)).1)
    (fun q hq hqb => by rw [he]; exact hRange q hq (by rw [hy] at hqb; exact hqb))
  change result.isfinite = true ∧ result.signbit = false ∧ _ at hf ⊢
  rw [hm, hd, hy, he, ← hResult] at hf
  exact hf

theorem mantissa_numerics {T : FTy} (y : FV T) (hy : y.isfinite = true) (hy0 : 0 < y.magnitude) :
    let m := mantissaNat y
    0 < m ∧ m < 2 ^ (T.fmt.sb + 1) ∧
    (y.expField ≠ 0 → m.log2 = T.fmt.sb) ∧
    (y.expField - 1) + m.log2 + 1 < T.fmt.emax + T.fmt.sb := by
  intro m
  obtain ⟨hmag, hfrac⟩ := mag_decomp y
  have hE := finite_exp_lt y hy
  have hp := Nat.two_pow_pos T.fmt.sb
  have hmax : 0 < T.fmt.emax := by
    have hh : ∀ S : FTy, 0 < S.fmt.emax := by intro S; cases S <;> decide
    exact hh T
  by_cases hz : y.expField = 0
  · have hm : m = y.frac := by simp only [m, mantissaNat, hz, ↓reduceIte, Nat.add_zero]
    have hpos : 0 < y.frac := by rw [hz, Nat.zero_mul, Nat.zero_add] at hmag; omega
    have hlog : y.frac.log2 < T.fmt.sb := (Nat.log2_lt (by omega)).mpr hfrac
    rw [hm]
    refine ⟨hpos, Nat.lt_trans hfrac (Nat.pow_lt_pow_right (by decide) (by omega)), ?_, ?_⟩
    · intro h; contradiction
    · rw [hz]
      omega
  · have hm : m = y.frac + 2 ^ T.fmt.sb := by simp only [m, mantissaNat, hz, ↓reduceIte]
    have hpos : 0 < m := by rw [hm]; omega
    have hsmall : m < 2 ^ (T.fmt.sb + 1) := by rw [hm, Nat.pow_succ]; omega
    have hlog : m.log2 = T.fmt.sb := by
      apply (Nat.log2_eq_iff (by omega : m ≠ 0)).mpr
      exact ⟨by rw [hm]; omega, hsmall⟩
    refine ⟨hpos, hsmall, fun _ => hlog, ?_⟩
    rw [hlog]
    omega

def divisorState {T : FTy} (y : FV T) : JInt T.uintTy × JInt T.uintTy × JInt T.uintTy :=
  let e := unbiased_exponent y
  if int.lt (int.lit .i64 0) e then
    (int.sub e (int.lit T.uintTy 1), explicit_mantissa_noinfnan y, int.remT T.uintTy (exponent_bits T))
  else
    let m := mantissa y
    (e, m, int.ctlz_int m)

theorem divisor_state_fields {T : FTy} (y : FV T) (hy : y.isfinite = true) (hy0 : 0 < y.magnitude) :
    pattern (divisorState y).1 = y.expField - 1 ∧
    pattern (divisorState y).2.1 = mantissaNat y ∧
    pattern (divisorState y).2.2 = T.fmt.width - (mantissaNat y).log2 - 1 := by
  have hu : T.uintTy.signed = false := by cases T <;> rfl
  have hev : (unbiased_exponent y).val = (y.expField : Int) := (floatFieldsAndRemModCore_proven T y y).1
  have hcondition : int.lt (int.lit .i64 0) (unbiased_exponent y) = decide (0 < y.expField) := by
    rw [JuliaLean.Proofs.base.int.lt_eq, hev]
    change decide ((0 : Int) < (y.expField : Int)) = decide (0 < y.expField)
    simp
  obtain ⟨hmpos, hmsmall, hnorm, -⟩ := mantissa_numerics y hy hy0
  have hpone : pattern (int.lit T.uintTy 1) = 1 := by cases T <;> rfl
  have heb : pattern (int.remT T.uintTy (exponent_bits T)) = T.fmt.eb := by
    have hall : ∀ S : FTy, pattern (int.remT S.uintTy (exponent_bits S)) = S.fmt.eb := by intro S; cases S <;> decide
    exact hall T
  unfold divisorState
  dsimp only
  rw [hcondition]
  by_cases hz : y.expField = 0
  · simp only [hz, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte, Prod.fst, Prod.snd]
    refine ⟨?_, ?_, ?_⟩
    · rw [unbiased_pattern, hz]
    · rw [mantissa_pattern]
      simp only [mantissaNat, hz, ↓reduceIte, Nat.add_zero]
    · have hm : pattern (mantissa y) = mantissaNat y := by rw [mantissa_pattern]; simp only [mantissaNat, hz, ↓reduceIte, Nat.add_zero]
      have hv := ctlz_fty_val T (mantissa y)
      rw [hm] at hv
      simp only [show mantissaNat y ≠ 0 by omega, ↓reduceIte] at hv
      have hp := val_of_unsigned_pattern hu (int.ctlz_int (mantissa y))
      omega
  · simp only [show 0 < y.expField by omega, decide_true, ↓reduceIte, Prod.fst, Prod.snd]
    refine ⟨?_, ?_, ?_⟩
    · rw [uint_fty_sub T _ _ (by rw [unbiased_pattern, hpone]; omega), unbiased_pattern, hpone]
    · rw [explicit_normal_pattern y hz]
      simp only [mantissaNat, hz, ↓reduceIte]
    · rw [heb, hnorm hz]
      unfold Fmt.width
      omega

theorem fast_condition {T : FTy} (x y : FV T) (hE : y.expField ≤ x.expField) :
    (int.lt (significand_bits T) (unbiased_exponent y) &&
      int.le (int.sub (unbiased_exponent x) (unbiased_exponent y)) (exponent_bits T)) =
    decide (T.fmt.sb < y.expField ∧ x.expField - y.expField ≤ T.fmt.eb) := by
  have hu : T.uintTy.signed = false := by cases T <;> rfl
  have hd : pattern (int.sub (unbiased_exponent x) (unbiased_exponent y)) = x.expField - y.expField := by
    rw [uint_fty_sub T _ _ (by rw [unbiased_pattern, unbiased_pattern]; exact hE), unbiased_pattern, unbiased_pattern]
  have hdv := val_of_unsigned_pattern hu (int.sub (unbiased_exponent x) (unbiased_exponent y))
  rw [hd] at hdv
  have he := (floatFieldsAndRemModCore_proven T y x).1
  have hmeta : ∀ S : FTy, (significand_bits S).val = (S.fmt.sb : Int) ∧ (exponent_bits S).val = (S.fmt.eb : Int) := by
    intro S; cases S <;> decide
  obtain ⟨hsb, heb⟩ := hmeta T
  rw [JuliaLean.Proofs.base.int.lt_eq, JuliaLean.Proofs.base.int.le_eq, hsb, heb, he, ← hdv]
  simp only [Int.ofNat_lt, Int.ofNat_le, Bool.decide_and]

theorem rem_internal_slow_key {T : FTy} (x y : FV T)
    (hxs : x.signbit = false) (hys : y.signbit = false) (hxf : x.isfinite = true) (hyf : y.isfinite = true)
    (hxy : y.magnitude < x.magnitude) (hy0 : 0 < y.magnitude) (hxe : x.expField ≠ 0)
    (hfast : ¬(T.fmt.sb < y.expField ∧ x.expField - y.expField ≤ T.fmt.eb)) :
    (rem_internal x y).isfinite = true ∧ (rem_internal x y).signbit = false ∧
      (rem_internal x y).key = x.key % y.key := by
  have hE : y.expField ≤ x.expField := by
    rw [Fl.expField_eq, Fl.expField_eq]
    exact Nat.div_le_div_right (Nat.le_of_lt hxy)
  have hfirst : int.le_BitUnsigned (reinterpret_Unsigned x) (reinterpret_Unsigned y) = false := by
    rw [uint_fty_le, pattern_reinterpret_Unsigned, pattern_reinterpret_Unsigned,
      positive_float_bits x hxs, positive_float_bits y hys]
    exact decide_eq_false (by omega)
  have hfastval := fast_condition x y hE
  rw [show decide (T.fmt.sb < y.expField ∧ x.expField - y.expField ≤ T.fmt.eb) = false from decide_eq_false hfast] at hfastval
  have hxe0 : int.eq (unbiased_exponent x) (int.lit .i64 0) = false := by
    rw [JuliaLean.Proofs.base.int.eq_eq]
    have hexv := (floatFieldsAndRemModCore_proven T x y).1
    change decide ((unbiased_exponent x).val = 0) = false
    rw [hexv]
    exact decide_eq_false (by omega)
  let mx := explicit_mantissa_noinfnan x
  let ex := int.sub (unbiased_exponent x) (int.lit T.uintTy 1)
  let st := divisorState y
  have hone : pattern (int.lit T.uintTy 1) = 1 := by cases T <;> rfl
  have hmx : pattern mx = mantissaNat x := by
    rw [explicit_normal_pattern x hxe]
    simp only [mantissaNat, hxe, ↓reduceIte]
  have hex : pattern ex = x.expField - 1 := by
    rw [uint_fty_sub T _ _ (by rw [unbiased_pattern, hone]; omega), unbiased_pattern, hone]
  obtain ⟨hey, hmy, hlz⟩ := divisor_state_fields y hyf hy0
  obtain ⟨hMXpos, hMXsmall, -, -⟩ := mantissa_numerics x hxf (by omega)
  obtain ⟨hMYpos, hMYsmall, -, hRange⟩ := mantissa_numerics y hyf hy0
  have hcore := slow_core_key T mx st.2.1 ex st.1 st.2.2
    (by rw [hmx]; exact hMXsmall) (by rw [hmy]; exact hMYpos) (by rw [hmy]; exact hMYsmall)
    (by rw [hex]; have hh := finite_exp_lt x hxf; omega)
    (by rw [hey, hex]; exact Nat.sub_le_sub_right hE 1)
    (by rw [hlz, hmy]) (by rw [hey, hmy]; exact hRange)
  have hkey : x.key % y.key = (((pattern mx * 2 ^ pattern ex) % (pattern st.2.1 * 2 ^ pattern st.1) : Nat) : Int) := by
    rw [positive_float_key x hxs, positive_float_key y hys, ← Int.natCast_emod]
    rw [hmx, hex, hmy, hey]
    rfl
  rw [hkey]
  unfold rem_internal
  dsimp only
  rw [hfirst, hfastval, hxe0]
  simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  exact hcore

theorem rem_internal_exact_key {T : FTy} (x y : FV T)
    (hxf : x.isfinite = true) (hyf : y.isfinite = true)
    (hxs : x.signbit = false) (hys : y.signbit = false) (hy0 : 0 < y.magnitude) :
    (rem_internal x y).isfinite = true ∧ (rem_internal x y).signbit = false ∧
      (rem_internal x y).key = x.key % y.key := by
  have hkx : x.key = ((magKey T.fmt x.magnitude : Nat) : Int) := by simp only [Fl.key, hxs, Bool.false_eq_true, ↓reduceIte]
  have hky : y.key = ((magKey T.fmt y.magnitude : Nat) : Int) := by simp only [Fl.key, hys, Bool.false_eq_true, ↓reduceIte]
  by_cases hle : x.magnitude ≤ y.magnitude
  · rw [rem_internal_le x y (by rw [positive_float_bits x hxs, positive_float_bits y hys]; exact hle),
      positive_float_bits x hxs, positive_float_bits y hys]
    by_cases hlt : x.magnitude < y.magnitude
    · simp only [hlt, ↓reduceIte]
      have hlo : 0 ≤ x.key := by rw [hkx]; exact Int.natCast_nonneg _
      have hhi : x.key < y.key := by rw [hkx, hky]; exact Int.ofNat_lt.mpr (magKey_strictMono T.fmt hlt)
      rw [Int.emod_eq_of_lt hlo hhi]
      exact ⟨hxf, hxs, rfl⟩
    · simp only [hlt, ↓reduceIte]
      have he : x.magnitude = y.magnitude := by omega
      have hke : x.key = y.key := by rw [hkx, hky, he]
      rw [hke, Int.emod_self]
      have hz := Fl.zero_spec (good_fty T) false
      have hs : (zero_float T).signbit = false := by
        have hall : ∀ S : FTy, (zero_float S).signbit = false := by intro S; cases S <;> decide
        exact hall T
      exact ⟨hz.1, hs, hz.2⟩
  · have hxy : y.magnitude < x.magnitude := by omega
    have hE : y.expField ≤ x.expField := by
      rw [Fl.expField_eq, Fl.expField_eq]
      exact Nat.div_le_div_right (Nat.le_of_lt hxy)
    by_cases hxe : x.expField = 0
    · have hye : y.expField = 0 := by omega
      have hfrac : 0 < y.frac := by
        have hh := (mag_decomp y).1
        rw [hye, Nat.zero_mul, Nat.zero_add] at hh
        omega
      rw [subnormal_remainder_pack x y hxs hys hxe hye hfrac]
      have hrb : x.frac % y.frac < 2 ^ T.fmt.sb := Nat.lt_trans (Nat.mod_lt _ hfrac) (mag_decomp y).2
      have hp := Fl.pack_parts (f := T.fmt) false 0 (x.frac % y.frac) (Nat.two_pow_pos T.fmt.eb) hrb
      have hmax : T.fmt.emax ≠ 0 := by
        have hall : ∀ S : FTy, S.fmt.emax ≠ 0 := by intro S; cases S <;> decide
        exact hall T
      refine ⟨?_, hp.1, ?_⟩
      · simp only [Fl.isfinite, hp.2.1, bne_iff_ne]
        omega
      · rw [Fl.pack_key false 0 (x.frac % y.frac) (Nat.two_pow_pos T.fmt.eb) hrb,
          positive_float_key x hxs, positive_float_key y hys, hxe, hye]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_sub, Nat.pow_zero, Nat.add_zero, Nat.mul_one]
        rw [← Int.natCast_emod]
    · by_cases hfast : T.fmt.sb < y.expField ∧ x.expField - y.expField ≤ T.fmt.eb
      · exact rem_internal_fast_key x y hxs hys hyf hxy hfast.1 hfast.2
      · exact rem_internal_slow_key x y hxs hys hxf hyf hxy hy0 hxe hfast

theorem abs_encoded {T : FTy} (x : FV T) (hx : x.isfinite = true) :
    abs_float x = encode T false x.magnitude := by
  unfold abs_float jlAbsFloat unaryFloat encode
  simp only [Fl.isnan_of_finite hx, Bool.and_false, Bool.false_eq_true, ↓reduceIte, finishFloat_eq, Nat.zero_add]

theorem copysign_encoded {T : FTy} (r x : FV T) :
    copysign_float r x = encode T x.signbit r.magnitude := by
  unfold copysign_float jlCopysignFloat encode signMask
  rw [finishFloat_eq, Nat.add_comm]

theorem copy_positive_metadata {T : FTy} (r x : FV T) (hr : r.isfinite = true) (hs : r.signbit = false) :
    (copysign_float r x).isfinite = true ∧ (copysign_float r x).signbit = x.signbit ∧
    (copysign_float r x).key = if x.signbit then -r.key else r.key := by
  have hm : r.magnitude < infMag T := (isfinite_iff_mag r).mp hr
  have hcap := Nat.lt_trans hm (infMag_lt_signMask T)
  rw [copysign_encoded]
  refine ⟨?_, sign_encode T x.signbit hcap, ?_⟩
  · rw [isfinite_iff_mag, mag_encode T x.signbit hcap]
    exact hm
  · unfold Fl.key
    rw [sign_encode T x.signbit hcap, mag_encode T x.signbit hcap, hs]
    simp only [Bool.false_eq_true, ↓reduceIte]

theorem signed_tmod (a b : Nat) (s t : Bool) :
    (if s then -(a : Int) else (a : Int)).tmod (if t then -(b : Int) else (b : Int)) =
      if s then -((a : Int) % (b : Int)) else (a : Int) % (b : Int) := by
  cases s <;> cases t <;> simp [Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg a)]

theorem key_natAbs {T : FTy} (x : FV T) : x.key.natAbs = magKey T.fmt x.magnitude := by
  unfold Fl.key
  cases x.signbit <;> simp

theorem rem_IEEEFloat_tmod {T : FTy} (x y : FV T)
    (hxf : x.isfinite = true) (hyf : y.isfinite = true) (hy0 : y.iszero = false) :
    (rem_IEEEFloat x y).isfinite = true ∧ (rem_IEEEFloat x y).signbit = x.signbit ∧
      (rem_IEEEFloat x y).key = x.key.tmod y.key := by
  have hY : 0 < y.magnitude := by
    have hh := hy0
    simp only [Fl.iszero, beq_eq_false_iff_ne] at hh
    omega
  by_cases hx0 : x.iszero = true
  · have hr := (rem_IEEEFloat_small_and_diag x y).2.1 hxf (by rw [iszero_float_eq]; exact hx0)
      (Fl.isnan_of_finite hyf) (by rw [iszero_float_eq]; exact hy0)
    have hmag : x.magnitude = 0 := by simpa only [Fl.iszero, beq_iff_eq] using hx0
    have hk : x.key = 0 := by unfold Fl.key; rw [hmag, magKey_zero]; cases x.signbit <;> simp
    rw [hr]
    refine ⟨hxf, rfl, ?_⟩
    rw [hk]
    simp
  · have hx0f : x.iszero = false := Bool.eq_false_iff.mpr hx0
    have hX : x.magnitude < infMag T := (isfinite_iff_mag x).mp hxf
    have hYC : y.magnitude < infMag T := (isfinite_iff_mag y).mp hyf
    have hxcap := Nat.lt_trans hX (infMag_lt_signMask T)
    have hycap := Nat.lt_trans hYC (infMag_lt_signMask T)
    let ax := abs_float x
    let ay := abs_float y
    have hax : ax = encode T false x.magnitude := abs_encoded x hxf
    have hay : ay = encode T false y.magnitude := abs_encoded y hyf
    have haxf : ax.isfinite = true := by rw [hax, isfinite_iff_mag, mag_encode T false hxcap]; exact hX
    have hayf : ay.isfinite = true := by rw [hay, isfinite_iff_mag, mag_encode T false hycap]; exact hYC
    have haxs : ax.signbit = false := by rw [hax]; exact sign_encode T false hxcap
    have hays : ay.signbit = false := by rw [hay]; exact sign_encode T false hycap
    have hay0 : 0 < ay.magnitude := by rw [hay, mag_encode T false hycap]; exact hY
    have hr := rem_internal_exact_key ax ay haxf hayf haxs hays hay0
    have hc := copy_positive_metadata (rem_internal ax ay) x hr.1 hr.2.1
    have hAxKey : ax.key = ((magKey T.fmt x.magnitude : Nat) : Int) := by
      unfold Fl.key
      rw [hax, sign_encode T false hxcap, mag_encode T false hxcap]
      rfl
    have hAyKey : ay.key = ((magKey T.fmt y.magnitude : Nat) : Int) := by
      unfold Fl.key
      rw [hay, sign_encode T false hycap, mag_encode T false hycap]
      rfl
    have hK : (copysign_float (rem_internal ax ay) x).key = x.key.tmod y.key := by
      rw [hc.2.2, hr.2.2, hAxKey, hAyKey]
      unfold Fl.key
      rw [signed_tmod]
    have hfx : isfinite_callee x = x.isfinite := isfinite_IEEEFloat_eq x
    have hfy : isfinite_callee y = y.isfinite := isfinite_IEEEFloat_eq y
    unfold rem_IEEEFloat
    rw [hfx, hfy, iszero_float_eq, iszero_float_eq]
    simp only [hxf, hyf, hx0f, hy0, Bool.not_false, Bool.and_true, ↓reduceIte]
    exact ⟨hc.1, hc.2.1, hK⟩

theorem rational_ratio_tdiv {T : FTy} (x y : FV T) (hx : x.isfinite = true) (hy : y.isfinite = true) :
    (x.toRat.1 * (y.toRat.2 : Int)).tdiv (y.toRat.1 * (x.toRat.2 : Int)) = x.key.tdiv y.key := by
  have hrx := Fl.toRat_key (good_fty T) x hx
  have hry := Fl.toRat_key (good_fty T) y hy
  let P := (x.toRat.2 : Int) * (y.toRat.2 : Int)
  have hp : 0 < P := Int.mul_pos (Int.natCast_pos.mpr hrx.1) (Int.natCast_pos.mpr hry.1)
  have hd : 0 < (T.fmt.den : Int) := Int.natCast_pos.mpr (Fmt.den_pos _)
  have hsx : (x.toRat.1 * (y.toRat.2 : Int)) * (T.fmt.den : Int) = x.key * P := by
    rw [Int.mul_right_comm, hrx.2, Int.mul_assoc]
  have hsy : (y.toRat.1 * (x.toRat.2 : Int)) * (T.fmt.den : Int) = y.key * P := by
    rw [Int.mul_right_comm, hry.2, Int.mul_assoc, Int.mul_comm (y.toRat.2 : Int) (x.toRat.2 : Int)]
  calc
    _ = ((x.toRat.1 * (y.toRat.2 : Int)) * (T.fmt.den : Int)).tdiv
        ((y.toRat.1 * (x.toRat.2 : Int)) * (T.fmt.den : Int)) := (Int.mul_tdiv_mul_of_pos_left _ _ hd).symm
    _ = (x.key * P).tdiv (y.key * P) := by rw [hsx, hsy]
    _ = _ := Int.mul_tdiv_mul_of_pos_left _ _ hp

theorem rational_remainder_identity {T : FTy} (x y r : FV T) (q : Int)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hr : r.isfinite = true)
    (hk : r.key = x.key - y.key * q) :
    r.toRat.1 * ((x.toRat.2 : Int) * (y.toRat.2 : Int)) =
      (x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int) * q) * (r.toRat.2 : Int) := by
  have hrx := (Fl.toRat_key (good_fty T) x hx).2
  have hry := (Fl.toRat_key (good_fty T) y hy).2
  have hrr := (Fl.toRat_key (good_fty T) r hr).2
  let P := (x.toRat.2 : Int) * (y.toRat.2 : Int)
  let N := x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int) * q
  have hsx : (x.toRat.1 * (y.toRat.2 : Int)) * (T.fmt.den : Int) = x.key * P := by
    rw [Int.mul_right_comm, hrx, Int.mul_assoc]
  have hsy : (y.toRat.1 * (x.toRat.2 : Int)) * (T.fmt.den : Int) = y.key * P := by
    rw [Int.mul_right_comm, hry, Int.mul_assoc, Int.mul_comm (y.toRat.2 : Int) (x.toRat.2 : Int)]
  have hscale : N * (T.fmt.den : Int) = (x.key - y.key * q) * P := by
    dsimp only [N]
    rw [Int.sub_mul, Int.mul_right_comm (y.toRat.1 * (x.toRat.2 : Int)) q (T.fmt.den : Int), hsx, hsy,
      Int.sub_mul, Int.mul_right_comm y.key P q]
  apply Int.eq_of_mul_eq_mul_right (show (T.fmt.den : Int) ≠ 0 by
    have hp := Int.natCast_pos.mpr (Fmt.den_pos T.fmt)
    omega)
  change (r.toRat.1 * P) * (T.fmt.den : Int) = (N * (r.toRat.2 : Int)) * (T.fmt.den : Int)
  calc
    _ = (r.toRat.1 * (T.fmt.den : Int)) * P := Int.mul_right_comm _ _ _
    _ = ((x.key - y.key * q) * (r.toRat.2 : Int)) * P := by rw [hrr, hk]
    _ = ((x.key - y.key * q) * P) * (r.toRat.2 : Int) := Int.mul_right_comm _ _ _
    _ = (N * (T.fmt.den : Int)) * (r.toRat.2 : Int) := by rw [hscale]
    _ = _ := Int.mul_right_comm _ _ _

def RemainderRelation {T : FTy} (x y r : FV T) : Prop :=
  let q := (x.toRat.1 * (y.toRat.2 : Int)).tdiv (y.toRat.1 * (x.toRat.2 : Int))
  r.isfinite = true ∧ r.signbit = x.signbit ∧
  r.key = x.key - y.key * q ∧ r.key.natAbs < y.key.natAbs ∧ 0 < r.toRat.2 ∧
  r.toRat.1 * ((x.toRat.2 : Int) * (y.toRat.2 : Int)) =
    (x.toRat.1 * (y.toRat.2 : Int) - y.toRat.1 * (x.toRat.2 : Int) * q) * (r.toRat.2 : Int)

theorem remainder_relation_of_key {T : FTy} (x y r : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hy0 : y.iszero = false)
    (hr : r.isfinite = true) (hs : r.signbit = x.signbit) (hk : r.key = x.key.tmod y.key) :
    RemainderRelation x y r := by
  have hyM : 0 < y.magnitude := by
    have hh := hy0
    simp only [Fl.iszero, beq_eq_false_iff_ne] at hh
    omega
  have hyK : 0 < y.key.natAbs := by
    rw [key_natAbs]
    have hh := magKey_strictMono T.fmt hyM
    simpa only [magKey_zero] using hh
  have hbound : r.key.natAbs < y.key.natAbs := by
    rw [hk, Int.natAbs_tmod]
    exact Nat.mod_lt _ hyK
  have hresult : r.key = x.key - y.key *
      (x.toRat.1 * (y.toRat.2 : Int)).tdiv (y.toRat.1 * (x.toRat.2 : Int)) := by
    rw [rational_ratio_tdiv x y hx hy, hk, Int.tmod_def]
  refine ⟨hr, hs, hresult, hbound, (Fl.toRat_key (good_fty T) r hr).1, ?_⟩
  exact rational_remainder_identity x y r _ hx hy hr hresult

def FiniteRemainderExact : Prop := ∀ (T : FTy) (x y : FV T),
  x.isfinite = true → y.isfinite = true → y.iszero = false →
  RemainderRelation x y (rem_IEEEFloat x y)

theorem finiteRemainderExact_proven : FiniteRemainderExact := by
  intro T x y hx hy hy0
  obtain ⟨hr, hs, hk⟩ := rem_IEEEFloat_tmod x y hx hy hy0
  exact remainder_relation_of_key x y _ hx hy hy0 hr hs hk

def PositiveInternalRemainderExact : Prop := ∀ (T : FTy) (x y : FV T),
  x.isfinite = true → y.isfinite = true → y.iszero = false →
  x.signbit = false → y.signbit = false → RemainderRelation x y (rem_internal x y)

theorem positiveInternalRemainderExact_proven : PositiveInternalRemainderExact := by
  intro T x y hx hy hy0 hsx hsy
  have hyM : 0 < y.magnitude := by
    have hh := hy0
    simp only [Fl.iszero, beq_eq_false_iff_ne] at hh
    omega
  obtain ⟨hr, hs, hk⟩ := rem_internal_exact_key x y hx hy hsx hsy hyM
  have hxK : 0 ≤ x.key := by
    unfold Fl.key
    rw [hsx]
    exact Int.natCast_nonneg _
  apply remainder_relation_of_key x y _ hx hy hy0 hr (hs.trans hsx.symm)
  rw [Int.tmod_eq_emod_of_nonneg hxK]
  exact hk

end RemainderProofs

/-! ## Registry entries -/

def GenericIntegerFloat16Conversion : Prop :=
  ∀ (I : Type) (value : I → Int) (toFloat32 : I → FV .f32),
  (∀ x, toFloat32 x = (Fl.roundRat (value x) 1 false : FV .f32)) →
  ∀ x, Float16_Integer toFloat32 Float16_Float32 x =
    (Fl.convert (Fl.roundRat (value x) 1 false : FV .f32) : FV .f16)

theorem genericIntegerFloat16Conversion_proven : GenericIntegerFloat16Conversion := by
  intro I value toFloat32 hconvert x
  unfold Float16_Integer
  rw [hconvert]
  exact @convertFloat_eq .f16 .f32 _

def GenericNumericFloatQueries : Prop :=
  ∀ (I F M Ty : Type) (constructor : I → F) (value : F → M) (rounded : I → M)
    (typeof : F → Ty) (resultType : Ty) (zero : Unit → I),
  (∀ x, value (constructor x) = rounded x) →
  (∀ y, typeof y = resultType) →
  (∀ x, value (float_any constructor x) = rounded x) ∧
    float_Type_Number zero (float_any constructor) typeof = resultType

theorem genericNumericFloatQueries_proven : GenericNumericFloatQueries := by
  intro I F M Ty constructor value rounded typeof resultType zero hvalue htype
  exact ⟨hvalue, htype _⟩

def PrecisionResultCorrect {t : IntTy} (p : JInt .i64) (b : JInt t) (result : Jl (JInt .i64)) : Prop :=
  (b.val ≤ 1 → result = .error (.domainError "`base` cannot be less than 2.")) ∧
  (1 < b.val → ∃ q, result = .ok q ∧ 0 ≤ q.val ∧
    b.val.toNat ^ q.val.toNat ≤ 2 ^ p.val.toNat ∧
    2 ^ p.val.toNat < b.val.toNat ^ (q.val.toNat + 1))

def GenericPrecisionMethods : Prop :=
  ∀ (A F : Type) (t : IntTy) (typeof : F → A) (binaryPrecision : A → JInt .i64)
    (floorLog : JInt .i64 → JInt t → Jl (JInt .i64)),
  (∀ p b, 0 ≤ p.val → 1 < b.val → b.val ≠ 2 →
    ∃ q, floorLog p b = .ok q ∧ 0 ≤ q.val ∧
      b.val.toNat ^ q.val.toNat ≤ 2 ^ p.val.toNat ∧
      2 ^ p.val.toNat < b.val.toNat ^ (q.val.toNat + 1)) →
  (∀ T b, 0 ≤ (binaryPrecision T).val → PrecisionResultCorrect (binaryPrecision T) b
    (precision_Type binaryPrecision floorLog T b)) ∧
  (∀ x b, 0 ≤ (binaryPrecision (typeof x)).val → PrecisionResultCorrect (binaryPrecision (typeof x)) b
    (precision_AbstractFloat typeof (precision_Type binaryPrecision floorLog) x b))

theorem genericPrecisionMethods_proven : GenericPrecisionMethods := by
  intro A F t typeof binaryPrecision floorLog hfloor
  constructor
  · intro T b hp
    exact radixPrecisionInterval_proven A t binaryPrecision floorLog hfloor T b hp
  · intro x b hp
    exact radixPrecisionInterval_proven A t binaryPrecision floorLog hfloor (typeof x) b hp

def GenericRealTypeBounds : Prop :=
  ∀ (Ty : Type) (Value : Ty → Type) (le : (t : Ty) → Value t → Value t → Prop)
    (lower upper : (t : Ty) → Value t),
  (∀ t z, le t (lower t) z) → (∀ t z, le t z (upper t)) →
  ∀ t (x z : Value t), le t (typemin_Real lower t x) z ∧ le t z (typemax_Real upper t x)

theorem genericRealTypeBounds_proven : GenericRealTypeBounds := by
  intro Ty Value le lower upper hlow hhigh t x z
  exact ⟨hlow t z, hhigh t z⟩

def GenericFloatingTypeLimits : Prop :=
  ∀ (Ty : Type) (Value : Ty → Type) (normal finite : (t : Ty) → Value t → Bool)
    (positive : (t : Ty) → Value t → Prop) (le : (t : Ty) → Value t → Value t → Prop)
    (minimum maximum : (t : Ty) → Value t),
  (∀ t, normal t (minimum t) = true ∧ positive t (minimum t) ∧
    ∀ z, normal t z = true → positive t z → le t (minimum t) z) →
  (∀ t, finite t (maximum t) = true ∧ ∀ z, finite t z = true → le t z (maximum t)) →
  ∀ t (x : Value t),
    normal t (floatmin_AbstractFloat minimum t x) = true ∧
    positive t (floatmin_AbstractFloat minimum t x) ∧
    (∀ z, normal t z = true → positive t z → le t (floatmin_AbstractFloat minimum t x) z) ∧
    finite t (floatmax_AbstractFloat maximum t x) = true ∧
    (∀ z, finite t z = true → le t z (floatmax_AbstractFloat maximum t x))

theorem genericFloatingTypeLimits_proven : GenericFloatingTypeLimits := by
  intro Ty Value normal finite positive le minimum maximum hmin hmax t x
  exact ⟨(hmin t).1, (hmin t).2.1, (hmin t).2.2, (hmax t).1, (hmax t).2⟩

def GenericFloatingInterfaces : Prop := GenericFloatingTypeLimits ∧
  (∀ (Ty : Type) (t : Ty), float_Type_AbstractFloat t = t) ∧
  (∀ (A : Type) (a : A), float_AbstractArray_AbstractFloat a = a)

theorem genericFloatingInterfaces_proven : GenericFloatingInterfaces := by
  exact ⟨genericFloatingTypeLimits_proven, fun _ _ => rfl, fun _ _ => rfl⟩


def entries : List Entry := [
  { id := "float-generic-integer-to-float16"
    juliaFile := "base/float.jl"
    juliaFns := ["Float16(::Integer)"]
    statement := "For every Integer subtype and every value, the generic Float16 conversion produces the Float16 rounding of the correctly rounded Float32 conversion, including overflow, assuming the subtype's Float32 constructor obeys its numeric conversion contract."
    source := "base/float.jl:238-242"
    status := .proven, prop := ``GenericIntegerFloat16Conversion, thm := some ``genericIntegerFloat16Conversion_proven },
  { id := "float-generic-numeric-conversion-and-type"
    juliaFile := "base/float.jl"
    juliaFns := ["float(x)", "float(::Type{T<:Number})"]
    statement := "For every Number subtype with a typed floating constructor, float(x) has the rounded mathematical value supplied by that constructor, and float(T) returns the constructor's result type; the constructor's numeric correctness and typeof's result-type invariant are the interface assumptions."
    source := "base/float.jl:367-384"
    status := .proven, prop := ``GenericNumericFloatQueries, thm := some ``genericNumericFloatQueries_proven },
  { id := "float-generic-precision-methods"
    juliaFile := "base/float.jl"
    juliaFns := ["precision(Type{T<:AbstractFloat})", "precision(AbstractFloat)"]
    statement := "For every AbstractFloat subtype, both type and value precision reject bases below two and return a nonnegative exponent bracketing 2^binaryPrecision between consecutive powers of the requested base, under the logarithm-floor callee's numeric contract."
    source := "base/float.jl:800-806"
    status := .proven, prop := ``GenericPrecisionMethods, thm := some ``genericPrecisionMethods_proven },
  { id := "float-generic-real-type-bounds"
    juliaFile := "base/float.jl"
    juliaFns := ["typemin(Real)", "typemax(Real)"]
    statement := "For every Real subtype, value-level typemin is a lower bound and typemax is an upper bound for every value of that subtype, assuming the selected type-level extrema satisfy those order contracts."
    source := "base/float.jl:969-970"
    status := .proven, prop := ``GenericRealTypeBounds, thm := some ``genericRealTypeBounds_proven },
  { id := "float-generic-floating-interfaces"
    juliaFile := "base/float.jl"
    juliaFns := ["floatmin(AbstractFloat)", "floatmax(AbstractFloat)", "float(::Type{T<:AbstractFloat})", "float(AbstractArray{<:AbstractFloat})"]
    statement := "For every AbstractFloat subtype, value-level floatmin is its smallest positive normal value and floatmax its greatest finite value under the type-level extrema contracts. float leaves every AbstractFloat type token and every already-floating AbstractArray unchanged."
    source := "base/float.jl:385,1019,1045,1166"
    status := .proven, prop := ``GenericFloatingInterfaces, thm := some ``genericFloatingInterfaces_proven },

  { id := "float-finite-remainder-exact"
    juliaFile := "base/float.jl"
    juliaFns := ["rem(::IEEEFloat,::IEEEFloat)"]
    statement := "For every finite x and finite nonzero y, rem(x,y) is the exact rational value x-y*trunc(x/y), preserves x's sign including signed zero, and has absolute value strictly below abs(y). The quotient truncates the exact rational x/y toward zero."
    source := "rem docstring and remainder invariant; base/float.jl:590-599"
    status := .proven, prop := ``RemainderProofs.FiniteRemainderExact, thm := some ``RemainderProofs.finiteRemainderExact_proven },
  { id := "float-internal-remainder-exact"
    juliaFile := "base/float.jl"
    juliaFns := ["rem_internal"]
    statement := "For every nonnegative finite x and positive finite y, rem_internal returns the exact rational x-y*trunc(x/y), with a positive sign and magnitude below y, across the fast, subnormal and normalized-loop branches."
    source := "rem_internal caller invariant; base/float.jl:524-589"
    status := .proven, prop := ``RemainderProofs.PositiveInternalRemainderExact, thm := some ``RemainderProofs.positiveInternalRemainderExact_proven },

  { id := "float-epsilon-neighbor-gap"
    juliaFile := "base/float.jl"
    juliaFns := ["eps(::IEEEFloat)"]
    statement := "For every finite x, eps(x) equals max(x-prevfloat(x), nextfloat(x)-x), except at nextfloat(-Inf) and prevfloat(Inf), where it equals the smaller gap."
    source := "eps docstring; base/float.jl:966-995"
    status := .proven, prop := ``EpsilonNeighborProofs.DocumentedEpsilonSpacing, thm := some ``EpsilonNeighborProofs.documentedEpsilonSpacing_proven },
  { id := "float-generic-modulo-divisor-sign"
    juliaFile := "base/float.jl"
    juliaFns := ["mod(::AbstractFloat,::AbstractFloat)"]
    statement := "For any AbstractFloat interface with finite small remainders, correct zero/sign tests, sign-copying and dominant-magnitude addition, mod of finite inputs and a nonzero finite divisor is finite with the divisor's sign, including signed-zero results."
    source := "mod docstring; base/float.jl:600-613"
    status := .proven, prop := ``GenericModuloSign, thm := some ``genericModuloSign_proven },

  { id := "float-finite-epsilon-bit-spacing"
    juliaFile := "base/float.jl"
    juliaFns := ["eps(::IEEEFloat)"]
    statement := "For every finite IEEEFloat x, eps(x) is finite and positive; its exact binary spacing in smallest-subnormal units is 2^(max(exponent_field(x)-1,0))."
    source := "base/float.jl:987-995"
    status := .proven, prop := ``EpsilonProofs.FiniteEpsilonBitSpacing, thm := some ``EpsilonProofs.finiteEpsilonBitSpacing_proven },

  { id := "float-positive-mantissa-reconstruction"
    juliaFile := "base/float.jl"
    juliaFns := ["_to_float"]
    statement := "Reconstructing a positive integer significand within the finite exponent range produces a finite nonnegative float with exact scaled value significand times 2^ep, including subnormal results."
    source := "base/float.jl:508-523"
    status := .proven, prop := ``FloatReconstructionExact, thm := some ``floatReconstructionExact_proven },
  { id := "float-subnormal-remainder-exact"
    juliaFile := "base/float.jl"
    juliaFns := ["rem_internal"]
    statement := "For every pair of nonnegative subnormal inputs with nonzero divisor, the remainder is the exact integer remainder of their stored fractions, with a positive sign."
    source := "base/float.jl:524-589"
    status := .proven, prop := ``SubnormalRemainderExact, thm := some ``subnormalRemainderExact_proven },
  { id := "float-remainder-loop-invariant"
    juliaFile := "base/float.jl"
    juliaFns := ["rem_internal (loop)"]
    statement := "The shifted remainder loop terminates with the exponent at most the shift size, preserves the exact integer dyadic remainder, and keeps its significand below the divisor."
    source := "base/float.jl:580-584"
    status := .proven, prop := ``RemainderLoopExact, thm := some ``remainderLoopExact_proven },
  { id := "float-generic-epsilon-spacing"
    juliaFile := "base/float.jl"
    juliaFns := ["eps(::AbstractFloat)"]
    statement := "Under the binary scaling interfaces of exponent and ldexp, finite AbstractFloat epsilon has the exact positive power-of-two spacing for its exponent bin; subnormals use the least positive spacing and nonfinite values produce NaN."
    source := "base/float.jl:985"
    status := .proven, prop := ``GenericEpsilonSpacing, thm := some ``genericEpsilonSpacing_proven },

  { id := "float-arbitrary-integer-step-iteration"
    juliaFile := "base/float.jl"
    juliaFns := ["_nextfloat(::IEEEFloat,::Bool,::Integer)"]
    statement := "For any nonnegative Integer step, including unbounded integers, stepping agrees with that many actual single nextfloat or prevfloat calls, saturating at infinity and preserving NaNs."
    source := "base/float.jl:810-846"
    status := .proven, prop := ``ArbitraryIntegerStepping, thm := some ``arbitraryIntegerStepping_proven },
  { id := "float-generic-binary-power-of-two"
    juliaFile := "base/float.jl"
    juliaFns := ["ispow2(::AbstractFloat)"]
    statement := "Under the exact binary frexp interface, a floating value is a power of two exactly when it is finite and its binary rational numerator is a positive integral power of two; NaNs, infinities, negatives and zero are rejected."
    source := "base/float.jl:958"
    status := .proven, prop := ``GenericBinaryPowerOfTwo, thm := some ``genericBinaryPowerOfTwo_proven },
  { id := "float-generic-abstract-classification"
    juliaFile := "base/float.jl"
    juliaFns := ["isnan(::AbstractFloat)", "isfinite(::AbstractFloat)", "isinf(::Real)"]
    statement := "AbstractFloat classification distinguishes NaN, finite and infinite inputs for every subtype obeying IEEE equality and self-subtraction laws."
    source := "base/float.jl:702,705,716"
    status := .proven, prop := ``GenericFloatClassification, thm := some ``genericFloatClassification_proven },
  { id := "float-generic-real-classification"
    juliaFile := "base/float.jl"
    juliaFns := ["isfinite(::Real)", "isinf(::Real)"]
    statement := "Real classification agrees with a nonzero decomposition denominator, for independently typed numerator and exponent components."
    source := "base/float.jl:706,716"
    status := .proven, prop := ``GenericRealClassification, thm := some ``genericRealClassification_proven },
  { id := "float-generic-integer-finite"
    juliaFile := "base/float.jl"
    juliaFns := ["isnan(::Number)", "isfinite(::Integer)", "isfinite(::Real)"]
    statement := "Every Integer subtype, including unbounded integers, is finite, non-NaN and non-infinite under its exact decomposition."
    source := "base/float.jl:703,706-707,716,745"
    status := .proven, prop := ``GenericIntegerFinite, thm := some ``genericIntegerFinite_proven },
  { id := "float-generic-parity"
    juliaFile := "base/float.jl"
    juliaFns := ["iseven(::AbstractFloat)", "isodd(::AbstractFloat)"]
    statement := "Floating parity agrees with divisibility of the exact Integer value, including the large-even-integer shortcut and nonintegral rejection."
    source := "base/float.jl:959-960"
    status := .proven, prop := ``GenericFloatParity, thm := some ``genericFloatParity_proven },
  { id := "float-radix-precision-interval"
    juliaFile := "base/float.jl"
    juliaFns := ["_precision"]
    statement := "Radix precision rejects bases below two and returns the integer exponent bracketing 2^binaryPrecision between successive powers of the requested base, assuming the logarithm-floor callee satisfies that numeric contract."
    source := "base/float.jl:800-804"
    status := .proven, prop := ``RadixPrecisionInterval, thm := some ``radixPrecisionInterval_proven },
  { id := "float-integer-all-widths-correct-rounding"
    juliaFile := "base/float.jl"
    juliaFns := ["Float16/32/64(::BitInteger)", "AbstractFloat(::BitInteger)"]
    statement := "All ten signed and unsigned BitInteger types convert to each IEEE format by nearest rounding with ties to even; AbstractFloat selects the same correctly-rounded Float64 conversion."
    source := "base/float.jl:246-256,350"
    status := .proven, prop := ``IntegerConversionsRounded, thm := some ``integerConversionsRounded_proven },
  { id := "float-narrowing-correct-rounding"
    juliaFile := "base/float.jl"
    juliaFns := ["Float16(::Float32)", "Float16(::Float64)", "Float32(::Float64)"]
    statement := "Every finite narrowing conversion is nearest-even rounding of the exact rational input; infinities keep their sign and NaNs remain NaN."
    source := "base/float.jl:341-343"
    status := .proven, prop := ``NarrowFloatConversions, thm := some ``narrowFloatConversions_proven },
  { id := "float-generic-integer-decomposition"
    juliaFile := "base/float.jl"
    juliaFns := ["decompose(::Integer)"]
    statement := "Every Integer representation has a nonzero denominator and reconstructs its mathematical integer value exactly."
    source := "base/float.jl:745"
    status := .proven, prop := ``GenericIntegerDecomposition, thm := some ``genericIntegerDecomposition_proven },
  { id := "float-generic-array-conversion"
    juliaFile := "base/float.jl"
    juliaFns := ["float(::AbstractArray{T})"]
    statement := "Every abstractly-typed array is rejected with ErrorException; successful concrete-array conversion preserves the elementwise floating analog required by the convert interface."
    source := "base/float.jl:1168-1174"
    status := .proven, prop := ``GenericArrayFloatConversion, thm := some ``genericArrayFloatConversion_proven },
  { id := "float-positive-normal-minimum-and-finite-maximum"
    juliaFile := "base/float.jl"
    juliaFns := ["floatmin(::Type{Float16/32/64})", "floatmax(::Type{Float16/32/64})"]
    statement := "Floatmin is the smallest positive normal value, and floatmax is the greatest finite value, in every IEEE format."
    source := "base/float.jl:972-977"
    status := .proven, prop := ``FloatExtrema, thm := some ``floatExtrema_proven },
  { id := "float-machine-epsilon-gap"
    juliaFile := "base/float.jl"
    juliaFns := ["eps(::Type{Float16/32/64})", "eps()"]
    statement := "Machine epsilon has exact value 2^(-significand_bits), and adding it to one produces the least representable value greater than one."
    source := "base/float.jl:979-982"
    status := .proven, prop := ``MachineEpsilonGap, thm := some ``machineEpsilonGap_proven },
  { id := "float-mixed-comparison-all-formats"
    juliaFile := "base/float.jl"
    juliaFns := ["==(::IEEEFloat,::BitInteger)", "==(::BitInteger,::IEEEFloat)", "<(::IEEEFloat,::BitInteger)", "<(::BitInteger,::IEEEFloat)", "<=(::IEEEFloat,::BitInteger)", "<=(::BitInteger,::IEEEFloat)"]
    statement := "All mixed equality, strict-order, and non-strict-order methods compare exact mathematical values in both argument orders for all Float16/32/64 bit patterns and all ten BitInteger types; every comparison with NaN is false."
    source := "base/float.jl:652-690"
    status := .proven, prop := ``MixedCompareAll, thm := some ``mixedCompareAll_proven },
  { id := "float-wide-mixed-comparison-exact"
    juliaFile := "base/float.jl"
    juliaFns := ["==(::Float32/Float64,::Int64/UInt64/Int128/UInt128)", "==(::Int64/UInt64/Int128/UInt128,::Float32/Float64)", "<(::Float32/Float64,::Int64/UInt64/Int128/UInt128)", "<(::Int64/UInt64/Int128/UInt128,::Float32/Float64)", "<=(::Float32/Float64,::Int64/UInt64/Int128/UInt128)", "<=(::Int64/UInt64/Int128/UInt128,::Float32/Float64)"]
    statement := "Equality, strict ordering, and non-strict ordering between every Float32/Float64 bit pattern and every Int64/UInt64/Int128/UInt128 value compare their exact mathematical values in both argument orders; NaN comparisons are false."
    source := "base/float.jl:652-674"
    status := .proven, prop := ``WideMixedComparisons, thm := some ``wideMixedComparisons_proven },
  { id := "float128-all-formats-correct-rounding"
    juliaFile := "base/float.jl"
    juliaFns := ["Float16(::UInt128)", "Float16(::Int128)", "Float32(::UInt128)", "Float32(::Int128)", "Float64(::UInt128)", "Float64(::Int128)"]
    statement := "Every UInt128 and Int128 converts to Float16, Float32, and Float64 by IEEE 754 nearest rounding with ties to even, across its complete integer domain."
    source := "base/float.jl:265-340"
    status := .proven, prop := ``Integer128AllFormatsRounded, thm := some ``integer128AllFormatsRounded_proven },
  { id := "float64-uint128-correct-rounding"
    juliaFile := "base/float.jl"
    juliaFns := ["Float64(::UInt128)"]
    statement := "Every UInt128 converts to Float64 by IEEE 754 nearest rounding with ties to even, including both exponent-packing branches and their sticky low bits."
    source := "base/float.jl:265-283"
    status := .proven, prop := ``Unsigned128Float64Rounded, thm := some ``unsigned128Float64Rounded_proven },
  { id := "float64-int128-correct-rounding"
    juliaFile := "base/float.jl"
    juliaFns := ["Float64(::Int128)"]
    statement := "Every Int128 converts to Float64 by IEEE 754 nearest rounding with ties to even, including typemin(Int128) and both signs."
    source := "base/float.jl:285-305"
    status := .proven, prop := ``Signed128Float64Rounded, thm := some ``signed128Float64Rounded_proven },
  { id := "float32-int128-correct-rounding"
    juliaFile := "base/float.jl"
    juliaFns := ["Float32(::Int128)"]
    statement := "Every Int128 converts to Float32 by IEEE 754 nearest rounding with ties to even, including typemin(Int128), both signs, and exponent carries."
    source := "base/float.jl:321-336"
    status := .proven, prop := ``Signed128Float32Rounded, thm := some ``signed128Float32Rounded_proven },
  { id := "float32-uint128-correct-rounding"
    juliaFile := "base/float.jl"
    juliaFns := ["Float32(::UInt128)"]
    statement := "Every UInt128 converts to Float32 by IEEE 754 nearest rounding with ties to even, including carry into the next exponent and overflow to positive infinity."
    source := "base/float.jl:307-319"
    status := .proven, prop := ``Unsigned128Float32Rounded, thm := some ``unsigned128Float32Rounded_proven },

  { id := "float-isless-partition"
    juliaFile := "base/float.jl"
    juliaFns := ["isless(::IEEEFloat, ::IEEEFloat)", "isequal(::IEEEFloat, ::IEEEFloat)"]
    statement := "For every IEEEFloat format (Float16, Float32, Float64), isless and isequal partition all bit patterns into a strict total order on isequal classes, with -0.0 strictly before +0.0 and all NaNs in one top class."
    source := "base/float.jl:619-634"
    status := .proven, prop := ``IslessPartition, thm := some ``islessPartition_proven },
  { id := "float-isless-transitive"
    juliaFile := "base/float.jl"
    juliaFns := ["isless(::IEEEFloat, ::IEEEFloat)", "_fpint"]
    statement := "For every IEEEFloat format (Float16, Float32, Float64), isless is transitive across every triple of bit patterns, including signed zeros and NaN payloads."
    source := "base/float.jl:621-634"
    status := .proven, prop := ``IslessTransitive, thm := some ``islessTransitive_proven },
  { id := "intarith-division-uabs-typemin"
    juliaFile := "base/float.jl"
    juliaFns := ["uabs(::Integer)", "uabs(::BitSigned)"]
    statement := "Base.uabs(x) returns the exact non-negative magnitude |x| as an unsigned integer of the same bit width for every BitInteger x, avoiding signed overflow at typemin(T)."
    source := "base/float.jl:225-237"
    status := .proven, prop := ``UabsExact, thm := some ``uabsExact_proven },
  { id := "float-small-integer-exact"
    juliaFile := "base/float.jl"
    juliaFns := ["Float16(::Integer)", "Float32(::BitSigned64)", "Float64(::BitSigned64)", "Float32(::BitUnsigned64)", "Float64(::BitUnsigned64)", "Float16(::Bool)", "Float32(::Bool)", "Float64(::Bool)", "AbstractFloat(::BitInteger)", "AbstractFloat(::Bool)"]
    statement := "Every integer of a BitInteger type whose bit width does not exceed the target IEEEFloat significand precision, as well as Bool, converts exactly to a finite IEEEFloat with that integer's rational value."
    source := "base/float.jl:238-256,350-351"
    status := .proven, prop := ``SmallIntegerExact, thm := some ``smallIntegerExact_proven },
  { id := "promotion-mixed-compare-small"
    juliaFile := "base/float.jl"
    juliaFns := ["==(::IEEEFloat, ::BitInteger)", "<(::IEEEFloat, ::BitInteger)", "<=(::IEEEFloat, ::BitInteger)", "==(::BitInteger, ::IEEEFloat)", "<(::BitInteger, ::IEEEFloat)", "<=(::BitInteger, ::IEEEFloat)"]
    statement := "==, <, and <= between Float16/Float32/Float64 and every BitInteger type of at most 32 bits, in both argument orders, compare the exact mathematical values; NaN compares false."
    source := "base/float.jl:636-692"
    status := .proven, prop := ``MixedCompareSmall, thm := some ``mixedCompareSmall_proven },
  { id := "floatfuncs-trunc-int-exact"
    juliaFile := "base/float.jl"
    juliaFns := ["round(::Type{Ti}, ::Tf, ::RoundingMode{:ToZero})", "unsafe_trunc(::Type{Ti}, ::Tf)", "round(::Type{Signed}, ::IEEEFloat, ::RoundingMode)", "round(::Type{Unsigned}, ::IEEEFloat, ::RoundingMode)", "round(::Type{Integer}, ::IEEEFloat, ::RoundingMode)"]
    statement := "For every IEEEFloat format Tf and BitInteger type Ti, round(Ti, x, RoundToZero) returns the exact integer truncation toward zero when x is finite and in Ti's range and throws InexactError(:round) otherwise; unsafe_trunc agrees on all in-range inputs."
    source := "base/float.jl:408-456,881-931"
    status := .proven, prop := ``TruncIntExact, thm := some ``truncIntExact_proven },
  { id := "floatfuncs-int-convert-exact"
    juliaFile := "base/float.jl"
    juliaFns := ["Ti(::Tf)", "Bool(::Float16)"]
    statement := "For every IEEEFloat format Tf and BitInteger type Ti, Ti(x) returns the exact integer value when x is a finite integral value in Ti's range and throws InexactError otherwise; Bool(x::Float16) accepts ±0.0 and 1.0 and throws InexactError(:Bool) otherwise."
    source := "base/float.jl:352-353,881-931"
    status := .proven, prop := ``IntConvertExact, thm := some ``intConvertExact_proven },
  { id := "floatfuncs-nextfloat-iterate"
    juliaFile := "base/float.jl"
    juliaFns := ["_nextfloat", "nextfloat(::AbstractFloat, ::Integer)", "nextfloat(::AbstractFloat)", "prevfloat(::AbstractFloat, ::Integer)", "prevfloat(::AbstractFloat)"]
    statement := "For every IEEEFloat format and BitInteger step d, nextfloat(x, d) and prevfloat(x, d) equal |d| iterative applications of single-step nextfloat/prevfloat, and single-step nextfloat/prevfloat produce the adjacent IEEEFloat value with no float strictly between."
    source := "base/float.jl:810-880"
    status := .proven, prop := ``NextfloatIterate, thm := some ``nextfloatIterate_proven },
  { id := "float-bit-layout-invariants"
    juliaFile := "base/float.jl"
    juliaFns := ["reinterpret(::Type{Unsigned}, ::IEEEFloat)", "reinterpret(::Type{Signed}, ::IEEEFloat)", "sign_mask", "exponent_mask", "exponent_one", "exponent_half", "significand_mask", "mantissa", "significand_bits", "exponent_bits", "exponent_bias", "exponent_max", "exponent_raw_max", "ieee754_exponent_min", "exponent_min", "uinttype", "inttype", "floattype"]
    statement := "For Float16, Float32, and Float64, sign_mask, exponent_mask, and significand_mask are disjoint and partition all bits; exponent/significand metadata match IEEE 754 parameters; mantissa extracts the significand bits; and reinterpret round-trips with integer bit patterns."
    source := "base/float.jl:1-170,1135-1150"
    status := .proven, prop := ``FloatBitLayoutInvariants, thm := some ``floatBitLayoutInvariants_proven },
  { id := "float-ieee754-representation-spec"
    juliaFile := "base/float.jl"
    juliaFns := ["ieee754_representation"]
    statement := "ieee754_representation packs sign, biased exponent, and significand into the exact IEEE 754 bit pattern, and its :omega, :nan, :inf, :subnormal, and :zero overloads produce ±floatmax, quiet/payload NaNs, ±Inf, subnormals, and ±0.0."
    source := "base/float.jl:171-224"
    status := .proven, prop := ``FloatIeee754RepresentationSpec, thm := some ``floatIeee754RepresentationSpec_proven },
  { id := "float-classification-and-decompose"
    juliaFile := "base/float.jl"
    juliaFns := ["isnan", "isfinite", "isinf", "decompose(::Integer)", "decompose(::Float16)", "decompose(::Float32)", "decompose(::Float64)"]
    statement := "isnan, isinf, and isfinite match the IEEE 754 exponent/significand classification, and decompose(x) returns (0,0,0) for NaN, (±1,0,0) for ±Inf, and (num, pow, ±1) for finite floats such that x equals (num/den) * 2^pow."
    source := "base/float.jl:694-780"
    status := .proven, prop := ``FloatClassificationAndDecompose, thm := some ``floatClassificationAndDecompose_proven },
  { id := "float-widen-convert-roundtrip"
    juliaFile := "base/float.jl"
    juliaFns := ["promote_rule", "widen", "Float16(::Float32)", "Float16(::Float64)", "Float32(::Float64)", "Float32(::Float16)", "Float64(::Float32)", "Float64(::Float16)", "Float64(::UInt128)", "Float64(::Int128)", "Float32(::UInt128)", "Float32(::Int128)", "Float16(::UInt128)", "Float16(::Int128)", "float"]
    statement := "Widening conversions between Float16, Float32, and Float64 preserve exact rational order; promote_rule and widen select the wider IEEEFloat type; and 128-bit integer-to-float conversions handle zero, sign, and two-part/top-bit mantissa reconstruction."
    source := "base/float.jl:247-388,477-485"
    status := .proven, prop := ``FloatWidenConvertRoundtrip, thm := some ``floatWidenConvertRoundtrip_proven },
  { id := "float-ieee-eq-lt-le"
    juliaFile := "base/float.jl"
    juliaFns := ["==(::IEEEFloat, ::IEEEFloat)", "<(::IEEEFloat, ::IEEEFloat)", "<=(::IEEEFloat, ::IEEEFloat)"]
    statement := "IEEE ==, <, and <= return false whenever either operand is NaN, equate -0.0 and +0.0, and form a strict total order on non-NaN values up to signed-zero equality."
    source := "base/float.jl:615-618,636-692"
    status := .proven, prop := ``FloatIeeeEqLtLe, thm := some ``floatIeeeEqLtLe_proven },
  { id := "float-round-llvm-and-convert"
    juliaFile := "base/float.jl"
    juliaFns := ["round(::IEEEFloat, ::RoundingMode{:ToZero})", "round(::IEEEFloat, ::RoundingMode{:Down})", "round(::IEEEFloat, ::RoundingMode{:Up})", "round(::IEEEFloat, ::RoundingMode{:Nearest})", "rounds_up", "_round_convert"]
    statement := "IEEEFloat round modes preserve non-finite and zero inputs, round finite non-zero values by truncated/floored/ceiled integer quotients with sign preservation, and _round_convert adjusts converted integers by one ulp according to rounds_up."
    source := "base/float.jl:457-476"
    status := .proven, prop := ``FloatRoundLlvmAndConvert, thm := some ``floatRoundLlvmAndConvert_proven },
  { id := "float-arithmetic-and-nan-propagation"
    juliaFile := "base/float.jl"
    juliaFns := ["-(::IEEEFloat)", "+(::IEEEFloat, ::IEEEFloat)", "-(::IEEEFloat, ::IEEEFloat)", "*(::IEEEFloat, ::IEEEFloat)", "/(::IEEEFloat, ::IEEEFloat)", "muladd(::IEEEFloat, ::IEEEFloat, ::IEEEFloat)", "abs(::IEEEFloat)"]
    statement := "Unary - flips the sign bit and preserves magnitude on non-NaN floats, abs clears the sign bit, NaN operands propagate through +, -, *, /, and muladd, and invalid forms Inf - Inf, Inf * 0, 0 / 0, and Inf / Inf yield NaN."
    source := "base/float.jl:486-497,693"
    status := .proven, prop := ``FloatArithmeticAndNanPropagation, thm := some ``floatArithmeticAndNanPropagation_proven },
  { id := "float-fields-and-rem-mod-spec"
    juliaFile := "base/float.jl"
    juliaFns := ["unbiased_exponent", "explicit_mantissa_noinfnan", "_to_float", "rem_internal", "rem(::IEEEFloat, ::IEEEFloat)", "mod(::AbstractFloat, ::AbstractFloat)"]
    statement := "unbiased_exponent extracts the raw exponent field, explicit_mantissa_noinfnan sets the hidden leading bit iff the float is not subnormal, _to_float reconstructs normalized floats, rem and mod return NaN on infinite dividends, zero divisors, or NaN inputs; finite dividends smaller than the divisor are unchanged by rem, equal magnitudes give signed zero, and infinite divisors preserve finite dividends."
    source := "base/float.jl:498-614"
    status := .proven, prop := ``FloatFieldsAndRemModSpec, thm := some ``floatFieldsAndRemModSpec_proven },
  { id := "float-bounds-and-eps"
    juliaFile := "base/float.jl"
    juliaFns := ["_precision_with_base_2", "_precision", "precision", "issubnormal", "ispow2", "iseven", "isodd", "typemin", "typemax", "floatmin", "floatmax", "eps"]
    statement := "precision returns 11, 24, and 53 for Float16, Float32, and Float64 and rejects bases below 2 with DomainError; issubnormal, ispow2, iseven, isodd, typemin, typemax, floatmin, floatmax, and eps satisfy their IEEE 754 boundary and unit-in-last-place invariants."
    source := "base/float.jl:781-809,932-1131"
    status := .proven, prop := ``FloatBoundsAndEps, thm := some ``floatBoundsAndEps_proven },
  { id := "float-bswap-and-collections"
    juliaFile := "base/float.jl"
    juliaFns := ["bswap(::IEEEFloat)", "float(::AbstractArray)", "float(::StepRange)", "float(::UnitRange)", "float(::StepRangeLen)", "float(::LinRange)"]
    statement := "bswap on IEEEFloat reverses the byte order of the underlying unsigned bit pattern as an involution, and float on arrays and ranges converts concrete elements or range endpoints while rejecting abstractly-typed arrays with ErrorException."
    source := "base/float.jl:1132-1134,1166-1180"
    status := .proven, prop := ``FloatBswapAndCollections, thm := some ``floatBswapAndCollections_proven }
]


end JuliaLean.Proofs.base.float
