import JuliaLean.base.bool
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.complex
import JuliaLean.Registry.Types

/-!
# Properties of `base/int.jl`

Specifications of the methods modelled in `JuliaLean.base.int`, stated as the docstrings, the
manual or obvious invariants promise them, with their proofs and refutations.

Specification vocabulary (independent of the model): `wrapInt t z` is two's-complement reduction
of `z` into `t`'s range (`JuliaLean.Core`), `pattern x` is `x mod 2^n`, `bitOf x k` is bit `k`
of that pattern, `Int.tdiv`/`Int.tmod` are truncated and `Int.fdiv`/`Int.fmod` floored division.
-/

namespace JuliaLean.Proofs.base.int

open JuliaLean JuliaLean.C JuliaLean.Promotion JuliaLean.base.int

/-! ## Specification vocabulary -/

/-- Bit `k` (from the least significant bit) of the `n`-bit two's-complement representation
of the integer `z`. -/
def bitOfInt (n : Nat) (z : Int) (k : Nat) : Bool := (z % ((2 ^ n : Nat) : Int)).toNat.testBit k

/-- The bit pattern of `x`: `x mod 2^n` as a natural number below `2^n`. -/
def pattern {t : IntTy} (x : JInt t) : Nat := (x.val % ((2 ^ t.bits : Nat) : Int)).toNat

/-- Bit `k` of `x`'s two's-complement representation. -/
def bitOf {t : IntTy} (x : JInt t) (k : Nat) : Bool := bitOfInt t.bits x.val k

/-- `t` can represent the integer `z`. -/
def fits (t : IntTy) (z : Int) : Prop := t.min ≤ z ∧ z ≤ t.max

/-- The number of set bits among the `n` bits of `x`. -/
def onesCount {t : IntTy} (x : JInt t) : Nat := (List.range t.bits).countP (fun k => bitOf x k)

/-! ## Two's-complement reduction -/

theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp at h ⊢ <;> omega

theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem wrapInt_wrapInt (t : IntTy) (z : Int) : wrapInt t (wrapInt t z) = wrapInt t z :=
  wrapInt_congr t (wrapInt_emod_self t z)

theorem wrapInt_val {t : IntTy} (x : JInt t) : wrapInt t x.val = x.val :=
  wrapInt_of_inRange t x.val x.property

theorem wrapInt_add_left (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a + b) = wrapInt t (a + b) :=
  wrapInt_congr t (by rw [Int.add_emod, wrapInt_emod_self, ← Int.add_emod])

theorem wrapInt_add_right (t : IntTy) (a b : Int) : wrapInt t (a + wrapInt t b) = wrapInt t (a + b) :=
  wrapInt_congr t (by rw [Int.add_emod, wrapInt_emod_self, ← Int.add_emod])

theorem wrapInt_mul_left (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a * b) = wrapInt t (a * b) :=
  wrapInt_congr t (by rw [Int.mul_emod, wrapInt_emod_self, ← Int.mul_emod])

theorem wrapInt_mul_right (t : IntTy) (a b : Int) : wrapInt t (a * wrapInt t b) = wrapInt t (a * b) :=
  wrapInt_congr t (by rw [Int.mul_emod, wrapInt_emod_self, ← Int.mul_emod])

theorem wrapInt_neg (t : IntTy) (a : Int) : wrapInt t (-wrapInt t a) = wrapInt t (-a) :=
  wrapInt_congr t (by cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega)

theorem wrapInt_sub_left (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a - b) = wrapInt t (a - b) :=
  wrapInt_congr t (by cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega)

theorem wrapInt_sub_right (t : IntTy) (a b : Int) : wrapInt t (a - wrapInt t b) = wrapInt t (a - b) :=
  wrapInt_congr t (by cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega)

theorem jint_eq {t : IntTy} {x y : JInt t} (h : x.val = y.val) : x = y := Subtype.ext h

theorem lit_val (t : IntTy) (z : Int) : (lit t z).val = wrapInt t z := rfl

/-! ## Bit patterns of model values -/

theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2); omega

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

theorem toJInt_fromJInt {t : IntTy} (x : JInt t) : toJInt t (fromJInt x) = x :=
  jint_eq (by rw [fromJInt, toJInt_ofInt_val, wrapInt_val])

/-- The value of a model integer as a function of its bit pattern. -/
theorem toJInt_congr {t : IntTy} (b : BitVec t.bits) (z : Int)
    (h : (b.toNat : Int) = z % ((2 ^ t.bits : Nat) : Int)) : (toJInt t b).val = wrapInt t z := by
  have hb : b = BitVec.ofInt t.bits z := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    omega
  rw [hb, toJInt_ofInt_val]

/-! ## Intrinsics -/

theorem neg_int_val {t : IntTy} (x : JInt t) : (neg_int x).val = wrapInt t (-x.val) := by
  simp only [neg_int, jlNegInt, fromJInt]
  rw [← BitVec.ofInt_neg, toJInt_ofInt_val]

theorem add_int_val {t : IntTy} (x y : JInt t) : (add_int x y).val = wrapInt t (x.val + y.val) := by
  simp only [add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add, toJInt_ofInt_val]

theorem sub_int_val {t : IntTy} (x y : JInt t) : (sub_int x y).val = wrapInt t (x.val - y.val) := by
  simp only [sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, toJInt_ofInt_val, Int.sub_eq_add_neg]

theorem mul_int_val {t : IntTy} (x y : JInt t) : (mul_int x y).val = wrapInt t (x.val * y.val) := by
  simp only [mul_int, jlMulInt, fromJInt]
  rw [← BitVec.ofInt_mul, toJInt_ofInt_val]

theorem eq_int_eq {t : IntTy} (x y : JInt t) : eq_int x y = decide (x.val = y.val) := by
  simp only [eq_int, jlEqInt]
  by_cases h : x.val = y.val
  · simp [fromJInt, show x = y from jint_eq h]
  · have : fromJInt x ≠ fromJInt y := by
      intro hb
      apply h
      rw [← wrapInt_val x, ← wrapInt_val y, ← toJInt_ofInt_val, ← toJInt_ofInt_val]
      exact congrArg (fun b => (toJInt t b).val) hb
    simp [h, this]

theorem slt_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    slt_int x y = decide (x.val < y.val) := by
  simp [slt_int, jlSltInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem sle_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    sle_int x y = decide (x.val ≤ y.val) := by
  simp [sle_int, jlSleInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem ult_int_eq {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    ult_int x y = decide (x.val < y.val) := by
  have hx := fromJInt_toNat_unsigned x h
  have hy := fromJInt_toNat_unsigned y h
  simp only [ult_int, jlUltInt]
  by_cases hl : x.val < y.val
  · simp [hl]; omega
  · simp [hl]; omega

theorem ule_int_eq {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    ule_int x y = decide (x.val ≤ y.val) := by
  have hx := fromJInt_toNat_unsigned x h
  have hy := fromJInt_toNat_unsigned y h
  simp only [ule_int, jlUleInt]
  by_cases hl : x.val ≤ y.val
  · simp [hl]; omega
  · simp [hl]; omega

theorem flipsign_int_val {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    (flipsign_int x y).val = wrapInt t (if y.val < 0 then -x.val else x.val) := by
  simp only [flipsign_int, jlFlipsignInt, fromJInt_toInt y h]
  split
  · simp only [fromJInt]; rw [← BitVec.ofInt_neg, toJInt_ofInt_val]
  · rw [toJInt_fromJInt, wrapInt_val]

/-! ## `x % T`, `unsigned`, `signed` -/

theorem okOf_eq {ε α : Type} {r : Except ε α} {h : ∀ e, r ≠ .error e} {a : α} (hr : r = .ok a) :
    okOf r h = a := by
  subst hr; rfl

theorem bitcast_val (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits = T.bits) :
    (bitcast T x h).val = wrapInt T x.val := by
  unfold bitcast
  apply toJInt_congr
  simp only [jlBitcast, BitVec.toNat_cast]
  rw [fromJInt_toNat, h]

theorem rem_BitInteger_Type_val (to : IntTy) {fr : IntTy} (x : JInt fr) :
    (rem_BitInteger_Type to x).val = wrapInt to x.val := by
  unfold rem_BitInteger_Type
  split
  · rename_i h
    have hlt := bits_lt_of_sizeofT_lt h
    unfold Generated.rem_trunc trunc_int
    rw [okOf_eq (a := BitVec.ofInt to.bits ((fromJInt x).toNat : Int)) (by simp [jlTruncInt, Nat.not_le.mpr hlt, pure, Except.pure])]
    rw [toJInt_ofInt_val]
    apply wrapInt_congr
    rw [fromJInt_toNat]
    have hd : ((2 ^ to.bits : Nat) : Int) ∣ ((2 ^ fr.bits : Nat) : Int) := by
      exact Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (Nat.le_of_lt hlt))
    exact Int.emod_emod_of_dvd _ hd
  · split
    · rename_i h h2
      have hlt := bits_lt_of_sizeofT_lt h2
      split
      · rename_i hs
        unfold Generated.rem_sext sext_int
        rw [okOf_eq (a := BitVec.ofInt to.bits (fromJInt x).toInt) (by simp [jlSextInt, Nat.not_le.mpr hlt, pure, Except.pure])]
        rw [toJInt_ofInt_val, fromJInt_toInt x (by simpa using hs)]
      · rfl
    · rename_i h h2
      have heq := bits_eq_of_sizeofT h h2
      exact bitcast_val to x heq

theorem remT_val (to : IntTy) {fr : IntTy} (x : JInt fr) : (remT to x).val = wrapInt to x.val := by
  unfold remT
  split
  · rename_i h
    subst h
    simp [rem_same, wrapInt_val]
  · exact rem_BitInteger_Type_val to x

theorem unsigned_BitSigned_val {t : IntTy} (x : JInt t) :
    (unsigned_BitSigned x).val = wrapInt t.toUnsigned x.val := bitcast_val _ x _

theorem signed_BitUnsigned_val {t : IntTy} (x : JInt t) :
    (signed_BitUnsigned x).val = wrapInt t.toSigned x.val := bitcast_val _ x _

theorem unsigned_val {t : IntTy} (x : JInt t) : (unsigned x).val = wrapInt t.toUnsigned x.val := by
  unfold unsigned
  split
  · exact unsigned_BitSigned_val x
  · exact remT_val _ x

theorem signed_val {t : IntTy} (x : JInt t) : (signed x).val = wrapInt t.toSigned x.val := by
  unfold signed
  split
  · exact remT_val _ x
  · exact signed_BitUnsigned_val x

theorem widenTo_val (T : IntTy) {S : IntTy} (x : JInt S) : (widenTo T x).val = wrapInt T x.val := rfl

/-! ## Checked division intrinsics -/

theorem checked_sdiv_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    checked_sdiv_int x y =
      if y.val = 0 ∨ (x.val = t.min ∧ y.val = -1) then .error .divideError
      else .ok (lit t (x.val.tdiv y.val)) := by
  have hx := x.property
  have hy := y.property
  have hmin : -((2 ^ (t.bits - 1) : Nat) : Int) = t.min := by
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.bits]
  unfold checked_sdiv_int jlCheckedSdivInt integerDivide
  simp only [Bool.true_or, ite_true, fromJInt_toInt x h, fromJInt_toInt y h, hmin]
  by_cases h0 : y.val = 0
  · simp [h0, divideResult, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
  · by_cases h1 : x.val = t.min ∧ y.val = -1
    · simp [h1, divideResult, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    · simp only [h0, h1, false_or, ite_false]
      simp [h0, h1, divideResult, pure, Except.pure]
      apply jint_eq
      rw [toJInt_ofInt_val, lit_val]

/-! ## Constants -/

theorem typemin_val (t : IntTy) : (typemin t).val = t.min := by cases t <;> decide

theorem typemax_val (t : IntTy) : (typemax t).val = t.max := by cases t <;> decide

/-! ## Primitive arithmetic and comparison (lines 84-94, 573-575) -/

/-- `-x` on a BitInteger is negation modulo `2^n` (`base/int.jl:86`). -/
def NegWraps : Prop := ∀ (t : IntTy) (x : JInt t), (neg x).val = wrapInt t (-x.val)
theorem negWraps_proven : NegWraps := fun _ x => neg_int_val x

/-- `x - y` on one BitInteger type is subtraction modulo `2^n` (`base/int.jl:87`). -/
def SubWraps : Prop := ∀ (t : IntTy) (x y : JInt t), (sub x y).val = wrapInt t (x.val - y.val)
theorem subWraps_proven : SubWraps := fun _ x y => sub_int_val x y

/-- `x + y` on one BitInteger type is addition modulo `2^n` (`base/int.jl:88`). -/
def AddWraps : Prop := ∀ (t : IntTy) (x y : JInt t), (add x y).val = wrapInt t (x.val + y.val)
theorem addWraps_proven : AddWraps := fun _ x y => add_int_val x y

/-- `x * y` on one BitInteger type is multiplication modulo `2^n` (`base/int.jl:89`). -/
def MulWraps : Prop := ∀ (t : IntTy) (x y : JInt t), (mul x y).val = wrapInt t (x.val * y.val)
theorem mulWraps_proven : MulWraps := fun _ x y => mul_int_val x y

/-- `-%x` is negation modulo `2^n` (`base/int.jl:91`). -/
def NegWrapWraps : Prop := ∀ (t : IntTy) (x : JInt t), (negWrap x).val = wrapInt t (-x.val)
theorem negWrapWraps_proven : NegWrapWraps := fun _ x => neg_int_val x

/-- `x -% y` is subtraction modulo `2^n` (`base/int.jl:92`). -/
def SubWrapWraps : Prop := ∀ (t : IntTy) (x y : JInt t), (subWrap x y).val = wrapInt t (x.val - y.val)
theorem subWrapWraps_proven : SubWrapWraps := fun _ x y => sub_int_val x y

/-- `x +% y` is addition modulo `2^n` (`base/int.jl:93`). -/
def AddWrapWraps : Prop := ∀ (t : IntTy) (x y : JInt t), (addWrap x y).val = wrapInt t (x.val + y.val)
theorem addWrapWraps_proven : AddWrapWraps := fun _ x y => add_int_val x y

/-- `x *% y` is multiplication modulo `2^n` (`base/int.jl:94`). -/
def MulWrapWraps : Prop := ∀ (t : IntTy) (x y : JInt t), (mulWrap x y).val = wrapInt t (x.val * y.val)
theorem mulWrapWraps_proven : MulWrapWraps := fun _ x y => mul_int_val x y

/-- The wrapping operators form the ring of integers modulo `2^n`, and `typemax(T) + 1 ==
typemin(T)` (the overflow behaviour of the manual's "Overflow behavior" section). -/
def PrimitiveRingLaws : Prop := ∀ (t : IntTy) (x y z : JInt t),
  add (sub x y) y = x ∧ mul x (add y z) = add (mul x y) (mul x z) ∧
  add (neg x) x = lit t 0 ∧ mul x (lit t 1) = x ∧ add (typemax t) (lit t 1) = typemin t
theorem primitiveRingLaws_proven : PrimitiveRingLaws := by
  intro t x y z
  refine ⟨jint_eq ?_, jint_eq ?_, jint_eq ?_, jint_eq ?_, jint_eq ?_⟩
  · simp only [add, sub, add_int_val, sub_int_val, wrapInt_add_left, Int.sub_add_cancel, wrapInt_val]
  · simp only [add, mul, add_int_val, mul_int_val, wrapInt_mul_right, wrapInt_add_left,
      wrapInt_add_right, Int.mul_add]
  · simp only [add, neg, add_int_val, neg_int_val, wrapInt_add_left, lit_val, Int.add_left_neg]
  · simp only [mul, mul_int_val, lit_val]
    rw [wrapInt_mul_right, Int.mul_one, wrapInt_val]
  · rw [add, add_int_val, typemax_val, typemin_val, lit_val]
    cases t <;> decide

/-- `x < y` on one BitSigned type compares the integer values (`base/int.jl:84`). -/
def LtSignedExact : Prop := ∀ t : IntTy, t.signed = true → ∀ x y : JInt t,
  lt_BitSigned x y = decide (x.val < y.val)
theorem ltSignedExact_proven : LtSignedExact := fun _ h x y => slt_int_eq h x y

/-- `x < y` on one BitUnsigned type compares the integer values (`base/int.jl:573`). -/
def LtUnsignedExact : Prop := ∀ t : IntTy, t.signed = false → ∀ x y : JInt t,
  lt_BitUnsigned x y = decide (x.val < y.val)
theorem ltUnsignedExact_proven : LtUnsignedExact := fun _ h x y => ult_int_eq h x y

/-- `x <= y` on one BitSigned type compares the integer values (`base/int.jl:574`). -/
def LeSignedExact : Prop := ∀ t : IntTy, t.signed = true → ∀ x y : JInt t,
  le_BitSigned x y = decide (x.val ≤ y.val)
theorem leSignedExact_proven : LeSignedExact := fun _ h x y => sle_int_eq h x y

/-- `x <= y` on one BitUnsigned type compares the integer values (`base/int.jl:575`). -/
def LeUnsignedExact : Prop := ∀ t : IntTy, t.signed = false → ∀ x y : JInt t,
  le_BitUnsigned x y = decide (x.val ≤ y.val)
theorem leUnsignedExact_proven : LeUnsignedExact := fun _ h x y => ule_int_eq h x y

/-- `*` on `Int128`/`UInt128` is multiplication modulo `2^128` (`base/int.jl:1083`). -/
def Mul128Wraps : Prop := ∀ t : IntTy, t.bits = 128 → ∀ x y : JInt t,
  (mul_128 x y).val = wrapInt t (x.val * y.val)
theorem mul128Wraps_proven : Mul128Wraps := fun _ _ x y => mul_int_val x y

/-! ## `unsigned`, `signed` (lines 238-273) -/

/-- `unsigned(x)` of an unsigned `x` is `x` (`base/int.jl:261`). -/
def UnsignedOfUnsigned : Prop := ∀ t : IntTy, t.signed = false → ∀ x : JInt t,
  (unsigned_any x).val = x.val
theorem unsignedOfUnsigned_proven : UnsignedOfUnsigned := by
  intro t h x
  have hx := x.property
  rw [unsigned_any, remT_val]
  cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned, wrapInt_val]

/-- `unsigned(x)` of a signed `x` reinterprets it: negative values become `x + 2^n`
(`base/int.jl:262`, docstring: "reinterpreted as unsigned without checking"). -/
def UnsignedReinterprets : Prop := ∀ t : IntTy, t.signed = true → ∀ x : JInt t,
  (unsigned_BitSigned x).val = if x.val < 0 then x.val + 2 ^ t.bits else x.val
theorem unsignedReinterprets_proven : UnsignedReinterprets := by
  intro t h x
  have hx := x.property
  rw [unsigned_BitSigned_val]
  cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;>
    split <;> omega

/-- `signed(x)` of a signed `x` is `x` (`base/int.jl:272`). -/
def SignedOfSigned : Prop := ∀ t : IntTy, t.signed = true → ∀ x : JInt t,
  (signed_any x).val = x.val
theorem signedOfSigned_proven : SignedOfSigned := by
  intro t h x
  have hx := x.property
  rw [signed_any, remT_val]
  cases t <;> simp_all [IntTy.signed, IntTy.toSigned, wrapInt_val]

/-- `signed(x)` of an unsigned `x` reinterprets it: values of at least `2^(n-1)` become
`x - 2^n` (`base/int.jl:273`, docstring: "reinterpreted as signed without checking"). -/
def SignedReinterprets : Prop := ∀ t : IntTy, t.signed = false → ∀ x : JInt t,
  (signed_BitUnsigned x).val = if 2 ^ (t.bits - 1) ≤ x.val then x.val - 2 ^ t.bits else x.val
theorem signedReinterprets_proven : SignedReinterprets := by
  intro t h x
  have hx := x.property
  rw [signed_BitUnsigned_val]
  by_cases hc : (2 : Int) ^ (t.bits - 1) ≤ x.val
  · rw [if_pos hc]
    cases t <;> simp_all [IntTy.signed, IntTy.toSigned, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;> omega
  · rw [if_neg hc]
    cases t <;> simp_all [IntTy.signed, IntTy.toSigned, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;> omega

/-- `signed(unsigned(x)) == x` for every signed `x` and `unsigned(signed(x)) == x` for every
unsigned `x` (the `unsigned` docstring example `signed(unsigned(-2)) == -2`). -/
def SignedRoundtrip : Prop :=
  (∀ t : IntTy, t.signed = true → ∀ x : JInt t, (signed (unsigned x)).val = x.val) ∧
  (∀ t : IntTy, t.signed = false → ∀ x : JInt t, (unsigned (signed x)).val = x.val)
theorem signedRoundtrip_proven : SignedRoundtrip := by
  constructor <;> intro t h x <;> have hx := x.property <;> simp only [signed_val, unsigned_val] <;>
    cases t <;> simp_all [IntTy.signed, IntTy.toSigned, IntTy.toUnsigned, IntTy.min, IntTy.max,
      IntTy.bits, wrapInt] <;> omega

/-! ## `x % T` (lines 618-634, 667-704) -/

/-- Narrowing `x % T` keeps the residue of `x` modulo `2^n` of `T` (`base/int.jl:621`,
docstring of `rem(x::Integer, T::Type{<:Integer})`: `x ≡ y (mod n)` with `y` in `T`'s range). -/
def RemTruncates : Prop := ∀ to fr : IntTy, ∀ h : sizeofT to < sizeofT fr, ∀ x : JInt fr,
  (Generated.rem_trunc to (bits_lt_of_sizeofT_lt h) x).val = wrapInt to x.val
theorem remTruncates_proven : RemTruncates := by
  intro to fr h x
  have hv := rem_BitInteger_Type_val to x
  simpa only [rem_BitInteger_Type, h, dite_true] using hv

/-- `true % T == 1` and `false % T == 0` (`base/int.jl:623`). -/
def RemBool : Prop := ∀ (to : IntTy) (b : Bool),
  (Generated.rem_bool to (ofBool to) b).val = if b then 1 else 0
theorem remBool_proven : RemBool := by
  intro to b
  cases to <;> cases b <;> decide

/-- Widening `x % T` from a signed `x` keeps the residue modulo `2^n` of `T`: the value for a
signed `T`, `x + 2^n` for negative `x` and unsigned `T` (`base/int.jl:626`). -/
def RemSignExtends : Prop := ∀ to fr : IntTy, ∀ h : sizeofT fr < sizeofT to, fr.signed = true →
  ∀ x : JInt fr, (Generated.rem_sext to (bits_lt_of_sizeofT_lt h) x).val = wrapInt to x.val
theorem remSignExtends_proven : RemSignExtends := by
  intro to fr h hs x
  have hv := rem_BitInteger_Type_val to x
  have hn : ¬ sizeofT to < sizeofT fr := by omega
  simpa only [rem_BitInteger_Type, hn, h, hs, dite_false, dite_true, ite_true] using hv

/-- Widening `x % T` from an unsigned `x` keeps its value (`base/int.jl:628`). -/
def RemZeroExtends : Prop := ∀ to fr : IntTy, sizeofT fr < sizeofT to → fr.signed = false →
  ∀ x : JInt fr, (Generated.rem_convert to (widenTo to) x).val = x.val
theorem remZeroExtends_proven : RemZeroExtends := by
  intro to fr h hs x
  have hx := x.property
  change wrapInt to x.val = x.val
  cases to <;> cases fr <;> simp_all [sizeofT, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max, wrapInt] <;>
    omega

/-- `x % T` between distinct types of one size reinterprets the bits: the residue modulo `2^n`
(`base/int.jl:631`). -/
def RemReinterprets : Prop := ∀ to fr : IntTy, ∀ h : fr.bits = to.bits, to ≠ fr →
  ∀ x : JInt fr, (Generated.rem_bitcast to h x).val = wrapInt to x.val
theorem remReinterprets_proven : RemReinterprets := fun to _ h _ x => bitcast_val to x h

/-- For any two BitInteger types, `x % T` is the representative of `x` modulo `2^n` in `T`'s
range, and converting back through a type at least as wide recovers `x`
(`base/int.jl:618-634,695`). -/
def RemTypeResidue : Prop := ∀ (to fr : IntTy) (x : JInt fr),
  (remT to x).val = wrapInt to x.val ∧
  ((fr.signed = to.signed ∧ fr.bits ≤ to.bits) ∨ (fr.signed = false ∧ fr.bits < to.bits) →
    remT fr (remT to x) = x)
theorem remTypeResidue_proven : RemTypeResidue := by
  intro to fr x
  refine ⟨remT_val to x, fun h => jint_eq ?_⟩
  have hx := x.property
  rw [remT_val, remT_val]
  cases to <;> cases fr <;> simp_all [IntTy.bits, IntTy.signed, IntTy.min, IntTy.max, wrapInt] <;> omega

/-- `x % Unsigned` reinterprets a signed `x` in the unsigned type of the same size
(`base/int.jl:696`). -/
def RemSignedUnsigned : Prop := ∀ t : IntTy, t.signed = true → ∀ x : JInt t,
  (rem_Signed_Unsigned x).val = if x.val < 0 then x.val + 2 ^ t.bits else x.val
theorem remSignedUnsigned_proven : RemSignedUnsigned := by
  intro t h x
  have hx := x.property
  rw [rem_Signed_Unsigned, remT_val]
  cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;>
    split <;> omega

/-- `x % Signed` reinterprets an unsigned `x` in the signed type of the same size
(`base/int.jl:697`). -/
def RemUnsignedSigned : Prop := ∀ t : IntTy, t.signed = false → ∀ x : JInt t,
  (signedType t).signed = true ∧ (signedType t).bits = t.bits ∧
  (rem_Unsigned_Signed x).val = if 2 ^ (t.bits - 1) ≤ x.val then x.val - 2 ^ t.bits else x.val
theorem remUnsignedSigned_proven : RemUnsignedSigned := by
  intro t h x
  have hx := x.property
  rw [rem_Unsigned_Signed, remT_val]
  by_cases hc : (2 : Int) ^ (t.bits - 1) ≤ x.val
  · rw [if_pos hc]
    cases t <;> simp_all [signedType, signed_Type_UInt8, signed_Type_UInt16, signed_Type_UInt32,
      signed_Type_UInt64, signed_Type_UInt128, IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;>
      omega
  · rw [if_neg hc]
    cases t <;> simp_all [signedType, signed_Type_UInt8, signed_Type_UInt16, signed_Type_UInt32,
      signed_Type_UInt64, signed_Type_UInt128, IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;>
      omega

/-- `mod(x, T)` is the residue of `x` modulo `2^n` of `T` in `T`'s range (`base/int.jl:701`). -/
def ModTypeResidue : Prop := ∀ (to fr : IntTy) (x : JInt fr),
  (mod_Integer_Type to x).val = wrapInt to x.val
theorem modTypeResidue_proven : ModTypeResidue := fun to _ x => remT_val to x

/-- `unsafe_trunc(T, x)` of an integer is its residue modulo `2^n` of `T` (`base/int.jl:704`). -/
def UnsafeTruncResidue : Prop := ∀ (to fr : IntTy) (x : JInt fr),
  (unsafe_trunc to x).val = wrapInt to x.val
theorem unsafeTruncResidue_proven : UnsafeTruncResidue := fun to _ x => remT_val to x

instance (t : IntTy) (z : Int) : Decidable (fits t z) := by unfold fits; infer_instance

/-! ## Comparisons across BitInteger types (lines 577-589) -/

theorem ltSame_eq {t : IntTy} (x y : JInt t) : ltSame x y = decide (x.val < y.val) := by
  unfold ltSame
  cases h : t.signed
  · simp [lt_BitUnsigned, ult_int_eq h]
  · simp [lt_BitSigned, slt_int_eq h]

theorem leSame_eq {t : IntTy} (x y : JInt t) : leSame x y = decide (x.val ≤ y.val) := by
  unfold leSame
  cases h : t.signed
  · simp [le_BitUnsigned, ule_int_eq h]
  · simp [le_BitSigned, sle_int_eq h]

theorem eqSame_eq {t : IntTy} (x y : JInt t) : eqSame x y = decide (x.val = y.val) := eq_int_eq x y

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

theorem ltPromote_eq {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) (y : JInt t) :
    ltPromote x y = decide (x.val < y.val) := by
  simp only [ltPromote, promoteSameSign, ltSame_eq, widenTo_val, widen_promote_left h,
    widen_promote_right h]

theorem lePromote_eq {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) (y : JInt t) :
    lePromote x y = decide (x.val ≤ y.val) := by
  simp only [lePromote, promoteSameSign, leSame_eq, widenTo_val, widen_promote_left h,
    widen_promote_right h]

theorem eqPromote_eq {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) (y : JInt t) :
    eqPromote x y = decide (x.val = y.val) := by
  simp only [eqPromote, promoteSameSign, eqSame_eq, widenTo_val, widen_promote_left h,
    widen_promote_right h]

theorem cmp_eq (op : {r : IntTy} → JInt r → JInt r → Bool) (R : Int → Int → Prop)
    [DecidableRel R] (hop : ∀ {r : IntTy} (a b : JInt r), op a b = decide (R a.val b.val))
    (hR : ∀ a b : Int, 0 ≤ a → b < 0 → ¬ R a b) {u s : IntTy} (hu : u.signed = false)
    (hs : s.signed = true) (x : JInt u) (y : JInt s) :
    cmp_BitUnsigned_BitSigned op x y = decide (R x.val y.val) := by
  have hx := x.property
  have hy := y.property
  unfold cmp_BitUnsigned_BitSigned
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
    have h0 : (lit IntTy.i64 0).val = 0 := by decide
    rw [h0]
    by_cases hy0 : 0 ≤ y.val
    · rw [wrapInt_of_inRange s.toUnsigned y.val ⟨by omega, by omega⟩,
        wrapInt_of_inRange u y.val ⟨by omega, by omega⟩]
      simp [hy0]
    · have hu0 : 0 ≤ x.val := by omega
      simp [hy0, hR x.val y.val hu0 (by omega)]

theorem eqUnsignedSigned_eq {u s : IntTy} (hu : u.signed = false) (hs : s.signed = true)
    (x : JInt u) (y : JInt s) :
    eq_BitUnsigned_BitSigned x y = decide (x.val = y.val) :=
  cmp_eq eqSame (· = ·) eqSame_eq (by intros; omega) hu hs x y

theorem ltUnsignedSigned_eq {u s : IntTy} (hu : u.signed = false) (hs : s.signed = true)
    (x : JInt u) (y : JInt s) :
    lt_BitUnsigned_BitSigned x y = decide (x.val < y.val) :=
  cmp_eq ltSame (· < ·) ltSame_eq (by intros; omega) hu hs x y

theorem leUnsignedSigned_eq {u s : IntTy} (hu : u.signed = false) (hs : s.signed = true)
    (x : JInt u) (y : JInt s) :
    le_BitUnsigned_BitSigned x y = decide (x.val ≤ y.val) :=
  cmp_eq leSame (· ≤ ·) leSame_eq (by intros; omega) hu hs x y

/-- `==` between a signed and an unsigned BitInteger compares the integer values
(`base/int.jl:577`). -/
def EqSignedUnsignedExact : Prop := ∀ s u : IntTy, s.signed = true → u.signed = false →
  ∀ (x : JInt s) (y : JInt u), eq_BitSigned_BitUnsigned x y = decide (x.val = y.val)
theorem eqSignedUnsignedExact_proven : EqSignedUnsignedExact := by
  intro s u hs hu x y
  rw [eq_BitSigned_BitUnsigned, eqUnsignedSigned_eq hu hs]
  simp [eq_comm]

/-- `<` between a signed and an unsigned BitInteger compares the integer values
(`base/int.jl:578`). -/
def LtSignedUnsignedExact : Prop := ∀ s u : IntTy, s.signed = true → u.signed = false →
  ∀ (x : JInt s) (y : JInt u), lt_BitSigned_BitUnsigned x y = decide (x.val < y.val)
theorem ltSignedUnsignedExact_proven : LtSignedUnsignedExact := by
  intro s u hs hu x y
  rw [lt_BitSigned_BitUnsigned, leUnsignedSigned_eq hu hs]
  by_cases h : x.val < y.val <;> simp [h] <;> omega

/-- `<=` between a signed and an unsigned BitInteger compares the integer values
(`base/int.jl:579`). -/
def LeSignedUnsignedExact : Prop := ∀ s u : IntTy, s.signed = true → u.signed = false →
  ∀ (x : JInt s) (y : JInt u), le_BitSigned_BitUnsigned x y = decide (x.val ≤ y.val)
theorem leSignedUnsignedExact_proven : LeSignedUnsignedExact := by
  intro s u hs hu x y
  rw [le_BitSigned_BitUnsigned, ltUnsignedSigned_eq hu hs]
  by_cases h : x.val ≤ y.val <;> simp [h] <;> omega

/-- `==`, `<` and `<=` from an unsigned to a signed BitInteger compare the integer values, for
any two sizes (`base/int.jl:581-589`). -/
def CmpUnsignedSignedExact : Prop := ∀ u s : IntTy, u.signed = false → s.signed = true →
  ∀ (x : JInt u) (y : JInt s),
    eq_BitUnsigned_BitSigned x y = decide (x.val = y.val) ∧
    lt_BitUnsigned_BitSigned x y = decide (x.val < y.val) ∧
    le_BitUnsigned_BitSigned x y = decide (x.val ≤ y.val)
theorem cmpUnsignedSignedExact_proven : CmpUnsignedSignedExact := by
  intro u s hu hs x y
  exact ⟨cmp_eq eqSame (· = ·) eqSame_eq (by intros; omega) hu hs x y,
    cmp_eq ltSame (· < ·) ltSame_eq (by intros; omega) hu hs x y,
    cmp_eq leSame (· ≤ ·) leSame_eq (by intros; omega) hu hs x y⟩

theorem lt_eq {s t : IntTy} (x : JInt s) (y : JInt t) : lt x y = decide (x.val < y.val) := by
  unfold lt
  split
  · exact ltPromote_eq (by assumption) x y
  · split
    · exact ltSignedUnsignedExact_proven s t (by assumption) (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y
    · exact cmp_eq ltSame (· < ·) ltSame_eq (by intros; omega)
        (by cases s <;> simp_all [IntTy.signed]) (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y

theorem le_eq {s t : IntTy} (x : JInt s) (y : JInt t) : le x y = decide (x.val ≤ y.val) := by
  unfold le
  split
  · exact lePromote_eq (by assumption) x y
  · split
    · exact leSignedUnsignedExact_proven s t (by assumption) (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y
    · exact cmp_eq leSame (· ≤ ·) leSame_eq (by intros; omega)
        (by cases s <;> simp_all [IntTy.signed]) (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y

theorem eq_eq {s t : IntTy} (x : JInt s) (y : JInt t) : eq x y = decide (x.val = y.val) := by
  unfold eq
  split
  · exact eqPromote_eq (by assumption) x y
  · split
    · exact eqSignedUnsignedExact_proven s t (by assumption) (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y
    · exact cmp_eq eqSame (· = ·) eqSame_eq (by intros; omega)
        (by cases s <;> simp_all [IntTy.signed]) (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y

/-- `==`, `<` and `<=` between any two BitIntegers, including mixed signedness and 128-bit
types, compare the integer values (`base/int.jl:84,573-589`, `promotion.jl:516-518`). -/
def IntCompareExact : Prop := ∀ (s t : IntTy) (x : JInt s) (y : JInt t),
  eq x y = decide (x.val = y.val) ∧ lt x y = decide (x.val < y.val) ∧ le x y = decide (x.val ≤ y.val)
theorem intCompareExact_proven : IntCompareExact := fun _ _ x y => ⟨eq_eq x y, lt_eq x y, le_eq x y⟩

/-! ## `max`, `min`, `minmax` (lines 591-599) -/

/-- `max(x, y)` of two BitIntegers is the larger integer value, exactly, in
`promote_type(S, T)` (`base/int.jl:591-594`). -/
def MaxExact : Prop := ∀ (s t : IntTy) (x : JInt s) (y : JInt t),
  (max_BitInteger x y).val = Max.max x.val y.val
theorem maxExact_proven : MaxExact := by
  intro s t x y
  have hx := x.property
  have hy := y.property
  simp only [max_BitInteger, ifelse, lt_eq]
  by_cases h : x.val < y.val
  · simp only [h, decide_true, ite_true, remT_val]
    rw [show Max.max x.val y.val = y.val by omega]
    cases s <;> cases t <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
      omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, remT_val]
    rw [show Max.max x.val y.val = x.val by omega]
    cases s <;> cases t <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
      omega

/-- `min(x, y)` of a signed and an unsigned BitInteger is the smaller integer value, exactly, in
the signed type (`base/int.jl:596`). -/
def MinSignedUnsignedExact : Prop := ∀ s u : IntTy, s.signed = true → u.signed = false →
  ∀ (x : JInt s) (y : JInt u), (min_BitSigned_BitUnsigned x y).val = Min.min x.val y.val
theorem minSignedUnsignedExact_proven : MinSignedUnsignedExact := by
  intro s u hs hu x y
  have hx := x.property
  have hy := y.property
  simp only [min_BitSigned_BitUnsigned, ifelse, lt_eq]
  by_cases h : x.val < y.val
  · simp only [h, decide_true, ite_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, remT_val]
    rw [show Min.min x.val y.val = y.val by omega]
    cases s <;> cases u <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;> omega

/-- `min(x, y)` of an unsigned and a signed BitInteger is the smaller integer value, exactly, in
the signed type (`base/int.jl:597`). -/
def MinUnsignedSignedExact : Prop := ∀ u s : IntTy, u.signed = false → s.signed = true →
  ∀ (x : JInt u) (y : JInt s), (min_BitUnsigned_BitSigned x y).val = Min.min x.val y.val
theorem minUnsignedSignedExact_proven : MinUnsignedSignedExact := by
  intro u s hu hs x y
  have hx := x.property
  have hy := y.property
  simp only [min_BitUnsigned_BitSigned, ifelse, lt_eq]
  by_cases h : x.val < y.val
  · simp only [h, decide_true, ite_true, remT_val]
    rw [show Min.min x.val y.val = x.val by omega]
    cases s <;> cases u <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;> omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]; omega

theorem jmin_val {s t : IntTy} (x : JInt s) (y : JInt t) : (jmin x y).val = Min.min x.val y.val := by
  have hx := x.property
  have hy := y.property
  unfold jmin
  split
  · rename_i h
    simp only [promoteSameSign, ifelse, ltSame_eq, widenTo_val, widen_promote_left h,
      widen_promote_right h, remT_val]
    by_cases hl : y.val < x.val
    · simp only [hl, decide_true, ite_true, widenTo_val, widen_promote_right h]
      rw [show Min.min x.val y.val = y.val by omega]
      cases s <;> cases t <;> simp_all [minType, IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min,
        IntTy.max, wrapInt] <;> omega
    · simp only [hl, decide_false, Bool.false_eq_true, ite_false, widenTo_val, widen_promote_left h]
      rw [show Min.min x.val y.val = x.val by omega]
      cases s <;> cases t <;> simp_all [minType, IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min,
        IntTy.max, wrapInt] <;> omega
  · split
    · rename_i h hs
      rw [remT_val, minSignedUnsignedExact_proven s t hs (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y]
      cases s <;> cases t <;> simp_all [minType, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
        omega
    · rename_i h hs
      rw [remT_val, minUnsignedSignedExact_proven s t (by cases s <;> simp_all [IntTy.signed])
        (by cases s <;> cases t <;> simp_all [IntTy.signed]) x y]
      cases s <;> cases t <;> simp_all [minType, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
        omega

theorem jmax_val {s t : IntTy} (x : JInt s) (y : JInt t) : (jmax x y).val = Max.max x.val y.val := by
  unfold jmax
  split
  · rename_i h
    subst h
    have hx := x.property
    have hy := y.property
    simp only [ifelse, lt_eq, remT_val]
    by_cases hl : y.val < x.val
    · simp only [hl, decide_true, ite_true]
      rw [show Max.max x.val y.val = x.val by omega]
      cases s <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;> omega
    · simp only [hl, decide_false, Bool.false_eq_true, ite_false, remT_val]
      rw [show Max.max x.val y.val = y.val by omega]
      cases s <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;> omega
  · exact maxExact_proven s t x y

/-- `minmax(x, y)` of two BitIntegers is `(min(x, y), max(x, y))` with the exact smaller and
larger integer values (`base/int.jl:599`). -/
def MinmaxExact : Prop := ∀ (s t : IntTy) (x : JInt s) (y : JInt t),
  (minmax_BitInteger x y).1.val = Min.min x.val y.val ∧ (minmax_BitInteger x y).2.val = Max.max x.val y.val
theorem minmaxExact_proven : MinmaxExact := fun _ _ x y => ⟨jmin_val x y, jmax_val x y⟩

/-- `min(x, y) + max(x, y) == x + y` and `min(x, y) <= max(x, y)` as integers, for any two
BitIntegers (`base/int.jl:591-599`). -/
def MinMaxSum : Prop := ∀ (s t : IntTy) (x : JInt s) (y : JInt t),
  (jmin x y).val + (jmax x y).val = x.val + y.val ∧ (jmin x y).val ≤ (jmax x y).val
theorem minMaxSum_proven : MinMaxSum := by
  intro s t x y
  rw [jmin_val, jmax_val]
  omega

/-! ## Promotion rules and type functions (lines 47-80, 806-822, 887-918) -/

/-- `signed(T)` for every BitInteger type `T` is a signed type of the same bit width, and `T`
itself when `T` is signed (`base/int.jl:74-79`, docstring of `signed(T::Integer)`). -/
def SignedTypeSameWidth : Prop := ∀ t : IntTy,
  (signedType t).signed = true ∧ (signedType t).bits = t.bits ∧ (t.signed = true → signedType t = t)
theorem signedTypeSameWidth_proven : SignedTypeSameWidth := by
  intro t; cases t <;> decide

/-- "Convert an integer bitstype to the signed type of the same size" (docstring of
`signed(T::Integer)`, `base/int.jl:61-71`), for `Bool` (`Core.sizeof(Bool) == 1`, line 73) and
every BitInteger type (lines 74-79). -/
def SignedTypeSameSize : Prop :=
  sizeofT signed_Type_Bool = 1 ∧ ∀ t : IntTy, sizeofT (signedType t) = sizeofT t
theorem signedTypeSameSize_refuted : ¬ SignedTypeSameSize := fun h => absurd h.1 (by decide)

/-- Integer promotion picks the wider type, and for equal widths and mixed signedness the
unsigned one (manual, "Conversion and Promotion"): for two distinct BitInteger types exactly one
of `promote_rule(T, S)` and `promote_rule(S, T)` is defined (`base/int.jl:806-822`), and it is
the type `IntTy.promote T S` in which the model's mixed-type methods return their results. -/
def PromotionRules : Prop := ∀ T S : IntTy, T ≠ S →
  (promote_rule T S).isSome = !(promote_rule S T).isSome ∧
  ∀ R, (promote_rule T S = some R ∨ promote_rule S T = some R) →
    R = IntTy.promote T S ∧ R.bits = Nat.max T.bits S.bits ∧
    R.signed = (if T.bits = S.bits then T.signed && S.signed
      else if S.bits < T.bits then T.signed else S.signed)
theorem promotionRules_proven : PromotionRules := by
  intro T S h
  cases T <;> cases S <;> simp only [ne_eq, not_true_eq_false] at h <;>
    refine ⟨by decide, fun R hR => ?_⟩ <;>
    simp only [promote_rule, promote_rule_Int16, promote_rule_Int32, promote_rule_Int64,
      promote_rule_Int128, promote_rule_UInt16, promote_rule_UInt32, promote_rule_UInt64,
      promote_rule_UInt128, promote_rule_UInt8_Int8, promote_rule_UInt16_Int16,
      promote_rule_UInt32_Int32, promote_rule_UInt64_Int64, promote_rule_UInt128_Int128,
      reduceCtorEq, Option.some.injEq, false_or, or_false] at hR <;>
    subst hR <;> decide

theorem typemin_le (t : IntTy) (x : JInt t) : (typemin t).val ≤ x.val := by
  rw [typemin_val]; exact x.property.1

theorem le_typemax (t : IntTy) (x : JInt t) : x.val ≤ (typemax t).val := by
  rw [typemax_val]; exact x.property.2

/-- `typemin(T) <= x <= typemax(T)` for every value `x` of a BitInteger type `T`, and both bounds
are the lowest and highest representable values (`base/int.jl:887-906`). -/
def IntegerBounds : Prop := ∀ (t : IntTy) (x : JInt t),
  (typemin t).val ≤ x.val ∧ x.val ≤ (typemax t).val ∧ (typemin t).val = t.min ∧ (typemax t).val = t.max
theorem integerBounds_proven : IntegerBounds :=
  fun t x => ⟨typemin_le t x, le_typemax t x, typemin_val t, typemax_val t⟩

theorem mul_natAbs_le {x y : Int} {a b : Nat} (hx : x.natAbs ≤ a) (hy : y.natAbs ≤ b) :
    (x * y).natAbs ≤ a * b := by
  rw [Int.natAbs_mul]; exact Nat.mul_le_mul hx hy

/-- The sum, difference and product of two values of `T` are representable in `widen(T)`, for a
type below 128 bits: the purpose of `widen` (docstring of `widen`, `operators.jl:955-962`), for
signed `T`. -/
def WidenSignedHolds (t w : IntTy) : Prop := ∀ x y : JInt t,
  fits w (x.val + y.val) ∧ fits w (x.val - y.val) ∧ fits w (x.val * y.val)
/-- The sum and product of two values of an unsigned `T` are representable in `widen(T)`. -/
def WidenUnsignedHolds (t w : IntTy) : Prop := ∀ x y : JInt t,
  fits w (x.val + y.val) ∧ fits w (x.val * y.val)

theorem widenSignedHolds_of {t w : IntTy} (m : Nat) (hm : (m : Int) = -t.min)
    (hb : t.max < m) (hw1 : w.min ≤ -((m * m : Nat) : Int)) (hw2 : ((m * m : Nat) : Int) ≤ w.max)
    (hw3 : w.min ≤ 2 * t.min) (hw4 : 2 * (m : Int) ≤ w.max) : WidenSignedHolds t w := by
  intro x y
  have hx := x.property
  have hy := y.property
  have hp := mul_natAbs_le (x := x.val) (y := y.val) (a := m) (b := m) (by omega) (by omega)
  unfold fits
  omega

theorem widenUnsignedHolds_of {t w : IntTy} (m : Nat) (h0 : t.min = 0) (hm : t.max = m)
    (hw0 : w.min = 0) (hw1 : ((m * m : Nat) : Int) ≤ w.max) (hw2 : 2 * (m : Int) ≤ w.max) :
    WidenUnsignedHolds t w := by
  intro x y
  have hx := x.property
  have hy := y.property
  have hp := mul_natAbs_le (x := x.val) (y := y.val) (a := m) (b := m) (by omega) (by omega)
  have hnn : 0 ≤ x.val * y.val := Int.mul_nonneg (by omega) (by omega)
  unfold fits
  omega

/-- `widen(Int8)` holds every sum, difference and product of two `Int8`s (`base/int.jl:911`). -/
def WidenInt8 : Prop := WidenSignedHolds .i8 widen_Int8
theorem widenInt8_proven : WidenInt8 := widenSignedHolds_of 128 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `widen(Int16)` holds every sum, difference and product of two `Int16`s (`base/int.jl:912`). -/
def WidenInt16 : Prop := WidenSignedHolds .i16 widen_Int16
theorem widenInt16_proven : WidenInt16 := widenSignedHolds_of 32768 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `widen(Int32)` holds every sum, difference and product of two `Int32`s (`base/int.jl:913`). -/
def WidenInt32 : Prop := WidenSignedHolds .i32 widen_Int32
theorem widenInt32_proven : WidenInt32 := widenSignedHolds_of 2147483648 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `widen(Int64)` holds every sum, difference and product of two `Int64`s (`base/int.jl:914`). -/
def WidenInt64 : Prop := WidenSignedHolds .i64 widen_Int64
theorem widenInt64_proven : WidenInt64 := widenSignedHolds_of 9223372036854775808 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `widen(UInt8)` holds every sum and product of two `UInt8`s (`base/int.jl:915`). -/
def WidenUInt8 : Prop := WidenUnsignedHolds .u8 widen_UInt8
theorem widenUInt8_proven : WidenUInt8 := widenUnsignedHolds_of 255 (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `widen(UInt16)` holds every sum and product of two `UInt16`s (`base/int.jl:916`). -/
def WidenUInt16 : Prop := WidenUnsignedHolds .u16 widen_UInt16
theorem widenUInt16_proven : WidenUInt16 := widenUnsignedHolds_of 65535 (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `widen(UInt32)` holds every sum and product of two `UInt32`s (`base/int.jl:917`). -/
def WidenUInt32 : Prop := WidenUnsignedHolds .u32 widen_UInt32
theorem widenUInt32_proven : WidenUInt32 := widenUnsignedHolds_of 4294967295 (by decide) (by decide) (by decide) (by decide) (by decide)
/-- `widen(UInt64)` holds every sum and product of two `UInt64`s (`base/int.jl:918`). -/
def WidenUInt64 : Prop := WidenUnsignedHolds .u64 widen_UInt64
theorem widenUInt64_proven : WidenUInt64 := widenUnsignedHolds_of 18446744073709551615 (by decide) (by decide) (by decide) (by decide) (by decide)

/-- After `widen`, the sum of two values of a BitInteger type below 128 bits is their exact
integer sum (`widen` docstring, `operators.jl:955-962`; `base/int.jl:88,911-918`). -/
def WidenAdditionNoLoss : Prop := ∀ t w : IntTy, widenType t = some w →
  ∀ widen : JInt t → JInt w, (∀ x, (widen x).val = x.val) → ∀ x y : JInt t,
    (add (widen x) (widen y)).val = x.val + y.val
theorem widenAdditionNoLoss_proven : WidenAdditionNoLoss := by
  intro t w hw widen hW x y
  have hx := x.property
  have hy := y.property
  rw [add, add_int_val, hW, hW]
  cases t <;> simp [widenType] at hw <;> subst hw <;>
    simp_all [widen_Int8, widen_Int16, widen_Int32, widen_Int64, widen_UInt8, widen_UInt16,
      widen_UInt32, widen_UInt64, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;> omega

/-! ## Promoted binary operations (lines 1092-1100) -/

/-- `+`, `-`, `*`, `+%`, `-%`, `*%` between BitIntegers of different types compute modulo `2^n`
in `promote_type` (issue #15489 comment, `base/int.jl:1092-1100`). -/
def PromotedArithmeticWraps : Prop := ∀ (s t : IntTy) (x : JInt s) (y : JInt t),
  let R := s.promote t
  (op_Integer R add (remT R) (remT R) x y).val = wrapInt R (x.val + y.val) ∧
  (op_Integer R sub (remT R) (remT R) x y).val = wrapInt R (x.val - y.val) ∧
  (op_Integer R mul (remT R) (remT R) x y).val = wrapInt R (x.val * y.val) ∧
  (op_Integer R addWrap (remT R) (remT R) x y).val = wrapInt R (x.val + y.val) ∧
  (op_Integer R subWrap (remT R) (remT R) x y).val = wrapInt R (x.val - y.val) ∧
  (op_Integer R mulWrap (remT R) (remT R) x y).val = wrapInt R (x.val * y.val)
theorem promotedArithmeticWraps_proven : PromotedArithmeticWraps := by
  intro s t x y
  simp only [op_Integer, add, sub, mul, addWrap, subWrap, mulWrap, add_int_val, sub_int_val,
    mul_int_val, remT_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [wrapInt_add_left, wrapInt_add_right, wrapInt_mul_left, wrapInt_mul_right,
      wrapInt_sub_left, wrapInt_sub_right]

/-! ## Bit patterns -/

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
  · rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_emod, hm] at hc
    omega
  · rw [hm] at hc
    omega

theorem val_eq_wrap_pattern {t : IntTy} (x : JInt t) : x.val = wrapInt t (pattern x) := by
  rw [← wrapInt_val x]
  apply wrapInt_congr
  rw [pattern_cast, Int.emod_emod]

theorem jint_eq_of_pattern {t : IntTy} {x y : JInt t} (h : pattern x = pattern y) : x = y :=
  jint_eq (by rw [val_eq_wrap_pattern x, val_eq_wrap_pattern y, h])

theorem bitOf_eq {t : IntTy} (x : JInt t) (k : Nat) : bitOf x k = (pattern x).testBit k := rfl

theorem jint_ext {t : IntTy} {x y : JInt t} (h : ∀ k, k < t.bits → bitOf x k = bitOf y k) : x = y := by
  apply jint_eq_of_pattern
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < t.bits
  · exact h i hi
  · have hle : 2 ^ t.bits ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (pattern_lt x) hle),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (pattern_lt y) hle)]

theorem bitOf_toJInt (t : IntTy) (b : BitVec t.bits) (k : Nat) : bitOf (toJInt t b) k = b.getLsbD k := by
  rw [bitOf_eq, pattern_toJInt, BitVec.testBit_toNat]

theorem getLsbD_fromJInt {t : IntTy} (x : JInt t) (k : Nat) : (fromJInt x).getLsbD k = bitOf x k := by
  rw [bitOf_eq, pattern_fromJInt, BitVec.testBit_toNat]

theorem val_bounds {t : IntTy} (x : JInt t) :
    -((2 ^ t.bits : Nat) : Int) < x.val ∧ x.val < ((2 ^ t.bits : Nat) : Int) := by
  have hx := x.property
  cases t <;> simp_all [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem pattern_of_nonneg {t : IntTy} (x : JInt t) (h : 0 ≤ x.val) : pattern x = x.val.toNat := by
  have hc := pattern_cast x
  rw [Int.emod_eq_of_lt h (val_bounds x).2] at hc
  omega

theorem pattern_of_cong {t : IntTy} (x : JInt t) (z : Int) (h : x.val = wrapInt t z) :
    pattern x = (z % ((2 ^ t.bits : Nat) : Int)).toNat := by
  unfold pattern
  rw [h, wrapInt_emod_self]

theorem toUnsigned_bits (t : IntTy) : t.toUnsigned.bits = t.bits := by cases t <;> rfl

theorem toSigned_bits (t : IntTy) : t.toSigned.bits = t.bits := by cases t <;> rfl

theorem pattern_unsigned {t : IntTy} (x : JInt t) : pattern (unsigned x) = pattern x := by
  rw [pattern_of_cong _ x.val (unsigned_val x), toUnsigned_bits]
  rfl

theorem pattern_signed {t : IntTy} (x : JInt t) : pattern (signed x) = pattern x := by
  rw [pattern_of_cong _ x.val (signed_val x), toSigned_bits]
  rfl

theorem val_of_unsigned_pattern {t : IntTy} (h : t.signed = false) (x : JInt t) : (pattern x : Int) = x.val := by
  have hx := x.property
  have h0 : 0 ≤ x.val := by
    have := hx.1
    cases t <;> simp_all [IntTy.signed, IntTy.min]
  rw [pattern_of_nonneg x h0]
  exact Int.toNat_of_nonneg h0

/-! ## Bitwise operations (lines 236, 381-433) -/

theorem bitOf_bnot {t : IntTy} (x : JInt t) {k : Nat} (hk : k < t.bits) : bitOf (bnot x) k = !bitOf x k := by
  simp only [bnot, not_int, jlNotInt, bitOf_toJInt, BitVec.getLsbD_not, getLsbD_fromJInt, hk,
    decide_true, Bool.true_and]

theorem bitOf_band {t : IntTy} (x y : JInt t) (k : Nat) : bitOf (band x y) k = (bitOf x k && bitOf y k) := by
  simp only [band, and_int, jlAndInt, bitOf_toJInt, BitVec.getLsbD_and, getLsbD_fromJInt]

theorem bitOf_bor {t : IntTy} (x y : JInt t) (k : Nat) : bitOf (bor x y) k = (bitOf x k || bitOf y k) := by
  simp only [bor, or_int, jlOrInt, bitOf_toJInt, BitVec.getLsbD_or, getLsbD_fromJInt]

theorem bitOf_bxor {t : IntTy} (x y : JInt t) (k : Nat) : bitOf (bxor x y) k = (bitOf x k ^^ bitOf y k) := by
  simp only [bxor, xor_int, jlXorInt, bitOf_toJInt, BitVec.getLsbD_xor, getLsbD_fromJInt]

theorem pattern_bnot {t : IntTy} (x : JInt t) : pattern (bnot x) = 2 ^ t.bits - 1 - pattern x := by
  simp only [bnot, not_int, jlNotInt, pattern_toJInt, BitVec.toNat_not, ← pattern_fromJInt]

theorem pattern_band {t : IntTy} (x y : JInt t) : pattern (band x y) = pattern x &&& pattern y := by
  simp only [band, and_int, jlAndInt, pattern_toJInt, BitVec.toNat_and, ← pattern_fromJInt]

theorem bnot_val {t : IntTy} (x : JInt t) : (bnot x).val = wrapInt t (-x.val - 1) := by
  rw [val_eq_wrap_pattern (bnot x)]
  apply wrapInt_congr
  have hc := pattern_cast x
  have hl := pattern_lt x
  rw [pattern_bnot]
  cases t <;> simp only [IntTy.bits, Nat.reducePow] at * <;> omega

/-- `~x`, `x & y`, `x | y` and `xor(x, y)` act bit by bit on the two's-complement representation,
and `~x == -x - 1` in `T`'s arithmetic (`base/int.jl:381,407,432,433`; docstring examples
`~4 == -5`, `4 & 10 == 0`, `4 | 10 == 14`). -/
def BitwiseOps : Prop := ∀ (t : IntTy) (x y : JInt t) (k : Nat), k < t.bits →
  bitOf (bnot x) k = !bitOf x k ∧ bitOf (band x y) k = (bitOf x k && bitOf y k) ∧
  bitOf (bor x y) k = (bitOf x k || bitOf y k) ∧ bitOf (bxor x y) k = (bitOf x k ^^ bitOf y k) ∧
  (bnot x).val = wrapInt t (-x.val - 1)
theorem bitwiseOps_proven : BitwiseOps := fun _ x y _ hk =>
  ⟨bitOf_bnot x hk, bitOf_band x y _, bitOf_bor x y _, bitOf_bxor x y _, bnot_val x⟩

theorem testBit_complement {n p k : Nat} (hp : p < 2 ^ n) (hk : k < n) :
    (2 ^ n - 1 - p).testBit k = !p.testBit k := by
  have h := BitVec.getLsbD_not (x := BitVec.ofNat n p) (i := k)
  rw [← BitVec.testBit_toNat, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    BitVec.getLsbD_ofNat] at h
  simpa [hk] using h

theorem neg_sub_one_emod (z M : Int) (hM : 0 < M) : (-z - 1) % M = M - 1 - z % M := by
  have hz := Int.emod_add_mul_ediv z M
  have h0 := Int.emod_nonneg z (by omega : M ≠ 0)
  have h1 := Int.emod_lt_of_pos z hM
  have : -z - 1 = (M - 1 - z % M) + M * (-(z / M) - 1) := by
    rw [Int.mul_sub, Int.mul_neg, Int.mul_one]
    omega
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

/-- The generic `~(n::Integer) = -n-1` (`base/int.jl:236`), reached by arbitrary-precision integers,
complements every bit of the two's-complement representation, at every width `n`. -/
def GenericComplementBits : Prop := ∀ (z : Int) (n k : Nat), k < n →
  bitOfInt n (bnot_Integer (fun a : Int => -a) (fun a b => a - b.val) z) k = !bitOfInt n z k
theorem genericComplementBits_proven : GenericComplementBits := by
  intro z n k hk
  have h1 : (lit IntTy.i64 1).val = 1 := by decide
  have hM := two_pow_pos_int n
  have h0 := Int.emod_nonneg z (by omega : ((2 ^ n : Nat) : Int) ≠ 0)
  have hl := Int.emod_lt_of_pos z hM
  simp only [bnot_Integer, bitOfInt, h1]
  rw [neg_sub_one_emod z _ hM]
  have hp : (z % ((2 ^ n : Nat) : Int)).toNat < 2 ^ n := by omega
  have : (((2 ^ n : Nat) : Int) - 1 - z % ((2 ^ n : Nat) : Int)).toNat =
      2 ^ n - 1 - (z % ((2 ^ n : Nat) : Int)).toNat := by omega
  rw [this, testBit_complement hp hk]

/-! ## Shift intrinsics -/

theorem pattern_shl_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (shl_int x y) = pattern x * 2 ^ pattern y % 2 ^ t.bits := by
  simp only [shl_int, jlShlInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 h) _)).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]

theorem pattern_lshr_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (lshr_int x y) = pattern x / 2 ^ pattern y := by
  simp only [lshr_int, jlLshrInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (pattern_lt x) (Nat.pow_le_pow_right (by decide) h))).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (pattern_lt x))

theorem shl_int_val {t u : IntTy} (x : JInt t) (y : JInt u) :
    (shl_int x y).val = wrapInt t (x.val * 2 ^ pattern y) := by
  rw [val_eq_wrap_pattern (shl_int x y), pattern_shl_int]
  apply wrapInt_congr
  have hp : ((pattern x : Nat) : Int) % 2 ^ t.bits = x.val % 2 ^ t.bits := by
    have := pattern_cast x
    push_cast at this
    rw [this, Int.emod_emod]
  push_cast
  rw [Int.emod_emod, Int.mul_emod, hp, ← Int.mul_emod]

theorem lshr_int_val {t u : IntTy} (x : JInt t) (y : JInt u) :
    (lshr_int x y).val = wrapInt t ((pattern x : Int) / 2 ^ pattern y) := by
  rw [val_eq_wrap_pattern (lshr_int x y), pattern_lshr_int]
  push_cast
  rfl

theorem ediv_bounds {t : IntTy} (x : JInt t) {D : Int} (hD : 0 < D) : t.min ≤ x.val / D ∧ x.val / D ≤ t.max := by
  have hx := x.property
  by_cases h0 : 0 ≤ x.val
  · have := Int.ediv_nonneg h0 (by omega : 0 ≤ D)
    have := Int.ediv_le_self D h0
    have : t.min ≤ 0 := by cases t <;> decide
    omega
  · have := Int.self_le_ediv_of_nonpos_of_nonneg (by omega : x.val ≤ 0) (by omega : 0 ≤ D)
    have h2 := Int.ediv_le_ediv hD (by omega : x.val ≤ 0)
    rw [Int.zero_ediv] at h2
    have : 0 ≤ t.max := by cases t <;> decide
    omega

theorem ashr_int_val {t u : IntTy} (h : t.signed = true) (x : JInt t) (y : JInt u) :
    (ashr_int x y).val = x.val / 2 ^ pattern y := by
  simp only [ashr_int, jlAshrInt, ← pattern_fromJInt, fromJInt_toInt x h]
  rw [toJInt_ofInt_val]
  have hx := x.property
  have hd : (0 : Int) < 2 ^ pattern y := Int.pow_pos (by decide)
  split
  · rename_i hq
    have hD : ((2 ^ t.bits : Nat) : Int) ≤ 2 ^ pattern y := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hq
      have h2 : ((2 ^ pattern y : Nat) : Int) = (2 : Int) ^ pattern y := by simp
      omega
    generalize (2 : Int) ^ pattern y = D at *
    split
    · rename_i hneg
      have hlo : 0 ≤ x.val + D := by
        cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.bits] <;> omega
      have hq1 : x.val / D = -1 :=
        ((Int.ediv_emod_unique (a := x.val) (r := x.val + D) (q := -1) hd).mpr
          ⟨by omega, hlo, by omega⟩).1
      rw [hq1]
      cases t <;> first | decide | simp [IntTy.signed] at h
    · rename_i hneg
      have hq0 : x.val / D = 0 := Int.ediv_eq_zero_of_lt (by omega) (by
        cases t <;> simp_all [IntTy.signed, IntTy.max, IntTy.bits] <;> omega)
      rw [hq0]
      cases t <;> decide
  · have h2 : ((2 ^ pattern y : Nat) : Int) = (2 : Int) ^ pattern y := by simp
    rw [h2]
    exact wrapInt_of_inRange t _ (ediv_bounds x hd)

/-! ## Shifts (lines 601-616) -/

theorem shrU_val {t u : IntTy} (x : JInt t) (y : JInt u) : (shrU x y).val = x.val / 2 ^ pattern y := by
  unfold shrU
  split
  · rename_i h
    exact ashr_int_val h x y
  · rename_i h
    have h' : t.signed = false := by simpa using h
    rw [shr_BitUnsigned_BitUnsigned, lshr_int_val, val_of_unsigned_pattern h' x]
    exact wrapInt_of_inRange t _ (ediv_bounds x (Int.pow_pos (by decide)))

theorem pattern_of_unsigned {u : IntTy} (h : u.signed = false) (y : JInt u) : pattern y = y.val.toNat := by
  have := val_of_unsigned_pattern h y
  omega

/-- With an unsigned shift count `k`, `x >> k` is `fld(x, 2^k)`, `x << k` is `x * 2^k` modulo `2^n`
and `x >>> k` shifts the unsigned bit pattern, `signed(unsigned(x) >> k)`; counts of at least the
bit width give `0` or `-1` (`base/int.jl:604-607`; docstrings of `>>`, `<<`, `>>>` in
`operators.jl`). -/
def ShiftUnsignedCount : Prop := ∀ (t u : IntTy), u.signed = false → ∀ (x : JInt t) (y : JInt u),
  (shrU x y).val = x.val / 2 ^ y.val.toNat ∧
  (shl_BitInteger_BitUnsigned x y).val = wrapInt t (x.val * 2 ^ y.val.toNat) ∧
  (lshr_BitInteger_BitUnsigned x y).val = wrapInt t ((pattern x : Int) / 2 ^ y.val.toNat)
theorem shiftUnsignedCount_proven : ShiftUnsignedCount := by
  intro t u hu x y
  rw [← pattern_of_unsigned hu y]
  exact ⟨shrU_val x y, shl_int_val x y, lshr_int_val x y⟩

theorem le_zero_eq (y : JInt .i64) : le_BitSigned (lit .i64 0) y = decide (0 ≤ y.val) := by
  have h0 : (lit IntTy.i64 0).val = 0 := by decide
  rw [le_BitSigned, sle_int_eq rfl, h0]

theorem pattern_unsigned_count (y : JInt .i64) (h : 0 ≤ y.val) : pattern (unsigned y) = y.val.toNat := by
  rw [pattern_unsigned, pattern_of_nonneg y h]

theorem pattern_unsigned_neg_count (y : JInt .i64) (h : ¬ 0 ≤ y.val) :
    pattern (unsigned (neg y)) = (-y.val).toNat := by
  rw [pattern_unsigned, pattern_of_cong (neg y) (-y.val) (neg_int_val y)]
  have hy : -9223372036854775808 ≤ y.val := y.property.1
  have hb : ((2 ^ IntTy.i64.bits : Nat) : Int) = 18446744073709551616 := by decide
  rw [hb, Int.emod_eq_of_lt (by omega) (by omega)]

/-- With a signed `Int` count `k`, `x >> k`, `x << k` and `x >>> k` shift as for an unsigned count
when `k >= 0` and shift the other way by `-k` when `k < 0`, including `k == typemin(Int)`
(`base/int.jl:611-616`; docstrings: "For n < 0, this is equivalent to x << -n"). -/
def ShiftIntCount : Prop := ∀ (t : IntTy) (x : JInt t) (y : JInt .i64),
  (shr_Int x y).val =
    (if 0 ≤ y.val then x.val / 2 ^ y.val.toNat else wrapInt t (x.val * 2 ^ (-y.val).toNat)) ∧
  (shl_Int x y).val =
    (if 0 ≤ y.val then wrapInt t (x.val * 2 ^ y.val.toNat) else x.val / 2 ^ (-y.val).toNat) ∧
  (lshr_Int x y).val =
    (if 0 ≤ y.val then wrapInt t ((pattern x : Int) / 2 ^ y.val.toNat)
      else wrapInt t (x.val * 2 ^ (-y.val).toNat))
theorem shiftIntCount_proven : ShiftIntCount := by
  intro t x y
  by_cases h : 0 ≤ y.val
  · simp only [shr_Int, shl_Int, lshr_Int, ifelse, le_zero_eq, decide_eq_true_eq, h, ite_true]
    rw [shrU_val, shl_BitInteger_BitUnsigned, shl_int_val, lshr_BitInteger_BitUnsigned, lshr_int_val,
      pattern_unsigned_count y h]
    exact ⟨rfl, rfl, rfl⟩
  · simp only [shr_Int, shl_Int, lshr_Int, ifelse, le_zero_eq, decide_eq_true_eq, h, ite_false]
    rw [shrU_val, shl_BitInteger_BitUnsigned, shl_int_val, pattern_unsigned_neg_count y h]
    exact ⟨rfl, rfl, rfl⟩

theorem pattern_shl_Int {t : IntTy} (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (shl_Int x c) = pattern x * 2 ^ c.val.toNat % 2 ^ t.bits := by
  simp only [shl_Int, ifelse, le_zero_eq, decide_eq_true_eq, h, ite_true, shl_BitInteger_BitUnsigned,
    pattern_shl_int, pattern_unsigned_count c h]

theorem pattern_lshr_Int {t : IntTy} (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (lshr_Int x c) = pattern x / 2 ^ c.val.toNat := by
  simp only [lshr_Int, ifelse, le_zero_eq, decide_eq_true_eq, h, ite_true, lshr_BitInteger_BitUnsigned,
    pattern_lshr_int, pattern_unsigned_count c h]

/-! ## Bit counts (lines 461-569) -/

theorem foldl_count (p : Nat) (l : List Nat) (acc : Nat) :
    l.foldl (fun r i => r + p / 2 ^ i % 2) acc = acc + l.countP (fun i => p.testBit i) := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    have : p / 2 ^ i % 2 = if p.testBit i then 1 else 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ i) with h | h <;> simp [h]
    rw [this]
    cases hb : p.testBit i <;> simp <;> omega

theorem countP_add_countP_not {l : List Nat} {p q : Nat → Bool} (h : ∀ k ∈ l, q k = !p k) :
    l.countP p + l.countP q = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, List.length_cons]
    have := ih (fun k hk => h k (List.mem_cons_of_mem a hk))
    rw [h a (by simp)]
    cases hp : p a <;> simp <;> omega

theorem onesCount_le {t : IntTy} (x : JInt t) : onesCount x ≤ t.bits := by
  unfold onesCount
  exact Nat.le_trans List.countP_le_length (by simp)

theorem onesCount_bnot {t : IntTy} (x : JInt t) : onesCount (bnot x) = t.bits - onesCount x := by
  have h := countP_add_countP_not (l := List.range t.bits) (p := fun k => bitOf x k)
    (q := fun k => bitOf (bnot x) k) (fun k hk => bitOf_bnot x (List.mem_range.mp hk))
  rw [List.length_range] at h
  unfold onesCount
  omega

theorem small_val {t : IntTy} (n : Nat) (h : n ≤ t.bits) :
    (remT .i64 (toJInt t (BitVec.ofNat t.bits n))).val = n := by
  rw [remT_val, toJInt_ofNat_val]
  cases t <;> simp only [IntTy.bits] at h <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem count_ones_val {t : IntTy} (x : JInt t) : (count_ones x).val = onesCount x := by
  unfold count_ones ctpop_int jlCtpopInt
  rw [← pattern_fromJInt, foldl_count, Nat.zero_add]
  exact small_val _ (onesCount_le x)

/-- `count_ones(x)` is the number of ones and `count_zeros(x)` the number of zeros in the `n`-bit
representation of `x` (`base/int.jl:475,517`; docstring example `count_ones(Int32(-1)) == 32`). -/
def CountOnesZeros : Prop := ∀ (t : IntTy) (x : JInt t),
  (count_ones x).val = onesCount x ∧
  (count_zeros_Integer count_ones bnot x).val = t.bits - onesCount x
theorem countOnesZeros_proven : CountOnesZeros := by
  intro t x
  refine ⟨count_ones_val x, ?_⟩
  rw [count_zeros_Integer, count_ones_val, onesCount_bnot]
  have := onesCount_le x
  omega

theorem leading_zeros_val {t : IntTy} (x : JInt t) :
    (leading_zeros x).val =
      ((if pattern x = 0 then t.bits else t.bits - (pattern x).log2 - 1 : Nat) : Int) := by
  unfold leading_zeros ctlz_int jlCtlzInt
  rw [← pattern_fromJInt]
  have hc : (if (pattern x == 0) = true then t.bits else t.bits - (pattern x).log2 - 1) =
      (if pattern x = 0 then t.bits else t.bits - (pattern x).log2 - 1) := by simp
  rw [hc]
  exact small_val _ (by split <;> omega)

theorem log2_lt_bits {t : IntTy} (x : JInt t) (h : pattern x ≠ 0) : (pattern x).log2 < t.bits :=
  (Nat.log2_lt h).mpr (pattern_lt x)

/-- `leading_zeros(x)` is the number `r` of zeros leading the `n`-bit representation of `x`: the
pattern fits in `n - r` bits and, unless `r == n`, not in `n - r - 1` (`base/int.jl:488`; docstring
example `leading_zeros(Int32(1)) == 31`). -/
def LeadingZeros : Prop := ∀ (t : IntTy) (x : JInt t),
  0 ≤ (leading_zeros x).val ∧ (leading_zeros x).val ≤ t.bits ∧
  pattern x < 2 ^ (t.bits - (leading_zeros x).val.toNat) ∧
  ((leading_zeros x).val < t.bits → 2 ^ (t.bits - (leading_zeros x).val.toNat - 1) ≤ pattern x)
theorem leadingZeros_proven : LeadingZeros := by
  intro t x
  rw [leading_zeros_val, Int.toNat_natCast]
  by_cases h : pattern x = 0
  · rw [if_pos h, Nat.sub_self, Nat.pow_zero]
    omega
  · rw [if_neg h]
    have hl := log2_lt_bits x h
    have e1 : t.bits - (t.bits - (pattern x).log2 - 1) = (pattern x).log2 + 1 := by omega
    rw [e1, Nat.add_sub_cancel]
    exact ⟨by omega, by omega, Nat.lt_log2_self, fun _ => Nat.log2_self_le h⟩

/-- `leading_ones(x)` is the number `r` of ones leading the `n`-bit representation of `x`
(`base/int.jl:530`; docstring example `leading_ones(UInt32(2^32 - 2)) == 31`). -/
def LeadingOnes : Prop := ∀ (t : IntTy) (x : JInt t),
  let r := (leading_ones_Integer leading_zeros bnot x).val
  0 ≤ r ∧ r ≤ t.bits ∧ 2 ^ t.bits - 2 ^ (t.bits - r.toNat) ≤ pattern x ∧
  (r < t.bits → pattern x < 2 ^ t.bits - 2 ^ (t.bits - r.toNat - 1))
theorem leadingOnes_proven : LeadingOnes := by
  intro t x
  have h := leadingZeros_proven t (bnot x)
  simp only [leading_ones_Integer]
  rw [pattern_bnot] at h
  generalize (leading_zeros (bnot x)).val = r at *
  have hp := pattern_lt x
  have hA : 2 ^ (t.bits - r.toNat) ≤ 2 ^ t.bits := Nat.pow_le_pow_right (by decide) (by omega)
  have hB : 1 ≤ 2 ^ (t.bits - r.toNat - 1) := Nat.one_le_two_pow
  have hC : 2 ^ (t.bits - r.toNat - 1) ≤ 2 ^ t.bits := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem trailing_zeros_val {t : IntTy} (x : JInt t) :
    (trailing_zeros x).val =
      (((List.range t.bits).find? (fun i => (pattern x).testBit i)).getD t.bits : Nat) := by
  unfold trailing_zeros cttz_int jlCttzInt
  rw [← pattern_fromJInt]
  have hf : (fun i => pattern x / 2 ^ i % 2 == 1) = (fun i => (pattern x).testBit i) := by
    funext i
    rw [Nat.testBit_eq_decide_div_mod_eq]
    cases h : (pattern x / 2 ^ i % 2 == 1) <;> simp_all
  rw [hf]
  apply small_val
  cases hc : (List.range t.bits).find? (fun i => (pattern x).testBit i) with
  | none => simp
  | some i =>
    simp only [Option.getD_some]
    exact Nat.le_of_lt (List.mem_range.mp (List.mem_of_find?_eq_some hc))

theorem trailing_spec {t : IntTy} (x : JInt t) :
    ((List.range t.bits).find? (fun i => (pattern x).testBit i)).getD t.bits ≤ t.bits ∧
    (∀ k, k < ((List.range t.bits).find? (fun i => (pattern x).testBit i)).getD t.bits →
      bitOf x k = false) ∧
    (((List.range t.bits).find? (fun i => (pattern x).testBit i)).getD t.bits < t.bits →
      bitOf x (((List.range t.bits).find? (fun i => (pattern x).testBit i)).getD t.bits) = true) := by
  cases hc : (List.range t.bits).find? (fun i => (pattern x).testBit i) with
  | none =>
    have h := List.find?_eq_none.mp hc
    simp only [Option.getD_none]
    refine ⟨Nat.le_refl _, fun k hk => ?_, fun h' => absurd h' (Nat.lt_irrefl _)⟩
    have := h k (List.mem_range.mpr hk)
    simpa [bitOf_eq] using this
  | some i =>
    have h := List.find?_range_eq_some.mp hc
    simp only [Option.getD_some]
    refine ⟨Nat.le_of_lt (List.mem_range.mp h.2.1), fun k hk => ?_, fun _ => h.1⟩
    have := h.2.2 k hk
    simpa [bitOf_eq] using this

/-- `trailing_zeros(x)` is the number `r` of zeros trailing the `n`-bit representation of `x`: bits
`0..r-1` are zero and bit `r` is one unless `r == n` (`base/int.jl:501`; docstring example
`trailing_zeros(2) == 1`). -/
def TrailingZeros : Prop := ∀ (t : IntTy) (x : JInt t),
  let r := (trailing_zeros x).val
  0 ≤ r ∧ r ≤ t.bits ∧ (∀ k : Nat, (k : Int) < r → bitOf x k = false) ∧
  (r < t.bits → bitOf x r.toNat = true)
theorem trailingZeros_proven : TrailingZeros := by
  intro t x
  simp only [trailing_zeros_val, Int.toNat_natCast]
  obtain ⟨h1, h2, h3⟩ := trailing_spec x
  exact ⟨by omega, by omega, fun k hk => h2 k (by omega), fun h => h3 (by omega)⟩

/-- `trailing_ones(x)` is the number `r` of ones trailing the `n`-bit representation of `x`
(`base/int.jl:543`; docstring example `trailing_ones(3) == 2`). -/
def TrailingOnes : Prop := ∀ (t : IntTy) (x : JInt t),
  let r := (trailing_ones_Integer trailing_zeros bnot x).val
  0 ≤ r ∧ r ≤ t.bits ∧ (∀ k : Nat, (k : Int) < r → bitOf x k = true) ∧
  (r < t.bits → bitOf x r.toNat = false)
theorem trailingOnes_proven : TrailingOnes := by
  intro t x
  obtain ⟨h0, h1, h2, h3⟩ := trailingZeros_proven t (bnot x)
  simp only [trailing_ones_Integer]
  refine ⟨h0, h1, fun k hk => ?_, fun h => ?_⟩
  · have := h2 k hk
    rw [bitOf_bnot x (by omega)] at this
    simpa using this
  · have := h3 h
    rw [bitOf_bnot x (by omega)] at this
    simpa using this

/-- `top_set_bit(x)` is the number of bits of `x`'s binary representation excluding leading zeros
(`base/int.jl:569`; docstring examples `top_set_bit(4) == 3`, `top_set_bit(0) == 0`,
`top_set_bit(-1) == 64`). -/
def TopSetBit : Prop := ∀ (t : IntTy) (x : JInt t),
  let r := (top_set_bit x).val
  0 ≤ r ∧ r ≤ t.bits ∧ pattern x < 2 ^ r.toNat ∧ (0 < r → 2 ^ (r.toNat - 1) ≤ pattern x)
theorem topSetBit_proven : TopSetBit := by
  intro t x
  have h8 : (mul (lit .i64 8) (sizeof x)).val = t.bits := by
    simp only [sizeof]
    cases t <;> decide
  simp only [top_set_bit]
  rw [sub, sub_int_val, h8, leading_zeros_val]
  by_cases h : pattern x = 0
  · rw [if_pos h]
    have : wrapInt IntTy.i64 ((t.bits : Int) - ((t.bits : Nat) : Int)) = 0 := by
      rw [Int.sub_self]; decide
    rw [this]
    simp [h]
  · rw [if_neg h]
    have hl := log2_lt_bits x h
    have : wrapInt IntTy.i64 ((t.bits : Int) - ((t.bits - (pattern x).log2 - 1 : Nat) : Int)) =
        ((pattern x).log2 + 1 : Nat) := by
      rw [wrapInt_of_inRange]
      · omega
      · have : t.bits ≤ 128 := by cases t <;> decide
        simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
        omega
    rw [this, Int.toNat_natCast]
    exact ⟨by omega, by omega, Nat.lt_log2_self, fun _ => by simpa using Nat.log2_self_le h⟩

/-! ## `bswap` and `bitreverse` (lines 435-459, 1106-1134) -/

/-- Byte `j` (from the least significant byte) of the natural number `z`. -/
def byteOf (z j : Nat) : Nat := z / 256 ^ j % 256

theorem foldl_bytes (b : Nat → Nat) (hb : ∀ i, b i < 256) (m : Nat) :
    (List.range m).foldl (fun r i => r * 256 + b i) 0 < 256 ^ m ∧
    ∀ j, j < m → byteOf ((List.range m).foldl (fun r i => r * 256 + b i) 0) j = b (m - 1 - j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hlt, hbyte⟩ := ih
    generalize (List.range m).foldl (fun r i => r * 256 + b i) 0 = F at hlt hbyte ⊢
    have hbm := hb m
    constructor
    · rw [Nat.pow_succ]
      generalize 256 ^ m = P at *
      omega
    · intro j hj
      cases j with
      | zero =>
        simp only [byteOf, Nat.pow_zero, Nat.div_one, Nat.add_sub_cancel, Nat.sub_zero]
        omega
      | succ j =>
        unfold byteOf
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul,
          show (F * 256 + b m) / 256 = F by omega]
        have := hbyte j (by omega)
        unfold byteOf at this
        rw [this]
        congr 1
        omega

theorem testBit_byteOf (p i j : Nat) (hi : i < 8) : (byteOf p j).testBit i = p.testBit (i + 8 * j) := by
  unfold byteOf
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, Nat.mul_comm 8 j, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  simp [hi, Nat.mul_comm j 8]

theorem bits_dvd8 (t : IntTy) : t.bits = 8 * (t.bits / 8) := by cases t <;> rfl

theorem pattern_bswap_wide {t : IntTy} (x : JInt t) (h : t.bits % 16 = 0) :
    pattern (bswap x) = (List.range (t.bits / 8)).foldl
      (fun r i => r * 256 + byteOf (pattern x) i) 0 := by
  have hb : ∀ i, byteOf (pattern x) i < 256 := fun i => Nat.mod_lt _ (by decide)
  have hlt := (foldl_bytes _ hb (t.bits / 8)).1
  have hpow : 256 ^ (t.bits / 8) = 2 ^ t.bits := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, ← bits_dvd8]
  unfold bswap
  rw [dif_pos h]
  unfold bswap_wide bswap_int
  have hok : jlBswapInt (fromJInt x) = .ok (BitVec.ofNat t.bits ((List.range (t.bits / 8)).foldl
      (fun r i => r * 256 + byteOf (pattern x) i) 0)) := by
    have hf : (fun r i => r * 256 + (fromJInt x).toNat / 2 ^ (8 * i) % 256) =
        (fun r i => r * 256 + byteOf (pattern x) i) := by
      funext r i
      rw [← pattern_fromJInt, byteOf, show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    simp only [jlBswapInt, h, hf] <;> rfl
  rw [okOf_eq hok, pattern_toJInt, BitVec.toNat_ofNat, ← hpow, Nat.mod_eq_of_lt hlt]

/-- `bswap(x)` reverses the byte order: byte `j` of the result is byte `n/8 - 1 - j` of `x`
(`base/int.jl:457-459`; docstring: "Reverse the byte order of `n`"). -/
def ByteSwap : Prop := ∀ (t : IntTy) (x : JInt t) (j : Nat), j < t.bits / 8 →
  byteOf (pattern (bswap x)) j = byteOf (pattern x) (t.bits / 8 - 1 - j)
theorem byteSwap_proven : ByteSwap := by
  intro t x j hj
  by_cases h : t.bits % 16 = 0
  · rw [pattern_bswap_wide x h]
    exact (foldl_bytes _ (fun i => Nat.mod_lt _ (by decide)) _).2 j hj
  · have h8 : t.bits = 8 := by cases t <;> simp_all [IntTy.bits]
    unfold bswap
    rw [dif_neg h, bswap_small]
    congr 1
    rw [h8] at hj ⊢
    omega

theorem bitOf_bswap {t : IntTy} (x : JInt t) (k : Nat) (hk : k < t.bits) :
    bitOf (bswap x) k = bitOf x (k % 8 + 8 * (t.bits / 8 - 1 - k / 8)) := by
  have hn := bits_dvd8 t
  rw [bitOf_eq, bitOf_eq]
  have e := testBit_byteOf (pattern (bswap x)) (k % 8) (k / 8) (Nat.mod_lt _ (by decide))
  rw [show k % 8 + 8 * (k / 8) = k by omega, byteSwap_proven t x (k / 8) (by omega),
    testBit_byteOf _ _ _ (Nat.mod_lt _ (by decide))] at e
  exact e.symm

theorem pattern_remT_same {t u : IntTy} (x : JInt u) (h : u.bits = t.bits) : pattern (remT t x) = pattern x := by
  rw [pattern_of_cong _ x.val (remT_val t x), ← h]
  rfl

theorem pattern_remT_narrow {t u : IntTy} (x : JInt u) (h : t.bits ≤ u.bits) :
    pattern (remT t x) = pattern x % 2 ^ t.bits := by
  rw [pattern_of_cong _ x.val (remT_val t x)]
  have hd : ((2 ^ t.bits : Nat) : Int) ∣ ((2 ^ u.bits : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
  have hc := pattern_cast x
  have hp : 0 ≤ x.val % ((2 ^ t.bits : Nat) : Int) := Int.emod_nonneg _ (by have := two_pow_pos_int t.bits; omega)
  have : ((pattern x % 2 ^ t.bits : Nat) : Int) = x.val % ((2 ^ t.bits : Nat) : Int) := by
    rw [Int.natCast_emod, hc, Int.emod_emod_of_dvd _ hd]
  omega

theorem mask1_pattern : pattern _mask1_uint128 = 0x55555555555555555555555555555555 := by decide
theorem mask2_pattern : pattern _mask2_uint128 = 0x33333333333333333333333333333333 := by decide
theorem mask4_pattern : pattern _mask4_uint128 = 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f := by decide

theorem mask1_bits : ∀ k, k < 128 → (0x55555555555555555555555555555555 : Nat).testBit k = decide (k % (2 * 1) < 1) := by
  decide
theorem mask2_bits : ∀ k, k < 128 → (0x33333333333333333333333333333333 : Nat).testBit k = decide (k % (2 * 2) < 2) := by
  decide
theorem mask4_bits : ∀ k, k < 128 → (0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Nat).testBit k = decide (k % (2 * 4) < 4) := by
  decide

theorem bitOf_mask {u : IntTy} (m : JInt .u128) (P : Nat) (hm : pattern m = P) (d : Nat)
    (hbits : ∀ k, k < 128 → P.testBit k = decide (k % (2 * d) < d)) (k : Nat) (hk : k < u.bits) :
    bitOf (remT u m) k = decide (k % (2 * d) < d) := by
  have hu : u.bits ≤ 128 := by cases u <;> decide
  rw [bitOf_eq, pattern_remT_narrow m hu, Nat.testBit_mod_two_pow, hm, hbits k (by omega)]
  simp [hk]

/-- Index map of one `bitreverse` stage: swap neighbouring blocks of `d` bits. -/
def swapIdx (d j : Nat) : Nat := if j % (2 * d) < d then j + d else j - d

theorem shr_Int_unsigned_pattern {u : IntTy} (hu : u.signed = false) (z : JInt u) (c : JInt .i64)
    (h : 0 ≤ c.val) : pattern (shr_Int z c) = pattern z / 2 ^ c.val.toNat := by
  simp only [shr_Int, ifelse, le_zero_eq, decide_eq_true_eq, h, ite_true, shrU, hu,
    Bool.false_eq_true, ite_false, shr_BitUnsigned_BitUnsigned, pattern_lshr_int,
    pattern_unsigned_count c h]

theorem swapIdx_cases (d j : Nat) :
    (j % (2 * d) < d ∧ swapIdx d j = j + d) ∨ (¬ j % (2 * d) < d ∧ swapIdx d j = j - d) := by
  unfold swapIdx
  split <;> simp_all

theorem bitOf_stage {u : IntTy} (hu : u.signed = false) (z m : JInt u) (c : JInt .i64) (d : Nat)
    (hcd : c.val = d) (hd : d = 1 ∨ d = 2 ∨ d = 4)
    (hm : ∀ k, k < u.bits → bitOf m k = decide (k % (2 * d) < d))
    (k : Nat) (hk : k < u.bits) :
    bitOf (bor (shl_Int (band z m) c) (band (shr_Int z c) m)) k = bitOf z (swapIdx d k) := by
  have hc0 : 0 ≤ c.val := by omega
  have hn := bits_dvd8 u
  rw [bitOf_bor, bitOf_band, bitOf_eq (shl_Int _ _), pattern_shl_Int _ _ hc0, hcd, Int.toNat_natCast,
    Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow, ← bitOf_eq, bitOf_band,
    bitOf_eq (shr_Int _ _), shr_Int_unsigned_pattern hu _ _ hc0, hcd, Int.toNat_natCast,
    Nat.testBit_div_two_pow, ← bitOf_eq, hm k hk]
  unfold swapIdx
  by_cases hc : k % (2 * d) < d
  · have hfalse : ¬ (d ≤ k ∧ (k - d) % (2 * d) < d) := by rcases hd with rfl | rfl | rfl <;> omega
    by_cases hdk : d ≤ k
    · rw [hm (k - d) (by omega)]
      have : ¬ (k - d) % (2 * d) < d := fun h => hfalse ⟨hdk, h⟩
      simp [hk, hdk, hc, this]
    · simp [hk, hdk, hc]
  · have hdk : d ≤ k := by rcases hd with rfl | rfl | rfl <;> omega
    have hk2 : (k - d) % (2 * d) < d := by rcases hd with rfl | rfl | rfl <;> omega
    rw [hm (k - d) (by omega)]
    simp [hk, hdk, hc, hk2]

theorem swapIdx_lt {n : Nat} (hn : n = 8 * (n / 8)) (d : Nat) (hd : d = 1 ∨ d = 2 ∨ d = 4)
    (j : Nat) (hj : j < n) : swapIdx d j < n := by
  have c := swapIdx_cases d j
  generalize swapIdx d j = a at *
  rcases hd with rfl | rfl | rfl <;> omega

theorem swapIdx_compose (j : Nat) :
    swapIdx 1 (swapIdx 2 (swapIdx 4 j)) = 8 * (j / 8) + 7 - j % 8 := by
  have c1 := swapIdx_cases 4 j
  generalize swapIdx 4 j = a at *
  have c2 := swapIdx_cases 2 a
  generalize swapIdx 2 a = b at *
  have c3 := swapIdx_cases 1 b
  generalize swapIdx 1 b = c at *
  omega

/-- `bitreverse(x)` reverses the order of the `n` bits of `x`: bit `k` of the result is bit
`n - 1 - k` of `x` (`base/int.jl:1124-1134`; docstring: "Reverse the order of bits in integer `x`"). -/
def BitReverse : Prop := ∀ (t : IntTy) (x : JInt t) (k : Nat), k < t.bits →
  bitOf (bitreverse x) k = bitOf x (t.bits - 1 - k)
theorem bitReverse_proven : BitReverse := by
  intro t x k hk
  have hu : t.toUnsigned.signed = false := by cases t <;> rfl
  have hub := toUnsigned_bits t
  have hn := bits_dvd8 t.toUnsigned
  have m1 := fun k (hk : k < t.toUnsigned.bits) =>
    bitOf_mask (u := t.toUnsigned) _ _ mask1_pattern 1 mask1_bits k hk
  have m2 := fun k (hk : k < t.toUnsigned.bits) =>
    bitOf_mask (u := t.toUnsigned) _ _ mask2_pattern 2 mask2_bits k hk
  have m4 := fun k (hk : k < t.toUnsigned.bits) =>
    bitOf_mask (u := t.toUnsigned) _ _ mask4_pattern 4 mask4_bits k hk
  simp only [bitreverse]
  rw [bitOf_eq, pattern_remT_same _ hub, ← bitOf_eq, bitOf_bswap _ _ (by omega)]
  generalize hj : k % 8 + 8 * (t.toUnsigned.bits / 8 - 1 - k / 8) = j
  have hjn : j < t.toUnsigned.bits := by omega
  rw [bitOf_stage hu _ _ (lit .i64 4) 4 (by decide) (by simp) m4 j hjn,
    bitOf_stage hu _ _ (lit .i64 2) 2 (by decide) (by simp) m2 _ (swapIdx_lt hn 4 (by simp) j hjn),
    bitOf_stage hu _ _ (lit .i64 1) 1 (by decide) (by simp) m1 _
      (swapIdx_lt hn 2 (by simp) _ (swapIdx_lt hn 4 (by simp) j hjn)),
    swapIdx_compose, bitOf_eq, pattern_unsigned, ← bitOf_eq]
  congr 1
  omega

/-! ## `bitrotate` (lines 636-665) -/

theorem i64_bounds (k : JInt .i64) : -9223372036854775808 ≤ k.val ∧ k.val ≤ 9223372036854775807 := by
  have h := k.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem rot_mask_val (t : IntTy) :
    (sub (shl_Int (lit .i64 (sizeofT t)) (lit .i64 3)) (lit .i64 1)).val = t.bits - 1 := by
  cases t <;> decide

theorem pattern_rot_count {t : IntTy} (k : JInt .i64) :
    pattern (band (sub (shl_Int (lit .i64 (sizeofT t)) (lit .i64 3)) (lit .i64 1)) k) =
      (k.val % (t.bits : Int)).toNat := by
  have hm := rot_mask_val t
  have hl : t.bits = 2 ^ t.bits.log2 := by cases t <;> decide
  have hn : 0 < t.bits := by cases t <;> decide
  have hpm : pattern (sub (shl_Int (lit .i64 (sizeofT t)) (lit .i64 3)) (lit .i64 1)) =
      2 ^ t.bits.log2 - 1 := by
    rw [pattern_of_nonneg _ (by rw [hm]; omega), hm, ← hl]
    omega
  rw [pattern_band, hpm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, ← hl]
  have hc := pattern_cast k
  have hk := i64_bounds k
  cases t <;> simp only [IntTy.bits, Nat.reducePow] at * <;> omega

/-- `bitrotate(x, k)` rotates the bits of `x` left `k` times, and right for negative `k`: bit `j` of
the result is bit `(j - k) mod n` of `x` (`base/int.jl:664-665`; docstring examples
`bitrotate(0b01110010, 2) == 0b11001001`, `bitrotate(0b01110010, -2) == 0b10011100`). -/
def BitRotate : Prop := ∀ (t : IntTy) (x : JInt t) (k : JInt .i64) (j : Nat), j < t.bits →
  bitOf (bitrotate band neg shl_Int lshr_Int x k) j =
    bitOf x ((j + t.bits - (k.val % t.bits).toNat) % t.bits)
theorem bitRotate_proven : BitRotate := by
  intro t x k j hj
  have hn : 0 < t.bits := by cases t <;> decide
  have ha := pattern_rot_count (t := t) k
  have hb := pattern_rot_count (t := t) (neg k)
  have hmod : ((neg k).val % (t.bits : Int)).toNat = (t.bits - (k.val % (t.bits : Int)).toNat) % t.bits := by
    rw [show (neg k).val = wrapInt .i64 (-k.val) from neg_int_val k]
    have hk := i64_bounds k
    cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega
  rw [hmod] at hb
  have haN : (k.val % (t.bits : Int)).toNat < t.bits := by
    have := Int.emod_lt_of_pos k.val (by omega : (0 : Int) < t.bits)
    have := Int.emod_nonneg k.val (by omega : (t.bits : Int) ≠ 0)
    omega
  simp only [bitrotate]
  generalize sub (shl_Int (lit .i64 (sizeofT t)) (lit .i64 3)) (lit .i64 1) = m at ha hb ⊢
  have hc1 : 0 ≤ (band m k).val := by
    rw [val_eq_wrap_pattern (band m k), ha]
    cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega
  have hc2 : 0 ≤ (band m (neg k)).val := by
    rw [val_eq_wrap_pattern (band m (neg k)), hb]
    cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega
  rw [bitOf_bor, bitOf_eq (shl_Int _ _), bitOf_eq (lshr_Int _ _), pattern_shl_Int _ _ hc1,
    pattern_lshr_Int _ _ hc2, ← pattern_of_nonneg _ hc1, ← pattern_of_nonneg _ hc2, ha, hb,
    Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow, bitOf_eq]
  generalize (k.val % (t.bits : Int)).toNat = a at haN ⊢
  have hp := pattern_lt x
  by_cases ha0 : a = 0
  · subst ha0
    have e1 : (t.bits - 0) % t.bits = 0 := by simp
    have e2 : (j + t.bits - 0) % t.bits = j := by
      rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    rw [e1, e2]
    simp [hj]
  · have e1 : (t.bits - a) % t.bits = t.bits - a := Nat.mod_eq_of_lt (by omega)
    rw [e1]
    by_cases hja : a ≤ j
    · have e2 : (j + t.bits - a) % t.bits = j - a := by
        rw [show j + t.bits - a = (j - a) + t.bits by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hf : (pattern x).testBit (j + (t.bits - a)) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [e2, hf]
      simp [hj, hja]
    · have e2 : (j + t.bits - a) % t.bits = j + (t.bits - a) := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [e2]
      simp [hja]

/-! ## Sign operations (lines 182-237) -/

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

theorem bits_le_promote_right (s t : IntTy) : t.bits ≤ (s.promote t).bits := by
  cases s <;> cases t <;> decide

theorem binop_eq (op : {r : IntTy} → JInt r → JInt r → JInt r) {s t : IntTy} (x : JInt s) (y : JInt t) :
    binop op x y = op (remT (s.promote t) x) (remT (s.promote t) y) := by
  unfold binop op_Integer
  split <;> rfl

theorem nonneg_of_unsigned {t : IntTy} (h : t.signed = false) (x : JInt t) : 0 ≤ x.val := by
  have hx := x.property
  cases t <;> simp_all [IntTy.signed, IntTy.min]

theorem neg_iff_top {t : IntTy} (h : t.signed = true) (x : JInt t) :
    x.val < 0 ↔ bitOf x (t.bits - 1) = true := by
  have hx := x.property
  rw [bitOf_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  unfold pattern
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

theorem bxor_neg_iff {t : IntTy} (h : t.signed = true) (a b : JInt t) :
    (bxor a b).val < 0 ↔ ¬ (a.val < 0 ↔ b.val < 0) := by
  rw [neg_iff_top h, neg_iff_top h, neg_iff_top h, bitOf_bxor]
  cases bitOf a (t.bits - 1) <;> cases bitOf b (t.bits - 1) <;> simp

theorem flipsign_val {s t : IntTy} (hs : s.signed = true) (ht : t.signed = true) (x : JInt s)
    (y : JInt t) : (flipsign x y).val = wrapInt s (if y.val < 0 then -x.val else x.val) := by
  unfold flipsign
  rw [if_pos ht]
  split
  · rename_i h
    subst h
    rw [flipsign_same, flipsign_int_val hs, remT_val, wrapInt_val]
  · simp only [flipsign_BitSigned, promoteSameSign, remT_val]
    rw [flipsign_int_val (promote_signed hs ht), widenTo_val, widenTo_val,
      widen_promote_left (by rw [hs, ht]) x, widen_promote_right (by rw [hs, ht]) y]
    exact wrapInt_narrow (bits_le_promote_left s t) _

theorem neg_ofBool_val (s : IntTy) (hs : s.signed = true) (b : Bool) :
    (neg (ofBool s b)).val = if b then -1 else 0 := by
  rw [neg, neg_int_val, ofBool, lit_val]
  cases b <;> cases s <;> simp_all [IntTy.signed] <;> decide

theorem flipsign_Real_val {s : IntTy} (hs : s.signed = true) {R : Type} (sb : R → Bool) (x : JInt s)
    (y : R) : (flipsign_Real sb x y).val = wrapInt s (if sb y then -x.val else x.val) := by
  rw [flipsign_Real, Generic.flipsign_Real, flipsign_same, flipsign_int_val hs, neg_ofBool_val s hs]
  cases sb y <;> simp

/-- `signbit(x)` is true exactly for negative integers, and an unsigned integer has neither a
sign bit nor a negative value (docstrings of `signbit` and `isnegative`;
`base/int.jl:183-185`). -/
def SignPredicates : Prop := ∀ (t : IntTy) (x : JInt t),
  signbit_Integer x = decide (x.val < 0) ∧
  (t.signed = false → signbit_Unsigned x = decide (x.val < 0) ∧
    isnegative_Unsigned x = decide (x.val < 0))
theorem signPredicates_proven : SignPredicates := by
  intro t x
  have h0 : (lit .i64 0).val = 0 := by decide
  refine ⟨by rw [signbit_Integer, Generic.signbit_Integer, lt_eq, h0], fun h => ?_⟩
  have hx := nonneg_of_unsigned h x
  simp [signbit_Unsigned, isnegative_Unsigned, Int.not_lt.mpr hx]

/-- `flipsign(x, y)` returns `x` with its sign flipped when `y` is negative, the negation
wrapping like all BitInteger arithmetic (`flipsign` docstring, `base/number.jl`), for a signed
`x` and every BitInteger `y` (`base/int.jl:188-190`, and line 194 through `signbit` for
unsigned `y`), and for every `y::Real` whose `signbit` is supplied (`base/int.jl:194`). -/
def FlipsignExact : Prop :=
  (∀ (s t : IntTy), s.signed = true → ∀ (x : JInt s) (y : JInt t),
    (flipsign x y).val = wrapInt s (if y.val < 0 then -x.val else x.val)) ∧
  (∀ (s : IntTy), s.signed = true → ∀ (R : Type) (signbit : R → Bool) (x : JInt s) (y : R),
    (flipsign_Real signbit x y).val = wrapInt s (if signbit y then -x.val else x.val))
theorem flipsignExact_proven : FlipsignExact := by
  refine ⟨fun s t hs x y => ?_, fun s hs R sb x y => flipsign_Real_val hs sb x y⟩
  cases ht : t.signed
  · have h0 : ¬ y.val < 0 := Int.not_lt.mpr (nonneg_of_unsigned ht y)
    simp only [flipsign, ht, Bool.false_eq_true, ite_false]
    rw [flipsign_Real_val hs]
    simp [signbit_Unsigned, h0]
  · exact flipsign_val hs ht x y

theorem bitcastFloat_neg (T : IntTy) {f : Fmt} (y : Fl f) (hw : f.width = T.bits)
    (hT : T.signed = true) : (bitcastFloat T y).val < 0 ↔ 2 ^ (T.bits - 1) ≤ y.toBits := by
  have hy : y.toBits < 2 ^ T.bits := by rw [← hw]; exact y.bits.isLt
  rw [bitcastFloat, jlBitcast, toJInt_ofNat_val]
  cases T <;> simp_all [wrapInt, IntTy.signed, IntTy.bits] <;> omega

/-- `flipsign(x, y)` for a float `y` flips `x` exactly when the sign bit of `y`'s IEEE
representation is set, including `-0.0` and NaNs with the sign bit (`base/int.jl:191-193`). -/
def FlipsignFloat : Prop := ∀ (s : IntTy), s.signed = true →
  ∀ (x : JInt s) (a : Fl half) (b : Fl single) (c : Fl double),
  (flipsign_Float16 x a).val = wrapInt s (if 2 ^ 15 ≤ a.toBits then -x.val else x.val) ∧
  (flipsign_Float32 x b).val = wrapInt s (if 2 ^ 31 ≤ b.toBits then -x.val else x.val) ∧
  (flipsign_Float64 x c).val = wrapInt s (if 2 ^ 63 ≤ c.toBits then -x.val else x.val)
theorem flipsignFloat_proven : FlipsignFloat := by
  intro s hs x a b c
  refine ⟨?_, ?_, ?_⟩
  · simp only [flipsign_Float16, flipsign_val hs (rfl : IntTy.i16.signed = true),
      bitcastFloat_neg .i16 a (by decide) rfl]
    rfl
  · simp only [flipsign_Float32, flipsign_val hs (rfl : IntTy.i32.signed = true),
      bitcastFloat_neg .i32 b (by decide) rfl]
    rfl
  · simp only [flipsign_Float64, flipsign_val hs (rfl : IntTy.i64.signed = true),
      bitcastFloat_neg .i64 c (by decide) rfl]
    rfl

theorem copysign_Signed_val {s t : IntTy} (hs : s.signed = true) (ht : t.signed = true) (x : JInt s)
    (y : JInt t) : (copysign_Signed x y).val =
      wrapInt s (if y.val < 0 then -(x.val.natAbs : Int) else x.val.natAbs) := by
  have hP := promote_signed hs ht
  simp only [copysign_Signed, flipsign_val hs hP, binop_eq, bxor_neg_iff hP, remT_val,
    widen_promote_left (show s.signed = t.signed by rw [hs, ht]) x,
    widen_promote_right (show s.signed = t.signed by rw [hs, ht]) y]
  by_cases hx : x.val < 0 <;> by_cases hy : y.val < 0 <;> simp [hx, hy] <;> congr 1 <;> omega

theorem copysign_Real_val {s : IntTy} (hs : s.signed = true) {R : Type} (sb : R → Bool) (x : JInt s)
    (y : R) : (copysign_Real sb x y).val =
      wrapInt s (if sb y then -(x.val.natAbs : Int) else x.val.natAbs) := by
  rw [copysign_Real, copysign_Signed_val hs hs, neg_ofBool_val s hs]
  cases sb y <;> simp

/-- `copysign(x, y)` has the magnitude of `x` and the sign of `y`, the negation wrapping
(`copysign` docstring, `base/number.jl`), for a signed `x` and every BitInteger `y`
(`base/int.jl:196`, and line 200 through `signbit` for unsigned `y`), and for every `y::Real`
whose `signbit` is supplied (`base/int.jl:200`). -/
def CopysignExact : Prop :=
  (∀ (s t : IntTy), s.signed = true → ∀ (x : JInt s) (y : JInt t),
    (copysign x y).val = wrapInt s (if y.val < 0 then -(x.val.natAbs : Int) else x.val.natAbs)) ∧
  (∀ (s : IntTy), s.signed = true → ∀ (R : Type) (signbit : R → Bool) (x : JInt s) (y : R),
    (copysign_Real signbit x y).val =
      wrapInt s (if signbit y then -(x.val.natAbs : Int) else x.val.natAbs))
theorem copysignExact_proven : CopysignExact := by
  refine ⟨fun s t hs x y => ?_, fun s hs R sb x y => copysign_Real_val hs sb x y⟩
  cases ht : t.signed
  · have h0 : ¬ y.val < 0 := Int.not_lt.mpr (nonneg_of_unsigned ht y)
    simp only [copysign, ht, Bool.false_eq_true, ite_false]
    rw [copysign_Real_val hs]
    simp [signbit_Unsigned, h0]
  · simp only [copysign, ht, ite_true]
    exact copysign_Signed_val hs ht x y

/-- `copysign(x, y)` for a float `y` gives `x` the sign of `y`'s IEEE sign bit
(`base/int.jl:197-199`). -/
def CopysignFloat : Prop := ∀ (s : IntTy), s.signed = true →
  ∀ (x : JInt s) (a : Fl half) (b : Fl single) (c : Fl double),
  (copysign_Float16 x a).val =
    wrapInt s (if 2 ^ 15 ≤ a.toBits then -(x.val.natAbs : Int) else x.val.natAbs) ∧
  (copysign_Float32 x b).val =
    wrapInt s (if 2 ^ 31 ≤ b.toBits then -(x.val.natAbs : Int) else x.val.natAbs) ∧
  (copysign_Float64 x c).val =
    wrapInt s (if 2 ^ 63 ≤ c.toBits then -(x.val.natAbs : Int) else x.val.natAbs)
theorem copysignFloat_proven : CopysignFloat := by
  intro s hs x a b c
  refine ⟨?_, ?_, ?_⟩
  · simp only [copysign_Float16, copysign]
    rw [if_pos (show IntTy.i16.signed = true from rfl), copysign_Signed_val hs rfl]
    simp only [bitcastFloat_neg .i16 a (by decide) rfl]
    rfl
  · simp only [copysign_Float32, copysign]
    rw [if_pos (show IntTy.i32.signed = true from rfl), copysign_Signed_val hs rfl]
    simp only [bitcastFloat_neg .i32 b (by decide) rfl]
    rfl
  · simp only [copysign_Float64, copysign]
    rw [if_pos (show IntTy.i64.signed = true from rfl), copysign_Signed_val hs rfl]
    simp only [bitcastFloat_neg .i64 c (by decide) rfl]
    rfl

/-- `copysign(x, y)` has the magnitude of `x` and the sign of `y` for all nonzero signed `x` and
`y` (`copysign` docstring, `base/number.jl:260`: "Return `z` which has the magnitude of `x` and
the same sign as `y`"; `base/int.jl:196`). Refuted: `copysign(typemin(Int64), 1)` is negative. -/
def CopysignMagnitudeSign : Prop := ∀ (s t : IntTy), s.signed = true → t.signed = true →
  ∀ (x : JInt s) (y : JInt t), x.val ≠ 0 → y.val ≠ 0 →
    (copysign x y).val.natAbs = x.val.natAbs ∧ ((copysign x y).val < 0 ↔ y.val < 0)
theorem copysignMagnitudeSign_refuted : ¬ CopysignMagnitudeSign := by
  intro h
  have h1 := (h .i64 .i64 rfl rfl (lit .i64 (-9223372036854775808)) (lit .i64 1) (by decide)
    (by decide)).2
  rw [copysignExact_proven.1 .i64 .i64 rfl] at h1
  revert h1
  decide

theorem abs_val {t : IntTy} (x : JInt t) :
    (abs x).val = if t.signed = true ∧ x.val = t.min then t.min else (x.val.natAbs : Int) := by
  have hx := x.property
  cases h : t.signed
  · have h0 := nonneg_of_unsigned h x
    simp only [abs, h, Bool.false_eq_true, ite_false, abs_Unsigned, Generic.abs_Unsigned, false_and]
    omega
  · simp only [abs, h, ite_true, abs_Signed, flipsign_same, flipsign_int_val h, true_and]
    by_cases hn : x.val < 0 <;> by_cases hm : x.val = t.min <;> simp only [hn, hm, ite_true, ite_false] <;>
      cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;> omega

/-- `abs(x)` is the absolute value of `x`, except that for a signed type
`abs(typemin(T)) == typemin(T) < 0`, the only negative result (`abs` docstring;
`base/int.jl:202-235`). -/
def AbsExact : Prop := ∀ (t : IntTy) (x : JInt t),
  (abs x).val = (if t.signed = true ∧ x.val = t.min then t.min else (x.val.natAbs : Int)) ∧
  ((abs x).val < 0 ↔ t.signed = true ∧ x.val = t.min)
theorem absExact_proven : AbsExact := by
  intro t x
  refine ⟨abs_val x, ?_⟩
  rw [abs_val]
  by_cases hc : t.signed = true ∧ x.val = t.min
  · have : t.min < 0 := by cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.bits]
    simp only [hc, and_self, ite_true, iff_true]
    exact this
  · simp only [hc, ite_false, iff_false]
    omega

/-! ## Same-type `div`, `rem` and `mod` (lines 292-358, 1082-1090) -/

theorem checked_srem_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    checked_srem_int x y =
      if y.val = 0 then .error .divideError else .ok (lit t (x.val.tmod y.val)) := by
  have hx := x.property
  have hy := y.property
  have hmin : -((2 ^ (t.bits - 1) : Nat) : Int) = t.min := by
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.bits]
  unfold checked_srem_int jlCheckedSremInt integerDivide
  simp only [Bool.true_or, ite_true, fromJInt_toInt x h, fromJInt_toInt y h, hmin]
  by_cases h0 : y.val = 0
  · simp [h0, divideResult, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
  · by_cases h1 : x.val = t.min ∧ y.val = -1
    · simp [h0, h1, divideResult, pure, Except.pure]
      apply jint_eq
      rw [toJInt_ofNat_val, lit_val]
      simp
    · simp [h0, h1, divideResult, pure, Except.pure]
      apply jint_eq
      rw [toJInt_ofInt_val, lit_val]

theorem checked_udiv_int_eq {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    checked_udiv_int x y =
      if y.val = 0 then .error .divideError else .ok (lit t (x.val.tdiv y.val)) := by
  have hx := fromJInt_toNat_unsigned x h
  have hy := fromJInt_toNat_unsigned y h
  unfold checked_udiv_int jlCheckedUdivInt integerDivide
  simp only [Bool.true_or, ite_true, Bool.false_eq_true, ite_false, Bool.false_and, hx, hy]
  by_cases h0 : y.val = 0
  · simp [h0, divideResult, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
  · simp [h0, divideResult, pure, Except.pure]
    apply jint_eq
    rw [toJInt_ofInt_val, lit_val]

theorem checked_urem_int_eq {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    checked_urem_int x y =
      if y.val = 0 then .error .divideError else .ok (lit t (x.val.tmod y.val)) := by
  have hx := fromJInt_toNat_unsigned x h
  have hy := fromJInt_toNat_unsigned y h
  unfold checked_urem_int jlCheckedUremInt integerDivide
  simp only [Bool.true_or, ite_true, Bool.false_eq_true, ite_false, Bool.false_and, hx, hy]
  by_cases h0 : y.val = 0
  · simp [h0, divideResult, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
  · simp [h0, divideResult, pure, Except.pure]
    apply jint_eq
    rw [toJInt_ofInt_val, lit_val]

theorem divSame_eq {t : IntTy} (x y : JInt t) :
    divSame x y = if y.val = 0 ∨ (t.signed = true ∧ x.val = t.min ∧ y.val = -1)
      then .error .divideError else .ok (lit t (x.val.tdiv y.val)) := by
  cases t <;> simp only [divSame, div_BitSigned64, div_BitUnsigned64, div_Int128, div_UInt128] <;>
    first
    | (rw [checked_sdiv_int_eq rfl]; simp [IntTy.signed])
    | (rw [checked_udiv_int_eq rfl]; simp [IntTy.signed])

theorem remSame_eq {t : IntTy} (x y : JInt t) :
    remSame x y = if y.val = 0 then .error .divideError else .ok (lit t (x.val.tmod y.val)) := by
  cases t <;> simp only [remSame, rem_BitSigned64, rem_BitUnsigned64, rem_Int128, rem_UInt128] <;>
    first
    | exact checked_srem_int_eq rfl x y
    | exact checked_urem_int_eq rfl x y

theorem tmod_between (a b : Int) :
    (0 ≤ a → 0 ≤ a.tmod b ∧ a.tmod b ≤ a) ∧ (a < 0 → a ≤ a.tmod b ∧ a.tmod b ≤ 0) := by
  have hn := Int.natAbs_tmod a b
  have hle : a.natAbs % b.natAbs ≤ a.natAbs := Nat.mod_le _ _
  generalize a.natAbs % b.natAbs = m at hn hle
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · have := Int.tmod_nonneg b ha
    omega
  · have h2 : (-a).tmod b = -(a.tmod b) := Int.neg_tmod a b
    have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
    omega

theorem tmod_fits {t : IntTy} (x y : JInt t) : fits t (x.val.tmod y.val) := by
  have hx := x.property
  have hb := tmod_between x.val y.val
  generalize x.val.tmod y.val = r at hb ⊢
  unfold fits
  by_cases h : 0 ≤ x.val
  · have := hb.1 h
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
  · have := hb.2 (by omega)
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega

theorem tdiv_fits {t : IntTy} (x y : JInt t) (h0 : y.val ≠ 0)
    (h1 : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1)) : fits t (x.val.tdiv y.val) := by
  have hx := x.property
  have hy := y.property
  by_cases hy1 : y.val.natAbs = 1
  · have : y.val = 1 ∨ y.val = -1 := by omega
    rcases this with h | h
    · rw [h, Int.tdiv_one]; exact hx
    · rw [h, Int.tdiv_neg, Int.tdiv_one]
      unfold fits
      cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
  · have h2 : 2 ≤ y.val.natAbs := by omega
    have hq : (x.val.tdiv y.val).natAbs ≤ x.val.natAbs / 2 := by
      rw [Int.natAbs_tdiv]; exact Nat.div_le_div_left h2 (by decide)
    have hs : t.signed = false → 0 ≤ x.val.tdiv y.val := fun hu =>
      Int.tdiv_nonneg (nonneg_of_unsigned hu x) (nonneg_of_unsigned hu y)
    generalize x.val.tdiv y.val = q at hq hs ⊢
    unfold fits
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega

theorem lit_of_fits {t : IntTy} {z : Int} (h : fits t z) : (lit t z).val = z := by
  rw [lit_val]; exact wrapInt_of_inRange t z h

/-- `div(x, y)` is the quotient truncated toward zero and `rem(x, y)` the remainder of that
division, which has the sign of `x` and magnitude below `|y|` (docstrings of `div` and `rem`);
`div` throws `DivideError` exactly when `y == 0` or `x == typemin(T)` and `y == -1`, and `rem`
exactly when `y == 0` (manual, "Integers and Floating-Point Numbers", Division errors); for
every BitInteger type (`base/int.jl:355-358,1085-1089`). -/
def DivRemSame : Prop := ∀ (t : IntTy) (x y : JInt t),
  (divSame x y = .error .divideError ↔
    (y.val = 0 ∨ (t.signed = true ∧ x.val = t.min ∧ y.val = -1))) ∧
  (∀ q, divSame x y = .ok q ↔
    (y.val ≠ 0 ∧ ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) ∧ q.val = x.val.tdiv y.val)) ∧
  (remSame x y = .error .divideError ↔ y.val = 0) ∧
  (∀ r, remSame x y = .ok r ↔ (y.val ≠ 0 ∧ r.val = x.val.tmod y.val))
theorem divRemSame_proven : DivRemSame := by
  intro t x y
  rw [divSame_eq, remSame_eq]
  refine ⟨?_, fun q => ?_, ?_, fun r => ?_⟩
  · by_cases hc : y.val = 0 ∨ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) <;> simp [hc]
  · by_cases hc : y.val = 0 ∨ (t.signed = true ∧ x.val = t.min ∧ y.val = -1)
    · simp only [hc, ite_true, reduceCtorEq, false_iff]
      intro ⟨a, b, _⟩
      rcases hc with hc | hc
      · exact a hc
      · exact b hc
    · simp only [hc, ite_false, Except.ok.injEq]
      have hn : ¬ y.val = 0 := fun h => hc (Or.inl h)
      have hm : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) := fun h => hc (Or.inr h)
      have hv := lit_of_fits (tdiv_fits x y hn hm)
      constructor
      · intro he; subst he; exact ⟨hn, hm, hv⟩
      · intro ⟨_, _, he⟩; exact jint_eq (by rw [hv, he])
  · by_cases hc : y.val = 0 <;> simp [hc]
  · by_cases hc : y.val = 0
    · simp [hc]
    · simp only [hc, ite_false, Except.ok.injEq]
      have hv := lit_of_fits (tmod_fits x y)
      constructor
      · intro he; subst he; exact ⟨hc, hv⟩
      · intro ⟨_, he⟩; exact jint_eq (by rw [hv, he])

theorem fmod_bounds (a b : Int) (hb : b ≠ 0) :
    (0 < b → 0 ≤ a.fmod b ∧ a.fmod b < b) ∧ (b < 0 → b < a.fmod b ∧ a.fmod b ≤ 0) := by
  refine ⟨fun h => ⟨Int.fmod_nonneg_of_pos a h, Int.fmod_lt_of_pos a h⟩, fun h => ?_⟩
  have e := Int.neg_fmod_neg (-a) (-b)
  rw [Int.neg_neg, Int.neg_neg] at e
  have h1 := Int.fmod_nonneg_of_pos (-a) (show 0 < -b by omega)
  have h2 := Int.fmod_lt_of_pos (-a) (show 0 < -b by omega)
  omega

theorem fmod_fits {t : IntTy} (x y : JInt t) (hy : y.val ≠ 0) : fits t (x.val.fmod y.val) := by
  have hb := fmod_bounds x.val y.val hy
  have h := y.property
  generalize x.val.fmod y.val = r at hb ⊢
  unfold fits
  by_cases hp : 0 < y.val
  · have := hb.1 hp
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
  · have := hb.2 (by omega)
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega

/-- `mod(x, y)` on an unsigned type is the floored remainder `x - y*fld(x, y)`, nonnegative and
below `y`, and throws `DivideError` exactly when `y == 0` (`mod` docstring;
`base/int.jl:351`). -/
def ModUnsigned : Prop := ∀ (t : IntTy), t.signed = false → ∀ x y : JInt t,
  (mod_Unsigned x y = .error .divideError ↔ y.val = 0) ∧
  (∀ r, mod_Unsigned x y = .ok r ↔ (y.val ≠ 0 ∧ r.val = x.val.fmod y.val))
theorem modUnsigned_proven : ModUnsigned := by
  intro t ht x y
  have he : x.val.fmod y.val = x.val.tmod y.val :=
    Int.fmod_eq_tmod_of_nonneg (nonneg_of_unsigned ht x) (nonneg_of_unsigned ht y)
  have h := (divRemSame_proven t x y).2.2
  simp only [mod_Unsigned, he]
  exact h

/-- What `mod` needs from `fld(x, y)` (`base/div.jl`, a later file): the floored quotient
(`fld` docstring), and `DivideError` for a zero divisor. -/
def FldSpec {t : IntTy} (fld : JInt t → JInt t → Jl (JInt t)) : Prop :=
  ∀ a b : JInt t, b.val ≠ -1 →
    fld a b = if b.val = 0 then .error .divideError else .ok (lit t (a.val.fdiv b.val))

/-- `mod(x, y)` on a signed type is the floored remainder `x - y*fld(x, y)` computed without
intermediate overflow, with the sign of `y` and magnitude below `|y|` (`mod` docstring),
including `mod(typemin(T), -1) == 0`, and throws `DivideError` exactly when `y == 0`; for every
`fld` (`base/div.jl`) with its documented behaviour (`base/int.jl:338-341`). The generic method of
lines 331-334, with BitInteger `==`, `-` and `*`, computes the same for every BitInteger type. -/
def ModSigned : Prop :=
  (∀ (t : IntTy), t.signed = true → ∀ (fld : JInt t → JInt t → Jl (JInt t)), FldSpec fld →
    ∀ x y : JInt t,
    (mod_BitSigned fld x y = .error .divideError ↔ y.val = 0) ∧
    (∀ r, mod_BitSigned fld x y = .ok r ↔ (y.val ≠ 0 ∧ r.val = x.val.fmod y.val))) ∧
  (∀ (t : IntTy) (fld : JInt t → JInt t → Jl (JInt t)), FldSpec fld → ∀ x y : JInt t,
    (mod_Integer (fun y => eq y (lit .i64 (-1))) (lit t 0) fld sub mul x y = .error .divideError ↔
      y.val = 0) ∧
    (∀ r, mod_Integer (fun y => eq y (lit .i64 (-1))) (lit t 0) fld sub mul x y = .ok r ↔
      (y.val ≠ 0 ∧ r.val = x.val.fmod y.val)))
theorem modSigned_proven : ModSigned := by
  refine ⟨fun t ht fld hfld x y => ?_, fun t fld hfld x y => ?_⟩
  · have hm1 : (lit IntTy.i64 (-1)).val = -1 := by decide
    have hfm : x.val.fmod (-1) = 0 := by
      have e := Int.neg_fmod_neg (-x.val) 1
      rw [Int.neg_neg, Int.fmod_one] at e
      omega
    by_cases h1 : y.val = -1
    · have hl : (lit t 0).val = 0 := by rw [lit_val]; cases t <;> rfl
      have hm : mod_BitSigned fld x y = .ok (lit t 0) := by
        unfold mod_BitSigned; rw [eq_eq, hm1]; simp [h1, pure, Except.pure]
      rw [hm, h1, hfm]
      refine ⟨by simp, fun r => ?_⟩
      simp only [Except.ok.injEq]
      constructor
      · intro he; subst he; exact ⟨by decide, hl⟩
      · intro he; exact jint_eq (by rw [hl, he.2])
    · by_cases h0 : y.val = 0
      · have hm : mod_BitSigned fld x y = .error .divideError := by
          unfold mod_BitSigned; rw [eq_eq, hm1, hfld x y h1]; simp [h1, h0, bind, Except.bind]
        rw [hm]; simp [h0]
      · have hval : (subWrap x (mulWrap (lit t (x.val.fdiv y.val)) y)).val = x.val.fmod y.val := by
          rw [subWrap, sub_int_val, mulWrap, mul_int_val, lit_val, wrapInt_mul_left,
            wrapInt_sub_right]
          have e := Int.fmod_add_fdiv_mul x.val y.val
          rw [show x.val - x.val.fdiv y.val * y.val = x.val.fmod y.val by omega]
          exact wrapInt_of_inRange t _ (fmod_fits x y h0)
        have hm : mod_BitSigned fld x y = .ok (subWrap x (mulWrap (lit t (x.val.fdiv y.val)) y)) := by
          unfold mod_BitSigned; rw [eq_eq, hm1, hfld x y h1]
          simp [h1, h0, bind, Except.bind, pure, Except.pure]
        rw [hm]
        refine ⟨by simp [h0], fun r => ?_⟩
        simp only [Except.ok.injEq]
        constructor
        · intro he; subst he; exact ⟨h0, hval⟩
        · intro he; exact jint_eq (by rw [hval, he.2])
  · have hm1 : (lit IntTy.i64 (-1)).val = -1 := by decide
    have hfm : x.val.fmod (-1) = 0 := by
      have e := Int.neg_fmod_neg (-x.val) 1
      rw [Int.neg_neg, Int.fmod_one] at e
      omega
    by_cases h1 : y.val = -1
    · have hl : (lit t 0).val = 0 := by rw [lit_val]; cases t <;> rfl
      have hm : mod_Integer (fun y => eq y (lit .i64 (-1))) (lit t 0) fld sub mul x y =
          .ok (lit t 0) := by
        simp only [mod_Integer, eq_eq, hm1, h1]; rfl
      rw [hm, h1, hfm]
      refine ⟨by simp, fun r => ?_⟩
      simp only [Except.ok.injEq]
      constructor
      · intro he; subst he; exact ⟨by decide, hl⟩
      · intro he; exact jint_eq (by rw [hl, he.2])
    · by_cases h0 : y.val = 0
      · have hm : mod_Integer (fun y => eq y (lit .i64 (-1))) (lit t 0) fld sub mul x y =
            .error .divideError := by
          simp only [mod_Integer, eq_eq, hm1, h1, decide_false, Bool.false_eq_true, ite_false]
          rw [hfld x y h1]; simp [h0, bind, Except.bind]
        rw [hm]; simp [h0]
      · have hval : (sub x (mul (lit t (x.val.fdiv y.val)) y)).val = x.val.fmod y.val := by
          rw [sub, sub_int_val, mul, mul_int_val, lit_val, wrapInt_mul_left, wrapInt_sub_right]
          have e := Int.fmod_add_fdiv_mul x.val y.val
          rw [show x.val - x.val.fdiv y.val * y.val = x.val.fmod y.val by omega]
          exact wrapInt_of_inRange t _ (fmod_fits x y h0)
        have hm : mod_Integer (fun y => eq y (lit .i64 (-1))) (lit t 0) fld sub mul x y =
            .ok (sub x (mul (lit t (x.val.fdiv y.val)) y)) := by
          simp only [mod_Integer, eq_eq, hm1, h1, decide_false, Bool.false_eq_true, ite_false]
          rw [hfld x y h1]; simp [h0, bind, Except.bind, pure, Except.pure]
        rw [hm]
        refine ⟨by simp [h0], fun r => ?_⟩
        simp only [Except.ok.injEq]
        constructor
        · intro he; subst he; exact ⟨h0, hval⟩
        · intro he; exact jint_eq (by rw [hval, he.2])

/-! ## Mixed-signedness `div`, `rem`, `divrem` and `mod` (lines 275-291, 342-350) -/

theorem fmod_char (a b c : Int) (hb : b ≠ 0) (hd : b ∣ a - c)
    (hr : (0 < b → 0 ≤ c ∧ c < b) ∧ (b < 0 → b < c ∧ c ≤ 0)) : a.fmod b = c := by
  have hf := fmod_bounds a b hb
  have hd2 : b ∣ a.fmod b - c := by
    have e : a.fmod b - c = (a - c) - b * a.fdiv b := by rw [Int.fmod_def]; omega
    rw [e]; exact Int.dvd_sub hd (Int.dvd_mul_right b _)
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd2 (by
    by_cases hp : 0 < b
    · have := hf.1 hp; have := hr.1 hp; omega
    · have := hf.2 (by omega); have := hr.2 (by omega); omega)
  omega

theorem tdiv_pos_eq (a b : Int) (hb : 0 < b) :
    a.tdiv b = if a < 0 then -((a.natAbs : Int) / b) else (a.natAbs : Int) / b := by
  by_cases ha : a < 0
  · have h1 : (-a).tdiv b = (-a) / b := Int.tdiv_eq_ediv_of_nonneg (by omega)
    have h2 : (-a).tdiv b = -(a.tdiv b) := Int.neg_tdiv a b
    have e : (a.natAbs : Int) = -a := by omega
    rw [if_pos ha, e]; omega
  · have h1 : a.tdiv b = a / b := Int.tdiv_eq_ediv_of_nonneg (by omega)
    have e : (a.natAbs : Int) = a := by omega
    rw [if_neg ha, e, h1]

theorem tmod_pos_eq (a b : Int) :
    a.tmod b = if a < 0 then -((a.natAbs : Int) % b) else (a.natAbs : Int) % b := by
  by_cases ha : a < 0
  · have h1 : (-a).tmod b = (-a) % b := Int.tmod_eq_emod_of_nonneg (by omega)
    have h2 : (-a).tmod b = -(a.tmod b) := Int.neg_tmod a b
    have e : (a.natAbs : Int) = -a := by omega
    rw [if_pos ha, e]; omega
  · have h1 : a.tmod b = a % b := Int.tmod_eq_emod_of_nonneg (by omega)
    have e : (a.natAbs : Int) = a := by omega
    rw [if_neg ha, e, h1]

theorem tdiv_between (a b : Int) (hb : 0 < b) :
    (0 ≤ a → 0 ≤ a.tdiv b ∧ a.tdiv b ≤ a) ∧ (a < 0 → a ≤ a.tdiv b ∧ a.tdiv b ≤ 0) := by
  rw [tdiv_pos_eq a b hb]
  have h1 := Int.ediv_nonneg (Int.natCast_nonneg a.natAbs) (Int.le_of_lt hb)
  have h2 := Int.ediv_le_self (b := b) (Int.natCast_nonneg a.natAbs)
  constructor <;> intro ha <;> split <;> omega

theorem fits_of_bounds {s R : IntTy} (h : R.min ≤ s.min ∧ s.max ≤ R.max) {z : Int} (hz : fits s z) :
    fits R z := by
  unfold fits at *; omega

theorem fits_between {t : IntTy} (x : JInt t) {z : Int}
    (h : (0 ≤ x.val → 0 ≤ z ∧ z ≤ x.val) ∧ (x.val < 0 → x.val ≤ z ∧ z ≤ 0)) : fits t z := by
  have hx := x.property
  have h0 : t.min ≤ 0 ∧ 0 ≤ t.max := by cases t <;> decide
  unfold fits
  by_cases hp : 0 ≤ x.val
  · have := h.1 hp; omega
  · have := h.2 (by omega); omega

theorem unsigned_abs_val {s : IntTy} (hs : s.signed = true) (x : JInt s) :
    (unsigned (abs x)).val = (x.val.natAbs : Int) := by
  have hx := x.property
  rw [unsigned_val, abs_val]
  by_cases hm : x.val = s.min
  · rw [if_pos ⟨hs, hm⟩, hm]
    cases s <;> simp_all [IntTy.signed] <;> decide
  · rw [if_neg (fun h => hm h.2)]
    cases s <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.toUnsigned, IntTy.bits, wrapInt] <;>
      omega

theorem mulBool_val {t : IntTy} (b : Bool) (y : JInt t) : (mulBool b y).val = if b then y.val else 0 := by
  rw [mulBool, op_Integer, mul, mul_int_val, remT_val, wrapInt_val, rem_Bool_Type,
    Generated.rem_bool, ofBool, lit_val]
  have h1 : wrapInt t 1 = 1 := by cases t <;> decide
  have h0 : wrapInt t 0 = 0 := by cases t <;> decide
  cases b
  · simp [h0, wrapInt_val]
  · simp [h1, wrapInt_val]

theorem zero_val {t : IntTy} (x : JInt t) : (zero x).val = 0 := by
  rw [zero, lit_val]; cases t <;> decide

theorem result_iff {t : IntTy} {f : Jl (JInt t)} {c : Prop} [Decidable c] {z : JInt t} {v : Int}
    (hf : f = if c then .error .divideError else .ok z) (hz : ¬ c → z.val = v) :
    (f = .error .divideError ↔ c) ∧ (∀ q, f = .ok q ↔ (¬ c ∧ q.val = v)) := by
  subst hf
  by_cases hc : c
  · rw [if_pos hc]
    exact ⟨⟨fun _ => hc, fun _ => rfl⟩, fun q => ⟨fun h => (by cases h), fun h => absurd hc h.1⟩⟩
  · rw [if_neg hc]
    refine ⟨⟨fun h => (by cases h), fun h => absurd h hc⟩, fun q => ⟨fun he => ?_, fun he => ?_⟩⟩
    · cases he; exact ⟨hc, hz hc⟩
    · rw [jint_eq (show z.val = q.val by rw [hz hc, he.2])]

theorem result_pair_iff {t : IntTy} {f : Jl (JInt t × JInt t)} {c : Prop} [Decidable c] {z w : JInt t}
    {v u : Int} (hf : f = if c then .error .divideError else .ok (z, w)) (hz : ¬ c → z.val = v)
    (hw : ¬ c → w.val = u) :
    (f = .error .divideError ↔ c) ∧ (∀ q r, f = .ok (q, r) ↔ (¬ c ∧ q.val = v ∧ r.val = u)) := by
  subst hf
  by_cases hc : c
  · rw [if_pos hc]
    exact ⟨⟨fun _ => hc, fun _ => rfl⟩, fun q r => ⟨fun h => (by cases h), fun h => absurd hc h.1⟩⟩
  · rw [if_neg hc]
    refine ⟨⟨fun h => (by cases h), fun h => absurd h hc⟩, fun q r => ⟨fun he => ?_, fun he => ?_⟩⟩
    · cases he; exact ⟨hc, hz hc, hw hc⟩
    · rw [jint_eq (show z.val = q.val by rw [hz hc, he.2.1]),
        jint_eq (show w.val = r.val by rw [hw hc, he.2.2])]

/-- What the mixed-signedness methods need from `div`, `rem` and `divrem` on two unsigned
integers (generic functions completed in `base/div.jl` and `base/promotion.jl`, later files):
the truncated quotient and remainder in the promoted type, and `DivideError` for a zero divisor
(docstrings of `div`, `rem` and `divrem`). -/
def UnsignedDivSpec (div : BinOpJl) : Prop := ∀ (a b : IntTy), a.signed = false → b.signed = false →
  ∀ (x : JInt a) (y : JInt b),
    div x y = if y.val = 0 then .error .divideError else .ok (lit (a.promote b) (x.val / y.val))
/-- See `UnsignedDivSpec`. -/
def UnsignedRemSpec (rem : BinOpJl) : Prop := ∀ (a b : IntTy), a.signed = false → b.signed = false →
  ∀ (x : JInt a) (y : JInt b),
    rem x y = if y.val = 0 then .error .divideError else .ok (lit (a.promote b) (x.val % y.val))
/-- See `UnsignedDivSpec`. -/
def UnsignedDivremSpec (divrem : DivremJl) : Prop := ∀ (a b : IntTy), a.signed = false →
  b.signed = false → ∀ (x : JInt a) (y : JInt b),
    divrem x y = if y.val = 0 then .error .divideError
      else .ok (lit (a.promote b) (x.val / y.val), lit (a.promote b) (x.val % y.val))

theorem mixedSU_types (s u : IntTy) (hs : s.signed = true) (hu : u.signed = false) :
    s.toUnsigned.signed = false ∧ (s.toUnsigned.promote u).toSigned.signed = true ∧
    (s.toUnsigned.promote u).toSigned.bits ≤ (s.toUnsigned.promote u).bits ∧
    ((s.toUnsigned.promote u).toSigned.min ≤ s.min ∧ s.max ≤ (s.toUnsigned.promote u).toSigned.max) := by
  cases s <;> cases u <;> simp_all [IntTy.signed] <;> decide

theorem mixedUS_types (u s : IntTy) (hu : u.signed = false) (hs : s.signed = true) :
    s.toUnsigned.signed = false ∧
    ((u.promote s.toUnsigned).min ≤ u.min ∧ u.max ≤ (u.promote s.toUnsigned).max) := by
  cases s <;> cases u <;> simp_all [IntTy.signed] <;> decide

/-- `flipsign(signed(q), x)` where `q` is a nonnegative unsigned result: `q` with the sign of `x`. -/
theorem flip_signed_lit_val {s P : IntTy} (hs : s.signed = true) (hR : P.toSigned.signed = true)
    (hb : P.toSigned.bits ≤ P.bits) (v : Int) (x : JInt s) :
    (flipsign (signed (lit P v)) x).val = wrapInt P.toSigned (if x.val < 0 then -v else v) := by
  rw [flipsign_val hR hs, signed_val, lit_val, wrapInt_narrow hb]
  split
  · exact wrapInt_neg _ _
  · exact wrapInt_wrapInt _ _

/-- `div(x, y)`, `rem(x, y)` and `divrem(x, y)` for a signed `x` and an unsigned `y` are the
exact truncated quotient and remainder (docstrings of `div`, `rem`, `divrem`), with no
wraparound even for `x == typemin`, and throw `DivideError` exactly for `y == 0`
(`base/int.jl:275,278,281-285`); `rem(x, y)` for an unsigned `x` and a signed `y`, and the
remainder of `divrem(x, y)`, are the exact truncated remainder (`base/int.jl:279,286-289`). For
every `div`, `rem` and `divrem` on unsigned arguments with their documented behaviour. -/
def MixedDivRem : Prop := ∀ (div rem : BinOpJl) (divrem : DivremJl), UnsignedDivSpec div →
  UnsignedRemSpec rem → UnsignedDivremSpec divrem →
  (∀ (s u : IntTy), s.signed = true → u.signed = false → ∀ (x : JInt s) (y : JInt u),
    (div_BitSigned_Unsigned div x y = .error .divideError ↔ y.val = 0) ∧
    (∀ q, div_BitSigned_Unsigned div x y = .ok q ↔ (¬ y.val = 0 ∧ q.val = x.val.tdiv y.val)) ∧
    (rem_BitSigned_Unsigned rem x y = .error .divideError ↔ y.val = 0) ∧
    (∀ r, rem_BitSigned_Unsigned rem x y = .ok r ↔ (¬ y.val = 0 ∧ r.val = x.val.tmod y.val)) ∧
    (divrem_BitSigned_Unsigned divrem x y = .error .divideError ↔ y.val = 0) ∧
    (∀ q r, divrem_BitSigned_Unsigned divrem x y = .ok (q, r) ↔
      (¬ y.val = 0 ∧ q.val = x.val.tdiv y.val ∧ r.val = x.val.tmod y.val))) ∧
  (∀ (u s : IntTy), u.signed = false → s.signed = true → ∀ (x : JInt u) (y : JInt s),
    (rem_Unsigned_BitSigned rem x y = .error .divideError ↔ y.val = 0) ∧
    (∀ r, rem_Unsigned_BitSigned rem x y = .ok r ↔ (¬ y.val = 0 ∧ r.val = x.val.tmod y.val)) ∧
    (∀ q r, divrem_Unsigned_BitSigned divrem x y = .ok (q, r) → r.val = x.val.tmod y.val))

theorem rem_Unsigned_BitSigned_eq (rem : BinOpJl) (hr : UnsignedRemSpec rem) {u s : IntTy}
    (hu : u.signed = false) (hs : s.signed = true) (x : JInt u) (y : JInt s) :
    rem_Unsigned_BitSigned rem x y = if y.val = 0 then .error .divideError
      else .ok (lit (u.promote s.toUnsigned) (x.val % (y.val.natAbs : Int))) := by
  rw [rem_Unsigned_BitSigned]
  refine (hr u s.toUnsigned hu (mixedUS_types u s hu hs).1 x (unsigned (abs y))).trans ?_
  rw [unsigned_abs_val hs]
  have : ((y.val.natAbs : Int) = 0) = (y.val = 0) := by
    apply propext; omega
  simp only [this]

theorem emod_natAbs_eq_tmod {u : IntTy} (hu : u.signed = false) (x : JInt u) (b : Int) :
    x.val % (b.natAbs : Int) = x.val.tmod b := by
  rw [Int.tmod_eq_emod_of_nonneg (nonneg_of_unsigned hu x)]
  by_cases hb : 0 ≤ b
  · rw [show (b.natAbs : Int) = b by omega]
  · rw [show (b.natAbs : Int) = -b by omega, Int.emod_neg]

theorem div_BitSigned_Unsigned_form (div : BinOpJl) (hd : UnsignedDivSpec div) {s u : IntTy}
    (hs : s.signed = true) (hu : u.signed = false) (x : JInt s) (y : JInt u) :
    ∃ z, div_BitSigned_Unsigned div x y = (if y.val = 0 then .error .divideError else .ok z) ∧
      (¬ y.val = 0 → z.val = x.val.tdiv y.val) := by
  obtain ⟨ht, hR, hb, hbd⟩ := mixedSU_types s u hs hu
  have hy0 := nonneg_of_unsigned hu y
  refine ⟨flipsign (signed (lit (s.toUnsigned.promote u) ((x.val.natAbs : Int) / y.val))) x, ?_, ?_⟩
  · unfold div_BitSigned_Unsigned Generic.div_BitSigned_Unsigned
    rw [hd s.toUnsigned u ht hu (unsigned (abs x)) y, unsigned_abs_val hs]
    by_cases h0 : y.val = 0 <;> simp [h0, bind, Except.bind, pure, Except.pure]
  · intro h0
    have hp : 0 < y.val := by omega
    rw [flip_signed_lit_val hs hR hb, ← tdiv_pos_eq x.val y.val hp]
    exact wrapInt_of_inRange _ _ (fits_of_bounds hbd (fits_between x (tdiv_between x.val y.val hp)))

theorem rem_BitSigned_Unsigned_form (rem : BinOpJl) (hr : UnsignedRemSpec rem) {s u : IntTy}
    (hs : s.signed = true) (hu : u.signed = false) (x : JInt s) (y : JInt u) :
    ∃ z, rem_BitSigned_Unsigned rem x y = (if y.val = 0 then .error .divideError else .ok z) ∧
      (¬ y.val = 0 → z.val = x.val.tmod y.val) := by
  obtain ⟨ht, hR, hb, hbd⟩ := mixedSU_types s u hs hu
  refine ⟨flipsign (signed (lit (s.toUnsigned.promote u) ((x.val.natAbs : Int) % y.val))) x, ?_, ?_⟩
  · unfold rem_BitSigned_Unsigned Generic.rem_BitSigned_Unsigned
    rw [hr s.toUnsigned u ht hu (unsigned (abs x)) y, unsigned_abs_val hs]
    by_cases h0 : y.val = 0 <;> simp [h0, bind, Except.bind, pure, Except.pure]
  · intro _
    rw [flip_signed_lit_val hs hR hb, ← tmod_pos_eq x.val y.val]
    exact wrapInt_of_inRange _ _ (fits_of_bounds hbd (fits_between x (tmod_between x.val y.val)))

theorem divrem_BitSigned_Unsigned_form (divrem : DivremJl) (hdr : UnsignedDivremSpec divrem)
    {s u : IntTy} (hs : s.signed = true) (hu : u.signed = false) (x : JInt s) (y : JInt u) :
    ∃ z w, divrem_BitSigned_Unsigned divrem x y =
      (if y.val = 0 then .error .divideError else .ok (z, w)) ∧
      (¬ y.val = 0 → z.val = x.val.tdiv y.val) ∧ (¬ y.val = 0 → w.val = x.val.tmod y.val) := by
  obtain ⟨ht, hR, hb, hbd⟩ := mixedSU_types s u hs hu
  have hy0 := nonneg_of_unsigned hu y
  refine ⟨flipsign (signed (lit (s.toUnsigned.promote u) ((x.val.natAbs : Int) / y.val))) x,
    flipsign (signed (lit (s.toUnsigned.promote u) ((x.val.natAbs : Int) % y.val))) x, ?_, ?_, ?_⟩
  · unfold divrem_BitSigned_Unsigned Generic.divrem_BitSigned_Unsigned
    rw [hdr s.toUnsigned u ht hu (unsigned (abs x)) y, unsigned_abs_val hs]
    by_cases h0 : y.val = 0 <;> simp [h0, bind, Except.bind, pure, Except.pure]
  · intro h0
    have hp : 0 < y.val := by omega
    rw [flip_signed_lit_val hs hR hb, ← tdiv_pos_eq x.val y.val hp]
    exact wrapInt_of_inRange _ _ (fits_of_bounds hbd (fits_between x (tdiv_between x.val y.val hp)))
  · intro _
    rw [flip_signed_lit_val hs hR hb, ← tmod_pos_eq x.val y.val]
    exact wrapInt_of_inRange _ _ (fits_of_bounds hbd (fits_between x (tmod_between x.val y.val)))

theorem mixedDivRem_proven : MixedDivRem := by
  intro div rem divrem hd hr hdr
  refine ⟨fun s u hs hu x y => ?_, fun u s hu s_ x y => ?_⟩
  · obtain ⟨z1, f1, v1⟩ := div_BitSigned_Unsigned_form div hd hs hu x y
    obtain ⟨z2, f2, v2⟩ := rem_BitSigned_Unsigned_form rem hr hs hu x y
    obtain ⟨z3, w3, f3, v3, v4⟩ := divrem_BitSigned_Unsigned_form divrem hdr hs hu x y
    obtain ⟨d1, d2⟩ := result_iff f1 v1
    obtain ⟨r1, r2⟩ := result_iff f2 v2
    obtain ⟨p1, p2⟩ := result_pair_iff f3 v3 v4
    exact ⟨d1, d2, r1, r2, p1, p2⟩
  · have hfr := rem_Unsigned_BitSigned_eq rem hr hu s_ x y
    have vr : ¬ y.val = 0 → (lit (u.promote s.toUnsigned) (x.val % (y.val.natAbs : Int))).val =
        x.val.tmod y.val := fun _ => by
      rw [emod_natAbs_eq_tmod hu x]
      exact lit_of_fits (fits_of_bounds (mixedUS_types u s hu s_).2
        (fits_between x (tmod_between x.val y.val)))
    obtain ⟨r1, r2⟩ := result_iff hfr vr
    refine ⟨r1, r2, fun q r h => ?_⟩
    unfold divrem_Unsigned_BitSigned Generic.divrem_Unsigned_BitSigned at h
    rw [hdr u s.toUnsigned hu (mixedUS_types u s hu s_).1 x (unsigned (abs y)), unsigned_abs_val s_] at h
    by_cases h0 : y.val = 0
    · have : ((y.val.natAbs : Int) = 0) := by omega
      simp [this, bind, Except.bind] at h
    · have : ¬ ((y.val.natAbs : Int) = 0) := by omega
      simp only [this, ite_false, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.2]
      exact vr h0

/-- Unsigned-dividend division and divrem return the mathematical quotient rounded toward
zero, as promised by their docstrings. Refuted: div(0x0a, Int16(-3)) returns 65533,
where the quotient rounded toward zero is -3. -/
def UnsignedSignedExactQuotient : Prop := ∀ (div : BinOpJl) (divrem : DivremJl), UnsignedDivSpec div →
  UnsignedDivremSpec divrem → ∀ (u s : IntTy), u.signed = false → s.signed = true →
  ∀ (x : JInt u) (y : JInt s),
    (∀ q, div_Unsigned_BitSigned div x y = .ok q → q.val = x.val.tdiv y.val) ∧
    (∀ q r, divrem_Unsigned_BitSigned divrem x y = .ok (q, r) →
      q.val = x.val.tdiv y.val)

/-- `div` on two unsigned BitIntegers with the behaviour `UnsignedDivSpec` requires. -/
def unsignedDivWitness : BinOpJl := fun x y =>
  if y.val = 0 then .error .divideError else .ok (lit _ (x.val / y.val))

/-- `divrem` on two unsigned BitIntegers with the behaviour `UnsignedDivremSpec` requires. -/
def unsignedDivremWitness : DivremJl := fun x y =>
  if y.val = 0 then .error .divideError else .ok (lit _ (x.val / y.val), lit _ (x.val % y.val))

theorem unsignedSignedExactQuotient_refuted : ¬ UnsignedSignedExactQuotient := by
  intro h
  have h1 := (h unsignedDivWitness unsignedDivremWitness (fun _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl) .u8 .i16 rfl rfl (lit .u8 10) (lit .i16 (-3))).1 (lit .u16 65533) (by rfl)
  revert h1
  decide

/-- `mod(x, y)` for a signed `x` and an unsigned `y`, and for an unsigned `x` and a signed `y`,
is the exact floored remainder `x - y*fld(x, y)`, with the sign of `y` and magnitude below
`|y|` (`mod` docstring), and throws `DivideError` exactly for `y == 0`, for every `rem` on
unsigned arguments with its documented behaviour (`base/int.jl:342-350`). -/
def ModMixed : Prop := ∀ (rem : BinOpJl), UnsignedRemSpec rem →
  (∀ (s u : IntTy), s.signed = true → u.signed = false → ∀ (x : JInt s) (y : JInt u),
    (mod_BitSigned_Unsigned rem x y = .error .divideError ↔ y.val = 0) ∧
    (∀ r, mod_BitSigned_Unsigned rem x y = .ok r ↔ (¬ y.val = 0 ∧ r.val = x.val.fmod y.val))) ∧
  (∀ (u s : IntTy), u.signed = false → s.signed = true → ∀ (x : JInt u) (y : JInt s),
    (mod_Unsigned_Signed rem x y = .error .divideError ↔ y.val = 0) ∧
    (∀ r, mod_Unsigned_Signed rem x y = .ok r ↔ (¬ y.val = 0 ∧ r.val = x.val.fmod y.val)))

theorem modMixed_types1 (s u : IntTy) (hs : s.signed = true) (hu : u.signed = false) :
    ((s.toUnsigned.promote u).toSigned.promote u).toUnsigned.bits ≤
      ((s.toUnsigned.promote u).toSigned.promote u).bits ∧
    (((s.toUnsigned.promote u).toSigned.promote u).toUnsigned.min ≤ u.min ∧
      u.max ≤ ((s.toUnsigned.promote u).toSigned.promote u).toUnsigned.max) := by
  cases s <;> cases u <;> simp_all [IntTy.signed] <;> decide

theorem modMixed_types2 (u s : IntTy) (hu : u.signed = false) (hs : s.signed = true) :
    (u.promote s.toUnsigned).toSigned.signed = true ∧
    ((u.promote s.toUnsigned).toSigned.min ≤ s.min ∧ s.max ≤ (u.promote s.toUnsigned).toSigned.max) ∧
    ((u.promote s.toUnsigned).toSigned.promote s).signed = true ∧
    (((u.promote s.toUnsigned).toSigned.promote s).min ≤ s.min ∧
      s.max ≤ ((u.promote s.toUnsigned).toSigned.promote s).max) := by
  cases s <;> cases u <;> simp_all [IntTy.signed] <;> decide

theorem fmod_pos_tmod (a b : Int) (hb : 0 < b) :
    a.fmod b = a.tmod b + (if a.tmod b < 0 then b else 0) := by
  have e := Int.mul_tdiv_add_tmod a b
  have hl : (a.tmod b).natAbs < b.natAbs := by
    rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by omega)
  apply fmod_char a b _ (by omega)
  · by_cases hn : a.tmod b < 0
    · rw [if_pos hn]; exact ⟨a.tdiv b - 1, by rw [Int.mul_sub, Int.mul_one]; omega⟩
    · rw [if_neg hn]; exact ⟨a.tdiv b, by omega⟩
  · refine ⟨fun _ => ?_, fun h => absurd h (by omega)⟩
    split <;> omega

theorem fmod_nonneg_tmod (a b : Int) (ha : 0 ≤ a) (hb : b ≠ 0) :
    a.fmod b = a.tmod b + (if a.tmod b ≠ 0 ∧ b < 0 then b else 0) := by
  have e := Int.mul_tdiv_add_tmod a b
  have hl : (a.tmod b).natAbs < b.natAbs := by
    rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by omega)
  have h0 := Int.tmod_nonneg b ha
  apply fmod_char a b _ hb
  · by_cases hn : a.tmod b ≠ 0 ∧ b < 0
    · rw [if_pos hn]; exact ⟨a.tdiv b - 1, by rw [Int.mul_sub, Int.mul_one]; omega⟩
    · rw [if_neg hn]; exact ⟨a.tdiv b, by omega⟩
  · constructor <;> intro hp <;> split <;> omega

theorem modMixed_proven : ModMixed := by
  intro rem hr
  refine ⟨fun s u hs hu x y => ?_, fun u s hu hs x y => ?_⟩
  · obtain ⟨z, fz, vz⟩ := rem_BitSigned_Unsigned_form rem hr hs hu x y
    obtain ⟨hb, hbd⟩ := modMixed_types1 s u hs hu
    have hy0 := nonneg_of_unsigned hu y
    apply result_iff (z := unsigned (binop addWrap z (mulBool (lt z (zero z)) y)))
    · unfold mod_BitSigned_Unsigned Generic.mod_BitSigned_Unsigned
      rw [fz]
      by_cases h0 : y.val = 0 <;> simp [h0, bind, Except.bind, pure, Except.pure]
    · intro h0
      have hp : 0 < y.val := by omega
      rw [unsigned_val, binop_eq, addWrap, add_int_val, remT_val, remT_val, wrapInt_add_left,
        wrapInt_add_right, wrapInt_narrow hb, mulBool_val, lt_eq, zero_val, vz h0]
      simp only [decide_eq_true_eq]
      rw [← fmod_pos_tmod x.val y.val hp]
      apply wrapInt_of_inRange
      have hf := (fmod_bounds x.val y.val h0).1 hp
      have hy := y.property
      have hu0 : u.min = 0 := by cases u <;> simp_all [IntTy.signed, IntTy.min]
      omega
  · have hfr := rem_Unsigned_BitSigned_eq rem hr hu hs x y
    obtain ⟨hR, hbR, hP, hbP⟩ := modMixed_types2 u s hu hs
    have hx0 := nonneg_of_unsigned hu x
    have hy := y.property
    have hsm : s.max = -s.min - 1 := by cases s <;> simp_all [IntTy.signed] <;> decide
    have hrv : ¬ y.val = 0 → (lit (u.promote s.toUnsigned) (x.val % (y.val.natAbs : Int))).val =
        x.val.tmod y.val := fun _ => by
      rw [emod_natAbs_eq_tmod hu x]
      exact lit_of_fits (fits_of_bounds (mixedUS_types u s hu hs).2
        (fits_between x (tmod_between x.val y.val)))
    generalize lit (u.promote s.toUnsigned) (x.val % (y.val.natAbs : Int)) = r at hfr hrv
    apply result_iff (z := binop add (signed r)
      (mulBool (!(eq (signed r) (zero (signed r))) && lt y (zero y)) y))
    · unfold mod_Unsigned_Signed
      rw [hfr]
      by_cases h0 : y.val = 0 <;> simp [h0, bind, Except.bind, pure, Except.pure]
    · intro h0
      have hl : (x.val.tmod y.val).natAbs < y.val.natAbs := by
        rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (by omega)
      have ht0 := Int.tmod_nonneg y.val hx0
      have hsv : (signed r).val = x.val.tmod y.val := by
        rw [signed_val, hrv h0]
        apply wrapInt_of_inRange
        have : fits s (x.val.tmod y.val) := by unfold fits; omega
        exact fits_of_bounds hbR this
      rw [binop_eq, add, add_int_val, remT_val, remT_val, wrapInt_add_left, wrapInt_add_right,
        mulBool_val, eq_eq, lt_eq, zero_val, zero_val, hsv]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      rw [← fmod_nonneg_tmod x.val y.val hx0 h0]
      apply wrapInt_of_inRange
      apply fits_of_bounds hbP
      have hf := fmod_bounds x.val y.val h0
      unfold fits
      by_cases hp : 0 < y.val
      · have := hf.1 hp; omega
      · have := hf.2 (by omega); omega

/-! ## Parity and `x % Bool` (lines 143-181, 699) -/

/-- `isodd(n)` is true exactly for odd integers and `iseven(n)` exactly for even ones
(docstrings of `isodd` and `iseven`), for every BitInteger `n` through the `Real` methods
(`base/int.jl:161,181`), with `isinteger(::Integer) = true` from `base/number.jl`, and for every
`Integer(n)` (`boot.jl`), `rem(n, 2)` (`promotion.jl`, then lines 356-358) and `iszero`
(`number.jl`) with their documented behaviour: `Integer(n) == n` for an integer, the truncated
remainder, and `iszero(r) == (r == 0)`. -/
def ParityExact : Prop := ∀ (t : IntTy) (Integer : JInt t → JInt t)
  (rem : JInt t → JInt .i64 → JInt (t.promote .i64)) (iszero : JInt (t.promote .i64) → Bool),
  (∀ n, Integer n = n) → (∀ n, (rem n (lit .i64 2)).val = n.val.tmod 2) →
  (∀ r, iszero r = decide (r.val = 0)) → ∀ n : JInt t,
    isodd_Real JuliaLean.base.number.isintegerInteger Integer rem iszero n = decide (n.val % 2 = 1) ∧
    iseven_Real JuliaLean.base.number.isintegerInteger Integer rem iszero n = decide (n.val % 2 = 0)
theorem parityExact_proven : ParityExact := by
  intro t Integer rem iszero hI hrem hz n
  have h2 : (n.val.tmod 2 = 0) ↔ (n.val % 2 = 0) := by
    rw [← Int.dvd_iff_tmod_eq_zero, Int.dvd_iff_emod_eq_zero]
  simp only [isodd_Real, iseven_Real, JuliaLean.base.number.isintegerInteger, hI, hz, hrem,
    Bool.true_and]
  constructor
  · by_cases h : n.val % 2 = 0
    · have := h2.2 h; simp [this, h]
    · have h' : ¬ n.val.tmod 2 = 0 := fun e => h (h2.1 e)
      have h1 : n.val % 2 = 1 := by omega
      simp [h', h1]
  · by_cases h : n.val % 2 = 0
    · have := h2.2 h; simp [this, h]
    · have h' : ¬ n.val.tmod 2 = 0 := fun e => h (h2.1 e)
      simp [h', h]

/-- `x % Bool` is `true` exactly for odd `x`: the `Bool` congruent to `x` modulo 2, the number of
values of `Bool` (docstring of `rem(x::Integer, T::Type{<:Integer})`, `base/int.jl:673-676`;
method at line 699). -/
def RemBoolParity : Prop := ∀ (t : IntTy) (x : JInt t), rem_Integer_Bool x = decide (x.val % 2 = 1)
theorem remBoolParity_proven : RemBoolParity := by
  intro t x
  have h1 : 1 ≤ (t.promote .i64).bits := by cases t <;> decide
  have hpx : pattern (remT (t.promote .i64) x) =
      (x.val % ((2 ^ (t.promote .i64).bits : Nat) : Int)).toNat :=
    pattern_of_cong _ x.val (remT_val _ x)
  have hp1 : pattern (remT (t.promote .i64) (lit .i64 1)) = 1 := by cases t <;> decide
  have hM : (2 : Int) ∣ ((2 ^ (t.promote .i64).bits : Nat) : Int) := by
    have := Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h1)
    simpa using this
  have hmm := Int.emod_emod_of_dvd x.val hM
  have hnn := Int.emod_nonneg x.val (by have := two_pow_pos_int (t.promote .i64).bits; omega :
    ((2 ^ (t.promote .i64).bits : Nat) : Int) ≠ 0)
  have hb : pattern (band (remT (t.promote .i64) x) (remT (t.promote .i64) (lit .i64 1))) =
      (x.val % 2).toNat := by
    rw [pattern_band, hpx, hp1, Nat.and_one_is_mod]
    omega
  have h0 : (lit IntTy.i64 0).val = 0 := by decide
  unfold rem_Integer_Bool Generic.rem_Integer_Bool
  dsimp only
  rw [eq_eq, binop_eq, h0, val_eq_wrap_pattern (band _ _), hb]
  have hc : x.val % 2 = 0 ∨ x.val % 2 = 1 := by omega
  rcases hc with hc | hc <;> rw [hc] <;> cases t <;> decide

/-! ## `negate` (lines 95-98) -/

/-- `Base.negate(x)` of an unsigned `x` is the exact negation `-x` as a value of the signed type of
the same size, and throws `InexactError` exactly when `x` exceeds that type's `typemax`
(`base/int.jl:97`, through `convert(Signed, x)`). -/
def NegateUnsigned : Prop := ∀ (t : IntTy), t.signed = false → ∀ x : JInt t,
  (∀ q, negate_Unsigned x = .ok q ↔ (x.val ≤ t.toSigned.max ∧ q.val = -x.val)) ∧
  (t.toSigned.max < x.val → negate_Unsigned x = .error (.inexactError t.toSigned.name))
theorem negateUnsigned_proven : NegateUnsigned := by
  intro t ht x
  have hx0 := nonneg_of_unsigned ht x
  have hmin : t.toSigned.min = -t.toSigned.max - 1 := by cases t <;> simp_all [IntTy.signed] <;> decide
  have hmax : 0 ≤ t.toSigned.max := by cases t <;> decide
  unfold negate_Unsigned Generic.negate_Unsigned convert JInt.convert
  by_cases hf : t.toSigned.min ≤ x.val ∧ x.val ≤ t.toSigned.max
  · rw [dif_pos hf]
    have hv : (neg (⟨x.val, hf⟩ : JInt t.toSigned)).val = -x.val := by
      rw [neg, neg_int_val]
      show wrapInt _ (-x.val) = -x.val
      exact wrapInt_of_inRange _ _ ⟨by omega, by omega⟩
    refine ⟨fun q => ⟨fun h => ?_, fun h => ?_⟩, fun h => absurd hf.2 (by omega)⟩
    · cases h; exact ⟨hf.2, hv⟩
    · show Except.ok _ = Except.ok q
      rw [jint_eq (show (neg (⟨x.val, hf⟩ : JInt t.toSigned)).val = q.val by rw [hv, h.2])]
  · rw [dif_neg hf]
    refine ⟨fun q => ⟨fun h => (by cases h), fun h => absurd ⟨by omega, h.1⟩ hf⟩, fun _ => rfl⟩

/-! ## `widemul` (lines 920-930) -/

theorem mulSame_val {t : IntTy} (x y : JInt t) : (mulSame x y).val = wrapInt t (x.val * y.val) := by
  cases t <;> simp only [mulSame, mul, mul_128] <;> exact mul_int_val x y

theorem widemul_bound (s u : IntTy) (hs : s.signed = true) (hu : u.signed = false) (x : JInt s)
    (y : JInt u) : (x.val * y.val).natAbs ≤ s.min.natAbs * u.max.natAbs := by
  have hx := x.property
  have hy := y.property
  apply mul_natAbs_le
  · cases s <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
  · cases u <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega

/-- `widemul(x, y)` of a signed and an unsigned BitInteger below 128 bits, in either order, is the
exact product (docstring of `widemul`: "Multiply `x` and `y`, giving the result as a larger
type"), for every `widen` (`base/operators.jl`) that converts its argument to `widen(T)`
(`base/int.jl:911-918`) keeping its value, as documented (`base/int.jl:923-924`);
`widemul` of two `Bool`s is their product (`base/int.jl:926`). -/
def WidemulExact : Prop :=
  (∀ (s u ws wu : IntTy), s.signed = true → u.signed = false → widenType s = some ws →
    widenType u = some wu → ∀ (widenS : JInt s → JInt ws) (widenU : JInt u → JInt wu),
    (∀ x, (widenS x).val = x.val) → (∀ y, (widenU y).val = y.val) → ∀ (x : JInt s) (y : JInt u),
    (widemul_Signed_Unsigned widenS widenU x y).val = x.val * y.val ∧
    (widemul_Unsigned_Signed widenU widenS y x).val = y.val * x.val) ∧
  (∀ a b : Bool, (if Generic.widemul_Bool_Bool JuliaLean.base.bool.mulBool a b then 1 else 0 : Int) =
    (if a then 1 else 0) * (if b then 1 else 0))
theorem widemul_types (s u ws wu : IntTy) (hs : s.signed = true) (hu : u.signed = false)
    (hws : widenType s = some ws) (hwu : widenType u = some wu) :
    (ws.min ≤ s.min ∧ s.max ≤ ws.max) ∧ (wu.min ≤ u.min ∧ u.max ≤ wu.max) ∧
    (wu.toSigned.min ≤ u.min ∧ u.max ≤ wu.toSigned.max) ∧
    ((ws.promote wu.toSigned).min ≤ s.min ∧ s.max ≤ (ws.promote wu.toSigned).max ∧
      (ws.promote wu.toSigned).min ≤ u.min ∧ u.max ≤ (ws.promote wu.toSigned).max ∧
      (ws.promote wu.toSigned).min ≤ -((s.min.natAbs * u.max.natAbs : Nat) : Int) ∧
      ((s.min.natAbs * u.max.natAbs : Nat) : Int) ≤ (ws.promote wu.toSigned).max) ∧
    ((wu.toSigned.promote ws).min ≤ s.min ∧ s.max ≤ (wu.toSigned.promote ws).max ∧
      (wu.toSigned.promote ws).min ≤ u.min ∧ u.max ≤ (wu.toSigned.promote ws).max ∧
      (wu.toSigned.promote ws).min ≤ -((s.min.natAbs * u.max.natAbs : Nat) : Int) ∧
      ((s.min.natAbs * u.max.natAbs : Nat) : Int) ≤ (wu.toSigned.promote ws).max) := by
  cases s <;> cases u <;> simp only [IntTy.signed] at hs hu <;> (try contradiction) <;>
    simp only [widenType, widen_Int8, widen_Int16, widen_Int32, widen_Int64, widen_UInt8,
      widen_UInt16, widen_UInt32, widen_UInt64, reduceCtorEq, Option.some.injEq] at hws hwu <;>
    (try contradiction) <;> subst hws <;> subst hwu <;> decide

theorem widemulExact_proven : WidemulExact := by
  refine ⟨fun s u ws wu hs hu hws hwu widenS widenU hS hU x y => ?_,
    fun a b => by cases a <;> cases b <;> rfl⟩
  have hx := x.property
  have hy := y.property
  have hp := widemul_bound s u hs hu x y
  have hp' : (y.val * x.val).natAbs ≤ s.min.natAbs * u.max.natAbs := by rw [Int.mul_comm]; exact hp
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2, d3, d4, d5, d6⟩, ⟨e1, e2, e3, e4, e5, e6⟩⟩ :=
    widemul_types s u ws wu hs hu hws hwu
  simp only [widemul_Signed_Unsigned, widemul_Unsigned_Signed, binop_eq, mulSame_val, remT_val,
    signed_val, hS, hU]
  rw [wrapInt_of_inRange wu.toSigned y.val ⟨by omega, by omega⟩,
    wrapInt_of_inRange (ws.promote wu.toSigned) x.val ⟨by omega, by omega⟩,
    wrapInt_of_inRange (ws.promote wu.toSigned) y.val ⟨by omega, by omega⟩,
    wrapInt_of_inRange (wu.toSigned.promote ws) x.val ⟨by omega, by omega⟩,
    wrapInt_of_inRange (wu.toSigned.promote ws) y.val ⟨by omega, by omega⟩]
  exact ⟨wrapInt_of_inRange _ _ ⟨by omega, by omega⟩, wrapInt_of_inRange _ _ ⟨by omega, by omega⟩⟩

/-! ## `mul_hi` (lines 105-142) -/

theorem mulhi_shift_val (t : IntTy) : (top_set_bit (remT t (lit .i64 (-1)))).val = t.bits := by
  have h := topSetBit_proven t (remT t (lit .i64 (-1)))
  simp only at h
  obtain ⟨h0, h1, h2, -⟩ := h
  have hp : pattern (remT t (lit .i64 (-1))) = 2 ^ t.bits - 1 := by
    rw [pattern_of_cong _ (-1) (by rw [remT_val, lit_val]; cases t <;> decide)]
    cases t <;> decide
  rw [hp] at h2
  have h3 : 2 ^ t.bits ≤ 2 ^ (top_set_bit (remT t (lit .i64 (-1)))).val.toNat := by
    have := Nat.two_pow_pos t.bits; omega
  have h4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 h3
  omega

theorem mulhi_types (t w : IntTy) (hw : widenType t = some w) :
    t.bits ≤ (w.promote t).bits ∧ (w.promote t).bits ≤ w.bits ∧
    ((w.promote t).bits = 2 * t.bits ∧ (w.promote t).signed = t.signed) := by
  cases t <;> simp only [widenType, widen_Int8, widen_Int16, widen_Int32, widen_Int64, widen_UInt8,
      widen_UInt16, widen_UInt32, widen_UInt64, reduceCtorEq, Option.some.injEq] at hw <;>
    (try contradiction) <;> subst hw <;> decide

/-- `mul_hi(a, b)` is the higher half of the product, `floor(a*b / 2^n)` for `n`-bit `a` and `b`
(docstring of `mul_hi`), for every BitInteger type below 128 bits and every `widen`
(`base/operators.jl`) that converts its argument to `widen(T)` keeping its value
(`base/int.jl:122-124`). -/
def MulHiExact : Prop := ∀ (t w : IntTy), widenType t = some w → ∀ (widen : JInt t → JInt w),
  (∀ x, (widen x).val = x.val) → ∀ a b : JInt t,
  (mul_hi_Integer widen a b).val = (a.val * b.val) / 2 ^ t.bits
theorem mulHiExact_proven : MulHiExact := by
  intro t w hw widen hW a b
  obtain ⟨hle, -, -, -⟩ := mulhi_types t w hw
  have hc := mulhi_shift_val t
  have ha := a.property
  have hb := b.property
  have hab : (binop mulSame (widen a) b).val = wrapInt (w.promote t) (a.val * b.val) := by
    rw [binop_eq, mulSame_val, remT_val, remT_val, hW, wrapInt_mul_left, wrapInt_mul_right]
  have hK : ∀ z : JInt t, z.val.natAbs ≤ (if t.signed then t.min.natAbs else t.max.natAbs) := by
    intro z
    have hz := z.property
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
  have hp := mul_natAbs_le (hK a) (hK b)
  have hnn : t.signed = false → 0 ≤ a.val * b.val := fun h =>
    Int.mul_nonneg (nonneg_of_unsigned h a) (nonneg_of_unsigned h b)
  unfold mul_hi_Integer Generic.mul_hi_Integer
  rw [remT_val, val_eq_wrap_pattern (lshr_Int _ _), pattern_lshr_Int _ _ (by rw [hc]; omega), hc,
    wrapInt_narrow hle, pattern_of_cong _ _ hab]
  generalize a.val * b.val = ab at hp hnn ⊢
  cases t <;> simp only [widenType, widen_Int8, widen_Int16, widen_Int32, widen_Int64, widen_UInt8,
      widen_UInt16, widen_UInt32, widen_UInt64, reduceCtorEq, Option.some.injEq] at hw <;>
    (try contradiction) <;> subst hw <;>
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, IntTy.promote, wrapInt] at hp hnn ⊢ <;>
    omega

/-! ## `mul_hi` for 128-bit integers (lines 126-142) -/

theorem pattern_add_int {t : IntTy} (x y : JInt t) :
    pattern (add_int x y) = (pattern x + pattern y) % 2 ^ t.bits := by
  simp only [add_int, jlAddInt, pattern_toJInt, BitVec.toNat_add, ← pattern_fromJInt]

theorem pattern_mul_int {t : IntTy} (x y : JInt t) :
    pattern (mul_int x y) = pattern x * pattern y % 2 ^ t.bits := by
  simp only [mul_int, jlMulInt, pattern_toJInt, BitVec.toNat_mul, ← pattern_fromJInt]

theorem expand4 (a1 a2 b1 b2 K : Nat) :
    (a1 * K + a2) * (b1 * K + b2) = a1 * b1 * (K * K) + a1 * b2 * K + a2 * b1 * K + a2 * b2 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm K, Nat.mul_left_comm K,
    Nat.add_assoc]
  omega

theorem and_mask64 (x : Nat) : x &&& 18446744073709551615 = x % 18446744073709551616 :=
  Nat.and_two_pow_sub_one_eq_mod x 64

/-- The limb arithmetic of `mul_hi(::UInt128, ::UInt128)`: the high half of a product from the
four 64-bit partial products. -/
theorem limb_high (a1 a2 b1 b2 : Nat) (ha1 : a1 < 18446744073709551616) (ha2 : a2 < 18446744073709551616)
    (hb1 : b1 < 18446744073709551616) (hb2 : b2 < 18446744073709551616) :
    ((((a1 * b1 % 2 ^ 128 + a1 * b2 % 2 ^ 128 / 18446744073709551616) % 2 ^ 128 +
      a2 * b1 % 2 ^ 128 / 18446744073709551616) % 2 ^ 128 +
      ((a1 * b2 % 2 ^ 128 % 18446744073709551616 + a2 * b1 % 2 ^ 128 % 18446744073709551616) % 2 ^ 128 +
        a2 * b2 % 2 ^ 128 / 18446744073709551616) % 2 ^ 128 / 18446744073709551616) % 2 ^ 128) =
    (a1 * 18446744073709551616 + a2) * (b1 * 18446744073709551616 + b2) / 2 ^ 128 := by
  rw [expand4]
  have h11 : a1 * b1 ≤ 18446744073709551615 * 18446744073709551615 := Nat.mul_le_mul (by omega) (by omega)
  have h12 : a1 * b2 ≤ 18446744073709551615 * 18446744073709551615 := Nat.mul_le_mul (by omega) (by omega)
  have h21 : a2 * b1 ≤ 18446744073709551615 * 18446744073709551615 := Nat.mul_le_mul (by omega) (by omega)
  have h22 : a2 * b2 ≤ 18446744073709551615 * 18446744073709551615 := Nat.mul_le_mul (by omega) (by omega)
  generalize a1 * b1 = p11 at *
  generalize a1 * b2 = p12 at *
  generalize a2 * b1 = p21 at *
  generalize a2 * b2 = p22 at *
  have m11 : p11 % 2 ^ 128 = p11 := Nat.mod_eq_of_lt (by omega)
  have m12 : p12 % 2 ^ 128 = p12 := Nat.mod_eq_of_lt (by omega)
  have m21 : p21 % 2 ^ 128 = p21 := Nat.mod_eq_of_lt (by omega)
  have m22 : p22 % 2 ^ 128 = p22 := Nat.mod_eq_of_lt (by omega)
  rw [m11, m12, m21, m22]
  have q12 := Nat.div_add_mod p12 18446744073709551616
  have q21 := Nat.div_add_mod p21 18446744073709551616
  have q22 := Nat.div_add_mod p22 18446744073709551616
  have r12 := Nat.mod_lt p12 (show 0 < 18446744073709551616 by omega)
  have r21 := Nat.mod_lt p21 (show 0 < 18446744073709551616 by omega)
  have r22 := Nat.mod_lt p22 (show 0 < 18446744073709551616 by omega)
  generalize p12 / 18446744073709551616 = d12 at *
  generalize p21 / 18446744073709551616 = d21 at *
  generalize p22 / 18446744073709551616 = d22 at *
  generalize p12 % 18446744073709551616 = e12 at *
  generalize p21 % 18446744073709551616 = e21 at *
  generalize p22 % 18446744073709551616 = e22 at *
  subst q12 q21 q22
  omega

theorem mulHiU128_pattern (a b : JInt .u128) :
    pattern (mul_hi_UInt128 a b) = pattern a * pattern b / 2 ^ 128 := by
  have hsh : mul (sizeof a) (lit .i64 4) = lit .i64 64 := by unfold sizeof; decide
  have h64 : 0 ≤ (lit IntTy.i64 64).val := by decide
  have h64' : (lit IntTy.i64 64).val.toNat = 64 := by decide
  have hmax : pattern typemax_UInt128 = 2 ^ 128 - 1 := by decide
  have hm : pattern (shr_Int typemax_UInt128 (lit .i64 64)) = 18446744073709551615 := by
    rw [shr_Int_unsigned_pattern rfl _ _ h64, hmax, h64']
  have hl := fun (x : JInt .u128) => pattern_lshr_Int x (lit .i64 64) h64
  have hA := pattern_lt a
  have hB := pattern_lt b
  unfold mul_hi_UInt128
  simp only [hsh, add, mul_128, pattern_add_int, pattern_mul_int, hl, h64', pattern_band, hm,
    and_mask64, IntTy.bits]
  generalize pattern a = A at hA ⊢
  generalize pattern b = B at hB ⊢
  simp only [IntTy.bits] at hA hB
  have dA := Nat.div_add_mod' A 18446744073709551616
  have rA := Nat.mod_lt A (show 0 < 18446744073709551616 by omega)
  have dB := Nat.div_add_mod' B 18446744073709551616
  have rB := Nat.mod_lt B (show 0 < 18446744073709551616 by omega)
  generalize A / 18446744073709551616 = a1 at dA rA ⊢
  generalize A % 18446744073709551616 = a2 at dA rA ⊢
  generalize B / 18446744073709551616 = b1 at dB rB ⊢
  generalize B % 18446744073709551616 = b2 at dB rB ⊢
  subst dA dB
  exact limb_high a1 a2 b1 b2 (by omega) rA (by omega) rB

theorem mulHiU128_val (a b : JInt .u128) : (mul_hi_UInt128 a b).val = (a.val * b.val) / 2 ^ 128 := by
  rw [← val_of_unsigned_pattern rfl (mul_hi_UInt128 a b), mulHiU128_pattern,
    ← val_of_unsigned_pattern rfl a, ← val_of_unsigned_pattern rfl b, Int.natCast_ediv,
    Int.natCast_mul, Int.natCast_pow]
  rfl

theorem wrapU128_pattern (v : JInt .i128) : wrapInt .u128 v.val = (pattern v : Int) := by
  rw [pattern_cast]
  simp [wrapInt, IntTy.signed, IntTy.bits]

theorem shr127_val (x : JInt .i128) : (shr_Int x (lit .i64 127)).val = if x.val < 0 then -1 else 0 := by
  have hx := x.property
  have h := (shiftIntCount_proven .i128 x (lit .i64 127)).1
  have h127 : (lit IntTy.i64 127).val = 127 := by decide
  rw [h127] at h
  rw [h]
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx ⊢
  split <;> omega

theorem pattern_sign_mask (x y : JInt .i128) :
    pattern (band (shr_Int x (lit .i64 127)) y) = if x.val < 0 then pattern y else 0 := by
  rw [pattern_band]
  have hy := pattern_lt y
  have hs := shr127_val x
  by_cases hn : x.val < 0
  · rw [if_pos hn] at hs
    rw [if_pos hn, pattern_of_cong _ (-1) (by rw [hs]; decide)]
    have e : ((-1 : Int) % ((2 ^ IntTy.i128.bits : Nat) : Int)).toNat = 2 ^ 128 - 1 := by decide
    rw [e, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt hy
  · rw [if_neg hn] at hs
    rw [if_neg hn, pattern_of_cong _ 0 (by rw [hs]; decide)]
    simp

theorem pattern_signed_cast (x : JInt .i128) :
    (pattern x : Int) = if x.val < 0 then x.val + 2 ^ 128 else x.val := by
  rw [pattern_cast]
  have hx := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx ⊢
  split <;> omega

theorem mulHiI128_val (a b : JInt .i128) : (mul_hi_Int128 a b).val = (a.val * b.val) / 2 ^ 128 := by
  have hsh : sub (mul (sizeof a) (lit .i64 8)) (lit .i64 1) = lit .i64 127 := by unfold sizeof; decide
  have ha := a.property
  have hb := b.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at ha hb
  have hp := mul_natAbs_le (x := a.val) (y := b.val) (a := 170141183460469231731687303715884105728)
    (b := 170141183460469231731687303715884105728) (by omega) (by omega)
  unfold mul_hi_Int128
  simp only [hsh, subWrap, remT_val, sub_int_val, mulHiU128_val, wrapU128_pattern, pattern_sign_mask]
  by_cases han : a.val < 0 <;> by_cases hbn : b.val < 0 <;>
    simp only [han, hbn, if_true, if_false, pattern_signed_cast] <;>
    push_cast <;>
    (try simp only [Int.add_mul, Int.mul_add]) <;>
    generalize a.val * b.val = ab at hp ⊢ <;>
    simp [wrapInt, IntTy.signed, IntTy.bits] <;>
    omega

/-- `mul_hi(a, b)` for `UInt128` and `Int128` is the higher half of the 256-bit product,
`floor(a*b / 2^128)` (docstring of `mul_hi`; `base/int.jl:126-142`). -/
def MulHi128 : Prop := (∀ a b : JInt .u128, (mul_hi_UInt128 a b).val = (a.val * b.val) / 2 ^ 128) ∧
  (∀ a b : JInt .i128, (mul_hi_Int128 a b).val = (a.val * b.val) / 2 ^ 128)
theorem mulHi128_proven : MulHi128 := ⟨mulHiU128_val, mulHiI128_val⟩

/-! ## Registry statements combining the methods of one function -/

/-- `unsigned(x)` gives the value of the unsigned type of the same size whose bits are those of `x`:
`x` itself for an unsigned `x` and `x + 2^n` for a negative signed `x` (docstring of `unsigned`:
"If the argument is signed, it is reinterpreted as unsigned without checking for negative values";
`base/int.jl:261-262`). -/
def UnsignedExact : Prop := UnsignedOfUnsigned ∧ UnsignedReinterprets
theorem unsignedExact_proven : UnsignedExact := ⟨unsignedOfUnsigned_proven, unsignedReinterprets_proven⟩

/-- `signed(x)` gives the value of the signed type of the same size whose bits are those of `x`:
`x` itself for a signed `x` and `x - 2^n` for an unsigned `x` of at least `2^(n-1)` (docstring of
`signed`: "If the argument is unsigned, it is reinterpreted as signed without checking for
overflow"; `base/int.jl:272-273`). -/
def SignedExact : Prop := SignedOfSigned ∧ SignedReinterprets
theorem signedExact_proven : SignedExact := ⟨signedOfSigned_proven, signedReinterprets_proven⟩

/-- `widen(T)` of every BitInteger type below 128 bits is the type of the same signedness and twice
the width, and it holds every sum and product of two values of `T`, and every difference when `T`
is signed (docstring of `widen`, `operators.jl:955-962`: "the result is guaranteed to be large
enough to hold all values of the type"; `base/int.jl:911-918`). -/
def WidenTypes : Prop :=
  (∀ t w : IntTy, widenType t = some w → w.bits = 2 * t.bits ∧ w.signed = t.signed) ∧
  WidenInt8 ∧ WidenInt16 ∧ WidenInt32 ∧ WidenInt64 ∧
  WidenUInt8 ∧ WidenUInt16 ∧ WidenUInt32 ∧ WidenUInt64
theorem widenTypes_proven : WidenTypes := by
  refine ⟨fun t w h => ?_, widenInt8_proven, widenInt16_proven, widenInt32_proven, widenInt64_proven,
    widenUInt8_proven, widenUInt16_proven, widenUInt32_proven, widenUInt64_proven⟩
  cases t <;> simp only [widenType, widen_Int8, widen_Int16, widen_Int32, widen_Int64, widen_UInt8,
    widen_UInt16, widen_UInt32, widen_UInt64, reduceCtorEq, Option.some.injEq] at h <;>
    subst h <;> decide

/-! ## `negate` (lines 95-98) -/

/-- `Base.negate(x)` of a signed BitInteger is the additive inverse of `x` in `x`'s type,
`x + negate(x) == 0`, and it is the exact negation `-x` unless `x == typemin(T)` (`base/int.jl:96`;
`negate` is the step negation of `range.jl:1322,1445,1451` and `broadcast.jl:1178-1209`). For an
unsigned `x` it is the exact `-x` in the signed type of the same size, or `InexactError`
(`NegateUnsigned`, `base/int.jl:97`). -/
def NegateExact : Prop :=
  (∀ t : IntTy, t.signed = true → ∀ x : JInt t,
    (add x (negate neg x)).val = 0 ∧ (x.val ≠ t.min → (negate neg x).val = -x.val)) ∧
  NegateUnsigned
theorem negateExact_proven : NegateExact := by
  refine ⟨fun t ht x => ?_, negateUnsigned_proven⟩
  have hx := x.property
  have hn : (negate neg x).val = wrapInt t (-x.val) := negWraps_proven t x
  refine ⟨?_, fun hm => ?_⟩
  · rw [addWraps_proven t x (negate neg x), hn, wrapInt_add_right, Int.add_right_neg]
    exact wrapInt_of_inRange t 0 (by cases t <;> decide)
  · rw [hn]
    apply wrapInt_of_inRange
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega

/-! ## `isodd`, `iseven` on `Number` (lines 143-181) -/

/-- `isodd(x)` is true exactly for odd integers and `iseven(x)` exactly for even integers
(docstrings of `isodd(x::Number)` and `iseven(x::Number)`): for every BitInteger `n` through the
`Real` methods (`base/int.jl:161,181`), and for every `z::Complex{T}` with BitInteger `T` through the
`Number` methods (`base/int.jl:160,180`) with `isreal`, `real` and `imag` of `base/complex.jl`: `z` is
an odd (even) integer exactly when its imaginary part is zero and its real part is odd (even).
`isinteger(::Integer) = true` is `base/number.jl`'s; `Integer(n)` (`boot.jl`), `rem(n, 2)`
(`promotion.jl`, then lines 356-358) and `iszero` (`number.jl`) are parameters with their
documented behaviour. -/
def ParityNumber : Prop := ∀ (t : IntTy) (Integer : JInt t → JInt t)
  (rem : JInt t → JInt .i64 → JInt (t.promote .i64)) (iszero : JInt (t.promote .i64) → Bool)
  (iszeroT : JInt t → Bool),
  (∀ n, Integer n = n) → (∀ n, (rem n (lit .i64 2)).val = n.val.tmod 2) →
  (∀ r, iszero r = decide (r.val = 0)) → (∀ r, iszeroT r = decide (r.val = 0)) →
  (∀ n : JInt t,
    isodd_Real JuliaLean.base.number.isintegerInteger Integer rem iszero n = decide (n.val % 2 = 1) ∧
    iseven_Real JuliaLean.base.number.isintegerInteger Integer rem iszero n = decide (n.val % 2 = 0)) ∧
  (∀ z : JuliaLean.base.complex.Complex (JInt t),
    isodd_Number (JuliaLean.base.complex.isreal_Complex iszeroT) JuliaLean.base.complex.real_Complex
        (isodd_Real JuliaLean.base.number.isintegerInteger Integer rem iszero) z =
      decide (z.im.val = 0 ∧ z.re.val % 2 = 1) ∧
    iseven_Number (JuliaLean.base.complex.isreal_Complex iszeroT) JuliaLean.base.complex.real_Complex
        (iseven_Real JuliaLean.base.number.isintegerInteger Integer rem iszero) z =
      decide (z.im.val = 0 ∧ z.re.val % 2 = 0))
theorem parityNumber_proven : ParityNumber := by
  intro t Integer rem iszero iszeroT hI hrem hz hzT
  have hP := parityExact_proven t Integer rem iszero hI hrem hz
  refine ⟨hP, fun z => ?_⟩
  simp only [isodd_Number, iseven_Number, JuliaLean.base.complex.isreal_Complex,
    JuliaLean.base.complex.real_Complex, JuliaLean.base.complex.imag_Complex, hzT, (hP z.re).1,
    (hP z.re).2]
  constructor <;> simp [Bool.decide_and]

/-! ## `widemul` with a `Bool` (lines 925-928) -/

/-- `widemul(b, y)` and `widemul(y, b)` of a `Bool` `b` and a BitInteger `y` are the exact product,
`y` or `0` ("multiplication by Bool doesn't require widening", `base/int.jl:925-928`; docstring of
`widemul`), with `b * y` and `y * b` the promoted `Integer` method of `base/int.jl:1092-1100`
(`promote_type(Bool, T) == T`). -/
def WidemulBool : Prop := ∀ (t : IntTy) (b : Bool) (y : JInt t),
  (widemul_Bool_Number mulBool b y).val = (if b then y.val else 0) ∧
  (widemul_Number_Bool (op_Integer t mul (remT t) (rem_Bool_Type t)) y b).val =
    (if b then y.val else 0)
theorem widemulBool_proven : WidemulBool := by
  intro t b y
  have h0 : wrapInt t 0 = 0 := wrapInt_of_inRange t 0 (by cases t <;> decide)
  have hb := remBool_proven t b
  simp only [widemul_Bool_Number, widemul_Number_Bool, mulBool, op_Integer, mul, mul_int_val,
    remT_val, wrapInt_val, rem_Bool_Type, hb]
  cases b <;> simp [wrapInt_val, h0]

/-! ## `@big_str` (lines 748-805) -/

/-- The characters `s` contain `_` right before or right after `.`. -/
def adjUnderscoreDot : List Char → Bool
  | a :: b :: rest => (a == '_' && b == '.') || (a == '.' && b == '_') || adjUnderscoreDot (b :: rest)
  | _ => false

theorem adjUnderscoreDot_prefix : ∀ (l m : List Char),
    adjUnderscoreDot (l ++ m) = false → adjUnderscoreDot l = false
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: l, m, h => by
    simp only [List.cons_append, adjUnderscoreDot, Bool.or_eq_false_iff] at h ⊢
    exact ⟨h.1, adjUnderscoreDot_prefix (b :: l) m h.2⟩

theorem big_str_loop_filter : ∀ (cs : List Char) (p : Char), adjUnderscoreDot (p :: cs) = false →
    big_str_loop cs (p == '_') (p == '.') = some (cs.filter (· != '_'))
  | [], _, _ => rfl
  | c :: cs, p, h => by
    simp only [adjUnderscoreDot, Bool.or_eq_false_iff] at h
    have h1 : (c == '_' && p == '.') = false := by rw [Bool.and_comm]; exact h.1.2
    have h2 : (c == '.' && p == '_') = false := by rw [Bool.and_comm]; exact h.1.1
    have ih := big_str_loop_filter cs c h.2
    simp only [big_str_loop, h1, h2, Bool.false_eq_true, if_false, ih, Option.map_some,
      List.filter_cons]
    by_cases hc : c = '_' <;> simp [hc]

/-- `@big_str` treats `_` as a separator (docstring: "For integers `_` is allowed in the string as a
separator"): for a string that neither starts nor ends with `_` and has no `_` next to a `.`, the
result is the `BigInt` parsed from the characters without the `_`s if they form one, else the
`BigFloat` they form, and otherwise an `ArgumentError` ("throw an `ArgumentError` if the string is
not a valid number"), for every `tryparse(BigInt, ·)` (`gmp.jl`) and `tryparse(BigFloat, ·)`
(`mpfr.jl`) (`base/int.jl:776-804`). -/
def BigStrSeparators : Prop := ∀ (α : Type) (tryparseBigInt tryparseBigFloat : List Char → Option α)
  (s : List Char), s.head? ≠ some '_' → s.getLast? ≠ some '_' → adjUnderscoreDot s = false →
  (∀ n, big_str tryparseBigInt tryparseBigFloat s = .ok n ↔
    (tryparseBigInt (s.filter (· != '_')) = some n ∨
      (tryparseBigInt (s.filter (· != '_')) = none ∧ tryparseBigFloat (s.filter (· != '_')) = some n))) ∧
  (tryparseBigInt (s.filter (· != '_')) = none → tryparseBigFloat (s.filter (· != '_')) = none →
    ∃ msg, big_str tryparseBigInt tryparseBigFloat s = .error (.argumentError msg))

/-- The underscore-removal step of `@big_str` (`base/int.jl:779-794`), named for the proof. -/
def bigStrNormalize (s : List Char) : Option (List Char) :=
  if s.contains '_' then
    match s with
    | [] => some []
    | c :: _ => (big_str_loop ((s.drop 1).dropLast) (c == '_') (c == '.')).map
        (fun mid => c :: mid ++ [s.getLast!])
  else some s

theorem big_str_of_normalized {α : Type} (P Q : List Char → Option α) (s d : List Char)
    (hd : bigStrNormalize s = some d) :
    (∀ n, big_str P Q s = .ok n ↔ (P d = some n ∨ (P d = none ∧ Q d = some n))) ∧
    (P d = none → Q d = none → ∃ msg, big_str P Q s = .error (.argumentError msg)) := by
  have e : big_str P Q s =
      match bigStrNormalize s with
      | none => .error (.argumentError s!"invalid number format {String.ofList s} for BigInt or BigFloat")
      | some d =>
        match P d with
        | some n => .ok n
        | none =>
          match Q d with
          | some n => .ok n
          | none => .error (.argumentError
              s!"invalid number format {String.ofList s} for BigInt or BigFloat") := rfl
  rw [e, hd]
  dsimp only
  refine ⟨fun n => ?_, fun hp hq => ?_⟩
  · cases hp : P d <;> cases hq : Q d <;> simp
  · rw [hp, hq]; exact ⟨_, rfl⟩

theorem bigStrSeparators_proven : BigStrSeparators := by
  intro α P Q s hh hl ha
  apply big_str_of_normalized
  unfold bigStrNormalize
  by_cases hc : s.contains '_' = true
  · rw [if_pos hc]
    match s, hh, hl, ha, hc with
    | [], _, _, _, hc => simp at hc
    | [c], hh, _, _, hc => exact absurd (by simpa using hc : '_' = c).symm (by simpa using hh)
    | c :: d :: rest, hh, hl, ha, _ =>
      obtain ⟨init, z, hiz⟩ : ∃ init z, d :: rest = init ++ [z] := by
        rcases List.eq_nil_or_concat (d :: rest) with h | ⟨L, b, h⟩
        · simp at h
        · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
      have hc' : c ≠ '_' := by simpa using hh
      have hz : z ≠ '_' := by
        intro e; apply hl; rw [hiz, ← List.cons_append, List.getLast?_concat, e]
      have ha' : adjUnderscoreDot (c :: init) = false :=
        adjUnderscoreDot_prefix (c :: init) [z] (by rw [List.cons_append, ← hiz]; exact ha)
      have hlast : (c :: (init ++ [z])).getLast! = z := by
        rw [← List.cons_append, List.getLast!_eq_getLast?_getD, List.getLast?_concat]
        rfl
      rw [hiz]
      simp only [List.drop_one, List.tail_cons, List.dropLast_concat, big_str_loop_filter init c ha',
        Option.map_some, hlast]
      simp [List.filter_cons, List.filter_append, hc', hz]
  · rw [if_neg hc]
    congr 1
    symm
    rw [List.filter_eq_self]
    intro a ha
    simp only [Bool.not_eq_true, List.contains_eq_any_beq, List.any_eq_false] at hc
    have h1 := hc a ha
    simp only [bne_iff_ne, ne_eq]
    intro e
    subst e
    simp at h1


/-! Nothing to promise:
- `signed(::Type{T}) where T<:Signed`@79: returns its argument unchanged; no behaviour beyond the identity
- `rem(x::T, ::Type{T}) where T<:Integer`@695: returns its argument unchanged; no behaviour beyond the identity
- `bswap(x::Union{Int8, UInt8, Bool})`@457: returns its argument unchanged; no behaviour beyond the identity
- `BitSigned32_types`@10-45 (and the other `Bit*_types` tuples and `Bit*` unions of lines 1-46):
  type constants that name sets of types; they have no behaviour of their own, and every method
  declared on them is stated below for each member type.
- `rem(x::Integer, T::Type{<:Integer})`@698: the fallback `convert(T, x)` for non-BitInteger
  arguments (source comment: "`x % T` falls back to `convert`"); BitInteger arguments reach the
  methods stated by `floatintcov-int-type-remainder` and the `int-rem-type-*` entries.
- `_mask1_uint128`@1101, `_mask2_uint128`@1103, `_mask4_uint128`@1104: constants used only by
  `bitreverse(x::BitInteger128)`, whose result is stated by `int-bitreverse`.
-/

/-! ## Registry -/

open JuliaLean.Registry in

/-- A custom integer's comparison with integer literals agrees with its mathematical value. -/
def GenericSignPredicates : Prop :=
  (∀ (I : Type) (value : I → Int) (lt : I → Int → Bool),
    (∀ x n, lt x n = decide (value x < n)) → ∀ x,
      Generic.signbit_Integer lt x = decide (value x < 0)) ∧
  (∀ (U : Type) (value : U → Int), (∀ x, 0 ≤ value x) → ∀ x,
    Generic.signbit_Unsigned x = decide (value x < 0) ∧
    Generic.isnegative_Unsigned x = decide (value x < 0))
theorem genericSignPredicates_proven : GenericSignPredicates := by
  constructor
  · intro I value lt h x
    exact h x 0
  · intro U value h x
    simp [Generic.signbit_Unsigned, Generic.isnegative_Unsigned, Int.not_lt.mpr (h x)]

/-- Unsigned absolute value is nonnegative and preserves the mathematical magnitude. -/
def GenericAbsUnsigned : Prop := ∀ (U : Type) (value : U → Int),
  (∀ x, 0 ≤ value x) → ∀ x,
    value (Generic.abs_Unsigned x) = (value x).natAbs ∧ 0 ≤ value (Generic.abs_Unsigned x)
theorem genericAbsUnsigned_proven : GenericAbsUnsigned := by
  intro U value h x
  dsimp only [Generic.abs_Unsigned]
  have := h x
  constructor <;> omega

/-- Generic complement flips every bit when unary minus and subtraction have their integer laws. -/
def GenericComplement : Prop := ∀ (I : Type) (value : I → Int)
    (neg : I → I) (sub : I → JInt .i64 → I),
  (∀ x, value (neg x) = -value x) →
  (∀ x y, value (sub x y) = value x - y.val) → ∀ x,
    value (bnot_Integer neg sub x) + value x = -1
theorem genericComplement_proven : GenericComplement := by
  intro I value neg sub hn hs x
  simp only [bnot_Integer, hs, hn]
  have : (lit .i64 1).val = 1 := rfl
  rw [this]
  omega

/-- An arbitrary finite integer representation has one zero for each unset bit. -/
def GenericZeroCount : Prop := ∀ (I : Type) (width : Nat) (bits : I → Nat → Bool)
    (neg : I → I) (sub : I → JInt .i64 → I) (count : I → JInt .i64),
  (∀ x k, k < width → bits (bnot_Integer neg sub x) k = !bits x k) →
  (∀ x, (count x).val = ((List.range width).countP (bits x) : Nat)) → ∀ x,
    (count_zeros_Integer count (bnot_Integer neg sub) x).val =
      (width : Int) - ((List.range width).countP (bits x) : Nat)
theorem genericZeroCount_proven : GenericZeroCount := by
  intro I width bits neg sub count hb hc x
  rw [count_zeros_Integer, hc]
  have he : ∀ (l : List Nat), (∀ k ∈ l, k < width) →
      l.countP (bits x) + l.countP (bits (bnot_Integer neg sub x)) = l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl
      have hi := ih (fun k hk => hl k (by simp [hk]))
      have ha := hb x a (hl a (by simp))
      simp only [List.countP_cons, List.length_cons, ha]
      cases bits x a <;> simp_all <;> omega
  have hh := he (List.range width) (fun k hk => List.mem_range.mp hk)
  simp only [List.length_range] at hh
  omega

/-- Leading-one counts locate the first unset bit in any finite representation. -/
def GenericLeadingOnes : Prop := ∀ (I : Type) (width : Nat) (bits : I → Nat → Bool)
    (neg : I → I) (sub : I → JInt .i64 → I) (count : I → JInt .i64),
  (∀ x k, k < width → bits (bnot_Integer neg sub x) k = !bits x k) →
  (∀ x, 0 ≤ (count x).val ∧ (count x).val ≤ width ∧
    (∀ k, k < (count x).val.toNat → bits x (width - 1 - k) = false) ∧
    ((count x).val.toNat < width → bits x (width - 1 - (count x).val.toNat) = true)) → ∀ x,
  let r := (leading_ones_Integer count (bnot_Integer neg sub) x).val
  0 ≤ r ∧ r ≤ width ∧
    (∀ k, k < r.toNat → bits x (width - 1 - k) = true) ∧
    (r.toNat < width → bits x (width - 1 - r.toNat) = false)
theorem genericLeadingOnes_proven : GenericLeadingOnes := by
  intro I width bits neg sub count hb hc x
  dsimp only [leading_ones_Integer]
  obtain ⟨h0, hw, hz, hs⟩ := hc (bnot_Integer neg sub x)
  refine ⟨h0, hw, ?_, ?_⟩
  · intro k hk
    have hk' : k < width := by omega
    have h := hz k hk
    rw [hb x _ (by omega)] at h
    cases he : bits x (width - 1 - k) <;> simp_all
  · intro hk
    have h := hs hk
    rw [hb x _ (by omega)] at h
    cases he : bits x (width - 1 - (count (bnot_Integer neg sub x)).val.toNat) <;> simp_all

/-- Trailing-one counts locate the first unset low bit in any finite representation. -/
def GenericTrailingOnes : Prop := ∀ (I : Type) (width : Nat) (bits : I → Nat → Bool)
    (neg : I → I) (sub : I → JInt .i64 → I) (count : I → JInt .i64),
  (∀ x k, k < width → bits (bnot_Integer neg sub x) k = !bits x k) →
  (∀ x, 0 ≤ (count x).val ∧ (count x).val ≤ width ∧
    (∀ k, k < (count x).val.toNat → bits x k = false) ∧
    ((count x).val.toNat < width → bits x (count x).val.toNat = true)) → ∀ x,
  let r := (trailing_ones_Integer count (bnot_Integer neg sub) x).val
  0 ≤ r ∧ r ≤ width ∧ (∀ k, k < r.toNat → bits x k = true) ∧
    (r.toNat < width → bits x r.toNat = false)
theorem genericTrailingOnes_proven : GenericTrailingOnes := by
  intro I width bits neg sub count hb hc x
  dsimp only [trailing_ones_Integer]
  obtain ⟨h0, hw, hz, hs⟩ := hc (bnot_Integer neg sub x)
  refine ⟨h0, hw, ?_, ?_⟩
  · intro k hk
    have h := hz k hk
    rw [hb x k (by omega)] at h
    cases he : bits x k <;> simp_all
  · intro hk
    have h := hs hk
    rw [hb x _ hk] at h
    cases he : bits x (count (bnot_Integer neg sub x)).val.toNat <;> simp_all

/-- Real parity tests classify every integral real value by divisibility by two. -/
def GenericParityReal : Prop := ∀ (R I : Type) (value : R → Int) (integerValue : I → Int)
    (isinteger : R → Bool) (Integer : R → I) (rem : I → JInt .i64 → Int),
  (∀ n, isinteger n = true → integerValue (Integer n) = value n) →
  (∀ n, rem n (lit .i64 2) = (integerValue n).tmod 2) → ∀ n,
    isodd_Real isinteger Integer rem (fun r => decide (r = 0)) n =
      (isinteger n && decide (value n % 2 = 1)) ∧
    iseven_Real isinteger Integer rem (fun r => decide (r = 0)) n =
      (isinteger n && decide (value n % 2 = 0))
theorem genericParityReal_proven : GenericParityReal := by
  intro R I value iv isinteger Integer rem hi hr n
  cases h : isinteger n
  · simp [isodd_Real, iseven_Real, h]
  · have hv := hi n h
    simp only [isodd_Real, iseven_Real, h, Bool.true_and, hr, hv]
    have ht : (value n).tmod 2 = 0 ↔ value n % 2 = 0 := by
      rw [← Int.dvd_iff_tmod_eq_zero, Int.dvd_iff_emod_eq_zero]
    have hm := Int.emod_nonneg (value n) (by decide : (2 : Int) ≠ 0)
    have hl := Int.emod_lt_of_pos (value n) (by decide : (0 : Int) < 2)
    constructor
    · by_cases hz : value n % 2 = 0
      · have htz := ht.mpr hz
        simp [htz, hz]
      · have htz : (value n).tmod 2 ≠ 0 := fun h => hz (ht.mp h)
        have h1 : value n % 2 = 1 := by omega
        simp [htz, h1]
    · simp only [ht]


structure BigStringLaws {B : Type} (ops : Generic.BigStringOps B) (view : B → List Char) : Prop where
  initial : ∀ n, view (ops.ioBuffer n) = []
  printed : ∀ b c, view (ops.print b c) = view b ++ [c]
  taken : ∀ b, ops.unsafe_takestring b = String.ofList (view b)
  first : ∀ c cs, ops.getindex (String.ofList (c :: cs)) 1 = c
  last : ∀ c cs, ops.getindex (String.ofList (c :: cs))
    (ops.lastindex (String.ofList (c :: cs))) = (c :: cs).getLast!
  middle : ∀ cs, ops.substring (String.ofList cs) (ops.nextind (String.ofList cs) 1)
    (ops.prevind (String.ofList cs) (ops.lastindex (String.ofList cs))) = (cs.drop 1).dropLast
  contains : ∀ cs, (String.ofList cs).contains '_' = cs.contains '_'

theorem big_str_print_loop_view {B : Type} (print : B → Char → B) (view : B → List Char)
    (hp : ∀ b c, view (print b c) = view b ++ [c]) (cs : List Char)
    (bf : B) (u d : Bool) :
    (Generic.big_str_print_loop print cs bf u d).map view =
      (big_str_loop cs u d).map (fun rest => view bf ++ rest) := by
  induction cs generalizing bf u d with
  | nil => simp [Generic.big_str_print_loop, big_str_loop]
  | cons c cs ih =>
    by_cases hu : c = '_'
    · subst c
      cases u <;> cases d <;> simp [Generic.big_str_print_loop, big_str_loop, ih]
    · by_cases hd : c = '.'
      · subst c
        cases u <;> cases d <;>
          simp [Generic.big_str_print_loop, big_str_loop, ih, hp, List.append_assoc, Function.comp_def]
      · cases u <;> cases d <;>
          simp [Generic.big_str_print_loop, big_str_loop, hu, hd, ih, hp, List.append_assoc, Function.comp_def]

theorem big_str_source_eq {α B : Type} (ops : Generic.BigStringOps B) (view : B → List Char)
    (hl : BigStringLaws ops view) (integer floating : String → Option α) (cs : List Char) :
    Generic.big_str ops integer floating (String.ofList cs) =
      big_str (fun l => integer (String.ofList l)) (fun l => floating (String.ofList l)) cs := by
  unfold Generic.big_str big_str
  rw [hl.contains]
  by_cases hc : cs.contains '_' = true
  · simp only [hc, ite_true]
    cases cs with
    | nil => simp at hc
    | cons c cs =>
      simp only [hl.first, hl.middle, hl.last, List.drop_succ_cons, List.drop_zero]
      have hv := big_str_print_loop_view ops.print view hl.printed cs.dropLast
        (ops.print (ops.ioBuffer (ops.ncodeunits (String.ofList (c :: cs)))) c)
        (c == '_') (c == '.')
      cases he : Generic.big_str_print_loop ops.print cs.dropLast
          (ops.print (ops.ioBuffer (ops.ncodeunits (String.ofList (c :: cs)))) c)
          (c == '_') (c == '.') with
      | none =>
        rw [he] at hv
        simp only [Option.map_none] at hv
        cases hm : big_str_loop cs.dropLast (c == '_') (c == '.') with
        | none => rfl
        | some rest => rw [hm] at hv; cases hv
      | some bf =>
        rw [he] at hv
        simp only [Option.map_some, hl.printed, hl.initial, List.nil_append] at hv
        cases hm : big_str_loop cs.dropLast (c == '_') (c == '.') with
        | none => rw [hm] at hv; cases hv
        | some rest =>
          rw [hm] at hv
          have hv' : view bf = [c] ++ rest := Option.some.inj hv
          simp only [hl.taken, hl.printed, hv', List.append_assoc, List.singleton_append,
            List.cons_append, List.nil_append, Option.map_some]
  · have hf : cs.contains '_' = false := by cases h : cs.contains '_' <;> simp_all
    simp only [hf, Bool.false_eq_true, ite_false]



/-- The parser laws used by the separator check: a decimal trailing dot is legal, while
an underscore alone is not a number. These are interface facts, not a parser implementation. -/
structure BigParserLaws {α : Type} (integer floating : String → Option α) (one : α) : Prop where
  integer_trailing_dot : integer "1." = none
  float_trailing_dot : floating "1." = some one
  integer_underscore : integer "_" = none
  float_underscore : floating "_" = none

/-- A concrete instance of precisely the parser interface laws used by the refutation. -/
def lawfulIntegerParserWitness (s : String) : Option Int :=
  if s = "0" then some 0 else if s = "1" then some 1 else none

def lawfulFloatParserWitness (s : String) : Option Int :=
  if s = "1." then some 1 else none

theorem lawfulParserWitness_laws :
    BigParserLaws lawfulIntegerParserWitness lawfulFloatParserWitness 1 := by
  constructor <;> decide

/-- Character-sequence implementation of the string/IOBuffer interface. The indices are
positions in the character sequence, with 1 as the first index. -/
def bigStringInterface : Generic.BigStringOps (List Char) where
  ncodeunits := fun s => s.utf8ByteSize
  getindex := fun s i => (s.toList[i - 1]?).getD '\x00'
  nextind := fun _ i => i + 1
  prevind := fun _ i => i - 1
  lastindex := fun s => s.toList.length
  substring := fun s a b => (s.toList.drop (a - 1)).take (b + 1 - a)
  ioBuffer := fun _ => []
  print := fun b c => b ++ [c]
  unsafe_takestring := String.ofList

/-- Without separators, the macro returns the integer parse if successful, then the floating
parse, and rejects a string if both parsers reject it. -/
def BigStrNoSeparators : Prop := ∀ (α B : Type) (ops : Generic.BigStringOps B)
    (integer floating : String → Option α) (s : String), s.contains '_' = false →
  (∀ n, Generic.big_str ops integer floating s = .ok n ↔
    integer s = some n ∨ (integer s = none ∧ floating s = some n)) ∧
  ((∃ msg, Generic.big_str ops integer floating s = .error (.argumentError msg)) ↔
    integer s = none ∧ floating s = none)
theorem bigStrNoSeparators_proven : BigStrNoSeparators := by
  intro α B ops integer floating s hs
  simp only [Generic.big_str, hs, Bool.false_eq_true, ite_false]
  cases hi : integer s <;> cases hf : floating s <;> simp [hi, hf]

/-- The source's underscore/dot check must run before parsing, including the final character. -/
def BigStrSourceUnderscoreDot : Prop := ∀ (α : Type) (integer floating : String → Option α)
    (one : α), BigParserLaws integer floating one → ∀ (s : String),
  adjUnderscoreDot s.toList = true →
    ∃ msg, Generic.big_str bigStringInterface integer floating s = .error (.argumentError msg)
theorem bigStrSourceUnderscoreDot_refuted : ¬ BigStrSourceUnderscoreDot := by
  intro h
  obtain ⟨msg, hm⟩ := h Int lawfulIntegerParserWitness lawfulFloatParserWitness 1
    lawfulParserWitness_laws "1_." (by decide)
  have hv : Generic.big_str bigStringInterface lawfulIntegerParserWitness lawfulFloatParserWitness
      "1_." = .ok 1 := by
    simp [Generic.big_str, bigStringInterface, Generic.big_str_print_loop,
      lawfulIntegerParserWitness, lawfulFloatParserWitness]
  rw [hv] at hm
  cases hm



/-- Generic real-to-signed sign forwarding preserves the magnitude and flips according to
signbit, using the documented laws of the custom signed type's same-type operations. -/
def GenericFlipsignReal : Prop := ∀ (S R : Type) (value : S → Int) (wrap : Int → Int)
    (sb : R → Bool) (oftype : S → Bool → S) (neg : S → S) (flip : S → S → S),
  wrap (-1) = -1 → wrap 0 = 0 →
  (∀ x b, value (oftype x b) = if b then 1 else 0) →
  (∀ x, value (neg x) = wrap (-value x)) →
  (∀ x y, value (flip x y) = wrap (if value y < 0 then -value x else value x)) → ∀ x y,
    value (Generic.flipsign_Real sb oftype neg flip x y) =
      wrap (if sb y then -value x else value x)
theorem genericFlipsignReal_proven : GenericFlipsignReal := by
  intro S R value wrap sb oftype neg flip hm hz ho hn hf x y
  simp only [Generic.flipsign_Real, hf, hn, ho]
  cases h : sb y <;> simp [h, hm, hz]

/-- Signed absolute value has the magnitude of x, with the type's wrapping convention. -/
def GenericAbsSigned : Prop := ∀ (S : Type) (value : S → Int) (wrap : Int → Int)
    (flip : S → S → S),
  (∀ x y, value (flip x y) = wrap (if value y < 0 then -value x else value x)) → ∀ x,
    value (Generic.abs_Signed flip x) = wrap ((value x).natAbs : Int)
theorem genericAbsSigned_proven : GenericAbsSigned := by
  intro S value wrap flip hf x
  rw [Generic.abs_Signed, hf]
  have he : (if value x < 0 then -value x else value x) = ((value x).natAbs : Int) := by
    split <;> omega
  rw [he]

/-- The sign of a signed xor is the xor of operand signs; copying a sign gives the
corresponding magnitude, subject to the signed type's overflow convention. -/
def GenericCopysignSigned : Prop := ∀ (S T X : Type) (sv : S → Int) (tv : T → Int)
    (xv : X → Int) (wrap : Int → Int) (xor : S → T → X) (flip : S → X → S),
  (∀ x y, xv (xor x y) < 0 ↔ (sv x < 0 ∧ 0 ≤ tv y) ∨ (0 ≤ sv x ∧ tv y < 0)) →
  (∀ x y, sv (flip x y) = wrap (if xv y < 0 then -sv x else sv x)) → ∀ x y,
    sv (Generic.copysign_Signed xor flip x y) =
      wrap (if tv y < 0 then -((sv x).natAbs : Int) else (sv x).natAbs)
theorem genericCopysignSigned_proven : GenericCopysignSigned := by
  intro S T X sv tv xv wrap xor flip hx hf x y
  rw [Generic.copysign_Signed, hf]
  congr 1
  simp only [hx]
  by_cases hs : sv x < 0 <;> by_cases ht : tv y < 0 <;> simp [hs, ht] <;> omega

/-- Signed-float sign forwarding uses the stored sign bit, including signed zeros and NaNs. -/
def GenericFloatFlipsign : Prop := ∀ (S : Type) (value : S → Int) (wrap : Int → Int)
    (flip16 : S → JInt .i16 → S) (flip32 : S → JInt .i32 → S) (flip64 : S → JInt .i64 → S),
  (∀ x y, value (flip16 x y) = wrap (if y.val < 0 then -value x else value x)) →
  (∀ x y, value (flip32 x y) = wrap (if y.val < 0 then -value x else value x)) →
  (∀ x y, value (flip64 x y) = wrap (if y.val < 0 then -value x else value x)) →
  ∀ (x : S) (a : Fl half) (b : Fl single) (c : Fl double),
    value (Generic.flipsign_Float16 flip16 x a) = wrap (if 2 ^ 15 ≤ a.toBits then -value x else value x) ∧
    value (Generic.flipsign_Float32 flip32 x b) = wrap (if 2 ^ 31 ≤ b.toBits then -value x else value x) ∧
    value (Generic.flipsign_Float64 flip64 x c) = wrap (if 2 ^ 63 ≤ c.toBits then -value x else value x)
theorem genericFloatFlipsign_proven : GenericFloatFlipsign := by
  intro S value wrap f16 f32 f64 h16 h32 h64 x a b c
  simp only [Generic.flipsign_Float16, Generic.flipsign_Float32, Generic.flipsign_Float64,
    h16, h32, h64, bitcastFloat_neg .i16 a (by decide) rfl,
    bitcastFloat_neg .i32 b (by decide) rfl, bitcastFloat_neg .i64 c (by decide) rfl]
  exact ⟨rfl, rfl, rfl⟩

/-- Generic unsigned negation returns the exact negative when conversion to Signed succeeds,
and propagates the documented conversion exception otherwise. -/
def GenericNegateUnsigned : Prop := ∀ (U S : Type) (uv : U → Int) (sv : S → Int)
    (convert : U → Jl S) (neg : S → S),
  (∀ x y, convert x = .ok y → sv y = uv x) →
  (∀ y, 0 ≤ sv y → sv (neg y) = -sv y) → (∀ x, 0 ≤ uv x) → ∀ x,
  (∀ y, Generic.negate_Unsigned convert neg x = .ok y → sv y = -uv x) ∧
  (∀ e, Generic.negate_Unsigned convert neg x = .error e ↔ convert x = .error e)
theorem genericNegateUnsigned_proven : GenericNegateUnsigned := by
  intro U S uv sv convert neg hc hn hu x
  cases he : convert x with
  | error e => simp [Generic.negate_Unsigned, he, Functor.map, Except.map]
  | ok y =>
    have hv := hc x y he
    have hn' := hn y (by rw [hv]; exact hu x)
    simp [Generic.negate_Unsigned, he, Functor.map, Except.map, hn', hv]


def GenericFloatCopysign : Prop := ∀ (S : Type) (value : S → Int) (wrap : Int → Int)
    (flip16 : S → JInt .i16 → S) (flip32 : S → JInt .i32 → S) (flip64 : S → JInt .i64 → S),
  (∀ x y, value (flip16 x y) = wrap (if y.val < 0 then -((value x).natAbs : Int) else (value x).natAbs)) →
  (∀ x y, value (flip32 x y) = wrap (if y.val < 0 then -((value x).natAbs : Int) else (value x).natAbs)) →
  (∀ x y, value (flip64 x y) = wrap (if y.val < 0 then -((value x).natAbs : Int) else (value x).natAbs)) →
  ∀ (x : S) (a : Fl half) (b : Fl single) (c : Fl double),
    value (Generic.copysign_Float16 flip16 x a) = wrap (if 2 ^ 15 ≤ a.toBits then -((value x).natAbs : Int) else (value x).natAbs) ∧
    value (Generic.copysign_Float32 flip32 x b) = wrap (if 2 ^ 31 ≤ b.toBits then -((value x).natAbs : Int) else (value x).natAbs) ∧
    value (Generic.copysign_Float64 flip64 x c) = wrap (if 2 ^ 63 ≤ c.toBits then -((value x).natAbs : Int) else (value x).natAbs)
theorem genericFloatCopysign_proven : GenericFloatCopysign := by
  intro S value wrap f16 f32 f64 h16 h32 h64 x a b c
  simp only [Generic.copysign_Float16, Generic.copysign_Float32, Generic.copysign_Float64,
    h16, h32, h64, bitcastFloat_neg .i16 a (by decide) rfl,
    bitcastFloat_neg .i32 b (by decide) rfl, bitcastFloat_neg .i64 c (by decide) rfl]
  exact ⟨rfl, rfl, rfl⟩



/-- The source-mirrored String/IOBuffer method parses legal underscore separators exactly
as the separator-free number, under the string and buffer interface laws. -/
def BigStrSourceSeparators : Prop := ∀ (α B : Type) (ops : Generic.BigStringOps B)
    (view : B → List Char), BigStringLaws ops view →
    ∀ (integer floating : String → Option α) (cs : List Char),
  cs.head? ≠ some '_' → cs.getLast? ≠ some '_' → adjUnderscoreDot cs = false →
  (∀ n, Generic.big_str ops integer floating (String.ofList cs) = .ok n ↔
    integer (String.ofList (cs.filter (· != '_'))) = some n ∨
    (integer (String.ofList (cs.filter (· != '_'))) = none ∧
      floating (String.ofList (cs.filter (· != '_'))) = some n)) ∧
  ((∃ msg, Generic.big_str ops integer floating (String.ofList cs) = .error (.argumentError msg)) ↔
    integer (String.ofList (cs.filter (· != '_'))) = none ∧
    floating (String.ofList (cs.filter (· != '_'))) = none)
theorem bigStrSourceSeparators_proven : BigStrSourceSeparators := by
  intro α B ops view hl integer floating cs hh ht ha
  rw [big_str_source_eq ops view hl]
  have hp := bigStrSeparators_proven α (fun l => integer (String.ofList l))
    (fun l => floating (String.ofList l)) cs hh ht ha
  refine ⟨hp.1, ⟨?_, fun h => hp.2 h.1 h.2⟩⟩
  rintro ⟨msg, he⟩
  cases hi : integer (String.ofList (cs.filter (· != '_'))) with
  | some n =>
    have hv := (hp.1 n).mpr (Or.inl hi)
    rw [hv] at he
    cases he
  | none =>
    refine ⟨rfl, ?_⟩
    cases hf : floating (String.ofList (cs.filter (· != '_'))) with
    | none => rfl
    | some n =>
      have hv := (hp.1 n).mpr (Or.inr ⟨hi, hf⟩)
      rw [hv] at he
      cases he

/-- The generated remainder methods preserve the unique representable residue. -/
def GeneratedRemMethods : Prop := RemTypeResidue ∧ RemTruncates ∧ RemBool ∧ RemSignExtends ∧ RemZeroExtends ∧ RemReinterprets
theorem generatedRemMethods_proven : GeneratedRemMethods :=
  ⟨remTypeResidue_proven, remTruncates_proven, remBool_proven, remSignExtends_proven, remZeroExtends_proven, remReinterprets_proven⟩

def AllZeroCounts : Prop := CountOnesZeros ∧ GenericZeroCount
theorem allZeroCounts_proven : AllZeroCounts := ⟨countOnesZeros_proven, genericZeroCount_proven⟩
def AllLeadingOnes : Prop := LeadingOnes ∧ GenericLeadingOnes
theorem allLeadingOnes_proven : AllLeadingOnes := ⟨leadingOnes_proven, genericLeadingOnes_proven⟩
def AllTrailingOnes : Prop := TrailingOnes ∧ GenericTrailingOnes
theorem allTrailingOnes_proven : AllTrailingOnes := ⟨trailingOnes_proven, genericTrailingOnes_proven⟩

/-- A Bool occupies one byte; reversal preserves that byte's value, including true. -/
def AllByteSwap : Prop := ByteSwap ∧ ∀ b : Bool,
  (if bswap_small b then (1 : Nat) else 0) =
    byteOf (if b then 1 else 0) (1 - 1)
theorem allByteSwap_proven : AllByteSwap := by
  refine ⟨byteSwap_proven, ?_⟩
  intro b
  cases b <;> decide

/-- A rotation count can have any integer type; only its residue modulo the word size
influences the result. Masking and negation have their documented residue laws. -/
def GenericBitRotate : Prop := ∀ (K : Type) (value : K → Int)
    (mask : JInt .i64 → K → JInt .i64) (negK : K → K) (t : IntTy),
  (∀ k, (mask (sub (shl_Int (lit .i64 (sizeofT t)) (lit .i64 3)) (lit .i64 1)) k).val =
    value k % (t.bits : Int)) →
  (∀ k, value (negK k) % (t.bits : Int) = (-value k) % (t.bits : Int)) →
  ∀ (x : JInt t) (k : K) (j : Nat), j < t.bits →
    bitOf (bitrotate mask negK shl_Int lshr_Int x k) j =
      bitOf x ((j + t.bits - (value k % t.bits).toNat) % t.bits)
theorem genericBitRotate_proven : GenericBitRotate := by
  intro K value mask negK t hm hn x k j hj
  let q := lit .i64 (value k % (t.bits : Int))
  have hq : q.val = value k % (t.bits : Int) := by
    have hpos : (0 : Int) < t.bits := by cases t <;> decide
    have hlo := Int.emod_nonneg (value k) (by omega : (t.bits : Int) ≠ 0)
    have hhi := Int.emod_lt_of_pos (value k) hpos
    change wrapInt .i64 (value k % (t.bits : Int)) = _
    apply wrapInt_of_inRange
    cases t <;> simp_all [IntTy.bits, IntTy.min, IntTy.max, IntTy.signed] <;> omega
  have hqn : (neg q).val % (t.bits : Int) = (-value k) % (t.bits : Int) := by
    rw [neg, neg_int_val, hq]
    cases t <;> simp [wrapInt, IntTy.bits, IntTy.signed] <;> omega
  have he : bitrotate mask negK shl_Int lshr_Int x k = bitrotate band neg shl_Int lshr_Int x q := by
    dsimp only [bitrotate]
    congr 1
    · apply congrArg (shl_Int x)
      apply jint_eq
      rw [hm, val_eq_wrap_pattern (band _ _), pattern_rot_count, hq]
      cases t <;> simp [wrapInt, IntTy.bits, IntTy.signed] <;> omega
    · apply congrArg (lshr_Int x)
      apply jint_eq
      rw [hm, hn, val_eq_wrap_pattern (band _ _), pattern_rot_count, hqn]
      cases t <;> simp [wrapInt, IntTy.bits, IntTy.signed] <;> omega
  rw [he, bitRotate_proven t x q j hj, hq, Int.emod_emod]

def AllBitRotate : Prop := BitRotate ∧ GenericBitRotate
theorem allBitRotate_proven : AllBitRotate := ⟨bitRotate_proven, genericBitRotate_proven⟩



def promotedRem {s : IntTy} (x : JInt s) (T : IntTy) : Jl (JInt T) := .ok (remT T x)
def promotedOp (op : {t : IntTy} → JInt t → JInt t → JInt t)
    (T : IntTy) (a b : JInt T) : Jl (JInt T) := .ok (op a b)

/-- Checked generated arithmetic methods calculate the mathematical operation modulo the
promoted word size, with the promotion module's documented successful type-change check. -/
def CheckedPromotedArithmetic : Prop := ∀ (s t : IntTy), s ≠ t →
  ∀ (check : JInt s × JInt t → (T : IntTy) → JInt T × JInt T → Jl Unit),
  (∀ ab T r, check ab T r = .ok ()) → ∀ (x : JInt s) (y : JInt t),
  (Generated.add_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp add) x y).map Subtype.val = .ok (wrapInt (s.promote t) (x.val + y.val)) ∧
  (Generated.sub_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp sub) x y).map Subtype.val = .ok (wrapInt (s.promote t) (x.val - y.val)) ∧
  (Generated.mul_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp mul) x y).map Subtype.val = .ok (wrapInt (s.promote t) (x.val * y.val)) ∧
  (Generated.addWrap_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp addWrap) x y).map Subtype.val = .ok (wrapInt (s.promote t) (x.val + y.val)) ∧
  (Generated.subWrap_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp subWrap) x y).map Subtype.val = .ok (wrapInt (s.promote t) (x.val - y.val)) ∧
  (Generated.mulWrap_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp mulWrap) x y).map Subtype.val = .ok (wrapInt (s.promote t) (x.val * y.val))
theorem checkedPromotedArithmetic_proven : CheckedPromotedArithmetic := by
  intro s t hst check hc x y
  have hp := promotedArithmeticWraps_proven s t x y
  simp only [op_Integer] at hp
  simpa only [Generated.add_Integer, Generated.sub_Integer, Generated.mul_Integer,
    Generated.addWrap_Integer, Generated.subWrap_Integer, Generated.mulWrap_Integer,
    promotedRem, promotedOp, hc, bind, Except.bind, Except.map, pure, Except.pure,
    Except.ok.injEq] using hp

/-- Each bitwise generated operator applies its Boolean truth table to the promoted
representation, including mixed widths and signedness. -/
def CheckedPromotedBits : Prop := ∀ (s t : IntTy), s ≠ t →
  ∀ (check : JInt s × JInt t → (T : IntTy) → JInt T × JInt T → Jl Unit),
  (∀ ab T r, check ab T r = .ok ()) → ∀ (x : JInt s) (y : JInt t) (k : Nat),
  (Generated.and_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp band) x y).map (fun r => bitOf r k) =
    .ok (bitOfInt (s.promote t).bits x.val k && bitOfInt (s.promote t).bits y.val k) ∧
  (Generated.or_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp bor) x y).map (fun r => bitOf r k) =
    .ok (bitOfInt (s.promote t).bits x.val k || bitOfInt (s.promote t).bits y.val k) ∧
  (Generated.xor_Integer (fun _ _ => s.promote t) promotedRem promotedRem check
    (promotedOp bxor) x y).map (fun r => bitOf r k) =
    .ok (bitOfInt (s.promote t).bits x.val k ^^ bitOfInt (s.promote t).bits y.val k)
theorem checkedPromotedBits_proven : CheckedPromotedBits := by
  intro s t hst check hc x y k
  have hr (a : IntTy) (v : JInt a) :
      bitOf (remT (s.promote t) v) k = bitOfInt (s.promote t).bits v.val k := by
    unfold bitOf bitOfInt
    rw [remT_val, wrapInt_emod_self]
  simp only [Generated.and_Integer, Generated.or_Integer, Generated.xor_Integer,
    promotedRem, promotedOp, hc, bind, Except.bind, Except.map, pure, Except.pure,
    bitOf_band, bitOf_bor, bitOf_bxor, hr, Except.ok.injEq]
  trivial




/-- Generic mod-to-type and unsafe_trunc preserve exactly the converted residue, including
conversion errors, through int.jl's actual fallback remainder method. -/
def GenericTypeResidues : Prop := ∀ (I O : Type) (value : I → Int) (outValue : O → Int)
    (residue : Int → Int) (convert : I → Jl O),
  (∀ x, (convert x).map outValue = .ok (residue (value x))) → ∀ x,
  (Generic.mod_Integer_Type (fun x (_ : Unit) => rem_Integer_Type convert x) () x).map outValue =
    .ok (residue (value x)) ∧
  (Generic.unsafe_trunc (fun x (_ : Unit) => rem_Integer_Type convert x) () x).map outValue =
    .ok (residue (value x))
theorem genericTypeResidues_proven : GenericTypeResidues := by
  intro I O value outValue residue convert hc x
  exact ⟨hc x, hc x⟩

/-- The Bool type remainder checks the low bit, for every custom integer type. -/
def GenericRemBool : Prop := ∀ (I R : Type) (value : I → Int) (rv : R → Int)
    (band : I → Int → R) (neq : R → Int → Bool),
  (∀ x, rv (band x 1) = value x % 2) →
  (∀ r n, neq r n = decide (rv r ≠ n)) → ∀ x,
    Generic.rem_Integer_Bool band neq x = decide (value x % 2 = 1)
theorem genericRemBool_proven : GenericRemBool := by
  intro I R value rv band neq hb hn x
  simp only [Generic.rem_Integer_Bool, hn, hb]
  have h0 := Int.emod_nonneg (value x) (by decide : (2 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos (value x) (by decide : (0 : Int) < 2)
  by_cases hz : value x % 2 = 0 <;> simp [hz] <;> omega

/-- Widened multiplication is the full mathematical product on custom signed/unsigned
integer types, provided widening and conversion preserve the values as documented. -/
def GenericWidemul : Prop := ∀ (S U WS WU SU O : Type) (sv : S → Int) (uv : U → Int)
    (wsv : WS → Int) (wuv : WU → Int) (suv : SU → Int) (ov : O → Int)
    (widenS : S → WS) (widenU : U → WU) (zero : WU → WU) (convert : WU → SU)
    (typeof : SU → Unit) (rem : WU → Unit → SU)
    (mulSU : WS → SU → O) (mulUS : SU → WS → O),
  (∀ x, wsv (widenS x) = sv x) → (∀ y, wuv (widenU y) = uv y) →
  (∀ y T, suv (rem y T) = wuv y) →
  (∀ x y, ov (mulSU x y) = wsv x * suv y) →
  (∀ y x, ov (mulUS y x) = suv y * wsv x) → ∀ x y,
  ov (Generic.widemul_Signed_Unsigned widenS widenU
    (Generic.signed zero convert typeof rem) mulSU x y) = sv x * uv y ∧
  ov (Generic.widemul_Unsigned_Signed widenU widenS
    (Generic.signed zero convert typeof rem) mulUS y x) = uv y * sv x
theorem genericWidemul_proven : GenericWidemul := by
  intro S U WS WU SU O sv uv wsv wuv suv ov widenS widenU zero convert typeof rem
    mulSU mulUS hs hu hr hm1 hm2 x y
  simp [Generic.widemul_Signed_Unsigned, Generic.widemul_Unsigned_Signed,
    Generic.signed, hm1, hm2, hr, hs, hu]

/-- Every Number's parity test is false for non-real values; for real values the parity
is that of the integral real part, using the actual int.jl real-parity method. -/
def GenericParityNumbers : Prop := ∀ (N R I : Type) (isreal : N → Bool) (real : N → R)
    (isinteger : R → Bool) (Integer : R → I) (value : R → Int) (iv : I → Int)
    (rem : I → JInt .i64 → Int),
  (∀ n, isinteger n = true → iv (Integer n) = value n) →
  (∀ n, rem n (lit .i64 2) = (iv n).tmod 2) → ∀ n,
  isodd_Number isreal real (isodd_Real isinteger Integer rem (fun r => decide (r = 0))) n =
    (isreal n && isinteger (real n) && decide (value (real n) % 2 = 1)) ∧
  iseven_Number isreal real (iseven_Real isinteger Integer rem (fun r => decide (r = 0))) n =
    (isreal n && isinteger (real n) && decide (value (real n) % 2 = 0))
theorem genericParityNumbers_proven : GenericParityNumbers := by
  intro N R I isreal real isinteger Integer value iv rem hi hr n
  have hp := genericParityReal_proven R I value iv isinteger Integer rem hi hr (real n)
  simp only [isodd_Number, iseven_Number, hp.1, hp.2, Bool.and_assoc]
  trivial



/-- Value laws of a custom signed representation and its same-type primitives. -/
structure SignedValueOps (S : Type) where
  value : S → Int
  wrap : Int → Int
  oftype : S → Bool → S
  neg : S → S
  flip : S → S → S
  negOne : wrap (-1) = -1
  zero : wrap 0 = 0
  oftype_value : ∀ x b, value (oftype x b) = if b then 1 else 0
  neg_value : ∀ x, value (neg x) = wrap (-value x)
  flip_value : ∀ x y, value (flip x y) = wrap (if value y < 0 then -value x else value x)
  wrap_idem : ∀ n, wrap (wrap n) = wrap n
  wrap_neg : ∀ n, wrap (-wrap n) = wrap (-n)

theorem signedMixed_output_value {Q S : Type} (ops : SignedValueOps S) (qv : Q → Int)
    (zeroQ : Q → Q) (convertQ : Q → S) (typeQ : S → Unit) (remQ : Q → Unit → S)
    (hr : ∀ q T, ops.value (remQ q T) = ops.wrap (qv q))
    {s : IntTy} (x : JInt s) (q : Q) :
    ops.value (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip
      (Generic.signed zeroQ convertQ typeQ remQ q) x) =
      ops.wrap (if x.val < 0 then -qv q else qv q) := by
  rw [genericFlipsignReal_proven S (JInt s) ops.value ops.wrap signbit_Integer ops.oftype
    ops.neg ops.flip ops.negOne ops.zero ops.oftype_value ops.neg_value ops.flip_value]
  simp only [Generic.signed, hr, (signPredicates_proven s x).1, decide_eq_true_eq]
  split <;> simp only [ops.wrap_neg, ops.wrap_idem]

/-- For every unsigned argument type, the signed-dividend div/rem methods attach the
original dividend's sign to the exact magnitude returned by unsigned division/remainder.
The returned signed representation may wrap, as documented for fixed-width integers. -/
def GenericSignedMixed : Prop := ∀ (U Q S : Type) (uv : U → Int) (qv : Q → Int)
    (ops : SignedValueOps S) (s : IntTy), s.signed = true →
    ∀ (f : JInt s.toUnsigned → U → Jl Q) (result : JInt s.toUnsigned → U → Q)
    (magnitude : Int → Int → Int) (zeroQ : Q → Q) (convertQ : Q → S)
    (typeQ : S → Unit) (remQ : Q → Unit → S),
  (∀ q T, ops.value (remQ q T) = ops.wrap (qv q)) →
  (∀ a y, f a y = if uv y = 0 then .error .divideError else .ok (result a y)) →
  (∀ a y, uv y ≠ 0 → qv (result a y) = magnitude a.val (uv y)) →
  ∀ (x : JInt s) (y : U),
  (Generic.div_BitSigned_Unsigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
      (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip) x y).map ops.value =
    (if uv y = 0 then .error .divideError else
      .ok (ops.wrap (if x.val < 0 then -magnitude (x.val.natAbs : Int) (uv y)
        else magnitude (x.val.natAbs : Int) (uv y)))) ∧
  (Generic.rem_BitSigned_Unsigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
      (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip) x y).map ops.value =
    (if uv y = 0 then .error .divideError else
      .ok (ops.wrap (if x.val < 0 then -magnitude (x.val.natAbs : Int) (uv y)
        else magnitude (x.val.natAbs : Int) (uv y))))
theorem genericSignedMixed_proven : GenericSignedMixed := by
  intro U Q S uv qv ops s hs f result magnitude zeroQ convertQ typeQ remQ hr hf hv x y
  by_cases hy : uv y = 0
  · simp [Generic.div_BitSigned_Unsigned, Generic.rem_BitSigned_Unsigned, hf, hy, Functor.map, Except.map]
  · simp only [Generic.div_BitSigned_Unsigned, Generic.rem_BitSigned_Unsigned, hf, hy, ite_false,
      bind, Except.bind, pure, Except.pure, Except.map]
    rw [signedMixed_output_value ops qv zeroQ convertQ typeQ remQ hr, hv _ y hy, unsigned_abs_val hs]
    exact ⟨rfl, rfl⟩

/-- Generic signed-dividend divrem returns the signed quotient and signed remainder together,
with the same zero-divisor error and magnitude laws as div and rem. -/
def GenericSignedDivrem : Prop := ∀ (U Q S : Type) (uv : U → Int) (qv : Q → Int)
    (ops : SignedValueOps S) (s : IntTy), s.signed = true →
    ∀ (f : JInt s.toUnsigned → U → Jl (Q × Q)) (q r : JInt s.toUnsigned → U → Q)
    (quotient remainder : Int → Int → Int) (zeroQ : Q → Q) (convertQ : Q → S)
    (typeQ : S → Unit) (remQ : Q → Unit → S),
  (∀ q T, ops.value (remQ q T) = ops.wrap (qv q)) →
  (∀ a y, f a y = if uv y = 0 then .error .divideError else .ok (q a y, r a y)) →
  (∀ a y, uv y ≠ 0 → qv (q a y) = quotient a.val (uv y) ∧ qv (r a y) = remainder a.val (uv y)) →
  ∀ (x : JInt s) (y : U),
  (Generic.divrem_BitSigned_Unsigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
      (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip) x y).map
        (fun p => (ops.value p.1, ops.value p.2)) =
    (if uv y = 0 then .error .divideError else .ok
      (ops.wrap (if x.val < 0 then -quotient (x.val.natAbs : Int) (uv y) else quotient (x.val.natAbs : Int) (uv y)),
       ops.wrap (if x.val < 0 then -remainder (x.val.natAbs : Int) (uv y) else remainder (x.val.natAbs : Int) (uv y))))
theorem genericSignedDivrem_proven : GenericSignedDivrem := by
  intro U Q S uv qv ops s hs f q r quotient remainder zeroQ convertQ typeQ remQ hr hf hv x y
  by_cases hy : uv y = 0
  · simp [Generic.divrem_BitSigned_Unsigned, hf, hy, Functor.map, Except.map]
  · simp only [Generic.divrem_BitSigned_Unsigned, hf, hy, ite_false,
      bind, Except.bind, pure, Except.pure, Except.map]
    rw [signedMixed_output_value ops qv zeroQ convertQ typeQ remQ hr,
      signedMixed_output_value ops qv zeroQ convertQ typeQ remQ hr,
      (hv _ y hy).1, (hv _ y hy).2, unsigned_abs_val hs]

/-- The unsigned-dividend mixed methods retain the unsigned return conversion after attaching
the divisor's sign. The statement records both conversions, including their modular effects. -/
def GenericUnsignedMixed : Prop := ∀ (U Q S O : Type) (uv : U → Int) (qv : Q → Int)
    (ov : O → Int) (unsignedWrap : Int → Int) (ops : SignedValueOps S) (s : IntTy),
    s.signed = true → ∀ (f : U → JInt s.toUnsigned → Jl Q)
    (result : U → JInt s.toUnsigned → Q) (magnitude : Int → Int → Int)
    (zeroQ : Q → Q) (convertQ : Q → S) (typeQ : S → Unit) (remQ : Q → Unit → S)
    (zeroS : S → S) (convertS : S → O) (typeS : O → Unit) (remS : S → Unit → O),
  (∀ q T, ops.value (remQ q T) = ops.wrap (qv q)) →
  (∀ a T, ov (remS a T) = unsignedWrap (ops.value a)) →
  (∀ x a, f x a = if a.val = 0 then .error .divideError else .ok (result x a)) →
  (∀ x a, a.val ≠ 0 → qv (result x a) = magnitude (uv x) a.val) →
  ∀ (x : U) (y : JInt s),
  (Generic.div_Unsigned_BitSigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
    (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip)
    (Generic.unsigned zeroS convertS typeS remS) x y).map ov =
    (if y.val = 0 then .error .divideError else .ok (unsignedWrap
      (ops.wrap (if y.val < 0 then -magnitude (uv x) (y.val.natAbs : Int)
        else magnitude (uv x) (y.val.natAbs : Int))))) ∧
  (Generic.rem_Unsigned_BitSigned abs unsigned f x y).map qv =
    (if y.val = 0 then .error .divideError else .ok (magnitude (uv x) (y.val.natAbs : Int)))
theorem genericUnsignedMixed_proven : GenericUnsignedMixed := by
  intro U Q S O uv qv ov unsignedWrap ops s hs f result magnitude zeroQ convertQ typeQ remQ
    zeroS convertS typeS remS hr hu hf hv x y
  have hzero : ((y.val.natAbs : Int) = 0) ↔ y.val = 0 := by omega
  have hmag : (unsigned (abs y)).val = (y.val.natAbs : Int) := unsigned_abs_val hs y
  by_cases hy : y.val = 0
  · simp [Generic.div_Unsigned_BitSigned, Generic.rem_Unsigned_BitSigned, hf, hmag, hzero,
      hy, Functor.map, Except.map]
  · have ha : (unsigned (abs y)).val ≠ 0 := fun he => hy (hzero.mp (hmag.symm.trans he))
    simp only [Generic.div_Unsigned_BitSigned, Generic.rem_Unsigned_BitSigned, hf,
      ha, hy, ite_false, bind, Except.bind, pure, Except.pure, Except.map,
      Generic.unsigned, hu]
    rw [signedMixed_output_value ops qv zeroQ convertQ typeQ remQ hr,
      hv x _ ha, hmag]
    exact ⟨rfl, rfl⟩

/-- Generic unsigned-dividend divrem preserves the same signed quotient conversion as div
and returns the exact unsigned remainder as its second component. -/
def GenericUnsignedDivrem : Prop := ∀ (U Q S O : Type) (uv : U → Int) (qv : Q → Int)
    (ov : O → Int) (unsignedWrap : Int → Int) (ops : SignedValueOps S) (s : IntTy),
    s.signed = true → ∀ (f : U → JInt s.toUnsigned → Jl (Q × Q))
    (q r : U → JInt s.toUnsigned → Q) (quotient remainder : Int → Int → Int)
    (zeroQ : Q → Q) (convertQ : Q → S) (typeQ : S → Unit) (remQ : Q → Unit → S)
    (zeroS : S → S) (convertS : S → O) (typeS : O → Unit) (remS : S → Unit → O),
  (∀ q T, ops.value (remQ q T) = ops.wrap (qv q)) →
  (∀ a T, ov (remS a T) = unsignedWrap (ops.value a)) →
  (∀ x a, f x a = if a.val = 0 then .error .divideError else .ok (q x a, r x a)) →
  (∀ x a, a.val ≠ 0 → qv (q x a) = quotient (uv x) a.val ∧ qv (r x a) = remainder (uv x) a.val) →
  ∀ (x : U) (y : JInt s),
  (Generic.divrem_Unsigned_BitSigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
    (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip)
    (Generic.unsigned zeroS convertS typeS remS) x y).map (fun p => (ov p.1, qv p.2)) =
    (if y.val = 0 then .error .divideError else .ok
      (unsignedWrap (ops.wrap (if y.val < 0 then -quotient (uv x) (y.val.natAbs : Int)
        else quotient (uv x) (y.val.natAbs : Int))),
       remainder (uv x) (y.val.natAbs : Int)))
theorem genericUnsignedDivrem_proven : GenericUnsignedDivrem := by
  intro U Q S O uv qv ov unsignedWrap ops s hs f q r quotient remainder zeroQ convertQ typeQ remQ
    zeroS convertS typeS remS hr hu hf hv x y
  have hzero : ((y.val.natAbs : Int) = 0) ↔ y.val = 0 := by omega
  have hmag : (unsigned (abs y)).val = (y.val.natAbs : Int) := unsigned_abs_val hs y
  by_cases hy : y.val = 0
  · simp [Generic.divrem_Unsigned_BitSigned, hf, hmag, hzero, hy, Functor.map, Except.map]
  · have ha : (unsigned (abs y)).val ≠ 0 := fun he => hy (hzero.mp (hmag.symm.trans he))
    simp only [Generic.divrem_Unsigned_BitSigned, hf, ha, hy, ite_false,
      bind, Except.bind, pure, Except.pure, Except.map, Generic.unsigned, hu]
    rw [signedMixed_output_value ops qv zeroQ convertQ typeQ remQ hr,
      (hv x _ ha).1, (hv x _ ha).2, hmag]



/-- High-half multiplication on any fixed-width custom integer returns the high word of the
full widened product. Logical shifting and reduction preserve those word bits. -/
def GenericMulHi : Prop := ∀ (I W P K : Type) (value : I → Int) (wv : W → Int)
    (pv : P → Int) (kv : K → Nat) (wrap : Int → Int) (width : Nat)
    (widen : I → W) (mul : W → I → P) (remLiteral : Int → I)
    (top : I → K) (lshr : P → K → P) (rem : P → I),
  (∀ a, wv (widen a) = value a) → (∀ a b, pv (mul a b) = wv a * value b) →
  kv (top (remLiteral (-1))) = width →
  (∀ p, value (rem p) = wrap (pv p)) →
  (∀ p k, kv k = width → wrap (pv (lshr p k)) = wrap (pv p / (2 ^ width : Nat))) → ∀ a b,
    value (Generic.mul_hi_Integer widen mul remLiteral top lshr rem a b) =
      wrap (value a * value b / (2 ^ width : Nat))
theorem genericMulHi_proven : GenericMulHi := by
  intro I W P K value wv pv kv wrap width widen mul remLiteral top lshr rem hw hm ht hr hs a b
  simp only [Generic.mul_hi_Integer, hr, hs _ _ ht, hm, hw]

/-- Generic modulo reconstructs the input modulo the divisor, with cancellation of wrapped
intermediate multiplication and subtraction, for custom finite and unbounded integer types. -/
def GenericModuloInteger : Prop := ∀ (I : Type) (value : I → Int) (wrap : Int → Int)
    (minusOne : I → Bool) (zero : I) (fld : I → I → Jl I) (quotient : I → I → I)
    (sub mul : I → I → I),
  (∀ y, minusOne y = decide (value y = -1)) → value zero = 0 →
  (∀ x y, value y ≠ -1 → fld x y = if value y = 0 then .error .divideError else .ok (quotient x y)) →
  (∀ x y, value y ≠ 0 → value y ≠ -1 → value (quotient x y) = (value x).fdiv (value y)) →
  (∀ x y, value (sub x y) = wrap (value x - value y)) →
  (∀ x y, value (mul x y) = wrap (value x * value y)) →
  (∀ a b, wrap (a - wrap b) = wrap (a - b)) →
  (∀ x y, value y ≠ 0 → wrap ((value x).fmod (value y)) = (value x).fmod (value y)) → ∀ x y,
    (mod_Integer minusOne zero fld sub mul x y).map value =
      (if value y = 0 then .error .divideError else .ok ((value x).fmod (value y)))
theorem genericModuloInteger_proven : GenericModuloInteger := by
  intro I value wrap minusOne zero fld quotient sub mul h1 hz hf hq hs hm hc hr x y
  by_cases hy1 : value y = -1
  · have he : (value x).fmod (-1) = 0 := by
      have h := Int.neg_fmod_neg (-value x) 1
      rw [Int.neg_neg, Int.fmod_one] at h
      omega
    simp [mod_Integer, h1, hy1, hz, he, pure, Except.pure, Except.map]
  · by_cases hy0 : value y = 0
    · simp [mod_Integer, h1, hy1, hf x y hy1, hy0, bind, Except.bind, Except.map]
    · simp only [mod_Integer, h1, hy1, decide_false, Bool.false_eq_true, ite_false,
        hf x y hy1, hy0, bind, Except.bind, pure, Except.pure, Except.map,
        hs, hm, hq x y hy0 hy1, hc]
      have he := Int.fmod_add_fdiv_mul (value x) (value y)
      rw [show value x - (value x).fdiv (value y) * value y = (value x).fmod (value y) by omega,
        hr x y hy0]

/-- Generic real copysign first converts signbit into a signed zero or minus one, so every
signed type receives the requested magnitude and sign with its own wrapping convention. -/
def GenericCopysignReal : Prop := ∀ (S X R : Type) (value : S → Int) (xv : X → Int)
    (wrap : Int → Int) (sb : R → Bool) (oftype : S → Bool → S) (neg : S → S)
    (xor : S → S → X) (flip : S → X → S),
  wrap (-1) = -1 → wrap 0 = 0 →
  (∀ x b, value (oftype x b) = if b then 1 else 0) →
  (∀ x, value (neg x) = wrap (-value x)) →
  (∀ x y, xv (xor x y) < 0 ↔ (value x < 0 ∧ 0 ≤ value y) ∨ (0 ≤ value x ∧ value y < 0)) →
  (∀ x y, value (flip x y) = wrap (if xv y < 0 then -value x else value x)) → ∀ x y,
    value (Generic.copysign_Real sb oftype neg (Generic.copysign_Signed xor flip) x y) =
      wrap (if sb y then -((value x).natAbs : Int) else (value x).natAbs)
theorem genericCopysignReal_proven : GenericCopysignReal := by
  intro S X R value xv wrap sb oftype neg xor flip hm hz ho hn hx hf x y
  unfold Generic.copysign_Real
  rw [genericCopysignSigned_proven S S X value value xv wrap xor flip hx hf]
  simp only [hn, ho]
  cases hb : sb y <;> simp [hm, hz]



/-- Mixed signed/unsigned modulo corrects the source-mirrored signed remainder into the
unsigned divisor's range, for every unsigned divisor type. -/
def GenericModSignedUnsigned : Prop := ∀ (U Q S P V O : Type) (uv : U → Int) (qv : Q → Int)
    (pv : P → Int) (vv : V → Int) (ov : O → Int) (ops : SignedValueOps S)
    (vw uw : Int → Int) (s : IntTy), s.signed = true →
    ∀ (f : JInt s.toUnsigned → U → Jl Q) (result : JInt s.toUnsigned → U → Q)
    (zeroQ : Q → Q) (convertQ : Q → S) (typeQ : S → Unit) (remQ : Q → Unit → S)
    (zeroS : S → S) (ltS : S → S → Bool) (mul : Bool → U → P) (add : S → P → V)
    (zeroV : V → V) (convertV : V → O) (typeV : O → Unit) (remV : V → Unit → O),
  (∀ y, 0 ≤ uv y) →
  (∀ q T, ops.value (remQ q T) = ops.wrap (qv q)) →
  (∀ a y, f a y = if uv y = 0 then .error .divideError else .ok (result a y)) →
  (∀ a y, uv y ≠ 0 → qv (result a y) = a.val % uv y) →
  (∀ (x : JInt s) y, uv y ≠ 0 → ops.wrap (x.val.tmod (uv y)) = x.val.tmod (uv y)) →
  (∀ r, ops.value (zeroS r) = 0) →
  (∀ a b, ltS a b = decide (ops.value a < ops.value b)) →
  (∀ b y, pv (mul b y) = if b then uv y else 0) →
  (∀ r p, vv (add r p) = vw (ops.value r + pv p)) →
  (∀ a T, ov (remV a T) = uw (vv a)) →
  (∀ n, uw (vw n) = uw n) →
  (∀ (x : JInt s) y, uv y ≠ 0 → uw (x.val.fmod (uv y)) = x.val.fmod (uv y)) →
  ∀ (x : JInt s) (y : U),
  (Generic.mod_BitSigned_Unsigned
      (Generic.rem_BitSigned_Unsigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
        (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip))
      zeroS ltS mul add (Generic.unsigned zeroV convertV typeV remV) x y).map ov =
    (if uv y = 0 then .error .divideError else .ok (x.val.fmod (uv y)))
theorem genericModSignedUnsigned_proven : GenericModSignedUnsigned := by
  intro U Q S P V O uv qv pv vv ov ops vw uw s hs f result zeroQ convertQ typeQ remQ
    zeroS ltS mul add zeroV convertV typeV remV hu hr hf hv hc hz hl hm ha hrem hw hfit x y
  have hp := (genericSignedMixed_proven U Q S uv qv ops s hs f result (· % ·)
    zeroQ convertQ typeQ remQ hr hf hv x y).2
  have hrep : (if x.val < 0 then -((x.val.natAbs : Int) % uv y)
      else (x.val.natAbs : Int) % uv y) = x.val.tmod (uv y) := (tmod_pos_eq _ _).symm
  rw [hrep] at hp
  by_cases hy : uv y = 0
  · rw [if_pos hy] at hp
    cases he : Generic.rem_BitSigned_Unsigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
        (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip) x y with
    | ok r => rw [he] at hp; cases hp
    | error e =>
      rw [he] at hp
      have he' : e = .divideError := Except.error.inj hp
      subst e
      simp [Generic.mod_BitSigned_Unsigned, he, hy, Functor.map, Except.map]
  · rw [if_neg hy, hc x y hy] at hp
    cases he : Generic.rem_BitSigned_Unsigned abs unsigned f (Generic.signed zeroQ convertQ typeQ remQ)
        (Generic.flipsign_Real signbit_Integer ops.oftype ops.neg ops.flip) x y with
    | error e => rw [he] at hp; cases hp
    | ok r =>
      rw [he] at hp
      have hrv : ops.value r = x.val.tmod (uv y) := Except.ok.inj hp
      simp only [Generic.mod_BitSigned_Unsigned, he, bind, Except.bind, pure, Except.pure,
        Except.map, Generic.unsigned, hrem, ha, hw, hm, hl, hz, hrv, decide_eq_true_eq, hy, ite_false]
      rw [← fmod_pos_tmod x.val (uv y) (by have := hu y; omega), hfit x y hy]



/-- For every custom Signed divisor type, modulo adds the negative divisor exactly when
the unsigned remainder is nonzero. The result is the exact floored remainder. -/
def GenericModUnsignedSigned : Prop := ∀ (U S Q V P O : Type) (uv : U → Int) (sv : S → Int)
    (qv : Q → Int) (vv : V → Int) (pv : P → Int) (ov : O → Int) (wrap : Int → Int)
    (rem : U → S → Jl Q) (result : U → S → Q) (zeroQ : Q → Q) (convertQ : Q → V)
    (typeQ : V → Unit) (remQ : Q → Unit → V) (iszero : V → Bool)
    (zeroS : S → S) (ltS : S → S → Bool) (mul : Bool → S → P) (add : V → P → O),
  (∀ x, 0 ≤ uv x) →
  (∀ x y, rem x y = if sv y = 0 then .error .divideError else .ok (result x y)) →
  (∀ x y, sv y ≠ 0 → qv (result x y) = (uv x).tmod (sv y)) →
  (∀ x y T, sv y ≠ 0 → vv (remQ (result x y) T) = qv (result x y)) →
  (∀ r, iszero r = decide (vv r = 0)) →
  (∀ y, sv (zeroS y) = 0) → (∀ a b, ltS a b = decide (sv a < sv b)) →
  (∀ b y, pv (mul b y) = if b then sv y else 0) →
  (∀ r p, ov (add r p) = wrap (vv r + pv p)) →
  (∀ x y, sv y ≠ 0 → wrap ((uv x).fmod (sv y)) = (uv x).fmod (sv y)) →
  ∀ x y,
  (Generic.mod_Unsigned_Signed rem (Generic.signed zeroQ convertQ typeQ remQ)
    iszero zeroS ltS mul add x y).map ov =
    (if sv y = 0 then .error .divideError else .ok ((uv x).fmod (sv y)))
theorem genericModUnsignedSigned_proven : GenericModUnsignedSigned := by
  intro U S Q V P O uv sv qv vv pv ov wrap rem result zeroQ convertQ typeQ remQ iszero
    zeroS ltS mul add hu hr hv hcast hz hzero hl hm ha hfit x y
  by_cases hy : sv y = 0
  · simp [Generic.mod_Unsigned_Signed, hr, hy, Functor.map, Except.map]
  · simp only [Generic.mod_Unsigned_Signed, hr, hy, ite_false, bind, Except.bind,
      pure, Except.pure, Except.map, ha, hm, hz, hl, hzero, Generic.signed,
      hcast x y _ hy, hv x y hy]
    have he : ((!decide ((uv x).tmod (sv y) = 0)) && decide (sv y < 0)) =
        decide ((uv x).tmod (sv y) ≠ 0 ∧ sv y < 0) := by simp
    rw [he]
    simp only [decide_eq_true_eq]
    rw [← fmod_nonneg_tmod (uv x) (sv y) (hu x) hy, hfit x y hy]




/-- Bool's actual multiplication method gives the numerical product in the int.jl Bool
widemul method, without widening. -/
def SourceBoolWidemul : Prop := ∀ a b : Bool,
  (if Generic.widemul_Bool_Bool JuliaLean.base.bool.mulBool a b then (1 : Int) else 0) =
    (if a then 1 else 0) * (if b then 1 else 0)
theorem sourceBoolWidemul_proven : SourceBoolWidemul := by
  intro a b
  cases a <;> cases b <;> decide

/-- Multiplication by Bool needs no wider result type for any Number implementation. -/
def GenericBoolWidemul : Prop := ∀ (N : Type) (value : N → Int)
    (mulLeft : Bool → N → N) (mulRight : N → Bool → N),
  (∀ b y, value (mulLeft b y) = if b then value y else 0) →
  (∀ y b, value (mulRight y b) = if b then value y else 0) → ∀ b y,
  value (widemul_Bool_Number mulLeft b y) = (if b then value y else 0) ∧
  value (widemul_Number_Bool mulRight y b) = (if b then value y else 0)
theorem genericBoolWidemul_proven : GenericBoolWidemul := by
  intro N value mulLeft mulRight hl hr b y
  exact ⟨hl b y, hr y b⟩



/-- The two's-complement representative in a type with the given width and signedness. -/
def integerRepresentative (width : Nat) (signed : Bool) (z : Int) : Int :=
  if signed then z.bmod (2 ^ width) else z % (2 ^ width)

/-- The external zero conversion selects a same-width signed or unsigned type. Remainder's
interface preserves that selected type and returns its mathematical representative. -/
def WidthPreservingConversions : Prop := ∀ (I Z U S Ty : Type)
    (iv : I → Int) (uv : U → Int) (sv : S → Int) (inputWidth : I → Nat)
    (width : Ty → Nat) (signed : Ty → Bool) (zero : I → Z)
    (toUnsigned : Z → U) (toSigned : Z → S) (typeofU : U → Ty) (typeofS : S → Ty)
    (remU : I → Ty → U) (remS : I → Ty → S),
  (∀ x, width (typeofU (toUnsigned (zero x))) = inputWidth x ∧
    signed (typeofU (toUnsigned (zero x))) = false) →
  (∀ x, width (typeofS (toSigned (zero x))) = inputWidth x ∧
    signed (typeofS (toSigned (zero x))) = true) →
  (∀ x T, uv (remU x T) = integerRepresentative (width T) (signed T) (iv x) ∧
    typeofU (remU x T) = T) →
  (∀ x T, sv (remS x T) = integerRepresentative (width T) (signed T) (iv x) ∧
    typeofS (remS x T) = T) → ∀ x,
  let u := Generic.unsigned zero toUnsigned typeofU remU x
  let s := Generic.signed zero toSigned typeofS remS x
  (width (typeofU u) = inputWidth x ∧ signed (typeofU u) = false ∧
    uv u = iv x % (2 ^ inputWidth x)) ∧
  (width (typeofS s) = inputWidth x ∧ signed (typeofS s) = true ∧
    sv s = (iv x).bmod (2 ^ inputWidth x))
theorem widthPreservingConversions_proven : WidthPreservingConversions := by
  intro I Z U S Ty iv uv sv inputWidth width signed zero toUnsigned toSigned typeofU typeofS
    remU remS hU hS hrU hrS x
  dsimp only [Generic.unsigned, Generic.signed]
  obtain ⟨hwU, hsU⟩ := hU x
  obtain ⟨hwS, hsS⟩ := hS x
  obtain ⟨hvU, htU⟩ := hrU x (typeofU (toUnsigned (zero x)))
  obtain ⟨hvS, htS⟩ := hrS x (typeofS (toSigned (zero x)))
  refine ⟨⟨by rw [htU]; exact hwU, by rw [htU]; exact hsU, ?_⟩,
    ⟨by rw [htS]; exact hwS, by rw [htS]; exact hsS, ?_⟩⟩
  · simpa only [integerRepresentative, hwU, hsU, Bool.false_eq_true, ite_false] using hvU
  · simpa only [integerRepresentative, hwS, hsS, ite_true] using hvS

/-- Abstract Signed/Unsigned remainder preserves the input type's width, selects the
requested signedness, and returns the corresponding numerical representative. -/
def WidthPreservingAbstractRemainders : Prop := ∀ (I O Ty : Type)
    (iv : I → Int) (ov : O → Int) (typeofI : I → Ty) (typeofO : O → Ty)
    (width : Ty → Nat) (isSigned : Ty → Bool) (unsigned signed : Ty → Ty)
    (rem : I → Ty → O),
  (∀ T, width (unsigned T) = width T ∧ isSigned (unsigned T) = false) →
  (∀ T, width (signed T) = width T ∧ isSigned (signed T) = true) →
  (∀ x T, ov (rem x T) = integerRepresentative (width T) (isSigned T) (iv x) ∧
    typeofO (rem x T) = T) → ∀ x,
  let u := Generic.rem_Signed_Unsigned typeofI unsigned rem x
  let s := Generic.rem_Unsigned_Signed typeofI signed rem x
  (width (typeofO u) = width (typeofI x) ∧ isSigned (typeofO u) = false ∧
    ov u = iv x % (2 ^ width (typeofI x))) ∧
  (width (typeofO s) = width (typeofI x) ∧ isSigned (typeofO s) = true ∧
    ov s = (iv x).bmod (2 ^ width (typeofI x)))
theorem widthPreservingAbstractRemainders_proven : WidthPreservingAbstractRemainders := by
  intro I O Ty iv ov typeofI typeofO width isSigned unsigned signed rem hU hS hr x
  dsimp only [Generic.rem_Signed_Unsigned, Generic.rem_Unsigned_Signed]
  obtain ⟨hwU, hsU⟩ := hU (typeofI x)
  obtain ⟨hwS, hsS⟩ := hS (typeofI x)
  obtain ⟨hvU, htU⟩ := hr x (unsigned (typeofI x))
  obtain ⟨hvS, htS⟩ := hr x (signed (typeofI x))
  refine ⟨⟨by rw [htU]; exact hwU, by rw [htU]; exact hsU, ?_⟩,
    ⟨by rw [htS]; exact hwS, by rw [htS]; exact hsS, ?_⟩⟩
  · simpa only [integerRepresentative, hwU, hsU, Bool.false_eq_true, ite_false] using hvU
  · simpa only [integerRepresentative, hwS, hsS, ite_true] using hvS


inductive IntegerShape where
  | unbounded
  | word (width : Nat) (signed : Bool)

def shapeRepresentative (shape : IntegerShape) (z : Int) : Int :=
  match shape with
  | .unbounded => z
  | .word width signed => integerRepresentative width signed z

/-- Bit k of an integer's infinite two's-complement expansion. -/
def integerBit (z : Int) (k : Nat) : Bool := decide (z / (2 ^ k) % 2 = 1)

private theorem representative_congr (w : Nat) (s : Bool) (a b : Int)
    (h : a % (2 ^ w) = b % (2 ^ w)) :
    integerRepresentative w s a = integerRepresentative w s b := by
  cases s <;> simp only [integerRepresentative, Bool.false_eq_true, ite_false, ite_true]
  · exact h
  · simp only [Int.bmod_def, Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl, h]

private theorem representative_emod (w : Nat) (s : Bool) (z : Int) :
    integerRepresentative w s z % (2 ^ w) = z % (2 ^ w) := by
  cases s
  · exact Int.emod_emod _ _
  · exact Int.bmod_emod

private theorem shape_rep_add (shape : IntegerShape) (a b : Int) :
    shapeRepresentative shape (shapeRepresentative shape a + shapeRepresentative shape b) =
      shapeRepresentative shape (a + b) := by
  cases shape with
  | unbounded => rfl
  | word w s =>
    simp only [shapeRepresentative]
    apply representative_congr
    rw [Int.add_emod, representative_emod, representative_emod, ← Int.add_emod]

private theorem shape_rep_sub (shape : IntegerShape) (a b : Int) :
    shapeRepresentative shape (shapeRepresentative shape a - shapeRepresentative shape b) =
      shapeRepresentative shape (a - b) := by
  cases shape with
  | unbounded => rfl
  | word w s =>
    simp only [shapeRepresentative]
    apply representative_congr
    rw [Int.sub_emod, representative_emod, representative_emod, ← Int.sub_emod]

private theorem shape_rep_mul (shape : IntegerShape) (a b : Int) :
    shapeRepresentative shape (shapeRepresentative shape a * shapeRepresentative shape b) =
      shapeRepresentative shape (a * b) := by
  cases shape with
  | unbounded => rfl
  | word w s =>
    simp only [shapeRepresentative]
    apply representative_congr
    rw [Int.mul_emod, representative_emod, representative_emod, ← Int.mul_emod]

/-- Promoted add_Integer: exact integer arithmetic for arbitrary-precision targets, and
modular arithmetic for fixed-width targets, preserving conversion and checker errors. -/
def GenericPromotedAdd : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b, (op T a b).map (value T) =
    .ok (shapeRepresentative (shape T) (value T a + value T b))) → ∀ a b,
  let T := promote a b
  (Generated.add_Integer promote remA remB check op a b).map (value T) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (shapeRepresentative (shape T) (av a + bv b))
theorem genericPromotedAdd_proven : GenericPromotedAdd := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.add_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.add_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.add_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.add_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb, shape_rep_add]


/-- Promoted sub_Integer: exact integer arithmetic for arbitrary-precision targets, and
modular arithmetic for fixed-width targets, preserving conversion and checker errors. -/
def GenericPromotedSub : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b, (op T a b).map (value T) =
    .ok (shapeRepresentative (shape T) (value T a - value T b))) → ∀ a b,
  let T := promote a b
  (Generated.sub_Integer promote remA remB check op a b).map (value T) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (shapeRepresentative (shape T) (av a - bv b))
theorem genericPromotedSub_proven : GenericPromotedSub := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.sub_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.sub_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.sub_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.sub_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb, shape_rep_sub]


/-- Promoted mul_Integer: exact integer arithmetic for arbitrary-precision targets, and
modular arithmetic for fixed-width targets, preserving conversion and checker errors. -/
def GenericPromotedMul : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b, (op T a b).map (value T) =
    .ok (shapeRepresentative (shape T) (value T a * value T b))) → ∀ a b,
  let T := promote a b
  (Generated.mul_Integer promote remA remB check op a b).map (value T) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (shapeRepresentative (shape T) (av a * bv b))
theorem genericPromotedMul_proven : GenericPromotedMul := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.mul_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.mul_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.mul_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.mul_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb, shape_rep_mul]


/-- Promoted addWrap_Integer: exact integer arithmetic for arbitrary-precision targets, and
modular arithmetic for fixed-width targets, preserving conversion and checker errors. -/
def GenericPromotedAddWrap : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b, (op T a b).map (value T) =
    .ok (shapeRepresentative (shape T) (value T a + value T b))) → ∀ a b,
  let T := promote a b
  (Generated.addWrap_Integer promote remA remB check op a b).map (value T) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (shapeRepresentative (shape T) (av a + bv b))
theorem genericPromotedAddWrap_proven : GenericPromotedAddWrap := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.addWrap_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.addWrap_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.addWrap_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.addWrap_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb, shape_rep_add]


/-- Promoted subWrap_Integer: exact integer arithmetic for arbitrary-precision targets, and
modular arithmetic for fixed-width targets, preserving conversion and checker errors. -/
def GenericPromotedSubWrap : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b, (op T a b).map (value T) =
    .ok (shapeRepresentative (shape T) (value T a - value T b))) → ∀ a b,
  let T := promote a b
  (Generated.subWrap_Integer promote remA remB check op a b).map (value T) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (shapeRepresentative (shape T) (av a - bv b))
theorem genericPromotedSubWrap_proven : GenericPromotedSubWrap := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.subWrap_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.subWrap_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.subWrap_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.subWrap_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb, shape_rep_sub]


/-- Promoted mulWrap_Integer: exact integer arithmetic for arbitrary-precision targets, and
modular arithmetic for fixed-width targets, preserving conversion and checker errors. -/
def GenericPromotedMulWrap : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b, (op T a b).map (value T) =
    .ok (shapeRepresentative (shape T) (value T a * value T b))) → ∀ a b,
  let T := promote a b
  (Generated.mulWrap_Integer promote remA remB check op a b).map (value T) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (shapeRepresentative (shape T) (av a * bv b))
theorem genericPromotedMulWrap_proven : GenericPromotedMulWrap := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.mulWrap_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.mulWrap_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.mulWrap_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.mulWrap_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb, shape_rep_mul]


/-- Promoted and_Integer applies the Boolean truth table at every bit of arbitrary Integer
operands, with the target representation's signed extension or arbitrary precision. -/
def GenericPromotedAnd : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b k, (op T a b).map (fun r => integerBit (value T r) k) =
    .ok (integerBit (value T a) k && integerBit (value T b) k)) → ∀ a b k,
  let T := promote a b
  (Generated.and_Integer promote remA remB check op a b).map (fun r => integerBit (value T r) k) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (integerBit (shapeRepresentative (shape T) (av a)) k &&
      integerBit (shapeRepresentative (shape T) (bv b)) k)
theorem genericPromotedAnd_proven : GenericPromotedAnd := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b k
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.and_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.and_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.and_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.and_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb]


/-- Promoted or_Integer applies the Boolean truth table at every bit of arbitrary Integer
operands, with the target representation's signed extension or arbitrary precision. -/
def GenericPromotedOr : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b k, (op T a b).map (fun r => integerBit (value T r) k) =
    .ok (integerBit (value T a) k || integerBit (value T b) k)) → ∀ a b k,
  let T := promote a b
  (Generated.or_Integer promote remA remB check op a b).map (fun r => integerBit (value T r) k) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (integerBit (shapeRepresentative (shape T) (av a)) k ||
      integerBit (shapeRepresentative (shape T) (bv b)) k)
theorem genericPromotedOr_proven : GenericPromotedOr := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b k
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.or_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.or_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.or_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.or_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb]


/-- Promoted xor_Integer applies the Boolean truth table at every bit of arbitrary Integer
operands, with the target representation's signed extension or arbitrary precision. -/
def GenericPromotedXor : Prop := ∀ (A B Ty : Type) (V : Ty → Type)
    (av : A → Int) (bv : B → Int) (value : (T : Ty) → V T → Int)
    (shape : Ty → IntegerShape) (promote : A → B → Ty)
    (remA : (a : A) → (T : Ty) → Jl (V T))
    (remB : (b : B) → (T : Ty) → Jl (V T))
    (check : A × B → (T : Ty) → V T × V T → Jl Unit)
    (op : (T : Ty) → V T → V T → Jl (V T)),
  (∀ a T r, remA a T = .ok r → value T r = shapeRepresentative (shape T) (av a)) →
  (∀ b T r, remB b T = .ok r → value T r = shapeRepresentative (shape T) (bv b)) →
  (∀ T a b k, (op T a b).map (fun r => integerBit (value T r) k) =
    .ok (integerBit (value T a) k ^^ integerBit (value T b) k)) → ∀ a b k,
  let T := promote a b
  (Generated.xor_Integer promote remA remB check op a b).map (fun r => integerBit (value T r) k) = do
    let aT ← remA a T
    let bT ← remB b T
    let _ ← check (a, b) T (aT, bT)
    pure (integerBit (shapeRepresentative (shape T) (av a)) k ^^
      integerBit (shapeRepresentative (shape T) (bv b)) k)
theorem genericPromotedXor_proven : GenericPromotedXor := by
  intro A B Ty V av bv value shape promote remA remB check op ha hb hop a b k
  dsimp only
  cases ea : remA a (promote a b) with
  | error e => simp [Generated.xor_Integer, ea, bind, Except.bind, Except.map]
  | ok ar =>
    cases eb : remB b (promote a b) with
    | error e => simp [Generated.xor_Integer, ea, eb, bind, Except.bind, Except.map]
    | ok br =>
      cases ec : check (a, b) (promote a b) (ar, br) with
      | error e => simp [Generated.xor_Integer, ea, eb, ec, bind, Except.bind, Except.map]
      | ok unit =>
        simp only [Generated.xor_Integer, ea, eb, ec, bind, Except.bind, pure, Except.pure]
        rw [hop, ha a _ ar ea, hb b _ br eb]




/-- A call with this typed MethodError result cannot return a value. -/
def rejectsValue {Args α : Type} (result : Except (InvalidMethodError Args) α) : Prop :=
  ∀ value, result ≠ .ok value

/-- Every Union{} call rejects every possible return value with MethodError. Distinct
supplied arguments remain distinguishable in the errors, and different functions' errors
do not become confused. -/
def InvalidTypeErrorsLossless : Prop :=
  (∀ (I Tail α : Type) (x : I) (tail : Tail),
    rejectsValue (signed_Type_Union (α := α) .type tail) ∧
    rejectsValue (rem_Union (α := α) x .type tail) ∧
    rejectsValue (mod_Union (α := α) x .type tail) ∧
    rejectsValue (unsafe_trunc_Union (α := α) .type tail) ∧
    rejectsValue (typemin_Union (α := α) .type tail) ∧
    rejectsValue (typemax_Union (α := α) .type tail)) ∧
  (∀ (Tail α : Type) (a b : Tail),
    (signed_Type_Union (α := α) .type a = signed_Type_Union .type b ↔ a = b) ∧
    (unsafe_trunc_Union (α := α) .type a = unsafe_trunc_Union .type b ↔ a = b) ∧
    (typemin_Union (α := α) .type a = typemin_Union .type b ↔ a = b) ∧
    (typemax_Union (α := α) .type a = typemax_Union .type b ↔ a = b)) ∧
  (∀ (I Tail α : Type) (x y : I) (a b : Tail),
    (rem_Union (α := α) x .type a = rem_Union y .type b ↔ x = y ∧ a = b) ∧
    (mod_Union (α := α) x .type a = mod_Union y .type b ↔ x = y ∧ a = b)) ∧
  (∀ (Tail α : Type) (a b : Tail),
    signed_Type_Union (α := α) .type a ≠ unsafe_trunc_Union .type b ∧
    signed_Type_Union (α := α) .type a ≠ typemin_Union .type b ∧
    signed_Type_Union (α := α) .type a ≠ typemax_Union .type b ∧
    unsafe_trunc_Union (α := α) .type a ≠ typemin_Union .type b ∧
    unsafe_trunc_Union (α := α) .type a ≠ typemax_Union .type b ∧
    typemin_Union (α := α) .type a ≠ typemax_Union .type b) ∧
  (∀ (I Tail α : Type) (x y : I) (a b : Tail),
    rem_Union (α := α) x .type a ≠ mod_Union y .type b)
theorem invalidTypeErrorsLossless_proven : InvalidTypeErrorsLossless := by
  simp [InvalidTypeErrorsLossless, rejectsValue, signed_Type_Union, rem_Union, mod_Union,
    unsafe_trunc_Union, typemin_Union, typemax_Union, InvalidMethodError.mk.injEq]



/-- Generic signed negation is the additive inverse in the integer's numerical representation. -/
def GenericSignedNegation : Prop := ∀ (I : Type) (value : I → Int) (neg : I → I),
  (∀ x, value (neg x) = -value x) → ∀ x, value (negate neg x) + value x = 0
theorem genericSignedNegation_proven : GenericSignedNegation := by
  intro I value neg hn x
  rw [negate, hn]
  omega

/-- Modulo on custom unsigned types returns the nonnegative Euclidean remainder and
propagates DivideError exactly when the divisor is zero. -/
def GenericUnsignedModulo : Prop := ∀ (U : Type) (value : U → Int)
    (rem : U → U → Jl U),
  (∀ x y, (rem x y).map value =
    if value y = 0 then .error .divideError else .ok (value x % value y)) → ∀ x y,
  (Generic.mod_Unsigned rem x y).map value =
    if value y = 0 then .error .divideError else .ok (value x % value y)
theorem genericUnsignedModulo_proven : GenericUnsignedModulo := by
  intro U value rem hr x y
  exact hr x y


/-- Bool multiplication acts as the multiplicative identity or as a strong zero. Its
result type is arbitrary, so the law includes floating-point and complex Number types. -/
def GenericNumberBoolWidemul : Prop := ∀ (N P : Type) (identity zero : N → P)
    (mulLeft : Bool → N → P) (mulRight : N → Bool → P),
  (∀ x, mulLeft true x = identity x ∧ mulLeft false x = zero x) →
  (∀ x, mulRight x true = identity x ∧ mulRight x false = zero x) → ∀ b x,
  widemul_Bool_Number mulLeft b x = (if b then identity x else zero x) ∧
  widemul_Number_Bool mulRight x b = (if b then identity x else zero x)
theorem genericNumberBoolWidemul_proven : GenericNumberBoolWidemul := by
  intro N P identity zero mulLeft mulRight hl hr b x
  cases b
  · exact ⟨(hl x).2, (hr x).2⟩
  · exact ⟨(hl x).1, (hr x).1⟩

/-- The parser's grammar gives an integer value, or rejects an invalid token. The error
message is external parser text; malformed input remains an ArgumentError. -/
def integerParseContract (t : IntTy) (grammar : String → Option Int)
    (parse : String → Jl (JInt t)) : Prop := ∀ s,
  match grammar s with
  | none => ∃ message, parse s = .error (.argumentError message)
  | some n =>
    if t.min ≤ n ∧ n ≤ t.max then (parse s).map Subtype.val = .ok n
    else ∃ message, parse s = .error (.overflowError message)

def IntegerLiteralMacros : Prop :=
  (∀ (grammar : String → Option Int) (parse : String → Jl (JInt .i128)),
    integerParseContract .i128 grammar parse → ∀ s,
    match grammar s with
    | none => ∃ message, int128_str parse s = .error (.argumentError message)
    | some n => if IntTy.i128.min ≤ n ∧ n ≤ IntTy.i128.max then
        (int128_str parse s).map Subtype.val = .ok n
      else ∃ message, int128_str parse s = .error (.overflowError message)) ∧
  (∀ (grammar : String → Option Int) (parse : String → Jl (JInt .u128)),
    integerParseContract .u128 grammar parse → ∀ s,
    match grammar s with
    | none => ∃ message, uint128_str parse s = .error (.argumentError message)
    | some n => if IntTy.u128.min ≤ n ∧ n ≤ IntTy.u128.max then
        (uint128_str parse s).map Subtype.val = .ok n
      else ∃ message, uint128_str parse s = .error (.overflowError message))
theorem integerLiteralMacros_proven : IntegerLiteralMacros := by
  constructor
  · intro grammar parse hp s; exact hp s
  · intro grammar parse hp s; exact hp s



/-- Numerical observations distinguish NaN, signed infinities, finite rational values,
and the sign of a finite zero. The representation may have any precision. -/
inductive FloatingValue where
  | nan
  | infinity (negative : Bool)
  | finite (numerator : Int) (denominator : Nat) (negativeZero : Bool)

def floatingSign : FloatingValue → Bool
  | .nan => false
  | .infinity negative => negative
  | .finite n _ negativeZero => if n = 0 then negativeZero else decide (n < 0)

/-- Division of numerical floating-point values, rounded in the target format. -/
def roundedQuotient (round : Int → Nat → Bool → FloatingValue) :
    FloatingValue → FloatingValue → FloatingValue
  | .nan, _ | _, .nan => .nan
  | .infinity _, .infinity _ => .nan
  | .infinity s, b@(.finite _ _ _) => .infinity (s != floatingSign b)
  | a@(.finite _ _ _), .infinity s => .finite 0 1 (floatingSign a != s)
  | a@(.finite n d _), b@(.finite m e _) =>
    if m = 0 then
      if n = 0 then .nan else .infinity (floatingSign a != floatingSign b)
    else round (n * (e : Int) * (if m < 0 then -1 else 1))
      (d * m.natAbs) (floatingSign a != floatingSign b)

/-- Integer reciprocal first rounds its integer argument to the selected floating format,
then rounds the reciprocal. Zero, infinities and NaN follow floating-point division. -/
def GenericIntegerReciprocal : Prop := ∀ (I F : Type) (iv : I → Int)
    (value : F → FloatingValue) (round : Int → Nat → Bool → FloatingValue)
    (one : I → I) (float : I → F) (div : F → F → F),
  (∀ x, iv (one x) = 1) →
  (∀ x, value (float x) = round (iv x) 1 false) →
  (∀ x y, value (div x y) = roundedQuotient round (value x) (value y)) → ∀ x,
  value (inv_Integer one float div x) =
    roundedQuotient round (round 1 1 false) (round (iv x) 1 false)
theorem genericIntegerReciprocal_proven : GenericIntegerReciprocal := by
  intro I F iv value round one float div h1 hf hd x
  rw [inv_Integer, hd, hf, hf, h1]

/-- Integer true division divides the rounded floating operands, then rounds the quotient;
it includes arbitrary user-defined integer and floating representations. -/
def GenericIntegerTrueDivision : Prop := ∀ (I F : Type) (iv : I → Int)
    (value : F → FloatingValue) (round : Int → Nat → Bool → FloatingValue)
    (float : I → F) (div : F → F → F),
  (∀ x, value (float x) = round (iv x) 1 false) →
  (∀ x y, value (div x y) = roundedQuotient round (value x) (value y)) → ∀ x y,
  value (fdiv_Integer float div x y) =
    roundedQuotient round (round (iv x) 1 false) (round (iv y) 1 false)
theorem genericIntegerTrueDivision_proven : GenericIntegerTrueDivision := by
  intro I F iv value round float div hf hd x y
  rw [fdiv_Integer, hd, hf, hf]

/-- BitInteger true division converts each operand independently, without promoting the
integers before conversion, and computes the rounded floating-point quotient. -/
def BitIntegerTrueDivision : Prop := ∀ (s t : IntTy) (F : Type)
    (value : F → FloatingValue) (round : Int → Nat → Bool → FloatingValue)
    (floatS : JInt s → F) (floatT : JInt t → F) (div : F → F → F),
  (∀ x, value (floatS x) = round x.val 1 false) →
  (∀ y, value (floatT y) = round y.val 1 false) →
  (∀ x y, value (div x y) = roundedQuotient round (value x) (value y)) → ∀ x y,
  value (fdiv_BitInteger floatS floatT div x y) =
    roundedQuotient round (round x.val 1 false) (round y.val 1 false)
theorem bitIntegerTrueDivision_proven : BitIntegerTrueDivision := by
  intro s t F value round floatS floatT div hs ht hd x y
  rw [fdiv_BitInteger, hd, hs, ht]

/-- The floating parser's interface specifies the precision and rounding context used
when it is called. The macro's value has that load-time precision and numerical value. -/
def BigStrLoadTimeContext : Prop := ∀ (C A B : Type) (ops : Generic.BigStringOps B)
    (view : B → List Char), BigStringLaws ops view →
  ∀ (precision : C → Nat) (round : C → Int → Nat → Bool → FloatingValue)
    (value : A → FloatingValue) (valuePrecision : A → Nat)
    (grammar : String → Option (Int × Nat))
    (integer : String → Option A) (floating : C → String → Option A),
  (∀ context s n d, grammar s = some (n, d) →
    (floating context s).map (fun x => (valuePrecision x, value x)) =
      some (precision context, round context n d false)) →
  ∀ (loadContext : C) (cs : List Char) (n : Int) (d : Nat),
    cs.head? ≠ some '_' → cs.getLast? ≠ some '_' → adjUnderscoreDot cs = false →
    let normalized := String.ofList (cs.filter (· != '_'))
    integer normalized = none → grammar normalized = some (n, d) →
    (Generic.big_str ops integer (floating loadContext) (String.ofList cs)).map
      (fun x => (valuePrecision x, value x)) =
      .ok (precision loadContext, round loadContext n d false)
theorem bigStrLoadTimeContext_proven : BigStrLoadTimeContext := by
  intro C A B ops view hl precision round value valuePrecision grammar integer floating hp
    loadContext cs n d hh ht ha
  dsimp only
  intro hi hg
  have hf := hp loadContext _ n d hg
  cases he : floating loadContext (String.ofList (cs.filter (· != '_'))) with
  | none => simp [he] at hf
  | some parsed =>
    have hparsed := (bigStrSourceSeparators_proven A B ops view hl integer
      (floating loadContext) cs hh ht ha).1 parsed
    have hm : Generic.big_str ops integer (floating loadContext) (String.ofList cs) =
        .ok parsed := hparsed.mpr (Or.inr ⟨hi, he⟩)
    rw [hm]
    simpa only [he, Option.map_some, Option.some.injEq, Except.map, Except.ok.injEq] using hf


def AllPromotedArithmetic : Prop := CheckedPromotedArithmetic ∧ GenericPromotedAdd ∧
  GenericPromotedSub ∧ GenericPromotedMul ∧ GenericPromotedAddWrap ∧
  GenericPromotedSubWrap ∧ GenericPromotedMulWrap
theorem allPromotedArithmetic_proven : AllPromotedArithmetic :=
  ⟨checkedPromotedArithmetic_proven, genericPromotedAdd_proven, genericPromotedSub_proven,
    genericPromotedMul_proven, genericPromotedAddWrap_proven, genericPromotedSubWrap_proven,
    genericPromotedMulWrap_proven⟩

def AllPromotedBits : Prop := CheckedPromotedBits ∧ GenericPromotedAnd ∧ GenericPromotedOr ∧ GenericPromotedXor
theorem allPromotedBits_proven : AllPromotedBits :=
  ⟨checkedPromotedBits_proven, genericPromotedAnd_proven, genericPromotedOr_proven, genericPromotedXor_proven⟩

def AllBoolWidemul : Prop := GenericBoolWidemul ∧ GenericNumberBoolWidemul
theorem allBoolWidemul_proven : AllBoolWidemul :=
  ⟨genericBoolWidemul_proven, genericNumberBoolWidemul_proven⟩

def AllStringMacros : Prop := BigStrSourceSeparators ∧ IntegerLiteralMacros ∧ BigStrLoadTimeContext
theorem allStringMacros_proven : AllStringMacros :=
  ⟨bigStrSourceSeparators_proven, integerLiteralMacros_proven, bigStrLoadTimeContext_proven⟩


def IntegerFloatingDivision : Prop := GenericIntegerReciprocal ∧
  GenericIntegerTrueDivision ∧ BitIntegerTrueDivision
theorem integerFloatingDivision_proven : IntegerFloatingDivision :=
  ⟨genericIntegerReciprocal_proven, genericIntegerTrueDivision_proven, bitIntegerTrueDivision_proven⟩

/-- Registry entries of `base/int.jl`. -/
def entries : List JuliaLean.Registry.Entry := [
  { id := "int-neg-wraps", juliaFile := "base/int.jl", juliaFns := ["-(::BitInteger)"],
    statement := "Unary minus on every BitInteger type is negation modulo 2^n.",
    source := "manual, Integers and Floating-Point Numbers, Overflow behavior; base/int.jl:86",
    status := .proven, prop := ``NegWraps, thm := some ``negWraps_proven },
  { id := "int-sub-wraps", juliaFile := "base/int.jl", juliaFns := ["-(::T, ::T) where T<:BitInteger"],
    statement := "Subtraction on one BitInteger type is subtraction modulo 2^n.",
    source := "manual, Overflow behavior; base/int.jl:87", status := .proven,
    prop := ``SubWraps, thm := some ``subWraps_proven },
  { id := "int-add-wraps", juliaFile := "base/int.jl", juliaFns := ["+(::T, ::T) where T<:BitInteger"],
    statement := "Addition on one BitInteger type is addition modulo 2^n.",
    source := "manual, Overflow behavior; base/int.jl:88", status := .proven,
    prop := ``AddWraps, thm := some ``addWraps_proven },
  { id := "int-mul-wraps", juliaFile := "base/int.jl", juliaFns := ["*(::T, ::T) where T<:BitInteger"],
    statement := "Multiplication on one BitInteger type is multiplication modulo 2^n.",
    source := "manual, Overflow behavior; base/int.jl:89", status := .proven,
    prop := ``MulWraps, thm := some ``mulWraps_proven },
  { id := "int-neg-wrap-op", juliaFile := "base/int.jl", juliaFns := ["-%(::BitInteger)"],
    statement := "The wrapping operator -%x is negation modulo 2^n.",
    source := "docstring of -% (operators.jl); base/int.jl:91", status := .proven,
    prop := ``NegWrapWraps, thm := some ``negWrapWraps_proven },
  { id := "int-sub-wrap-op", juliaFile := "base/int.jl", juliaFns := ["-%(::T, ::T) where T<:BitInteger"],
    statement := "The wrapping operator x -% y is subtraction modulo 2^n.",
    source := "docstring of -% (operators.jl); base/int.jl:92", status := .proven,
    prop := ``SubWrapWraps, thm := some ``subWrapWraps_proven },
  { id := "int-add-wrap-op", juliaFile := "base/int.jl", juliaFns := ["+%(::T, ::T) where T<:BitInteger"],
    statement := "The wrapping operator x +% y is addition modulo 2^n.",
    source := "docstring of +% (operators.jl); base/int.jl:93", status := .proven,
    prop := ``AddWrapWraps, thm := some ``addWrapWraps_proven },
  { id := "int-mul-wrap-op", juliaFile := "base/int.jl", juliaFns := ["*%(::T, ::T) where T<:BitInteger"],
    statement := "The wrapping operator x *% y is multiplication modulo 2^n.",
    source := "docstring of *% (operators.jl); base/int.jl:94", status := .proven,
    prop := ``MulWrapWraps, thm := some ``mulWrapWraps_proven },
  { id := "floatintcov-int-primitives", juliaFile := "base/int.jl",
    juliaFns := ["-(::BitInteger)", "-(::T, ::T)", "+(::T, ::T)", "*(::T, ::T)", "-%", "+%", "*%"],
    statement := "The BitInteger arithmetic operators form the ring of integers modulo 2^n, and typemax(T) + 1 == typemin(T).",
    source := "manual, Integers and Floating-Point Numbers, Overflow behavior; base/int.jl:86-94",
    status := .proven, prop := ``PrimitiveRingLaws, thm := some ``primitiveRingLaws_proven },
  { id := "int-lt-signed", juliaFile := "base/int.jl", juliaFns := ["<(::T, ::T) where T<:BitSigned"],
    statement := "< on one signed BitInteger type compares the integer values.",
    source := "invariant; base/int.jl:84", status := .proven,
    prop := ``LtSignedExact, thm := some ``ltSignedExact_proven },
  { id := "int-lt-unsigned", juliaFile := "base/int.jl", juliaFns := ["<(::T, ::T) where T<:BitUnsigned"],
    statement := "< on one unsigned BitInteger type compares the integer values.",
    source := "invariant; base/int.jl:573", status := .proven,
    prop := ``LtUnsignedExact, thm := some ``ltUnsignedExact_proven },
  { id := "int-le-signed", juliaFile := "base/int.jl", juliaFns := ["<=(::T, ::T) where T<:BitSigned"],
    statement := "<= on one signed BitInteger type compares the integer values.",
    source := "invariant; base/int.jl:574", status := .proven,
    prop := ``LeSignedExact, thm := some ``leSignedExact_proven },
  { id := "int-le-unsigned", juliaFile := "base/int.jl", juliaFns := ["<=(::T, ::T) where T<:BitUnsigned"],
    statement := "<= on one unsigned BitInteger type compares the integer values.",
    source := "invariant; base/int.jl:575", status := .proven,
    prop := ``LeUnsignedExact, thm := some ``leUnsignedExact_proven },
  { id := "floatintcov-int-128-primitives", juliaFile := "base/int.jl",
    juliaFns := ["*(::T, ::T) where T<:Union{Int128,UInt128}"],
    statement := "On the 64-bit build, Int128 and UInt128 multiplication is multiplication modulo 2^128.",
    source := "manual, Overflow behavior; base/int.jl:1083", status := .proven,
    prop := ``Mul128Wraps, thm := some ``mul128Wraps_proven,
    notes := "Int128/UInt128 div and rem (lines 1085-1089) are stated by int-divrem-same." },
  { id := "int-unsigned-reinterprets", juliaFile := "base/int.jl",
    juliaFns := ["unsigned(::BitUnsigned)", "unsigned(::BitSigned)"],
    statement := "unsigned(x) is x for an unsigned x and x + 2^n for a negative signed x, the same bits in the unsigned type of the same size.",
    source := "docstring of unsigned (base/int.jl:238-260); base/int.jl:261-262", status := .proven,
    prop := ``UnsignedExact, thm := some ``unsignedExact_proven },
  { id := "int-signed-reinterprets", juliaFile := "base/int.jl",
    juliaFns := ["signed(::BitSigned)", "signed(::BitUnsigned)"],
    statement := "signed(x) is x for a signed x and x - 2^n for an unsigned x of at least 2^(n-1), the same bits in the signed type of the same size.",
    source := "docstring of signed (base/int.jl:264-271); base/int.jl:272-273", status := .proven,
    prop := ``SignedExact, thm := some ``signedExact_proven },
  { id := "intarith-division-signed-roundtrip", juliaFile := "base/int.jl",
    juliaFns := ["signed", "unsigned"],
    statement := "signed(unsigned(x)) == x for every signed BitInteger x and unsigned(signed(x)) == x for every unsigned x.",
    source := "docstring example of unsigned, base/int.jl:238-273", status := .proven,
    prop := ``SignedRoundtrip, thm := some ``signedRoundtrip_proven },
  { id := "int-rem-type-truncate", juliaFile := "base/int.jl",
    juliaFns := ["rem(::BitInteger, ::Type{<:BitInteger}) (narrowing)"],
    statement := "Narrowing x % T is the representative of x modulo 2^n in T's range.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}), base/int.jl:667-676; base/int.jl:621",
    status := .proven, prop := ``RemTruncates, thm := some ``remTruncates_proven },
  { id := "int-rem-bool-type", juliaFile := "base/int.jl", juliaFns := ["rem(::Bool, ::Type{<:BitInteger})"],
    statement := "true % T == 1 and false % T == 0 for every BitInteger type T.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}); base/int.jl:623", status := .proven,
    prop := ``RemBool, thm := some ``remBool_proven },
  { id := "int-rem-type-sext", juliaFile := "base/int.jl",
    juliaFns := ["rem(::BitSigned, ::Type{<:BitInteger}) (widening)"],
    statement := "Widening x % T of a signed x is the representative of x modulo 2^n in T's range.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}); base/int.jl:626", status := .proven,
    prop := ``RemSignExtends, thm := some ``remSignExtends_proven },
  { id := "int-rem-type-zext", juliaFile := "base/int.jl",
    juliaFns := ["rem(::BitUnsigned, ::Type{<:BitInteger}) (widening)"],
    statement := "Widening x % T of an unsigned x keeps its value.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}); base/int.jl:628", status := .proven,
    prop := ``RemZeroExtends, thm := some ``remZeroExtends_proven },
  { id := "int-rem-type-bitcast", juliaFile := "base/int.jl",
    juliaFns := ["rem(::BitInteger, ::Type{<:BitInteger}) (same size)"],
    statement := "x % T between distinct BitInteger types of one size is the representative of x modulo 2^n in T's range.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}); base/int.jl:631", status := .proven,
    prop := ``RemReinterprets, thm := some ``remReinterprets_proven },
  { id := "floatintcov-int-type-remainder", juliaFile := "base/int.jl",
    juliaFns := ["rem(::BitInteger, ::Type{<:BitInteger})", "rem(x::T, ::Type{T})"],
    statement := "For any two BitInteger types x % T is the representative of x modulo 2^n in T's range, and converting back through a type at least as wide recovers x.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}), base/int.jl:667-676; base/int.jl:618-634,695",
    status := .proven, prop := ``GeneratedRemMethods, thm := some ``generatedRemMethods_proven },
  { id := "int-rem-signed-unsigned", juliaFile := "base/int.jl", juliaFns := ["rem(::Signed, ::Type{Unsigned})"],
    statement := "x % Unsigned of a signed BitInteger is x reinterpreted in the unsigned type of the same size.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}); base/int.jl:696", status := .proven,
    prop := ``RemSignedUnsigned, thm := some ``remSignedUnsigned_proven },
  { id := "int-rem-unsigned-signed", juliaFile := "base/int.jl", juliaFns := ["rem(::Unsigned, ::Type{Signed})"],
    statement := "x % Signed of an unsigned BitInteger is x reinterpreted in the signed type of the same size.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}); base/int.jl:697", status := .proven,
    prop := ``RemUnsignedSigned, thm := some ``remUnsignedSigned_proven },
  { id := "int-mod-type", juliaFile := "base/int.jl", juliaFns := ["mod(::Integer, ::Type{T}) where T<:Integer"],
    statement := "mod(x, T) of a BitInteger is the representative of x modulo 2^n in T's range.",
    source := "docstring of mod(x::Integer, T::Type{<:Integer}) (base/int.jl:678-693); base/int.jl:701",
    status := .proven, prop := ``ModTypeResidue, thm := some ``modTypeResidue_proven },
  { id := "int-unsafe-trunc", juliaFile := "base/int.jl", juliaFns := ["unsafe_trunc(::Type{T}, ::Integer) where T<:Integer"],
    statement := "unsafe_trunc(T, x) of a BitInteger is the representative of x modulo 2^n in T's range.",
    source := "docstring of unsafe_trunc (float.jl); base/int.jl:704", status := .proven,
    prop := ``UnsafeTruncResidue, thm := some ``unsafeTruncResidue_proven },
  { id := "int-eq-signed-unsigned", juliaFile := "base/int.jl", juliaFns := ["==(::BitSigned, ::BitUnsigned)"],
    statement := "== between a signed and an unsigned BitInteger compares the integer values.",
    source := "invariant; base/int.jl:577", status := .proven,
    prop := ``EqSignedUnsignedExact, thm := some ``eqSignedUnsignedExact_proven },
  { id := "int-lt-signed-unsigned", juliaFile := "base/int.jl", juliaFns := ["<(::BitSigned, ::BitUnsigned)"],
    statement := "< between a signed and an unsigned BitInteger compares the integer values.",
    source := "invariant; base/int.jl:578", status := .proven,
    prop := ``LtSignedUnsignedExact, thm := some ``ltSignedUnsignedExact_proven },
  { id := "int-le-signed-unsigned", juliaFile := "base/int.jl", juliaFns := ["<=(::BitSigned, ::BitUnsigned)"],
    statement := "<= between a signed and an unsigned BitInteger compares the integer values.",
    source := "invariant; base/int.jl:579", status := .proven,
    prop := ``LeSignedUnsignedExact, thm := some ``leSignedUnsignedExact_proven },
  { id := "int-cmp-unsigned-signed", juliaFile := "base/int.jl",
    juliaFns := ["==(::BitUnsigned, ::BitSigned)", "<(::BitUnsigned, ::BitSigned)", "<=(::BitUnsigned, ::BitSigned)"],
    statement := "==, < and <= from an unsigned to a signed BitInteger compare the integer values, for any two sizes.",
    source := "invariant; base/int.jl:581-589", status := .proven,
    prop := ``CmpUnsignedSignedExact, thm := some ``cmpUnsignedSignedExact_proven },
  { id := "promotion-int-compare-exact", juliaFile := "base/int.jl",
    juliaFns := ["==(::BitInteger, ::BitInteger)", "<(::BitSigned, ::BitUnsigned)", "<=(::BitUnsigned, ::BitSigned)"],
    statement := "==, < and <= between any two BitInteger types, including mixed signedness and Int128/UInt128, compare the mathematical values.",
    source := "invariant; base/int.jl:84,573-589 and base/promotion.jl:516-518", status := .proven,
    prop := ``IntCompareExact, thm := some ``intCompareExact_proven },
  { id := "int-max-exact", juliaFile := "base/int.jl",
    juliaFns := ["max(::BitSigned, ::BitUnsigned)", "max(::BitUnsigned, ::BitSigned)"],
    statement := "max(x, y) of two BitIntegers is the larger integer value, exactly, in promote_type.",
    source := "docstring of max (operators.jl); base/int.jl:591-594", status := .proven,
    prop := ``MaxExact, thm := some ``maxExact_proven },
  { id := "int-min-signed-unsigned", juliaFile := "base/int.jl", juliaFns := ["min(::BitSigned, ::BitUnsigned)"],
    statement := "min(x, y) of a signed and an unsigned BitInteger is the smaller integer value, exactly.",
    source := "docstring of min (operators.jl); base/int.jl:596", status := .proven,
    prop := ``MinSignedUnsignedExact, thm := some ``minSignedUnsignedExact_proven },
  { id := "int-min-unsigned-signed", juliaFile := "base/int.jl", juliaFns := ["min(::BitUnsigned, ::BitSigned)"],
    statement := "min(x, y) of an unsigned and a signed BitInteger is the smaller integer value, exactly.",
    source := "docstring of min (operators.jl); base/int.jl:597", status := .proven,
    prop := ``MinUnsignedSignedExact, thm := some ``minUnsignedSignedExact_proven },
  { id := "int-minmax-exact", juliaFile := "base/int.jl",
    juliaFns := ["minmax(::BitSigned, ::BitUnsigned)", "minmax(::BitUnsigned, ::BitSigned)"],
    statement := "minmax(x, y) of two BitIntegers is (min(x, y), max(x, y)) with the exact smaller and larger values.",
    source := "docstring of minmax (operators.jl); base/int.jl:599", status := .proven,
    prop := ``MinmaxExact, thm := some ``minmaxExact_proven },
  { id := "floatintcov-int-extrema", juliaFile := "base/int.jl", juliaFns := ["max", "min", "minmax"],
    statement := "For any two BitIntegers, min(x, y) + max(x, y) == x + y and min(x, y) <= max(x, y) as integers.",
    source := "docstrings of min, max, minmax (operators.jl); base/int.jl:591-599", status := .proven,
    prop := ``MinMaxSum, thm := some ``minMaxSum_proven },
  { id := "floatintcov-int-signed-types", juliaFile := "base/int.jl", juliaFns := ["signed(::Type)"],
    statement := "signed(T) of every BitInteger type is a signed type of the same bit width, and T itself when T is signed.",
    source := "docstring of signed(T::Integer), base/int.jl:61-71; base/int.jl:74-79", status := .proven,
    prop := ``SignedTypeSameWidth, thm := some ``signedTypeSameWidth_proven },
  { id := "int-signed-bool-size", juliaFile := "base/int.jl", juliaFns := ["signed(::Type{Bool})", "signed(::Type)"],
    statement := "signed(T) is the signed type of the same size for Bool and every BitInteger type.",
    source := "docstring of signed(T::Integer), base/int.jl:61-71; base/int.jl:73-79", status := .refuted,
    prop := ``SignedTypeSameSize, thm := some ``signedTypeSameSize_refuted,
    issue := "none found (queries: signed Bool, signed Bool Int sizeof, unsigned Bool)",
    notes := "signed(Bool) is Int (8 bytes) while sizeof(Bool) == 1." },
  { id := "intarith-division-promotion-shape", juliaFile := "base/int.jl", juliaFns := ["promote_rule"],
    statement := "For two distinct BitInteger types exactly one promote_rule direction is defined; it picks the wider width, and the unsigned type for equal widths and mixed signedness.",
    source := "manual, Conversion and Promotion; base/int.jl:806-822", status := .proven,
    prop := ``PromotionRules, thm := some ``promotionRules_proven },
  { id := "floatintcov-int-bounds", juliaFile := "base/int.jl", juliaFns := ["typemin", "typemax"],
    statement := "typemin(T) <= x <= typemax(T) for every x of a BitInteger type T, and both bounds are the lowest and highest representable values.",
    source := "docstrings of typemin, typemax; base/int.jl:887-906", status := .proven,
    prop := ``IntegerBounds, thm := some ``integerBounds_proven },
  { id := "floatintcov-int-widen", juliaFile := "base/int.jl", juliaFns := ["widen(::Type{<:BitInteger})"],
    statement := "widen(T) below 128 bits has the same signedness and twice the width, and holds every sum and product of two values of T, and every difference for signed T.",
    source := "docstring of widen (operators.jl:955-962); base/int.jl:911-918", status := .proven,
    prop := ``WidenTypes, thm := some ``widenTypes_proven },
  { id := "hashops-widen-addition", juliaFile := "base/int.jl",
    juliaFns := ["widen(::Type{<:BitInteger})", "+(::BitInteger, ::BitInteger)"],
    statement := "After widening two values of a BitInteger type below 128 bits, their sum is the exact integer sum.",
    source := "docstring of widen (operators.jl:955-962); base/int.jl:88,911-918", status := .proven,
    prop := ``WidenAdditionNoLoss, thm := some ``widenAdditionNoLoss_proven },
  { id := "floatintcov-int-promoted-binary", juliaFile := "base/int.jl",
    juliaFns := ["+(::Integer, ::Integer)", "-(::Integer, ::Integer)", "*(::Integer, ::Integer)", "+%(::Integer, ::Integer)", "-%(::Integer, ::Integer)", "*%(::Integer, ::Integer)"],
    statement := "Promoted arithmetic on arbitrary Integer pairs gives exact results for arbitrary-precision targets and modular results for fixed-width targets, preserving conversion and checker errors.",
    source := "issue #15489 comment; manual, Conversion and Promotion; base/int.jl:1092-1100", status := .proven,
    prop := ``AllPromotedArithmetic, thm := some ``allPromotedArithmetic_proven },
  { id := "floatintcov-int-bitwise", juliaFile := "base/int.jl",
    juliaFns := ["~(::BitInteger)", "&(::T, ::T)", "|(::T, ::T)", "xor(::T, ::T)"],
    statement := "~, &, | and xor act bit by bit on the two's-complement representation, and ~x == -x - 1.",
    source := "docstrings of ~, &, |, xor; base/int.jl:381,407,432,433", status := .proven,
    prop := ``BitwiseOps, thm := some ``bitwiseOps_proven },
  { id := "int-complement-integer", juliaFile := "base/int.jl", juliaFns := ["~(::Integer)"],
    statement := "For every integer representation with the documented arithmetic laws, the input and its complement sum to -1.",
    source := "docstring of ~ (base/int.jl:357-380); base/int.jl:236", status := .proven,
    prop := ``GenericComplement, thm := some ``genericComplement_proven },
  { id := "floatintcov-int-shifts", juliaFile := "base/int.jl",
    juliaFns := [">>(::BitSigned, ::BitUnsigned)", ">>(::BitUnsigned, ::BitUnsigned)", "<<(::BitInteger, ::BitUnsigned)", ">>>(::BitInteger, ::BitUnsigned)"],
    statement := "With an unsigned count k, x >> k is fld(x, 2^k), x << k is x * 2^k modulo 2^n, and x >>> k shifts the unsigned pattern; counts of at least the width give 0 or -1.",
    source := "docstrings of >>, <<, >>> (operators.jl); base/int.jl:601-607", status := .proven,
    prop := ``ShiftUnsignedCount, thm := some ``shiftUnsignedCount_proven },
  { id := "int-shift-int-count", juliaFile := "base/int.jl",
    juliaFns := [">>(::BitInteger, ::Int)", "<<(::BitInteger, ::Int)", ">>>(::BitInteger, ::Int)"],
    statement := "With an Int count k, shifts behave as for an unsigned count when k >= 0 and shift the other way by -k when k < 0, including k == typemin(Int).",
    source := "docstrings of >>, <<, >>> (operators.jl); base/int.jl:611-616", status := .proven,
    prop := ``ShiftIntCount, thm := some ``shiftIntCount_proven },
  { id := "floatintcov-int-bit-counts", juliaFile := "base/int.jl", juliaFns := ["count_ones", "count_zeros"],
    statement := "count_ones(x) and count_zeros(x) are the numbers of ones and zeros in the n-bit representation of x.",
    source := "docstrings of count_ones, count_zeros; base/int.jl:461-475,505-517", status := .proven,
    prop := ``AllZeroCounts, thm := some ``allZeroCounts_proven },
  { id := "int-leading-zeros", juliaFile := "base/int.jl", juliaFns := ["leading_zeros"],
    statement := "leading_zeros(x) is the number of zeros leading the n-bit representation of x.",
    source := "docstring of leading_zeros; base/int.jl:477-488", status := .proven,
    prop := ``LeadingZeros, thm := some ``leadingZeros_proven },
  { id := "int-leading-ones", juliaFile := "base/int.jl", juliaFns := ["leading_ones"],
    statement := "leading_ones(x) is the number of ones leading the n-bit representation of x.",
    source := "docstring of leading_ones; base/int.jl:519-530", status := .proven,
    prop := ``AllLeadingOnes, thm := some ``allLeadingOnes_proven },
  { id := "int-trailing-zeros", juliaFile := "base/int.jl", juliaFns := ["trailing_zeros"],
    statement := "trailing_zeros(x) is the number of zeros trailing the n-bit representation of x.",
    source := "docstring of trailing_zeros; base/int.jl:490-501", status := .proven,
    prop := ``TrailingZeros, thm := some ``trailingZeros_proven },
  { id := "int-trailing-ones", juliaFile := "base/int.jl", juliaFns := ["trailing_ones"],
    statement := "trailing_ones(x) is the number of ones trailing the n-bit representation of x.",
    source := "docstring of trailing_ones; base/int.jl:532-543", status := .proven,
    prop := ``AllTrailingOnes, thm := some ``allTrailingOnes_proven },
  { id := "int-top-set-bit", juliaFile := "base/int.jl", juliaFns := ["top_set_bit(::BitInteger)"],
    statement := "top_set_bit(x) is the number of bits of x's binary representation excluding leading zeros.",
    source := "docstring of top_set_bit; base/int.jl:545-569", status := .proven,
    prop := ``TopSetBit, thm := some ``topSetBit_proven },
  { id := "floatintcov-int-bit-reversal", juliaFile := "base/int.jl", juliaFns := ["bswap"],
    statement := "bswap(x) reverses the byte order of x.",
    source := "docstring of bswap; base/int.jl:435-459", status := .proven,
    prop := ``AllByteSwap, thm := some ``allByteSwap_proven },
  { id := "int-bitreverse", juliaFile := "base/int.jl", juliaFns := ["bitreverse"],
    statement := "bitreverse(x) reverses the order of the n bits of x.",
    source := "docstring of bitreverse; base/int.jl:1101-1134", status := .proven,
    prop := ``BitReverse, thm := some ``bitReverse_proven },
  { id := "floatintcov-int-bitrotate", juliaFile := "base/int.jl", juliaFns := ["bitrotate"],
    statement := "bitrotate(x, k) rotates the bits of x left k times, and right for negative k.",
    source := "docstring of bitrotate; base/int.jl:636-665", status := .proven,
    prop := ``AllBitRotate, thm := some ``allBitRotate_proven },
  { id := "floatintcov-int-sign-predicates", juliaFile := "base/int.jl",
    juliaFns := ["signbit(::Integer)", "signbit(::Unsigned)", "isnegative(::Unsigned)"],
    statement := "signbit(x) is true exactly for negative integers, and an unsigned integer has neither a sign bit nor a negative value.",
    source := "docstrings of signbit, isnegative; base/int.jl:183-185", status := .proven,
    prop := ``SignPredicates, thm := some ``signPredicates_proven },
  { id := "floatintcov-int-sign-operations", juliaFile := "base/int.jl",
    juliaFns := ["flipsign(::T, ::T) where T<:BitSigned", "flipsign(::BitSigned, ::BitSigned)", "flipsign(::Signed, ::Real)"],
    statement := "flipsign(x, y) returns x with its sign flipped when y is negative, the negation wrapping, for a signed x and every BitInteger or Real y.",
    source := "docstring of flipsign (number.jl); base/int.jl:187-194", status := .proven,
    prop := ``FlipsignExact, thm := some ``flipsignExact_proven },
  { id := "int-flipsign-float", juliaFile := "base/int.jl",
    juliaFns := ["flipsign(::Signed, ::Float16)", "flipsign(::Signed, ::Float32)", "flipsign(::Signed, ::Float64)"],
    statement := "flipsign(x, y) for a float y flips x exactly when the IEEE sign bit of y is set.",
    source := "docstring of flipsign (number.jl); base/int.jl:191-193", status := .proven,
    prop := ``FlipsignFloat, thm := some ``flipsignFloat_proven },
  { id := "int-copysign-exact", juliaFile := "base/int.jl",
    juliaFns := ["copysign(::Signed, ::Signed)", "copysign(::Signed, ::Real)"],
    statement := "copysign(x, y) has the magnitude of x and the sign of y, the negation wrapping, for a signed x and every BitInteger or Real y.",
    source := "docstring of copysign (number.jl); base/int.jl:196,200", status := .proven,
    prop := ``CopysignExact, thm := some ``copysignExact_proven },
  { id := "int-copysign-float", juliaFile := "base/int.jl",
    juliaFns := ["copysign(::Signed, ::Float16)", "copysign(::Signed, ::Float32)", "copysign(::Signed, ::Float64)"],
    statement := "copysign(x, y) for a float y gives x the sign of y's IEEE sign bit.",
    source := "docstring of copysign (number.jl); base/int.jl:197-199", status := .proven,
    prop := ``CopysignFloat, thm := some ``copysignFloat_proven },
  { id := "mathfuncs-copysign-typemin", juliaFile := "base/int.jl", juliaFns := ["copysign(::Signed, ::Signed)"],
    statement := "copysign(x, y) has the magnitude of x and the sign of y for all nonzero signed BitInteger x and y.",
    source := "docstring of copysign, base/number.jl:260; base/int.jl:196", status := .refuted,
    prop := ``CopysignMagnitudeSign, thm := some ``copysignMagnitudeSign_refuted,
    issue := "none found (queries: copysign typemin, flipsign typemin, copysign overflow, flipsign overflow, copysign, flipsign)",
    notes := "copysign(typemin(Int), 1) == typemin(Int): negation wraps, as for abs." },
  { id := "intarith-division-abs-typemin", juliaFile := "base/int.jl", juliaFns := ["abs(::Unsigned)", "abs(::Signed)"],
    statement := "abs(x) is the absolute value of x, except abs(typemin(T)) == typemin(T) < 0 for a signed type, the only negative result.",
    source := "docstring of abs; base/int.jl:202-235", status := .proven,
    prop := ``AbsExact, thm := some ``absExact_proven },
  { id := "int-divrem-same", juliaFile := "base/int.jl",
    juliaFns := ["div(::T, ::T) where T<:BitInteger", "rem(::T, ::T) where T<:BitInteger", "div(::Int128, ::Int128)", "rem(::Int128, ::Int128)", "div(::UInt128, ::UInt128)", "rem(::UInt128, ::UInt128)"],
    statement := "div is the quotient truncated toward zero and rem its remainder with the sign of x; div throws DivideError exactly for y == 0 or typemin(T) / -1, and rem exactly for y == 0, at every width.",
    source := "docstrings of div, rem; manual, Division errors; base/int.jl:292-358,1084-1090", status := .proven,
    prop := ``DivRemSame, thm := some ``divRemSame_proven },
  { id := "intarith-division-unsigned-mod-bounds", juliaFile := "base/int.jl", juliaFns := ["mod(::T, ::T) where T<:BitUnsigned"],
    statement := "Unsigned mod(x, y) is the floored remainder, nonnegative and below y, and throws DivideError exactly when y == 0.",
    source := "docstring of mod; base/int.jl:351", status := .proven,
    prop := ``ModUnsigned, thm := some ``modUnsigned_proven },
  { id := "intarith-division-signed-mod-reconstruct", juliaFile := "base/int.jl",
    juliaFns := ["mod(::T, ::T) where T<:BitSigned", "mod(::T, ::T) where T<:Integer"],
    statement := "Signed mod(x, y) is the floored remainder x - y*fld(x, y) without intermediate overflow, with the sign of y and magnitude below |y|, including mod(typemin(T), -1) == 0, and throws DivideError exactly when y == 0.",
    source := "docstring of mod; base/int.jl:331-341", status := .proven,
    prop := ``ModSigned, thm := some ``modSigned_proven },
  { id := "floatintcov-int-division-methods", juliaFile := "base/int.jl",
    juliaFns := ["div(::BitSigned, ::BitUnsigned)", "rem(::BitSigned, ::BitUnsigned)", "divrem(::BitSigned, ::BitUnsigned)", "rem(::BitUnsigned, ::BitSigned)", "divrem(::BitUnsigned, ::BitSigned)"],
    statement := "Mixed-signedness div, rem and divrem return the exact truncated quotient and remainder with no wraparound, and throw DivideError exactly for a zero divisor.",
    source := "docstrings of div, rem, divrem; base/int.jl:275-291", status := .proven,
    prop := ``MixedDivRem, thm := some ``mixedDivRem_proven },
  { id := "int-div-unsigned-signed-promotes", juliaFile := "base/int.jl",
    juliaFns := ["div(::BitUnsigned, ::BitSigned)", "divrem(::BitUnsigned, ::BitSigned)"],
    statement := "div(x, y) and the quotient of divrem(x, y) for unsigned x and signed y equal the mathematical quotient rounded toward zero.",
    source := "docstrings of div and divrem; base/int.jl:276,286-289", status := .refuted,
    prop := ``UnsignedSignedExactQuotient, thm := some ``unsignedSignedExactQuotient_refuted,
    issue := "related: #57851 (closed); none found as duplicate (queries: div unsigned signed, div UInt negative divisor, mixed signed unsigned division, div promote_type)",
    notes := "div(0x0a, Int16(-3)) returns 0xfffd::UInt16 instead of Int16(-3)." },
  { id := "int-mod-mixed", juliaFile := "base/int.jl",
    juliaFns := ["mod(::BitSigned, ::BitUnsigned)", "mod(::BitUnsigned, ::BitSigned)"],
    statement := "Mixed-signedness mod(x, y) is the exact floored remainder with the sign of y and magnitude below |y|, and throws DivideError exactly for y == 0.",
    source := "docstring of mod; base/int.jl:342-350", status := .proven,
    prop := ``ModMixed, thm := some ``modMixed_proven },
  { id := "floatintcov-int-parity-dispatch", juliaFile := "base/int.jl",
    juliaFns := ["isodd(::Number)", "isodd(::Real)", "iseven(::Number)", "iseven(::Real)"],
    statement := "isodd(x) is true exactly for odd integers and iseven(x) exactly for even integers: every BitInteger, and every Complex{<:BitInteger} whose imaginary part is zero and whose real part is odd (even).",
    source := "docstrings of isodd, iseven; base/int.jl:143-181", status := .proven,
    prop := ``ParityNumber, thm := some ``parityNumber_proven },
  { id := "int-rem-bool-parity", juliaFile := "base/int.jl", juliaFns := ["rem(::Integer, ::Type{Bool})"],
    statement := "x % Bool is true exactly for odd x.",
    source := "docstring of rem(x::Integer, T::Type{<:Integer}), base/int.jl:667-676; base/int.jl:699",
    status := .proven, prop := ``RemBoolParity, thm := some ``remBoolParity_proven },
  { id := "floatintcov-int-negate", juliaFile := "base/int.jl", juliaFns := ["negate", "negate(::Unsigned)"],
    statement := "negate(x) of a signed BitInteger is its additive inverse, exactly -x unless x == typemin; of an unsigned x it is exactly -x in the signed type of the same size, or InexactError.",
    source := "invariant (step negation in range.jl:1322,1445,1451); base/int.jl:95-98", status := .proven,
    prop := ``NegateExact, thm := some ``negateExact_proven },
  { id := "floatintcov-int-widemul", juliaFile := "base/int.jl",
    juliaFns := ["widemul(::Signed, ::Unsigned)", "widemul(::Unsigned, ::Signed)", "widemul(::Bool, ::Bool)"],
    statement := "widemul of a signed and an unsigned BitInteger below 128 bits, in either order, is the exact product; widemul of two Bools is their product.",
    source := "docstring of widemul, base/number.jl:307-326; base/int.jl:920-926", status := .proven,
    prop := ``WidemulExact, thm := some ``widemulExact_proven },
  { id := "int-widemul-bool", juliaFile := "base/int.jl",
    juliaFns := ["widemul(::Bool, ::Number)", "widemul(::Number, ::Bool)"],
    statement := "Bool widemul preserves the ordinary multiplication result: the Number identity for true and its strong zero for false, including floating-point and complex values.",
    source := "docstring of widemul; source comment \"multiplication by Bool doesn't require widening\"; base/int.jl:925-928",
    status := .proven, prop := ``AllBoolWidemul, thm := some ``allBoolWidemul_proven },
  { id := "floatintcov-int-mul-hi", juliaFile := "base/int.jl", juliaFns := ["mul_hi(::T, ::T) where T<:BitInteger"],
    statement := "mul_hi(a, b) is floor(a*b / 2^n) for every BitInteger type below 128 bits.",
    source := "docstring of mul_hi; base/int.jl:105-124", status := .proven,
    prop := ``MulHiExact, thm := some ``mulHiExact_proven },
  { id := "int-mul-hi-128", juliaFile := "base/int.jl",
    juliaFns := ["mul_hi(::UInt128, ::UInt128)", "mul_hi(::Int128, ::Int128)"],
    statement := "mul_hi(a, b) for UInt128 and Int128 is floor(a*b / 2^128).",
    source := "docstring of mul_hi; base/int.jl:126-142", status := .proven,
    prop := ``MulHi128, thm := some ``mulHi128_proven },
  { id := "floatintcov-int-string-macros", juliaFile := "base/int.jl", juliaFns := ["@int128_str", "@uint128_str", "@big_str"],
    statement := "Integer literal macros parse representable values and preserve syntax and overflow errors; big literals remove legal separators and use load-time BigFloat precision and rounding.",
    source := "integer string macro docstrings; @big_str load-time precision warning; base/int.jl:707-805", status := .proven,
    prop := ``AllStringMacros, thm := some ``allStringMacros_proven },
  { id := "int-big-str-underscore-dot", juliaFile := "base/int.jl", juliaFns := ["@big_str"],
    statement := "big\"s\" throws ArgumentError whenever _ is right before or right after a dot.",
    source := "source comment \"Do not allow '_' right before or after dot\", base/int.jl:780-781; docstring of @big_str",
    status := .refuted, prop := ``BigStrSourceUnderscoreDot, thm := some ``bigStrSourceUnderscoreDot_refuted,
    issue := "none found (queries: big_str underscore, big string macro underscore dot, BigFloat literal underscore, big\"1_.\")",
    notes := "big\"1_.\" returns 1.0 while big\"1_.0\" and big\"1._5\" throw: the loop never checks the last character." },
  { id := "int-generic-sign-predicates", juliaFile := "base/int.jl",
    juliaFns := ["signbit(::Integer)", "signbit(::Unsigned)", "isnegative(::Unsigned)"],
    statement := "For every custom integer type, signbit detects negative values; unsigned values are never negative.",
    source := "signbit and isnegative contracts; base/int.jl:183-186", status := .proven,
    prop := ``GenericSignPredicates, thm := some ``genericSignPredicates_proven },
  { id := "int-generic-unsigned-abs", juliaFile := "base/int.jl", juliaFns := ["abs(::Unsigned)"],
    statement := "Absolute value preserves every unsigned integer's magnitude and is nonnegative.",
    source := "abs docstring; base/int.jl:233", status := .proven,
    prop := ``GenericAbsUnsigned, thm := some ``genericAbsUnsigned_proven },
  { id := "int-generic-complement", juliaFile := "base/int.jl", juliaFns := ["~(::Integer)"],
    statement := "An integer and its bitwise complement sum to -1, including custom integer types.",
    source := "two's-complement invariant; base/int.jl:236", status := .proven,
    prop := ``GenericComplement, thm := some ``genericComplement_proven },
  { id := "int-generic-zero-count", juliaFile := "base/int.jl", juliaFns := ["count_zeros(::Integer)"],
    statement := "For every finite custom integer representation, count_zeros counts the unset bits.",
    source := "count_zeros docstring; base/int.jl:503-517", status := .proven,
    prop := ``GenericZeroCount, thm := some ``genericZeroCount_proven },
  { id := "int-generic-leading-ones", juliaFile := "base/int.jl", juliaFns := ["leading_ones(::Integer)"],
    statement := "Leading-one counts locate the first unset bit in every finite custom integer representation.",
    source := "leading_ones docstring; base/int.jl:519-530", status := .proven,
    prop := ``GenericLeadingOnes, thm := some ``genericLeadingOnes_proven },
  { id := "int-generic-trailing-ones", juliaFile := "base/int.jl", juliaFns := ["trailing_ones(::Integer)"],
    statement := "Trailing-one counts locate the first unset low bit in every finite custom integer representation.",
    source := "trailing_ones docstring; base/int.jl:532-543", status := .proven,
    prop := ``GenericTrailingOnes, thm := some ``genericTrailingOnes_proven },
  { id := "int-generic-real-parity", juliaFile := "base/int.jl",
    juliaFns := ["isodd(::Real)", "iseven(::Real)"],
    statement := "Every integral real value is classified as odd or even by divisibility by two, and nonintegral values give false.",
    source := "isodd and iseven docstrings; base/int.jl:161,181", status := .proven,
    prop := ``GenericParityReal, thm := some ``genericParityReal_proven },
  { id := "int-generic-flipsign-real", juliaFile := "base/int.jl", juliaFns := ["flipsign(::Signed, ::Real)"],
    statement := "Flipsign on every custom signed type flips the input sign according to the real argument's signbit.",
    source := "flipsign docstring; base/int.jl:194", status := .proven,
    prop := ``GenericFlipsignReal, thm := some ``genericFlipsignReal_proven },
  { id := "int-generic-abs-signed", juliaFile := "base/int.jl", juliaFns := ["abs(::Signed)"],
    statement := "Signed absolute value returns the magnitude with the integer type's wrapping convention.",
    source := "abs docstring; base/int.jl:234", status := .proven,
    prop := ``GenericAbsSigned, thm := some ``genericAbsSigned_proven },
  { id := "int-generic-copysign-signed", juliaFile := "base/int.jl", juliaFns := ["copysign(::Signed, ::Signed)"],
    statement := "Copying a signed argument's sign preserves the input magnitude, with signed overflow.",
    source := "copysign docstring; base/int.jl:196", status := .proven,
    prop := ``GenericCopysignSigned, thm := some ``genericCopysignSigned_proven },
  { id := "int-generic-flipsign-float", juliaFile := "base/int.jl",
    juliaFns := ["flipsign(::Signed, ::Float16)", "flipsign(::Signed, ::Float32)", "flipsign(::Signed, ::Float64)"],
    statement := "All signed integer types use the stored IEEE sign bit for floating-point flipsign arguments.",
    source := "flipsign contract; base/int.jl:191-193", status := .proven,
    prop := ``GenericFloatFlipsign, thm := some ``genericFloatFlipsign_proven },
  { id := "int-generic-copysign-float", juliaFile := "base/int.jl",
    juliaFns := ["copysign(::Signed, ::Float16)", "copysign(::Signed, ::Float32)", "copysign(::Signed, ::Float64)"],
    statement := "All signed integer types copy the stored IEEE sign bit from floating-point arguments.",
    source := "copysign contract; base/int.jl:197-199", status := .proven,
    prop := ``GenericFloatCopysign, thm := some ``genericFloatCopysign_proven },
  { id := "int-generic-negate-unsigned", juliaFile := "base/int.jl", juliaFns := ["negate(::Unsigned)"],
    statement := "Unsigned negation returns the exact negative after a successful Signed conversion, or propagates the conversion error.",
    source := "negation invariant; base/int.jl:97", status := .proven,
    prop := ``GenericNegateUnsigned, thm := some ``genericNegateUnsigned_proven },
  { id := "int-promoted-bitwise", juliaFile := "base/int.jl", juliaFns := ["&(::Integer, ::Integer)", "|(::Integer, ::Integer)", "xor(::Integer, ::Integer)"],
    statement := "For arbitrary Integer pairs, promoted bitwise operators apply their truth tables at every bit of the target representation, preserving conversion and checker errors.",
    source := "bitwise operator docstrings; base/int.jl:1092-1100", status := .proven,
    prop := ``AllPromotedBits, thm := some ``allPromotedBits_proven },
  { id := "int-generic-signed-unsigned-values", juliaFile := "base/int.jl", juliaFns := ["signed", "unsigned"],
    statement := "Generic signed and unsigned conversions preserve the input width, select the requested signedness, and return its mathematical two's-complement representative.",
    source := "signed and unsigned docstrings; base/int.jl:261,272", status := .proven,
    prop := ``WidthPreservingConversions, thm := some ``widthPreservingConversions_proven },
  { id := "int-generic-type-residues", juliaFile := "base/int.jl",
    juliaFns := ["mod(::Integer, ::Type)", "unsafe_trunc(::Type, ::Integer)"],
    statement := "Generic mod-to-type and unsafe_trunc preserve the converted residue through the actual fallback remainder method.",
    source := "type remainder docstring; base/int.jl:698,701,704", status := .proven,
    prop := ``GenericTypeResidues, thm := some ``genericTypeResidues_proven },
  { id := "int-generic-bool-residue", juliaFile := "base/int.jl", juliaFns := ["rem(::Integer, ::Type{Bool})"],
    statement := "For every custom integer representation, x % Bool is true exactly for odd integer values.",
    source := "type remainder docstring; base/int.jl:699", status := .proven,
    prop := ``GenericRemBool, thm := some ``genericRemBool_proven },
  { id := "int-generic-widemul", juliaFile := "base/int.jl",
    juliaFns := ["widemul(::Signed, ::Unsigned)", "widemul(::Unsigned, ::Signed)"],
    statement := "Widened signed/unsigned multiplication gives the full mathematical product for custom integer types.",
    source := "widemul contract; base/int.jl:923-924", status := .proven,
    prop := ``GenericWidemul, thm := some ``genericWidemul_proven },
  { id := "int-generic-number-parity", juliaFile := "base/int.jl", juliaFns := ["isodd(::Number)", "iseven(::Number)"],
    statement := "Number parity is false for non-real inputs and otherwise classifies the integral real part by divisibility by two.",
    source := "isodd and iseven docstrings; base/int.jl:160,180", status := .proven,
    prop := ``GenericParityNumbers, thm := some ``genericParityNumbers_proven },
  { id := "int-generic-signed-mixed", juliaFile := "base/int.jl",
    juliaFns := ["div(::BitSigned, ::Unsigned)", "rem(::BitSigned, ::Unsigned)"],
    statement := "For every unsigned argument type, mixed div and rem attach the dividend's sign to the unsigned quotient or remainder magnitude.",
    source := "div and rem contracts; base/int.jl:275,278", status := .proven,
    prop := ``GenericSignedMixed, thm := some ``genericSignedMixed_proven },
  { id := "int-generic-signed-divrem", juliaFile := "base/int.jl", juliaFns := ["divrem(::BitSigned, ::Unsigned)"],
    statement := "Generic signed-dividend divrem returns the signed quotient and remainder together, or DivideError for a zero divisor.",
    source := "divrem contract; base/int.jl:281-285", status := .proven,
    prop := ``GenericSignedDivrem, thm := some ``genericSignedDivrem_proven },
  { id := "int-generic-unsigned-mixed", juliaFile := "base/int.jl",
    juliaFns := ["div(::Unsigned, ::BitSigned)", "rem(::Unsigned, ::BitSigned)"],
    statement := "Generic unsigned-dividend division retains the source's unsigned result conversion; remainder preserves its exact magnitude.",
    source := "div and rem contracts; base/int.jl:276,279", status := .proven,
    prop := ``GenericUnsignedMixed, thm := some ``genericUnsignedMixed_proven },
  { id := "int-generic-unsigned-divrem", juliaFile := "base/int.jl", juliaFns := ["divrem(::Unsigned, ::BitSigned)"],
    statement := "Generic unsigned-dividend divrem preserves the source's converted quotient and exact unsigned remainder.",
    source := "divrem contract; base/int.jl:286-290", status := .proven,
    prop := ``GenericUnsignedDivrem, thm := some ``genericUnsignedDivrem_proven },
  { id := "int-generic-mul-hi", juliaFile := "base/int.jl", juliaFns := ["mul_hi(::T, ::T) where T<:Integer"],
    statement := "High-half multiplication returns the high word of the full widened mathematical product for every fixed-width custom integer type.",
    source := "mul_hi docstring; base/int.jl:123-125", status := .proven,
    prop := ``GenericMulHi, thm := some ``genericMulHi_proven },
  { id := "int-generic-modulo", juliaFile := "base/int.jl", juliaFns := ["mod(::T, ::T) where T<:Integer"],
    statement := "Generic modulo computes the exact floored remainder, including cancellation of wrapped intermediate arithmetic.",
    source := "mod docstring; base/int.jl:331-334", status := .proven,
    prop := ``GenericModuloInteger, thm := some ``genericModuloInteger_proven },
  { id := "int-generic-copysign-real", juliaFile := "base/int.jl", juliaFns := ["copysign(::Signed, ::Real)"],
    statement := "Generic real copysign gives the input magnitude with the real argument's signbit, subject to signed wrapping.",
    source := "copysign contract; base/int.jl:200", status := .proven,
    prop := ``GenericCopysignReal, thm := some ``genericCopysignReal_proven },
  { id := "int-generic-mod-signed-unsigned", juliaFile := "base/int.jl", juliaFns := ["mod(::BitSigned, ::Unsigned)"],
    statement := "Mixed modulo returns the exact floored remainder for every unsigned divisor type.",
    source := "mod docstring; base/int.jl:342-346", status := .proven,
    prop := ``GenericModSignedUnsigned, thm := some ``genericModSignedUnsigned_proven },
  { id := "int-generic-mod-unsigned-signed", juliaFile := "base/int.jl", juliaFns := ["mod(::Unsigned, ::Signed)"],
    statement := "Mixed modulo returns the exact floored remainder for every custom signed divisor type.",
    source := "mod docstring; base/int.jl:347-350", status := .proven,
    prop := ``GenericModUnsignedSigned, thm := some ``genericModUnsignedSigned_proven },
  { id := "int-generic-abstract-type-residues", juliaFile := "base/int.jl",
    juliaFns := ["rem(::Signed, ::Type{Unsigned})", "rem(::Unsigned, ::Type{Signed})"],
    statement := "Abstract signedness remainders preserve the input type width, select the requested signedness, and return the corresponding mathematical representative.",
    source := "type remainder docstring; base/int.jl:696-697", status := .proven,
    prop := ``WidthPreservingAbstractRemainders, thm := some ``widthPreservingAbstractRemainders_proven },
  { id := "int-invalid-type-method-errors", juliaFile := "base/int.jl",
    juliaFns := ["signed(::Type{Union{}}, ...)", "rem(x, ::Type{Union{}}, ...)", "mod(x, ::Type{Union{}}, ...)", "unsafe_trunc(::Type{Union{}}, ...)", "typemin(::Type{Union{}}, ...)", "typemax(::Type{Union{}}, ...)"],
    statement := "Every invalid Union{} call throws MethodError instead of returning a value; different supplied argument tuples and different functions remain distinguishable in the error metadata.",
    source := "MethodError invariant; base/int.jl:80,700,702,705,907-908", status := .proven,
    prop := ``InvalidTypeErrorsLossless, thm := some ``invalidTypeErrorsLossless_proven },
  { id := "int-generic-signed-negation", juliaFile := "base/int.jl", juliaFns := ["negate(::Signed)"],
    statement := "Generic signed negation returns the additive inverse of the integer's numerical value.",
    source := "negation invariant; base/int.jl:96", status := .proven,
    prop := ``GenericSignedNegation, thm := some ``genericSignedNegation_proven },
  { id := "int-generic-unsigned-modulo", juliaFile := "base/int.jl", juliaFns := ["mod(::T, ::T) where T<:Unsigned"],
    statement := "Modulo on arbitrary unsigned integer types returns the Euclidean remainder and preserves DivideError for a zero divisor.",
    source := "mod docstring; base/int.jl:351", status := .proven,
    prop := ``GenericUnsignedModulo, thm := some ``genericUnsignedModulo_proven },
  { id := "int-floating-integer-division", juliaFile := "base/int.jl",
    juliaFns := ["inv(::Integer)", "/(::T, ::T) where T<:Integer", "/(::BitInteger, ::BitInteger)"],
    statement := "Integer reciprocal and true division round the floating operands and their numerical quotient in the selected floating format, including signed zero, infinity and NaN behavior.",
    source := "inv, / and float contracts; base/int.jl:100-103", status := .proven,
    prop := ``IntegerFloatingDivision, thm := some ``integerFloatingDivision_proven }
]

end JuliaLean.Proofs.base.int
