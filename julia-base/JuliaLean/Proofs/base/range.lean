import JuliaLean.base.range
import JuliaLean.base.int
import JuliaLean.base.number
import JuliaLean.base.checked
import JuliaLean.base.bool
import JuliaLean.base.tuple
import JuliaLean.base.float
import JuliaLean.base.operators
import JuliaLean.base.promotion
import JuliaLean.base.abstractarray
import JuliaLean.base.char
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.checked
import JuliaLean.Registry.Types

/-!
# Properties of `base/range.jl`

Specifications of the methods modelled in `JuliaLean.base.range`, stated as the docstrings, the
manual or obvious invariants promise them, with their proofs, refutations and registry entries.

The model calls every generic function through a typeclass. The first part of this file is the
dispatch world: the instances of those classes for the Julia types the properties talk about.
Julia's dispatch is trusted; each range instance names the `base/range.jl` method that `which`
selects for those argument types on the target build. Integer
callees from `base/int.jl` are the definitions of `JuliaLean.base.int`; callees from files that
are not migrated yet (`div.jl`, `checked.jl`, `abstractarray.jl`, `number.jl`) are written here
from their Julia definitions.

Specification vocabulary (independent of the model): `Int` arithmetic, `intsFromTo a b` (the
integers `a, a+1, ..., b`), `stepElems a s n` (the `n` integers `a, a+s, ...`) and `iterList r`
(the elements a `for` loop over `r` visits through Julia's iteration protocol).
-/

/-! ## Integer value lemmas

Value lemmas for the `base/int.jl` definitions the world uses, copied from
`JuliaLean.Proofs.base.int` (`wrapInt t z` is `z` reduced into `t`'s range). -/

namespace JuliaLean.Proofs.base.range.IntVal

open JuliaLean JuliaLean.C JuliaLean.Promotion JuliaLean.base.int

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
    cmp_BitUnsigned_BitSigned eqSame x y = decide (x.val = y.val) ∧
    cmp_BitUnsigned_BitSigned ltSame x y = decide (x.val < y.val) ∧
    cmp_BitUnsigned_BitSigned leSame x y = decide (x.val ≤ y.val)
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

end JuliaLean.Proofs.base.range.IntVal

namespace JuliaLean.Proofs.base.range

open JuliaLean JuliaLean.base.range JuliaLean.Registry
open JuliaLean.base.int (add sub mul neg mulSame addWrap subWrap mulWrap lt le eq remT unsigned
  flipsign jmin jmax minType divSame remSame binop lit mod_BitSigned mod_Unsigned)

/-- A `base/int.jl` computation inside a range method: its `JlError` is the range exception. -/
def liftJl {α : Type} (x : Jl α) : JlX α :=
  match x with
  | .ok v => .ok v
  | .error e => .error (.jl e)

@[simp] theorem liftJl_ok {α : Type} (v : α) : liftJl (.ok v) = .ok v := rfl
@[simp] theorem liftJl_error {α : Type} (e : JlError) : liftJl (.error e : Jl α) = .error (.jl e) := rfl

/-! ## Dispatch world: integer scalars -/

/-! ## Result types as reducible tables

The result type of an operation on two BitInteger types, tabulated so that instance resolution
computes it for concrete types (a call on `UInt64` and `Int64` values then continues with the
`UInt64` methods, as in Julia). Each table equals the definition it tabulates. -/

/-- `signed(T)` as a reducible table (`IntTy.toSigned`). -/
abbrev sTy : IntTy → IntTy
  | .u8 => .i8 | .u16 => .i16 | .u32 => .i32 | .u64 => .i64 | .u128 => .i128 | t => t

theorem sTy_eq (t : IntTy) : sTy t = t.toSigned := by cases t <;> rfl

/-- A value of a BitInteger type, at a type index proved equal. -/
abbrev castJ {a b : IntTy} (h : a = b) (x : JInt a) : JInt b := ⟨x.val, h ▸ x.property⟩

@[simp] theorem castJ_val {a b : IntTy} (h : a = b) (x : JInt a) : (castJ h x).val = x.val := rfl

/-- `promote_type(S, T)` of two BitInteger types (`base/int.jl:809-822`), `IntTy.promote`, as a reducible table. -/
abbrev pTy : IntTy → IntTy → IntTy
  | .i8, .i8 => .i8 | .i8, .i16 => .i16 | .i8, .i32 => .i32 | .i8, .i64 => .i64 | .i8, .i128 => .i128 | .i8, .u8 => .u8 | .i8, .u16 => .u16 | .i8, .u32 => .u32 | .i8, .u64 => .u64 | .i8, .u128 => .u128
  | .i16, .i8 => .i16 | .i16, .i16 => .i16 | .i16, .i32 => .i32 | .i16, .i64 => .i64 | .i16, .i128 => .i128 | .i16, .u8 => .i16 | .i16, .u16 => .u16 | .i16, .u32 => .u32 | .i16, .u64 => .u64 | .i16, .u128 => .u128
  | .i32, .i8 => .i32 | .i32, .i16 => .i32 | .i32, .i32 => .i32 | .i32, .i64 => .i64 | .i32, .i128 => .i128 | .i32, .u8 => .i32 | .i32, .u16 => .i32 | .i32, .u32 => .u32 | .i32, .u64 => .u64 | .i32, .u128 => .u128
  | .i64, .i8 => .i64 | .i64, .i16 => .i64 | .i64, .i32 => .i64 | .i64, .i64 => .i64 | .i64, .i128 => .i128 | .i64, .u8 => .i64 | .i64, .u16 => .i64 | .i64, .u32 => .i64 | .i64, .u64 => .u64 | .i64, .u128 => .u128
  | .i128, .i8 => .i128 | .i128, .i16 => .i128 | .i128, .i32 => .i128 | .i128, .i64 => .i128 | .i128, .i128 => .i128 | .i128, .u8 => .i128 | .i128, .u16 => .i128 | .i128, .u32 => .i128 | .i128, .u64 => .i128 | .i128, .u128 => .u128
  | .u8, .i8 => .u8 | .u8, .i16 => .i16 | .u8, .i32 => .i32 | .u8, .i64 => .i64 | .u8, .i128 => .i128 | .u8, .u8 => .u8 | .u8, .u16 => .u16 | .u8, .u32 => .u32 | .u8, .u64 => .u64 | .u8, .u128 => .u128
  | .u16, .i8 => .u16 | .u16, .i16 => .u16 | .u16, .i32 => .i32 | .u16, .i64 => .i64 | .u16, .i128 => .i128 | .u16, .u8 => .u16 | .u16, .u16 => .u16 | .u16, .u32 => .u32 | .u16, .u64 => .u64 | .u16, .u128 => .u128
  | .u32, .i8 => .u32 | .u32, .i16 => .u32 | .u32, .i32 => .u32 | .u32, .i64 => .i64 | .u32, .i128 => .i128 | .u32, .u8 => .u32 | .u32, .u16 => .u32 | .u32, .u32 => .u32 | .u32, .u64 => .u64 | .u32, .u128 => .u128
  | .u64, .i8 => .u64 | .u64, .i16 => .u64 | .u64, .i32 => .u64 | .u64, .i64 => .u64 | .u64, .i128 => .i128 | .u64, .u8 => .u64 | .u64, .u16 => .u64 | .u64, .u32 => .u64 | .u64, .u64 => .u64 | .u64, .u128 => .u128
  | .u128, .i8 => .u128 | .u128, .i16 => .u128 | .u128, .i32 => .u128 | .u128, .i64 => .u128 | .u128, .i128 => .u128 | .u128, .u8 => .u128 | .u128, .u16 => .u128 | .u128, .u32 => .u128 | .u128, .u64 => .u128 | .u128, .u128 => .u128

theorem pTy_eq (s t : IntTy) : pTy s t = s.promote t := by cases s <;> cases t <;> rfl

/-- the result type `minType` of `min(x::S, y::T)` (`base/int.jl`), as a reducible table. -/
abbrev minTyR : IntTy → IntTy → IntTy
  | .i8, .i8 => .i8 | .i8, .i16 => .i16 | .i8, .i32 => .i32 | .i8, .i64 => .i64 | .i8, .i128 => .i128 | .i8, .u8 => .i8 | .i8, .u16 => .i8 | .i8, .u32 => .i8 | .i8, .u64 => .i8 | .i8, .u128 => .i8
  | .i16, .i8 => .i16 | .i16, .i16 => .i16 | .i16, .i32 => .i32 | .i16, .i64 => .i64 | .i16, .i128 => .i128 | .i16, .u8 => .i16 | .i16, .u16 => .i16 | .i16, .u32 => .i16 | .i16, .u64 => .i16 | .i16, .u128 => .i16
  | .i32, .i8 => .i32 | .i32, .i16 => .i32 | .i32, .i32 => .i32 | .i32, .i64 => .i64 | .i32, .i128 => .i128 | .i32, .u8 => .i32 | .i32, .u16 => .i32 | .i32, .u32 => .i32 | .i32, .u64 => .i32 | .i32, .u128 => .i32
  | .i64, .i8 => .i64 | .i64, .i16 => .i64 | .i64, .i32 => .i64 | .i64, .i64 => .i64 | .i64, .i128 => .i128 | .i64, .u8 => .i64 | .i64, .u16 => .i64 | .i64, .u32 => .i64 | .i64, .u64 => .i64 | .i64, .u128 => .i64
  | .i128, .i8 => .i128 | .i128, .i16 => .i128 | .i128, .i32 => .i128 | .i128, .i64 => .i128 | .i128, .i128 => .i128 | .i128, .u8 => .i128 | .i128, .u16 => .i128 | .i128, .u32 => .i128 | .i128, .u64 => .i128 | .i128, .u128 => .i128
  | .u8, .i8 => .i8 | .u8, .i16 => .i16 | .u8, .i32 => .i32 | .u8, .i64 => .i64 | .u8, .i128 => .i128 | .u8, .u8 => .u8 | .u8, .u16 => .u16 | .u8, .u32 => .u32 | .u8, .u64 => .u64 | .u8, .u128 => .u128
  | .u16, .i8 => .i8 | .u16, .i16 => .i16 | .u16, .i32 => .i32 | .u16, .i64 => .i64 | .u16, .i128 => .i128 | .u16, .u8 => .u16 | .u16, .u16 => .u16 | .u16, .u32 => .u32 | .u16, .u64 => .u64 | .u16, .u128 => .u128
  | .u32, .i8 => .i8 | .u32, .i16 => .i16 | .u32, .i32 => .i32 | .u32, .i64 => .i64 | .u32, .i128 => .i128 | .u32, .u8 => .u32 | .u32, .u16 => .u32 | .u32, .u32 => .u32 | .u32, .u64 => .u64 | .u32, .u128 => .u128
  | .u64, .i8 => .i8 | .u64, .i16 => .i16 | .u64, .i32 => .i32 | .u64, .i64 => .i64 | .u64, .i128 => .i128 | .u64, .u8 => .u64 | .u64, .u16 => .u64 | .u64, .u32 => .u64 | .u64, .u64 => .u64 | .u64, .u128 => .u128
  | .u128, .i8 => .i8 | .u128, .i16 => .i16 | .u128, .i32 => .i32 | .u128, .i64 => .i64 | .u128, .i128 => .i128 | .u128, .u8 => .u128 | .u128, .u16 => .u128 | .u128, .u32 => .u128 | .u128, .u64 => .u128 | .u128, .u128 => .u128

theorem minTyR_eq (s t : IntTy) : minTyR s t = JuliaLean.base.int.minType s t := by cases s <;> cases t <;> rfl

section IntScalars

variable {s t : IntTy}

/-- Julia's type tests on a BitInteger type `T`: `T === Bool` is false, `T <: Signed` is the
signedness, `T <: Integer` holds, `T <: AbstractFloat` fails. -/
instance : JType (JInt t) where
  isBool := false
  isSigned := t.signed
  isInteger := true
  isAbstractFloat := false
  bool_eq := by intro h; cases h

/-- `x == y` on BitIntegers (`base/int.jl`). -/
instance : JEq (JInt s) (JInt t) := ⟨eq⟩
/-- `x < y` on BitIntegers (`base/int.jl`). -/
instance : JLt (JInt s) (JInt t) := ⟨lt⟩
/-- `x <= y` on BitIntegers (`base/int.jl`). -/
instance : JLe (JInt s) (JInt t) := ⟨le⟩
/-- `isless(x::Real, y::Real) = x < y` (`operators.jl`). -/
instance : JIsless (JInt s) (JInt t) := ⟨lt⟩
/-- `zero(T) = convert(T, 0)` (`number.jl`). -/
instance : JZero (JInt t) := ⟨lit t 0⟩
/-- `oneunit(T) = T(one(T))` (`number.jl`). -/
instance : JOneunit (JInt t) := ⟨lit t 1⟩
/-- `one(T) = T(1)` (`number.jl`). -/
instance : JOne (JInt t) := ⟨lit t 1⟩
/-- `iszero(x) = x == zero(x)` (`number.jl:44`), with `zero(x)` of `base/int.jl` and `==` of
`base/int.jl:84`. -/
instance : JIszero (JInt t) := ⟨fun x => eq x (JuliaLean.base.int.zero x)⟩
/-- `isone(x) = x == one(x)` (`number.jl:66`), with `one(x) = one(T) = convert(T, 1)`. -/
instance : JIsone (JInt t) := ⟨fun x => eq x (lit t 1)⟩
/-- `isinteger(x::Integer) = true` (`number.jl:22`). -/
instance : JIsinteger (JInt t) := ⟨JuliaLean.base.number.isintegerInteger⟩
/-- Unary minus, `-(x::BitInteger) = neg_int(x)` (`base/int.jl:85`). -/
instance : JNeg (JInt t) (JInt t) := ⟨neg⟩
/-- `x + y` on one BitInteger type (`base/int.jl:88`). -/
scoped instance (priority := high) : HAdd (JInt t) (JInt t) (JInt t) := ⟨add⟩
/-- `x - y` on one BitInteger type (`base/int.jl:87`). -/
scoped instance (priority := high) : HSub (JInt t) (JInt t) (JInt t) := ⟨sub⟩
/-- `x * y` on one BitInteger type (`base/int.jl:89`, `base/int.jl:1020` for 128 bits). -/
scoped instance (priority := high) : HMul (JInt t) (JInt t) (JInt t) := ⟨mulSame⟩
/-- `x + y` on two BitInteger types: promote, then add (`base/int.jl:1092-1100`). -/
scoped instance (priority := low) : HAdd (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨fun x y => castJ (pTy_eq s t).symm (binop add x y)⟩
/-- `x - y` on two BitInteger types (`base/int.jl:1092-1100`). -/
scoped instance (priority := low) : HSub (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨fun x y => castJ (pTy_eq s t).symm (binop sub x y)⟩
/-- `x * y` on two BitInteger types (`base/int.jl:1092-1100`). -/
scoped instance (priority := low) : HMul (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨fun x y => castJ (pTy_eq s t).symm (binop mulSame x y)⟩
/-- `x +% y` (`base/int.jl:93`). -/
instance : JWrappingAdd (JInt t) (JInt t) (JInt t) := ⟨addWrap⟩
/-- `x -% y` (`base/int.jl:92`). -/
instance : JWrappingSub (JInt t) (JInt t) (JInt t) := ⟨subWrap⟩
/-- `x *% y` (`base/int.jl:94`). -/
instance : JWrappingMul (JInt t) (JInt t) (JInt t) := ⟨mulWrap⟩
/-- `_range_wrapping_add(x::_RangeWrappingInteger, y::_RangeWrappingInteger)`, range.jl:34. -/
instance : JRangeWrappingAdd (JInt t) (JInt t) (JInt t) := ⟨_range_wrapping_add_BitInteger⟩
/-- range.jl:36. -/
instance : JRangeWrappingSub (JInt t) (JInt t) (JInt t) := ⟨_range_wrapping_sub_BitInteger⟩
/-- range.jl:38. -/
instance : JRangeWrappingMul (JInt t) (JInt t) (JInt t) := ⟨_range_wrapping_mul_BitInteger⟩
/-- `convert(T, x)` between BitIntegers (`boot.jl` checked conversions, `base/int.jl`). -/
instance : JConvert (JInt t) (JInt s) := ⟨fun x => liftJl (JuliaLean.base.int.convert t x)⟩
/-- `T(x)` between BitIntegers is the checked conversion (`boot.jl`). -/
instance : JCtor (JInt t) (JInt s) := ⟨fun x => liftJl (JuliaLean.base.int.convert t x)⟩
/-- `Integer(x::Integer) = x` (`boot.jl`). -/
instance : JInteger (JInt t) (JInt t) := ⟨pure⟩
/-- `x % T` (`base/int.jl:632-648`). -/
instance : JRemType (JInt t) (JInt s) := ⟨remT t⟩
/-- `unsigned(x)` (`base/int.jl`). -/
instance : JUnsigned (JInt t) (JInt t.toUnsigned) := ⟨unsigned⟩
/-- `flipsign(x, y)` (`base/int.jl`). -/
instance : JFlipsign (JInt s) (JInt t) := ⟨flipsign⟩
/-- `min(x, y)` (`base/int.jl`, `promotion.jl`). -/
instance : JMin (JInt s) (JInt t) (JInt (minTyR s t)) :=
  ⟨fun x y => pure (castJ (minTyR_eq s t).symm (jmin x y))⟩
/-- `max(x, y)` (`base/int.jl`, `promotion.jl`). -/
instance : JMax (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨fun x y => pure (castJ (pTy_eq s t).symm (jmax x y))⟩
/-- `min(x::T, y::T)`: `jmin`, whose type `minType t t` is `T`. -/
instance (priority := high) : JMin (JInt t) (JInt t) (JInt t) :=
  ⟨fun x y => pure (remT t (jmin x y))⟩
/-- `max(x::T, y::T)`: `jmax`, whose type `promote t t` is `T`. -/
instance (priority := high) : JMax (JInt t) (JInt t) (JInt t) :=
  ⟨fun x y => pure (remT t (jmax x y))⟩
/-- `div(x::T, y::T)` (`base/int.jl:1110-1113`, `1140-1143`). -/
instance : JDiv (JInt t) (JInt t) (JInt t) := ⟨fun x y => liftJl (divSame x y)⟩
/-- `rem(x::T, y::T)` (`base/int.jl:1110-1113`, `1145-1148`). -/
instance : JRem (JInt t) (JInt t) (JInt t) := ⟨fun x y => liftJl (remSame x y)⟩
/-- `div(x, y)`/`rem(x, y)` of two BitIntegers through `promote` (`promotion.jl`), the callee
parameter of `base/int.jl`'s mixed-signedness methods. -/
def divPromoted : JuliaLean.base.int.BinOpJl := fun x y => divSame (remT _ x) (remT _ y)
def remPromoted : JuliaLean.base.int.BinOpJl := fun x y => remSame (remT _ x) (remT _ y)
/-- `div(x::unsigned(T), y::T)`: for signed `T`,
`div(x::Unsigned, y::BitSigned) = unsigned(flipsign(signed(div(x, unsigned(abs(y)))), y))`
(`base/int.jl:276`); for unsigned `T`, the same-type `div`. -/
instance : JDiv (JInt t.toUnsigned) (JInt t) (JInt t.toUnsigned) := ⟨fun x y =>
  if t.signed then
    liftJl ((JuliaLean.base.int.div_Unsigned_BitSigned divPromoted x y).map (remT _))
  else liftJl (divSame x (remT _ y))⟩
/-- `rem(x::unsigned(T), y::T)`: for signed `T`, `rem(x::Unsigned, y::BitSigned) =
rem(x, unsigned(abs(y)))` (`base/int.jl:278`); for unsigned `T`, the same-type `rem`. -/
instance : JRem (JInt t.toUnsigned) (JInt t) (JInt t.toUnsigned) := ⟨fun x y =>
  if t.signed then
    liftJl ((JuliaLean.base.int.rem_Unsigned_BitSigned remPromoted x y).map (remT _))
  else liftJl (remSame x (remT _ y))⟩
/-- Result type of `div(x::S, y::T)` for BitIntegers: the promoted type for equal signedness,
else the type of `base/int.jl:275-276`. -/
abbrev divTy (s t : IntTy) : IntTy :=
  if s.signed = t.signed then s.promote t
  else if s.signed then (s.toUnsigned.promote t).toSigned
  else (s.promote t.toUnsigned).toSigned.toUnsigned
/-- the result type `divTy` of `div(x::S, y::T)`, as a reducible table. -/
abbrev divTyR : IntTy → IntTy → IntTy
  | .i8, .i8 => .i8 | .i8, .i16 => .i16 | .i8, .i32 => .i32 | .i8, .i64 => .i64 | .i8, .i128 => .i128 | .i8, .u8 => .i8 | .i8, .u16 => .i16 | .i8, .u32 => .i32 | .i8, .u64 => .i64 | .i8, .u128 => .i128
  | .i16, .i8 => .i16 | .i16, .i16 => .i16 | .i16, .i32 => .i32 | .i16, .i64 => .i64 | .i16, .i128 => .i128 | .i16, .u8 => .i16 | .i16, .u16 => .i16 | .i16, .u32 => .i32 | .i16, .u64 => .i64 | .i16, .u128 => .i128
  | .i32, .i8 => .i32 | .i32, .i16 => .i32 | .i32, .i32 => .i32 | .i32, .i64 => .i64 | .i32, .i128 => .i128 | .i32, .u8 => .i32 | .i32, .u16 => .i32 | .i32, .u32 => .i32 | .i32, .u64 => .i64 | .i32, .u128 => .i128
  | .i64, .i8 => .i64 | .i64, .i16 => .i64 | .i64, .i32 => .i64 | .i64, .i64 => .i64 | .i64, .i128 => .i128 | .i64, .u8 => .i64 | .i64, .u16 => .i64 | .i64, .u32 => .i64 | .i64, .u64 => .i64 | .i64, .u128 => .i128
  | .i128, .i8 => .i128 | .i128, .i16 => .i128 | .i128, .i32 => .i128 | .i128, .i64 => .i128 | .i128, .i128 => .i128 | .i128, .u8 => .i128 | .i128, .u16 => .i128 | .i128, .u32 => .i128 | .i128, .u64 => .i128 | .i128, .u128 => .i128
  | .u8, .i8 => .u8 | .u8, .i16 => .u16 | .u8, .i32 => .u32 | .u8, .i64 => .u64 | .u8, .i128 => .u128 | .u8, .u8 => .u8 | .u8, .u16 => .u16 | .u8, .u32 => .u32 | .u8, .u64 => .u64 | .u8, .u128 => .u128
  | .u16, .i8 => .u16 | .u16, .i16 => .u16 | .u16, .i32 => .u32 | .u16, .i64 => .u64 | .u16, .i128 => .u128 | .u16, .u8 => .u16 | .u16, .u16 => .u16 | .u16, .u32 => .u32 | .u16, .u64 => .u64 | .u16, .u128 => .u128
  | .u32, .i8 => .u32 | .u32, .i16 => .u32 | .u32, .i32 => .u32 | .u32, .i64 => .u64 | .u32, .i128 => .u128 | .u32, .u8 => .u32 | .u32, .u16 => .u32 | .u32, .u32 => .u32 | .u32, .u64 => .u64 | .u32, .u128 => .u128
  | .u64, .i8 => .u64 | .u64, .i16 => .u64 | .u64, .i32 => .u64 | .u64, .i64 => .u64 | .u64, .i128 => .u128 | .u64, .u8 => .u64 | .u64, .u16 => .u64 | .u64, .u32 => .u64 | .u64, .u64 => .u64 | .u64, .u128 => .u128
  | .u128, .i8 => .u128 | .u128, .i16 => .u128 | .u128, .i32 => .u128 | .u128, .i64 => .u128 | .u128, .i128 => .u128 | .u128, .u8 => .u128 | .u128, .u16 => .u128 | .u128, .u32 => .u128 | .u128, .u64 => .u128 | .u128, .u128 => .u128

theorem divTyR_eq (s t : IntTy) : divTyR s t = divTy s t := by cases s <;> cases t <;> rfl
/-- `div(x::S, y::T)` for BitIntegers of different types: promoted for equal signedness
(`promotion.jl`), else `base/int.jl:275` or `base/int.jl:276`. -/
instance (priority := low) : JDiv (JInt s) (JInt t) (JInt (divTyR s t)) := ⟨fun x y =>
  if s.signed = t.signed then liftJl ((divPromoted x y).map (remT _))
  else if s.signed then
    liftJl ((JuliaLean.base.int.div_BitSigned_Unsigned divPromoted x y).map (remT _))
  else liftJl ((JuliaLean.base.int.div_Unsigned_BitSigned divPromoted x y).map (remT _))⟩
/-- A value of a `Union` type dispatches on its runtime component (`rem`). -/
instance {α β δ γ : Type} [JRem α β γ] [JRem α δ γ] : JRem α (β ⊕ δ) γ :=
  ⟨fun a b => match b with | .inl x => JRem.rem a x | .inr x => JRem.rem a x⟩
/-- A value of a `Union` type dispatches on its runtime component (`div`). -/
instance {α β δ γ : Type} [JDiv α β γ] [JDiv α δ γ] : JDiv α (β ⊕ δ) γ :=
  ⟨fun a b => match b with | .inl x => JDiv.div a x | .inr x => JDiv.div a x⟩
/-- `fld(x::T, y::T)` for BitIntegers (`div.jl:460-464`): `d = div(x, y)`, corrected by one when
the signs differ and the division is inexact. -/
instance : JFld (JInt t) (JInt t) (JInt t) := ⟨fun x y => liftJl (JInt.fld x y)⟩
/-- `cld(x::T, y::T)` for BitIntegers (`div.jl:467-474`). -/
instance : JCld (JInt t) (JInt t) (JInt t) := ⟨fun x y => liftJl (JInt.cld x y)⟩
/-- `mod(x::T, y::T)` (`base/int.jl:331-351`, with `fld` of `div.jl`). -/
instance : JMod (JInt t) (JInt t) (JInt t) :=
  ⟨fun x y => liftJl (if t.signed then mod_BitSigned JInt.fld x y else mod_Unsigned x y)⟩
/-- `checked_add(x::T, y::T)` (`checked.jl:225-228`): `add_with_overflow`, `OverflowError` on
overflow (`JuliaLean.base.checked.checkedAddBits`). -/
instance : JCheckedAdd (JInt t) (JInt t) (JInt t) := ⟨fun x y =>
  liftJl (JuliaLean.base.checked.checkedAddBits x y)⟩
/-- `checked_sub(x::T, y::T)` (`checked.jl:282-285`, `JuliaLean.base.checked.checkedSubBits`). -/
instance : JCheckedSub (JInt t) (JInt t) (JInt t) := ⟨fun x y =>
  liftJl (JuliaLean.base.checked.checkedSubBits x y)⟩
/-- `print(io, x)` of an integer writes its decimal digits (`show.jl`). -/
instance : JPrint (JInt t) := ⟨fun x => toString x.val⟩
/-- `show(io, T)` of a BitInteger type. -/
instance : JShowType (JInt t) := ⟨t.name⟩
/-- `x === nothing`. -/
instance : JIsNothing (JInt t) := ⟨fun _ => false⟩

end IntScalars

/-- `nothing === nothing`. -/
instance : JIsNothing Nothing := ⟨fun _ => true⟩
/-- `print(io, nothing)`. -/
instance : JPrint Nothing := ⟨fun _ => "nothing"⟩

/-- The trait `ArithmeticWraps()` (`traits.jl`). -/
structure ArithmeticWraps where

/-- Length type of an integer range on 64-bit Julia: `Int` for the `smallints` (range.jl:810-814),
else the element type. -/
abbrev lenTy : IntTy → IntTy
  | .i8 | .i16 | .i32 | .u8 | .u16 | .u32 => .i64
  | t => t

/-! ## Dispatch world: integer ranges

`UnitRange{T}`, `StepRange{T,T}` and `OneTo{T}` for every BitInteger `T`, indexed by `Int`. -/

section IntRanges

variable {t : IntTy}

instance : JEltype (UnitRange (JInt t)) (JInt t) := ⟨⟩
instance : JEltype (StepRange (JInt t) (JInt t)) (JInt t) := ⟨⟩
instance : JEltype (OneTo (JInt t)) (JInt t) := ⟨⟩
instance : JFieldStart (UnitRange (JInt t)) (JInt t) := ⟨UnitRange.start⟩
instance : JFieldStop (UnitRange (JInt t)) (JInt t) := ⟨UnitRange.stop⟩
instance : JFieldStart (StepRange (JInt t) (JInt t)) (JInt t) := ⟨StepRange.start⟩
instance : JFieldStop (StepRange (JInt t) (JInt t)) (JInt t) := ⟨StepRange.stop⟩
instance : JFieldStop (OneTo (JInt t)) (JInt t) := ⟨OneTo.stop⟩

/-- `OrderStyle(::Type{<:Real}) = Ordered()` (`traits.jl:10`). -/
instance : JOrderStyle (JInt t) Ordered := ⟨⟨⟩⟩
/-- `ArithmeticStyle(::Type{<:Integer}) = ArithmeticWraps()` (`traits.jl:30`). -/
instance : JArithmeticStyle (JInt t) ArithmeticWraps := ⟨⟨⟩⟩

/-! ### Construction -/

/-- `unitrange_last(start::Integer, stop::Integer)`, range.jl:439. -/
instance : JUnitrangeLast (JInt t) (JInt t) := ⟨unitrange_last_Integer⟩
/-- `UnitRange{T}(start::T, stop::T)`, range.jl:428. -/
instance : JUnitRangeT (JInt t) (JInt t) (JInt t) := ⟨UnitRange_T_new⟩
/-- `UnitRange(start::T, stop::T) where {T<:Real}`, range.jl:431. -/
instance : JUnitRange2 (JInt t) (JInt t) (UnitRange (JInt t)) := ⟨UnitRange_T_T⟩
/-- `(:)(start::T, stop::T) where {T<:Real}`, range.jl:5. -/
instance : JColon2 (JInt t) (JInt t) (UnitRange (JInt t)) := ⟨colon_T_T_Real⟩
/-- `steprange_last_empty(start::Integer, step, stop)`, range.jl:389. -/
instance : JSteprangeLastEmpty (JInt t) (JInt t) (JInt t) := ⟨steprange_last_empty_Integer⟩
/-- `steprange_last(start, step, stop)`, range.jl:353. -/
instance : JSteprangeLast (JInt t) (JInt t) (JInt t) := ⟨steprange_last⟩
/-- `StepRange{T,S}(start, step, stop)`, range.jl:344. -/
instance : JStepRangeTS (JInt t) (JInt t) (JInt t) (JInt t) (JInt t) :=
  ⟨StepRange_TS_new (JInt t) (JInt t)⟩
/-- `StepRange(start::T, step::S, stop::T)`, range.jl:404. -/
instance : JStepRange3 (JInt t) (JInt t) (JInt t) (StepRange (JInt t) (JInt t)) :=
  ⟨StepRange_T_S_T⟩
/-- `_colon(::Ordered, ::Any, start::T, step, stop::T)`, range.jl:24. -/
instance : JColonStyle Ordered ArithmeticWraps (JInt t) (JInt t) (JInt t)
    (StepRange (JInt t) (JInt t)) := ⟨_colon_Ordered_Any⟩
/-- `(:)(start::T, step::T, stop::T) where {T<:Real}`, range.jl:22. -/
instance : JColon3 (JInt t) (JInt t) (JInt t) (StepRange (JInt t) (JInt t)) :=
  ⟨colon_T_T_T_Real⟩
/-- `OneTo{T}(stop)`, range.jl:487. -/
instance : JOneToT (JInt t) (JInt t) := ⟨OneTo_T_stop⟩
/-- `OneTo(stop::T) where {T<:Integer}`, range.jl:505. -/
instance : JOneTo1 (JInt t) (OneTo (JInt t)) := ⟨OneTo_stop⟩

/-! ### Endpoints, step, emptiness -/

/-- `first(r::OrdinalRange{T})`, range.jl:867. -/
instance : JFirst (UnitRange (JInt t)) (JInt t) := ⟨first_OrdinalRange⟩
instance : JFirst (StepRange (JInt t) (JInt t)) (JInt t) := ⟨first_OrdinalRange⟩
/-- `first(r::OneTo{T})`, range.jl:868. -/
instance : JFirst (OneTo (JInt t)) (JInt t) := ⟨fun r => pure (first_OneTo r)⟩
/-- `last(r::OrdinalRange{T})`, range.jl:877. -/
instance : JLast (UnitRange (JInt t)) (JInt t) := ⟨last_OrdinalRange⟩
instance : JLast (StepRange (JInt t) (JInt t)) (JInt t) := ⟨last_OrdinalRange⟩
instance : JLast (OneTo (JInt t)) (JInt t) := ⟨last_OrdinalRange⟩
/-- `isempty(r::AbstractUnitRange)`, range.jl:711. -/
instance : JIsempty (UnitRange (JInt t)) := ⟨isempty_AbstractUnitRange⟩
instance : JIsempty (OneTo (JInt t)) := ⟨isempty_AbstractUnitRange⟩
/-- `isempty(r::StepRange)`, range.jl:708. -/
instance : JIsempty (StepRange (JInt t) (JInt t)) := ⟨fun r => pure (isempty_StepRange r)⟩
/-- `step(r::AbstractUnitRange{T})`, range.jl:736. -/
instance : JStep (UnitRange (JInt t)) (JInt t) := ⟨fun r => pure (step_AbstractUnitRange r)⟩
instance : JStep (OneTo (JInt t)) (JInt t) := ⟨fun r => pure (step_AbstractUnitRange r)⟩
/-- `step(r::StepRange)`, range.jl:735. -/
instance : JStep (StepRange (JInt t) (JInt t)) (JInt t) := ⟨fun r => pure (step_StepRange r)⟩
/-- `step_hp(r::AbstractRange)`, range.jl:744. -/
instance : JStepHp (UnitRange (JInt t)) (JInt t) := ⟨step_hp_AbstractRange⟩
instance : JStepHp (OneTo (JInt t)) (JInt t) := ⟨step_hp_AbstractRange⟩
instance : JStepHp (StepRange (JInt t) (JInt t)) (JInt t) := ⟨step_hp_AbstractRange⟩
/-- `iterate(r::OrdinalRange)`, range.jl:935. -/
instance : JIterate1 (UnitRange (JInt t)) (JInt t) (JInt t) := ⟨iterate_OrdinalRange⟩
instance : JIterate1 (StepRange (JInt t) (JInt t)) (JInt t) (JInt t) := ⟨iterate_OrdinalRange⟩
instance : JIterate1 (OneTo (JInt t)) (JInt t) (JInt t) := ⟨iterate_OrdinalRange⟩
/-- `iterate(r::OrdinalRange{T}, i)`, range.jl:937. -/
instance : JIterate2 (UnitRange (JInt t)) (JInt t) (JInt t) := ⟨iterate_OrdinalRange_state⟩
instance : JIterate2 (StepRange (JInt t) (JInt t)) (JInt t) (JInt t) := ⟨iterate_OrdinalRange_state⟩
instance : JIterate2 (OneTo (JInt t)) (JInt t) (JInt t) := ⟨iterate_OrdinalRange_state⟩

end IntRanges

/-! ### Lengths

Julia selects the `smallints` methods for 8 to 32 bits and the generic or `bigints` methods for
64 and 128 bits. -/

/-- `length(r::AbstractUnitRange{<:smallints})` (range.jl:859) or
`length(r::AbstractUnitRange{T})` (range.jl:794). -/
def lengthUnit : {t : IntTy} → UnitRange (JInt t) → JlX (JInt (lenTy t))
  | .i8, r => length_AbstractUnitRange_smallints r
  | .i16, r => length_AbstractUnitRange_smallints r
  | .i32, r => length_AbstractUnitRange_smallints r
  | .u8, r => length_AbstractUnitRange_smallints r
  | .u16, r => length_AbstractUnitRange_smallints r
  | .u32, r => length_AbstractUnitRange_smallints r
  | .i64, r => length_AbstractUnitRange r
  | .u64, r => length_AbstractUnitRange r
  | .i128, r => length_AbstractUnitRange r
  | .u128, r => length_AbstractUnitRange r

/-- `length(r::OneTo{<:smallints})` (range.jl:860) or `length(r::OneTo{T}) where {T<:bigints}`
(range.jl:817). -/
def lengthOneTo : {t : IntTy} → OneTo (JInt t) → JlX (JInt (lenTy t))
  | .i8, r => length_OneTo_smallints r
  | .i16, r => length_OneTo_smallints r
  | .i32, r => length_OneTo_smallints r
  | .u8, r => length_OneTo_smallints r
  | .u16, r => length_OneTo_smallints r
  | .u32, r => length_OneTo_smallints r
  | .i64, r => pure (length_OneTo_bigints r)
  | .u64, r => pure (length_OneTo_bigints r)
  | .i128, r => pure (length_OneTo_bigints r)
  | .u128, r => pure (length_OneTo_bigints r)

/-- `length(r::OrdinalRange{<:smallints})` (range.jl:853) or
`length(r::OrdinalRange{T}) where T<:bigints` (range.jl:820). -/
def lengthStep : {t : IntTy} → StepRange (JInt t) (JInt t) → JlX (JInt (lenTy t))
  | .i8, r => length_OrdinalRange_smallints r
  | .i16, r => length_OrdinalRange_smallints r
  | .i32, r => length_OrdinalRange_smallints r
  | .u8, r => length_OrdinalRange_smallints r
  | .u16, r => length_OrdinalRange_smallints r
  | .u32, r => length_OrdinalRange_smallints r
  | .i64, r => length_OrdinalRange_bigints r
  | .u64, r => length_OrdinalRange_bigints r
  | .i128, r => length_OrdinalRange_bigints r
  | .u128, r => length_OrdinalRange_bigints r

instance {t : IntTy} : JLength (UnitRange (JInt t)) (JInt (lenTy t)) := ⟨lengthUnit⟩
instance {t : IntTy} : JLength (OneTo (JInt t)) (JInt (lenTy t)) := ⟨lengthOneTo⟩
instance {t : IntTy} : JLength (StepRange (JInt t) (JInt t)) (JInt (lenTy t)) := ⟨lengthStep⟩

/-! ## Dispatch world: BitIntegers of two types

Mixed-type calls promote (`promotion.jl`) or use the mixed-signedness methods of `base/int.jl`.
The same-type instances above have higher priority, so a call on one type uses them. -/

section MixedScalars

variable {s t u : IntTy}

/-- `promote_type(T, T) = T`. -/
instance (priority := high) : JPromoteType (JInt t) (JInt t) (JInt t) := ⟨⟩
/-- `promote_type(S, T)` of two BitInteger types (`base/int.jl:809-822`). -/
instance (priority := low) : JPromoteType (JInt s) (JInt t) (JInt (pTy s t)) := ⟨⟩
/-- `x -% y` of two BitIntegers: promote, then wrap (`base/int.jl:92`, `promotion.jl`). -/
instance (priority := low) : JWrappingSub (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨fun x y => castJ (pTy_eq s t).symm (binop subWrap x y)⟩
/-- `x +% y` of two BitIntegers (`base/int.jl:93`, `promotion.jl`). -/
instance (priority := low) : JWrappingAdd (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨fun x y => castJ (pTy_eq s t).symm (binop addWrap x y)⟩
/-- `x *% y` of two BitIntegers (`base/int.jl:94`, `promotion.jl`). -/
instance (priority := low) : JWrappingMul (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨fun x y => castJ (pTy_eq s t).symm (binop mulWrap x y)⟩
/-- `_range_wrapping_sub(x::_RangeWrappingInteger, y::_RangeWrappingInteger)`, range.jl:36. -/
instance (priority := low) : JRangeWrappingSub (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨_range_wrapping_sub_BitInteger⟩
/-- `_range_wrapping_add(x::_RangeWrappingInteger, y::_RangeWrappingInteger)`, range.jl:34. -/
instance (priority := low) : JRangeWrappingAdd (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨_range_wrapping_add_BitInteger⟩
/-- `_range_wrapping_mul(x::_RangeWrappingInteger, y::_RangeWrappingInteger)`, range.jl:38. -/
instance (priority := low) : JRangeWrappingMul (JInt s) (JInt t) (JInt (pTy s t)) :=
  ⟨_range_wrapping_mul_BitInteger⟩

/-- Result type of `rem(x::S, y::T)` for BitIntegers: promoted for equal signedness, else the
type of `base/int.jl:278-279`. -/
abbrev remTy (s t : IntTy) : IntTy :=
  if s.signed = t.signed then s.promote t
  else if s.signed then (s.toUnsigned.promote t).toSigned
  else s.promote t.toUnsigned
/-- the result type `remTy` of `rem(x::S, y::T)`, as a reducible table. -/
abbrev remTyR : IntTy → IntTy → IntTy
  | .i8, .i8 => .i8 | .i8, .i16 => .i16 | .i8, .i32 => .i32 | .i8, .i64 => .i64 | .i8, .i128 => .i128 | .i8, .u8 => .i8 | .i8, .u16 => .i16 | .i8, .u32 => .i32 | .i8, .u64 => .i64 | .i8, .u128 => .i128
  | .i16, .i8 => .i16 | .i16, .i16 => .i16 | .i16, .i32 => .i32 | .i16, .i64 => .i64 | .i16, .i128 => .i128 | .i16, .u8 => .i16 | .i16, .u16 => .i16 | .i16, .u32 => .i32 | .i16, .u64 => .i64 | .i16, .u128 => .i128
  | .i32, .i8 => .i32 | .i32, .i16 => .i32 | .i32, .i32 => .i32 | .i32, .i64 => .i64 | .i32, .i128 => .i128 | .i32, .u8 => .i32 | .i32, .u16 => .i32 | .i32, .u32 => .i32 | .i32, .u64 => .i64 | .i32, .u128 => .i128
  | .i64, .i8 => .i64 | .i64, .i16 => .i64 | .i64, .i32 => .i64 | .i64, .i64 => .i64 | .i64, .i128 => .i128 | .i64, .u8 => .i64 | .i64, .u16 => .i64 | .i64, .u32 => .i64 | .i64, .u64 => .i64 | .i64, .u128 => .i128
  | .i128, .i8 => .i128 | .i128, .i16 => .i128 | .i128, .i32 => .i128 | .i128, .i64 => .i128 | .i128, .i128 => .i128 | .i128, .u8 => .i128 | .i128, .u16 => .i128 | .i128, .u32 => .i128 | .i128, .u64 => .i128 | .i128, .u128 => .i128
  | .u8, .i8 => .u8 | .u8, .i16 => .u16 | .u8, .i32 => .u32 | .u8, .i64 => .u64 | .u8, .i128 => .u128 | .u8, .u8 => .u8 | .u8, .u16 => .u16 | .u8, .u32 => .u32 | .u8, .u64 => .u64 | .u8, .u128 => .u128
  | .u16, .i8 => .u16 | .u16, .i16 => .u16 | .u16, .i32 => .u32 | .u16, .i64 => .u64 | .u16, .i128 => .u128 | .u16, .u8 => .u16 | .u16, .u16 => .u16 | .u16, .u32 => .u32 | .u16, .u64 => .u64 | .u16, .u128 => .u128
  | .u32, .i8 => .u32 | .u32, .i16 => .u32 | .u32, .i32 => .u32 | .u32, .i64 => .u64 | .u32, .i128 => .u128 | .u32, .u8 => .u32 | .u32, .u16 => .u32 | .u32, .u32 => .u32 | .u32, .u64 => .u64 | .u32, .u128 => .u128
  | .u64, .i8 => .u64 | .u64, .i16 => .u64 | .u64, .i32 => .u64 | .u64, .i64 => .u64 | .u64, .i128 => .u128 | .u64, .u8 => .u64 | .u64, .u16 => .u64 | .u64, .u32 => .u64 | .u64, .u64 => .u64 | .u64, .u128 => .u128
  | .u128, .i8 => .u128 | .u128, .i16 => .u128 | .u128, .i32 => .u128 | .u128, .i64 => .u128 | .u128, .i128 => .u128 | .u128, .u8 => .u128 | .u128, .u16 => .u128 | .u128, .u32 => .u128 | .u128, .u64 => .u128 | .u128, .u128 => .u128

theorem remTyR_eq (s t : IntTy) : remTyR s t = remTy s t := by cases s <;> cases t <;> rfl
/-- `rem(x::S, y::T)` for BitIntegers of different types: `promote` for equal signedness
(`promotion.jl`), else `base/int.jl:278` or `base/int.jl:279`. -/
instance (priority := low) : JRem (JInt s) (JInt t) (JInt (remTyR s t)) := ⟨fun x y =>
  if s.signed = t.signed then liftJl ((remPromoted x y).map (remT _))
  else if s.signed then
    liftJl ((JuliaLean.base.int.rem_BitSigned_Unsigned remPromoted x y).map (remT _))
  else liftJl ((JuliaLean.base.int.rem_Unsigned_BitSigned remPromoted x y).map (remT _))⟩

/-- `mod(x::T, y::T)` of one BitInteger type (`base/int.jl:331-351`). -/
def modSame {r : IntTy} (x y : JInt r) : Jl (JInt r) :=
  if r.signed then mod_BitSigned JInt.fld x y else mod_Unsigned x y
/-- Result type of `mod(x::S, y::T)` for BitIntegers (`base/int.jl:281-298`). -/
abbrev modTy (s t : IntTy) : IntTy :=
  if s.signed = t.signed then s.promote t
  else if s.signed then ((s.toUnsigned.promote t).toSigned.promote t).toUnsigned
  else (s.promote t.toUnsigned).toSigned.promote t
/-- the result type `modTy` of `mod(x::S, y::T)`, as a reducible table. -/
abbrev modTyR : IntTy → IntTy → IntTy
  | .i8, .i8 => .i8 | .i8, .i16 => .i16 | .i8, .i32 => .i32 | .i8, .i64 => .i64 | .i8, .i128 => .i128 | .i8, .u8 => .u8 | .i8, .u16 => .u16 | .i8, .u32 => .u32 | .i8, .u64 => .u64 | .i8, .u128 => .u128
  | .i16, .i8 => .i16 | .i16, .i16 => .i16 | .i16, .i32 => .i32 | .i16, .i64 => .i64 | .i16, .i128 => .i128 | .i16, .u8 => .u16 | .i16, .u16 => .u16 | .i16, .u32 => .u32 | .i16, .u64 => .u64 | .i16, .u128 => .u128
  | .i32, .i8 => .i32 | .i32, .i16 => .i32 | .i32, .i32 => .i32 | .i32, .i64 => .i64 | .i32, .i128 => .i128 | .i32, .u8 => .u32 | .i32, .u16 => .u32 | .i32, .u32 => .u32 | .i32, .u64 => .u64 | .i32, .u128 => .u128
  | .i64, .i8 => .i64 | .i64, .i16 => .i64 | .i64, .i32 => .i64 | .i64, .i64 => .i64 | .i64, .i128 => .i128 | .i64, .u8 => .u64 | .i64, .u16 => .u64 | .i64, .u32 => .u64 | .i64, .u64 => .u64 | .i64, .u128 => .u128
  | .i128, .i8 => .i128 | .i128, .i16 => .i128 | .i128, .i32 => .i128 | .i128, .i64 => .i128 | .i128, .i128 => .i128 | .i128, .u8 => .u128 | .i128, .u16 => .u128 | .i128, .u32 => .u128 | .i128, .u64 => .u128 | .i128, .u128 => .u128
  | .u8, .i8 => .i8 | .u8, .i16 => .i16 | .u8, .i32 => .i32 | .u8, .i64 => .i64 | .u8, .i128 => .i128 | .u8, .u8 => .u8 | .u8, .u16 => .u16 | .u8, .u32 => .u32 | .u8, .u64 => .u64 | .u8, .u128 => .u128
  | .u16, .i8 => .i16 | .u16, .i16 => .i16 | .u16, .i32 => .i32 | .u16, .i64 => .i64 | .u16, .i128 => .i128 | .u16, .u8 => .u16 | .u16, .u16 => .u16 | .u16, .u32 => .u32 | .u16, .u64 => .u64 | .u16, .u128 => .u128
  | .u32, .i8 => .i32 | .u32, .i16 => .i32 | .u32, .i32 => .i32 | .u32, .i64 => .i64 | .u32, .i128 => .i128 | .u32, .u8 => .u32 | .u32, .u16 => .u32 | .u32, .u32 => .u32 | .u32, .u64 => .u64 | .u32, .u128 => .u128
  | .u64, .i8 => .i64 | .u64, .i16 => .i64 | .u64, .i32 => .i64 | .u64, .i64 => .i64 | .u64, .i128 => .i128 | .u64, .u8 => .u64 | .u64, .u16 => .u64 | .u64, .u32 => .u64 | .u64, .u64 => .u64 | .u64, .u128 => .u128
  | .u128, .i8 => .i128 | .u128, .i16 => .i128 | .u128, .i32 => .i128 | .u128, .i64 => .i128 | .u128, .i128 => .i128 | .u128, .u8 => .u128 | .u128, .u16 => .u128 | .u128, .u32 => .u128 | .u128, .u64 => .u128 | .u128, .u128 => .u128

theorem modTyR_eq (s t : IntTy) : modTyR s t = modTy s t := by cases s <;> cases t <;> rfl
/-- `mod(x::S, y::T)` for BitIntegers of different types: `promote` for equal signedness, else the
mixed-signedness methods of `base/int.jl:281-298`. -/
instance (priority := low) : JMod (JInt s) (JInt t) (JInt (modTyR s t)) := ⟨fun x y =>
  if s.signed = t.signed then liftJl ((modSame (remT (s.promote t) x) (remT _ y)).map (remT _))
  else if s.signed then
    liftJl ((JuliaLean.base.int.mod_BitSigned_Unsigned remPromoted x y).map (remT _))
  else liftJl ((JuliaLean.base.int.mod_Unsigned_Signed remPromoted x y).map (remT _))⟩

/-- Unary plus, `+(x::Number) = x` (`operators.jl`). -/
instance : JPos (JInt t) (JInt t) := ⟨id⟩
/-- `negate(x) = -x` (`base/int.jl:96`) for signed `T`; `negate(x::Unsigned) =
-convert(Signed, x)` (`base/int.jl:97`) for unsigned `T`. -/
instance : JNegate (JInt t) (JInt (sTy t)) := ⟨fun x =>
  if t.signed then pure (remT _ (neg x))
  else liftJl ((JuliaLean.base.int.negate_Unsigned x).map (castJ (sTy_eq t).symm))⟩

/-- `widen(T)` of a BitInteger type of at most 64 bits (`base/int.jl:906-919`). -/
def widenTy : IntTy → IntTy
  | .i8 => .i16 | .i16 => .i32 | .i32 => .i64 | .i64 => .i128
  | .u8 => .u16 | .u16 => .u32 | .u32 => .u64 | .u64 => .u128 | t => t
/-- Result type of `widemul(x::S, y::T)` (`number.jl:327`, `base/int.jl:923-924`). -/
def wideTy (s t : IntTy) : IntTy :=
  if s.signed = t.signed then (widenTy s).promote (widenTy t)
  else if s.signed then (widenTy s).promote (widenTy t).toSigned
  else (widenTy s).toSigned.promote (widenTy t)
/-- the result type `wideTy` of `widemul(x::S, y::T)`, as a reducible table. -/
abbrev wideTyR : IntTy → IntTy → IntTy
  | .i8, .i8 => .i16 | .i8, .i16 => .i32 | .i8, .i32 => .i64 | .i8, .i64 => .i128 | .i8, .i128 => .i128 | .i8, .u8 => .i16 | .i8, .u16 => .i32 | .i8, .u32 => .i64 | .i8, .u64 => .i128 | .i8, .u128 => .i128
  | .i16, .i8 => .i32 | .i16, .i16 => .i32 | .i16, .i32 => .i64 | .i16, .i64 => .i128 | .i16, .i128 => .i128 | .i16, .u8 => .i32 | .i16, .u16 => .i32 | .i16, .u32 => .i64 | .i16, .u64 => .i128 | .i16, .u128 => .i128
  | .i32, .i8 => .i64 | .i32, .i16 => .i64 | .i32, .i32 => .i64 | .i32, .i64 => .i128 | .i32, .i128 => .i128 | .i32, .u8 => .i64 | .i32, .u16 => .i64 | .i32, .u32 => .i64 | .i32, .u64 => .i128 | .i32, .u128 => .i128
  | .i64, .i8 => .i128 | .i64, .i16 => .i128 | .i64, .i32 => .i128 | .i64, .i64 => .i128 | .i64, .i128 => .i128 | .i64, .u8 => .i128 | .i64, .u16 => .i128 | .i64, .u32 => .i128 | .i64, .u64 => .i128 | .i64, .u128 => .i128
  | .i128, .i8 => .i128 | .i128, .i16 => .i128 | .i128, .i32 => .i128 | .i128, .i64 => .i128 | .i128, .i128 => .i128 | .i128, .u8 => .i128 | .i128, .u16 => .i128 | .i128, .u32 => .i128 | .i128, .u64 => .i128 | .i128, .u128 => .i128
  | .u8, .i8 => .i16 | .u8, .i16 => .i32 | .u8, .i32 => .i64 | .u8, .i64 => .i128 | .u8, .i128 => .i128 | .u8, .u8 => .u16 | .u8, .u16 => .u32 | .u8, .u32 => .u64 | .u8, .u64 => .u128 | .u8, .u128 => .u128
  | .u16, .i8 => .i32 | .u16, .i16 => .i32 | .u16, .i32 => .i64 | .u16, .i64 => .i128 | .u16, .i128 => .i128 | .u16, .u8 => .u32 | .u16, .u16 => .u32 | .u16, .u32 => .u64 | .u16, .u64 => .u128 | .u16, .u128 => .u128
  | .u32, .i8 => .i64 | .u32, .i16 => .i64 | .u32, .i32 => .i64 | .u32, .i64 => .i128 | .u32, .i128 => .i128 | .u32, .u8 => .u64 | .u32, .u16 => .u64 | .u32, .u32 => .u64 | .u32, .u64 => .u128 | .u32, .u128 => .u128
  | .u64, .i8 => .i128 | .u64, .i16 => .i128 | .u64, .i32 => .i128 | .u64, .i64 => .i128 | .u64, .i128 => .i128 | .u64, .u8 => .u128 | .u64, .u16 => .u128 | .u64, .u32 => .u128 | .u64, .u64 => .u128 | .u64, .u128 => .u128
  | .u128, .i8 => .i128 | .u128, .i16 => .i128 | .u128, .i32 => .i128 | .u128, .i64 => .i128 | .u128, .i128 => .i128 | .u128, .u8 => .u128 | .u128, .u16 => .u128 | .u128, .u32 => .u128 | .u128, .u64 => .u128 | .u128, .u128 => .u128

theorem wideTyR_eq (s t : IntTy) : wideTyR s t = wideTy s t := by cases s <;> cases t <;> rfl
/-- `widemul(x, y)` of two `BitInteger64` values: `widen(x)*widen(y)` (`number.jl:327`) for equal
signedness, else `base/int.jl:923` or `924`; `widen(x)` converts to `widen(T)`. -/
instance : JWidemul (JInt s) (JInt t) (JInt (wideTyR s t)) := ⟨fun x y =>
  if s.signed = t.signed then
    remT _ (binop mulSame (JuliaLean.base.int.widenTo (widenTy s) x)
      (JuliaLean.base.int.widenTo (widenTy t) y))
  else if s.signed then
    remT _ (JuliaLean.base.int.widemul_Signed_Unsigned (JuliaLean.base.int.widenTo (widenTy s))
      (JuliaLean.base.int.widenTo (widenTy t)) x y)
  else
    remT _ (JuliaLean.base.int.widemul_Unsigned_Signed (JuliaLean.base.int.widenTo (widenTy s))
      (JuliaLean.base.int.widenTo (widenTy t)) x y)⟩

/-- `throw_boundserror(A, I)`. -/
instance {R I : Type} : JThrowBoundserror R I := ⟨fun _ _ => throw (.jl .boundsError)⟩


end MixedScalars

/-! ## Dispatch world: integer ranges with two element types

`StepRange{T,S}` with a step type `S` other than `T` (built by `StepRange(start, step, stop)`),
and the methods that take ranges and indices of other BitInteger types. -/

section MixedRanges

variable {s t u : IntTy}

instance (priority := low) : JEltype (StepRange (JInt t) (JInt s)) (JInt t) := ⟨⟩
instance (priority := low) : JFieldStart (StepRange (JInt t) (JInt s)) (JInt t) := ⟨StepRange.start⟩
instance (priority := low) : JFieldStop (StepRange (JInt t) (JInt s)) (JInt t) := ⟨StepRange.stop⟩
/-- `steprange_last_empty(start::Integer, step, stop)`, range.jl:389. -/
instance (priority := low) : JSteprangeLastEmpty (JInt t) (JInt s) (JInt t) :=
  ⟨steprange_last_empty_Integer⟩
/-- `steprange_last(start, step, stop)`, range.jl:353. -/
instance (priority := low) : JSteprangeLast (JInt t) (JInt s) (JInt t) := ⟨steprange_last⟩
/-- `StepRange{T,S}(start, step, stop)`, range.jl:344. -/
instance (priority := low) {a b c : IntTy} :
    JStepRangeTS (JInt t) (JInt s) (JInt a) (JInt b) (JInt c) := ⟨StepRange_TS_new (JInt t) (JInt s)⟩
/-- `StepRange(start::T, step::S, stop::T)`, range.jl:404. -/
instance (priority := low) : JStepRange3 (JInt t) (JInt s) (JInt t) (StepRange (JInt t) (JInt s)) :=
  ⟨StepRange_T_S_T⟩
/-- `StepRange{T}(start, step::S, stop)`, range.jl:403. -/
instance {a c : IntTy} : JStepRangeT (JInt t) (JInt a) (JInt s) (JInt c) (StepRange (JInt t) (JInt s)) :=
  ⟨StepRange_T⟩
/-- `(:)(start::T, step, stop::T) where {T<:Real}`, range.jl:65, for a step of another type. -/
instance (priority := low) : JColon3 (JInt t) (JInt s) (JInt t)
    (StepRange (JInt (pTy t s)) (JInt s)) := ⟨colon_T_step_T_Real⟩
/-- `first(r::OrdinalRange{T})`, range.jl:867. -/
instance (priority := low) : JFirst (StepRange (JInt t) (JInt s)) (JInt t) := ⟨first_OrdinalRange⟩
/-- `last(r::OrdinalRange{T})`, range.jl:877. -/
instance (priority := low) : JLast (StepRange (JInt t) (JInt s)) (JInt t) := ⟨last_OrdinalRange⟩
/-- `step(r::StepRange)`, range.jl:735. -/
instance (priority := low) : JStep (StepRange (JInt t) (JInt s)) (JInt s) :=
  ⟨fun r => pure (step_StepRange r)⟩
/-- `step_hp(r::AbstractRange)`, range.jl:744. -/
instance (priority := low) : JStepHp (StepRange (JInt t) (JInt s)) (JInt s) := ⟨step_hp_AbstractRange⟩
/-- `isempty(r::StepRange)`, range.jl:708. -/
instance (priority := low) : JIsempty (StepRange (JInt t) (JInt s)) :=
  ⟨fun r => pure (isempty_StepRange r)⟩
/-- `iterate(r::OrdinalRange)`, range.jl:935. -/
instance (priority := low) : JIterate1 (StepRange (JInt t) (JInt s)) (JInt t) (JInt t) :=
  ⟨iterate_OrdinalRange⟩
/-- `iterate(r::OrdinalRange{T}, i)`, range.jl:937. -/
instance (priority := low) : JIterate2 (StepRange (JInt t) (JInt s)) (JInt t) (JInt t) :=
  ⟨iterate_OrdinalRange_state⟩

end MixedRanges

/-- `length(r::OrdinalRange{<:smallints})` (range.jl:853) or
`length(r::OrdinalRange{T}) where T<:bigints` (range.jl:820), for any BitInteger step type. -/
def lengthStepMixed : {t s : IntTy} → StepRange (JInt t) (JInt s) → JlX (JInt (lenTy t))
  | .i8, _, r => length_OrdinalRange_smallints r
  | .i16, _, r => length_OrdinalRange_smallints r
  | .i32, _, r => length_OrdinalRange_smallints r
  | .u8, _, r => length_OrdinalRange_smallints r
  | .u16, _, r => length_OrdinalRange_smallints r
  | .u32, _, r => length_OrdinalRange_smallints r
  | .i64, _, r => length_OrdinalRange_bigints r
  | .u64, _, r => length_OrdinalRange_bigints r
  | .i128, _, r => length_OrdinalRange_bigints r
  | .u128, _, r => length_OrdinalRange_bigints r

instance (priority := low) {t s : IntTy} : JLength (StepRange (JInt t) (JInt s)) (JInt (lenTy t)) :=
  ⟨lengthStepMixed⟩

/-- `checked_length(r::AbstractUnitRange{<:smallints})` (range.jl:862) or
`checked_length(r::AbstractUnitRange{T})` (range.jl:768), whose two branches have one type. -/
def checkedLengthUnit : {t : IntTy} → UnitRange (JInt t) → JlX (JInt (lenTy t))
  | .i8, r => checked_length_AbstractUnitRange_smallints r
  | .i16, r => checked_length_AbstractUnitRange_smallints r
  | .i32, r => checked_length_AbstractUnitRange_smallints r
  | .u8, r => checked_length_AbstractUnitRange_smallints r
  | .u16, r => checked_length_AbstractUnitRange_smallints r
  | .u32, r => checked_length_AbstractUnitRange_smallints r
  | .i64, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)
  | .u64, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)
  | .i128, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)
  | .u128, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)

/-- `checked_length(r::OrdinalRange{<:smallints})` (range.jl:861) or
`checked_length(r::OrdinalRange{T}) where T<:bigints` (range.jl:831). -/
def checkedLengthStep : {t : IntTy} → StepRange (JInt t) (JInt t) → JlX (JInt (lenTy t))
  | .i8, r => checked_length_OrdinalRange_smallints r
  | .i16, r => checked_length_OrdinalRange_smallints r
  | .i32, r => checked_length_OrdinalRange_smallints r
  | .u8, r => checked_length_OrdinalRange_smallints r
  | .u16, r => checked_length_OrdinalRange_smallints r
  | .u32, r => checked_length_OrdinalRange_smallints r
  | .i64, r => checked_length_OrdinalRange_bigints r
  | .u64, r => checked_length_OrdinalRange_bigints r
  | .i128, r => checked_length_OrdinalRange_bigints r
  | .u128, r => checked_length_OrdinalRange_bigints r

/-- `checked_length(r::OneTo{<:smallints})` (range.jl:863) or
`checked_length(r::AbstractUnitRange{T})` (range.jl:768). -/
def checkedLengthOneTo : {t : IntTy} → OneTo (JInt t) → JlX (JInt (lenTy t))
  | .i8, r => checked_length_OneTo_smallints r
  | .i16, r => checked_length_OneTo_smallints r
  | .i32, r => checked_length_OneTo_smallints r
  | .u8, r => checked_length_OneTo_smallints r
  | .u16, r => checked_length_OneTo_smallints r
  | .u32, r => checked_length_OneTo_smallints r
  | .i64, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)
  | .u64, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)
  | .i128, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)
  | .u128, r => (checked_length_AbstractUnitRange r).map (Sum.elim id id)

instance {t : IntTy} : JCheckedLength (UnitRange (JInt t)) (JInt (lenTy t)) := ⟨checkedLengthUnit⟩
instance {t : IntTy} : JCheckedLength (StepRange (JInt t) (JInt t)) (JInt (lenTy t)) :=
  ⟨checkedLengthStep⟩
instance {t : IntTy} : JCheckedLength (OneTo (JInt t)) (JInt (lenTy t)) := ⟨checkedLengthOneTo⟩

/-! ### Indices -/

section Indices

variable {s t u : IntTy}

/-- `firstindex(a::AbstractArray)` (abstractarray.jl:452): `first(axes1(a))`, the `1` of the
length type. -/
instance : JFirstindex (UnitRange (JInt t)) (JInt (lenTy t)) := ⟨fun _ => pure (lit _ 1)⟩
instance : JFirstindex (OneTo (JInt t)) (JInt (lenTy t)) := ⟨fun _ => pure (lit _ 1)⟩
/-- `lastindex(a::AbstractArray)` (abstractarray.jl:429): `last(axes1(a))`, the length. -/
instance : JLastindex (UnitRange (JInt t)) (JInt (lenTy t)) := ⟨JLength.length⟩
instance : JLastindex (OneTo (JInt t)) (JInt (lenTy t)) := ⟨JLength.length⟩
instance (priority := low) : JLastindex (StepRange (JInt t) (JInt s)) (JInt (lenTy t)) :=
  ⟨JLength.length⟩

/-- `firstindex(::StepRange{<:smallints,<:bitints}) = 1` (range.jl:864) or
`firstindex(r::StepRange{<:bigints,<:bitints})` (range.jl:850). -/
def firstindexStep : {t s : IntTy} → StepRange (JInt t) (JInt s) → JlX (JInt (lenTy t))
  | .i8, _, r => pure (firstindex_StepRange_smallints r)
  | .i16, _, r => pure (firstindex_StepRange_smallints r)
  | .i32, _, r => pure (firstindex_StepRange_smallints r)
  | .u8, _, r => pure (firstindex_StepRange_smallints r)
  | .u16, _, r => pure (firstindex_StepRange_smallints r)
  | .u32, _, r => pure (firstindex_StepRange_smallints r)
  | .i64, _, r => firstindex_StepRange_bigints r
  | .u64, _, r => firstindex_StepRange_bigints r
  | .i128, _, r => firstindex_StepRange_bigints r
  | .u128, _, r => firstindex_StepRange_bigints r

instance : JFirstindex (StepRange (JInt t) (JInt s)) (JInt (lenTy t)) := ⟨firstindexStep⟩

/-- Specification of `checkbounds(v, i)` for a vector `v` with a nonnegative length: the valid
indices are `1:length(v)`, others throw `BoundsError` (checkbounds docstring, abstractarray.jl:696:
"Throw an error if the specified indices `I` are not in bounds for the given array `A`").
`checkboundsVector_eq` proves that the model `checkboundsVector` meets it. -/
def checkboundsLinear {R : Type} {L : IntTy} [JLength R (JInt L)] {s : IntTy} (r : R) (i : JInt s) :
    JlX Unit := do
  let n ← JLength.length r
  if 1 ≤ i.val ∧ i.val ≤ n.val then pure () else throw (.jl .boundsError)

/-- A range-file computation as an `abstractarray.jl` computation (`ArrayError.julia` carries the
same `JlError`). -/
def toArr {α : Type} (x : JlX α) : JuliaLean.base.abstractarray.Result α :=
  match x with
  | .ok v => .ok v
  | .error (.jl e) => .error (.julia e)
  | .error (.errorException m) => .error (.errorException m)
  | .error (.dimensionMismatch m) => .error (.dimensionMismatch m)
  | .error .inboundsViolation => .error (.errorException "inbounds violation")

/-- An `abstractarray.jl` computation as a range-file computation. -/
def ofArr {α : Type} (x : JuliaLean.base.abstractarray.Result α) : JlX α :=
  match x with
  | .ok v => .ok v
  | .error (.julia e) => .error (.jl e)
  | .error (.dimensionMismatch m) => .error (.dimensionMismatch m)
  | .error (.errorException m) => .error (.errorException m)
  | .error _ => .error (.errorException "abstractarray.jl error")

/-- `checkindex(Bool, inds, i)` for the axis `inds = OneTo(n)` of a range and an integer index:
`checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger}` (abstractarray.jl:753,
`checkindexOneTo`) when the index has the axis type, else
`checkindex(::Type{Bool}, inds::AbstractUnitRange, i::Real)` (abstractarray.jl:751,
`checkindexReal`) with `first(r::OneTo)` (range.jl:868), `last(r::OrdinalRange)` (range.jl:877)
and `<=` of `base/int.jl`. -/
def checkindexAxis {L s : IntTy} (inds : OneTo (JInt L)) (i : JInt s) :
    JuliaLean.base.abstractarray.Result Bool :=
  if h : s = L then
    pure (JuliaLean.base.abstractarray.checkindexOneTo inds.stop (castJ h i))
  else
    JuliaLean.base.abstractarray.checkindexReal (fun r => toArr (JFirst.first r))
      (fun r => toArr (JLast.last r)) (fun a b => pure (JLe.le a b)) (fun a b => pure (JLe.le a b)) inds i

/-- `checkbounds(A, i)` of a range `A` and an integer index `i`: `checkbounds(A::AbstractArray,
I...)` (essentials.jl:389) is `checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)`;
`checkbounds(::Type{Bool}, A::AbstractArray, i)` (abstractarray.jl:690, `checkboundsOne`) is
`checkindex(Bool, eachindex(IndexLinear(), A), i)` with `eachindex(::IndexLinear,
A::AbstractVector) = axes1(A)` (abstractarray.jl:396, `eachindexLinearVector`),
`axes1(A) = axes(A)[1]` (abstractarray.jl:141, `axes1`) and `axes(A) = map(unchecked_oneto,
size(A))` (abstractarray.jl:100) of `size(r::AbstractRange) = (length(r),)` (range.jl:706,
`size_AbstractRange`) and `unchecked_oneto` (range.jl:503); `checkindex` is `checkindexAxis`.
(`axesDefault` of abstractarray.lean fixes the sizes to `Int`, while a range's `length` may be an
`UInt64` or `Int128`, so `axes` is applied here at the length type.) -/
def checkboundsVector {R : Type} {L : IntTy} [JLength R (JInt L)] {s : IntTy} (r : R) (i : JInt s) :
    JlX Unit := do
  let ok ← ofArr (JuliaLean.base.abstractarray.checkboundsOne
    (JuliaLean.base.abstractarray.eachindexLinearVector
      (JuliaLean.base.abstractarray.axes1 (fun a => toArr (do
        let sz ← size_AbstractRange a
        return [unchecked_oneto sz._1]))))
    checkindexAxis r i)
  if ok then pure () else do
    let e ← JThrowBoundserror.throwBoundserror r (Tuple1.mk i)
    nomatch e

instance : JCheckbounds (UnitRange (JInt t)) (JInt s) := ⟨checkboundsVector⟩
instance : JCheckbounds (OneTo (JInt t)) (JInt s) := ⟨checkboundsVector⟩

/-- `checkbounds(v, i)` for a `StepRange`: range.jl:975 when the element, step and index types are
`BitInteger64`, else `1 <= i <= length(v)` (abstractarray.jl:690). -/
def checkboundsStep {t s u : IntTy} (v : StepRange (JInt t) (JInt s)) (i : JInt u) : JlX Unit := do
  if t.bits ≤ 64 ∧ s.bits ≤ 64 ∧ u.bits ≤ 64 then
    if ← checkbounds_Bool_StepRange_BitInteger64 v i then pure () else throw (.jl .boundsError)
  else checkboundsVector v i

instance : JCheckbounds (StepRange (JInt t) (JInt s)) (JInt u) := ⟨checkboundsStep⟩

/-- `unsafe_getindex(v::OneTo{T}, i::Integer)`, range.jl:984. -/
instance : JUnsafeGetindex (OneTo (JInt t)) (JInt s) (JInt t) := ⟨unsafe_getindex_OneTo⟩
/-- `unsafe_getindex(v::AbstractRange{T}, i::Integer)`, range.jl:985. -/
instance : JUnsafeGetindex (UnitRange (JInt t)) (JInt s) (JInt t) := ⟨unsafe_getindex_AbstractRange⟩
instance : JUnsafeGetindex (StepRange (JInt t) (JInt u)) (JInt s) (JInt t) :=
  ⟨unsafe_getindex_AbstractRange⟩

/-- `getindex(v::AbstractRange, i::Integer)` (array.jl:3219-3225): a BitInteger index is not a
`Bool`, so this is `_getindex(v, i)`, which for `UnitRange{<:OverflowSafe}` is range.jl:968. -/
instance : JGetindex (UnitRange (JInt t)) (JInt s) (JInt t) := ⟨_getindex_UnitRange_OverflowSafe⟩
/-- `getindex(v::AbstractRange, i::Integer)` (array.jl:3219): `_getindex(v, i)`, range.jl:952. -/
instance : JGetindex (StepRange (JInt t) (JInt u)) (JInt s) (JInt t) := ⟨_getindex_AbstractRange⟩
instance : JGetindex (OneTo (JInt t)) (JInt s) (JInt t) := ⟨_getindex_AbstractRange⟩

end Indices

end JuliaLean.Proofs.base.range

namespace JuliaLean.Proofs.base.range

open JuliaLean JuliaLean.base.range JuliaLean.Registry
open JuliaLean.base.int (add sub mul neg mulSame addWrap subWrap mulWrap lt le eq remT unsigned
  flipsign jmin jmax minType divSame remSame binop lit)

/-! ## Evaluation lemmas: integer scalars

Each lemma evaluates one world instance to `Int` arithmetic (`wrapInt t z` is `z` reduced into
`t`'s range, `JuliaLean.Core`). -/

section IntEval

variable {s t : IntTy}

theorem min_le_zero (t : IntTy) : t.min ≤ 0 := by cases t <;> decide
theorem zero_lt_max (t : IntTy) : 1 ≤ t.max := by cases t <;> decide

theorem wrap_in (t : IntTy) {z : Int} (h1 : t.min ≤ z) (h2 : z ≤ t.max) : wrapInt t z = z :=
  wrapInt_of_inRange t z ⟨h1, h2⟩

@[simp] theorem eq_iv (x : JInt s) (y : JInt t) : JEq.eq x y = decide (x.val = y.val) :=
  IntVal.eq_eq x y
@[simp] theorem lt_iv (x : JInt s) (y : JInt t) : JLt.lt x y = decide (x.val < y.val) :=
  IntVal.lt_eq x y
@[simp] theorem le_iv (x : JInt s) (y : JInt t) : JLe.le x y = decide (x.val ≤ y.val) :=
  IntVal.le_eq x y
@[simp] theorem isless_iv (x : JInt s) (y : JInt t) : JIsless.isless x y = decide (x.val < y.val) :=
  IntVal.lt_eq x y
@[simp] theorem zero_iv : (JZero.zero : JInt t).val = 0 := by
  show wrapInt t 0 = 0
  exact wrap_in t (min_le_zero t) (by have := zero_lt_max t; omega)
@[simp] theorem oneunit_iv : (JOneunit.oneunit : JInt t).val = 1 := by
  show wrapInt t 1 = 1
  exact wrap_in t (by have := min_le_zero t; omega) (zero_lt_max t)
@[simp] theorem one_iv : (JOne.one : JInt t).val = 1 := by
  show wrapInt t 1 = 1
  exact wrap_in t (by have := min_le_zero t; omega) (zero_lt_max t)
@[simp] theorem add_iv (x y : JInt t) : (x + y).val = wrapInt t (x.val + y.val) :=
  IntVal.add_int_val x y
@[simp] theorem sub_iv (x y : JInt t) : (x - y).val = wrapInt t (x.val - y.val) :=
  IntVal.sub_int_val x y
@[simp] theorem mul_iv (x y : JInt t) : (x * y).val = wrapInt t (x.val * y.val) := by
  show (mulSame x y).val = _
  cases t <;> exact IntVal.mul_int_val x y
@[simp] theorem neg_iv (x : JInt t) : (JNeg.neg x).val = wrapInt t (-x.val) :=
  IntVal.neg_int_val x
@[simp] theorem wrappingSub_iv (x y : JInt t) :
    (JRangeWrappingSub.rangeWrappingSub x y : JInt t).val = wrapInt t (x.val - y.val) :=
  IntVal.sub_int_val x y
@[simp] theorem wrappingAdd_iv (x y : JInt t) :
    (JRangeWrappingAdd.rangeWrappingAdd x y : JInt t).val = wrapInt t (x.val + y.val) :=
  IntVal.add_int_val x y
@[simp] theorem wrappingSub'_iv (x y : JInt t) :
    (JWrappingSub.wrappingSub x y : JInt t).val = wrapInt t (x.val - y.val) :=
  IntVal.sub_int_val x y
@[simp] theorem remType_iv (x : JInt s) : (JRemType.remType x : JInt t).val = wrapInt t x.val :=
  IntVal.remT_val t x

theorem convert_iv (x : JInt s) : (JConvert.convert x : JlX (JInt t)) =
    if h : t.min ≤ x.val ∧ x.val ≤ t.max then .ok ⟨x.val, h⟩
    else .error (.jl (.inexactError t.name)) := by
  show liftJl (JInt.convert t x.val) = _
  unfold JInt.convert
  split <;> rfl

@[simp] theorem convert_self (x : JInt t) : (JConvert.convert x : JlX (JInt t)) = .ok x := by
  rw [convert_iv, dif_pos x.property]

theorem ctor_iv (x : JInt s) : (JCtor.ctor x : JlX (JInt t)) = JConvert.convert x := rfl

theorem convert_ok {x : JInt s} (h1 : t.min ≤ x.val) (h2 : x.val ≤ t.max) :
    (JConvert.convert x : JlX (JInt t)) = .ok ⟨x.val, h1, h2⟩ := by
  rw [convert_iv, dif_pos ⟨h1, h2⟩]

end IntEval

/-! ## Specification vocabulary -/

/-- The integers `a, a+1, ..., b` (empty when `b < a`). -/
def intsFromTo (a b : Int) : List Int :=
  (List.range (b - a + 1).toNat).map fun (k : Nat) => a + (k : Int)

/-- The elements a `for` loop visits after state `st`, calling `iterate(r, st)` at most `fuel`
times. -/
def iterFrom {R S T : Type} [JIterate2 R S T] (r : R) : Nat → S → JlX (List T)
  | 0, _ => throw (.errorException "fuel")
  | n + 1, st => do
    match ← JIterate2.iterate r st with
    | none => pure []
    | some (x, st') => return x :: (← iterFrom r n st')

/-- The elements a `for x in r` loop visits through Julia's iteration protocol
(`iterate(r)`, then `iterate(r, state)` until `nothing`), with at most `fuel` calls of
`iterate(r, state)`. -/
def iterList {R S T : Type} [JIterate1 R T S] [JIterate2 R S T] (r : R) (fuel : Nat) :
    JlX (List T) := do
  match ← JIterate1.iterate r with
  | none => pure []
  | some (x, st) => return x :: (← iterFrom r fuel st)

/-- The values of a list of integers. -/
abbrev vals {t : IntTy} (l : List (JInt t)) : List Int := l.map Subtype.val

theorem intsFromTo_empty {a b : Int} (h : b < a) : intsFromTo a b = [] := by
  simp [intsFromTo, show (b - a + 1).toNat = 0 by omega]

theorem intsFromTo_cons {a b : Int} (h : a ≤ b) : intsFromTo a b = a :: intsFromTo (a + 1) b := by
  unfold intsFromTo
  rw [show (b - a + 1).toNat = (b - (a + 1) + 1).toNat + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1
  · omega
  · apply List.map_congr_left; intro k _; simp; omega

theorem intsFromTo_length (a b : Int) : (intsFromTo a b).length = (b - a + 1).toNat := by
  simp [intsFromTo]

/-! ## Evaluation lemmas: unit ranges of integers -/

section UnitEval

variable {t : IntTy}

/-- The stop that `a:b` stores: `b`, or `a - 1` when `b < a`. -/
def unitStop (a b : JInt t) : JInt t :=
  if h : a.val ≤ b.val then b
  else ⟨a.val - 1, by have := a.property; have := b.property; omega,
    by have := a.property; omega⟩

theorem colon_unit (a b : JInt t) : JColon2.colon a b = .ok ⟨a, unitStop a b⟩ := by
  simp only [JColon2.colon, colon_T_T_Real, JUnitRangeT.unitRangeT, UnitRange_T_new,
    JUnitrangeLast.unitrangeLast, unitrange_last_Integer, le_iv, unitStop]
  by_cases h : a.val ≤ b.val
  · simp [h, pure, Except.pure, bind, Except.bind]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, dite_false, convert_self]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, UnitRange.mk.injEq, true_and]
    apply Subtype.ext
    simp only [wrappingSub_iv, oneunit_iv]
    have := a.property; have := b.property
    exact wrap_in t (by omega) (by omega)

@[simp] theorem first_unit (r : UnitRange (JInt t)) : JFirst.first r = .ok r.start := by
  simp [JFirst.first, first_OrdinalRange, JFieldStart.start]
@[simp] theorem last_unit (r : UnitRange (JInt t)) : JLast.last r = .ok r.stop := by
  simp [JLast.last, last_OrdinalRange, JFieldStop.stop]
@[simp] theorem isempty_unit (r : UnitRange (JInt t)) :
    JIsempty.isempty r = .ok (decide (r.stop.val < r.start.val)) := by
  simp [JIsempty.isempty, isempty_AbstractUnitRange, bind, Except.bind, pure, Except.pure]
theorem step_unit (r : UnitRange (JInt t)) : ∃ s : JInt t, JStep.step r = .ok s ∧ s.val = 1 :=
  ⟨_, rfl, by
    simp [step_AbstractUnitRange]; exact wrap_in t (by have := min_le_zero t; omega) (zero_lt_max t)⟩

theorem iterate1_unit (r : UnitRange (JInt t)) : JIterate1.iterate r =
    .ok (if r.stop.val < r.start.val then none else some (r.start, r.start)) := by
  simp only [JIterate1.iterate, iterate_OrdinalRange, isempty_unit, first_unit]
  by_cases h : r.stop.val < r.start.val <;> simp [h, bind, Except.bind, pure, Except.pure]

theorem iterate2_unit (r : UnitRange (JInt t)) (i : JInt t) (hi : i.val < r.stop.val) :
    ∃ j : JInt t, JIterate2.iterate r i = .ok (some (j, j)) ∧ j.val = i.val + 1 := by
  simp only [JIterate2.iterate, iterate_OrdinalRange_state, last_unit, eq_iv]
  simp only [bind, Except.bind, show i.val ≠ r.stop.val by omega, decide_false,
    Bool.false_eq_true, ite_false]
  obtain ⟨s, hs, hs1⟩ := step_unit r
  rw [hs]
  simp only [convert_self, pure, Except.pure]
  refine ⟨i + s, rfl, ?_⟩
  rw [add_iv, hs1]; have := r.stop.property; exact wrap_in t (by have := i.property; omega) (by omega)

theorem iterate2_unit_last (r : UnitRange (JInt t)) (i : JInt t) (hi : i.val = r.stop.val) :
    JIterate2.iterate r i = .ok none := by
  simp [JIterate2.iterate, iterate_OrdinalRange_state, hi, bind, Except.bind, pure, Except.pure]

theorem iterFrom_unit (r : UnitRange (JInt t)) : ∀ (fuel : Nat) (i : JInt t),
    i.val ≤ r.stop.val → (r.stop.val - i.val).toNat < fuel →
    (iterFrom r fuel i).map vals = .ok (intsFromTo (i.val + 1) r.stop.val)
  | 0, _, _, h => by omega
  | fuel + 1, i, hle, hf => by
    by_cases heq : i.val = r.stop.val
    · simp [iterFrom, iterate2_unit_last r i heq, bind, Except.bind, pure, Except.pure,
        Except.map, intsFromTo_empty (show r.stop.val < i.val + 1 by omega)]
    · have hlt : i.val < r.stop.val := by omega
      obtain ⟨j, hj, hjv⟩ := iterate2_unit r i hlt
      have ih := iterFrom_unit r fuel j (by omega) (by omega)
      rw [hjv] at ih
      simp only [iterFrom, hj, bind, Except.bind]
      rw [intsFromTo_cons (show i.val + 1 ≤ r.stop.val by omega)]
      revert ih
      cases iterFrom r fuel j <;> simp [Except.map, pure, Except.pure, hjv]

/-- Iterating a unit range of integers visits exactly the integers from its start to its stop. -/
theorem iterList_unit (r : UnitRange (JInt t)) (fuel : Nat)
    (hf : (r.stop.val - r.start.val).toNat < fuel) :
    (iterList r fuel).map vals = .ok (intsFromTo r.start.val r.stop.val) := by
  unfold iterList
  rw [iterate1_unit]
  by_cases h : r.stop.val < r.start.val
  · simp [h, bind, Except.bind, pure, Except.pure, Except.map, intsFromTo_empty h]
  · have ih := iterFrom_unit r fuel r.start (by omega) hf
    simp only [h, ite_false, bind, Except.bind]
    rw [intsFromTo_cons (show r.start.val ≤ r.stop.val by omega)]
    revert ih
    cases iterFrom r fuel r.start <;> simp [Except.map, pure, Except.pure]

end UnitEval

end JuliaLean.Proofs.base.range

namespace JuliaLean.Proofs.base.range

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-- Equality of computation results, for evaluating concrete counterexamples by `decide`. -/
instance exceptDecEq {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-! ## Dispatch world: integer `StepRangeLen`

`StepRangeLen{T,R,S,Int}` with BitInteger `T`, `R` and `S`, as built by `range(start; length)`
for unsigned `start` (range.jl:225) and by `StepRangeLen(ref, step, len)` (range.jl:550). -/

section SRLInt
variable {q a s w l o : IntTy}

/-- `StepRangeLen{T,R,S,L}(ref, step, len, offset)`, the inner constructor, range.jl:533. -/
instance : JStepRangeLenTRSL (JInt q) (JInt a) (JInt s) (JInt w) (JInt a) (JInt s) (JInt l) (JInt o) :=
  ⟨StepRangeLen_TRSL_new (JInt q)⟩
/-- `StepRangeLen{T,R,S}(ref, step, len, offset)`, range.jl:546. -/
instance : JStepRangeLenTRS (JInt q) (JInt a) (JInt s) (JInt a) (JInt s) (JInt l) (JInt o)
    (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt (pTy .i64 l))) := ⟨StepRangeLen_TRS⟩
/-- `StepRangeLen(ref::R, step::S, len, offset = 1)`, range.jl:548. -/
instance : JStepRangeLen3 (JInt a) (JInt s) (JInt l)
    (StepRangeLen (JInt (pTy a s)) (JInt a) (JInt s) (JInt (pTy .i64 l))) :=
  ⟨fun ref step len => StepRangeLen_ref_step ref step len (jint 1)⟩
instance : JEltype (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt q) := ⟨⟩
/-- `length(r::StepRangeLen) = r.len`, range.jl:807. -/
instance : JLength (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt w) :=
  ⟨fun r => pure (length_StepRangeLen r)⟩
/-- `unsafe_getindex(r::StepRangeLen{T}, i::Integer)`, range.jl:986. -/
instance : JUnsafeGetindex (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt l) (JInt q) :=
  ⟨unsafe_getindex_StepRangeLen⟩
/-- `first(r::StepRangeLen)`, range.jl:869. -/
instance : JFirst (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt q) := ⟨first_StepRangeLen⟩
/-- `last(r::StepRangeLen)`, range.jl:878. -/
instance : JLast (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt q) := ⟨last_StepRangeLen⟩
/-- `isempty(r::StepRangeLen)`, range.jl:712. -/
instance : JIsempty (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) := ⟨isempty_StepRangeLen⟩
/-- `iterate(r::StepRangeLen, i::Integer = zero(length(r)))`, range.jl:928. -/
instance : JIterate1 (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt q) (JInt w) :=
  ⟨fun r => iterate_StepRangeLen_LinRange r (JZero.zero : JInt w)⟩
instance : JIterate2 (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt w) (JInt q) :=
  ⟨iterate_StepRangeLen_LinRange⟩
end SRLInt

/-! ## Dispatch world: keyword `range`

`_range(start, step, stop, length)` dispatches on which arguments are `nothing`. Each instance
forwards to the `_range` method Julia selects; its own callees are resolved where it is used. -/

section RangeKw
variable {t s l u : IntTy}

/-- `range(start; stop, length, step) = _range(start, step, stop, length)`, range.jl:167. -/
instance {α β Λ σ ρ : Type} [JRangeImpl α σ β Λ ρ] : JRangeStartKw α β Λ σ ρ := ⟨range_start_kw⟩
/-- `range(start, stop; length, step)`, range.jl:169. -/
instance {α β Λ σ ρ : Type} [JRangeImpl α σ β Λ ρ] : JRangeStartStopKw α β Λ σ ρ :=
  ⟨range_start_stop_kw⟩
/-- `_range(start::Any, ::Nothing, ::Nothing, len::Integer)`, range.jl:184. -/
instance {D M Q U ρ : Type} [HSub (JInt t) (JInt t) D] [JConvert D JInt64]
    [HSub (JInt l) (JInt l) M] [JRangeWrappingAdd (JInt t) M Q] [JType Q] [JConvert Q (JInt t)]
    [JUnitRange2 Q Q U] [JStepRangeLenTRS Q (JInt t) D (JInt t) D (JInt l) JInt64 ρ] :
    JRangeImpl (JInt t) Nothing Nothing (JInt l) (U ⊕ ρ) := ⟨_range_A_N_N_A⟩
/-- `_range(::Nothing, ::Nothing, stop::Any, len::Integer)`, range.jl:178. -/
instance {D M Q U ρ : Type} [HSub (JInt t) (JInt t) D] [JConvert D JInt64]
    [HSub (JInt l) (JInt l) M] [JRangeWrappingSub (JInt t) M Q] [JType Q] [JConvert Q (JInt t)]
    [JUnitRange2 Q Q U] [JStepRangeLenTRS Q Q D Q D (JInt l) JInt64 ρ] :
    JRangeImpl Nothing Nothing (JInt t) (JInt l) (U ⊕ ρ) := ⟨_range_N_N_A_A⟩
/-- `_range(start::Any, step::Any, ::Nothing, len::Integer)`, range.jl:188. -/
instance {M P Q ρ : Type} [HSub (JInt l) (JInt l) M] [JRangeWrappingMul (JInt s) M P]
    [JRangeWrappingAdd (JInt t) P Q] [JType Q] [JConvert Q (JInt t)]
    [JStepRangeTS Q (JInt s) Q (JInt s) Q] [JStepRangeLenTRS Q (JInt t) (JInt s) (JInt t) (JInt s) (JInt l) JInt64 ρ] :
    JRangeImpl (JInt t) (JInt s) Nothing (JInt l) (StepRange Q (JInt s) ⊕ ρ) := ⟨_range_A_A_N_A⟩
/-- `_range(start::Any, ::Nothing, stop::Any, ::Nothing)`, range.jl:185. -/
instance {ρ : Type} [JColon2 (JInt t) (JInt u) ρ] : JRangeImpl (JInt t) Nothing (JInt u) Nothing ρ :=
  ⟨_range_A_N_A_N⟩
/-- `_range(start::Any, step::Any, stop::Any, ::Nothing)`, range.jl:189. -/
instance {ρ : Type} [JColon3 (JInt t) (JInt s) (JInt u) ρ] :
    JRangeImpl (JInt t) (JInt s) (JInt u) Nothing ρ := ⟨_range_A_A_A_N⟩
/-- `_range(::Nothing, step::Any, ::Nothing, len::Any)`, range.jl:180: always an error. -/
instance : JRangeImpl Nothing (JInt s) Nothing (JInt l) Unit := ⟨_range_N_A_N_A⟩
end RangeKw

/-! ## Dispatch world: range operations -/

section RangeOps
variable {t s u : IntTy}

/-- `first_step_last_ascending(r::StepRange)`, range.jl:1229. -/
instance : JFirstStepLastAscending (StepRange (JInt t) (JInt s)) (JInt t) (JInt s) :=
  ⟨first_step_last_ascending⟩
/-- `UnitRange{T}(start, stop) where {T<:Real}`, range.jl:430, for endpoints of other types. -/
instance (priority := low) : JUnitRangeT (JInt t) (JInt s) (JInt u) := ⟨UnitRange_T⟩
/-- `reverse(r::OrdinalRange)`, range.jl:1445 (`_reverse(r, ::Colon)`). -/
instance {S' ρ : Type} [JNegate (JInt s) S'] [JColon3 (JInt t) S' (JInt t) ρ] :
    JReverse (StepRange (JInt t) (JInt s)) ρ := ⟨fun r => _reverse_OrdinalRange r ⟨⟩⟩
instance {S' ρ : Type} [JNegate (JInt t) S'] [JColon3 (JInt t) S' (JInt t) ρ] :
    JReverse (UnitRange (JInt t)) ρ := ⟨fun r => _reverse_OrdinalRange r ⟨⟩⟩
/-- `intersect(r::AbstractUnitRange{<:Integer}, s::StepRange{<:Integer})`, range.jl:1215. -/
instance : JIntersect (UnitRange (JInt t)) (StepRange (JInt u) (JInt s))
    (StepRange (JInt (pTy t u)) (JInt s)) := ⟨intersect_AbstractUnitRange_StepRange⟩
/-- `intersect(r::StepRange{<:Integer}, s::AbstractUnitRange{<:Integer})`, range.jl:1237. -/
instance {V W ρ₁ ρ₂ : Type} [JReverse (StepRange (JInt u) (JInt s)) V] [JIntersect (UnitRange (JInt t)) V W]
    [JReverse W ρ₁] [JIntersect (UnitRange (JInt t)) (StepRange (JInt u) (JInt s)) ρ₂] :
    JIntersect (StepRange (JInt u) (JInt s)) (UnitRange (JInt t)) (ρ₁ ⊕ ρ₂) :=
  ⟨intersect_StepRange_AbstractUnitRange⟩
/-- `+` of two values (`base/int.jl:88` after promotion), the operator `_define_range_op(:+)`
generates range methods for. -/
instance {α β γ : Type} [HAdd α β γ] : JScalarOp PlusOp α β γ := ⟨fun x y => x + y⟩
/-- `-` of two values. -/
instance {α β γ : Type} [HSub α β γ] : JScalarOp MinusOp α β γ := ⟨fun x y => x - y⟩
/-- `issorted(r::AbstractRange)`, range.jl:1458. -/
instance : JIssorted (StepRange (JInt t) (JInt s)) := ⟨issorted_AbstractRange⟩
/-- `Vector{T}(undef, n)`, the `Array{T,1}(::UndefInitializer, ::Int)` builtin (`boot.jl`):
`n` unassigned slots, `ArgumentError` for negative `n`. -/
instance {T : Type} : JVectorUndef T := ⟨fun n =>
  if n.val < 0 then throw (.jl (.argumentError "invalid Array dimensions"))
  else pure (List.replicate n.val.toNat none)⟩
/-- `_empty_stop(start, step)`, range.jl:1002. -/
instance : JEmptyStop (JInt t) (JInt s) (JInt (pTy t s)) := ⟨_empty_stop⟩
/-- `checkbounds(A, s)` of a range `A` and a range index `s`: as `checkboundsVector`
(essentials.jl:389, abstractarray.jl:690, 396, 141, 100, range.jl:706, 503), with the `checkindex`
method `checkindex(::Type{Bool}, inds::AbstractUnitRange, i::AbstractRange)` (abstractarray.jl:756,
`checkindexRange`): `isempty(i) | (checkindex(Bool, inds, first(i)) & checkindex(Bool, inds,
last(i)))`, each endpoint checked by `checkindexAxis`. -/
def checkboundsVectorRange {R U : Type} {L e : IntTy} [JLength R (JInt L)] [JIsempty U] [JFirst U (JInt e)]
    [JLast U (JInt e)] (r : R) (s : U) : JlX Unit := do
  let ok ← ofArr (JuliaLean.base.abstractarray.checkboundsOne
    (JuliaLean.base.abstractarray.eachindexLinearVector
      (JuliaLean.base.abstractarray.axes1 (fun a => toArr (do
        let sz ← size_AbstractRange a
        return [unchecked_oneto sz._1]))))
    (JuliaLean.base.abstractarray.checkindexRange (fun x => toArr (JIsempty.isempty x))
      (fun x => toArr (JFirst.first x)) (fun x => toArr (JLast.last x)) checkindexAxis)
    r s)
  if ok then pure () else do
    let e ← JThrowBoundserror.throwBoundserror r (Tuple1.mk s)
    nomatch e
instance {a : IntTy} : JCheckbounds (UnitRange (JInt t)) (UnitRange (JInt a)) := ⟨checkboundsVectorRange⟩
instance {a b : IntTy} : JCheckbounds (StepRange (JInt t) (JInt s)) (StepRange (JInt a) (JInt b)) :=
  ⟨checkboundsVectorRange⟩
/-- `Int(x::Bool)` (`boot.jl`, `base/int.jl`): `0` or `1`. -/
instance : JCtor JInt64 Bool := ⟨fun b => pure (JuliaLean.base.int.ofBool .i64 b)⟩
end RangeOps

end JuliaLean.Proofs.base.range

namespace JuliaLean.Proofs.base.range

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-- The number of integers `a, a+s, a+2s, ...` that lie between `a` and `b` (inclusive): the
length of `a:s:b`. Zero when `s` points away from `b` or `s = 0`. -/
def stepCount (a s b : Int) : Int :=
  if 0 < s ∧ a ≤ b then (b - a).tdiv s + 1
  else if s < 0 ∧ b ≤ a then (a - b).tdiv (-s) + 1 else 0

/-- The integers `a, a+s, a+2s, ...` that lie between `a` and `b` (inclusive): the elements that
`a:s:b` denotes. -/
def stepInts (a s b : Int) : List Int :=
  (List.range (stepCount a s b).toNat).map fun (k : Nat) => a + k * s

/-- The values of the elements that iterating `r` yields (at most `fuel + 1` of them). -/
def iterVals {R S : Type} {q : IntTy} [JIterate1 R (JInt q) S] [JIterate2 R S (JInt q)] (r : R)
    (fuel : Nat) : JlX (List Int) :=
  (iterList r fuel).map vals

/-- `reverse(r)` of a `StepRange{T,T}`: `_reverse(r, :)` (range.jl:1445); `last(r):negate(step(r)):first(r)`
selects `(:)(start::T, step::T, stop::T)` (range.jl:22) for signed `T` and
`(:)(start::T, step, stop::T)` (range.jl:65) for unsigned `T`, whose negated step is signed. -/
def reverseStep : {t : IntTy} → StepRange (JInt t) (JInt t) → JlX (StepRange (JInt t) (JInt (sTy t)))
  | .i8, r => _reverse_OrdinalRange r ⟨⟩
  | .i16, r => _reverse_OrdinalRange r ⟨⟩
  | .i32, r => _reverse_OrdinalRange r ⟨⟩
  | .i64, r => _reverse_OrdinalRange r ⟨⟩
  | .i128, r => _reverse_OrdinalRange r ⟨⟩
  | .u8, r => _reverse_OrdinalRange r ⟨⟩
  | .u16, r => _reverse_OrdinalRange r ⟨⟩
  | .u32, r => _reverse_OrdinalRange r ⟨⟩
  | .u64, r => _reverse_OrdinalRange r ⟨⟩
  | .u128, r => _reverse_OrdinalRange r ⟨⟩

/-- `intersect(r::StepRange{T,T}, s::UnitRange{T})` (range.jl:1237) for each BitInteger `T`. -/
def intersectStepUnit : {t : IntTy} → StepRange (JInt t) (JInt t) → UnitRange (JInt t) →
    JlX (StepRange (JInt t) (JInt (sTy t)) ⊕ StepRange (JInt t) (JInt t))
  | .i8, r, s => intersect_StepRange_AbstractUnitRange r s
  | .i16, r, s => intersect_StepRange_AbstractUnitRange r s
  | .i32, r, s => intersect_StepRange_AbstractUnitRange r s
  | .i64, r, s => intersect_StepRange_AbstractUnitRange r s
  | .i128, r, s => intersect_StepRange_AbstractUnitRange r s
  | .u8, r, s => intersect_StepRange_AbstractUnitRange r s
  | .u16, r, s => intersect_StepRange_AbstractUnitRange r s
  | .u32, r, s => intersect_StepRange_AbstractUnitRange r s
  | .u64, r, s => intersect_StepRange_AbstractUnitRange r s
  | .u128, r, s => intersect_StepRange_AbstractUnitRange r s

/-! ## Refuted properties -/

/-- `r[i]` of a unit range `a:b` at an in-bounds integer index `i` of any BitInteger type is
`a + (i - 1)`: Julia's indexing is by value, independent of the index's signedness. -/
def UnsignedIndexAgreement : Prop :=
  ∀ (t s : IntTy) (a b : JInt t) (r : UnitRange (JInt t)) (i : JInt s),
    colon_T_T_Real a b = .ok r → 1 ≤ i.val → i.val ≤ b.val - a.val + 1 →
    (_getindex_UnitRange_OverflowSafe r i).map Subtype.val = .ok (a.val + i.val - 1)

theorem unsignedIndexAgreement_refuted : ¬ UnsignedIndexAgreement := by
  intro h
  have := h .i8 .u8 (lit .i8 (-1)) (lit .i8 1) ⟨lit .i8 (-1), lit .i8 1⟩ (lit .u8 1) (by decide)
    (by decide) (by decide)
  revert this; decide

/-- `checked_length(a:s:b)` of a nonempty integer range whose element count `n = (b-a)÷s + 1` is
representable in the length type returns `n`. -/
def CheckedLengthCount : Prop :=
  ∀ (t : IntTy) (a s b : JInt t) (r : StepRange (JInt t) (JInt t)),
    colon_T_T_T_Real a s b = .ok r → 0 < stepCount a.val s.val b.val →
    stepCount a.val s.val b.val ≤ (lenTy t).max →
    (checkedLengthStep r).map Subtype.val = .ok (stepCount a.val s.val b.val)

theorem checkedLengthCount_refuted : ¬ CheckedLengthCount := by
  intro h
  have := h .i64 (lit .i64 0) (lit .i64 (-9223372036854775808)) (lit .i64 (-9223372036854775808))
    ⟨lit .i64 0, lit .i64 (-9223372036854775808), lit .i64 (-9223372036854775808)⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- In a nonempty `StepRange(start::T, step::S, stop::T)` of BitIntegers, the element at the
last index `length(r)` is `last(r)`. -/
def StepRangeLastIndex : Prop :=
  ∀ (t s : IntTy) (a b : JInt t) (st : JInt s) (r : StepRange (JInt t) (JInt s)) (n : JInt (lenTy t)),
    StepRange_T_S_T a st b = .ok r → JIsempty.isempty r = .ok false → lengthStepMixed r = .ok n →
    _getindex_AbstractRange r n = JLast.last r

theorem stepRangeLastIndex_refuted : ¬ StepRangeLastIndex := by
  intro h
  have := h .i64 .u64 (lit .i64 (-2)) (lit .i64 (-1)) (lit .u64 1) ⟨lit .i64 (-2), lit .u64 1, lit .i64 (-1)⟩
    (lit .i64 2) (by decide) (by decide) (by decide)
  revert this; decide

/-- `range(start; length=n)` and `range(start; step, length=n)` with BitInteger arguments and
`n >= 0` return a range of `n` elements when they return. -/
def KeywordLength : Prop :=
  (∀ (t : IntTy) (a : JInt t) (n : JInt64) res, 0 ≤ n.val → range_start_length a n = .ok res →
    (match res with
     | .inl u => (lengthUnit u).map Subtype.val
     | .inr g => pure g.len.val) = .ok n.val) ∧
  (∀ (t : IntTy) (a st : JInt t) (n : JInt64) res, 0 ≤ n.val →
    range_start_step_length a st n = .ok res →
    (match res with
     | .inl u => (lengthStepMixed u).map Subtype.val
     | .inr g => pure g.len.val) = .ok n.val)

theorem keywordLength_refuted : ¬ KeywordLength := by
  intro ⟨h, _⟩
  have := h .i64 (lit .i64 9223372036854775806) (lit .i64 5)
    (.inl ⟨lit .i64 9223372036854775806, lit .i64 9223372036854775805⟩) (by decide) (by decide)
  revert this; decide

/-- `range(start; length=n)` with a negative requested count `n` throws. -/
def KeywordNegativeLength : Prop :=
  ∀ (t : IntTy) (a : JInt t) (n : JInt64), n.val < 0 → ∃ e, range_start_length a n = .error e

theorem keywordNegativeLength_refuted : ¬ KeywordNegativeLength := by
  intro h
  obtain ⟨e, he⟩ := h .i64 (lit .i64 1) (lit .i64 (-1)) (by decide)
  have hv : range_start_length (lit .i64 1) (lit .i64 (-1)) =
      .ok (.inl ⟨lit .i64 1, lit .i64 0⟩) := by decide
  cases he.symm.trans hv

/-- `mod(x, r)` for a nonempty unit range `r = a:b` of `n` elements returns the `y` in `r` with
`x ≡ y (mod n)`: `y = a + (x - a) mod n` (the docstring of `mod(::Integer, ::AbstractUnitRange)`). -/
def ModCongruence : Prop :=
  ∀ (t : IntTy) (a b x : JInt t) (r : UnitRange (JInt t)), colon_T_T_Real a b = .ok r → a.val ≤ b.val →
    b.val - a.val + 1 ≤ (lenTy t).max →
    (mod_Integer_AbstractUnitRange x r).map Subtype.val =
      .ok (a.val + (x.val - a.val) % (b.val - a.val + 1))

theorem modCongruence_refuted : ¬ ModCongruence := by
  intro h
  have := h .i64 (lit .i64 1) (lit .i64 3) (lit .i64 (-9223372036854775808)) ⟨lit .i64 1, lit .i64 3⟩
    (by decide) (by decide) (by decide)
  revert this; decide

/-- The hint in the `ArgumentError` of `range(; step, length)` (no start, no stop) does not claim
that `length`, which the caller supplied, is missing. -/
def RangeErrorHint : Prop :=
  ∀ (t u : IntTy) (st : JInt t) (n : JInt u) (msg : String),
    (range_error (ρ := Unit) Nothing.nothing st Nothing.nothing n = .error (.jl (.argumentError msg))) →
    ¬ ∃ pre, msg = pre ++ "At least one of `length` or `stop` must be specified.\n"

theorem rangeErrorHint_refuted : ¬ RangeErrorHint := by
  intro h
  have := h .i64 .i64 (lit .i64 1) (lit .i64 3)
    "Cannot construct range from arguments:\nstart = nothing\nstep = 1\nstop = nothing\nlength = 3\nAt least one of `length` or `stop` must be specified.\n"
    (by decide +kernel)
  exact this ⟨"Cannot construct range from arguments:\nstart = nothing\nstep = 1\nstop = nothing\nlength = 3\n", by decide +kernel⟩

/-- `range(; stop, length)` with BitInteger `stop` and `length` returns a `UnitRange` (the `range`
docstring: integer arguments with only `length` and `stop` give a `UnitRange`). -/
def KeywordStopLengthUnitRange : Prop :=
  ∀ (t : IntTy) (b : JInt t) (n : JInt64) res, range_stop_length b n = .ok res → res.isLeft = true

theorem keywordStopLengthUnitRange_refuted : ¬ KeywordStopLengthUnitRange := by
  intro h
  have := h .u64 (lit .u64 10) (lit .i64 5) (.inr ⟨lit .u64 6, lit .u64 1, lit .i64 5, lit .i64 1⟩)
    (by decide)
  revert this; decide

/-- `intersect(a:b, c:s:d)` of a unit range and a step range of one BitInteger type contains every
integer that both ranges contain. -/
def UnitStepIntersectComplete : Prop :=
  ∀ (t : IntTy) (a b c st d : JInt t) (r : UnitRange (JInt t)) (s : StepRange (JInt t) (JInt t))
    (res : StepRange (JInt t) (JInt t)) (fuel : Nat) (xs : List Int),
    colon_T_T_Real a b = .ok r → colon_T_T_T_Real c st d = .ok s →
    intersect_AbstractUnitRange_StepRange r s = .ok res → iterVals res fuel = .ok xs →
    ∀ x, a.val ≤ x → x ≤ b.val → x ∈ stepInts c.val st.val d.val → x ∈ xs

theorem unitStepIntersectComplete_refuted : ¬ UnitStepIntersectComplete := by
  intro h
  have := h .i8 (lit .i8 (-100)) (lit .i8 100) (lit .i8 (-120)) (lit .i8 7) (lit .i8 125)
    ⟨lit .i8 (-100), lit .i8 100⟩ ⟨lit .i8 (-120), lit .i8 7, lit .i8 125⟩
    ⟨lit .i8 (-99), lit .i8 7, lit .i8 90⟩ 300 ((List.range 28).map fun (k : Nat) => -99 + 7 * k)
    (by decide) (by decide) (by decide) (by decide +kernel) 97 (by decide) (by decide)
    (by decide +kernel)
  revert this; decide +kernel

/-- Reversing an integer step range `a:s:b` keeps its number of elements. -/
def ReverseLength : Prop :=
  ∀ (t : IntTy) (a st b : JInt t) (r : StepRange (JInt t) (JInt t)) rr,
    colon_T_T_T_Real a st b = .ok r → reverseStep r = .ok rr →
    (lengthStepMixed rr).map Subtype.val = (lengthStep r).map Subtype.val

theorem reverseLength_refuted : ¬ ReverseLength := by
  intro h
  have := h .i8 (lit .i8 0) (lit .i8 (-128)) (lit .i8 (-128)) ⟨lit .i8 0, lit .i8 (-128), lit .i8 (-128)⟩
    ⟨lit .i8 (-128), lit .i8 (-128), lit .i8 (-127)⟩ (by decide) (by decide)
  revert this; decide

/-- Slicing a unit range `a:b` by an in-bounds nonempty unit range `c:d` gives the range whose
elements are `r[c], ..., r[d]`, that is `a+c-1, ..., a+d-1`. -/
def UnitSlice : Prop :=
  ∀ (t : IntTy) (a b c d : JInt t) (r s : UnitRange (JInt t)),
    colon_T_T_Real a b = .ok r → colon_T_T_Real c d = .ok s → 1 ≤ c.val → c.val ≤ d.val →
    d.val ≤ b.val - a.val + 1 →
    ∃ u, getindex_AbstractUnitRange_AbstractUnitRange r s = .ok (.inr u) ∧
      iterVals u (d.val - c.val + 1).toNat = .ok (intsFromTo (a.val + c.val - 1) (a.val + d.val - 1))

theorem unitSlice_refuted : ¬ UnitSlice := by
  intro h
  obtain ⟨u, hu, _⟩ := h .i8 (lit .i8 120) (lit .i8 127) (lit .i8 8) (lit .i8 8)
    ⟨lit .i8 120, lit .i8 127⟩ ⟨lit .i8 8, lit .i8 8⟩ (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have hv : getindex_AbstractUnitRange_AbstractUnitRange (⟨lit .i8 120, lit .i8 127⟩ : UnitRange (JInt .i8))
      (⟨lit .i8 8, lit .i8 8⟩ : UnitRange (JInt .i8)) = .error (.jl (.inexactError "Int8")) := by decide
  cases hu.symm.trans hv

/-- Intersecting an integer step range with an empty unit range gives an empty range. -/
def IntersectEmpty : Prop :=
  ∀ (t : IntTy) (a st b c d : JInt t) (r : StepRange (JInt t) (JInt t)) (u : UnitRange (JInt t)) res,
    colon_T_T_T_Real a st b = .ok r → colon_T_T_Real c d = .ok u → d.val < c.val →
    intersectStepUnit r u = .ok res →
    (match res with | .inl x => isempty_StepRange x | .inr x => isempty_StepRange x) = true

theorem intersectEmpty_refuted : ¬ IntersectEmpty := by
  intro h
  have := h .i8 (lit .i8 (-128)) (lit .i8 127) (lit .i8 126) (lit .i8 5) (lit .i8 4)
    ⟨lit .i8 (-128), lit .i8 127, lit .i8 126⟩ ⟨lit .i8 5, lit .i8 4⟩
    (.inr ⟨lit .i8 (-128), lit .i8 127, lit .i8 (-1)⟩) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- `intersect(a:b, c:s:d)` of a unit range and a step range of BitInteger types contains only
integers that both ranges contain. -/
def UnitStepIntersectSound : Prop :=
  ∀ (t u : IntTy) (a b : JInt t) (c st d : JInt u) (r : UnitRange (JInt t))
    (s : StepRange (JInt u) (JInt u)) res (fuel : Nat) (xs : List Int),
    colon_T_T_Real a b = .ok r → colon_T_T_T_Real c st d = .ok s →
    intersect_AbstractUnitRange_StepRange r s = .ok res → iterVals res fuel = .ok xs →
    ∀ x ∈ xs, a.val ≤ x ∧ x ≤ b.val ∧ x ∈ stepInts c.val st.val d.val

theorem unitStepIntersectSound_refuted : ¬ UnitStepIntersectSound := by
  intro h
  have := h .u8 .i8 (lit .u8 0) (lit .u8 255) (lit .i8 (-100)) (lit .i8 7) (lit .i8 117)
    ⟨lit .u8 0, lit .u8 255⟩ ⟨lit .i8 (-100), lit .i8 7, lit .i8 117⟩
    ⟨lit .u8 2, lit .i8 7, lit .u8 114⟩ 20 ((List.range 17).map fun (k : Nat) => 2 + 7 * k)
    (by decide) (by decide) (by decide) (by decide +kernel) 2 (by decide)
  revert this; decide +kernel

/-- `length(a:b)` of a unit range of any BitInteger type is its number of elements `b - a + 1`
whenever it returns (`length` throws rather than return a wrong count). -/
def UnitLengthCount : Prop :=
  ∀ (t : IntTy) (a b : JInt t) (r : UnitRange (JInt t)) (n : JInt (lenTy t)),
    colon_T_T_Real a b = .ok r → a.val ≤ b.val → lengthUnit r = .ok n → n.val = b.val - a.val + 1

theorem unitLengthCount_refuted : ¬ UnitLengthCount := by
  intro h
  have := h .i64 (lit .i64 (-9223372036854775808)) (lit .i64 9223372036854775807)
    ⟨lit .i64 (-9223372036854775808), lit .i64 9223372036854775807⟩ (lit .i64 0)
    (by decide) (by decide) (by decide)
  revert this; decide

/-- `Array{T,1}(r)`, which `collect(r)` calls, fills the vector it allocates without writing
past its end (Julia's `@inbounds` writes outside the vector are undefined behaviour). -/
def CollectInBounds : Prop :=
  ∀ (t : IntTy) (a b : JInt t) (r : UnitRange (JInt t)) (fuel : Nat),
    colon_T_T_Real a b = .ok r → Array_T_1_AbstractRange r fuel ≠ .error .inboundsViolation

theorem collectInBounds_refuted : ¬ CollectInBounds := by
  intro h
  exact h .i64 (lit .i64 (-9223372036854775808)) (lit .i64 9223372036854775807)
    ⟨lit .i64 (-9223372036854775808), lit .i64 9223372036854775807⟩ 3 (by decide) (by decide)

/-- `r == s` for a nonempty unit range and a range of the same element type implies that `s` is
nonempty (`==(r::AbstractRange, s::AbstractRange)` compares elements). -/
def EqEmptiness : Prop :=
  ∀ (t : IntTy) (a b : JInt t) (r : UnitRange (JInt t)) (c : JInt t) (n : JInt64) e (fuel : Nat),
    colon_T_T_Real a b = .ok r → a.val ≤ b.val → range_start_length c n = .ok (.inr e) →
    eq_AbstractRange_AbstractRange r e fuel = .ok true → e.len.val ≠ 0

theorem eqEmptiness_refuted : ¬ EqEmptiness := by
  intro h
  exact h .u64 (lit .u64 0) (lit .u64 18446744073709551615) ⟨lit .u64 0, lit .u64 18446744073709551615⟩
    (lit .u64 7) (lit .i64 0) ⟨lit .u64 7, lit .u64 1, lit .i64 0, lit .i64 1⟩ 2
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `StepRange(start::T, step::S, stop::T)` of BitIntegers whose step points away from `stop`
is constructed, and is empty (like `StepRange(-5, 1, -10)`). -/
def StepAwayEmpty : Prop :=
  ∀ (t s : IntTy) (a b : JInt t) (st : JInt s), 0 < st.val → b.val < a.val →
    ∃ r, StepRange_T_S_T a st b = .ok r ∧ JIsempty.isempty r = .ok true

theorem stepAwayEmpty_refuted : ¬ StepAwayEmpty := by
  intro h
  obtain ⟨r, hr, _⟩ := h .i64 .u64 (lit .i64 (-5)) (lit .i64 (-10)) (lit .u64 1) (by decide) (by decide)
  have hv : (StepRange_T_S_T (lit .i64 (-5)) (lit .u64 1) (lit .i64 (-10)) :
      JlX (StepRange (JInt .i64) (JInt .u64))) = .error (.jl (.inexactError "Int64")) := by decide
  cases hr.symm.trans hv

/-- Converting an empty integer unit range to `UnitRange{T}` of another non-`Bool` BitInteger
type `T` succeeds and gives an empty range. -/
def ConvertEmptyUnit : Prop :=
  ∀ (t u : IntTy) (a b : JInt t) (r : UnitRange (JInt t)), colon_T_T_Real a b = .ok r →
    b.val < a.val → ∃ v, UnitRange_T_AbstractUnitRange (T := JInt u) r = .ok v ∧ v.stop.val < v.start.val

theorem convertEmptyUnit_refuted : ¬ ConvertEmptyUnit := by
  intro h
  obtain ⟨v, hv, _⟩ := h .i64 .u8 (lit .i64 0) (lit .i64 (-1)) ⟨lit .i64 0, lit .i64 (-1)⟩ (by decide)
    (by decide)
  have he : UnitRange_T_AbstractUnitRange (T := JInt .u8) (⟨lit .i64 0, lit .i64 (-1)⟩ : UnitRange (JInt .i64))
      = .error (.jl (.inexactError "UInt8")) := by decide
  cases hv.symm.trans he

/-- `r1 + r2` of two integer unit ranges of equal length is the range whose `i`-th element is
`r1[i] + r2[i]`; its elements can all be read. -/
def RangeAddPointwise : Prop :=
  ∀ (t : IntTy) (a b c d : JInt t) (r1 r2 : UnitRange (JInt t)) g,
    colon_T_T_Real a b = .ok r1 → colon_T_T_Real c d = .ok r2 → a.val ≤ b.val →
    b.val - a.val = d.val - c.val →
    rangeop_OrdinalRange_OrdinalRange PlusOp r1 r2 = .ok g →
    iterVals g (b.val - a.val + 1).toNat =
      .ok ((intsFromTo 0 (b.val - a.val)).map fun k => wrapInt t (a.val + k + (c.val + k)))

theorem rangeAddPointwise_refuted : ¬ RangeAddPointwise := by
  intro h
  have := h .i8 (lit .i8 126) (lit .i8 127) (lit .i8 1) (lit .i8 2) ⟨lit .i8 126, lit .i8 127⟩
    ⟨lit .i8 1, lit .i8 2⟩ ⟨lit .i8 127, lit .i8 2, lit .i64 2, lit .i64 1⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
  revert this; decide +kernel

/-- `issorted(a:s:b)` of an integer step range with at least two elements implies a
nonnegative step. -/
def IssortedStep : Prop :=
  ∀ (t : IntTy) (a st b : JInt t) (r : StepRange (JInt t) (JInt t)),
    colon_T_T_T_Real a st b = .ok r → 2 ≤ stepCount a.val st.val b.val →
    issorted_AbstractRange r = .ok true → 0 ≤ st.val

theorem issortedStep_refuted : ¬ IssortedStep := by
  intro h
  have := h .i64 (lit .i64 9223372036854775807) (lit .i64 (-1)) (lit .i64 (-9223372036854775808))
    ⟨lit .i64 9223372036854775807, lit .i64 (-1), lit .i64 (-9223372036854775808)⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- The documented contract of `gcdx(a, b)` (intfuncs.jl) on one BitInteger
type: a returned `(d, u, v)` has `d = gcd(a, b)` and `u*a + v*b = d`, with the minimal
coefficients `|u| <= |b/d|` and `|v| <= |a/d|` its docstring promises. -/
def GcdxLaw (t : IntTy) [JGcdx (JInt t) (JInt t) (JInt t)] : Prop :=
  ∀ (a b d u v : JInt t), JGcdx.gcdx a b = .ok (d, u, v) →
    d.val = Int.gcd a.val b.val ∧ u.val * a.val + v.val * b.val = d.val ∧
    (d.val ≠ 0 → u.val.natAbs * d.val.natAbs ≤ b.val.natAbs ∧ v.val.natAbs * d.val.natAbs ≤ a.val.natAbs)

/-- The documented contract of `lcm(a, b)` (intfuncs.jl): a returned value is the nonnegative
least common multiple. -/
def LcmLaw (t : IntTy) [JLcm (JInt t) (JInt t) (JInt t)] : Prop :=
  ∀ (a b l : JInt t), JLcm.lcm a b = .ok l → l.val = Int.lcm a.val b.val

/-- `intersect(r::StepRange, s::StepRange)` of two step ranges of one BitInteger type contains
every integer both ranges contain, for any `gcdx` and `lcm` that meet their documented
contracts. -/
def StepStepIntersectComplete : Prop :=
  ∀ (t : IntTy) [JGcdx (JInt t) (JInt t) (JInt t)] [JLcm (JInt t) (JInt t) (JInt t)],
    GcdxLaw t → LcmLaw t →
    ∀ (a st b c su d : JInt t) (r s res : StepRange (JInt t) (JInt t)) (fuel : Nat) (xs : List Int),
      colon_T_T_T_Real a st b = .ok r → colon_T_T_T_Real c su d = .ok s →
      intersect_StepRange_StepRange r s = .ok res → iterVals res fuel = .ok xs →
      ∀ x, x ∈ stepInts a.val st.val b.val → x ∈ stepInts c.val su.val d.val → x ∈ xs

/-- `gcdx(2, 3) = (1, -1, 1)` on `Int8`, Julia's value; other arguments are not needed. -/
def gcdx8 (a b : JInt .i8) : JlX (JInt .i8 × JInt .i8 × JInt .i8) :=
  if a.val = 2 ∧ b.val = 3 then pure (lit .i8 1, lit .i8 (-1), lit .i8 1)
  else throw (.errorException "not needed")

/-- `lcm(2, 3) = 6` on `Int8`. -/
def lcm8 (a b : JInt .i8) : JlX (JInt .i8) :=
  if a.val = 2 ∧ b.val = 3 then pure (lit .i8 6) else throw (.errorException "not needed")

theorem stepStepIntersectComplete_refuted : ¬ StepStepIntersectComplete := by
  intro h
  unfold StepStepIntersectComplete at h
  have hg : @GcdxLaw .i8 ⟨gcdx8⟩ := by
    intro a b d u v hv
    simp only [JGcdx.gcdx, gcdx8] at hv
    split at hv
    · rename_i hab
      obtain ⟨ha, hb⟩ := hab
      cases hv
      simp only [ha, hb]
      decide
    · cases hv
  have hl : @LcmLaw .i8 ⟨lcm8⟩ := by
    intro a b l hv
    simp only [JLcm.lcm, lcm8] at hv
    split at hv
    · rename_i hab
      obtain ⟨ha, hb⟩ := hab
      cases hv
      simp only [ha, hb]
      decide
    · cases hv
  have := @h .i8 ⟨gcdx8⟩ ⟨lcm8⟩ hg hl (lit .i8 (-100)) (lit .i8 2) (lit .i8 120) (lit .i8 (-100))
    (lit .i8 3) (lit .i8 120) ⟨lit .i8 (-100), lit .i8 2, lit .i8 120⟩
    ⟨lit .i8 (-100), lit .i8 3, lit .i8 119⟩ ⟨lit .i8 (-100), lit .i8 6, lit .i8 110⟩ 50
    ((List.range 36).map fun (k : Nat) => -100 + 6 * k)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) 116 (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

/-! ### Dispatch world: `UnitRange{Bool}` and tuples -/

section BoolRanges

/-- A `base/tuple.jl` computation inside a range method: its `JlError` is the range exception. -/
def liftTuple {α : Type} : JuliaLean.base.tuple.R α → JlX α
  | .ok v => .ok v
  | .error (.julia e) => .error (.jl e)
  | .error e => .error (.errorException e.kind)

instance : JEltype (UnitRange Bool) Bool := ⟨⟩
instance : JFieldStart (UnitRange Bool) Bool := ⟨UnitRange.start⟩
instance : JFieldStop (UnitRange Bool) Bool := ⟨UnitRange.stop⟩
/-- `convert(Bool, x::Bool) = x`. -/
instance : JConvert Bool Bool := ⟨pure⟩
/-- `first(r::OrdinalRange{T})`, range.jl:867. -/
instance : JFirst (UnitRange Bool) Bool := ⟨first_OrdinalRange⟩
/-- `last(r::OrdinalRange{T})`, range.jl:877. -/
instance : JLast (UnitRange Bool) Bool := ⟨last_OrdinalRange⟩
/-- `zero(Bool) = false`. -/
instance : JZero Bool := ⟨false⟩
/-- `x - y` of two `Bool`s is an `Int` (`bool.jl:150`). -/
instance : HSub Bool Bool JInt64 := ⟨JuliaLean.base.bool.subBool⟩
/-- `x + y` of two `Bool`s is an `Int` (`bool.jl:149`). -/
instance : HAdd Bool Bool JInt64 := ⟨JuliaLean.base.bool.addBool⟩
/-- `x <= y` on `Bool` (`bool.jl:130`). -/
instance : JLe Bool Bool := ⟨JuliaLean.base.bool.leBool⟩
/-- `x < y` on `Bool` (`bool.jl:129`). -/
instance : JLt Bool Bool := ⟨JuliaLean.base.bool.ltBool⟩
/-- `x == y` on `Bool`. -/
instance : JEq Bool Bool := ⟨fun x y => x == y⟩
/-- `x == y` of a `Bool` and an `Int`: promote the `Bool` to `Int` (`promotion.jl`). -/
instance : JEq Bool JInt64 := ⟨fun x y => JuliaLean.base.int.eq (JuliaLean.base.int.ofBool .i64 x) y⟩
/-- `x + y` of an `Int` and a `Bool`: promote the `Bool` to `Int` (`promotion.jl`), then add. -/
instance : HAdd JInt64 Bool JInt64 := ⟨fun x y => x + JuliaLean.base.int.ofBool .i64 y⟩
/-- `Bool(x::Real) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))`
(`bool.jl:170`), the conversion `convert(Bool, x)` uses. -/
instance : JConvert Bool JInt64 := ⟨fun x =>
  liftJl (JuliaLean.base.bool.boolFromReal (fun x n => pure (JuliaLean.base.int.eq x (lit .i64 n))) x)⟩
/-- `step(r::AbstractUnitRange{Bool}) = true`, range.jl:737. -/
instance : JStep (UnitRange Bool) Bool := ⟨fun r => pure (step_AbstractUnitRange_Bool r)⟩
/-- `length(r::AbstractUnitRange{T})`, range.jl:794 (`Bool` is not among the `smallints`). -/
instance : JLength (UnitRange Bool) JInt64 := ⟨length_AbstractUnitRange⟩
/-- `isempty(r::AbstractUnitRange)`, range.jl:711. -/
instance : JIsempty (UnitRange Bool) := ⟨isempty_AbstractUnitRange⟩
/-- `iterate(r::OrdinalRange)`, range.jl:935. -/
instance : JIterate1 (UnitRange Bool) Bool Bool := ⟨iterate_OrdinalRange⟩
/-- `iterate(r::OrdinalRange{T}, i)`, range.jl:937. -/
instance : JIterate2 (UnitRange Bool) Bool Bool := ⟨iterate_OrdinalRange_state⟩
/-- `require_one_based_indexing(r)` (abstractarray.jl): a `UnitRange` has one-based axes. -/
instance : JRequireOneBased (UnitRange Bool) := ⟨fun _ => pure ()⟩
/-- `t[i::Int] = getfield(t, i)` (`tuple.jl:33`). -/
instance : JTupleGetindex JInt64 := ⟨fun t i => liftTuple (JuliaLean.base.tuple.getindexInt t i)⟩
/-- `t[i::Integer] = getfield(t, convert(Int, i))` (`tuple.jl:34`) for a `Bool` index. -/
instance : JTupleGetindex Bool := ⟨fun t i =>
  liftTuple (JuliaLean.base.tuple.getindexInt t (JuliaLean.base.int.ofBool .i64 i))⟩

end BoolRanges

/-- The `Bool` values of `a:b`. -/
def boolsFromTo (a b : Bool) : List Bool :=
  match a, b with
  | false, false => [false] | false, true => [false, true] | true, true => [true] | true, false => []

/-- Indexing a tuple by a `UnitRange{Bool}` agrees with logical indexing by the same `Bool`
values: it keeps the entries at the positions where the range is `true`. -/
def TupleBoolRangeIndex : Prop :=
  ∀ (t : List Int) (a b : Bool) (fuel : Nat), t.length = (boolsFromTo a b).length → 2 ≤ fuel →
    getindex_Tuple_AbstractUnitRange t (⟨a, b⟩ : UnitRange Bool) fuel =
      .ok ((t.zip (boolsFromTo a b)).filterMap fun p => if p.2 then some p.1 else none)

theorem tupleBoolRangeIndex_refuted : ¬ TupleBoolRangeIndex := by
  intro h
  have := h [10, 20] false true 2 (by decide) (by decide)
  revert this; decide

/-- Slicing an integer step range `r = a:s:b` by a nonempty in-bounds `Int` step range `c:u:d`
gives `length(c:u:d)` elements. -/
def StepSliceLength : Prop :=
  ∀ (t : IntTy) (a st b : JInt t) (r : StepRange (JInt t) (JInt t)) (c su d : JInt64)
    (s : StepRange JInt64 JInt64) res,
    colon_T_T_T_Real a st b = .ok r → colon_T_T_T_Real c su d = .ok s →
    0 < stepCount c.val su.val d.val → 1 ≤ c.val → c.val ≤ stepCount a.val st.val b.val →
    1 ≤ d.val → d.val ≤ stepCount a.val st.val b.val →
    getindex_StepRange_AbstractRange r s = .ok res →
    (match res with
     | .inl _ => (Except.error (Exc.errorException "Bool index") : JlX Int)
     | .inr v => (lengthStepMixed v).map Subtype.val) = .ok (stepCount c.val su.val d.val)

theorem stepSliceLength_refuted : ¬ StepSliceLength := by
  intro h
  have := h .u64 (lit .u64 1) (lit .u64 1) (lit .u64 4) ⟨lit .u64 1, lit .u64 1, lit .u64 4⟩
    (lit .i64 4) (lit .i64 (-1)) (lit .i64 1) ⟨lit .i64 4, lit .i64 (-1), lit .i64 1⟩
    (.inr ⟨lit .u64 4, lit .u64 18446744073709551615, lit .u64 3⟩)
    (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- `-r` of an integer step range `a:s:b` agrees elementwise with scalar negation `-x` of each
element `x` of `r` in its type `T`. -/
def NegatePointwise : Prop :=
  ∀ (t : IntTy) (a st b : JInt t) (r : StepRange (JInt t) (JInt t)) res (fuel : Nat) (xs : List Int),
    colon_T_T_T_Real a st b = .ok r → neg_OrdinalRange r = .ok res →
    (match res with | .inl v => iterVals v fuel | .inr v => iterVals v fuel) = .ok xs →
    xs = (stepInts a.val st.val b.val).map fun x => wrapInt t (-x)

theorem negatePointwise_refuted : ¬ NegatePointwise := by
  intro h
  have := h .i8 (lit .i8 (-128)) (lit .i8 1) (lit .i8 (-126)) ⟨lit .i8 (-128), lit .i8 1, lit .i8 (-126)⟩
    (.inl ⟨lit .i64 (-128), lit .i8 (-1), lit .i64 (-130)⟩) 5 [-128, -129, -130]
    (by decide) (by decide) (by decide)
  revert this; decide +kernel

end JuliaLean.Proofs.base.range

namespace JuliaLean.Proofs.base.range

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)
open JuliaLean.base.float (FV FTy)

/-! ## Dispatch world: `Float64` -/

section FloatWorld

/-- `Float64`. -/
abbrev F64 := FV .f64

/-- The `Float64` with IEEE bit pattern `n` (`reinterpret(Float64, n)`). -/
def f64 (n : Nat) : F64 := JuliaLean.Promotion.Fl.ofBits n

open JuliaLean.base.float in
section
/-- Type tests on `Float64`. -/
instance : JType F64 where
  isBool := false
  isSigned := false
  isInteger := false
  isAbstractFloat := true
  bool_eq := by intro h; cases h
/-- `zero(Float64)`. -/
instance : JZero F64 := ⟨zero_float .f64⟩
/-- `oneunit(Float64)`. -/
instance : JOneunit F64 := ⟨one_float .f64⟩
/-- `x + y`, `-`, `*`, `/` on `Float64` (float.jl:487-491). -/
instance : HAdd F64 F64 F64 := ⟨add_IEEEFloat⟩
instance : HSub F64 F64 F64 := ⟨sub_IEEEFloat⟩
instance : HMul F64 F64 F64 := ⟨mul_IEEEFloat⟩
instance : HDiv F64 F64 F64 := ⟨div_IEEEFloat⟩
/-- `x == y`, `<`, `<=` on `Float64` (float.jl:616-620). -/
instance : JEq F64 F64 := ⟨eq_IEEEFloat⟩
instance : JLt F64 F64 := ⟨lt_IEEEFloat⟩
instance : JLe F64 F64 := ⟨le_IEEEFloat⟩
/-- `iszero(x)` on `Float64`. -/
instance : JIszero F64 := ⟨iszero_float⟩
/-- `isinteger(x)` on `Float64`. -/
instance : JIsinteger F64 := ⟨isinteger_callee⟩
/-- `Float64(x::Float64) = x`, `convert(Float64, x::Float64) = x`. -/
instance : JConvert F64 F64 := ⟨pure⟩
instance : JCtor F64 F64 := ⟨pure⟩
/-- `Float64(x::Int)` (float.jl:245, `sitofp`). -/
instance : JConvert F64 JInt64 := ⟨fun x => pure (float_BitSigned64 .f64 x)⟩
/-- `Int64(x::Float64)` (float.jl:936-953): `InexactError` unless `x` is an integer in range. -/
instance : JCtor JInt64 F64 := ⟨fun x => liftJl (intOfFloat .i64 x)⟩
instance : JConvert JInt64 F64 := ⟨fun x => liftJl (intOfFloat .i64 x)⟩
/-- `x / y` of two `Int`s: `float(x) / float(y)` (int.jl:102). -/
instance : HDiv JInt64 JInt64 F64 :=
  ⟨JuliaLean.base.int.fdiv_BitInteger (float_BitSigned64 .f64) (float_BitSigned64 .f64) div_IEEEFloat⟩
/-- Arithmetic of an `Int` and a `Float64` promotes the `Int` to `Float64` (`promotion.jl`). -/
instance : HSub JInt64 F64 F64 := ⟨fun x y => sub_IEEEFloat (float_BitSigned64 .f64 x) y⟩
instance : HMul JInt64 F64 F64 := ⟨fun x y => mul_IEEEFloat (float_BitSigned64 .f64 x) y⟩
instance : HMul F64 JInt64 F64 := ⟨fun x y => mul_IEEEFloat x (float_BitSigned64 .f64 y)⟩
instance : HDiv F64 JInt64 F64 := ⟨fun x y => div_IEEEFloat x (float_BitSigned64 .f64 y)⟩
/-- `round(Integer, x)` of a `Float64` (float.jl:456, `round(Int, x, RoundNearest)`): round to
the nearest integer, then convert to `Int`, `InexactError` when it is not representable. -/
instance : JRoundInteger F64 JInt64 := ⟨fun x => liftJl (intOfFloat .i64 (round_Nearest_llvm x))⟩
/-- `mod(x::Float64, y::Int)`: promote, then `mod(x::T, y::T) where {T<:AbstractFloat}`
(float.jl). -/
instance : JMod F64 JInt64 F64 := ⟨fun x y => pure (mod_AbstractFloat x (float_BitSigned64 .f64 y))⟩
/-- A `print(io, x::Float64)` implementation (`ryu/`, not modelled). Every property whose model
functions print a `Float64` (exception messages of the `LinRange` and `LogRange` constructors) takes
the printer as a typed parameter `[JPrint F64]`; counterexamples instantiate it with this one, on
computations that never print. -/
def somePrintF64 : JPrint F64 := ⟨fun _ => ""⟩
end

/-! ### `LinRange{Float64,Int}` -/

/-- `lerpi(j, d, a, b)`, range.jl:992. -/
instance : JLerpi JInt64 JInt64 F64 := ⟨lerpi⟩
/-- `LinRange{T,L}(start, stop, len)`, the inner constructor, range.jl:597. -/
instance [JPrint F64] : JLinRangeTL F64 JInt64 F64 F64 JInt64 := ⟨LinRange_TL_new⟩
instance [JPrint F64] : JSameType3 (LinRange F64 JInt64) F64 F64 JInt64 := ⟨LinRange_TL_new⟩
/-- `LinRange{T}(start, stop, len)`, range.jl:616. -/
instance [JPrint F64] : JLinRangeT F64 F64 F64 JInt64 (LinRange F64 JInt64) := ⟨LinRange_T⟩
instance : JEltype (LinRange F64 JInt64) F64 := ⟨⟩
instance : JLength (LinRange F64 JInt64) JInt64 := ⟨fun r => pure (length_LinRange r)⟩
instance : JFirst (LinRange F64 JInt64) F64 := ⟨fun r => pure (first_LinRange r)⟩
instance : JLast (LinRange F64 JInt64) F64 := ⟨fun r => pure (last_LinRange r)⟩
instance : JIsempty (LinRange F64 JInt64) := ⟨isempty_LinRange⟩
instance : JStep (LinRange F64 JInt64) F64 := ⟨step_LinRange⟩
instance : JUnsafeGetindex (LinRange F64 JInt64) JInt64 F64 := ⟨unsafe_getindex_LinRange⟩
instance : JCheckbounds (LinRange F64 JInt64) JInt64 := ⟨checkboundsVector⟩
instance : JGetindex (LinRange F64 JInt64) JInt64 F64 := ⟨_getindex_AbstractRange⟩
instance [JPrint F64] : JReverse (LinRange F64 JInt64) (LinRange F64 JInt64) := ⟨fun r => _reverse_LinRange r ⟨⟩⟩
instance : JIterate1 (LinRange F64 JInt64) F64 JInt64 :=
  ⟨fun r => iterate_StepRangeLen_LinRange r (jint 0)⟩
instance : JIterate2 (LinRange F64 JInt64) JInt64 F64 := ⟨iterate_StepRangeLen_LinRange⟩
instance : JInRange F64 (LinRange F64 JInt64) := ⟨_in_range⟩


/-! ### `LinRange{Int,Int}` -/

/-- `lerpi(j, d, a, b)` with `Int` endpoints, range.jl:992. -/
instance : JLerpi JInt64 JInt64 JInt64 := ⟨lerpi⟩
/-- `LinRange{T,L}(start, stop, len)`, range.jl:597. -/
instance : JLinRangeTL JInt64 JInt64 JInt64 JInt64 JInt64 := ⟨LinRange_TL_new⟩
/-- `LinRange{T}(r::AbstractRange)`, range.jl:1404. -/
instance : JLinRangeTOf JInt64 (StepRange JInt64 JInt64) (LinRange JInt64 JInt64) := ⟨LinRange_T_AbstractRange⟩
instance : JLength (LinRange JInt64 JInt64) JInt64 := ⟨fun r => pure (length_LinRange r)⟩
instance : JUnsafeGetindex (LinRange JInt64 JInt64) JInt64 JInt64 := ⟨unsafe_getindex_LinRange⟩
instance : JCheckbounds (LinRange JInt64 JInt64) JInt64 := ⟨checkboundsVector⟩

/-! ### `StepRangeLen{Float64,Float64,Float64,Int}` -/

/-- `StepRangeLen{T,R,S,L}(ref, step, len, offset)`, range.jl:533. -/
instance : JStepRangeLenTRSL F64 F64 F64 JInt64 F64 F64 JInt64 JInt64 := ⟨StepRangeLen_TRSL_new F64⟩
/-- `StepRangeLen(ref::R, step::S, len, offset = 1)`, range.jl:548. -/
instance : JStepRangeLen3 F64 F64 JInt64 (StepRangeLen F64 F64 F64 JInt64) :=
  ⟨fun ref step len => StepRangeLen_ref_step ref step len (jint 1)⟩
instance : JLength (StepRangeLen F64 F64 F64 JInt64) JInt64 := ⟨fun r => pure (length_StepRangeLen r)⟩
instance : JUnsafeGetindex (StepRangeLen F64 F64 F64 JInt64) JInt64 F64 := ⟨unsafe_getindex_StepRangeLen⟩
instance : JFirst (StepRangeLen F64 F64 F64 JInt64) F64 := ⟨first_StepRangeLen⟩
instance : JLast (StepRangeLen F64 F64 F64 JInt64) F64 := ⟨last_StepRangeLen⟩
instance : JIsempty (StepRangeLen F64 F64 F64 JInt64) := ⟨isempty_StepRangeLen⟩
instance : JCheckbounds (StepRangeLen F64 F64 F64 JInt64) JInt64 := ⟨checkboundsVector⟩
instance : JGetindex (StepRangeLen F64 F64 F64 JInt64) JInt64 F64 := ⟨_getindex_AbstractRange⟩
instance : JFirstindex (StepRangeLen F64 F64 F64 JInt64) JInt64 := ⟨fun _ => pure (jint 1)⟩
instance : JLastindex (StepRangeLen F64 F64 F64 JInt64) JInt64 := ⟨fun r => pure (length_StepRangeLen r)⟩
instance : JIterate1 (StepRangeLen F64 F64 F64 JInt64) F64 JInt64 :=
  ⟨fun r => iterate_StepRangeLen_LinRange r (jint 0)⟩
instance : JIterate2 (StepRangeLen F64 F64 F64 JInt64) JInt64 F64 := ⟨iterate_StepRangeLen_LinRange⟩
/-- `cmp(x::Integer, y::Integer)` (operators.jl:537) on `Int`. -/
instance : JCmp JInt64 JInt64 := ⟨fun x y =>
  pure (lit .i64 (JuliaLean.base.operators.cmpInteger (fun a b => JuliaLean.base.int.lt a b)
    (fun a b => JuliaLean.base.int.lt a b) x y))⟩
/-- `cmp(x, y)` (operators.jl:526) on `Bool`, with `isless(x::Real, y::Real) = x < y`. -/
instance : JCmp Bool Bool := ⟨fun x y =>
  pure (lit .i64 (JuliaLean.base.operators.cmp (JuliaLean.base.operators.islessReal
    JuliaLean.base.bool.ltBool)
    (JuliaLean.base.operators.islessReal
    JuliaLean.base.bool.ltBool) x y))⟩
/-- `cmp(x, y)` (operators.jl:526) on `Float64`, with `isless(x::AbstractFloat, y::AbstractFloat)`
(operators.jl:240). -/
instance : JCmp F64 F64 := ⟨fun x y =>
  pure (lit .i64 (JuliaLean.base.operators.cmp
    (JuliaLean.base.operators.islessFloatFloat (α := F64) (β := F64)
      (fun z : F64 => JuliaLean.base.float.isnan_IEEEFloat z)
      (fun z : F64 => JuliaLean.base.float.signbit_float z) JuliaLean.base.float.lt_IEEEFloat)
    (JuliaLean.base.operators.islessFloatFloat (α := F64) (β := F64)
      (fun z : F64 => JuliaLean.base.float.isnan_IEEEFloat z)
      (fun z : F64 => JuliaLean.base.float.signbit_float z) JuliaLean.base.float.lt_IEEEFloat) x y))⟩

/-! ### `UnitRange{Float64}` -/

/-- `floor(x::Float64)` (float.jl, `round(x, RoundDown)`). -/
instance : JFloor F64 F64 := ⟨fun x => pure (JuliaLean.base.float.round_Down_llvm x)⟩
/-- `unitrange_last(start, stop)` for non-`Integer` endpoints, range.jl:443. -/
instance : JUnitrangeLast F64 F64 := ⟨unitrange_last_Any⟩
/-- `UnitRange{T}(start::T, stop::T)`, range.jl:428. -/
instance : JUnitRangeT F64 F64 F64 := ⟨UnitRange_T_new⟩
instance : JEltype (UnitRange F64) F64 := ⟨⟩
instance : JFieldStop (UnitRange F64) F64 := ⟨UnitRange.stop⟩
/-- `last(r::OrdinalRange{T})`, range.jl:877. -/
instance : JLast (UnitRange F64) F64 := ⟨last_OrdinalRange⟩

/-! ### `LogRange{Float64}` -/

/-- `first(r::LogRange) = r.start`, range.jl:1698. -/
instance {X : Type} : JFirst (LogRange F64 X) F64 := ⟨fun r => pure (first_LogRange r)⟩
/-- `last(r::LogRange) = r.stop`, range.jl:1699. -/
instance {X : Type} : JLast (LogRange F64 X) F64 := ⟨fun r => pure (last_LogRange r)⟩
/-- `length(r::LogRange) = r.len`, range.jl:1696. -/
instance {X : Type} : JLength (LogRange F64 X) JInt64 := ⟨fun r => pure (length_LogRange r)⟩

end FloatWorld

/-! ## Refuted properties: floating-point ranges -/

/-- `LinRange(a, b, n)` of `Float64` endpoints `a <= b` keeps every element `r[i]` inside
`[a, b]`. -/
def LinRangeWithinEndpoints : Prop :=
  ∀ [JPrint F64] (a b : F64) (n i : JInt64) (r : LinRange F64 JInt64) (x : F64),
    JLe.le a b = true → LinRange_start_stop_len a b n = .ok r → 1 ≤ i.val → i.val ≤ n.val →
    _getindex_AbstractRange r i = .ok x → JLe.le a x = true ∧ JLe.le x b = true

theorem linRangeWithinEndpoints_refuted : ¬ LinRangeWithinEndpoints := by
  intro h
  have := @h somePrintF64 (f64 4591870180066957722) (f64 4591870180066957722) (lit .i64 6) (lit .i64 2)
    ⟨f64 4591870180066957722, f64 4591870180066957722, lit .i64 6, lit .i64 5⟩ (f64 4591870180066957723)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel)
  revert this; decide +kernel

/-- Every element `r[i]` of a `LinRange(a, b, n)` with finite `Float64` endpoints is `in` it. -/
def LinRangeElementsIn : Prop :=
  ∀ [JPrint F64] (a b : F64) (n i : JInt64) (r : LinRange F64 JInt64) (x : F64),
    JuliaLean.base.float.isfinite_callee a = true → JuliaLean.base.float.isfinite_callee b = true →
    LinRange_start_stop_len a b n = .ok r → 1 ≤ i.val → i.val ≤ n.val →
    _getindex_AbstractRange r i = .ok x → _in_range x r = .ok true

theorem linRangeElementsIn_refuted : ¬ LinRangeElementsIn := by
  intro h
  have := @h somePrintF64 (f64 18438243695727462560) (f64 9214871658872686752) (lit .i64 3) (lit .i64 2)
    ⟨f64 18438243695727462560, f64 9214871658872686752, lit .i64 3, lit .i64 2⟩ (f64 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel)
  revert this; decide +kernel

/-- `x in r` for a `Float64` and a `LinRange(a, b, n)` of `Float64`s returns a `Bool`: it does
not throw. -/
def LinRangeInTotal : Prop :=
  ∀ [JPrint F64] (a b x : F64) (n : JInt64) (r : LinRange F64 JInt64),
    LinRange_start_stop_len a b n = .ok r → ∃ v, _in_range x r = .ok v

theorem linRangeInTotal_refuted : ¬ LinRangeInTotal := by
  intro h
  obtain ⟨v, hv⟩ := @h somePrintF64 (f64 18438243695727462560) (f64 9214871658872686752) (f64 9214871658872686752)
    (lit .i64 3) ⟨f64 18438243695727462560, f64 9214871658872686752, lit .i64 3, lit .i64 2⟩
    (by decide +kernel)
  have he : _in_range (f64 9214871658872686752)
      (⟨f64 18438243695727462560, f64 9214871658872686752, lit .i64 3, lit .i64 2⟩ : LinRange F64 JInt64)
      = .error (.jl (.inexactError "Int64")) := by decide +kernel
  cases hv.symm.trans he

/-- `reverse(r)[i]` is bitwise identical to `r[length(r)+1-i]` for a `Float64` `LinRange`. -/
def LinRangeReverse : Prop :=
  ∀ [JPrint F64] (a b : F64) (n i : JInt64) (r rr : LinRange F64 JInt64),
    LinRange_start_stop_len a b n = .ok r → _reverse_LinRange r ⟨⟩ = .ok rr → 1 ≤ i.val → i.val ≤ n.val →
    _getindex_AbstractRange rr i = _getindex_AbstractRange r (lit .i64 (n.val + 1 - i.val))

theorem linRangeReverse_refuted : ¬ LinRangeReverse := by
  intro h
  have := @h somePrintF64 (f64 0) (f64 4607182418800017408) (lit .i64 4) (lit .i64 2)
    ⟨f64 0, f64 4607182418800017408, lit .i64 4, lit .i64 3⟩
    ⟨f64 4607182418800017408, f64 0, lit .i64 4, lit .i64 3⟩
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
  revert this; decide +kernel

/-- `LinRange(a, b, n)` of `Float64`s with `a < b` is nondecreasing: `r[i] <= r[i+1]`. -/
def LinRangeMonotone : Prop :=
  ∀ [JPrint F64] (a b : F64) (n i : JInt64) (r : LinRange F64 JInt64) (x y : F64),
    JLt.lt a b = true → LinRange_start_stop_len a b n = .ok r → 1 ≤ i.val → i.val < n.val →
    _getindex_AbstractRange r i = .ok x → _getindex_AbstractRange r (lit .i64 (i.val + 1)) = .ok y →
    JLe.le x y = true

theorem linRangeMonotone_refuted : ¬ LinRangeMonotone := by
  intro h
  have := @h somePrintF64 (f64 4633942850007099402) (f64 4633942850007099536) (lit .i64 283) (lit .i64 8)
    ⟨f64 4633942850007099402, f64 4633942850007099536, lit .i64 283, lit .i64 282⟩
    (f64 4633942850007099406) (f64 4633942850007099405)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- For a `Float64` `LinRange(a, b, n)` with non-NaN endpoints and `n >= 2`, `r[1] == first(r)`
and `r[n] == last(r)`. -/
def LinRangeEndpoints : Prop :=
  ∀ [JPrint F64] (a b : F64) (n : JInt64) (r : LinRange F64 JInt64),
    JuliaLean.base.float.isnan_IEEEFloat a = false → JuliaLean.base.float.isnan_IEEEFloat b = false →
    2 ≤ n.val → LinRange_start_stop_len a b n = .ok r →
    ((_getindex_AbstractRange r (lit .i64 1)).map fun x => JEq.eq x (first_LinRange r)) = .ok true ∧
    ((_getindex_AbstractRange r n).map fun x => JEq.eq x (last_LinRange r)) = .ok true

theorem linRangeEndpoints_refuted : ¬ LinRangeEndpoints := by
  intro h
  have := (@h somePrintF64 (f64 0) (f64 9218868437227405312) (lit .i64 3) ⟨f64 0, f64 9218868437227405312, lit .i64 3, lit .i64 2⟩
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)).1
  revert this; decide +kernel

/-- `cmp(r1, r2)` of two `Float64` `StepRangeLen`s is `0` only when their elements are equal. -/
def StepRangeLenCmp : Prop :=
  ∀ (a1 s1 a2 s2 : F64) (n : JInt64) (r1 r2 : StepRangeLen F64 F64 F64 JInt64) (fuel : Nat) (x1 x2 : List F64),
    JStepRangeLen3.stepRangeLen a1 s1 n = .ok r1 → JStepRangeLen3.stepRangeLen a2 s2 n = .ok r2 →
    cmp_T_T_AbstractRange r1 r2 = .ok (lit .i64 0) → iterList r1 fuel = .ok x1 → iterList r2 fuel = .ok x2 →
    x1 = x2

theorem stepRangeLenCmp_refuted : ¬ StepRangeLenCmp := by
  intro h
  have := h (f64 0) (f64 4591870180066957722) (f64 0) (f64 4591870180066957723) (lit .i64 4)
    ⟨f64 0, f64 4591870180066957722, lit .i64 4, lit .i64 1⟩ ⟨f64 0, f64 4591870180066957723, lit .i64 4, lit .i64 1⟩
    5 ([f64 0, f64 4591870180066957722, f64 4596373779694328218, f64 4599075939470750516])
    ([f64 0, f64 4591870180066957723, f64 4596373779694328219, f64 4599075939470750516])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- `UnitRange(a, b)` of `Float64`s with `a <= b` has `last(r) <= b`. -/
def FloatUnitRangeLast : Prop :=
  ∀ (a b : F64) (r : UnitRange F64) (l : F64), JLe.le a b = true → UnitRange_T_T a b = .ok r →
    last_OrdinalRange r = .ok l → JLe.le l b = true

theorem floatUnitRangeLast_refuted : ¬ FloatUnitRangeLast := by
  intro h
  have := h (f64 4604480259023595110) (f64 4615514078110652825)
    ⟨f64 4604480259023595110, JuliaLean.base.float.add_IEEEFloat (f64 4604480259023595110) (f64 4613937818241073152)⟩
    (JuliaLean.base.float.add_IEEEFloat (f64 4604480259023595110) (f64 4613937818241073152))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-- Every in-bounds element `r[i]` of `LinRange(a:s:b)` built from an `Int` step range can be
read. -/
def IntLinRangeElements : Prop :=
  ∀ (a s b : JInt64) (r : StepRange JInt64 JInt64) (lr : LinRange JInt64 JInt64) (i : JInt64),
    colon_T_T_T_Real a s b = .ok r → LinRange_AbstractRange r = .ok lr → 1 ≤ i.val → i.val ≤ lr.len.val →
    ∃ x, _getindex_AbstractRange lr i = .ok x

theorem intLinRangeElements_refuted : ¬ IntLinRangeElements := by
  intro h
  obtain ⟨x, hx⟩ := h (lit .i64 (-90)) (lit .i64 60) (lit .i64 90) ⟨lit .i64 (-90), lit .i64 60, lit .i64 90⟩
    ⟨lit .i64 (-90), lit .i64 90, lit .i64 4, lit .i64 3⟩ (lit .i64 2) (by decide) (by decide +kernel)
    (by decide) (by decide)
  have he : _getindex_AbstractRange (⟨lit .i64 (-90), lit .i64 90, lit .i64 4, lit .i64 3⟩ : LinRange JInt64 JInt64)
      (lit .i64 2) = .error (.jl (.inexactError "Int64")) := by decide +kernel
  cases hx.symm.trans he

/-- `show(io, r::LogRange)` writes text that starts with the qualified name `Base.LogRange{`
(as `repr(Base.OneTo(3))` starts with `Base.OneTo(`), whatever the element printing. -/
def LogRangeShowQualified : Prop :=
  ∀ (X : Type) [JShowType F64] [JShowTypeinfo F64 F64] [JShow JInt64] (r : LogRange F64 X) (s : String),
    show_LogRange ⟨⟩ r = .ok s → s.startsWith "Base.LogRange{" = true

theorem logRangeShowQualified_refuted : ¬ LogRangeShowQualified := by
  intro h
  unfold LogRangeShowQualified at h
  have := @h Unit ⟨"Float64"⟩ ⟨fun _ => pure "1.0"⟩ ⟨fun n => pure (toString n.val)⟩
    ⟨f64 4607182418800017408, f64 4616189618054758400, lit .i64 5, ((), ())⟩
    "LogRange{Float64}(1.0, 1.0, 5)" (by decide +kernel)
  revert this; decide +kernel


open JuliaLean.Registry

/-! ## Element specifications of integer ranges

`a:b`, `OneTo(n)` and their queries, specified by the integers iteration visits. Value lemmas for
the world's `checked_add`/`checked_sub`, `min`/`max` and mixed-type arithmetic come first. -/

open JuliaLean.base.int (add sub binop remT jmax jmin)
open JuliaLean.C (toJInt fromJInt)


section Mixed
variable {s t : IntTy}

theorem binop_val (op : {r : IntTy} → JInt r → JInt r → JInt r)
    (hop : ∀ {r : IntTy} (a b : JInt r), (op a b).val = wrapInt r (a.val + b.val))
    (x : JInt s) (y : JInt t) : (binop op x y).val = wrapInt (s.promote t) (x.val + y.val) := by
  unfold binop JuliaLean.base.int.op_Integer
  split <;> simp only [hop, IntVal.remT_val, IntVal.wrapInt_add_left, IntVal.wrapInt_add_right]

theorem binop_val_sub (op : {r : IntTy} → JInt r → JInt r → JInt r)
    (hop : ∀ {r : IntTy} (a b : JInt r), (op a b).val = wrapInt r (a.val - b.val))
    (x : JInt s) (y : JInt t) : (binop op x y).val = wrapInt (s.promote t) (x.val - y.val) := by
  unfold binop JuliaLean.base.int.op_Integer
  split <;> simp only [hop, IntVal.remT_val, IntVal.wrapInt_sub_left, IntVal.wrapInt_sub_right]

@[simp] theorem addMixed_iv (x : JInt s) (y : JInt t) :
    (x + y : JInt (pTy s t)).val = wrapInt (pTy s t) (x.val + y.val) := by
  show (castJ _ (binop add x y)).val = _
  rw [castJ_val, binop_val add (fun a b => IntVal.add_int_val a b), pTy_eq]

@[simp] theorem subMixed_iv (x : JInt s) (y : JInt t) :
    (x - y : JInt (pTy s t)).val = wrapInt (pTy s t) (x.val - y.val) := by
  show (castJ _ (binop sub x y)).val = _
  rw [castJ_val, binop_val_sub sub (fun a b => IntVal.sub_int_val a b), pTy_eq]

@[simp] theorem jint0_val : (jint 0).val = 0 := by decide
@[simp] theorem jint1_val : (jint 1).val = 1 := by decide

/-- `r[i]` of a `UnitRange` with a nonpositive index of any BitInteger type throws
`BoundsError`. -/
theorem getindex_unit_nonpos (r : UnitRange (JInt t)) (i : JInt s) (hi : i.val ≤ 0) :
    (JGetindex.getindex r i : JlX (JInt t)) = .error (.jl .boundsError) := by
  simp [JGetindex.getindex, _getindex_UnitRange_OverflowSafe, _in_unit_range,
    JThrowBoundserror.throwBoundserror, bind, Except.bind, show ¬ (0 < i.val) by omega, throw,
    throwThe, MonadExceptOf.throw]

end Mixed

section UnitLen
variable {t : IntTy}

/-- The number of integers `a, ..., b`: `b - a + 1`, or `0` when `b < a`. -/
def cnt (a b : Int) : Int := if a ≤ b then b - a + 1 else 0

theorem unitStop_val (a b : JInt t) :
    (unitStop a b).val = if a.val ≤ b.val then b.val else a.val - 1 := by
  unfold unitStop; split <;> simp_all

theorem convert_wide {s t : IntTy} (x : JInt s) (h : t.min ≤ s.min ∧ s.max ≤ t.max) :
    (JConvert.convert x : JlX (JInt t)) = .ok ⟨x.val, by have := x.property; omega⟩ := by
  rw [convert_iv, dite_cond_eq_true (eq_true (by have := x.property; omega))]

@[simp] theorem coreAdd_val {t : IntTy} (x y : JInt t) :
    (@HAdd.hAdd (JInt t) (JInt t) (JInt t) (@instHAdd (JInt t) _) x y).val = wrapInt t (x.val + y.val) := rfl
@[simp] theorem coreSub_val {t : IntTy} (x y : JInt t) :
    (@HSub.hSub (JInt t) (JInt t) (JInt t) (@instHSub (JInt t) _) x y).val = wrapInt t (x.val - y.val) := rfl
@[simp] theorem coreMul_val {t : IntTy} (x y : JInt t) :
    (@HMul.hMul (JInt t) (JInt t) (JInt t) (@instHMul (JInt t) _) x y).val = wrapInt t (x.val * y.val) := rfl
@[simp] theorem coreNeg_val {t : IntTy} (x : JInt t) : (-x).val = wrapInt t (-x.val) := rfl
@[simp] theorem jint_val (n : Int) : (jint n).val = wrapInt .i64 n := rfl

theorem checkindexOneTo_iff {t : IntTy} (last i : JInt t) (h0 : 0 ≤ last.val) :
    JuliaLean.base.abstractarray.checkindexOneTo last i = decide (1 ≤ i.val ∧ i.val ≤ last.val) := by
  have hl := last.property; have hi := i.property
  unfold JuliaLean.base.abstractarray.checkindexOneTo
  simp only [JInt.rem, JInt.wrap, coreSub_val, JInt.lit]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  cases t <;> simp [wrapInt, IntTy.toUnsigned, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at hl hi ⊢ <;>
    omega

/-- For a range whose length `n` is nonnegative, `checkbounds(r, i)` succeeds exactly for
`1 <= i <= n` (`checkboundsLinear`). -/
theorem checkboundsVector_eq {R : Type} {L : IntTy} [JLength R (JInt L)] {s : IntTy} (r : R) (i : JInt s)
    (n : JInt L) (hr : JLength.length r = .ok n) (h0 : 0 ≤ n.val) :
    checkboundsVector r i = checkboundsLinear r i := by
  have hc : checkindexAxis (⟨n⟩ : OneTo (JInt L)) i = .ok (decide (1 ≤ i.val ∧ i.val ≤ n.val)) := by
    unfold checkindexAxis
    split
    · rename_i h
      subst h
      rw [checkindexOneTo_iff _ _ h0]; rfl
    · simp [JuliaLean.base.abstractarray.checkindexReal, toArr, JFirst.first, JLast.last,
        last_OrdinalRange, JFieldStop.stop, le_iv, bind, Except.bind, pure, Except.pure, first_OneTo,
        oneunit_iv]
  simp only [checkboundsVector, checkboundsLinear, JuliaLean.base.abstractarray.checkboundsOne,
    JuliaLean.base.abstractarray.eachindexLinearVector, JuliaLean.base.abstractarray.axes1,
    size_AbstractRange, hr, toArr, bind, Except.bind, pure, Except.pure,
    JuliaLean.base.abstractarray.tupleGet, JuliaLean.base.abstractarray.int, JInt.lit, JInt.wrap]
  have h1 : wrapInt .i64 1 = 1 := by decide
  simp only [h1, show ¬ ((1 : Int) < 1) by decide, ite_false, show ((1 : Int) - 1).toNat = 0 by decide,
    List.getElem?_cons_zero, unchecked_oneto, hc, ofArr]
  by_cases h : 1 ≤ i.val ∧ i.val ≤ n.val <;>
    simp [h, JThrowBoundserror.throwBoundserror, throw, throwThe, MonadExceptOf.throw]

/-- `checkbounds` of a `LogRange` with a nonnegative length is `checkboundsLinear`. -/
theorem checkbounds_logRange {X : Type} (a b : F64) (n : JInt64) (ex : X × X) (i : JInt64) (h0 : 0 ≤ n.val) :
    checkboundsVector (⟨a, b, n, ex⟩ : LogRange F64 X) i = checkboundsLinear (⟨a, b, n, ex⟩ : LogRange F64 X) i :=
  checkboundsVector_eq _ i n rfl h0

theorem bounds_num (t : IntTy) (x : JInt t) :
    (if t.signed then -(2 ^ (t.bits - 1) : Int) else 0) ≤ x.val ∧
    x.val ≤ (if t.signed then (2 ^ (t.bits - 1) : Int) - 1 else (2 ^ t.bits : Int) - 1) := x.property

theorem lengthUnit_colon (a b : JInt t) :
    (lengthUnit (⟨a, unitStop a b⟩ : UnitRange (JInt t))).map Subtype.val =
      .ok (wrapInt (lenTy t) (cnt a.val b.val)) := by
  have ha := bounds_num t a; have hb := bounds_num t b
  have hs := unitStop_val a b
  generalize unitStop a b = s at hs
  have hsp := bounds_num t s
  cases t <;>
    simp (disch := decide) only [lengthUnit, length_AbstractUnitRange_smallints, length_AbstractUnitRange,
      JLast.last, JFirst.first, last_OrdinalRange, first_OrdinalRange, JFieldStart.start,
      JFieldStop.stop, ctor_iv, convert_self, convert_wide, bind, Except.bind, pure, Except.pure] <;>
    simp [Except.map, JInteger.integer, pure, Except.pure, JType.isSigned, IntTy.signed, cnt] at * <;>
    (by_cases hab : a.val ≤ b.val <;> by_cases h2 : a.val ≤ s.val <;> (try omega) <;>
      simp [hab, h2] at * <;>
      simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at * <;> omega)

/-! ### Checked arithmetic -/

private theorem flag_signed {t : IntTy} (hs : t.signed = true) (n : Int) :
    (n < -(2 ^ (t.bits - 1) : Nat) || n ≥ (2 ^ (t.bits - 1) : Nat)) =
      decide (¬ (t.min ≤ n ∧ n ≤ t.max)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

private theorem flag_unsigned {t : IntTy} (hu : t.signed = false) (n : Int) :
    (n < 0 || n ≥ (2 ^ t.bits : Nat)) = decide (¬ (t.min ≤ n ∧ n ≤ t.max)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

/-- The `checked_*_int` intrinsics on `JInt t` values: the wrapped result and the range flag. -/
theorem checkedInteger_jint (x y : JInt t) (op : Int → Int → Int) :
    toJInt t (JuliaLean.C.checkedInteger t.signed op (fromJInt x) (fromJInt y)).1 =
      JInt.wrap t (op x.val y.val) ∧
    (JuliaLean.C.checkedInteger t.signed op (fromJInt x) (fromJInt y)).2 =
      decide (¬ (t.min ≤ op x.val y.val ∧ op x.val y.val ≤ t.max)) := by
  cases hs : t.signed
  · have hf := flag_unsigned hs (op x.val y.val)
    simp only [JuliaLean.C.checkedInteger, Bool.false_eq_true, ↓reduceIte,
      IntVal.fromJInt_toNat_unsigned x hs, IntVal.fromJInt_toNat_unsigned y hs]
    refine ⟨Subtype.ext ?_, by simpa using hf⟩
    simp [JInt.wrap, IntVal.toJInt_ofInt_val]
  · have hf := flag_signed hs (op x.val y.val)
    simp only [JuliaLean.C.checkedInteger, ↓reduceIte, IntVal.fromJInt_toInt x hs,
      IntVal.fromJInt_toInt y hs]
    refine ⟨Subtype.ext ?_, by simpa using hf⟩
    simp [JInt.wrap, IntVal.toJInt_ofInt_val]

theorem checkedSub_spec (x y : JInt t) :
    (∀ h : t.min ≤ x.val - y.val ∧ x.val - y.val ≤ t.max,
      (JCheckedSub.checkedSub x y : JlX (JInt t)) = .ok ⟨x.val - y.val, h⟩) ∧
    (¬ (t.min ≤ x.val - y.val ∧ x.val - y.val ≤ t.max) →
      ∃ msg, (JCheckedSub.checkedSub x y : JlX (JInt t)) = .error (.jl (.overflowError msg))) := by
  obtain ⟨h1, h2⟩ := checkedInteger_jint x y (· - ·)
  show (∀ h, liftJl (JuliaLean.base.checked.checkedSubBits x y) = _) ∧
    (_ → ∃ msg, liftJl (JuliaLean.base.checked.checkedSubBits x y) = _)
  unfold JuliaLean.base.checked.checkedSubBits JuliaLean.base.checked.checkedSubSame
  by_cases hs : t.signed = true
  · simp only [hs, dite_true, JuliaLean.base.checked.subWithOverflowSigned,
      JuliaLean.C.jlCheckedSsubInt] at h1 h2 ⊢
    rw [h1, h2]
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · simp [hf, JInt.wrap, wrapInt_of_inRange t _ hf]
    · simp [hf, JuliaLean.base.checked.throwOverflowBinary]
  · have hu : t.signed = false := by simpa using hs
    simp only [hu, Bool.false_eq_true, dite_false, JuliaLean.base.checked.subWithOverflowUnsigned,
      JuliaLean.C.jlCheckedUsubInt] at h1 h2 ⊢
    rw [h1, h2]
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · simp [hf, JInt.wrap, wrapInt_of_inRange t _ hf]
    · simp [hf, JuliaLean.base.checked.throwOverflowBinary]

theorem checkedAdd_spec (x y : JInt t) :
    (∀ h : t.min ≤ x.val + y.val ∧ x.val + y.val ≤ t.max,
      (JCheckedAdd.checkedAdd x y : JlX (JInt t)) = .ok ⟨x.val + y.val, h⟩) ∧
    (¬ (t.min ≤ x.val + y.val ∧ x.val + y.val ≤ t.max) →
      ∃ msg, (JCheckedAdd.checkedAdd x y : JlX (JInt t)) = .error (.jl (.overflowError msg))) := by
  obtain ⟨h1, h2⟩ := checkedInteger_jint x y (· + ·)
  show (∀ h, liftJl (JuliaLean.base.checked.checkedAddBits x y) = _) ∧
    (_ → ∃ msg, liftJl (JuliaLean.base.checked.checkedAddBits x y) = _)
  unfold JuliaLean.base.checked.checkedAddBits JuliaLean.base.checked.checkedAddSame
  by_cases hs : t.signed = true
  · simp only [hs, dite_true, JuliaLean.base.checked.addWithOverflowSigned,
      JuliaLean.C.jlCheckedSaddInt] at h1 h2 ⊢
    rw [h1, h2]
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · simp [hf, JInt.wrap, wrapInt_of_inRange t _ hf]
    · simp [hf, JuliaLean.base.checked.throwOverflowBinary]
  · have hu : t.signed = false := by simpa using hs
    simp only [hu, Bool.false_eq_true, dite_false, JuliaLean.base.checked.addWithOverflowUnsigned,
      JuliaLean.C.jlCheckedUaddInt] at h1 h2 ⊢
    rw [h1, h2]
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · simp [hf, JInt.wrap, wrapInt_of_inRange t _ hf]
    · simp [hf, JuliaLean.base.checked.throwOverflowBinary]

/-- `r` returns the count `n` when it fits in `L`, and throws `OverflowError` otherwise. -/
def CountOrOverflow {L : IntTy} (r : JlX (JInt L)) (n : Int) : Prop :=
  if L.min ≤ n ∧ n ≤ L.max then r.map Subtype.val = .ok n
  else ∃ msg, r = .error (.jl (.overflowError msg))

theorem checkedLenAUR (a b s : JInt t) (hs : s.val = if a.val ≤ b.val then b.val else a.val - 1) :
    CountOrOverflow ((checked_length_AbstractUnitRange (⟨a, s⟩ : UnitRange (JInt t)) :
      JlX (JInt t ⊕ JInt t)).map (Sum.elim id id)) (cnt a.val b.val) := by
  have ha := a.property; have hb := b.property; have hsp := s.property
  have hmin := min_le_zero t
  unfold CountOrOverflow
  simp only [checked_length_AbstractUnitRange, JIsempty.isempty,
    isempty_AbstractUnitRange, JFirst.first, JLast.last, first_OrdinalRange, last_OrdinalRange,
    JFieldStart.start, JFieldStop.stop, convert_self, bind, Except.bind, pure, Except.pure, lt_iv]
  by_cases hab : a.val ≤ b.val
  · simp only [hab, ite_true] at hs
    simp only [show ¬ (s.val < a.val) by omega, decide_false, Bool.false_eq_true, ite_false]
    have hsub := checkedSub_spec s a
    by_cases h1 : t.min ≤ s.val - a.val ∧ s.val - a.val ≤ t.max
    · rw [hsub.1 h1]; dsimp only
      have hadd := checkedAdd_spec (⟨s.val - a.val, h1⟩ : JInt t) (JOneunit.oneunit)
      simp only [oneunit_iv] at hadd
      by_cases h2 : t.min ≤ s.val - a.val + 1 ∧ s.val - a.val + 1 ≤ t.max
      · rw [hadd.1 h2]; dsimp only
        rw [if_pos (by simp [cnt, hab]; omega)]
        simp [Except.map, JInteger.integer, cnt, hab, pure, Except.pure]; omega
      · obtain ⟨msg, hm⟩ := hadd.2 h2
        rw [hm, if_neg (by simp [cnt, hab]; omega)]
        exact ⟨msg, rfl⟩
    · obtain ⟨msg, hm⟩ := hsub.2 h1
      rw [hm, if_neg (by simp [cnt, hab]; omega)]
      exact ⟨msg, rfl⟩
  · have hsa : s.val = a.val - 1 := by simp [hab] at hs; exact hs
    simp only [show s.val < a.val by omega, decide_true, ite_true]
    rw [if_pos (by simp [cnt, hab]; have := zero_lt_max t; have := min_le_zero t; omega)]
    simp [Except.map, JInteger.integer, cnt, hab, pure, Except.pure]
    exact wrap_in t (min_le_zero t) (by have := zero_lt_max t; omega)

theorem checkedLengthUnit_colon (a b : JInt t) :
    CountOrOverflow (checkedLengthUnit (⟨a, unitStop a b⟩ : UnitRange (JInt t))) (cnt a.val b.val) := by
  have hl := lengthUnit_colon a b
  have ha := bounds_num t a; have hb := bounds_num t b
  have hs := unitStop_val a b
  generalize unitStop a b = s at hs hl
  have hsp := bounds_num t s
  cases t
  case i64 | i128 | u64 | u128 => exact checkedLenAUR a b s hs
  all_goals
    unfold CountOrOverflow
    simp only [checkedLengthUnit, checked_length_AbstractUnitRange_smallints, JLength.length]
    rw [if_pos (by simp [cnt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, lenTy] at *; split <;> omega), hl]
    simp [cnt, wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, lenTy] at *
    split <;> omega

/-- `r[i]` of `a:b` at an `Int` index. -/
theorem getindex_unit_int (a b : JInt t) (i : JInt64) :
    (JGetindex.getindex (⟨a, unitStop a b⟩ : UnitRange (JInt t)) i : JlX (JInt t)).map Subtype.val =
      if 1 ≤ i.val ∧ i.val ≤ cnt a.val b.val then .ok (a.val + i.val - 1)
      else .error (.jl .boundsError) := by
  have ha := bounds_num t a; have hb := bounds_num t b; have hi := bounds_num .i64 i
  have hs := unitStop_val a b
  generalize unitStop a b = s at hs
  have hsp := bounds_num t s
  by_cases hpos : i.val ≤ 0
  · rw [getindex_unit_nonpos _ i hpos, if_neg (by omega)]; rfl
  cases t <;>
    simp [JGetindex.getindex, _getindex_UnitRange_OverflowSafe, _in_unit_range,
      JThrowBoundserror.throwBoundserror, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
      show 0 < i.val by omega, cnt, pure, Except.pure] <;>
    (by_cases hab : a.val ≤ b.val <;> simp [hab] at hs <;> rw [hs] <;>
      (rw [apply_ite (Except.map Subtype.val)] <;>
        split <;> rename_i hc <;> split <;> rename_i hd <;>
        simp [hab, remType_iv, Except.map] at hc hd ⊢ <;>
        simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, pTy] at * <;> omega))


/-! ### The unit range `a:b` -/

theorem cnt_eq_length (a b : Int) : cnt a b = ((intsFromTo a b).length : Int) := by
  rw [intsFromTo_length]; unfold cnt; split <;> omega

/-- `a:b` for integers `a`, `b` of one BitInteger type `T` (`(:)(start::T, stop::T)`, range.jl:5,
which is `UnitRange{T}(start, stop)`, range.jl:428) is "filled with elements spaced by `1` from
`start` until `stop` is exceeded" (UnitRange docstring, range.jl:409-411): its elements are the
integers `a, a+1, ..., b`, its first element is `a` and its last element is `b`, or `a - 1` when
the range is empty. -/
def UnitRangeColon : Prop :=
  ∀ (t : IntTy) (a b : JInt t), ∃ r : UnitRange (JInt t), JColon2.colon a b = .ok r ∧
    UnitRange_T_new a b = .ok r ∧ UnitRange_T_T a b = .ok r ∧
    (JFirst.first r).map Subtype.val = .ok a.val ∧
    (JLast.last r).map Subtype.val = .ok (if a.val ≤ b.val then b.val else a.val - 1) ∧
    JIsempty.isempty r = .ok (decide (b.val < a.val)) ∧
    (JStep.step r).map Subtype.val = .ok 1 ∧
    (∀ fuel, (b.val - a.val).toNat < fuel → iterVals r fuel = .ok (intsFromTo a.val b.val)) ∧
    (JLength.length r).map Subtype.val = .ok (wrapInt (lenTy t) (intsFromTo a.val b.val).length) ∧
    CountOrOverflow (JCheckedLength.checkedLength r) (intsFromTo a.val b.val).length ∧
    (∀ i : JInt64, (JGetindex.getindex r i).map Subtype.val =
      if 1 ≤ i.val ∧ i.val ≤ (intsFromTo a.val b.val).length then .ok (a.val + i.val - 1)
      else .error (.jl .boundsError))

theorem unitRangeColon_proven : UnitRangeColon := by
  intro t a b
  refine ⟨⟨a, unitStop a b⟩, colon_unit a b, colon_unit a b, colon_unit a b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Except.map]
  · simp [Except.map, unitStop_val]
  · simp [unitStop_val]; split <;> omega
  · obtain ⟨s, hs, h1⟩ := step_unit (⟨a, unitStop a b⟩ : UnitRange (JInt t))
    simp [hs, Except.map, h1]
  · intro fuel hf
    have := iterList_unit (⟨a, unitStop a b⟩ : UnitRange (JInt t)) fuel
      (by simp only [unitStop_val]; split <;> omega)
    simp only [unitStop_val] at this
    unfold iterVals; rw [this]
    split
    · rfl
    · rw [intsFromTo_empty (by omega), intsFromTo_empty (by omega)]
  · rw [← cnt_eq_length]; exact lengthUnit_colon a b
  · rw [← cnt_eq_length]; exact checkedLengthUnit_colon a b
  · intro i; rw [← cnt_eq_length]; exact getindex_unit_int a b i

/-- `r[i]` of a `UnitRange` of any BitInteger type with a nonpositive integer index of any
BitInteger type throws `BoundsError` (`_getindex(v::UnitRange{T}, i::Integer)`, range.jl:968, and
`checkbounds`: the valid indices of a vector are `1:length(v)`). -/
def UnitRangeNonposIndex : Prop :=
  ∀ (t s : IntTy) (r : UnitRange (JInt t)) (i : JInt s), i.val ≤ 0 →
    (JGetindex.getindex r i : JlX (JInt t)) = .error (.jl .boundsError)

theorem unitRangeNonposIndex_proven : UnitRangeNonposIndex :=
  fun _ _ r i hi => getindex_unit_nonpos r i hi

end UnitLen
section OneToSpec
variable {t : IntTy}


theorem promote_self (t : IntTy) : t.promote t = t := by cases t <;> rfl
theorem minType_self (t : IntTy) : JuliaLean.base.int.minType t t = t := by cases t <;> rfl

theorem max_same (x y : JInt t) :
    (JMax.max x y : JlX (JInt t)) = .ok (if y.val < x.val then x else y) := by
  show pure (remT t (jmax x y)) = _
  congr 1; apply Subtype.ext
  simp only [jmax, JuliaLean.base.int.ifelse, IntVal.remT_val, IntVal.lt_eq]
  have hp : ∀ z, wrapInt (t.promote t) z = wrapInt t z := fun z => by rw [promote_self]
  by_cases h : y.val < x.val <;> simp [h, IntVal.remT_val, IntVal.wrapInt_val, hp]

theorem min_same (x y : JInt t) :
    (JMin.min x y : JlX (JInt t)) = .ok (if y.val < x.val then y else x) := by
  show pure (remT t (jmin x y)) = _
  congr 1; apply Subtype.ext
  simp only [jmin, JuliaLean.base.int.ifelse, IntVal.remT_val,
    JuliaLean.base.int.promoteSameSign, IntVal.ltSame_eq]
  have hp : ∀ z, wrapInt (t.promote t) z = wrapInt t z := fun z => by rw [promote_self]
  have hm : ∀ z, wrapInt (JuliaLean.base.int.minType t t) z = wrapInt t z := fun z => by
    rw [minType_self]
  by_cases h : y.val < x.val <;> simp [h, IntVal.remT_val, IntVal.wrapInt_val, IntVal.widenTo_val,
    hp, hm, IntVal.wrapInt_wrapInt]


/-- The stop that `OneTo(n)` stores: `max(0, n)`. -/
def oneToStop (n : JInt t) : JInt t := if n.val < 0 then (JZero.zero : JInt t) else n

theorem oneToStop_val (n : JInt t) : (oneToStop n).val = max 0 n.val := by
  unfold oneToStop; split <;> simp_all <;> omega

theorem oneTo_ok (n : JInt t) : JOneTo1.oneTo n = .ok (⟨oneToStop n⟩ : OneTo (JInt t)) := by
  show OneTo_T_stop (T := JInt t) n = _
  unfold OneTo_T_stop
  rw [max_same (t := t)]
  simp only [JType.isBool, Bool.false_eq_true, ite_false, zero_iv, bind, Except.bind, pure,
    Except.pure, oneToStop]

@[simp] theorem first_oneTo (r : OneTo (JInt t)) : JFirst.first r = .ok JOneunit.oneunit := rfl
@[simp] theorem last_oneTo (r : OneTo (JInt t)) : JLast.last r = .ok r.stop := by
  simp [JLast.last, last_OrdinalRange, JFieldStop.stop]
@[simp] theorem isempty_oneTo (r : OneTo (JInt t)) :
    JIsempty.isempty r = .ok (decide (r.stop.val < 1)) := by
  simp [JIsempty.isempty, isempty_AbstractUnitRange, bind, Except.bind, pure, Except.pure]

theorem stepOneTo_val (r : OneTo (JInt t)) : (step_AbstractUnitRange r : JInt t).val = 1 := by
  simp [step_AbstractUnitRange]; exact wrap_in t (by have := min_le_zero t; omega) (zero_lt_max t)

theorem iterate2_oneTo (r : OneTo (JInt t)) (i : JInt t) (hi : i.val < r.stop.val) :
    ∃ j : JInt t, JIterate2.iterate r i = .ok (some (j, j)) ∧ j.val = i.val + 1 := by
  simp only [JIterate2.iterate, iterate_OrdinalRange_state, last_oneTo, eq_iv]
  simp only [bind, Except.bind, show i.val ≠ r.stop.val by omega, decide_false,
    Bool.false_eq_true, ite_false]
  refine ⟨i + step_AbstractUnitRange r, ?_, ?_⟩
  · show (do let next ← JConvert.convert (i + step_AbstractUnitRange r); pure (some (next, next))) = _
    simp [convert_self, pure, Except.pure]; rfl
  · simp only [add_iv, stepOneTo_val]
    have := r.stop.property; have := i.property
    exact wrap_in t (by omega) (by omega)

theorem iterate2_oneTo_last (r : OneTo (JInt t)) (i : JInt t) (hi : i.val = r.stop.val) :
    JIterate2.iterate r i = .ok none := by
  simp [JIterate2.iterate, iterate_OrdinalRange_state, hi, bind, Except.bind, pure, Except.pure]

theorem iterFrom_oneTo (r : OneTo (JInt t)) : ∀ (fuel : Nat) (i : JInt t),
    i.val ≤ r.stop.val → (r.stop.val - i.val).toNat < fuel →
    (iterFrom r fuel i).map vals = .ok (intsFromTo (i.val + 1) r.stop.val)
  | 0, _, _, h => by omega
  | fuel + 1, i, hle, hf => by
    by_cases heq : i.val = r.stop.val
    · simp [iterFrom, iterate2_oneTo_last r i heq, bind, Except.bind, pure, Except.pure,
        Except.map, intsFromTo_empty (show r.stop.val < i.val + 1 by omega)]
    · have hlt : i.val < r.stop.val := by omega
      obtain ⟨j, hj, hjv⟩ := iterate2_oneTo r i hlt
      have ih := iterFrom_oneTo r fuel j (by omega) (by omega)
      rw [hjv] at ih
      simp only [iterFrom, hj, bind, Except.bind]
      rw [intsFromTo_cons (show i.val + 1 ≤ r.stop.val by omega)]
      revert ih
      cases iterFrom r fuel j <;> simp [Except.map, pure, Except.pure, hjv]

theorem iterList_oneTo (r : OneTo (JInt t)) (fuel : Nat) (h0 : 0 ≤ r.stop.val)
    (hf : r.stop.val.toNat < fuel) :
    (iterList r fuel).map vals = .ok (intsFromTo 1 r.stop.val) := by
  unfold iterList
  simp only [JIterate1.iterate, iterate_OrdinalRange, isempty_oneTo, first_oneTo, bind, Except.bind]
  by_cases h : r.stop.val < 1
  · simp [h, pure, Except.pure, Except.map, intsFromTo_empty h]
  · have ih := iterFrom_oneTo r fuel (JOneunit.oneunit : JInt t) (by simp; omega) (by simp; omega)
    simp only [oneunit_iv] at ih
    simp only [h, decide_false, Bool.false_eq_true, ite_false, pure, Except.pure]
    rw [intsFromTo_cons (show (1 : Int) ≤ r.stop.val by omega)]
    revert ih
    cases iterFrom r fuel (JOneunit.oneunit : JInt t) <;> simp [Except.map, pure, Except.pure]

theorem lengthOneTo_val (m : JInt t) (h0 : 0 ≤ m.val) :
    (lengthOneTo (⟨m⟩ : OneTo (JInt t))).map Subtype.val = .ok m.val := by
  have hm := bounds_num t m
  cases t <;>
    simp (disch := decide) only [lengthOneTo, length_OneTo_smallints, length_OneTo_bigints, ctor_iv,
      convert_wide, Except.map, pure, Except.pure]

theorem checkedLenAUR_oneTo (m : JInt t) (h0 : 0 ≤ m.val) :
    ((checked_length_AbstractUnitRange (⟨m⟩ : OneTo (JInt t)) : JlX (JInt t ⊕ JInt t)).map
      (Sum.elim id id)).map Subtype.val = .ok m.val := by
  have hm := m.property; have hmin := min_le_zero t; have hmax := zero_lt_max t
  simp only [checked_length_AbstractUnitRange, isempty_oneTo, first_oneTo, last_oneTo, bind,
    Except.bind, pure, Except.pure]
  by_cases h1 : m.val < 1
  · have hm0 : m.val = 0 := by omega
    simp only [h1, decide_true, ite_true]
    simp [Except.map, JInteger.integer, hm0, pure, Except.pure]
    exact wrap_in t hmin (by omega)
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false]
    have hsub := checkedSub_spec m (JOneunit.oneunit : JInt t)
    simp only [oneunit_iv] at hsub
    rw [hsub.1 ⟨by omega, by omega⟩]; dsimp only
    have hadd := checkedAdd_spec (⟨m.val - 1, by omega, by omega⟩ : JInt t) (JOneunit.oneunit)
    simp only [oneunit_iv] at hadd
    rw [hadd.1 ⟨by omega, by omega⟩]
    simp [Except.map, JInteger.integer, pure, Except.pure]

theorem checkedLengthOneTo_val (m : JInt t) (h0 : 0 ≤ m.val) :
    (checkedLengthOneTo (⟨m⟩ : OneTo (JInt t))).map Subtype.val = .ok m.val := by
  have hm := bounds_num t m
  have hl := lengthOneTo_val m h0
  cases t
  case i64 | i128 | u64 | u128 => exact checkedLenAUR_oneTo m h0
  all_goals exact hl


theorem getindex_oneTo_int (m : JInt t) (h0 : 0 ≤ m.val) (i : JInt64) :
    (JGetindex.getindex (⟨m⟩ : OneTo (JInt t)) i : JlX (JInt t)).map Subtype.val =
      if 1 ≤ i.val ∧ i.val ≤ m.val then .ok i.val else .error (.jl .boundsError) := by
  have hl := lengthOneTo_val m h0
  obtain ⟨n, hn, hnv⟩ : ∃ n, lengthOneTo (⟨m⟩ : OneTo (JInt t)) = .ok n ∧ n.val = m.val := by
    revert hl; cases lengthOneTo (⟨m⟩ : OneTo (JInt t)) <;> simp [Except.map]
  have hcb := checkboundsVector_eq (⟨m⟩ : OneTo (JInt t)) i n hn (by omega)
  simp only [JGetindex.getindex, _getindex_AbstractRange, JCheckbounds.checkbounds, hcb,
    checkboundsLinear, JLength.length, hn, bind, Except.bind]
  rw [hnv]
  by_cases hc : 1 ≤ i.val ∧ i.val ≤ m.val
  · simp only [hc, and_self, ite_true, JUnsafeGetindex.unsafeGetindex, unsafe_getindex_OneTo, pure,
      Except.pure]
    have := m.property; have := min_le_zero t
    rw [convert_ok (t := t) (x := i) (by omega) (by omega)]
    rfl
  · simp [hc, throw, throwThe, MonadExceptOf.throw]
    rfl

/-- `OneTo(n)` for an integer `n` of any BitInteger type is the range `1, 2, ..., n` of the same
type (docstring of `Base.OneTo`, range.jl:467-486: "Define an `AbstractUnitRange` that behaves
like `1:n`"; a negative `n` gives the empty range, stored as `OneTo(0)`): its first element is
`1`, its last `max(0, n)`, iteration visits `1, ..., n`, `length` is the number of elements,
and `r[i]` is `i` for `1 <= i <= n` and a `BoundsError` otherwise. -/
def OneToElements : Prop :=
  ∀ (t : IntTy) (n : JInt t), ∃ r : OneTo (JInt t), JOneTo1.oneTo n = .ok r ∧
    r.stop.val = max 0 n.val ∧
    (JFirst.first r).map Subtype.val = .ok 1 ∧
    (JLast.last r).map Subtype.val = .ok (max 0 n.val) ∧
    JIsempty.isempty r = .ok (decide (n.val < 1)) ∧
    (∀ fuel, n.val.toNat < fuel → iterVals r fuel = .ok (intsFromTo 1 n.val)) ∧
    (JLength.length r).map Subtype.val = .ok (intsFromTo 1 n.val).length ∧
    (JCheckedLength.checkedLength r).map Subtype.val = .ok (intsFromTo 1 n.val).length ∧
    (∀ i : JInt64, (JGetindex.getindex r i).map Subtype.val =
      if 1 ≤ i.val ∧ i.val ≤ n.val then .ok i.val else .error (.jl .boundsError))

theorem oneToElements_proven : OneToElements := by
  intro t n
  have hv := oneToStop_val n
  have hlen : ((intsFromTo 1 n.val).length : Int) = max 0 n.val := by
    rw [intsFromTo_length]; omega
  refine ⟨⟨oneToStop n⟩, oneTo_ok n, hv, by simp [Except.map], by simp [Except.map, hv], ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [hv]; omega
  · intro fuel hf
    have := iterList_oneTo (⟨oneToStop n⟩ : OneTo (JInt t)) fuel (by rw [hv]; omega)
      (by rw [hv]; omega)
    unfold iterVals; rw [this]; simp only [hv]
    by_cases h : 0 ≤ n.val
    · congr 2; omega
    · rw [intsFromTo_empty (by omega), intsFromTo_empty (by omega)]
  · rw [hlen, ← hv]; exact lengthOneTo_val _ (by rw [hv]; omega)
  · rw [hlen, ← hv]; exact checkedLengthOneTo_val _ (by rw [hv]; omega)
  · intro i
    rw [getindex_oneTo_int _ (by rw [hv]; omega), hv]
    by_cases hc : 1 ≤ i.val ∧ i.val ≤ n.val
    · rw [if_pos (by omega), if_pos hc]
    · rw [if_neg (by omega), if_neg hc]

end OneToSpec


end JuliaLean.Proofs.base.range

namespace JuliaLean.Proofs.base.range.IntVal

open JuliaLean JuliaLean.C JuliaLean.Promotion JuliaLean.base.int

theorem nonneg_of_unsigned {t : IntTy} (h : t.signed = false) (x : JInt t) : 0 ≤ x.val := by
  have := x.property; cases t <;> simp_all [IntTy.signed, IntTy.min]

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

theorem tmod_lit_val {t : IntTy} (x y : JInt t) : (lit t (x.val.tmod y.val)).val = x.val.tmod y.val := by
  have hx := x.property
  have hb := tmod_between x.val y.val
  rw [lit_val]; apply wrapInt_of_inRange
  generalize x.val.tmod y.val = r at hb ⊢
  by_cases h : 0 ≤ x.val
  · have := hb.1 h
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
  · have := hb.2 (by omega)
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega

theorem abs_val {t : IntTy} (x : JInt t) :
    (abs x).val = if t.signed = true ∧ x.val = t.min then t.min else (x.val.natAbs : Int) := by
  have hx := x.property
  cases h : t.signed
  · have h0 := nonneg_of_unsigned h x
    have e : JuliaLean.base.int.abs x = x := by unfold JuliaLean.base.int.abs; rw [h]; rfl
    rw [e]; simp only [Bool.false_eq_true, false_and, ite_false]
    omega
  · have e : JuliaLean.base.int.abs x = flipsign_int x x := by
      unfold JuliaLean.base.int.abs; rw [h]; rfl
    rw [e, flipsign_int_val h]
    simp only [true_and]
    by_cases hn : x.val < 0 <;> by_cases hm : x.val = t.min <;> simp only [hn, hm, ite_true, ite_false] <;>
      cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;> omega

/-- `unsigned(abs(y))` is `|y|` for every BitInteger `y` (including `typemin`). -/
theorem unsigned_abs_val {t : IntTy} (y : JInt t) : (unsigned (abs y)).val = (y.val.natAbs : Int) := by
  rw [unsigned_val, abs_val]
  have hy := y.property
  split
  · rename_i h
    obtain ⟨hs, hm⟩ := h
    rw [hm]
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.bits, IntTy.toUnsigned, wrapInt]
  · apply wrapInt_of_inRange
    cases hs : t.signed
    · cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, IntTy.toUnsigned] <;> omega
    · cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, IntTy.toUnsigned] <;> omega

end JuliaLean.Proofs.base.range.IntVal

namespace JuliaLean.Proofs.base.range
open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit remT remSame)

section StepLast
variable {t : IntTy}

/-- Same-type `rem(x, y)` with `y != 0` is the truncated remainder. -/
theorem rem_same_ok (x y : JInt t) (hy : y.val ≠ 0) :
    ∃ q : JInt t, (JRem.rem x y : JlX (JInt t)) = .ok q ∧ q.val = x.val.tmod y.val := by
  refine ⟨lit t (x.val.tmod y.val), ?_, IntVal.tmod_lit_val x y⟩
  show liftJl (remSame x y) = _
  rw [IntVal.remSame_eq, if_neg hy]; rfl

/-- `rem(x::unsigned(T), y::T)` with `y != 0` is `x` reduced modulo `|y|`. -/
theorem rem_us_ok (x : JInt t.toUnsigned) (y : JInt t) (hy : y.val ≠ 0) :
    ∃ q : JInt t.toUnsigned, (JRem.rem x y : JlX (JInt t.toUnsigned)) = .ok q ∧
      q.val = x.val.tmod (y.val.natAbs : Int) := by
  have hy' := IntVal.unsigned_abs_val y
  have hx := x.property
  by_cases hs : t.signed = true
  · simp only [JRem.rem, hs, ↓reduceIte, JuliaLean.base.int.rem_Unsigned_BitSigned,
      JuliaLean.base.int.Generic.rem_Unsigned_BitSigned, remPromoted]
    rw [IntVal.remSame_eq, if_neg (by
      rw [IntVal.remT_val, hy', wrapInt_of_inRange]
      · omega
      · have := y.property
        cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, IntTy.toUnsigned, IntTy.promote] <;> omega)]
    refine ⟨_, rfl, ?_⟩
    have hP : t.toUnsigned.promote t.toUnsigned = t.toUnsigned := promote_self _
    have hx0 : 0 ≤ x.val := IntVal.nonneg_of_unsigned (by cases t <;> rfl) x
    have hyU : wrapInt t.toUnsigned (y.val.natAbs : Int) = y.val.natAbs := by
      apply wrapInt_of_inRange
      have := y.property
      cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, IntTy.toUnsigned] <;> omega
    simp only [IntVal.remT_val, IntVal.lit_val, hy', hP, IntVal.wrapInt_val, hyU, IntVal.wrapInt_wrapInt]
    have hb := (IntVal.tmod_between x.val (y.val.natAbs : Int)).1 hx0
    exact wrapInt_of_inRange _ _ ⟨by have := min_le_zero t.toUnsigned; omega, by omega⟩
  · have hu : t.signed = false := by simpa using hs
    have hU : t.toUnsigned = t := by cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned]
    simp only [JRem.rem, hu, Bool.false_eq_true, ↓reduceIte]
    rw [IntVal.remSame_eq, if_neg (by
      rw [IntVal.remT_val, hU, IntVal.wrapInt_val]; exact hy)]
    refine ⟨_, rfl, ?_⟩
    have hy0 : 0 ≤ y.val := IntVal.nonneg_of_unsigned hu y
    have hyw : wrapInt t.toUnsigned y.val = y.val := by rw [hU]; exact IntVal.wrapInt_val y
    rw [IntVal.tmod_lit_val, IntVal.remT_val, hyw]
    congr 1; omega


@[simp] theorem rem_sum_inl {α β δ γ : Type} [JRem α β γ] [JRem α δ γ] (x : α) (y : β) :
    (JRem.rem x (Sum.inl y : β ⊕ δ) : JlX γ) = JRem.rem x y := rfl
@[simp] theorem rem_sum_inr {α β δ γ : Type} [JRem α β γ] [JRem α δ γ] (x : α) (y : δ) :
    (JRem.rem x (Sum.inr y : β ⊕ δ) : JlX γ) = JRem.rem x y := rfl

/-- The last element `steprange_last(a, s, b)` stores, as an integer. -/
def lastVal (a s b : Int) : Int :=
  if a = b then b
  else if (0 < s) ≠ (a < b) then (if 0 < s then a - 1 else a + 1)
  else if a < b then b - (b - a).tmod s
  else b + (a - b).tmod (-s)

theorem wrap_neg_cases {t : IntTy} (s : JInt t) (hs : s.val < 0) :
    wrapInt t (-s.val) = -s.val ∨ (wrapInt t (-s.val) = s.val ∧ s.val = t.min) := by
  have hp := s.property
  by_cases hm : s.val = t.min
  · right; refine ⟨?_, hm⟩
    have hsg : t.signed = true := by
      cases ht : t.signed
      · have := IntVal.nonneg_of_unsigned ht s; omega
      · rfl
    rw [hm]; cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.bits, wrapInt]
  · left; apply wrapInt_of_inRange
    have hsg : t.signed = true := by
      cases ht : t.signed
      · have := IntVal.nonneg_of_unsigned ht s; omega
      · rfl
    cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega

theorem tmod_wrap_neg {t : IntTy} (x : Int) (s : JInt t) (hs : s.val < 0) :
    x.tmod (wrapInt t (-s.val)) = x.tmod (-s.val) := by
  rcases wrap_neg_cases s hs with h | ⟨h, _⟩
  · rw [h]
  · rw [h, Int.tmod_neg]

theorem natAbs_wrap_neg {t : IntTy} (s : JInt t) (hs : s.val < 0) :
    ((wrapInt t (-s.val)).natAbs : Int) = -s.val := by
  rcases wrap_neg_cases s hs with h | ⟨h, _⟩ <;> rw [h] <;> omega

theorem steprange_last_ok (a s b : JInt t) (hs : s.val ≠ 0) :
    ∃ l : JInt t, (JSteprangeLast.steprangeLast a s b : JlX (JInt t)) = .ok l ∧
      l.val = lastVal a.val s.val b.val := by
  have ha := a.property; have hb := b.property; have hsp := s.property
  simp only [JSteprangeLast.steprangeLast, steprange_last, JType.isAbstractFloat, JType.isInteger,
    JIsinteger.isinteger, JuliaLean.base.number.isintegerInteger, Bool.or_false, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ite_false, eq_iv, zero_iv, lt_iv, hs, decide_false,
    JType.isSigned]
  have hmin := min_le_zero t; have hmax := zero_lt_max t
  by_cases hab : b.val = a.val
  · refine ⟨b, ?_, ?_⟩
    · simp [hab, pure, Except.pure, bind, Except.bind, convert_self]
    · simp [lastVal, hab]
  simp only [hab, decide_false, Bool.false_eq_true, ite_false]
  by_cases hdir : (0 < s.val) ≠ (a.val < b.val)
  · have hd : (decide (0 < s.val) != decide (a.val < b.val)) = true := by
      by_cases h1 : 0 < s.val <;> by_cases h2 : a.val < b.val <;> simp_all
    simp only [hd, ite_true, JSteprangeLastEmpty.steprangeLastEmpty, steprange_last_empty_Integer,
      zero_iv, lt_iv, convert_self, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
    by_cases hs0 : 0 < s.val
    · refine ⟨_, rfl, ?_⟩
      simp only [hs0, decide_true, ite_true, wrappingSub_iv, oneunit_iv]
      have hl : lastVal a.val s.val b.val = a.val - 1 := by
        unfold lastVal; rw [if_neg (by omega), if_pos hdir, if_pos hs0]
      have : b.val < a.val := by by_cases h : a.val < b.val <;> simp_all <;> omega
      rw [hl]; exact wrap_in t (by omega) (by omega)
    · refine ⟨_, rfl, ?_⟩
      simp only [hs0, decide_false, Bool.false_eq_true, ite_false, wrappingAdd_iv, oneunit_iv]
      have hl : lastVal a.val s.val b.val = a.val + 1 := by
        unfold lastVal; rw [if_neg (by omega), if_pos hdir, if_neg hs0]
      have : a.val < b.val := by by_cases h : a.val < b.val <;> simp_all
      rw [hl]; exact wrap_in t (by omega) (by omega)
  · have hd : (decide (0 < s.val) != decide (a.val < b.val)) = false := by
      by_cases h1 : 0 < s.val <;> by_cases h2 : a.val < b.val <;> simp_all <;> omega
    simp only [hd, Bool.false_eq_true, ite_false]
    have hlv : lastVal a.val s.val b.val =
        if a.val < b.val then b.val - (b.val - a.val).tmod s.val
        else b.val + (a.val - b.val).tmod (-s.val) := by
      simp only [lastVal, show a.val ≠ b.val by omega, ite_false]
      rw [if_neg (by simpa using hdir)]
    by_cases hlt : a.val < b.val
    · have hs0 : 0 < s.val := by by_cases h1 : 0 < s.val <;> simp_all
      simp only [hlt, decide_true, ite_true]
      have hd : (JRangeWrappingSub.rangeWrappingSub b a : JInt t).val = wrapInt t (b.val - a.val) :=
        wrappingSub_iv b a
      by_cases hov : t.signed = true ∧ wrapInt t (b.val - a.val) < 0
      · simp only [hd, hov, decide_true, Bool.and_true, ite_true, steprange_last.overflow_case, rem_sum_inl,
          bind, Except.bind]
        obtain ⟨q, hq, hqv⟩ := rem_us_ok (JUnsigned.unsigned (JRangeWrappingSub.rangeWrappingSub b a : JInt t)) s
          (by omega)
        rw [hq]; dsimp only
        have huv : (JUnsigned.unsigned (JRangeWrappingSub.rangeWrappingSub b a : JInt t) : JInt t.toUnsigned).val
            = b.val - a.val := by
          show (JuliaLean.base.int.unsigned _).val = _
          rw [IntVal.unsigned_val, hd]
          have := hov.1
          cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, IntTy.toUnsigned, wrapInt] <;> omega
        have hqv' : q.val = (b.val - a.val).tmod s.val := by rw [hqv, huv]; congr 1; omega
        have hb' := (IntVal.tmod_between (b.val - a.val) s.val).1 (by omega)
        have hqlt : q.val < s.val := by rw [hqv']; exact Int.tmod_lt_of_pos _ hs0
        rw [convert_ok (t := t) (x := q) (by omega) (by omega)]
        refine ⟨_, by simp [convert_self, pure, Except.pure]; rfl, ?_⟩
        simp only [sub_iv]
        rw [wrap_in t (by omega) (by omega), hqv', hlv, if_pos hlt]
      · have hov' : (t.signed && decide (wrapInt t (b.val - a.val) < 0)) = false := by
          cases h : t.signed <;> simp_all
        simp only [hd, hov', Bool.false_eq_true, ite_false, rem_sum_inl, bind, Except.bind]
        have hdv : wrapInt t (b.val - a.val) = b.val - a.val := by
          by_cases hfit : b.val - a.val ≤ t.max
          · exact wrap_in t (by omega) hfit
          · exfalso
            cases ht : t.signed
            · have := IntVal.nonneg_of_unsigned ht a
              cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
            · apply hov; refine ⟨ht, ?_⟩
              cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;> omega
        obtain ⟨q, hq, hqv⟩ := rem_same_ok (JRangeWrappingSub.rangeWrappingSub b a : JInt t) s (by omega)
        rw [hq]
        have hqv' : q.val = (b.val - a.val).tmod s.val := by rw [hqv, hd, hdv]
        have hb' := (IntVal.tmod_between (b.val - a.val) s.val).1 (by omega)
        refine ⟨_, by simp [convert_self, pure, Except.pure]; rfl, ?_⟩
        simp only [sub_iv]
        rw [wrap_in t (by omega) (by omega), hqv', hlv, if_pos hlt]
    · have hgt : b.val < a.val := by omega
      have hs0 : s.val < 0 := by by_cases h1 : 0 < s.val <;> simp_all <;> omega
      have hsg : t.signed = true := by
        cases ht : t.signed
        · have := IntVal.nonneg_of_unsigned ht s; omega
        · rfl
      simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      have hd : (JRangeWrappingSub.rangeWrappingSub a b : JInt t).val = wrapInt t (a.val - b.val) :=
        wrappingSub_iv a b
      have hns : (JNeg.neg s : JInt t).val = wrapInt t (-s.val) := neg_iv s
      have hnabs := natAbs_wrap_neg s hs0
      by_cases hov : wrapInt t (a.val - b.val) < 0
      · simp only [hd, hov, hsg, decide_true, Bool.and_true, ite_true, steprange_last.overflow_case,
          rem_sum_inr, bind, Except.bind]
        obtain ⟨q, hq, hqv⟩ := rem_us_ok (JUnsigned.unsigned (JRangeWrappingSub.rangeWrappingSub a b : JInt t))
          (JNeg.neg s) (by rw [hns]; rcases wrap_neg_cases s hs0 with h | ⟨h, _⟩ <;> omega)
        rw [hq]; dsimp only
        have huv : (JUnsigned.unsigned (JRangeWrappingSub.rangeWrappingSub a b : JInt t) : JInt t.toUnsigned).val
            = a.val - b.val := by
          show (JuliaLean.base.int.unsigned _).val = _
          rw [IntVal.unsigned_val, hd]
          cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, IntTy.toUnsigned, wrapInt] <;> omega
        have hqv' : q.val = (a.val - b.val).tmod (-s.val) := by rw [hqv, huv, hns, hnabs]
        have hb' := (IntVal.tmod_between (a.val - b.val) (-s.val)).1 (by omega)
        have hqlt : q.val < -s.val := by rw [hqv']; exact Int.tmod_lt_of_pos _ (by omega)
        have hmm : t.max = -t.min - 1 := by cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits]
        rw [convert_ok (t := t) (x := q) (by omega) (by omega)]
        refine ⟨_, by simp [convert_self, pure, Except.pure]; rfl, ?_⟩
        simp only [add_iv]
        rw [wrap_in t (by omega) (by omega), hqv', hlv, if_neg hlt]
      · simp only [hd, hov, hsg, decide_false, Bool.and_false, Bool.false_eq_true, ite_false,
          rem_sum_inr, bind, Except.bind]
        have hdv : wrapInt t (a.val - b.val) = a.val - b.val := by
          by_cases hfit : a.val - b.val ≤ t.max
          · exact wrap_in t (by omega) hfit
          · exfalso; apply hov
            cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits, wrapInt] <;> omega
        obtain ⟨q, hq, hqv⟩ := rem_same_ok (JRangeWrappingSub.rangeWrappingSub a b : JInt t) (JNeg.neg s)
          (by rw [hns]; rcases wrap_neg_cases s hs0 with h | ⟨h, _⟩ <;> omega)
        rw [hq]
        have hqv' : q.val = (a.val - b.val).tmod (-s.val) := by
          rw [hqv, hd, hdv, hns, tmod_wrap_neg _ s hs0]
        have hb' := (IntVal.tmod_between (a.val - b.val) (-s.val)).1 (by omega)
        refine ⟨_, by simp [convert_self, pure, Except.pure]; rfl, ?_⟩
        simp only [add_iv]
        rw [wrap_in t (by omega) (by omega), hqv', hlv, if_neg hlt]


/-- `a:s:b` of one BitInteger type with a nonzero step. -/
theorem colon_step (a s b : JInt t) (hs : s.val ≠ 0) :
    ∃ l : JInt t, (JColon3.colon a s b : JlX (StepRange (JInt t) (JInt t))) = .ok ⟨a, s, l⟩ ∧
      StepRange_T_S_T a s b = .ok (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) ∧
      l.val = lastVal a.val s.val b.val := by
  obtain ⟨l, hl, hlv⟩ := steprange_last_ok a s b hs
  refine ⟨l, ?_, ?_, hlv⟩ <;>
  · simp only [JColon3.colon, colon_T_T_T_Real, JColonStyle.colonStyle, _colon_Ordered_Any,
      JStepRange3.stepRange, StepRange_T_S_T, JStepRangeTS.stepRangeTS, StepRange_TS_new, convert_self,
      bind, Except.bind, hl, pure, Except.pure]

/-- `a:0:b` throws `ArgumentError("step cannot be zero")`. -/
theorem colon_step_zero (a s b : JInt t) (hs : s.val = 0) :
    (JColon3.colon a s b : JlX (StepRange (JInt t) (JInt t))) =
      .error (.jl (.argumentError "step cannot be zero")) := by
  simp [JColon3.colon, colon_T_T_T_Real, JColonStyle.colonStyle, _colon_Ordered_Any,
    JStepRange3.stepRange, StepRange_T_S_T, JStepRangeTS.stepRangeTS, StepRange_TS_new, convert_self,
    bind, Except.bind, JSteprangeLast.steprangeLast, steprange_last, JType.isAbstractFloat,
    JType.isInteger, JIsinteger.isinteger, JuliaLean.base.number.isintegerInteger, hs, throw,
    throwThe, MonadExceptOf.throw]

theorem lastVal_count (a s b : Int) (hs : s ≠ 0) (hc : 0 < stepCount a s b) :
    lastVal a s b = a + (stepCount a s b - 1) * s := by
  unfold stepCount at hc ⊢; unfold lastVal
  by_cases h1 : 0 < s ∧ a ≤ b
  · rw [if_pos h1] at hc ⊢
    have := Int.tmod_add_tdiv_mul (b - a) s
    by_cases hab : a = b
    · subst hab; simp
    rw [if_neg hab, if_neg (by simp [h1.1, show a < b by omega]), if_pos (by omega)]
    simp only [Int.add_sub_cancel]; omega
  · rw [if_neg h1] at hc ⊢
    by_cases h2 : s < 0 ∧ b ≤ a
    · rw [if_pos h2] at hc ⊢
      have := Int.tmod_add_tdiv_mul (a - b) (-s)
      by_cases hab : a = b
      · subst hab; simp
      rw [if_neg hab, if_neg (by simp [show ¬ 0 < s by omega, show ¬ a < b by omega]),
        if_neg (by omega)]
      simp only [Int.add_sub_cancel]
      have h3 : (a - b).tdiv (-s) * (-s) = -((a - b).tdiv (-s) * s) := by rw [Int.mul_neg]
      omega
    · rw [if_neg h2] at hc; omega

theorem stepCount_nonneg (a s b : Int) : 0 ≤ stepCount a s b := by
  unfold stepCount
  split
  · have := Int.tdiv_nonneg (a := b - a) (b := s) (by omega) (by omega); omega
  · split
    · have := Int.tdiv_nonneg (a := a - b) (b := -s) (by omega) (by omega); omega
    · omega

/-- The elements of `a:s:b` lie between `a` and `b`. -/
theorem stepCount_bound (a s b : Int) (k : Int) (hk0 : 0 ≤ k) (hk : k < stepCount a s b) :
    (a ≤ a + k * s ∧ a + k * s ≤ b) ∨ (b ≤ a + k * s ∧ a + k * s ≤ a) := by
  unfold stepCount at hk
  by_cases h1 : 0 < s ∧ a ≤ b
  · rw [if_pos h1] at hk
    left
    have := Int.tmod_add_tdiv_mul (b - a) s
    have := Int.tmod_nonneg s (show 0 ≤ b - a by omega)
    have hk' : k * s ≤ (b - a).tdiv s * s := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    constructor
    · have := Int.mul_nonneg hk0 (show 0 ≤ s by omega); omega
    · omega
  · rw [if_neg h1] at hk
    by_cases h2 : s < 0 ∧ b ≤ a
    · rw [if_pos h2] at hk
      right
      have := Int.tmod_add_tdiv_mul (a - b) (-s)
      have := Int.tmod_nonneg (-s) (show 0 ≤ a - b by omega)
      have hk' : k * (-s) ≤ (a - b).tdiv (-s) * (-s) :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have e1 : k * (-s) = -(k * s) := Int.mul_neg k s
      constructor
      · omega
      · have := Int.mul_nonneg hk0 (show 0 ≤ -s by omega); omega
    · rw [if_neg h2] at hk; omega


section StepIter
variable {t : IntTy}

@[simp] theorem first_step (r : StepRange (JInt t) (JInt t)) : JFirst.first r = .ok r.start := by
  simp [JFirst.first, first_OrdinalRange, JFieldStart.start]
@[simp] theorem last_step (r : StepRange (JInt t) (JInt t)) : JLast.last r = .ok r.stop := by
  simp [JLast.last, last_OrdinalRange, JFieldStop.stop]
@[simp] theorem step_step (r : StepRange (JInt t) (JInt t)) : JStep.step r = .ok r.step := rfl
@[simp] theorem isempty_step (r : StepRange (JInt t) (JInt t)) :
    JIsempty.isempty r = .ok (decide (r.start.val ≠ r.stop.val) &&
      (decide (0 < r.step.val) != decide (r.start.val < r.stop.val))) := by
  simp [JIsempty.isempty, isempty_StepRange, pure, Except.pure]

theorem iterate2_step (r : StepRange (JInt t) (JInt t)) (i : JInt t) (hi : i.val ≠ r.stop.val) :
    ∃ j : JInt t, JIterate2.iterate r i = .ok (some (j, j)) ∧ j.val = wrapInt t (i.val + r.step.val) := by
  simp only [JIterate2.iterate, iterate_OrdinalRange_state, last_step, eq_iv, step_step]
  simp only [bind, Except.bind, hi, decide_false, Bool.false_eq_true, ite_false, convert_self,
    pure, Except.pure]
  exact ⟨_, rfl, add_iv _ _⟩

theorem iterate2_step_last (r : StepRange (JInt t) (JInt t)) (i : JInt t) (hi : i.val = r.stop.val) :
    JIterate2.iterate r i = .ok none := by
  simp [JIterate2.iterate, iterate_OrdinalRange_state, hi, bind, Except.bind, pure, Except.pure]

/-- Iterating a step range `r` whose stop is `start + q*step`, with every intermediate value
representable, from the state `start + j*step` visits `start + (j+1)*step, ..., start + q*step`. -/
theorem iterFrom_step (r : StepRange (JInt t) (JInt t)) (q : Nat) (hs : r.step.val ≠ 0)
    (hq : r.stop.val = r.start.val + q * r.step.val)
    (hin : ∀ j : Nat, j ≤ q → t.min ≤ r.start.val + j * r.step.val ∧ r.start.val + j * r.step.val ≤ t.max) :
    ∀ (fuel j : Nat) (i : JInt t), j ≤ q → q - j < fuel → i.val = r.start.val + j * r.step.val →
      (iterFrom r fuel i).map vals =
        .ok ((List.range (q - j)).map fun (k : Nat) => r.start.val + ((j + 1 + k : Nat) : Int) * r.step.val)
  | 0, _, _, _, h, _ => by omega
  | fuel + 1, j, i, hj, hf, hi => by
    by_cases heq : j = q
    · subst heq
      simp [iterFrom, iterate2_step_last r i (by rw [hi, hq]), bind, Except.bind, pure, Except.pure,
        Except.map]
    · have hne : i.val ≠ r.stop.val := by
        rw [hi, hq]; intro h
        have : ((j : Int) - q) * r.step.val = 0 := by rw [Int.sub_mul]; omega
        rcases Int.mul_eq_zero.mp this with h0 | h0 <;> omega
      obtain ⟨k, hk, hkv⟩ := iterate2_step r i hne
      have hkv' : k.val = r.start.val + ((j + 1 : Nat) : Int) * r.step.val := by
        rw [hkv, hi]
        have := hin (j + 1) (by omega)
        rw [wrap_in t (by push_cast at this ⊢; rw [Int.add_mul] at this; simp at this; omega)
          (by push_cast at this ⊢; rw [Int.add_mul] at this; simp at this; omega)]
        push_cast; rw [Int.add_mul]; simp; omega
      have ih := iterFrom_step r q hs hq hin fuel (j + 1) k (by omega) (by omega) hkv'
      simp only [iterFrom, hk, bind, Except.bind]
      rw [show q - j = (q - (j + 1)) + 1 by omega, List.range_succ_eq_map]
      revert ih
      cases iterFrom r fuel k <;> simp [Except.map, pure, Except.pure, hkv', List.map_map]
      intro h; rw [h]; apply List.map_congr_left; intro x _; simp only [Function.comp]; push_cast
      congr 2; omega


theorem isempty_lastVal (a s b : Int) (hs : s ≠ 0) :
    (decide (a ≠ lastVal a s b) && (decide (0 < s) != decide (a < lastVal a s b))) =
      decide (stepCount a s b = 0) := by
  have hc := stepCount_nonneg a s b
  by_cases h0 : stepCount a s b = 0
  · have hl : lastVal a s b = if 0 < s then a - 1 else a + 1 := by
      unfold stepCount at h0; unfold lastVal
      by_cases h1 : 0 < s ∧ a ≤ b
      · rw [if_pos h1] at h0; have := Int.tdiv_nonneg (a := b - a) (b := s) (by omega) (by omega); omega
      · rw [if_neg h1] at h0
        by_cases h2 : s < 0 ∧ b ≤ a
        · rw [if_pos h2] at h0; have := Int.tdiv_nonneg (a := a - b) (b := -s) (by omega) (by omega); omega
        · rw [if_neg (by omega), if_pos (by by_cases h : 0 < s <;> simp [h] <;> omega)]
    rw [hl]; by_cases hp : 0 < s <;> simp [hp, h0] <;> omega
  · have hl := lastVal_count a s b hs (by omega)
    rw [hl]
    have hb := stepCount_bound a s b (stepCount a s b - 1) (by omega) (by omega)
    simp only [h0, decide_false]
    by_cases hq : stepCount a s b - 1 = 0
    · rw [hq]; simp
    · have hne : (stepCount a s b - 1) * s ≠ 0 := Int.mul_ne_zero hq hs
      by_cases hp : 0 < s
      · have := Int.mul_pos (show 0 < stepCount a s b - 1 by omega) hp
        simp [hp]; omega
      · have : (stepCount a s b - 1) * s < 0 :=
          Int.mul_neg_of_pos_of_neg (by omega) (by omega)
        simp [hp]; omega

end StepIter


/-- `a:s:b` for integers `a`, `s`, `b` of one BitInteger type `T` (`(:)(start::T, step::T, stop::T)`,
range.jl:22, which builds `StepRange(start, step, stop)`, range.jl:404) denotes the integers
`a, a+s, a+2s, ...` that lie between `a` and `b` (StepRange docstring, range.jl:289-343; manual,
"Ranges"): a zero step throws `ArgumentError`; otherwise `first` is `a`, `step` is `s`, `isempty`
holds exactly when no such integer exists, `last` is the last of them, and iteration visits exactly
them, for every width, including steps of `typemin` and ranges spanning the whole type. -/
def StepRangeColon : Prop :=
  ∀ (t : IntTy) (a s b : JInt t),
    (s.val = 0 → (JColon3.colon a s b : JlX (StepRange (JInt t) (JInt t))) =
      .error (.jl (.argumentError "step cannot be zero"))) ∧
    (s.val ≠ 0 → ∃ r : StepRange (JInt t) (JInt t), JColon3.colon a s b = .ok r ∧
      StepRange_T_S_T a s b = .ok r ∧
      (JFirst.first r).map Subtype.val = .ok a.val ∧
      (JStep.step r).map Subtype.val = .ok s.val ∧
      JIsempty.isempty r = .ok (decide (stepInts a.val s.val b.val = [])) ∧
      (0 < stepCount a.val s.val b.val →
        (JLast.last r).map Subtype.val = .ok (a.val + (stepCount a.val s.val b.val - 1) * s.val)) ∧
      (∀ fuel, (stepCount a.val s.val b.val).toNat ≤ fuel →
        iterVals r fuel = .ok (stepInts a.val s.val b.val)))

theorem stepInts_nil_iff (a s b : Int) : stepInts a s b = [] ↔ stepCount a s b = 0 := by
  have := stepCount_nonneg a s b
  simp [stepInts]; omega

theorem stepRangeColon_proven : StepRangeColon := by
  intro t a s b
  refine ⟨colon_step_zero a s b, fun hs => ?_⟩
  obtain ⟨l, hc, hc', hlv⟩ := colon_step a s b hs
  have hcn := stepCount_nonneg a.val s.val b.val
  have hemp := isempty_lastVal a.val s.val b.val hs
  refine ⟨⟨a, s, l⟩, hc, hc', by simp [Except.map], by simp [Except.map], ?_, ?_, ?_⟩
  · simp only [isempty_step, hlv, hemp, stepInts_nil_iff]
  · intro hpos; simp [Except.map, hlv, lastVal_count _ _ _ hs hpos]
  · intro fuel hf
    by_cases h0 : stepCount a.val s.val b.val = 0
    · have hnil : stepInts a.val s.val b.val = [] := (stepInts_nil_iff _ _ _).mpr h0
      have he : (decide (a.val ≠ l.val) && (decide (0 < s.val) != decide (a.val < l.val))) = true := by
        rw [hlv, hemp]; simp [h0]
      unfold iterVals iterList
      simp only [JIterate1.iterate, iterate_OrdinalRange, isempty_step, he, bind, Except.bind,
        ite_true, pure, Except.pure, hnil]
      rfl
    · obtain ⟨q, hq⟩ : ∃ q : Nat, stepCount a.val s.val b.val = q + 1 := ⟨(stepCount a.val s.val b.val - 1).toNat, by omega⟩
      have hl' : l.val = a.val + q * s.val := by rw [hlv, lastVal_count _ _ _ hs (by omega), hq]; simp
      have hin : ∀ j : Nat, j ≤ q → t.min ≤ a.val + j * s.val ∧ a.val + j * s.val ≤ t.max := by
        intro j hj
        have := stepCount_bound a.val s.val b.val j (by omega) (by omega)
        have := a.property; have := b.property; omega
      have hit := iterFrom_step (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) q hs hl' hin fuel 0 a
        (by omega) (by omega) (by simp)
      have hne : (decide (a.val ≠ l.val) && (decide (0 < s.val) != decide (a.val < l.val))) = false := by
        rw [hlv, hemp]; simp [h0]
      unfold iterVals iterList
      simp only [JIterate1.iterate, iterate_OrdinalRange, isempty_step, hne, first_step, bind,
        Except.bind, Bool.false_eq_true, ite_false, pure, Except.pure]
      revert hit
      cases iterFrom (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) fuel a <;> simp [Except.map]
      intro h
      simp only [stepInts, hq]
      rw [show (q + 1 : Int).toNat = q + 1 by omega, List.range_succ_eq_map]
      simp [h, List.map_map]
      intro x _; rw [Int.add_comm 1]

end StepLast

section UnitQueries
variable {s t : IntTy}

theorem mem_intsFromTo (x a b : Int) : x ∈ intsFromTo a b ↔ a ≤ x ∧ x ≤ b := by
  unfold intsFromTo
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨(x - a).toNat, by omega, by omega⟩

theorem intsFromTo_eq_iff (a b c d : Int) :
    intsFromTo a b = intsFromTo c d ↔ ((b < a ∧ d < c) ∨ (a = c ∧ b = d)) := by
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [intsFromTo_length] at hl
    by_cases h1 : b < a
    · left; refine ⟨h1, ?_⟩; omega
    · right
      have ha : a ∈ intsFromTo c d := h ▸ (mem_intsFromTo a a b).mpr ⟨Int.le_refl _, by omega⟩
      have hc : c ∈ intsFromTo a b := h.symm ▸ (mem_intsFromTo c c d).mpr ⟨Int.le_refl _, by
        rw [mem_intsFromTo] at ha; omega⟩
      rw [mem_intsFromTo] at ha hc
      omega
  · rintro (⟨h1, h2⟩ | ⟨rfl, rfl⟩)
    · rw [intsFromTo_empty h1, intsFromTo_empty h2]
    · rfl

/-- `in(x::Integer, r::AbstractUnitRange{<:Integer})` (range.jl:1489) on `a:b`. -/
theorem in_unit (a b : JInt t) (x : JInt s) :
    in_Integer_AbstractUnitRange x (⟨a, unitStop a b⟩ : UnitRange (JInt t)) =
      .ok (decide (x.val ∈ intsFromTo a.val b.val)) := by
  have hs := unitStop_val a b
  simp only [in_Integer_AbstractUnitRange, first_unit, last_unit, le_iv, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq]
  rw [hs]
  by_cases h : a.val ≤ b.val
  · simp [h, mem_intsFromTo]
  · simp only [h, ite_false, mem_intsFromTo]
    by_cases h2 : a.val ≤ x.val <;> simp [h2] <;> omega


theorem bool_eq_decide {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) : b = decide P := by
  by_cases hP : P
  · simp [hP, h.mpr hP]
  · cases hb : b
    · simp [hP]
    · exact absurd (h.mp hb) hP

theorem intsFromTo_pairwise (a b : Int) : (intsFromTo a b).Pairwise (· < ·) := by
  unfold intsFromTo
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.pairwise_lt_range)
  intro x y h; omega

/-- `minimum(r::AbstractUnitRange)` (range.jl:881) and `maximum` (range.jl:882) on `a:b`. -/
theorem minmax_unit (a b : JInt t) :
    (minimum_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t))).map Subtype.val =
      (if b.val < a.val then .error (.jl (.argumentError "range must be non-empty")) else .ok a.val) ∧
    (maximum_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t))).map Subtype.val =
      (if b.val < a.val then .error (.jl (.argumentError "range must be non-empty")) else .ok b.val) := by
  have hs := unitStop_val a b
  simp only [minimum_AbstractUnitRange, maximum_AbstractUnitRange, isempty_unit, first_unit, last_unit,
    bind, Except.bind, hs]
  by_cases h : b.val < a.val
  · simp [h, show ¬ a.val ≤ b.val by omega, show a.val - 1 < a.val by omega, throw, throwThe,
      MonadExceptOf.throw, Except.map]
  · simp [h, show a.val ≤ b.val by omega, Except.map]
    rw [hs, if_pos (by omega)]

/-- `intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})` (range.jl:1209)
on `a:b` and `c:d` is the unit range from the larger start to the smaller stop. -/
theorem intersect_unit (a b c d : JInt t) :
    intersect_AbstractUnitRange_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t))
        (⟨c, unitStop c d⟩ : UnitRange (JInt t)) =
      .ok ⟨(if c.val < a.val then a else c), unitStop (if c.val < a.val then a else c)
        (if (unitStop c d).val < (unitStop a b).val then unitStop c d else unitStop a b)⟩ := by
  simp only [intersect_AbstractUnitRange_AbstractUnitRange, first_unit, last_unit, bind, Except.bind]
  rw [max_same, min_same]
  exact colon_unit _ _

/-- `issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})` (range.jl:1317). -/
theorem issubset_unit (a b c d : JInt t) :
    issubset_AbstractUnitRange_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t))
        (⟨c, unitStop c d⟩ : UnitRange (JInt t)) =
      .ok (decide (∀ x ∈ intsFromTo a.val b.val, x ∈ intsFromTo c.val d.val)) := by
  have hb := unitStop_val a b; have hd := unitStop_val c d
  simp only [issubset_AbstractUnitRange_AbstractUnitRange, isempty_unit, first_unit, last_unit,
    le_iv, bind, Except.bind, pure, Except.pure, hb, hd]
  by_cases h1 : b.val < a.val
  · simp [h1, show ¬ a.val ≤ b.val by omega, intsFromTo_empty h1, show a.val - 1 < a.val by omega]
  · simp only [show a.val ≤ b.val by omega, ite_true, show ¬ b.val < a.val from h1, decide_false,
      Bool.false_eq_true, ite_false]
    split
    · rename_i hca
      congr 1; symm; rw [decide_eq_false_iff_not]; intro h
      have := (mem_intsFromTo _ _ _).mp (h a.val ((mem_intsFromTo _ _ _).mpr ⟨Int.le_refl _, by omega⟩))
      simp at hca; omega
    · rename_i hca
      congr 1; apply bool_eq_decide
      simp only [decide_eq_true_eq, mem_intsFromTo]
      simp at hca
      constructor
      · intro h x hx; constructor <;> split at h <;> omega
      · intro h
        have := h b.val ⟨by omega, Int.le_refl _⟩
        have := h a.val ⟨Int.le_refl _, by omega⟩
        split <;> omega

/-- `==(r::AbstractUnitRange, s::AbstractUnitRange)` (range.jl:1163). -/
theorem eq_unit (a b c d : JInt t) :
    eq_AbstractUnitRange_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t))
        (⟨c, unitStop c d⟩ : UnitRange (JInt t)) =
      .ok (decide (intsFromTo a.val b.val = intsFromTo c.val d.val)) := by
  have hb := unitStop_val a b; have hd := unitStop_val c d
  simp only [eq_AbstractUnitRange_AbstractUnitRange, isempty_unit, first_unit, last_unit, eq_iv,
    bind, Except.bind, pure, Except.pure, hb, hd]
  congr 1
  apply bool_eq_decide
  rw [intsFromTo_eq_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; constructor <;> split at * <;> omega
    · by_cases ha : a.val ≤ b.val <;> by_cases hc : c.val ≤ d.val <;>
        simp only [ha, hc, ite_true, ite_false] at h2 <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; constructor <;> split <;> omega
    · right; refine ⟨h1, ?_⟩; split <;> split <;> omega


theorem intsFromTo_ne_nil {a b : Int} : intsFromTo a b ≠ [] ↔ a ≤ b := by
  rw [Ne, ← List.length_eq_zero_iff, intsFromTo_length]; omega

/-- Iterating `⟨m, unitStop m n⟩` visits `m, ..., n`. -/
theorem iterVals_unitStop (m n : JInt t) (fuel : Nat) (hf : (n.val - m.val).toNat < fuel) :
    iterVals (⟨m, unitStop m n⟩ : UnitRange (JInt t)) fuel = .ok (intsFromTo m.val n.val) := by
  have hs := unitStop_val m n
  have := iterList_unit (⟨m, unitStop m n⟩ : UnitRange (JInt t)) fuel (by simp only [hs]; split <;> omega)
  unfold iterVals; rw [this]; simp only [hs]
  split
  · rfl
  · rw [intsFromTo_empty (by omega), intsFromTo_empty (by omega)]

/-- Queries on integer unit ranges `a:b`, `c:d` of one BitInteger type agree with their element
lists `A = [a, ..., b]` and `C = [c, ..., d]`: `x in a:b` (range.jl:1489, for `x` of any BitInteger
type) is membership in `A`; `minimum`/`maximum` (range.jl:881-882) are the least/greatest element and
throw `ArgumentError` on an empty range; `==` (range.jl:1163) is equality of `A` and `C`;
`issubset` (range.jl:1317) is inclusion of `A` in `C`; iterating `intersect(a:b, c:d)`
(range.jl:1209) visits, in increasing order, exactly the integers in both; and `issorted`/`sort`
(range.jl:1457, 1460) report and return the range unchanged, whose elements are increasing. -/
def UnitRangeQueries : Prop :=
  ∀ (t : IntTy) (a b c d : JInt t), ∃ r q : UnitRange (JInt t),
    JColon2.colon a b = .ok r ∧ JColon2.colon c d = .ok q ∧
    (∀ (s : IntTy) (x : JInt s),
      in_Integer_AbstractUnitRange x r = .ok (decide (x.val ∈ intsFromTo a.val b.val))) ∧
    (intsFromTo a.val b.val = [] →
      (∃ m, minimum_AbstractUnitRange r = .error (.jl (.argumentError m))) ∧
      (∃ m, maximum_AbstractUnitRange r = .error (.jl (.argumentError m)))) ∧
    (intsFromTo a.val b.val ≠ [] → ∃ lo hi : JInt t,
      minimum_AbstractUnitRange r = .ok lo ∧ maximum_AbstractUnitRange r = .ok hi ∧
      lo.val ∈ intsFromTo a.val b.val ∧ hi.val ∈ intsFromTo a.val b.val ∧
      ∀ x ∈ intsFromTo a.val b.val, lo.val ≤ x ∧ x ≤ hi.val) ∧
    eq_AbstractUnitRange_AbstractUnitRange r q =
      .ok (decide (intsFromTo a.val b.val = intsFromTo c.val d.val)) ∧
    issubset_AbstractUnitRange_AbstractUnitRange r q =
      .ok (decide (∀ x ∈ intsFromTo a.val b.val, x ∈ intsFromTo c.val d.val)) ∧
    (∃ i : UnitRange (JInt t), intersect_AbstractUnitRange_AbstractUnitRange r q = .ok i ∧
      ∀ fuel, (b.val - a.val).toNat < fuel → ∃ xs, iterVals i fuel = .ok xs ∧
        xs.Pairwise (· < ·) ∧
        ∀ x, x ∈ xs ↔ x ∈ intsFromTo a.val b.val ∧ x ∈ intsFromTo c.val d.val) ∧
    issorted_AbstractUnitRange r = true ∧ sort_AbstractUnitRange r = r ∧
      (intsFromTo a.val b.val).Pairwise (· < ·)

theorem unitRangeQueries_proven : UnitRangeQueries := by
  intro t a b c d
  have hb := unitStop_val a b; have hd := unitStop_val c d
  refine ⟨_, _, colon_unit a b, colon_unit c d, fun s x => in_unit a b x, ?_, ?_, eq_unit a b c d,
    issubset_unit a b c d, ?_, rfl, rfl, intsFromTo_pairwise _ _⟩
  · intro h
    have hlt : b.val < a.val := by
      have := intsFromTo_length a.val b.val; rw [h] at this; simp at this; omega
    have hm := minmax_unit a b
    rw [if_pos hlt, if_pos hlt] at hm
    refine ⟨⟨"range must be non-empty", ?_⟩, ⟨"range must be non-empty", ?_⟩⟩
    · have := hm.1; revert this
      cases minimum_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t)) <;> simp [Except.map]
    · have := hm.2; revert this
      cases maximum_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t)) <;> simp [Except.map]
  · intro h
    have hle : a.val ≤ b.val := intsFromTo_ne_nil.mp h
    have hm := minmax_unit a b
    rw [if_neg (by omega), if_neg (by omega)] at hm
    obtain ⟨h1, h2⟩ := hm
    revert h1 h2
    cases hmin : minimum_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t)) <;>
    cases hmax : maximum_AbstractUnitRange (⟨a, unitStop a b⟩ : UnitRange (JInt t)) <;>
      simp [Except.map]
    intro h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> simp only [mem_intsFromTo, h1, h2] <;> omega
  · refine ⟨_, intersect_unit a b c d, fun fuel hf => ?_⟩
    refine ⟨_, iterVals_unitStop _ _ fuel ?_, intsFromTo_pairwise _ _, fun x => ?_⟩
    · split <;> split <;> simp only [hb, hd] at * <;> split at * <;> split at * <;> omega
    · simp only [mem_intsFromTo]
      split <;> split <;> simp only [hb, hd] at * <;> split at * <;> split at * <;> omega

end UnitQueries

section KwWorld
variable {t : IntTy}
/-- `range_stop(stop::Integer) = range_length(stop)`, range.jl:197. -/
instance : JRangeStop (JInt t) (OneTo (JInt t)) := ⟨range_stop_Integer⟩
/-- `_range(::Nothing, ::Nothing, ::Nothing, len::Any) = range_length(len)`, range.jl:176. -/
instance : JRangeImpl Nothing Nothing Nothing (JInt t) (OneTo (JInt t)) := ⟨_range_N_N_N_A⟩
/-- `_range(::Nothing, ::Nothing, stop::Any, ::Nothing) = range_stop(stop)`, range.jl:177. -/
instance : JRangeImpl Nothing Nothing (JInt t) Nothing (OneTo (JInt t)) := ⟨_range_N_N_A_N⟩
/-- `_range(::Nothing, ::Nothing, ::Nothing, ::Nothing) = range_error(...)`, range.jl:175. -/
instance : JRangeImpl Nothing Nothing Nothing Nothing Unit := ⟨_range_N_N_N_N⟩
end KwWorld

section KwSpec
variable {t : IntTy}

/-- Keyword `range` with BitInteger arguments builds the range the `range` docstring
(range.jl:72-160) describes: with only `length=n` or only `stop=n` it is `Base.OneTo(n)`, the
integers `1, ..., n`; with `start=a` and `stop=b` (as keywords or positionally) it is the integers
`a, ..., b`; with `start=a`, `step=s`, `stop=b` it is the integers `a, a+s, ...` between `a` and
`b` (an `ArgumentError` for `s == 0`); and the invalid combinations `range()` and
`range(; step, length)` throw `ArgumentError`. -/
def KeywordRange : Prop :=
  ∀ (t : IntTy) (a b s n : JInt t),
    (∃ r : OneTo (JInt t), range_kw Nothing.nothing Nothing.nothing n Nothing.nothing = .ok r ∧
      ∀ fuel, n.val.toNat < fuel → iterVals r fuel = .ok (intsFromTo 1 n.val)) ∧
    (∃ r : OneTo (JInt t), range_kw Nothing.nothing b Nothing.nothing Nothing.nothing = .ok r ∧
      ∀ fuel, b.val.toNat < fuel → iterVals r fuel = .ok (intsFromTo 1 b.val)) ∧
    (∃ r : UnitRange (JInt t), range_start_kw a b Nothing.nothing Nothing.nothing = .ok r ∧
      range_start_stop_kw a b Nothing.nothing Nothing.nothing = .ok r ∧
      range_kw a b Nothing.nothing Nothing.nothing = .ok r ∧
      ∀ fuel, (b.val - a.val).toNat < fuel → iterVals r fuel = .ok (intsFromTo a.val b.val)) ∧
    (s.val = 0 → ∃ m, (range_start_kw a b Nothing.nothing s : JlX (StepRange (JInt t) (JInt t))) =
      .error (.jl (.argumentError m))) ∧
    (s.val ≠ 0 → ∃ r : StepRange (JInt t) (JInt t), range_start_kw a b Nothing.nothing s = .ok r ∧
      range_start_stop_kw a b Nothing.nothing s = .ok r ∧ range_kw a b Nothing.nothing s = .ok r ∧
      ∀ fuel, (stepCount a.val s.val b.val).toNat ≤ fuel →
        iterVals r fuel = .ok (stepInts a.val s.val b.val)) ∧
    (∃ m, (range_kw Nothing.nothing Nothing.nothing n s : JlX Unit) = .error (.jl (.argumentError m))) ∧
    (∃ m, (range_kw Nothing.nothing Nothing.nothing Nothing.nothing Nothing.nothing : JlX Unit) =
      .error (.jl (.argumentError m)))

theorem keywordRange_proven : KeywordRange := by
  intro t a b s n
  obtain ⟨_, hn, _, _, _, _, hit, -⟩ := oneToElements_proven t n
  obtain ⟨_, hb, _, _, _, _, hitb, -⟩ := oneToElements_proven t b
  obtain ⟨r, hc, -, -, -, -, -, -, hitr, -⟩ := unitRangeColon_proven t a b
  obtain ⟨hz, hnz⟩ := stepRangeColon_proven t a s b
  refine ⟨⟨_, hn, hit⟩, ⟨_, hb, hitb⟩, ⟨r, hc, hc, hc, hitr⟩, fun h0 => ⟨_, hz h0⟩, fun h0 => ?_, ⟨_, rfl⟩,
    ⟨_, rfl⟩⟩
  obtain ⟨q, hq, -, -, -, -, -, hitq⟩ := hnz h0
  exact ⟨q, hq, hq, hq, hitq⟩

end KwSpec

end JuliaLean.Proofs.base.range

namespace JuliaLean.Proofs.base.range

open JuliaLean JuliaLean.base.range JuliaLean.Registry
open JuliaLean.base.int (lit)
open JuliaLean.base.float (FV FTy)

section TwicePrecisionEq

/-- A `StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}` as built by
`range(start; step, length)` for `Float64` arguments. `TwicePrecision` (twiceprecision.jl, not yet
migrated) is the typed parameter `TP`. -/
abbrev TPRange (TP : Type) := StepRangeLen F64 TP TP JInt64

/-- `==` on two such ranges, with the instances Julia selects (`which` on the target build):
`==(r::T, s::T) where {T<:Union{StepRangeLen,LinRange}}` (range.jl:1168), `isempty` (range.jl:712),
`length` (range.jl:807), `first` (range.jl:869), `last` (range.jl:878) and `==` on `Float64`/`Int`;
the element function `unsafe_getindex(r::StepRangeLen{T,<:TwicePrecision,<:TwicePrecision}, i)`
(twiceprecision.jl:480) is the typed parameter `ug`. -/
def tpEq {TP : Type} (ug : TPRange TP → JInt64 → F64) (r s : TPRange TP) : JlX Bool :=
  letI : JUnsafeGetindex (TPRange TP) JInt64 F64 := ⟨fun r i => pure (ug r i)⟩
  letI : JLength (TPRange TP) JInt64 := ⟨fun r => pure (length_StepRangeLen r)⟩
  letI : JIsempty (TPRange TP) := ⟨isempty_StepRangeLen⟩
  letI : JFirst (TPRange TP) F64 := ⟨first_StepRangeLen⟩
  letI : JLast (TPRange TP) F64 := ⟨last_StepRangeLen⟩
  eq_T_T_StepRangeLen_LinRange r s

/-- Two `Float64` `StepRangeLen`s with `TwicePrecision` reference and step that are `==` have
equal elements (`==` on arrays is elementwise equality, and a range is an `AbstractVector`), for
every element function `ug`. -/
def TPEqElementwise : Prop :=
  ∀ (TP : Type) (ug : TPRange TP → JInt64 → F64) (r s : TPRange TP),
    tpEq ug r s = .ok true → r.len.val = s.len.val →
    ∀ i : JInt64, 1 ≤ i.val → i.val ≤ r.len.val → JEq.eq (ug r i) (ug s i) = true

/-- The elements twiceprecision.jl:480 returns for `range(0.0; step=0.30000000000000004, length=8)`
(`r1`) and `range(0.0; step=0.3000000000000001, length=8)` (`r2`), as printed on the
target build; the refutation instantiates `ug` with these
values. `TwicePrecision{Float64}` is represented by its `(hi, lo)` bit patterns. -/
def tpR1 : List Nat := [0, 4599075939470750516, 4603579539098121012, 4606281698874543310,
  4608083138725491508, 4609434218613702657, 4610785298501913806, 4611911198408756430]
def tpR2 : List Nat := [0, 4599075939470750517, 4603579539098121013, 4606281698874543312,
  4608083138725491509, 4609434218613702658, 4610785298501913808, 4611911198408756430]

def tpUg (r : TPRange (Nat × Nat)) (i : JInt64) : F64 :=
  let tbl := if r.step.1 = 4599075939470750516 then tpR1 else tpR2
  f64 (tbl.getD (i.val.toNat - 1) 0)

def tpRange1 : TPRange (Nat × Nat) := ⟨(0, 0), (4599075939470750516, 0), lit .i64 8, lit .i64 1⟩
def tpRange2 : TPRange (Nat × Nat) := ⟨(0, 0), (4599075939470750517, 0), lit .i64 8, lit .i64 1⟩

theorem tpEqElementwise_refuted : ¬ TPEqElementwise := by
  intro h
  have := h (Nat × Nat) tpUg tpRange1 tpRange2 (by decide +kernel) (by decide) (lit .i64 2)
    (by decide) (by decide)
  revert this; decide +kernel

end TwicePrecisionEq

section RoundsColon

/-- The operations `a:b` needs from a non-IEEE `AbstractFloat` type `B` such as `BigFloat`
(mpfr.jl, not yet migrated), as typed parameters: `B(1)`, `-`, `+`, `zero`, `isinteger`, `fld`,
`convert(Integer, x)` into the unbounded `BigInt` (Lean `Int`), and `<`. The one law used is that of
floored division: for `b < a`, `fld(b - a, 1)` is a negative integer. -/
structure RoundsFloatOps (B : Type) where
  one : B
  zero : B
  sub : B → B → B
  add : B → B → B
  isinteger : B → Bool
  fld : B → B → B
  toInteger : B → Int
  lt : B → B → Bool
  fld_neg : ∀ a b, lt b a = true → toInteger (fld (sub b a) one) < 0

/-- `a:b` for `a, b` of such a type: `(:)(a::T, b::T) where {T<:AbstractFloat}` (range.jl:14),
`(:)(start::T, step::T, stop::T) where {T<:AbstractFloat}` (range.jl:20) with
`OrderStyle(T) = Ordered()` and `ArithmeticStyle(T) = ArithmeticRounds()` (traits.jl),
`_colon(::Ordered, ::ArithmeticRounds, ...)` (range.jl:26), `StepRangeLen(ref, step, len)`
(range.jl:548) and its inner constructor (range.jl:533), with `L = promote_type(Int, BigInt)`. -/
def roundsColon {B : Type} (ops : RoundsFloatOps B) (a b : B) : JlX (StepRangeLen B B B Int) :=
  letI : HSub B B B := ⟨ops.sub⟩
  letI : HAdd B B B := ⟨ops.add⟩
  letI : JZero B := ⟨ops.zero⟩
  letI : JType B := ⟨false, false, false, true, fun h => nomatch h⟩
  letI : JIsinteger B := ⟨ops.isinteger⟩
  letI : JCtor B JInt64 := ⟨fun _ => pure ops.one⟩
  letI : JFld B B B := ⟨fun x y => pure (ops.fld x y)⟩
  letI : JConvertInteger B Int := ⟨fun x => pure (ops.toInteger x)⟩
  letI : HAdd Int JInt64 Int := ⟨fun x y => x + y.val⟩
  letI : JConvert Int Int := ⟨fun x => pure x⟩
  letI : JConvert Int JInt64 := ⟨fun x => pure x.val⟩
  letI : JZero Int := ⟨0⟩
  letI : JOneunit Int := ⟨1⟩
  letI : JLe Int Int := ⟨fun x y => decide (x ≤ y)⟩
  letI : JMax Int Int Int := ⟨fun x y => pure (max x y)⟩
  letI : JPrint Int := ⟨toString⟩
  letI : JPromoteType JInt64 Int Int := ⟨⟩
  letI : JStepRangeLenTRSL B B B Int B B Int JInt64 := ⟨StepRangeLen_TRSL_new B⟩
  letI : JStepRangeLen3 B B Int (StepRangeLen B B B Int) :=
    ⟨fun ref step len => StepRangeLen_ref_step ref step len (jint 1)⟩
  letI : JOrderStyle B Ordered := ⟨⟨⟩⟩
  letI : JArithmeticStyle B ArithmeticRounds := ⟨⟨⟩⟩
  letI : JColonStyle Ordered ArithmeticRounds B B B (StepRangeLen B B B Int) :=
    ⟨_colon_Ordered_ArithmeticRounds⟩
  letI : JColon3 B B B (StepRangeLen B B B Int) := ⟨colon_T_T_T_AbstractFloat⟩
  colon_T_T_AbstractFloat a b

/-- `a:b` with `b < a` is an empty range (`(:)` docstring, range.jl:54: "when `b < a`, an empty
range will be constructed"), for every rounding float type with lawful arithmetic. -/
def RoundsColonEmpty : Prop :=
  ∀ (B : Type) (ops : RoundsFloatOps B) (a b : B), ops.lt b a = true →
    ∃ r, roundsColon ops a b = .ok r ∧ r.len = 0

/-- `BigFloat`s holding integers, with exact `-`, `+` and floored division: the values
`big(3.0)` and `big(1.0)` of `repro/rangescov-bigfloat-colon-empty.jl` and the results of the
operations on them. -/
def bigIntOps : RoundsFloatOps Int where
  one := 1
  zero := 0
  sub := (· - ·)
  add := (· + ·)
  isinteger := fun _ => true
  fld := fun x y => x.fdiv y
  toInteger := id
  lt := fun x y => decide (x < y)
  fld_neg := by
    intro a b h
    simp only [decide_eq_true_eq] at h
    simp only [Int.fdiv_one, id]
    omega

theorem roundsColonEmpty_refuted : ¬ RoundsColonEmpty := by
  intro h
  obtain ⟨r, hr, -⟩ := h Int bigIntOps 3 1 (by decide)
  have : (match roundsColon bigIntOps 3 1 with | .ok _ => true | .error _ => false) = false := by
    decide +kernel
  rw [hr] at this
  exact Bool.noConfusion this

end RoundsColon

section LogRangeSpec

/-- `LogRange{Float64}(start, stop, len)` (range.jl:1660) as Julia builds it, with
`_logrange_extra(a::Float64, b::Float64, len::Int)` (range.jl:1706). The twiceprecision.jl callees
`_log_twice64_unchecked` and `/` on its result are the typed parameters `[JLogTwice64 F64 X]` and
`[JSlash X JInt64 X]`; the float.jl comparison `x < 0` of a `Float64` with an `Int` is the typed
parameter `ltI`; `print(io, ::Float64)` in the error messages is `[JPrint F64]`. -/
def logRangeNew (X : Type) [JPrint F64] [JLogTwice64 F64 X] [JSlash X JInt64 X] (ltI : F64 → JInt64 → Bool)
    (a b : F64) (n : JInt64) : JlX (LogRange F64 X) :=
  letI : JLt F64 JInt64 := ⟨ltI⟩
  letI : JIsfinite F64 := ⟨JuliaLean.base.float.isfinite_IEEEFloat⟩
  letI : JLograngeExtra F64 F64 X := ⟨_logrange_extra_Float64⟩
  LogRange_T_new a b n

/-- `r[i]` for a `LogRange{Float64}` (range.jl:1714), whose twiceprecision.jl callees
(`*`, `+` and `_exp_allowing_twice64` on `TwicePrecision`, and `Float64(x)`) are typed
parameters. -/
def logRangeGet (X P W E : Type) [HMul JInt64 X P] [HAdd P P W] [JExpTwice64 W E] [JCtor F64 E]
    (r : LogRange F64 X) (i : JInt64) : JlX F64 :=
  letI : JCheckbounds (LogRange F64 X) JInt64 := ⟨checkboundsVector⟩
  getindex_LogRange r i

/-- `LogRange(start, stop, len)` of `Float64`s (docstring, range.jl:1604-1659: "a range whose
elements are spaced logarithmically between `start` and `stop`"; "`r[1] == start`, `r[end] == stop`"
up to rounding of the interior points): it throws `DomainError` when an endpoint is zero, negative
or not finite; a constructed range has `first(r) == start`, `last(r) == stop`, `length(r) == len`
with `len >= 0`, `r[1]` is exactly `start`, `r[len]` is exactly `stop` for `len >= 2`, and for
`len == 1` the endpoints are `==`. Stated for every implementation of the twiceprecision.jl
logarithm, division and exponential and every `Float64` printer. -/
def LogRangeConstruct : Prop :=
  ∀ (X P W E : Type) [JPrint F64] [JLogTwice64 F64 X] [JSlash X JInt64 X] [HMul JInt64 X P] [HAdd P P W]
    [JExpTwice64 W E] [JCtor F64 E] (ltI : F64 → JInt64 → Bool) (a b : F64) (n : JInt64),
    ((JIszero.iszero a || JIszero.iszero b) = true →
      ∃ m, logRangeNew X ltI a b n = .error (.jl (.domainError m))) ∧
    ((JIszero.iszero a || JIszero.iszero b) = false → (ltI a (jint 0) || ltI b (jint 0)) = true →
      ∃ m, logRangeNew X ltI a b n = .error (.jl (.domainError m))) ∧
    ((JIszero.iszero a || JIszero.iszero b) = false → (ltI a (jint 0) || ltI b (jint 0)) = false →
      (JuliaLean.base.float.isfinite_IEEEFloat a && JuliaLean.base.float.isfinite_IEEEFloat b) = false →
      ∃ m, logRangeNew X ltI a b n = .error (.jl (.domainError m))) ∧
    (∀ r, logRangeNew X ltI a b n = .ok r →
      0 ≤ n.val ∧ JFirst.first r = .ok a ∧ JLast.last r = .ok b ∧ JLength.length r = .ok n ∧
      (1 ≤ n.val → logRangeGet X P W E r (jint 1) = .ok a) ∧
      (2 ≤ n.val → logRangeGet X P W E r n = .ok b) ∧
      (n.val = 1 → JEq.eq a b = true))

theorem logRangeConstruct_proven : LogRangeConstruct := by
  intro X P W E _ _ _ _ _ _ _ ltI a b n
  have hT : JType.isInteger (α := F64) = false := rfl
  refine ⟨fun hz => ?_, fun hz hn => ?_, fun hz hn hf => ?_, fun r hr => ?_⟩
  · exact ⟨"LogRange cannot start or stop at zero", by simp [logRangeNew, LogRange_T_new, hT, hz, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]⟩
  · exact ⟨"LogRange does not accept negative numbers", by simp [logRangeNew, LogRange_T_new, hT, hz, JLt.lt, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]⟩
  · refine ⟨"LogRange is only defined for finite start & stop", ?_⟩
    simp only [logRangeNew, LogRange_T_new, hT, hz, JLt.lt, hn, Bool.false_eq_true, ite_false]
    simp only [Bool.and_eq_false_iff] at hf
    rcases hf with hf | hf <;> simp [JIsfinite.isfinite, hf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp only [logRangeNew, LogRange_T_new, hT, Bool.false_eq_true, ite_false] at hr
    split at hr
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
    split at hr
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
    split at hr
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
    split at hr
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
    rename_i hneg
    split at hr
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
    rename_i hone
    revert hr
    cases hex : (_logrange_extra_Float64 a b n : JlX (X × X)) with
    | error e => simp [bind, Except.bind]
    | ok ex =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
      intro hr; subst hr
      refine ⟨by omega, rfl, rfl, rfl, fun h1 => ?_, fun h2 => ?_, fun h1 => ?_⟩
      · have hj1 : wrapInt IntTy.i64 1 = 1 := by decide
        simp (disch := omega) [logRangeGet, getindex_LogRange, JCheckbounds.checkbounds, checkbounds_logRange, checkboundsLinear,
          JLength.length, length_LogRange, bind, Except.bind, pure, Except.pure, hj1, h1]
      · have hj1 : wrapInt IntTy.i64 1 = 1 := by decide
        simp (disch := omega) [logRangeGet, getindex_LogRange, JCheckbounds.checkbounds, checkbounds_logRange, checkboundsLinear,
          JLength.length, length_LogRange, bind, Except.bind, pure, Except.pure, hj1,
          show (1 : Int) ≤ n.val by omega, show n.val ≠ 1 by omega]
      · simp [h1] at hone; exact hone

end LogRangeSpec

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)
open JuliaLean.base.float (FV FTy)

/-- `step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)`, range.jl:739. -/
instance : JStep (StepRangeLen F64 F64 F64 JInt64) F64 := ⟨step_StepRangeLen_AbstractFloat⟩
/-- `-(x::Float64) = neg_float(x)` (float.jl). -/
instance : JNeg F64 F64 := ⟨JuliaLean.base.float.neg_IEEEFloat⟩

@[simp] theorem wrap64_0 : wrapInt .i64 0 = 0 := by decide
@[simp] theorem wrap64_1 : wrapInt .i64 1 = 1 := by decide

section ShowRepr

/-- `show(io, r)` of a `StepRangeLen{Float64,Float64,Float64,Int}` (range.jl:1142), with
`repr(x::Float64)` (`ryu/`) and `repr(n::Int)` (show.jl) the typed parameters `reprF`, `reprI`. -/
def showSRL (reprF : F64 → String) (reprI : JInt64 → String) (r : StepRangeLen F64 F64 F64 JInt64) :
    JlX String :=
  letI : JRepr F64 := ⟨fun x => pure (reprF x)⟩
  letI : JRepr JInt64 := ⟨fun x => pure (reprI x)⟩
  show_StepRangeLen ⟨⟩ r

/-- The 2-argument `show` writes Julia code that reproduces the value (show/repr docstrings): for a
`Float64` `StepRangeLen(ref, step, len)` printed in colon form `A:S:B`, evaluating the text gives a
range with the same length and bitwise identical elements. `repr(::Float64)` is any printing that
`parse(Float64, _)` inverts and that writes no `:`; the `Float64` colon `a:s:b` (twiceprecision.jl)
is any function whose result starts at `a`. -/
def ShowReprElements : Prop :=
  ∀ (reprF : F64 → String) (parseF : String → Option F64) (reprI : JInt64 → String)
    (colonF : F64 → F64 → F64 → JlX (List F64)),
    (∀ x, parseF (reprF x) = some x) → (∀ x, ':' ∉ (reprF x).toList) →
    (∀ a s b xs, colonF a s b = .ok xs → xs.head? = some a) →
    ∀ (ref step : F64) (len : JInt64) (r : StepRangeLen F64 F64 F64 JInt64),
      JStepRangeLen3.stepRangeLen ref step len = .ok r →
      ∀ text, showSRL reprF reprI r = .ok text →
      ∀ (ta ts tb : String) (a s b : F64), text = ta ++ ":" ++ ts ++ ":" ++ tb →
        parseF ta = some a → parseF ts = some s → parseF tb = some b →
        ∀ xs, colonF a s b = .ok xs →
          xs.length = len.val.toNat ∧ ∀ i : JInt64, 1 ≤ i.val → i.val ≤ len.val →
            _getindex_AbstractRange r i = .ok (xs.getD (i.val.toNat - 1) (f64 0))

/-- A `Float64` printed as the decimal digits of its bit pattern. -/
def bitsRepr (x : F64) : String := toString x.toBits
/-- The inverse of `bitsRepr`. -/
def bitsParse (s : String) : Option F64 := some (f64 (Nat.ofDigitChars 10 s.toList 0))

theorem f64_toBits (x : F64) : f64 x.toBits = x := by
  rcases x with ⟨b⟩
  simp only [f64, JuliaLean.Promotion.Fl.ofBits, JuliaLean.Promotion.Fl.toBits]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt b.isLt)

theorem bitsParse_repr (x : F64) : bitsParse (bitsRepr x) = some x := by
  simp only [bitsParse, bitsRepr, Nat.toString_eq_ofList_toDigits, String.toList_ofList,
    Nat.ofDigitChars_ten_toDigits, f64_toBits]

theorem bitsRepr_noColon (x : F64) : ':' ∉ (bitsRepr x).toList := by
  simp only [bitsRepr, Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  intro h
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

/-- `0.3:0.1:0.8` as Julia evaluates it (twiceprecision.jl), printed by
`repro/show-range-repr-elements.jl`: `[0.3, 0.4, 0.5, 0.6, 0.7, 0.8]`. -/
def juliaColon038 : List F64 := [f64 4599075939470750515, f64 4600877379321698714,
  f64 4602678819172646912, f64 4603579539098121011, f64 4604480259023595110, f64 4605380978949069210]

/-- A `Float64` colon that returns Julia's elements for `0.3:0.1:0.8` and `[a]` otherwise. -/
def colonJ (a s b : F64) : JlX (List F64) :=
  if a = f64 4599075939470750515 ∧ s = f64 4591870180066957722 ∧ b = f64 4605380978949069210 then
    .ok juliaColon038 else .ok [a]

theorem colonJ_head (a s b : F64) (xs : List F64) (h : colonJ a s b = .ok xs) : xs.head? = some a := by
  unfold colonJ at h
  split at h
  · rename_i hc; cases h; rw [hc.1]; rfl
  · cases h; rfl

theorem showReprElements_refuted : ¬ ShowReprElements := by
  intro h
  have := (h bitsRepr bitsParse (fun _ => "") colonJ bitsParse_repr bitsRepr_noColon colonJ_head
    (f64 4599075939470750515) (f64 4591870180066957722) (lit .i64 6)
    ⟨f64 4599075939470750515, f64 4591870180066957722, lit .i64 6, lit .i64 1⟩ (by decide +kernel)
    (bitsRepr (f64 4599075939470750515) ++ ":" ++ bitsRepr (f64 4591870180066957722) ++ ":" ++
      bitsRepr (f64 4605380978949069210)) (by decide +kernel)
    _ _ _ _ _ _ rfl (bitsParse_repr _) (bitsParse_repr _) (bitsParse_repr _) juliaColon038
    (by decide +kernel)).2 (lit .i64 4) (by decide) (by decide)
  revert this; decide +kernel

end ShowRepr

section LinRangeFloat

/-- `LinRange(start, stop, len)` (range.jl:620, 616, 597) of `Float64` endpoints: "a range with
`len` linearly spaced elements between its `start` and `stop`" (LinRange docstring, range.jl:555):
it throws `ArgumentError` for a negative length and for length 1 with endpoints that differ;
otherwise `first(r) == start`, `last(r) == stop`, `length(r) == len`, `size(r) == (len,)`,
`isempty(r)` iff `len == 0`, and for `len != 1` the negation `-r` (range.jl:1325) has endpoints
`-start`, `-stop` and the same length. Stated for every `Float64` printer used in the error
messages. -/
def LinRangeFloatConstruct : Prop :=
  ∀ [JPrint F64] (a b : F64) (n : JInt64),
    (n.val < 0 → ∃ m, (LinRange_start_stop_len a b n : JlX (LinRange F64 JInt64)) =
      .error (.jl (.argumentError m))) ∧
    (n.val = 1 → JEq.eq a b = false → ∃ m, (LinRange_start_stop_len a b n : JlX (LinRange F64 JInt64)) =
      .error (.jl (.argumentError m))) ∧
    (0 ≤ n.val → (n.val = 1 → JEq.eq a b = true) → ∃ r : LinRange F64 JInt64,
      LinRange_start_stop_len a b n = .ok r ∧ JFirst.first r = .ok a ∧ JLast.last r = .ok b ∧
      JLength.length r = .ok n ∧ JIsempty.isempty r = .ok (decide (n.val = 0)) ∧
      size_AbstractRange r = .ok ⟨n⟩ ∧
      (n.val ≠ 1 → ∃ nr : LinRange F64 JInt64, neg_LinRange r = .ok nr ∧
        JFirst.first nr = .ok (JNeg.neg a) ∧ JLast.last nr = .ok (JNeg.neg b) ∧
        JLength.length nr = .ok n))

theorem linRangeFloatConstruct_proven : LinRangeFloatConstruct := by
  intro _ a b n
  refine ⟨fun hn => ?_, fun h1 hab => ?_, fun hn h1 => ?_⟩
  · simp [LinRange_start_stop_len, JLinRangeT.linRangeT, LinRange_T, JLinRangeTL.linRangeTL,
      LinRange_TL_new, show ¬ (0 ≤ n.val) by omega, wrap64_0, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  · simp [LinRange_start_stop_len, JLinRangeT.linRangeT, LinRange_T, JLinRangeTL.linRangeTL,
      LinRange_TL_new, h1, hab, wrap64_0, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have hle : (0 : Int) ≤ n.val := hn
    obtain ⟨d, hd⟩ : ∃ d, (JMax.max (n - (JOneunit.oneunit : JInt64)) (JOneunit.oneunit : JInt64) :
        JlX JInt64) = .ok d := ⟨_, max_same _ _⟩
    have hc : ∀ x y : F64, (LinRange_start_stop_len x y n : JlX (LinRange F64 JInt64)) =
        if n.val = 1 then (if JEq.eq x y = true then .ok ⟨x, y, n, n⟩ else .error (.jl (.argumentError
          ("range(" ++ JPrint.print x ++ ", stop=" ++ JPrint.print y ++ ", length=" ++ JPrint.print n ++
            "): endpoints differ"))))
        else .ok ⟨x, y, n, d⟩ := by
      intro x y
      simp [LinRange_start_stop_len, JLinRangeT.linRangeT, LinRange_T, JLinRangeTL.linRangeTL,
        LinRange_TL_new, hle, wrap64_0, hd, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, JType.isInteger, JMod.mod]
    have hneg : ∀ r : LinRange F64 JInt64, r.len = n → neg_LinRange r =
        (LinRange_start_stop_len (JNeg.neg r.start) (JNeg.neg r.stop) n : JlX (LinRange F64 JInt64)) := by
      intro r hr
      subst hr
      rfl
    by_cases h : n.val = 1
    · have hab := h1 h
      refine ⟨⟨a, b, n, n⟩, ?_, rfl, rfl, rfl, ?_, rfl, fun h' => absurd h h'⟩
      · rw [hc, if_pos h, if_pos hab]
      · simp [JIsempty.isempty, isempty_LinRange, JLength.length, length_LinRange, h, wrap64_0, bind,
          Except.bind, pure, Except.pure]
    · refine ⟨⟨a, b, n, d⟩, ?_, rfl, rfl, rfl, ?_, rfl, fun _ => ⟨⟨JNeg.neg a, JNeg.neg b, n, d⟩, ?_, rfl,
        rfl, rfl⟩⟩
      · rw [hc, if_neg h]
      · simp [JIsempty.isempty, isempty_LinRange, JLength.length, length_LinRange, wrap64_0, bind,
          Except.bind, pure, Except.pure]
      · rw [hneg _ rfl, hc, if_neg h]

end LinRangeFloat

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit binop mulSame)

section SRLIntSpec
variable {t : IntTy}

/-- `getindex(v::AbstractRange, i::Integer)` of an integer `StepRangeLen` (array.jl:3219): a
BitInteger index is not a `Bool`, so this is `_getindex(v, i)`, range.jl:952. -/
instance {q a s w l : IntTy} : JCheckbounds (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt l) :=
  ⟨checkboundsVector⟩
instance {q a s w l : IntTy} : JGetindex (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt l) (JInt q) :=
  ⟨_getindex_AbstractRange⟩
/-- `step(r::StepRangeLen) = r.step`, range.jl:738. -/
instance {q a s w : IntTy} : JStep (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) (JInt s) :=
  ⟨fun r => pure (step_StepRangeLen r)⟩

theorem mulSame_val {r : IntTy} (a b : JInt r) : (mulSame a b).val = wrapInt r (a.val * b.val) := by
  cases r <;> exact IntVal.mul_int_val a b

theorem binop_val_mul {s t : IntTy} (x : JInt s) (y : JInt t) :
    (binop mulSame x y).val = wrapInt (s.promote t) (x.val * y.val) := by
  unfold binop JuliaLean.base.int.op_Integer
  split <;> rw [mulSame_val, IntVal.remT_val, IntVal.remT_val, IntVal.wrapInt_mul_left,
    IntVal.wrapInt_mul_right]

@[simp] theorem mulMixed_iv {s t : IntTy} (x : JInt s) (y : JInt t) :
    (x * y : JInt (pTy s t)).val = wrapInt (pTy s t) (x.val * y.val) := by
  show (castJ _ (binop mulSame x y)).val = _
  rw [castJ_val, binop_val_mul, pTy_eq]

/-- `v` lies in the range of the BitInteger type `t`. -/
abbrev InT (t : IntTy) (v : Int) : Prop := t.min ≤ v ∧ v ≤ t.max

theorem pTy_i64_absorb (t : IntTy) : pTy t (pTy .i64 t) = pTy .i64 t := by cases t <;> rfl
theorem pTy_i64_wider (t : IntTy) : (pTy .i64 t).min ≤ t.min ∧ t.max ≤ (pTy .i64 t).max := by
  cases t <;> decide

/-- The element `ref + (i - offset) * step` of an integer `StepRangeLen`, read with
`unsafe_getindex` (range.jl:986), when it is representable in the element type. -/
theorem ugi_srl (ref step : JInt t) (len off i : JInt64)
    (hi : wrapInt .i64 (i.val - off.val) = i.val - off.val)
    (hv : InT t (ref.val + (i.val - off.val) * step.val)) :
    ((JUnsafeGetindex.unsafeGetindex (⟨ref, step, len, off⟩ : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64) i
      : JlX (JInt t))).map Subtype.val = .ok (ref.val + (i.val - off.val) * step.val) := by
  simp only [JUnsafeGetindex.unsafeGetindex, unsafe_getindex_StepRangeLen, oftype, convert_self,
    bind, Except.bind]
  have hval : (ref + (i - off) * step : JInt (pTy t (pTy .i64 t))).val =
      ref.val + (i.val - off.val) * step.val := by
    rw [addMixed_iv, mulMixed_iv, sub_iv, hi, pTy_i64_absorb, IntVal.wrapInt_add_right]
    have := pTy_i64_wider t
    exact wrap_in _ (by omega) (by omega)
  rw [convert_iv, dif_pos (by rw [hval]; exact hv)]
  simp [Except.map, hval]

/-- The value `ref + (i - offset) * step` of element `i` of `StepRangeLen(ref, step, len, offset)`. -/
abbrev srlE {t : IntTy} (ref step : JInt t) (off : JInt64) (i : Int) : Int := ref.val + (i - off.val) * step.val

/-- `StepRangeLen(ref, step, len, offset)` (range.jl:548), `StepRangeLen{T,R,S}` (range.jl:546) and
`StepRangeLen{T}` (range.jl:550) of BitInteger `ref` and `step` of one type `T` and an `Int`
length and offset, through the inner constructor (range.jl:533). StepRangeLen docstring
(range.jl:512-531): "A range `r` where `r[i]` produces values of type `T` ..., parameterized by a
`ref`erence value, a `step`, and the `len`gth. By default `ref` is the starting value `r[1]`, but
alternatively you can supply it as the value of `r[offset]` for some other index
`1 <= offset <= len`." The constructors throw `ArgumentError` for a negative length or an offset
outside `[1, max(1, len)]`; otherwise `length(r) == len`, `size(r) == (len,)`, `isempty(r)` iff
`len == 0`, `step(r) == step`, `r[i]` throws `BoundsError` unless `1 <= i <= len`, and
`r[i]`, `first(r)`, `last(r)` and the iteration protocol (`iterate(r)`, `iterate(r, k)`) give the
values `ref + (i - offset) * step` whenever these are representable in `T`. Iteration stops after
`len` elements (for `len < typemax(Int)`; see `range-srl-iterate-typemax`). -/
def SRLIntConstruct : Prop :=
  ∀ (t : IntTy) (ref step : JInt t) (len off : JInt64),
    (len.val < 0 → ∃ m, (StepRangeLen_ref_step ref step len off :
      JlX (StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)) = .error (.jl (.argumentError m))) ∧
    (0 ≤ len.val → ¬ (1 ≤ off.val ∧ off.val ≤ max 1 len.val) → ∃ m, (StepRangeLen_ref_step ref step len off :
      JlX (StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)) = .error (.jl (.argumentError m))) ∧
    (0 ≤ len.val → 1 ≤ off.val → off.val ≤ max 1 len.val →
      ∃ r : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64,
        StepRangeLen_ref_step ref step len off = .ok r ∧
        StepRangeLen_TRS (T := JInt t) ref step len off = .ok r ∧
        StepRangeLen_T (T := JInt t) ref step len off = .ok r ∧
        JLength.length r = .ok len ∧ JIsempty.isempty r = .ok (decide (len.val = 0)) ∧
        size_AbstractRange r = .ok ⟨len⟩ ∧ JStep.step r = .ok step ∧
        (∀ i : JInt64, ¬ (1 ≤ i.val ∧ i.val ≤ len.val) →
          (JGetindex.getindex r i : JlX (JInt t)) = .error (.jl .boundsError)) ∧
        (∀ i : JInt64, 1 ≤ i.val → i.val ≤ len.val → InT t (srlE ref step off i.val) →
          (JGetindex.getindex r i : JlX (JInt t)).map Subtype.val = .ok (srlE ref step off i.val)) ∧
        (1 ≤ len.val → InT t (srlE ref step off 1) →
          (JFirst.first r).map Subtype.val = .ok (srlE ref step off 1)) ∧
        (1 ≤ len.val → InT t (srlE ref step off len.val) →
          (JLast.last r).map Subtype.val = .ok (srlE ref step off len.val)) ∧
        (len.val = 0 → JIterate1.iterate r = .ok none) ∧
        (∀ k : JInt64, 0 ≤ k.val → k.val < len.val → InT t (srlE ref step off (k.val + 1)) →
          (JIterate2.iterate r k).map (Option.map fun p => (p.1.val, p.2.val)) =
            .ok (some (srlE ref step off (k.val + 1), k.val + 1))) ∧
        (len.val < IntTy.i64.max → JIterate2.iterate r len = .ok none))

theorem i64min : IntTy.i64.min = -9223372036854775808 := by decide
theorem i64max : IntTy.i64.max = 9223372036854775807 := by decide

theorem i64_bounds (x : JInt64) : -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 := x.property

theorem srl_ctor (ref step : JInt t) (len off : JInt64) :
    (StepRangeLen_ref_step ref step len off : JlX (StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)) =
      if 0 ≤ len.val then
        (if 1 ≤ off.val ∧ off.val ≤ max 1 len.val then .ok ⟨ref, step, len, off⟩
         else .error (.jl (.argumentError ("StepRangeLen: offset must be in [1," ++ JPrint.print len ++
           "], got " ++ JPrint.print off))))
      else .error (.jl (.argumentError ("length cannot be negative, got " ++ JPrint.print len))) := by
  simp only [StepRangeLen_ref_step, JStepRangeLenTRSL.stepRangeLenTRSL, StepRangeLen_TRSL_new,
    JType.isInteger, JIsinteger.isinteger, JuliaLean.base.number.isintegerInteger, convert_self,
    le_iv, max_same, bind, Except.bind, pure, Except.pure, zero_iv, oneunit_iv, throw, throwThe,
    MonadExceptOf.throw, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
  have hm : (if len.val < 1 then (JOneunit.oneunit : JInt64) else len).val = max 1 len.val := by
    by_cases h : len.val < 1 <;> simp [h, oneunit_iv] <;> omega
  simp only [hm]
  by_cases h0 : 0 ≤ len.val <;> by_cases h1 : 1 ≤ off.val ∧ off.val ≤ max 1 len.val <;> simp [h0, h1]

theorem srl_getindex (r : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64) (i : JInt64) (h0 : 0 ≤ r.len.val) :
    (JGetindex.getindex r i : JlX (JInt t)) =
      if 1 ≤ i.val ∧ i.val ≤ r.len.val then JUnsafeGetindex.unsafeGetindex r i
      else .error (.jl .boundsError) := by
  have hcb := checkboundsVector_eq r i r.len rfl h0
  simp only [JGetindex.getindex, _getindex_AbstractRange, JCheckbounds.checkbounds, hcb, checkboundsLinear,
    JLength.length, length_StepRangeLen, bind, Except.bind, pure, Except.pure]
  by_cases h : 1 ≤ i.val ∧ i.val ≤ r.len.val <;> simp [h, throw, throwThe, MonadExceptOf.throw]

theorem sRLIntConstruct_proven : SRLIntConstruct := by
  intro t ref step len off
  have hl := i64_bounds len; have ho := i64_bounds off
  refine ⟨fun h => ?_, fun h0 h1 => ?_, fun h0 h1 h2 => ?_⟩
  · rw [srl_ctor, if_neg (by omega)]; exact ⟨_, rfl⟩
  · rw [srl_ctor, if_pos h0, if_neg h1]; exact ⟨_, rfl⟩
  · have hok := srl_ctor ref step len off
    rw [if_pos h0, if_pos ⟨h1, h2⟩] at hok
    have hw : ∀ i : JInt64, 1 ≤ i.val → i.val ≤ len.val → wrapInt .i64 (i.val - off.val) = i.val - off.val :=
      fun i h3 h4 => wrap_in _ (by have := i64min; omega) (by have := i64max; omega)
    refine ⟨⟨ref, step, len, off⟩, hok, hok, hok, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [JIsempty.isempty, isempty_StepRangeLen, JLength.length, length_StepRangeLen, bind,
        Except.bind, pure, Except.pure]
    · intro i hi; rw [srl_getindex _ _ h0, if_neg hi]
    · intro i h3 h4 hv; rw [srl_getindex _ _ h0, if_pos ⟨h3, h4⟩]; exact ugi_srl ref step len off i (hw i h3 h4) hv
    · intro h3 hv
      have := ugi_srl ref step len off (jint 1) (hw (jint 1) (by simp) (by simp; omega)) (by simpa using hv)
      simpa [JFirst.first, first_StepRangeLen] using this
    · intro h3 hv
      exact ugi_srl ref step len off len (hw len h3 (Int.le_refl _)) hv
    · intro h3
      simp [JIterate1.iterate, iterate_StepRangeLen_LinRange, JLength.length, length_StepRangeLen, h3,
        bind, Except.bind, pure, Except.pure]
    · intro k h3 h4 hv
      have hk1 : (k + (JOneunit.oneunit : JInt64)).val = k.val + 1 := by
        rw [add_iv, oneunit_iv]; exact wrap_in _ (by have := i64min; omega) (by have := i64max; omega)
      have hu := ugi_srl ref step len off (k + JOneunit.oneunit) (hw _ (by omega) (by omega)) (by rw [hk1]; exact hv)
      simp only [JIterate2.iterate, iterate_StepRangeLen_LinRange, JLength.length, length_StepRangeLen,
        lt_iv, hk1, show ¬ (len.val < k.val + 1) by omega, decide_false, Bool.false_eq_true, ite_false,
        bind, Except.bind, pure, Except.pure]
      revert hu; rw [hk1]
      cases JUnsafeGetindex.unsafeGetindex (⟨ref, step, len, off⟩ : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)
        (k + JOneunit.oneunit) <;> simp [Except.map, hk1]
    · intro h3
      have hk1 : (len + (JOneunit.oneunit : JInt64)).val = len.val + 1 := by
        rw [add_iv, oneunit_iv]; exact wrap_in _ (by have := i64min; omega) (by have := i64max; omega)
      simp [JIterate2.iterate, iterate_StepRangeLen_LinRange, JLength.length, length_StepRangeLen,
        hk1, bind, Except.bind, pure, Except.pure]
      omega

/-- The iteration protocol (`iterate(r, state)`, range.jl:928): once the state of the last element
is reached, `iterate` returns `nothing`. For `StepRangeLen(ref, step, n)` of `Int`s the state after
the last element is `n`, so `iterate(r, n) === nothing` for every length `n`. -/
def SRLIterateEnds : Prop :=
  ∀ (ref step len : JInt64) (r : StepRangeLen JInt64 JInt64 JInt64 JInt64),
    StepRangeLen_ref_step ref step len (jint 1) = .ok r → JIterate2.iterate r len = .ok none

theorem sRLIterateEnds_refuted : ¬ SRLIterateEnds := by
  intro h
  have := h (lit .i64 0) (lit .i64 1) (lit .i64 9223372036854775807)
    ⟨lit .i64 0, lit .i64 1, lit .i64 9223372036854775807, lit .i64 1⟩ (by decide +kernel)
  revert this; decide +kernel

end SRLIntSpec

section FloatIter
open JuliaLean.base.float (FV FTy)

theorem succ64 (k : JInt64) :
    k + (JOneunit.oneunit : JInt64) = lit .i64 (k.val + 1) := by
  apply Subtype.ext
  rw [add_iv, oneunit_iv]
  rfl

/-- The iteration protocol of `Float64` `StepRangeLen` and `LinRange` (`iterate(r, i)`,
range.jl:928) agrees with indexing (an `AbstractVector` iterates its elements in index order):
`iterate(r)` and `iterate(r, k)` for `0 <= k < length(r)` return `(r[k+1], k+1)`, and
`iterate(r, length(r))` is `nothing` (for lengths below `typemax(Int)`). -/
def FloatIterateIndexed : Prop :=
  (∀ (r : StepRangeLen F64 F64 F64 JInt64) (k : JInt64), 0 ≤ k.val → k.val < r.len.val →
    JIterate2.iterate r k = (JGetindex.getindex r (lit .i64 (k.val + 1))).map
      (fun x => some (x, lit .i64 (k.val + 1)))) ∧
  (∀ r : StepRangeLen F64 F64 F64 JInt64, 0 ≤ r.len.val → r.len.val < IntTy.i64.max →
    JIterate2.iterate r r.len = .ok none) ∧
  (∀ r : StepRangeLen F64 F64 F64 JInt64, JIterate1.iterate r = JIterate2.iterate r (lit .i64 0)) ∧
  (∀ (r : LinRange F64 JInt64) (k : JInt64), 0 ≤ k.val → k.val < r.len.val →
    JIterate2.iterate r k = (JGetindex.getindex r (lit .i64 (k.val + 1))).map
      (fun x => some (x, lit .i64 (k.val + 1)))) ∧
  (∀ r : LinRange F64 JInt64, 0 ≤ r.len.val → r.len.val < IntTy.i64.max →
    JIterate2.iterate r r.len = .ok none) ∧
  (∀ r : LinRange F64 JInt64, JIterate1.iterate r = JIterate2.iterate r (lit .i64 0))

theorem floatIterateIndexed_proven : FloatIterateIndexed := by
  have hmax := i64max
  refine ⟨fun r k h0 h1 => ?_, fun r h0 h1 => ?_, fun r => rfl, fun r k h0 h1 => ?_, fun r h0 h1 => ?_,
    fun r => rfl⟩
  · have hl := i64_bounds r.len
    have hcb := checkboundsVector_eq r (lit .i64 (k.val + 1)) r.len rfl (by omega)
    simp only [JIterate2.iterate, iterate_StepRangeLen_LinRange, JLength.length, length_StepRangeLen,
      succ64 k, JGetindex.getindex, _getindex_AbstractRange, JCheckbounds.checkbounds, hcb,
      checkboundsLinear, lt_iv, bind, Except.bind, pure, Except.pure]
    have hv : (lit .i64 (k.val + 1)).val = k.val + 1 := by
      show wrapInt .i64 (k.val + 1) = _; have := i64min; exact wrap_in _ (by omega) (by omega)
    simp only [hv, show ¬ (r.len.val < k.val + 1) by omega, show 1 ≤ k.val + 1 ∧ k.val + 1 ≤ r.len.val from
      ⟨by omega, by omega⟩, decide_false, Bool.false_eq_true, ite_false]
    cases JUnsafeGetindex.unsafeGetindex r (lit .i64 (k.val + 1)) <;> rfl
  · have hv : (lit .i64 (r.len.val + 1)).val = r.len.val + 1 := by
      show wrapInt .i64 (r.len.val + 1) = _
      have := i64min; have := i64_bounds r.len; exact wrap_in _ (by omega) (by omega)
    simp [JIterate2.iterate, iterate_StepRangeLen_LinRange, JLength.length, length_StepRangeLen,
      succ64 r.len, hv, bind, Except.bind, pure, Except.pure]
    omega
  · have hl := i64_bounds r.len
    have hcb := checkboundsVector_eq r (lit .i64 (k.val + 1)) r.len rfl (by omega)
    simp only [JIterate2.iterate, iterate_StepRangeLen_LinRange, JLength.length, length_LinRange,
      succ64 k, JGetindex.getindex, _getindex_AbstractRange, JCheckbounds.checkbounds, hcb,
      checkboundsLinear, lt_iv, bind, Except.bind, pure, Except.pure]
    have hv : (lit .i64 (k.val + 1)).val = k.val + 1 := by
      show wrapInt .i64 (k.val + 1) = _; have := i64min; exact wrap_in _ (by omega) (by omega)
    simp only [hv, show ¬ (r.len.val < k.val + 1) by omega, show 1 ≤ k.val + 1 ∧ k.val + 1 ≤ r.len.val from
      ⟨by omega, by omega⟩, decide_false, Bool.false_eq_true, ite_false]
    cases JUnsafeGetindex.unsafeGetindex r (lit .i64 (k.val + 1)) <;> rfl
  · have hv : (lit .i64 (r.len.val + 1)).val = r.len.val + 1 := by
      show wrapInt .i64 (r.len.val + 1) = _
      have := i64min; have := i64_bounds r.len; exact wrap_in _ (by omega) (by omega)
    simp [JIterate2.iterate, iterate_StepRangeLen_LinRange, JLength.length, length_LinRange,
      succ64 r.len, hv, bind, Except.bind, pure, Except.pure]
    omega

end FloatIter

section KwErrors
variable {t s u l : IntTy}

/-- `_range(::Nothing, step::Any, ::Nothing, ::Nothing)`, range.jl:179. -/
instance : JRangeImpl Nothing (JInt s) Nothing Nothing Unit := ⟨_range_N_A_N_N⟩
/-- `_range(::Nothing, step::Any, stop::Any, ::Nothing)`, range.jl:181. -/
instance : JRangeImpl Nothing (JInt s) (JInt u) Nothing Unit := ⟨_range_N_A_A_N⟩
/-- `_range(start::Any, ::Nothing, ::Nothing, ::Nothing)`, range.jl:183. -/
instance : JRangeImpl (JInt t) Nothing Nothing Nothing Unit := ⟨_range_A_N_N_N⟩
/-- `_range(start::Any, step::Any, ::Nothing, ::Nothing)`, range.jl:187. -/
instance : JRangeImpl (JInt t) (JInt s) Nothing Nothing Unit := ⟨_range_A_A_N_N⟩
/-- `_range(start::Any, step::Any, stop::Any, len::Any)`, range.jl:190. -/
instance : JRangeImpl (JInt t) (JInt s) (JInt u) (JInt l) Unit := ⟨_range_A_A_A_A⟩

/-- The `range` docstring (range.jl:72-160): "Valid invocations of range are: call `range` with any
three of `start`, `step`, `stop`, `length`; with two of `start`, `stop`, `length` ...; with one of
`stop` or `length`." Every other combination throws `ArgumentError`: `range(; step)`,
`range(; step, stop)`, `range(start)`, `range(start; step)` and all four arguments, for BitInteger
arguments of any types. -/
def KeywordRangeErrors : Prop :=
  ∀ (t s u l : IntTy) (a : JInt t) (st : JInt s) (b : JInt u) (n : JInt l),
    (∃ m, (range_kw Nothing.nothing Nothing.nothing Nothing.nothing st : JlX Unit) =
      .error (.jl (.argumentError m))) ∧
    (∃ m, (range_kw Nothing.nothing b Nothing.nothing st : JlX Unit) = .error (.jl (.argumentError m))) ∧
    (∃ m, (range_start_kw a Nothing.nothing Nothing.nothing Nothing.nothing : JlX Unit) =
      .error (.jl (.argumentError m))) ∧
    (∃ m, (range_start_kw a Nothing.nothing Nothing.nothing st : JlX Unit) =
      .error (.jl (.argumentError m))) ∧
    (∃ m, (range_start_kw a b n st : JlX Unit) = .error (.jl (.argumentError m))) ∧
    (∃ m, (range_start_stop_kw a b n st : JlX Unit) = .error (.jl (.argumentError m)))

theorem keywordRangeErrors_proven : KeywordRangeErrors := by
  intro t s u l a st b n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [range_kw, range_start_kw, range_start_stop_kw, JRangeImpl.rangeImpl, _range_N_A_N_N,
    _range_N_A_A_N, _range_A_N_N_N, _range_A_A_N_N, _range_A_A_A_A, range_error, throw, throwThe,
    MonadExceptOf.throw]

end KwErrors

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section OneToOpsSpec
variable {t : IntTy}

/-- Julia's type tests on `Bool`: `Bool === Bool`, `Bool <: Integer`, `Bool` is not `Signed`. -/
instance : JType Bool where
  isBool := true
  isSigned := false
  isInteger := true
  isAbstractFloat := false
  bool_eq := fun _ => rfl
/-- `max(x, y) = ifelse(isless(y, x), x, y)` (operators.jl:572) on `Bool`, with
`isless(x::Real, y::Real) = x < y` (operators.jl), `<` on `Bool` (bool.jl) and the builtin
`Core.ifelse(c, x, y)`. -/
instance : JMax Bool Bool Bool := ⟨fun x y => pure (JuliaLean.base.operators.max
  (JuliaLean.base.operators.islessReal JuliaLean.base.bool.ltBool) (fun c x y => if c then x else y) x y)⟩

/-- `OneTo(m)` and `OneTo(n)` of one BitInteger type, which are `1:max(0,m)` and `1:max(0,n)`
(OneTo docstring, range.jl:449-460, and `OneToElements`): `==` (range.jl:1166) holds iff they have
the same elements; `issubset` (range.jl:1315) iff every element of the first is in the second;
`intersect` (range.jl:1206) and `union` (range.jl:1207) are the `OneTo` of the common and the
combined elements; `first(r, k)` (range.jl:872, "the first `k` elements") throws `ArgumentError`
for `k < 0` and is otherwise `OneTo(min(length(r), k))`; `OneTo(n)` stores `max(0, n)` and
`OneTo{Bool}(x)` throws `ArgumentError` (range.jl:483-492); and `OneTo{T}(a:b)` (range.jl:493) throws
`ArgumentError` unless `first(a:b) == 1`, giving `OneTo(b)` (whatever the range printing in the
messages). -/
def OneToOps : Prop :=
  ∀ (t : IntTy) (m n k a b : JInt t) (P : JPrint (UnitRange (JInt t))) (PB : JPrint Bool),
    (∀ x : Bool, ∃ msg, (letI := PB; OneTo_T_stop (T := Bool) x : JlX (OneTo Bool)) =
      .error (.jl (.argumentError msg))) ∧
    ∃ r s : OneTo (JInt t), JOneTo1.oneTo m = .ok r ∧ JOneTo1.oneTo n = .ok s ∧
    r.stop.val = max 0 m.val ∧
    eq_OneTo_OneTo r s = .ok (decide (max 0 m.val = max 0 n.val)) ∧
    issubset_OneTo_OneTo r s = decide (max 0 m.val ≤ max 0 n.val) ∧
    (∃ q : OneTo (JInt t), intersect_OneTo_OneTo r s = .ok q ∧ q.stop.val = min (max 0 m.val) (max 0 n.val)) ∧
    (∃ q : OneTo (JInt t), union_OneTo_OneTo r s = .ok q ∧ q.stop.val = max (max 0 m.val) (max 0 n.val)) ∧
    (k.val < 0 → ∃ msg, (first_OneTo_n r k : JlX (OneTo (JInt t))) = .error (.jl (.argumentError msg))) ∧
    (0 ≤ k.val → ∃ q : OneTo (JInt t), first_OneTo_n r k = .ok q ∧ q.stop.val = min (max 0 m.val) k.val) ∧
    (∀ u : UnitRange (JInt t), JColon2.colon a b = .ok u →
      (a.val ≠ 1 → ∃ msg, (letI := P; OneTo_T_range (T := JInt t) u : JlX (OneTo (JInt t))) =
        .error (.jl (.argumentError msg))) ∧
      (a.val = 1 → ∃ q : OneTo (JInt t), (letI := P; OneTo_T_range (T := JInt t) u) = .ok q ∧
        q.stop.val = max 0 b.val))

theorem oneToOps_proven : OneToOps := by
  intro t m n k a b P PB
  have hm := oneToStop_val m; have hn := oneToStop_val n
  refine ⟨fun x => ?_, _, _, oneTo_ok m, oneTo_ok n, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [OneTo_T_stop, JType.isBool, OneTo_T.throwbool, throw, throwThe, MonadExceptOf.throw, bind,
      Except.bind]
  · simp [eq_OneTo_OneTo, hm, hn, bind, Except.bind, pure, Except.pure]
  · simp [issubset_OneTo_OneTo, hm, hn]
  · refine ⟨⟨oneToStop (if (oneToStop n).val < (oneToStop m).val then oneToStop n else oneToStop m)⟩, ?_, ?_⟩
    · simp only [intersect_OneTo_OneTo, min_same, bind, Except.bind]
      exact oneTo_ok _
    · rw [oneToStop_val]; split <;> simp_all <;> omega
  · refine ⟨⟨oneToStop (if (oneToStop n).val < (oneToStop m).val then oneToStop m else oneToStop n)⟩, ?_, ?_⟩
    · simp only [union_OneTo_OneTo, max_same, bind, Except.bind]
      exact oneTo_ok _
    · rw [oneToStop_val]; split <;> simp_all <;> omega
  · intro hk
    simp [first_OneTo_n, hk, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · intro hk
    refine ⟨⟨oneToStop (if k.val < (oneToStop m).val then k else oneToStop m)⟩, ?_, ?_⟩
    · simp only [first_OneTo_n, lt_iv, jint0_val, show ¬ (k.val < 0) by omega, decide_false,
        Bool.false_eq_true, ite_false, min_same, oftype, convert_self, bind, Except.bind]
      exact oneTo_ok _
    · rw [oneToStop_val]; split <;> simp_all <;> omega
  · intro u hu
    rw [colon_unit] at hu
    cases hu
    have hs := unitStop_val a b
    obtain ⟨st, hst, hst1⟩ := step_unit (⟨a, unitStop a b⟩ : UnitRange (JInt t))
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · simp [OneTo_T_range, ha, OneTo_T_range.throwstart, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind]
    · refine ⟨⟨if (unitStop a b).val < (JZero.zero : JInt t).val then JZero.zero else unitStop a b⟩, ?_, ?_⟩
      · simp only [OneTo_T_range, first_unit, eq_iv, jint1_val, ha, hst, hst1, decide_true,
          JType.isBool, Bool.false_eq_true, ite_false, last_unit, max_same, bind,
          Except.bind, pure, Except.pure, Bool.false_eq_true]
        rfl
      · show (if (unitStop a b).val < (JZero.zero : JInt t).val then (JZero.zero : JInt t) else unitStop a b).val = _
        by_cases h1 : (unitStop a b).val < (JZero.zero : JInt t).val
        · rw [if_pos h1, zero_iv]; rw [zero_iv, hs, ha] at h1; revert h1; split <;> intro h1 <;> omega
        · rw [if_neg h1, hs, ha]; rw [zero_iv, hs, ha] at h1; revert h1; split <;> intro h1 <;> omega

end OneToOpsSpec

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section FloatUnitRange

/-- `x + y` of a `Float64` and an `Int`: promote the `Int` to `Float64` (`promotion.jl`,
float.jl:245), then `+` on `Float64` (float.jl:487). -/
instance : HAdd F64 JInt64 F64 :=
  ⟨fun x y => JuliaLean.base.float.add_IEEEFloat x (JuliaLean.base.float.float_BitSigned64 .f64 y)⟩

/-- `UnitRange(a, b)` of `Float64` endpoints (`UnitRange{T}(start::T, stop::T)`, range.jl:428, with
`unitrange_last(start, stop)`, range.jl:443): when `b < a` (or the endpoints are unordered) the
range is empty and "normalized to `a:a-1`" (`:` docstring, range.jl:54): `first(r) == a` and
`last(r) == a - 1`. Indexing `r[i]` (`_getindex(v::UnitRange{T}, i::Integer)`, range.jl:959, as
`Float64` is not `OverflowSafe`) throws `BoundsError` for `i <= 0`, and for `i >= 1` returns the
element `start + (i - 1)` ("elements spaced by 1 from start", UnitRange docstring) whenever it lies
in `[start, stop]`. -/
def FloatUnitRange : Prop :=
  (∀ a b : F64, JLe.le a b = false → ∃ r : UnitRange F64, UnitRange_T_T a b = .ok r ∧
    r.start = a ∧ JLast.last r = .ok (a - JOneunit.oneunit)) ∧
  (∀ (r : UnitRange F64) (i : JInt64), i.val ≤ 0 → _getindex_UnitRange r i = .error (.jl .boundsError)) ∧
  (∀ (r : UnitRange F64) (i : JInt64), 1 ≤ i.val →
    JLe.le (r.start + (i - JOneunit.oneunit : JInt64)) r.stop = true → JLe.le r.start (r.start + (i - JOneunit.oneunit : JInt64)) = true →
    _getindex_UnitRange r i = .ok (r.start + (i - JOneunit.oneunit : JInt64)))

theorem floatUnitRange_proven : FloatUnitRange := by
  refine ⟨fun a b h => ?_, fun r i hi => ?_, fun r i hi h1 h2 => ?_⟩
  · refine ⟨⟨a, a - JOneunit.oneunit⟩, ?_, rfl, rfl⟩
    simp [UnitRange_T_T, JUnitRangeT.unitRangeT, UnitRange_T_new, JUnitrangeLast.unitrangeLast,
      unitrange_last_Any, h, JConvert.convert, bind, Except.bind, pure, Except.pure]
  · simp [_getindex_UnitRange, _in_unit_range, lt_iv, show ¬ (0 < i.val) by omega, JConvert.convert,
      JThrowBoundserror.throwBoundserror, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]
  · simp only [_getindex_UnitRange, _in_unit_range, lt_iv, JConvert.convert, bind, Except.bind, pure,
      Except.pure]
    split
    · rfl
    · rename_i hne
      exfalso; apply hne
      simp only [Bool.and_eq_true, decide_eq_true_eq, jint0_val]
      exact ⟨⟨by omega, h1⟩, h2⟩

end FloatUnitRange

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section MixedStepColon

/-- `a:s:b` with BitInteger endpoints of type `T` and a step of another BitInteger type
(`(:)(start::T, step, stop::T) where {T<:Real}`, range.jl:65, and `_colon(start::T, step, stop::T)`,
range.jl:68): the endpoints are converted to `T′ = typeof(start + zero(step))`, which throws
`InexactError` when one of them is not representable in `T′`; once they convert, a zero step throws
`ArgumentError("step cannot be zero")` (StepRange docstring, range.jl:289-343). -/
def MixedStepColon : Prop :=
  ∀ (t s : IntTy) (a b : JInt t) (st : JInt s),
    (¬ InT (pTy t s) a.val → ∃ e, (colon_T_step_T_Real a st b : JlX (StepRange (JInt (pTy t s)) (JInt s))) =
      .error (.jl (.inexactError e))) ∧
    (InT (pTy t s) a.val → ¬ InT (pTy t s) b.val → ∃ e,
      (colon_T_step_T_Real a st b : JlX (StepRange (JInt (pTy t s)) (JInt s))) = .error (.jl (.inexactError e))) ∧
    (InT (pTy t s) a.val → InT (pTy t s) b.val → st.val = 0 →
      (colon_T_step_T_Real a st b : JlX (StepRange (JInt (pTy t s)) (JInt s))) =
        .error (.jl (.argumentError "step cannot be zero")))

theorem mixedStepColon_proven : MixedStepColon := by
  intro t s a b st
  refine ⟨fun ha => ?_, fun ha hb => ?_, fun ha hb hz => ?_⟩
  · refine ⟨(pTy t s).name, ?_⟩
    simp only [colon_T_step_T_Real, _colon_T_step_T, convert_iv, dif_neg ha, bind, Except.bind]
  · refine ⟨(pTy t s).name, ?_⟩
    simp only [colon_T_step_T_Real, _colon_T_step_T, convert_iv, dif_pos ha, dif_neg hb, bind, Except.bind]
  · simp [colon_T_step_T_Real, _colon_T_step_T, convert_iv, ha, hb, JStepRange3.stepRange,
      StepRange_T_S_T, JStepRangeTS.stepRangeTS, StepRange_TS_new, convert_self, bind, Except.bind,
      JSteprangeLast.steprangeLast, steprange_last, JType.isAbstractFloat, JType.isInteger,
      JIsinteger.isinteger, JuliaLean.base.number.isintegerInteger, hz, throw, throwThe, MonadExceptOf.throw]

end MixedStepColon

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section MixedColon
variable {s t : IntTy}

/-- The type object of a BitInteger type, as `promotion.jl` values carry it. -/
def intPType (t : IntTy) : JuliaLean.base.promotion.PType := .data ⟨"Core", t.name⟩ t.name [] none

/-- `promote(x, y)` of BitIntegers of two different types (promotion.jl:423,
`promoteTwoValues`): `_promote(x, y)` (promotion.jl:397, `promotePairValues`) converts both to
`R = promote_type(T, S)` (`pTy`, int.jl:809-822) with `convert` of `base/int.jl`; `not_sametype`
of `(x, y)` and `(px, py)`, whose types differ, is `nothing` (promotion.jl:445,
`notSameTypeDifferent`). -/
instance (priority := low) : JPromote2 (JInt s) (JInt t) (JInt (pTy s t)) := ⟨fun x y =>
  liftJl (JuliaLean.base.promotion.promoteTwoValues
    (JuliaLean.base.promotion.promotePairValues (fun _ _ => pure (intPType (pTy s t)))
      (fun _ v => JuliaLean.base.int.convert (pTy s t) v)
      (fun _ v => JuliaLean.base.int.convert (pTy s t) v))
    JuliaLean.base.promotion.notSameTypeDifferent x y)⟩

/-- `not_sametype(x, y) = nothing` (promotion.jl:445) for the argument and promoted pairs of
`UnitRange(start, stop)`, whose types differ. -/
instance (priority := low) : JNotSametype (JInt s × JInt t) (JInt (pTy s t) × JInt (pTy s t)) :=
  ⟨fun x y => liftJl (JuliaLean.base.promotion.notSameTypeDifferent x y)⟩

theorem promote_iv (a : JInt s) (b : JInt t) :
    (JPromote2.promote a b : JlX (JInt (pTy s t) × JInt (pTy s t))) =
      if h : InT (pTy s t) a.val ∧ InT (pTy s t) b.val then .ok (⟨a.val, h.1⟩, ⟨b.val, h.2⟩)
      else .error (.jl (.inexactError (pTy s t).name)) := by
  simp only [JPromote2.promote, JuliaLean.base.promotion.promoteTwoValues,
    JuliaLean.base.promotion.promotePairValues, JuliaLean.base.promotion.notSameTypeDifferent,
    JuliaLean.base.int.convert, JInt.convert]
  by_cases ha : InT (pTy s t) a.val <;> by_cases hb : InT (pTy s t) b.val <;>
    simp [ha, hb, InT, liftJl, bind, Except.bind, pure, Except.pure] at * 

/-- `a:b` for integers `a`, `b` of two BitInteger types (`(:)(a::Real, b::Real) =
(:)(promote(a, b)...)`, range.jl:3) and `UnitRange(a, b)` (range.jl:432-436) promote both to
`R = promote_type(typeof(a), typeof(b))` (colon docstring, range.jl:30-50, "a `UnitRange` when `a`
and `b` are integers"; `promote` docstring): when both are representable in `R` the result is the
unit range of `R` whose elements are `a, a+1, ..., b` (empty when `b < a`), and `UnitRange(r)` of
it (range.jl:1352) is the same range; otherwise `InexactError`. -/
def MixedUnitColon : Prop :=
  ∀ (s t : IntTy) (a : JInt s) (b : JInt t),
    (InT (pTy s t) a.val → InT (pTy s t) b.val →
      ∃ r : UnitRange (JInt (pTy s t)), colon_Real_Real a b = .ok r ∧ UnitRange_Any_Any a b = .ok r ∧
        (JFirst.first r).map Subtype.val = .ok a.val ∧
        (∀ fuel, (b.val - a.val).toNat < fuel → iterVals r fuel = .ok (intsFromTo a.val b.val)) ∧
        (UnitRange_AbstractUnitRange r : JlX (UnitRange (JInt (pTy s t)))) = .ok r) ∧
    (¬ (InT (pTy s t) a.val ∧ InT (pTy s t) b.val) → ∃ m,
      (colon_Real_Real a b : JlX (UnitRange (JInt (pTy s t)))) = .error (.jl (.inexactError m)) ∧
      (UnitRange_Any_Any a b : JlX (UnitRange (JInt (pTy s t)))) = .error (.jl (.inexactError m)))

theorem mixedUnitColon_proven : MixedUnitColon := by
  intro s t a b
  refine ⟨fun ha hb => ?_, fun hn => ⟨(pTy s t).name, ?_, ?_⟩⟩
  · refine ⟨⟨⟨a.val, ha⟩, unitStop ⟨a.val, ha⟩ ⟨b.val, hb⟩⟩, ?_, ?_, by simp [Except.map], ?_, ?_⟩
    · simp only [colon_Real_Real, promote_iv, dif_pos (And.intro ha hb), bind, Except.bind]
      exact colon_unit _ _
    · simp only [UnitRange_Any_Any, promote_iv, dif_pos (And.intro ha hb), bind, Except.bind,
        JNotSametype.notSametype, JuliaLean.base.promotion.notSameTypeDifferent, liftJl]
      exact colon_unit _ _
    · intro fuel hf
      exact iterVals_unitStop (t := pTy s t) ⟨a.val, ha⟩ ⟨b.val, hb⟩ fuel hf
    · simp only [UnitRange_AbstractUnitRange, first_unit, last_unit, bind, Except.bind]
      refine (colon_unit _ _).trans ?_
      congr 2
      apply Subtype.ext
      simp only [unitStop_val]; split <;> (try split) <;> omega
  · simp only [colon_Real_Real, promote_iv, dif_neg hn, bind, Except.bind]
  · simp only [UnitRange_Any_Any, promote_iv, dif_neg hn, bind, Except.bind]

end MixedColon

section UnitIndexQueries
variable {t : IntTy}

/-- `eachindex(A::AbstractVector) = (@inline(); axes1(A))` (abstractarray.jl:325,
`eachindexVector`) of a unit range, with `axes1` as in `checkboundsVector`. -/
instance : JEachindex (UnitRange (JInt t)) (OneTo (JInt (lenTy t))) := ⟨fun r => ofArr
  (JuliaLean.base.abstractarray.eachindexVector (JuliaLean.base.abstractarray.axes1 (fun a => toArr (do
    let sz ← size_AbstractRange a
    return [unchecked_oneto sz._1]))) r)⟩

theorem lengthUnit_fits (a b : JInt t) (h : cnt a.val b.val ≤ (lenTy t).max) :
    ∃ n : JInt (lenTy t), lengthUnit (⟨a, unitStop a b⟩ : UnitRange (JInt t)) = .ok n ∧
      n.val = cnt a.val b.val := by
  have hl := lengthUnit_colon a b
  have h0 : (lenTy t).min ≤ cnt a.val b.val := by
    have := min_le_zero (lenTy t); unfold cnt; split <;> omega
  rw [wrap_in _ h0 h] at hl
  cases hq : lengthUnit (⟨a, unitStop a b⟩ : UnitRange (JInt t)) with
  | error e => rw [hq] at hl; cases hl
  | ok n => rw [hq] at hl; simp [Except.map] at hl; exact ⟨n, rfl, hl⟩

/-- For a unit range `r = a:b` of BitIntegers whose element count `n` fits its length type:
`argmin(r)` is `1` and `argmax(r)` is `n`, the indices of its smallest and largest elements
(argmin/argmax docstrings), and both throw `ArgumentError` when `r` is empty; `isassigned(r, i)`
holds exactly for `1 <= i <= n`, for an index of any BitInteger type (isassigned docstring); and
`sortperm(r)` is the identity permutation `OneTo(n)` (sortperm docstring; `r` is sorted). -/
def UnitIndexQueries : Prop :=
  ∀ (t : IntTy) (a b : JInt t), cnt a.val b.val ≤ (lenTy t).max →
    ∃ r : UnitRange (JInt t), JColon2.colon a b = .ok r ∧
    (b.val < a.val →
      (∃ m, (argmin_AbstractRange r : JlX (JInt (lenTy t))) = .error (.jl (.argumentError m))) ∧
      (∃ m, (argmax_AbstractRange r : JlX (JInt (lenTy t))) = .error (.jl (.argumentError m)))) ∧
    (a.val ≤ b.val →
      (argmin_AbstractRange r : JlX (JInt (lenTy t))).map Subtype.val = .ok 1 ∧
      (argmax_AbstractRange r : JlX (JInt (lenTy t))).map Subtype.val = .ok (b.val - a.val + 1)) ∧
    (∀ (s : IntTy) (i : JInt s),
      isassigned_AbstractRange r i = .ok (decide (1 ≤ i.val ∧ i.val ≤ cnt a.val b.val))) ∧
    (∃ p : OneTo (JInt (lenTy t)), sortperm_AbstractUnitRange r = .ok p ∧ p.stop.val = cnt a.val b.val)

theorem unitIndexQueries_proven : UnitIndexQueries := by
  intro t a b hc
  obtain ⟨n, hn, hnv⟩ := lengthUnit_fits a b hc
  have hs := unitStop_val a b
  have h1 : (lit (lenTy t) 1).val = 1 := by cases t <;> decide
  refine ⟨⟨a, unitStop a b⟩, colon_unit a b, fun hab => ⟨⟨"range must be non-empty", ?_⟩, ⟨"range must be non-empty", ?_⟩⟩, fun hab => ⟨?_, ?_⟩, ?_, ?_⟩
  · simp [argmin_AbstractRange, hs, show ¬ a.val ≤ b.val by omega,
      bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    intro h; omega
  · simp [argmax_AbstractRange, hs, show ¬ a.val ≤ b.val by omega,
      bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    intro h; omega
  · obtain ⟨st, hst, hst1⟩ := step_unit (⟨a, unitStop a b⟩ : UnitRange (JInt t))
    rw [if_pos hab] at hs
    simp [argmin_AbstractRange, hs, show ¬ b.val < a.val by omega, hst, hst1, JFirstindex.firstindex,
      h1, Except.map, bind, Except.bind, pure, Except.pure]
  · obtain ⟨st, hst, hst1⟩ := step_unit (⟨a, unitStop a b⟩ : UnitRange (JInt t))
    rw [if_pos hab] at hs
    unfold cnt at hnv; simp [hab] at hnv
    simp [argmax_AbstractRange, hs, show ¬ b.val < a.val by omega, hst, hst1, JLastindex.lastindex,
      JLength.length, hn, hnv, Except.map, bind, Except.bind, pure, Except.pure]
  · intro s i
    by_cases hb : JType.isBool (JInt s) = true
    · simp [JType.isBool] at hb
    simp [isassigned_AbstractRange, JFirstindex.firstindex, JLastindex.lastindex, JLength.length, hn,
      h1, hnv, bind, Except.bind, pure, Except.pure, JType.isBool]
    by_cases h : 1 ≤ i.val <;> simp [h] <;> omega
  · refine ⟨⟨n⟩, ?_, hnv⟩
    simp [sortperm_AbstractUnitRange, JEachindex.eachindex, JuliaLean.base.abstractarray.eachindexVector,
      JuliaLean.base.abstractarray.axes1, size_AbstractRange, JLength.length, hn, toArr, ofArr,
      bind, Except.bind, pure, Except.pure, JuliaLean.base.abstractarray.tupleGet,
      JuliaLean.base.abstractarray.int, JInt.lit, JInt.wrap, unchecked_oneto]

end UnitIndexQueries

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section StepExtrema
variable {t : IntTy}

theorem mem_stepInts (x a s b : Int) :
    x ∈ stepInts a s b ↔ ∃ k : Nat, (k : Int) < stepCount a s b ∧ x = a + k * s := by
  unfold stepInts
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩

/-- The elements of `a:s:b` lie between its first element `a` and its last `a + (n-1)*s`. -/
theorem stepInts_between (a s b : Int) (k : Nat) (hk : (k : Int) < stepCount a s b) :
    (0 < s → a ≤ a + k * s ∧ a + k * s ≤ a + (stepCount a s b - 1) * s) ∧
    (s < 0 → a + (stepCount a s b - 1) * s ≤ a + k * s ∧ a + k * s ≤ a) := by
  refine ⟨fun hs => ⟨?_, ?_⟩, fun hs => ⟨?_, ?_⟩⟩
  · have := Int.mul_nonneg (show (0 : Int) ≤ k by omega) (show 0 ≤ s by omega); omega
  · have := Int.mul_le_mul_of_nonneg_right (show (k : Int) ≤ stepCount a s b - 1 by omega)
      (show 0 ≤ s by omega); omega
  · have := Int.mul_le_mul_of_nonpos_right (show (k : Int) ≤ stepCount a s b - 1 by omega)
      (show s ≤ 0 by omega); omega
  · have := Int.mul_le_mul_of_nonpos_right (show (0 : Int) ≤ k by omega) (show s ≤ 0 by omega)
    simp at this; omega

/-- `minimum`/`maximum` of `a:s:b` (range.jl:883-884). -/
theorem minmax_step (a s b l : JInt t) (hs : s.val ≠ 0) (hlv : l.val = lastVal a.val s.val b.val) :
    (stepCount a.val s.val b.val = 0 →
      minimum_AbstractRange (M := JInt t) (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) =
        .error (.jl (.argumentError "range must be non-empty")) ∧
      maximum_AbstractRange (M := JInt t) (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) =
        .error (.jl (.argumentError "range must be non-empty"))) ∧
    (0 < stepCount a.val s.val b.val →
      minimum_AbstractRange (M := JInt t) (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) =
        .ok (if l.val < a.val then l else a) ∧
      maximum_AbstractRange (M := JInt t) (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) =
        .ok (if l.val < a.val then a else l)) := by
  have hemp := isempty_lastVal a.val s.val b.val hs
  rw [← hlv] at hemp
  have hc := stepCount_nonneg a.val s.val b.val
  refine ⟨fun h0 => ?_, fun hpos => ?_⟩
  · have he : (decide (a.val ≠ l.val) && (decide (0 < s.val) != decide (a.val < l.val))) = true := by
      rw [hemp]; simp [h0]
    simp only [minimum_AbstractRange, maximum_AbstractRange, isempty_step, he, bind, Except.bind,
      ite_true]
    refine ⟨?_, ?_⟩ <;> first | rfl | trivial
  · have he : (decide (a.val ≠ l.val) && (decide (0 < s.val) != decide (a.val < l.val))) = false := by
      rw [hemp]; simp; omega
    simp only [minimum_AbstractRange, maximum_AbstractRange, isempty_step, he, bind, Except.bind,
      Bool.false_eq_true, ite_false, first_step, last_step, min_same, max_same]
    refine ⟨?_, ?_⟩ <;> first | rfl | trivial

/-- `a:s:b` for integers of one BitInteger type (`(:)(start::T, step::T, stop::T)`,
range.jl:22): `minimum(r)` and `maximum(r)` (range.jl:883-884, "the smallest/largest element",
docstrings of `minimum`/`maximum`) are the least and greatest of its elements `a, a+s, ...`
between `a` and `b`, and throw `ArgumentError` when it has none; `extrema(r)` (range.jl:885) is
the pair of them. -/
def StepRangeExtrema : Prop :=
  ∀ (t : IntTy) (a s b : JInt t) (r : StepRange (JInt t) (JInt t)), JColon3.colon a s b = .ok r →
    (stepInts a.val s.val b.val = [] →
      minimum_AbstractRange (M := JInt t) r = .error (.jl (.argumentError "range must be non-empty")) ∧
      maximum_AbstractRange (M := JInt t) r = .error (.jl (.argumentError "range must be non-empty"))) ∧
    (stepInts a.val s.val b.val ≠ [] → ∃ lo hi : JInt t,
      minimum_AbstractRange r = .ok lo ∧ maximum_AbstractRange r = .ok hi ∧
      lo.val ∈ stepInts a.val s.val b.val ∧ hi.val ∈ stepInts a.val s.val b.val ∧
      ∀ x ∈ stepInts a.val s.val b.val, lo.val ≤ x ∧ x ≤ hi.val)

theorem stepRangeExtrema_proven : StepRangeExtrema := by
  intro t a s b r hr
  by_cases hs : s.val = 0
  · rw [colon_step_zero a s b hs] at hr; cases hr
  obtain ⟨l, hc, _, hlv⟩ := colon_step a s b hs
  rw [hc] at hr; cases hr
  have hmm := minmax_step a s b l hs hlv
  have hcn := stepCount_nonneg a.val s.val b.val
  refine ⟨fun h => hmm.1 ((stepInts_nil_iff _ _ _).mp h), fun h => ?_⟩
  have hpos : 0 < stepCount a.val s.val b.val := by
    have := mt (stepInts_nil_iff a.val s.val b.val).mpr h; omega
  obtain ⟨h1, h2⟩ := hmm.2 hpos
  have hl := lastVal_count a.val s.val b.val hs hpos
  rw [← hlv] at hl
  have hmemA : a.val ∈ stepInts a.val s.val b.val :=
    (mem_stepInts _ _ _ _).mpr ⟨0, by simpa using hpos, by simp⟩
  have hmemL : l.val ∈ stepInts a.val s.val b.val :=
    (mem_stepInts _ _ _ _).mpr ⟨(stepCount a.val s.val b.val - 1).toNat, by omega, by
      rw [hl]; congr 2; omega⟩
  have hall : ∀ x ∈ stepInts a.val s.val b.val,
      (0 < s.val → a.val ≤ x ∧ x ≤ l.val) ∧ (s.val < 0 → l.val ≤ x ∧ x ≤ a.val) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (mem_stepInts _ _ _ _).mp hx
    have := stepInts_between a.val s.val b.val k hk
    rw [hl]; exact this
  refine ⟨_, _, h1, h2, ?_, ?_, ?_⟩
  · split <;> assumption
  · split <;> assumption
  · intro x hx
    have := hall x hx
    by_cases hp : 0 < s.val
    · have := this.1 hp; split <;> omega
    · have := this.2 (by omega); split <;> omega

end StepExtrema

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit remT)

section StepLength
variable {t : IntTy}

/-- `divPromoted` (same-type `div` after `promote`) on two unsigned BitIntegers is floor division
with `DivideError` for a zero divisor: the law `base/int.jl`'s mixed methods need. -/
theorem divPromoted_unsignedSpec : JuliaLean.Proofs.base.int.UnsignedDivSpec divPromoted := by
  intro a b ha hb x y
  have hab : a.signed = b.signed := by rw [ha, hb]
  have hx : wrapInt (a.promote b) x.val = x.val := IntVal.widen_promote_left hab x
  have hy : wrapInt (a.promote b) y.val = y.val := IntVal.widen_promote_right hab y
  have hP : (a.promote b).signed = false := by cases a <;> cases b <;> simp_all [IntTy.signed] <;> rfl
  simp only [divPromoted]
  rw [JuliaLean.Proofs.base.int.divSame_eq]
  simp only [IntVal.remT_val, hx, hy, hP, Bool.false_eq_true, false_and, or_false]
  have hx0 := IntVal.nonneg_of_unsigned ha x
  have hy0 := IntVal.nonneg_of_unsigned hb y
  split
  · rfl
  · congr 2
    exact Int.tdiv_eq_ediv_of_nonneg hx0

theorem div64_signed (x : JInt .i64) (y : JInt t) (ht : t.bits ≤ 32) (hts : t.signed = true)
    (hy : y.val ≠ 0) (hx : x.val ≠ -9223372036854775808) :
    ∃ q : JInt (divTyR .i64 t), (JDiv.div x y : JlX (JInt (divTyR .i64 t))) = .ok q ∧
      q.val = x.val.tdiv y.val := by
  have hxb := x.property
  have hyb := y.property
  have hP : IntTy.i64.promote t = .i64 := by
    cases t <;> simp [IntTy.bits, IntTy.signed] at ht hts <;> rfl
  have hD : divTyR .i64 t = .i64 := by
    cases t <;> simp [IntTy.bits, IntTy.signed] at ht hts <;> rfl
  have hsg : (IntTy.i64.signed = t.signed) := by rw [hts]; rfl
  have hxs : wrapInt (IntTy.i64.promote t) x.val = x.val := IntVal.widen_promote_left hsg x
  have hys : wrapInt (IntTy.i64.promote t) y.val = y.val := IntVal.widen_promote_right hsg y
  simp only [JDiv.div, divPromoted, hsg, ↓reduceIte]
  rw [JuliaLean.Proofs.base.int.divSame_eq]
  simp only [IntVal.remT_val, hxs, hys]
  rw [if_neg (by rw [hP]; simp only [i64min]; omega)]
  refine ⟨_, rfl, ?_⟩
  simp only [IntVal.remT_val, IntVal.lit_val, hP, hD, IntVal.wrapInt_wrapInt]
  have hb := Int.natAbs_tdiv_le_natAbs x.val y.val
  apply wrapInt_of_inRange
  simp only [i64min, i64max] at hxb ⊢
  omega

theorem div64_unsigned (x : JInt .i64) (y : JInt t) (ht : t.bits ≤ 32) (hts : t.signed = false)
    (hy : y.val ≠ 0) :
    ∃ q : JInt (divTyR .i64 t), (JDiv.div x y : JlX (JInt (divTyR .i64 t))) = .ok q ∧
      q.val = x.val.tdiv y.val := by
  have hxb := x.property
  obtain ⟨z, hz, hzv⟩ := JuliaLean.Proofs.base.int.div_BitSigned_Unsigned_form divPromoted
    divPromoted_unsignedSpec (s := .i64) rfl hts x y
  have hD : divTyR .i64 t = .i64 := by
    cases t <;> simp [IntTy.bits, IntTy.signed] at ht hts <;> rfl
  simp only [JDiv.div, show IntTy.i64.signed = true from rfl, hts, Bool.true_eq_false, ↓reduceIte, hz, if_neg hy]
  refine ⟨_, rfl, ?_⟩
  simp only [Except.map, liftJl, IntVal.remT_val, hD]
  rw [hzv hy]
  have hy0 := IntVal.nonneg_of_unsigned hts y
  have hb := JuliaLean.Proofs.base.int.tdiv_between x.val y.val (by omega)
  apply wrapInt_of_inRange
  simp only [i64min, i64max] at hxb ⊢
  omega

theorem div64_val (x : JInt .i64) (y : JInt t) (ht : t.bits ≤ 32) (hy : y.val ≠ 0)
    (hx : x.val ≠ -9223372036854775808) :
    ∃ q : JInt (divTyR .i64 t), (JDiv.div x y : JlX (JInt (divTyR .i64 t))) = .ok q ∧
      q.val = x.val.tdiv y.val := by
  cases hts : t.signed
  · exact div64_unsigned x y ht hts hy
  · exact div64_signed x y ht hts hy hx

/-- A value of a BitInteger type of at most 32 bits, as an `Int`. -/
def wid (x : JInt t) (ht : t.bits ≤ 32) : JInt .i64 :=
  ⟨x.val, by
    have := x.property
    cases t <;> simp [IntTy.bits] at ht <;>
      simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] at this ⊢ <;> omega⟩

theorem ctor_wid (x : JInt t) (ht : t.bits ≤ 32) : (JCtor.ctor x : JlX (JInt .i64)) = .ok (wid x ht) := by
  simp only [ctor_iv, convert_iv,
    dif_pos (show IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max from (wid x ht).property)]; rfl

theorem small_bounds (x : JInt t) (ht : t.bits ≤ 32) :
    -4294967296 ≤ x.val ∧ x.val ≤ 4294967295 := by
  have := x.property
  cases t <;> simp [IntTy.bits] at ht <;>
    simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] at this ⊢ <;> omega

theorem count_tdiv (a s b : Int) (hs : s ≠ 0) (hc : 0 < stepCount a s b) :
    (lastVal a s b - a).tdiv s = stepCount a s b - 1 := by
  rw [lastVal_count a s b hs hc, show a + (stepCount a s b - 1) * s - a = (stepCount a s b - 1) * s by omega]
  exact Int.mul_tdiv_cancel _ hs

/-- `length(r::OrdinalRange{<:smallints})` (range.jl:853) of `a:s:b` is its number of elements. -/
theorem length_small_val (a s b l : JInt t) (ht : t.bits ≤ 32) (hs : s.val ≠ 0)
    (hlv : l.val = lastVal a.val s.val b.val) :
    (length_OrdinalRange_smallints (⟨a, s, l⟩ : StepRange (JInt t) (JInt t))).map Subtype.val =
      .ok (stepCount a.val s.val b.val) := by
  have hemp := isempty_lastVal a.val s.val b.val hs
  rw [← hlv] at hemp
  have hc := stepCount_nonneg a.val s.val b.val
  have hba := small_bounds a ht; have hbl := small_bounds l ht; have hbs := small_bounds s ht
  have hbb := small_bounds b ht
  unfold length_OrdinalRange_smallints
  simp only [step_step, isempty_step, hemp, bind, Except.bind]
  by_cases h0 : stepCount a.val s.val b.val = 0
  · simp [h0, pure, Except.pure, Except.map]
  · have hpos : 0 < stepCount a.val s.val b.val := by omega
    simp only [h0, decide_false, Bool.false_eq_true, ite_false, last_step, first_step, ctor_wid _ ht]
    have hsub : (@HSub.hSub (JInt .i64) (JInt .i64) (JInt .i64) (@instHSub (JInt .i64) _)
        (wid l ht) (wid a ht)).val = l.val - a.val := by
      rw [coreSub_val]; apply wrapInt_of_inRange; simp only [wid, i64min, i64max]; omega
    obtain ⟨q, hq, hqv⟩ := div64_val (@HSub.hSub (JInt .i64) (JInt .i64) (JInt .i64)
      (@instHSub (JInt .i64) _) (wid l ht) (wid a ht)) s ht hs (by rw [hsub]; omega)
    rw [hq]
    rw [hsub, hlv, count_tdiv _ _ _ hs hpos] at hqv
    have hcb : stepCount a.val s.val b.val ≤ 8589934592 := by
      have := stepCount_bound a.val s.val b.val (stepCount a.val s.val b.val - 1) (by omega) (by omega)
      have h1 : (stepCount a.val s.val b.val - 1) * s.val ≤ 8589934591 ∧
          -8589934591 ≤ (stepCount a.val s.val b.val - 1) * s.val := by omega
      have h2 : 0 ≤ stepCount a.val s.val b.val - 1 := by omega
      rcases Int.lt_or_gt_of_ne hs with hn | hp
      · have := Int.mul_le_mul_of_nonneg_left (show s.val ≤ -1 by omega) h2
        omega
      · have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ s.val by omega) h2
        omega
    have hq64 : IntTy.i64.min ≤ q.val ∧ q.val ≤ IntTy.i64.max := by
      rw [hqv, i64min, i64max]; omega
    simp only [ctor_iv, convert_iv, dif_pos hq64, pure, Except.pure, Except.map]
    congr 1
    rw [coreAdd_val]; simp only [hqv, jint1_val]
    rw [show stepCount a.val s.val b.val - 1 + 1 = stepCount a.val s.val b.val by omega]
    apply wrapInt_of_inRange; rw [i64min, i64max]; omega

/-! ### `length` for 64- and 128-bit ranges -/

theorem wrap_cross (T U : IntTy) (h : T.bits = U.bits) (z : Int) :
    wrapInt T (wrapInt U z) = wrapInt T z :=
  IntVal.wrapInt_congr T (by rw [h]; exact IntVal.wrapInt_emod_self U z)

theorem wrap_cross_neg (T U : IntTy) (h : T.bits = U.bits) (z : Int) :
    wrapInt T (-(wrapInt U z)) = wrapInt T (-z) :=
  IntVal.wrapInt_congr T (by
    rw [show -(wrapInt U z) = 0 - wrapInt U z by omega, show -z = 0 - z by omega, Int.sub_emod, h,
      IntVal.wrapInt_emod_self U z, ← Int.sub_emod])

theorem toUnsigned_bits (t : IntTy) : t.toUnsigned.bits = t.bits := by cases t <;> rfl
theorem toSigned_bits (t : IntTy) : t.toSigned.bits = t.bits := by cases t <;> rfl

/-- `flipsign(x, y)` of two values of one BitInteger type (`base/int.jl:188` for signed types; for
unsigned types `y` is never negative and `x` is returned). -/
theorem flipsign_tt (x y : JInt t) :
    (JuliaLean.base.int.flipsign x y).val = wrapInt t (if y.val < 0 then -x.val else x.val) := by
  cases hts : t.signed
  · have hy0 := IntVal.nonneg_of_unsigned hts y
    rw [if_neg (by omega), IntVal.wrapInt_val]
    simp only [JuliaLean.base.int.flipsign, hts, Bool.false_eq_true, ↓reduceIte,
      JuliaLean.base.int.flipsign_Real, JuliaLean.base.int.Generic.flipsign_Real,
      JuliaLean.base.int.flipsign_same, JuliaLean.base.int.signbit_Unsigned,
      JuliaLean.base.int.Generic.signbit_Unsigned]
    have hz : (JuliaLean.base.int.neg (JuliaLean.base.int.ofBool t false)).val = 0 := by
      rw [JuliaLean.base.int.neg, IntVal.neg_int_val, JuliaLean.base.int.ofBool, IntVal.lit_val]
      cases t <;> decide
    generalize JuliaLean.base.int.neg (JuliaLean.base.int.ofBool t false) = z at hz
    simp only [JuliaLean.base.int.flipsign_int, JuliaLean.C.jlFlipsignInt, JuliaLean.C.fromJInt, hz]
    rw [if_neg (by simp [BitVec.toInt_ofInt]), IntVal.toJInt_ofInt_val, IntVal.wrapInt_val]
  · exact JuliaLean.Proofs.base.int.flipsign_val hts hts x y

/-- `div(x::unsigned(T), y::T)` (the world's instance: `base/int.jl:276` for signed `T`, same-type
`div` for unsigned `T`) is, modulo `2^bits`, the quotient `x ÷ |y|` with the sign of `y`. -/
theorem divUT_val (x : JInt t.toUnsigned) (y : JInt t) (hy : y.val ≠ 0) :
    ∃ q : JInt t.toUnsigned, (JDiv.div x y : JlX (JInt t.toUnsigned)) = .ok q ∧
      q.val = wrapInt t.toUnsigned
        (if y.val < 0 then -(x.val / (y.val.natAbs : Int)) else x.val / (y.val.natAbs : Int)) := by
  have hu : t.toUnsigned.signed = false := by cases t <;> rfl
  have hx0 := IntVal.nonneg_of_unsigned hu x
  cases hts : t.signed
  · have hU : t.toUnsigned = t := by cases t <;> simp_all [IntTy.signed, IntTy.toUnsigned]
    have hy0 := IntVal.nonneg_of_unsigned hts y
    have hyw : wrapInt t.toUnsigned y.val = y.val := by rw [hU]; exact IntVal.wrapInt_val y
    simp only [JDiv.div, hts, Bool.false_eq_true, ↓reduceIte]
    rw [JuliaLean.Proofs.base.int.divSame_eq]
    simp only [IntVal.remT_val, hyw, hy, false_or, hu, Bool.false_eq_true, false_and, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    rw [if_neg (by omega), IntVal.lit_val, Int.tdiv_eq_ediv_of_nonneg hx0,
      show ((y.val.natAbs : Int)) = y.val by omega]
  · have hP : t.toUnsigned.promote t.toUnsigned = t.toUnsigned := promote_self _
    have hyabs := IntVal.unsigned_abs_val y
    have hd : divPromoted x (JuliaLean.base.int.unsigned (JuliaLean.base.int.abs y)) = _ :=
      divPromoted_unsignedSpec t.toUnsigned t.toUnsigned hu hu x
        (JuliaLean.base.int.unsigned (JuliaLean.base.int.abs y))
    simp only [JDiv.div, hts, ↓reduceIte, JuliaLean.base.int.div_Unsigned_BitSigned,
      JuliaLean.base.int.Generic.div_Unsigned_BitSigned]
    simp only [hd, hyabs, show ((y.val.natAbs : Int) = 0) = False by simp [hy], ↓reduceIte, bind,
      Except.bind, pure, Except.pure, Except.map, liftJl]
    refine ⟨_, rfl, ?_⟩
    have hPs : (t.toUnsigned.promote t.toUnsigned).toSigned.signed = true := by rw [hP]; cases t <;> simp_all [IntTy.signed] <;> rfl
    rw [IntVal.remT_val, IntVal.unsigned_val, JuliaLean.Proofs.base.int.flipsign_val hPs hts,
      IntVal.signed_val, IntVal.lit_val]
    have hb1 : (t.toUnsigned.promote t.toUnsigned).toSigned.toUnsigned.bits = t.toUnsigned.bits := by
      rw [hP, toUnsigned_bits, toSigned_bits, toUnsigned_bits]
    have hb2 : (t.toUnsigned.promote t.toUnsigned).toSigned.bits = t.toUnsigned.bits := by
      rw [hP, toSigned_bits, toUnsigned_bits]
    have hb3 : (t.toUnsigned.promote t.toUnsigned).bits = t.toUnsigned.bits := by rw [hP]
    rw [wrap_cross _ _ hb1.symm]
    split
    · rw [wrap_cross _ _ hb2.symm, wrap_cross_neg _ _ hb2.symm, wrap_cross_neg _ _ hb3.symm]
    · rw [wrap_cross _ _ hb2.symm, wrap_cross _ _ hb2.symm, wrap_cross _ _ hb3.symm]

theorem max_sub_min (t : IntTy) : t.max - t.min = t.toUnsigned.max := by cases t <;> decide

/-- `length(r::OrdinalRange{T}) where T<:bigints` (range.jl:820) of `a:s:b` is its number of
elements when that number is representable in `T`. -/
theorem length_big_val (a s b l : JInt t) (hs : s.val ≠ 0)
    (hlv : l.val = lastVal a.val s.val b.val) (hfit : stepCount a.val s.val b.val ≤ t.max) :
    (length_OrdinalRange_bigints (⟨a, s, l⟩ : StepRange (JInt t) (JInt t))).map Subtype.val =
      .ok (stepCount a.val s.val b.val) := by
  have hemp := isempty_lastVal a.val s.val b.val hs
  rw [← hlv] at hemp
  have hc := stepCount_nonneg a.val s.val b.val
  have ha := a.property; have hl := l.property
  have hm := max_sub_min t
  have hmin := min_le_zero t
  unfold length_OrdinalRange_bigints
  simp only [step_step, last_step, first_step, isempty_step, hemp, bind, Except.bind]
  by_cases h0 : stepCount a.val s.val b.val = 0
  · simp [h0, pure, Except.pure, Except.map]
  have hpos : 0 < stepCount a.val s.val b.val := by omega
  simp only [h0, decide_false, Bool.false_eq_true, ite_false]
  have hK : l.val - a.val = (stepCount a.val s.val b.val - 1) * s.val := by
    rw [hlv, lastVal_count _ _ _ hs hpos]; omega
  have hK0 : 0 ≤ stepCount a.val s.val b.val - 1 := by omega
  have hS : 0 < (s.val.natAbs : Int) := by omega
  have hKS : (if s.val < 0 then -(l.val - a.val) else l.val - a.val) =
      (stepCount a.val s.val b.val - 1) * (s.val.natAbs : Int) := by
    rw [hK]; split
    · rw [show (s.val.natAbs : Int) = -s.val by omega, Int.mul_neg]
    · rw [show (s.val.natAbs : Int) = s.val by omega]
  have hKSb : 0 ≤ (stepCount a.val s.val b.val - 1) * (s.val.natAbs : Int) ∧
      (stepCount a.val s.val b.val - 1) * (s.val.natAbs : Int) ≤ t.toUnsigned.max := by
    refine ⟨Int.mul_nonneg hK0 (by omega), ?_⟩
    rw [← hKS]; split <;> omega
  have hU0 : t.toUnsigned.min = 0 := by cases t <;> rfl
  have hxv : (JUnsigned.unsigned (JFlipsign.flipsign (JWrappingSub.wrappingSub l a : JInt t) s) :
      JInt t.toUnsigned).val = (stepCount a.val s.val b.val - 1) * (s.val.natAbs : Int) := by
    show (JuliaLean.base.int.unsigned (JuliaLean.base.int.flipsign (JWrappingSub.wrappingSub l a : JInt t) s)).val = _
    rw [IntVal.unsigned_val, flipsign_tt, wrappingSub'_iv, wrap_cross _ _ (toUnsigned_bits t)]
    have : wrapInt t.toUnsigned (if s.val < 0 then -wrapInt t (l.val - a.val) else wrapInt t (l.val - a.val)) =
        wrapInt t.toUnsigned (if s.val < 0 then -(l.val - a.val) else l.val - a.val) := by
      split
      · exact wrap_cross_neg _ _ (toUnsigned_bits t) _
      · exact wrap_cross _ _ (toUnsigned_bits t) _
    rw [this, hKS]
    exact wrapInt_of_inRange _ _ ⟨by rw [hU0]; exact hKSb.1, hKSb.2⟩
  obtain ⟨q, hq, hqv⟩ := divUT_val
    (JUnsigned.unsigned (JFlipsign.flipsign (JWrappingSub.wrappingSub l a : JInt t) s) : JInt t.toUnsigned) s hs
  rw [hq]
  simp only [pure, Except.pure, Except.map, Except.ok.injEq]
  rw [hxv, Int.mul_ediv_cancel _ (by omega)] at hqv
  rw [add_iv, oneunit_iv]
  show wrapInt t ((JuliaLean.base.int.flipsign (JRemType.remType q : JInt t) s).val + 1) = _
  rw [flipsign_tt, remType_iv, hqv, wrap_cross _ _ (toUnsigned_bits t).symm]
  have : wrapInt t (if s.val < 0 then -wrapInt t (if s.val < 0 then -(stepCount a.val s.val b.val - 1)
      else stepCount a.val s.val b.val - 1) else wrapInt t (if s.val < 0 then -(stepCount a.val s.val b.val - 1)
      else stepCount a.val s.val b.val - 1)) = wrapInt t (stepCount a.val s.val b.val - 1) := by
    split
    · rw [IntVal.wrapInt_neg, Int.neg_neg]
    · exact IntVal.wrapInt_wrapInt _ _
  rw [← IntVal.wrapInt_add_left, this, IntVal.wrapInt_wrapInt]
  rw [IntVal.wrapInt_add_left t (stepCount a.val s.val b.val - 1) 1,
    show stepCount a.val s.val b.val - 1 + 1 = stepCount a.val s.val b.val by omega]
  exact wrapInt_of_inRange _ _ ⟨by omega, hfit⟩

theorem stepInts_length (a s b : Int) : ((stepInts a s b).length : Int) = stepCount a s b := by
  have := stepCount_nonneg a s b
  simp [stepInts]; omega

theorem lengthStep_colon (a s b l : JInt t) (hs : s.val ≠ 0) (hlv : l.val = lastVal a.val s.val b.val)
    (hfit : stepCount a.val s.val b.val ≤ (lenTy t).max) :
    (lengthStep (⟨a, s, l⟩ : StepRange (JInt t) (JInt t))).map Subtype.val =
      .ok (stepCount a.val s.val b.val) := by
  cases t
  case i64 => exact length_big_val a s b l hs hlv hfit
  case u64 => exact length_big_val a s b l hs hlv hfit
  case i128 => exact length_big_val a s b l hs hlv hfit
  case u128 => exact length_big_val a s b l hs hlv hfit
  all_goals exact length_small_val a s b l (by decide) hs hlv

theorem small_count_fits (a s b : JInt t) (ht : t.bits ≤ 32) :
    stepCount a.val s.val b.val ≤ (lenTy t).max := by
  have ha := small_bounds a ht; have hb := small_bounds b ht
  have hc := stepCount_nonneg a.val s.val b.val
  have hl : (lenTy t).max = 9223372036854775807 := by
    cases t <;> simp [IntTy.bits] at ht <;> rfl
  rw [hl]
  by_cases h0 : stepCount a.val s.val b.val = 0
  · omega
  have := stepCount_bound a.val s.val b.val (stepCount a.val s.val b.val - 1) (by omega) (by omega)
  have h2 : 0 ≤ stepCount a.val s.val b.val - 1 := by omega
  by_cases hp : 0 < s.val
  · have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ s.val by omega) h2; omega
  · have hn : s.val ≤ -1 := by
      unfold stepCount at h0
      by_cases h1 : 0 < s.val ∧ a.val ≤ b.val
      · omega
      · rw [if_neg h1] at h0
        by_cases h3 : s.val < 0 ∧ b.val ≤ a.val
        · omega
        · rw [if_neg h3] at h0; omega
    have := Int.mul_le_mul_of_nonneg_left hn h2; omega

/-- `a:s:b` for integers of one BitInteger type `T` (`(:)(start::T, step::T, stop::T)`,
range.jl:22): `length(r)` ("the number of elements in the collection", `length` docstring;
range.jl:853 for 8 to 32 bits, range.jl:820 for 64 and 128 bits) is the number of its elements
`a, a+s, ...` between `a` and `b` whenever that number is representable in the length type (`Int`
for 8 to 32 bits, `T` otherwise; beyond it `length` overflows, see `checked_length`, range.jl:700);
`checked_length(r)` for 8 to 32 bits (range.jl:861) is the same; and `firstindex(r)` is `1`
(ranges are one-based vectors; range.jl:864 and 850). -/
def StepRangeLength : Prop :=
  ∀ (t : IntTy) (a s b : JInt t) (r : StepRange (JInt t) (JInt t)), JColon3.colon a s b = .ok r →
    (((stepInts a.val s.val b.val).length : Int) ≤ (lenTy t).max →
      (JLength.length r).map Subtype.val = .ok ((stepInts a.val s.val b.val).length : Int)) ∧
    (t.bits ≤ 32 →
      (JCheckedLength.checkedLength r).map Subtype.val = .ok ((stepInts a.val s.val b.val).length : Int)) ∧
    (JFirstindex.firstindex r).map Subtype.val = .ok 1

theorem stepRangeLength_proven : StepRangeLength := by
  intro t a s b r hr
  by_cases hs : s.val = 0
  · rw [colon_step_zero a s b hs] at hr; cases hr
  obtain ⟨l, hc, _, hlv⟩ := colon_step a s b hs
  rw [hc] at hr; cases hr
  rw [stepInts_length]
  refine ⟨fun hfit => lengthStep_colon a s b l hs hlv hfit, fun ht => ?_, ?_⟩
  · have hfit := small_count_fits a s b ht
    show (checkedLengthStep (⟨a, s, l⟩ : StepRange (JInt t) (JInt t))).map Subtype.val = _
    cases t <;> simp [IntTy.bits] at ht <;>
      exact lengthStep_colon a s b l hs hlv hfit
  · show (firstindexStep (⟨a, s, l⟩ : StepRange (JInt t) (JInt t))).map Subtype.val = _
    cases t <;> simp [firstindexStep, firstindex_StepRange_smallints, firstindex_StepRange_bigints,
      first_step, last_step, bind, Except.bind, pure, Except.pure, Except.map] <;> decide

end StepLength

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section Findin
variable {t : IntTy}

theorem pTy_lenTy_left (t : IntTy) : pTy t .i64 = lenTy t := by cases t <;> rfl
theorem pTy_lenTy_i64 (t : IntTy) : pTy (lenTy t) .i64 = lenTy t := by cases t <;> rfl
theorem pTy_lenTy_right (t : IntTy) : pTy (lenTy t) t = lenTy t := by cases t <;> rfl

/-- `length(r) + 1` in `_findin` (range.jl:1314) on the length type. -/
local instance (priority := high) : HAdd (JInt (lenTy t)) JInt64 (JInt (lenTy t)) :=
  ⟨fun x y => castJ (pTy_lenTy_i64 t) (x + y)⟩
/-- `length(r) - cld(lr-lspan, sr)` in `_findin` (range.jl:1306): the length type minus the
element type promotes to the length type. -/
local instance : HSub (JInt (lenTy t)) (JInt t) (JInt (lenTy t)) :=
  ⟨fun x y => castJ (pTy_lenTy_right t) (x - y)⟩
/-- `cld(fspan-fr, sr) + 1` in `_findin` (range.jl:1305): `+(x::T, y::Int)` promotes the element
type `T` and `Int` (`promotion.jl`), which is the length type of a range of `T`. -/
local instance : HAdd (JInt t) JInt64 (JInt (lenTy t)) :=
  ⟨fun x y => castJ (pTy_lenTy_left t) (x + y)⟩
/-- `r isa AbstractUnitRange` (range.jl:1318) holds for a `UnitRange`. -/
local instance : JIsAbstractUnitRange (UnitRange (JInt t)) := ⟨true⟩

/-- The indices `k` of `a:b` (that is, `1, ..., b-a+1`) whose element `a+k-1` lies in `c:d`. -/
def findinSpec (a b c d : Int) : List Int :=
  (intsFromTo 1 (b - a + 1)).filter fun k => decide (c ≤ a + k - 1 ∧ a + k - 1 ≤ d)

/-- `findall(in(span), r)` for integer ranges (`_findin`, range.jl:1295-1320, "the index of
intersection"; `findall` docstring: "Return a vector `I` of the indices or keys of `A` where
`f(A[I])` is true") of unit ranges `a:b` and `c:d` of one BitInteger type is the unit range of the
indices `k` of `a:b` whose element `a+k-1` lies in `c:d`. -/
def FindinIndices : Prop :=
  ∀ (t : IntTy) (a b c d : JInt t) (r span : UnitRange (JInt t)),
    JColon2.colon a b = .ok r → JColon2.colon c d = .ok span →
    ∃ ρ : UnitRange (JInt (lenTy t)), _findin (I := JInt (lenTy t)) r span = .ok (.inl ρ) ∧
      ∀ fuel, (findinSpec a.val b.val c.val d.val).length < fuel →
        iterVals ρ fuel = .ok (findinSpec a.val b.val c.val d.val)

/-- `findall(in(Int8(50):Int8(100)), Int8(-100):Int8(-90))` is `-105:11` instead of empty:
`first(span) - first(r)` is `150`, which wraps to `-106` in `Int8`. -/
theorem findinIndices_refuted : ¬ FindinIndices := by
  intro h
  have := h .i8 (lit .i8 (-100)) (lit .i8 (-90)) (lit .i8 50) (lit .i8 100)
    ⟨lit .i8 (-100), lit .i8 (-90)⟩ ⟨lit .i8 50, lit .i8 100⟩ (by decide) (by decide)
  obtain ⟨ρ, hρ, hv⟩ := this
  have h2 := hρ.symm.trans (show _ = (Except.ok (Sum.inl
    (⟨lit .i64 (-105), lit .i64 11⟩ : UnitRange (JInt .i64))) : JlX (_ ⊕ _)) from by decide)
  cases h2
  have hv1 := hv 1 (by decide)
  revert hv1
  decide

/-- `findall(in(c:d), a:b)` for unit ranges of one BitInteger type with `a:b` nonempty and inside
`c:d` (`c <= a <= b <= d`) is `1:length(a:b)`, the indices of all its elements (`_findin`,
range.jl:1295-1320; `findall` docstring), whenever the number of elements fits the length type. -/
def FindinInside : Prop :=
  ∀ (t : IntTy) (a b c d : JInt t) (r span : UnitRange (JInt t)),
    JColon2.colon a b = .ok r → JColon2.colon c d = .ok span →
    c.val ≤ a.val → a.val ≤ b.val → b.val ≤ d.val → cnt a.val b.val ≤ (lenTy t).max →
    ∃ ρ : UnitRange (JInt (lenTy t)), _findin (I := JInt (lenTy t)) r span = .ok (.inl ρ) ∧
      ∀ fuel, (cnt a.val b.val).toNat < fuel → iterVals ρ fuel = .ok (intsFromTo 1 (cnt a.val b.val))

theorem findinInside_proven : FindinInside := by
  intro t a b c d r span hr hs hca hab hbd hfit
  rw [colon_unit] at hr hs; cases hr; cases hs
  obtain ⟨n, hn, hnv⟩ := lengthUnit_fits a b hfit
  obtain ⟨s, hst, hsv⟩ := step_unit (⟨a, unitStop a b⟩ : UnitRange (JInt t))
  have hb : (unitStop a b).val = b.val := by rw [unitStop_val]; simp [hab]
  have hd : (unitStop c d).val = d.val := by rw [unitStop_val]; simp; omega
  obtain ⟨ρ, hρ, -, -, -, -, -, -, hit, -⟩ := unitRangeColon_proven (lenTy t) (JOne.one) n
  refine ⟨ρ, ?_, ?_⟩
  · unfold _findin
    simp only [first_unit, last_unit, hst, bind, Except.bind, pure, Except.pure]
    simp only [lt_iv, le_iv, hsv, hb, hd, JLength.length, hn,
      show (jint 0 : JInt64).val = 0 from rfl]
    simp [hca, hbd, hρ, JIsAbstractUnitRange.isAbstractUnitRange]
  · intro fuel hf
    have := hit fuel (by rw [one_iv, hnv]; omega)
    rwa [one_iv, hnv] at this

end Findin

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit shr_Int)

section UnitSum
variable {t : IntTy}

/-- `iseven(n::Real) = isinteger(n) && iszero(rem(Integer(n), 2))` (int.jl:181), which `which`
selects for a BitInteger `n`; an integer remainder by 2 is zero exactly when `n` is even. -/
local instance : JIseven (JInt t) := ⟨fun x => decide (x.val % 2 = 0)⟩
/-- `x >> y` for a BitInteger `x` and an `Int` count (`>>(x::BitInteger, y::Int)`, int.jl:611). -/
local instance : JShr (JInt t) JInt64 (JInt t) := ⟨shr_Int⟩
/-- `l - 1` on the length type of a range (`-(x::T, y::Int)`: promote, then subtract;
`promotion.jl`, int.jl:1092-1100); the promoted type is the length type itself. -/
def lenSubInt (x : JInt (lenTy t)) (y : JInt64) : JInt (lenTy t) := castJ (pTy_lenTy_i64 t) (x - y)
theorem lenSubInt_val (x : JInt (lenTy t)) (y : JInt64) :
    (lenSubInt x y).val = wrapInt (lenTy t) (x.val - y.val) := by
  unfold lenSubInt; rw [castJ_val, subMixed_iv, pTy_lenTy_i64]
local instance (priority := high) : HSub (JInt (lenTy t)) JInt64 (JInt (lenTy t)) := ⟨lenSubInt⟩
@[simp] theorem lenSub_iv (x : JInt (lenTy t)) (y : JInt64) :
    (x - y : JInt (lenTy t)).val = wrapInt (lenTy t) (x.val - y.val) := lenSubInt_val x y

theorem shr1_val (x : JInt t) : (JShr.shr x (jint 1) : JInt t).val = x.val / 2 := by
  have := (JuliaLean.Proofs.base.int.shiftIntCount_proven t x (jint 1)).1
  simp only [jint1_val] at this
  exact this

theorem sum_range_two (a : Int) (m : Nat) :
    2 * ((List.range m).map fun k : Nat => a + (k : Int)).sum = (m : Int) * (2 * a + m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.add_zero]
    have h1 := Int.mul_sub (m : Int) (2 * a + m) 1
    have h2 := Int.add_mul (m : Int) 1 (2 * a + m)
    rw [show (2 * a + (m : Int) - 1) = 2 * a + m - 1 from rfl] at ih
    push_cast
    rw [show 2 * a + ((m : Int) + 1) - 1 = 2 * a + m by omega, h2]
    omega

theorem sum_ints_two (a b : Int) : 2 * (intsFromTo a b).sum = cnt a b * (2 * a + cnt a b - 1) := by
  unfold intsFromTo
  rw [sum_range_two]
  unfold cnt
  split
  · rw [Int.toNat_of_nonneg (by omega)]
  · rw [show (b - a + 1).toNat = 0 by omega]; simp

theorem pTy_lenTy_cases (t : IntTy) : pTy (lenTy t) t = lenTy t ∧ pTy t (lenTy t) = lenTy t ∧
    pTy (lenTy t) (lenTy t) = lenTy t := by cases t <;> decide

/-- `sum(a:b)` for integers `a`, `b` of one BitInteger type (`sum(r::AbstractRange{<:Real})`,
range.jl:1468; `sum` docstring: "Return the sum of all elements in a collection") is the sum of its
elements `a, a+1, ..., b` in the length type (`Int` for types narrower than 64 bits, the element
type otherwise, with that type's wrapping arithmetic), whenever the number of elements fits the
length type (beyond it `length` overflows, see `checked_length`). The empty range sums to zero. -/
def UnitRangeSum : Prop :=
  ∀ (t : IntTy) (a b : JInt t) (r : UnitRange (JInt t)), JColon2.colon a b = .ok r →
    cnt a.val b.val ≤ (lenTy t).max →
    (sum_AbstractRange (D := Unit) r).map Subtype.val = .ok (wrapInt (lenTy t) (intsFromTo a.val b.val).sum)

theorem unitRangeSum_proven : UnitRangeSum := by
  intro t a b r hr hfit
  rw [colon_unit] at hr; cases hr
  obtain ⟨n, hn, hnv⟩ := lengthUnit_fits a b hfit
  obtain ⟨s, hs, hsv⟩ := step_unit (⟨a, unitStop a b⟩ : UnitRange (JInt t))
  obtain ⟨e1, e2, e3⟩ := pTy_lenTy_cases t
  have hS := sum_ints_two a.val b.val
  have hc0 : 0 ≤ cnt a.val b.val := by unfold cnt; split <;> omega
  unfold sum_AbstractRange
  simp only [JLength.length, hn, first_unit, hs, bind, Except.bind, pure, Except.pure]
  by_cases he : n.val % 2 = 0
  · simp only [JIseven.iseven, he, decide_true, ite_true, Except.map, Except.ok.injEq]
    simp only [addMixed_iv, mulMixed_iv, castJ_val, lenSub_iv, shr1_val, hsv, hnv, jint1_val, e1, e2, e3]
    simp only [IntVal.wrapInt_add_left, IntVal.wrapInt_add_right, IntVal.wrapInt_mul_left,
      IntVal.wrapInt_mul_right, Int.one_mul]
    apply congrArg
    rw [hnv] at he
    obtain ⟨h, hh⟩ : ∃ h, cnt a.val b.val = 2 * h := ⟨cnt a.val b.val / 2, by omega⟩
    rw [hh] at hS ⊢
    rw [show 2 * h / 2 = h by omega]
    grind
  · simp only [JIseven.iseven, he, decide_false, Bool.false_eq_true, ite_false, Except.map, Except.ok.injEq]
    simp only [addMixed_iv, mulMixed_iv, castJ_val, lenSub_iv, shr1_val, hsv, hnv, jint1_val, e1, e2, e3]
    simp only [IntVal.wrapInt_add_left, IntVal.wrapInt_add_right, IntVal.wrapInt_mul_left,
      IntVal.wrapInt_mul_right, IntVal.wrapInt_sub_left, Int.one_mul]
    apply congrArg
    rw [hnv] at he
    obtain ⟨h, hh⟩ : ∃ h, cnt a.val b.val = 2 * h + 1 := ⟨cnt a.val b.val / 2, by omega⟩
    have hn1 : wrapInt (lenTy t) (2 * h + 1 - 1) = 2 * h := by
      rw [show 2 * h + 1 - 1 = 2 * h by omega]
      exact wrapInt_of_inRange _ _ ⟨by have := min_le_zero (lenTy t); omega, by omega⟩
    rw [hh] at hS ⊢
    rw [hn1, show 2 * h / 2 = h by omega]
    grind

end UnitSum



open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section StepEq
variable {t : IntTy}

/-- `_has_length_one(r::OrdinalRange) = first(r) == last(r)` (range.jl:1177), which `which`
selects for a `StepRange` of BitIntegers. -/
local instance : JHasLengthOne (StepRange (JInt t) (JInt t)) := ⟨_has_length_one_OrdinalRange⟩

theorem stepInts_get (a s b : Int) (k : Nat) (hk : (k : Int) < stepCount a s b) :
    (stepInts a s b)[k]? = some (a + k * s) := by
  unfold stepInts
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem stepInts_eq_iff (a s b c u d : Int) (hs : s ≠ 0) (hu : u ≠ 0)
    (hn : 2 ≤ stepCount a s b) :
    stepInts a s b = stepInts c u d ↔ a = c ∧ s = u ∧ lastVal a s b = lastVal c u d := by
  have hm0 := stepCount_nonneg c u d
  constructor
  · intro h
    have hl := congrArg (fun l => (l.length : Int)) h
    simp only [stepInts_length] at hl
    have h0 := congrArg (fun l => l[0]?) h
    have h1 := congrArg (fun l => l[1]?) h
    rw [stepInts_get _ _ _ 0 (by omega), stepInts_get _ _ _ 0 (by omega)] at h0
    rw [stepInts_get _ _ _ 1 (by omega), stepInts_get _ _ _ 1 (by omega)] at h1
    simp at h0 h1
    have hsu : s = u := by omega
    refine ⟨h0, hsu, ?_⟩
    rw [lastVal_count _ _ _ hs (by omega), lastVal_count _ _ _ hu (by omega), hl, h0, hsu]
  · rintro ⟨hac, hsu, hl⟩
    subst hac hsu
    have hm : stepCount a s d = stepCount a s b := by
      by_cases hm : stepCount a s d = 0
      · have e1 := isempty_lastVal a s b hs
        have e2 := isempty_lastVal a s d hs
        rw [hl] at e1
        rw [e1, hm] at e2
        simp at e2; omega
      · rw [lastVal_count _ _ _ hs (by omega), lastVal_count _ _ _ hs (by omega)] at hl
        have : (stepCount a s b - 1) * s = (stepCount a s d - 1) * s := by omega
        have := Int.eq_of_mul_eq_mul_right hs this
        omega
    unfold stepInts; rw [hm]

/-- `r == q` for ranges `a:s:b` and `c:u:d` of one BitInteger type (`==` on
`Union{StepRange{T},StepRangeLen{T,T}}`, range.jl:1171; `==` docstring: collections are equal when
they have the same elements in the same order) holds exactly when they have the same elements. -/
def StepRangeEq : Prop :=
  ∀ (t : IntTy) (a s b c u d : JInt t) (r q : StepRange (JInt t) (JInt t)),
    JColon3.colon a s b = .ok r → JColon3.colon c u d = .ok q →
    eq_StepRange_StepRangeLen r q =
      .ok (decide (stepInts a.val s.val b.val = stepInts c.val u.val d.val))

theorem stepRangeEq_proven : StepRangeEq := by
  intro t a s b c u d r q hr hq
  by_cases hs : s.val = 0
  · rw [colon_step_zero a s b hs] at hr; cases hr
  by_cases hu : u.val = 0
  · rw [colon_step_zero c u d hu] at hq; cases hq
  obtain ⟨l, hc, -, hlv⟩ := colon_step a s b hs
  obtain ⟨k, hc2, -, hkv⟩ := colon_step c u d hu
  rw [hc] at hr; cases hr; rw [hc2] at hq; cases hq
  have e1 := isempty_lastVal a.val s.val b.val hs
  have e2 := isempty_lastVal c.val u.val d.val hu
  have n0 := stepCount_nonneg a.val s.val b.val
  have m0 := stepCount_nonneg c.val u.val d.val
  simp only [eq_StepRange_StepRangeLen, isempty_step, JHasLengthOne.hasLengthOne,
    _has_length_one_OrdinalRange, first_step, last_step, step_step, eq_iv, hlv, hkv, e1, e2,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq]
  by_cases hn : stepCount a.val s.val b.val = 0
  · have : stepInts a.val s.val b.val = [] := (stepInts_nil_iff _ _ _).mpr hn
    have key : ([] = stepInts c.val u.val d.val) ↔ stepCount c.val u.val d.val = 0 := by
      rw [eq_comm]; exact stepInts_nil_iff _ _ _
    simp only [hn, decide_true, ite_true, this, key]
  by_cases h1 : stepCount a.val s.val b.val = 1
  · have hl1 : lastVal a.val s.val b.val = a.val := by
      rw [lastVal_count _ _ _ hs (by omega), h1]; simp
    have hsi : stepInts a.val s.val b.val = [a.val] := by simp [stepInts, h1]
    simp only [hn, decide_false, Bool.false_eq_true, ite_false, hl1, decide_true, ite_true, hsi]
    by_cases hm : stepCount c.val u.val d.val = 0
    · have : stepInts c.val u.val d.val = [] := (stepInts_nil_iff _ _ _).mpr hm
      rw [this]
      have : c.val ≠ lastVal c.val u.val d.val := by
        have := e2; rw [hm] at this; simp at this; exact this.1
      simp [this]
    by_cases hm1 : stepCount c.val u.val d.val = 1
    · have hk1 : lastVal c.val u.val d.val = c.val := by
        rw [lastVal_count _ _ _ hu (by omega), hm1]; simp
      have : stepInts c.val u.val d.val = [c.val] := by simp [stepInts, hm1]
      rw [this, hk1]; simp [eq_comm]
    · have hne : c.val ≠ lastVal c.val u.val d.val := by
        rw [lastVal_count _ _ _ hu (by omega)]
        intro h
        have : (stepCount c.val u.val d.val - 1) * u.val = 0 := by omega
        rcases Int.mul_eq_zero.mp this with h' | h' <;> omega
      have hlen : (stepInts c.val u.val d.val).length ≠ 1 := by
        have := stepInts_length c.val u.val d.val; omega
      have hnot : ¬ ([a.val] = stepInts c.val u.val d.val) := fun h => hlen (by rw [← h]; rfl)
      simp [hne, hnot]
  · have hne : a.val ≠ lastVal a.val s.val b.val := by
      rw [lastVal_count _ _ _ hs (by omega)]
      intro h
      have : (stepCount a.val s.val b.val - 1) * s.val = 0 := by omega
      rcases Int.mul_eq_zero.mp this with h' | h' <;> omega
    simp only [hn, decide_false, Bool.false_eq_true, ite_false, hne, decide_false]
    simp only [stepInts_eq_iff a.val s.val b.val c.val u.val d.val hs hu (by omega)]
    simp [Bool.and_assoc]

end StepEq

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## Dispatch world: `StepRange{Bool,Int}` -/

section BoolStep

/-- `x + y` of a `Bool` and an `Int`: promote the `Bool` to `Int` (`promotion.jl`), then add. -/
instance : HAdd Bool JInt64 JInt64 := ⟨fun x y => JuliaLean.base.int.ofBool .i64 x + y⟩
/-- `x - y` of a `Bool` and an `Int`: promote the `Bool` to `Int`, then subtract. -/
instance : HSub Bool JInt64 JInt64 := ⟨fun x y => JuliaLean.base.int.ofBool .i64 x - y⟩
/-- `_range_wrapping_sub(x, y) = x - y`, range.jl:36: `Bool` is not a `_RangeWrappingInteger`. -/
instance : JRangeWrappingSub Bool Bool JInt64 := ⟨_range_wrapping_sub_Any⟩
/-- `steprange_last_empty(start::Bool, step, stop)`, range.jl:399. -/
instance : JSteprangeLastEmpty Bool JInt64 Bool := ⟨steprange_last_empty_Bool⟩
/-- `steprange_last(start, step, stop)`, range.jl:353. -/
instance : JSteprangeLast Bool JInt64 Bool := ⟨steprange_last⟩
/-- `StepRange{T,S}(start, step, stop)`, range.jl:344. -/
instance : JStepRangeTS Bool JInt64 Bool JInt64 Bool := ⟨StepRange_TS_new Bool JInt64⟩
instance : JEltype (StepRange Bool JInt64) Bool := ⟨⟩
instance : JFieldStart (StepRange Bool JInt64) Bool := ⟨StepRange.start⟩
instance : JFieldStop (StepRange Bool JInt64) Bool := ⟨StepRange.stop⟩
/-- `first(r::OrdinalRange{T})`, range.jl:867. -/
instance : JFirst (StepRange Bool JInt64) Bool := ⟨first_OrdinalRange⟩
/-- `last(r::OrdinalRange{T})`, range.jl:877. -/
instance : JLast (StepRange Bool JInt64) Bool := ⟨last_OrdinalRange⟩
/-- `step(r::StepRange)`, range.jl:735. -/
instance : JStep (StepRange Bool JInt64) JInt64 := ⟨fun r => pure (step_StepRange r)⟩
/-- `isempty(r::StepRange)`, range.jl:708. -/
instance : JIsempty (StepRange Bool JInt64) := ⟨fun r => pure (isempty_StepRange r)⟩
/-- `iterate(r::OrdinalRange)`, range.jl:935. -/
instance : JIterate1 (StepRange Bool JInt64) Bool Bool := ⟨iterate_OrdinalRange⟩
/-- `iterate(r::OrdinalRange{T}, i)`, range.jl:937. -/
instance : JIterate2 (StepRange Bool JInt64) Bool Bool := ⟨iterate_OrdinalRange_state⟩

end BoolStep

/-- The integer value of a `Bool`. -/
def boolInt (b : Bool) : Int := if b then 1 else 0

/-- `StepRange(start, step, stop)` (range.jl:404; `StepRange` docstring, range.jl:293: "Ranges with
elements of type `T` with spacing of type `S`. The step between each element is constant, and the
range is defined in terms of a `start` and `stop` of type `T` and a `step` of type `S`"): for `Bool`
endpoints and a nonzero `Int` step, iterating the range yields exactly the values
`start, start + step, start + 2step, ...` that do not pass `stop`, as `Bool`s; in particular the
range is empty when `stop` lies on the other side of `start` from the direction of `step`. -/
def BoolStepRangeElements : Prop :=
  ∀ (a b : Bool) (s : JInt64) (r : StepRange Bool JInt64),
    s.val ≠ 0 → StepRange_T_S_T a s b = .ok r →
    iterList r 2 = .ok ((stepInts (boolInt a) s.val (boolInt b)).map fun v => decide (v = 1))

theorem boolStepRangeElements_refuted : ¬ BoolStepRangeElements := by
  intro h
  have := h false true (lit .i64 (-1)) ⟨false, lit .i64 (-1), false⟩ (by decide) (by decide +kernel)
  revert this; decide +kernel

/-! ## `==` of integer `StepRangeLen`s -/

/-- `_has_length_one(r::AbstractRange) = isone(length(r))`, range.jl:1178, which `which` selects
for a `StepRangeLen` (not an `OrdinalRange`). -/
instance {q a s w : IntTy} : JHasLengthOne (StepRangeLen (JInt q) (JInt a) (JInt s) (JInt w)) :=
  ⟨_has_length_one_AbstractRange⟩

/-- `==` of two integer `StepRangeLen{T,T,T,Int}`s, which `which` resolves to
`==(r::Union{StepRange{T},StepRangeLen{T,T}}, s::Union{StepRange{T},StepRangeLen{T,T}})`
(range.jl:1171): the `==` docstring promises that collections are equal when they have the same
elements in the same order, so `r == s` holds exactly when iterating them yields the same lists. -/
def SRLIntEq : Prop :=
  ∀ (t : IntTy) (a s b u : JInt t) (n o m p : JInt64) (r q : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)
    (fuel : Nat) (xs ys : List (JInt t)),
    StepRangeLen_ref_step a s n o = .ok r → StepRangeLen_ref_step b u m p = .ok q →
    n.val < fuel → m.val < fuel → iterList r fuel = .ok xs → iterList q fuel = .ok ys →
    eq_StepRange_StepRangeLen r q = .ok (decide (xs = ys))

theorem sRLIntEq_refuted : ¬ SRLIntEq := by
  intro h
  have := h .i64 (lit .i64 1) (lit .i64 0) (lit .i64 1) (lit .i64 0) (lit .i64 2) (lit .i64 1)
    (lit .i64 3) (lit .i64 1) ⟨lit .i64 1, lit .i64 0, lit .i64 2, lit .i64 1⟩
    ⟨lit .i64 1, lit .i64 0, lit .i64 3, lit .i64 1⟩ 4 [lit .i64 1, lit .i64 1]
    [lit .i64 1, lit .i64 1, lit .i64 1]
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

/-! ## `reverse` of integer `StepRangeLen`s -/

/-- `typeof(r)(ref, step, len, offset)` for an integer `StepRangeLen{T,T,T,Int}` (range.jl:1451)
with the negated step: for signed `T`, `negate(step)` (int.jl:96) has type `T` and this is the
inner constructor `StepRangeLen{T,R,S,L}(ref::R, step::S, len, offset)` (range.jl:533); for unsigned
`T`, `negate(step)` (int.jl:97) is a signed integer and no method
`StepRangeLen{T,T,T,Int}(::T, ::signed(T), ::Int, ::Int)` exists, a `MethodError`. -/
instance {t : IntTy} :
    JSameType4 (StepRangeLen (JInt t) (JInt t) (JInt t) JInt64) (JInt t) (JInt (sTy t)) JInt64 JInt64 :=
  ⟨fun ref st len off => if h : sTy t = t then StepRangeLen_TRSL_new (JInt t) ref (castJ h st) len off
    else throw (.jl (.methodError "StepRangeLen{T,T,T,Int64}(::T, ::Signed, ::Int64, ::Int64)"))⟩

/-- `reverse(r)` (`_reverse(r::StepRangeLen, ::Colon)`, range.jl:1446; docstring of `reverse`,
"Return a copy of `v` reversed from start to stop") of an integer
`StepRangeLen(ref, step, len, offset)` iterates the elements of `r` in reverse order. -/
def SRLIntReverse : Prop :=
  ∀ (t : IntTy) (ref step : JInt t) (len off : JInt64)
    (r : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64) (fuel : Nat) (xs : List (JInt t)),
    StepRangeLen_ref_step ref step len off = .ok r → len.val < fuel → iterList r fuel = .ok xs →
    (_reverse_StepRangeLen (Λ := JInt64) r ⟨⟩ >>= fun rr => iterList rr fuel) = .ok xs.reverse

theorem sRLIntReverse_refuted : ¬ SRLIntReverse := by
  intro h
  have := h .u8 (lit .u8 1) (lit .u8 2) (lit .i64 3) (lit .i64 1)
    ⟨lit .u8 1, lit .u8 2, lit .i64 3, lit .i64 1⟩ 4 [lit .u8 1, lit .u8 3, lit .u8 5]
    (by decide +kernel) (by decide) (by decide +kernel)
  revert this; decide +kernel

/-! ## `sort` of integer step ranges -/

/-- `sort(r::AbstractRange) = issorted(r) ? r : reverse(r)` (range.jl:1463; docstring of `sort`:
"Return a sorted copy of an array"): for an integer step range `a:s:b`, iterating `sort(r)` yields the
elements of `a:s:b` in ascending order: the elements of `a:s:b` themselves for a positive step, in
reverse for a negative one. -/
def StepRangeSort : Prop :=
  ∀ (t : IntTy) (a s b : JInt t) (r : StepRange (JInt t) (JInt t)) res (fuel : Nat) (xs : List Int),
    colon_T_T_T_Real a s b = .ok r → stepCount a.val s.val b.val < fuel →
    sort_AbstractRange r = .ok res →
    (match res with | .inl v => iterVals v fuel | .inr v => iterVals v fuel) = .ok xs →
    xs = if 0 < s.val then stepInts a.val s.val b.val else (stepInts a.val s.val b.val).reverse

theorem stepRangeSort_refuted : ¬ StepRangeSort := by
  intro h
  have := h .i8 (lit .i8 0) (lit .i8 (-128)) (lit .i8 (-128)) ⟨lit .i8 0, lit .i8 (-128), lit .i8 (-128)⟩
    (.inr ⟨lit .i8 (-128), lit .i8 (-128), lit .i8 (-127)⟩) 3 []
    (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## `UnitRange{Bool}` -/

section BoolUnit

/-- `_range_wrapping_sub(x, y) = x - y`, range.jl:36, of a `Bool` and an `Int`. -/
instance : JRangeWrappingSub Bool JInt64 JInt64 := ⟨_range_wrapping_sub_Any⟩
/-- `unitrange_last(start::Integer, stop::Integer)`, range.jl:439, for `Bool` endpoints. -/
instance : JUnitrangeLast Bool Bool := ⟨unitrange_last_Integer⟩
/-- `UnitRange{T}(start::T, stop::T)`, range.jl:428. -/
instance : JUnitRangeT Bool Bool Bool := ⟨UnitRange_T_new⟩
/-- `firstindex(r)` of a `UnitRange` (abstractarray.jl: `first(eachindex(r))`) is `1`. -/
instance : JFirstindex (UnitRange Bool) JInt64 := ⟨fun _ => pure (lit .i64 1)⟩
/-- `lastindex(r)` of a `UnitRange` (abstractarray.jl: `last(eachindex(r))`) is `length(r)`. -/
instance : JLastindex (UnitRange Bool) JInt64 := ⟨JLength.length⟩
/-- `x <= y` of an `Int` and a `Bool`: promote the `Bool` to `Int` (`promotion.jl`). -/
instance : JLe JInt64 Bool := ⟨fun x y => JuliaLean.base.int.le x (JuliaLean.base.int.ofBool .i64 y)⟩
/-- `x <= y` of a `Bool` and an `Int`: promote the `Bool` to `Int` (`promotion.jl`). -/
instance : JLe Bool JInt64 := ⟨fun x y => JuliaLean.base.int.le (JuliaLean.base.int.ofBool .i64 x) y⟩

theorem boolColon (a b : Bool) : (colon_T_T_Real a b : JlX (UnitRange Bool)) = .ok ⟨a, b⟩ := by
  cases a <;> cases b <;> decide +kernel

/-- `a:b` for `Bool` endpoints (`(:)(start::T, stop::T) where {T<:Real}`, range.jl:5; `UnitRange`
docstring, range.jl:407: "A range parameterized by a `start` and `stop` of type `T`, filled with
elements spaced by `1` from `start` until `stop` is exceeded"): iterating it yields the `Bool`s from
`a` to `b` (none for `true:false`) and then stops; `length` (range.jl:794) and `isempty`
(range.jl:711) agree with that list; `step(r)` (range.jl:737, "the step size") is `true`, the
`Bool` `oneunit`, and consecutive elements differ by it; and `isassigned(r, i)` (range.jl:946)
rejects a `Bool` index with `ArgumentError`, for every printer of `Bool` in the message. -/
def BoolUnitRange : Prop :=
  ∀ (P : JPrint Bool) (a b : Bool) (r : UnitRange Bool), colon_T_T_Real a b = .ok r →
    iterList r 2 = .ok (boolsFromTo a b) ∧
    JLength.length r = .ok (lit .i64 (boolsFromTo a b).length) ∧
    JIsempty.isempty r = .ok (boolsFromTo a b).isEmpty ∧
    JStep.step r = .ok true ∧
    (∀ i < (boolsFromTo a b).length - 1,
      JuliaLean.base.bool.subBool (boolsFromTo a b)[i + 1]! (boolsFromTo a b)[i]! =
        JuliaLean.base.int.ofBool .i64 true) ∧
    (∀ i : Bool, ∃ m, isassigned_AbstractRange r i = .error (.jl (.argumentError m)))

theorem boolUnitRange_proven : BoolUnitRange := by
  intro P a b r h
  rw [boolColon] at h
  cases h
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i => ⟨_, rfl⟩⟩ <;> cases a <;> cases b <;> decide +kernel

end BoolUnit

/-! ## `show` of integer ranges -/

section ShowInt
variable {t : IntTy}

theorem stepCount_mul (a s m : Int) (hs : s ≠ 0) (hm : 0 ≤ m) :
    stepCount a s (a + m * s) = m + 1 := by
  unfold stepCount
  by_cases hp : 0 < s
  · have h1 : 0 ≤ m * s := Int.mul_nonneg hm (by omega)
    rw [if_pos ⟨hp, by omega⟩, show a + m * s - a = m * s by omega, Int.mul_tdiv_cancel _ hs]
  · have h1 := Int.mul_le_mul_of_nonpos_right hm (show s ≤ 0 by omega)
    simp only [Int.zero_mul] at h1
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩,
      show a - (a + m * s) = m * (-s) by rw [Int.mul_neg]; omega, Int.mul_tdiv_cancel _ (by omega)]

theorem stepCount_lastVal (a s b : Int) (hs : s ≠ 0) :
    stepCount a s (lastVal a s b) = stepCount a s b := by
  have hn := stepCount_nonneg a s b
  by_cases hc : 0 < stepCount a s b
  · rw [lastVal_count a s b hs hc, stepCount_mul a s _ hs (by omega)]; omega
  · have h0 : stepCount a s b = 0 := by omega
    rw [h0]
    have hab : a ≠ b := by
      intro e; subst e
      have := stepCount_mul a s 0 hs (Int.le_refl 0)
      simp only [Int.zero_mul, Int.add_zero] at this; omega
    have hdir : (0 < s ∧ b < a) ∨ (s < 0 ∧ a < b) := by
      unfold stepCount at h0
      by_cases hp : 0 < s
      · left; refine ⟨hp, ?_⟩
        by_cases hba : a ≤ b
        · rw [if_pos ⟨hp, hba⟩] at h0
          have := Int.tdiv_nonneg (show 0 ≤ b - a by omega) (show 0 ≤ s by omega); omega
        · omega
      · right; refine ⟨by omega, ?_⟩
        by_cases hba : b ≤ a
        · rw [if_neg (by omega), if_pos ⟨by omega, hba⟩] at h0
          have := Int.tdiv_nonneg (show 0 ≤ a - b by omega) (show 0 ≤ -s by omega); omega
        · omega
    have hne : (0 < s) ≠ (a < b) := by
      intro e
      rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := e ▸ h1; omega
      · have h3 : ¬ (0 < s) := by omega
        rw [e] at h3; omega
    have hl : lastVal a s b = if 0 < s then a - 1 else a + 1 := by
      unfold lastVal; rw [if_neg hab, if_pos hne]
    rw [hl]
    rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1]; unfold stepCount; rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by omega)]; unfold stepCount; rw [if_neg (by omega), if_neg (by omega)]

theorem stepInts_lastVal (a s b : Int) (hs : s ≠ 0) :
    stepInts a s (lastVal a s b) = stepInts a s b := by
  unfold stepInts; rw [stepCount_lastVal a s b hs]

/-- `show(io, r)` of integer ranges writes text that reads back as an equal range (the manual,
"Output": `show` writes "a text representation of an object ... that should be parseable Julia
code when possible"):
- `show(io, a:b)` (`show(io::IO, r::UnitRange)`, range.jl:1136) writes `x:y` where `x` and `y` are
  texts that `parse` reads back as integers `x'`, `y'` with `x':y'` having the elements of `a:b`;
- `show(io, a:s:b)` (`show(io::IO, r::AbstractRange)`, range.jl:1135) writes `x:z:y` that reads back
  as `x':z':y'` with the elements of `a:s:b`;
- `show(io, Base.OneTo(n))` (range.jl:1141) writes `Base.OneTo(m)` with `m` the decimal digits of
  `max(0, n)`, so `Base.OneTo(m)` is the same range.
Stated for every element printer `show`/`repr` that writes no `:` and that `parse` inverts. -/
def ShowIntRanges : Prop :=
  ∀ (t : IntTy) (shw : JInt t → String) (parse : String → Option Int),
    (∀ x, parse (shw x) = some x.val) → (∀ x, ':' ∉ (shw x).toList) →
    (∀ (a b : JInt t) (r : UnitRange (JInt t)) (text : String), colon_T_T_Real a b = .ok r →
      (letI : JShow (JInt t) := ⟨fun x => pure (shw x)⟩; show_UnitRange ⟨⟩ r) = .ok text →
      ∃ x y : String, text = x ++ ":" ++ y ∧ ∃ x' y', parse x = some x' ∧ parse y = some y' ∧
        intsFromTo x' y' = intsFromTo a.val b.val) ∧
    (∀ (a s b : JInt t) (r : StepRange (JInt t) (JInt t)) (text : String),
      colon_T_T_T_Real a s b = .ok r →
      (letI : JRepr (JInt t) := ⟨fun x => pure (shw x)⟩; show_AbstractRange ⟨⟩ r) = .ok text →
      ∃ x z y : String, text = x ++ ":" ++ z ++ ":" ++ y ∧ ∃ x' z' y', parse x = some x' ∧
        parse z = some z' ∧ parse y = some y' ∧ stepInts x' z' y' = stepInts a.val s.val b.val) ∧
    (∀ (n : JInt t) (r : OneTo (JInt t)), OneTo_stop n = .ok r →
      show_OneTo ⟨⟩ r = .ok ("Base.OneTo(" ++ toString (max 0 n.val) ++ ")"))

theorem showIntRanges_proven : ShowIntRanges := by
  intro t shw parse hp _hc
  refine ⟨fun a b r text hr ht => ?_, fun a s b r text hr ht => ?_, fun n r hr => ?_⟩
  · have hu := colon_unit a b
    simp only [JColon2.colon] at hu
    rw [hu] at hr; cases hr
    simp only [show_UnitRange, first_unit, last_unit, bind, Except.bind, pure, Except.pure,
      JShow.showValue] at ht
    cases ht
    refine ⟨_, _, rfl, _, _, hp _, hp _, ?_⟩
    rw [unitStop_val]
    split
    · rfl
    · rw [intsFromTo_empty (by omega), intsFromTo_empty (by omega)]
  · by_cases hs : s.val = 0
    · have hz := colon_step_zero a s b hs
      simp only [JColon3.colon] at hz
      rw [hz] at hr; cases hr
    obtain ⟨l, hc, _, hlv⟩ := colon_step a s b hs
    simp only [JColon3.colon] at hc
    rw [hc] at hr; cases hr
    simp only [show_AbstractRange, first_step, last_step, step_step, bind, Except.bind, pure,
      Except.pure, JRepr.repr] at ht
    cases ht
    refine ⟨_, _, _, rfl, _, _, _, hp _, hp _, hp _, ?_⟩
    rw [hlv, stepInts_lastVal _ _ _ hs]
  · have ho := oneTo_ok n
    simp only [JOneTo1.oneTo] at ho
    rw [ho] at hr; cases hr
    simp only [show_OneTo, JPrint.print, oneToStop_val]
    rfl

end ShowInt

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section T3
variable {t : IntTy}

/-! ## `checkbounds(r, s)` for a range index -/

/-- For a range `r` whose length `n` is nonnegative and a range index `s`, `checkbounds(r, s)`
(`checkboundsVectorRange`) succeeds exactly when `s` is empty or both its endpoints lie in
`1:n`, and throws `BoundsError` otherwise. -/
theorem checkboundsVectorRange_eq {R U : Type} {L e : IntTy} [JLength R (JInt L)] [JIsempty U]
    [JFirst U (JInt e)] [JLast U (JInt e)] (r : R) (s : U) (n : JInt L) (hr : JLength.length r = .ok n)
    (h0 : 0 ≤ n.val) (emp : Bool) (f l : JInt e) (he : JIsempty.isempty s = .ok emp)
    (hf : JFirst.first s = .ok f) (hl : JLast.last s = .ok l) :
    checkboundsVectorRange r s =
      if (emp || (decide (1 ≤ f.val ∧ f.val ≤ n.val) && decide (1 ≤ l.val ∧ l.val ≤ n.val))) = true
      then .ok () else .error (.jl .boundsError) := by
  have hc : ∀ i : JInt e, checkindexAxis (⟨n⟩ : OneTo (JInt L)) i = .ok (decide (1 ≤ i.val ∧ i.val ≤ n.val)) := by
    intro i
    unfold checkindexAxis
    split
    · rename_i h
      subst h
      rw [checkindexOneTo_iff _ _ h0]; rfl
    · simp [JuliaLean.base.abstractarray.checkindexReal, toArr, JFirst.first, JLast.last,
        last_OrdinalRange, JFieldStop.stop, le_iv, bind, Except.bind, pure, Except.pure, first_OneTo,
        oneunit_iv]
  simp only [checkboundsVectorRange, JuliaLean.base.abstractarray.checkboundsOne,
    JuliaLean.base.abstractarray.eachindexLinearVector, JuliaLean.base.abstractarray.axes1,
    size_AbstractRange, hr, toArr, bind, Except.bind, pure, Except.pure,
    JuliaLean.base.abstractarray.tupleGet, JuliaLean.base.abstractarray.int, JInt.lit, JInt.wrap,
    JuliaLean.base.abstractarray.checkindexRange, he, hf, hl]
  have h1 : wrapInt .i64 1 = 1 := by decide
  simp only [h1, show ¬ ((1 : Int) < 1) by decide, ite_false, show ((1 : Int) - 1).toNat = 0 by decide,
    List.getElem?_cons_zero, unchecked_oneto, hc, ofArr]
  by_cases h : (emp || (decide (1 ≤ f.val ∧ f.val ≤ n.val) && decide (1 ≤ l.val ∧ l.val ≤ n.val))) = true <;>
    simp_all [JThrowBoundserror.throwBoundserror, throw, throwThe, MonadExceptOf.throw]

/-! ## `OneTo` indexed by `OneTo`, `length(::OneTo)` -/

/-- `checkbounds(A, s)` of a `OneTo` and a `OneTo` index, as for the other integer ranges. -/
instance {u : IntTy} : JCheckbounds (OneTo (JInt t)) (OneTo (JInt u)) := ⟨checkboundsVectorRange⟩

/-- `r[s]` for `r = Base.OneTo(n)` and `s = Base.OneTo(m)` (`getindex(r::OneTo{T}, s::OneTo)`,
range.jl:1028; indexing a vector by a range of indices selects the elements at those indices, the
manual "Indexing"): when `s` lies inside `r`, `r[s]` is a `OneTo` with the `max(0, m)` elements
`r[1], ..., r[m]`, that is, `1, ..., max(0, m)`; otherwise `BoundsError`. -/
def GetindexOneTo : Prop :=
  ∀ (t u : IntTy) (n : JInt t) (m : JInt u) (r : OneTo (JInt t)) (s : OneTo (JInt u)),
    OneTo_stop n = .ok r → OneTo_stop m = .ok s →
    (max 0 m.val ≤ max 0 n.val →
      (getindex_OneTo_OneTo r s).map (fun q => q.stop.val) = .ok (max 0 m.val)) ∧
    (max 0 n.val < max 0 m.val → getindex_OneTo_OneTo r s = .error (.jl .boundsError))

theorem lengthOneTo_ok (m : JInt t) (h0 : 0 ≤ m.val) :
    ∃ len : JInt (lenTy t), (JLength.length (⟨m⟩ : OneTo (JInt t)) : JlX (JInt (lenTy t))) = .ok len ∧
      len.val = m.val := by
  have := lengthOneTo_val m h0
  revert this
  show (lengthOneTo (⟨m⟩ : OneTo (JInt t))).map Subtype.val = .ok m.val → _
  cases h : lengthOneTo (⟨m⟩ : OneTo (JInt t)) with
  | error e => simp [Except.map]
  | ok v => intro hv; simp [Except.map] at hv; exact ⟨v, h, hv⟩

theorem getindexOneTo_proven : GetindexOneTo := by
  intro t u n m r s hr hs
  have hro := oneTo_ok n
  have hso := oneTo_ok m
  simp only [JOneTo1.oneTo] at hro hso
  rw [hro] at hr; rw [hso] at hs; cases hr; cases hs
  have hn := oneToStop_val n
  have hm := oneToStop_val m
  obtain ⟨len, hlen, hlv⟩ := lengthOneTo_ok (oneToStop n) (by omega)
  have hcb := checkboundsVectorRange_eq (⟨oneToStop n⟩ : OneTo (JInt t)) (⟨oneToStop m⟩ : OneTo (JInt u))
    len hlen (by omega) _ JOneunit.oneunit (oneToStop m) (isempty_oneTo _) (first_oneTo _) (last_oneTo _)
  have h1 : (JOneunit.oneunit : JInt u).val = 1 := oneunit_iv
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · have hc : (decide ((oneToStop m).val < 1) || (decide (1 ≤ (JOneunit.oneunit : JInt u).val ∧
        (JOneunit.oneunit : JInt u).val ≤ len.val) && decide (1 ≤ (oneToStop m).val ∧
        (oneToStop m).val ≤ len.val))) = true := by
      rw [h1]; simp; omega
    have hmin : t.min ≤ 0 := by cases t <;> decide
    have hcv : (JCtor.ctor (oneToStop m) : JlX (JInt t)) = .ok ⟨(oneToStop m).val, by omega, by
        have := (oneToStop n).property; omega⟩ := by
      rw [ctor_iv, convert_ok (by omega) (by have := (oneToStop n).property; omega)]
    simp only [getindex_OneTo_OneTo, JCheckbounds.checkbounds, hcb, if_pos hc, hcv, bind,
      Except.bind]
    rw [oneTo_ok]
    simp [Except.map, oneToStop_val]
  · have hc : (decide ((oneToStop m).val < 1) || (decide (1 ≤ (JOneunit.oneunit : JInt u).val ∧
        (JOneunit.oneunit : JInt u).val ≤ len.val) && decide (1 ≤ (oneToStop m).val ∧
        (oneToStop m).val ≤ len.val))) = false := by
      rw [h1]; simp; omega
    simp only [getindex_OneTo_OneTo, JCheckbounds.checkbounds, hcb, hc, Bool.false_eq_true,
      ite_false, bind, Except.bind]

/-- `length(r::OneTo)` (range.jl:806), the method Julia selects for `OneTo{T}` of integer types
outside the BitIntegers (the BitIntegers use the `smallints`/`bigints` methods), applied to the
BitInteger arithmetic: `length(Base.OneTo(n))` is `max(0, n)`, the number of elements `1, ..., n`
(OneTo docstring, range.jl:449: "Define an `AbstractUnitRange` that behaves like `1:n`"). -/
def LengthOneToGeneric : Prop :=
  ∀ (t : IntTy) (n : JInt t) (r : OneTo (JInt t)), OneTo_stop n = .ok r →
    (length_OneTo (I := JInt t) r).map Subtype.val = .ok (max 0 n.val)

theorem lengthOneToGeneric_proven : LengthOneToGeneric := by
  intro t n r hr
  have hro := oneTo_ok n
  simp only [JOneTo1.oneTo] at hro
  rw [hro] at hr; cases hr
  have hn := oneToStop_val n
  have hz : ((oneToStop n - (JZero.zero : JInt t)) : JInt t).val = (oneToStop n).val := by
    rw [sub_iv, zero_iv, Int.sub_zero]
    exact wrap_in _ (oneToStop n).property.1 (oneToStop n).property.2
  simp [length_OneTo, JInteger.integer, Except.map, hz, hn, bind, Except.bind, pure, Except.pure]

/-! ## `mod(i, r::OneTo)` -/

theorem fldSpec_jint (t : IntTy) : JuliaLean.Proofs.base.int.FldSpec (JInt.fld (t := t)) := by
  intro a b hb1
  have hd := JuliaLean.Proofs.base.checked.divisionExact t a b
  by_cases hb0 : b.val = 0
  · rw [if_pos hb0]
    have := (hd.1 hb0).2.2.2.1
    simpa [JuliaLean.base.checked.checkedFld] using this
  · rw [if_neg hb0]
    have h := ((hd.2 hb0).2.2 (fun h => hb1 h.2.2)).2.1
    simp only [JuliaLean.base.checked.checkedFld] at h
    revert h
    cases hf : JInt.fld a b with
    | error e => simp [Except.map]
    | ok z =>
      intro h
      simp only [Except.map, Except.ok.injEq] at h
      congr 1
      apply Subtype.ext
      rw [← h]
      exact (wrap_in _ z.property.1 z.property.2).symm

/-- `mod(x::T, y::T)` of BitIntegers (int.jl:331-351), the function the `JMod` instance lifts. -/
def modJ (x y : JInt t) : Jl (JInt t) :=
  if t.signed then JuliaLean.base.int.mod_BitSigned JInt.fld x y else JuliaLean.base.int.mod_Unsigned x y

theorem modJ_ok (x y : JInt t) (hy : y.val ≠ 0) :
    modJ x y = .ok ⟨x.val.fmod y.val, JuliaLean.Proofs.base.int.fmod_fits x y hy⟩ := by
  unfold modJ
  split
  · rename_i hs
    exact ((JuliaLean.Proofs.base.int.modSigned_proven.1 t hs JInt.fld (fldSpec_jint t) x y).2 _).mpr
      ⟨hy, rfl⟩
  · rename_i hs
    exact ((JuliaLean.Proofs.base.int.modUnsigned_proven t (by simpa using hs) x y).2 _).mpr ⟨hy, rfl⟩

theorem modJ_zero (x y : JInt t) (hy : y.val = 0) : modJ x y = .error .divideError := by
  unfold modJ
  split
  · rename_i hs
    exact (JuliaLean.Proofs.base.int.modSigned_proven.1 t hs JInt.fld (fldSpec_jint t) x y).1.mpr hy
  · rename_i hs
    exact (JuliaLean.Proofs.base.int.modUnsigned_proven t (by simpa using hs) x y).1.mpr hy

theorem iszero_iv (x : JInt t) : JIszero.iszero x = decide (x.val = 0) := by
  show JuliaLean.base.int.eq x (JuliaLean.base.int.zero x) = _
  rw [IntVal.eq_eq]
  have : (JuliaLean.base.int.zero x).val = 0 := zero_iv
  rw [this]

/-- `mod1(x::T, y::T) where {T<:Real}` (operators.jl:914) for BitIntegers, with `mod(x::T, y::T)`
(int.jl:331-351) and `iszero`. -/
instance : JMod1 (JInt t) (JInt t) (JInt t) := ⟨fun x y =>
  liftJl (JuliaLean.base.operators.mod1 modJ (fun a => pure (JIszero.iszero a)) x y)⟩

/-- `mod(x::Integer, r::AbstractUnitRange)` docstring (range.jl:1537-1556): "Find `y` in the range
`r` such that `x ≡ y (mod n)`, where `n = length(r)`", with the example
`mod(0, Base.OneTo(3)) == 3`. For `mod(i::Integer, r::OneTo) = mod1(i, last(r))` (range.jl:1558)
and `r = Base.OneTo(n)` with `n >= 1`, the result `y` lies in `r` (`1 <= y <= n`) and `n` divides
`i - y`; an empty `OneTo` has no such `y`, and the call throws `DivideError`. -/
def ModOneTo : Prop :=
  ∀ (t : IntTy) (i n : JInt t) (r : OneTo (JInt t)), OneTo_stop n = .ok r →
    (1 ≤ n.val → ∃ y : JInt t, mod_Integer_OneTo i r = .ok y ∧ 1 ≤ y.val ∧ y.val ≤ n.val ∧
      n.val ∣ i.val - y.val) ∧
    (n.val < 1 → mod_Integer_OneTo i r = .error (.jl .divideError))

theorem modOneTo_proven : ModOneTo := by
  intro t i n r hr
  have hro := oneTo_ok n
  simp only [JOneTo1.oneTo] at hro
  rw [hro] at hr; cases hr
  have hn := oneToStop_val n
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hs : oneToStop n = n := by unfold oneToStop; rw [if_neg (by omega)]
    have hy : n.val ≠ 0 := by omega
    have hfb := Int.fmod_nonneg_of_pos i.val (show 0 < n.val by omega)
    have hfl := Int.fmod_lt_of_pos i.val (show 0 < n.val by omega)
    have hfd := Int.fmod_def i.val n.val
    by_cases hm0 : i.val.fmod n.val = 0
    · refine ⟨n, ?_, by omega, by omega, ?_⟩
      · simp [mod_Integer_OneTo, last_oneTo, hs, JMod1.mod1, JuliaLean.base.operators.mod1,
          modJ_ok i n hy, iszero_iv, hm0, bind, Except.bind, pure, Except.pure]
      · exact ⟨i.val.fdiv n.val - 1, by rw [Int.mul_sub]; omega⟩
    · refine ⟨⟨i.val.fmod n.val, JuliaLean.Proofs.base.int.fmod_fits i n hy⟩, ?_, by
        show 1 ≤ i.val.fmod n.val; omega, by show i.val.fmod n.val ≤ n.val; omega, ?_⟩
      · simp [mod_Integer_OneTo, last_oneTo, hs, JMod1.mod1, JuliaLean.base.operators.mod1,
          modJ_ok i n hy, iszero_iv, hm0, bind, Except.bind, pure, Except.pure]
      · exact ⟨i.val.fdiv n.val, by show i.val - i.val.fmod n.val = _; omega⟩
  · have hs : (oneToStop n).val = 0 := by rw [hn]; omega
    simp [mod_Integer_OneTo, last_oneTo, JMod1.mod1, JuliaLean.base.operators.mod1,
      modJ_zero i _ hs, bind, Except.bind]

end T3

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section T4
variable {t : IntTy}

/-! ## `+` and `-` of ranges -/

theorem lengthStep_ok (a s b l : JInt t) (hs : s.val ≠ 0) (hlv : l.val = lastVal a.val s.val b.val)
    (hfit : stepCount a.val s.val b.val ≤ (lenTy t).max) :
    ∃ n : JInt (lenTy t), (JLength.length (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) : JlX _) = .ok n ∧
      n.val = stepCount a.val s.val b.val := by
  have := lengthStep_colon a s b l hs hlv hfit
  revert this
  show (lengthStep (⟨a, s, l⟩ : StepRange (JInt t) (JInt t))).map Subtype.val = _ → _
  cases h : lengthStep (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) with
  | error e => simp [Except.map]
  | ok v => intro hv; simp [Except.map] at hv; exact ⟨v, h, hv⟩

/-- `r1 + r2` and `r1 - r2` of integer step ranges (`$f(r1::OrdinalRange, r2::OrdinalRange)`
generated by `_define_range_op`, range.jl:1504; the manual, "Arithmetic operators" on arrays:
"the dimensions must match"): when `a:s:b` and `c:u:d` (of one BitInteger type, with element counts
that fit the length type) have different numbers of elements, both throw `DimensionMismatch`. -/
def OrdinalOpMismatch : Prop :=
  ∀ (t : IntTy) (a s b c u d : JInt t) (r q : StepRange (JInt t) (JInt t)),
    colon_T_T_T_Real a s b = .ok r → colon_T_T_T_Real c u d = .ok q →
    stepCount a.val s.val b.val ≤ (lenTy t).max → stepCount c.val u.val d.val ≤ (lenTy t).max →
    stepCount a.val s.val b.val ≠ stepCount c.val u.val d.val →
    (∃ m, rangeop_OrdinalRange_OrdinalRange PlusOp r q = .error (.dimensionMismatch m)) ∧
    (∃ m, rangeop_OrdinalRange_OrdinalRange MinusOp r q = .error (.dimensionMismatch m))

theorem ordinalOpMismatch_proven : OrdinalOpMismatch := by
  intro t a s b c u d r q hr hq h1 h2 hne
  by_cases hs : s.val = 0
  · have hz := colon_step_zero a s b hs
    simp only [JColon3.colon] at hz
    rw [hz] at hr; cases hr
  by_cases hu : u.val = 0
  · have hz := colon_step_zero c u d hu
    simp only [JColon3.colon] at hz
    rw [hz] at hq; cases hq
  obtain ⟨l, hc, _, hlv⟩ := colon_step a s b hs
  obtain ⟨l', hc', _, hlv'⟩ := colon_step c u d hu
  simp only [JColon3.colon] at hc hc'
  rw [hc] at hr; rw [hc'] at hq; cases hr; cases hq
  obtain ⟨n, hn, hnv⟩ := lengthStep_ok a s b l hs hlv h1
  obtain ⟨m, hm, hmv⟩ := lengthStep_ok c u d l' hu hlv' h2
  have he : JEq.eq n m = false := by rw [eq_iv]; simp; omega
  refine ⟨?_, ?_⟩ <;>
    simp [rangeop_OrdinalRange_OrdinalRange, hn, hm, he, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]

/-- `r1 + r2` of two integer `StepRangeLen`s (`+(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S})`,
range.jl:1527; "the dimensions must match"): built by `StepRangeLen(ref, step, len, offset)` with
lengths `n` and `m` that differ, the sum throws `DimensionMismatch`. -/
def SRLAddMismatch : Prop :=
  ∀ (t : IntTy) (a s b u : JInt t) (n o m p : JInt64) (r q : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64),
    StepRangeLen_ref_step a s n o = .ok r → StepRangeLen_ref_step b u m p = .ok q → n.val ≠ m.val →
    ∃ msg, plus_StepRangeLen_StepRangeLen r q = .error (.dimensionMismatch msg)

theorem sRLAddMismatch_proven : SRLAddMismatch := by
  intro t a s b u n o m p r q hr hq hne
  rw [srl_ctor] at hr hq
  split at hr
  · split at hr
    · cases hr
      split at hq
      · split at hq
        · cases hq
          simp [plus_StepRangeLen_StepRangeLen, JLength.length, length_StepRangeLen, eq_iv, hne,
            bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
        · cases hq
      · cases hq
    · cases hr
  · cases hr

/-- `r1 + r2` of two integer `StepRangeLen`s of equal length `n` (range.jl:1527; the manual,
"Arithmetic operators": `+` on arrays is elementwise) has the elements `r1[i] + r2[i]`: for every
`1 <= i <= n` whose elements `r1[i]`, `r2[i]` can be read and whose exact sum is representable in
the element type, `(r1 + r2)[i]` is that sum. -/
def SRLAddElements : Prop :=
  ∀ (t : IntTy) (a s b u : JInt t) (n o p : JInt64) (r q : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)
    (i : JInt64) (x y : JInt t),
    StepRangeLen_ref_step a s n o = .ok r → StepRangeLen_ref_step b u n p = .ok q →
    1 ≤ i.val → i.val ≤ n.val → JGetindex.getindex r i = .ok x → JGetindex.getindex q i = .ok y →
    InT t (x.val + y.val) →
    ((plus_StepRangeLen_StepRangeLen r q >>= fun w => (JGetindex.getindex w i : JlX (JInt (pTy t t))))).map
      Subtype.val = .ok (x.val + y.val)

theorem sRLAddElements_refuted : ¬ SRLAddElements := by
  intro h
  have := h .i8 (lit .i8 (-60)) (lit .i8 100) (lit .i8 (-60)) (lit .i8 100) (lit .i64 2) (lit .i64 1)
    (lit .i64 1) ⟨lit .i8 (-60), lit .i8 100, lit .i64 2, lit .i64 1⟩
    ⟨lit .i8 (-60), lit .i8 100, lit .i64 2, lit .i64 1⟩ (lit .i64 2) (lit .i8 40) (lit .i8 40)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide)
  revert this; decide +kernel

/-- `-r` of an integer `StepRangeLen` (`-(r::StepRangeLen{T,R,S,L})`, range.jl:1323; the manual,
"Arithmetic operators": unary `-` on arrays is elementwise) has the elements `-r[i]`: for every
`1 <= i <= len` whose element `r[i]` can be read, `(-r)[i] == -r[i]`, the scalar negation of `T`
(which wraps for unsigned `T`). -/
def SRLNegElements : Prop :=
  ∀ (t : IntTy) (a s : JInt t) (n o : JInt64) (r : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)
    (i : JInt64) (x : JInt t),
    StepRangeLen_ref_step a s n o = .ok r → 1 ≤ i.val → i.val ≤ n.val →
    JGetindex.getindex r i = .ok x →
    (neg_StepRangeLen r >>= fun w => (JGetindex.getindex w i : JlX (JInt t))) = .ok (JNeg.neg x)

theorem sRLNegElements_refuted : ¬ SRLNegElements := by
  intro h
  have := h .u8 (lit .u8 0) (lit .u8 1) (lit .i64 3) (lit .i64 1)
    ⟨lit .u8 0, lit .u8 1, lit .i64 3, lit .i64 1⟩ (lit .i64 3) (lit .u8 2)
    (by decide +kernel) (by decide) (by decide) (by decide +kernel)
  revert this; decide +kernel

/-! ## `+` of `Float64` `LinRange`s -/

/-- `r1 + r2` and `r1 - r2` of `Float64` `LinRange`s (`$f(r1::LinRange{T}, r2::LinRange{T})`,
range.jl:1511; "the dimensions must match"): built by `LinRange(a, b, n)` with lengths that differ,
both throw `DimensionMismatch`; with equal lengths `n != 1`, the result is
`LinRange(f(a1, a2), f(b1, b2), n)`: its first and last elements combine the endpoints and its
length is `n`. Stated for every `Float64` printer in the error messages. -/
def LinRangeOp : Prop :=
  ∀ [JPrint F64] (a1 b1 a2 b2 : F64) (n m : JInt64) (r1 r2 : LinRange F64 JInt64),
    LinRange_start_stop_len a1 b1 n = .ok r1 → LinRange_start_stop_len a2 b2 m = .ok r2 →
    (n.val ≠ m.val →
      (∃ msg, rangeop_LinRange_LinRange PlusOp r1 r2 = .error (.dimensionMismatch msg)) ∧
      (∃ msg, rangeop_LinRange_LinRange MinusOp r1 r2 = .error (.dimensionMismatch msg))) ∧
    (n.val = m.val → n.val ≠ 1 →
      (∃ w : LinRange F64 JInt64, rangeop_LinRange_LinRange PlusOp r1 r2 = .ok w ∧
        JFirst.first w = .ok (a1 + a2) ∧ JLast.last w = .ok (b1 + b2) ∧ JLength.length w = .ok n) ∧
      (∃ w : LinRange F64 JInt64, rangeop_LinRange_LinRange MinusOp r1 r2 = .ok w ∧
        JFirst.first w = .ok (a1 - a2) ∧ JLast.last w = .ok (b1 - b2) ∧ JLength.length w = .ok n))

theorem linRange_ctor_fields [JPrint F64] (x y : F64) (k : JInt64) (w : LinRange F64 JInt64)
    (hw : LinRange_start_stop_len x y k = .ok w) : w.start = x ∧ w.stop = y ∧ w.len = k ∧ 0 ≤ k.val := by
  have hk := (linRangeFloatConstruct_proven x y k)
  by_cases hk0 : k.val < 0
  · obtain ⟨_, he⟩ := hk.1 hk0; rw [he] at hw; cases hw
  by_cases hk1 : k.val = 1 ∧ JEq.eq x y = false
  · obtain ⟨_, he⟩ := hk.2.1 hk1.1 hk1.2; rw [he] at hw; cases hw
  obtain ⟨w', hw', hf, hl, hn, -⟩ := hk.2.2 (by omega) (fun h => by
    cases hxy : JEq.eq x y
    · exact absurd ⟨h, hxy⟩ hk1
    · rfl)
  rw [hw'] at hw; cases hw
  simp only [JFirst.first, first_LinRange, pure, Except.pure, Except.ok.injEq] at hf
  simp only [JLast.last, last_LinRange, pure, Except.pure, Except.ok.injEq] at hl
  simp only [JLength.length, length_LinRange, pure, Except.pure, Except.ok.injEq] at hn
  exact ⟨hf, hl, hn, by omega⟩

theorem linRangeT_ok [JPrint F64] (x y : F64) (n : JInt64) (hn0 : 0 ≤ n.val) (hn1 : n.val ≠ 1) :
    ∃ w : LinRange F64 JInt64, (JLinRangeT.linRangeT (T := F64) x y n : JlX (LinRange F64 JInt64)) = .ok w ∧
      w.start = x ∧ w.stop = y ∧ w.len = n := by
  obtain ⟨d, hd⟩ : ∃ d, (JMax.max (n - (JOneunit.oneunit : JInt64)) (JOneunit.oneunit : JInt64) :
      JlX JInt64) = .ok d := ⟨_, max_same _ _⟩
  refine ⟨⟨x, y, n, d⟩, ?_, rfl, rfl, rfl⟩
  simp [JLinRangeT.linRangeT, LinRange_T, JLinRangeTL.linRangeTL, LinRange_TL_new, hn0, hn1,
    wrap64_0, hd, bind, Except.bind, pure, Except.pure, JType.isInteger, JMod.mod]

theorem linRangeOp_proven : LinRangeOp := by
  intro _ a1 b1 a2 b2 n m r1 r2 h1 h2
  obtain ⟨hs1, ht1, hl1, hn0⟩ := linRange_ctor_fields _ _ _ _ h1
  obtain ⟨hs2, ht2, hl2, hm0⟩ := linRange_ctor_fields _ _ _ _ h2
  refine ⟨fun hne => ⟨?_, ?_⟩, fun heq hn1 => ⟨?_, ?_⟩⟩
  · simp [rangeop_LinRange_LinRange, hl1, hl2, eq_iv, hne, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  · simp [rangeop_LinRange_LinRange, hl1, hl2, eq_iv, hne, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  · obtain ⟨w, hw, h1', h2', h3'⟩ := linRangeT_ok (a1 + a2) (b1 + b2) n hn0 hn1
    refine ⟨w, ?_, by simp [JFirst.first, first_LinRange, h1', pure, Except.pure],
      by simp [JLast.last, last_LinRange, h2', pure, Except.pure],
      by simp [JLength.length, length_LinRange, h3', pure, Except.pure]⟩
    have hnm : n = m := Subtype.ext heq
    subst hnm
    rw [← hw]
    obtain ⟨s1, t1, l1, d1⟩ := r1
    obtain ⟨s2, t2, l2, d2⟩ := r2
    simp only at hs1 ht1 hl1 hs2 ht2 hl2
    subst hs1 ht1 hl1 hs2 ht2 hl2
    unfold rangeop_LinRange_LinRange
    simp only [eq_iv, decide_true]
    rfl
  · obtain ⟨w, hw, h1', h2', h3'⟩ := linRangeT_ok (a1 - a2) (b1 - b2) n hn0 hn1
    refine ⟨w, ?_, by simp [JFirst.first, first_LinRange, h1', pure, Except.pure],
      by simp [JLast.last, last_LinRange, h2', pure, Except.pure],
      by simp [JLength.length, length_LinRange, h3', pure, Except.pure]⟩
    have hnm : n = m := Subtype.ext heq
    subst hnm
    rw [← hw]
    obtain ⟨s1, t1, l1, d1⟩ := r1
    obtain ⟨s2, t2, l2, d2⟩ := r2
    simp only at hs1 ht1 hl1 hs2 ht2 hl2
    subst hs1 ht1 hl1 hs2 ht2 hl2
    unfold rangeop_LinRange_LinRange
    simp only [eq_iv, decide_true]
    rfl

end T4

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## The `_colon(::Any, ::Any, start, step, stop)` fallback -/

/-- `convert(Integer, x::Int) = x` (`convert(::Type{T}, x::T) where {T<:Number} = x`, number.jl). -/
instance : JConvertInteger JInt64 JInt64 := ⟨pure⟩

/-- `_colon(::Any, ::Any, start::T, step, stop::T)` (range.jl:28; the `:` docstring: "`a:s:b` is
similar but uses a step size of `s`"), called with `Int` endpoints and step: whenever it returns,
the result is a `StepRangeLen` whose reference value is `start`, whose step is `step`, whose
reference index is `1` and whose length is nonnegative (the `StepRangeLen` docstring: "By default
`ref` is the starting value `r[1]`"). -/
def FallbackColonInvariant : Prop :=
  ∀ (a s b : JInt64) (r : StepRangeLen JInt64 JInt64 JInt64 JInt64),
    (_colon_Any_Any () () a s b : JlX (StepRangeLen JInt64 JInt64 JInt64 JInt64)) = .ok r →
    0 ≤ r.len.val ∧ r.ref = a ∧ r.step = s ∧ r.offset.val = 1

theorem fallbackColonInvariant_proven : FallbackColonInvariant := by
  intro a s b r hr
  cases hf : (JFld.fld (b - a) s : JlX JInt64) with
  | error e => simp [_colon_Any_Any, hf, bind, Except.bind] at hr
  | ok q =>
    have e : (_colon_Any_Any () () a s b : JlX (StepRangeLen JInt64 JInt64 JInt64 JInt64)) =
        StepRangeLen_ref_step a s (q + jint 1) (jint 1) := by
      simp only [_colon_Any_Any, hf, JConvertInteger.convertInteger, bind, Except.bind, pure,
        Except.pure]
      rfl
    rw [e, srl_ctor] at hr
    split at hr
    · rename_i h
      split at hr
      · cases hr; exact ⟨h, rfl, rfl, jint1_val⟩
      · cases hr
    · cases hr

/-! ## The generic `==` methods -/

section GenEq
variable {t : IntTy}

/-- `_has_length_one(r::OrdinalRange)`, range.jl:1177. -/
local instance : JHasLengthOne (StepRange (JInt t) (JInt t)) := ⟨_has_length_one_OrdinalRange⟩

/-- `==(r::T, s::T) where {T<:AbstractRange}` (range.jl:1151) and
`==(r::OrdinalRange, s::OrdinalRange)` (range.jl:1157), as `invoke` reaches them for two integer step
ranges `a:s:b` and `c:u:d` of one BitInteger type (the `==` docstring: collections are equal when
they have the same elements in the same order): each holds exactly when the ranges have the same
elements, including the empty and one-element cases. -/
def GenericRangeEquality : Prop :=
  ∀ (t : IntTy) (a s b c u d : JInt t) (r q : StepRange (JInt t) (JInt t)),
    colon_T_T_T_Real a s b = .ok r → colon_T_T_T_Real c u d = .ok q →
    eq_T_T_AbstractRange r q = .ok (decide (stepInts a.val s.val b.val = stepInts c.val u.val d.val)) ∧
    eq_OrdinalRange_OrdinalRange r q =
      .ok (decide (stepInts a.val s.val b.val = stepInts c.val u.val d.val))

theorem genericRangeEquality_proven : GenericRangeEquality := by
  intro t a s b c u d r q hr hq
  have h := stepRangeEq_proven t a s b c u d r q hr hq
  exact ⟨h, h⟩

end GenEq

/-! ## `step` of a `Float64` `StepRangeLen` -/

theorem floatSRL_ctor (a s : F64) (n o : JInt64) :
    (StepRangeLen_ref_step a s n o : JlX (StepRangeLen F64 F64 F64 JInt64)) =
      if 0 ≤ n.val then
        if 1 ≤ o.val ∧ o.val ≤ max 1 n.val then .ok ⟨a, s, n, o⟩
        else .error (.jl (.argumentError ("StepRangeLen: offset must be in [1," ++ JPrint.print n ++
          "], got " ++ JPrint.print o)))
      else .error (.jl (.argumentError ("length cannot be negative, got " ++ JPrint.print n))) := by
  simp only [StepRangeLen_ref_step, JStepRangeLenTRSL.stepRangeLenTRSL, StepRangeLen_TRSL_new,
    JType.isInteger, Bool.false_and, Bool.false_eq_true, ite_false, convert_self, le_iv,
    max_same, bind, Except.bind, pure, Except.pure, zero_iv, oneunit_iv,
    throw, throwThe, MonadExceptOf.throw]
  have hm : (if n.val < 1 then (JOneunit.oneunit : JInt64) else n).val = max 1 n.val := by
    by_cases h : n.val < 1 <;> simp [h, oneunit_iv] <;> omega
  simp only [hm]
  by_cases h0 : 0 ≤ n.val <;> by_cases h1 : 1 ≤ o.val ∧ o.val ≤ max 1 n.val <;> simp [h0, h1]

/-- `step(r::StepRangeLen{T}) where {T<:AbstractFloat} = T(r.step)` (range.jl:739; `step`
docstring: "Get the step size of an `AbstractRange` object") of
`StepRangeLen(ref, step, len, offset)` with `Float64` `ref` and `step` is that step, bit for bit
(including signed zeros and NaN payloads). -/
def FloatingSRLStep : Prop :=
  ∀ (a s : F64) (n o : JInt64) (r : StepRangeLen F64 F64 F64 JInt64),
    StepRangeLen_ref_step a s n o = .ok r → step_StepRangeLen_AbstractFloat r = .ok s

theorem floatingSRLStep_proven : FloatingSRLStep := by
  intro a s n o r hr
  rw [floatSRL_ctor] at hr
  split at hr
  · split at hr
    · cases hr; rfl
    · cases hr
  · cases hr

/-! ## `show(::LinRange)` -/

/-- `show(io, r::LinRange{T})` (range.jl:634; the manual, "Output": `show` writes "a text
representation of an object ... that should be parseable Julia code when possible") of
`LinRange(a, b, n)` with `Float64` endpoints writes `LinRange{Float64}(x, y, k)` where `x`, `y` and
`k` read back as `a`, `b` and `n`, so the text reconstructs the same range. Stated for every
`Float64` element printer (`show` with `:typeinfo`) and `Int` printer that a parser inverts, and every
`Float64` printer in the constructor's error messages. -/
def ShowLinRangeRoundTrip : Prop :=
  ∀ [JPrint F64] (sh : F64 → String) (parse : String → Option F64) (shn : JInt64 → String)
    (parseN : String → Option Int),
    (∀ x, parse (sh x) = some x) → (∀ k, parseN (shn k) = some k.val) →
    ∀ (a b : F64) (n : JInt64) (r : LinRange F64 JInt64), LinRange_start_stop_len a b n = .ok r →
      ∃ x y k : String,
        (letI : JShowType F64 := ⟨"Float64"⟩
         letI : JShowTypeinfo F64 F64 := ⟨fun z => pure (sh z)⟩
         letI : JShow JInt64 := ⟨fun z => pure (shn z)⟩
         show_LinRange ⟨⟩ r) =
          .ok ("LinRange{" ++ "Float64" ++ "}(" ++ x ++ ", " ++ y ++ ", " ++ k ++ ")") ∧
        parse x = some a ∧ parse y = some b ∧ parseN k = some n.val

theorem showLinRangeRoundTrip_proven : ShowLinRangeRoundTrip := by
  intro _ sh parse shn parseN hp hpn a b n r hr
  obtain ⟨hs, ht, hl, -⟩ := linRange_ctor_fields a b n r hr
  refine ⟨sh a, sh b, shn n, ?_, hp a, hp b, hpn n⟩
  subst hs ht hl
  rfl

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## `reverse` of a `Float64` `StepRangeLen` -/

section FloatReverse
open JuliaLean.Promotion

/-- `negate(x) = -x` (int.jl:99) on `Float64`, with `-(x::Float64) = neg_float(x)` (float.jl:485). -/
instance : JNegate F64 F64 := ⟨fun x => pure (JuliaLean.base.float.neg_IEEEFloat x)⟩
/-- `typeof(r)(ref, step, len, offset)` for a `StepRangeLen{Float64,Float64,Float64,Int}`: the inner
constructor, range.jl:533. -/
instance : JSameType4 (StepRangeLen F64 F64 F64 JInt64) F64 F64 JInt64 JInt64 :=
  ⟨StepRangeLen_TRSL_new F64⟩

theorem fl_ext {f : Fmt} (x y : Fl f) (h : x.toBits = y.toBits) : x = y := by
  obtain ⟨⟨u, hu⟩⟩ := x
  obtain ⟨⟨v, hv⟩⟩ := y
  simp only [Fl.toBits] at h
  subst h
  rfl

theorem fl_toBits_ofBits {f : Fmt} (n : Nat) : (Fl.ofBits n : Fl f).toBits = n % 2 ^ f.width := rfl

theorem fl_neg_eq {f : Fmt} (y : Fl f) : y.neg =
    if 2 ^ (f.eb + f.sb) ≤ y.toBits then Fl.ofBits (y.toBits - 2 ^ (f.eb + f.sb))
    else Fl.ofBits (y.toBits + 2 ^ (f.eb + f.sb)) := by
  simp only [Fl.neg, Fl.signbit, ge_iff_le, decide_eq_true_eq]

/-- Negating a float twice (toggling the sign bit twice) gives back the same bits. -/
theorem fl_neg_neg {f : Fmt} (x : Fl f) : x.neg.neg = x := by
  apply fl_ext
  have hv : x.toBits < 2 ^ f.width := x.bits.isLt
  have hW : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
    rw [Fmt.width, show 1 + f.eb + f.sb = (f.eb + f.sb) + 1 by omega, Nat.pow_succ]
    omega
  rw [fl_neg_eq x.neg, fl_neg_eq x]
  rw [hW] at hv
  generalize 2 ^ (f.eb + f.sb) = K at hv hW ⊢
  by_cases h : K ≤ x.toBits
  · simp only [if_pos h, fl_toBits_ofBits, hW]
    rw [Nat.mod_eq_of_lt (show x.toBits - K < 2 * K by omega), if_neg (by omega)]
    simp only [fl_toBits_ofBits, hW]
    rw [Nat.sub_add_cancel h, Nat.mod_eq_of_lt hv]
  · simp only [if_neg h, fl_toBits_ofBits, hW]
    rw [Nat.mod_eq_of_lt (show x.toBits + K < 2 * K by omega), if_pos (by omega)]
    simp only [fl_toBits_ofBits, hW]
    rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt hv]

theorem negFloat64_twice (x : F64) :
    JuliaLean.base.float.neg_IEEEFloat (JuliaLean.base.float.neg_IEEEFloat x) = x := by
  have hh : (JuliaLean.base.float.FTy.f64.fmt == half) = false := by decide
  have hb : (JuliaLean.base.float.FTy.f64.fmt == JuliaLean.C.bfloat) = false := by decide
  simp only [JuliaLean.base.float.neg_IEEEFloat, JuliaLean.base.float.neg_float,
    JuliaLean.C.jlNegFloat, JuliaLean.C.unaryFloat, JuliaLean.C.finishFloat, hh, hb,
    Bool.false_and, Bool.false_eq_true, ite_false]
  exact fl_neg_neg x

theorem wrap64_id (z : Int) (h1 : -9223372036854775808 ≤ z) (h2 : z ≤ 9223372036854775807) :
    wrapInt .i64 z = z :=
  wrap_in .i64 (by rw [i64min]; exact h1) (by rw [i64max]; exact h2)

/-- `reverse(r)` (`_reverse(r::StepRangeLen, ::Colon)`, range.jl:1446; `reverse` docstring: "Return a
copy of `v` reversed from start to stop") of a `Float64` `StepRangeLen(ref, step, len, offset)`
applied twice gives back `r` exactly: the same `ref`, the same step bits (including signed zeros
and NaN payloads), the same length and the same reference index, also for empty ranges. -/
def FloatSRLReverseInvolution : Prop :=
  ∀ (a s : F64) (n o : JInt64) (r : StepRangeLen F64 F64 F64 JInt64),
    StepRangeLen_ref_step a s n o = .ok r →
    (_reverse_StepRangeLen (Λ := JInt64) r ⟨⟩ >>= fun rr => _reverse_StepRangeLen (Λ := JInt64) rr ⟨⟩) =
      .ok r

theorem floatSRLReverseInvolution_proven : FloatSRLReverseInvolution := by
  intro a s n o r hr
  rw [floatSRL_ctor] at hr
  split at hr
  · rename_i hn
    split at hr
    · rename_i ho
      cases hr
      have hc : ∀ (x y : F64) (p : JInt64),
          (JSameType4.make x y n p : JlX (StepRangeLen F64 F64 F64 JInt64)) =
            StepRangeLen_ref_step x y n p := fun _ _ _ => rfl
      have hl : ∀ (x y : F64) (p : JInt64),
          (JLength.length (⟨x, y, n, p⟩ : StepRangeLen F64 F64 F64 JInt64) : JlX JInt64) = .ok n :=
        fun _ _ _ => rfl
      have hn1 := i64_bounds n
      have ho1 := i64_bounds o
      by_cases h0 : n.val = 0
      · have hz : JEq.eq n (jint 0) = true := by rw [eq_iv]; simp [h0]
        have r1 : _reverse_StepRangeLen (Λ := JInt64) (⟨a, s, n, o⟩ : StepRangeLen F64 F64 F64 JInt64) ⟨⟩ =
            .ok ⟨a, JuliaLean.base.float.neg_IEEEFloat s, n, o⟩ := by
          simp only [_reverse_StepRangeLen, JIsempty.isempty, isempty_StepRangeLen, hl, hz, bind,
            Except.bind, pure, Except.pure, JNegate.negate, ite_true]
          rw [hc, floatSRL_ctor, if_pos hn, if_pos ho]
        have r2 : _reverse_StepRangeLen (Λ := JInt64)
            (⟨a, JuliaLean.base.float.neg_IEEEFloat s, n, o⟩ : StepRangeLen F64 F64 F64 JInt64) ⟨⟩ =
            .ok ⟨a, s, n, o⟩ := by
          simp only [_reverse_StepRangeLen, JIsempty.isempty, isempty_StepRangeLen, hl, hz, bind,
            Except.bind, pure, Except.pure, JNegate.negate, ite_true]
          rw [negFloat64_twice, hc, floatSRL_ctor, if_pos hn, if_pos ho]
        rw [r1]; exact r2
      · have hz : JEq.eq n (jint 0) = false := by rw [eq_iv]; simp [h0]
        have e1 := i64min
        have e2 := i64max
        have hpv : (n - o + jint 1 : JInt64).val = n.val - o.val + 1 := by
          rw [add_iv, sub_iv, jint1_val, wrap64_id (n.val - o.val) (by omega) (by omega),
            wrap64_id (n.val - o.val + 1) (by omega) (by omega)]
        have hp : 1 ≤ (n - o + jint 1 : JInt64).val ∧ (n - o + jint 1 : JInt64).val ≤ max 1 n.val := by
          rw [hpv]; omega
        have hoff : n - (n - o + jint 1) + jint 1 = o := by
          apply Subtype.ext
          rw [add_iv, sub_iv, hpv, jint1_val, wrap64_id (n.val - (n.val - o.val + 1)) (by omega) (by omega),
            wrap64_id (n.val - (n.val - o.val + 1) + 1) (by omega) (by omega)]
          omega
        have r1 : _reverse_StepRangeLen (Λ := JInt64) (⟨a, s, n, o⟩ : StepRangeLen F64 F64 F64 JInt64) ⟨⟩ =
            .ok ⟨a, JuliaLean.base.float.neg_IEEEFloat s, n, n - o + jint 1⟩ := by
          simp only [_reverse_StepRangeLen, JIsempty.isempty, isempty_StepRangeLen, hl, hz, bind,
            Except.bind, pure, Except.pure, JNegate.negate, Bool.false_eq_true, ite_false]
          rw [hc, floatSRL_ctor, if_pos hn, if_pos hp]
        have r2 : _reverse_StepRangeLen (Λ := JInt64)
            (⟨a, JuliaLean.base.float.neg_IEEEFloat s, n, n - o + jint 1⟩ : StepRangeLen F64 F64 F64 JInt64) ⟨⟩ =
            .ok ⟨a, s, n, o⟩ := by
          simp only [_reverse_StepRangeLen, JIsempty.isempty, isempty_StepRangeLen, hl, hz, bind,
            Except.bind, pure, Except.pure, JNegate.negate, Bool.false_eq_true, ite_false]
          rw [hoff, negFloat64_twice, hc, floatSRL_ctor, if_pos hn, if_pos ho]
        rw [r1]; exact r2
    · cases hr
  · cases hr

end FloatReverse

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## Conversion of integer `StepRangeLen`s -/

section SRLConvert

/-- `StepRangeLen(ref, step, len, offset)`, range.jl:548, as `StepRangeLen{T}(r::StepRangeLen)`
(range.jl:1387) calls it. -/
instance {t : IntTy} : JStepRangeLen4 (JInt t) (JInt t) JInt64 JInt64
    (StepRangeLen (JInt t) (JInt t) (JInt t) JInt64) := ⟨StepRangeLen_ref_step⟩

theorem srl_success_fields {t : IntTy} (a s : JInt t) (n o : JInt64)
    (r : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64)
    (h : StepRangeLen_ref_step a s n o = .ok r) :
    r.ref = a ∧ r.step = s ∧ r.len = n ∧ r.offset = o ∧
      0 ≤ n.val ∧ 1 ≤ o.val ∧ o.val ≤ max 1 n.val := by
  rw [srl_ctor] at h
  split at h
  · rename_i hn
    split at h
    · rename_i ho
      cases h
      exact ⟨rfl, rfl, rfl, rfl, hn, ho⟩
    · cases h
  · cases h

theorem convert_val_of_ok {s u : IntTy} (x : JInt s) (y : JInt u)
    (h : (JConvert.convert x : JlX (JInt u)) = .ok y) : y.val = x.val := by
  rw [convert_iv] at h
  split at h
  · cases h; rfl
  · cases h

/-- Element `i` of an integer `StepRangeLen` with a valid length and offset, when representable. -/
theorem srl_read {u : IntTy} (q : StepRangeLen (JInt u) (JInt u) (JInt u) JInt64)
    (hn : 0 ≤ q.len.val) (ho : 1 ≤ q.offset.val ∧ q.offset.val ≤ max 1 q.len.val)
    (i : JInt64) (hi : 1 ≤ i.val ∧ i.val ≤ q.len.val)
    (hv : InT u (q.ref.val + (i.val - q.offset.val) * q.step.val)) :
    (JGetindex.getindex q i : JlX (JInt u)).map Subtype.val =
      .ok (q.ref.val + (i.val - q.offset.val) * q.step.val) := by
  rw [srl_getindex q i hn, if_pos hi]
  have h1 := i64_bounds i
  have h2 := i64_bounds q.offset
  have h3 := i64_bounds q.len
  have e1 := i64min
  have e2 := i64max
  have hw : wrapInt .i64 (i.val - q.offset.val) = i.val - q.offset.val :=
    wrap_in .i64 (by omega) (by omega)
  exact ugi_srl q.ref q.step q.len q.offset i hw hv

/-- `StepRangeLen{T,R,S,L}(r::StepRangeLen)` (range.jl:1385) and `StepRangeLen{T}(r::StepRangeLen)`
(range.jl:1387) convert a range to another element type (the `convert` docstring: "Convert `x` to
a value of type `T`"; an array conversion keeps the elements). For an integer
`StepRangeLen(ref, step, len, offset)` and any BitInteger target type, a converted range has the
same length and, at every index whose element is representable in the target type, the same
element `ref + (i - offset) * step`. -/
def SRLConversionElements : Prop :=
  ∀ (t u : IntTy) (a s : JInt t) (n o : JInt64)
    (r : StepRangeLen (JInt t) (JInt t) (JInt t) JInt64),
    StepRangeLen_ref_step a s n o = .ok r →
    ∀ q : StepRangeLen (JInt u) (JInt u) (JInt u) JInt64,
      (StepRangeLen_TRSL_StepRangeLen (T := JInt u) r = .ok q ∨
        StepRangeLen_T_StepRangeLen (T := JInt u) r = .ok q) →
      JLength.length q = .ok n ∧
      ∀ i : JInt64, 1 ≤ i.val → i.val ≤ n.val → InT u (a.val + (i.val - o.val) * s.val) →
        (JGetindex.getindex q i : JlX (JInt u)).map Subtype.val =
          .ok (a.val + (i.val - o.val) * s.val)

theorem sRLConversionElements_proven : SRLConversionElements := by
  intro t u a s n o r hr q hq
  obtain ⟨hra, hrs, hrn, hro, hn, ho⟩ := srl_success_fields a s n o r hr
  have hf : q.ref.val = a.val ∧ q.step.val = s.val ∧ q.len = n ∧ q.offset = o := by
    rcases hq with hq | hq
    · simp only [StepRangeLen_TRSL_StepRangeLen, convert_self, bind, Except.bind] at hq
      cases h1 : (JConvert.convert r.ref : JlX (JInt u)) with
      | error e => simp [h1] at hq
      | ok a' =>
        cases h2 : (JConvert.convert r.step : JlX (JInt u)) with
        | error e => simp [h1, h2] at hq
        | ok b' =>
          simp only [h1, h2] at hq
          obtain ⟨ha, hs, hl, ho', -⟩ := srl_success_fields a' b' r.len r.offset q hq
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [ha, convert_val_of_ok _ _ h1, hra]
          · rw [hs, convert_val_of_ok _ _ h2, hrs]
          · rw [hl, hrn]
          · rw [ho', hro]
    · simp only [StepRangeLen_T_StepRangeLen, bind, Except.bind] at hq
      cases h1 : (JConvert.convert r.ref : JlX (JInt u)) with
      | error e => simp [h1] at hq
      | ok a' =>
        cases h2 : (JConvert.convert r.step : JlX (JInt u)) with
        | error e => simp [h1, h2] at hq
        | ok b' =>
          simp only [h1, h2] at hq
          obtain ⟨ha, hs, hl, ho', -⟩ := srl_success_fields a' b' r.len r.offset q hq
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [ha, convert_val_of_ok _ _ h1, hra]
          · rw [hs, convert_val_of_ok _ _ h2, hrs]
          · rw [hl, hrn]
          · rw [ho', hro]
  obtain ⟨hqa, hqs, hqn, hqo⟩ := hf
  refine ⟨by simp [JLength.length, length_StepRangeLen, hqn, pure, Except.pure], fun i hi0 hi1 hv => ?_⟩
  have := srl_read q (by rw [hqn]; exact hn) (by rw [hqo, hqn]; exact ho) i
    ⟨hi0, by rw [hqn]; exact hi1⟩ (by rw [hqa, hqs, hqo]; exact hv)
  rw [hqa, hqs, hqo] at this
  exact this

end SRLConvert

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## Conversion of integer step ranges to `StepRange` -/

section StepConvert
variable {t : IntTy}

/-- `StepRange{T1,T2}(r::AbstractRange)` (range.jl:1372), `StepRange(r::OrdinalRange{T,S})`
(range.jl:1374) and `StepRange{T}(r::OrdinalRange{<:Any,S})` (range.jl:1375), as `invoke` reaches
them for an integer step range `a:s:b` converted to its own element and step types (the `convert`
docstring: "Convert `x` to a value of type `T`"; converting an array keeps its elements): all three
succeed with the same range, and iterating it yields exactly the elements of `a:s:b`. -/
def StepRangeConvertElements : Prop :=
  ∀ (t : IntTy) (a s b : JInt t) (r : StepRange (JInt t) (JInt t)), colon_T_T_T_Real a s b = .ok r →
    ∃ q : StepRange (JInt t) (JInt t),
      StepRange_OrdinalRange r = .ok q ∧ StepRange_T_OrdinalRange (T := JInt t) r = .ok q ∧
      StepRange_TS_AbstractRange (T1 := JInt t) (T2 := JInt t) r = .ok q ∧
      ∀ fuel, (stepCount a.val s.val b.val).toNat ≤ fuel →
        iterVals q fuel = .ok (stepInts a.val s.val b.val)

theorem stepRangeConvertElements_proven : StepRangeConvertElements := by
  intro t a s b r hr
  by_cases hs : s.val = 0
  · have hz := colon_step_zero a s b hs
    simp only [JColon3.colon] at hz
    rw [hz] at hr; cases hr
  obtain ⟨l, hc, -, hlv⟩ := colon_step a s b hs
  simp only [JColon3.colon] at hc
  rw [hc] at hr; cases hr
  obtain ⟨l', -, hc2', -⟩ := colon_step a s l hs
  have hq : StepRange_OrdinalRange (⟨a, s, l⟩ : StepRange (JInt t) (JInt t)) = .ok ⟨a, s, l'⟩ := by
    simp only [StepRange_OrdinalRange, first_step, last_step, step_step, bind, Except.bind]
    exact hc2'
  refine ⟨⟨a, s, l'⟩, hq, hq, ?_, ?_⟩
  · simp only [StepRange_TS_AbstractRange, first_step, last_step, step_step, convert_self, bind,
      Except.bind]
    exact hc2'
  · intro fuel hf
    have hcount : stepCount a.val s.val l.val = stepCount a.val s.val b.val := by
      rw [hlv]; exact stepCount_lastVal _ _ _ hs
    obtain ⟨r', -, hr2, -, -, -, -, hit⟩ := (stepRangeColon_proven t a s l).2 hs
    rw [hc2'] at hr2
    cases hr2
    rw [hit fuel (by rw [hcount]; exact hf), hlv, stepInts_lastVal _ _ _ hs]

end StepConvert

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## Membership in integer step ranges -/

section StepMembership
variable {s t : IntTy}

/-- `minimum(r::AbstractRange)`, range.jl:883. -/
instance : JMinimum (StepRange (JInt t) (JInt t)) (JInt t) := ⟨minimum_AbstractRange⟩
/-- `maximum(r::AbstractRange)`, range.jl:884. -/
instance : JMaximum (StepRange (JInt t) (JInt t)) (JInt t) := ⟨maximum_AbstractRange⟩

/-- `x % T` of a difference `d` that lies strictly between `-(2^bits)` and `2^bits` is zero
exactly when `d` is. -/
theorem wrap_eq_zero_iff (t : IntTy) (d : Int) (h1 : t.min - t.max ≤ d) (h2 : d ≤ t.max - t.min) :
    wrapInt t d = 0 ↔ d = 0 := by
  cases t <;> simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at * <;> omega

/-- The elements of `a:s:b` (with at least one element and last element `l`) are the integers
between `min(a, l)` and `max(a, l)` that are congruent to `a` modulo `s`. -/
theorem mem_stepInts_fmod (a s b x : Int) (hs : s ≠ 0) (hc : 0 < stepCount a s b) :
    x ∈ stepInts a s b ↔
      ((if a + (stepCount a s b - 1) * s < a then a + (stepCount a s b - 1) * s else a) ≤ x ∧
        x ≤ (if a + (stepCount a s b - 1) * s < a then a else a + (stepCount a s b - 1) * s) ∧
        x.fmod s = a.fmod s) := by
  rw [mem_stepInts]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hb := stepInts_between a s b k hk
    have hm : (a + (k : Int) * s).fmod s = a.fmod s := by
      rw [Int.mul_comm]; exact Int.add_mul_fmod_self_left a s k
    rcases Int.lt_or_gt_of_ne hs with h | h
    · have := hb.2 h
      refine ⟨?_, ?_, hm⟩ <;> split <;> omega
    · have := hb.1 h
      refine ⟨?_, ?_, hm⟩ <;> split <;> omega
  · rintro ⟨h1, h2, h3⟩
    have hz : (x - a).fmod s = 0 := Int.fmod_eq_fmod_iff_fmod_sub_eq_zero.mp h3
    have hd := Int.fmod_def (x - a) s
    rw [hz] at hd
    generalize hq : (x - a).fdiv s = q at hd
    have hx : x = a + q * s := by rw [Int.mul_comm]; omega
    subst hx
    generalize hn : stepCount a s b = n at *
    have e1 : q * s = s * q := Int.mul_comm q s
    have e2 : (n - 1) * s = s * (n - 1) := Int.mul_comm (n - 1) s
    rcases Int.lt_or_gt_of_ne hs with h | h
    · have hle : (n - 1) * s ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      have hb1 : a + (n - 1) * s ≤ a + q * s := by split at h1 <;> omega
      have hb2 : a + q * s ≤ a := by split at h2 <;> omega
      have hq0 : 0 ≤ q := by
        have : (-s) * 0 ≤ (-s) * q := by rw [Int.mul_zero, Int.neg_mul]; omega
        exact Int.le_of_mul_le_mul_left this (by omega)
      have hq1 : q ≤ n - 1 := by
        have : (-s) * q ≤ (-s) * (n - 1) := by rw [Int.neg_mul, Int.neg_mul]; omega
        exact Int.le_of_mul_le_mul_left this (by omega)
      exact ⟨q.toNat, by omega, by rw [Int.toNat_of_nonneg hq0]⟩
    · have hle : 0 ≤ (n - 1) * s := Int.mul_nonneg (by omega) (by omega)
      have hb1 : a ≤ a + q * s := by split at h1 <;> omega
      have hb2 : a + q * s ≤ a + (n - 1) * s := by split at h2 <;> omega
      have hq0 : 0 ≤ q := by
        have : s * 0 ≤ s * q := by rw [Int.mul_zero]; omega
        exact Int.le_of_mul_le_mul_left this (by omega)
      have hq1 : q ≤ n - 1 := by
        have : s * q ≤ s * (n - 1) := by omega
        exact Int.le_of_mul_le_mul_left this (by omega)
      exact ⟨q.toNat, by omega, by rw [Int.toNat_of_nonneg hq0]⟩

/-- `mod(x::T, y::T)` of BitIntegers through the world instance. -/
theorem mod_iv (x y : JInt t) (hy : y.val ≠ 0) :
    (JMod.mod x y : JlX (JInt t)) =
      .ok ⟨x.val.fmod y.val, JuliaLean.Proofs.base.int.fmod_fits x y hy⟩ := by
  show liftJl (modJ x y) = _
  rw [modJ_ok x y hy]; rfl

/-- `x in r` for an integer step range `r = a:s:b` of any BitInteger type and an integer `x` of
any BitInteger type (`in(x::Real, r::AbstractRange{T}) where {T<:Integer}`, range.jl:1491, which
Julia selects for these arguments; the `in` docstring: "Determine whether an item is in the given
collection"): it holds exactly when `x` equals one of the elements `a, a+s, ...` between `a` and
`b`, for every pair of widths, including steps of `typemin`, empty ranges and ranges spanning the
whole type. -/
def StepRangeMembership : Prop :=
  ∀ (t s : IntTy) (a st b : JInt t) (r : StepRange (JInt t) (JInt t)) (x : JInt s),
    colon_T_T_T_Real a st b = .ok r →
    in_Real_AbstractRange_Integer x r = .ok (decide (x.val ∈ stepInts a.val st.val b.val))

theorem stepRangeMembership_proven : StepRangeMembership := by
  intro t s a st b r x hr
  by_cases hs : st.val = 0
  · have := colon_step_zero a st b hs
    simp only [JColon3.colon] at this
    rw [this] at hr; cases hr
  obtain ⟨l, hc, _, hlv⟩ := colon_step a st b hs
  simp only [JColon3.colon] at hc
  rw [hc] at hr; cases hr
  have hemp := isempty_lastVal a.val st.val b.val hs
  rw [← hlv] at hemp
  have hcn := stepCount_nonneg a.val st.val b.val
  have hst : JIszero.iszero st = false := by rw [iszero_iv]; simp [hs]
  by_cases h0 : stepCount a.val st.val b.val = 0
  · have he : (decide (a.val ≠ l.val) && (decide (0 < st.val) != decide (a.val < l.val))) = true := by
      rw [hemp]; simp [h0]
    have hnil : stepInts a.val st.val b.val = [] := (stepInts_nil_iff _ _ _).mpr h0
    simp only [in_Real_AbstractRange_Integer, JIsinteger.isinteger,
      JuliaLean.base.number.isintegerInteger, Bool.not_true, Bool.false_eq_true, ite_false,
      isempty_step, he, hnil, bind, Except.bind, pure, Except.pure, ite_true]
    simp
  · have he : (decide (a.val ≠ l.val) && (decide (0 < st.val) != decide (a.val < l.val))) = false := by
      rw [hemp]; simp; omega
    obtain ⟨hmin, hmax⟩ := (minmax_step a st b l hs hlv).2 (by omega)
    have hlast : l.val = a.val + (stepCount a.val st.val b.val - 1) * st.val := by
      rw [hlv]; exact lastVal_count _ _ _ hs (by omega)
    have hmem := mem_stepInts_fmod a.val st.val b.val x.val hs (by omega)
    rw [← hlast] at hmem
    have hmin' : JMinimum.minimum (⟨a, st, l⟩ : StepRange (JInt t) (JInt t)) =
        .ok (if l.val < a.val then l else a) := hmin
    have hmax' : JMaximum.maximum (⟨a, st, l⟩ : StepRange (JInt t) (JInt t)) =
        .ok (if l.val < a.val then a else l) := hmax
    simp only [in_Real_AbstractRange_Integer, JIsinteger.isinteger,
      JuliaLean.base.number.isintegerInteger, Bool.not_true, Bool.false_eq_true, ite_false,
      isempty_step, he, step_step, hst, first_step, hmin', hmax', bind, Except.bind, pure,
      Except.pure, le_iv]
    by_cases hlo : (if l.val < a.val then l else a).val ≤ x.val
    · by_cases hhi : x.val ≤ (if l.val < a.val then a else l).val
      · have hlo' := (if l.val < a.val then l else a).property
        have hhi' := (if l.val < a.val then a else l).property
        have hxt : t.min ≤ x.val ∧ x.val ≤ t.max := ⟨by omega, by omega⟩
        simp only [hlo, hhi, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
        rw [convert_ok hxt.1 hxt.2]
        simp only [mod_iv _ st hs, eq_iv, sub_iv, jint0_val]
        have hb := JuliaLean.Proofs.base.int.fmod_bounds x.val st.val hs
        have hb' := JuliaLean.Proofs.base.int.fmod_bounds a.val st.val hs
        have hsp := st.property
        have hmz := min_le_zero t; have hmx := zero_lt_max t
        have hw := wrap_eq_zero_iff t (x.val.fmod st.val - a.val.fmod st.val)
          (by rcases Int.lt_or_gt_of_ne hs with h | h
              · have := hb.2 h; have := hb'.2 h; omega
              · have := hb.1 h; have := hb'.1 h; omega)
          (by rcases Int.lt_or_gt_of_ne hs with h | h
              · have := hb.2 h; have := hb'.2 h; omega
              · have := hb.1 h; have := hb'.1 h; omega)
        have hite1 : (if l.val < a.val then l else a).val = (if l.val < a.val then l.val else a.val) := by
          split <;> rfl
        have hite2 : (if l.val < a.val then a else l).val = (if l.val < a.val then a.val else l.val) := by
          split <;> rfl
        rw [hite1] at hlo; rw [hite2] at hhi
        congr 1
        apply bool_eq_decide
        rw [decide_eq_true_iff, hw, hmem]
        constructor
        · intro h; exact ⟨hlo, hhi, by omega⟩
        · rintro ⟨-, -, h⟩; omega
      · simp only [hlo, hhi, decide_true, decide_false, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true, Except.ok.injEq]
        symm; rw [decide_eq_false_iff_not, hmem]
        rintro ⟨-, h2, -⟩; apply hhi; split <;> split at h2 <;> simp_all <;> omega
    · simp only [hlo, decide_false, Bool.not_false, ite_true, Except.ok.injEq]
      symm; rw [decide_eq_false_iff_not, hmem]
      rintro ⟨h1, -, -⟩; apply hlo; split <;> split at h1 <;> simp_all <;> omega

end StepMembership

/-! ## Intersections of several integer unit ranges -/

section IntersectMany
variable {t : IntTy}

/-- `intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})`, range.jl:1209. -/
instance : JIntersect (UnitRange (JInt t)) (UnitRange (JInt t)) (UnitRange (JInt t)) :=
  ⟨intersect_AbstractUnitRange_AbstractUnitRange⟩

theorem intersect_step (m n c d : JInt t) :
    ∃ m' n' : JInt t,
      (JIntersect.intersect (⟨m, unitStop m n⟩ : UnitRange (JInt t)) (⟨c, unitStop c d⟩ : UnitRange (JInt t)) :
        JlX (UnitRange (JInt t))) = .ok ⟨m', unitStop m' n'⟩ ∧
      ∀ x, (m'.val ≤ x ∧ x ≤ n'.val) ↔ ((m.val ≤ x ∧ x ≤ n.val) ∧ (c.val ≤ x ∧ x ≤ d.val)) := by
  refine ⟨_, _, intersect_unit m n c d, fun x => ?_⟩
  have h1 := unitStop_val m n; have h2 := unitStop_val c d
  split <;> split <;> simp only [h1, h2] at * <;> split at * <;> split at * <;> omega

/-- One step of the loop `for t in r; i = intersect(i, t); end` of range.jl:1289. -/
def interStep (r u : UnitRange (JInt t)) : JlX (ForInStep (UnitRange (JInt t))) :=
  (JIntersect.intersect u r : JlX (UnitRange (JInt t))).map ForInStep.yield

theorem forIn_fun_congr {F G : UnitRange (JInt t) → UnitRange (JInt t) → JlX (ForInStep (UnitRange (JInt t)))}
    (rs : List (UnitRange (JInt t))) (x : UnitRange (JInt t)) (h : ∀ r u, F r u = G r u) :
    forIn rs x F = forIn rs x G := by
  have : F = G := funext fun r => funext fun u => h r u
  rw [this]

theorem forIn_intersect :
    ∀ (ps : List (JInt t × JInt t)) (rs : List (UnitRange (JInt t))),
      ps.mapM (fun p => (JColon2.colon p.1 p.2 : JlX (UnitRange (JInt t)))) = .ok rs → ∀ m n : JInt t,
      ∃ m' n' : JInt t, forIn rs (⟨m, unitStop m n⟩ : UnitRange (JInt t)) interStep = .ok ⟨m', unitStop m' n'⟩ ∧
        ∀ x, (m'.val ≤ x ∧ x ≤ n'.val) ↔
          ((m.val ≤ x ∧ x ≤ n.val) ∧ ∀ p ∈ ps, x ∈ intsFromTo p.1.val p.2.val) := by
  intro ps
  induction ps with
  | nil =>
    intro rs h m n
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨m, n, rfl, fun x => by simp⟩
  | cons p ps ih =>
    intro rs h m n
    rw [List.mapM_cons, colon_unit] at h
    cases hq : ps.mapM (fun p => (JColon2.colon p.1 p.2 : JlX (UnitRange (JInt t)))) with
    | error e => rw [hq] at h; simp [bind, Except.bind] at h
    | ok qs =>
      rw [hq] at h
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨m1, n1, h1, hx1⟩ := intersect_step m n p.1 p.2
      obtain ⟨m2, n2, h2, hx2⟩ := ih qs hq m1 n1
      refine ⟨m2, n2, ?_, fun x => ?_⟩
      · simp only [List.forIn_cons, interStep, h1, Except.map, bind, Except.bind]
        exact h2
      · rw [hx2, hx1]
        simp only [List.mem_cons, forall_eq_or_imp, mem_intsFromTo]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- `intersect(r1, r2, r3, r...)` of integer unit ranges (range.jl:1287; the `intersect` docstring:
"Construct the set containing those elements which appear in all of the arguments"): for unit
ranges `a:b`, `c:d`, `e:f` and any further unit ranges `p:q`, all of one BitInteger type,
iterating the result visits, in increasing order, exactly the integers that lie in every one of
them. -/
def IntersectUnitMany : Prop :=
  ∀ (t : IntTy) (a b c d e f : JInt t) (ps : List (JInt t × JInt t)) (r1 r2 r3 : UnitRange (JInt t))
    (rs : List (UnitRange (JInt t))) (fuel : Nat),
    JColon2.colon a b = .ok r1 → JColon2.colon c d = .ok r2 → JColon2.colon e f = .ok r3 →
    ps.mapM (fun p => (JColon2.colon p.1 p.2 : JlX (UnitRange (JInt t)))) = .ok rs → (b.val - a.val).toNat < fuel →
    ∃ i : UnitRange (JInt t), intersect_AbstractRange_3 r1 r2 r3 rs = .ok i ∧
      ∃ xs, iterVals i fuel = .ok xs ∧ xs.Pairwise (· < ·) ∧
        ∀ x, x ∈ xs ↔ (x ∈ intsFromTo a.val b.val ∧ x ∈ intsFromTo c.val d.val ∧
          x ∈ intsFromTo e.val f.val ∧ ∀ p ∈ ps, x ∈ intsFromTo p.1.val p.2.val)

theorem intersectUnitMany_proven : IntersectUnitMany := by
  intro t a b c d e f ps r1 r2 r3 rs fuel h1 h2 h3 hps hf
  rw [colon_unit] at h1 h2 h3; cases h1; cases h2; cases h3
  obtain ⟨m1, n1, hi1, hx1⟩ := intersect_step a b c d
  obtain ⟨m2, n2, hi2, hx2⟩ := intersect_step m1 n1 e f
  obtain ⟨m3, n3, hloop, hx3⟩ := forIn_intersect ps rs hps m2 n2
  refine ⟨⟨m3, unitStop m3 n3⟩, ?_, intsFromTo m3.val n3.val, ?_, intsFromTo_pairwise _ _, ?_⟩
  · simp only [intersect_AbstractRange_3, hi1, hi2, bind, Except.bind]
    rw [forIn_fun_congr (G := interStep) rs _ ?hF, hloop]
    · rfl
    · intro r u
      cases h : (JIntersect.intersect u r : JlX (UnitRange (JInt t))) <;> simp [interStep, h, Except.map] <;> rfl
  · apply iterVals_unitStop
    by_cases hmn : m3.val ≤ n3.val
    · have hm := (hx3 m3.val).mp ⟨Int.le_refl _, hmn⟩
      have hn := (hx3 n3.val).mp ⟨hmn, Int.le_refl _⟩
      rw [hx2, hx1] at hm hn
      omega
    · omega
  · intro x
    rw [mem_intsFromTo, hx3, hx2, hx1]
    simp only [mem_intsFromTo]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

end IntersectMany

/-! ## Sorting ranges -/

section Sorting

/-- `lastindex(a::AbstractArray)` (abstractarray.jl:429): `last(axes1(a))`, the length
`length(r::OrdinalRange)` of a step range whose step has its element type. -/
instance {t : IntTy} : JLastindex (StepRange (JInt t) (JInt t)) (JInt (lenTy t)) := ⟨JLength.length⟩
/-- `issorted(r::AbstractRange)`, range.jl:1458, for a step range whose step has its element type. -/
instance {t : IntTy} : JIssorted (StepRange (JInt t) (JInt t)) := ⟨issorted_AbstractRange⟩

theorem pairwise_affine (a s : Int) (l : List Int) (hl : l.Pairwise (· < ·)) (hs : 0 < s) :
    (l.map fun k => a + (k - 1) * s).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  exact hl.imp fun {x y} h => by
    have := Int.mul_lt_mul_of_pos_right (show x - 1 < y - 1 by omega) hs; omega

theorem pairwise_affine_neg (a s : Int) (l : List Int) (hl : l.Pairwise (· < ·)) (hs : s < 0) :
    (l.reverse.map fun k => a + (k - 1) * s).Pairwise (· < ·) := by
  rw [List.map_reverse, List.pairwise_reverse, List.pairwise_map]
  exact hl.imp fun {x y} h => by
    have := Int.mul_lt_mul_of_pos_right (show x - 1 < y - 1 by omega) (show 0 < -s by omega)
    rw [Int.mul_neg, Int.mul_neg] at this; omega

theorem stepCount_one (m : Int) (h : 0 ≤ m) : stepCount 1 1 m = m := by
  unfold stepCount
  by_cases h1 : 1 ≤ m
  · rw [if_pos ⟨by decide, h1⟩, Int.tdiv_one]; omega
  · rw [if_neg (by omega), if_neg (by omega)]; omega

theorem stepInts_one (a b : Int) : stepInts a 1 b = intsFromTo a b := by
  unfold stepInts intsFromTo stepCount
  by_cases h : a ≤ b
  · rw [if_pos ⟨by decide, h⟩, Int.tdiv_one]
    apply List.map_congr_left; intro k _; omega
  · rw [if_neg (by omega), if_neg (by omega), show (b - a + 1).toNat = 0 by omega]; simp

theorem stepInts_neg_one (n : Int) (h : 0 ≤ n) : stepInts n (-1) 1 = (intsFromTo 1 n).reverse := by
  have hc : stepCount n (-1) 1 = n := by
    unfold stepCount
    by_cases h1 : 1 ≤ n
    · rw [if_neg (by omega), if_pos ⟨by decide, h1⟩, Int.neg_neg, Int.tdiv_one]; omega
    · rw [if_neg (by omega), if_neg (by omega)]; omega
  unfold stepInts intsFromTo
  rw [hc, show n - 1 + 1 = n by omega]
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range, List.length_reverse] at h1 h2 ⊢
    omega

/-- Sorting ranges (docstrings of `issorted`, `sort`, `sort!` and `sortperm`: "Return a
permutation vector `I` that puts `v[I]` in sorted order"): an integer unit range `a:b` of any
BitInteger type is sorted, `sort` and `sort!` return it unchanged (range.jl:1457, 1460, 1461), and
`sortperm(a:b)` (range.jl:1465) iterates the identity permutation `1, ..., n`; for an `Int` step
range `a:s:b` whose length `n` is representable, `sortperm(a:s:b)` (range.jl:1466) iterates a
permutation of `1, ..., n` that lists the indices of the elements `a + (k-1)*s` in increasing order
of the elements. -/
def SortingMethods : Prop :=
  (∀ (t : IntTy) (a b : JInt t) (r : UnitRange (JInt t)), JColon2.colon a b = .ok r →
    issorted_AbstractUnitRange r = true ∧ sort_AbstractUnitRange r = r ∧ sort!_AbstractUnitRange r = r ∧
    (cnt a.val b.val ≤ (lenTy t).max → ∃ p : OneTo (JInt (lenTy t)), sortperm_AbstractUnitRange r = .ok p ∧
      ∀ fuel : Nat, cnt a.val b.val < (fuel : Int) → iterVals p fuel = .ok (intsFromTo 1 (cnt a.val b.val)))) ∧
  (∀ (a s b : JInt64) (r : StepRange JInt64 JInt64), colon_T_T_T_Real a s b = .ok r →
    stepCount a.val s.val b.val ≤ IntTy.i64.max →
    ∃ p : StepRange JInt64 JInt64, sortperm_AbstractRange r = .ok p ∧
      ∀ fuel : Nat, stepCount a.val s.val b.val ≤ (fuel : Int) → ∃ ps, iterVals p fuel = .ok ps ∧
        ps.Perm (intsFromTo 1 (stepCount a.val s.val b.val)) ∧
        (ps.map fun k => a.val + (k - 1) * s.val).Pairwise (· < ·))

theorem sortingMethods_proven : SortingMethods := by
  refine ⟨fun t a b r hr => ?_, fun a s b r hr hfit => ?_⟩
  · refine ⟨rfl, rfl, rfl, fun hc => ?_⟩
    obtain ⟨r', hr', -, -, -, hp⟩ := unitIndexQueries_proven t a b hc
    rw [hr] at hr'; cases hr'
    obtain ⟨p, hp, hpv⟩ := hp
    refine ⟨p, hp, fun fuel hf => ?_⟩
    have h0 : 0 ≤ p.stop.val := by rw [hpv]; unfold cnt; split <;> omega
    have := iterList_oneTo p fuel h0 (by rw [hpv]; omega)
    unfold iterVals; rw [this, hpv]
  · by_cases hs : s.val = 0
    · have := colon_step_zero a s b hs; simp only [JColon3.colon] at this; rw [this] at hr; cases hr
    obtain ⟨l, hc, _, hlv⟩ := colon_step a s b hs
    simp only [JColon3.colon] at hc
    rw [hc] at hr; cases hr
    obtain ⟨n, hn, hnv⟩ := lengthStep_ok a s b l hs hlv hfit
    have hcn := stepCount_nonneg a.val s.val b.val
    have hsorted : JIssorted.issorted (⟨a, s, l⟩ : StepRange JInt64 JInt64) =
        .ok (decide (stepCount a.val s.val b.val ≤ 1 ∨ 0 ≤ s.val)) := by
      simp only [JIssorted.issorted, issorted_AbstractRange, hn, le_iv, jint1_val, step_step,
        zero_iv, bind, Except.bind, pure, Except.pure, hnv]
      by_cases h1 : stepCount a.val s.val b.val ≤ 1 <;> simp [h1]
    have hfirst : JFirstindex.firstindex (⟨a, s, l⟩ : StepRange JInt64 JInt64) = .ok (jint 1) := by
      simp [JFirstindex.firstindex, firstindexStep, firstindex_StepRange_bigints, first_step, last_step,
        bind, Except.bind, pure, Except.pure]; rfl
    have hlast : JLastindex.lastindex (⟨a, s, l⟩ : StepRange JInt64 JInt64) = .ok n := hn
    have hn0 : 0 ≤ n.val := by omega
    by_cases hord : stepCount a.val s.val b.val ≤ 1 ∨ 0 ≤ s.val
    · obtain ⟨-, hp⟩ := stepRangeColon_proven .i64 (jint 1) (jint 1) n
      obtain ⟨p, hp, -, -, -, -, -, hit⟩ := hp (by simp)
      refine ⟨p, ?_, fun fuel hf => ⟨_, hit fuel ?_, ?_, ?_⟩⟩
      · simp only [sortperm_AbstractRange, hsorted, hord, decide_true, hfirst, hlast, bind, Except.bind,
          ite_true]
        exact hp
      · rw [jint1_val, stepCount_one _ hn0, hnv]; omega
      · rw [jint1_val, stepInts_one, hnv]
      · rw [jint1_val, stepInts_one, hnv]
        rcases hord with h1 | h1
        · rw [List.pairwise_map]
          apply List.Pairwise.imp_of_mem _ (intsFromTo_pairwise 1 _)
          intro x y hx hy hxy
          rw [mem_intsFromTo] at hx hy
          omega
        · exact pairwise_affine _ _ _ (intsFromTo_pairwise _ _) (by omega)
    · have hneg : s.val < 0 := by omega
      obtain ⟨-, hp⟩ := stepRangeColon_proven .i64 n (lit .i64 (-1)) (jint 1)
      obtain ⟨p, hp, -, -, -, -, -, hit⟩ := hp (by decide)
      have hm1 : (lit .i64 (-1)).val = -1 := by decide
      refine ⟨p, ?_, fun fuel hf => ⟨_, hit fuel ?_, ?_, ?_⟩⟩
      · simp only [sortperm_AbstractRange, hsorted, hord, decide_false, hfirst, hlast, bind, Except.bind,
          Bool.false_eq_true, ite_false]
        exact hp
      · rw [hm1, jint1_val]
        have := stepInts_length n.val (-1) 1
        rw [stepInts_neg_one _ hn0, List.length_reverse, intsFromTo_length] at this
        omega
      · rw [hm1, jint1_val, stepInts_neg_one _ hn0, hnv]; exact List.reverse_perm _
      · rw [hm1, jint1_val, stepInts_neg_one _ hn0, hnv]
        exact pairwise_affine_neg _ _ _ (intsFromTo_pairwise _ _) hneg

end Sorting

/-! ## Indexing a unit range by an integer step range -/

section UnitStepIndex
variable {t : IntTy}

/-- `checkbounds(A, s)` of a unit range and a step-range index (abstractarray.jl:690, 756). -/
instance {a b : IntTy} : JCheckbounds (UnitRange (JInt t)) (StepRange (JInt a) (JInt b)) :=
  ⟨checkboundsVectorRange⟩

/-- `r[s]` for an integer unit range `r = a:b` and an in-bounds integer step range index
`s = c:u:d` of the same BitInteger type (`getindex(r::AbstractUnitRange, s::StepRange{T}) where
{T<:Integer}`, range.jl:1034; the `getindex` docstring and the manual's indexing rules: `A[I]`
for a vector of indices `I` is the vector of `A[i]` for `i` in `I`): it returns the range whose
elements are `r[i] = a + i - 1` for the indices `i = c, c+u, ...` of `s`, in order, including an
empty `s`. -/
def GetindexUnitStep : Prop :=
  ∀ (t : IntTy) (a b c u d : JInt t) (r : UnitRange (JInt t)) (s : StepRange (JInt t) (JInt t))
    (fuel : Nat),
    JColon2.colon a b = .ok r → JColon3.colon c u d = .ok s →
    (∀ i ∈ stepInts c.val u.val d.val, 1 ≤ i ∧ i ≤ cnt a.val b.val) →
    stepCount c.val u.val d.val ≤ fuel →
    ∃ res, getindex_AbstractUnitRange_StepRange r s = .ok res ∧
      (match res with
       | .inl _ => (Except.error (Exc.errorException "Bool index") : JlX (List Int))
       | .inr v => iterVals v fuel) = .ok ((stepInts c.val u.val d.val).map fun i => a.val + i - 1)

theorem getindexUnitStep_refuted : ¬ GetindexUnitStep := by
  intro h
  obtain ⟨res, hres, -⟩ := h .i8 (lit .i8 (-128)) (lit .i8 127) (lit .i8 1) (lit .i8 1) (lit .i8 0)
    ⟨lit .i8 (-128), lit .i8 127⟩ ⟨lit .i8 1, lit .i8 1, lit .i8 0⟩ 1 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hv : getindex_AbstractUnitRange_StepRange (⟨lit .i8 (-128), lit .i8 127⟩ : UnitRange (JInt .i8))
      (⟨lit .i8 1, lit .i8 1, lit .i8 0⟩ : StepRange (JInt .i8) (JInt .i8)) =
      .error (.jl (.overflowError "cannot represent an empty range starting at -128")) := by
    decide +kernel
  rw [hv] at hres; cases hres

end UnitStepIndex

/-! ## `range(; stop, step, length)` -/

section StepStopLength

/-- `range(; stop, step, length=n)` with BitInteger `stop` and `step` (`range_step_stop_length`,
range.jl:199; the `range` docstring: "Construct a specialized array with evenly spaced elements
and optimized storage ... from the arguments", with `length` the number of elements) returns, for
a nonzero step and `n >= 0`, a range of `n` elements when it returns. -/
def RangeStepStopLength : Prop :=
  ∀ (t : IntTy) (st b : JInt t) (n : JInt64) res, 0 ≤ n.val → st.val ≠ 0 →
    range_step_stop_length st b n = .ok res →
    (match res with
     | .inl u => (lengthStepMixed u).map Subtype.val
     | .inr g => pure g.len.val) = .ok n.val

theorem rangeStepStopLength_refuted : ¬ RangeStepStopLength := by
  intro h
  have := h .i64 (lit .i64 2) (lit .i64 (-9223372036854775807)) (lit .i64 3)
    (.inl ⟨lit .i64 9223372036854775805, lit .i64 2, lit .i64 9223372036854775804⟩)
    (by decide) (by decide) (by decide +kernel)
  revert this; decide +kernel

end StepStopLength

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## `StepRangeLen` and `LinRange` built from an integer step range -/

section RangeFromRange

theorem srl_new_ok {u l : IntTy} (a s : JInt u) (n : JInt l) (o : JInt64)
    (q : StepRangeLen (JInt u) (JInt u) (JInt u) JInt64)
    (h : (StepRangeLen_TRSL_new (JInt u) a s n o : JlX (StepRangeLen (JInt u) (JInt u) (JInt u) JInt64)) =
      .ok q) :
    q.ref = a ∧ q.step = s ∧ q.len.val = n.val ∧ q.offset = o ∧ 0 ≤ n.val ∧ 1 ≤ o.val ∧
      o.val ≤ max 1 n.val := by
  revert h
  unfold StepRangeLen_TRSL_new
  simp only [JType.isInteger, JIsinteger.isinteger, JuliaLean.base.number.isintegerInteger,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, convert_iv, le_iv,
    zero_iv, oneunit_iv, max_same, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, o.property, and_self, dite_true]
  by_cases hc : IntTy.i64.min ≤ n.val ∧ n.val ≤ IntTy.i64.max
  · rw [dif_pos hc]
    simp only []
    have hm : (if n.val < 1 then (JOneunit.oneunit : JInt64) else (⟨n.val, hc⟩ : JInt64)).val =
        max 1 n.val := by
      by_cases h1 : n.val < 1 <;> simp [h1, oneunit_iv] <;> omega
    simp only [hm]
    by_cases h0 : 0 ≤ n.val
    · by_cases h1 : 1 ≤ o.val ∧ o.val ≤ max 1 n.val
      · intro h
        simp [h0, h1] at h
        subst h
        exact ⟨rfl, rfl, rfl, rfl, h0, h1⟩
      · intro h; simp [h0, h1] at h
    · intro h; simp [h0] at h
  · rw [dif_neg hc]; simp

/-- `StepRangeLen{T,R,S,L}(r::AbstractRange)` (range.jl:1392) and `StepRangeLen{T}(r::AbstractRange)`
(range.jl:1394) convert a range (the `convert` docstring: "Convert `x` to a value of type `T`";
an array conversion keeps the elements). For an integer step range `a:s:b` of any BitInteger
type with a representable length `n`, converted to `StepRangeLen{U,U,U,Int}` for any BitInteger
`U`, or to `StepRangeLen{Int}` from an `Int` range: whenever the conversion returns, the result has
length `n`, and every element `a + (i-1)*s` representable in `U` is the result's element `i`. -/
def SRLFromRange : Prop :=
  (∀ (t u : IntTy) (a s b : JInt t) (r : StepRange (JInt t) (JInt t)),
    JColon3.colon a s b = .ok r → stepCount a.val s.val b.val ≤ (lenTy t).max →
    ∀ q : StepRangeLen (JInt u) (JInt u) (JInt u) JInt64, StepRangeLen_TRSL_AbstractRange r = .ok q →
      (JLength.length q).map Subtype.val = .ok (stepCount a.val s.val b.val) ∧
      ∀ i : JInt64, 1 ≤ i.val → i.val ≤ stepCount a.val s.val b.val → InT u (a.val + (i.val - 1) * s.val) →
        (JGetindex.getindex q i : JlX (JInt u)).map Subtype.val = .ok (a.val + (i.val - 1) * s.val)) ∧
  (∀ (a s b : JInt64) (r : StepRange JInt64 JInt64), JColon3.colon a s b = .ok r →
    stepCount a.val s.val b.val ≤ IntTy.i64.max →
    ∃ q : StepRangeLen JInt64 JInt64 JInt64 JInt64, StepRangeLen_T_AbstractRange (T := JInt64) r = .ok q ∧
      (JLength.length q).map Subtype.val = .ok (stepCount a.val s.val b.val) ∧
      ∀ i : JInt64, 1 ≤ i.val → i.val ≤ stepCount a.val s.val b.val →
        (JGetindex.getindex q i : JlX JInt64).map Subtype.val = .ok (a.val + (i.val - 1) * s.val))

theorem sRLFromRange_proven : SRLFromRange := by
  refine ⟨fun t u a s b r hr hfit q hq => ?_, fun a s b r hr hfit => ?_⟩
  · by_cases hs : s.val = 0
    · rw [colon_step_zero a s b hs] at hr; cases hr
    obtain ⟨l, hc, _, hlv⟩ := colon_step a s b hs
    rw [hc] at hr; cases hr
    obtain ⟨n, hn, hnv⟩ := lengthStep_ok a s b l hs hlv hfit
    simp only [StepRangeLen_TRSL_AbstractRange, first_step, step_step, hn, ctor_iv, bind,
      Except.bind] at hq
    cases h1 : (JConvert.convert a : JlX (JInt u)) with
    | error e => rw [h1] at hq; cases hq
    | ok a' =>
      cases h2 : (JConvert.convert s : JlX (JInt u)) with
      | error e => rw [h1, h2] at hq; cases hq
      | ok s' =>
        rw [h1, h2] at hq
        obtain ⟨hqa, hqs, hql, hqo, hn0, ho1, ho2⟩ := srl_new_ok a' s' n (jint 1) q hq
        have ha := convert_val_of_ok _ _ h1
        have hs' := convert_val_of_ok _ _ h2
        refine ⟨by simp [JLength.length, length_StepRangeLen, hql, hnv, pure, Except.pure, Except.map],
          fun i hi0 hi1 hv => ?_⟩
        have := srl_read q (by rw [hql]; exact hn0) (by rw [hqo, hql]; exact ⟨ho1, ho2⟩) i
          ⟨hi0, by rw [hql, hnv]; exact hi1⟩ (by rw [hqa, hqs, hqo, ha, hs', jint1_val]; exact hv)
        rw [hqa, hqs, hqo, ha, hs', jint1_val] at this
        exact this
  · by_cases hs : s.val = 0
    · rw [colon_step_zero a s b hs] at hr; cases hr
    obtain ⟨l, hc, _, hlv⟩ := colon_step a s b hs
    rw [hc] at hr; cases hr
    obtain ⟨n, hn, hnv⟩ := lengthStep_ok a s b l hs hlv hfit
    have hn0 : 0 ≤ n.val := by rw [hnv]; exact stepCount_nonneg _ _ _
    obtain ⟨-, -, hok⟩ := sRLIntConstruct_proven .i64 a s n (jint 1)
    obtain ⟨q, hq, -, -, hlen, -, -, -, -, hget, -⟩ := hok hn0 (by simp) (by simp; omega)
    refine ⟨q, ?_, by simp [hlen, hnv, Except.map], fun i hi0 hi1 => ?_⟩
    · simp only [StepRangeLen_T_AbstractRange, first_step, step_step, hn, ctor_iv, convert_self, bind,
        Except.bind, JStepRangeLen3.stepRangeLen]
      exact hq
    · have hv := stepCount_bound a.val s.val b.val (i.val - 1) (by omega) (by omega)
      have := hget i hi0 (by omega) (by
        have := a.property; have := b.property
        simp only [srlE, jint1_val]
        constructor <;> rcases hv with h | h <;> omega)
      simpa [srlE] using this

/-- `LinRange{T,L}(start, stop, len::Integer)` (range.jl:612): convert the `Int` endpoints to
`Float64`, then the inner constructor. -/
instance [JPrint F64] : JLinRangeTL F64 JInt64 JInt64 JInt64 JInt64 := ⟨LinRange_TL⟩

/-- `LinRange{T,L}(r::AbstractRange)` (range.jl:1403), which calls `LinRange{T,L}(first(r), last(r),
length(r))` (range.jl:612): converting an `Int` step range `a:s:b` with a representable length
`n` to `LinRange{Float64,Int}` (the `convert` docstring; a `LinRange` is determined by its endpoints
and length) gives, whenever it returns, a range of length `n` whose first and last elements are
`Float64(first(r))` and `Float64(last(r))`; it returns for every `n >= 0` other than `1` (for `n == 1` the
`LinRange` constructor requires equal endpoints). Stated for every `Float64` printer used in the
error messages. -/
def LinRangeFromIntRange : Prop :=
  ∀ [JPrint F64] (a s b : JInt64) (r : StepRange JInt64 JInt64) (n l : JInt64),
    JColon3.colon a s b = .ok r → JLength.length r = .ok n → JLast.last r = .ok l →
    (∀ w : LinRange F64 JInt64, LinRange_TL_AbstractRange (T := F64) (L := JInt64) r = .ok w →
      JLength.length w = .ok n ∧ JFirst.first w = JConvert.convert a ∧ JLast.last w = JConvert.convert l) ∧
    (0 ≤ n.val → n.val ≠ 1 →
      ∃ w : LinRange F64 JInt64, LinRange_TL_AbstractRange (T := F64) (L := JInt64) r = .ok w)

theorem linRangeFromIntRange_proven : LinRangeFromIntRange := by
  intro _ a s b r n l hr hn hl
  by_cases hs : s.val = 0
  · rw [colon_step_zero a s b hs] at hr; cases hr
  obtain ⟨l', hc, _, hlv⟩ := colon_step a s b hs
  rw [hc] at hr; cases hr
  rw [last_step] at hl; cases hl
  have hca : (JConvert.convert a : JlX F64) = .ok (JuliaLean.base.float.float_BitSigned64 .f64 a) := rfl
  have hcl : (JConvert.convert l' : JlX F64) = .ok (JuliaLean.base.float.float_BitSigned64 .f64 l') := rfl
  simp only [LinRange_TL_AbstractRange, first_step, last_step, hn, bind, Except.bind,
    JLinRangeTL.linRangeTL, LinRange_TL, convert_self, hca, hcl]
  refine ⟨fun w hw => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨hs', hl', hn', -⟩ := linRange_ctor_fields _ _ _ w hw
    refine ⟨?_, ?_, ?_⟩
    · simp [JLength.length, length_LinRange, hn', pure, Except.pure]
    · simp [JFirst.first, first_LinRange, hs', pure, Except.pure]
    · simp [JLast.last, last_LinRange, hl', pure, Except.pure]
  · obtain ⟨w, hw, -⟩ := linRangeT_ok (JuliaLean.base.float.float_BitSigned64 .f64 a)
      (JuliaLean.base.float.float_BitSigned64 .f64 l') n h0 h1
    exact ⟨w, hw⟩

end RangeFromRange

/-! ## `intersect(i::Integer, r::AbstractUnitRange{<:Integer})` -/

section IntersectInt
variable {t : IntTy}

/-- `oneunit(Bool) = true` (`bool.jl`: `one(::Type{Bool}) = true`). -/
instance : JOneunit Bool := ⟨true⟩
/-- `convert(T, x::Bool)` for a BitInteger `T` (`boot.jl`, `bool.jl`): `0` or `1`. -/
instance {w : IntTy} : JConvert (JInt w) Bool := ⟨fun b => pure (JuliaLean.base.int.ofBool w b)⟩
/-- `promote_type(Int, Bool) = Int` (`bool.jl`). -/
instance : JPromoteType JInt64 Bool JInt64 := ⟨⟩
/-- `StepRangeLen{T,R,S,L}(ref, step, len, offset)` (range.jl:533) for a `Bool` length. -/
instance {q a s w o : IntTy} :
    JStepRangeLenTRSL (JInt q) (JInt a) (JInt s) (JInt w) (JInt a) (JInt s) Bool (JInt o) :=
  ⟨StepRangeLen_TRSL_new (JInt q)⟩
/-- `StepRangeLen{T,R,S}(ref, step, len, offset)` (range.jl:546) for a `Bool` length. -/
instance {q a s o : IntTy} : JStepRangeLenTRS (JInt q) (JInt a) (JInt s) (JInt a) (JInt s) Bool (JInt o)
    (StepRangeLen (JInt q) (JInt a) (JInt s) JInt64) := ⟨StepRangeLen_TRS⟩
/-- `_range(start::Any, ::Nothing, ::Nothing, len::Integer)` (range.jl:184) for a `Bool` length. -/
instance {D Q U ρ : Type} [HSub (JInt t) (JInt t) D] [JConvert D JInt64]
    [JRangeWrappingAdd (JInt t) JInt64 Q] [JType Q] [JConvert Q (JInt t)] [JUnitRange2 Q Q U]
    [JStepRangeLenTRS Q (JInt t) D (JInt t) D Bool JInt64 ρ] :
    JRangeImpl (JInt t) Nothing Nothing Bool (U ⊕ ρ) := ⟨_range_A_N_N_A⟩
/-- `in(x::Integer, r::AbstractUnitRange{<:Integer})`, range.jl:1489. -/
instance {s : IntTy} : JIn (JInt s) (UnitRange (JInt t)) := ⟨in_Integer_AbstractUnitRange⟩

/-- `intersect(i::Integer, r::AbstractUnitRange{<:Integer})` (range.jl:1211; the `intersect`
docstring: "the set containing those elements which appear in all of the arguments") for an `Int`
and an `Int` unit range `a:b`: it returns a unit range whose elements are `[i]` when `i` lies in
`a:b` and none otherwise. -/
def IntersectIntUnit : Prop :=
  ∀ (i a b : JInt64) (r : UnitRange JInt64), JColon2.colon a b = .ok r →
    ∃ u : UnitRange JInt64, intersect_Integer_AbstractUnitRange i r = .ok (.inl u) ∧
      ∀ fuel : Nat, 1 < fuel →
        iterVals u fuel = .ok (if i.val ∈ intsFromTo a.val b.val then [i.val] else [])

theorem intersectIntUnit_proven : IntersectIntUnit := by
  intro i a b r hr
  rw [colon_unit] at hr; cases hr
  simp only [intersect_Integer_AbstractUnitRange, first_unit, JIn.isIn, in_unit, max_same, bind,
    Except.bind, JRangeStartKw.range, range_start_kw, JRangeImpl.rangeImpl, _range_A_N_N_A]
  have key : ∀ (m : JInt64) (c : Bool), (c = false → IntTy.i64.min < m.val) →
      ∃ u : UnitRange JInt64, range_start_length m c = .ok (.inl u) ∧
        ∀ fuel : Nat, 1 < fuel → iterVals u fuel = .ok (if c then [m.val] else []) := by
    intro m c hc2
    have hmp := m.property
    have hd : ((c - (JOneunit.oneunit : Bool) : JInt64)).val = if c then 0 else -1 := by
      cases c <;> decide
    have hw : (JRangeWrappingAdd.rangeWrappingAdd m (c - (JOneunit.oneunit : Bool)) :
        JInt (pTy .i64 .i64)).val = m.val + (if c then 0 else -1) := by
      show (castJ (pTy_eq .i64 .i64).symm (JuliaLean.base.int.binop JuliaLean.base.int.addWrap m
        (c - (JOneunit.oneunit : Bool)))).val = _
      rw [castJ_val, binop_val JuliaLean.base.int.addWrap (fun x y => IntVal.add_int_val x y), hd,
        promote_self .i64]
      apply wrap_in
      · cases c <;> simp at hc2 ⊢ <;> omega
      · cases c <;> simp <;> omega
    generalize hst : (JRangeWrappingAdd.rangeWrappingAdd m (c - (JOneunit.oneunit : Bool)) :
      JInt (pTy .i64 .i64)) = st at hw
    obtain ⟨u, -, -, hT, -, -, -, -, hit, -⟩ := unitRangeColon_proven .i64 m st
    refine ⟨u, ?_, fun fuel hf => ?_⟩
    · unfold range_start_length
      simp only [bind, Except.bind, oftype, convert_self, hst, pure, Except.pure]
      rw [if_pos (show JType.isSigned (JInt IntTy.i64) = true from rfl)]
      have hU : (JUnitRange2.unitRange m st : JlX (UnitRange (JInt IntTy.i64))) = .ok u := hT
      rw [hU]
    · rw [hit fuel (by rw [hw]; cases c <;> simp <;> omega), hw]
      cases c
      · simp only [Bool.false_eq_true, ite_false]; rw [intsFromTo_empty (by omega)]
      · simp only [ite_true, Int.add_zero]; rw [intsFromTo_cons (Int.le_refl _), intsFromTo_empty (by omega)]
  obtain ⟨u, hu, hit⟩ := key (if a.val < i.val then i else a) (decide (i.val ∈ intsFromTo a.val b.val)) (by
    intro hc
    simp only [decide_eq_false_iff_not, mem_intsFromTo] at hc
    have := a.property; have := b.property; have := i.property
    split <;> simp only [i64min] at * <;> omega)
  refine ⟨u, hu, fun fuel hf => ?_⟩
  rw [hit fuel hf]
  by_cases hin : i.val ∈ intsFromTo a.val b.val
  · rw [mem_intsFromTo] at hin
    simp only [decide_eq_true_eq, mem_intsFromTo, hin, and_self, ite_true]
    split <;> simp_all <;> omega
  · simp [hin]

end IntersectInt

section CharRanges
open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)
open JuliaLean.base.char (JChar CharError CharResult shl32 ushr32 charIntegerOps charBitOps
  codepoint_Char remUInt32ToIntTy constructor_Integer_AbstractChar char_UInt32
  add_AbstractChar_Integer sub_AbstractChar_Integer sub_AbstractChar_AbstractChar eq_Char isless_Char)

/-! ## Dispatch world: `Char` ranges

A `Char` is its 32-bit storage pattern `JChar` (`JuliaLean.base.char`). Range methods compute
`Int(x) - Int(y)` of two `Char`s (char.jl:275) through `-`, which the model treats as total, so
this world's `Char` type `VChar` holds the `Char`s whose `Int(c)` succeeds, together with that
codepoint. `Char + Int` and `Char - Int` (char.jl:298-299) can throw; the world gives them the
result type `JlX VChar`, and `convert(Char, ·)` (which the range methods apply to every `+`/`-`
result) raises the exception. -/

/-- `Int(c)` of a `Char` (char.jl:57): `codepoint(c) % Int`. -/
def charInt (c : JChar) : CharResult JInt64 :=
  constructor_Integer_AbstractChar .i64 (codepoint_Char charBitOps) remUInt32ToIntTy c

/-- An exception of a `Char` method as a range-model exception; `Exc` has no constructor for
`InvalidCharError` and `CodePointError`, which are named instead. -/
def charExc : CharError → Exc
  | .foreign e => .jl e
  | .boundsError => .jl .boundsError
  | .invalidChar _ => .errorException "InvalidCharError"
  | .codePointError _ => .errorException "CodePointError"

/-- A `Char` computation as a range-model computation. -/
def liftChar {α : Type} : CharResult α → JlX α
  | .ok v => .ok v
  | .error e => .error (charExc e)

/-- A Julia `Char` whose `Int(c)` (char.jl:57) succeeds, with that value `cp`. -/
structure VChar where
  bits : JChar
  cp : JInt64
  hcp : charInt bits = .ok cp

theorem VChar.ext' {x y : VChar} (h : x.bits = y.bits) : x = y := by
  cases x with
  | mk b c hc =>
    cases y with
    | mk b' c' hc' =>
      simp only at h; subst h
      rw [hc] at hc'; cases hc'; rfl

instance : DecidableEq VChar := fun x y =>
  if h : x.bits = y.bits then isTrue (VChar.ext' h) else isFalse (fun e => h (e ▸ rfl))

/-- The `Char` `c`, when `Int(c)` succeeds; otherwise the exception `Int(c)` throws. -/
def toVChar (c : JChar) : JlX VChar :=
  match h : charInt c with
  | .ok v => .ok ⟨c, v, h⟩
  | .error e => .error (charExc e)

section CharWorld

/-- `Char` is not `Bool`, `Signed`, `Integer` or `AbstractFloat`. -/
instance instJTypeVChar : JType VChar := ⟨false, false, false, false, by intro h; cases h⟩
/-- `x == y` of `Char`s (char.jl:263). -/
instance instJEqVChar : JEq VChar VChar := ⟨fun x y => eq_Char x.bits y.bits⟩
/-- `x < y` of `Char`s: `isless(x, y)` (operators.jl:417, char.jl:264). -/
instance instJLtVChar : JLt VChar VChar := ⟨fun x y => isless_Char x.bits y.bits⟩
/-- `x <= y` of `Char`s: `(x < y) | (x == y)` (operators.jl:467). -/
instance instJLeVChar : JLe VChar VChar := ⟨fun x y => isless_Char x.bits y.bits || eq_Char x.bits y.bits⟩
/-- `min(x, y)` of `Char`s: `ifelse(isless(y, x), y, x)` (operators.jl:573). -/
instance instJMinVChar : JMin VChar VChar VChar := ⟨fun x y => pure (if isless_Char y.bits x.bits then y else x)⟩
/-- `max(x, y)` of `Char`s: `ifelse(isless(y, x), x, y)` (operators.jl:555). -/
instance instJMaxVChar : JMax VChar VChar VChar := ⟨fun x y => pure (if isless_Char y.bits x.bits then x else y)⟩
/-- `Int(x)` of a `Char` (char.jl:57). -/
instance instJCtorVChar : JCtor JInt64 VChar := ⟨fun x => liftChar (charInt x.bits)⟩
/-- `x - y` of `Char`s: `Int(x) - Int(y)` (char.jl:275), whose `Int` calls succeed in this world
(`charSub_spec`). -/
instance instHSubVChar : HSub VChar VChar JInt64 := ⟨fun x y => x.cp - y.cp⟩
/-- `x + y` of a `Char` and an `Int`: `x +% y` (char.jl:299, 286). -/
instance instHAddVCharInt : HAdd VChar JInt64 (JlX VChar) :=
  ⟨fun x y => liftChar (add_AbstractChar_Integer charIntegerOps x.bits y) >>= toVChar⟩
/-- `x - y` of a `Char` and an `Int`: `x -% y` (char.jl:298, 276). -/
instance instHSubVCharInt : HSub VChar JInt64 (JlX VChar) :=
  ⟨fun x y => liftChar (sub_AbstractChar_Integer charIntegerOps x.bits y) >>= toVChar⟩
/-- `convert(Char, c)` of a `Char` (`convert(::Type{T}, x::T) where {T} = x`, essentials.jl):
applied to the result of `c ± n`, it raises the exception `±` threw. -/
instance instJConvertVCharX : JConvert VChar (JlX VChar) := ⟨id⟩
instance instJConvertVChar : JConvert VChar VChar := ⟨pure⟩
/-- `convert(T′, c)` in `_colon(start::T, step, stop::T)` (range.jl:73), where `T′` is the type of
`start + zero(step)`, a `Char`: the identity. -/
instance instJConvertXVChar : JConvert (JlX VChar) VChar := ⟨fun c => pure (pure c)⟩
/-- `isinteger(start + step)` in `steprange_last` (range.jl:357) is evaluated only when
`start isa Integer`, never for a `Char`. -/
instance instJIsintegerXVChar : JIsinteger (JlX VChar) := ⟨fun _ => false⟩
/-- `checked_sub(x::Char, y::Char)`: no such method (checked.jl defines `checked_sub` for
integers), a `MethodError`. -/
instance instJCheckedSubVChar : JCheckedSub VChar VChar JInt64 :=
  ⟨fun _ _ => throw (.jl (.methodError "checked_sub"))⟩

/-- `_range_wrapping_sub(x, y) = x - y`, range.jl:37: `Char` is not a `_RangeWrappingInteger`. -/
instance : JRangeWrappingSub VChar VChar JInt64 := ⟨_range_wrapping_sub_Any⟩
/-- `steprange_last_empty(start, step, stop)`, range.jl:401. -/
instance : JSteprangeLastEmpty VChar JInt64 VChar := ⟨steprange_last_empty_Any⟩
/-- `steprange_last(start, step, stop)`, range.jl:353. -/
instance : JSteprangeLast VChar JInt64 VChar := ⟨steprange_last⟩
/-- `StepRange{T,S}(start, step, stop)`, range.jl:344. -/
instance : JStepRangeTS VChar JInt64 VChar JInt64 VChar := ⟨StepRange_TS_new VChar JInt64⟩
/-- `StepRange(start::T, step::S, stop::T)` (range.jl:404) on the converted endpoints of `_colon`
(range.jl:75). -/
instance : JStepRange3 (JlX VChar) JInt64 (JlX VChar) (StepRange VChar JInt64) :=
  ⟨fun a s b => do StepRange_T_S_T (← a) s (← b)⟩
/-- `(:)(start::T, step, stop::T) where {T}`, range.jl:64. -/
instance : JColon3 VChar JInt64 VChar (StepRange VChar JInt64) := ⟨colon_T_step_T⟩
/-- `(:)(start::T, stop::T) where {T}`, range.jl:7. -/
instance : JColon2 VChar VChar (StepRange VChar JInt64) := ⟨colon_T_T⟩

instance : JEltype (StepRange VChar JInt64) VChar := ⟨⟩
instance : JFieldStart (StepRange VChar JInt64) VChar := ⟨StepRange.start⟩
instance : JFieldStop (StepRange VChar JInt64) VChar := ⟨StepRange.stop⟩
/-- `first(r::OrdinalRange{T})`, range.jl:867. -/
instance : JFirst (StepRange VChar JInt64) VChar := ⟨first_OrdinalRange⟩
/-- `last(r::OrdinalRange{T})`, range.jl:877. -/
instance : JLast (StepRange VChar JInt64) VChar := ⟨last_OrdinalRange⟩
/-- `step(r::StepRange)`, range.jl:735. -/
instance : JStep (StepRange VChar JInt64) JInt64 := ⟨fun r => pure (step_StepRange r)⟩
/-- `isempty(r::StepRange)`, range.jl:708. -/
instance : JIsempty (StepRange VChar JInt64) := ⟨fun r => pure (isempty_StepRange r)⟩
/-- `iterate(r::OrdinalRange)`, range.jl:935. -/
instance : JIterate1 (StepRange VChar JInt64) VChar VChar := ⟨iterate_OrdinalRange⟩
/-- `iterate(r::OrdinalRange{T}, i)`, range.jl:937. -/
instance : JIterate2 (StepRange VChar JInt64) VChar VChar := ⟨iterate_OrdinalRange_state⟩
/-- `minimum(r::AbstractRange)`, range.jl:883. -/
instance : JMinimum (StepRange VChar JInt64) VChar := ⟨minimum_AbstractRange⟩
/-- `maximum(r::AbstractRange)`, range.jl:884. -/
instance : JMaximum (StepRange VChar JInt64) VChar := ⟨maximum_AbstractRange⟩

end CharWorld

/-! ### ASCII `Char`s -/

/-- The storage pattern of the ASCII `Char` with codepoint `p`. -/
def asc (p : Nat) : JChar := shl32 (UInt32.ofNat p) 24

theorem asc_toNat {p : Nat} (hp : p < 128) : (asc p).toNat = p * 2 ^ 24 := by
  simp only [asc, shl32, show (24 : Nat) < 32 by decide, ite_true, UInt32.toNat_shiftLeft,
    UInt32.toNat_ofNat']
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show p < 2 ^ 32 by omega)]
  rw [show (24 % 2 ^ 32 % 32 : Nat) = 24 by decide]
  exact Nat.mod_eq_of_lt (by omega)

theorem asc_inj {p q : Nat} (hp : p < 128) (hq : q < 128) : asc p = asc q ↔ p = q := by
  constructor
  · intro h
    have := congrArg UInt32.toNat h
    rw [asc_toNat hp, asc_toNat hq] at this; omega
  · intro h; rw [h]

theorem asc_lt {p q : Nat} (hp : p < 128) (hq : q < 128) : asc p < asc q ↔ p < q := by
  rw [UInt32.lt_iff_toNat_lt, asc_toNat hp, asc_toNat hq]; omega

theorem ushr_asc {p : Nat} (hp : p < 128) : ushr32 (asc p) 24 = UInt32.ofNat p := by
  apply UInt32.toNat_inj.mp
  simp only [ushr32, show (24 : Nat) < 32 by decide, ite_true, UInt32.toNat_shiftRight,
    asc_toNat hp, UInt32.toNat_ofNat']
  rw [show (24 % 2 ^ 32 % 32 : Nat) = 24 by decide, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show p < 2 ^ 32 by omega)]
  simp

/-- `char_UInt32` (`Char(u::UInt32)`, char.jl:211) of an ASCII codepoint. -/
theorem char_asc {p : Nat} (hp : p < 128) : char_UInt32 (UInt32.ofNat p) = .ok (asc p) := by
  have h : UInt32.ofNat p < 0x80 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; simp; omega
  simp [char_UInt32, h, asc, pure, Except.pure]

theorem signedByte_ascii : ∀ p : Fin 128,
    (Int32.ofInt (Int8.ofBitVec (UInt8.ofNat (UInt32.ofNat p.val).toNat).toBitVec).toInt).toInt =
      (p.val : Int) := by
  decide

theorem charInt_asc {p : Nat} (hp : p < 128) : charInt (asc p) = .ok (lit .i64 p) := by
  have hlt : asc p < 0x80000000 := by
    rw [UInt32.lt_iff_toNat_lt, asc_toNat hp]; simp; omega
  simp only [charInt, constructor_Integer_AbstractChar, codepoint_Char,
    JuliaLean.base.char.uint32_Char, hlt, ite_true, bind, Except.bind, pure, Except.pure,
    remUInt32ToIntTy, ushr_asc hp]
  refine congrArg Except.ok (Subtype.ext ?_)
  rw [IntVal.remT_val]
  show wrapInt .i64 (wrapInt .u32 ((UInt32.ofNat p).toNat : Int)) = wrapInt .i64 p
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
    wrap_in .u32 (by simp [IntTy.min, IntTy.signed]) (by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega)]

theorem i64_small {z : Int} (h0 : 0 ≤ z) (h1 : z < 128) : wrapInt .i64 z = z :=
  wrap_in .i64 (by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega)
    (by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega)

/-- Small `Int` values need no wrapping. -/
theorem i64_small' {z : Int} (h0 : -2 ^ 62 ≤ z) (h1 : z < 2 ^ 62) : wrapInt .i64 z = z :=
  wrap_in .i64 (by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega)
    (by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega)

theorem wrap_small_eq {z w : Int} (h : z = w) (h0 : -2 ^ 62 ≤ w) (h1 : w < 2 ^ 62) :
    wrapInt .i64 z = w := by
  subst h; exact i64_small' h0 h1

/-- The ASCII `Char` with codepoint `p`, in this world. -/
def vasc (p : Nat) (hp : p < 128) : VChar := ⟨asc p, lit .i64 p, charInt_asc hp⟩

theorem cp_asc {c : VChar} {p : Nat} (hp : p < 128) (h : c.bits = asc p) : c.cp.val = p := by
  have := c.hcp
  rw [h, charInt_asc hp] at this
  injection this with h'
  rw [← h']
  exact i64_small (by omega) (by omega)

theorem toVChar_asc {p : Nat} (hp : p < 128) : toVChar (asc p) = .ok (vasc p hp) := by
  unfold toVChar
  split
  · next v h => exact congrArg Except.ok (VChar.ext' rfl)
  · next e h => rw [charInt_asc hp] at h; cases h

theorem charSub_spec (x y : VChar) :
    sub_AbstractChar_AbstractChar charInt (· - ·) x.bits y.bits = .ok (x - y) := by
  simp [sub_AbstractChar_AbstractChar, x.hcp, y.hcp, bind, Except.bind, pure, Except.pure]; rfl

theorem u32_conv {z : Int} (h0 : 0 ≤ z) (h1 : z < 128) :
    JuliaLean.base.char.exactUInt32 z = .ok (UInt32.ofNat z.toNat) := by
  have hm : IntTy.u32.min ≤ z ∧ z ≤ IntTy.u32.max := by
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  simp only [JuliaLean.base.char.exactUInt32, JInt.convert, hm, and_self, dite_true]

theorem add_asc {p : Nat} (hp : p < 128) (n : JInt64) (h0 : 0 ≤ (p : Int) + n.val)
    (h1 : (p : Int) + n.val < 128) :
    add_AbstractChar_Integer charIntegerOps (asc p) n = .ok (asc ((p : Int) + n.val).toNat) := by
  have hb : (Int32.ofInt (Int8.ofBitVec (UInt8.ofNat (UInt32.ofNat p).toNat).toBitVec).toInt).toInt =
      (p : Int) := signedByte_ascii ⟨p, hp⟩
  have hn := n.property
  simp only [add_AbstractChar_Integer, JuliaLean.base.char.addWrap_AbstractChar_Integer,
    charIntegerOps, JuliaLean.base.char.rawCharIdentity, ushr_asc hp, ite_true, hb,
    show (p : Int) ≥ 0 by omega]
  generalize hzd : JuliaLean.base.char.addPromotedInt64 (JuliaLean.base.char.int64PromoteInt32
      (Int32.ofInt (Int8.ofBitVec (UInt8.ofNat (UInt32.ofNat p).toNat).toBitVec).toInt))
      (JuliaLean.base.char.int64Identity n) = z
  have hz : z.val = (p : Int) + n.val := by
    rw [← hzd]
    simp only [JuliaLean.base.char.addPromotedInt64, JuliaLean.base.char.int64PromoteInt32,
      JuliaLean.base.char.int64Identity, hb]
    show wrapInt .i64 (wrapInt .i64 (p : Int) + n.val) = _
    rw [i64_small (z := (p : Int)) (by omega) (by omega)]
    exact wrap_in .i64 (by simp [IntTy.min, IntTy.signed, IntTy.bits] at hn ⊢; omega)
      (by simp [IntTy.max, IntTy.signed, IntTy.bits] at hn ⊢; omega)
  have hc1 : (JuliaLean.base.char.nonnegativeInt64 z && JuliaLean.base.char.belowAsciiInt64 z) = true := by
    simp only [JuliaLean.base.char.nonnegativeInt64, JuliaLean.base.char.belowAsciiInt64, hz,
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hc3 : JuliaLean.base.char.int64ToUInt32 z = .ok (UInt32.ofNat ((p : Int) + n.val).toNat) := by
    simp only [JuliaLean.base.char.int64ToUInt32, hz]; exact u32_conv h0 h1
  simp only [hc1, hc3, ite_true, bind, Except.bind, pure, Except.pure, asc]

theorem vadd_asc {c : VChar} {p : Nat} (hp : p < 128) (hc : c.bits = asc p) (n : JInt64)
    (h0 : 0 ≤ (p : Int) + n.val) (h1 : (p : Int) + n.val < 128) :
    (c + n : JlX VChar) = .ok (vasc ((p : Int) + n.val).toNat (by omega)) := by
  show liftChar (add_AbstractChar_Integer charIntegerOps c.bits n) >>= toVChar = _
  rw [hc, add_asc hp n h0 h1]
  simp only [liftChar, bind, Except.bind]
  exact toVChar_asc _

theorem sub_asc {p : Nat} (hp : p < 128) (n : JInt64) (h0 : 0 ≤ (p : Int) - n.val)
    (h1 : (p : Int) - n.val < 128) :
    sub_AbstractChar_Integer charIntegerOps (asc p) n = .ok (asc ((p : Int) - n.val).toNat) := by
  have hb : (Int32.ofInt (Int8.ofBitVec (UInt8.ofNat (UInt32.ofNat p).toNat).toBitVec).toInt).toInt =
      (p : Int) := signedByte_ascii ⟨p, hp⟩
  have hn := n.property
  simp only [sub_AbstractChar_Integer, JuliaLean.base.char.subWrap_AbstractChar_Integer,
    charIntegerOps, JuliaLean.base.char.rawCharIdentity, ushr_asc hp, ite_true, hb,
    show (p : Int) ≥ 0 by omega]
  generalize hzd : JuliaLean.base.char.subPromotedInt64 (JuliaLean.base.char.int64PromoteInt32
      (Int32.ofInt (Int8.ofBitVec (UInt8.ofNat (UInt32.ofNat p).toNat).toBitVec).toInt))
      (JuliaLean.base.char.int64Identity n) = z
  have hz : z.val = (p : Int) - n.val := by
    rw [← hzd]
    simp only [JuliaLean.base.char.subPromotedInt64, JuliaLean.base.char.int64PromoteInt32,
      JuliaLean.base.char.int64Identity, hb]
    show wrapInt .i64 (wrapInt .i64 (p : Int) - n.val) = _
    rw [i64_small (z := (p : Int)) (by omega) (by omega)]
    exact wrap_in .i64 (by simp [IntTy.min, IntTy.signed, IntTy.bits] at hn ⊢; omega)
      (by simp [IntTy.max, IntTy.signed, IntTy.bits] at hn ⊢; omega)
  have hc1 : (JuliaLean.base.char.nonnegativeInt64 z && JuliaLean.base.char.belowAsciiInt64 z) = true := by
    simp only [JuliaLean.base.char.nonnegativeInt64, JuliaLean.base.char.belowAsciiInt64, hz,
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hc3 : JuliaLean.base.char.int64ToUInt32 z = .ok (UInt32.ofNat ((p : Int) - n.val).toNat) := by
    simp only [JuliaLean.base.char.int64ToUInt32, hz]; exact u32_conv h0 h1
  simp only [hc1, hc3, ite_true, bind, Except.bind, pure, Except.pure, asc]

theorem vsub_asc {c : VChar} {p : Nat} (hp : p < 128) (hc : c.bits = asc p) (n : JInt64)
    (h0 : 0 ≤ (p : Int) - n.val) (h1 : (p : Int) - n.val < 128) :
    (c - n : JlX VChar) = .ok (vasc ((p : Int) - n.val).toNat (by omega)) := by
  show liftChar (sub_AbstractChar_Integer charIntegerOps c.bits n) >>= toVChar = _
  rw [hc, sub_asc hp n h0 h1]
  simp only [liftChar, bind, Except.bind]
  exact toVChar_asc _

theorem eqc_asc {p q : Nat} (hp : p < 128) (hq : q < 128) :
    eq_Char (asc p) (asc q) = decide (p = q) := by
  by_cases h : p = q
  · subst h; simp [eq_Char]
  · have : asc p ≠ asc q := fun e => h ((asc_inj hp hq).mp e)
    simp [eq_Char, h, this]

theorem ltc_asc {p q : Nat} (hp : p < 128) (hq : q < 128) :
    isless_Char (asc p) (asc q) = decide (p < q) := by
  simp [isless_Char, asc_lt hp hq]

@[simp] theorem jeq_vchar (x y : VChar) : JEq.eq x y = eq_Char x.bits y.bits := rfl
@[simp] theorem jlt_vchar (x y : VChar) : JLt.lt x y = isless_Char x.bits y.bits := rfl
@[simp] theorem jle_vchar (x y : VChar) :
    JLe.le x y = (isless_Char x.bits y.bits || eq_Char x.bits y.bits) := rfl
@[simp] theorem rws_vchar (x y : VChar) :
    (JRangeWrappingSub.rangeWrappingSub x y : JInt64) = x.cp - y.cp := rfl
@[simp] theorem convX_vchar (x : JlX VChar) : (JConvert.convert x : JlX VChar) = x := rfl
@[simp] theorem conv_vchar (x : VChar) : (JConvert.convert x : JlX VChar) = .ok x := rfl

theorem stepCount_mismatch (p s q : Int) (hpq : p ≠ q) (h : (0 < s) ≠ (p < q)) :
    stepCount p s q = 0 := by
  unfold stepCount
  rw [if_neg (by intro h'; apply h; simp [h'.1]; omega), if_neg (by intro h'; apply h; simp [h'.1]; omega)]

theorem stepCount_self (p s : Int) (hs : s ≠ 0) : stepCount p s p = 1 := by
  unfold stepCount
  by_cases h : 0 < s
  · rw [if_pos ⟨h, Int.le_refl p⟩]; simp
  · rw [if_neg (by omega), if_pos ⟨by omega, Int.le_refl p⟩]; simp

/-- `steprange_last(a, s, b)` (range.jl:353) for ASCII `Char`s `a`, `b` and a nonzero `Int` step. -/
theorem char_last {p q : Nat} (hp : p < 128) (hq : q < 128) (a b : VChar)
    (ha : a.bits = asc p) (hb : b.bits = asc q) (s : JInt64) (hs : s.val ≠ 0) :
    ∃ l : VChar, (JSteprangeLast.steprangeLast a s b : JlX VChar) = .ok l ∧
      (stepCount p s.val q = 0 → l = b) ∧
      (stepCount p s.val q ≠ 0 → l.bits = asc (p + (stepCount p s.val q - 1) * s.val).toNat) := by
  have hap := cp_asc hp ha; have hbp := cp_asc hq hb
  have hsp := s.property
  have hcn := stepCount_nonneg p s.val q
  simp only [JSteprangeLast.steprangeLast, steprange_last, JType.isAbstractFloat, JType.isInteger,
    Bool.or_false, Bool.false_and, Bool.false_eq_true, ite_false, eq_iv, zero_iv, hs, decide_false,
    jeq_vchar, jlt_vchar, ha, hb, eqc_asc hq hp, ltc_asc hp hq, lt_iv]
  by_cases hpq : p = q
  · subst hpq
    refine ⟨b, by simp [pure, Except.pure, bind, Except.bind], fun _ => rfl, fun _ => ?_⟩
    rw [hb, stepCount_self _ _ hs]; simp
  have hqp : ¬ q = p := fun h => hpq h.symm
  simp only [hqp, decide_false, Bool.false_eq_true, ite_false]
  by_cases hdir : (0 < s.val) ≠ ((p : Int) < q)
  · have hd : (decide (0 < s.val) != decide (p < q)) = true := by
      by_cases h1 : 0 < s.val <;> by_cases h2 : p < q <;> simp_all <;> omega
    have h0 := stepCount_mismatch p s.val q (by omega) hdir
    refine ⟨b, ?_, fun _ => rfl, fun h => absurd h0 h⟩
    simp [hd, JSteprangeLastEmpty.steprangeLastEmpty, steprange_last_empty_Any, Functor.map,
      Except.map, bind, Except.bind, pure, Except.pure]
  have hd : (decide (0 < s.val) != decide (p < q)) = false := by
    by_cases h1 : 0 < s.val <;> by_cases h2 : p < q <;> simp_all <;> omega
  have hdir' : (0 < s.val ↔ (p : Int) < q) := by simpa using hdir
  have hc0 : stepCount p s.val q ≠ 0 := by
    unfold stepCount
    by_cases h1 : 0 < s.val
    · have h2 := hdir'.mp h1
      rw [if_pos ⟨h1, by omega⟩]
      have := Int.tdiv_nonneg (a := (q : Int) - p) (b := s.val) (by omega) (by omega); omega
    · have h2 : ¬ (p : Int) < q := fun h => h1 (hdir'.mpr h)
      rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
      have := Int.tdiv_nonneg (a := (p : Int) - q) (b := -s.val) (by omega) (by omega); omega
  have hl := lastVal_count p s.val q hs (by omega)
  have hlv : lastVal p s.val q =
      if (p : Int) < q then q - ((q : Int) - p).tmod s.val else q + ((p : Int) - q).tmod (-s.val) := by
    simp only [lastVal, show (p : Int) ≠ q by omega, ite_false]
    rw [if_neg (by simpa using hdir)]
  simp only [hd, Bool.false_eq_true, ite_false, JType.isSigned, Bool.true_and, zero_iv]
  by_cases hlt : p < q
  · have hs0 : 0 < s.val := hdir'.mpr (by omega)
    have hdv : (b.cp - a.cp).val = (q : Int) - p := by
      rw [sub_iv, hap, hbp]; exact wrap_in .i64 (by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega)
        (by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega)
    obtain ⟨r, hr, hrv⟩ := rem_same_ok (b.cp - a.cp) s hs
    have hb' := (IntVal.tmod_between ((q : Int) - p) s.val).1 (by omega)
    rw [hdv] at hrv
    have hsub := vsub_asc hq hb r (by omega) (by omega)
    simp only [hlt, decide_true, ite_true, rws_vchar, hdv, show ¬ ((q : Int) - p < 0) by omega,
      decide_false, Bool.false_eq_true, ite_false, rem_sum_inl, hr, convert_self, bind, Except.bind,
      pure, Except.pure, hsub, convX_vchar]
    refine ⟨_, rfl, fun h => absurd h hc0, fun _ => ?_⟩
    show asc _ = _
    rw [← hl, hlv, if_pos (by omega), hrv]
  · have hs0 : s.val < 0 := by
      have : ¬ 0 < s.val := fun h => hlt (by have := hdir'.mp h; omega)
      omega
    have hgt : q < p := by omega
    have hdv : (a.cp - b.cp).val = (p : Int) - q := by
      rw [sub_iv, hap, hbp]; exact wrap_in .i64 (by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega)
        (by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega)
    have hns : (JNeg.neg s : JInt64).val = wrapInt .i64 (-s.val) := neg_iv s
    obtain ⟨r, hr, hrv⟩ := rem_same_ok (a.cp - b.cp) (JNeg.neg s)
      (by rw [hns]; rcases wrap_neg_cases s hs0 with h | ⟨h, _⟩ <;> omega)
    rw [hdv, hns, tmod_wrap_neg _ s hs0] at hrv
    have hb' := (IntVal.tmod_between ((p : Int) - q) (-s.val)).1 (by omega)
    have hadd := vadd_asc hq hb r (by omega) (by omega)
    simp only [hlt, decide_false, Bool.false_eq_true, ite_false, rws_vchar, hdv,
      show ¬ ((p : Int) - q < 0) by omega, rem_sum_inr, hr, convert_self, bind, Except.bind,
      pure, Except.pure, hadd, convX_vchar]
    refine ⟨_, rfl, fun h => absurd h hc0, fun _ => ?_⟩
    show asc _ = _
    rw [← hl, hlv, if_neg (by omega), hrv]

theorem eqChar_dec (x y : JChar) : eq_Char x y = decide (x = y) := by
  unfold eq_Char; by_cases h : x = y <;> simp [h]

theorem char_last_zero (a b : VChar) (s : JInt64) (hs : s.val = 0) :
    (JSteprangeLast.steprangeLast a s b : JlX VChar) =
      .error (.jl (.argumentError "step cannot be zero")) := by
  simp [JSteprangeLast.steprangeLast, steprange_last, JType.isAbstractFloat, JType.isInteger,
    eq_iv, zero_iv, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem colon_vchar (a b : VChar) (s : JInt64) :
    (JColon3.colon a s b : JlX (StepRange VChar JInt64)) =
      (JSteprangeLast.steprangeLast a s b : JlX VChar).map (fun l => ⟨a, s, l⟩) := by
  simp only [JColon3.colon, colon_T_step_T, _colon_T_step_T, JStepRange3.stepRange, StepRange_T_S_T,
    JStepRangeTS.stepRangeTS, StepRange_TS_new, conv_vchar, convert_self, bind, Except.bind, pure,
    Except.pure]
  show (do let x ← (do let a' ← (Except.ok (Except.ok a) : JlX (JlX VChar)); a') ; _) = _
  cases JSteprangeLast.steprangeLast a s b <;> rfl

theorem colon2_vchar (a b : VChar) :
    (JColon2.colon a b : JlX (StepRange VChar JInt64)) = JColon3.colon a (jint 1) b := by
  simp only [JColon2.colon, colon_T_T, oftype, convert_self, bind, Except.bind]

@[simp] theorem first_vchar (r : StepRange VChar JInt64) : JFirst.first r = .ok r.start := rfl
@[simp] theorem last_vchar (r : StepRange VChar JInt64) : JLast.last r = .ok r.stop := rfl
@[simp] theorem step_vchar (r : StepRange VChar JInt64) : JStep.step r = .ok r.step := rfl
@[simp] theorem isempty_vchar (r : StepRange VChar JInt64) :
    JIsempty.isempty r = .ok (isempty_StepRange r) := rfl

theorem iterate2_vchar_last (r : StepRange VChar JInt64) (i : VChar) (h : i.bits = r.stop.bits) :
    JIterate2.iterate r i = .ok none := by
  simp [JIterate2.iterate, iterate_OrdinalRange_state, jeq_vchar, eqChar_dec, h, bind, Except.bind,
    pure, Except.pure]

theorem iterate2_vchar_step (r : StepRange VChar JInt64) (i j : VChar) (h : i.bits ≠ r.stop.bits)
    (hj : (i + r.step : JlX VChar) = .ok j) : JIterate2.iterate r i = .ok (some (j, j)) := by
  simp [JIterate2.iterate, iterate_OrdinalRange_state, jeq_vchar, eqChar_dec, h, bind, Except.bind,
    pure, Except.pure, hj]

/-- Iterating a `Char` step range whose elements `p + j*s` (`j ≤ q`) are ASCII codepoints, from the
state `p + j*s`, visits the `Char`s with codepoints `p + (j+1)*s, ..., p + q*s`. -/
theorem iterFrom_vchar (r : StepRange VChar JInt64) (p : Int) (q : Nat) (hs : r.step.val ≠ 0)
    (hin : ∀ j : Nat, j ≤ q → 0 ≤ p + j * r.step.val ∧ p + j * r.step.val < 128)
    (hstop : r.stop.bits = asc (p + q * r.step.val).toNat) :
    ∀ (fuel j : Nat) (i : VChar), j ≤ q → q - j < fuel → i.bits = asc (p + j * r.step.val).toNat →
      ∃ ys : List VChar, iterFrom r fuel i = .ok ys ∧
        ys.map VChar.bits = (List.range (q - j)).map fun k =>
          asc (p + ((j + 1 + k : Nat) : Int) * r.step.val).toNat
  | 0, _, _, _, h, _ => by omega
  | fuel + 1, j, i, hj, hf, hi => by
    by_cases heq : j = q
    · subst heq
      refine ⟨[], ?_, by simp⟩
      simp [iterFrom, iterate2_vchar_last r i (by rw [hi, hstop]), bind, Except.bind, pure, Except.pure]
    · have h1 := hin j hj; have h2 := hin q (Nat.le_refl q); have h3 := hin (j + 1) (by omega)
      have hne : i.bits ≠ r.stop.bits := by
        rw [hi, hstop]; intro h
        rw [asc_inj (by omega) (by omega)] at h
        have h' : p + j * r.step.val = p + q * r.step.val := by
          have := congrArg (fun n : Nat => (n : Int)) h
          simp only [Int.toNat_of_nonneg h1.1, Int.toNat_of_nonneg h2.1] at this
          exact this
        have : ((j : Int) - q) * r.step.val = 0 := by rw [Int.sub_mul]; omega
        rcases Int.mul_eq_zero.mp this with h0 | h0 <;> omega
      have hjs : ((p + j * r.step.val).toNat : Int) = p + j * r.step.val := Int.toNat_of_nonneg h1.1
      have h3' : p + ((j + 1 : Nat) : Int) * r.step.val = p + j * r.step.val + r.step.val := by
        push_cast; rw [Int.add_mul, Int.one_mul]; omega
      have hadd := vadd_asc (c := i) (p := (p + j * r.step.val).toNat) (by omega) hi r.step
        (by rw [hjs]; omega) (by rw [hjs]; omega)
      have hnb : ((((p + j * r.step.val).toNat : Int) + r.step.val).toNat) =
          (p + ((j + 1 : Nat) : Int) * r.step.val).toNat := by rw [hjs, h3']
      obtain ⟨ys, hys, hysv⟩ := iterFrom_vchar r p q hs hin hstop fuel (j + 1)
        (vasc ((((p + j * r.step.val).toNat : Int) + r.step.val).toNat) (by omega)) (by omega) (by omega)
        (show asc _ = asc _ by rw [hnb])
      refine ⟨vasc ((((p + j * r.step.val).toNat : Int) + r.step.val).toNat) (by omega) :: ys, ?_, ?_⟩
      · simp only [iterFrom, iterate2_vchar_step r i _ hne hadd, hys, bind, Except.bind, pure,
          Except.pure]
      · rw [show q - j = (q - (j + 1)) + 1 by omega, List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, hysv]
        rw [List.cons.injEq]
        refine ⟨?_, ?_⟩
        · show asc _ = asc _
          rw [hnb, Nat.add_zero]
        · apply List.map_congr_left; intro k _
          simp only [Function.comp_apply]
          rw [show j + 1 + 1 + k = j + 1 + (k + 1) by omega]

/-- The codepoints of `a:s:b` lie between those of `a` and `b`. -/
theorem stepInts_ascii {p q : Int} (s : Int) (hp : 0 ≤ p ∧ p < 128) (hq : 0 ≤ q ∧ q < 128) (k : Nat)
    (hk : (k : Int) < stepCount p s q) : 0 ≤ p + k * s ∧ p + k * s < 128 := by
  have := stepCount_bound p s q k (by omega) hk
  omega

/-- `a:s:b` for ASCII `Char`s `a = Char(p)`, `b = Char(q)` and a nonzero `Int` step. -/
theorem char_colon {p q : Nat} (hp : p < 128) (hq : q < 128) (a b : VChar)
    (ha : a.bits = asc p) (hb : b.bits = asc q) (s : JInt64) (hs : s.val ≠ 0) :
    ∃ l : VChar, (JColon3.colon a s b : JlX (StepRange VChar JInt64)) = .ok ⟨a, s, l⟩ ∧
      (stepCount p s.val q = 0 → l = b) ∧
      (stepCount p s.val q ≠ 0 → l.bits = asc (p + (stepCount p s.val q - 1) * s.val).toNat) := by
  obtain ⟨l, hl, h0, h1⟩ := char_last hp hq a b ha hb s hs
  exact ⟨l, by rw [colon_vchar, hl]; rfl, h0, h1⟩

theorem char_isempty {p q : Nat} (hp : p < 128) (hq : q < 128) (a b l : VChar)
    (ha : a.bits = asc p) (hb : b.bits = asc q) (s : JInt64) (hs : s.val ≠ 0)
    (h0 : stepCount p s.val q = 0 → l = b)
    (h1 : stepCount p s.val q ≠ 0 → l.bits = asc (p + (stepCount p s.val q - 1) * s.val).toNat) :
    isempty_StepRange (⟨a, s, l⟩ : StepRange VChar JInt64) = decide (stepCount p s.val q = 0) := by
  have hcn := stepCount_nonneg p s.val q
  simp only [isempty_StepRange, jeq_vchar, jlt_vchar, eqChar_dec, lt_iv, zero_iv]
  by_cases hc : stepCount p s.val q = 0
  · rw [h0 hc, ha, hb]
    have hpq : p ≠ q := by intro h; subst h; rw [stepCount_self _ _ hs] at hc; omega
    have : (0 < s.val) ≠ ((p : Int) < q) := by
      intro h
      have hpos : stepCount p s.val q ≠ 0 := by
        unfold stepCount
        by_cases h1 : 0 < s.val
        · have : (p : Int) < q := h ▸ h1
          rw [if_pos ⟨h1, by omega⟩]
          have := Int.tdiv_nonneg (a := (q : Int) - p) (b := s.val) (by omega) (by omega); omega
        · have h2 : ¬ (p : Int) < q := fun h' => h1 (h ▸ h')
          rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
          have := Int.tdiv_nonneg (a := (p : Int) - q) (b := -s.val) (by omega) (by omega); omega
      exact hpos hc
    have hne : asc p ≠ asc q := fun e => hpq ((asc_inj hp hq).mp e)
    simp only [hne, decide_false, Bool.not_false, Bool.true_and, ltc_asc hp hq, hc, decide_true]
    by_cases h1 : 0 < s.val <;> by_cases h2 : p < q <;> simp_all <;> omega
  · have hL := stepInts_ascii (p := p) (q := q) s.val ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (stepCount p s.val q - 1).toNat (by rw [Int.toNat_of_nonneg (by omega)]; omega)
    rw [Int.toNat_of_nonneg (show 0 ≤ stepCount p s.val q - 1 by omega)] at hL
    rw [h1 hc, ha]
    have hemp := isempty_lastVal p s.val q hs
    rw [lastVal_count _ _ _ hs (by omega)] at hemp
    have e1 := asc_inj (p := p) (q := (p + (stepCount p s.val q - 1) * s.val).toNat) hp (by omega)
    have e2 := ltc_asc (p := p) (q := (p + (stepCount p s.val q - 1) * s.val).toNat) hp (by omega)
    rw [e2]
    have : (decide (asc p = asc (p + (stepCount p s.val q - 1) * s.val).toNat)) =
        decide ((p : Int) = p + (stepCount p s.val q - 1) * s.val) := by
      rw [decide_eq_decide, e1]; omega
    rw [this]
    have h3 : decide (p < (p + (stepCount p s.val q - 1) * s.val).toNat) =
        decide ((p : Int) < p + (stepCount p s.val q - 1) * s.val) := by
      rw [decide_eq_decide]; omega
    rw [h3, decide_eq_false hc]
    rw [decide_eq_false hc] at hemp
    rw [← hemp]; simp

@[simp] theorem div_sum_inl' {α β δ γ : Type} [JDiv α β γ] [JDiv α δ γ] (x : α) (y : β) :
    (JDiv.div x (Sum.inl y : β ⊕ δ) : JlX γ) = JDiv.div x y := rfl
@[simp] theorem div_sum_inr' {α β δ γ : Type} [JDiv α β γ] [JDiv α δ γ] (x : α) (y : δ) :
    (JDiv.div x (Sum.inr y : β ⊕ δ) : JlX γ) = JDiv.div x y := rfl

theorem div64_ok (x y : JInt64) (hy : y.val ≠ 0) (hx : x.val ≠ IntTy.i64.min) :
    (JDiv.div x y : JlX JInt64) = .ok (lit .i64 (x.val.tdiv y.val)) := by
  show liftJl (JuliaLean.base.int.divSame x y) = _
  rw [JuliaLean.Proofs.base.int.divSame_eq, if_neg (by rintro (h' | ⟨_, h', _⟩) <;> contradiction)]
  rfl

theorem vsub_cp (x y : VChar) : (x - y : JInt64) = x.cp - y.cp := rfl

theorem stepCount_le128 {p q : Int} (s : Int) (hp : 0 ≤ p ∧ p < 128) (hq : 0 ≤ q ∧ q < 128) :
    stepCount p s q ≤ 128 := by
  unfold stepCount
  split
  · have := Int.tdiv_le_self (a := q - p) s (by omega); omega
  · split
    · have := Int.tdiv_le_self (a := p - q) (-s) (by omega); omega
    · omega

theorem ctor_vchar (x : VChar) : (JCtor.ctor x : JlX JInt64) = .ok x.cp := by
  show liftChar (charInt x.bits) = _
  rw [x.hcp]; rfl

/-- The value of `length(r)` / `checked_length(r)`, which returns an `Int` on each branch. -/
def sumVal : JInt64 ⊕ JInt64 → Int := Sum.elim Subtype.val Subtype.val

/-- The facts `char_colon` establishes about the stored stop `l` of `a:s:b`. -/
structure CharStop (p q : Nat) (a b l : VChar) (s : JInt64) : Prop where
  hp : p < 128
  hq : q < 128
  ha : a.bits = asc p
  hb : b.bits = asc q
  hs : s.val ≠ 0
  h0 : stepCount p s.val q = 0 → l = b
  h1 : stepCount p s.val q ≠ 0 → l.bits = asc (p + (stepCount p s.val q - 1) * s.val).toNat

theorem CharStop.last_bounds {p q : Nat} {a b l : VChar} {s : JInt64} (h : CharStop p q a b l s)
    (hc : stepCount p s.val q ≠ 0) :
    0 ≤ (p : Int) + (stepCount p s.val q - 1) * s.val ∧ (p : Int) + (stepCount p s.val q - 1) * s.val < 128 := by
  have hcn := stepCount_nonneg p s.val q
  have := stepInts_ascii (p := p) (q := q) s.val ⟨by omega, by have := h.hp; omega⟩
    ⟨by omega, by have := h.hq; omega⟩ (stepCount p s.val q - 1).toNat
    (by rw [Int.toNat_of_nonneg (by omega)]; omega)
  rwa [Int.toNat_of_nonneg (show 0 ≤ stepCount p s.val q - 1 by omega)] at this

theorem char_length {p q : Nat} {a b l : VChar} {s : JInt64} (h : CharStop p q a b l s) :
    (length_OrdinalRange (⟨a, s, l⟩ : StepRange VChar JInt64) : JlX (JInt64 ⊕ JInt64)).map sumVal =
      .ok (stepCount p s.val q) := by
  have hcn := stepCount_nonneg p s.val q
  have hsp := s.property
  have hs := h.hs
  have hp := h.hp; have hq := h.hq
  have hap := cp_asc h.hp h.ha
  have hle := stepCount_le128 (p := p) (q := q) s.val ⟨by omega, by have := h.hp; omega⟩
    ⟨by omega, by have := h.hq; omega⟩
  have hemp := char_isempty h.hp h.hq a b l h.ha h.hb s h.hs h.h0 h.h1
  simp only [length_OrdinalRange, step_vchar, first_vchar, isempty_vchar, hemp, last_vchar, bind,
    Except.bind, pure, Except.pure]
  by_cases hc : stepCount p s.val q = 0
  · have hz : (a - a : JInt64).val = 0 := by rw [vsub_cp, sub_iv]; simp
    simp only [hc, decide_true, ite_true]
    rw [div64_ok _ _ (by rw [oneunit_iv]; omega) (by rw [hz]; simp [IntTy.min, IntTy.signed, IntTy.bits])]
    show Except.ok (lit .i64 ((a - a : JInt64).val.tdiv (JOneunit.oneunit : JInt64).val)).val = _
    rw [hz, IntVal.lit_val]; simp
  · have hb := h.last_bounds hc
    have hlp := cp_asc (c := l) (p := ((p : Int) + (stepCount p s.val q - 1) * s.val).toNat)
      (by omega) (h.h1 hc)
    rw [Int.toNat_of_nonneg hb.1] at hlp
    simp only [hc, decide_false, Bool.false_eq_true, ite_false, isless_iv, zero_iv]
    have hfin : ∀ y : JInt64, (Except.ok (Sum.inr (lit .i64 (stepCount p s.val q - 1) + JOneunit.oneunit)) :
        JlX (JInt64 ⊕ JInt64)).map sumVal = .ok (stepCount p s.val q) := by
      intro _
      show Except.ok ((lit .i64 (stepCount p s.val q - 1) + JOneunit.oneunit : JInt64).val) = _
      rw [add_iv, IntVal.lit_val, oneunit_iv, i64_small' (z := stepCount p s.val q - 1) (by omega) (by omega),
        show stepCount p s.val q - 1 + 1 = stepCount p s.val q by omega, i64_small' (by omega) (by omega)]
    by_cases hneg : s.val < 0
    · simp only [hneg, decide_true, ite_true, div_sum_inr']
      have hns : (JNeg.neg s : JInt64).val = wrapInt .i64 (-s.val) := neg_iv s
      have hnz : (JNeg.neg s : JInt64).val ≠ 0 := by
        rw [hns]; rcases wrap_neg_cases s hneg with h' | ⟨h', _⟩ <;> omega
      have hav : (a - l : JInt64).val = -((stepCount p s.val q - 1) * s.val) := by
        rw [vsub_cp, sub_iv, hap, hlp]; exact wrap_small_eq (by omega) (by omega) (by omega)
      have hdv : (a - l : JInt64).val = (stepCount p s.val q - 1) * (JNeg.neg s : JInt64).val := by
        rw [hav, hns]
        by_cases h1 : stepCount p s.val q - 1 = 0
        · rw [h1]; simp
        · have := Int.mul_le_mul_of_nonpos_right (show (1 : Int) ≤ stepCount p s.val q - 1 by omega)
            (show s.val ≤ 0 by omega)
          rw [wrap_small_eq (w := -s.val) rfl (by omega) (by omega), Int.mul_neg]
      have hnm : (a - l : JInt64).val ≠ IntTy.i64.min := by
        rw [hav]; simp [IntTy.min, IntTy.signed, IntTy.bits]; omega
      rw [div64_ok _ _ hnz hnm, hdv, Int.mul_tdiv_cancel _ hnz]
      exact hfin s
    · simp only [hneg, decide_false, Bool.false_eq_true, ite_false, div_sum_inl']
      have hdv : (l - a : JInt64).val = (stepCount p s.val q - 1) * s.val := by
        rw [vsub_cp, sub_iv, hap, hlp]; exact wrap_small_eq (by omega) (by omega) (by omega)
      have hnm : (l - a : JInt64).val ≠ IntTy.i64.min := by
        rw [hdv]; simp [IntTy.min, IntTy.signed, IntTy.bits]; omega
      rw [div64_ok _ _ hs hnm, hdv, Int.mul_tdiv_cancel _ hs]
      exact hfin s

theorem char_checked_length {p q : Nat} {a b l : VChar} {s : JInt64} (h : CharStop p q a b l s) :
    (stepCount p s.val q = 0 →
      (checked_length_OrdinalRange (⟨a, s, l⟩ : StepRange VChar JInt64) :
        JlX (JInt64 ⊕ JInt64)).map sumVal = .ok 0) ∧
    (stepCount p s.val q ≠ 0 →
      (checked_length_OrdinalRange (⟨a, s, l⟩ : StepRange VChar JInt64) : JlX (JInt64 ⊕ JInt64)) =
        .error (.jl (.methodError "checked_sub"))) := by
  have hemp := char_isempty h.hp h.hq a b l h.ha h.hb s h.hs h.h0 h.h1
  have hz : (a - a : JInt64).val = 0 := by rw [vsub_cp, sub_iv]; simp
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · simp only [checked_length_OrdinalRange, step_vchar, first_vchar, isempty_vchar, hemp, hc,
      decide_true, ite_true, bind, Except.bind, pure, Except.pure]
    rw [div64_ok _ _ (by rw [oneunit_iv]; omega) (by rw [hz]; simp [IntTy.min, IntTy.signed, IntTy.bits])]
    show Except.ok (lit .i64 ((a - a : JInt64).val.tdiv (JOneunit.oneunit : JInt64).val)).val = _
    rw [hz, IntVal.lit_val]; simp
  · simp only [checked_length_OrdinalRange, step_vchar, first_vchar, isempty_vchar, hemp, hc,
      decide_false, Bool.false_eq_true, ite_false, last_vchar, bind, Except.bind, pure, Except.pure]
    split <;> rfl

theorem iszero64 (x : JInt64) : JIszero.iszero x = decide (x.val = 0) := iszero_iv x

/-- `x in r` (range.jl:1495) for an ASCII `Char` `x = Char(m)` and `r = a:s:b`. -/
theorem char_in {p q m : Nat} {a b l x : VChar} {s : JInt64} (h : CharStop p q a b l s)
    (hm : m < 128) (hx : x.bits = asc m) :
    in_AbstractChar_AbstractRange x (⟨a, s, l⟩ : StepRange VChar JInt64) =
      .ok (decide ((m : Int) ∈ stepInts p s.val q)) := by
  have hp := h.hp; have hq := h.hq; have hs := h.hs
  have hcn := stepCount_nonneg p s.val q
  have hap := cp_asc hp h.ha
  have hxp := cp_asc hm hx
  have hemp := char_isempty h.hp h.hq a b l h.ha h.hb s h.hs h.h0 h.h1
  by_cases hc : stepCount p s.val q = 0
  · have hnil : stepInts p s.val q = [] := (stepInts_nil_iff _ _ _).mpr hc
    simp [in_AbstractChar_AbstractRange, isempty_vchar, hemp, hc, hnil, bind, Except.bind, pure,
      Except.pure]
  have hb := h.last_bounds hc
  have hl := h.h1 hc
  have hlp := cp_asc (c := l) (p := ((p : Int) + (stepCount p s.val q - 1) * s.val).toNat) (by omega) hl
  rw [Int.toNat_of_nonneg hb.1] at hlp
  generalize hL : ((p : Int) + (stepCount p s.val q - 1) * s.val).toNat = L at hl
  have hLv : (L : Int) = (p : Int) + (stepCount p s.val q - 1) * s.val := by rw [← hL]; omega
  have hL128 : L < 128 := by omega
  have hmem := mem_stepInts_fmod p s.val q m hs (by omega)
  rw [← hLv] at hmem
  have hmin : JMinimum.minimum (⟨a, s, l⟩ : StepRange VChar JInt64) =
      .ok (if L < p then l else a) := by
    simp [JMinimum.minimum, minimum_AbstractRange, isempty_vchar, hemp, hc, first_vchar, last_vchar,
      JMin.min, hl, h.ha, ltc_asc hL128 hp, bind, Except.bind, pure, Except.pure]
  have hmax : JMaximum.maximum (⟨a, s, l⟩ : StepRange VChar JInt64) =
      .ok (if L < p then a else l) := by
    simp [JMaximum.maximum, maximum_AbstractRange, isempty_vchar, hemp, hc, first_vchar, last_vchar,
      JMax.max, hl, h.ha, ltc_asc hL128 hp, bind, Except.bind, pure, Except.pure]
  simp only [in_AbstractChar_AbstractRange, isempty_vchar, hemp, hc, decide_false,
    Bool.false_eq_true, ite_false, step_vchar, iszero64, hs, hmin, hmax, first_vchar, ctor_vchar,
    bind, Except.bind, pure, Except.pure]
  rw [mod_iv _ _ hs]
  simp only [eq_iv, jint0_val]
  by_cases hLp : L < p
  · simp only [hLp, ite_true, jle_vchar, hl, hx, h.ha, ltc_asc hL128 hm, eqc_asc hL128 hm,
      ltc_asc hm hp, eqc_asc hm hp]
    have hLp' : (L : Int) < p := by omega
    simp only [hLp', ite_true] at hmem
    by_cases h1 : L ≤ m
    · by_cases h2 : m ≤ p
      · have e1 : (decide (L < m) || decide (L = m)) = true := by
          simp; omega
        have e2 : (decide (m < p) || decide (m = p)) = true := by simp; omega
        simp only [e1, e2, Bool.not_true, Bool.false_eq_true, ite_false]
        congr 1
        rw [decide_eq_decide, hmem, Int.fmod_eq_fmod_iff_fmod_sub_eq_zero]
        show (wrapInt .i64 (x.cp.val - a.cp.val)).fmod s.val = 0 ↔ _
        rw [hap, hxp, wrap_small_eq (w := (m : Int) - p) rfl (by omega) (by omega)]
        omega
      · have e2 : (decide (m < p) || decide (m = p)) = false := by simp; omega
        have e1 : (decide (L < m) || decide (L = m)) = true := by simp; omega
        simp only [e1, e2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
        congr 1; symm; rw [decide_eq_false_iff_not, hmem]; omega
    · have e1 : (decide (L < m) || decide (L = m)) = false := by simp; omega
      simp only [e1, Bool.not_false, ite_true]
      congr 1; symm; rw [decide_eq_false_iff_not, hmem]; omega
  · simp only [hLp, ite_false, jle_vchar, hl, hx, h.ha, ltc_asc hp hm, eqc_asc hp hm,
      ltc_asc hm hL128, eqc_asc hm hL128]
    have hLp' : ¬ (L : Int) < p := by omega
    simp only [hLp', ite_false] at hmem
    by_cases h1 : p ≤ m
    · by_cases h2 : m ≤ L
      · have e1 : (decide (p < m) || decide (p = m)) = true := by simp; omega
        have e2 : (decide (m < L) || decide (m = L)) = true := by simp; omega
        simp only [e1, e2, Bool.not_true, Bool.false_eq_true, ite_false]
        congr 1
        rw [decide_eq_decide, hmem, Int.fmod_eq_fmod_iff_fmod_sub_eq_zero]
        show (wrapInt .i64 (x.cp.val - a.cp.val)).fmod s.val = 0 ↔ _
        rw [hap, hxp, wrap_small_eq (w := (m : Int) - p) rfl (by omega) (by omega)]
        omega
      · have e1 : (decide (p < m) || decide (p = m)) = true := by simp; omega
        have e2 : (decide (m < L) || decide (m = L)) = false := by simp; omega
        simp only [e1, e2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
        congr 1; symm; rw [decide_eq_false_iff_not, hmem]; omega
    · have e1 : (decide (p < m) || decide (p = m)) = false := by simp; omega
      simp only [e1, Bool.not_false, ite_true]
      congr 1; symm; rw [decide_eq_false_iff_not, hmem]; omega

theorem char_iter {p q : Nat} {a b l : VChar} {s : JInt64} (h : CharStop p q a b l s) (fuel : Nat)
    (hf : (stepCount p s.val q).toNat ≤ fuel) :
    ∃ xs, iterList (⟨a, s, l⟩ : StepRange VChar JInt64) fuel = .ok xs ∧
      xs.map VChar.bits = (stepInts p s.val q).map fun k => asc k.toNat := by
  have hp := h.hp; have hq := h.hq
  have hcn := stepCount_nonneg p s.val q
  have hemp := char_isempty h.hp h.hq a b l h.ha h.hb s h.hs h.h0 h.h1
  by_cases hc : stepCount p s.val q = 0
  · refine ⟨[], ?_, by rw [(stepInts_nil_iff _ _ _).mpr hc]; rfl⟩
    simp [iterList, JIterate1.iterate, iterate_OrdinalRange, isempty_vchar, hemp, hc, bind,
      Except.bind, pure, Except.pure]
  have hin : ∀ j : Nat, j ≤ (stepCount p s.val q - 1).toNat →
      0 ≤ (p : Int) + j * s.val ∧ (p : Int) + j * s.val < 128 := fun j hj =>
    stepInts_ascii (p := p) (q := q) s.val ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ j (by omega)
  have hstop : l.bits = asc ((p : Int) + ((stepCount p s.val q - 1).toNat : Nat) * s.val).toNat := by
    rw [h.h1 hc, Int.toNat_of_nonneg (show 0 ≤ stepCount p s.val q - 1 by omega)]
  obtain ⟨ys, hys, hysv⟩ := iterFrom_vchar ⟨a, s, l⟩ p (stepCount p s.val q - 1).toNat h.hs hin hstop
    fuel 0 a (Nat.zero_le _) (by omega) (by rw [h.ha]; simp)
  refine ⟨a :: ys, ?_, ?_⟩
  · simp [iterList, JIterate1.iterate, iterate_OrdinalRange, isempty_vchar, hemp, hc, hys, bind,
      Except.bind, pure, Except.pure]
  · simp only [List.map_cons, hysv, stepInts]
    rw [show (stepCount p s.val q).toNat = (stepCount p s.val q - 1).toNat + 1 by omega,
      List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, h.ha]
    rw [List.cons.injEq]
    refine ⟨by simp, ?_⟩
    apply List.map_congr_left; intro k _
    simp only [Function.comp_apply]
    rw [show 0 + 1 + k = k + 1 by omega]

theorem bits_to_cps : ∀ (xs : List VChar) (ks : List Int), (∀ k ∈ ks, 0 ≤ k ∧ k < 128) →
    xs.map VChar.bits = ks.map (fun k => asc k.toNat) →
    xs.map (fun c => c.cp.val) = ks ∧ ∀ c ∈ xs, char_UInt32 (UInt32.ofNat c.cp.val.toNat) = .ok c.bits
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, k :: ks, hk, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hk0 := hk k (by simp)
    have hcp := cp_asc (c := x) (p := k.toNat) (by omega) h.1
    rw [Int.toNat_of_nonneg hk0.1] at hcp
    obtain ⟨ih1, ih2⟩ := bits_to_cps xs ks (fun k' hk' => hk k' (by simp [hk'])) h.2
    refine ⟨by simp [hcp, ih1], ?_⟩
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [hcp, h.1]; exact char_asc (by omega)
    · exact ih2 c hc

/-- `a:b` and `a:s:b` for `Char` endpoints (`(:)(start::T, stop::T) where {T}`, range.jl:7;
`(:)(start::T, step, stop::T) where {T}`, range.jl:64; the `:` docstring: "`a:b` constructs a range
from `a` to `b` with a step size equal to +1, which produces ... a `StepRange` when `a` and `b` are
characters", "`a:s:b` is similar but uses a step size of `s`"). For `a = Char(p)`, `b = Char(q)` with
ASCII codepoints `p, q < 0x80` and an `Int` step `s`: `a:b` is `a:1:b`; a zero step throws
`ArgumentError`; otherwise `a:s:b` is a `StepRange` with first element `a` and step `s` that is empty
exactly when no codepoint `p, p+s, p+2s, ...` lies between `p` and `q`, its `length` (range.jl:777)
is the number of such codepoints, `checked_length` (range.jl:751) is `0` when it is empty and
otherwise throws `MethodError` (range.jl:747: it "is defined iff checked_add and checked_sub are
defined between the relevant types", and there is no `checked_sub(::Char, ::Char)`), when it is empty
and `a ≠ b` it keeps the given stop `b` (range.jl:400, `steprange_last_empty`: "use the user-given
value for stop"), and iterating it yields the `Char`s `Char(c)` for exactly those codepoints `c`, in
order. -/
def CharColon : Prop :=
  ∀ (p q : Nat) (a b : VChar) (s : JInt64), p < 128 → q < 128 →
    char_UInt32 (UInt32.ofNat p) = .ok a.bits → char_UInt32 (UInt32.ofNat q) = .ok b.bits →
    (JColon2.colon a b : JlX (StepRange VChar JInt64)) = JColon3.colon a (jint 1) b ∧
    (s.val = 0 → (JColon3.colon a s b : JlX (StepRange VChar JInt64)) =
      .error (.jl (.argumentError "step cannot be zero"))) ∧
    (s.val ≠ 0 → ∃ r : StepRange VChar JInt64, JColon3.colon a s b = .ok r ∧
      JFirst.first r = .ok a ∧ JStep.step r = .ok s ∧
      JIsempty.isempty r = .ok (decide (stepCount p s.val q = 0)) ∧
      (length_OrdinalRange r : JlX (JInt64 ⊕ JInt64)).map sumVal = .ok (stepCount p s.val q) ∧
      (stepCount p s.val q = 0 →
        (checked_length_OrdinalRange r : JlX (JInt64 ⊕ JInt64)).map sumVal = .ok 0) ∧
      (stepCount p s.val q ≠ 0 →
        (checked_length_OrdinalRange r : JlX (JInt64 ⊕ JInt64)) = .error (.jl (.methodError "checked_sub"))) ∧
      (stepCount p s.val q = 0 → p ≠ q → r.stop = b) ∧
      ∀ fuel, (stepCount p s.val q).toNat ≤ fuel → ∃ xs, iterList r fuel = .ok xs ∧
        xs.map (fun c => c.cp.val) = stepInts p s.val q ∧
        ∀ c ∈ xs, char_UInt32 (UInt32.ofNat c.cp.val.toNat) = .ok c.bits)

theorem charColon_proven : CharColon := by
  intro p q a b s hp hq ha hb
  rw [char_asc hp] at ha; rw [char_asc hq] at hb
  injection ha with ha; injection hb with hb
  refine ⟨colon2_vchar a b, fun hs => ?_, fun hs => ?_⟩
  · rw [colon_vchar, char_last_zero a b s hs]; rfl
  obtain ⟨l, hc, h0, h1⟩ := char_colon hp hq a b ha.symm hb.symm s hs
  have h : CharStop p q a b l s := ⟨hp, hq, ha.symm, hb.symm, hs, h0, h1⟩
  obtain ⟨hcl0, hcl1⟩ := char_checked_length h
  refine ⟨_, hc, rfl, rfl, by rw [isempty_vchar, char_isempty hp hq a b l ha.symm hb.symm s hs h0 h1],
    char_length h, hcl0, hcl1, fun hz _ => h0 hz, fun fuel hf => ?_⟩
  obtain ⟨xs, hxs, hbits⟩ := char_iter h fuel hf
  have hks : ∀ k ∈ stepInts p s.val q, 0 ≤ k ∧ k < 128 := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := (mem_stepInts _ _ _ _).mp hk
    exact stepInts_ascii (p := p) (q := q) s.val ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ j hj
  exact ⟨xs, hxs, bits_to_cps xs _ hks hbits⟩

/-- `x in r` for an ASCII `Char` `x` and a `Char` range `r = a:s:b` with ASCII endpoints
(`in(x::AbstractChar, r::AbstractRange{<:AbstractChar})`, range.jl:1495, which Julia selects for
these arguments; the `in` docstring: "Determine whether an item is in the given collection"): for
`x = Char(m)`, `a = Char(p)`, `b = Char(q)` with `m, p, q < 0x80`, it holds exactly when `m` is one of
the codepoints `p, p+s, p+2s, ...` that lie between `p` and `q`. In particular the first element of a
nonempty range is in it and a `Char` outside `[minimum(r), maximum(r)]` is not. -/
def CharRangeIn : Prop :=
  ∀ (p q m : Nat) (a b x : VChar) (s : JInt64) (r : StepRange VChar JInt64),
    p < 128 → q < 128 → m < 128 →
    char_UInt32 (UInt32.ofNat p) = .ok a.bits → char_UInt32 (UInt32.ofNat q) = .ok b.bits →
    char_UInt32 (UInt32.ofNat m) = .ok x.bits → JColon3.colon a s b = .ok r →
    in_AbstractChar_AbstractRange x r = .ok (decide ((m : Int) ∈ stepInts p s.val q))

theorem charRangeIn_proven : CharRangeIn := by
  intro p q m a b x s r hp hq hm ha hb hx hr
  rw [char_asc hp] at ha; rw [char_asc hq] at hb; rw [char_asc hm] at hx
  injection ha with ha; injection hb with hb; injection hx with hx
  by_cases hs : s.val = 0
  · rw [colon_vchar, char_last_zero a b s hs] at hr; cases hr
  obtain ⟨l, hc, h0, h1⟩ := char_colon hp hq a b ha.symm hb.symm s hs
  rw [hc] at hr; cases hr
  exact char_in ⟨hp, hq, ha.symm, hb.symm, hs, h0, h1⟩ hm hx.symm

/-- `x in r` for a `Char` `x` and the `Char` range `r = a:b` (range.jl:1495; the `in` docstring:
"Determine whether an item is in the given collection, in the sense that it is `==` to one of the
values generated by iterating over the collection"): it holds exactly when `x == c` (char.jl:263) for
an element `c` that iterating `r` yields. -/
def CharRangeInEq : Prop :=
  ∀ (a b x : VChar) (r : StepRange VChar JInt64) (fuel : Nat) (xs : List VChar),
    JColon2.colon a b = .ok r → iterList r fuel = .ok xs →
    in_AbstractChar_AbstractRange x r = .ok (xs.any fun c => eq_Char x.bits c.bits)

theorem charInt_malformedA : charInt 0x41000041 = .ok (lit .i64 65) := by rfl

/-- The malformed `Char` `'\x41\x00\x00\x41'` (`reinterpret(Char, 0x41000041)`): `Int` of it is
`65`, the codepoint of `'A'`, but it is not `==` to `'A'`. -/
def malformedA : VChar := ⟨0x41000041, lit .i64 65, charInt_malformedA⟩

theorem charRangeInEq_refuted : ¬ CharRangeInEq := by
  intro h
  have := h (vasc 65 (by decide)) (vasc 66 (by decide)) malformedA
    ⟨vasc 65 (by decide), jint 1, vasc 66 (by decide)⟩ 2 [vasc 65 (by decide), vasc 66 (by decide)]
    (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

end CharRanges

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section VcatRanges

/-- The model's `for x in r` loop visits the elements that iterating `r` yields. -/
theorem forIn_go_eq {R E St σ : Type} [JIterate1 R E St] [JIterate2 R St E] (r : R)
    (body : E → σ → JlX σ) :
    ∀ (n : Nat) (s : St) (acc : σ) (xs : List E), iterFrom r n s = .ok xs →
      forIn.go r body n s acc = xs.foldlM (fun acc x => body x acc) acc
  | 0, s, acc, xs, h => by simp [iterFrom, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, s, acc, xs, h => by
    simp only [iterFrom, bind, Except.bind] at h
    simp only [forIn.go, bind, Except.bind]
    cases hi : JIterate2.iterate r s with
    | error e => rw [hi] at h; cases h
    | ok o =>
      rw [hi] at h
      cases o with
      | none => simp [pure, Except.pure] at h; subst h; rfl
      | some p =>
        obtain ⟨x, s'⟩ := p
        simp only at h
        cases hr : iterFrom r n s' with
        | error e => rw [hr] at h; cases h
        | ok ys =>
          rw [hr] at h; simp [pure, Except.pure] at h; subst h
          simp only [List.foldlM_cons, bind, Except.bind]
          cases hb : body x acc with
          | error e => rfl
          | ok acc' => exact forIn_go_eq r body n s' acc' ys hr

theorem forIn_eq {R E St σ : Type} [JIterate1 R E St] [JIterate2 R St E] (r : R) (init : σ)
    (body : E → σ → JlX σ) (fuel : Nat) (xs : List E) (h : iterList r fuel = .ok xs) :
    JuliaLean.base.range.forIn r init body fuel = xs.foldlM (fun acc x => body x acc) init := by
  simp only [iterList, bind, Except.bind] at h
  simp only [JuliaLean.base.range.forIn, bind, Except.bind]
  cases hi : JIterate1.iterate r with
  | error e => rw [hi] at h; cases h
  | ok o =>
    rw [hi] at h
    cases o with
    | none => simp [pure, Except.pure] at h; subst h; rfl
    | some p =>
      obtain ⟨x, s⟩ := p
      simp only at h
      cases hr : iterFrom r fuel s with
      | error e => rw [hr] at h; cases h
      | ok ys =>
        rw [hr] at h; simp [pure, Except.pure] at h; subst h
        simp only [List.foldlM_cons, bind, Except.bind]
        cases hb : body x init with
        | error e => rfl
        | ok acc' => exact forIn_go_eq r body fuel s acc' ys hr

/-- `x + y` of `Int`s as the model's concrete `Int` code computes it (`JuliaLean.Core`). -/
abbrev addI (x y : JInt64) : JInt64 := @HAdd.hAdd JInt64 JInt64 JInt64 instHAdd x y

theorem lit_succ (z : Int) : addI (lit .i64 z) (jint 1) = lit .i64 (z + 1) := by
  apply Subtype.ext
  show wrapInt .i64 (wrapInt .i64 z + wrapInt .i64 1) = wrapInt .i64 (z + 1)
  rw [IntVal.wrapInt_add_left, IntVal.wrapInt_add_right]

theorem i64_max_val : IntTy.i64.max = 2 ^ 63 - 1 := by simp [IntTy.max, IntTy.signed, IntTy.bits]
theorem i64_min_val : IntTy.i64.min = -2 ^ 63 := by simp [IntTy.min, IntTy.signed, IntTy.bits]

/-- Writing the elements `xs` one after another with `@inbounds a[i] = x; i += 1` into
`pre ++ [undef, ...]` from `i = length(pre) + 1`. -/
theorem setindex_fold (body : JInt64 → List (Option JInt64) × JInt64 → JlX (List (Option JInt64) × JInt64))
    (hbody : ∀ x acc, body x acc = do let a ← setindexInbounds acc.1 x acc.2; pure (a, addI acc.2 (jint 1))) :
    ∀ (xs : List JInt64) (pre : List (Option JInt64)) (k : Nat) (i : JInt64),
      i.val = wrapInt .i64 (pre.length + 1) → xs.length ≤ k → (pre.length : Int) + k ≤ IntTy.i64.max →
      ∃ j : JInt64, j.val = wrapInt .i64 (pre.length + xs.length + 1) ∧
        xs.foldlM (fun acc x => body x acc) (pre ++ List.replicate k none, i) =
          .ok (pre ++ xs.map some ++ List.replicate (k - xs.length) none, j)
  | [], pre, k, i, hi, _, _ => ⟨i, by simp [hi], by simp [pure, Except.pure]⟩
  | x :: xs, pre, k, i, hi, hk, hmax => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hmx := i64_max_val
    have hmn := i64_min_val
    have hi' : i.val = pre.length + 1 := by
      rw [hi]; exact wrap_in .i64 (by omega) (by omega)
    have hset : setindexInbounds (pre ++ List.replicate (k' + 1) none) x i =
        .ok (pre ++ some x :: List.replicate k' none) := by
      unfold setindexInbounds
      rw [if_pos (by simp; omega)]
      have hidx : i.val.toNat - 1 = pre.length := by omega
      rw [hidx]
      simp [List.set_append_right, List.replicate_succ, pure, Except.pure]
    have hi1 : (addI i (jint 1)).val = wrapInt .i64 ((pre ++ [some x]).length + 1) := by
      show wrapInt .i64 (i.val + (jint 1).val) = _
      rw [jint1_val, hi']
      simp only [List.length_append, List.length_singleton]
      congr 1
    obtain ⟨j, hj, hfold⟩ := setindex_fold body hbody xs (pre ++ [some x]) k' (addI i (jint 1)) hi1
      (by simp at hk; omega) (by simp; omega)
    refine ⟨j, by rw [hj]; congr 1; simp; omega, ?_⟩
    rw [List.foldlM_cons, hbody x]
    simp only [bind, Except.bind, hset, pure, Except.pure]
    rw [show pre ++ some x :: List.replicate k' none = (pre ++ [some x]) ++ List.replicate k' none by simp,
      hfold]
    simp [Nat.add_sub_add_right]

theorem sum_cnt_nonneg (rs : List (JInt64 × JInt64)) :
    0 ≤ (rs.map fun p => cnt p.1.val p.2.val).sum := by
  induction rs with
  | nil => simp
  | cons p rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have : 0 ≤ cnt p.1.val p.2.val := by unfold cnt; split <;> omega
    omega

/-- The first loop of `vcat`: `n = checked_add(n, length(ra))` over the ranges. -/
theorem vcat_loop1 (f : UnitRange JInt64 → JInt64 → JlX (ForInStep JInt64))
    (hf : ∀ (p : JInt64 × JInt64) (s : JInt64), 0 ≤ s.val → cnt p.1.val p.2.val ≤ IntTy.i64.max →
      (s.val + cnt p.1.val p.2.val ≤ IntTy.i64.max →
        f ⟨p.1, unitStop p.1 p.2⟩ s = .ok (.yield (lit .i64 (s.val + cnt p.1.val p.2.val)))) ∧
      (IntTy.i64.max < s.val + cnt p.1.val p.2.val →
        ∃ msg, f ⟨p.1, unitStop p.1 p.2⟩ s = .error (.jl (.overflowError msg)))) :
    ∀ (rs : List (JInt64 × JInt64)) (s : JInt64), 0 ≤ s.val →
      (∀ p ∈ rs, cnt p.1.val p.2.val ≤ IntTy.i64.max) →
      (s.val + (rs.map fun p => cnt p.1.val p.2.val).sum ≤ IntTy.i64.max →
        ForIn.forIn (rs.map fun p => (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64)) s f =
          .ok (lit .i64 (s.val + (rs.map fun p => cnt p.1.val p.2.val).sum))) ∧
      (IntTy.i64.max < s.val + (rs.map fun p => cnt p.1.val p.2.val).sum →
        ∃ msg, ForIn.forIn (rs.map fun p => (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64)) s f =
          .error (.jl (.overflowError msg)))
  | [], s, hs, _ => by
    refine ⟨fun _ => ?_, fun h => ?_⟩
    · simp only [List.map_nil, List.forIn_nil, List.sum_nil, Int.add_zero, pure, Except.pure]
      congr 1; apply Subtype.ext; exact (IntVal.wrapInt_val s).symm
    · have := s.property; simp at h; omega
  | p :: rs, s, hs, hrs => by
    have hc0 : 0 ≤ cnt p.1.val p.2.val := by unfold cnt; split <;> omega
    have hcs : ∀ q ∈ rs, 0 ≤ cnt q.1.val q.2.val := fun q _ => by unfold cnt; split <;> omega
    have hsum := sum_cnt_nonneg rs
    have hfp := hf p s hs (hrs p (by simp))
    simp only [List.map_cons, List.sum_cons, List.forIn_cons, bind, Except.bind]
    by_cases hfit : s.val + cnt p.1.val p.2.val ≤ IntTy.i64.max
    · simp only [hfp.1 hfit]
      have hv : (lit .i64 (s.val + cnt p.1.val p.2.val)).val = s.val + cnt p.1.val p.2.val :=
        wrap_in .i64 (by have := s.property; omega) hfit
      have ih := vcat_loop1 f hf rs (lit .i64 (s.val + cnt p.1.val p.2.val)) (by omega)
        (fun q hq => hrs q (by simp [hq]))
      rw [hv] at ih
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [(ih.1 (by omega))]; congr 2; omega
      · exact ih.2 (by omega)
    · obtain ⟨msg, hm⟩ := hfp.2 (by omega)
      simp only [hm]
      exact ⟨fun h => absurd (by omega : s.val + cnt p.1.val p.2.val ≤ IntTy.i64.max) hfit, fun _ => ⟨msg, rfl⟩⟩

/-- The second loop of `vcat`: copying the elements of each range in turn. -/
theorem vcat_loop2 (fuel : Nat)
    (body : JInt64 → List (Option JInt64) × JInt64 → JlX (List (Option JInt64) × JInt64))
    (hbody : ∀ x acc, body x acc = do let a ← setindexInbounds acc.1 x acc.2; pure (a, addI acc.2 (jint 1)))
    (g : UnitRange JInt64 → List (Option JInt64) × JInt64 → JlX (ForInStep (List (Option JInt64) × JInt64)))
    (hg : ∀ ra st, g ra st = do
      let x ← JuliaLean.base.range.forIn ra (st.1, st.2) body fuel
      pure (ForInStep.yield (x.1, x.2))) :
    ∀ (rs : List (JInt64 × JInt64)) (pre : List (Option JInt64)) (k : Nat) (i : JInt64),
      i.val = wrapInt .i64 (pre.length + 1) → (∀ p ∈ rs, cnt p.1.val p.2.val < fuel) →
      (rs.map fun p => cnt p.1.val p.2.val).sum ≤ k → (pre.length : Int) + k ≤ IntTy.i64.max →
      ∃ (ys : List JInt64) (j : JInt64), ys.map Subtype.val = rs.flatMap (fun p => intsFromTo p.1.val p.2.val) ∧
        ForIn.forIn (rs.map fun p => (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64))
          (pre ++ List.replicate k none, i) g =
          .ok (pre ++ ys.map some ++ List.replicate (k - ys.length) none, j)
  | [], pre, k, i, _, _, _, _ => ⟨[], i, rfl, by simp [pure, Except.pure]⟩
  | p :: rs, pre, k, i, hi, hf, hk, hmax => by
    have hc0 : 0 ≤ cnt p.1.val p.2.val := by unfold cnt; split <;> omega
    have hsum := sum_cnt_nonneg rs
    simp only [List.map_cons, List.sum_cons] at hk
    have hfp := hf p (by simp)
    have hus := unitStop_val p.1 p.2
    have hit := iterList_unit (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64) fuel (by
      show (( unitStop p.1 p.2).val - p.1.val).toNat < fuel
      rw [hus]; unfold cnt at hfp; split at hfp <;> split <;> omega)
    obtain ⟨xs, hxs, hxv⟩ : ∃ xs, iterList (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64) fuel = .ok xs ∧
        xs.map Subtype.val = intsFromTo p.1.val p.2.val := by
      cases h : iterList (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64) fuel with
      | error e => rw [h] at hit; cases hit
      | ok xs =>
        rw [h] at hit
        refine ⟨xs, rfl, ?_⟩
        simp only [Except.map, Except.ok.injEq] at hit
        show vals xs = _
        rw [hit, hus]; split
        · rfl
        · rw [intsFromTo_empty (by omega), intsFromTo_empty (by omega)]
    have hlen : (xs.length : Int) = cnt p.1.val p.2.val := by
      have := congrArg List.length hxv
      simp only [List.length_map, intsFromTo_length] at this
      rw [this]; unfold cnt; split <;> omega
    obtain ⟨j, hj, hfold⟩ := setindex_fold body hbody xs pre k i hi (by omega) hmax
    have hfor := forIn_eq (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64)
      (pre ++ List.replicate k none, i) body fuel xs hxs
    obtain ⟨ys, j', hys, hrest⟩ := vcat_loop2 fuel body hbody g hg rs (pre ++ xs.map some) (k - xs.length) j
      (by rw [hj, List.length_append, List.length_map]; push_cast; rfl) (fun q hq => hf q (by simp [hq]))
      (by omega) (by simp; omega)
    refine ⟨xs ++ ys, j', by simp [hxv, hys], ?_⟩
    simp only [List.map_cons, List.forIn_cons, hg, bind, Except.bind, hfor, hfold, pure, Except.pure]
    rw [hrest]
    simp only [List.map_append, List.append_assoc, List.length_append, Nat.sub_sub]

theorem errBind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

theorem okBind {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

theorem flat_len (ps : List (JInt64 × JInt64)) :
    (((ps.flatMap fun p => intsFromTo p.1.val p.2.val).length : Nat) : Int) =
      (ps.map fun p => cnt p.1.val p.2.val).sum := by
  induction ps with
  | nil => simp
  | cons q qs ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    have hq : ((intsFromTo q.1.val q.2.val).length : Int) = cnt q.1.val q.2.val := by
      rw [intsFromTo_length]; unfold cnt; split <;> omega
    omega

/-- The model's `vcat` of `Int` unit ranges, with its two loops written out. -/
theorem vcat_unfold (ps : List (UnitRange JInt64)) (fuel : Nat) :
    vcat_AbstractRange (T := JInt64) ps fuel = (do
      let n ← ForIn.forIn ps (jint 0) (fun (ra : UnitRange JInt64) (r : JInt64) => (do
        let x ← JLength.length ra
        let y ← JCheckedAdd.checkedAdd r x
        let n ← (JConvert.convert y : JlX JInt64)
        pure (ForInStep.yield n) : JlX (ForInStep JInt64)))
      let a ← JVectorUndef.vectorUndef (T := JInt64) n
      let st ← ForIn.forIn ps (a, jint 1) (fun (ra : UnitRange JInt64) (st : List (Option JInt64) × JInt64) => (do
        let x ← JuliaLean.base.range.forIn ra (st.1, st.2) (fun (x : JInt64) (acc : List (Option JInt64) × JInt64) => (do
          let a ← setindexInbounds acc.1 x acc.2
          pure (a, addI acc.2 (jint 1)) : JlX (List (Option JInt64) × JInt64))) fuel
        pure (ForInStep.yield (x.1, x.2)) : JlX (ForInStep (List (Option JInt64) × JInt64))))
      pure st.1) := rfl

/-- `vcat(rs::AbstractRange{T}...)` (range.jl:1415; the `vcat` docstring: "Concatenate arrays or
numbers vertically") of `Int` unit ranges `a:b` whose lengths fit in `Int`: when the total length
fits in `Int` it returns the vector of all their elements in order; otherwise `checked_add` throws
`OverflowError`. -/
def VcatUnitRanges : Prop :=
  ∀ (rs : List (JInt64 × JInt64 × UnitRange JInt64)) (fuel : Nat),
    (∀ x ∈ rs, JColon2.colon x.1 x.2.1 = .ok x.2.2 ∧ cnt x.1.val x.2.1.val ≤ IntTy.i64.max ∧
      cnt x.1.val x.2.1.val < fuel) →
    ((rs.map fun x => cnt x.1.val x.2.1.val).sum ≤ IntTy.i64.max →
      (vcat_AbstractRange (T := JInt64) (rs.map fun x => x.2.2) fuel).map
          (List.map (Option.map Subtype.val)) =
        .ok ((rs.flatMap fun x => intsFromTo x.1.val x.2.1.val).map some)) ∧
    (IntTy.i64.max < (rs.map fun x => cnt x.1.val x.2.1.val).sum →
      ∃ msg, vcat_AbstractRange (T := JInt64) (rs.map fun x => x.2.2) fuel =
        .error (.jl (.overflowError msg)))

theorem vcatUnitRanges_proven : VcatUnitRanges := by
  intro rs fuel hrs
  have hr : (rs.map fun x => x.2.2) = ((rs.map fun x => (x.1, x.2.1)).map
      fun p => (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64)) := by
    simp only [List.map_map]
    apply List.map_congr_left; intro x hx
    have := (hrs x hx).1; rw [colon_unit] at this; injection this with h; exact h.symm
  have hsum : (rs.map fun x => cnt x.1.val x.2.1.val) =
      ((rs.map fun x => (x.1, x.2.1)).map fun p => cnt p.1.val p.2.val) := by simp [List.map_map]
  have hflat : (rs.flatMap fun x => intsFromTo x.1.val x.2.1.val) =
      ((rs.map fun x => (x.1, x.2.1)).flatMap fun p => intsFromTo p.1.val p.2.val) := by
    simp [List.flatMap_map]
  have hps : ∀ p ∈ rs.map (fun x => (x.1, x.2.1)),
      cnt p.1.val p.2.val ≤ IntTy.i64.max ∧ cnt p.1.val p.2.val < fuel := by
    intro p hp; simp only [List.mem_map] at hp; obtain ⟨x, hx, rfl⟩ := hp
    exact ⟨(hrs x hx).2.1, (hrs x hx).2.2⟩
  rw [hr, hsum, hflat]
  clear hr hsum hflat
  generalize rs.map (fun x => (x.1, x.2.1)) = ps at hps ⊢
  have hmx := i64_max_val
  have hmn := i64_min_val
  have hsum0 := sum_cnt_nonneg ps
  have hf : ∀ (p : JInt64 × JInt64) (s : JInt64), 0 ≤ s.val → cnt p.1.val p.2.val ≤ IntTy.i64.max →
      (s.val + cnt p.1.val p.2.val ≤ IntTy.i64.max →
        (fun (ra : UnitRange JInt64) (r : JInt64) => (do
          let x ← JLength.length ra
          let y ← JCheckedAdd.checkedAdd r x
          let n ← (JConvert.convert y : JlX JInt64)
          pure (ForInStep.yield n) : JlX (ForInStep JInt64))) ⟨p.1, unitStop p.1 p.2⟩ s =
          .ok (.yield (lit .i64 (s.val + cnt p.1.val p.2.val)))) ∧
      (IntTy.i64.max < s.val + cnt p.1.val p.2.val →
        ∃ msg, (fun (ra : UnitRange JInt64) (r : JInt64) => (do
          let x ← JLength.length ra
          let y ← JCheckedAdd.checkedAdd r x
          let n ← (JConvert.convert y : JlX JInt64)
          pure (ForInStep.yield n) : JlX (ForInStep JInt64))) ⟨p.1, unitStop p.1 p.2⟩ s =
          .error (.jl (.overflowError msg))) := by
    intro p s hs hc
    obtain ⟨n, hn, hnv⟩ := lengthUnit_fits p.1 p.2 hc
    have hc0 : 0 ≤ cnt p.1.val p.2.val := by unfold cnt; split <;> omega
    obtain ⟨hadd1, hadd2⟩ := checkedAdd_spec s (n : JInt64)
    have hlen : (JLength.length (⟨p.1, unitStop p.1 p.2⟩ : UnitRange JInt64) : JlX JInt64) = .ok n := hn
    have hnv' : (n : JInt64).val = cnt p.1.val p.2.val := hnv
    refine ⟨fun hfit => ?_, fun hov => ?_⟩
    · have hin : IntTy.i64.min ≤ s.val + (n : JInt64).val ∧ s.val + (n : JInt64).val ≤ IntTy.i64.max := by
        rw [hnv']; constructor <;> omega
      simp only [hlen, hadd1 hin, convert_self, bind, Except.bind, pure, Except.pure]
      congr 2; apply Subtype.ext
      show s.val + (n : JInt64).val = wrapInt .i64 (s.val + cnt p.1.val p.2.val)
      rw [← hnv']; exact (wrap_in .i64 hin.1 hin.2).symm
    · obtain ⟨msg, hm⟩ := hadd2 (by rw [hnv']; omega)
      exact ⟨msg, by simp only [hlen, hm, bind, Except.bind]⟩
  have hl1 := vcat_loop1 (fun (ra : UnitRange JInt64) (r : JInt64) => (do
          let x ← JLength.length ra
          let y ← JCheckedAdd.checkedAdd r x
          let n ← (JConvert.convert y : JlX JInt64)
          pure (ForInStep.yield n) : JlX (ForInStep JInt64))) hf ps (jint 0) (by simp)
    (fun p hp => (hps p hp).1)
  simp only [jint0_val, Int.zero_add] at hl1
  rw [vcat_unfold]
  refine ⟨fun hfit => ?_, fun hov => ?_⟩
  · have hlv : (lit .i64 (ps.map fun p => cnt p.1.val p.2.val).sum).val =
        (ps.map fun p => cnt p.1.val p.2.val).sum := wrap_in .i64 (by omega) hfit
    obtain ⟨ys, j, hys, hl2⟩ := vcat_loop2 fuel _ (fun x acc => rfl) _ (fun ra st => rfl) ps []
      (ps.map fun p => cnt p.1.val p.2.val).sum.toNat (jint 1) (by simp) (fun p hp => (hps p hp).2)
      (by omega) (by simp; omega)
    simp only [List.nil_append] at hl2
    have hys_len : (ys.length : Int) = (ps.map fun p => cnt p.1.val p.2.val).sum := by
      have := congrArg List.length hys
      rw [List.length_map] at this; rw [this, flat_len]
    have hvu : JVectorUndef.vectorUndef (T := JInt64) (lit .i64 (ps.map fun p => cnt p.1.val p.2.val).sum) =
        .ok (List.replicate (ps.map fun p => cnt p.1.val p.2.val).sum.toNat none) := by
      simp only [JVectorUndef.vectorUndef, hlv, show ¬ ((ps.map fun p => cnt p.1.val p.2.val).sum < 0) by omega,
        ite_false, pure, Except.pure]
    simp only [hl1.1 hfit, okBind, hvu, hl2]
    rw [show (ps.map fun p => cnt p.1.val p.2.val).sum.toNat - ys.length = 0 by omega]
    simp [pure, Except.pure, Except.map, ← hys, Function.comp_def]
  · obtain ⟨msg, hm⟩ := hl1.2 hov
    refine ⟨msg, ?_⟩
    simp only [hm, errBind]

end VcatRanges

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)
open JuliaLean.base.float (round_Nearest_llvm)

section RangeIndexRange

/-- `step_hp(r::StepRangeLen) = r.step`, range.jl:742. -/
instance : JStepHp (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 := ⟨fun r => pure (step_hp_StepRangeLen r)⟩
/-- `checkbounds(r, s)` of an `Int` `StepRangeLen` and an `Int` unit range index: `checkbounds`
(abstractarray.jl:690) with `checkindex(::Type{Bool}, inds::AbstractUnitRange, i::AbstractRange)`
(abstractarray.jl:756). -/
instance : JCheckbounds (StepRangeLen JInt64 JInt64 JInt64 JInt64) (UnitRange JInt64) :=
  ⟨checkboundsVectorRange⟩
/-- `checkbounds(r, s)` of a `LinRange{Float64}` and an `Int` unit range index (abstractarray.jl:690,
756). -/
instance : JCheckbounds (LinRange F64 JInt64) (UnitRange JInt64) := ⟨checkboundsVectorRange⟩
/-- `LinearIndices(s)` of a vector `s` with one-based axes (`LinearIndices(A::AbstractArray)`,
indices.jl:1433): the indices `1:length(s)`, whose `first` and `last` are those of
`Base.OneTo(length(s))`. -/
instance : JLinearIndices (UnitRange JInt64) (OneTo JInt64) := ⟨fun s => do return ⟨← JLength.length s⟩⟩
/-- `round(Int, x::Float64)` (float.jl:456): round to the nearest integer, then convert to `Int`,
`InexactError` when it is not representable. -/
instance : JRoundTo JInt64 F64 := ⟨fun x => liftJl (JuliaLean.base.float.intOfFloat .i64 (round_Nearest_llvm x))⟩
/-- `_getindex_hiprec(r::StepRangeLen, i::Integer)`, range.jl:1105. -/
instance : JGetindexHiprec (StepRangeLen JInt64 JInt64 JInt64 JInt64) JInt64 JInt64 := ⟨_getindex_hiprec⟩
/-- `StepRangeLen{T}(ref, step, len, offset)`, range.jl:550. -/
instance : JStepRangeLenT JInt64 JInt64 JInt64 JInt64 JInt64 (StepRangeLen JInt64 JInt64 JInt64 JInt64) :=
  ⟨StepRangeLen_T⟩

/-- `getindex(r::StepRangeLen{T}, s::OrdinalRange{S})` (range.jl:1075), with `_getindex_hiprec`
(range.jl:1105): indexing an `Int` `StepRangeLen` `r` by an in-bounds nonempty `Int` unit range
`s = c:d` returns a range `w` of `length(s)` elements with `w[k] == r[s[k]]` for every `k` (the
indexing contract of the `getindex` docstring, "Return a subset of array `A` as selected by the
indices `inds`", abstractarray.jl; the `StepRangeLen` docstring, range.jl:512-531, describes `r[i]`
for every `1 <= i <= len`). -/
def SRLRangeIndex : Prop :=
  ∀ (ref step len off : JInt64) (r : StepRangeLen JInt64 JInt64 JInt64 JInt64) (c d : JInt64),
    StepRangeLen_ref_step ref step len off = .ok r → 1 ≤ c.val → c.val ≤ d.val → d.val ≤ len.val →
    ∃ w : StepRangeLen JInt64 JInt64 JInt64 JInt64,
      getindex_StepRangeLen_OrdinalRange r (⟨c, d⟩ : UnitRange JInt64) = .ok (.inr w) ∧
      (JLength.length w).map Subtype.val = .ok (d.val - c.val + 1) ∧
      ∀ k : JInt64, 1 ≤ k.val → k.val ≤ d.val - c.val + 1 →
        (JGetindex.getindex w k : JlX JInt64) = JGetindex.getindex r (lit .i64 (c.val + k.val - 1))

/-- `StepRangeLen(0, 1, typemax(Int), typemax(Int))[1:2]` throws `InexactError`: the closest
offset `round(Int, (r.offset - first(s))/step(s))` is computed in `Float64`, where
`typemax(Int) - 1` rounds to `2^63`, which `round(Int, ...)` cannot represent. -/
theorem srlRangeIndex_refuted : ¬ SRLRangeIndex := by
  intro h
  obtain ⟨w, hw, -⟩ := h (lit .i64 0) (lit .i64 1) (lit .i64 IntTy.i64.max) (lit .i64 IntTy.i64.max)
    ⟨lit .i64 0, lit .i64 1, lit .i64 IntTy.i64.max, lit .i64 IntTy.i64.max⟩ (lit .i64 1) (lit .i64 2)
    (by decide +kernel) (by decide) (by decide) (by decide)
  have hne : (getindex_StepRangeLen_OrdinalRange
      (⟨lit .i64 0, lit .i64 1, lit .i64 IntTy.i64.max, lit .i64 IntTy.i64.max⟩ :
        StepRangeLen JInt64 JInt64 JInt64 JInt64) (⟨lit .i64 1, lit .i64 2⟩ : UnitRange JInt64)).isOk = false := by
    decide +kernel
  rw [hw] at hne
  cases hne

/-- `getindex(r::LinRange{T}, s::OrdinalRange{S})` (range.jl:1110): indexing a `Float64`
`LinRange(a, b, n)` (range.jl:620, "a range with `len` linearly spaced elements between its
`start` and `stop`", LinRange docstring, range.jl:555) by an in-bounds nonempty `Int` unit range
`s = c:d` returns a `LinRange` `w` of `length(s)` elements whose first and last elements are
`r[c]` and `r[d]` (the indexing contract of the `getindex` docstring). Stated for every `Float64`
printer used in the error messages. -/
def LinRangeRangeIndex : Prop :=
  ∀ [JPrint F64] (a b : F64) (n : JInt64) (r : LinRange F64 JInt64) (c d : JInt64),
    LinRange_start_stop_len a b n = .ok r → 1 ≤ c.val → c.val ≤ d.val → d.val ≤ n.val →
    ∃ w : LinRange F64 JInt64,
      getindex_LinRange_OrdinalRange r (⟨c, d⟩ : UnitRange JInt64) = .ok w ∧
      (JLength.length w).map Subtype.val = .ok (d.val - c.val + 1) ∧
      JFirst.first w = JGetindex.getindex r c ∧ JLast.last w = JGetindex.getindex r d

/-- `LinRange(-Inf, Inf, 3)[2:2]` throws `ArgumentError` ("endpoints differ"), although `r[2]` is
`NaN`: the one-element result is built as `LinRange(r[2], r[2], 1)`, whose constructor requires
`start == stop`, and `NaN == NaN` is false. -/
theorem linRangeRangeIndex_refuted : ¬ LinRangeRangeIndex := by
  intro h
  letI : JPrint F64 := somePrintF64
  obtain ⟨w, hw, -⟩ := h (f64 18442240474082181120) (f64 9218868437227405312) (lit .i64 3)
    ⟨f64 18442240474082181120, f64 9218868437227405312, lit .i64 3, lit .i64 2⟩ (lit .i64 2) (lit .i64 2)
    (by decide +kernel) (by decide) (by decide) (by decide)
  have hne : (getindex_LinRange_OrdinalRange
      (⟨f64 18442240474082181120, f64 9218868437227405312, lit .i64 3, lit .i64 2⟩ : LinRange F64 JInt64)
      (⟨lit .i64 2, lit .i64 2⟩ : UnitRange JInt64)).isOk = false := by
    decide +kernel
  rw [hw] at hne
  cases hne

/-- The contract of `LinRangeRangeIndex` on ordinary inputs, whose indexed elements are numbers
(`r[c] == r[c]`, true for every element of a `LinRange` with finite endpoints): indexing a
`Float64` `LinRange(a, b, n)` by an in-bounds nonempty `Int` unit range `s = c:d` (range.jl:1110)
returns a `LinRange` `w` of `length(s)` elements whose first and last elements are `r[c]` and
`r[d]`. Stated for every `Float64` printer used in the error messages. -/
def LinRangeRangeIndexOrdinary : Prop :=
  ∀ [JPrint F64] (a b : F64) (n : JInt64) (r : LinRange F64 JInt64) (c d : JInt64),
    LinRange_start_stop_len a b n = .ok r → 1 ≤ c.val → c.val ≤ d.val → d.val ≤ n.val →
    (∀ x, JGetindex.getindex r c = .ok x → JEq.eq x x = true) →
    ∃ w : LinRange F64 JInt64,
      getindex_LinRange_OrdinalRange r (⟨c, d⟩ : UnitRange JInt64) = .ok w ∧
      (JLength.length w).map Subtype.val = .ok (d.val - c.val + 1) ∧
      JFirst.first w = JGetindex.getindex r c ∧ JLast.last w = JGetindex.getindex r d

theorem linRangeRangeIndexOrdinary_proven : LinRangeRangeIndexOrdinary := by
  intro _ a b n r c d hr hc hcd hd hnan
  obtain ⟨-, -, hn, hn0⟩ := linRange_ctor_fields a b n r hr
  have hmx := i64_max_val
  have hmn := i64_min_val
  have hus : unitStop c d = d := by simp [unitStop, hcd]
  have hlt : (lenTy IntTy.i64).max = IntTy.i64.max := rfl
  obtain ⟨m, hm, hmv⟩ := lengthUnit_fits c d (by unfold cnt; rw [if_pos hcd]; have := n.property; omega)
  rw [hus] at hm
  have hl' : (JLength.length (⟨c, d⟩ : UnitRange JInt64) : JlX JInt64) = .ok m := hm
  have hmv' : (m : JInt64).val = d.val - c.val + 1 := by
    show m.val = _; rw [hmv]; unfold cnt; rw [if_pos hcd]
  have hrlen : (JLength.length r : JlX JInt64) = .ok n := by
    simp [JLength.length, length_LinRange, hn, pure, Except.pure]
  have hgi : ∀ i : JInt64, 1 ≤ i.val → i.val ≤ n.val →
      (JGetindex.getindex r i : JlX F64) = JUnsafeGetindex.unsafeGetindex r i := by
    intro i h1 h2
    show _getindex_AbstractRange r i = _
    simp only [_getindex_AbstractRange, JCheckbounds.checkbounds, checkboundsVector_eq r i n hrlen hn0,
      checkboundsLinear, hrlen, bind, Except.bind, if_pos (And.intro h1 h2), pure, Except.pure]
  obtain ⟨x, hx⟩ : ∃ x, (JUnsafeGetindex.unsafeGetindex r c : JlX F64) = .ok x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, (JUnsafeGetindex.unsafeGetindex r d : JlX F64) = .ok y := ⟨_, rfl⟩
  have hgc := hgi c hc (by omega); rw [hx] at hgc
  have hgd := hgi d (by omega) hd; rw [hy] at hgd
  have h1 : (m : JInt64).val = 1 → JEq.eq x y = true := by
    intro h
    have hcd' : c = d := Subtype.ext (by omega)
    subst hcd'; rw [hx] at hy; cases hy; exact hnan x hgc
  obtain ⟨w, hw, hwf, hwl, hwn, -⟩ := (linRangeFloatConstruct_proven x y m).2.2 (by omega) h1
  have hcb : JCheckbounds.checkbounds r (⟨c, d⟩ : UnitRange JInt64) = .ok () := by
    show checkboundsVectorRange r _ = _
    rw [checkboundsVectorRange_eq r _ n hrlen hn0 false c d (by rw [isempty_unit]; simp; omega)
      (first_unit _) (last_unit _)]
    simp [show 1 ≤ c.val ∧ c.val ≤ n.val by omega, show 1 ≤ d.val ∧ d.val ≤ n.val by omega]
  refine ⟨w, ?_, ?_, by rw [hwf, hgc], by rw [hwl, hgd]⟩
  · unfold getindex_LinRange_OrdinalRange
    simp only [hcb, hl', bind, Except.bind, first_unit, last_unit, hx, hy]
    simp only [JType.isBool, dite_false, Bool.false_eq_true]
    exact hw
  · rw [hwn]; simp [Except.map, hmv']

end RangeIndexRange

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)
open JuliaLean.base.float (float_BitSigned64)

section Linspace
variable {t : IntTy}

/-- `first(r::LinRange) = r.start`, range.jl:870. -/
instance : JFirst (LinRange JInt64 JInt64) JInt64 := ⟨fun r => pure (first_LinRange r)⟩
/-- `last(r::LinRange) = r.stop`, range.jl:879. -/
instance : JLast (LinRange JInt64 JInt64) JInt64 := ⟨fun r => pure (last_LinRange r)⟩
/-- `LinRange{T}(start, stop, len)` (range.jl:616) with `T = Int` and `Int` endpoints and length. -/
instance : JLinRangeT JInt64 JInt64 JInt64 JInt64 (LinRange JInt64 JInt64) := ⟨LinRange_T⟩
/-- `LinRange{T}(start, stop, len)` (range.jl:616) with `T = Float64` and `Int` endpoints and
length. -/
instance [JPrint F64] : JLinRangeT F64 JInt64 JInt64 JInt64 (LinRange F64 JInt64) := ⟨LinRange_T⟩
/-- `LinRange(start, stop, len)` (range.jl:620) of `Int` endpoints and length: the element type
`typeof((zero(stop) - zero(start)) / oneunit(len))` is `Float64`. -/
instance [JPrint F64] : JLinRange3 JInt64 JInt64 JInt64 (LinRange F64 JInt64) := ⟨LinRange_start_stop_len⟩
/-- `float(T) = Float64` for every BitInteger type `T` (float.jl: `float(::Type{T}) where
{T<:Number} = typeof(float(zero(T)))` with `AbstractFloat(x::BitInteger) = Float64(x)`). -/
instance : JFloatType (JInt t) F64 := ⟨⟩
/-- `range_start_stop_length(start::T, stop::T, len::Integer) where {T<:Integer}`, range.jl:628. -/
instance (priority := high) {ρ : Type} [JLinspace F64 (JInt t) (JInt t) JInt64 ρ] :
    JRangeStartStopLength (JInt t) (JInt t) JInt64 ρ := ⟨range_start_stop_length_Integer⟩
/-- `range_start_stop_length(start, stop, len::Integer)` (range.jl:625) for endpoints of two
BitInteger types. -/
instance (priority := low) {s u : IntTy} {ρ : Type}
    [JRangeStartStopLength (JInt (pTy s u)) (JInt (pTy s u)) JInt64 ρ] :
    JRangeStartStopLength (JInt s) (JInt u) JInt64 ρ := ⟨range_start_stop_length_Any⟩
/-- `_range(start::Any, step::Nothing, stop::Any, len::Any) = range_start_stop_length(start, stop,
len)`, range.jl:186. -/
instance {s u : IntTy} {ρ : Type} [JRangeStartStopLength (JInt s) (JInt u) JInt64 ρ] :
    JRangeImpl (JInt s) Nothing (JInt u) JInt64 ρ := ⟨_range_A_N_A_A⟩

/-- `_linspace(::Type{T}, start::Integer, stop::Integer, len::Integer) where T =
LinRange{T}(start, stop, len)` (range.jl:632, the fallback for element types other than `Float16`,
`Float32`, `Float64`) with `T = Int`, through `LinRange{T}` (range.jl:616) and the inner
constructor (range.jl:597-611). The LinRange docstring (range.jl:555) promises "a range with `len`
linearly spaced elements between its `start` and `stop`"; the constructor throws `ArgumentError`
for a negative length, for length 1 with `start != stop`, and when an integer `LinRange` would have
a non-integer step `(stop - start)/(len - 1)`; otherwise `first(r) == start`, `last(r) == stop` and
`length(r) == len`. -/
def LinspaceIntGeneric : Prop :=
  ∀ (a b n : JInt64),
    (n.val < 0 → ∃ m, (_linspace JInt64 a b n : JlX (LinRange JInt64 JInt64)) =
      .error (.jl (.argumentError m))) ∧
    (n.val = 1 → a.val ≠ b.val → ∃ m, (_linspace JInt64 a b n : JlX (LinRange JInt64 JInt64)) =
      .error (.jl (.argumentError m))) ∧
    (2 ≤ n.val → ¬ (n.val - 1 ∣ b.val - a.val) → ∃ m,
      (_linspace JInt64 a b n : JlX (LinRange JInt64 JInt64)) = .error (.jl (.argumentError m))) ∧
    (0 ≤ n.val → (n.val = 1 → a.val = b.val) → (2 ≤ n.val → n.val - 1 ∣ b.val - a.val) →
      ∃ r : LinRange JInt64 JInt64, _linspace JInt64 a b n = .ok r ∧ JFirst.first r = .ok a ∧
        JLast.last r = .ok b ∧ JLength.length r = .ok n)

/-- `LinRange{Int}(typemin(Int), typemax(Int), 4)` (and `_linspace(Int, ...)`) throws "LinRange{<:Integer}
cannot have non-integer step", although the step `(2^64 - 1)/3 = 6148914691236517205` is an integer:
the constructor tests `mod(stop - start, len - 1)`, and `stop - start` wraps to `-1`. -/
theorem linspaceIntGeneric_refuted : ¬ LinspaceIntGeneric := by
  intro h
  obtain ⟨r, hr, -⟩ := (h (lit .i64 IntTy.i64.min) (lit .i64 IntTy.i64.max) (lit .i64 4)).2.2.2
    (by decide) (by decide) (by decide)
  have hne : (_linspace JInt64 (lit .i64 IntTy.i64.min) (lit .i64 IntTy.i64.max) (lit .i64 4) :
      JlX (LinRange JInt64 JInt64)).isOk = false := by
    decide +kernel
  rw [hr] at hne
  cases hne

/-- The contract of `LinspaceIntGeneric` on ordinary inputs, whose difference `stop - start` is an
`Int`. -/
def LinspaceIntGenericOrdinary : Prop :=
  ∀ (a b n : JInt64), InT .i64 (b.val - a.val) →
    (n.val < 0 → ∃ m, (_linspace JInt64 a b n : JlX (LinRange JInt64 JInt64)) =
      .error (.jl (.argumentError m))) ∧
    (n.val = 1 → a.val ≠ b.val → ∃ m, (_linspace JInt64 a b n : JlX (LinRange JInt64 JInt64)) =
      .error (.jl (.argumentError m))) ∧
    (2 ≤ n.val → ¬ (n.val - 1 ∣ b.val - a.val) → ∃ m,
      (_linspace JInt64 a b n : JlX (LinRange JInt64 JInt64)) = .error (.jl (.argumentError m))) ∧
    (0 ≤ n.val → (n.val = 1 → a.val = b.val) → (2 ≤ n.val → n.val - 1 ∣ b.val - a.val) →
      ∃ r : LinRange JInt64 JInt64, _linspace JInt64 a b n = .ok r ∧ JFirst.first r = .ok a ∧
        JLast.last r = .ok b ∧ JLength.length r = .ok n)

theorem linspaceIntGenericOrdinary_proven : LinspaceIntGenericOrdinary := by
  intro a b n hd
  have hmx := i64_max_val
  have hmn := i64_min_val
  have hsub : (b - a : JInt64).val = b.val - a.val := by rw [sub_iv]; exact wrap_in .i64 hd.1 hd.2
  have hev : ∀ (x : JInt64), (JIszero.iszero x) = decide (x.val = 0) := by
    intro x
    show JEq.eq x (lit .i64 0) = _
    rw [eq_iv, show (lit .i64 0 : JInt64).val = 0 by decide]
  have hred : ∀ x y m : JInt64, (_linspace JInt64 x y m : JlX (LinRange JInt64 JInt64)) =
      LinRange_TL_new x y m := fun _ _ _ => rfl
  have h1v : (JOneunit.oneunit : JInt64).val = 1 := by decide
  have hm1' : 0 ≤ n.val → (n - JOneunit.oneunit : JInt64).val = n.val - 1 := by
    intro h; rw [sub_iv, h1v]; exact wrap_in .i64 (by have := n.property; omega) (by have := n.property; omega)
  refine ⟨fun hn => ?_, fun hn hab => ?_, fun hn hnd => ?_, fun h0 h1 h2 => ?_⟩
  · rw [hred]
    simp [LinRange_TL_new, le_iv, jint0_val, show ¬ (0 ≤ n.val) by omega, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]
  · rw [hred]
    simp [LinRange_TL_new, le_iv, jint0_val, eq_iv, h1v, hn, hab, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind, pure, Except.pure]
  · rw [hred]
    have hm1 := hm1' (by omega)
    obtain ⟨ld, hld, hldv⟩ : ∃ ld : JInt64, (JMax.max (n - JOneunit.oneunit) (JOneunit.oneunit : JInt64) :
        JlX JInt64) = .ok ld ∧ ld.val = max (n.val - 1) 1 := by
      rw [max_same]; refine ⟨_, rfl, ?_⟩; split <;> rename_i h <;> simp only [hm1, h1v] at h ⊢ <;> omega
    have hmod := mod_iv (b - a) ld (by omega)
    have hz : Int.fmod (b - a : JInt64).val ld.val ≠ 0 := by
      rw [hsub, hldv, Int.fmod_eq_emod, if_pos (Or.inl (by omega)), Int.add_zero]
      intro h; exact hnd (by rw [show n.val - 1 = max (n.val - 1) 1 by omega]; exact Int.dvd_of_emod_eq_zero h)
    simp only [LinRange_TL_new, le_iv, jint0_val, eq_iv, h1v, show n.val ≠ 1 by omega,
      show 0 ≤ n.val by omega, hld, hmod, hev, hz, JType.isInteger, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind, pure, Except.pure, decide_true, decide_false, Bool.not_false, Bool.and_self,
      ite_true, ite_false, Bool.not_true, Bool.true_and, Bool.false_eq_true]
    exact ⟨_, rfl⟩
  · rw [hred]
    have hm1 := hm1' h0
    by_cases hn1 : n.val = 1
    · refine ⟨⟨a, b, n, n⟩, ?_, rfl, rfl, rfl⟩
      simp [LinRange_TL_new, le_iv, jint0_val, eq_iv, h1v, hn1, h1 hn1, bind, Except.bind, pure, Except.pure]
    obtain ⟨ld, hld, hldv⟩ : ∃ ld : JInt64, (JMax.max (n - JOneunit.oneunit) (JOneunit.oneunit : JInt64) :
        JlX JInt64) = .ok ld ∧ ld.val = max (n.val - 1) 1 := by
      rw [max_same]; refine ⟨_, rfl, ?_⟩; split <;> rename_i h <;> simp only [hm1, h1v] at h ⊢ <;> omega
    have hmod := mod_iv (b - a) ld (by omega)
    have hz : Int.fmod (b - a : JInt64).val ld.val = 0 := by
      rw [hsub, hldv, Int.fmod_eq_emod, if_pos (Or.inl (by omega)), Int.add_zero]
      by_cases hn0 : n.val = 0
      · rw [show max (n.val - 1) 1 = 1 by omega]; exact Int.emod_one _
      · exact Int.emod_eq_zero_of_dvd (by rw [show max (n.val - 1) 1 = n.val - 1 by omega]; exact h2 (by omega))
    refine ⟨⟨a, b, n, ld⟩, ?_, rfl, rfl, rfl⟩
    simp only [LinRange_TL_new, le_iv, jint0_val, eq_iv, h1v, hn1, h0, hld, hmod, hev, hz,
      JType.isInteger, bind, Except.bind, pure, Except.pure, decide_true, decide_false, ite_true, ite_false,
      Bool.not_true, Bool.and_false, Bool.false_eq_true]

/-- `range_start_stop_length(start::T, stop::T, len::Integer) where {T} = LinRange(start, stop, len)`
(range.jl:627, the method for endpoint types that are neither `Integer` nor IEEE floats), called with
`Int` endpoints (Julia reaches it with `invoke`): it is `LinRange(start, stop, len)` (range.jl:620),
whose element type `typeof((zero(stop) - zero(start)) / oneunit(len))` is `Float64`. It throws
`ArgumentError` for a negative length and for length 1 with `Float64(start) != Float64(stop)`;
otherwise the result has first element `Float64(start)`, last element `Float64(stop)` and length
`len` (LinRange docstring, range.jl:555). Stated for every `Float64` printer used in the error
messages. -/
def RangeStartStopLengthGeneric : Prop :=
  ∀ [JPrint F64] (a b n : JInt64),
    (n.val < 0 → ∃ m, (range_start_stop_length_T a b n : JlX (LinRange F64 JInt64)) =
      .error (.jl (.argumentError m))) ∧
    (n.val = 1 → JEq.eq (float_BitSigned64 .f64 a : F64) (float_BitSigned64 .f64 b) = false → ∃ m,
      (range_start_stop_length_T a b n : JlX (LinRange F64 JInt64)) = .error (.jl (.argumentError m))) ∧
    (0 ≤ n.val → (n.val = 1 → JEq.eq (float_BitSigned64 .f64 a : F64) (float_BitSigned64 .f64 b) = true) →
      ∃ r : LinRange F64 JInt64, range_start_stop_length_T a b n = .ok r ∧
        JFirst.first r = .ok (float_BitSigned64 .f64 a) ∧ JLast.last r = .ok (float_BitSigned64 .f64 b) ∧
        JLength.length r = .ok n)

theorem rangeStartStopLengthGeneric_proven : RangeStartStopLengthGeneric := by
  intro _ a b n
  have hred : (range_start_stop_length_T a b n : JlX (LinRange F64 JInt64)) =
      LinRange_start_stop_len (float_BitSigned64 .f64 a : F64) (float_BitSigned64 .f64 b) n := by
    simp only [range_start_stop_length_T, JLinRange3.linRange, LinRange_start_stop_len,
      JLinRangeT.linRangeT, LinRange_T, JLinRangeTL.linRangeTL, LinRange_TL, convert_self, bind, Except.bind]
    rfl
  have h := linRangeFloatConstruct_proven (float_BitSigned64 .f64 a : F64) (float_BitSigned64 .f64 b) n
  rw [hred]
  exact ⟨h.1, h.2.1, fun h0 h1 => by
    obtain ⟨r, hr, hf, hl, hn, -⟩ := h.2.2 h0 h1
    exact ⟨r, hr, hf, hl, hn⟩⟩

/-- `range(start, stop, length::Integer)` (range.jl:170) of BitInteger endpoints, through
`_range(start, nothing, stop, len)` (range.jl:186), `range_start_stop_length(start, stop, len)`
(range.jl:625, which promotes endpoints of two types) and `range_start_stop_length(start::T,
stop::T, len::Integer) where {T<:Integer} = _linspace(float(T), start, stop, len)` (range.jl:628).
The callee `_linspace(::Type{Float64}, start::Integer, stop::Integer, len::Integer)` is defined in
twiceprecision.jl:717; it is a typed parameter here, with the length law of the `range` docstring
("`range(start, stop, length)`": a range with `length` elements) as its only hypothesis. Then for
endpoints of one type `T` (any width), `range(a, b, n)` is `_linspace(Float64, a, b, n)` (the element
type `float(T)` is `Float64` for every BitInteger) and has `n` elements whenever it returns; for
endpoints of two types it is `_linspace(Float64, a', b', n)` with `a'`, `b'` the values of `a`, `b` in
`promote_type`, and has `n` elements, or throws `InexactError` when a value is not representable in
`promote_type` (the `promote` docstring). -/
def RangeIntLength : Prop :=
  ∀ (ρ : Type) [JLength ρ JInt64] [∀ t : IntTy, JLinspace F64 (JInt t) (JInt t) JInt64 ρ],
    (∀ (t : IntTy) (a b : JInt t) (n : JInt64) (r : ρ),
      JLinspace.linspace (T := F64) a b n = .ok r → JLength.length r = .ok n) →
    (∀ (t : IntTy) (a b : JInt t) (n : JInt64) (r : ρ), range_start_stop_length3 a b n = .ok r →
      JLength.length r = .ok n ∧ JLinspace.linspace (T := F64) a b n = .ok r) ∧
    (∀ (s u : IntTy) (a : JInt s) (b : JInt u) (n : JInt64), s ≠ u →
      (InT (pTy s u) a.val → InT (pTy s u) b.val → ∀ r : ρ, range_start_stop_length3 a b n = .ok r →
        JLength.length r = .ok n ∧ ∃ a' b' : JInt (pTy s u), a'.val = a.val ∧ b'.val = b.val ∧
          JLinspace.linspace (T := F64) a' b' n = .ok r) ∧
      (¬ (InT (pTy s u) a.val ∧ InT (pTy s u) b.val) →
        ∃ m, (range_start_stop_length3 a b n : JlX ρ) = .error (.jl (.inexactError m))))

theorem rangeIntLength_proven : RangeIntLength := by
  intro ρ _ _ law
  refine ⟨fun t a b n r h => ?_, fun s u a b n _ => ⟨fun ha hb r h => ?_, fun hn => ?_⟩⟩
  · have hr : (range_start_stop_length3 a b n : JlX ρ) = JLinspace.linspace (T := F64) a b n := rfl
    rw [hr] at h
    exact ⟨law t a b n r h, h⟩
  · have hr : (range_start_stop_length3 a b n : JlX ρ) =
        (do let p ← (JPromote2.promote a b : JlX (JInt (pTy s u) × JInt (pTy s u)))
            JLinspace.linspace (T := F64) p.1 p.2 n) := rfl
    rw [hr, promote_iv, dif_pos (And.intro ha hb)] at h
    exact ⟨law _ _ _ n r h, ⟨a.val, ha⟩, ⟨b.val, hb⟩, rfl, rfl, h⟩
  · have hr : (range_start_stop_length3 a b n : JlX ρ) =
        (do let p ← (JPromote2.promote a b : JlX (JInt (pTy s u) × JInt (pTy s u)))
            JLinspace.linspace (T := F64) p.1 p.2 n) := rfl
    rw [hr, promote_iv, dif_neg hn]
    exact ⟨_, rfl⟩

/-- `range_start_stop_length` and `_linspace` dispatch (range.jl:625-632): `range(a, b; length=n)`
of BitInteger endpoints (`RangeIntLength`), the generic method for other endpoint types
(`RangeStartStopLengthGeneric`) and the generic integer `_linspace` on ordinary inputs
(`LinspaceIntGenericOrdinary`) each return a range of `n` elements whenever they return. -/
def StartStopLengthDispatch : Prop :=
  RangeIntLength ∧ RangeStartStopLengthGeneric ∧ LinspaceIntGenericOrdinary

theorem startStopLengthDispatch_proven : StartStopLengthDispatch :=
  ⟨rangeIntLength_proven, rangeStartStopLengthGeneric_proven, linspaceIntGenericOrdinary_proven⟩

end Linspace

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

/-! ## Intersection of two integer `StepRangeLen`s (the generic range method) -/

section IntersectGeneric
variable {t : IntTy}

/-- An integer `StepRangeLen{T,T,T,Int}`, as built by `StepRangeLen(ref, step, len, offset)`. -/
abbrev SRLI (t : IntTy) := StepRangeLen (JInt t) (JInt t) (JInt t) JInt64

/-- `minimum(r::AbstractRange)`, range.jl:883, of an integer `StepRangeLen`. -/
instance : JMinimum (SRLI t) (JInt t) := ⟨minimum_AbstractRange⟩
/-- `maximum(r::AbstractRange)`, range.jl:884, of an integer `StepRangeLen`. -/
instance : JMaximum (SRLI t) (JInt t) := ⟨maximum_AbstractRange⟩
/-- `x in r` for a BitInteger `x` and an integer `StepRangeLen` `r` of the same type: Julia selects
`in(x::Real, r::AbstractRange{T}) where {T<:Integer}`, range.jl:1491. -/
instance : JIn (JInt t) (SRLI t) := ⟨in_Real_AbstractRange_Integer⟩

/-- `intersect(r1, r2)` of two integer `StepRangeLen`s of one type: Julia selects
`intersect(r1::AbstractRange, r2::AbstractRange)` (range.jl:1277), and its call
`intersect(r2, r1)` with the arguments swapped selects the same method again. `depth` bounds that
recursion; the method's vector `T[x for x in r1 if x ∈ r2]` is the result at either level.
`unique` (set.jl:262) is the instance parameter. -/
def intersectSRL [JUnique (SRLI t) (SRLI t)] (fuel : Nat) :
    Nat → SRLI t → SRLI t → JlX (List (JInt t))
  | 0, _, _ => throw (.errorException "fuel")
  | d + 1, r1, r2 =>
    letI : JIntersect (SRLI t) (SRLI t) (List (JInt t)) := ⟨intersectSRL fuel d⟩
    do
      match ← intersect_AbstractRange_AbstractRange (T := JInt t) r1 r2 fuel with
      | .inl xs => pure xs
      | .inr xs => pure xs

/-- The values `ref + (i - offset) * step`, `i = 1, ..., len`, of the elements of
`StepRangeLen(ref, step, len, offset)` (StepRangeLen docstring, range.jl:512-531). -/
def srlVals (ref step : JInt t) (len off : JInt64) : List Int :=
  (List.range len.val.toNat).map fun k : Nat => srlE ref step off ((k : Int) + 1)

theorem map_val_ok {x : JlX (JInt t)} {v : Int} (h : x.map Subtype.val = .ok v) :
    ∃ y : JInt t, x = .ok y ∧ y.val = v := by
  cases x with
  | error e => simp [Except.map] at h
  | ok y => simp only [Except.map, Except.ok.injEq] at h; exact ⟨y, rfl, h⟩

/-- Iterating an integer `StepRangeLen` from the state `k` visits the elements `k+1, ..., n`. -/
theorem iterFrom_srl (r : SRLI t) (n : Int) (f : Int → Int)
    (hit : ∀ k : JInt64, 0 ≤ k.val → k.val < n →
      (JIterate2.iterate r k).map (Option.map fun p => (p.1.val, p.2.val)) =
        .ok (some (f (k.val + 1), k.val + 1)))
    (hend : ∀ k : JInt64, k.val = n → JIterate2.iterate r k = .ok none) :
    ∀ (fuel : Nat) (k : JInt64), 0 ≤ k.val → k.val ≤ n → n - k.val < fuel →
      (iterFrom r fuel k).map vals =
        .ok ((List.range (n - k.val).toNat).map fun j : Nat => f (k.val + 1 + j))
  | 0, k, _, _, hf => by omega
  | fuel + 1, k, h0, hn, hf => by
    by_cases heq : k.val = n
    · simp [iterFrom, hend k heq, bind, Except.bind, pure, Except.pure, Except.map,
        show (n - k.val).toNat = 0 by omega]
    · have h := hit k h0 (by omega)
      cases hi : JIterate2.iterate r k with
      | error e => rw [hi] at h; simp [Except.map] at h
      | ok o =>
        rw [hi] at h
        cases o with
        | none => simp [Except.map] at h
        | some p =>
          obtain ⟨x, k'⟩ := p
          simp only [Except.map, Option.map, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hx, hk'⟩ := h
          have ih := iterFrom_srl r n f hit hend fuel k' (by omega) (by omega) (by omega)
          simp only [iterFrom, hi, bind, Except.bind]
          rw [show (n - k.val).toNat = (n - k'.val).toNat + 1 by omega, List.range_succ_eq_map]
          revert ih
          cases iterFrom r fuel k' <;> simp [Except.map, pure, Except.pure, hx, List.map_map]
          intro h; rw [h]; apply List.map_congr_left; intro j _
          (try simp only [Function.comp_apply, Nat.succ_eq_add_one])
          congr 1; (try push_cast); omega

/-- The facts of `StepRangeLen(ref, step, len, offset)` with representable elements that the
intersection needs: its length, emptiness, step, first and last values, iteration and membership
of any `x`. -/
theorem srl_world (ref st : JInt t) (n o : JInt64) (r : SRLI t)
    (hr : StepRangeLen_ref_step ref st n o = .ok r)
    (hv : ∀ i : Int, 1 ≤ i → i ≤ n.val → InT t (srlE ref st o i)) (hmax : n.val < IntTy.i64.max) :
    0 ≤ n.val ∧ JLength.length r = .ok n ∧
      (∀ fuel : Nat, n.val ≤ fuel → ∃ xs, iterList r fuel = .ok xs ∧ vals xs = srlVals ref st n o) ∧
      (∀ x : JInt t, (JIn.isIn x r : JlX Bool) = .ok (decide (x.val ∈ srlVals ref st n o))) := by
  have hl := i64_bounds n; have ho := i64_bounds o
  have hok := srl_ctor ref st n o
  have h0 : 0 ≤ n.val := by
    by_cases h : 0 ≤ n.val
    · exact h
    · rw [if_neg h] at hok; rw [hok] at hr; cases hr
  have h1 : 1 ≤ o.val ∧ o.val ≤ max 1 n.val := by
    by_cases h : 1 ≤ o.val ∧ o.val ≤ max 1 n.val
    · exact h
    · rw [if_pos h0, if_neg h] at hok; rw [hok] at hr; cases hr
  obtain ⟨r', hr', -, -, hlen, hemp, -, hstep, -, -, hfirst, hlast, -, hit2, hend⟩ :=
    (sRLIntConstruct_proven t ref st n o).2.2 h0 h1.1 h1.2
  have hrr : r' = r := by rw [hr'] at hr; cases hr; rfl
  subst hrr
  refine ⟨h0, hlen, ?_, ?_⟩
  · -- iteration
    intro fuel hf
    have hI : ∀ k : JInt64, 0 ≤ k.val → k.val < n.val →
        (JIterate2.iterate r' k).map (Option.map fun p => (p.1.val, p.2.val)) =
          .ok (some (srlE ref st o (k.val + 1), k.val + 1)) :=
      fun k hk0 hk1 => hit2 k hk0 hk1 (hv _ (by omega) (by omega))
    have hE : ∀ k : JInt64, k.val = n.val → JIterate2.iterate r' k = .ok none := by
      intro k hk; have : k = n := Subtype.ext hk; subst this; exact hend hmax
    have h1eq : (JIterate1.iterate r' : JlX (Option (JInt t × JInt64))) =
        JIterate2.iterate r' (JZero.zero : JInt64) := rfl
    have hz : (JZero.zero : JInt64).val = 0 := zero_iv
    unfold iterList
    rw [h1eq]
    by_cases hn0 : n.val = 0
    · rw [hE (JZero.zero : JInt64) (by omega)]
      refine ⟨[], rfl, ?_⟩
      simp [srlVals, hn0]
    · have h := hI (JZero.zero : JInt64) (by omega) (by omega)
      cases hi : JIterate2.iterate r' (JZero.zero : JInt64) with
      | error e => rw [hi] at h; simp [Except.map] at h
      | ok oo =>
        rw [hi] at h
        cases oo with
        | none => simp [Except.map] at h
        | some p =>
          obtain ⟨x, k'⟩ := p
          simp only [Except.map, Option.map, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq,
            hz, Int.zero_add] at h
          obtain ⟨hx, hk'⟩ := h
          have ih := iterFrom_srl r' n.val (srlE ref st o) hI hE fuel k' (by omega) (by omega)
            (by omega)
          simp only [bind, Except.bind]
          cases hr2 : iterFrom r' fuel k' with
          | error e => rw [hr2] at ih; simp [Except.map] at ih
          | ok ys =>
            have ih' : vals ys = (List.range (n.val - k'.val).toNat).map
                fun j : Nat => srlE ref st o (k'.val + 1 + j) := by
              rw [hr2] at ih; simpa [Except.map] using ih
            refine ⟨x :: ys, rfl, ?_⟩
            show x.val :: vals ys = _
            rw [ih', hx, hk']
            unfold srlVals
            rw [show n.val.toNat = (n.val - 1).toNat + 1 by omega, List.range_succ_eq_map]
            simp only [List.map_cons, List.map_map]
            congr 1
            all_goals first
              | (simp; done)
              | (apply List.map_congr_left; intro j _
                 (try simp only [Function.comp_apply, Nat.succ_eq_add_one])
                 congr 1; (try push_cast); omega)
  · -- membership: `in(x::Real, r::AbstractRange{T}) where {T<:Integer}`
    intro x
    have hemp' : JIsempty.isempty r' = .ok (decide (n.val = 0)) := hemp
    by_cases hn0 : n.val = 0
    · have hnil : srlVals ref st n o = [] := by simp [srlVals, hn0]
      simp [JIn.isIn, in_Real_AbstractRange_Integer, JIsinteger.isinteger,
        JuliaLean.base.number.isintegerInteger, hemp', hn0, hnil, bind, Except.bind, pure,
        Except.pure]
    obtain ⟨f, hf, hfv⟩ := map_val_ok (hfirst (by omega) (hv 1 (by omega) (by omega)))
    obtain ⟨l, hl', hlv⟩ := map_val_ok (hlast (by omega) (hv n.val (by omega) (by omega)))
    have hst : (JStep.step r' : JlX (JInt t)) = .ok st := hstep
    have hne : decide (n.val = 0) = false := by simp [hn0]
    -- the element list is the arithmetic sequence `f, f + st, ..., l`
    have hseq : ∀ k : Nat, srlE ref st o ((k : Int) + 1) = f.val + k * st.val := by
      intro k; rw [hfv]; simp only [srlE]; rw [Int.sub_mul, Int.sub_mul, Int.add_mul]; omega
    have hlf : l.val = f.val + (n.val - 1) * st.val := by
      rw [hlv, hfv]; simp only [srlE]; rw [Int.sub_mul, Int.sub_mul, Int.sub_mul]; omega
    by_cases hs0 : st.val = 0
    · have hz : JIszero.iszero st = true := by rw [iszero_iv]; simp [hs0]
      have hmem : x.val ∈ srlVals ref st n o ↔ x.val = f.val := by
        unfold srlVals
        simp only [List.mem_map, List.mem_range, hseq, hs0, Int.mul_zero, Int.add_zero]
        constructor
        · rintro ⟨k, -, h⟩; exact h.symm
        · intro h; exact ⟨0, by omega, h.symm⟩
      simp only [JIn.isIn, in_Real_AbstractRange_Integer, JIsinteger.isinteger,
        JuliaLean.base.number.isintegerInteger, Bool.not_true, Bool.false_eq_true, ite_false,
        hemp', hne, hst, hz, ite_true, hf, eq_iv, bind, Except.bind, pure, Except.pure]
      congr 1
      exact (decide_eq_decide).mpr hmem.symm
    · have hz : JIszero.iszero st = false := by rw [iszero_iv]; simp [hs0]
      have hmin : (JMinimum.minimum r' : JlX (JInt t)) = .ok (if l.val < f.val then l else f) := by
        show minimum_AbstractRange r' = _
        simp only [minimum_AbstractRange, hemp', hne, hf, hl', Bool.false_eq_true, ite_false, bind,
          Except.bind]
        exact min_same f l
      have hmaxe : (JMaximum.maximum r' : JlX (JInt t)) = .ok (if l.val < f.val then f else l) := by
        show maximum_AbstractRange r' = _
        simp only [maximum_AbstractRange, hemp', hne, hf, hl', Bool.false_eq_true, ite_false, bind,
          Except.bind]
        exact max_same f l
      -- `srlVals` is the step list `f:st:l`
      have hcount : stepCount f.val st.val (f.val + (n.val - 1) * st.val) = n.val := by
        rw [stepCount_mul f.val st.val (n.val - 1) hs0 (by omega)]; omega
      have hsv : srlVals ref st n o = stepInts f.val st.val (f.val + (n.val - 1) * st.val) := by
        unfold srlVals stepInts
        rw [hcount]
        apply List.map_congr_left; intro k _; exact hseq k
      have hmem := mem_stepInts_fmod f.val st.val (f.val + (n.val - 1) * st.val) x.val hs0
        (by rw [hcount]; omega)
      rw [← hsv, hcount, ← hlf] at hmem
      simp only [JIn.isIn, in_Real_AbstractRange_Integer, JIsinteger.isinteger,
        JuliaLean.base.number.isintegerInteger, Bool.not_true, Bool.false_eq_true, ite_false,
        hemp', hne, hst, hz, hf, hmin, hmaxe, bind, Except.bind, pure, Except.pure, le_iv]
      by_cases hlo : (if l.val < f.val then l else f).val ≤ x.val
      · by_cases hhi : x.val ≤ (if l.val < f.val then f else l).val
        · simp only [hlo, hhi, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
            convert_self]
          simp only [mod_iv _ st hs0, eq_iv, sub_iv, jint0_val]
          have hb := JuliaLean.Proofs.base.int.fmod_bounds x.val st.val hs0
          have hb' := JuliaLean.Proofs.base.int.fmod_bounds f.val st.val hs0
          have hmz := min_le_zero t; have hmx := zero_lt_max t
          have hsp := st.property
          have hw := wrap_eq_zero_iff t (x.val.fmod st.val - f.val.fmod st.val)
            (by rcases Int.lt_or_gt_of_ne hs0 with h | h
                · have := hb.2 h; have := hb'.2 h; omega
                · have := hb.1 h; have := hb'.1 h; omega)
            (by rcases Int.lt_or_gt_of_ne hs0 with h | h
                · have := hb.2 h; have := hb'.2 h; omega
                · have := hb.1 h; have := hb'.1 h; omega)
          have hite1 : (if l.val < f.val then l else f).val = (if l.val < f.val then l.val else f.val) := by
            split <;> rfl
          have hite2 : (if l.val < f.val then f else l).val = (if l.val < f.val then f.val else l.val) := by
            split <;> rfl
          rw [hite1] at hlo; rw [hite2] at hhi
          congr 1
          apply bool_eq_decide
          rw [decide_eq_true_iff, hw, hmem]
          constructor
          · intro h; exact ⟨hlo, hhi, by omega⟩
          · rintro ⟨-, -, h⟩; omega
        · simp only [hlo, hhi, decide_true, decide_false, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, ite_false, ite_true, Except.ok.injEq]
          symm; rw [decide_eq_false_iff_not, hmem]
          rintro ⟨-, h2, -⟩; apply hhi; split <;> split at h2 <;> simp_all <;> omega
      · simp only [hlo, decide_false, Bool.not_false, ite_true, Except.ok.injEq]
        symm; rw [decide_eq_false_iff_not, hmem]
        rintro ⟨h1, -, -⟩; apply hlo; split <;> split at h1 <;> simp_all <;> omega

/-- A loop that appends each element satisfying a test keeps exactly those elements. -/
theorem foldlM_filter {E : Type} (f : List E → E → JlX (List E)) (b : E → Bool)
    (hf : ∀ acc x, f acc x = .ok (if b x then acc ++ [x] else acc)) :
    ∀ (ys acc : List E), ys.foldlM f acc = .ok (acc ++ ys.filter b)
  | [], acc => by simp [pure, Except.pure]
  | y :: ys, acc => by
    rw [List.foldlM_cons, hf acc y]
    show List.foldlM f (if b y then acc ++ [y] else acc) ys = _
    rw [foldlM_filter f b hf ys]
    by_cases hb : b y <;> simp [hb, List.filter_cons]

/-- `intersect(r1, r2)` of two `StepRangeLen`s of one BitInteger type. The `intersect` docstring
(abstractset.jl:118): "Construct the set containing those elements which appear in all of the
arguments." Julia selects `intersect(r1::AbstractRange, r2::AbstractRange)` (range.jl:1277), which
returns a `Vector`; its comment (range.jl:1278) "To iterate over the shorter range" fixes the order:
the result lists each common value once, in the order of the shorter range (the first range when
the lengths are equal). `unique` (set.jl:262, a later file) is a parameter satisfying its
docstring on these ranges ("Return an array containing only the unique elements of collection `itr`
... in the order that the first of each set of equivalent elements originally appears"): no
duplicates, the same elements, in their original order. Hypotheses: every element value
`ref + (i - offset) * step` is representable in `T` (no wraparound), the lengths are below
`typemax(Int)` (see `range-srl-iterate-typemax`), and the loop fuel covers the lengths. -/
def IntersectRangesGeneric : Prop :=
  ∀ (t : IntTy) [JUnique (SRLI t) (SRLI t)] (ref1 st1 ref2 st2 : JInt t) (n1 o1 n2 o2 : JInt64)
    (r1 r2 : SRLI t) (fuel : Nat),
    StepRangeLen_ref_step ref1 st1 n1 o1 = .ok r1 → StepRangeLen_ref_step ref2 st2 n2 o2 = .ok r2 →
    (∀ i : Int, 1 ≤ i → i ≤ n1.val → InT t (srlE ref1 st1 o1 i)) →
    (∀ i : Int, 1 ≤ i → i ≤ n2.val → InT t (srlE ref2 st2 o2 i)) →
    n1.val < IntTy.i64.max → n2.val < IntTy.i64.max → n1.val ≤ fuel → n2.val ≤ fuel →
    (∀ r ∈ [r1, r2], ∀ xs, iterList r fuel = .ok xs → ∃ u ys, JUnique.unique r = .ok u ∧
      iterList u fuel = .ok ys ∧ (vals ys).Nodup ∧ (∀ x, x ∈ ys ↔ x ∈ xs) ∧ ys.Sublist xs) →
    ∃ out, intersectSRL fuel 2 r1 r2 = .ok out ∧ (vals out).Nodup ∧
      (∀ x : Int, x ∈ vals out ↔ x ∈ srlVals ref1 st1 n1 o1 ∧ x ∈ srlVals ref2 st2 n2 o2) ∧
      (vals out).Sublist (if n2.val < n1.val then srlVals ref2 st2 n2 o2 else srlVals ref1 st1 n1 o1)

/-- One level of `intersect(r1::AbstractRange, r2::AbstractRange)` when `r1` is not longer than
`r2`: the elements of `unique(r1)` that are in `r2`. -/
theorem intersect_level [JUnique (SRLI t) (SRLI t)] (fuel d : Nat) (p q : SRLI t) (np nq : JInt64)
    (ep eq : List Int) (hp : JLength.length p = .ok np) (hq : JLength.length q = .ok nq)
    (hle : ¬ nq.val < np.val)
    (hin : ∀ x : JInt t, (JIn.isIn x q : JlX Bool) = .ok (decide (x.val ∈ eq)))
    (u : SRLI t) (ys : List (JInt t)) (hu : JUnique.unique p = .ok u) (hys : iterList u fuel = .ok ys) :
    intersectSRL fuel (d + 1) p q = .ok (ys.filter fun x => decide (x.val ∈ eq)) := by
  rw [intersectSRL.eq_2]
  simp only [intersect_AbstractRange_AbstractRange, bind, Except.bind]
  rw [hp, hq]
  simp only [lt_iv, hle, decide_false, Bool.false_eq_true, ite_false]
  rw [hu]
  simp only []
  rw [forIn_eq u _ _ fuel ys hys, foldlM_filter _ (fun x => decide (x.val ∈ eq))]
  · simp [pure, Except.pure]
  · intro acc x
    simp only [hin x, convert_self, bind, Except.bind, pure, Except.pure]
    by_cases h : x.val ∈ eq <;> simp [h]

/-- When `r1` is longer than `r2`, `intersect(r1::AbstractRange, r2::AbstractRange)` returns
`intersect(r2, r1)`. -/
theorem intersect_swap [JUnique (SRLI t) (SRLI t)] (fuel d : Nat) (p q : SRLI t) (np nq : JInt64)
    (hp : JLength.length p = .ok np) (hq : JLength.length q = .ok nq) (hlt : nq.val < np.val) :
    intersectSRL fuel (d + 1) p q = intersectSRL fuel d q p := by
  rw [intersectSRL.eq_2]
  simp only [intersect_AbstractRange_AbstractRange, bind, Except.bind]
  rw [hp, hq]
  simp only [lt_iv, hlt, decide_true, ite_true]
  cases intersectSRL fuel d q p <;> rfl

theorem intersectRangesGeneric_proven : IntersectRangesGeneric := by
  intro t _ ref1 st1 ref2 st2 n1 o1 n2 o2 r1 r2 fuel hr1 hr2 hv1 hv2 hm1 hm2 hf1 hf2 hU
  obtain ⟨h01, hl1, hit1, hin1⟩ := srl_world ref1 st1 n1 o1 r1 hr1 hv1 hm1
  obtain ⟨h02, hl2, hit2, hin2⟩ := srl_world ref2 st2 n2 o2 r2 hr2 hv2 hm2
  obtain ⟨xs1, hxs1, hv1'⟩ := hit1 fuel hf1
  obtain ⟨xs2, hxs2, hv2'⟩ := hit2 fuel hf2
  -- the filtered elements of `unique(p)` have the promised properties
  have key : ∀ (ep eq : List Int) (xs ys : List (JInt t)), vals xs = ep → (vals ys).Nodup →
      (∀ x, x ∈ ys ↔ x ∈ xs) → ys.Sublist xs →
      (vals (ys.filter fun x => decide (x.val ∈ eq))).Nodup ∧
        (∀ x : Int, x ∈ vals (ys.filter fun x => decide (x.val ∈ eq)) ↔ x ∈ ep ∧ x ∈ eq) ∧
        (vals (ys.filter fun x => decide (x.val ∈ eq))).Sublist ep := by
    intro ep eq xs ys hxv hnd hmem hsub
    have hfm : vals (ys.filter fun x => decide (x.val ∈ eq)) =
        (vals ys).filter fun v => decide (v ∈ eq) := by
      simp only [vals]; rw [List.filter_map]; rfl
    rw [hfm]
    refine ⟨List.Pairwise.filter _ hnd, ?_, ?_⟩
    · intro v
      simp only [List.mem_filter, decide_eq_true_eq, ← hxv, vals, List.mem_map]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, h⟩; exact ⟨⟨y, (hmem y).mp hy, rfl⟩, h⟩
      · rintro ⟨⟨y, hy, rfl⟩, h⟩; exact ⟨⟨y, (hmem y).mpr hy, rfl⟩, h⟩
    · rw [← hxv]; exact List.filter_sublist.trans (hsub.map _)
  by_cases hlt : n2.val < n1.val
  · -- `length(r1) > length(r2)`: `intersect(r2, r1)`
    obtain ⟨u, ys, hu, hys, hnd, hmem, hsub⟩ := hU r2 (by simp) xs2 hxs2
    have hlev := intersect_level fuel 0 r2 r1 n2 n1 (srlVals ref2 st2 n2 o2) (srlVals ref1 st1 n1 o1)
      hl2 hl1 (by omega) hin1 u ys hu hys
    have htop : intersectSRL fuel 2 r1 r2 =
        .ok (ys.filter fun x => decide (x.val ∈ srlVals ref1 st1 n1 o1)) := by
      rw [intersect_swap fuel 1 r1 r2 n1 n2 hl1 hl2 hlt]; exact hlev
    obtain ⟨k1, k2, k3⟩ := key _ _ xs2 ys hv2' hnd hmem hsub
    refine ⟨_, htop, k1, fun x => (k2 x).trans And.comm, ?_⟩
    rw [if_pos hlt]; exact k3
  · obtain ⟨u, ys, hu, hys, hnd, hmem, hsub⟩ := hU r1 (by simp) xs1 hxs1
    have hlev := intersect_level fuel 1 r1 r2 n1 n2 (srlVals ref1 st1 n1 o1) (srlVals ref2 st2 n2 o2)
      hl1 hl2 hlt hin2 u ys hu hys
    obtain ⟨k1, k2, k3⟩ := key _ _ xs1 ys hv1' hnd hmem hsub
    refine ⟨_, hlev, k1, k2, ?_⟩
    rw [if_neg hlt]; exact k3

end IntersectGeneric

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

section TupleIndex

/-- `require_one_based_indexing(r)` (abstractarray.jl:131) of a `UnitRange`: its axes are
one-based, so it returns `true`. -/
instance : JRequireOneBased (UnitRange JInt64) := ⟨fun _ => pure ()⟩

theorem mapM_congr' {α β : Type} (f g : α → JlX β) : ∀ l : List α, (∀ x ∈ l, f x = g x) →
    l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (by simp),
      mapM_congr' f g xs (fun y hy => h y (by simp [hy]))]

theorem mapM_map' {α β γ : Type} (f : β → JlX γ) (g : α → β) : ∀ l : List α,
    (l.map g).mapM f = l.mapM (fun x => f (g x))
  | [] => rfl
  | x :: xs => by rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map' f g xs]

/-- `t[i]` of a tuple (`getfield`, tuple.jl:33) as a range-file computation. -/
abbrev tget {α : Type} (t : List α) (i : Int) : JlX α := liftTuple (JuliaLean.base.tuple.getfield t i)

theorem tget_ok {α : Type} (t : List α) (i : Int) (h1 : 1 ≤ i) (h2 : i ≤ t.length) :
    tget t i = .ok (t[(i - 1).toNat]'(by omega)) := by
  unfold tget JuliaLean.base.tuple.getfield
  rw [if_pos h1, List.getElem?_eq_getElem (show (i - 1).toNat < t.length by omega)]
  rfl

theorem tget_bounds {α : Type} (t : List α) (i : Int) (h : ¬ (1 ≤ i ∧ i ≤ t.length)) :
    tget t i = .error (.jl .boundsError) := by
  unfold tget JuliaLean.base.tuple.getfield
  by_cases h1 : 1 ≤ i
  · rw [if_pos h1, List.getElem?_eq_none (show t.length ≤ (i - 1).toNat by omega)]; rfl
  · rw [if_neg h1]; rfl

theorem tget_cases {α : Type} (t : List α) (i : Int) :
    (∃ y, tget t i = .ok y) ∨ tget t i = .error (.jl .boundsError) := by
  by_cases h : 1 ≤ i ∧ i ≤ t.length
  · exact .inl ⟨_, tget_ok t i h.1 h.2⟩
  · exact .inr (tget_bounds t i h)

theorem mapM_err {α β : Type} (f : α → JlX β) (e : Exc) : ∀ l : List α,
    (∀ x ∈ l, (∃ y, f x = .ok y) ∨ f x = .error e) → (∃ x ∈ l, f x = .error e) → l.mapM f = .error e
  | [], _, ⟨x, hx, _⟩ => by simp at hx
  | x :: xs, h, ⟨z, hz, hze⟩ => by
    rw [List.mapM_cons]
    rcases h x (by simp) with ⟨y, hy⟩ | hy
    · have hzx : z ∈ xs := by
        rcases List.mem_cons.mp hz with rfl | hz'
        · rw [hy] at hze; cases hze
        · exact hz'
      rw [hy, mapM_err f e xs (fun w hw => h w (by simp [hw])) ⟨z, hzx, hze⟩]
      rfl
    · rw [hy]; rfl

/-- Reading the tuple entries at `a, a+1, ..., b` one by one: the slice `t[a:b]` when it is in
bounds, `BoundsError` otherwise. -/
theorem slice_mapM {α : Type} (t : List α) (a b : Int) :
    (intsFromTo a b).mapM (tget t) =
      if b < a then .ok []
      else if 1 ≤ a ∧ b ≤ t.length then .ok ((t.drop (a - 1).toNat).take (b - a + 1).toNat)
      else .error (.jl .boundsError) := by
  by_cases hba : b < a
  · rw [if_pos hba, intsFromTo_empty hba]; rfl
  rw [if_neg hba]
  by_cases hin : 1 ≤ a ∧ b ≤ t.length
  · rw [if_pos hin]
    -- induction on the number of entries
    obtain ⟨n, hn⟩ : ∃ n : Nat, (b - a).toNat = n := ⟨_, rfl⟩
    induction n generalizing a with
    | zero =>
      have hab : a = b := by omega
      subst hab
      rw [intsFromTo_cons (by omega), intsFromTo_empty (by omega), List.mapM_cons,
        tget_ok t a hin.1 (by omega)]
      simp only [show (a - a + 1).toNat = 1 by omega, List.mapM_nil]
      rw [List.drop_eq_getElem_cons (show (a - 1).toNat < t.length by omega)]
      rfl
    | succ n ih =>
      rw [intsFromTo_cons (by omega), List.mapM_cons, tget_ok t a hin.1 (by omega),
        ih (a + 1) (by omega) ⟨by omega, hin.2⟩ (by omega)]
      rw [List.drop_eq_getElem_cons (show (a - 1).toNat < t.length by omega),
        show (b - a + 1).toNat = (b - (a + 1) + 1).toNat + 1 by omega, List.take_succ_cons,
        show (a - 1).toNat + 1 = (a + 1 - 1).toNat by omega]
      rfl
  · rw [if_neg hin]
    apply mapM_err _ _ _ (fun x _ => tget_cases t x)
    by_cases h1 : 1 ≤ a
    · refine ⟨b, ?_, tget_bounds t b (by omega)⟩
      unfold intsFromTo
      simp only [List.mem_map, List.mem_range]
      exact ⟨(b - a).toNat, by omega, by omega⟩
    · refine ⟨a, ?_, tget_bounds t a (by omega)⟩
      rw [intsFromTo_cons (by omega)]; simp

theorem collectIter_go_eq {R E St β : Type} [JIterate1 R E St] [JIterate2 R St E] (r : R)
    (f : E → JlX β) : ∀ (n : Nat) (s : St) (acc : List β) (xs : List E), iterFrom r n s = .ok xs →
      collectIter.go r f n s acc = (xs.mapM f).map (fun ys => acc.reverse ++ ys)
  | 0, s, acc, xs, h => by simp [iterFrom, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, s, acc, xs, h => by
    simp only [iterFrom, bind, Except.bind] at h
    simp only [collectIter.go, bind, Except.bind]
    cases hi : JIterate2.iterate r s with
    | error e => rw [hi] at h; cases h
    | ok o =>
      rw [hi] at h
      cases o with
      | none => simp [pure, Except.pure] at h; subst h; simp [pure, Except.pure, Except.map]
      | some p =>
        obtain ⟨x, s'⟩ := p
        simp only at h
        cases hr : iterFrom r n s' with
        | error e => rw [hr] at h; cases h
        | ok ys =>
          rw [hr] at h; simp [pure, Except.pure] at h; subst h
          rw [List.mapM_cons]
          cases hb : f x with
          | error e => simp only [hb, errBind]; rfl
          | ok b =>
            simp only [hb, okBind]
            rw [collectIter_go_eq r f n s' (b :: acc) ys hr]
            cases ys.mapM f <;> simp [Except.map, pure, Except.pure, okBind, errBind]

theorem collectIter_eq {R E St β : Type} [JIterate1 R E St] [JIterate2 R St E] (r : R)
    (f : E → JlX β) (fuel : Nat) (xs : List E) (h : iterList r fuel = .ok xs) :
    collectIter r f fuel = xs.mapM f := by
  simp only [iterList, bind, Except.bind] at h
  simp only [collectIter, bind, Except.bind]
  cases hi : JIterate1.iterate r with
  | error e => rw [hi] at h; cases h
  | ok o =>
    rw [hi] at h
    cases o with
    | none => simp [pure, Except.pure] at h; subst h; rfl
    | some p =>
      obtain ⟨x, s⟩ := p
      simp only at h
      cases hr : iterFrom r fuel s with
      | error e => rw [hr] at h; cases h
      | ok ys =>
        rw [hr] at h; simp [pure, Except.pure] at h; subst h
        rw [List.mapM_cons]
        cases hb : f x with
        | error e => simp only [hb, errBind]
        | ok b =>
          simp only [hb, okBind]
          rw [collectIter_go_eq r f fuel s [b] ys hr]
          cases ys.mapM f <;> simp [Except.map, pure, Except.pure, okBind, errBind]

/-- `getindex(t::Tuple, r::AbstractUnitRange)` (range.jl:451, the constant-foldable tuple indexing
that exposes `front` and `tail`) returns the same values as indexing `t` at each element of `r` (the
generic method `getindex(t::Tuple, b::AbstractArray)`, tuple.jl:36, and `t[i]` = `getfield`): for
`Int` endpoints `a`, `b` whose range `a:b` has a length that fits in `Int`, `t[a:b]` is `()` when
`a:b` is empty, the entries `t[a], ..., t[b]` when `1 <= a` and `b <= length(t)`, and `BoundsError`
otherwise. -/
def TupleUnitRangeIndex : Prop :=
  ∀ {α : Type} (t : List α) (a b : JInt64) (r : UnitRange JInt64) (fuel : Nat),
    JColon2.colon a b = .ok r → (t.length : Int) ≤ IntTy.i64.max → cnt a.val b.val ≤ IntTy.i64.max →
    (b.val - a.val).toNat < fuel →
    getindex_Tuple_AbstractUnitRange t r fuel =
      if b.val < a.val then .ok []
      else if 1 ≤ a.val ∧ b.val ≤ t.length then .ok ((t.drop (a.val - 1).toNat).take (b.val - a.val + 1).toNat)
      else .error (.jl .boundsError)

theorem bindOk_id {α : Type} (x : JlX α) : (x >>= fun y => Except.ok y) = x := by
  cases x <;> rfl

theorem wrap64_succ (k : Nat) (hk : (k : Int) < 10) : wrapInt .i64 ((k : Int) + 1) = (k : Int) + 1 :=
  wrap_in .i64 (Int.le_trans (by decide : IntTy.i64.min ≤ 0) (by omega))
    (Int.le_trans (by omega : (k : Int) + 1 ≤ 10) (by decide))

theorem wrap64_slice (a b : JInt64) (k : Nat) (hk : k < (b.val - a.val + 1).toNat) :
    wrapInt .i64 ((k : Int) + 1 + a.val - 1) = a.val + k := by
  have h1 : a.val ≤ (k : Int) + 1 + a.val - 1 := by omega
  have h2 : (k : Int) + 1 + a.val - 1 ≤ b.val := by omega
  rw [wrap_in .i64 (Int.le_trans a.property.1 h1) (Int.le_trans h2 b.property.2)]
  omega

theorem wrap64_len (L c : Int) (hL : 0 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 2) (h : L ≤ IntTy.i64.max) :
    wrapInt .i64 (L - c) = L - c :=
  wrap_in .i64 (Int.le_trans (by decide : IntTy.i64.min ≤ -2) (by omega)) (Int.le_trans (by omega) h)

theorem wrap64_nat (n : Nat) (h : (n : Int) ≤ IntTy.i64.max) : wrapInt .i64 (n : Int) = n :=
  wrap_in .i64 (Int.le_trans (by decide : IntTy.i64.min ≤ 0) (Int.natCast_nonneg n)) h

theorem small_index (a b : JInt64) (k : Nat) (hk : k < (b.val - a.val + 1).toNat)
    (h : cnt a.val b.val ≤ 10) : (k : Int) < 10 := by
  unfold cnt at h; split at h <;> omega

/-- `getindex(t::Tuple, r::AbstractUnitRange)` once `length(r)`, `first(r)` and `last(r)` are
known (and `length(r) >= 0`): the branches of range.jl:451-465 in order. -/
theorem getindex_tuple_unfold {α R E St I : Type} [JRequireOneBased R] [JLength R JInt64]
    [JFirst R E] [JLast R E] [HAdd JInt64 E I] [HSub I JInt64 I] [JTupleGetindex I]
    [JTupleGetindex E] [JEq E JInt64] [JIterate1 R E St] [JIterate2 R St E]
    (t : List α) (r : R) (fuel : Nat) (n : JInt64) (f l : E)
    (h0 : JRequireOneBased.requireOneBased r = .ok ()) (hn : JLength.length r = .ok n)
    (hf : JFirst.first r = .ok f) (hl : JLast.last r = .ok l) (hpos : 0 ≤ n.val) :
    getindex_Tuple_AbstractUnitRange t r fuel =
      if n.val ≤ 10 then
        (List.range n.val.toNat).mapM fun k : Nat =>
          JTupleGetindex.tupleGetindex t (jint ((k : Int) + 1) + f - jint 1)
      else if JEq.eq f (jint 1) = true then
        (if JEq.eq l (jint t.length) = true then Except.ok t
         else if JEq.eq l (@HSub.hSub JInt64 JInt64 JInt64 instHSub (jint t.length) (jint 1)) = true then
           tupleFront t
         else if JEq.eq l (@HSub.hSub JInt64 JInt64 JInt64 instHSub (jint t.length) (jint 2)) = true then
           tupleFront t >>= tupleFront
         else collectIter r (fun ri => JTupleGetindex.tupleGetindex t ri) fuel)
      else if JEq.eq l (jint t.length) = true then
        (if JEq.eq f (jint 2) = true then tupleTail t
         else if JEq.eq f (jint 3) = true then tupleTail t >>= tupleTail
         else collectIter r (fun ri => JTupleGetindex.tupleGetindex t ri) fuel)
      else collectIter r (fun ri => JTupleGetindex.tupleGetindex t ri) fuel := by
  have hneg : ¬ n.val < 0 := by omega
  simp only [getindex_Tuple_AbstractUnitRange, h0, hn, hf, hl, okBind, hneg, ite_false, pure,
    Except.pure, bindOk_id]
  all_goals rfl

theorem tupleIdx_cnt (a b : Int) : 0 ≤ cnt a b ∧ (cnt a b).toNat = (b - a + 1).toNat := by
  unfold cnt; split <;> omega

theorem tupleIdx_long_bounds (a b : Int) (h : ¬ cnt a b ≤ 10) : a ≤ b ∧ 11 ≤ b - a + 1 := by
  unfold cnt at h; split at h <;> omega

/-- One entry of the short-range `ntuple`: `t[i + first(r) - 1]` at `i = k + 1` reads `t[a + k]`. -/
theorem tupleIdx_short_elem {α : Type} (t : List α) (a b : JInt64) (k : Nat)
    (hk : k < (b.val - a.val + 1).toNat) (h : cnt a.val b.val ≤ 10) :
    (JTupleGetindex.tupleGetindex t (jint ((k : Int) + 1) + a - jint 1 : JInt64) : JlX α) =
      tget t (a.val + k) := by
  have e1 := wrap64_succ k (small_index a b k hk h)
  have e3 := wrap64_slice a b k hk
  have hc1 : wrapInt .i64 1 = 1 := by decide
  have hval : (jint ((k : Int) + 1) + a - jint 1 : JInt64).val = a.val + k := by
    rw [sub_iv, add_iv]; simp only [jint_val]
    rw [e1, hc1, IntVal.wrapInt_sub_left, e3]
  show liftTuple (JuliaLean.base.tuple.getfield t (jint ((k : Int) + 1) + a - jint 1 : JInt64).val) =
    liftTuple (JuliaLean.base.tuple.getfield t (a.val + k))
  rw [hval]

/-- `ntuple(i -> t[i + first(r) - 1], length(r))` for `a:b` with at most 10 entries. -/
theorem tupleIdx_short {α : Type} (t : List α) (a b : JInt64) (h : cnt a.val b.val ≤ 10) :
    (List.range (b.val - a.val + 1).toNat).mapM (fun k : Nat =>
      (JTupleGetindex.tupleGetindex t (jint ((k : Int) + 1) + a - jint 1 : JInt64) : JlX α)) =
    (intsFromTo a.val b.val).mapM (tget t) := by
  unfold intsFromTo
  rw [mapM_map']
  apply mapM_congr'
  intro k hk
  rw [List.mem_range] at hk
  exact tupleIdx_short_elem t a b k hk h

/-- `(eltype(t)[t[ri] for ri in r]...,)` iterates the unit range `a:l`. -/
theorem tupleIdx_collect {α : Type} (t : List α) (a l : JInt64) (fuel : Nat)
    (hf : (l.val - a.val).toNat < fuel) :
    collectIter (⟨a, l⟩ : UnitRange JInt64) (fun ri => (JTupleGetindex.tupleGetindex t ri : JlX α))
      fuel = (intsFromTo a.val l.val).mapM (tget t) := by
  have hit := iterList_unit (⟨a, l⟩ : UnitRange JInt64) fuel hf
  cases h : iterList (⟨a, l⟩ : UnitRange JInt64) fuel with
  | error e => rw [h] at hit; cases hit
  | ok xs =>
    rw [h] at hit
    have hxv : vals xs = intsFromTo a.val l.val := by
      simp only [Except.map, Except.ok.injEq] at hit
      exact hit
    rw [collectIter_eq _ _ fuel xs h, ← hxv, mapM_map']; rfl

theorem tupleIdx_dropLast2 {α : Type} (t : List α) : t.dropLast.dropLast = t.take (t.length - 2) := by
  simp only [List.dropLast_eq_take, List.length_take, List.take_take]
  congr 1
  omega

theorem tupleIdx_ne {α : Type} (t : List α) (h : 0 < t.length) : t.isEmpty = false := by
  cases t with
  | nil => simp at h
  | cons _ _ => rfl

theorem tupleIdx_tail2 {α : Type} (t : List α) : t.tail.tail = t.drop 2 := by
  cases t with
  | nil => rfl
  | cons x xs => cases xs <;> rfl

/-- The `front`/`tail` shortcuts of range.jl:455-464 for an index range `A:B` with at least 11
entries agree with the in-bounds slice, and every other case falls through to the generic
collection `X`. -/
theorem tupleIdx_long_core {α : Type} (t : List α) (A B : Int) (X : JlX (List α))
    (hX : X = if 1 ≤ A ∧ B ≤ t.length then .ok ((t.drop (A - 1).toNat).take (B - A + 1).toNat)
      else .error (.jl .boundsError))
    (hab : A ≤ B) (h11 : 11 ≤ B - A + 1) :
    (if decide (A = 1) = true then
        (if decide (B = t.length) = true then Except.ok t
         else if decide (B = t.length - 1) = true then tupleFront t
         else if decide (B = t.length - 2) = true then tupleFront t >>= tupleFront
         else X)
      else if decide (B = t.length) = true then
        (if decide (A = 2) = true then tupleTail t
         else if decide (A = 3) = true then tupleTail t >>= tupleTail
         else X)
      else X) = X := by
  by_cases h1 : A = 1
  · rw [if_pos (decide_eq_true h1)]
    have q0 : (A - 1).toNat = 0 := by omega
    have hA : 1 ≤ A := by omega
    by_cases h2 : B = t.length
    · have q1 : (B - A + 1).toNat = t.length := by omega
      have hin : 1 ≤ A ∧ B ≤ (t.length : Int) := ⟨hA, by omega⟩
      rw [if_pos (decide_eq_true h2), hX, if_pos hin, q0, q1, List.drop_zero,
        List.take_of_length_le (Nat.le_refl _)]
    rw [if_neg (by simpa using h2)]
    by_cases h3 : B = t.length - 1
    · have q1 : (B - A + 1).toNat = t.length - 1 := by omega
      have hin : 1 ≤ A ∧ B ≤ (t.length : Int) := ⟨hA, by omega⟩
      have hne := tupleIdx_ne t (by omega)
      rw [if_pos (decide_eq_true h3), hX, if_pos hin, q0, q1, List.drop_zero]
      simp only [tupleFront, hne, Bool.false_eq_true, ite_false, pure, Except.pure,
        List.dropLast_eq_take]
    rw [if_neg (by simpa using h3)]
    by_cases h4 : B = t.length - 2
    · have q1 : (B - A + 1).toNat = t.length - 2 := by omega
      have hne := tupleIdx_ne t (by omega)
      have hne2 := tupleIdx_ne t.dropLast (by simp only [List.length_dropLast]; omega)
      have hf1 : tupleFront t = .ok t.dropLast := by
        simp only [tupleFront, hne, Bool.false_eq_true, ite_false, pure, Except.pure]
      have hf2 : tupleFront t.dropLast = .ok t.dropLast.dropLast := by
        simp only [tupleFront, hne2, Bool.false_eq_true, ite_false, pure, Except.pure]
      rw [if_pos (decide_eq_true h4), hf1]
      show tupleFront t.dropLast = X
      have hin : 1 ≤ A ∧ B ≤ (t.length : Int) := ⟨hA, by omega⟩
      rw [hf2, hX, if_pos hin, q0, q1, List.drop_zero, tupleIdx_dropLast2]
    rw [if_neg (by simpa using h4)]
  · rw [if_neg (by simpa using h1)]
    by_cases h2 : B = t.length
    · rw [if_pos (decide_eq_true h2)]
      by_cases h5 : A = 2
      · have hne := tupleIdx_ne t (by omega)
        have q0 : (A - 1).toNat = 1 := by omega
        have q1 : (B - A + 1).toNat = t.length - 1 := by omega
        have hdl : (t.drop 1).length ≤ t.length - 1 := by simp
        have hin : 1 ≤ A ∧ B ≤ (t.length : Int) := ⟨by omega, by omega⟩
        rw [if_pos (decide_eq_true h5), hX, if_pos hin, q0, q1,
          List.take_of_length_le hdl]
        simp only [tupleTail, hne, Bool.false_eq_true, ite_false, pure, Except.pure, List.drop_one]
      rw [if_neg (by simpa using h5)]
      by_cases h6 : A = 3
      · have hne := tupleIdx_ne t (by omega)
        have q0 : (A - 1).toNat = 2 := by omega
        have q1 : (B - A + 1).toNat = t.length - 2 := by omega
        have hdl : (t.drop 2).length ≤ t.length - 2 := by simp
        have hne2 := tupleIdx_ne t.tail (by simp only [List.length_tail]; omega)
        have hf1 : tupleTail t = .ok t.tail := by
          simp only [tupleTail, hne, Bool.false_eq_true, ite_false, pure, Except.pure]
        have hf2 : tupleTail t.tail = .ok t.tail.tail := by
          simp only [tupleTail, hne2, Bool.false_eq_true, ite_false, pure, Except.pure]
        rw [if_pos (decide_eq_true h6), hf1]
        show tupleTail t.tail = X
        have hin : 1 ≤ A ∧ B ≤ (t.length : Int) := ⟨by omega, by omega⟩
        rw [hf2, hX, if_pos hin, q0, q1, List.take_of_length_le hdl, tupleIdx_tail2]
      rw [if_neg (by simpa using h6)]
    rw [if_neg (by simpa using h2)]

theorem tupleUnitRangeIndex_proven : TupleUnitRangeIndex := by
  intro α t a b r fuel hr htl hfit hfuel
  rw [colon_unit] at hr; cases hr
  obtain ⟨m, hm, hmv⟩ := lengthUnit_fits a b (show cnt a.val b.val ≤ (lenTy IntTy.i64).max from hfit)
  have hl' : (JLength.length (⟨a, unitStop a b⟩ : UnitRange JInt64) : JlX JInt64) = .ok m := hm
  have hmv' : (m : JInt64).val = cnt a.val b.val := hmv
  have hus := unitStop_val a b
  suffices h : getindex_Tuple_AbstractUnitRange t (⟨a, unitStop a b⟩ : UnitRange JInt64) fuel =
      (intsFromTo a.val b.val).mapM (tget t) by
    rw [h, slice_mapM]
  have h0m : 0 ≤ (m : JInt64).val := by rw [hmv']; exact (tupleIdx_cnt _ _).1
  rw [getindex_tuple_unfold t (⟨a, unitStop a b⟩ : UnitRange JInt64) fuel m a (unitStop a b) rfl hl'
    (first_unit _) (last_unit _) h0m]
  have hc1 : wrapInt .i64 1 = 1 := by decide
  by_cases h10 : (m : JInt64).val ≤ 10
  · -- `ntuple(i -> t[i + first(r) - 1], length(r))`
    rw [if_pos h10, hmv', (tupleIdx_cnt _ _).2]
    exact tupleIdx_short t a b (by rw [← hmv']; exact h10)
  · -- longer ranges: the `front`/`tail` shortcuts, else `(eltype(t)[t[ri] for ri in r]...,)`
    rw [if_neg h10]
    obtain ⟨hab, hm11⟩ := tupleIdx_long_bounds a.val b.val (by rw [← hmv']; exact h10)
    have hus' : (unitStop a b).val = b.val := by rw [hus, if_pos hab]
    have hw0 := wrap64_nat t.length htl
    have hw1 := wrap64_len (t.length : Int) 1 (Int.natCast_nonneg _) (by decide) (by decide) htl
    have hw2 := wrap64_len (t.length : Int) 2 (Int.natCast_nonneg _) (by decide) (by decide) htl
    have hc2 : wrapInt .i64 2 = 2 := by decide
    have hc3 : wrapInt .i64 3 = 3 := by decide
    simp only [eq_iv, coreSub_val, jint_val, hus', hw0, hw1, hw2, hc1, hc2, hc3]
    have hf : ((unitStop a b).val - a.val).toNat < fuel := by rw [hus']; exact hfuel
    rw [tupleIdx_collect t a (unitStop a b) fuel hf, hus']
    exact tupleIdx_long_core t a.val b.val _ (by rw [slice_mapM, if_neg (Int.not_lt.mpr hab)])
      hab hm11

end TupleIndex

/-! Nothing to promise:
colon_A_step_C@10: promotes both endpoints to `promote_type(A, C)` and forwards to `(:)(start::T, step, stop::T)`
colon_T_AbstractFloat_T_Real@16: promotes the three arguments and forwards to the same-type colon
colon_T_AbstractFloat_T_AbstractFloat@17: converts the step to `T` and forwards to the same-type colon
colon_T_Real_T_AbstractFloat@18: converts the step to `T` and forwards to the same-type colon
_range_wrapping_add_Any@35: arithmetic helper `x + y` for non-BitInteger types; its callers state the ranges built
_range_wrapping_sub_Any@37: arithmetic helper `x - y`; its callers state the ranges built
_range_wrapping_mul_BitInteger@38: arithmetic helper `x *% y`; its callers state the ranges built
_range_wrapping_mul_Any@39: arithmetic helper `x * y`; its callers state the ranges built
JRangeStartKw@165: declaration `function range end` with no body; the methods are covered
_range_N_A_A_A@182: forwards to `range_step_stop_length(step, stop, len)`
_range_A_N_A_A@186: forwards to `range_start_stop_length(start, stop, len)`
range_stop_Any@196: forwards to `range_start_stop(oftype(stop, 1), stop)`
RangeStepStyle_AbstractRange@285: internal trait constant used for dispatch; no value behaviour
RangeStepStyle_AbstractRange_Integer@286: internal trait constant used for dispatch; no value behaviour
convert_Type_AbstractRange@288: returns `r` if it already has type `T`, else forwards to the constructor `T(r)`
StepRange_T@403: forwards to the constructor `StepRange{T,S}(start, step, stop)` with `S = typeof(step)`
UnitRange_T@430: converts both endpoints to `T` and forwards to the inner constructor `UnitRange{T}(start::T, stop::T)`
unitrange@447: convenience conversion; forwards to `UnitRange(x)`
OneTo_T.throwbool@488: error-message helper; the error is stated by the callers
OneTo_T_range.throwstart@494: error-message helper; the error is stated by the callers
OneTo_T_range.throwstep@495: error-message helper; the error is stated by the callers
OneTo_T_range.throwbool@496: error-message helper; the error is stated by the callers
unchecked_oneto@503: internal constructor that stores its argument without checks
OneTo_AbstractRange@506: forwards to `OneTo{T}(r)`
oneto@507: forwards to `OneTo(r)`
range_start_stop_length_Any@625: promotes `start` and `stop` to one type and forwards to `range_start_stop_length(start, stop, len)` of that type
length_AbstractRange@705: abstract fallback that throws "length implementation missing"; no concrete range reaches it
step_hp_StepRangeLen@743: internal high-precision step accessor
step_hp_AbstractRange@744: internal high-precision step accessor, `step(r)` for exact ranges
has_offset_axes_StepRange@747: constant `false` trait for the indexing machinery
extrema_AbstractRange@920: returns `(minimum(r), maximum(r))`; the two calls carry the behaviour
copy_AbstractRange@923: returns its argument: ranges are immutable, so the copy is the range itself
getindex_AbstractRange_Colon@1000: forwards to `copy(r)`, which returns `r`
intersect_AbstractUnitRange_Integer@1213: forwards to `intersect(i, r)` with the arguments swapped
el_same_T_T@1331: type-level promotion helper; no value behaviour
el_same_T_S@1332: type-level promotion helper; no value behaviour
el_same_S_T@1333: type-level promotion helper; no value behaviour
el_same_Any@1334: type-level promotion helper; no value behaviour
promote_rule_UnitRange_UnitRange@1336: type-level promotion rule; no value behaviour
UnitRange_T_UnitRange_T@1338: identity conversion `UnitRange{T}(r::UnitRange{T}) = r`
UnitRange_T_UnitRange@1339: forwards to `UnitRange{T}(r.start, r.stop)`
promote_rule_OneTo_OneTo@1341: type-level promotion rule; no value behaviour
OneTo_T_OneTo_T@1343: identity conversion `OneTo{T}(r::OneTo{T}) = r`
OneTo_T_OneTo@1344: forwards to `OneTo{T}(r.stop)`
promote_rule_OneTo_UR@1346: type-level promotion rule; no value behaviour
promote_rule_UnitRange_UR@1349: type-level promotion rule; no value behaviour
AbstractUnitRange_T_AbstractUnitRange_T@1354: identity conversion
AbstractUnitRange_T_UnitRange@1355: forwards to `UnitRange{T}(r)`
AbstractUnitRange_T_OneTo@1356: forwards to `OneTo{T}(r)`
OrdinalRange_TS_OrdinalRange@1358: forwards to `StepRange{T, S}(r)`
OrdinalRange_TT_AbstractUnitRange@1359: forwards to `AbstractUnitRange{T}(r)`
promote_rule_StepRange_StepRange@1361: type-level promotion rule; no value behaviour
StepRange_TS_StepRange_TS@1366: identity conversion
StepRange_T_StepRange_T@1367: identity conversion
StepRange_StepRange@1368: identity conversion `StepRange(r::StepRange) = r`
promote_rule_StepRange_UR@1370: type-level promotion rule; no value behaviour
StepRange_S_AbstractRange@1376: forwards to `StepRange{eltype(r),T2}(r)`
StepRange_StepRangeLen@1377: forwards to `StepRange{eltype(r)}(r)`
StepRange_T_StepRangeLen@1378: forwards to `StepRange{T,S}(r)`
promote_rule_StepRangeLen_StepRangeLen@1380: type-level promotion rule; no value behaviour
StepRangeLen_TRSL_same@1384: identity conversion
promote_rule_StepRangeLen_OR@1390: type-level promotion rule; no value behaviour
StepRangeLen_AbstractRange@1396: forwards to `StepRangeLen{eltype(r)}(r)`
promote_rule_LinRange_LinRange@1398: type-level promotion rule; no value behaviour
LinRange_TL_same@1402: identity conversion
LinRange_AbstractRange@1405: forwards to `LinRange{T}(r)`
promote_rule_LinRange_OR@1407: type-level promotion rule; no value behaviour
promote_rule_LinRange_StepRangeLen@1410: type-level promotion rule; no value behaviour
sort!_AbstractUnitRange@1461: returns its argument unchanged (a unit range is already sorted)
in_T_AbstractRange@1487: forwards to `_in_range(x, r)`
rangeop_promote@1519: promotes both ranges to a common type and forwards to the same-type `+`/`-` method
minus_StepRangeLen_StepRangeLen@1534: forwards to `+(r1, -r2)`
logrange@1602: forwards to `LogRange(start, stop, Int(length))`
logrange_kw@1603: keyword form; forwards to `logrange(start, stop, length)`
LogRange_T_Real@1687: converts the endpoints to `T` and forwards to the inner constructor
LogRange_Real@1690: computes the element type and forwards to `LogRange{T}`
size_LogRange@1695: returns `(r.len,)`, the stored length that `length(r::LogRange)` returns
_logrange_extra_Real@1701: converts the endpoints with `float` and forwards to the `Float64` method
_resolve_in_world@1739: internal world-age lookup used when the range operators are defined; no range values
-/

/-! ## Registry entries -/

/-- The registry entries of `base/range.jl`. -/
def entries : List Entry := [
  { id := "rangescov-logrange-endpoints"
    juliaFile := "base/range.jl"
    juliaFns := ["LogRange{T}(start::T, stop::T, len::Int) where {T<:Real}", "_logrange_extra(a::Float64, b::Float64, len::Int)", "getindex(r::LogRange{T}, i::Int) where {T}", "first(r::LogRange)", "last(r::LogRange)", "length(r::LogRange)"]
    statement := "LogRange{Float64}(a, b, n) throws DomainError when an endpoint is zero, negative or not finite; a constructed range has first(r) == a, last(r) == b, length(r) == n >= 0, r[1] == a exactly, r[n] == b exactly for n >= 2, and a == b when n == 1, for every implementation of the TwicePrecision log, division and exp."
    source := "LogRange docstring, range.jl:1604-1659"
    status := .proven
    prop := ``LogRangeConstruct
    thm := some ``logRangeConstruct_proven
    notes := "twiceprecision.jl callees and the float.jl Float64-Int comparison are typed parameters." },
  { id := "rangescov-logrange-domain"
    juliaFile := "base/range.jl"
    juliaFns := ["LogRange{T}(start::T, stop::T, len::Int) where {T<:Real}", "_logrange_extra(a::Float64, b::Float64, len::Int)", "getindex(r::LogRange{T}, i::Int) where {T}", "first(r::LogRange)", "last(r::LogRange)", "length(r::LogRange)"]
    statement := "LogRange{Float64}(a, b, n) throws DomainError when an endpoint is zero, negative or not finite; a constructed range has first(r) == a, last(r) == b, length(r) == n >= 0, r[1] == a exactly, r[n] == b exactly for n >= 2, and a == b when n == 1, for every implementation of the TwicePrecision log, division and exp."
    source := "LogRange docstring, range.jl:1604-1659"
    status := .proven
    prop := ``LogRangeConstruct
    thm := some ``logRangeConstruct_proven
    notes := "twiceprecision.jl callees and the float.jl Float64-Int comparison are typed parameters." },
  { id := "rangescov-eq-twiceprecision"
    juliaFile := "base/range.jl"
    juliaFns := ["==(r::T, s::T) where {T<:Union{StepRangeLen,LinRange}}", "isempty(r::StepRangeLen)", "length(r::StepRangeLen)", "first(r::StepRangeLen)", "last(r::StepRangeLen)"]
    statement := "Two Float64 StepRangeLens with TwicePrecision reference and step (range(start; step, length)) that are == have equal elements."
    source := "invariant: == on AbstractArrays compares elements"
    status := .refuted
    prop := ``TPEqElementwise
    thm := some ``tpEqElementwise_refuted
    issue := "repro/rangescov-eq-twiceprecision.jl"
    notes := "== (range.jl:1168, selected on the target build) compares only first, length and last; unsafe_getindex for TwicePrecision ranges (twiceprecision.jl:480) is a typed parameter, instantiated with the element values Julia prints for range(0.0; step=0.30000000000000004, length=8) and range(0.0; step=0.3000000000000001, length=8)." },
  { id := "rangescov-bigfloat-colon-empty"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(a::T, b::T) where {T<:AbstractFloat}", "(:)(start::T, step::T, stop::T) where {T<:AbstractFloat}", "_colon(::Ordered, ::ArithmeticRounds, start::T, step, stop::T) where {T}", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)"]
    statement := "For a non-IEEE AbstractFloat type such as BigFloat, a:b with b < a is an empty range."
    source := "range.jl:54: when b < a, an empty range will be constructed"
    status := .refuted
    prop := ``RoundsColonEmpty
    thm := some ``roundsColonEmpty_refuted
    issue := "repro/rangescov-bigfloat-colon-empty.jl"
    notes := "BigFloat arithmetic (mpfr.jl) is a typed parameter with the floored-division law; big(3.0):big(1.0) computes length fld(-2, 1) + 1 = -1 and the StepRangeLen constructor throws ArgumentError." },
  { id := "rangescov-range-length"
    juliaFile := "base/range.jl"
    juliaFns := ["range(;start=nothing, stop=nothing, length::Union{Integer, Nothing}=nothing, step=nothing)", "range(start; stop=nothing, length::Union{Integer,Nothing}=nothing, step=nothing)", "range(start, stop; length::Union{Integer,Nothing}=nothing, step=nothing)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Any, stop::Any, len::Nothing)", "_range(start::Nothing, step::Any, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Nothing)", "range_length(len::Integer)", "range_stop(stop::Integer)", "range_start_stop(start, stop)", "range_start_step_stop(start, step, stop)", "range_error(start, step, stop, length)"]
    statement := "Keyword range with BitInteger arguments: range(; length=n) and range(; stop=n) are OneTo(n) with elements 1..n; range(a; stop=b) and range(a, b) have elements a..b; range(a; step=s, stop=b) has elements a, a+s, ... between a and b (ArgumentError for s == 0); range() and range(; step, length) throw ArgumentError."
    source := "range docstring (range.jl:72-160)"
    status := .proven
    prop := ``KeywordRange
    thm := some ``keywordRange_proven },
  { id := "rangescov-range-stop-int"
    juliaFile := "base/range.jl"
    juliaFns := ["range(;start=nothing, stop=nothing, length::Union{Integer, Nothing}=nothing, step=nothing)", "range(start; stop=nothing, length::Union{Integer,Nothing}=nothing, step=nothing)", "range(start, stop; length::Union{Integer,Nothing}=nothing, step=nothing)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Any, stop::Any, len::Nothing)", "_range(start::Nothing, step::Any, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Nothing)", "range_length(len::Integer)", "range_stop(stop::Integer)", "range_start_stop(start, stop)", "range_start_step_stop(start, step, stop)", "range_error(start, step, stop, length)"]
    statement := "Keyword range with BitInteger arguments: range(; length=n) and range(; stop=n) are OneTo(n) with elements 1..n; range(a; stop=b) and range(a, b) have elements a..b; range(a; step=s, stop=b) has elements a, a+s, ... between a and b (ArgumentError for s == 0); range() and range(; step, length) throw ArgumentError."
    source := "range docstring (range.jl:72-160)"
    status := .proven
    prop := ``KeywordRange
    thm := some ``keywordRange_proven },
  { id := "rangescov-range-start-stop"
    juliaFile := "base/range.jl"
    juliaFns := ["range(;start=nothing, stop=nothing, length::Union{Integer, Nothing}=nothing, step=nothing)", "range(start; stop=nothing, length::Union{Integer,Nothing}=nothing, step=nothing)", "range(start, stop; length::Union{Integer,Nothing}=nothing, step=nothing)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Any, stop::Any, len::Nothing)", "_range(start::Nothing, step::Any, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Nothing)", "range_length(len::Integer)", "range_stop(stop::Integer)", "range_start_stop(start, stop)", "range_start_step_stop(start, step, stop)", "range_error(start, step, stop, length)"]
    statement := "Keyword range with BitInteger arguments: range(; length=n) and range(; stop=n) are OneTo(n) with elements 1..n; range(a; stop=b) and range(a, b) have elements a..b; range(a; step=s, stop=b) has elements a, a+s, ... between a and b (ArgumentError for s == 0); range() and range(; step, length) throw ArgumentError."
    source := "range docstring (range.jl:72-160)"
    status := .proven
    prop := ``KeywordRange
    thm := some ``keywordRange_proven },
  { id := "rangescov-colon-promote3-zero"
    juliaFile := "base/range.jl"
    juliaFns := ["range(;start=nothing, stop=nothing, length::Union{Integer, Nothing}=nothing, step=nothing)", "range(start; stop=nothing, length::Union{Integer,Nothing}=nothing, step=nothing)", "range(start, stop; length::Union{Integer,Nothing}=nothing, step=nothing)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Nothing, stop::Any, len::Nothing)", "_range(start::Any, step::Any, stop::Any, len::Nothing)", "_range(start::Nothing, step::Any, stop::Nothing, len::Any)", "_range(start::Nothing, step::Nothing, stop::Nothing, len::Nothing)", "range_length(len::Integer)", "range_stop(stop::Integer)", "range_start_stop(start, stop)", "range_start_step_stop(start, step, stop)", "range_error(start, step, stop, length)"]
    statement := "Keyword range with BitInteger arguments: range(; length=n) and range(; stop=n) are OneTo(n) with elements 1..n; range(a; stop=b) and range(a, b) have elements a..b; range(a; step=s, stop=b) has elements a, a+s, ... between a and b (ArgumentError for s == 0); range() and range(; step, length) throw ArgumentError."
    source := "range docstring (range.jl:72-160)"
    status := .proven
    prop := ``KeywordRange
    thm := some ``keywordRange_proven },
  { id := "rangescov-minimum-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::Integer, r::AbstractUnitRange{<:Integer})", "minimum(r::AbstractUnitRange)", "maximum(r::AbstractUnitRange)", "==(r::AbstractUnitRange, s::AbstractUnitRange)", "issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "issorted(r::AbstractUnitRange)", "sort(r::AbstractUnitRange)"]
    statement := "For unit ranges a:b and c:d of one BitInteger type with element lists A and C: x in a:b (x of any BitInteger type) is membership in A; minimum/maximum are the least/greatest element of A or ArgumentError when A is empty; == is A == C; issubset is A ⊆ C; iterating intersect(a:b, c:d) visits exactly the common integers in increasing order; issorted/sort report and return the range, whose elements increase."
    source := "docstrings of in, minimum, maximum, ==, issubset, intersect, issorted, sort; invariant: set operations agree with element lists"
    status := .proven
    prop := ``UnitRangeQueries
    thm := some ``unitRangeQueries_proven },
  { id := "rangescov-maximum-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::Integer, r::AbstractUnitRange{<:Integer})", "minimum(r::AbstractUnitRange)", "maximum(r::AbstractUnitRange)", "==(r::AbstractUnitRange, s::AbstractUnitRange)", "issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "issorted(r::AbstractUnitRange)", "sort(r::AbstractUnitRange)"]
    statement := "For unit ranges a:b and c:d of one BitInteger type with element lists A and C: x in a:b (x of any BitInteger type) is membership in A; minimum/maximum are the least/greatest element of A or ArgumentError when A is empty; == is A == C; issubset is A ⊆ C; iterating intersect(a:b, c:d) visits exactly the common integers in increasing order; issorted/sort report and return the range, whose elements increase."
    source := "docstrings of in, minimum, maximum, ==, issubset, intersect, issorted, sort; invariant: set operations agree with element lists"
    status := .proven
    prop := ``UnitRangeQueries
    thm := some ``unitRangeQueries_proven },
  { id := "rangescov-eq-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::Integer, r::AbstractUnitRange{<:Integer})", "minimum(r::AbstractUnitRange)", "maximum(r::AbstractUnitRange)", "==(r::AbstractUnitRange, s::AbstractUnitRange)", "issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "issorted(r::AbstractUnitRange)", "sort(r::AbstractUnitRange)"]
    statement := "For unit ranges a:b and c:d of one BitInteger type with element lists A and C: x in a:b (x of any BitInteger type) is membership in A; minimum/maximum are the least/greatest element of A or ArgumentError when A is empty; == is A == C; issubset is A ⊆ C; iterating intersect(a:b, c:d) visits exactly the common integers in increasing order; issorted/sort report and return the range, whose elements increase."
    source := "docstrings of in, minimum, maximum, ==, issubset, intersect, issorted, sort; invariant: set operations agree with element lists"
    status := .proven
    prop := ``UnitRangeQueries
    thm := some ``unitRangeQueries_proven },
  { id := "ranges-operations-unit-subset"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::Integer, r::AbstractUnitRange{<:Integer})", "minimum(r::AbstractUnitRange)", "maximum(r::AbstractUnitRange)", "==(r::AbstractUnitRange, s::AbstractUnitRange)", "issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "issorted(r::AbstractUnitRange)", "sort(r::AbstractUnitRange)"]
    statement := "For unit ranges a:b and c:d of one BitInteger type with element lists A and C: x in a:b (x of any BitInteger type) is membership in A; minimum/maximum are the least/greatest element of A or ArgumentError when A is empty; == is A == C; issubset is A ⊆ C; iterating intersect(a:b, c:d) visits exactly the common integers in increasing order; issorted/sort report and return the range, whose elements increase."
    source := "docstrings of in, minimum, maximum, ==, issubset, intersect, issorted, sort; invariant: set operations agree with element lists"
    status := .proven
    prop := ``UnitRangeQueries
    thm := some ``unitRangeQueries_proven },
  { id := "rangescov-unit-sorted"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::Integer, r::AbstractUnitRange{<:Integer})", "minimum(r::AbstractUnitRange)", "maximum(r::AbstractUnitRange)", "==(r::AbstractUnitRange, s::AbstractUnitRange)", "issubset(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})", "issorted(r::AbstractUnitRange)", "sort(r::AbstractUnitRange)"]
    statement := "For unit ranges a:b and c:d of one BitInteger type with element lists A and C: x in a:b (x of any BitInteger type) is membership in A; minimum/maximum are the least/greatest element of A or ArgumentError when A is empty; == is A == C; issubset is A ⊆ C; iterating intersect(a:b, c:d) visits exactly the common integers in increasing order; issorted/sort report and return the range, whose elements increase."
    source := "docstrings of in, minimum, maximum, ==, issubset, intersect, issorted, sort; invariant: set operations agree with element lists"
    status := .proven
    prop := ``UnitRangeQueries
    thm := some ``unitRangeQueries_proven },
  { id := "rangescov-steprange-zero-single"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, step::T, stop::T) where {T<:Real}", "_colon(::Ordered, ::Any, start::T, step, stop::T) where {T}", "StepRange(start::T, step::S, stop::T) where {T,S}", "StepRange{T,S}(start, step, stop) where {T,S}", "steprange_last(start, step, stop)", "overflow_case(absdiff, absstep)", "steprange_last_empty(start::Integer, step, stop)", "isempty(r::StepRange)", "step(r::StepRange)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)"]
    statement := "For a, s, b of any BitInteger type, a:s:b throws ArgumentError for s == 0 and otherwise denotes the integers a, a+s, ... between a and b: first is a, step is s, isempty iff there are none, last is the last of them, and iteration visits exactly them (all widths, including typemin steps and full-width spans)."
    source := "StepRange docstring (range.jl:289-343); range docstring (range.jl:72-160)"
    status := .proven
    prop := ``StepRangeColon
    thm := some ``stepRangeColon_proven },
  { id := "rangescov-colon-same3-zero"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, step::T, stop::T) where {T<:Real}", "_colon(::Ordered, ::Any, start::T, step, stop::T) where {T}", "StepRange(start::T, step::S, stop::T) where {T,S}", "StepRange{T,S}(start, step, stop) where {T,S}", "steprange_last(start, step, stop)", "overflow_case(absdiff, absstep)", "steprange_last_empty(start::Integer, step, stop)", "isempty(r::StepRange)", "step(r::StepRange)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)"]
    statement := "For a, s, b of any BitInteger type, a:s:b throws ArgumentError for s == 0 and otherwise denotes the integers a, a+s, ... between a and b: first is a, step is s, isempty iff there are none, last is the last of them, and iteration visits exactly them (all widths, including typemin steps and full-width spans)."
    source := "StepRange docstring (range.jl:289-343); range docstring (range.jl:72-160)"
    status := .proven
    prop := ``StepRangeColon
    thm := some ``stepRangeColon_proven },
  { id := "rangescov-colon-ordered-zero"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, step::T, stop::T) where {T<:Real}", "_colon(::Ordered, ::Any, start::T, step, stop::T) where {T}", "StepRange(start::T, step::S, stop::T) where {T,S}", "StepRange{T,S}(start, step, stop) where {T,S}", "steprange_last(start, step, stop)", "overflow_case(absdiff, absstep)", "steprange_last_empty(start::Integer, step, stop)", "isempty(r::StepRange)", "step(r::StepRange)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)"]
    statement := "For a, s, b of any BitInteger type, a:s:b throws ArgumentError for s == 0 and otherwise denotes the integers a, a+s, ... between a and b: first is a, step is s, isempty iff there are none, last is the last of them, and iteration visits exactly them (all widths, including typemin steps and full-width spans)."
    source := "StepRange docstring (range.jl:289-343); range docstring (range.jl:72-160)"
    status := .proven
    prop := ``StepRangeColon
    thm := some ``stepRangeColon_proven },
  { id := "rangescov-steprange-construction"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, step::T, stop::T) where {T<:Real}", "_colon(::Ordered, ::Any, start::T, step, stop::T) where {T}", "StepRange(start::T, step::S, stop::T) where {T,S}", "StepRange{T,S}(start, step, stop) where {T,S}", "steprange_last(start, step, stop)", "overflow_case(absdiff, absstep)", "steprange_last_empty(start::Integer, step, stop)", "isempty(r::StepRange)", "step(r::StepRange)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)"]
    statement := "For a, s, b of any BitInteger type, a:s:b throws ArgumentError for s == 0 and otherwise denotes the integers a, a+s, ... between a and b: first is a, step is s, isempty iff there are none, last is the last of them, and iteration visits exactly them (all widths, including typemin steps and full-width spans)."
    source := "StepRange docstring (range.jl:289-343); range docstring (range.jl:72-160)"
    status := .proven
    prop := ``StepRangeColon
    thm := some ``stepRangeColon_proven },
  { id := "rangescov-isempty-methods"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, step::T, stop::T) where {T<:Real}", "_colon(::Ordered, ::Any, start::T, step, stop::T) where {T}", "StepRange(start::T, step::S, stop::T) where {T,S}", "StepRange{T,S}(start, step, stop) where {T,S}", "steprange_last(start, step, stop)", "overflow_case(absdiff, absstep)", "steprange_last_empty(start::Integer, step, stop)", "isempty(r::StepRange)", "step(r::StepRange)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)"]
    statement := "For a, s, b of any BitInteger type, a:s:b throws ArgumentError for s == 0 and otherwise denotes the integers a, a+s, ... between a and b: first is a, step is s, isempty iff there are none, last is the last of them, and iteration visits exactly them (all widths, including typemin steps and full-width spans)."
    source := "StepRange docstring (range.jl:289-343); range docstring (range.jl:72-160)"
    status := .proven
    prop := ``StepRangeColon
    thm := some ``stepRangeColon_proven },
  { id := "ranges-ordinal-extremal-pairs"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, step::T, stop::T) where {T<:Real}", "_colon(::Ordered, ::Any, start::T, step, stop::T) where {T}", "StepRange(start::T, step::S, stop::T) where {T,S}", "StepRange{T,S}(start, step, stop) where {T,S}", "steprange_last(start, step, stop)", "overflow_case(absdiff, absstep)", "steprange_last_empty(start::Integer, step, stop)", "isempty(r::StepRange)", "step(r::StepRange)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)"]
    statement := "For a, s, b of any BitInteger type, a:s:b throws ArgumentError for s == 0 and otherwise denotes the integers a, a+s, ... between a and b: first is a, step is s, isempty iff there are none, last is the last of them, and iteration visits exactly them (all widths, including typemin steps and full-width spans)."
    source := "StepRange docstring (range.jl:289-343); range docstring (range.jl:72-160)"
    status := .proven
    prop := ``StepRangeColon
    thm := some ``stepRangeColon_proven },
  { id := "rangescov-integer-unitrange"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "rangescov-colon-same-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "rangescov-unitrange-t"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "rangescov-isempty-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "rangescov-step-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "rangescov-length-small-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "ranges-ordinal-full-width-count"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "rangescov-getindex-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T<:Real}", "UnitRange{T}(start::T, stop::T) where {T<:Real}", "UnitRange(start::T, stop::T) where {T<:Real}", "unitrange_last(start::Integer, stop::Integer)", "first(r::OrdinalRange{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "step(r::AbstractUnitRange{T})", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::AbstractUnitRange{<:smallints})", "length(r::AbstractUnitRange{T})", "checked_length(r::AbstractUnitRange{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)", "step_hp(r::AbstractRange)"]
    statement := "For a, b of any BitInteger type, a:b is the range of the integers a..b (stop normalised to a-1 when empty): first, last, isempty and step 1 agree, iteration visits exactly a..b, length is that count (reduced modulo 2^w when it exceeds the length type), checked_length is the count or OverflowError, and r[i] is a+i-1 for 1 <= i <= count and BoundsError otherwise."
    source := "docstrings of UnitRange (range.jl:405-427), length/checked_length (range.jl:748-766), getindex; invariant: length = number of iterated elements"
    status := .proven
    prop := ``UnitRangeColon
    thm := some ``unitRangeColon_proven },
  { id := "ranges-ordinal-invalid-lower-index"
    juliaFile := "base/range.jl"
    juliaFns := ["_getindex(v::UnitRange{T}, i::Integer) where {T<:OverflowSafe}", "_in_unit_range(v::UnitRange, val, i::Integer)"]
    statement := "r[i] of a UnitRange of any BitInteger type with a nonpositive index of any BitInteger type throws BoundsError."
    source := "checkbounds: the valid indices of a vector are 1:length(v)"
    status := .proven
    prop := ``UnitRangeNonposIndex
    thm := some ``unitRangeNonposIndex_proven },
  { id := "rangescov-length-oneto"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo(stop::T) where {T<:Integer}", "OneTo{T}(stop) where {T<:Integer}", "first(r::OneTo{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::OneTo{<:smallints})", "length(r::OneTo{T}) where {T<:bigints}", "checked_length(r::OneTo{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "unsafe_getindex(v::OneTo{T}, i::Integer)", "_getindex(v::AbstractRange, i::Integer)"]
    statement := "OneTo(n) for n of any BitInteger type is the range 1..n (stop max(0, n)): first is 1, last max(0, n), iteration visits 1..n, length and checked_length are the element count, and r[i] is i for 1 <= i <= n and BoundsError otherwise."
    source := "docstring of Base.OneTo (range.jl:467-486): behaves like 1:n"
    status := .proven
    prop := ``OneToElements
    thm := some ``oneToElements_proven },
  { id := "rangescov-first-oneto"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo(stop::T) where {T<:Integer}", "OneTo{T}(stop) where {T<:Integer}", "first(r::OneTo{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::OneTo{<:smallints})", "length(r::OneTo{T}) where {T<:bigints}", "checked_length(r::OneTo{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "unsafe_getindex(v::OneTo{T}, i::Integer)", "_getindex(v::AbstractRange, i::Integer)"]
    statement := "OneTo(n) for n of any BitInteger type is the range 1..n (stop max(0, n)): first is 1, last max(0, n), iteration visits 1..n, length and checked_length are the element count, and r[i] is i for 1 <= i <= n and BoundsError otherwise."
    source := "docstring of Base.OneTo (range.jl:467-486): behaves like 1:n"
    status := .proven
    prop := ``OneToElements
    thm := some ``oneToElements_proven },
  { id := "rangescov-unsafe-getindex-oneto"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo(stop::T) where {T<:Integer}", "OneTo{T}(stop) where {T<:Integer}", "first(r::OneTo{T})", "last(r::OrdinalRange{T})", "isempty(r::AbstractUnitRange)", "iterate(r::OrdinalRange)", "iterate(r::OrdinalRange{T}, i)", "length(r::OneTo{<:smallints})", "length(r::OneTo{T}) where {T<:bigints}", "checked_length(r::OneTo{<:smallints})", "checked_length(r::AbstractUnitRange{T})", "unsafe_getindex(v::OneTo{T}, i::Integer)", "_getindex(v::AbstractRange, i::Integer)"]
    statement := "OneTo(n) for n of any BitInteger type is the range 1..n (stop max(0, n)): first is 1, last max(0, n), iteration visits 1..n, length and checked_length are the element count, and r[i] is i for 1 <= i <= n and BoundsError otherwise."
    source := "docstring of Base.OneTo (range.jl:467-486): behaves like 1:n"
    status := .proven
    prop := ``OneToElements
    thm := some ``oneToElements_proven },
  { id := "ranges-ordinal-unsigned-index"
    juliaFile := "base/range.jl"
    juliaFns := ["_getindex(::UnitRange{T}, ::Integer)"]
    statement := "r[i] of a unit range a:b at an in-bounds BitInteger index i of any signedness is a + (i - 1)."
    source := "invariant"
    status := .refuted
    prop := ``UnsignedIndexAgreement
    thm := some ``unsignedIndexAgreement_refuted
    issue := "repro/ranges-ordinal-unsigned-index.jl" },
  { id := "ranges-ordinal-typemin-checked-length"
    juliaFile := "base/range.jl"
    juliaFns := ["checked_length(::OrdinalRange{T}) where T<:bigints", "steprange_last"]
    statement := "checked_length(a:s:b) of a nonempty integer range whose element count is representable returns that count, including a typemin step."
    source := "invariant"
    status := .refuted
    prop := ``CheckedLengthCount
    thm := some ``checkedLengthCount_refuted
    issue := "repro/ranges-ordinal-typemin-checked-length.jl" },
  { id := "ranges-ordinal-unsigned-step-last"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRange(::T, ::S, ::T)", "_getindex(::AbstractRange, ::Integer)", "unsafe_getindex(::AbstractRange, ::Integer)"]
    statement := "In a nonempty StepRange(start::T, step::S, stop::T) of BitIntegers, r[length(r)] is last(r)."
    source := "invariant"
    status := .refuted
    prop := ``StepRangeLastIndex
    thm := some ``stepRangeLastIndex_refuted
    issue := "repro/ranges-ordinal-unsigned-step-last.jl" },
  { id := "ranges-keyword-length"
    juliaFile := "base/range.jl"
    juliaFns := ["range(start; length)", "range(start; step, length)", "range_start_length", "range_start_step_length"]
    statement := "range(start; length=n) and range(start; step, length=n) with n >= 0 return n elements when they return."
    source := "invariant"
    status := .refuted
    prop := ``KeywordLength
    thm := some ``keywordLength_refuted
    issue := "repro/ranges-keyword-length.jl" },
  { id := "ranges-keyword-negative-length"
    juliaFile := "base/range.jl"
    juliaFns := ["range(start; length)", "range_start_length"]
    statement := "range(start; length=n) with a negative n throws."
    source := "invariant"
    status := .refuted
    prop := ``KeywordNegativeLength
    thm := some ``keywordNegativeLength_refuted
    issue := "repro/ranges-keyword-negative-length.jl" },
  { id := "ranges-mod-congruence"
    juliaFile := "base/range.jl"
    juliaFns := ["mod(::Integer, ::AbstractUnitRange)"]
    statement := "mod(x, a:b) of a nonempty unit range is a + (x - a) mod (b - a + 1)."
    source := "invariant"
    status := .refuted
    prop := ``ModCongruence
    thm := some ``modCongruence_refuted
    issue := "repro/ranges-mod-congruence.jl" },
  { id := "ranges-range-error-hint"
    juliaFile := "base/range.jl"
    juliaFns := ["range_error"]
    statement := "The ArgumentError hint of range(; step, length) does not claim that the supplied length is missing."
    source := "invariant"
    status := .refuted
    prop := ``RangeErrorHint
    thm := some ``rangeErrorHint_refuted
    issue := "repro/ranges-range-error-hint.jl" },
  { id := "ranges-keyword-stop-length-unitrange"
    juliaFile := "base/range.jl"
    juliaFns := ["range(; stop, length)", "range_stop_length"]
    statement := "range(; stop, length) with BitInteger arguments returns a UnitRange."
    source := "invariant"
    status := .refuted
    prop := ``KeywordStopLengthUnitRange
    thm := some ``keywordStopLengthUnitRange_refuted
    issue := "repro/ranges-keyword-stop-length-unitrange.jl" },
  { id := "ranges-operations-unit-intersect-overflow"
    juliaFile := "base/range.jl"
    juliaFns := ["intersect(::AbstractUnitRange{<:Integer}, ::StepRange{<:Integer})"]
    statement := "intersect(a:b, c:s:d) of one BitInteger type contains every integer both ranges contain."
    source := "invariant"
    status := .refuted
    prop := ``UnitStepIntersectComplete
    thm := some ``unitStepIntersectComplete_refuted
    issue := "repro/ranges-operations-unit-intersect-overflow.jl" },
  { id := "ranges-operations-step-intersect-overflow"
    juliaFile := "base/range.jl"
    juliaFns := ["intersect(::StepRange, ::StepRange)"]
    statement := "intersect(r::StepRange, s::StepRange) of one BitInteger type contains every integer both ranges contain, for any gcdx and lcm meeting their documented contracts."
    source := "invariant"
    status := .refuted
    prop := ``StepStepIntersectComplete
    thm := some ``stepStepIntersectComplete_refuted
    issue := "repro/ranges-operations-step-intersect-overflow.jl" },
  { id := "ranges-operations-reverse-typemin"
    juliaFile := "base/range.jl"
    juliaFns := ["reverse(::OrdinalRange)", "_reverse(::OrdinalRange, ::Colon)"]
    statement := "Reversing an integer step range keeps its number of elements."
    source := "invariant"
    status := .refuted
    prop := ``ReverseLength
    thm := some ``reverseLength_refuted
    issue := "repro/ranges-operations-reverse-typemin.jl" },
  { id := "ranges-operations-slice-overflow"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(::AbstractUnitRange, ::AbstractUnitRange{<:Integer})"]
    statement := "Slicing a unit range a:b by an in-bounds nonempty c:d gives the elements a+c-1, ..., a+d-1."
    source := "invariant"
    status := .refuted
    prop := ``UnitSlice
    thm := some ``unitSlice_refuted
    issue := "repro/ranges-operations-slice-overflow.jl" },
  { id := "ranges-operations-intersect-empty"
    juliaFile := "base/range.jl"
    juliaFns := ["intersect(::StepRange{<:Integer}, ::AbstractUnitRange{<:Integer})"]
    statement := "Intersecting an integer step range with an empty unit range gives an empty range."
    source := "invariant"
    status := .refuted
    prop := ``IntersectEmpty
    thm := some ``intersectEmpty_refuted
    issue := "repro/ranges-operations-intersect-empty.jl" },
  { id := "ranges-operations-intersect-mixed-regression"
    juliaFile := "base/range.jl"
    juliaFns := ["intersect(::AbstractUnitRange{<:Integer}, ::StepRange{<:Integer})"]
    statement := "intersect(a:b, c:s:d) of BitInteger ranges contains only integers both ranges contain."
    source := "invariant"
    status := .refuted
    prop := ``UnitStepIntersectSound
    thm := some ``unitStepIntersectSound_refuted
    issue := "repro/ranges-operations-intersect-mixed-regression.jl" },
  { id := "ranges-operations-slice-unsigned-step"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(::StepRange, ::AbstractRange{<:Integer})"]
    statement := "Slicing an integer step range by a nonempty in-bounds Int step range gives length(index) elements."
    source := "invariant"
    status := .refuted
    prop := ``StepSliceLength
    thm := some ``stepSliceLength_refuted
    issue := "repro/ranges-operations-slice-unsigned-step.jl" },
  { id := "ranges-operations-negate-typemin"
    juliaFile := "base/range.jl"
    juliaFns := ["-(::OrdinalRange)"]
    statement := "-r of an integer step range agrees elementwise with scalar -x in the element type."
    source := "invariant"
    status := .refuted
    prop := ``NegatePointwise
    thm := some ``negatePointwise_refuted
    issue := "repro/ranges-operations-negate-typemin.jl" },
  { id := "ranges-length-overflow-silent"
    juliaFile := "base/range.jl"
    juliaFns := ["length(::AbstractUnitRange{T})"]
    statement := "length(a:b) of a BitInteger unit range is b - a + 1 whenever it returns."
    source := "invariant"
    status := .refuted
    prop := ``UnitLengthCount
    thm := some ``unitLengthCount_refuted
    issue := "repro/ranges-length-overflow-silent.jl" },
  { id := "ranges-collect-full-width-crash"
    juliaFile := "base/range.jl"
    juliaFns := ["Array{T,1}(::AbstractRange{T})", "collect(::AbstractRange)"]
    statement := "Array{T,1}(r), which collect(r) calls, never writes past the vector it allocates."
    source := "invariant"
    status := .refuted
    prop := ``CollectInBounds
    thm := some ``collectInBounds_refuted
    issue := "repro/ranges-collect-full-width-crash.jl" },
  { id := "ranges-eq-wrapped-length"
    juliaFile := "base/range.jl"
    juliaFns := ["==(::AbstractRange, ::AbstractRange)"]
    statement := "r == s for a nonempty unit range r implies that s is nonempty."
    source := "invariant"
    status := .refuted
    prop := ``EqEmptiness
    thm := some ``eqEmptiness_refuted
    issue := "repro/ranges-eq-wrapped-length.jl" },
  { id := "rangescov-steprange-unsigned-step-empty"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRange(::T, ::S, ::T)", "steprange_last_empty(::Integer, step, stop)"]
    statement := "StepRange(start::T, step::S, stop::T) whose step points away from stop is constructed and empty."
    source := "invariant"
    status := .refuted
    prop := ``StepAwayEmpty
    thm := some ``stepAwayEmpty_refuted
    issue := "repro/rangescov-steprange-unsigned-step-empty.jl" },
  { id := "rangescov-unitrange-convert-empty"
    juliaFile := "base/range.jl"
    juliaFns := ["UnitRange{T}(::AbstractUnitRange)"]
    statement := "Converting an empty integer unit range to UnitRange{T} of another BitInteger type gives an empty range."
    source := "invariant"
    status := .refuted
    prop := ``ConvertEmptyUnit
    thm := some ``convertEmptyUnit_refuted
    issue := "repro/rangescov-unitrange-convert-empty.jl" },
  { id := "rangescov-ordinal-add-small-int"
    juliaFile := "base/range.jl"
    juliaFns := ["+(::OrdinalRange, ::OrdinalRange)"]
    statement := "r1 + r2 of equal-length integer unit ranges has elements r1[i] + r2[i], all readable."
    source := "invariant"
    status := .refuted
    prop := ``RangeAddPointwise
    thm := some ``rangeAddPointwise_refuted
    issue := "repro/rangescov-ordinal-add-small-int.jl" },
  { id := "rangescov-issorted-full-width"
    juliaFile := "base/range.jl"
    juliaFns := ["issorted(::AbstractRange)"]
    statement := "issorted(a:s:b) with at least two elements implies a nonnegative step."
    source := "invariant"
    status := .refuted
    prop := ``IssortedStep
    thm := some ``issortedStep_refuted
    issue := "repro/rangescov-issorted-full-width.jl" },
  { id := "tuples-getindex-bool-range"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(t::Tuple, r::AbstractUnitRange)"]
    statement := "Indexing a tuple by a UnitRange{Bool} agrees with logical indexing by the same Bool values."
    source := "invariant"
    status := .refuted
    prop := ``TupleBoolRangeIndex
    thm := some ``tupleBoolRangeIndex_refuted
    issue := "repro/tuples-getindex-bool-range.jl" },
  { id := "floatranges-in-overflow-throws"
    juliaFile := "base/range.jl"
    juliaFns := ["in(::Real, ::AbstractRange{<:Real})", "_in_range"]
    statement := "x in r for a Float64 x and a Float64 LinRange returns a Bool without throwing."
    source := "invariant"
    status := .refuted
    prop := ``LinRangeInTotal
    thm := some ``linRangeInTotal_refuted
    issue := "repro/floatranges-in-overflow-throws.jl" },
  { id := "floatranges-linrange-step-overflow"
    juliaFile := "base/range.jl"
    juliaFns := ["step(::LinRange)", "_in_range"]
    statement := "Every element of a LinRange with finite Float64 endpoints is in it."
    source := "invariant"
    status := .refuted
    prop := ``LinRangeElementsIn
    thm := some ``linRangeElementsIn_refuted
    issue := "repro/floatranges-linrange-step-overflow.jl" },
  { id := "floatranges-linrange-outside-endpoints"
    juliaFile := "base/range.jl"
    juliaFns := ["unsafe_getindex(::LinRange, ::Integer)", "lerpi"]
    statement := "Every element of LinRange(a, b, n) with a <= b lies in [a, b]."
    source := "invariant"
    status := .refuted
    prop := ``LinRangeWithinEndpoints
    thm := some ``linRangeWithinEndpoints_refuted
    issue := "repro/floatranges-linrange-outside-endpoints.jl" },
  { id := "floatranges-linrange-reverse"
    juliaFile := "base/range.jl"
    juliaFns := ["reverse(::LinRange)"]
    statement := "reverse(r)[i] is identical to r[length(r)+1-i] for a Float64 LinRange."
    source := "invariant"
    status := .refuted
    prop := ``LinRangeReverse
    thm := some ``linRangeReverse_refuted
    issue := "repro/floatranges-linrange-reverse.jl" },
  { id := "floatranges-linrange-nonmonotone"
    juliaFile := "base/range.jl"
    juliaFns := ["unsafe_getindex(::LinRange, ::Integer)", "lerpi"]
    statement := "LinRange(a, b, n) with a < b is nondecreasing."
    source := "invariant"
    status := .refuted
    prop := ``LinRangeMonotone
    thm := some ``linRangeMonotone_refuted
    issue := "repro/floatranges-linrange-nonmonotone.jl" },
  { id := "floatranges-linrange-infinite-endpoint"
    juliaFile := "base/range.jl"
    juliaFns := ["unsafe_getindex(::LinRange, ::Integer)", "first(::LinRange)"]
    statement := "r[1] == first(r) and r[n] == last(r) for a LinRange with non-NaN endpoints."
    source := "invariant"
    status := .refuted
    prop := ``LinRangeEndpoints
    thm := some ``linRangeEndpoints_refuted
    issue := "repro/floatranges-linrange-infinite-endpoint.jl" },
  { id := "rangescov-cmp-float-ranges"
    juliaFile := "base/range.jl"
    juliaFns := ["cmp(::T, ::T) where T<:AbstractRange"]
    statement := "cmp(r1, r2) of two Float64 StepRangeLens is 0 only when their elements are equal."
    source := "invariant"
    status := .refuted
    prop := ``StepRangeLenCmp
    thm := some ``stepRangeLenCmp_refuted
    issue := "repro/rangescov-cmp-float-ranges.jl" },
  { id := "rangescov-unitrange-float-last"
    juliaFile := "base/range.jl"
    juliaFns := ["unitrange_last(start, stop)", "UnitRange(::T, ::T) where T<:Real"]
    statement := "UnitRange(a, b) of Float64s with a <= b has last(r) <= b."
    source := "invariant"
    status := .refuted
    prop := ``FloatUnitRangeLast
    thm := some ``floatUnitRangeLast_refuted
    issue := "repro/rangescov-unitrange-float-last.jl" },
  { id := "rangescov-linrange-integer-elements"
    juliaFile := "base/range.jl"
    juliaFns := ["LinRange(::AbstractRange)", "unsafe_getindex(::LinRange, ::Integer)"]
    statement := "Every in-bounds element of LinRange(a:s:b) built from an Int step range can be read."
    source := "invariant"
    status := .refuted
    prop := ``IntLinRangeElements
    thm := some ``intLinRangeElements_refuted
    issue := "repro/rangescov-linrange-integer-elements.jl" },
  { id := "rangescov-logrange-show-unparseable"
    juliaFile := "base/range.jl"
    juliaFns := ["show(::IO, ::LogRange{T})"]
    statement := "show(io, r::LogRange) starts with the qualified name Base.LogRange{, like repr(Base.OneTo(3))."
    source := "invariant"
    status := .refuted
    prop := ``LogRangeShowQualified
    thm := some ``logRangeShowQualified_refuted
    issue := "repro/rangescov-logrange-show-unparseable.jl" },
  { id := "show-range-repr-elements"
    juliaFile := "base/range.jl"
    juliaFns := ["show(io::IO, r::StepRangeLen)", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)", "step(r::StepRangeLen{T}) where {T<:AbstractFloat}", "first(r::StepRangeLen)", "last(r::StepRangeLen)", "_getindex(v::AbstractRange, i::Integer)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T"]
    statement := "For every Float64 StepRangeLen(ref, step, len) that show prints in colon form a:s:b, evaluating that text gives a range with the same length and bitwise-identical elements, for every Float64 repr that parse inverts and every Float64 colon whose result starts at a."
    source := "show/repr docstrings (2-argument show writes parseable code that reproduces the value); base/range.jl:1142-1150"
    status := .refuted
    prop := ``ShowReprElements
    thm := some ``showReprElements_refuted
    issue := "repro/show-range-repr-elements.jl"
    notes := "repr(::Float64), parse(Float64, _) and the twiceprecision.jl colon are typed parameters. The refutation uses a bit-pattern repr with its inverse and the colon values Julia's 0.3:0.1:0.8 returns ([0.3, 0.4, 0.5, 0.6, 0.7, 0.8], repro output); StepRangeLen(0.3, 0.1, 6) prints 0.3:0.1:0.8 but r[4] == 0.6000000000000001." },
  { id := "rangescov-linrange-constructor"
    juliaFile := "base/range.jl"
    juliaFns := ["LinRange(start, stop, len::Integer)", "LinRange{T}(start, stop, len::Integer) where T", "LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}", "first(r::LinRange)", "last(r::LinRange)", "length(r::LinRange)", "isempty(r::LinRange)", "size(r::AbstractRange)", "-(r::LinRange)"]
    statement := "LinRange(a, b, n) of Float64 endpoints throws ArgumentError for n < 0 and for n == 1 with a != b; otherwise first(r) == a, last(r) == b, length(r) == n, size(r) == (n,), isempty(r) iff n == 0, and for n != 1 the negation -r has endpoints -a, -b and length n."
    source := "LinRange docstring, range.jl:552-596; inner constructor range.jl:597-611"
    status := .proven
    prop := ``LinRangeFloatConstruct
    thm := some ``linRangeFloatConstruct_proven },
  { id := "rangescov-linrange-negation"
    juliaFile := "base/range.jl"
    juliaFns := ["-(r::LinRange)", "LinRange{T}(start, stop, len::Integer) where T", "LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}", "first(r::LinRange)", "last(r::LinRange)", "length(r::LinRange)"]
    statement := "LinRange(a, b, n) of Float64 endpoints throws ArgumentError for n < 0 and for n == 1 with a != b; otherwise first(r) == a, last(r) == b, length(r) == n, size(r) == (n,), isempty(r) iff n == 0, and for n != 1 the negation -r has endpoints -a, -b and length n."
    source := "LinRange docstring, range.jl:552-596; -(r::LinRange), range.jl:1325"
    status := .proven
    prop := ``LinRangeFloatConstruct
    thm := some ``linRangeFloatConstruct_proven },
  { id := "rangescov-srl-inner"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "StepRangeLen{T}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "length(r::StepRangeLen)", "isempty(r::StepRangeLen)", "size(r::AbstractRange)", "step(r::StepRangeLen)", "_getindex(v::AbstractRange, i::Integer)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T", "first(r::StepRangeLen)", "last(r::StepRangeLen)", "iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))"]
    statement := "For BitInteger ref and step of one type T and Int len and offset, StepRangeLen(ref, step, len, offset), StepRangeLen{T,T,T}(...) and StepRangeLen{T}(...) throw ArgumentError for len < 0 or an offset outside [1, max(1, len)]; otherwise they return the same range r with length(r) == len, size(r) == (len,), isempty(r) iff len == 0, step(r) == step, r[i] a BoundsError unless 1 <= i <= len, and r[i], first(r), last(r) and iterate(r), iterate(r, k) giving ref + (i - offset) * step whenever that value is representable in T; iterate(r, len) is nothing for len < typemax(Int)."
    source := "StepRangeLen docstring, range.jl:512-531; inner constructor range.jl:533-545"
    status := .proven
    prop := ``SRLIntConstruct
    thm := some ``sRLIntConstruct_proven },
  { id := "rangescov-srl-trs"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "StepRangeLen{T}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "length(r::StepRangeLen)", "isempty(r::StepRangeLen)", "size(r::AbstractRange)", "step(r::StepRangeLen)", "_getindex(v::AbstractRange, i::Integer)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T", "first(r::StepRangeLen)", "last(r::StepRangeLen)", "iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))"]
    statement := "For BitInteger ref and step of one type T and Int len and offset, StepRangeLen(ref, step, len, offset), StepRangeLen{T,T,T}(...) and StepRangeLen{T}(...) throw ArgumentError for len < 0 or an offset outside [1, max(1, len)]; otherwise they return the same range r with length(r) == len, size(r) == (len,), isempty(r) iff len == 0, step(r) == step, r[i] a BoundsError unless 1 <= i <= len, and r[i], first(r), last(r) and iterate(r), iterate(r, k) giving ref + (i - offset) * step whenever that value is representable in T; iterate(r, len) is nothing for len < typemax(Int)."
    source := "StepRangeLen docstring, range.jl:512-531; inner constructor range.jl:533-545"
    status := .proven
    prop := ``SRLIntConstruct
    thm := some ``sRLIntConstruct_proven },
  { id := "rangescov-srl-auto"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "StepRangeLen{T}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "length(r::StepRangeLen)", "isempty(r::StepRangeLen)", "size(r::AbstractRange)", "step(r::StepRangeLen)", "_getindex(v::AbstractRange, i::Integer)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T", "first(r::StepRangeLen)", "last(r::StepRangeLen)", "iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))"]
    statement := "For BitInteger ref and step of one type T and Int len and offset, StepRangeLen(ref, step, len, offset), StepRangeLen{T,T,T}(...) and StepRangeLen{T}(...) throw ArgumentError for len < 0 or an offset outside [1, max(1, len)]; otherwise they return the same range r with length(r) == len, size(r) == (len,), isempty(r) iff len == 0, step(r) == step, r[i] a BoundsError unless 1 <= i <= len, and r[i], first(r), last(r) and iterate(r), iterate(r, k) giving ref + (i - offset) * step whenever that value is representable in T; iterate(r, len) is nothing for len < typemax(Int)."
    source := "StepRangeLen docstring, range.jl:512-531; inner constructor range.jl:533-545"
    status := .proven
    prop := ``SRLIntConstruct
    thm := some ``sRLIntConstruct_proven },
  { id := "rangescov-srl-t"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "StepRangeLen{T}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "length(r::StepRangeLen)", "isempty(r::StepRangeLen)", "size(r::AbstractRange)", "step(r::StepRangeLen)", "_getindex(v::AbstractRange, i::Integer)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T", "first(r::StepRangeLen)", "last(r::StepRangeLen)", "iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))"]
    statement := "For BitInteger ref and step of one type T and Int len and offset, StepRangeLen(ref, step, len, offset), StepRangeLen{T,T,T}(...) and StepRangeLen{T}(...) throw ArgumentError for len < 0 or an offset outside [1, max(1, len)]; otherwise they return the same range r with length(r) == len, size(r) == (len,), isempty(r) iff len == 0, step(r) == step, r[i] a BoundsError unless 1 <= i <= len, and r[i], first(r), last(r) and iterate(r), iterate(r, k) giving ref + (i - offset) * step whenever that value is representable in T; iterate(r, len) is nothing for len < typemax(Int)."
    source := "StepRangeLen docstring, range.jl:512-531; inner constructor range.jl:533-545"
    status := .proven
    prop := ``SRLIntConstruct
    thm := some ``sRLIntConstruct_proven },
  { id := "rangescov-iterate-methods"
    juliaFile := "base/range.jl"
    juliaFns := ["iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))", "_getindex(v::AbstractRange, i::Integer)", "length(r::StepRangeLen)", "length(r::LinRange)"]
    statement := "For Float64 StepRangeLen and LinRange, iterate(r) is iterate(r, 0), iterate(r, k) for 0 <= k < length(r) is (r[k+1], k+1), and iterate(r, length(r)) is nothing for lengths below typemax(Int)."
    source := "iteration protocol (iterate docstring) and AbstractVector indexing order; range.jl:928-933"
    status := .proven
    prop := ``FloatIterateIndexed
    thm := some ``floatIterateIndexed_proven
    notes := "Ordinal-range iteration is stated by UnitRangeColon, StepRangeColon and OneToElements; integer StepRangeLen iteration by SRLIntConstruct." },
  { id := "rangescov-getindex-checked"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "StepRangeLen{T}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "length(r::StepRangeLen)", "isempty(r::StepRangeLen)", "size(r::AbstractRange)", "step(r::StepRangeLen)", "_getindex(v::AbstractRange, i::Integer)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T", "first(r::StepRangeLen)", "last(r::StepRangeLen)", "iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))"]
    statement := "For BitInteger ref and step of one type T and Int len and offset, StepRangeLen(ref, step, len, offset), StepRangeLen{T,T,T}(...) and StepRangeLen{T}(...) throw ArgumentError for len < 0 or an offset outside [1, max(1, len)]; otherwise they return the same range r with length(r) == len, size(r) == (len,), isempty(r) iff len == 0, step(r) == step, r[i] a BoundsError unless 1 <= i <= len, and r[i], first(r), last(r) and iterate(r), iterate(r, k) giving ref + (i - offset) * step whenever that value is representable in T; iterate(r, len) is nothing for len < typemax(Int)."
    source := "StepRangeLen docstring, range.jl:512-531; inner constructor range.jl:533-545"
    status := .proven
    prop := ``SRLIntConstruct
    thm := some ``sRLIntConstruct_proven },
  { id := "range-srl-iterate-typemax-ordinary"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(ref::R, step::S, len::Integer, offset::Integer = 1)", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "StepRangeLen{T,R,S}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "StepRangeLen{T}(ref::R, step::S, len::Integer, offset::Integer = 1) where {T,R,S}", "length(r::StepRangeLen)", "isempty(r::StepRangeLen)", "size(r::AbstractRange)", "step(r::StepRangeLen)", "_getindex(v::AbstractRange, i::Integer)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T", "first(r::StepRangeLen)", "last(r::StepRangeLen)", "iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))"]
    statement := "For BitInteger ref and step of one type T and Int len and offset, StepRangeLen(ref, step, len, offset), StepRangeLen{T,T,T}(...) and StepRangeLen{T}(...) throw ArgumentError for len < 0 or an offset outside [1, max(1, len)]; otherwise they return the same range r with length(r) == len, size(r) == (len,), isempty(r) iff len == 0, step(r) == step, r[i] a BoundsError unless 1 <= i <= len, and r[i], first(r), last(r) and iterate(r), iterate(r, k) giving ref + (i - offset) * step whenever that value is representable in T; iterate(r, len) is nothing for len < typemax(Int)."
    source := "StepRangeLen docstring, range.jl:512-531; inner constructor range.jl:533-545"
    status := .proven
    prop := ``SRLIntConstruct
    thm := some ``sRLIntConstruct_proven },
  { id := "range-srl-iterate-typemax"
    juliaFile := "base/range.jl"
    juliaFns := ["iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))", "StepRangeLen(ref::R, step::S, len::Integer, offset::Integer = 1) where {R,S}", "length(r::StepRangeLen)", "unsafe_getindex(r::StepRangeLen{T}, i::Integer) where T"]
    statement := "For StepRangeLen(ref, step, n) of Ints, iterate(r, n) is nothing, so iteration stops after n elements, for every length n."
    source := "iteration protocol (iterate docstring): iterate(iter, state) returns nothing when no elements remain; range.jl:928-933"
    status := .refuted
    prop := ``SRLIterateEnds
    thm := some ``sRLIterateEnds_refuted
    issue := "repro/range-srl-iterate-typemax.jl"
    notes := "iterate computes i += 1 in Int; for n == typemax(Int) the state wraps to typemin(Int), length(r) < i is false and iterate(r, typemax(Int)) returns (typemax(Int), typemin(Int)). The ordinary-input entry range-srl-iterate-typemax-ordinary (SRLIntConstruct) proves iterate(r, n) === nothing for n < typemax(Int)." },
  { id := "rangescov-range-keyword-errors"
    juliaFile := "base/range.jl"
    juliaFns := ["range(;start=nothing, stop=nothing, length::Union{Integer, Nothing}=nothing, step=nothing)", "range(start; stop=nothing, length::Union{Integer,Nothing}=nothing, step=nothing)", "range(start, stop; length::Union{Integer,Nothing}=nothing, step=nothing)", "_range(start::Nothing, step::Any, stop::Nothing, len::Nothing)", "_range(start::Nothing, step::Any, stop::Any, len::Nothing)", "_range(start::Any, step::Nothing, stop::Nothing, len::Nothing)", "_range(start::Any, step::Any, stop::Nothing, len::Nothing)", "_range(start::Any, step::Any, stop::Any, len::Any)", "range_error(start, step, stop, length)"]
    statement := "For BitInteger arguments of any types, range(; step), range(; step, stop), range(start), range(start; step) and range with all four of start, step, stop, length throw ArgumentError."
    source := "range docstring, range.jl:72-160 (valid invocations: three of start, step, stop, length; two of start, stop, length; one of stop, length)"
    status := .proven
    prop := ``KeywordRangeErrors
    thm := some ``keywordRangeErrors_proven },
  { id := "rangescov-iterate-float"
    juliaFile := "base/range.jl"
    juliaFns := ["iterate(r::Union{StepRangeLen,LinRange}, i::Integer=zero(length(r)))", "_getindex(v::AbstractRange, i::Integer)", "length(r::StepRangeLen)", "length(r::LinRange)"]
    statement := "For Float64 StepRangeLen and LinRange, iterate(r) is iterate(r, 0), iterate(r, k) for 0 <= k < length(r) is (r[k+1], k+1), and iterate(r, length(r)) is nothing for lengths below typemax(Int)."
    source := "iteration protocol (iterate docstring) and AbstractVector indexing order; range.jl:928-933"
    status := .proven
    prop := ``FloatIterateIndexed
    thm := some ``floatIterateIndexed_proven
    notes := "Ordinal-range iteration is stated by UnitRangeColon, StepRangeColon and OneToElements; integer StepRangeLen iteration by SRLIntConstruct." },
  { id := "rangescov-oneto-construction"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo{T}(stop) where {T<:Integer}", "OneTo(stop::T) where {T<:Integer}", "OneTo{T}(r::AbstractRange) where {T<:Integer}", "==(r::OneTo, s::OneTo)", "issubset(r::OneTo, s::OneTo)", "intersect(r::OneTo, s::OneTo)", "union(r::OneTo, s::OneTo)", "first(r::OneTo, n::Integer)"]
    statement := "For OneTo(m) and OneTo(n) of one BitInteger type: OneTo(m) stores max(0, m) and OneTo{Bool}(x) throws ArgumentError; OneTo(m) == OneTo(n) iff max(0,m) == max(0,n); issubset iff max(0,m) <= max(0,n); intersect and union are the OneTo of the min and max of the stops; first(OneTo(m), k) throws ArgumentError for k < 0 and is otherwise OneTo(min(max(0,m), k)); OneTo{T}(a:b) throws ArgumentError unless a == 1 and is otherwise OneTo(b)."
    source := "OneTo docstring, range.jl:449-460; first(r, n) docstring; set semantics of issubset/intersect/union; range.jl:483-507, 1166, 1206-1207, 1315"
    status := .proven
    prop := ``OneToOps
    thm := some ``oneToOps_proven
    notes := "The range and Bool printing in the error messages are typed parameters." },
  { id := "rangescov-oneto-stop"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo{T}(stop) where {T<:Integer}", "OneTo(stop::T) where {T<:Integer}", "OneTo{T}(r::AbstractRange) where {T<:Integer}", "==(r::OneTo, s::OneTo)", "issubset(r::OneTo, s::OneTo)", "intersect(r::OneTo, s::OneTo)", "union(r::OneTo, s::OneTo)", "first(r::OneTo, n::Integer)"]
    statement := "For OneTo(m) and OneTo(n) of one BitInteger type: OneTo(m) stores max(0, m) and OneTo{Bool}(x) throws ArgumentError; OneTo(m) == OneTo(n) iff max(0,m) == max(0,n); issubset iff max(0,m) <= max(0,n); intersect and union are the OneTo of the min and max of the stops; first(OneTo(m), k) throws ArgumentError for k < 0 and is otherwise OneTo(min(max(0,m), k)); OneTo{T}(a:b) throws ArgumentError unless a == 1 and is otherwise OneTo(b)."
    source := "OneTo docstring, range.jl:449-460; first(r, n) docstring; set semantics of issubset/intersect/union; range.jl:483-507, 1166, 1206-1207, 1315"
    status := .proven
    prop := ``OneToOps
    thm := some ``oneToOps_proven
    notes := "The range and Bool printing in the error messages are typed parameters." },
  { id := "rangescov-oneto-of-range"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo{T}(stop) where {T<:Integer}", "OneTo(stop::T) where {T<:Integer}", "OneTo{T}(r::AbstractRange) where {T<:Integer}", "==(r::OneTo, s::OneTo)", "issubset(r::OneTo, s::OneTo)", "intersect(r::OneTo, s::OneTo)", "union(r::OneTo, s::OneTo)", "first(r::OneTo, n::Integer)"]
    statement := "For OneTo(m) and OneTo(n) of one BitInteger type: OneTo(m) stores max(0, m) and OneTo{Bool}(x) throws ArgumentError; OneTo(m) == OneTo(n) iff max(0,m) == max(0,n); issubset iff max(0,m) <= max(0,n); intersect and union are the OneTo of the min and max of the stops; first(OneTo(m), k) throws ArgumentError for k < 0 and is otherwise OneTo(min(max(0,m), k)); OneTo{T}(a:b) throws ArgumentError unless a == 1 and is otherwise OneTo(b)."
    source := "OneTo docstring, range.jl:449-460; first(r, n) docstring; set semantics of issubset/intersect/union; range.jl:483-507, 1166, 1206-1207, 1315"
    status := .proven
    prop := ``OneToOps
    thm := some ``oneToOps_proven
    notes := "The range and Bool printing in the error messages are typed parameters." },
  { id := "rangescov-first-oneto-n"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo{T}(stop) where {T<:Integer}", "OneTo(stop::T) where {T<:Integer}", "OneTo{T}(r::AbstractRange) where {T<:Integer}", "==(r::OneTo, s::OneTo)", "issubset(r::OneTo, s::OneTo)", "intersect(r::OneTo, s::OneTo)", "union(r::OneTo, s::OneTo)", "first(r::OneTo, n::Integer)"]
    statement := "For OneTo(m) and OneTo(n) of one BitInteger type: OneTo(m) stores max(0, m) and OneTo{Bool}(x) throws ArgumentError; OneTo(m) == OneTo(n) iff max(0,m) == max(0,n); issubset iff max(0,m) <= max(0,n); intersect and union are the OneTo of the min and max of the stops; first(OneTo(m), k) throws ArgumentError for k < 0 and is otherwise OneTo(min(max(0,m), k)); OneTo{T}(a:b) throws ArgumentError unless a == 1 and is otherwise OneTo(b)."
    source := "OneTo docstring, range.jl:449-460; first(r, n) docstring; set semantics of issubset/intersect/union; range.jl:483-507, 1166, 1206-1207, 1315"
    status := .proven
    prop := ``OneToOps
    thm := some ``oneToOps_proven
    notes := "The range and Bool printing in the error messages are typed parameters." },
  { id := "rangescov-eq-oneto"
    juliaFile := "base/range.jl"
    juliaFns := ["OneTo{T}(stop) where {T<:Integer}", "OneTo(stop::T) where {T<:Integer}", "OneTo{T}(r::AbstractRange) where {T<:Integer}", "==(r::OneTo, s::OneTo)", "issubset(r::OneTo, s::OneTo)", "intersect(r::OneTo, s::OneTo)", "union(r::OneTo, s::OneTo)", "first(r::OneTo, n::Integer)"]
    statement := "For OneTo(m) and OneTo(n) of one BitInteger type: OneTo(m) stores max(0, m) and OneTo{Bool}(x) throws ArgumentError; OneTo(m) == OneTo(n) iff max(0,m) == max(0,n); issubset iff max(0,m) <= max(0,n); intersect and union are the OneTo of the min and max of the stops; first(OneTo(m), k) throws ArgumentError for k < 0 and is otherwise OneTo(min(max(0,m), k)); OneTo{T}(a:b) throws ArgumentError unless a == 1 and is otherwise OneTo(b)."
    source := "OneTo docstring, range.jl:449-460; first(r, n) docstring; set semantics of issubset/intersect/union; range.jl:483-507, 1166, 1206-1207, 1315"
    status := .proven
    prop := ``OneToOps
    thm := some ``oneToOps_proven
    notes := "The range and Bool printing in the error messages are typed parameters." },
  { id := "rangescov-unitrange-float-empty"
    juliaFile := "base/range.jl"
    juliaFns := ["UnitRange{T}(start::T, stop::T) where {T<:Real}", "unitrange_last(start, stop)", "_getindex(v::UnitRange{T}, i::Integer) where T", "_in_unit_range(v::UnitRange, val, i::Integer)", "last(r::OrdinalRange{T}) where T"]
    statement := "UnitRange(a, b) of Float64 endpoints with b < a (or unordered) is normalized to a:a-1 (first a, last a - 1); r[i] of a UnitRange{Float64} throws BoundsError for i <= 0 and is start + (i - 1) whenever that lies in [start, stop]."
    source := "(:) docstring, range.jl:54 (empty ranges normalized to a:a-1); UnitRange docstring, range.jl:409-411"
    status := .proven
    prop := ``FloatUnitRange
    thm := some ``floatUnitRange_proven },
  { id := "rangescov-getindex-unit-float"
    juliaFile := "base/range.jl"
    juliaFns := ["UnitRange{T}(start::T, stop::T) where {T<:Real}", "unitrange_last(start, stop)", "_getindex(v::UnitRange{T}, i::Integer) where T", "_in_unit_range(v::UnitRange, val, i::Integer)", "last(r::OrdinalRange{T}) where T"]
    statement := "UnitRange(a, b) of Float64 endpoints with b < a (or unordered) is normalized to a:a-1 (first a, last a - 1); r[i] of a UnitRange{Float64} throws BoundsError for i <= 0 and is start + (i - 1) whenever that lies in [start, stop]."
    source := "(:) docstring, range.jl:54 (empty ranges normalized to a:a-1); UnitRange docstring, range.jl:409-411"
    status := .proven
    prop := ``FloatUnitRange
    thm := some ``floatUnitRange_proven },
  { id := "rangescov-colon-widen-zero"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, step, stop::T) where {T<:Real}", "_colon(start::T, step, stop::T) where T"]
    statement := "For BitInteger endpoints of type T and a BitInteger step of type S, a:s:b converts the endpoints to promote_type(T, S), throwing InexactError when either does not fit; once they convert, a zero step throws ArgumentError(\"step cannot be zero\")."
    source := "StepRange docstring, range.jl:289-343; colon docstring, range.jl:30-50"
    status := .proven
    prop := ``MixedStepColon
    thm := some ``mixedStepColon_proven },
  { id := "rangescov-unitrange-construction"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(a::Real, b::Real)", "UnitRange(start, stop)", "UnitRange(r::AbstractUnitRange)"]
    statement := "a:b and UnitRange(a, b) of BitIntegers of two types promote both to promote_type: when both fit, the result is the unit range a, a+1, ..., b of that type and UnitRange(r) of it is the same range; otherwise InexactError."
    source := "colon docstring, range.jl:30-50; promote docstring; range.jl:3, 432-436, 1352"
    status := .proven
    prop := ``MixedUnitColon
    thm := some ``mixedUnitColon_proven },
  { id := "rangescov-colon-promote-start"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(a::Real, b::Real)", "UnitRange(start, stop)", "UnitRange(r::AbstractUnitRange)"]
    statement := "a:b and UnitRange(a, b) of BitIntegers of two types promote both to promote_type: when both fit, the result is the unit range a, a+1, ..., b of that type and UnitRange(r) of it is the same range; otherwise InexactError."
    source := "colon docstring, range.jl:30-50; promote docstring; range.jl:3, 432-436, 1352"
    status := .proven
    prop := ``MixedUnitColon
    thm := some ``mixedUnitColon_proven },
  { id := "rangescov-unitrange-promote-start"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(a::Real, b::Real)", "UnitRange(start, stop)", "UnitRange(r::AbstractUnitRange)"]
    statement := "a:b and UnitRange(a, b) of BitIntegers of two types promote both to promote_type: when both fit, the result is the unit range a, a+1, ..., b of that type and UnitRange(r) of it is the same range; otherwise InexactError."
    source := "colon docstring, range.jl:30-50; promote docstring; range.jl:3, 432-436, 1352"
    status := .proven
    prop := ``MixedUnitColon
    thm := some ``mixedUnitColon_proven },
  { id := "rangescov-unitrange-of-range"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(a::Real, b::Real)", "UnitRange(start, stop)", "UnitRange(r::AbstractUnitRange)"]
    statement := "a:b and UnitRange(a, b) of BitIntegers of two types promote both to promote_type: when both fit, the result is the unit range a, a+1, ..., b of that type and UnitRange(r) of it is the same range; otherwise InexactError."
    source := "colon docstring, range.jl:30-50; promote docstring; range.jl:3, 432-436, 1352"
    status := .proven
    prop := ``MixedUnitColon
    thm := some ``mixedUnitColon_proven },
  { id := "rangescov-argmin-range"
    juliaFile := "base/range.jl"
    juliaFns := ["argmin(r::AbstractRange)", "argmax(r::AbstractRange)", "isassigned(r::AbstractRange, i::Integer)", "sortperm(r::AbstractUnitRange)"]
    statement := "For a:b of BitIntegers whose count n fits the length type: argmin is 1 and argmax is n (ArgumentError when empty), isassigned(r, i) is 1 <= i <= n for any BitInteger index, and sortperm(r) is OneTo(n)."
    source := "argmin, argmax, isassigned and sortperm docstrings"
    status := .proven
    prop := ``UnitIndexQueries
    thm := some ``unitIndexQueries_proven },
  { id := "rangescov-argmax-range"
    juliaFile := "base/range.jl"
    juliaFns := ["argmin(r::AbstractRange)", "argmax(r::AbstractRange)", "isassigned(r::AbstractRange, i::Integer)", "sortperm(r::AbstractUnitRange)"]
    statement := "For a:b of BitIntegers whose count n fits the length type: argmin is 1 and argmax is n (ArgumentError when empty), isassigned(r, i) is 1 <= i <= n for any BitInteger index, and sortperm(r) is OneTo(n)."
    source := "argmin, argmax, isassigned and sortperm docstrings"
    status := .proven
    prop := ``UnitIndexQueries
    thm := some ``unitIndexQueries_proven },
  { id := "rangescov-isassigned"
    juliaFile := "base/range.jl"
    juliaFns := ["argmin(r::AbstractRange)", "argmax(r::AbstractRange)", "isassigned(r::AbstractRange, i::Integer)", "sortperm(r::AbstractUnitRange)"]
    statement := "For a:b of BitIntegers whose count n fits the length type: argmin is 1 and argmax is n (ArgumentError when empty), isassigned(r, i) is 1 <= i <= n for any BitInteger index, and sortperm(r) is OneTo(n)."
    source := "argmin, argmax, isassigned and sortperm docstrings"
    status := .proven
    prop := ``UnitIndexQueries
    thm := some ``unitIndexQueries_proven },
  { id := "rangescov-sortperm-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["argmin(r::AbstractRange)", "argmax(r::AbstractRange)", "isassigned(r::AbstractRange, i::Integer)", "sortperm(r::AbstractUnitRange)"]
    statement := "For a:b of BitIntegers whose count n fits the length type: argmin is 1 and argmax is n (ArgumentError when empty), isassigned(r, i) is 1 <= i <= n for any BitInteger index, and sortperm(r) is OneTo(n)."
    source := "argmin, argmax, isassigned and sortperm docstrings"
    status := .proven
    prop := ``UnitIndexQueries
    thm := some ``unitIndexQueries_proven },
  { id := "rangescov-argextrema-methods"
    juliaFile := "base/range.jl"
    juliaFns := ["argmin(r::AbstractRange)", "argmax(r::AbstractRange)", "isassigned(r::AbstractRange, i::Integer)", "sortperm(r::AbstractUnitRange)"]
    statement := "For a:b of BitIntegers whose count n fits the length type: argmin is 1 and argmax is n (ArgumentError when empty), isassigned(r, i) is 1 <= i <= n for any BitInteger index, and sortperm(r) is OneTo(n)."
    source := "argmin, argmax, isassigned and sortperm docstrings"
    status := .proven
    prop := ``UnitIndexQueries
    thm := some ``unitIndexQueries_proven },
  { id := "range-steprange-extrema"
    juliaFile := "base/range.jl"
    juliaFns := ["minimum(r::AbstractRange)", "maximum(r::AbstractRange)"]
    statement := "For integers a, s, b of one BitInteger type, minimum(a:s:b) and maximum(a:s:b) are the least and greatest of its elements a, a+s, ... between a and b, and throw ArgumentError when the range is empty."
    source := "minimum/maximum docstrings; base/range.jl:883-884"
    status := .proven
    prop := ``StepRangeExtrema
    thm := some ``stepRangeExtrema_proven },
  { id := "range-steprange-length"
    juliaFile := "base/range.jl"
    juliaFns := ["length(r::OrdinalRange{<:smallints})", "length(r::OrdinalRange{T}) where T<:bigints", "checked_length(r::OrdinalRange{<:smallints})", "firstindex(::StepRange{<:smallints,<:bitints})", "firstindex(r::StepRange{<:bigints,<:bitints})"]
    statement := "For integers a, s, b of one BitInteger type, length(a:s:b) is the number of its elements whenever that number fits the length type (Int for 8 to 32 bits, the element type otherwise); checked_length is the same for 8 to 32 bits; firstindex is 1."
    source := "length docstring; checked_length docstring (base/range.jl:700); base/range.jl:820-864"
    status := .proven
    prop := ``StepRangeLength
    thm := some ``stepRangeLength_proven },
  { id := "range-findin-overflow"
    juliaFile := "base/range.jl"
    juliaFns := ["_findin(r::AbstractRange{<:Integer}, span::AbstractUnitRange{<:Integer})", "findall(in(span), r::AbstractRange)"]
    statement := "findall(in(c:d), a:b) for unit ranges of one BitInteger type is the unit range of the indices k of a:b whose element a+k-1 lies in c:d."
    source := "findall docstring: \"Return a vector I of the indices or keys of A where f(A[I]) is true\"; base/range.jl:1295-1320 (\"the index of intersection\")"
    status := .refuted
    prop := ``FindinIndices
    thm := some ``findinIndices_refuted
    issue := "repro/range-findin-overflow.jl"
    notes := "findall(in(Int8(50):Int8(100)), Int8(-100):Int8(-90)) == -105:11: first(span)-first(r) wraps in Int8. No upstream issue found; JuliaLang/julia#48653 is related." },
  { id := "ranges-operations-edge-sum"
    juliaFile := "base/range.jl"
    juliaFns := ["sum(r::AbstractRange{<:Real})"]
    statement := "sum(a:b) for integers a, b of one BitInteger type is the sum of its elements a, ..., b computed in the length type (Int below 64 bits, the element type otherwise, wrapping), whenever the element count fits that type; in particular empty ranges and two-element ranges next to typemin/typemax sum to their iterated values."
    source := "sum docstring: \"Return the sum of all elements in a collection\"; base/range.jl:1468-1475"
    status := .proven
    prop := ``UnitRangeSum
    thm := some ``unitRangeSum_proven },
  { id := "rangescov-findin-inside"
    juliaFile := "base/range.jl"
    juliaFns := ["_findin(r::AbstractRange{<:Integer}, span::AbstractUnitRange{<:Integer})", "findall(in(span), r::AbstractRange)"]
    statement := "findall(in(c:d), a:b) for unit ranges of one BitInteger type with c <= a <= b <= d is 1:length(a:b), whenever the element count fits the length type."
    source := "findall docstring: \"Return a vector I of the indices or keys of A where f(A[I]) is true\"; base/range.jl:1295-1320"
    status := .proven
    prop := ``FindinInside
    thm := some ``findinInside_proven },
  { id := "rangescov-eq-ordinal"
    juliaFile := "base/range.jl"
    juliaFns := ["==(r::Union{StepRange{T},StepRangeLen{T,T}}, s::Union{StepRange{T},StepRangeLen{T,T}}) where {T}", "_has_length_one(r::OrdinalRange)"]
    statement := "For ranges a:s:b and c:u:d of one BitInteger type, r == q holds exactly when they have the same elements in the same order; in particular == is reflexive and an empty range equals exactly the empty ranges."
    source := "== docstring (collections are equal when their elements are equal, in order); base/range.jl:1171-1177"
    status := .proven
    prop := ``StepRangeEq
    thm := some ``stepRangeEq_proven },
  { id := "range-bool-steprange-empty"
    juliaFile := "base/range.jl"
    juliaFns := ["steprange_last_empty(start::Bool, step, stop)", "StepRange(start::T, step::S, stop::T) where {T,S}", "StepRange{T,S}(start, step, stop) where {T,S}", "steprange_last(start, step, stop)"]
    statement := "For Bool endpoints and a nonzero Int step, StepRange(a, s, b) iterates exactly the values a, a+s, a+2s, ... that do not pass b; refuted: StepRange(false, -1, true) has the single element false instead of being empty."
    source := "StepRange docstring, base/range.jl:293-303 (constant step between start and stop); base/range.jl:399"
    status := .refuted
    prop := ``BoolStepRangeElements
    thm := some ``boolStepRangeElements_refuted
    issue := "none found"
    notes := "steprange_last_empty(start::Bool, step, stop) = start ⊻ (step > zero(step)) returns start for a negative step, so the stored last element equals the start." },
  { id := "range-srl-eq-length"
    juliaFile := "base/range.jl"
    juliaFns := ["==(r::Union{StepRange{T},StepRangeLen{T,T}}, s::Union{StepRange{T},StepRangeLen{T,T}}) where {T}", "_has_length_one(r::AbstractRange)"]
    statement := "For integer StepRangeLens r and q, r == q holds exactly when iterating them yields the same element lists; refuted: StepRangeLen(1, 0, 2) == StepRangeLen(1, 0, 3) is true."
    source := "== docstring (collections are equal when their elements are equal, in order); base/range.jl:1171-1178"
    status := .refuted
    prop := ``SRLIntEq
    thm := some ``sRLIntEq_refuted
    issue := "none found"
    notes := "With step 0 the first, step and last of ranges of different lengths agree, and the method never compares lengths." },
  { id := "range-srl-reverse-unsigned"
    juliaFile := "base/range.jl"
    juliaFns := ["_reverse(r::StepRangeLen, ::Colon)"]
    statement := "reverse(r) of an integer StepRangeLen(ref, step, len, offset) iterates the elements of r in reverse order; refuted: reverse(StepRangeLen(UInt8(1), UInt8(2), 3)) throws MethodError."
    source := "reverse docstring (a copy of v reversed from start to stop); base/range.jl:1446-1452"
    status := .refuted
    prop := ``SRLIntReverse
    thm := some ``sRLIntReverse_refuted
    issue := "none found"
    notes := "typeof(r)(r.ref, negate(r.step), length(r), offset) passes a signed step to StepRangeLen{UInt8,UInt8,UInt8,Int}, which has no such constructor." },
  { id := "range-sort-typemin-step"
    juliaFile := "base/range.jl"
    juliaFns := ["sort(r::AbstractRange)", "issorted(r::AbstractRange)"]
    statement := "For an integer step range a:s:b, iterating sort(a:s:b) yields its elements in ascending order (the elements themselves for s > 0, reversed for s < 0); refuted: sort(Int8(0):Int8(-128):Int8(-128)) is empty."
    source := "sort docstring (a sorted copy); base/range.jl:1463"
    status := .refuted
    prop := ``StepRangeSort
    thm := some ``stepRangeSort_refuted
    issue := "none found"
    notes := "reverse(r) negates the step; negating typemin wraps, so the reversed range is empty. Exotic step; see range-sort-typemin-step-ordinary." },
  { id := "ranges-ordinal-bool-unit"
    juliaFile := "base/range.jl"
    juliaFns := ["step(r::AbstractUnitRange{Bool})", "(:)(start::T, stop::T) where {T<:Real}", "unitrange_last(start::T, stop::T) where {T<:Integer}", "length(r::AbstractUnitRange{T}) where T", "isempty(r::AbstractUnitRange)", "iterate(r::OrdinalRange)", "isassigned(r::AbstractRange, i::Integer)"]
    statement := "For Bool endpoints a:b iterates exactly the Bools from a to b (none for true:false) and stops, length and isempty agree with that list, step(r) is true and consecutive elements differ by it, and isassigned(r, i) rejects a Bool index with ArgumentError."
    source := "UnitRange docstring, base/range.jl:407-414; step docstring; base/range.jl:737, 946"
    status := .proven
    prop := ``BoolUnitRange
    thm := some ``boolUnitRange_proven },
  { id := "range-show-int"
    juliaFile := "base/range.jl"
    juliaFns := ["show(io::IO, r::AbstractRange)", "show(io::IO, r::UnitRange)", "show(io::IO, r::OneTo)"]
    statement := "show writes integer ranges as text that reads back as an equal range: a:b as x:y and a:s:b as x:z:y whose parsed parts give ranges with the same elements, for every element printer that writes no colon and that parse inverts; Base.OneTo(n) as Base.OneTo(m) with m the decimal digits of max(0, n)."
    source := "manual, Output (show writes parseable text when possible); base/range.jl:1135-1141"
    status := .proven
    prop := ``ShowIntRanges
    thm := some ``showIntRanges_proven },
  { id := "range-oneto-getindex-oneto"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(r::OneTo{T}, s::OneTo) where T"]
    statement := "For r = Base.OneTo(n) and s = Base.OneTo(m) of any BitInteger types, r[s] is a OneTo with the max(0, m) elements 1, ..., max(0, m) when s lies inside r, and throws BoundsError otherwise."
    source := "manual, Indexing (a range of indices selects the elements at those indices); base/range.jl:1028-1032"
    status := .proven
    prop := ``GetindexOneTo
    thm := some ``getindexOneTo_proven },
  { id := "range-oneto-length-generic"
    juliaFile := "base/range.jl"
    juliaFns := ["length(r::OneTo)"]
    statement := "The generic method length(r::OneTo) applied to BitInteger arithmetic gives length(Base.OneTo(n)) == max(0, n), the number of elements 1, ..., n."
    source := "OneTo docstring, base/range.jl:449 (behaves like 1:n); base/range.jl:806"
    status := .proven
    prop := ``LengthOneToGeneric
    thm := some ``lengthOneToGeneric_proven
    notes := "Julia selects this method for OneTo of integer types outside the BitIntegers; the BitIntegers use the smallints/bigints methods (OneToElements)." },
  { id := "rangescov-mod-methods"
    juliaFile := "base/range.jl"
    juliaFns := ["mod(i::Integer, r::OneTo)"]
    statement := "For r = Base.OneTo(n) of a BitInteger type with n >= 1, mod(i, r) is the y with 1 <= y <= n and n dividing i - y (so mod(0, Base.OneTo(3)) == 3); for an empty OneTo it throws DivideError."
    source := "mod(x::Integer, r::AbstractUnitRange) docstring, base/range.jl:1537-1556; base/range.jl:1558"
    status := .proven
    prop := ``ModOneTo
    thm := some ``modOneTo_proven
    notes := "mod(i, r) for unit ranges is ModCongruence (ranges-mod-congruence, refuted)." },
  { id := "rangescov-ordinal-op-mismatch"
    juliaFile := "base/range.jl"
    juliaFns := ["+(r1::OrdinalRange, r2::OrdinalRange)", "-(r1::OrdinalRange, r2::OrdinalRange)"]
    statement := "For integer step ranges a:s:b and c:u:d of one BitInteger type whose element counts fit the length type and differ, r1 + r2 and r1 - r2 throw DimensionMismatch."
    source := "manual, Arithmetic operators on arrays (dimensions must match); base/range.jl:1503-1509"
    status := .proven
    prop := ``OrdinalOpMismatch
    thm := some ``ordinalOpMismatch_proven },
  { id := "rangescov-add-counted-mismatch"
    juliaFile := "base/range.jl"
    juliaFns := ["+(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S}) where {T,S}"]
    statement := "For integer StepRangeLens built by StepRangeLen(ref, step, len, offset) with different lengths, r1 + r2 throws DimensionMismatch."
    source := "manual, Arithmetic operators on arrays (dimensions must match); base/range.jl:1527-1532"
    status := .proven
    prop := ``SRLAddMismatch
    thm := some ``sRLAddMismatch_proven },
  { id := "range-srl-add-step-overflow"
    juliaFile := "base/range.jl"
    juliaFns := ["+(r1::StepRangeLen{T,S}, r2::StepRangeLen{T,S}) where {T,S}"]
    statement := "For integer StepRangeLens r1, r2 of equal length, (r1 + r2)[i] == r1[i] + r2[i] whenever both elements can be read and their sum is representable; refuted: for r = StepRangeLen(Int8(-60), Int8(100), 2), (r + r)[2] throws InexactError although r[2] + r[2] == 80."
    source := "manual, Arithmetic operators (elementwise on arrays); base/range.jl:1527-1532"
    status := .refuted
    prop := ``SRLAddElements
    thm := some ``sRLAddElements_refuted
    issue := "none found"
    notes := "The sum is StepRangeLen(first(r1)+first(r2), step(r1)+step(r2), len); the step sum 200 wraps to -56 in Int8, so element 2 is -120 - 56 = -176." },
  { id := "range-srl-neg-unsigned"
    juliaFile := "base/range.jl"
    juliaFns := ["-(r::StepRangeLen{T,R,S,L}) where {T,R,S,L}"]
    statement := "For an integer StepRangeLen r, (-r)[i] == -r[i] (scalar negation in T) for every readable element; refuted: element 3 of -StepRangeLen(UInt8(0), UInt8(1), 3) throws InexactError instead of being 0xfe."
    source := "manual, Arithmetic operators (unary minus is elementwise on arrays); base/range.jl:1323-1324"
    status := .refuted
    prop := ``SRLNegElements
    thm := some ``sRLNegElements_refuted
    issue := "none found"
    notes := "-r is StepRangeLen{T,R,S,L}(-r.ref, -r.step, r.len, r.offset); for UInt8 the step 0xff is multiplied by the Int index offset, giving 510." },
  { id := "rangescov-lin-op"
    juliaFile := "base/range.jl"
    juliaFns := ["+(r1::LinRange{T}, r2::LinRange{T}) where T", "-(r1::LinRange{T}, r2::LinRange{T}) where T"]
    statement := "For Float64 LinRanges built by LinRange(a, b, n): r1 + r2 and r1 - r2 throw DimensionMismatch when the lengths differ; with equal lengths n != 1 the result has first element f(a1, a2), last element f(b1, b2) and length n, for every Float64 printer in the error messages."
    source := "manual, Arithmetic operators on arrays; base/range.jl:1511-1518"
    status := .proven
    prop := ``LinRangeOp
    thm := some ``linRangeOp_proven },
  { id := "rangescov-colon-any-invariant"
    juliaFile := "base/range.jl"
    juliaFns := ["_colon(::Any, ::Any, start::T, step, stop::T) where {T}"]
    statement := "Whenever the fallback _colon(::Any, ::Any, start, step, stop) returns for Int arguments, the result is a StepRangeLen with reference value start, step step, reference index 1 and a nonnegative length."
    source := "StepRangeLen docstring, base/range.jl:512-531 (By default ref is the starting value r[1]); base/range.jl:28-29"
    status := .proven
    prop := ``FallbackColonInvariant
    thm := some ``fallbackColonInvariant_proven },
  { id := "rangescov-generic-eq"
    juliaFile := "base/range.jl"
    juliaFns := ["==(r::T, s::T) where {T<:AbstractRange}", "==(r::OrdinalRange, s::OrdinalRange)"]
    statement := "The generic == methods for ranges, invoked on integer step ranges a:s:b and c:u:d of one BitInteger type, return true exactly when the two ranges have the same elements in the same order, including empty and one-element ranges."
    source := "== docstring (collections are equal when they have the same elements in the same order); base/range.jl:1151-1161"
    status := .proven
    prop := ``GenericRangeEquality
    thm := some ``genericRangeEquality_proven },
  { id := "rangescov-float-srl-step"
    juliaFile := "base/range.jl"
    juliaFns := ["step(r::StepRangeLen{T}) where {T<:AbstractFloat}"]
    statement := "step(r) of StepRangeLen(ref, step, len, offset) with Float64 ref and step returns that step bit for bit."
    source := "step docstring, base/range.jl:715-733 (Get the step size of an AbstractRange object); base/range.jl:739"
    status := .proven
    prop := ``FloatingSRLStep
    thm := some ``floatingSRLStep_proven },
  { id := "rangescov-show-linrange"
    juliaFile := "base/range.jl"
    juliaFns := ["show(io::IO, r::LinRange{T}) where {T}"]
    statement := "show(io, LinRange(a, b, n)) with Float64 endpoints writes LinRange{Float64}(x, y, k) where x, y and k parse back as a, b and n, for every element and length printer that a parser inverts."
    source := "manual, Output: show writes a text representation that should be parseable Julia code when possible; base/range.jl:634-646"
    status := .proven
    prop := ``ShowLinRangeRoundTrip
    thm := some ``showLinRangeRoundTrip_proven },
  { id := "floatranges-reverse-involution"
    juliaFile := "base/range.jl"
    juliaFns := ["_reverse(r::StepRangeLen, ::Colon)"]
    statement := "reverse(reverse(r)) has exactly the fields of r (ref, step bits, length and offset) for every Float64 StepRangeLen built by StepRangeLen(ref, step, len, offset), including empty ranges."
    source := "reverse docstring (Return a copy of v reversed from start to stop); base/range.jl:1446-1452"
    status := .proven
    prop := ``FloatSRLReverseInvolution
    thm := some ``floatSRLReverseInvolution_proven },
  { id := "rangescov-srl-convert"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(r::StepRangeLen) where {T,R,S,L}", "StepRangeLen{T}(r::StepRangeLen) where {T}"]
    statement := "Converting an integer StepRangeLen(ref, step, len, offset) to another BitInteger element type, with either constructor, keeps the length and every element ref + (i - offset) * step that is representable in the target type."
    source := "convert docstring (Convert x to a value of type T); base/range.jl:1385-1388"
    status := .proven
    prop := ``SRLConversionElements
    thm := some ``sRLConversionElements_proven },
  { id := "rangescov-steprange-convert"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRange{T1,T2}(r::AbstractRange) where {T1,T2}", "StepRange(r::OrdinalRange{T,S}) where {T,S}", "StepRange{T}(r::OrdinalRange{<:Any,S}) where {T,S}"]
    statement := "StepRange{T1,T2}(r), StepRange(r) and StepRange{T}(r) of an integer step range a:s:b, converted to its own element and step types, all succeed with the same range, whose iteration yields exactly the elements of a:s:b."
    source := "convert docstring (Convert x to a value of type T); base/range.jl:1372-1375"
    status := .proven
    prop := ``StepRangeConvertElements
    thm := some ``stepRangeConvertElements_proven },
  { id := "ranges-operations-edge-membership"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::Real, r::AbstractRange{T}) where {T<:Integer}", "minimum(r::AbstractRange)", "maximum(r::AbstractRange)"]
    statement := "For an integer step range a:s:b of any BitInteger type and an integer x of any BitInteger type, x in a:s:b holds exactly when x equals one of the elements a, a+s, ... between a and b (including steps of typemin, empty ranges and ranges spanning the whole type)."
    source := "in docstring (Determine whether an item is in the given collection); base/range.jl:1491"
    status := .proven
    prop := ``StepRangeMembership
    thm := some ``stepRangeMembership_proven },
  { id := "rangescov-intersect-unit-many"
    juliaFile := "base/range.jl"
    juliaFns := ["intersect(r1::AbstractRange, r2::AbstractRange, r3::AbstractRange, r::AbstractRange...)", "intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})"]
    statement := "intersect(a:b, c:d, e:f, rs...) of integer unit ranges of one BitInteger type iterates, in increasing order, exactly the integers that lie in every argument."
    source := "intersect docstring (the set containing those elements which appear in all of the arguments); base/range.jl:1287"
    status := .proven
    prop := ``IntersectUnitMany
    thm := some ``intersectUnitMany_proven },
  { id := "rangescov-sorting-methods"
    juliaFile := "base/range.jl"
    juliaFns := ["sortperm(r::AbstractRange)", "sortperm(r::AbstractUnitRange)", "issorted(r::AbstractUnitRange)", "issorted(r::AbstractRange)", "sort(r::AbstractUnitRange)", "sort!(r::AbstractUnitRange)"]
    statement := "Integer unit ranges are sorted, sort and sort! return them, and sortperm(a:b) iterates 1, ..., n; for an Int step range a:s:b with representable length n, sortperm(a:s:b) iterates a permutation of 1, ..., n listing the indices of the elements in increasing order of the elements."
    source := "sortperm docstring (a permutation vector I that puts v[I] in sorted order); base/range.jl:1457-1466"
    status := .proven
    prop := ``SortingMethods
    thm := some ``sortingMethods_proven },
  { id := "range-unit-step-getindex-empty"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(r::AbstractUnitRange, s::StepRange{T}) where {T<:Integer}", "_empty_stop(start, step)"]
    statement := "For an integer unit range a:b and an in-bounds integer step range index c:u:d of the same BitInteger type, r[s] returns the range whose elements are a + i - 1 for the indices i of s, in order, including an empty s; refuted: (Int8(-128):Int8(127))[Int8(1):Int8(1):Int8(0)] throws OverflowError."
    source := "getindex docstring and the manual's indexing rules (A[I] is the vector of A[i] for i in I); base/range.jl:1034"
    status := .refuted
    prop := ``GetindexUnitStep
    thm := some ``getindexUnitStep_refuted
    issue := "none found"
    notes := "An empty index range whose start maps to typemin(T) makes _empty_stop throw OverflowError; with Int indices the same input throws InexactError." },
  { id := "range-step-stop-length-count"
    juliaFile := "base/range.jl"
    juliaFns := ["range_step_stop_length(step, a, len::Integer)", "_range(start::Nothing, step::Any, stop::Any, len::Any)"]
    statement := "range(; stop, step, length=n) with BitInteger stop and nonzero step and n >= 0 returns a range of n elements when it returns; refuted: range(stop=typemin(Int)+1, step=2, length=3) is empty."
    source := "range docstring (length is the number of elements); base/range.jl:199"
    status := .refuted
    prop := ``RangeStepStopLength
    thm := some ``rangeStepStopLength_refuted
    issue := "none found"
    notes := "The start is computed with wrapping arithmetic; when it underflows the StepRange is empty." },
  { id := "rangescov-srl-from-range"
    juliaFile := "base/range.jl"
    juliaFns := ["StepRangeLen{T,R,S,L}(r::AbstractRange) where {T,R,S,L}", "StepRangeLen{T}(r::AbstractRange) where {T}"]
    statement := "Converting an integer step range a:s:b with representable length n to StepRangeLen{U,U,U,Int} (any BitInteger U), or an Int range to StepRangeLen{Int}, gives (whenever it returns, and always for StepRangeLen{Int}) a range of length n whose element i is a + (i-1)*s wherever that value is representable in U."
    source := "convert docstring (Convert x to a value of type T); base/range.jl:1392-1395"
    status := .proven
    prop := ``SRLFromRange
    thm := some ``sRLFromRange_proven },
  { id := "rangescov-linrange-from-range"
    juliaFile := "base/range.jl"
    juliaFns := ["LinRange{T,L}(r::AbstractRange) where {T,L}", "LinRange{T,L}(start, stop, len::Integer) where {T,L}"]
    statement := "LinRange{Float64,Int}(a:s:b) of an Int step range of length n returns, for n >= 0 other than 1, and whenever it returns has length n, first element Float64(first(r)) and last element Float64(last(r))."
    source := "convert docstring; LinRange docstring (len linearly spaced elements between start and stop); base/range.jl:612, 1403"
    status := .proven
    prop := ``LinRangeFromIntRange
    thm := some ``linRangeFromIntRange_proven },
  { id := "rangescov-intersect-integer"
    juliaFile := "base/range.jl"
    juliaFns := ["intersect(i::Integer, r::AbstractUnitRange{<:Integer})", "in(x::Integer, r::AbstractUnitRange{<:Integer})"]
    statement := "intersect(i, a:b) for an Int i and an Int unit range a:b returns a unit range whose elements are [i] when i lies in a:b and none otherwise."
    source := "intersect docstring (the set containing those elements which appear in all of the arguments); base/range.jl:1211"
    status := .proven
    prop := ``IntersectIntUnit
    thm := some ``intersectIntUnit_proven },
  { id := "rangescov-char-colon"
    juliaFile := "base/range.jl"
    juliaFns := ["(:)(start::T, stop::T) where {T}", "(:)(start::T, step, stop::T) where {T}", "_colon(start::T, step, stop::T) where T", "steprange_last(start, step, stop)", "steprange_last_empty(start, step, stop)", "length(r::OrdinalRange{T}) where T", "checked_length(r::OrdinalRange{T}) where T", "iterate(r::OrdinalRange{T}, i) where {T}"]
    statement := "For Chars a = Char(p), b = Char(q) with ASCII codepoints p, q and an Int step s: a:b is a:1:b; a:0:b throws ArgumentError; otherwise a:s:b is a StepRange with first element a and step s that is empty exactly when no codepoint p, p+s, p+2s, ... lies between p and q, whose length is the number of such codepoints, whose checked_length is 0 when it is empty and otherwise throws MethodError (there is no checked_sub(::Char, ::Char)), which keeps the given stop b when it is empty and a != b, and whose iteration yields Char(c) for exactly those codepoints c, in order."
    source := "the (:) docstring, base/range.jl:40-63; StepRange docstring; comments at base/range.jl:400 and 747-748"
    status := .proven
    prop := ``CharColon
    thm := some ``charColon_proven },
  { id := "rangescov-in-char"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::AbstractChar, r::AbstractRange{<:AbstractChar})", "minimum(r::AbstractRange)", "maximum(r::AbstractRange)"]
    statement := "For an ASCII Char x = Char(m) and a Char range a:s:b with ASCII endpoints a = Char(p), b = Char(q), x in a:s:b holds exactly when m is one of the codepoints p, p+s, p+2s, ... that lie between p and q."
    source := "in docstring (Determine whether an item is in the given collection): base/range.jl:1495"
    status := .proven
    prop := ``CharRangeIn
    thm := some ``charRangeIn_proven },
  { id := "range-char-in-malformed"
    juliaFile := "base/range.jl"
    juliaFns := ["in(x::AbstractChar, r::AbstractRange{<:AbstractChar})"]
    statement := "For a Char x and the Char range a:b, x in a:b holds exactly when x == c for an element c that iterating a:b yields."
    source := "in docstring (in the sense that it is == to one of the values generated by iterating over the collection): base/range.jl:1495"
    status := .refuted
    prop := ``CharRangeInEq
    thm := some ``charRangeInEq_refuted
    issue := "none found"
    notes := "x = reinterpret(Char, 0x41000041) is malformed with Int(x) == 65, the codepoint of 'A'. For r = 'A':'B', x in r is true, but x is not == to 'A' or 'B'. in(x::AbstractChar, r) compares x with minimum(r) and maximum(r) by bit pattern and only the codepoint Int(x) against the step, so a malformed Char whose bits lie between two elements and whose codepoint equals an element's codepoint is reported as a member." },
  { id := "arrayops-vcat-ranges"
    juliaFile := "base/range.jl"
    juliaFns := ["vcat(rs::AbstractRange{T}...) where T"]
    statement := "For Int unit ranges a_1:b_1, ..., a_m:b_m whose lengths fit in Int: when their total length fits in Int, vcat(r_1, ..., r_m) returns the Vector of all their elements in order (the elements of r_1, then those of r_2, ...); otherwise checked_add throws OverflowError."
    source := "vcat docstring (Concatenate arrays or numbers vertically), base/abstractarray.jl; base/range.jl:1415-1427"
    status := .proven
    prop := ``VcatUnitRanges
    thm := some ``vcatUnitRanges_proven },
  { id := "range-srl-range-index-offset"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(r::StepRangeLen{T}, s::OrdinalRange{S}) where {T, S<:Integer}", "_getindex_hiprec(r::StepRangeLen, i::Integer)"]
    statement := "For an Int StepRangeLen r = StepRangeLen(ref, step, len, offset) and an in-bounds nonempty Int unit range s = c:d, r[s] returns a range w with length(w) == length(s) and w[k] == r[c + k - 1] for every 1 <= k <= length(s)."
    source := "getindex docstring (Return a subset of array A as selected by the indices inds), base/abstractarray.jl; StepRangeLen docstring, base/range.jl:512-531"
    status := .refuted
    prop := ``SRLRangeIndex
    thm := some ``srlRangeIndex_refuted
    issue := "none found (queries: StepRangeLen getindex InexactError; StepRangeLen offset round)"
    notes := "StepRangeLen(0, 1, typemax(Int), typemax(Int))[1:2] throws InexactError: the result offset 1 + round(Int, (r.offset - first(s))/step(s)) is computed in Float64, where typemax(Int) - 1 rounds to 2^63." },
  { id := "range-linrange-range-index-nan"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(r::LinRange{T}, s::OrdinalRange{S}) where {T, S<:Integer}"]
    statement := "For a Float64 LinRange r = LinRange(a, b, n) and an in-bounds nonempty Int unit range s = c:d, r[s] returns a LinRange w with length(w) == length(s), first(w) == r[c] and last(w) == r[d]."
    source := "getindex docstring (Return a subset of array A as selected by the indices inds), base/abstractarray.jl; LinRange docstring, base/range.jl:555"
    status := .refuted
    prop := ``LinRangeRangeIndex
    thm := some ``linRangeRangeIndex_refuted
    issue := "none found (queries: LinRange NaN endpoints differ; LinRange getindex range NaN)"
    notes := "LinRange(-Inf, Inf, 3)[2:2] throws ArgumentError (endpoints differ): r[c:c] is built as LinRange(r[c], r[c], 1) and NaN == NaN is false. Exotic endpoints; see range-linrange-range-index-nan-ordinary." },
  { id := "range-linrange-range-index-nan-ordinary"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(r::LinRange{T}, s::OrdinalRange{S}) where {T, S<:Integer}"]
    statement := "For a Float64 LinRange r = LinRange(a, b, n) and an in-bounds nonempty Int unit range s = c:d whose element r[c] is not NaN, r[s] returns a LinRange w with length(w) == length(s), first(w) == r[c] and last(w) == r[d]."
    source := "getindex docstring (Return a subset of array A as selected by the indices inds), base/abstractarray.jl; LinRange docstring, base/range.jl:555"
    status := .proven
    prop := ``LinRangeRangeIndexOrdinary
    thm := some ``linRangeRangeIndexOrdinary_proven },
  { id := "range-linrange-int-step-overflow"
    juliaFile := "base/range.jl"
    juliaFns := ["_linspace(::Type{T}, start::Integer, stop::Integer, len::Integer) where T", "LinRange{T}(start, stop, len::Integer) where T", "LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}"]
    statement := "For Int a, b, n, _linspace(Int, a, b, n) (= LinRange{Int}(a, b, n)) throws ArgumentError for n < 0, for n == 1 with a != b, and for n >= 2 when n - 1 does not divide b - a; otherwise it returns a LinRange r with first(r) == a, last(r) == b and length(r) == n."
    source := "LinRange docstring (a range with len linearly spaced elements between its start and stop), base/range.jl:555; constructor checks, base/range.jl:597-611"
    status := .refuted
    prop := ``LinspaceIntGeneric
    thm := some ``linspaceIntGeneric_refuted
    issue := "none found (queries: LinRange Int typemin typemax non-integer step; LinRange integer step overflow)"
    notes := "LinRange{Int}(typemin(Int), typemax(Int), 4) throws: the step (2^64 - 1)/3 is an integer, but mod(stop - start, len - 1) sees stop - start wrapped to -1. Exotic endpoints; see range-linrange-int-step-overflow-ordinary." },
  { id := "range-linrange-int-step-overflow-ordinary"
    juliaFile := "base/range.jl"
    juliaFns := ["_linspace(::Type{T}, start::Integer, stop::Integer, len::Integer) where T", "LinRange{T}(start, stop, len::Integer) where T", "LinRange{T,L}(start::T, stop::T, len::L) where {T,L<:Integer}"]
    statement := "For Int a, b, n with b - a representable in Int, _linspace(Int, a, b, n) throws ArgumentError for n < 0, for n == 1 with a != b, and for n >= 2 when n - 1 does not divide b - a; otherwise it returns a LinRange r with first(r) == a, last(r) == b and length(r) == n."
    source := "LinRange docstring (a range with len linearly spaced elements between its start and stop), base/range.jl:555; constructor checks, base/range.jl:597-611"
    status := .proven
    prop := ``LinspaceIntGenericOrdinary
    thm := some ``linspaceIntGenericOrdinary_proven },
  { id := "rangescov-range3-length"
    juliaFile := "base/range.jl"
    juliaFns := ["range(start, stop, length::Integer)", "range_start_stop_length(start, stop, len::Integer)", "range_start_stop_length(start::T, stop::T, len::Integer) where {T<:Integer}"]
    statement := "For BitInteger endpoints a, b and an Int n, and any _linspace(Float64, start::Integer, stop::Integer, len) (twiceprecision.jl:717) that returns ranges of length len: range(a, b, n) of one endpoint type is _linspace(Float64, a, b, n) and has n elements whenever it returns; for two endpoint types it is _linspace(Float64, a', b', n) with a', b' the values of a, b in promote_type, has n elements whenever it returns, and throws InexactError when a or b is not representable in promote_type."
    source := "range docstring (range(start, stop, length)), base/range.jl:73-81, 170; promote docstring"
    status := .proven
    prop := ``RangeIntLength
    thm := some ``rangeIntLength_proven },
  { id := "rangescov-start-stop-length-dispatch"
    juliaFile := "base/range.jl"
    juliaFns := ["range_start_stop_length(start, stop, len::Integer)", "range_start_stop_length(start::T, stop::T, len::Integer) where {T}", "range_start_stop_length(start::T, stop::T, len::Integer) where {T<:Integer}", "_linspace(::Type{T}, start::Integer, stop::Integer, len::Integer) where T"]
    statement := "range(a, b; length=n) has n elements whenever it returns: for BitInteger endpoints of one or two types through _linspace(Float64, ...) (RangeIntLength); for the generic method range_start_stop_length(start::T, stop::T, len), which is LinRange(start, stop, len) with first element Float64(start), last element Float64(stop) and length len, ArgumentError for a negative length or length 1 with different endpoints (RangeStartStopLengthGeneric); and for the generic integer _linspace(Int, a, b, n) with b - a representable (LinspaceIntGenericOrdinary)."
    source := "range docstring; LinRange docstring, base/range.jl:555; base/range.jl:625-632"
    status := .proven
    prop := ``StartStopLengthDispatch
    thm := some ``startStopLengthDispatch_proven },
  { id := "range-intersect-ranges-generic"
    juliaFile := "base/range.jl"
    juliaFns := ["intersect(r1::AbstractRange, r2::AbstractRange)", "in(x::Real, r::AbstractRange{T}) where {T<:Integer}", "minimum(r::AbstractRange)", "maximum(r::AbstractRange)"]
    statement := "For StepRangeLen(ref1, step1, n1, offset1) and StepRangeLen(ref2, step2, n2, offset2) of one BitInteger type whose element values ref + (i - offset) * step all fit in that type, and any unique(r) that returns each element of r once in its original order, intersect(r1, r2) returns a vector without duplicates that contains exactly the values lying in both ranges, listed in the order of the shorter range (r1 when the lengths are equal)."
    source := "intersect docstring ('Construct the set containing those elements which appear in all of the arguments'), base/abstractset.jl:118; base/range.jl:1277-1286 ('To iterate over the shorter range'); unique docstring, base/set.jl"
    status := .proven
    prop := ``IntersectRangesGeneric
    thm := some ``intersectRangesGeneric_proven
    notes := "Julia selects range.jl:1277 for two integer StepRangeLens (checked with which on nightly); a differential check compares the statement with nightly on 17646 random Int8/UInt8/Int16/Int64/UInt64 pairs with no mismatch. The order follows the shorter range, not the first argument (the array order sentence of the docstring; see JuliaLang/julia#64265, closed as a docstring issue)." },
  { id := "tuples-unitrange-index"
    juliaFile := "base/range.jl"
    juliaFns := ["getindex(t::Tuple, r::AbstractUnitRange)"]
    statement := "For Int endpoints a, b whose range a:b has a length representable in Int, t[a:b] (including the front/tail shortcuts for ranges longer than 10) is () when a:b is empty, the entries t[a], ..., t[b] when 1 <= a and b <= length(t), and throws BoundsError otherwise, as indexing a tuple elementwise does."
    source := "getindex(t::Tuple, r::AbstractUnitRange), base/range.jl:449-466, agrees with getindex(t::Tuple, b::AbstractArray), base/tuple.jl:36, and t[i] = getfield(t, i), base/tuple.jl:33"
    status := .proven
    prop := ``TupleUnitRangeIndex
    thm := some ``tupleUnitRangeIndex_proven
    notes := "A differential check compares the statement with nightly for tuple lengths 0-25 and all endpoints near the bounds (3983 cases, no mismatch)." } ]

end JuliaLean.Proofs.base.range
