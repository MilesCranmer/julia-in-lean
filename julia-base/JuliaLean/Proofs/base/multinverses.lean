import JuliaLean.base.multinverses
import JuliaLean.base.intfuncs
import JuliaLean.base.div
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.div
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.multinverses

open JuliaLean JuliaLean.base.multinverses JuliaLean.Registry
open JuliaLean.Proofs.base.int


/-- Supplemental type-dispatch facts retained from the existing aggregate contracts. -/
def UnsignedTypeSpecification : Prop :=
  unsignedTypeBool = .u64 ∧
  unsignedTypeInt8 = IntTy.toUnsigned .i8 ∧
  unsignedTypeInt16 = IntTy.toUnsigned .i16 ∧
  unsignedTypeInt32 = IntTy.toUnsigned .i32 ∧
  unsignedTypeInt64 = IntTy.toUnsigned .i64 ∧
  unsignedTypeInt128 = IntTy.toUnsigned .i128 ∧
  (∀ t : IntTy, ∀ h : t.signed = false,
    unsignedTypeUnsigned bitDomains t h = IntTy.toUnsigned t) ∧
  (∀ {types : List Type} (slurp : JuliaTuple types),
    unsignedTypeBottom slurp =
      .error ⟨"unsigned", .cons JuliaLean.base.int.UnionBottom.type slurp⟩)

/-- Zero is rejected by the inner constructors and both public constructor paths. -/
def ZeroDivisorsRejected : Prop :=
  ∀ t : IntTy,
    (∀ h : t.signed = true,
      (signedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
          h (JInt.lit t 0) = some (.error (.argumentError "cannot compute magic for d == 0"))) ∧
      (signedMultiplicativeInverse bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
          h (JInt.lit t 0) = some (.error (.argumentError "cannot compute magic for d == 0"))) ∧
      (multiplicativeinverseSigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
          h (JInt.lit t 0) = some (.error (.argumentError "cannot compute magic for d == 0")))) ∧
    (∀ h : t.signed = false,
      (unsignedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
          h (JInt.lit t 0) = some (.error (.argumentError "cannot compute magic for d == 0"))) ∧
      (unsignedMultiplicativeInverse bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
          h (JInt.lit t 0) = some (.error (.argumentError "cannot compute magic for d == 0"))) ∧
      (multiplicativeinverseUnsigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
          h (JInt.lit t 0) = some (.error (.argumentError "cannot compute magic for d == 0"))))

/-- Constant division agrees with checked Base division except for typemin divided by negative one. -/
def SignedInverseDivision : Prop :=
  ∀ (t : IntTy) (h : t.signed = true) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      signedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        (a.val ≠ (JInt.typemin t).val ∨ d.val ≠ -1) →
          divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
            (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits))
/-- Unsigned construction succeeds for every nonzero divisor and all dividends divide correctly. -/
def UnsignedInverseDivision : Prop :=
  ∀ (t : IntTy) (h : t.signed = false) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      unsignedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        divUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits))

/-- Remainder and modulus agree with their installed integer methods at every width. -/
def InverseRemainderAndModulus : Prop :=
  (∀ (t : IntTy) (h : t.signed = true) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      signedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)) ∧
        modSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.div.modBitInteger a d).map (fun m => (⟨t, m⟩ : Bits))) ∧
  (∀ (t : IntTy) (h : t.signed = false) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      unsignedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)) ∧
        modUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.div.modBitInteger a d).map (fun m => (⟨t, m⟩ : Bits)))

/-- Inverse divrem matches Base on signed ordinary inputs and every unsigned input. -/
def InverseDivremMatchesBase : Prop :=
  (∀ (t : IntTy) (h : t.signed = true) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      signedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      ∀ a : JInt t,
        (a.val ≠ (JInt.typemin t).val ∨ d.val ≠ -1) →
          divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
            (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
              (JuliaLean.base.intfuncs.divremBits a d).map
                (fun (q, r) => ((⟨t, q⟩ : Bits), (⟨t, r⟩ : Bits)))) ∧
  (∀ (t : IntTy) (h : t.signed = false) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      unsignedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      ∀ a : JInt t,
        divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            (JuliaLean.base.intfuncs.divremBits a d).map
              (fun (q, r) => ((⟨t, q⟩ : Bits), (⟨t, r⟩ : Bits))))

/-- Dispatch through multiplicativeinverse terminates and retains the nonzero divisor. -/
def MultiplicativeInverseDispatchPreservesDivisor : Prop :=
  (∀ (t : IntTy) (h : t.signed = true) (d : JInt t), d.val ≠ 0 →
    (multiplicativeinverseSigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits) h d).map
      (Except.map (fun inverse => inverse.divisor)) = some (.ok d)) ∧
  (∀ (t : IntTy) (h : t.signed = false) (d : JInt t), d.val ≠ 0 →
    (multiplicativeinverseUnsigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits) h d).map
      (Except.map (fun inverse => inverse.divisor)) = some (.ok d))

/-- Both signed public construction paths preserve divisor and match ordinary div/rem outside signed overflow. -/
def SignedPublicAPIBehavior : Prop :=
  ∀ (t : IntTy) (h : t.signed = true) (d : JInt t), d.val ≠ 0 →
    (∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      signedMultiplicativeInverse bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        ((a.val ≠ (JInt.typemin t).val ∨ d.val ≠ -1) →
          divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
            (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits))) ∧
        rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits))) ∧
    (∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      multiplicativeinverseSigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        ((a.val ≠ (JInt.typemin t).val ∨ d.val ≠ -1) →
          divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
            (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits))) ∧
        rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)))

/-- Both unsigned public construction paths give correct division and remainder. -/
def UnsignedPublicAPIBehavior : Prop :=
  ∀ (t : IntTy) (h : t.signed = false) (d : JInt t), d.val ≠ 0 →
    (∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      unsignedMultiplicativeInverse bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        divUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits)) ∧
        rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits))) ∧
    (∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      multiplicativeinverseUnsigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        divUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits)) ∧
        rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)))

def MultiplicativeInversePublicAPI : Prop :=
  ZeroDivisorsRejected ∧ SignedPublicAPIBehavior ∧
    UnsignedPublicAPIBehavior ∧ UnsignedTypeSpecification

def UnsignedMultiplicativeInverseCorrect : Prop :=
  UnsignedInverseDivision ∧ InverseRemainderAndModulus

def SignedInverseDivisionAndDivremRound3 : Prop :=
  SignedInverseDivision ∧ InverseDivremMatchesBase

def SignedInverseDivisionAndDivrem : Prop :=
  (∀ (t : IntTy) (h : t.signed = true) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      multiplicativeinverseSigned bitDomains
        (bitsCallees JuliaLean.base.intfuncs.divremBits) h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits)) ∧
        divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            (JuliaLean.base.intfuncs.divremBits a d).map
              (fun (q, r) => ((⟨t, q⟩ : Bits), (⟨t, r⟩ : Bits)))) ∧
  (∀ (t : IntTy) (h : t.signed = false) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      unsignedInverseConstructor bitDomains
        (bitsCallees JuliaLean.base.intfuncs.divremBits) h d = some (.ok inverse) ∧
      ∀ a : JInt t,
        divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            (JuliaLean.base.intfuncs.divremBits a d).map
              (fun (q, r) => ((⟨t, q⟩ : Bits), (⟨t, r⟩ : Bits))))

def MultiplicativeInverseSourceBehavior : Prop :=
  MultiplicativeInversePublicAPI ∧ SignedInverseDivision ∧
    UnsignedInverseDivision ∧ InverseRemainderAndModulus ∧
    InverseDivremMatchesBase ∧ MultiplicativeInverseDispatchPreservesDivisor

/--
Independent integer specification on ordinary signed inputs. The constructor must succeed
for every nonzero divisor before any dividend is selected. Only the unrepresentable quotient
is excluded from the dividend clause. There is no successful-run hypothesis.
-/
def SignedOrdinaryArithmetic : Prop :=
  ∀ (t : IntTy) (h : t.signed = true) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      multiplicativeinverseSigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t, (a.val ≠ (JInt.typemin t).val ∨ d.val ≠ -1) →
        ∃ q r m dq dr : JInt t,
          divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
            .ok ⟨t, q⟩ ∧
          rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
            (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            .ok ⟨t, r⟩ ∧
          modSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
            .ok ⟨t, m⟩ ∧
          divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
            (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            .ok (⟨t, dq⟩, ⟨t, dr⟩) ∧
          q.val = a.val.tdiv d.val ∧
          r.val = a.val.tmod d.val ∧
          m.val = a.val.fmod d.val ∧
          dq.val = a.val.tdiv d.val ∧
          dr.val = a.val.tmod d.val ∧
          a.val = q.val * d.val + r.val ∧
          r.val.natAbs < d.val.natAbs ∧
          (r.val = 0 ∨ (r.val < 0 ↔ a.val < 0)) ∧
          m.val.natAbs < d.val.natAbs ∧
          (m.val = 0 ∨ (m.val < 0 ↔ d.val < 0))

/-- Independent exact division and reduction specification on all unsigned inputs. -/
def UnsignedArithmetic : Prop :=
  ∀ (t : IntTy) (h : t.signed = false) (d : JInt t), d.val ≠ 0 →
    ∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      multiplicativeinverseUnsigned bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        ∃ q r m dq dr : JInt t,
          divUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
            .ok ⟨t, q⟩ ∧
          rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
            (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            .ok ⟨t, r⟩ ∧
          modUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
            .ok ⟨t, m⟩ ∧
          divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
            (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
            .ok (⟨t, dq⟩, ⟨t, dr⟩) ∧
          q.val = a.val.tdiv d.val ∧
          r.val = a.val.tmod d.val ∧
          m.val = a.val.fmod d.val ∧
          dq.val = a.val.tdiv d.val ∧
          dr.val = a.val.tmod d.val ∧
          a.val = q.val * d.val + r.val ∧
          0 ≤ r.val ∧ r.val < d.val ∧
          0 ≤ m.val ∧ m.val < d.val

private theorem bitsCallees_rem_same {t : IntTy} (a b : JInt t) :
    (bitsCallees JuliaLean.base.intfuncs.divremBits).rem ⟨t, a⟩ ⟨t, b⟩ =
      (I.remSame a b).map (fun r => (⟨t, r⟩ : Bits)) := by
  cases t <;> rfl

private theorem bitsCallees_divrem_same {t : IntTy} (a b : JInt t) :
    (bitsCallees JuliaLean.base.intfuncs.divremBits).divrem ⟨t, a⟩ ⟨t, b⟩ =
      (do let (q, r) ← JuliaLean.base.intfuncs.divremBits a b
          pure (⟨t, q⟩, ⟨t, r⟩)) := by
  cases t <;> rfl
private theorem intConvert_self {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.convert t x = .ok x := by
  simp only [JuliaLean.base.int.convert, JInt.convert, dif_pos x.property]

private theorem bitsCallees_convert_self {t : IntTy} (x : JInt t) :
    (bitsCallees JuliaLean.base.intfuncs.divremBits).convert t ⟨t, x⟩ =
      .ok ⟨t, x⟩ := by
  change (I.convert t x).map (fun y => (⟨t, y⟩ : Bits)) = .ok ⟨t, x⟩
  rw [intConvert_self]
  rfl

private theorem bitsCallees_field_self {t : IntTy} (x : JInt t) :
    (bitsCallees JuliaLean.base.intfuncs.divremBits).field t ⟨t, x⟩ =
      .ok x := by
  change I.convert t x = .ok x
  exact intConvert_self x

theorem mulHi_val {t : IntTy} (a b : JInt t) :
    (mulHi a b).val = (a.val * b.val) / 2 ^ t.bits := by
  cases t
  all_goals unfold mulHi
  case i128 => exact JuliaLean.Proofs.base.int.mulHiI128_val a b
  case u128 => exact JuliaLean.Proofs.base.int.mulHiU128_val a b
  all_goals
    apply JuliaLean.Proofs.base.int.mulHiExact_proven _ _ rfl
    intro x
    rw [JuliaLean.Proofs.base.int.widenTo_val]
    apply wrapInt_of_inRange
    have hx := x.property
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx ⊢
    omega

theorem remainder_of_wrapped_quotient {t : IntTy} (a d q : JInt t)
    (hq : q.val = wrapInt t (a.val.tdiv d.val)) :
    JuliaLean.base.int.subWrap a (JuliaLean.base.int.mulWrap q d) =
      JInt.wrap t (a.val.tmod d.val) := by
  apply JuliaLean.Proofs.base.int.jint_eq
  rw [JuliaLean.Proofs.base.int.subWrapWraps_proven,
    JuliaLean.Proofs.base.int.mulWrapWraps_proven, hq,
    JuliaLean.Proofs.base.int.wrapInt_mul_left,
    JuliaLean.Proofs.base.int.wrapInt_sub_right]
  have h := Int.tmod_add_mul_tdiv a.val d.val
  have heq : a.val - a.val.tdiv d.val * d.val = a.val.tmod d.val := by
    rw [Int.mul_comm] at h
    omega
  exact congrArg (wrapInt t) heq

theorem signed_mod_expansion {t : IntTy} (ht : t.signed = true)
    (a d : JInt t) (hd : d.val ≠ 0) (hd1 : d.val ≠ -1) :
    JInt.mod a d = .ok (a -
      (JInt.wrap t (a.val.tdiv d.val) - JInt.lit t
        (if ((a.val < 0 ∧ 0 ≤ d.val) ∨ (0 ≤ a.val ∧ d.val < 0)) ∧
          (JInt.wrap t (a.val.tdiv d.val) * d).val ≠ a.val then 1 else 0)) * d) := by
  have hdiv : JInt.div a d = .ok (JInt.wrap t (a.val.tdiv d.val)) := by
    simp only [JInt.div, hd, if_false]
    rw [if_neg (by rintro ⟨_, _, h⟩; exact hd1 h)]
  simp only [JInt.mod, ht, if_true, hd1, if_false, JInt.fld, hdiv]
  rfl

theorem signed_signbit_val {t : IntTy} (ht : t.signed = true) (a : JInt t) :
    JuliaLean.base.int.signbit a = decide (a.val < 0) := by
  simp only [JuliaLean.base.int.signbit, ht, if_true]
  exact (JuliaLean.Proofs.base.int.signPredicates_proven t a).1

private theorem magic_divmod_of_eq {x c q r : Int} (hc : 0 < c)
    (h : x = c * q + r) (h0 : 0 ≤ r) (h1 : r < c) :
    x / c = q ∧ x % c = r := by
  have hq : x / c = q := by
    subst h
    rw [Int.add_comm, Int.mul_comm, Int.add_mul_ediv_right _ _ (by omega : c ≠ 0),
      Int.ediv_eq_zero_of_lt h0 h1, Int.zero_add]
  refine ⟨hq, ?_⟩
  rw [Int.emod_def, hq]
  omega

private theorem magic_ediv_eq_of_bounds {x c q : Int} (hc : 0 < c)
    (h1 : c * q ≤ x) (h2 : x < c * q + c) : x / c = q :=
  (magic_divmod_of_eq hc (show x = c * q + (x - c * q) by omega)
    (by omega) (by omega)).1

private theorem magic_le_of_mul_le {D b c : Int} (hD : 0 < D)
    (h : D * b ≤ D * c) : b ≤ c := by
  rcases (show b ≤ c ∨ c + 1 ≤ b by omega) with h' | h'
  · exact h'
  · have := Int.mul_le_mul_of_nonneg_left h' (Int.le_of_lt hD)
    rw [Int.mul_add, Int.mul_one] at this
    omega

private theorem magic_lt_of_mul_lt {D b c : Int} (hD : 0 < D)
    (h : D * b < D * c) : b < c := by
  rcases (show b < c ∨ c ≤ b by omega) with h' | h'
  · exact h'
  · have := Int.mul_le_mul_of_nonneg_left h' (Int.le_of_lt hD)
    omega

private theorem magic_mul_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a * b := by
  have := Int.mul_le_mul_of_nonneg_left hb ha
  rwa [Int.mul_zero] at this

theorem unsigned_magic_div {W D nc K ρ X m e A : Int}
    (hD : 0 < D) (hK : 1 ≤ K) (hnc : nc = K * D)
    (hρ1 : ρ < D) (hW : W - 1 = nc + ρ) (hX : 0 < X)
    (hWX : ∃ j, X = W * j) (hm : D * m = X + e)
    (he0 : 0 ≤ e) (he1 : e < D) (hen : e * nc < X)
    (hA0 : 0 ≤ A) (hA1 : A < W) : A * m / X = A / D := by
  have hq := Int.mul_ediv_add_emod A D
  have hr0 := Int.emod_nonneg A (by omega : D ≠ 0)
  have hr1 := Int.emod_lt_of_pos A hD
  obtain ⟨q, hqd⟩ : ∃ q, q = A / D := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r, r = A % D := ⟨_, rfl⟩
  rw [← hqd, ← hrd] at hq
  rw [← hrd] at hr0 hr1
  rw [← hqd]
  have hDX : X ≤ (D - r) * X := by
    have := Int.mul_le_mul_of_nonneg_right (show 1 ≤ D - r by omega)
      (Int.le_of_lt hX)
    rwa [Int.one_mul] at this
  have hND : D ≤ nc := by
    have := Int.mul_le_mul_of_nonneg_right hK (Int.le_of_lt hD)
    rw [Int.one_mul] at this
    omega
  have hen' : nc * e < X := by rw [Int.mul_comm]; exact hen
  have hqK : q ≤ K := by
    have h1 : D * q < D * (K + 1) := by
      rw [Int.mul_add, Int.mul_one, Int.mul_comm D K]
      omega
    have := magic_lt_of_mul_lt hD h1
    omega
  have hkey : A * e < (D - r) * X := by
    rcases (show q < K ∨ q = K by omega) with hlt | heq
    · have h1 := Int.mul_le_mul_of_nonneg_left (show q ≤ K - 1 by omega)
        (Int.le_of_lt hD)
      rw [Int.mul_sub, Int.mul_one, Int.mul_comm D K] at h1
      have h2 := Int.mul_le_mul_of_nonneg_right (show A ≤ nc by omega) he0
      omega
    · rw [heq, Int.mul_comm] at hq
      rcases (show r = D - 1 ∨ r ≤ D - 2 by omega) with hr | hr
      · obtain ⟨j, hj⟩ := hWX
        have hWK : W = D * (K + 1) := by
          rw [Int.mul_add, Int.mul_one, Int.mul_comm D K]
          omega
        have h1 : D * (m - (K + 1) * j) = e := by
          rw [Int.mul_sub, ← Int.mul_assoc, ← hWK]
          omega
        have he : e = 0 := by
          rcases (show m - (K + 1) * j ≤ -1 ∨
              m - (K + 1) * j = 0 ∨ 1 ≤ m - (K + 1) * j by omega) with h | h | h
          · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hD)
            omega
          · rw [h, Int.mul_zero] at h1
            omega
          · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hD)
            omega
        rw [he, Int.mul_zero]
        omega
      · have h1 := Int.mul_le_mul_of_nonneg_right (show r ≤ nc by omega) he0
        have h2 : A * e = nc * e + r * e := by
          rw [← hq, ← hnc, Int.add_mul]
        have h3 := Int.mul_le_mul_of_nonneg_right (show 2 ≤ D - r by omega)
          (Int.le_of_lt hX)
        omega
  have h1 : D * (A * m) = A * X + A * e := by
    rw [Int.mul_left_comm, hm, Int.mul_add]
  have h2 : A * X = D * (X * q) + r * X := by
    rw [← hq, Int.add_mul, Int.mul_assoc, Int.mul_comm q X]
  have h3 : (D - r) * X = D * X - r * X := Int.sub_mul _ _ _
  have h4 : D * (X * q + X) = D * (X * q) + D * X := Int.mul_add _ _ _
  have h5 := magic_mul_nonneg hr0 (Int.le_of_lt hX)
  have h6 := magic_mul_nonneg hA0 he0
  apply magic_ediv_eq_of_bounds hX
  · apply magic_le_of_mul_le hD
    omega
  · apply magic_lt_of_mul_lt hD
    omega

theorem unsigned_magic_tdiv {W D nc K ρ X m e A : Int}
    (hD : 0 < D) (hK : 1 ≤ K) (hnc : nc = K * D)
    (hρ1 : ρ < D) (hW : W - 1 = nc + ρ) (hX : 0 < X)
    (hWX : ∃ j, X = W * j) (hm : D * m = X + e)
    (he0 : 0 ≤ e) (he1 : e < D) (hen : e * nc < X)
    (hA0 : 0 ≤ A) (hA1 : A < W) : A * m / X = A.tdiv D := by
  rw [Int.tdiv_eq_ediv_of_nonneg hA0]
  exact unsigned_magic_div hD hK hnc hρ1 hW hX hWX hm he0 he1 hen hA0 hA1


theorem unsignedStop_exact (X C E : Int) (hC : 0 < C) :
    ¬ (X / C < E ∨ (X / C = E ∧ X % C = 0)) ↔ E * C < X := by
  have hx := Int.emod_add_mul_ediv X C
  have hr0 := Int.emod_nonneg X (by omega : C ≠ 0)
  have hr1 := Int.emod_lt_of_pos X hC
  constructor
  · intro hs
    have hcases : E + 1 ≤ X / C ∨ (E = X / C ∧ 0 < X % C) := by omega
    rcases hcases with h | ⟨h, hr⟩
    · have hm := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hC)
      rw [Int.add_mul, Int.one_mul] at hm
      rw [Int.mul_comm C (X / C)] at hx
      omega
    · rw [h]
      rw [Int.mul_comm C (X / C)] at hx
      omega
  · intro hlt hc
    rw [Int.mul_comm C (X / C)] at hx
    rcases hc with h | ⟨h, hr⟩
    · have hm := Int.mul_le_mul_of_nonneg_right
        (show X / C + 1 ≤ E by omega) (Int.le_of_lt hC)
      rw [Int.add_mul, Int.one_mul] at hm
      omega
    · rw [h, hr, Int.zero_add] at hx
      omega

theorem zeroDivisorsRejected_proven : ZeroDivisorsRejected := by
  intro t
  cases t <;> constructor <;> intro h <;>
    first
    | contradiction
    | (repeat' constructor) <;> rfl
theorem unsignedTypeSpecification_proven : UnsignedTypeSpecification := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro t h
    cases t <;> cases h <;> rfl
  · intro types slurp
    rfl


theorem whileLoop_total_of_step {E S A : Type}
    (step : S → Except E (Sum A S)) (invariant : S → Prop) (measure : S → Nat)
    (progress : ∀ s, invariant s →
      (∃ a, step s = .ok (.inl a)) ∨
      ∃ next, step s = .ok (.inr next) ∧ invariant next ∧ measure next < measure s) :
    ∀ s, invariant s → ∃ a, whileLoop step s = some (.ok a) := by
  suffices total : ∀ fuel s, measure s < fuel → invariant s →
      ∃ a, whileLoop step s = some (.ok a) from
    fun s hs => total (measure s + 1) s (by omega) hs
  intro fuel
  induction fuel with
  | zero =>
      intro s h _
      omega
  | succ fuel ih =>
      intro s h hs
      rcases progress s hs with ⟨a, ha⟩ | ⟨next, hnext, hn, hm⟩
      · exact ⟨a, by rw [whileLoop.eq_def, ha]⟩
      · obtain ⟨a, ha⟩ := ih next (by omega) hn
        exact ⟨a, by rw [whileLoop.eq_def, hnext]; exact ha⟩

theorem doubled_divmod (d x q r c : Int) (hd : 0 < d)
    (hx : x = q * d + r) (hr0 : 0 ≤ r) (hr1 : r < d)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (2 * x + c) / d = 2 * q + (if d ≤ 2 * r + c then 1 else 0) ∧
    (2 * x + c) % d = (if d ≤ 2 * r + c then 2 * r + c - d else 2 * r + c) := by
  have hm : d * (2 * q) = 2 * (q * d) := by
    rw [Int.mul_comm d, Int.mul_assoc]
  by_cases h : d ≤ 2 * r + c
  · simp only [if_pos h]
    apply magic_divmod_of_eq hd
    · rw [Int.mul_add, Int.mul_one, hm]
      omega
    · omega
    · omega
  · simp only [if_neg h, Int.add_zero]
    apply magic_divmod_of_eq hd
    · rw [hm]
      omega
    · omega
    · omega

theorem unsigned_magic_from_state (W D X A : Int)
    (hD : 0 < D) (hDW : D < W) (hX : 0 < X)
    (hWX : ∃ j, X = W * j)
    (hstop : W * W ≤ X ∨
      ¬ (X / (W - 1 - (W - 1 - D) % D) < D - 1 - (X - 1) % D ∨
        (X / (W - 1 - (W - 1 - D) % D) = D - 1 - (X - 1) % D ∧
          X % (W - 1 - (W - 1 - D) % D) = 0)))
    (hA0 : 0 ≤ A) (hAW : A < W) :
    A * ((X - 1) / D + 1) / X = A.tdiv D := by
  have hD0 : D ≠ 0 := by omega
  have hr : (W - 1 - D) % D = (W - 1) % D := by
    simp [Int.sub_emod]
  rw [hr] at hstop
  have hWdiv := Int.emod_add_mul_ediv (W - 1) D
  have hWr0 := Int.emod_nonneg (W - 1) hD0
  have hWr1 := Int.emod_lt_of_pos (W - 1) hD
  have hK : 1 ≤ (W - 1) / D := by
    by_cases h : 1 ≤ (W - 1) / D
    · exact h
    · have hq : (W - 1) / D ≤ 0 := by omega
      have hp := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hD) hq
      omega
  have hnc : W - 1 - (W - 1) % D = ((W - 1) / D) * D := by
    rw [Int.mul_comm]
    omega
  have hnc0 : 0 < W - 1 - (W - 1) % D := by
    have hp := Int.mul_le_mul_of_nonneg_right hK (Int.le_of_lt hD)
    rw [Int.one_mul] at hp
    omega
  have hXdiv := Int.emod_add_mul_ediv (X - 1) D
  have hXr0 := Int.emod_nonneg (X - 1) hD0
  have hXr1 := Int.emod_lt_of_pos (X - 1) hD
  apply unsigned_magic_tdiv (nc := W - 1 - (W - 1) % D)
    (K := (W - 1) / D) (ρ := (W - 1) % D) (e := D - 1 - (X - 1) % D)
    hD hK hnc hWr1 (by omega) hX hWX
  · rw [Int.mul_add, Int.mul_one]
    omega
  · omega
  · omega
  · rcases hstop with hlarge | hstop
    · have hncW : W - 1 - (W - 1) % D ≤ W := by omega
      have heW : D - 1 - (X - 1) % D ≤ W - 1 := by omega
      have hfirst := Int.mul_le_mul_of_nonneg_right heW (Int.le_of_lt hnc0)
      have hrhs : (W - 1) * (W - 1 - (W - 1) % D) =
          W * (W - 1 - (W - 1) % D) - (W - 1 - (W - 1) % D) := by
        rw [Int.sub_mul, Int.one_mul]
      rw [hrhs] at hfirst
      have hsecond := Int.mul_le_mul_of_nonneg_left hncW (show 0 ≤ W by omega)
      omega
    · exact (unsignedStop_exact X _ _ hnc0).mp hstop
  · exact hA0
  · exact hAW


structure UnsignedNatState where
  p : Nat
  q1 : Nat
  r1 : Nat
  q2 : Nat
  r2 : Nat
  delta : Nat

def unsignedNatNext (d nc : Nat) (s : UnsignedNatState) : UnsignedNatState :=
  let r1 := (2 * s.r1) % nc
  let r2 := (2 * s.r2 + 1) % d
  ⟨s.p + 1, 2 * s.q1 + (2 * s.r1) / nc, r1,
    2 * s.q2 + (2 * s.r2 + 1) / d, r2, d - 1 - r2⟩

def unsignedNatContinue (bits : Nat) (s : UnsignedNatState) : Prop :=
  s.p < 2 * bits ∧ (s.q1 < s.delta ∨ (s.q1 = s.delta ∧ s.r1 = 0))

instance (bits : Nat) (s : UnsignedNatState) : Decidable (unsignedNatContinue bits s) :=
  inferInstanceAs (Decidable (s.p < 2 * bits ∧
    (s.q1 < s.delta ∨ (s.q1 = s.delta ∧ s.r1 = 0))))

def unsignedNatStep (bits d nc : Nat) (s : UnsignedNatState) :
    Except JuliaLean.JlError (Sum UnsignedNatState UnsignedNatState) :=
  let next := unsignedNatNext d nc s
  if unsignedNatContinue bits next then .ok (.inr next) else .ok (.inl next)

def UnsignedNatInvariant (d nc : Nat) (s : UnsignedNatState) : Prop :=
  s.q1 * nc + s.r1 = 2 ^ s.p ∧ s.r1 < nc ∧
  s.q2 * d + s.r2 + 1 = 2 ^ s.p ∧ s.r2 < d ∧
  s.delta = d - 1 - s.r2

theorem unsignedNatNext_invariant (d nc : Nat) (hd : 0 < d) (hnc : 0 < nc)
    (s : UnsignedNatState) (hs : UnsignedNatInvariant d nc s) :
    UnsignedNatInvariant d nc (unsignedNatNext d nc s) := by
  rcases hs with ⟨h1, hr1, h2, hr2, _⟩
  have he1 := Nat.mod_add_div (2 * s.r1) nc
  have he2 := Nat.mod_add_div (2 * s.r2 + 1) d
  have hmul1 : (2 * s.q1) * nc = 2 * (s.q1 * nc) := Nat.mul_assoc _ _ _
  have hmul2 : (2 * s.q2) * d = 2 * (s.q2 * d) := Nat.mul_assoc _ _ _
  have hpow : 2 ^ (s.p + 1) = 2 * 2 ^ s.p := by
    rw [Nat.pow_succ, Nat.mul_comm]
  unfold UnsignedNatInvariant unsignedNatNext
  simp only
  refine ⟨?_, Nat.mod_lt _ hnc, ?_, Nat.mod_lt _ hd, True.intro⟩
  · rw [Nat.add_mul, hmul1, Nat.mul_comm ((2 * s.r1) / nc) nc, hpow]
    omega
  · rw [Nat.add_mul, hmul2, Nat.mul_comm ((2 * s.r2 + 1) / d) d, hpow]
    omega

theorem unsignedNatContinue_bounds (d nc : Nat) (s : UnsignedNatState)
    (hs : UnsignedNatInvariant d nc s)
    (hc : s.q1 < s.delta ∨ (s.q1 = s.delta ∧ s.r1 = 0)) :
    s.q1 < d ∧ s.q2 < nc ∧ 2 ^ s.p < d * nc := by
  rcases hs with ⟨h1, hr1, h2, hr2, hdelta⟩
  have hq1 : s.q1 ≤ s.delta := by omega
  have hX : 2 ^ s.p ≤ s.delta * nc := by
    rcases hc with hc | ⟨hc, hz⟩
    · have hm := Nat.mul_le_mul_right nc (show s.q1 + 1 ≤ s.delta by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm
      omega
    · rw [← hc]
      omega
  have hm := Nat.mul_le_mul_right nc (show s.delta + 1 ≤ d by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hXlt : 2 ^ s.p < d * nc := by omega
  refine ⟨by omega, ?_, hXlt⟩
  by_cases hq2 : s.q2 < nc
  · exact hq2
  · have hm2 := Nat.mul_le_mul_right d (show nc ≤ s.q2 by omega)
    rw [Nat.mul_comm nc d] at hm2
    omega

theorem unsignedNatNc_bounds (half d : Nat) (hh : 0 < half)
    (hd : 0 < d) (hdW : d < 2 * half) :
    let nc := 2 * half - 1 - (2 * half - 1 - d) % d
    half ≤ nc ∧ nc < 2 * half ∧ d ≤ nc := by
  have hr := Nat.mod_lt (2 * half - 1 - d) hd
  have hrle := Nat.mod_le (2 * half - 1 - d) d
  dsimp only
  by_cases h : d ≤ half <;> omega

theorem unsignedNatNext_q1_bound (bits d nc : Nat) (s : UnsignedNatState)
    (hbits : 2 ≤ bits) (hd : 0 < d) (hdW : d < 2 ^ bits)
    (hnc : nc = 2 ^ bits - 1 - (2 ^ bits - 1 - d) % d)
    (hs : UnsignedNatInvariant d nc s)
    (hactive : s.p = bits - 1 ∨ s.q1 < s.delta ∨ (s.q1 = s.delta ∧ s.r1 = 0))
    (hp : (unsignedNatNext d nc s).p < 2 * bits) :
    (unsignedNatNext d nc s).q1 < 2 ^ bits := by
  have hW : 2 ^ bits = 2 * 2 ^ (bits - 1) := by
    calc
      2 ^ bits = 2 ^ ((bits - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (bits - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hh : 0 < 2 ^ (bits - 1) := Nat.pow_pos (by decide)
  have hncb := unsignedNatNc_bounds (2 ^ (bits - 1)) d hh hd (by omega)
  have hnc0 : 0 < nc := by rw [hW] at hnc; omega
  have hi := unsignedNatNext_invariant d nc hd hnc0 s hs
  have hncHalf : 2 ^ (bits - 1) ≤ nc := by rw [hW] at hnc; omega
  have hdnc : d ≤ nc := by rw [hW] at hnc; omega
  have hXlt : 2 ^ (unsignedNatNext d nc s).p < 2 ^ bits * nc := by
    rcases hactive with hinit | hc
    · have hnc2 : 2 ≤ nc := by
        have hb := Nat.pow_le_pow_right (by decide : 0 < 2)
          (show 1 ≤ bits - 1 by omega)
        simp only [Nat.pow_one] at hb
        omega
      have hm := Nat.mul_le_mul_left (2 ^ bits) hnc2
      have hw0 : 0 < 2 ^ bits := Nat.pow_pos (by decide)
      have hnext : (unsignedNatNext d nc s).p = bits := by
        change s.p + 1 = bits
        omega
      rw [hnext]
      omega
    · by_cases hdHalf : d ≤ 2 ^ (bits - 1)
      · have hsmall := (unsignedNatContinue_bounds d nc s hs hc).2.2
        have hm := Nat.mul_le_mul_right nc hdHalf
        have he : 2 ^ (unsignedNatNext d nc s).p = 2 * 2 ^ s.p := by
          change 2 ^ (s.p + 1) = _
          rw [Nat.pow_succ, Nat.mul_comm]
        have hWW : 2 ^ bits * nc = 2 * (2 ^ (bits - 1) * nc) := by
          rw [hW, Nat.mul_assoc]
        rw [he, hWW]
        omega
      · have hncBig : 2 ^ (bits - 1) + 1 ≤ nc := by omega
        have hm := Nat.mul_le_mul_left (2 ^ bits) hncBig
        rw [Nat.mul_add, Nat.mul_one] at hm
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
          (show (unsignedNatNext d nc s).p ≤ bits + (bits - 1) by omega)
        rw [Nat.pow_add] at hpow
        have hw0 : 0 < 2 ^ bits := Nat.pow_pos (by decide)
        omega
  by_cases hq : (unsignedNatNext d nc s).q1 < 2 ^ bits
  · exact hq
  · have hm := Nat.mul_le_mul_right nc
      (show 2 ^ bits ≤ (unsignedNatNext d nc s).q1 by omega)
    have he := hi.1
    omega

theorem unsignedNatStep_progress (bits d nc : Nat) (s : UnsignedNatState)
    (hp : s.p < 2 * bits) :
    (∃ a, unsignedNatStep bits d nc s = .ok (.inl a)) ∨
    ∃ next, unsignedNatStep bits d nc s = .ok (.inr next) ∧
      next.p < 2 * bits ∧ 2 * bits - next.p < 2 * bits - s.p := by
  by_cases h : unsignedNatContinue bits (unsignedNatNext d nc s)
  · refine Or.inr ⟨unsignedNatNext d nc s, by simp [unsignedNatStep, h], h.1, ?_⟩
    change 2 * bits - (s.p + 1) < 2 * bits - s.p
    omega
  · exact Or.inl ⟨unsignedNatNext d nc s, by simp [unsignedNatStep, h]⟩

theorem unsignedNatLoop_total (bits d nc : Nat) (s : UnsignedNatState)
    (hp : s.p < 2 * bits) :
    ∃ result, whileLoop (unsignedNatStep bits d nc) s = some (.ok result) := by
  apply whileLoop_total_of_step (unsignedNatStep bits d nc)
    (fun s => s.p < 2 * bits) (fun s => 2 * bits - s.p)
  · exact unsignedNatStep_progress bits d nc
  · exact hp

def unsignedNatInitial (bits d nc : Nat) : UnsignedNatState :=
  let x := 2 ^ (bits - 1)
  ⟨bits - 1, x / nc, x % nc, (x - 1) / d, (x - 1) % d,
    d - 1 - (x - 1) % d⟩

theorem unsignedNatInitial_invariant (bits d nc : Nat) (hd : 0 < d) (hnc : 0 < nc) :
    UnsignedNatInvariant d nc (unsignedNatInitial bits d nc) := by
  have h1 := Nat.mod_add_div (2 ^ (bits - 1)) nc
  have h2 := Nat.mod_add_div (2 ^ (bits - 1) - 1) d
  have hx : 0 < 2 ^ (bits - 1) := Nat.pow_pos (by decide)
  unfold UnsignedNatInvariant unsignedNatInitial
  simp only
  refine ⟨?_, Nat.mod_lt _ hnc, ?_, Nat.mod_lt _ hd, True.intro⟩
  · rw [Nat.mul_comm]
    omega
  · rw [Nat.mul_comm]
    omega

theorem unsignedNatLoop_spec (bits d nc : Nat) (hd : 0 < d) (hnc : 0 < nc)
    (s : UnsignedNatState) (hp : s.p < 2 * bits) (hs : UnsignedNatInvariant d nc s) :
    ∃ result, whileLoop (unsignedNatStep bits d nc) s = some (.ok result) ∧
      UnsignedNatInvariant d nc result ∧ ¬ unsignedNatContinue bits result := by
  suffices total : ∀ fuel s, 2 * bits - s.p < fuel → s.p < 2 * bits →
      UnsignedNatInvariant d nc s →
      ∃ result, whileLoop (unsignedNatStep bits d nc) s = some (.ok result) ∧
        UnsignedNatInvariant d nc result ∧ ¬ unsignedNatContinue bits result from
    total (2 * bits - s.p + 1) s (by omega) hp hs
  intro fuel
  induction fuel with
  | zero =>
      intro s h _ _
      omega
  | succ fuel ih =>
      intro s hf hp hs
      have hn := unsignedNatNext_invariant d nc hd hnc s hs
      by_cases hc : unsignedNatContinue bits (unsignedNatNext d nc s)
      · have hm : 2 * bits - (unsignedNatNext d nc s).p < fuel := by
          change 2 * bits - (s.p + 1) < fuel
          omega
        obtain ⟨result, hr, hi, hstop⟩ := ih (unsignedNatNext d nc s) hm hc.1 hn
        refine ⟨result, ?_, hi, hstop⟩
        rw [whileLoop.eq_def]
        simpa [unsignedNatStep, hc] using hr
      · refine ⟨unsignedNatNext d nc s, ?_, hn, hc⟩
        rw [whileLoop.eq_def]
        simp [unsignedNatStep, hc]

theorem unsignedNatTerminal_magic (bits d nc : Nat) (s : UnsignedNatState)
    (hd : 0 < d) (hnc : 0 < nc) (hdW : d < 2 ^ bits)
    (hncform : (nc : Int) = (2 : Int) ^ bits - 1 -
      ((2 : Int) ^ bits - 1 - d) % d)
    (hs : UnsignedNatInvariant d nc s) (hp : bits ≤ s.p)
    (hstop : ¬ unsignedNatContinue bits s)
    (A : Int) (hA0 : 0 ≤ A) (hAW : A < (2 : Int) ^ bits) :
    A * ((s.q2 : Int) + 1) / (2 : Int) ^ s.p = A.tdiv d := by
  rcases hs with ⟨h1, hr1, h2, hr2, hdelta⟩
  have h1i := congrArg (fun n : Nat => (n : Int)) h1
  have h2i := congrArg (fun n : Nat => (n : Int)) h2
  simp at h1i h2i
  have hq1 := (magic_divmod_of_eq (c := (nc : Int)) (q := (s.q1 : Int))
    (r := (s.r1 : Int)) (x := (2 : Int) ^ s.p) (by omega)
    (by rw [Int.mul_comm]; simpa using h1i.symm) (by omega) (by omega)).1
  have hqr2 := magic_divmod_of_eq (c := (d : Int)) (q := (s.q2 : Int))
    (r := (s.r2 : Int)) (x := (2 : Int) ^ s.p - 1) (by omega)
    (by rw [Int.mul_comm]; omega) (by omega) (by omega)
  have hdeltai : (s.delta : Int) = (d : Int) - 1 - s.r2 := by
    have hnat : s.delta + s.r2 + 1 = d := by omega
    have hi := congrArg (fun n : Nat => (n : Int)) hnat
    simp at hi
    omega
  have hX : 0 < (2 : Int) ^ s.p := Int.pow_pos (by decide)
  have hWX : ∃ j : Int, (2 : Int) ^ s.p = (2 : Int) ^ bits * j := by
    refine ⟨(2 : Int) ^ (s.p - bits), ?_⟩
    rw [← Int.pow_add, show bits + (s.p - bits) = s.p by omega]
  have hguard : (2 : Int) ^ bits * (2 : Int) ^ bits ≤ (2 : Int) ^ s.p ∨
      ¬ ((2 : Int) ^ s.p / (nc : Int) < (s.delta : Int) ∨
        ((2 : Int) ^ s.p / (nc : Int) = (s.delta : Int) ∧
          (2 : Int) ^ s.p % (nc : Int) = 0)) := by
    by_cases hlimit : 2 * bits ≤ s.p
    · apply Or.inl
      have hn := Nat.pow_le_pow_right (by decide : 0 < 2) hlimit
      have hi : ((2 ^ (2 * bits) : Nat) : Int) ≤ ((2 ^ s.p : Nat) : Int) := by omega
      have he : (2 : Int) ^ (2 * bits) = (2 : Int) ^ bits * (2 : Int) ^ bits := by
        rw [show 2 * bits = bits + bits by omega, Int.pow_add]
      simpa [he] using hi
    · apply Or.inr
      have hr1eq := (magic_divmod_of_eq (c := (nc : Int)) (q := (s.q1 : Int))
        (r := (s.r1 : Int)) (x := (2 : Int) ^ s.p) (by omega)
        (by rw [Int.mul_comm]; simpa using h1i.symm) (by omega) (by omega)).2
      rw [hq1, hr1eq]
      intro hbad
      apply hstop
      unfold unsignedNatContinue
      exact ⟨by omega, by omega⟩
  have hmagic := unsigned_magic_from_state ((2 : Int) ^ bits) (d : Int)
    ((2 : Int) ^ s.p) A (by omega) (by
      have hi : (d : Int) < ((2 ^ bits : Nat) : Int) := by omega
      simpa using hi) hX hWX
  rw [← hncform, hqr2.2, ← hdeltai] at hmagic
  have result := hmagic hguard hA0 hAW
  rw [hqr2.1] at result
  exact result

theorem unsignedNatLoop_transport {S : Type}
    (bits d nc : Nat) (modelStep : S → Except JuliaLean.JlError (Sum S S))
    (pack : UnsignedNatState → S) (valid : UnsignedNatState → Prop)
    (nextValid : ∀ s, valid s → valid (unsignedNatNext d nc s))
    (bridge : ∀ s, valid s → s.p < 2 * bits →
      modelStep (pack s) = (unsignedNatStep bits d nc s).map (Sum.map pack pack))
    (s : UnsignedNatState) (hs : valid s) (hp : s.p < 2 * bits) :
    ∃ result, whileLoop modelStep (pack s) = some (.ok (pack result)) ∧
      whileLoop (unsignedNatStep bits d nc) s = some (.ok result) ∧
      valid result ∧ ¬ unsignedNatContinue bits result := by
  suffices total : ∀ fuel s, 2 * bits - s.p < fuel → s.p < 2 * bits → valid s →
      ∃ result, whileLoop modelStep (pack s) = some (.ok (pack result)) ∧
        whileLoop (unsignedNatStep bits d nc) s = some (.ok result) ∧
        valid result ∧ ¬ unsignedNatContinue bits result from
    total (2 * bits - s.p + 1) s (by omega) hp hs
  intro fuel
  induction fuel with
  | zero =>
      intro s h _ _
      omega
  | succ fuel ih =>
      intro s hf hp hs
      by_cases hc : unsignedNatContinue bits (unsignedNatNext d nc s)
      · have hnat : unsignedNatStep bits d nc s =
            .ok (.inr (unsignedNatNext d nc s)) := by simp [unsignedNatStep, hc]
        have hmodel : modelStep (pack s) = .ok (.inr (pack (unsignedNatNext d nc s))) := by
          rw [bridge s hs hp, hnat]
          rfl
        have hm : 2 * bits - (unsignedNatNext d nc s).p < fuel := by
          change 2 * bits - (s.p + 1) < fuel
          omega
        obtain ⟨result, hr, hn, hv, hstop⟩ :=
          ih (unsignedNatNext d nc s) hm hc.1 (nextValid s hs)
        refine ⟨result, ?_, ?_, hv, hstop⟩
        · rw [whileLoop.eq_def, hmodel]
          exact hr
        · rw [whileLoop.eq_def, hnat]
          exact hn
      · have hnat : unsignedNatStep bits d nc s =
            .ok (.inl (unsignedNatNext d nc s)) := by simp [unsignedNatStep, hc]
        have hmodel : modelStep (pack s) = .ok (.inl (pack (unsignedNatNext d nc s))) := by
          rw [bridge s hs hp, hnat]
          rfl
        refine ⟨unsignedNatNext d nc s, ?_, ?_, nextValid s hs, hc⟩
        · rw [whileLoop.eq_def, hmodel]
        · rw [whileLoop.eq_def, hnat]


private theorem unsigned_min_zero {t : IntTy} (hu : t.signed = false) : t.min = 0 := by
  cases t <;> simp_all [IntTy.signed, IntTy.min]

private theorem unsigned_sub_val {t : IntTy} (hu : t.signed = false)
    (d r : JInt t) (hr : r.val < d.val) :
    (I.sub d r).val = d.val - r.val := by
  rw [I.sub, sub_int_val]
  apply wrapInt_of_inRange
  have hmin := unsigned_min_zero hu
  have hr0 := nonneg_of_unsigned hu r
  have hd := d.property
  omega

theorem unsigned_r1_threshold_bridge (f : SameTypeDivrem) (render : Bits → Jl String)
    {t : IntTy} (hu : t.signed = false) (d r : JInt t) (hr : r.val < d.val) :
    (bitsCallees f render).ge ⟨t, r⟩ ⟨t, I.sub d r⟩ =
      .ok (decide (d.val ≤ 2 * r.val)) := by
  change Except.ok (JuliaLean.base.operators.greaterEqual I.le r (I.sub d r)) = _
  rw [JuliaLean.base.operators.greaterEqual, le_eq, unsigned_sub_val hu d r hr]
  congr 1
  simp only [decide_eq_decide]
  omega

theorem unsigned_remainder_field_bridge {t : IntTy} (hu : t.signed = false)
    (d r : JInt t) (hd : 0 < d.val) (hr : r.val < d.val)
    (c : Int) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (if d.val ≤ 2 * r.val + c then
        I.subWrap (I.addWrap (I.addWrap r r) (I.lit t c)) d
      else I.addWrap (I.addWrap r r) (I.lit t c)).val = (2 * r.val + c) % d.val := by
  have hr0 := nonneg_of_unsigned hu r
  have hmin := unsigned_min_zero hu
  have hmax : 1 ≤ t.max := by cases t <;> simp [IntTy.max, IntTy.bits, IntTy.signed]
  have hc : (I.lit t c).val = c := lit_of_fits (by unfold fits; omega)
  have hm := (doubled_divmod d.val r.val 0 r.val c hd (by omega) hr0 hr hc0 hc1).2
  have hdmax := d.property.2
  by_cases h : d.val ≤ 2 * r.val + c
  · simp only [if_pos h] at hm ⊢
    rw [subWrapWraps_proven, addWrapWraps_proven, addWrapWraps_proven,
      hc, wrapInt_add_left, wrapInt_sub_left]
    have hsum : r.val + r.val + c - d.val = 2 * r.val + c - d.val := by omega
    rw [hsum, wrapInt_of_inRange t _ (by omega)]
    exact hm.symm
  · simp only [if_neg h] at hm ⊢
    rw [addWrapWraps_proven, addWrapWraps_proven, hc, wrapInt_add_left]
    have hsum : r.val + r.val + c = 2 * r.val + c := by omega
    rw [hsum, wrapInt_of_inRange t _ (by omega)]
    exact hm.symm

theorem unsigned_r2_threshold_bridge (f : SameTypeDivrem) (render : Bits → Jl String)
    {t : IntTy} (hu : t.signed = false) (d r : JInt t) (hr : r.val < d.val) :
    (bitsCallees f render).ge
      ⟨t, I.addWrap r (I.lit t 1)⟩ ⟨t, I.subWrap d r⟩ =
      .ok (decide (d.val ≤ 2 * r.val + 1)) := by
  have hr0 := nonneg_of_unsigned hu r
  have hmin := unsigned_min_zero hu
  have hdmax := d.property.2
  have hone : (I.lit t 1).val = 1 := by cases t <;> decide
  have hleft : (I.addWrap r (I.lit t 1)).val = r.val + 1 := by
    rw [addWrapWraps_proven, hone]
    apply wrapInt_of_inRange
    omega
  have hright : (I.subWrap d r).val = d.val - r.val := unsigned_sub_val hu d r hr
  change Except.ok (JuliaLean.base.operators.greaterEqual I.le _ _) = _
  rw [JuliaLean.base.operators.greaterEqual, le_eq, hleft, hright]
  congr 1
  simp only [decide_eq_decide]
  omega

theorem unsigned_quotient_field_bridge {t : IntTy} (q : JInt t) (carry : Bool) :
    (if carry then I.addWrap (I.addWrap q q) (I.lit t 1) else I.addWrap q q).val =
      wrapInt t (2 * q.val + if carry then 1 else 0) := by
  have hone : (I.lit t 1).val = 1 := by cases t <;> decide
  cases carry
  · simp only [Bool.false_eq_true, if_false, Int.add_zero]
    rw [addWrapWraps_proven, show q.val + q.val = 2 * q.val by omega]
  · simp only [if_true]
    rw [addWrapWraps_proven, addWrapWraps_proven, hone, wrapInt_add_left,
      show q.val + q.val + 1 = 2 * q.val + 1 by omega]

theorem unsigned_add_flag_bridge (half q : Nat) (hhalf : 0 < half) (carry : Bool) :
    (2 * half ≤ q + 1 ∨ (if carry then half - 1 ≤ q else half ≤ q)) ↔
      2 * half ≤ 2 * q + (if carry then 1 else 0) + 1 := by
  cases carry <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega


theorem unsigned_stop_field_bridge (f : SameTypeDivrem) (render : Bits → Jl String)
    {t : IntTy} (q delta r : JInt t) :
    needsAnother (bitsCallees f render) ⟨t, q⟩ ⟨t, delta⟩ ⟨t, r⟩ =
      .ok (decide (q.val < delta.val ∨ (q.val = delta.val ∧ r.val = 0))) := by
  have hz : (I.lit .i64 0).val = 0 := by decide
  unfold needsAnother
  simp only [bitsCallees, Bind.bind, Except.bind, pure, Except.pure,
    lt_eq, eq_eq, hz]
  by_cases hl : q.val < delta.val
  · simp [hl]
  · by_cases he : q.val = delta.val
    · simp [hl, he]
    · simp [hl, he]

theorem unsigned_counter_field_bridge {t : IntTy} (p : JInt .i64)
    (hp0 : 0 ≤ p.val) (hp1 : p.val ≤ 2 * t.bits) :
    (I.add p (I.lit .i64 1)).val = p.val + 1 ∧
    (I.mul (I.lit .i64 2) (I.lit .i64 t.bits)).val = 2 * t.bits := by
  have h1 : (I.lit .i64 1).val = 1 := by decide
  have h2 : (I.lit .i64 2).val = 2 := by decide
  have hw : (I.lit .i64 t.bits).val = t.bits := by cases t <;> decide
  constructor
  · rw [I.add, add_int_val, h1]
    apply wrapInt_of_inRange
    cases t <;>
      simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hp0 hp1 ⊢ <;> omega
  · rw [I.mul, mul_int_val, h2, hw]
    apply wrapInt_of_inRange
    cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega


private theorem phase_bind_assoc {E A B C : Type} (r : Except E A)
    (f : A → Except E B) (g : B → Except E C) :
    Except.bind (Except.bind r f) g = Except.bind r (fun a => Except.bind (f a) g) := by
  cases r <;> rfl

private theorem phase_bind_ite {E A B : Type} (p : Prop) [Decidable p]
    (a b : Except E A) (k : A → Except E B) :
    Except.bind (if p then a else b) k =
      if p then Except.bind a k else Except.bind b k := by
  by_cases h : p <;> simp [h]

private theorem phase_bind_ok {E A B : Type} (a : A) (k : A → Except E B) :
    Except.bind (.ok a) k = k a := rfl

private def unsignedQ1Phase {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (T : Ty) (nc q1 r1 : D) : Except E (D × D) := do
  let difference ← o.sub nc r1
  let threshold ← o.convert T difference
  if ← o.ge r1 threshold then do
    let q1 ← o.addWrap q1 q1
    let one ← o.oneType T
    let q1 ← o.addWrap q1 one
    let r1 ← o.addWrap r1 r1
    let r1 ← o.subWrap r1 nc
    pure (q1, r1)
  else do
    let q1 ← o.addWrap q1 q1
    let r1 ← o.addWrap r1 r1
    pure (q1, r1)

private def unsignedQ2Phase {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (T : Ty) (d signedmin signedmax q2 r2 : D)
    (add : o.Condition) : Except E (D × D × o.Condition) := do
  let one ← o.oneType T
  let left ← o.addWrap r2 one
  let left ← o.convert T left
  let right ← o.subWrap d r2
  let right ← o.convert T right
  if ← o.ge left right then do
    let comparison ← o.geValue q2 signedmax
    let add ← o.bitOr add comparison
    let q2 ← o.addWrap q2 q2
    let one ← o.oneType T
    let q2 ← o.addWrap q2 one
    let r2 ← o.addWrap r2 r2
    let one ← o.oneType T
    let r2 ← o.addWrap r2 one
    let r2 ← o.subWrap r2 d
    pure (q2, r2, add)
  else do
    let comparison ← o.geValue q2 signedmin
    let add ← o.bitOr add comparison
    let q2 ← o.addWrap q2 q2
    let r2 ← o.addWrap r2 r2
    let one ← o.oneType T
    let r2 ← o.addWrap r2 one
    pure (q2, r2, add)

theorem unsignedInverseStep_factor {Ty D E : Type} {V : Ty → Type}
    (o : Callees Ty V D E) (T : Ty) (d nc signedmin signedmax : D)
    (s : UnsignedLoopState D o.Condition) :
    unsignedInverseStep o T d nc signedmin signedmax s = (do
      let (q1, r1) ← unsignedQ1Phase o T nc s.q1 s.r1
      let (q2, r2, add) ← unsignedQ2Phase o T d signedmin signedmax s.q2 s.r2 s.add
      let one ← o.oneType T
      let delta ← o.subWrap d one
      let delta ← o.subWrap delta r2
      let width ← o.bitsizeof d
      let p := I.add s.p (I.lit .i64 1)
      let limit := I.mul (I.lit .i64 2) width
      let next : UnsignedLoopState D o.Condition := ⟨⟨p, q1, r1, q2, r2⟩, add⟩
      if I.ltSame p limit then
        if ← needsAnother o q1 delta r1 then return .inr next
      return .inl next) := by
  simp only [unsignedInverseStep, unsignedQ1Phase, unsignedQ2Phase,
    Bind.bind, pure, Except.pure, phase_bind_assoc, phase_bind_ite, phase_bind_ok]

private theorem phase_convert_self {t : IntTy} (x : JInt t) :
    I.convert t x = .ok x := by
  simp only [I.convert, JInt.convert, dif_pos x.property]

private theorem phase_bitsBin_same {t : IntTy}
    (op : {r : IntTy} → JInt r → JInt r → JInt r) (a b : JInt t) :
    bitsBin op ⟨t, a⟩ ⟨t, b⟩ = ⟨t, op a b⟩ := by
  cases t <;> rfl

theorem unsignedQ1Phase_bits (f : SameTypeDivrem) (render : Bits → Jl String)
    {t : IntTy} (nc q r : JInt t) :
    unsignedQ1Phase (bitsCallees f render) t ⟨t, nc⟩ ⟨t, q⟩ ⟨t, r⟩ =
      .ok (⟨t, if I.le (I.sub nc r) r then
          I.addWrap (I.addWrap q q) (I.lit t 1) else I.addWrap q q⟩,
        ⟨t, if I.le (I.sub nc r) r then
          I.subWrap (I.addWrap r r) nc else I.addWrap r r⟩) := by
  unfold unsignedQ1Phase
  dsimp only [bitsCallees]
  simp only [phase_bitsBin_same, phase_convert_self, Bind.bind, Except.bind, pure, Except.pure,
    JuliaLean.base.operators.greaterEqual]
  split <;> rfl

theorem unsignedQ2Phase_bits (f : SameTypeDivrem) (render : Bits → Jl String)
    {t : IntTy} (d signedmin signedmax q r : JInt t) (add : Bool) :
    unsignedQ2Phase (bitsCallees f render) t ⟨t, d⟩ ⟨t, signedmin⟩ ⟨t, signedmax⟩
      ⟨t, q⟩ ⟨t, r⟩ add =
      .ok (⟨t, if I.le (I.subWrap d r) (I.addWrap r (I.lit t 1)) then
          I.addWrap (I.addWrap q q) (I.lit t 1) else I.addWrap q q⟩,
        ⟨t, if I.le (I.subWrap d r) (I.addWrap r (I.lit t 1)) then
          I.subWrap (I.addWrap (I.addWrap r r) (I.lit t 1)) d
        else I.addWrap (I.addWrap r r) (I.lit t 1)⟩,
        if I.le (I.subWrap d r) (I.addWrap r (I.lit t 1)) then
          JuliaLean.base.bool.orBool add (I.le signedmax q)
        else JuliaLean.base.bool.orBool add (I.le signedmin q)) := by
  unfold unsignedQ2Phase
  dsimp only [bitsCallees]
  simp only [phase_bitsBin_same, phase_convert_self, Bind.bind, Except.bind, pure, Except.pure,
    JuliaLean.base.operators.greaterEqual]
  split <;> rfl


section UM

theorem um_bitsBin_same {t : IntTy}
    (op : {r : IntTy} → JInt r → JInt r → JInt r) (a b : JInt t) :
    bitsBin op ⟨t, a⟩ ⟨t, b⟩ = ⟨t, op a b⟩ := by
  cases t <;> rfl

theorem um_subWrap (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees f render).subWrap ⟨t, a⟩ ⟨t, b⟩ = .ok ⟨t, I.subWrap a b⟩ := by
  change Except.ok (bitsBin I.subWrap ⟨t, a⟩ ⟨t, b⟩) = _
  rw [um_bitsBin_same]

theorem um_orBool (x y : Bool) : JuliaLean.base.bool.orBool x y = (x || y) := by
  cases x <;> cases y <;> rfl

theorem um_wrap_unsigned {t : IntTy} (hu : t.signed = false) (x : Int) :
    wrapInt t x = x % 2 ^ t.bits := by
  simp [wrapInt, hu]

theorem um_lit_val {t : IntTy} (hu : t.signed = false) {x : Int}
    (h0 : 0 ≤ x) (h1 : x < 2 ^ t.bits) : (I.lit t x).val = x := by
  rw [lit_val, um_wrap_unsigned hu]
  exact Int.emod_eq_of_lt h0 h1

theorem um_natW {t : IntTy} {n : Nat} (h : n < 2 ^ t.bits) : (n : Int) < 2 ^ t.bits := by
  exact_mod_cast h

theorem um_lit_nat {t : IntTy} (hu : t.signed = false) {n : Nat}
    (h : n < 2 ^ t.bits) : (I.lit t (n : Int)).val = n :=
  um_lit_val hu (Int.natCast_nonneg n) (um_natW h)

theorem um_addWrap_lit (t : IntTy) (a b : Int) :
    I.addWrap (I.lit t a) (I.lit t b) = I.lit t (a + b) := by
  apply jint_eq
  rw [addWrapWraps_proven, lit_val, lit_val, lit_val, wrapInt_add_left, wrapInt_add_right]

theorem um_subWrap_lit (t : IntTy) (a b : Int) :
    I.subWrap (I.lit t a) (I.lit t b) = I.lit t (a - b) := by
  apply jint_eq
  rw [subWrapWraps_proven, lit_val, lit_val, lit_val, wrapInt_sub_left, wrapInt_sub_right]

theorem um_sub_lit (t : IntTy) (a b : Int) :
    I.sub (I.lit t a) (I.lit t b) = I.lit t (a - b) := by
  apply jint_eq
  rw [I.sub, sub_int_val, lit_val, lit_val, lit_val, wrapInt_sub_left, wrapInt_sub_right]

theorem um_add_lit (t : IntTy) (a b : Int) :
    I.add (I.lit t a) (I.lit t b) = I.lit t (a + b) := by
  apply jint_eq
  rw [I.add, add_int_val, lit_val, lit_val, lit_val, wrapInt_add_left, wrapInt_add_right]

theorem um_div2 {r n c : Nat} (hr : r < n) (hc : c ≤ 1) :
    (2 * r + c) / n = (if n ≤ 2 * r + c then 1 else 0) ∧
    (2 * r + c) % n = (if n ≤ 2 * r + c then 2 * r + c - n else 2 * r + c) := by
  by_cases h : n ≤ 2 * r + c
  · simp only [if_pos h]
    refine ⟨Nat.div_eq_of_lt_le (by omega) (by omega), ?_⟩
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · simp only [if_neg h]
    exact ⟨Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩

theorem um_c1 {t : IntTy} (hu : t.signed = false) (nc r : Nat) (hr : r < nc)
    (hnc : nc < 2 ^ t.bits) :
    I.le (I.sub (I.lit t (nc : Int)) (I.lit t (r : Int))) (I.lit t (r : Int)) =
      decide (nc ≤ 2 * r) := by
  have hW := um_natW hnc
  rw [um_sub_lit, le_eq, um_lit_val hu (by omega) (by omega), um_lit_nat hu (by omega),
    decide_eq_decide]
  omega

theorem um_c2 {t : IntTy} (hu : t.signed = false) (d r : Nat) (hr : r < d)
    (hd : d < 2 ^ t.bits) :
    I.le (I.subWrap (I.lit t (d : Int)) (I.lit t (r : Int)))
      (I.addWrap (I.lit t (r : Int)) (I.lit t 1)) = decide (d ≤ 2 * r + 1) := by
  have hW := um_natW hd
  rw [um_subWrap_lit, um_addWrap_lit, le_eq, um_lit_val hu (by omega) (by omega),
    um_lit_val hu (by omega) (by omega), decide_eq_decide]
  omega

theorem um_F1 {t : IntTy} (hu : t.signed = false) (nc q r : Nat) (hr : r < nc)
    (hnc : nc < 2 ^ t.bits) :
    (if I.le (I.sub (I.lit t (nc : Int)) (I.lit t (r : Int))) (I.lit t (r : Int)) then
        I.addWrap (I.addWrap (I.lit t (q : Int)) (I.lit t (q : Int))) (I.lit t 1)
      else I.addWrap (I.lit t (q : Int)) (I.lit t (q : Int))) =
      I.lit t ((2 * q + 2 * r / nc : Nat) : Int) := by
  rw [um_c1 hu nc r hr hnc]
  have hd := um_div2 (c := 0) hr (Nat.zero_le 1)
  simp only [Nat.add_zero] at hd
  by_cases h : nc ≤ 2 * r
  · rw [if_pos (decide_eq_true h), hd.1, if_pos h, um_addWrap_lit, um_addWrap_lit]
    exact congrArg (I.lit t) (by omega)
  · rw [if_neg (fun h' => h (of_decide_eq_true h')), hd.1, if_neg h, um_addWrap_lit]
    exact congrArg (I.lit t) (by omega)

theorem um_F2 {t : IntTy} (hu : t.signed = false) (nc r : Nat) (hr : r < nc)
    (hnc : nc < 2 ^ t.bits) :
    (if I.le (I.sub (I.lit t (nc : Int)) (I.lit t (r : Int))) (I.lit t (r : Int)) then
        I.subWrap (I.addWrap (I.lit t (r : Int)) (I.lit t (r : Int))) (I.lit t (nc : Int))
      else I.addWrap (I.lit t (r : Int)) (I.lit t (r : Int))) =
      I.lit t ((2 * r % nc : Nat) : Int) := by
  rw [um_c1 hu nc r hr hnc]
  have hd := um_div2 (c := 0) hr (Nat.zero_le 1)
  simp only [Nat.add_zero] at hd
  by_cases h : nc ≤ 2 * r
  · rw [if_pos (decide_eq_true h), hd.2, if_pos h, um_addWrap_lit, um_subWrap_lit]
    exact congrArg (I.lit t) (by omega)
  · rw [if_neg (fun h' => h (of_decide_eq_true h')), hd.2, if_neg h, um_addWrap_lit]
    exact congrArg (I.lit t) (by omega)

theorem um_F3 {t : IntTy} (hu : t.signed = false) (d q r : Nat) (hr : r < d)
    (hd : d < 2 ^ t.bits) :
    (if I.le (I.subWrap (I.lit t (d : Int)) (I.lit t (r : Int)))
          (I.addWrap (I.lit t (r : Int)) (I.lit t 1)) then
        I.addWrap (I.addWrap (I.lit t (q : Int)) (I.lit t (q : Int))) (I.lit t 1)
      else I.addWrap (I.lit t (q : Int)) (I.lit t (q : Int))) =
      I.lit t ((2 * q + (2 * r + 1) / d : Nat) : Int) := by
  rw [um_c2 hu d r hr hd]
  have hdv := um_div2 (c := 1) hr (Nat.le_refl 1)
  by_cases h : d ≤ 2 * r + 1
  · rw [if_pos (decide_eq_true h), hdv.1, if_pos h, um_addWrap_lit, um_addWrap_lit]
    exact congrArg (I.lit t) (by omega)
  · rw [if_neg (fun h' => h (of_decide_eq_true h')), hdv.1, if_neg h, um_addWrap_lit]
    exact congrArg (I.lit t) (by omega)

theorem um_F4 {t : IntTy} (hu : t.signed = false) (d r : Nat) (hr : r < d)
    (hd : d < 2 ^ t.bits) :
    (if I.le (I.subWrap (I.lit t (d : Int)) (I.lit t (r : Int)))
          (I.addWrap (I.lit t (r : Int)) (I.lit t 1)) then
        I.subWrap (I.addWrap (I.addWrap (I.lit t (r : Int)) (I.lit t (r : Int))) (I.lit t 1))
          (I.lit t (d : Int))
      else I.addWrap (I.addWrap (I.lit t (r : Int)) (I.lit t (r : Int))) (I.lit t 1)) =
      I.lit t (((2 * r + 1) % d : Nat) : Int) := by
  rw [um_c2 hu d r hr hd]
  have hdv := um_div2 (c := 1) hr (Nat.le_refl 1)
  by_cases h : d ≤ 2 * r + 1
  · rw [if_pos (decide_eq_true h), hdv.2, if_pos h, um_addWrap_lit, um_addWrap_lit,
      um_subWrap_lit]
    exact congrArg (I.lit t) (by omega)
  · rw [if_neg (fun h' => h (of_decide_eq_true h')), hdv.2, if_neg h, um_addWrap_lit,
      um_addWrap_lit]
    exact congrArg (I.lit t) (by omega)

theorem um_pow_half {t : IntTy} (hb : 1 ≤ t.bits) : 2 ^ t.bits = 2 * 2 ^ (t.bits - 1) := by
  calc
    2 ^ t.bits = 2 ^ ((t.bits - 1) + 1) := by congr 1; omega
    _ = 2 * 2 ^ (t.bits - 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem um_F5 {t : IntTy} (hu : t.signed = false) (hb : 1 ≤ t.bits) (d q r : Nat)
    (hr : r < d) (hd : d < 2 ^ t.bits) :
    (if I.le (I.subWrap (I.lit t (d : Int)) (I.lit t (r : Int)))
          (I.addWrap (I.lit t (r : Int)) (I.lit t 1)) then
        JuliaLean.base.bool.orBool (decide (2 ^ t.bits ≤ q + 1))
          (I.le (I.lit t ((2 ^ (t.bits - 1) - 1 : Nat) : Int)) (I.lit t (q : Int)))
      else JuliaLean.base.bool.orBool (decide (2 ^ t.bits ≤ q + 1))
          (I.le (I.lit t ((2 ^ (t.bits - 1) : Nat) : Int)) (I.lit t (q : Int)))) =
      decide (2 ^ t.bits ≤ (2 * q + (2 * r + 1) / d) + 1) := by
  rw [um_c2 hu d r hr hd, um_orBool, um_orBool]
  have hdv := um_div2 (c := 1) hr (Nat.le_refl 1)
  have hW := um_pow_half hb
  have hhalf : 0 < 2 ^ (t.bits - 1) := Nat.pow_pos (by decide)
  rw [hdv.1]
  by_cases hq : 2 ^ t.bits ≤ q + 1
  · rw [decide_eq_true hq]
    simp only [Bool.true_or, ite_self]
    symm
    apply decide_eq_true
    split <;> omega
  · have hl : decide (2 ^ t.bits ≤ q + 1) = false := decide_eq_false hq
    rw [hl, Bool.false_or, Bool.false_or, le_eq, le_eq, um_lit_nat hu (by omega),
      um_lit_nat hu (by omega), um_lit_nat hu (by omega)]
    by_cases h : d ≤ 2 * r + 1
    · rw [if_pos (decide_eq_true h), if_pos h, decide_eq_decide]
      omega
    · rw [if_neg (fun h' => h (of_decide_eq_true h')), if_neg h, decide_eq_decide]
      omega

theorem um_F5c (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (hu : t.signed = false) (hb : 1 ≤ t.bits) (d q r : Nat)
    (hr : r < d) (hd : d < 2 ^ t.bits) :
    ((if I.le (I.subWrap (I.lit t (d : Int)) (I.lit t (r : Int)))
          (I.addWrap (I.lit t (r : Int)) (I.lit t 1)) then
        JuliaLean.base.bool.orBool (decide (2 ^ t.bits ≤ q + 1))
          (I.le (I.lit t ((2 ^ (t.bits - 1) - 1 : Nat) : Int)) (I.lit t (q : Int)))
      else JuliaLean.base.bool.orBool (decide (2 ^ t.bits ≤ q + 1))
          (I.le (I.lit t ((2 ^ (t.bits - 1) : Nat) : Int)) (I.lit t (q : Int))) :
        (bitsCallees f render).Condition)) =
      decide (2 ^ t.bits ≤ (2 * q + (2 * r + 1) / d) + 1) :=
  um_F5 hu hb d q r hr hd

theorem um_i64_small {n : Int} (h0 : 0 ≤ n) (h1 : n ≤ 1000) : (I.lit .i64 n).val = n := by
  apply lit_of_fits
  simp [fits, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem um_bits_le (t : IntTy) : 8 ≤ t.bits ∧ t.bits ≤ 128 := by
  cases t <;> decide

theorem um_F6 (n : Nat) :
    I.add (I.lit .i64 (n : Int)) (I.lit .i64 1) = I.lit .i64 ((n + 1 : Nat) : Int) := by
  rw [um_add_lit]
  exact congrArg (I.lit .i64) (by omega)

theorem um_F7k (k n : Nat) (hk : k ≤ 128) (hn : n ≤ 2 * k + 1) :
    I.ltSame (I.lit .i64 (n : Int)) (I.mul (I.lit .i64 2) (I.lit .i64 (k : Int))) =
      decide (n < 2 * k) := by
  have hm : (I.mul (I.lit .i64 2) (I.lit .i64 (k : Int))).val = 2 * k := by
    rw [I.mul, mul_int_val, um_i64_small (by omega) (by omega),
      um_i64_small (by omega) (by omega)]
    apply wrapInt_of_inRange
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  rw [ltSame_eq, hm, um_i64_small (by omega) (by omega), decide_eq_decide]
  omega

theorem um_F7 (t : IntTy) (n : Nat) (hn : n ≤ 2 * t.bits + 1) :
    I.ltSame (I.lit .i64 (n : Int)) (I.mul (I.lit .i64 2) (I.lit .i64 (t.bits : Int))) =
      decide (n < 2 * t.bits) :=
  um_F7k t.bits n (um_bits_le t).2 hn

theorem um_F8 (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (hu : t.signed = false) (d q r r2 : Nat) (hq : q < 2 ^ t.bits) (hr : r < 2 ^ t.bits)
    (hr2 : r2 < d) (hd : d < 2 ^ t.bits) :
    needsAnother (bitsCallees f render) ⟨t, I.lit t (q : Int)⟩
      ⟨t, I.subWrap (I.subWrap (I.lit t (d : Int)) (I.lit t 1)) (I.lit t (r2 : Int))⟩
      ⟨t, I.lit t (r : Int)⟩ =
      .ok (decide (q < d - 1 - r2 ∨ (q = d - 1 - r2 ∧ r = 0))) := by
  have hW := um_natW hd
  rw [unsigned_stop_field_bridge, um_subWrap_lit, um_subWrap_lit, um_lit_nat hu hq,
    um_lit_nat hu hr, um_lit_val hu (by omega) (by omega)]
  congr 1
  rw [decide_eq_decide]
  omega

theorem um_bind_ok' {E A B : Type} (a : A) (k : A → Except E B) :
    (bind (Except.ok a) k : Except E B) = k a := Eq.trans rfl rfl

theorem um_pure' {E A : Type} (a : A) : (pure a : Except E A) = .ok a := Eq.trans rfl rfl

theorem um_oneType' (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy) :
    (bitsCallees f render).oneType t = .ok ⟨t, I.lit t 1⟩ := Eq.trans rfl rfl

theorem um_bitsizeof' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a : JInt t) :
    (bitsCallees f render).bitsizeof ⟨t, a⟩ = .ok (I.lit .i64 t.bits) := Eq.trans rfl rfl

def umPack (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy)
    (s : UnsignedNatState) : UnsignedLoopState Bits (bitsCallees f render).Condition :=
  ⟨⟨I.lit .i64 s.p, ⟨t, I.lit t s.q1⟩, ⟨t, I.lit t s.r1⟩,
    ⟨t, I.lit t s.q2⟩, ⟨t, I.lit t s.r2⟩⟩,
    decide (2 ^ t.bits ≤ s.q2 + 1)⟩

theorem um_step_bridge (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (hu : t.signed = false) (d nc : Nat) (s : UnsignedNatState)
    (hd0 : 0 < d) (hdW : d < 2 ^ t.bits) (hncW : nc < 2 ^ t.bits)
    (hr1 : s.r1 < nc) (hr2 : s.r2 < d) (hp : s.p < 2 * t.bits)
    (hq1 : (unsignedNatNext d nc s).p < 2 * t.bits →
      (unsignedNatNext d nc s).q1 < 2 ^ t.bits) :
    unsignedInverseStep (bitsCallees f render) t ⟨t, I.lit t d⟩ ⟨t, I.lit t nc⟩
      ⟨t, I.lit t (2 ^ (t.bits - 1) : Nat)⟩ ⟨t, I.lit t (2 ^ (t.bits - 1) - 1 : Nat)⟩
      (umPack f render t s) =
      (unsignedNatStep t.bits d nc s).map
        (Sum.map (umPack f render t) (umPack f render t)) := by
  have hb := um_bits_le t
  have hnc0 : 0 < nc := by omega
  rw [unsignedInverseStep_factor]
  dsimp only [umPack]
  rw [unsignedQ1Phase_bits, unsignedQ2Phase_bits]
  rw [um_F1 hu nc s.q1 s.r1 hr1 hncW, um_F2 hu nc s.r1 hr1 hncW,
    um_F3 hu d s.q2 s.r2 hr2 hdW, um_F4 hu d s.r2 hr2 hdW,
    um_F5c f render hu (by omega) d s.q2 s.r2 hr2 hdW, um_F6]
  simp only [um_bind_ok', um_pure', um_oneType', um_subWrap, um_bitsizeof']
  rw [um_F7 t (s.p + 1) (by omega)]
  unfold unsignedNatStep
  dsimp only
  by_cases hP : s.p + 1 < 2 * t.bits
  · rw [if_pos (decide_eq_true hP)]
    rw [um_F8 f render hu d (2 * s.q1 + 2 * s.r1 / nc) (2 * s.r1 % nc)
      ((2 * s.r2 + 1) % d) (hq1 hP) (Nat.lt_trans (Nat.mod_lt _ hnc0) hncW)
      (Nat.mod_lt _ hd0) hdW]
    simp only [um_bind_ok']
    split
    · rename_i hQ
      have hc : unsignedNatContinue t.bits (unsignedNatNext d nc s) :=
        ⟨hP, of_decide_eq_true hQ⟩
      rw [if_pos hc]
      rfl
    · rename_i hQ
      rw [if_neg (fun hc : unsignedNatContinue t.bits (unsignedNatNext d nc s) =>
        hQ (decide_eq_true hc.2))]
      rfl
  · rw [if_neg (fun h' => hP (of_decide_eq_true h'))]
    rw [if_neg (fun hc : unsignedNatContinue t.bits (unsignedNatNext d nc s) => hP hc.1)]
    rfl

end UM

section UM2

theorem um_nc_facts {t : IntTy} (d nc : Nat) (hd0 : 0 < d) (hdW : d < 2 ^ t.bits)
    (hnc : nc = 2 ^ t.bits - 1 - (2 ^ t.bits - 1 - d) % d) :
    2 ^ (t.bits - 1) ≤ nc ∧ nc < 2 ^ t.bits ∧ d ≤ nc := by
  have hW := um_pow_half (t := t) (by have := um_bits_le t; omega)
  have hh : 0 < 2 ^ (t.bits - 1) := Nat.pow_pos (by decide)
  have hm := Nat.mod_lt (2 ^ t.bits - 1 - d) hd0
  have hle := Nat.mod_le (2 ^ t.bits - 1 - d) d
  rw [hW] at hnc hdW hm hle ⊢
  by_cases h : d ≤ 2 ^ (t.bits - 1) <;> omega

def umValid (bits d nc : Nat) (s : UnsignedNatState) : Prop :=
  UnsignedNatInvariant d nc s ∧ bits - 1 ≤ s.p ∧ (s.p = bits - 1 ∨ unsignedNatContinue bits s)

theorem um_loop (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (hu : t.signed = false) (d nc : Nat) (hd0 : 0 < d) (hdW : d < 2 ^ t.bits)
    (hnc : nc = 2 ^ t.bits - 1 - (2 ^ t.bits - 1 - d) % d) (s : UnsignedNatState)
    (hs : umValid t.bits d nc s) :
    ∃ r, whileLoop (unsignedInverseStep (bitsCallees f render) t ⟨t, I.lit t d⟩
        ⟨t, I.lit t nc⟩ ⟨t, I.lit t (2 ^ (t.bits - 1) : Nat)⟩
        ⟨t, I.lit t (2 ^ (t.bits - 1) - 1 : Nat)⟩) (umPack f render t s) =
        some (.ok (umPack f render t r)) ∧
      UnsignedNatInvariant d nc r ∧ ¬ unsignedNatContinue t.bits r ∧ t.bits ≤ r.p ∧
      r.p ≤ 2 * t.bits ∧ r.q2 + 1 < 2 * 2 ^ t.bits := by
  have hb := um_bits_le t
  obtain ⟨hncH, hncW, hdnc⟩ := um_nc_facts d nc hd0 hdW hnc
  have hnc0 : 0 < nc := by omega
  have hW := um_pow_half (t := t) (by omega)
  suffices total : ∀ fuel s, 2 * t.bits - s.p < fuel → umValid t.bits d nc s →
      ∃ r, whileLoop (unsignedInverseStep (bitsCallees f render) t ⟨t, I.lit t d⟩
          ⟨t, I.lit t nc⟩ ⟨t, I.lit t (2 ^ (t.bits - 1) : Nat)⟩
          ⟨t, I.lit t (2 ^ (t.bits - 1) - 1 : Nat)⟩) (umPack f render t s) =
          some (.ok (umPack f render t r)) ∧
        UnsignedNatInvariant d nc r ∧ ¬ unsignedNatContinue t.bits r ∧ t.bits ≤ r.p ∧
        r.p ≤ 2 * t.bits ∧ r.q2 + 1 < 2 * 2 ^ t.bits from
    total (2 * t.bits - s.p + 1) s (by omega) hs
  intro fuel
  induction fuel with
  | zero =>
      intro s h _
      omega
  | succ fuel ih =>
      intro s hf hs
      obtain ⟨hinv, hlow, hact⟩ := hs
      have hp : s.p < 2 * t.bits := by
        rcases hact with h | h
        · omega
        · exact h.1
      have hbridge := um_step_bridge f render hu d nc s hd0 hdW hncW hinv.2.1
        hinv.2.2.2.1 hp
        (fun hP => unsignedNatNext_q1_bound t.bits d nc s (by omega) hd0 hdW hnc hinv
          (by
            rcases hact with h | h
            · exact Or.inl h
            · exact Or.inr h.2) hP)
      have hn := unsignedNatNext_invariant d nc hd0 hnc0 s hinv
      by_cases hc : unsignedNatContinue t.bits (unsignedNatNext d nc s)
      · have hnat : unsignedNatStep t.bits d nc s = .ok (.inr (unsignedNatNext d nc s)) := by
          simp [unsignedNatStep, hc]
        have hmodel : unsignedInverseStep (bitsCallees f render) t ⟨t, I.lit t d⟩
            ⟨t, I.lit t nc⟩ ⟨t, I.lit t (2 ^ (t.bits - 1) : Nat)⟩
            ⟨t, I.lit t (2 ^ (t.bits - 1) - 1 : Nat)⟩ (umPack f render t s) =
            .ok (.inr (umPack f render t (unsignedNatNext d nc s))) := by
          rw [hbridge, hnat]
          rfl
        obtain ⟨r, hr, hrest⟩ := ih (unsignedNatNext d nc s)
          (by change 2 * t.bits - (s.p + 1) < fuel; omega)
          ⟨hn, by change t.bits - 1 ≤ s.p + 1; omega, Or.inr hc⟩
        refine ⟨r, ?_, hrest⟩
        rw [whileLoop.eq_def, hmodel]
        exact hr
      · have hnat : unsignedNatStep t.bits d nc s = .ok (.inl (unsignedNatNext d nc s)) := by
          simp [unsignedNatStep, hc]
        have hmodel : unsignedInverseStep (bitsCallees f render) t ⟨t, I.lit t d⟩
            ⟨t, I.lit t nc⟩ ⟨t, I.lit t (2 ^ (t.bits - 1) : Nat)⟩
            ⟨t, I.lit t (2 ^ (t.bits - 1) - 1 : Nat)⟩ (umPack f render t s) =
            .ok (.inl (umPack f render t (unsignedNatNext d nc s))) := by
          rw [hbridge, hnat]
          rfl
        refine ⟨unsignedNatNext d nc s, ?_, hn, hc, ?_, ?_, ?_⟩
        · rw [whileLoop.eq_def, hmodel]
        · change t.bits ≤ s.p + 1
          omega
        · change s.p + 1 ≤ 2 * t.bits
          omega
        · have hn2 := hn.2.2.1
          rcases hact with h | h
          · have hpe : (unsignedNatNext d nc s).p = t.bits := by
              change s.p + 1 = t.bits
              omega
            rw [hpe] at hn2
            have hm := Nat.le_mul_of_pos_right (unsignedNatNext d nc s).q2 hd0
            omega
          · have hcb := (unsignedNatContinue_bounds d nc s hinv h.2).2.2
            have hpe : 2 ^ (unsignedNatNext d nc s).p = 2 * 2 ^ s.p := by
              change 2 ^ (s.p + 1) = _
              rw [Nat.pow_succ, Nat.mul_comm]
            rw [hpe] at hn2
            have e : 2 * nc * d = 2 * (d * nc) := by
              rw [Nat.mul_comm (2 * nc) d, Nat.mul_left_comm]
            have hlt : (unsignedNatNext d nc s).q2 * d < 2 * nc * d := by
              rw [e]
              omega
            have := Nat.lt_of_mul_lt_mul_right hlt
            omega

theorem um_map_ok' {E A B : Type} (g : A → B) (a : A) :
    Except.map g (Except.ok a : Except E A) = .ok (g a) := Eq.trans rfl rfl

theorem um_pack' (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy) (x : JInt t) :
    (bitsCallees f render).pack t x = ⟨t, x⟩ := Eq.trans rfl rfl

theorem um_int' (f : SameTypeDivrem) (render : Bits → Jl String) (x : JInt .i64) :
    (bitsCallees f render).int x = ⟨.i64, x⟩ := Eq.trans rfl rfl

theorem um_eq' (f : SameTypeDivrem) (render : Bits → Jl String) {s u : IntTy}
    (x : JInt s) (y : JInt u) :
    (bitsCallees f render).eq ⟨s, x⟩ ⟨u, y⟩ = .ok (I.eq x y) := Eq.trans rfl rfl

theorem um_eqValue' (f : SameTypeDivrem) (render : Bits → Jl String) {s u : IntTy}
    (x : JInt s) (y : JInt u) :
    (bitsCallees f render).eqValue ⟨s, x⟩ ⟨u, y⟩ = .ok (I.eq x y) := Eq.trans rfl rfl

theorem um_boolValue' (f : SameTypeDivrem) (render : Bits → Jl String) (b : Bool) :
    (bitsCallees f render).boolValue b = b := Eq.trans rfl rfl

theorem um_oneValue' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).oneValue ⟨t, x⟩ = .ok ⟨t, I.lit t 1⟩ := Eq.trans rfl rfl

theorem um_shl' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t)
    (n : JInt .i64) :
    (bitsCallees f render).shl ⟨t, x⟩ n = .ok ⟨t, I.shl_Int x n⟩ := Eq.trans rfl rfl

theorem um_zeroValue' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).zeroValue ⟨t, x⟩ = .ok ⟨t, I.zero x⟩ := Eq.trans rfl rfl

theorem um_remType' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t)
    (T : IntTy) :
    (bitsCallees f render).remType ⟨t, x⟩ T = .ok ⟨T, I.remT T x⟩ := Eq.trans rfl rfl

theorem um_sub (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees f render).sub ⟨t, a⟩ ⟨t, b⟩ = .ok ⟨t, I.sub a b⟩ := by
  change Except.ok (bitsBin I.sub ⟨t, a⟩ ⟨t, b⟩) = _
  rw [um_bitsBin_same]

theorem um_addWrap (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees f render).addWrap ⟨t, a⟩ ⟨t, b⟩ = .ok ⟨t, I.addWrap a b⟩ := by
  change Except.ok (bitsBin I.addWrap ⟨t, a⟩ ⟨t, b⟩) = _
  rw [um_bitsBin_same]

theorem um_jconvert_self {t : IntTy} (x : JInt t) : I.convert t x = .ok x := by
  simp only [I.convert, JInt.convert, dif_pos x.property]

theorem um_convert_self (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (x : JInt t) :
    (bitsCallees f render).convert t ⟨t, x⟩ = .ok ⟨t, x⟩ := by
  change (do return ⟨t, ← I.convert t x⟩ : Jl Bits) = _
  rw [um_jconvert_self]
  exact Eq.trans rfl rfl

theorem um_rem_same (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (a b : JInt t) :
    (bitsCallees f render).rem ⟨t, a⟩ ⟨t, b⟩ = (I.remSame a b).map (fun r => (⟨t, r⟩ : Bits)) := by
  cases t <;> exact Eq.trans rfl rfl

theorem um_divrem_bits (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees JuliaLean.base.intfuncs.divremBits render).divrem ⟨t, a⟩ ⟨t, b⟩ =
      (do let (q, r) ← JuliaLean.base.intfuncs.divremBits a b
          pure ((⟨t, q⟩ : Bits), (⟨t, r⟩ : Bits))) := by
  cases t <;> exact Eq.trans rfl rfl

theorem um_nat_tdiv (a b : Nat) : ((a : Int).tdiv (b : Int)) = ((a / b : Nat) : Int) := by
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.natCast_ediv]

theorem um_nat_tmod (a b : Nat) : ((a : Int).tmod (b : Int)) = ((a % b : Nat) : Int) := by
  rw [Int.tmod_eq_emod_of_nonneg (by omega), Int.natCast_emod]

theorem um_remSame_lits {t : IntTy} (hu : t.signed = false) (a b : Nat) (hb0 : 0 < b)
    (ha : a < 2 ^ t.bits) (hb : b < 2 ^ t.bits) :
    I.remSame (I.lit t (a : Int)) (I.lit t (b : Int)) = .ok (I.lit t ((a % b : Nat) : Int)) := by
  rw [remSame_eq, um_lit_nat hu ha, um_lit_nat hu hb, if_neg (by omega), um_nat_tmod]

theorem um_divSame_lits {t : IntTy} (hu : t.signed = false) (a b : Nat) (hb0 : 0 < b)
    (ha : a < 2 ^ t.bits) (hb : b < 2 ^ t.bits) :
    JuliaLean.base.int.divSame (I.lit t (a : Int)) (I.lit t (b : Int)) = .ok (I.lit t ((a / b : Nat) : Int)) := by
  rw [divSame_eq, um_lit_nat hu ha, um_lit_nat hu hb, if_neg (by simp [hu]; omega), um_nat_tdiv]

theorem um_divrem_lits (render : Bits → Jl String) {t : IntTy} (hu : t.signed = false)
    (a b : Nat) (hb0 : 0 < b) (ha : a < 2 ^ t.bits) (hb : b < 2 ^ t.bits) :
    (bitsCallees JuliaLean.base.intfuncs.divremBits render).divrem
        ⟨t, I.lit t (a : Int)⟩ ⟨t, I.lit t (b : Int)⟩ =
      .ok (⟨t, I.lit t ((a / b : Nat) : Int)⟩, ⟨t, I.lit t ((a % b : Nat) : Int)⟩) := by
  rw [um_divrem_bits]
  unfold JuliaLean.base.intfuncs.divremBits
  rw [um_divSame_lits hu a b hb0 ha hb, um_remSame_lits hu a b hb0 ha hb]
  exact Eq.trans rfl rfl

theorem um_rem_lits (render : Bits → Jl String) {t : IntTy} (hu : t.signed = false)
    (a b : Nat) (hb0 : 0 < b) (ha : a < 2 ^ t.bits) (hb : b < 2 ^ t.bits) :
    (bitsCallees JuliaLean.base.intfuncs.divremBits render).rem
        ⟨t, I.lit t (a : Int)⟩ ⟨t, I.lit t (b : Int)⟩ =
      .ok ⟨t, I.lit t ((a % b : Nat) : Int)⟩ := by
  rw [um_rem_same, um_remSame_lits hu a b hb0 ha hb, um_map_ok']

theorem um_pack_init (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy)
    (dn nc : Nat) (hadd : decide (2 ^ t.bits ≤ (2 ^ (t.bits - 1) - 1) / dn + 1) = false) :
    umPack f render t (unsignedNatInitial t.bits dn nc) =
      ⟨⟨I.lit .i64 ((t.bits - 1 : Nat) : Int),
        ⟨t, I.lit t ((2 ^ (t.bits - 1) / nc : Nat) : Int)⟩,
        ⟨t, I.lit t ((2 ^ (t.bits - 1) % nc : Nat) : Int)⟩,
        ⟨t, I.lit t (((2 ^ (t.bits - 1) - 1) / dn : Nat) : Int)⟩,
        ⟨t, I.lit t (((2 ^ (t.bits - 1) - 1) % dn : Nat) : Int)⟩⟩,
        (bitsCallees f render).boolValue false⟩ := by
  unfold umPack unsignedNatInitial
  dsimp only
  rw [hadd]
  rfl

theorem um_init (render : Bits → Jl String) {t : IntTy} (hu : t.signed = false) (dn : Nat)
    (hd0 : 0 < dn) (hdW : dn < 2 ^ t.bits) :
    unsignedInverseConstructor.initialState
        (bitsCallees JuliaLean.base.intfuncs.divremBits render) (T := t) (I.lit t (dn : Int)) =
      .ok (⟨t, I.lit t ((2 ^ t.bits - 1 - (2 ^ t.bits - 1 - dn) % dn : Nat) : Int)⟩,
        ⟨t, I.lit t ((2 ^ (t.bits - 1) : Nat) : Int)⟩,
        ⟨t, I.lit t ((2 ^ (t.bits - 1) - 1 : Nat) : Int)⟩,
        umPack JuliaLean.base.intfuncs.divremBits render t
          (unsignedNatInitial t.bits dn (2 ^ t.bits - 1 - (2 ^ t.bits - 1 - dn) % dn))) := by
  have hb := um_bits_le t
  have hW := um_pow_half (t := t) (by omega)
  have hh : 0 < 2 ^ (t.bits - 1) := Nat.pow_pos (by decide)
  have hWc : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := by norm_cast
  obtain ⟨hncH, hncW, hdnc⟩ := um_nc_facts (t := t) dn _ hd0 hdW rfl
  have h_eq : I.eq (I.lit t (dn : Int)) (I.lit .i64 0) = false := by
    rw [eq_eq, um_lit_nat hu hdW, um_i64_small (by omega) (by omega)]
    simp only [decide_eq_false_iff_not]
    omega
  have h_p : I.sub (I.lit .i64 (t.bits : Int)) (I.lit .i64 1) =
      I.lit .i64 ((t.bits - 1 : Nat) : Int) := by
    rw [um_sub_lit]
    exact congrArg (I.lit .i64) (by omega)
  have h_sm : I.shl_Int (I.lit t 1) (I.lit .i64 ((t.bits - 1 : Nat) : Int)) =
      I.lit t ((2 ^ (t.bits - 1) : Nat) : Int) := by
    apply jint_eq
    have hc : (I.lit .i64 ((t.bits - 1 : Nat) : Int)).val = ((t.bits - 1 : Nat) : Int) :=
      um_i64_small (by omega) (by omega)
    have hp1 : pattern (I.lit t 1) = 1 := by
      have h1 := val_of_unsigned_pattern hu (I.lit t 1)
      have h2 : (I.lit t 1).val = 1 := um_lit_val hu (by omega) (by
        have := um_natW (t := t) (n := 1) (by omega)
        omega)
      omega
    have hcN : (I.lit .i64 ((t.bits - 1 : Nat) : Int)).val.toNat = t.bits - 1 := by
      rw [hc]
      omega
    rw [← val_of_unsigned_pattern hu, pattern_shl_Int _ _ (by rw [hc]; omega), hp1, hcN,
      Nat.one_mul, Nat.mod_eq_of_lt (by omega), um_lit_nat hu (by omega)]
  have h_smax : I.sub (I.lit t ((2 ^ (t.bits - 1) : Nat) : Int)) (I.lit t 1) =
      I.lit t ((2 ^ (t.bits - 1) - 1 : Nat) : Int) := by
    rw [um_sub_lit]
    exact congrArg (I.lit t) (by omega)
  have h_zero : I.zero (I.lit t (dn : Int)) = I.lit t 0 := Eq.trans rfl rfl
  have h_m1 : I.subWrap (I.lit t 0) (I.lit t 1) = I.lit t (-1) := by
    rw [um_subWrap_lit]
    exact congrArg (I.lit t) (by omega)
  have h_all : I.remT t (I.lit t (-1)) = I.lit t ((2 ^ t.bits - 1 : Nat) : Int) := by
    apply jint_eq
    rw [remT_val, lit_val, wrapInt_wrapInt, um_wrap_unsigned hu, um_lit_nat hu (by omega),
      show (-1 : Int) = (2 ^ t.bits - 1) + 2 ^ t.bits * (-1) by omega,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have h_diff : I.sub (I.lit t ((2 ^ t.bits - 1 : Nat) : Int)) (I.lit t (dn : Int)) =
      I.lit t ((2 ^ t.bits - 1 - dn : Nat) : Int) := by
    rw [um_sub_lit]
    exact congrArg (I.lit t) (by omega)
  have h_rem := um_rem_lits render hu (2 ^ t.bits - 1 - dn) dn hd0 (by omega) hdW
  have h_nc : I.sub (I.lit t ((2 ^ t.bits - 1 : Nat) : Int))
      (I.lit t (((2 ^ t.bits - 1 - dn) % dn : Nat) : Int)) =
      I.lit t ((2 ^ t.bits - 1 - (2 ^ t.bits - 1 - dn) % dn : Nat) : Int) := by
    rw [um_sub_lit]
    have := Nat.mod_le (2 ^ t.bits - 1 - dn) dn
    exact congrArg (I.lit t) (by omega)
  have h_dr1 := um_divrem_lits render hu (2 ^ (t.bits - 1))
    (2 ^ t.bits - 1 - (2 ^ t.bits - 1 - dn) % dn) (by omega) (by omega) hncW
  have h_dr2 := um_divrem_lits render hu (2 ^ (t.bits - 1) - 1) dn hd0 (by omega) hdW
  have h_add : decide (2 ^ t.bits ≤ (2 ^ (t.bits - 1) - 1) / dn + 1) = false := by
    apply decide_eq_false
    have := Nat.div_le_self (2 ^ (t.bits - 1) - 1) dn
    omega
  rw [um_pack_init _ render t dn _ h_add]
  unfold unsignedInverseConstructor.initialState
  simp only [um_pack', um_int', um_eq', h_eq, um_bind_ok', um_pure', Bool.false_eq_true,
    ite_false, um_oneValue', um_bitsizeof', h_p, um_shl', h_sm, um_oneType', um_sub, h_smax,
    um_zeroValue', h_zero, um_subWrap, h_m1, um_remType', h_all, h_diff, um_convert_self,
    h_rem, h_nc, h_dr1, h_dr2]

end UM2

section UM3

def umShift (t : IntTy) (r : UnsignedNatState) : JInt .u8 :=
  I.remT .u8 (I.op_Integer .i64 I.sub (I.remT .i64) (I.rem_Bool_Type .i64)
    (I.sub (I.lit .i64 (r.p : Int)) (I.lit .i64 (t.bits : Int)))
    (decide (2 ^ t.bits ≤ r.q2 + 1)))

def umInv (t : IntTy) (hu : t.signed = false) (dn : Nat) (r : UnsignedNatState) :
    UnsignedMultiplicativeInverse JInt bitDomains t :=
  ⟨hu, I.lit t (dn : Int), I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1),
    decide (2 ^ t.bits ≤ r.q2 + 1), umShift t r⟩

theorem um_subCondition' (f : SameTypeDivrem) (render : Bits → Jl String) (x : JInt .i64)
    (b : Bool) :
    (bitsCallees f render).subCondition x b =
      .ok ⟨.i64, I.op_Integer .i64 I.sub (I.remT .i64) (I.rem_Bool_Type .i64) x b⟩ :=
  Eq.trans rfl rfl

theorem um_remUInt8' (f : SameTypeDivrem) (render : Bits → Jl String) {s : IntTy} (x : JInt s) :
    (bitsCallees f render).remUInt8 ⟨s, x⟩ = .ok ⟨.u8, I.remT .u8 x⟩ := Eq.trans rfl rfl

theorem um_field' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).field t ⟨t, x⟩ = I.convert t x := Eq.trans rfl rfl

theorem um_fieldBool' (f : SameTypeDivrem) (render : Bits → Jl String) (b : Bool) :
    (bitsCallees f render).fieldBool b = .ok b := Eq.trans rfl rfl

theorem um_fieldUInt8' (f : SameTypeDivrem) (render : Bits → Jl String) {s : IntTy}
    (x : JInt s) :
    (bitsCallees f render).fieldUInt8 ⟨s, x⟩ = I.convert .u8 x := Eq.trans rfl rfl

theorem um_after_ok' {E A B : Type} (a : A) (k : A → Run E B) :
    after (.ok a) k = k a := Eq.trans rfl rfl

theorem um_continueRun_some' {E A B : Type} (r : Except E A) (k : A → Run E B) :
    continueRun (some r) k = after r k := Eq.trans rfl rfl

theorem um_loop_def' {Ty D E : Type} {V : Ty → Type} (o : Callees Ty V D E) (T : Ty)
    (d nc smin smax : D) (s : UnsignedLoopState D o.Condition) :
    unsignedInverseLoop o T d nc smin smax s =
      whileLoop (unsignedInverseStep o T d nc smin smax) s := Eq.trans rfl rfl

theorem um_pack_q2 (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy)
    (r : UnsignedNatState) : (umPack f render t r).q2 = ⟨t, I.lit t (r.q2 : Int)⟩ :=
  Eq.trans rfl rfl

theorem um_pack_p (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy)
    (r : UnsignedNatState) : (umPack f render t r).p = I.lit .i64 (r.p : Int) :=
  Eq.trans rfl rfl

theorem um_pack_add (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy)
    (r : UnsignedNatState) : (umPack f render t r).add = decide (2 ^ t.bits ≤ r.q2 + 1) :=
  Eq.trans rfl rfl

theorem um_ctor (render : Bits → Jl String) {t : IntTy} (hu : t.signed = false) (dn : Nat)
    (hd0 : 0 < dn) (hdW : dn < 2 ^ t.bits) :
    ∃ r : UnsignedNatState,
      UnsignedNatInvariant dn (2 ^ t.bits - 1 - (2 ^ t.bits - 1 - dn) % dn) r ∧
      ¬ unsignedNatContinue t.bits r ∧ t.bits ≤ r.p ∧ r.p ≤ 2 * t.bits ∧
      r.q2 + 1 < 2 * 2 ^ t.bits ∧
      unsignedInverseConstructor bitDomains
        (bitsCallees JuliaLean.base.intfuncs.divremBits render)
        (T := t) hu (I.lit t (dn : Int)) = some (.ok (umInv t hu dn r)) := by
  have hb := um_bits_le t
  obtain ⟨hncH, hncW, hdnc⟩ := um_nc_facts (t := t) dn _ hd0 hdW rfl
  obtain ⟨r, hloop, hinv, hstop, hpb, hp2, hq2⟩ :=
    um_loop JuliaLean.base.intfuncs.divremBits render hu dn _ hd0 hdW rfl
      (unsignedNatInitial t.bits dn (2 ^ t.bits - 1 - (2 ^ t.bits - 1 - dn) % dn))
      ⟨unsignedNatInitial_invariant t.bits dn _ hd0 (by omega), Nat.le_refl _, Or.inl rfl⟩
  refine ⟨r, hinv, hstop, hpb, hp2, hq2, ?_⟩
  unfold unsignedInverseConstructor
  rw [um_init render hu dn hd0 hdW]
  simp only [um_after_ok', um_loop_def', um_pack', hloop, um_continueRun_some', um_oneType',
    um_pack_q2, um_pack_p, um_pack_add, um_addWrap, um_bitsizeof', um_subCondition',
    um_remUInt8', um_bind_ok', um_field', um_jconvert_self, um_fieldBool', um_fieldUInt8',
    um_pure']
  rfl

theorem um_mulHi' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees f render).mulHi t a b = .ok ⟨t, mulHi a b⟩ := Eq.trans rfl rfl

theorem um_lshrOne' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).lshrOne ⟨t, x⟩ = .ok ⟨t, I.lshr_Int x (I.lit .i64 1)⟩ :=
  Eq.trans rfl rfl

theorem um_ifelse' (f : SameTypeDivrem) (render : Bits → Jl String) (c : Bool) (x y : Bits) :
    (bitsCallees f render).ifelse c x y = .ok (I.ifelse c x y) := Eq.trans rfl rfl

theorem um_lshr' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t)
    (n : JInt .u8) :
    (bitsCallees f render).lshr ⟨t, x⟩ n = .ok ⟨t, I.lshr_BitInteger_BitUnsigned x n⟩ :=
  Eq.trans rfl rfl

theorem um_ifelse_true {α : Type} (x y : α) : I.ifelse true x y = x := Eq.trans rfl rfl

theorem um_ifelse_false {α : Type} (x y : α) : I.ifelse false x y = y := Eq.trans rfl rfl

theorem um_inv_mult (t : IntTy) (hu : t.signed = false) (dn : Nat) (r : UnsignedNatState) :
    (umInv t hu dn r).multiplier = I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1) :=
  Eq.trans rfl rfl

theorem um_inv_add (t : IntTy) (hu : t.signed = false) (dn : Nat) (r : UnsignedNatState) :
    (umInv t hu dn r).add = decide (2 ^ t.bits ≤ r.q2 + 1) := Eq.trans rfl rfl

theorem um_inv_div (t : IntTy) (hu : t.signed = false) (dn : Nat) (r : UnsignedNatState) :
    (umInv t hu dn r).divisor = I.lit t (dn : Int) := Eq.trans rfl rfl

theorem um_inv_shift (t : IntTy) (hu : t.signed = false) (dn : Nat) (r : UnsignedNatState) :
    (umInv t hu dn r).shift = umShift t r := Eq.trans rfl rfl

theorem um_shift_core (p b k : Nat) (A : Bool) (hk : (if A then 1 else 0) = k)
    (hpb : b + k ≤ p) (hp2 : p ≤ 2 * b) (hb : b ≤ 128) :
    (I.remT .u8 (I.op_Integer .i64 I.sub (I.remT .i64) (I.rem_Bool_Type .i64)
      (I.sub (I.lit .i64 (p : Int)) (I.lit .i64 (b : Int))) A)).val =
      ((p - b - k : Nat) : Int) := by
  have hrb : (I.rem_Bool_Type .i64 A).val = (k : Int) := by
    have h := remBool_proven .i64 A
    change (I.rem_Bool_Type .i64 A).val = if A then 1 else 0 at h
    rw [h]
    cases A <;> simp at hk ⊢ <;> omega
  have hv : (I.op_Integer .i64 I.sub (I.remT .i64) (I.rem_Bool_Type .i64)
      (I.sub (I.lit .i64 (p : Int)) (I.lit .i64 (b : Int))) A).val = (p : Int) - b - k := by
    change (I.sub (I.remT .i64 (I.sub (I.lit .i64 (p : Int)) (I.lit .i64 (b : Int))))
      (I.rem_Bool_Type .i64 A)).val = _
    rw [I.sub, sub_int_val, remT_val, um_sub_lit, lit_val, wrapInt_wrapInt, hrb,
      wrapInt_sub_left]
    apply wrapInt_of_inRange
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  rw [remT_val, hv, wrapInt_of_inRange .u8 _ (by
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega)]
  omega

theorem um_ok_bits_eq {t : IntTy} {Z W : JInt t} (h : Z.val = W.val) :
    (Except.ok (⟨t, Z⟩ : Bits) : Jl Bits) = .ok ⟨t, W⟩ := by
  rw [jint_eq h]

theorem um_pattern_nat {t : IntTy} (hu : t.signed = false) (x : JInt t) (n : Nat)
    (h : x.val = (n : Int)) : pattern x = n := by
  have := val_of_unsigned_pattern hu x
  omega

theorem um_wrap_nat {t : IntTy} (hu : t.signed = false) (n : Nat) (h : n < 2 ^ t.bits) :
    wrapInt t (n : Int) = n := by
  rw [um_wrap_unsigned hu]
  exact Int.emod_eq_of_lt (by omega) (um_natW h)

theorem um_alg_add (an Q W k xv : Nat) (hW : 0 < W) (hQ1 : W ≤ Q) (hQ2 : Q < 2 * W)
    (hxv : xv = an * (Q - W) / W) :
    xv ≤ an ∧ ((an - xv) / 2 + xv) / 2 ^ k = an * Q / (W * 2 * 2 ^ k) := by
  have hxle : xv ≤ an := by
    rw [hxv]
    apply Nat.div_le_of_le_mul
    rw [Nat.mul_comm W an]
    exact Nat.mul_le_mul_left an (by omega)
  refine ⟨hxle, ?_⟩
  have e1 : (an - xv) / 2 + xv = (an + xv) / 2 := by
    rw [← Nat.add_mul_div_right (an - xv) xv (by decide : 0 < 2)]
    congr 1
    omega
  have e2 : an + xv = an * Q / W := by
    have hsplit : an * Q = an * (Q - W) + W * an := by
      rw [Nat.mul_comm W an, ← Nat.mul_add]
      congr 1
      omega
    rw [hsplit, Nat.add_mul_div_left _ _ hW, ← hxv]
    omega
  rw [e1, e2, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_assoc]

theorem um_div (render : Bits → Jl String) {t : IntTy} (hu : t.signed = false)
    (dn an : Nat) (hd0 : 0 < dn) (hdW : dn < 2 ^ t.bits) (han : an < 2 ^ t.bits)
    (r : UnsignedNatState)
    (hinv : UnsignedNatInvariant dn (2 ^ t.bits - 1 - (2 ^ t.bits - 1 - dn) % dn) r)
    (hstop : ¬ unsignedNatContinue t.bits r) (hpb : t.bits ≤ r.p) (hp2 : r.p ≤ 2 * t.bits)
    (hq2 : r.q2 + 1 < 2 * 2 ^ t.bits) :
    divUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits render)
      (I.lit t (an : Int)) (umInv t hu dn r) = .ok ⟨t, I.lit t ((an / dn : Nat) : Int)⟩ := by
  have hb := um_bits_le t
  have hW := um_pow_half (t := t) (by omega)
  have hh : 0 < 2 ^ (t.bits - 1) := Nat.pow_pos (by decide)
  have hWc : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := by norm_cast
  obtain ⟨hncH, hncW, hdnc⟩ := um_nc_facts (t := t) dn _ hd0 hdW rfl
  have hmag : an * (r.q2 + 1) / 2 ^ r.p = an / dn := by
    obtain ⟨M, hMdef⟩ : ∃ M, M = (2 ^ t.bits - 1 - dn) % dn := ⟨_, rfl⟩
    have hm : M ≤ 2 ^ t.bits - 1 - dn := hMdef ▸ Nat.mod_le _ _
    have hmc : (M : Int) = ((2 : Int) ^ t.bits - 1 - dn) % dn := by
      rw [hMdef, Int.natCast_emod]
      exact congrArg (· % (dn : Int)) (by omega)
    have hinv' := hinv
    rw [← hMdef] at hinv'
    have h := unsignedNatTerminal_magic t.bits dn (2 ^ t.bits - 1 - M) r hd0 (by omega) hdW
      (by rw [← hmc]; omega) hinv' hpb hstop (an : Int) (by omega) (by omega)
    rw [um_nat_tdiv] at h
    exact_mod_cast h
  have hdiv_lt : an / dn < 2 ^ t.bits := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) han
  have hres : (I.lit t ((an / dn : Nat) : Int)).val = ((an / dn : Nat) : Int) :=
    um_lit_nat hu hdiv_lt
  have hpS : 2 ^ r.p = 2 ^ t.bits * 2 ^ (r.p - t.bits) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  unfold divUnsignedInverse
  by_cases hA : 2 ^ t.bits ≤ r.q2 + 1
  · have hA' : decide (2 ^ t.bits ≤ r.q2 + 1) = true := decide_eq_true hA
    by_cases hd1 : dn = 1
    · subst hd1
      have hE : I.eq (I.lit t ((1 : Nat) : Int)) (I.lit .i64 1) = true := by
        rw [eq_eq, um_lit_nat hu hdW, um_i64_small (by omega) (by omega)]
        simp
      simp only [um_inv_mult, um_inv_add, um_inv_div, um_inv_shift, hA', um_mulHi', um_pack',
        um_subWrap, um_convert_self, um_lshrOne', um_addWrap, um_boolValue', um_ifelse',
        um_bind_ok', um_ifelse_true, um_lshr', um_eqValue', um_int', hE, Nat.div_one]
      rfl
    · have hE : I.eq (I.lit t (dn : Int)) (I.lit .i64 1) = false := by
        rw [eq_eq, um_lit_nat hu hdW, um_i64_small (by omega) (by omega)]
        simp only [decide_eq_false_iff_not]
        omega
      simp only [um_inv_mult, um_inv_add, um_inv_div, um_inv_shift, hA', um_mulHi', um_pack',
        um_subWrap, um_convert_self, um_lshrOne', um_addWrap, um_boolValue', um_ifelse',
        um_bind_ok', um_ifelse_true, um_lshr', um_eqValue', um_int', hE, um_ifelse_false]
      apply um_ok_bits_eq
      rw [hres]
      -- p ≥ bits + 1 in the add case for divisors above one
      have hp1 : t.bits + 1 ≤ r.p := by
        rcases Nat.lt_or_ge t.bits r.p with h | h
        · omega
        · have hpe : r.p = t.bits := by omega
          have h2 := hinv.2.2.1
          rw [hpe] at h2
          have hm2 := Nat.mul_le_mul_left r.q2 (show 2 ≤ dn by omega)
          omega
      obtain ⟨mv, hmv⟩ : ∃ mv, mv = r.q2 + 1 - 2 ^ t.bits := ⟨_, rfl⟩
      obtain ⟨xv, hxv⟩ : ∃ xv, xv = an * mv / 2 ^ t.bits := ⟨_, rfl⟩
      have halg := um_alg_add an (r.q2 + 1) (2 ^ t.bits) (r.p - t.bits - 1) xv
        (by omega) hA (by omega) (by rw [hxv, hmv])
      have hmval : (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1)).val = (mv : Int) := by
        rw [um_addWrap_lit, lit_val, um_wrap_unsigned hu,
          show (r.q2 : Int) + 1 = (mv : Int) + 2 ^ t.bits * 1 by omega,
          Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
      have hX : (mulHi (I.lit t (an : Int)) (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1))).val =
          (xv : Int) := by
        rw [mulHi_val, um_lit_nat hu han, hmval, hxv]
        norm_cast
      have hD : (I.subWrap (I.lit t (an : Int))
          (mulHi (I.lit t (an : Int)) (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1)))).val =
          ((an - xv : Nat) : Int) := by
        rw [subWrapWraps_proven, um_lit_nat hu han, hX,
          show (an : Int) - (xv : Int) = ((an - xv : Nat) : Int) by omega, um_wrap_nat hu _ (by omega)]
      have hH : (I.lshr_Int (I.subWrap (I.lit t (an : Int))
          (mulHi (I.lit t (an : Int)) (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1))))
          (I.lit .i64 1)).val = (((an - xv) / 2 : Nat) : Int) := by
        have h1 : (I.lit .i64 1).val = 1 := um_i64_small (by omega) (by omega)
        rw [← val_of_unsigned_pattern hu, pattern_lshr_Int _ _ (by rw [h1]; omega),
          um_pattern_nat hu _ _ hD, h1]
        rfl
      have hS : (I.addWrap (I.lshr_Int (I.subWrap (I.lit t (an : Int))
          (mulHi (I.lit t (an : Int)) (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1))))
          (I.lit .i64 1))
          (mulHi (I.lit t (an : Int)) (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1)))).val =
          (((an - xv) / 2 + xv : Nat) : Int) := by
        rw [addWrapWraps_proven, hH, hX, show (((an - xv) / 2 : Nat) : Int) + (xv : Int) =
          (((an - xv) / 2 + xv : Nat) : Int) by omega, um_wrap_nat hu _ (by omega)]
      have hSh : (umShift t r).val = ((r.p - t.bits - 1 : Nat) : Int) :=
        um_shift_core r.p t.bits 1 _ (by rw [hA']; rfl) (by omega) hp2 hb.2
      rw [I.lshr_BitInteger_BitUnsigned, lshr_int_val, um_pattern_nat hu _ _ hS,
        um_pattern_nat (t := .u8) rfl _ _ hSh,
        show ((((an - xv) / 2 + xv : Nat) : Int) / 2 ^ (r.p - t.bits - 1)) =
          ((((an - xv) / 2 + xv) / 2 ^ (r.p - t.bits - 1) : Nat) : Int) by norm_cast,
        halg.2, show 2 ^ t.bits * 2 * 2 ^ (r.p - t.bits - 1) = 2 ^ r.p by
          rw [← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega,
        hmag, um_wrap_nat hu _ hdiv_lt]
  · have hA' : decide (2 ^ t.bits ≤ r.q2 + 1) = false := decide_eq_false hA
    by_cases hd1 : dn = 1
    · subst hd1
      have hE : I.eq (I.lit t ((1 : Nat) : Int)) (I.lit .i64 1) = true := by
        rw [eq_eq, um_lit_nat hu hdW, um_i64_small (by omega) (by omega)]
        simp
      simp only [um_inv_mult, um_inv_add, um_inv_div, um_inv_shift, hA', um_mulHi', um_pack',
        um_subWrap, um_convert_self, um_lshrOne', um_addWrap, um_boolValue', um_ifelse',
        um_bind_ok', um_ifelse_false, um_lshr', um_eqValue', um_int', hE, um_ifelse_true,
        Nat.div_one]
      rfl
    · have hE : I.eq (I.lit t (dn : Int)) (I.lit .i64 1) = false := by
        rw [eq_eq, um_lit_nat hu hdW, um_i64_small (by omega) (by omega)]
        simp only [decide_eq_false_iff_not]
        omega
      simp only [um_inv_mult, um_inv_add, um_inv_div, um_inv_shift, hA', um_mulHi', um_pack',
        um_subWrap, um_convert_self, um_lshrOne', um_addWrap, um_boolValue', um_ifelse',
        um_bind_ok', um_ifelse_false, um_lshr', um_eqValue', um_int', hE]
      apply um_ok_bits_eq
      rw [hres]
      have hmval : (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1)).val = ((r.q2 + 1 : Nat) : Int) := by
        rw [um_addWrap_lit, show (r.q2 : Int) + 1 = ((r.q2 + 1 : Nat) : Int) by omega]
        exact um_lit_nat hu (by omega)
      have hX : (mulHi (I.lit t (an : Int)) (I.addWrap (I.lit t (r.q2 : Int)) (I.lit t 1))).val =
          ((an * (r.q2 + 1) / 2 ^ t.bits : Nat) : Int) := by
        rw [mulHi_val, um_lit_nat hu han, hmval]
        norm_cast
      have hSh : (umShift t r).val = ((r.p - t.bits - 0 : Nat) : Int) :=
        um_shift_core r.p t.bits 0 _ (by rw [hA']; rfl) (by omega) hp2 hb.2
      rw [I.lshr_BitInteger_BitUnsigned, lshr_int_val, um_pattern_nat hu _ _ hX,
        um_pattern_nat (t := .u8) rfl _ _ hSh,
        show (((an * (r.q2 + 1) / 2 ^ t.bits : Nat) : Int) / 2 ^ (r.p - t.bits - 0)) =
          ((an * (r.q2 + 1) / 2 ^ t.bits / 2 ^ (r.p - t.bits - 0) : Nat) : Int) by norm_cast,
        Nat.div_div_eq_div_mul, Nat.sub_zero, ← hpS, hmag, um_wrap_nat hu _ hdiv_lt]

end UM3

section UM4

theorem um_as_lit {t : IntTy} (h : t.signed = false) (x : JInt t) :
    ∃ n : Nat, n < 2 ^ t.bits ∧ x = I.lit t (n : Int) := by
  have h0 := nonneg_of_unsigned h x
  have h1 := x.property.2
  have hWc : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := by norm_cast
  simp only [IntTy.max, h, Bool.false_eq_true, ite_false] at h1
  have hn : x.val.toNat < 2 ^ t.bits := by omega
  refine ⟨x.val.toNat, hn, jint_eq ?_⟩
  rw [um_lit_nat h hn]
  omega

theorem um_mul (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees f render).mul ⟨t, a⟩ ⟨t, b⟩ = .ok ⟨t, I.mulSame a b⟩ := by
  change Except.ok (bitsBin I.mulSame ⟨t, a⟩ ⟨t, b⟩) = _
  rw [um_bitsBin_same]

theorem um_divInverse_view {Ty D E : Type} {V : Ty → Type} {domain : IntegerDomains Ty}
    (o : Callees Ty V D E) {T : Ty} (a : V T) (b : UnsignedMultiplicativeInverse V domain T) :
    divInverse a (unsignedView o b) = divUnsignedInverse o a b := Eq.trans rfl rfl

theorem um_getDivisor_view {Ty D E : Type} {V : Ty → Type} {domain : IntegerDomains Ty}
    (o : Callees Ty V D E) {T : Ty} (b : UnsignedMultiplicativeInverse V domain T) :
    (unsignedView o b).getDivisor (unsignedView o b).value = .ok (o.pack T b.divisor) :=
  Eq.trans rfl rfl

theorem um_mod_view {Ty D E : Type} {V : Ty → Type} {domain : IntegerDomains Ty}
    (o : Callees Ty V D E) {T : Ty} (a : V T) (b : UnsignedMultiplicativeInverse V domain T) :
    modUnsignedInverse o a b = rem o a (unsignedView o b) := Eq.trans rfl rfl

theorem um_public_ctor {Ty D E : Type} {V : Ty → Type} (domain : IntegerDomains Ty)
    (o : Callees Ty V D E) {T : Ty} (h : domain.unsigned T) (x : V T) :
    multiplicativeinverseUnsigned domain o h x = unsignedInverseConstructor domain o h x :=
  Eq.trans rfl rfl

theorem um_public_ctor' {Ty D E : Type} {V : Ty → Type} (domain : IntegerDomains Ty)
    (o : Callees Ty V D E) {T : Ty} (h : domain.unsigned T) (x : V T) :
    unsignedMultiplicativeInverse domain o h x = unsignedInverseConstructor domain o h x :=
  Eq.trans rfl rfl

/-- Every nonzero unsigned divisor builds an inverse whose division is exact truncated
division, computed through the real constructor loop and `div`. -/
theorem unsignedInverse_exact (t : IntTy) (h : t.signed = false) (d : JInt t)
    (hd : d.val ≠ 0) :
    ∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      unsignedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        divUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          .ok ⟨t, I.lit t ((a.val.toNat / d.val.toNat : Nat) : Int)⟩ ∧
        JuliaLean.base.multinverses.rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          .ok ⟨t, I.lit t ((a.val.toNat % d.val.toNat : Nat) : Int)⟩ ∧
        divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          .ok (⟨t, I.lit t ((a.val.toNat / d.val.toNat : Nat) : Int)⟩,
            ⟨t, I.lit t ((a.val.toNat % d.val.toNat : Nat) : Int)⟩) := by
  have hb := um_bits_le t
  obtain ⟨dn, hdW, rfl⟩ := um_as_lit h d
  have hdv : (I.lit t (dn : Int)).val = dn := um_lit_nat h hdW
  have hd0 : 0 < dn := by rw [hdv] at hd; omega
  obtain ⟨r, hinv, hstop, hpb, hp2, hq2, hctor⟩ :=
    um_ctor (fun x => pure (toString x.2.val)) h dn hd0 hdW
  refine ⟨umInv t h dn r, hctor, rfl, ?_⟩
  intro a
  obtain ⟨an, han, rfl⟩ := um_as_lit h a
  have hdivv := um_div (fun x => pure (toString x.2.val)) h dn an hd0 hdW han r hinv hstop
    hpb hp2 hq2
  rw [um_lit_nat h han, hdv, Int.toNat_natCast, Int.toNat_natCast]
  have hq : an / dn < 2 ^ t.bits := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) han
  have hrem : I.sub (I.lit t (an : Int)) (I.mulSame (I.lit t ((an / dn : Nat) : Int))
      (I.lit t (dn : Int))) = I.lit t ((an % dn : Nat) : Int) := by
    apply jint_eq
    rw [I.sub, sub_int_val, mulSame_val, wrapInt_sub_right, um_lit_nat h han,
      um_lit_nat h hq, hdv, um_lit_nat h (Nat.lt_of_le_of_lt (Nat.mod_le _ _) han)]
    have hdm := Nat.div_add_mod an dn
    have h2 : ((dn * (an / dn) + an % dn : Nat) : Int) = (an : Int) := by rw [hdm]
    rw [Int.natCast_add, Int.natCast_mul] at h2
    rw [show (an : Int) - ((an / dn : Nat) : Int) * (dn : Int) = ((an % dn : Nat) : Int) by
      rw [← h2, Int.mul_comm (dn : Int)]
      omega]
    exact um_wrap_nat h _ (Nat.lt_of_le_of_lt (Nat.mod_le _ _) han)
  refine ⟨hdivv, ?_, ?_⟩
  · unfold JuliaLean.base.multinverses.rem
    simp only [um_divInverse_view, hdivv, um_bind_ok', um_getDivisor_view, um_inv_div, um_pack',
      um_mul, um_sub, hrem]
  · unfold divremInverse
    simp only [um_divInverse_view, hdivv, um_bind_ok', um_getDivisor_view, um_inv_div, um_pack',
      um_mul, um_sub, hrem]
    rfl

theorem um_tdiv_toNat {t : IntTy} (h : t.signed = false) (a d : JInt t) :
    ((a.val.toNat / d.val.toNat : Nat) : Int) = a.val.tdiv d.val := by
  have ha := nonneg_of_unsigned h a
  have hd := nonneg_of_unsigned h d
  rw [Int.tdiv_eq_ediv_of_nonneg ha, Int.natCast_ediv, Int.toNat_of_nonneg ha,
    Int.toNat_of_nonneg hd]

theorem um_tmod_toNat {t : IntTy} (h : t.signed = false) (a d : JInt t) :
    ((a.val.toNat % d.val.toNat : Nat) : Int) = a.val.tmod d.val := by
  have ha := nonneg_of_unsigned h a
  have hd := nonneg_of_unsigned h d
  rw [Int.tmod_eq_emod_of_nonneg ha, Int.natCast_emod, Int.toNat_of_nonneg ha,
    Int.toNat_of_nonneg hd]

theorem um_fmod_toNat {t : IntTy} (h : t.signed = false) (a d : JInt t) :
    ((a.val.toNat % d.val.toNat : Nat) : Int) = a.val.fmod d.val := by
  have ha := nonneg_of_unsigned h a
  have hd := nonneg_of_unsigned h d
  rw [Int.fmod_eq_emod_of_nonneg _ hd, Int.natCast_emod, Int.toNat_of_nonneg ha,
    Int.toNat_of_nonneg hd]

theorem um_lit_toNat {t : IntTy} (h : t.signed = false) (x : JInt t) (n : Nat)
    (hn : n ≤ x.val.toNat) : (I.lit t (n : Int)).val = n := by
  obtain ⟨m, hm, rfl⟩ := um_as_lit h x
  rw [um_lit_nat h hm, Int.toNat_natCast] at hn
  exact um_lit_nat h (by omega)

theorem unsignedInverseDivision_proven : UnsignedInverseDivision := by
  intro t h d hd
  obtain ⟨inv, hc, hdv, hall⟩ := unsignedInverse_exact t h d hd
  refine ⟨inv, hc, hdv, fun a => ?_⟩
  rw [(hall a).1, divSame_eq,
    if_neg (by rw [h]; simp only [Bool.false_eq_true, false_and, or_false]; exact hd)]
  rw [← um_tdiv_toNat h a d]
  rfl

theorem unsignedInverseRemainderAndModulus (t : IntTy) (h : t.signed = false) (d : JInt t)
    (hd : d.val ≠ 0) :
    ∃ inverse : UnsignedMultiplicativeInverse JInt bitDomains t,
      unsignedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        JuliaLean.base.multinverses.rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)) ∧
        modUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.div.modBitInteger a d).map (fun m => (⟨t, m⟩ : Bits)) := by
  obtain ⟨inv, hc, hdv, hall⟩ := unsignedInverse_exact t h d hd
  refine ⟨inv, hc, hdv, fun a => ⟨?_, ?_⟩⟩
  · rw [(hall a).2.1, remSame_eq, if_neg hd, ← um_tmod_toNat h a d]
    rfl
  · rw [um_mod_view, (hall a).2.1, JuliaLean.Proofs.base.div.modBitInteger_eq, if_neg hd,
      ← um_fmod_toNat h a d]
    rfl

theorem unsignedArithmetic_proven : UnsignedArithmetic := by
  intro t h d hd
  obtain ⟨inv, hc, hdv, hall⟩ := unsignedInverse_exact t h d hd
  refine ⟨inv, hc, hdv, fun a => ?_⟩
  have ha := nonneg_of_unsigned h a
  have hd0 := nonneg_of_unsigned h d
  have hqv := um_lit_toNat h a (a.val.toNat / d.val.toNat) (Nat.div_le_self _ _)
  have hrv := um_lit_toNat h a (a.val.toNat % d.val.toNat) (Nat.mod_le _ _)
  have hdm := Nat.div_add_mod a.val.toNat d.val.toNat
  have hml := Nat.mod_lt a.val.toNat (show 0 < d.val.toNat by omega)
  have h2 : ((d.val.toNat * (a.val.toNat / d.val.toNat) + a.val.toNat % d.val.toNat : Nat) :
      Int) = a.val := by rw [hdm, Int.toNat_of_nonneg ha]
  rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg hd0] at h2
  refine ⟨I.lit t ((a.val.toNat / d.val.toNat : Nat) : Int),
    I.lit t ((a.val.toNat % d.val.toNat : Nat) : Int),
    I.lit t ((a.val.toNat % d.val.toNat : Nat) : Int),
    I.lit t ((a.val.toNat / d.val.toNat : Nat) : Int),
    I.lit t ((a.val.toNat % d.val.toNat : Nat) : Int),
    (hall a).1, (hall a).2.1, by rw [um_mod_view]; exact (hall a).2.1, (hall a).2.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hqv, um_tdiv_toNat h a d]
  · rw [hrv, um_tmod_toNat h a d]
  · rw [hrv, um_fmod_toNat h a d]
  · rw [hqv, um_tdiv_toNat h a d]
  · rw [hrv, um_tmod_toNat h a d]
  · rw [hqv, hrv, Int.mul_comm]
    omega
  · rw [hrv]
    omega
  · rw [hrv]
    omega
  · rw [hrv]
    omega
  · rw [hrv]
    omega

end UM4

section SM

theorem sm_cancel_le {D a b : Nat} (hD : 0 < D) (h : D * a ≤ D * b) : a ≤ b := by
  rcases Nat.lt_or_ge b a with hab | hab
  · have := Nat.mul_lt_mul_of_pos_left hab hD
    omega
  · exact hab

theorem sm_cancel_lt {D a b : Nat} (h : D * a < D * b) : a < b := by
  rcases Nat.lt_or_ge a b with hab | hab
  · exact hab
  · have := Nat.mul_le_mul_left D hab
    omega

theorem sm_core (D anc X e c : Nat) (hD : 2 ≤ D) (hanc : D - 1 ≤ anc)
    (hmod : (anc + 1) % D = 0) (hea : e * anc < X) (hc : c ≤ anc + D - 1) :
    c * e < (D - c % D) * X := by
  have hr := Nat.mod_lt c (show 0 < D by omega)
  rw [Nat.mul_comm e anc] at hea
  by_cases h : c ≤ anc
  · have h1 : c * e ≤ anc * e := Nat.mul_le_mul_right e h
    have h2 : 1 * X ≤ (D - c % D) * X := Nat.mul_le_mul_right X (by omega)
    omega
  · obtain ⟨j, hj⟩ : ∃ j, c = anc + 1 + j := ⟨c - (anc + 1), by omega⟩
    have hjD : j ≤ D - 2 := by omega
    have hcm : c % D = j := by
      rw [hj, Nat.add_mod, hmod, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    have h1 : (1 + j) * e ≤ anc * e := Nat.mul_le_mul_right e (by omega)
    have h2 : c * e = anc * e + (1 + j) * e := by
      rw [hj, show anc + 1 + j = anc + (1 + j) by omega, Nat.add_mul]
    have h3 : 2 * X ≤ (D - j) * X := Nat.mul_le_mul_right X (by omega)
    rw [hcm]
    omega

theorem sm_pos (D M X e b : Nat) (hD : 0 < D) (hM : D * M = X + e)
    (hkey : b * e < (D - b % D) * X) : b * M / X = b / D := by
  have hb := Nat.div_add_mod b D
  have hr := Nat.mod_lt b hD
  apply Nat.div_eq_of_lt_le
  · apply sm_cancel_le hD
    have e1 : D * (b / D * X) = D * (b / D) * X := (Nat.mul_assoc _ _ _).symm
    have e2 : D * (b * M) = b * X + b * e := by
      rw [Nat.mul_left_comm, hM, Nat.mul_add]
    have e3 : D * (b / D) * X ≤ b * X := Nat.mul_le_mul_right X (by omega)
    omega
  · apply sm_cancel_lt (D := D)
    have e2 : D * (b * M) = b * X + b * e := by
      rw [Nat.mul_left_comm, hM, Nat.mul_add]
    have e4 : D * ((b / D + 1) * X) = b * X + (D - b % D) * X := by
      rw [← Nat.mul_assoc, Nat.mul_add, Nat.mul_one, ← Nat.add_mul]
      congr 1
      omega
    omega

theorem sm_neg (D M X e c : Nat) (hD : 0 < D) (hM : D * M = X + e) (he : 0 < e)
    (hc : 0 < c) (hkey : c * e ≤ (D - c % D) * X) :
    c / D * X < c * M ∧ c * M ≤ (c / D + 1) * X := by
  have hb := Nat.div_add_mod c D
  have hr := Nat.mod_lt c hD
  have e2 : D * (c * M) = c * X + c * e := by
    rw [Nat.mul_left_comm, hM, Nat.mul_add]
  have hce : 0 < c * e := Nat.mul_pos hc he
  constructor
  · apply sm_cancel_lt (D := D)
    have e1 : D * (c / D * X) = D * (c / D) * X := (Nat.mul_assoc _ _ _).symm
    have e3 : D * (c / D) * X ≤ c * X := Nat.mul_le_mul_right X (by omega)
    omega
  · apply sm_cancel_le hD
    have e4 : D * ((c / D + 1) * X) = c * X + (D - c % D) * X := by
      rw [← Nat.mul_assoc, Nat.mul_add, Nat.mul_one, ← Nat.add_mul]
      congr 1
      omega
    omega

theorem sm_ediv_of_bounds {x c q : Int} (hc : 0 < c) (h1 : c * q ≤ x) (h2 : x < c * q + c) :
    x / c = q := by
  have h : x = c * q + (x - c * q) := by omega
  rw [h, Int.add_comm, Int.add_mul_ediv_left _ _ (by omega : c ≠ 0),
    Int.ediv_eq_zero_of_lt (by omega) (by omega), Int.zero_add]

/-- Signed magic multiplier: floor(b*M/X) corrected by the sign bit is truncated division. -/
theorem sm_magic (D anc X M e : Nat) (hD : 2 ≤ D) (hanc : D - 1 ≤ anc)
    (hmod : (anc + 1) % D = 0) (hM : D * M = X + e) (he1 : 1 ≤ e) (hea : e * anc < X)
    (b : Int) (hb1 : b ≤ (anc : Int) + D - 1)
    (hb2 : -((anc : Int) + D - 1) ≤ b ∨ (b = -((anc : Int) + D) ∧ (anc + D) * e ≤ X)) :
    b * M / X + (if b < 0 then 1 else 0) = b.tdiv D := by
  have hD0 : 0 < D := by omega
  have hX : 0 < X := by omega
  rcases Int.lt_or_le b 0 with hneg | hpos
  · obtain ⟨c, hcdef⟩ : ∃ c : Nat, b = -(c : Int) := ⟨b.natAbs, by omega⟩
    subst hcdef
    have hc0 : 0 < c := by omega
    have hkey : c * e ≤ (D - c % D) * X := by
      rcases hb2 with hb2 | ⟨hb2, hbig⟩
      · exact Nat.le_of_lt (sm_core D anc X e c hD hanc hmod hea (by omega))
      · have hcv : c = anc + D := by omega
        have hcm : c % D = D - 1 := by
          rw [hcv, show anc + D = (anc + 1) + (D - 1) by omega, Nat.add_mod, hmod,
            Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
        rw [hcm, show D - (D - 1) = 1 by omega, Nat.one_mul, hcv]
        exact hbig
    obtain ⟨hlo, hhi⟩ := sm_neg D M X e c hD0 hM (by omega) hc0 hkey
    rw [if_pos hneg, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega),
      ← Int.natCast_ediv]
    have hhi' : (c : Int) * M ≤ ((c / D : Nat) : Int) * X + X := by
      have h := Int.ofNat_le.mpr hhi
      rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_add, Int.add_mul] at h
      omega
    have hlo' : ((c / D : Nat) : Int) * X < (c : Int) * M := by
      have h := Int.ofNat_lt.mpr hlo
      rw [Int.natCast_mul, Int.natCast_mul] at h
      exact h
    have hXQ : (X : Int) * (-((c / D : Nat) : Int) - 1) = -(((c / D : Nat) : Int) * X) - X := by
      rw [Int.mul_sub, Int.mul_neg, Int.mul_one, Int.mul_comm]
    have hq : -(c : Int) * (M : Int) / (X : Int) = -((c / D : Nat) : Int) - 1 := by
      apply sm_ediv_of_bounds (by omega)
      · rw [hXQ, Int.neg_mul]
        omega
      · rw [hXQ, Int.neg_mul]
        omega
    rw [hq]
    omega
  · obtain ⟨bn, hbdef⟩ : ∃ bn : Nat, b = (bn : Int) := ⟨b.toNat, by omega⟩
    subst hbdef
    have hkey := sm_core D anc X e bn hD hanc hmod hea (by omega)
    have h := sm_pos D M X e bn hD0 hM hkey
    rw [if_neg (by omega), Int.add_zero, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    rw [← Int.natCast_ediv, ← h]
    norm_cast

end SM

section SL

structure SNat where
  p : Nat
  q1 : Nat
  r1 : Nat
  q2 : Nat
  r2 : Nat

def snNext (D anc : Nat) (s : SNat) : SNat :=
  ⟨s.p + 1, 2 * s.q1 + 2 * s.r1 / anc, 2 * s.r1 % anc, 2 * s.q2 + 2 * s.r2 / D, 2 * s.r2 % D⟩

def snCont (D : Nat) (s : SNat) : Prop :=
  s.q1 < D - s.r2 ∨ (s.q1 = D - s.r2 ∧ s.r1 = 0)

instance (D : Nat) (s : SNat) : Decidable (snCont D s) :=
  inferInstanceAs (Decidable (s.q1 < D - s.r2 ∨ (s.q1 = D - s.r2 ∧ s.r1 = 0)))

def snStep (D anc : Nat) (s : SNat) : Except JuliaLean.JlError (Sum SNat SNat) :=
  if snCont D (snNext D anc s) then .ok (.inr (snNext D anc s)) else .ok (.inl (snNext D anc s))

def snInv (D anc : Nat) (s : SNat) : Prop :=
  s.q1 * anc + s.r1 = 2 ^ s.p ∧ s.r1 < anc ∧ s.q2 * D + s.r2 = 2 ^ s.p ∧ s.r2 < D

def sPack (UT : IntTy) (s : SNat) : SignedLoopState Bits :=
  ⟨I.lit .i64 (s.p : Int), ⟨UT, I.lit UT (s.q1 : Int)⟩, ⟨UT, I.lit UT (s.r1 : Int)⟩,
    ⟨UT, I.lit UT (s.q2 : Int)⟩, ⟨UT, I.lit UT (s.r2 : Int)⟩⟩

theorem sm_bind_assoc {E A B C : Type} (r : Except E A)
    (f : A → Except E B) (g : B → Except E C) :
    Except.bind (Except.bind r f) g = Except.bind r (fun a => Except.bind (f a) g) := by
  cases r <;> rfl

theorem sm_bind_ite {E A B : Type} (p : Prop) [Decidable p]
    (a b : Except E A) (k : A → Except E B) :
    Except.bind (if p then a else b) k =
      if p then Except.bind a k else Except.bind b k := by
  by_cases h : p <;> simp [h]

theorem sm_bind_ok {E A B : Type} (a : A) (k : A → Except E B) :
    Except.bind (.ok a) k = k a := rfl

def sPhase {Ty D E : Type} {V : Ty → Type} (o : Callees Ty V D E) (UT : Ty) (c q r : D) :
    Except E (D × D) := do
  let q ← o.shl q (I.lit .i64 1)
  let r ← o.shl r (I.lit .i64 1)
  if ← o.ge r c then do
    let one ← o.oneType UT
    let q ← o.addWrap q one
    let r ← o.sub r c
    pure (q, r)
  else pure (q, r)

theorem sm_step_factor {Ty D E : Type} {V : Ty → Type} (o : Callees Ty V D E) (UT : Ty)
    (anc ad : D) (s : SignedLoopState D) :
    signedInverseStep o UT anc ad s = (do
      let (q1, r1) ← sPhase o UT anc s.q1 s.r1
      let (q2, r2) ← sPhase o UT ad s.q2 s.r2
      let delta ← o.sub ad r2
      let next : SignedLoopState D := ⟨I.add s.p (I.lit .i64 1), q1, r1, q2, r2⟩
      if ← needsAnother o q1 delta r1 then return .inr next
      return .inl next) := by
  simp only [signedInverseStep, sPhase, Bind.bind, pure, Except.pure, sm_bind_assoc,
    sm_bind_ite, sm_bind_ok]

theorem sm_ge (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees f render).ge ⟨t, a⟩ ⟨t, b⟩ = .ok (decide (b.val ≤ a.val)) := by
  change Except.ok (JuliaLean.base.operators.greaterEqual I.le a b) = _
  rw [JuliaLean.base.operators.greaterEqual, le_eq]

theorem sm_shl' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t)
    (n : JInt .i64) :
    (bitsCallees f render).shl ⟨t, x⟩ n = .ok ⟨t, I.shl_Int x n⟩ := Eq.trans rfl rfl

theorem sm_shl_lit {UT : IntTy} (hu : UT.signed = false) (n : Nat) :
    I.shl_Int (I.lit UT (n : Int)) (I.lit .i64 1) = I.lit UT ((2 * n : Nat) : Int) := by
  apply jint_eq
  have h1 : (I.lit .i64 1).val = 1 := um_i64_small (by omega) (by omega)
  have hWc : ((2 ^ UT.bits : Nat) : Int) = (2 : Int) ^ UT.bits := by norm_cast
  have hp : pattern (I.lit UT (n : Int)) = n % 2 ^ UT.bits := by
    apply um_pattern_nat hu
    rw [lit_val, um_wrap_unsigned hu, ← hWc]
    norm_cast
  rw [← val_of_unsigned_pattern hu, pattern_shl_Int _ _ (by rw [h1]; omega), h1, hp,
    lit_val, um_wrap_unsigned hu, ← hWc]
  rw [show (1 : Int).toNat = 1 from rfl, Nat.pow_one]
  norm_cast
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm]

theorem sm_phase_bits (f : SameTypeDivrem) (render : Bits → Jl String) {UT : IntTy}
    (hu : UT.signed = false) (c q r : Nat) (hr : r < c) (hc : 2 * c ≤ 2 ^ UT.bits) :
    sPhase (bitsCallees f render) UT ⟨UT, I.lit UT (c : Int)⟩ ⟨UT, I.lit UT (q : Int)⟩
      ⟨UT, I.lit UT (r : Int)⟩ =
      .ok (⟨UT, I.lit UT ((2 * q + 2 * r / c : Nat) : Int)⟩,
        ⟨UT, I.lit UT ((2 * r % c : Nat) : Int)⟩) := by
  have hd := um_div2 (c := 0) hr (Nat.zero_le 1)
  simp only [Nat.add_zero] at hd
  have hcv : (I.lit UT (c : Int)).val = c := um_lit_nat hu (by omega)
  have hrv : (I.lit UT ((2 * r : Nat) : Int)).val = ((2 * r : Nat) : Int) := um_lit_nat hu (by omega)
  unfold sPhase
  simp only [sm_shl', sm_shl_lit hu, um_bind_ok', sm_ge, hcv, hrv]
  by_cases h : c ≤ 2 * r
  · have hdec : decide ((c : Int) ≤ ((2 * r : Nat) : Int)) = true := decide_eq_true (by omega)
    simp only [hdec, ite_true, um_oneType', um_addWrap, um_sub, um_bind_ok', um_pure',
      um_addWrap_lit, um_sub_lit]
    rw [hd.1, hd.2, if_pos h, if_pos h]
    rw [show ((2 * q : Nat) : Int) + 1 = ((2 * q + 1 : Nat) : Int) by omega,
      show ((2 * r : Nat) : Int) - (c : Int) = ((2 * r - c : Nat) : Int) by omega]
  · have hdec : decide ((c : Int) ≤ ((2 * r : Nat) : Int)) = false := decide_eq_false (by omega)
    simp only [hdec, Bool.false_eq_true, ite_false, um_pure']
    rw [hd.1, hd.2, if_neg h, if_neg h, Nat.add_zero]

theorem sm_needs (f : SameTypeDivrem) (render : Bits → Jl String) {UT : IntTy}
    (hu : UT.signed = false) (D q r r2 : Nat) (hq : q < 2 ^ UT.bits) (hr : r < 2 ^ UT.bits)
    (hr2 : r2 < D) (hD : D < 2 ^ UT.bits) :
    needsAnother (bitsCallees f render) ⟨UT, I.lit UT (q : Int)⟩
      ⟨UT, I.sub (I.lit UT (D : Int)) (I.lit UT (r2 : Int))⟩ ⟨UT, I.lit UT (r : Int)⟩ =
      .ok (decide (q < D - r2 ∨ (q = D - r2 ∧ r = 0))) := by
  have hW := um_natW hD
  rw [unsigned_stop_field_bridge, um_sub_lit, um_lit_nat hu hq, um_lit_nat hu hr,
    um_lit_val hu (by omega) (by omega)]
  congr 1
  rw [decide_eq_decide]
  omega

theorem sm_step_bridge (f : SameTypeDivrem) (render : Bits → Jl String) {UT : IntTy}
    (hu : UT.signed = false) (D anc : Nat) (s : SNat)
    (hD : 2 * D ≤ 2 ^ UT.bits) (hanc : 2 * anc ≤ 2 ^ UT.bits)
    (hr1 : s.r1 < anc) (hr2 : s.r2 < D) (hq1 : (snNext D anc s).q1 < 2 ^ UT.bits) :
    signedInverseStep (bitsCallees f render) UT ⟨UT, I.lit UT (anc : Int)⟩
      ⟨UT, I.lit UT (D : Int)⟩ (sPack UT s) =
      (snStep D anc s).map (Sum.map (sPack UT) (sPack UT)) := by
  have hD0 : 0 < D := by omega
  have hanc0 : 0 < anc := by omega
  rw [sm_step_factor]
  dsimp only [sPack]
  rw [sm_phase_bits f render hu anc s.q1 s.r1 hr1 hanc,
    sm_phase_bits f render hu D s.q2 s.r2 hr2 hD]
  simp only [um_bind_ok', um_sub]
  rw [um_F6, sm_needs f render hu D (2 * s.q1 + 2 * s.r1 / anc) (2 * s.r1 % anc)
    (2 * s.r2 % D) hq1 (by have := Nat.mod_lt (2 * s.r1) hanc0; omega)
    (Nat.mod_lt _ hD0) (by omega)]
  simp only [um_bind_ok']
  unfold snStep
  split
  · rename_i hQ
    have hc : snCont D (snNext D anc s) := of_decide_eq_true hQ
    rw [if_pos hc]
    rfl
  · rename_i hQ
    rw [if_neg (fun hc : snCont D (snNext D anc s) => hQ (decide_eq_true hc))]
    rfl

end SL

section SI

def snInit (W D anc : Nat) : SNat :=
  ⟨W - 1, 2 ^ (W - 1) / anc, 2 ^ (W - 1) % anc, 2 ^ (W - 1) / D, 2 ^ (W - 1) % D⟩

def SParams (W D anc : Nat) : Prop :=
  8 ≤ W ∧ W ≤ 128 ∧ 1 ≤ D ∧ D ≤ 2 ^ (W - 1) ∧ 2 ≤ anc ∧ anc ≤ 2 ^ (W - 1) ∧
    (anc + 1) % D = 0 ∧ D - 1 ≤ anc

def sValid (W D anc : Nat) (s : SNat) : Prop :=
  snInv D anc s ∧ W - 1 ≤ s.p ∧ 2 ^ (s.p + 1) < 2 ^ W * anc ∧ (s.p = W - 1 ∨ snCont D s)

theorem sn_pow_half (W : Nat) (h : 1 ≤ W) : 2 ^ W = 2 * 2 ^ (W - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega⟩
  rw [Nat.pow_succ, Nat.add_sub_cancel, Nat.mul_comm]

theorem sn_next_inv (D anc : Nat) (hD : 0 < D) (ha : 0 < anc) (s : SNat)
    (h : snInv D anc s) : snInv D anc (snNext D anc s) := by
  obtain ⟨h1, _, h3, _⟩ := h
  have e1 := Nat.div_add_mod (2 * s.r1) anc
  have e2 := Nat.div_add_mod (2 * s.r2) D
  refine ⟨?_, Nat.mod_lt _ ha, ?_, Nat.mod_lt _ hD⟩
  · show (2 * s.q1 + 2 * s.r1 / anc) * anc + 2 * s.r1 % anc = 2 ^ (s.p + 1)
    rw [Nat.pow_succ, Nat.add_mul, ← h1, Nat.mul_assoc, Nat.mul_comm (2 * s.r1 / anc) anc]
    omega
  · show (2 * s.q2 + 2 * s.r2 / D) * D + 2 * s.r2 % D = 2 ^ (s.p + 1)
    rw [Nat.pow_succ, Nat.add_mul, ← h3, Nat.mul_assoc, Nat.mul_comm (2 * s.r2 / D) D]
    omega

theorem sn_cont_iff (D anc : Nat) (s : SNat) (h : snInv D anc s) :
    snCont D s ↔ 2 ^ s.p ≤ (D - s.r2) * anc := by
  obtain ⟨h1, h2, _, _⟩ := h
  unfold snCont
  constructor
  · rintro (hq | ⟨hq, hr⟩)
    · have := Nat.mul_le_mul_right anc (show s.q1 + 1 ≤ D - s.r2 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · rw [← hq]
      omega
  · intro hle
    rcases Nat.lt_trichotomy s.q1 (D - s.r2) with hq | hq | hq
    · exact Or.inl hq
    · refine Or.inr ⟨hq, ?_⟩
      rw [hq] at h1
      omega
    · exfalso
      have := Nat.mul_le_mul_right anc (show D - s.r2 + 1 ≤ s.q1 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega

theorem sn_pow_mod_odd (D : Nat) (hD : 3 ≤ D) (hodd : D % 2 = 1) (k : Nat) :
    2 ^ k % D ≠ 0 := by
  induction k with
  | zero =>
      rw [Nat.pow_zero, Nat.mod_eq_of_lt (by omega)]
      omega
  | succ k ih =>
      have hy := Nat.mod_lt (2 ^ k) (show 0 < D by omega)
      rw [Nat.pow_succ, Nat.mul_mod, Nat.mod_eq_of_lt (show 2 < D by omega)]
      by_cases hlt : 2 ^ k % D * 2 < D
      · rw [Nat.mod_eq_of_lt hlt]
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega

theorem sn_valid_p (W D anc : Nat) (hP : SParams W D anc) (s : SNat)
    (hs : sValid W D anc s) : s.p ≤ 2 * W - 2 := by
  obtain ⟨hW8, -, hD1, hDX, -, hancX, -, -⟩ := hP
  rcases hs.2.2.2 with h | h
  · omega
  · have hc := (sn_cont_iff D anc s hs.1).1 h
    have h1 : (D - s.r2) * anc ≤ D * anc := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h2 : D * anc ≤ 2 ^ (W - 1) * 2 ^ (W - 1) := Nat.mul_le_mul hDX hancX
    rw [← Nat.pow_add] at h2
    refine Classical.byContradiction (fun hp => ?_)
    have h3 : 2 ^ (2 * W - 1) ≤ 2 ^ s.p := Nat.pow_le_pow_right (by decide) (by omega)
    have h4 : 2 ^ (2 * W - 1) = 2 * 2 ^ (W - 1 + (W - 1)) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    have h5 : 0 < 2 ^ (W - 1 + (W - 1)) := Nat.pow_pos (by decide)
    omega

theorem sn_valid_next (W D anc : Nat) (hP : SParams W D anc) (s : SNat)
    (hs : sValid W D anc s) (hc : snCont D (snNext D anc s)) :
    sValid W D anc (snNext D anc s) := by
  obtain ⟨hW8, hW128, hD1, hDX, hanc2, hancX, hmod, hDanc⟩ := hP
  have hn := sn_next_inv D anc (by omega) (by omega) s hs.1
  have hpn : (snNext D anc s).p = s.p + 1 := rfl
  refine ⟨hn, by rw [hpn]; exact Nat.le_succ_of_le hs.2.1, ?_, Or.inr hc⟩
  have hcc := (sn_cont_iff D anc _ hn).1 hc
  rw [hpn] at hcc ⊢
  have hW := sn_pow_half W (by omega)
  have hr2 := hn.2.2.2
  rw [Nat.pow_succ]
  by_cases he : (D - (snNext D anc s).r2) + 1 ≤ 2 ^ (W - 1)
  · have hA : (D - (snNext D anc s).r2) * anc + anc ≤ 2 ^ (W - 1) * anc := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ he
    have hB : 2 ^ W * anc = 2 * (2 ^ (W - 1) * anc) := by rw [hW, Nat.mul_assoc]
    omega
  · have hDe : D = 2 ^ (W - 1) := by omega
    have hrz : D - (snNext D anc s).r2 = D := by omega
    rw [hrz] at hcc
    have h128 : 128 ≤ 2 ^ (W - 1) :=
      Nat.le_trans (by decide : 128 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by decide) (by omega))
    have hodd : anc % 2 = 1 := by
      have h2 : 2 ∣ D := by
        have := Nat.pow_dvd_pow 2 (show 1 ≤ W - 1 by omega)
        rw [Nat.pow_one, ← hDe] at this
        exact this
      have h3 := Nat.mod_mod_of_dvd (anc + 1) h2
      rw [hmod] at h3
      omega
    have hne : 2 ^ (s.p + 1) ≠ D * anc := by
      intro heq
      have := sn_pow_mod_odd anc (by omega) hodd (s.p + 1)
      rw [heq, Nat.mul_mod_left] at this
      exact this rfl
    have hB : 2 ^ W * anc = 2 * (D * anc) := by rw [hW, hDe, Nat.mul_assoc]
    omega

theorem sn_init_valid (W D anc : Nat) (hP : SParams W D anc) :
    sValid W D anc (snInit W D anc) := by
  obtain ⟨hW8, -, hD1, hDX, hanc2, hancX, -, -⟩ := hP
  have e1 := Nat.div_add_mod (2 ^ (W - 1)) anc
  have e2 := Nat.div_add_mod (2 ^ (W - 1)) D
  refine ⟨⟨?_, Nat.mod_lt _ (by omega), ?_, Nat.mod_lt _ (by omega)⟩, Nat.le_refl _, ?_,
    Or.inl rfl⟩
  · show 2 ^ (W - 1) / anc * anc + 2 ^ (W - 1) % anc = 2 ^ (W - 1)
    rw [Nat.mul_comm]
    exact e1
  · show 2 ^ (W - 1) / D * D + 2 ^ (W - 1) % D = 2 ^ (W - 1)
    rw [Nat.mul_comm]
    exact e2
  · show 2 ^ (W - 1 + 1) < 2 ^ W * anc
    rw [Nat.sub_add_cancel (by omega)]
    have h0 : 0 < 2 ^ W := Nat.pow_pos (by decide)
    have := Nat.mul_lt_mul_of_pos_left (show 1 < anc by omega) h0
    omega

theorem sn_M_bound (W D anc : Nat) (hP : SParams W D anc) (hD2 : 2 ≤ D) (s : SNat)
    (hs : sValid W D anc s) : (snNext D anc s).q2 + 1 < 2 ^ W := by
  obtain ⟨hW8, hW128, hD1, hDX, hanc2, hancX, hmod, hDanc⟩ := hP
  have hW := sn_pow_half W (by omega)
  have hn := sn_next_inv D anc (by omega) (by omega) s hs.1
  have h1 := hn.2.2.1
  have hr2 := hn.2.2.2
  change (snNext D anc s).q2 * D + (snNext D anc s).r2 = 2 ^ (s.p + 1) at h1
  apply Nat.lt_of_mul_lt_mul_right (a := D)
  rw [Nat.add_mul, Nat.one_mul]
  rcases hs.2.2.2 with hp | hc
  · rw [hp, Nat.sub_add_cancel (by omega)] at h1
    have : 2 ^ W * 2 ≤ 2 ^ W * D := Nat.mul_le_mul_left _ hD2
    omega
  · have hcc := (sn_cont_iff D anc s hs.1).1 hc
    rw [Nat.pow_succ] at h1
    by_cases hz : s.r2 = 0
    · rw [hz, Nat.sub_zero] at hcc
      by_cases ha : anc + 1 ≤ 2 ^ (W - 1)
      · have hA : D * anc + D ≤ D * 2 ^ (W - 1) := by
          rw [← Nat.mul_succ]
          exact Nat.mul_le_mul_left _ ha
        have hB : 2 ^ W * D = 2 * (D * 2 ^ (W - 1)) := by
          rw [hW, Nat.mul_comm D, Nat.mul_assoc]
        omega
      · exfalso
        have hae : anc = 2 ^ (W - 1) := by omega
        have h4 : 2 ^ (W - 1) % 2 = 0 := by
          rw [sn_pow_half (W - 1) (by omega)]
          exact Nat.mul_mod_right 2 _
        have hodd : D % 2 = 1 := by
          refine Classical.byContradiction (fun hev => ?_)
          have h2 : 2 ∣ D := Nat.dvd_of_mod_eq_zero (by omega)
          have h3 := Nat.mod_mod_of_dvd (anc + 1) h2
          rw [hmod, hae] at h3
          omega
        have hs2 := hs.1.2.2.1
        rw [hz, Nat.add_zero] at hs2
        have := sn_pow_mod_odd D (by omega) hodd s.p
        rw [← hs2, Nat.mul_mod_left] at this
        exact this rfl
    · have hA : (D - s.r2) * anc ≤ (D - 1) * anc := Nat.mul_le_mul_right _ (by omega)
      have hB : (D - 1) * anc ≤ (D - 1) * 2 ^ (W - 1) := Nat.mul_le_mul_left _ hancX
      have hC : (D - 1) * 2 ^ (W - 1) + 2 ^ (W - 1) = D * 2 ^ (W - 1) := by
        rw [← Nat.succ_mul]
        congr 1
        omega
      have hE : 2 ^ W * D = 2 * (D * 2 ^ (W - 1)) := by
        rw [hW, Nat.mul_comm D, Nat.mul_assoc]
      omega

theorem sn_params (W D sg : Nat) (hW8 : 8 ≤ W) (hW128 : W ≤ 128) (hD1 : 1 ≤ D)
    (hDX : D ≤ 2 ^ (W - 1)) (hsg : sg ≤ 1) :
    SParams W D (2 ^ (W - 1) + sg - 1 - (2 ^ (W - 1) + sg) % D) := by
  have hX : 128 ≤ 2 ^ (W - 1) :=
    Nat.le_trans (by decide : 128 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by decide) (by omega))
  have e := Nat.div_add_mod (2 ^ (W - 1) + sg) D
  have hm := Nat.mod_lt (2 ^ (W - 1) + sg) (show 0 < D by omega)
  have hk : 0 < (2 ^ (W - 1) + sg) / D := Nat.div_pos (by omega) (by omega)
  have hP : D ≤ D * ((2 ^ (W - 1) + sg) / D) := Nat.le_mul_of_pos_right D hk
  refine ⟨hW8, hW128, hD1, hDX, by omega, by omega, ?_, by omega⟩
  have h : 2 ^ (W - 1) + sg - 1 - (2 ^ (W - 1) + sg) % D + 1 =
      D * ((2 ^ (W - 1) + sg) / D) := by omega
  rw [h]
  exact Nat.mul_mod_right _ _

theorem sm_loop_def' {Ty D E : Type} {V : Ty → Type} (o : Callees Ty V D E) (UT : Ty)
    (anc ad : D) (s : SignedLoopState D) :
    signedInverseLoop o UT anc ad s = whileLoop (signedInverseStep o UT anc ad) s :=
  Eq.trans rfl rfl

theorem sm_loop (f : SameTypeDivrem) (render : Bits → Jl String) {UT : IntTy}
    (hu : UT.signed = false) (D anc : Nat) (hP : SParams UT.bits D anc) (s : SNat)
    (hs : sValid UT.bits D anc s) :
    ∃ s', sValid UT.bits D anc s' ∧ ¬ snCont D (snNext D anc s') ∧
      whileLoop (signedInverseStep (bitsCallees f render) UT ⟨UT, I.lit UT (anc : Int)⟩
        ⟨UT, I.lit UT (D : Int)⟩) (sPack UT s) = some (.ok (sPack UT (snNext D anc s'))) := by
  have hP' := hP
  obtain ⟨hW8, hW128, hD1, hDX, hanc2, hancX, hmod, hDanc⟩ := hP'
  have hW := sn_pow_half UT.bits (by omega)
  suffices total : ∀ fuel s, 2 * UT.bits - s.p < fuel → sValid UT.bits D anc s →
      ∃ s', sValid UT.bits D anc s' ∧ ¬ snCont D (snNext D anc s') ∧
        whileLoop (signedInverseStep (bitsCallees f render) UT ⟨UT, I.lit UT (anc : Int)⟩
          ⟨UT, I.lit UT (D : Int)⟩) (sPack UT s) =
          some (.ok (sPack UT (snNext D anc s'))) from
    total _ s (Nat.lt_succ_self _) hs
  intro fuel
  induction fuel with
  | zero =>
      intro s h _
      omega
  | succ fuel ih =>
      intro s hf hs
      have hp := sn_valid_p UT.bits D anc hP s hs
      have hn := sn_next_inv D anc (by omega) (by omega) s hs.1
      have hq1 : (snNext D anc s).q1 < 2 ^ UT.bits := by
        have h1 := hn.1
        have h2 := hs.2.2.1
        change (snNext D anc s).q1 * anc + (snNext D anc s).r1 = 2 ^ (s.p + 1) at h1
        apply Nat.lt_of_mul_lt_mul_right (a := anc)
        omega
      have hbridge := sm_step_bridge f render hu D anc s (by omega) (by omega) hs.1.2.1
        hs.1.2.2.2 hq1
      by_cases hc : snCont D (snNext D anc s)
      · have hmodel : signedInverseStep (bitsCallees f render) UT ⟨UT, I.lit UT (anc : Int)⟩
            ⟨UT, I.lit UT (D : Int)⟩ (sPack UT s) = .ok (.inr (sPack UT (snNext D anc s))) := by
          rw [hbridge]
          unfold snStep
          rw [if_pos hc]
          rfl
        obtain ⟨s', hv, hst, hr⟩ := ih (snNext D anc s)
          (by change 2 * UT.bits - (s.p + 1) < fuel; omega) (sn_valid_next UT.bits D anc hP s hs hc)
        refine ⟨s', hv, hst, ?_⟩
        rw [whileLoop.eq_def, hmodel]
        exact hr
      · have hmodel : signedInverseStep (bitsCallees f render) UT ⟨UT, I.lit UT (anc : Int)⟩
            ⟨UT, I.lit UT (D : Int)⟩ (sPack UT s) = .ok (.inl (sPack UT (snNext D anc s))) := by
          rw [hbridge]
          unfold snStep
          rw [if_neg hc]
          rfl
        refine ⟨s, hs, hc, ?_⟩
        rw [whileLoop.eq_def, hmodel]

/-! ## Model-level initial state -/

theorem sm_toU_signed (t : IntTy) : t.toUnsigned.signed = false := by cases t <;> rfl

theorem sm_toU_bits (t : IntTy) : t.toUnsigned.bits = t.bits := by cases t <;> rfl

theorem sm_utype (t : IntTy) (h : t.signed = true) : unsignedTypeBits t = t.toUnsigned := by
  cases t <;> first | rfl | (simp [IntTy.signed] at h)

theorem sm_typemin' (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy) :
    (bitsCallees f render).typemin t = .ok ⟨t, I.typemin t⟩ := Eq.trans rfl rfl

theorem sm_unsigned' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).unsigned ⟨t, x⟩ = .ok ⟨t.toUnsigned, I.unsigned x⟩ := Eq.trans rfl rfl

theorem sm_unsignedType' (f : SameTypeDivrem) (render : Bits → Jl String) (t : IntTy) :
    (bitsCallees f render).unsignedType t = .ok (unsignedTypeBits t) := Eq.trans rfl rfl

theorem sm_abs' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).abs ⟨t, x⟩ = .ok ⟨t, I.abs x⟩ := Eq.trans rfl rfl

theorem sm_signbit' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).signbit ⟨t, x⟩ = .ok (I.signbit x) := Eq.trans rfl rfl

theorem sm_signbit_bind (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (x : JInt t) {B : Type} (k : (bitsCallees f render).Sign → Except JlError B) :
    (bind ((bitsCallees f render).signbit ⟨t, x⟩) k : Except JlError B) = k (I.signbit x) :=
  Eq.trans rfl rfl

theorem sm_addRightSign' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (x : JInt t) (b : Bool) :
    (bitsCallees f render).addRightSign ⟨t, x⟩ b =
      .ok ⟨t, I.op_Integer t I.add (I.remT t) (I.rem_Bool_Type t) x b⟩ := Eq.trans rfl rfl

theorem sm_flipsign' (f : SameTypeDivrem) (render : Bits → Jl String) {s u : IntTy}
    (x : JInt s) (y : JInt u) :
    (bitsCallees f render).flipsign ⟨s, x⟩ ⟨u, y⟩ = .ok ⟨s, I.flipsign x y⟩ := Eq.trans rfl rfl

theorem sm_gt' (f : SameTypeDivrem) (render : Bits → Jl String) {s u : IntTy}
    (x : JInt s) (y : JInt u) :
    (bitsCallees f render).gt ⟨s, x⟩ ⟨u, y⟩ = .ok (I.lt y x) := Eq.trans rfl rfl

theorem sm_lt' (f : SameTypeDivrem) (render : Bits → Jl String) {s u : IntTy}
    (x : JInt s) (y : JInt u) :
    (bitsCallees f render).lt ⟨s, x⟩ ⟨u, y⟩ = .ok (I.lt x y) := Eq.trans rfl rfl

theorem sm_toUInt8' (f : SameTypeDivrem) (render : Bits → Jl String) (x : JInt .i64) :
    (bitsCallees f render).toUInt8 x = I.convert .u8 x := Eq.trans rfl rfl

theorem sm_pack_q2 (UT : IntTy) (r : SNat) :
    (sPack UT r).q2 = ⟨UT, I.lit UT (r.q2 : Int)⟩ := Eq.trans rfl rfl

theorem sm_pack_p (UT : IntTy) (r : SNat) :
    (sPack UT r).p = I.lit .i64 (r.p : Int) := Eq.trans rfl rfl

def smD {t : IntTy} (d : JInt t) : Nat := d.val.natAbs

def smSg {t : IntTy} (d : JInt t) : Nat := if d.val < 0 then 1 else 0

def smAnc {t : IntTy} (d : JInt t) : Nat :=
  2 ^ (t.bits - 1) + smSg d - 1 - (2 ^ (t.bits - 1) + smSg d) % smD d

theorem sm_d_bounds {t : IntTy} (h : t.signed = true) (d : JInt t) (hd : d.val ≠ 0) :
    1 ≤ smD d ∧ smD d ≤ 2 ^ (t.bits - 1) ∧ smSg d ≤ 1 := by
  have hx := d.property
  simp only [IntTy.min, IntTy.max, h, if_true] at hx
  have hXc : ((2 ^ (t.bits - 1) : Nat) : Int) = (2 : Int) ^ (t.bits - 1) := by norm_cast
  unfold smD smSg
  refine ⟨by omega, by omega, by split <;> omega⟩

theorem sm_params {t : IntTy} (h : t.signed = true) (d : JInt t) (hd : d.val ≠ 0) :
    SParams t.toUnsigned.bits (smD d) (smAnc d) := by
  have hb := um_bits_le t
  obtain ⟨h1, h2, h3⟩ := sm_d_bounds h d hd
  rw [sm_toU_bits]
  exact sn_params t.bits (smD d) (smSg d) hb.1 hb.2 h1 h2 h3

theorem sm_init (render : Bits → Jl String) {t : IntTy} (h : t.signed = true) (d : JInt t)
    (hd : d.val ≠ 0) :
    signedInverseConstructor.initialState
        (bitsCallees JuliaLean.base.intfuncs.divremBits render) (T := t) d =
      .ok (t.toUnsigned, ⟨t.toUnsigned, I.lit t.toUnsigned (smAnc d : Int)⟩,
        ⟨t.toUnsigned, I.lit t.toUnsigned (smD d : Int)⟩,
        sPack t.toUnsigned (snInit t.toUnsigned.bits (smD d) (smAnc d))) := by
  have hb := um_bits_le t
  have hu := sm_toU_signed t
  have hbits := sm_toU_bits t
  obtain ⟨hD1, hDX, hsg⟩ := sm_d_bounds h d hd
  have hP := sm_params h d hd
  obtain ⟨-, -, -, -, hanc2, hancX, -, -⟩ := hP
  rw [hbits] at hancX
  have hW := sn_pow_half t.bits (by omega)
  have hh : 0 < 2 ^ (t.bits - 1) := Nat.pow_pos (by decide)
  have hWU : 2 ^ t.toUnsigned.bits = 2 * 2 ^ (t.bits - 1) := by rw [hbits, hW]
  have hXc : ((2 ^ (t.bits - 1) : Nat) : Int) = (2 : Int) ^ (t.bits - 1) := by norm_cast
  have hWc : ((2 ^ t.toUnsigned.bits : Nat) : Int) = (2 : Int) ^ t.toUnsigned.bits := by
    norm_cast
  have hT0 : 2 ^ (t.bits - 1) + smSg d < 2 ^ t.toUnsigned.bits := by omega
  have hm := Nat.mod_lt (2 ^ (t.bits - 1) + smSg d) (show 0 < smD d by omega)
  have hml := Nat.mod_le (2 ^ (t.bits - 1) + smSg d) (smD d)
  have h_eq : I.eq d (I.lit .i64 0) = false := by
    rw [eq_eq, um_i64_small (by omega) (by omega)]
    simp only [decide_eq_false_iff_not]
    exact hd
  have h_smin : I.unsigned (I.typemin t) =
      I.lit t.toUnsigned ((2 ^ (t.bits - 1) : Nat) : Int) := by
    apply jint_eq
    rw [unsigned_val, typemin_val, um_lit_nat hu (by omega), um_wrap_unsigned hu, ← hWc]
    simp only [IntTy.min, h, if_true]
    rw [hXc, show -(2 : Int) ^ (t.bits - 1) =
        (2 : Int) ^ (t.bits - 1) + ((2 ^ t.toUnsigned.bits : Nat) : Int) * (-1) by
      rw [hWU]; push_cast; omega,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by rw [hWU]; push_cast; omega)]
  have h_ad : I.unsigned (I.abs d) = I.lit t.toUnsigned (smD d : Int) := by
    apply jint_eq
    rw [unsigned_abs_val h, um_lit_nat hu (by omega)]
    rfl
  have h_sb : I.signbit d = decide (d.val < 0) := signed_signbit_val h d
  have h_t : I.op_Integer t.toUnsigned I.add (I.remT t.toUnsigned) (I.rem_Bool_Type t.toUnsigned)
      (I.lit t.toUnsigned ((2 ^ (t.bits - 1) : Nat) : Int)) (decide (d.val < 0)) =
      I.lit t.toUnsigned ((2 ^ (t.bits - 1) + smSg d : Nat) : Int) := by
    apply jint_eq
    have hrb : (I.rem_Bool_Type t.toUnsigned (decide (d.val < 0))).val = ((smSg d : Nat) : Int) := by
      have hr := remBool_proven t.toUnsigned (decide (d.val < 0))
      change (I.rem_Bool_Type t.toUnsigned (decide (d.val < 0))).val = _ at hr
      rw [hr]
      unfold smSg
      by_cases hneg : d.val < 0 <;> simp [hneg]
    change (I.add (I.remT t.toUnsigned (I.lit t.toUnsigned ((2 ^ (t.bits - 1) : Nat) : Int)))
      (I.rem_Bool_Type t.toUnsigned (decide (d.val < 0)))).val = _
    rw [I.add, add_int_val, remT_val, um_lit_nat hu (by omega), um_wrap_nat hu _ (by omega), hrb,
      um_lit_nat hu hT0, ← Int.natCast_add, um_wrap_nat hu _ hT0]
  have h_first : I.sub (I.lit t.toUnsigned ((2 ^ (t.bits - 1) + smSg d : Nat) : Int))
      (I.lit t.toUnsigned 1) = I.lit t.toUnsigned ((2 ^ (t.bits - 1) + smSg d - 1 : Nat) : Int) := by
    rw [um_sub_lit]
    exact congrArg (I.lit t.toUnsigned) (by omega)
  have h_rem := um_rem_lits render hu (2 ^ (t.bits - 1) + smSg d) (smD d) (by omega) hT0
    (by omega)
  have h_anc : I.sub (I.lit t.toUnsigned ((2 ^ (t.bits - 1) + smSg d - 1 : Nat) : Int))
      (I.lit t.toUnsigned (((2 ^ (t.bits - 1) + smSg d) % smD d : Nat) : Int)) =
      I.lit t.toUnsigned (smAnc d : Int) := by
    rw [um_sub_lit]
    unfold smAnc
    exact congrArg (I.lit t.toUnsigned) (by omega)
  have h_p : I.sub (I.lit .i64 (t.bits : Int)) (I.lit .i64 1) =
      I.lit .i64 ((t.bits - 1 : Nat) : Int) := by
    rw [um_sub_lit]
    exact congrArg (I.lit .i64) (by omega)
  have h_dr1 := um_divrem_lits render hu (2 ^ (t.bits - 1)) (smAnc d) (by omega) (by omega)
    (by omega)
  have h_dr2 := um_divrem_lits render hu (2 ^ (t.bits - 1)) (smD d) (by omega) (by omega)
    (by omega)
  unfold signedInverseConstructor.initialState sPack snInit
  rw [hbits]
  simp only [um_pack', um_int', um_eq', h_eq, um_bind_ok', Bool.false_eq_true, ite_false,
    sm_typemin', sm_unsigned', h_smin, sm_unsignedType', sm_utype t h, sm_abs', h_ad,
    sm_signbit_bind, h_sb, sm_addRightSign', h_t, um_oneType', um_sub, h_first, h_rem, h_anc,
    um_bitsizeof', h_p, h_dr1, h_dr2, um_pure']

/-! ## Constructor -/

def smM {t : IntTy} (d : JInt t) (q2 : Nat) : JInt t :=
  I.flipsign (I.remT t (I.addWrap (I.lit t.toUnsigned (q2 : Int)) (I.lit t.toUnsigned 1))) d

def smNeg (dneg mpos : Bool) : JInt .i8 :=
  if dneg = true then (if mpos = true then I.lit .i8 (-1) else I.lit .i8 0) else I.lit .i8 0

def smAddmul (dpos mneg dneg mpos : Bool) : JInt .i8 :=
  if dpos = true then (if mneg = true then I.lit .i8 1 else smNeg dneg mpos) else smNeg dneg mpos

def smInv {t : IntTy} (h : t.signed = true) (d : JInt t) (q2 p : Nat) :
    SignedMultiplicativeInverse JInt bitDomains t :=
  ⟨h, d, smM d q2,
    smAddmul (I.lt (I.lit .i64 0) d) (I.lt (smM d q2) (I.lit .i64 0)) (I.lt d (I.lit .i64 0))
      (I.lt (I.lit .i64 0) (smM d q2)),
    I.lit .u8 ((p - t.bits : Nat) : Int)⟩

theorem sm_negcase (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (d m : JInt t) :
    signedInverseConstructor.negativeCase (bitsCallees f render) d ⟨t, m⟩ =
      .ok (smNeg (I.lt d (I.lit .i64 0)) (I.lt (I.lit .i64 0) m)) := by
  unfold signedInverseConstructor.negativeCase smNeg
  simp only [um_pack', um_int', sm_lt', sm_gt', um_bind_ok', um_pure']
  generalize I.lt d (I.lit .i64 0) = A
  generalize I.lt (I.lit .i64 0) m = B
  cases A <;> cases B <;> rfl

theorem sm_convert_u8 (n : Nat) (hn : n < 256) :
    I.convert .u8 (I.lit .i64 (n : Int)) = .ok (I.lit .u8 (n : Int)) := by
  have h1 : (I.lit .i64 (n : Int)).val = n := um_i64_small (by omega) (by omega)
  have h2 : (I.lit .u8 (n : Int)).val = n :=
    um_lit_nat (t := .u8) rfl (Nat.lt_of_lt_of_le hn (by decide))
  have hr : IntTy.min .u8 ≤ (I.lit .i64 (n : Int)).val ∧
      (I.lit .i64 (n : Int)).val ≤ IntTy.max .u8 := by
    rw [h1]
    have hp := (I.lit .u8 (n : Int)).property
    rw [h2] at hp
    exact hp
  unfold I.convert JInt.convert
  rw [dif_pos hr]
  exact congrArg Except.ok (jint_eq (by rw [h2]; exact h1))

theorem sm_ctor (render : Bits → Jl String) {t : IntTy} (h : t.signed = true) (d : JInt t)
    (hd : d.val ≠ 0) :
    ∃ s : SNat, sValid t.toUnsigned.bits (smD d) (smAnc d) s ∧
      ¬ snCont (smD d) (snNext (smD d) (smAnc d) s) ∧
      signedInverseConstructor bitDomains
        (bitsCallees JuliaLean.base.intfuncs.divremBits render) (T := t) h d =
        some (.ok (smInv h d (snNext (smD d) (smAnc d) s).q2
          (snNext (smD d) (smAnc d) s).p)) := by
  have hb := um_bits_le t
  have hu := sm_toU_signed t
  have hbits := sm_toU_bits t
  have hP := sm_params h d hd
  obtain ⟨s, hv, hstop, hloop⟩ := sm_loop JuliaLean.base.intfuncs.divremBits render hu
    (smD d) (smAnc d) hP _ (sn_init_valid _ _ _ hP)
  refine ⟨s, hv, hstop, ?_⟩
  have hp := sn_valid_p _ _ _ hP s hv
  have hpl := hv.2.1
  rw [hbits] at hp hpl
  have hpn : (snNext (smD d) (smAnc d) s).p = s.p + 1 := rfl
  have h_s : I.sub (I.lit .i64 ((snNext (smD d) (smAnc d) s).p : Int)) (I.lit .i64 (t.bits : Int)) =
      I.lit .i64 (((snNext (smD d) (smAnc d) s).p - t.bits : Nat) : Int) := by
    rw [um_sub_lit, hpn]
    exact congrArg (I.lit .i64) (by omega)
  have h_u8 := sm_convert_u8 ((snNext (smD d) (smAnc d) s).p - t.bits) (by rw [hpn]; omega)
  unfold signedInverseConstructor smInv smM
  rw [sm_init render h d hd]
  simp only [um_after_ok', sm_loop_def', hloop, um_continueRun_some', um_oneType',
    sm_pack_q2, sm_pack_p, um_addWrap, um_remType', um_pack', sm_flipsign', um_bitsizeof', h_s,
    um_int', sm_gt', sm_lt', sm_negcase, sm_toUInt8', h_u8, um_field', um_jconvert_self,
    um_bind_ok', um_pure']
  unfold smAddmul
  generalize I.lt (I.lit .i64 0) d = A
  generalize I.lt (I.flipsign (I.remT t (I.addWrap
    (I.lit t.toUnsigned ((snNext (smD d) (smAnc d) s).q2 : Int)) (I.lit t.toUnsigned 1))) d)
    (I.lit .i64 0) = B
  cases A <;> cases B <;> rfl

end SI

section SD

/-! ## Integer helpers -/

theorem sm_ediv_ediv (y P S : Int) (hP : 0 < P) (hS : 0 < S) : y / P / S = y / (P * S) := by
  have e1 : y % P + P * (y / P) = y := by rw [Int.emod_def]; omega
  have e2 : (y / P) % S + S * (y / P / S) = y / P := by rw [Int.emod_def]; omega
  have r1 := Int.emod_nonneg y (show P ≠ 0 by omega)
  have r1' := Int.emod_lt_of_pos y hP
  have r2 := Int.emod_nonneg (y / P) (show S ≠ 0 by omega)
  have r2' := Int.emod_lt_of_pos (y / P) hS
  have hA : P * (y / P) = P * ((y / P) % S) + P * S * (y / P / S) := by
    conv => lhs; rw [← e2]
    rw [Int.mul_add, Int.mul_assoc]
  have hR : P * ((y / P) % S) ≤ P * (S - 1) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have hR0 : 0 ≤ P * ((y / P) % S) := Int.mul_nonneg (by omega) r2
  have hS1 : P * (S - 1) = P * S - P := by rw [Int.mul_sub, Int.mul_one]
  symm
  apply sm_ediv_of_bounds (Int.mul_pos hP hS)
  · omega
  · omega

theorem sm_ediv_neg_iff (y P : Int) (hP : 0 < P) : y / P < 0 ↔ y < 0 := by
  have e1 : y % P + P * (y / P) = y := by rw [Int.emod_def]; omega
  have r1 := Int.emod_nonneg y (show P ≠ 0 by omega)
  have r1' := Int.emod_lt_of_pos y hP
  constructor
  · intro hq
    have := Int.mul_le_mul_of_nonneg_left (show y / P ≤ -1 by omega) (Int.le_of_lt hP)
    omega
  · intro hy
    refine Classical.byContradiction (fun hq => ?_)
    have := Int.mul_nonneg (Int.le_of_lt hP) (show 0 ≤ y / P by omega)
    omega

theorem sm_range (b MI Hh P : Int) (hP : P = 2 * Hh) (hH : 0 < Hh) (hb1 : -Hh ≤ b)
    (hb2 : b ≤ Hh) (hM1 : 0 ≤ MI) (hM2 : MI < P) :
    -Hh ≤ b * MI / P ∧ b * MI / P < Hh := by
  have hP0 : 0 < P := by omega
  have e1 : b * MI % P + P * (b * MI / P) = b * MI := by rw [Int.emod_def]; omega
  have r1 := Int.emod_nonneg (b * MI) (show P ≠ 0 by omega)
  have r1' := Int.emod_lt_of_pos (b * MI) hP0
  have hlo : -(Hh * P) ≤ b * MI := by
    rcases Int.lt_or_le b 0 with hn | hn
    · have h1 := Int.mul_le_mul_of_nonneg_right hb1 hM1
      have h2 := Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hM2) (Int.le_of_lt hH)
      rw [Int.neg_mul] at h1
      omega
    · have := Int.mul_nonneg hn hM1
      have := Int.mul_pos hH hP0
      omega
  have hhi : b * MI < Hh * P := by
    rcases Int.lt_or_le 0 b with hn | hn
    · have h1 := Int.mul_le_mul_of_nonneg_right hb2 hM1
      have h2 := Int.mul_lt_mul_of_pos_left hM2 hH
      omega
    · have h1 := Int.mul_nonneg (show 0 ≤ -b by omega) hM1
      rw [Int.neg_mul] at h1
      have := Int.mul_pos hH hP0
      omega
  constructor
  · refine Classical.byContradiction (fun hq => ?_)
    have := Int.mul_le_mul_of_nonneg_left (show b * MI / P ≤ -Hh - 1 by omega) (Int.le_of_lt hP0)
    rw [Int.mul_sub, Int.mul_neg, Int.mul_one, Int.mul_comm P Hh] at this
    omega
  · refine Classical.byContradiction (fun hq => ?_)
    have := Int.mul_le_mul_of_nonneg_left (show Hh ≤ b * MI / P by omega) (Int.le_of_lt hP0)
    rw [Int.mul_comm P Hh] at this
    omega

theorem sn_special (X j D r2 H : Nat) (hX : X = H * j) (hj : 0 < j) (hr2 : r2 < D)
    (hXr : X % D = r2) (hmod : (H + 1) % D = 0) : D - r2 ≤ j := by
  have h1 : (X + j) % D = 0 := by
    rw [hX, show H * j + j = (H + 1) * j by rw [Nat.add_mul, Nat.one_mul], Nat.mul_mod, hmod,
      Nat.zero_mul, Nat.zero_mod]
  have h2 : (r2 + j) % D = 0 := by rw [← hXr, Nat.mod_add_mod]; exact h1
  rcases Nat.lt_or_ge j (D - r2) with hlt | hge
  · rw [Nat.mod_eq_of_lt (by omega)] at h2
    omega
  · exact hge

/-! ## Signed wrapping helpers -/

theorem sm_wrap_id {t : IntTy} (h : t.signed = true) (z : Int)
    (h1 : -(2 : Int) ^ (t.bits - 1) ≤ z) (h2 : z < (2 : Int) ^ (t.bits - 1)) : wrapInt t z = z :=
  wrapInt_of_inRange t z (by simp only [IntTy.min, IntTy.max, h, if_true]; omega)

theorem sm_wrap_add {t : IntTy} (h : t.signed = true) (w : Int)
    (h1 : -(2 : Int) ^ (t.bits - 1) ≤ w) (h2 : w < (2 : Int) ^ (t.bits - 1)) :
    wrapInt t (w + (2 : Int) ^ t.bits) = w := by
  have hc : ((2 ^ t.bits : Nat) : Int) = (2 : Int) ^ t.bits := by norm_cast
  rw [wrapInt_congr t (b := w) (by
    rw [hc, show w + (2 : Int) ^ t.bits = w + (2 : Int) ^ t.bits * 1 by rw [Int.mul_one],
      Int.add_mul_emod_self_left])]
  exact sm_wrap_id h w h1 h2

/-! ## Model-level division -/

theorem sm_int8' (f : SameTypeDivrem) (render : Bits → Jl String) (x : JInt .i8) :
    (bitsCallees f render).int8 x = ⟨.i8, x⟩ := Eq.trans rfl rfl

theorem sm_mulWrap' (f : SameTypeDivrem) (render : Bits → Jl String) {s u : IntTy}
    (x : JInt s) (y : JInt u) :
    (bitsCallees f render).mulWrap ⟨s, x⟩ ⟨u, y⟩ = .ok ⟨s.promote u, I.binop I.mulWrap x y⟩ :=
  Eq.trans rfl rfl

theorem sm_eqValue_bind (f : SameTypeDivrem) (render : Bits → Jl String) {s u : IntTy}
    (x : JInt s) (y : JInt u) {B : Type} (k : (bitsCallees f render).Condition → Except JlError B) :
    (bind ((bitsCallees f render).eqValue ⟨s, x⟩ ⟨u, y⟩) k : Except JlError B) = k (I.eq x y) :=
  Eq.trans rfl rfl

theorem sm_shr' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t)
    (n : JInt .u8) : (bitsCallees f render).shr ⟨t, x⟩ n = .ok ⟨t, I.shrU x n⟩ := Eq.trans rfl rfl

theorem sm_addLeftSign' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy}
    (b : Bool) (x : JInt t) :
    (bitsCallees f render).addLeftSign b ⟨t, x⟩ =
      .ok ⟨t, I.op_Integer t I.add (I.rem_Bool_Type t) (I.remT t) b x⟩ := Eq.trans rfl rfl

def smAm {t : IntTy} (d : JInt t) (q2 : Nat) : JInt .i8 :=
  smAddmul (I.lt (I.lit .i64 0) d) (I.lt (smM d q2) (I.lit .i64 0)) (I.lt d (I.lit .i64 0))
    (I.lt (I.lit .i64 0) (smM d q2))

def smX {t : IntTy} (d a : JInt t) (q2 : Nat) : JInt t :=
  I.addWrap (mulHi a (smM d q2)) (I.remT t (I.binop I.mulWrap a (smAm d q2)))

theorem sm_div_shape (render : Bits → Jl String) {t : IntTy} (h : t.signed = true)
    (d a : JInt t) (q2 p : Nat) :
    divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits render) a (smInv h d q2 p) =
      .ok (I.ifelse (I.eq (I.abs d) (I.lit .i64 1)) (⟨t, I.mulSame a d⟩ : Bits)
        ⟨t, I.remT t (I.op_Integer t I.add (I.rem_Bool_Type t) (I.remT t)
          (I.signbit (smX d a q2)) (I.shrU (smX d a q2) (I.lit .u8 ((p - t.bits : Nat) : Int))))⟩) := by
  unfold divSignedInverse smInv smX smAm
  simp only [um_mulHi', um_pack', sm_int8', sm_mulWrap', um_remType', um_addWrap, sm_abs',
    sm_eqValue_bind, um_int', um_mul, sm_signbit_bind, sm_shr', sm_addLeftSign', um_ifelse',
    um_bind_ok']

theorem sm_prod_val {t : IntTy} (a : JInt t) (am : JInt .i8) :
    (I.remT t (I.binop I.mulWrap a am)).val = wrapInt t (a.val * am.val) := by
  have hle : t.bits ≤ (t.promote .i8).bits := by cases t <;> decide
  rw [remT_val, binop_eq, mulWrapWraps_proven, remT_val, remT_val, wrapInt_narrow hle,
    ← wrapInt_mul_left t, wrapInt_narrow hle, wrapInt_mul_left, ← wrapInt_mul_right t,
    wrapInt_narrow hle, wrapInt_mul_right]

theorem sm_lit0 : (I.lit .i64 0).val = 0 := um_i64_small (by omega) (by omega)

theorem sm_xval {t : IntTy} (h : t.signed = true) (a d : JInt t) (hd : d.val ≠ 0) (q2 : Nat)
    (hM : q2 + 1 < 2 ^ t.bits) :
    (smX d a q2).val = (if d.val < 0 then -a.val else a.val) * ((q2 + 1 : Nat) : Int) /
      (2 : Int) ^ t.bits := by
  have hb := um_bits_le t
  have hu := sm_toU_signed t
  have hbits := sm_toU_bits t
  have hPH : (2 : Int) ^ t.bits = 2 * (2 : Int) ^ (t.bits - 1) := by
    have := congrArg (fun n : Nat => (n : Int)) (sn_pow_half t.bits (by omega))
    push_cast at this
    exact this
  have hH : 0 < (2 : Int) ^ (t.bits - 1) := Int.pow_pos (by decide)
  have hMc : ((q2 + 1 : Nat) : Int) < (2 : Int) ^ t.bits := um_natW hM
  have hMe : ((q2 + 1 : Nat) : Int) = (q2 : Int) + 1 := by push_cast; rfl
  have hax := a.property
  simp only [IntTy.min, IntTy.max, h, if_true] at hax
  have hrem : (I.remT t (I.addWrap (I.lit t.toUnsigned (q2 : Int)) (I.lit t.toUnsigned 1))).val =
      wrapInt t ((q2 + 1 : Nat) : Int) := by
    rw [remT_val, um_addWrap_lit, um_lit_val hu (by omega) (by rw [hbits]; omega), hMe]
  have hm : (smM d q2).val =
      wrapInt t (if d.val < 0 then -(wrapInt t ((q2 + 1 : Nat) : Int))
        else wrapInt t ((q2 + 1 : Nat) : Int)) := by
    unfold smM
    rw [flipsign_val h h, hrem]
  have hX : (smX d a q2).val = wrapInt t (a.val * (smM d q2).val / (2 : Int) ^ t.bits +
      a.val * (smAm d q2).val) := by
    unfold smX
    rw [addWrapWraps_proven, mulHi_val, sm_prod_val, wrapInt_add_right]
  have hl1 : I.lt (I.lit .i64 0) d = decide (0 < d.val) := by rw [lt_eq, sm_lit0]
  have hl2 : I.lt (smM d q2) (I.lit .i64 0) = decide ((smM d q2).val < 0) := by rw [lt_eq, sm_lit0]
  have hl3 : I.lt d (I.lit .i64 0) = decide (d.val < 0) := by rw [lt_eq, sm_lit0]
  have hl4 : I.lt (I.lit .i64 0) (smM d q2) = decide (0 < (smM d q2).val) := by rw [lt_eq, sm_lit0]
  have hPne : (2 : Int) ^ t.bits ≠ 0 := by omega
  generalize hMI : ((q2 + 1 : Nat) : Int) = MI at hm hMc hrem ⊢
  have hMI1 : 1 ≤ MI := by rw [← hMI]; omega
  rw [hX]
  rcases Int.lt_or_le d.val 0 with hdn | hdp
  · -- negative divisor
    rw [if_pos hdn] at hm ⊢
    have hb1 : -(2 : Int) ^ (t.bits - 1) ≤ -a.val := by omega
    have hb2 : -a.val ≤ (2 : Int) ^ (t.bits - 1) := by omega
    have hr := sm_range (-a.val) MI ((2 : Int) ^ (t.bits - 1)) ((2 : Int) ^ t.bits) hPH hH hb1 hb2
      (by omega) hMc
    rcases Int.lt_or_le MI ((2 : Int) ^ (t.bits - 1)) with hlo | hhi
    · rw [sm_wrap_id h MI (by omega) hlo, sm_wrap_id h (-MI) (by omega) (by omega)] at hm
      have hA : (smAm d q2).val = 0 := by
        unfold smAm smAddmul smNeg
        rw [hl1, hl2, hl3, hl4, hm, decide_eq_false (show ¬ (0 < d.val) by omega),
          decide_eq_true hdn, decide_eq_false (show ¬ (0 < -MI) by omega)]
        rfl
      rw [hm, hA, Int.mul_zero, Int.add_zero, Int.mul_neg, ← Int.neg_mul]
      exact sm_wrap_id h _ hr.1 hr.2
    · rcases Int.lt_or_le ((2 : Int) ^ (t.bits - 1)) MI with hgt | heq
      · have hw : wrapInt t MI = MI - (2 : Int) ^ t.bits := by
          have := sm_wrap_add h (MI - (2 : Int) ^ t.bits) (by omega) (by omega)
          rw [show MI - (2 : Int) ^ t.bits + (2 : Int) ^ t.bits = MI by omega] at this
          exact this
        rw [hw, sm_wrap_id h (-(MI - (2 : Int) ^ t.bits)) (by omega) (by omega)] at hm
        have hA : (smAm d q2).val = -1 := by
          unfold smAm smAddmul smNeg
          rw [hl1, hl2, hl3, hl4, hm, decide_eq_false (show ¬ (0 < d.val) by omega),
            decide_eq_true hdn, decide_eq_true (show 0 < -(MI - (2 : Int) ^ t.bits) by omega)]
          rfl
        rw [hm, hA]
        have e : a.val * -(MI - (2 : Int) ^ t.bits) = -a.val * MI + (2 : Int) ^ t.bits * a.val := by
          rw [Int.neg_sub, Int.mul_sub, Int.neg_mul, Int.mul_comm a.val ((2 : Int) ^ t.bits)]
          omega
        rw [e, Int.add_mul_ediv_left _ _ hPne, show -a.val * MI / (2 : Int) ^ t.bits + a.val +
          a.val * -1 = -a.val * MI / (2 : Int) ^ t.bits by omega]
        exact sm_wrap_id h _ hr.1 hr.2
      · have hMeq : MI = (2 : Int) ^ (t.bits - 1) := by omega
        have hw : wrapInt t MI = MI - (2 : Int) ^ t.bits := by
          have := sm_wrap_add h (MI - (2 : Int) ^ t.bits) (by omega) (by omega)
          rw [show MI - (2 : Int) ^ t.bits + (2 : Int) ^ t.bits = MI by omega] at this
          exact this
        have hw2 : wrapInt t (-(MI - (2 : Int) ^ t.bits)) = -MI := by
          have := sm_wrap_add h (-MI) (by omega) (by omega)
          rw [show -MI + (2 : Int) ^ t.bits = -(MI - (2 : Int) ^ t.bits) by omega] at this
          exact this
        rw [hw, hw2] at hm
        have hA : (smAm d q2).val = 0 := by
          unfold smAm smAddmul smNeg
          rw [hl1, hl2, hl3, hl4, hm, decide_eq_false (show ¬ (0 < d.val) by omega),
            decide_eq_true hdn, decide_eq_false (show ¬ (0 < -MI) by omega)]
          rfl
        rw [hm, hA, Int.mul_zero, Int.add_zero, Int.mul_neg, ← Int.neg_mul]
        exact sm_wrap_id h _ hr.1 hr.2
  · -- positive divisor
    have hdp' : 0 < d.val := by omega
    rw [if_neg (show ¬ d.val < 0 by omega)] at hm ⊢
    have hr := sm_range a.val MI ((2 : Int) ^ (t.bits - 1)) ((2 : Int) ^ t.bits) hPH hH
      (by omega) (by omega) (by omega) hMc
    rcases Int.lt_or_le MI ((2 : Int) ^ (t.bits - 1)) with hlo | hhi
    · rw [sm_wrap_id h MI (by omega) hlo, sm_wrap_id h MI (by omega) hlo] at hm
      have hA : (smAm d q2).val = 0 := by
        unfold smAm smAddmul smNeg
        rw [hl1, hl2, hl3, hl4, hm, decide_eq_true hdp', decide_eq_false (show ¬ (MI < 0) by omega),
          decide_eq_false (show ¬ (d.val < 0) by omega)]
        rfl
      rw [hm, hA, Int.mul_zero, Int.add_zero]
      exact sm_wrap_id h _ hr.1 hr.2
    · have hw : wrapInt t MI = MI - (2 : Int) ^ t.bits := by
        have := sm_wrap_add h (MI - (2 : Int) ^ t.bits) (by omega) (by omega)
        rw [show MI - (2 : Int) ^ t.bits + (2 : Int) ^ t.bits = MI by omega] at this
        exact this
      rw [hw, sm_wrap_id h (MI - (2 : Int) ^ t.bits) (by omega) (by omega)] at hm
      have hA : (smAm d q2).val = 1 := by
        unfold smAm smAddmul
        rw [hl1, hl2, hm, decide_eq_true hdp',
          decide_eq_true (show MI - (2 : Int) ^ t.bits < 0 by omega)]
        rfl
      rw [hm, hA]
      have e : a.val * (MI - (2 : Int) ^ t.bits) = a.val * MI + (2 : Int) ^ t.bits * -a.val := by
        rw [Int.mul_sub, Int.mul_neg, Int.mul_comm a.val ((2 : Int) ^ t.bits)]
        omega
      rw [e, Int.add_mul_ediv_left _ _ hPne, show a.val * MI / (2 : Int) ^ t.bits + -a.val +
        a.val * 1 = a.val * MI / (2 : Int) ^ t.bits by omega]
      exact sm_wrap_id h _ hr.1 hr.2

theorem sm_cond {t : IntTy} (h : t.signed = true) (d : JInt t) :
    I.eq (I.abs d) (I.lit .i64 1) = decide (smD d = 1) := by
  have hb := um_bits_le t
  have hH : 0 < (2 : Int) ^ (t.bits - 1) := Int.pow_pos (by decide)
  have h1 : (I.lit .i64 1).val = 1 := um_i64_small (by omega) (by omega)
  have hX : 128 ≤ 2 ^ (t.bits - 1) :=
    Nat.le_trans (by decide : 128 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by decide) (by omega))
  have hXc : ((2 ^ (t.bits - 1) : Nat) : Int) = (2 : Int) ^ (t.bits - 1) := by norm_cast
  have hmin : t.min = -(2 : Int) ^ (t.bits - 1) := by unfold IntTy.min; rw [if_pos h]
  rw [eq_eq, h1, abs_val]
  unfold smD
  by_cases hc : d.val = t.min
  · rw [if_pos ⟨h, hc⟩, decide_eq_decide, hc, hmin]
    constructor <;> intro <;> omega
  · rw [if_neg (fun hh => hc hh.2), decide_eq_decide]
    constructor <;> intro <;> omega

theorem sm_div_one (render : Bits → Jl String) {t : IntTy} (h : t.signed = true) (d : JInt t)
    (hD : smD d = 1) (q2 p : Nat) (a : JInt t) :
    divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits render) a (smInv h d q2 p) =
      .ok ⟨t, I.lit t (a.val.tdiv d.val)⟩ := by
  rw [sm_div_shape, sm_cond h, decide_eq_true hD, um_ifelse_true]
  apply um_ok_bits_eq
  rw [mulSame_val, lit_val]
  unfold smD at hD
  rcases (show d.val = 1 ∨ d.val = -1 by omega) with e | e <;> rw [e]
  · rw [Int.tdiv_one, Int.mul_one]
  · rw [Int.tdiv_neg, Int.tdiv_one, Int.mul_neg, Int.mul_one]

theorem sm_div_main (render : Bits → Jl String) {t : IntTy} (h : t.signed = true) (d : JInt t)
    (hd : d.val ≠ 0) (hD2 : 2 ≤ smD d) (s : SNat)
    (hv : sValid t.toUnsigned.bits (smD d) (smAnc d) s)
    (hstop : ¬ snCont (smD d) (snNext (smD d) (smAnc d) s)) (a : JInt t) :
    divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits render) a
      (smInv h d (snNext (smD d) (smAnc d) s).q2 (snNext (smD d) (smAnc d) s).p) =
      .ok ⟨t, I.lit t (a.val.tdiv d.val)⟩ := by
  have hb := um_bits_le t
  have hbits := sm_toU_bits t
  have hP := sm_params h d hd
  have hM := sn_M_bound _ _ _ hP hD2 s hv
  have hp2 := sn_valid_p _ _ _ hP s hv
  have hpl := hv.2.1
  have hn := sn_next_inv (smD d) (smAnc d) (by omega) (by have := hP.2.2.2.2.1; omega) s hv.1
  have hcont := mt (sn_cont_iff (smD d) (smAnc d) _ hn).2 hstop
  obtain ⟨-, -, hD1, hDX, hanc2, hancX, hmod, hDanc⟩ := hP
  rw [hbits] at hM hp2 hpl hDX hancX
  have hpn : (snNext (smD d) (smAnc d) s).p = s.p + 1 := rfl
  generalize hr : snNext (smD d) (smAnc d) s = r at hM hcont hn hpn ⊢
  have hcont' : (smD d - r.r2) * smAnc d < 2 ^ r.p := Nat.lt_of_not_le hcont
  obtain ⟨hq1e, hr1, hq2e, hr2⟩ := hn
  have hW := sn_pow_half t.bits (by omega)
  have hH : 0 < (2 : Int) ^ (t.bits - 1) := Int.pow_pos (by decide)
  have hPH : (2 : Int) ^ t.bits = 2 * (2 : Int) ^ (t.bits - 1) := by
    have := congrArg (fun n : Nat => (n : Int)) hW
    push_cast at this
    exact this
  have hXc : ((2 ^ (t.bits - 1) : Nat) : Int) = (2 : Int) ^ (t.bits - 1) := by norm_cast
  have hax := a.property
  simp only [IntTy.min, IntTy.max, h, if_true] at hax
  -- the division value
  have hxv := sm_xval h a d hd r.q2 hM
  generalize hb_def : (if d.val < 0 then -a.val else a.val) = b at hxv
  have hb1 : -(2 : Int) ^ (t.bits - 1) ≤ b := by
    rw [← hb_def]; split <;> omega
  have hb2 : b ≤ (2 : Int) ^ (t.bits - 1) := by
    rw [← hb_def]; split <;> omega
  have hk : r.p - t.bits < 256 := by omega
  have hsh : pattern (I.lit .u8 ((r.p - t.bits : Nat) : Int)) = r.p - t.bits :=
    um_pattern_nat (t := .u8) rfl _ _ (um_lit_nat (t := .u8) rfl (Nat.lt_of_lt_of_le hk (by decide)))
  have hS : (2 : Int) ^ t.bits * (2 : Int) ^ (r.p - t.bits) = ((2 ^ r.p : Nat) : Int) := by
    rw [← Int.pow_add, show t.bits + (r.p - t.bits) = r.p by omega]
    norm_cast
  have hXpos : 0 < ((2 ^ r.p : Nat) : Int) := by
    have : 0 < 2 ^ r.p := Nat.pow_pos (by decide)
    omega
  have hshift : (smX d a r.q2).val / (2 : Int) ^ (r.p - t.bits) =
      b * ((r.q2 + 1 : Nat) : Int) / ((2 ^ r.p : Nat) : Int) := by
    rw [hxv, sm_ediv_ediv _ _ _ (by omega) (Int.pow_pos (by decide)), hS]
  have hsign : (smX d a r.q2).val < 0 ↔ b < 0 := by
    rw [hxv, sm_ediv_neg_iff _ _ (by omega)]
    constructor
    · intro hy
      refine Classical.byContradiction (fun hb => ?_)
      have := Int.mul_nonneg (show 0 ≤ b by omega) (show (0 : Int) ≤ ((r.q2 + 1 : Nat) : Int) by omega)
      omega
    · intro hbn
      have := Int.mul_le_mul_of_nonneg_right (show b ≤ -1 by omega)
        (show (0 : Int) ≤ ((r.q2 + 1 : Nat) : Int) by omega)
      push_cast at this ⊢
      omega
  -- the magic identity
  have hDM : smD d * (r.q2 + 1) = 2 ^ r.p + (smD d - r.r2) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    omega
  have hT0 := Nat.mod_lt (2 ^ (t.bits - 1) + smSg d) (show 0 < smD d by omega)
  have hmagic := sm_magic (smD d) (smAnc d) (2 ^ r.p) (r.q2 + 1) (smD d - r.r2) hD2 hDanc hmod
    hDM (by omega) hcont' b
    (by
      have hge : 2 ^ (t.bits - 1) + smSg d - 1 ≤ smAnc d + smD d - 1 := by
        unfold smAnc; omega
      rw [← hb_def]
      unfold smSg at hge
      split
      · rename_i hdn
        rw [if_pos hdn] at hge
        omega
      · rename_i hdn
        rw [if_neg hdn] at hge
        omega)
    (by
      rw [← hb_def]
      by_cases hdn : d.val < 0
      · rw [if_pos hdn]
        left
        have hsg : smSg d = 1 := by unfold smSg; rw [if_pos hdn]
        have : 2 ^ (t.bits - 1) ≤ smAnc d + smD d - 1 := by
          unfold smAnc; omega
        omega
      · rw [if_neg hdn]
        have hsg : smSg d = 0 := by unfold smSg; rw [if_neg hdn]
        by_cases hlow : 2 ^ (t.bits - 1) ≤ smAnc d + smD d - 1
        · left
          omega
        · by_cases ha : -((smAnc d : Int) + (smD d : Int) - 1) ≤ a.val
          · exact Or.inl ha
          · right
            have hsum : smAnc d + smD d = 2 ^ (t.bits - 1) := by
              unfold smAnc at hlow ⊢; omega
            refine ⟨by omega, ?_⟩
            rw [hsum]
            have hXj : 2 ^ r.p = 2 ^ (t.bits - 1) * 2 ^ (r.p - (t.bits - 1)) := by
              rw [← Nat.pow_add]; congr 1; omega
            have hj : 0 < 2 ^ (r.p - (t.bits - 1)) := Nat.pow_pos (by decide)
            have hXr : 2 ^ r.p % smD d = r.r2 := by
              rw [← hq2e, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr2]
            have hmodH : (2 ^ (t.bits - 1) + 1) % smD d = 0 := by
              rw [← hsum, show smAnc d + smD d + 1 = smAnc d + 1 + smD d by omega,
                Nat.add_mod_right]
              exact hmod
            have hspec := sn_special (2 ^ r.p) (2 ^ (r.p - (t.bits - 1))) (smD d) r.r2
              (2 ^ (t.bits - 1)) hXj hj hr2 hXr hmodH
            rw [hXj]
            exact Nat.mul_le_mul_left _ hspec)
  -- assemble
  rw [sm_div_shape, sm_cond h, decide_eq_false (show ¬ smD d = 1 by omega), um_ifelse_false]
  apply um_ok_bits_eq
  have hrb : (I.rem_Bool_Type t (I.signbit (smX d a r.q2))).val = if b < 0 then 1 else 0 := by
    have hr := remBool_proven t (I.signbit (smX d a r.q2))
    change (I.rem_Bool_Type t (I.signbit (smX d a r.q2))).val = _ at hr
    rw [hr, signed_signbit_val h]
    by_cases hbn : b < 0
    · rw [if_pos hbn, decide_eq_true (hsign.2 hbn)]
      rfl
    · rw [if_neg hbn, decide_eq_false (fun hx => hbn (hsign.1 hx))]
      rfl
  change (I.remT t (I.add (I.rem_Bool_Type t (I.signbit (smX d a r.q2)))
    (I.remT t (I.shrU (smX d a r.q2) (I.lit .u8 ((r.p - t.bits : Nat) : Int)))))).val = _
  rw [remT_val, I.add, add_int_val, hrb, remT_val, shrU_val, hsh, wrapInt_add_right,
    wrapInt_wrapInt, lit_val]
  rw [hshift, Int.add_comm (if b < 0 then (1 : Int) else 0), hmagic]
  -- relate b.tdiv D to a.tdiv d
  congr 1
  rw [← hb_def]
  unfold smD
  by_cases hdn : d.val < 0
  · have e : ((d.val.natAbs : Nat) : Int) = -d.val := by omega
    rw [if_pos hdn, Int.neg_tdiv, e, Int.tdiv_neg, Int.neg_neg]
  · have e : ((d.val.natAbs : Nat) : Int) = d.val := by omega
    rw [if_neg hdn, e]

end SD

section SF

theorem sm_divInverse_view {Ty D E : Type} {V : Ty → Type} {domain : IntegerDomains Ty}
    (o : Callees Ty V D E) {T : Ty} (a : V T) (b : SignedMultiplicativeInverse V domain T) :
    divInverse a (signedView o b) = divSignedInverse o a b := Eq.trans rfl rfl

theorem sm_getDivisor_view {Ty D E : Type} {V : Ty → Type} {domain : IntegerDomains Ty}
    (o : Callees Ty V D E) {T : Ty} (b : SignedMultiplicativeInverse V domain T) :
    (signedView o b).getDivisor (signedView o b).value = .ok (o.pack T b.divisor) :=
  Eq.trans rfl rfl

theorem sm_public_ctor {Ty D E : Type} {V : Ty → Type} (domain : IntegerDomains Ty)
    (o : Callees Ty V D E) {T : Ty} (h : domain.signed T) (x : V T) :
    multiplicativeinverseSigned domain o h x = signedInverseConstructor domain o h x :=
  Eq.trans rfl rfl

theorem sm_iszero' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (x : JInt t) :
    (bitsCallees f render).iszero ⟨t, x⟩ = .ok (I.eq x (I.zero x)) := Eq.trans rfl rfl

theorem sm_eqSign' (f : SameTypeDivrem) (render : Bits → Jl String) (x y : Bool) :
    (bitsCallees f render).eqSign x y = .ok (x == y) := Eq.trans rfl rfl

theorem sm_add' (f : SameTypeDivrem) (render : Bits → Jl String) {t : IntTy} (a b : JInt t) :
    (bitsCallees f render).add ⟨t, a⟩ ⟨t, b⟩ = .ok ⟨t, I.add a b⟩ := by
  change Except.ok (bitsBin I.add ⟨t, a⟩ ⟨t, b⟩) = _
  rw [um_bitsBin_same]

/-- Every nonzero signed divisor builds an inverse whose `div` is the wrapped truncated
quotient, computed through the real constructor loop. -/
theorem signedInverse_div (t : IntTy) (h : t.signed = true) (d : JInt t) (hd : d.val ≠ 0) :
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      signedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          .ok ⟨t, I.lit t (a.val.tdiv d.val)⟩ := by
  obtain ⟨s, hv, hstop, hctor⟩ := sm_ctor (fun x => pure (toString x.2.val)) h d hd
  refine ⟨_, hctor, rfl, fun a => ?_⟩
  have hD1 := (sm_d_bounds h d hd).1
  by_cases hD : smD d = 1
  · exact sm_div_one _ h d hD _ _ a
  · exact sm_div_main _ h d hd (by omega) s hv hstop a

theorem sm_rem_lit {t : IntTy} (a d : JInt t) :
    I.sub a (I.mulSame (I.lit t (a.val.tdiv d.val)) d) = I.lit t (a.val.tmod d.val) := by
  apply jint_eq
  rw [I.sub, sub_int_val, mulSame_val, lit_val, lit_val, wrapInt_mul_left, wrapInt_sub_right]
  congr 1
  have h := Int.tmod_add_mul_tdiv a.val d.val
  have hc := Int.mul_comm d.val (a.val.tdiv d.val)
  omega

theorem sm_fmod_cases {t : IntTy} (a d : JInt t) (hd : d.val ≠ 0) :
    (a.val.tmod d.val = 0 → a.val.fmod d.val = a.val.tmod d.val) ∧
    (a.val.tmod d.val ≠ 0 → (a.val.tmod d.val < 0 ↔ d.val < 0) →
      a.val.fmod d.val = a.val.tmod d.val) ∧
    (a.val.tmod d.val ≠ 0 → ¬ (a.val.tmod d.val < 0 ↔ d.val < 0) →
      a.val.fmod d.val = a.val.tmod d.val + d.val) := by
  have hq := Int.tmod_add_mul_tdiv a.val d.val
  have hcomm := Int.mul_comm d.val (a.val.tdiv d.val)
  have hn := Int.natAbs_tmod a.val d.val
  have hlt : a.val.natAbs % d.val.natAbs < d.val.natAbs := Nat.mod_lt _ (by omega)
  have hdv : d.val ∣ a.val - a.val.tmod d.val := ⟨a.val.tdiv d.val, by omega⟩
  refine ⟨fun h0 => ?_, fun h0 hs => ?_, fun h0 hs => ?_⟩
  · apply fmod_char a.val d.val _ hd hdv
    constructor <;> intro <;> omega
  · apply fmod_char a.val d.val _ hd hdv
    constructor
    · intro hdp
      have : ¬ a.val.tmod d.val < 0 := fun hx => absurd (hs.1 hx) (by omega)
      omega
    · intro hdn
      have := hs.2 hdn
      omega
  · apply fmod_char a.val d.val (a.val.tmod d.val + d.val) hd
      ⟨a.val.tdiv d.val - 1, by rw [Int.mul_sub, Int.mul_one]; omega⟩
    constructor
    · intro hdp
      have : a.val.tmod d.val < 0 := Classical.byContradiction (fun hx =>
        hs ⟨fun hy => absurd hy hx, fun hy => absurd hy (by omega)⟩)
      omega
    · intro hdn
      have : ¬ a.val.tmod d.val < 0 := fun hx => hs ⟨fun _ => hdn, fun _ => hx⟩
      omega

/-- Division, remainder, divrem and modulus of the signed inverse, for every dividend. -/
theorem signedInverse_exact (t : IntTy) (h : t.signed = true) (d : JInt t) (hd : d.val ≠ 0) :
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      signedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          .ok ⟨t, I.lit t (a.val.tdiv d.val)⟩ ∧
        JuliaLean.base.multinverses.rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          .ok ⟨t, I.lit t (a.val.tmod d.val)⟩ ∧
        divremInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          .ok (⟨t, I.lit t (a.val.tdiv d.val)⟩, ⟨t, I.lit t (a.val.tmod d.val)⟩) ∧
        modSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          .ok ⟨t, I.lit t (a.val.fmod d.val)⟩ := by
  obtain ⟨inv, hc, hdv, hdiv⟩ := signedInverse_div t h d hd
  refine ⟨inv, hc, hdv, fun a => ?_⟩
  have hrem : JuliaLean.base.multinverses.rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
      (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inv) =
      .ok ⟨t, I.lit t (a.val.tmod d.val)⟩ := by
    unfold JuliaLean.base.multinverses.rem
    simp only [sm_divInverse_view, hdiv a, um_bind_ok', sm_getDivisor_view, hdv, um_pack',
      um_mul, um_sub, sm_rem_lit]
  refine ⟨hdiv a, hrem, ?_, ?_⟩
  · unfold divremInverse
    simp only [sm_divInverse_view, hdiv a, um_bind_ok', sm_getDivisor_view, hdv, um_pack',
      um_mul, um_sub, sm_rem_lit]
    rfl
  · have hfit := tmod_fits a d
    have htm : (I.lit t (a.val.tmod d.val)).val = a.val.tmod d.val := lit_of_fits hfit
    have hzero : I.zero (I.lit t (a.val.tmod d.val)) = I.lit t 0 := Eq.trans rfl rfl
    have hz0 : (I.lit t 0).val = 0 := lit_of_fits (by
      unfold fits; simp only [IntTy.min, IntTy.max, h, if_true]
      have : (0 : Int) < (2 : Int) ^ (t.bits - 1) := Int.pow_pos (by decide)
      omega)
    have hiz : I.eq (I.lit t (a.val.tmod d.val)) (I.zero (I.lit t (a.val.tmod d.val))) =
        decide (a.val.tmod d.val = 0) := by
      rw [eq_eq, hzero, htm, hz0]
    have hsr : I.signbit (I.lit t (a.val.tmod d.val)) = decide (a.val.tmod d.val < 0) := by
      rw [signed_signbit_val h, htm]
    have hsd : I.signbit d = decide (d.val < 0) := signed_signbit_val h d
    obtain ⟨c0, c1, c2⟩ := sm_fmod_cases a d hd
    unfold modSignedInverse
    rw [hrem]
    simp only [um_bind_ok', sm_iszero', hiz, sm_signbit_bind, um_pack', hdv, sm_eqSign', sm_add',
      um_pure']
    by_cases h0 : a.val.tmod d.val = 0
    · rw [decide_eq_true h0]
      simp only [eq_self_iff_true, ite_true, ↓reduceIte]
      apply um_ok_bits_eq
      rw [lit_val, lit_val, c0 h0, h0]
    · rw [decide_eq_false h0]
      by_cases hs : (a.val.tmod d.val < 0 ↔ d.val < 0)
      · have hb : (I.signbit (I.lit t (a.val.tmod d.val)) == I.signbit d) = true := by
          rw [hsr, hsd]
          by_cases hn : d.val < 0
          · rw [decide_eq_true hn, decide_eq_true (hs.2 hn)]; rfl
          · rw [decide_eq_false hn, decide_eq_false (fun hx => hn (hs.1 hx))]; rfl
        simp only [hb, Bool.false_eq_true, ite_false, eq_self_iff_true, ite_true, ↓reduceIte]
        apply um_ok_bits_eq
        rw [lit_val, lit_val, c1 h0 hs]
      · have hb : (I.signbit (I.lit t (a.val.tmod d.val)) == I.signbit d) = false := by
          rw [hsr, hsd]
          by_cases hn : d.val < 0
          · have : ¬ a.val.tmod d.val < 0 := fun hx => hs ⟨fun _ => hn, fun _ => hx⟩
            rw [decide_eq_true hn, decide_eq_false this]; rfl
          · have : a.val.tmod d.val < 0 := by
              refine Classical.byContradiction (fun hx => ?_)
              exact hs ⟨fun hy => absurd hy hx, fun hy => absurd hy hn⟩
            rw [decide_eq_false hn, decide_eq_true this]; rfl
        simp only [hb, Bool.false_eq_true, ite_false, eq_self_iff_true, ite_true, ↓reduceIte]
        apply um_ok_bits_eq
        rw [I.add, add_int_val, htm, lit_val, c2 h0 hs]

theorem signedInverseRemainderAndModulus (t : IntTy) (h : t.signed = true) (d : JInt t)
    (hd : d.val ≠ 0) :
    ∃ inverse : SignedMultiplicativeInverse JInt bitDomains t,
      signedInverseConstructor bitDomains (bitsCallees JuliaLean.base.intfuncs.divremBits)
        h d = some (.ok inverse) ∧
      inverse.divisor = d ∧
      ∀ a : JInt t,
        JuliaLean.base.multinverses.rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
          (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inverse) =
          (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)) ∧
        modSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inverse =
          (JuliaLean.base.div.modBitInteger a d).map (fun m => (⟨t, m⟩ : Bits)) := by
  obtain ⟨inv, hc, hdv, hall⟩ := signedInverse_exact t h d hd
  refine ⟨inv, hc, hdv, fun a => ⟨?_, ?_⟩⟩
  · rw [(hall a).2.1, remSame_eq, if_neg hd]
    rfl
  · rw [(hall a).2.2.2, JuliaLean.Proofs.base.div.modBitInteger_eq, if_neg hd]
    rfl

theorem inverseRemainderAndModulus_proven : InverseRemainderAndModulus :=
  ⟨signedInverseRemainderAndModulus, unsignedInverseRemainderAndModulus⟩

theorem unsignedMultiplicativeInverseCorrect_proven : UnsignedMultiplicativeInverseCorrect :=
  ⟨unsignedInverseDivision_proven, inverseRemainderAndModulus_proven⟩

theorem signedOrdinaryArithmetic_proven : SignedOrdinaryArithmetic := by
  intro t h d hd
  obtain ⟨inv, hc, hdv, hall⟩ := signedInverse_exact t h d hd
  refine ⟨inv, hc, hdv, fun a ha => ?_⟩
  have htmin : (JInt.typemin t).val = t.min := by cases t <;> decide
  have hq : (I.lit t (a.val.tdiv d.val)).val = a.val.tdiv d.val :=
    lit_of_fits (tdiv_fits a d hd (by
      rintro ⟨-, h1, h2⟩
      rcases ha with ha | ha
      · exact ha (by rw [htmin]; exact h1)
      · exact ha h2))
  have hr : (I.lit t (a.val.tmod d.val)).val = a.val.tmod d.val := lit_of_fits (tmod_fits a d)
  have hm : (I.lit t (a.val.fmod d.val)).val = a.val.fmod d.val := lit_of_fits (fmod_fits a d hd)
  have hqr := Int.tmod_add_mul_tdiv a.val d.val
  have hcomm := Int.mul_comm d.val (a.val.tdiv d.val)
  have hn := Int.natAbs_tmod a.val d.val
  have hlt : a.val.natAbs % d.val.natAbs < d.val.natAbs := Nat.mod_lt _ (by omega)
  have hb : (0 ≤ a.val → 0 ≤ a.val.tmod d.val) ∧ (a.val < 0 → a.val.tmod d.val ≤ 0) :=
    ⟨fun h0 => ((tmod_between a.val d.val).1 h0).1, fun h0 => ((tmod_between a.val d.val).2 h0).2⟩
  have hf := fmod_bounds a.val d.val hd
  refine ⟨I.lit t (a.val.tdiv d.val), I.lit t (a.val.tmod d.val), I.lit t (a.val.fmod d.val),
    I.lit t (a.val.tdiv d.val), I.lit t (a.val.tmod d.val),
    (hall a).1, (hall a).2.1, (hall a).2.2.2, (hall a).2.2.1, hq, hr, hm, hq, hr, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hq, hr]
    omega
  · rw [hr]
    omega
  · rw [hr]
    by_cases h0 : a.val.tmod d.val = 0
    · exact Or.inl h0
    · right
      rcases Int.lt_or_le a.val 0 with ha0 | ha0
      · have := hb.2 ha0
        constructor <;> intro <;> omega
      · have := hb.1 ha0
        constructor <;> intro <;> omega
  · rw [hm]
    rcases Int.lt_or_lt_of_ne hd with hd0 | hd0
    · have := hf.2 hd0
      omega
    · have := hf.1 hd0
      omega
  · rw [hm]
    by_cases h0 : a.val.fmod d.val = 0
    · exact Or.inl h0
    · right
      rcases Int.lt_or_lt_of_ne hd with hd0 | hd0
      · have := hf.2 hd0
        constructor <;> intro <;> omega
      · have := hf.1 hd0
        constructor <;> intro <;> omega

end SF
end JuliaLean.Proofs.base.multinverses


namespace JuliaLean.Proofs.base.multinverses

theorem round3SignedInverseDivision_proven : SignedInverseDivision := by
  intro t h d hd
  obtain ⟨inv, hc, hdv, hall⟩ := signedInverse_exact t h d hd
  have htmin : (JInt.typemin t).val = t.min := by cases t <;> decide
  refine ⟨inv, hc, hdv, ?_⟩
  intro a hguard
  have hgood : ¬ (d.val = 0 ∨ t.signed = true ∧ a.val = t.min ∧ d.val = -1) := by
    rintro (hz | ⟨_, ha, hd1⟩)
    · exact hd hz
    · rcases hguard with ha' | hd'
      · apply ha'
        rw [htmin]
        exact ha
      · exact hd' hd1
  simpa [JuliaLean.Proofs.base.int.divSame_eq, hgood, Except.map] using (hall a).1

end JuliaLean.Proofs.base.multinverses

namespace JuliaLean.Proofs.base.multinverses

theorem round3InverseDivremMatchesBase_proven : InverseDivremMatchesBase := by
  constructor
  · intro t h d hd
    obtain ⟨inv, hc, hdv, hall⟩ := signedInverse_exact t h d hd
    have htmin : (JInt.typemin t).val = t.min := by cases t <;> decide
    refine ⟨inv, hc, ?_⟩
    intro a hguard
    have hgood : ¬ (d.val = 0 ∨ t.signed = true ∧ a.val = t.min ∧ d.val = -1) := by
      rintro (hz | ⟨_, ha, hd1⟩)
      · exact hd hz
      · rcases hguard with ha' | hd'
        · apply ha'
          rw [htmin]
          exact ha
        · exact hd' hd1
    have hoverflow : ¬ (t.signed = true ∧ a.val = t.min ∧ d.val = -1) := by
      intro ho
      exact hgood (Or.inr ho)
    simpa [JuliaLean.base.intfuncs.divremBits,
      JuliaLean.Proofs.base.int.divSame_eq,
      JuliaLean.Proofs.base.int.remSame_eq,
      hd, hoverflow, Bind.bind, Except.bind, Functor.map, Except.map,
      Pure.pure, Except.pure] using (hall a).2.2.1
  · intro t h d hd
    obtain ⟨inv, hc, hdv, hall⟩ := unsignedInverse_exact t h d hd
    refine ⟨inv, hc, ?_⟩
    intro a
    have hdivrem := (hall a).2.2
    rw [um_tdiv_toNat h a d, um_tmod_toNat h a d] at hdivrem
    simpa [JuliaLean.base.intfuncs.divremBits,
      JuliaLean.Proofs.base.int.divSame_eq,
      JuliaLean.Proofs.base.int.remSame_eq,
      h, hd, Bind.bind, Except.bind, Functor.map, Except.map,
      Pure.pure, Except.pure] using hdivrem

end JuliaLean.Proofs.base.multinverses

namespace JuliaLean.Proofs.base.multinverses
open JuliaLean JuliaLean.base.multinverses JuliaLean.Registry
open JuliaLean.Proofs.base.int

theorem round3SignedPublicAPI_proven : SignedPublicAPIBehavior := by
  intro t h d hd
  obtain ⟨inv, hc, hdv, hall⟩ := signedInverse_exact t h d hd
  have htmin : (JInt.typemin t).val = t.min := by cases t <;> decide
  have hdiv (a : JInt t) (hguard : a.val ≠ (JInt.typemin t).val ∨ d.val ≠ -1) :
      divSignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inv =
        (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits)) := by
    have hgood : ¬ (d.val = 0 ∨ t.signed = true ∧ a.val = t.min ∧ d.val = -1) := by
      rintro (hz | ⟨_, ha, hd1⟩)
      · exact hd hz
      · rcases hguard with ha' | hd'
        · apply ha'
          rw [htmin]
          exact ha
        · exact hd' hd1
    simpa [JuliaLean.Proofs.base.int.divSame_eq, hgood, Except.map] using (hall a).1
  have hrem (a : JInt t) :
      rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
        (signedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inv) =
        (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)) := by
    rw [(hall a).2.1, JuliaLean.Proofs.base.int.remSame_eq, if_neg hd]
    rfl
  refine ⟨⟨inv, hc, hdv, fun a => ⟨hdiv a, hrem a⟩⟩,
    ⟨inv, hc, hdv, fun a => ⟨hdiv a, hrem a⟩⟩⟩

theorem round3UnsignedPublicAPI_proven : UnsignedPublicAPIBehavior := by
  intro t h d hd
  obtain ⟨inv, hc, hdv, hall⟩ := unsignedInverse_exact t h d hd
  have hdiv (a : JInt t) :
      divUnsignedInverse (bitsCallees JuliaLean.base.intfuncs.divremBits) a inv =
        (JuliaLean.base.int.divSame a d).map (fun q => (⟨t, q⟩ : Bits)) := by
    rw [(hall a).1, JuliaLean.Proofs.base.int.divSame_eq,
      if_neg (by rw [h]; simp only [Bool.false_eq_true, false_and, or_false]; exact hd)]
    rw [← um_tdiv_toNat h a d]
    rfl
  have hrem (a : JInt t) :
      rem (bitsCallees JuliaLean.base.intfuncs.divremBits) a
        (unsignedView (bitsCallees JuliaLean.base.intfuncs.divremBits) inv) =
        (JuliaLean.base.int.remSame a d).map (fun r => (⟨t, r⟩ : Bits)) := by
    rw [(hall a).2.1, JuliaLean.Proofs.base.int.remSame_eq, if_neg hd,
      ← um_tmod_toNat h a d]
    rfl
  refine ⟨⟨inv, hc, hdv, fun a => ⟨hdiv a, hrem a⟩⟩,
    ⟨inv, hc, hdv, fun a => ⟨hdiv a, hrem a⟩⟩⟩

theorem round3MultiplicativeInverseDispatchPreservesDivisor_proven :
    MultiplicativeInverseDispatchPreservesDivisor := by
  constructor
  · intro t h d hd
    obtain ⟨inv, hc, hdv, _⟩ := signedInverse_exact t h d hd
    change (signedInverseConstructor bitDomains
      (bitsCallees JuliaLean.base.intfuncs.divremBits) h d).map
      (Except.map (fun inverse => inverse.divisor)) = some (.ok d)
    rw [hc]
    simp [Functor.map, Except.map, hdv]
  · intro t h d hd
    obtain ⟨inv, hc, hdv, _⟩ := unsignedInverse_exact t h d hd
    change (unsignedInverseConstructor bitDomains
      (bitsCallees JuliaLean.base.intfuncs.divremBits) h d).map
      (Except.map (fun inverse => inverse.divisor)) = some (.ok d)
    rw [hc]
    simp [Functor.map, Except.map, hdv]

theorem round3MultiplicativeInversePublicAPI_proven : MultiplicativeInversePublicAPI :=
  ⟨zeroDivisorsRejected_proven, round3SignedPublicAPI_proven,
    round3UnsignedPublicAPI_proven, unsignedTypeSpecification_proven⟩

theorem round3SignedInverseDivisionAndDivrem_proven : SignedInverseDivisionAndDivremRound3 :=
  ⟨round3SignedInverseDivision_proven, round3InverseDivremMatchesBase_proven⟩

/-- `div(typemin(Int), multiplicativeinverse(-1))` returns typemin instead of throwing. -/
theorem round4SignedInverseDivisionAndDivrem_refuted :
    ¬ SignedInverseDivisionAndDivrem := by
  intro h
  let d : JInt .i64 := JInt.lit .i64 (-1)
  let a : JInt .i64 := JuliaLean.base.int.typemin .i64
  have hd : d.val ≠ 0 := by decide
  obtain ⟨inverse, hpublicCtor, _, hdiv⟩ := h.1 .i64 rfl d hd
  obtain ⟨actual, hactualCtor, _, hactualDiv⟩ := signedInverse_div .i64 rfl d hd
  have hconstructor : signedInverseConstructor bitDomains
      (bitsCallees JuliaLean.base.intfuncs.divremBits) (T := .i64) rfl d =
        some (Except.ok inverse) := by
    simpa [multiplicativeinverseSigned, signedMultiplicativeInverse] using hpublicCtor
  have hsome := hconstructor.symm.trans hactualCtor
  have hinverse : inverse = actual := by
    have hresult : Except.ok inverse = Except.ok actual := Option.some.inj hsome
    exact Except.ok.inj hresult
  have hdval : d.val = -1 := by
    change JuliaLean.wrapInt .i64 (-1) = -1
    exact JuliaLean.wrapInt_of_inRange .i64 (-1) (by decide)
  have haval : a.val = IntTy.i64.min := by
    change JuliaLean.wrapInt .i64 IntTy.i64.min = IntTy.i64.min
    exact JuliaLean.wrapInt_of_inRange .i64 _ (by decide)
  have hbase : JuliaLean.base.int.divSame a d = .error .divideError := by
    change JuliaLean.base.int.checked_sdiv_int a d = .error .divideError
    rw [JuliaLean.Proofs.base.int.checked_sdiv_int_eq rfl]
    simp [hdval, haval]
  have hclaim := (hdiv a).1
  rw [hinverse, hactualDiv a, hbase] at hclaim
  change Except.ok _ = Except.error JuliaLean.JlError.divideError at hclaim
  cases hclaim

theorem round3MultiplicativeInverseSourceBehavior_proven :
    MultiplicativeInverseSourceBehavior :=
  ⟨round3MultiplicativeInversePublicAPI_proven, round3SignedInverseDivision_proven,
    unsignedInverseDivision_proven, inverseRemainderAndModulus_proven,
    round3InverseDivremMatchesBase_proven,
    round3MultiplicativeInverseDispatchPreservesDivisor_proven⟩

end JuliaLean.Proofs.base.multinverses
namespace JuliaLean.Proofs.base.multinverses
open JuliaLean JuliaLean.base.multinverses JuliaLean.Registry
def entries : List Entry := [
  { id := "reinterpretarrays-umi-div", juliaFile := "base/multinverses.jl"
    juliaFns := ["UnsignedMultiplicativeInverse{T}(d)", "div(::T, ::UnsignedMultiplicativeInverse{T})",
      "rem(::T, ::MultiplicativeInverse{T})", "mod(::T, ::SignedMultiplicativeInverse{T})",
      "mod(::T, ::UnsignedMultiplicativeInverse{T})"]
    statement := "Every nonzero unsigned BitInteger divisor produces an inverse retaining its divisor and matching installed Base division for every dividend. For both signednesses, inverse remainder and modulus match installed Base methods."
    source := "base/multinverses.jl:19-45,98-149,156-161; base/div.jl rem contract; base/int.jl mod contract"
    status := .proven, prop := ``UnsignedMultiplicativeInverseCorrect,
    thm := some ``unsignedMultiplicativeInverseCorrect_proven },
  { id := "reinterpretarrays-smi-div", juliaFile := "base/multinverses.jl"
    juliaFns := ["SignedMultiplicativeInverse{T}(d)", "div(::T, ::SignedMultiplicativeInverse{T})"]
    statement := "Every nonzero signed BitInteger divisor produces an inverse retaining its divisor. For dividends other than typemin(T) divided by -1, inverse division agrees with checked Base div."
    source := "base/multinverses.jl:19-45,53-88,137-141; base/div.jl div contract"
    status := .proven, prop := ``SignedInverseDivision,
    thm := some ``round3SignedInverseDivision_proven },
  { id := "reinterpretarrays-smi-rem-mod", juliaFile := "base/multinverses.jl"
    juliaFns := ["SignedMultiplicativeInverse{T}(d)", "UnsignedMultiplicativeInverse{T}(d)",
      "rem(::T, ::MultiplicativeInverse{T})", "mod(::T, ::SignedMultiplicativeInverse{T})",
      "mod(::T, ::UnsignedMultiplicativeInverse{T})"]
    statement := "Every nonzero signed or unsigned BitInteger divisor produces an inverse retaining that divisor, and inverse remainder and modulus equal the installed ordinary Base methods for every dividend."
    source := "base/multinverses.jl:148-161; base/div.jl rem contract; base/int.jl mod contract"
    status := .proven, prop := ``InverseRemainderAndModulus,
    thm := some ``inverseRemainderAndModulus_proven },
  { id := "reinterpretarrays-smi-div-typemin", juliaFile := "base/multinverses.jl"
    juliaFns := ["SignedMultiplicativeInverse{T}(d)", "UnsignedMultiplicativeInverse{T}(d)",
      "multiplicativeinverse(x::Signed)", "div(::T, ::SignedMultiplicativeInverse{T})",
      "divrem(::T, ::MultiplicativeInverse{T})"]
    statement := "For every signed BitInteger type and every nonzero divisor, the public signed inverse constructor succeeds and retains the divisor. For every dividend, inverse div and divrem return the same values or errors as Base div and divrem with the plain divisor, including typemin(T) divided by -1. Unsigned inverse divrem agrees with Base for every dividend and nonzero divisor."
    source := "base/div.jl:5-14,255-273; base/multinverses.jl:53-90,98-135,137-154,163-164"
    status := .refuted, prop := ``SignedInverseDivisionAndDivrem,
    thm := some ``round4SignedInverseDivisionAndDivrem_refuted,
    issue := "none found (queries: SignedMultiplicativeInverse, multiplicativeinverse, MultiplicativeInverses, multiplicative inverse typemin)" },
  { id := "intfuncscov-multiplicative-inverse-source", juliaFile := "base/multinverses.jl"
    juliaFns := ["unsigned", "SignedMultiplicativeInverse", "UnsignedMultiplicativeInverse",
      "div", "rem", "divrem", "mod", "multiplicativeinverse"]
    statement := "For the modeled BitInteger widths, zero divisors make the constructors return an error and nonzero constructors retain their divisor. Signed inverse division and divrem match checked Base results when defined; remainder, modulus and unsigned arithmetic match Base methods, and type conversion and signedness dispatch retain their modeled behavior."
    source := "base/multinverses.jl:8-164; base/div.jl div and divrem contracts; base/int.jl mod contract"
    status := .proven, prop := ``MultiplicativeInverseSourceBehavior,
    thm := some ``round3MultiplicativeInverseSourceBehavior_proven },
  { id := "multinverses-zero-argumenterror", juliaFile := "base/multinverses.jl"
    juliaFns := ["unsigned", "SignedMultiplicativeInverse{T}(d)", "SignedMultiplicativeInverse(x::Signed)",
      "UnsignedMultiplicativeInverse{T}(d)", "UnsignedMultiplicativeInverse(x::Unsigned)",
      "div(::T, ::SignedMultiplicativeInverse{T})", "div(::T, ::UnsignedMultiplicativeInverse{T})",
      "rem(::T, ::MultiplicativeInverse{T})", "multiplicativeinverse(x::Signed)",
      "multiplicativeinverse(x::Unsigned)"]
    statement := "Across the modeled BitInteger widths, inner and public inverse constructors return an error for a zero divisor. Nonzero construction retains the divisor; signed inverse division agrees with checked Base div outside its typemin(T) divided by -1 error case, and signed remainder and unsigned division and remainder agree with Base. Unsigned type dispatch and Union{} MethodError arguments are preserved."
    source := "base/multinverses.jl:8-15,53-54,90,98-99,135,137-149,163-164; base/div.jl div contract"
    status := .proven, prop := ``MultiplicativeInversePublicAPI,
    thm := some ``round3MultiplicativeInversePublicAPI_proven },
  { id := "multinverses-signed-ordinary-arithmetic", juliaFile := "base/multinverses.jl"
    juliaFns := ["multiplicativeinverse(x::Signed)", "SignedMultiplicativeInverse(x::Signed)",
      "SignedMultiplicativeInverse{T}(d)", "div(::T, ::SignedMultiplicativeInverse{T})",
      "rem(::T, ::MultiplicativeInverse{T})", "divrem(::T, ::MultiplicativeInverse{T})",
      "mod(::T, ::SignedMultiplicativeInverse{T})"]
    statement := "Every nonzero signed BitInteger divisor constructs successfully. For every representable quotient, division truncates toward zero; remainder is exact with dividend sign and magnitude below the divisor; modulus has divisor sign and smaller magnitude; divrem gives the exact quotient and remainder."
    source := "base/multinverses.jl:19-45; base/div.jl div/rem/divrem contracts; base/int.jl:292-341 mod contract"
    status := .proven, prop := ``SignedOrdinaryArithmetic,
    thm := some ``signedOrdinaryArithmetic_proven },
  { id := "multinverses-unsigned-arithmetic", juliaFile := "base/multinverses.jl"
    juliaFns := ["multiplicativeinverse(x::Unsigned)", "UnsignedMultiplicativeInverse(x::Unsigned)",
      "UnsignedMultiplicativeInverse{T}(d)", "div(::T, ::UnsignedMultiplicativeInverse{T})",
      "rem(::T, ::MultiplicativeInverse{T})", "divrem(::T, ::MultiplicativeInverse{T})",
      "mod(::T, ::UnsignedMultiplicativeInverse{T})"]
    statement := "Every nonzero unsigned BitInteger divisor constructs successfully. For every dividend, quotient and remainder satisfy exact integer division, divrem returns both, and remainder and modulus lie between zero inclusive and the divisor exclusive."
    source := "base/multinverses.jl:19-45; base/div.jl div/rem/divrem contracts; base/int.jl mod contract"
    status := .proven, prop := ``UnsignedArithmetic, thm := some ``unsignedArithmetic_proven }
]

end JuliaLean.Proofs.base.multinverses
