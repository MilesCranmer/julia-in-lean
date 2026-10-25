import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.IntArith.Division

/-- A fixed-width integer with its runtime type, as used by mixed dispatch. -/
structure Value where
  ty : IntTy
  int : JInt ty
  deriving DecidableEq

/-- Pack a typed primitive without changing its bits. -/
def pack {t : IntTy} (x : JInt t) : Value := ⟨t, x⟩

/-- Julia literal of an explicitly supplied integer type. -/
def lit (t : IntTy) (x : Int) : Value := pack (JInt.lit t x)

/-- `base/int.jl:183-184`: unsigned sign bits are always false. -/
def signbit (x : Value) : Bool := decide (x.int.val < 0)

/-- `base/int.jl:261-262`: same-width reinterpretation, including negative inputs. -/
def unsigned (x : Value) : Value := pack (JInt.rem x.ty.toUnsigned x.int)

/-- `base/int.jl:272-273`: same-width reinterpretation, including large unsigned inputs. -/
def signed (x : Value) : Value := pack (JInt.rem x.ty.toSigned x.int)

/-- `base/int.jl:809-822`, `base/promotion.jl:397-401,423-428`: checked value promotion. -/
def promote (x y : Value) : Jl (Value × Value) := do
  let t := IntTy.promote x.ty y.ty
  let a ← JInt.convert t x.int.val
  let b ← JInt.convert t y.int.val
  pure (pack a, pack b)

/-- `base/int.jl:188-194`, `base/number.jl:255`: promote signed operands,
flip the promoted intrinsic sign, and truncate back to the first operand's type. -/
def flipsign (x y : Value) : Value :=
  if x.ty.signed && y.ty.signed then
    let t := IntTy.promote x.ty y.ty
    let a := JInt.rem t x.int
    let b := JInt.rem t y.int
    pack (JInt.rem x.ty (if b.val < 0 then -a else a))
  else if x.ty.signed then
    let b := -(JInt.lit x.ty (if signbit y then 1 else 0))
    pack (if b.val < 0 then -x.int else x.int)
  else pack (if signbit y then -x.int else x.int)

/-- `base/int.jl:196-200`, `base/number.jl:271`: the sign of signed XOR
is the XOR of sign bits after sign-extending promotion. -/
def copysign (x y : Value) : Value :=
  if x.ty.signed && y.ty.signed then
    let t := IntTy.promote x.ty y.ty
    let a := JInt.rem t x.int
    let b := JInt.rem t y.int
    flipsign x (lit t (if (a.val < 0) ↔ (b.val < 0) then 0 else -1))
  else if x.ty.signed then
    let b := -(JInt.lit x.ty (if signbit y then 1 else 0))
    flipsign x (lit x.ty (if (x.int.val < 0) ↔ (b.val < 0) then 0 else -1))
  else pack (if signbit x != signbit y then -x.int else x.int)

/-- `base/int.jl:233-234`: signed absolute value uses wrapping flipsign. -/
def abs (x : Value) : Value := if x.ty.signed then flipsign x x else x

/-- `base/float.jl:235-236`: unsigned absolute value reinterprets signed abs. -/
def uabs (x : Value) : Value := if x.ty.signed then unsigned (abs x) else abs x

/-- Arithmetic promotion is wrapping, `base/int.jl:1092-1100`; unlike
`promote`, mixed arithmetic never exact-converts negative signed operands. -/
def mul (x y : Value) : Value :=
  let t := IntTy.promote x.ty y.ty
  pack (JInt.rem t x.int * JInt.rem t y.int)

/-- Wrapping promoted subtraction, `base/int.jl:1092-1100`. -/
def sub (x y : Value) : Value :=
  let t := IntTy.promote x.ty y.ty
  pack (JInt.rem t x.int - JInt.rem t y.int)

/-- Wrapping promoted addition, `base/int.jl:1092-1100`. -/
def add (x y : Value) : Value :=
  let t := IntTy.promote x.ty y.ty
  pack (JInt.rem t x.int + JInt.rem t y.int)

/-- Same-signedness division after checked promotion, `base/div.jl:448-455`;
`base/int.jl:355-358,1085-1089` supplies the primitive (64-bit platform). -/
def promotedDiv (x y : Value) : Jl Value := do
  let t := IntTy.promote x.ty y.ty
  let a ← JInt.convert t x.int.val
  let b ← JInt.convert t y.int.val
  pure (pack (← JInt.div a b))

/-- Same-signedness remainder after checked promotion, `base/promotion.jl:520`,
`base/int.jl:355-358,1085-1089`. -/
def promotedRem (x y : Value) : Jl Value := do
  let t := IntTy.promote x.ty y.ty
  let a ← JInt.convert t x.int.val
  let b ← JInt.convert t y.int.val
  pure (pack (← JInt.remInt a b))

/-- `base/int.jl:275-276`: mixed division unsigned-divides magnitudes,
reinterprets its quotient as signed, flips the original sign, then optionally
reinterprets back to unsigned. No promote-first mixed conversion occurs. -/
def div (x y : Value) : Jl Value := do
  if x.ty.signed && !y.ty.signed then
    pure (flipsign (signed (← promotedDiv (unsigned (abs x)) y)) x)
  else if !x.ty.signed && y.ty.signed then
    pure (unsigned (flipsign (signed (← promotedDiv x (unsigned (abs y)))) y))
  else promotedDiv x y

/-- `base/int.jl:278-279`: mixed remainder keeps the numerator's sign. -/
def rem (x y : Value) : Jl Value := do
  if x.ty.signed && !y.ty.signed then
    pure (flipsign (signed (← promotedRem (unsigned (abs x)) y)) x)
  else if !x.ty.signed && y.ty.signed then
    promotedRem x (unsigned (abs y))
  else promotedRem x y

/-- Same-signedness `divrem`, `base/div.jl:290-324`: quotient first,
then wrapping multiply and subtract, including at typemin. -/
def promotedDivrem (x y : Value) : Jl (Value × Value) := do
  let q ← promotedDiv x y
  pure (q, sub x (mul q y))

/-- `base/int.jl:281-289`: mixed `divrem` computes unsigned magnitudes
before independently restoring quotient and remainder signs. -/
def divrem (x y : Value) : Jl (Value × Value) := do
  if x.ty.signed && !y.ty.signed then
    let (q, r) ← promotedDivrem (unsigned (abs x)) y
    pure (flipsign (signed q) x, flipsign (signed r) x)
  else if !x.ty.signed && y.ty.signed then
    let (q, r) ← promotedDivrem x (unsigned (abs y))
    pure (unsigned (flipsign (signed q) y), r)
  else promotedDivrem x y

/-- `base/div.jl:391-398,438-443,460-464`: mixed floor uses mixed
`divrem`; same-signedness operands use checked promotion and same-type fld. -/
def fld (x y : Value) : Jl Value := do
  if x.ty.signed != y.ty.signed then
    let (q, r) ← divrem x y
    let neg := if x.ty.signed then signbit x else signbit y
    pure (pack (q.int - JInt.lit q.ty (if neg && r.int.val != 0 then 1 else 0)))
  else
    let t := IntTy.promote x.ty y.ty
    let a ← JInt.convert t x.int.val
    let b ← JInt.convert t y.int.val
    pure (pack (← JInt.fld a b))

/-- `base/div.jl:400-407,438-443,467-474`: ceiled mixed quotient
corrects unsigned-magnitude divrem and wraps in the quotient's own type. -/
def cld (x y : Value) : Jl Value := do
  if x.ty.signed != y.ty.signed then
    let (q, r) ← divrem x y
    let neg := if x.ty.signed then signbit x else signbit y
    pure (pack (q.int + JInt.lit q.ty (if !neg && r.int.val != 0 then 1 else 0)))
  else
    let t := IntTy.promote x.ty y.ty
    let a ← JInt.convert t x.int.val
    let b ← JInt.convert t y.int.val
    pure (pack (← JInt.cld a b))

/-- `base/int.jl:331-351`: mixed signed/unsigned mod restores the divisor's
sign using wrapping promoted arithmetic; same-signedness mod promotes first. -/
def mod (x y : Value) : Jl Value := do
  if x.ty.signed && !y.ty.signed then
    let r ← rem x y
    pure (unsigned (add r (mul (lit y.ty (if r.int.val < 0 then 1 else 0)) y)))
  else if !x.ty.signed && y.ty.signed then
    let r := signed (← rem x y)
    pure (add r (mul (lit y.ty (if r.int.val ≠ 0 ∧ y.int.val < 0 then 1 else 0)) y))
  else
    let t := IntTy.promote x.ty y.ty
    let a ← JInt.convert t x.int.val
    let b ← JInt.convert t y.int.val
    pure (pack (← JInt.mod a b))

/-- `base/div.jl:290-324,387`: fldmod uses the generic integer
reconstruction, rather than calling mixed mod. -/
def fldmod (x y : Value) : Jl (Value × Value) := do
  let q ← fld x y
  pure (q, sub x (mul q y))

/-- Modulo by -1 bypasses the signed division overflow for every signed type. -/
def ModNegativeOne : Prop := ∀ t : IntTy, t.signed = true → ∀ x : JInt t,
  JInt.mod x (JInt.lit t (-1)) = .ok (JInt.lit t 0)

theorem modNegativeOne : ModNegativeOne := by
  intro t ht x
  cases t <;> simp_all [JInt.mod, JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits] <;> rfl

/-- The documented absolute-value overflow at each signed typemin. -/
def AbsTypemin : Prop := ∀ t : IntTy, t.signed = true →
  abs (lit t t.min) = lit t t.min

theorem absTypemin : AbsTypemin := by
  intro t ht
  cases t <;> first | contradiction | decide

/-- uabs returns the mathematical magnitude even at every signed typemin. -/
def UabsTypemin : Prop := ∀ t : IntTy, t.signed = true →
  (uabs (lit t t.min)).int.val = -t.min

theorem uabsTypemin : UabsTypemin := by
  intro t ht
  cases t <;> first | contradiction | decide

/-- fldmod's documentation promises the same numeric pair as fld and mod,
including when fixed-width inputs have different signedness. -/
def FldmodConsistency : Prop := ∀ x y : Value, ∀ q r m : Value,
  fldmod x y = .ok (q, r) → mod x y = .ok m → r.int.val = m.int.val

set_option maxRecDepth 10000 in
theorem fldmodInconsistent : ¬ FldmodConsistency := by
  intro h
  have bad := h (lit .u8 1) (lit .i8 (-2)) (lit .u8 255) (lit .u8 255)
    (lit .i8 (-1)) (by rfl) (by rfl)
  exact (by decide : ¬ ((lit .u8 255).int.val = (lit .i8 (-1)).int.val)) bad

/-- Reinterpreting a signed value as unsigned and back preserves its value. -/
def SignedRoundtrip : Prop := ∀ t : IntTy, t.signed = true → ∀ x : JInt t,
  (signed (unsigned (pack x))).int.val = x.val

theorem signedRoundtrip : SignedRoundtrip := by
  intro t ht x
  have hx := x.property
  cases t <;> simp_all [signed, unsigned, pack, JInt.rem, JInt.wrap, wrapInt,
    IntTy.toSigned, IntTy.toUnsigned, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

/-- Type promotion is symmetric and always selects the greater bit width. -/
def PromotionShape : Prop := ∀ t s : IntTy,
  IntTy.promote t s = IntTy.promote s t ∧
  (IntTy.promote t s).bits = max t.bits s.bits

theorem promotionShape : PromotionShape := by
  intro t s
  cases t <;> cases s <;> decide

theorem wrapCancellation {t : IntTy} (x z : JInt t) : z + (x - z) = x := by
  apply Subtype.ext
  change wrapInt t (z.val + wrapInt t (x.val - z.val)) = x.val
  have hx := x.property
  cases t <;> simp_all [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

theorem subZero {t : IntTy} (x : JInt t) : x - JInt.lit t 0 = x := by
  apply Subtype.ext
  change wrapInt t (x.val - wrapInt t 0) = x.val
  have hx := x.property
  cases t <;> simp_all [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

/-- On all unsigned widths, modulus has the documented nonnegative sign,
strict bound, and exact mathematical value for every nonzero divisor. -/
def UnsignedModuloBounds : Prop := ∀ t : IntTy, t.signed = false →
  ∀ a b : JInt t, b.val ≠ 0 → ∀ r : JInt t,
  JInt.mod a b = .ok r →
  r.val = a.val % b.val ∧ 0 ≤ r.val ∧ r.val < b.val

theorem unsignedModuloBounds : UnsignedModuloBounds := by
  intro t ht a b hb r hr
  have ha : 0 ≤ a.val := by simpa [IntTy.min, ht] using a.property.1
  have hbpos : 0 < b.val := by
    have := b.property.1
    simp [IntTy.min, ht] at this
    omega
  have hlo := Int.emod_nonneg a.val hb
  have hhi := Int.emod_lt_of_pos a.val hbpos
  have hrange : t.min ≤ a.val % b.val ∧ a.val % b.val ≤ t.max := by
    have := b.property.2
    simp [IntTy.min, ht]
    omega
  have hw := wrapInt_of_inRange t (a.val % b.val) hrange
  simp [JInt.mod, ht, JInt.remInt, hb, Int.tmod_eq_emod_of_nonneg ha] at hr
  cases hr
  exact ⟨hw, by simpa [JInt.wrap, hw] using hlo, by simpa [JInt.wrap, hw] using hhi⟩

/-- Every successful signed modulo/floor pair reconstructs the numerator
with Julia's wrapping arithmetic, including products overflowing at typemin. -/
def SignedModuloReconstruction : Prop := ∀ t : IntTy, t.signed = true →
  ∀ a b q r : JInt t, JInt.fld a b = .ok q →
  JInt.mod a b = .ok r → q * b + r = a

theorem signedModuloReconstruction : SignedModuloReconstruction := by
  intro t ht a b q r hq hr
  by_cases hb : b.val = -1
  · have ha := a.property
    have hbad : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1) := by
      intro h
      have hd : JInt.div a b = .error .divideError := by simp [JInt.div, h]
      unfold JInt.fld at hq
      rw [hd] at hq
      change Except.error JlError.divideError = Except.ok q at hq
      cases hq
    have hav : a.val ≠ t.min := by
      intro h
      exact hbad ⟨ht, h, hb⟩
    have hrzero : r = JInt.lit t 0 := by
      simpa [JInt.mod, ht, hb, Pure.pure, Except.pure] using hr.symm
    subst r
    have hd : JInt.div a b = .ok (-a) := by
      simp [JInt.div, hb, ht, hav, Int.tdiv_neg, Int.tdiv_one] <;> rfl
    have hmul : (-a) * b = a := by
      apply Subtype.ext
      change wrapInt t (wrapInt t (-a.val) * b.val) = a.val
      cases t <;> simp_all [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega
    have hf : JInt.fld a b = .ok (-a) := by
      unfold JInt.fld
      rw [hd]
      change (if t.signed then
        pure (-a - JInt.lit t (if ((a.val < 0 ∧ 0 ≤ b.val) ∨
          (0 ≤ a.val ∧ b.val < 0)) ∧ ((-a) * b).val ≠ a.val then 1 else 0))
        else pure (-a)) = Except.ok (-a)
      simp [ht, hmul, subZero] <;> rfl
    have hqq : -a = q := Except.ok.inj (hf.symm.trans hq)
    rw [← hqq, hmul]
    apply Subtype.ext
    change wrapInt t (a.val + wrapInt t 0) = a.val
    cases t <;> simp_all [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega
  · have hm : JInt.mod a b = .ok (a - q * b) := by
      simp [JInt.mod, ht, hb, hq] <;> rfl
    have hr' : a - q * b = r := Except.ok.inj (hm.symm.trans hr)
    rw [← hr']
    exact wrapCancellation a (q * b)

def entries : List JuliaLean.Registry.Entry := [
  { id := "intarith-division-mod-negative-one", juliaFile := "base/int.jl",
    juliaFns := ["mod(::T,::T) where T<:BitSigned"],
    statement := "Modulo -1 is zero for every signed input, including typemin.",
    source := "base/int.jl:338-340", status := .proven,
    prop := ``ModNegativeOne, thm := some ``modNegativeOne },
  { id := "intarith-division-abs-typemin", juliaFile := "base/int.jl",
    juliaFns := ["abs"], statement := "Signed typemin is a fixed point of wrapping abs.",
    source := "base/int.jl:207-211", status := .proven,
    prop := ``AbsTypemin, thm := some ``absTypemin },
  { id := "intarith-division-uabs-typemin", juliaFile := "base/float.jl",
    juliaFns := ["Base.uabs"], statement := "Unsigned abs represents the exact magnitude of signed typemin.",
    source := "base/float.jl:226-236", status := .proven,
    prop := ``UabsTypemin, thm := some ``uabsTypemin },
  { id := "intarith-division-signed-roundtrip", juliaFile := "base/int.jl",
    juliaFns := ["signed", "unsigned"], statement := "Unsigned reinterpretation followed by signed reinterpretation preserves every signed input.",
    source := "base/int.jl:261-273", status := .proven,
    prop := ``SignedRoundtrip, thm := some ``signedRoundtrip },
  { id := "intarith-division-promotion-shape", juliaFile := "base/int.jl",
    juliaFns := ["promote_type"], statement := "Integer promotion is symmetric and chooses the wider bit width.",
    source := "base/int.jl:809-822", status := .proven,
    prop := ``PromotionShape, thm := some ``promotionShape },
  { id := "intarith-division-unsigned-mod-bounds", juliaFile := "base/int.jl",
    juliaFns := ["mod"], statement := "Unsigned modulo is exact, nonnegative, and smaller than its nonzero divisor at every width.",
    source := "base/int.jl:296-300,351", status := .proven,
    prop := ``UnsignedModuloBounds, thm := some ``unsignedModuloBounds },
  { id := "intarith-division-signed-mod-reconstruct", juliaFile := "base/int.jl",
    juliaFns := ["mod", "fld"], statement := "Every successful signed floor/modulo pair reconstructs the numerator with wrapping arithmetic.",
    source := "base/int.jl:296-297,338-340", status := .proven,
    prop := ``SignedModuloReconstruction, thm := some ``signedModuloReconstruction },
  { id := "intarith-division-fldmod-consistency", juliaFile := "base/div.jl",
    juliaFns := ["fldmod", "mod", "divrem(::Integer,::Integer,::typeof(RoundDown))"],
    statement := "The remainder from fldmod equals mod for mixed fixed-width inputs.",
    source := "base/div.jl:379-387", status := .refuted,
    prop := ``FldmodConsistency, thm := some ``fldmodInconsistent,
    issue := "#57855 (related mixed-signedness behavior, triage retained wrapping); PR #62319 (rounded remainder consistency). Searches: issues/prs fldmod unsigned; fldmod signed; fldmod mod; divrem mixed signed.",
    notes := "fldmod(UInt8(1), Int8(-2)) = (0xff, 0xff), but mod = Int8(-1). Both versions use generic mixed reconstruction. Master adds explicit wrapping same-type BitSigned divrem/mod methods; these do not cover mixed inputs." }
]

end JuliaLean.IntArith.Division
