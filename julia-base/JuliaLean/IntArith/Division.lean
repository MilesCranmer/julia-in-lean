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

def entries : List JuliaLean.Registry.Entry := []

end JuliaLean.IntArith.Division
