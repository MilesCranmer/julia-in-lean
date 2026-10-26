import JuliaLean.IntArith.PowersDigits
import JuliaLean.IntArith.NumberTheory
import JuliaLean.IntFuncsCov.Common

/-!
Coverage of the integer power methods of `base/intfuncs.jl:384-624` (master
`bbfa0ce4150`): `power_by_squaring`, `^`, `literal_pow`, `throw_domerr_powbysq`, `powermod`,
`_powermod_mi_legal`, `_nextpow2`, `_prevpow2` and `ispow2`. The BitInteger algorithms are
the `IntArith.PowersDigits` (`powerBySquaring`, `nextpow2`, `prevpow2`, `ispow2`) and
`IntArith.NumberTheory` (`powermod`, `powermodMILegal`) models.
-/

namespace JuliaLean.IntFuncsCov.Power

open JuliaLean JuliaLean.IntFuncsCov
open JuliaLean.IntArith.PowersDigits (powerBySquaring nextpow2 prevpow2 ispow2)

/-! ### `power_by_squaring` and `^` -/

/-- `^(x::T, p::T) where {T<:Integer}` and `^(x::Number, p::Integer)`,
`base/intfuncs.jl:450-451`: both are `power_by_squaring(x, p)`. -/
def pow {t pty : IntTy} (x : JInt t) (p : JInt pty) : Jl (JInt t) := powerBySquaring x p

/-- The documented integer power in the wrapping arithmetic of `t`: `x^p` for `p ≥ 0`;
for `p < 0` only the units `1` and `-1` (`x ≡ -1 mod 2^bits`) have an integer power, and
any other base throws `DomainError`. -/
def powSpec (t : IntTy) (x p : Int) : Jl Int :=
  if 0 ≤ p then .ok (wrapInt t (x ^ p.toNat))
  else if x = 1 then .ok 1
  else if wrapInt t (-x) = 1 then .ok (if p % 2 = 0 then 1 else x)
  else .error (.domainError "negative integer exponent")

/-- Exponents of the exhaustive power check: every `Int8` exponent in `-3:20` and the
boundary exponents 31, 63, 64, 127, -128. -/
def expo (k : Fin 29) : Int :=
  if k.val < 24 then (k.val : Int) - 3 else [31, 63, 64, 127, -128].getD (k.val - 24) 0

/-- `x^p` (`power_by_squaring`, `base/intfuncs.jl:399-443`) equals the wrapping power for
every byte base and every exponent of the grid, and for a negative exponent returns the
power of a unit or throws `DomainError`. -/
def PowerBySquaringExact : Prop := ∀ (s : Bool) (a : Fin 256) (k : Fin 29),
  let t := byteTy s
  let x := JInt.lit t a.val
  okVal (pow x (JInt.lit .i8 (expo k))) = powSpec t x.val (expo k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem powerBySquaringExact : PowerBySquaringExact := by
  unfold PowerBySquaringExact; decide +kernel

/-- `power_by_squaring(x::Bool, p::Unsigned) = (p==0) | x`, `base/intfuncs.jl:444`, and
`power_by_squaring(x::Bool, p::Integer)`, `:445-448`. -/
def powerBool {pty : IntTy} (x : Bool) (p : JInt pty) : Jl Bool :=
  if pty.signed then
    if p.val < 0 ∧ x = false then .error (.domainError "negative integer exponent")
    else .ok (decide (p.val = 0) || x)
  else .ok (decide (p.val = 0) || x)

/-- `Bool` powers agree with the integer powers of 0 and 1: `x^p == (Int(x)^p == 1)` for
`p ≥ 0`, `true^p == true` for every `p`, and `false^p` throws `DomainError` for `p < 0`. -/
def PowerBool : Prop := ∀ (s : Bool) (n : Fin 256) (x : Bool),
  let pty := byteTy s
  let p := JInt.lit pty n.val
  powerBool x p = (if 0 ≤ p.val then .ok (decide (((if x then 1 else 0 : Int)) ^ p.val.toNat = 1))
    else if x then .ok true else .error (.domainError "negative integer exponent"))

theorem powerBoolProp : PowerBool := by
  unfold PowerBool; decide +kernel

/-- The receiver of `throw_domerr_powbysq`: an `Integer`, an `AbstractMatrix`, or anything
else; the three methods at `base/intfuncs.jl:385-397` differ only in their message. -/
inductive PowBase where
  | integer
  | matrix
  | other
  deriving DecidableEq

/-- `throw_domerr_powbysq(x, p)`, `base/intfuncs.jl:385-397`. -/
def throwDomerrPowbysq (k : PowBase) (p : Int) : Jl Unit :=
  match k with
  | .integer => .error (.domainError s!"Cannot raise an integer x to a negative power {p}.")
  | .matrix => .error (.domainError s!"Cannot raise an integer matrix x to a negative power {p}.")
  | .other => .error (.domainError s!"Cannot raise an integer x to a negative power {p}.")

/-- Every method of `throw_domerr_powbysq` throws a `DomainError`. -/
def ThrowDomerrPowbysq : Prop := ∀ (k : PowBase) (p : Int),
  ∃ msg, throwDomerrPowbysq k p = .error (.domainError msg)

theorem throwDomerrPowbysqProp : ThrowDomerrPowbysq := by
  intro k p
  cases k <;> exact ⟨_, rfl⟩

/-! ### `literal_pow` -/

/-- `literal_pow(f, x, ::Val{p}) = f(x, p)`, `base/intfuncs.jl:460`. -/
def literalPowFallback {α β : Type} (f : α → Int → β) (x : α) (p : Int) : β := f x p

/-- The hardware-integer specializations of `literal_pow(^, x, Val(p))` for `p` in `0:3`,
`base/intfuncs.jl:470-473`: `one(x)`, `x`, `x*x`, `x*x*x`. -/
def literalPowHW {t : IntTy} (x : JInt t) (p : Fin 4) : JInt t :=
  match p with
  | 0 => JInt.lit t 1
  | 1 => x
  | 2 => x * x
  | 3 => x * x * x

/-- `literal_pow(^, x::HWNumber, Val{-1}) = inv(x)` and `Val{-2}`: `(i=inv(x); i*i)`,
`base/intfuncs.jl:474-475`, for a BitInteger `x`: `inv` is `1/Float64(x)`. -/
def literalPowHWNeg {t : IntTy} (x : JInt t) (two : Bool) : JuliaLean.Float.F64 :=
  let i := JuliaLean.Float.F64.div JuliaLean.Float.F64.one (JuliaLean.Float.F64.ofJInt x)
  if two then JuliaLean.Float.F64.mul i i else i

/-- `literal_pow(^, x::AbstractFloat, Val{p}) = x^p` and `Val{-1}`: `inv(x)`,
`base/intfuncs.jl:478-479`, for a floating-point `^` and `inv`. -/
def literalPowFloat {α : Type} (pow : α → Int → α) (inv : α → α) (x : α) (p : Int) : α :=
  if p = -1 then inv x else pow x p

/-- The generic `literal_pow(::typeof(^), x, Val{p})`, `base/intfuncs.jl:483-493`: a negative
power of a `BitInteger64` is computed as `Float64(x)^p`, of anything else as `inv(x)^(-p)`. -/
def literalPowGeneric {α β : Type} (pow : α → Int → β) (inv : α → α) (toFloat : α → α)
    (isBitInteger64 : Bool) (x : α) (p : Int) : β :=
  if p < 0 then
    if isBitInteger64 then pow (toFloat x) p else pow (inv x) (-p)
  else pow x p

/-- Literal exponents agree with run-time exponents: for every byte value `x` and literal
`p` in `0:3`, `literal_pow(^, x, Val(p)) == x^p`; a negative literal is computed through
floating point (`inv(x)` and `inv(x)^2` for `p = -1, -2`, `Float64(x)^p` for other
negative literals of a `BitInteger64`, `inv(x)^(-p)` otherwise), and nonnegative literals
of other types call `^` unchanged. -/
def LiteralPowConsistent : Prop :=
  (∀ (s : Bool) (a : Fin 256) (p : Fin 4),
    let t := byteTy s
    let x := JInt.lit t a.val
    .ok (literalPowHW x p) = pow x (JInt.lit .i64 p.val)) ∧
  (∀ (t : IntTy) (x : JInt t),
    literalPowHWNeg x false =
      JuliaLean.Float.F64.div JuliaLean.Float.F64.one (JuliaLean.Float.F64.ofJInt x) ∧
    literalPowHWNeg x true = JuliaLean.Float.F64.mul (literalPowHWNeg x false) (literalPowHWNeg x false)) ∧
  (∀ (α β : Type) (pow : α → Int → β) (inv toFloat : α → α) (b : Bool) (x : α) (p : Int),
    (0 ≤ p → literalPowGeneric pow inv toFloat b x p = pow x p) ∧
    (p < 0 → literalPowGeneric pow inv toFloat b x p =
      if b then pow (toFloat x) p else pow (inv x) (-p)) ∧
    literalPowFallback pow x p = pow x p) ∧
  (∀ (α : Type) (pow : α → Int → α) (inv : α → α) (x : α) (p : Int),
    literalPowFloat pow inv x p = if p = -1 then inv x else pow x p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem literalPowConsistent : LiteralPowConsistent := by
  refine ⟨?_, fun _ _ => ⟨by simp [literalPowHWNeg], by simp [literalPowHWNeg]⟩, ?_,
    fun _ _ _ _ _ => rfl⟩
  · unfold pow; decide +kernel
  · intro α β pow inv toFloat b x p
    refine ⟨fun h => ?_, fun h => ?_, rfl⟩
    · simp [literalPowGeneric, show ¬ p < 0 by omega]
    · simp [literalPowGeneric, h]

/-! ### `powermod` -/

/-- `powermod(x, p, m)` (`base/intfuncs.jl:524-579`, and the `Int128`/`UInt128` method at
`:587`) as documented: `x^p mod m`, with `mod` taking the sign of `m`, for every
nonnegative exponent; a negative exponent uses the modular inverse of `x`. -/
def powermodSpec (x p m : Int) : Option Int :=
  if m = 0 then none
  else if 0 ≤ p then some ((x ^ p.toNat) % m - (if (x ^ p.toNat) % m ≠ 0 ∧ m < 0 then m.natAbs else 0))
  else none

/-- Bases for the exhaustive `powermod` check. -/
def pmBase (k : Fin 16) : Int := [0, 1, 2, 3, 5, 7, 10, 64, 100, 127, -1, -2, -3, -64, -127, -128].getD k.val 0

/-- Exponents for the exhaustive `powermod` check: `0:17` and the values that select the
multiplicative-inverse loop. -/
def pmExp (k : Fin 20) : Int := if k.val < 18 then k.val else [63, 127].getD (k.val - 18) 0

/-- Moduli for the exhaustive `powermod` check. -/
def pmMod (k : Fin 12) : Int := [1, -1, 2, 3, 7, 15, 16, 100, 127, -128, -7, -100].getD k.val 0

/-- For `Int8` bases and moduli and `Int64` exponents from the grids above, `powermod`
returns `x^p mod m` (nonnegative for positive `m`, nonpositive for negative `m`). The
unsigned moduli of the optimized multiplicative-inverse branch (`_powermod_mi_legal`) are
exercised by `UInt8` moduli in `1:15`. -/
def PowermodExact : Prop :=
  (∀ (a : Fin 16) (e : Fin 20) (k : Fin 12),
    let x := JInt.lit .i8 (pmBase a)
    let m := JInt.lit .i8 (pmMod k)
    (powermodSpec x.val (pmExp e) m.val).map (fun r => (.ok r : Jl Int)) =
      some (okVal (IntArith.NumberTheory.powermod x (JInt.lit .i64 (pmExp e)) m))) ∧
  (∀ (a : Fin 16) (e : Fin 20) (k : Fin 16),
    let x := JInt.lit .u8 (pmBase a)
    let m := JInt.lit .u8 (k.val + 1)
    (powermodSpec x.val (pmExp e) m.val).map (fun r => (.ok r : Jl Int)) =
      some (okVal (IntArith.NumberTheory.powermod x (JInt.lit .i64 (pmExp e)) m)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem powermodExact : PowermodExact := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- `_powermod_mi_legal(::Integer) = false` and `_powermod_mi_legal(mm::Unsigned)`,
`base/intfuncs.jl:581-584`: the multiplicative-inverse branch is taken only for unsigned
moduli below `2^(bits/2)`, so that the product of two residues cannot overflow. -/
def PowermodMILegal : Prop := ∀ (t : IntTy) (m : JInt t),
  IntArith.NumberTheory.powermodMILegal t m = true ↔ (t.signed = false ∧ m.val < 2 ^ (t.bits / 2))

theorem powermodMILegalProp : PowermodMILegal := by
  intro t m
  have hm := m.property
  cases t <;>
    simp [IntArith.NumberTheory.powermodMILegal, IntTy.signed, IntTy.max, IntTy.min, IntTy.bits] at hm ⊢ <;>
    omega

/-! ### `_nextpow2`, `_prevpow2`, `ispow2` -/

/-- `_prevpow2(x::Unsigned)` and `_prevpow2(x::Integer)`, `base/intfuncs.jl:591-592`, give the
largest power of two not above every positive byte value; `_nextpow2` (`:589-590`) gives the
smallest power of two not below it whenever that power is representable (the overflow
beyond is `intarith-powers-nextpow-overflow`); `ispow2(x::Integer)` (`:624`) holds exactly for
the positive powers of two. -/
def Pow2Helpers : Prop := ∀ (s : Bool) (a : Fin 256),
  let t := byteTy s
  let x := JInt.lit t a.val
  let pows : List Int := (List.range 8).map (fun k => 2 ^ k)
  (0 < x.val →
    (prevpow2 x).val ∈ pows ∧ (prevpow2 x).val ≤ x.val ∧ x.val < 2 * (prevpow2 x).val) ∧
  (0 < x.val → x.val ≤ 2 ^ (t.bits - (if s then 2 else 1)) →
    (nextpow2 x).val ∈ pows ∧ x.val ≤ (nextpow2 x).val ∧ (nextpow2 x).val < 2 * x.val) ∧
  (ispow2 x = decide (x.val ∈ pows))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pow2Helpers : Pow2Helpers := by
  unfold Pow2Helpers; decide +kernel

/-- `ispow2(x::Number) = isreal(x) && ispow2(real(x))`, `base/intfuncs.jl:622`, for a number
type with `isreal`, `real` and the real `ispow2`. -/
def ispow2Number {α ρ : Type} (isreal : α → Bool) (real : α → ρ) (ispow2Real : ρ → Bool)
    (x : α) : Bool :=
  isreal x && ispow2Real (real x)

/-- A non-real number is never a power of two; a real one is one exactly when its real part
is. -/
def Ispow2Number : Prop := ∀ (α ρ : Type) (isreal : α → Bool) (real : α → ρ)
    (ispow2Real : ρ → Bool) (x : α),
  (isreal x = false → ispow2Number isreal real ispow2Real x = false) ∧
  (isreal x = true → ispow2Number isreal real ispow2Real x = ispow2Real (real x))

theorem ispow2NumberProp : Ispow2Number := by
  intro α ρ isreal real ispow2Real x
  constructor <;> intro h <;> simp [ispow2Number, h]

end JuliaLean.IntFuncsCov.Power
