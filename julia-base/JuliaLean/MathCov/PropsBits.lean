import JuliaLean.MathCov.Bits

/-! Source equations and documented invariants for bit-level methods in `base/math.jl`
and `base/floatfuncs.jl`. -/

namespace JuliaLean.MathCov.Bits

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.FloatIntCov.Float (signMask significandBits)

/-- `copysign`, `flipsign`, and `signbit` use exactly the source bit operations. -/
def CopysignFlipsignBehavior : Prop :=
  ∀ T S : FTy, ∀ x y : FV T, ∀ z : FV S,
    copysignF x y = copysign x y ∧ copysignReal x z = copysign x (conv z) ∧
    flipsignF x y = Fl.ofBits (Nat.xor x.toBits
      (y.toBits / signMask T % 2 * signMask T)) ∧
    flipsignReal x z = flipsignF x (conv z) ∧
    signbitBits x = decide (wrapInt (FloatIntCov.Float.intTy T) x.toBits < 0)

theorem copysignFlipsignBehavior : CopysignFlipsignBehavior := by
  simp [CopysignFlipsignBehavior, copysignF, copysignReal, flipsignF, flipsignReal,
    signbitBits]

/-- `maxintfloat` returns the source-selected power of two, type bound, or default. -/
def MaxintfloatBehavior : Prop :=
  ∀ T : FTy, ∀ t : IntTy, ∀ x : FV T,
    maxintfloat T = ofInt T (2 ^ (significandBits T + 1)) ∧
    maxintfloatOf x = maxintfloat T ∧
    maxintfloatInt T t =
      (let a := maxintfloat T; let b : FV T := Fl.ofInt t.max; if lt b a then b else a) ∧
    maxintfloatDefault = maxintfloat .f64 ∧
    maxintfloatBottom (α := FV T) = .error (.methodError "maxintfloat")

theorem maxintfloatBehavior : MaxintfloatBehavior := by
  simp [MaxintfloatBehavior, maxintfloat, maxintfloatOf, maxintfloatInt,
    maxintfloatDefault, maxintfloatBottom]

/-- Generic and IEEE `min` and `max` follow their documented NaN and total-order branches. -/
def MinMaxBehavior : Prop :=
  ∀ T : FTy, ∀ x y : FV T,
    isless_ x y = (lt x y || (x.signbit && !y.signbit)) ∧
    minGeneric x y = (if x.isnan || (!y.isnan && isless_ x y) then x else y) ∧
    maxGeneric x y = (if x.isnan || (!y.isnan && isless_ y x) then x else y) ∧
    minFloat x y =
      (if x.isnan then x else if y.isnan then y else if isless_ y x then y else x) ∧
    maxFloat x y =
      (if x.isnan then x else if y.isnan then y else if isless_ x y then y else x)

theorem minMaxBehavior : MinMaxBehavior := by
  simp [MinMaxBehavior, isless_, minGeneric, maxGeneric, minFloat, maxFloat]

/-- `highword`, `fromhighword`, and `poshighword` use the source shifts and masks. -/
def HighwordBehavior : Prop :=
  ∀ x : FV .f64, ∀ y : FV .f32, ∀ u : Nat,
    highword64 x = x.toBits / 2 ^ 32 % 2 ^ 32 ∧
    highwordU64 u = u / 2 ^ 32 % 2 ^ 32 ∧ highword32 y = y.toBits ∧
    fromhighword64 u = Fl.ofBits (u % 2 ^ 32 * 2 ^ 32) ∧
    fromhighword32 u = Fl.ofBits (u % 2 ^ 32) ∧
    poshighword64 x = highword64 x % 2 ^ 31 ∧
    poshighwordU64 u = highwordU64 u % 2 ^ 31 ∧ poshighword32 y = y.toBits % 2 ^ 31

theorem highwordBehavior : HighwordBehavior := by
  simp [HighwordBehavior, highword64, highwordU64, highword32, fromhighword64,
    fromhighword32, poshighword64, poshighwordU64, poshighword32]

end JuliaLean.MathCov.Bits
