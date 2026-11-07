import JuliaLean.base.floatfuncs
import JuliaLean.Proofs.base.floatfuncs.Misc
import JuliaLean.Registry.Types

/-!
# Properties of `base/floatfuncs.jl`

The TODO specifications use the typed models in `JuliaLean.base.floatfuncs`; their operation
records are interfaces to methods defined by other Base files.
-/

namespace JuliaLean.Proofs.base.floatfuncs

open JuliaLean JuliaLean.base.float JuliaLean.base.floatfuncs JuliaLean.base.rounding
  JuliaLean.Registry
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

private def predicateOps {T : FTy} : FloatPredicateOps (FV T) where
  iszero := JuliaLean.base.float.iszero_float
  sub := JuliaLean.base.float.sub_float
  trunc := JuliaLean.base.float.trunc_llvm

private def floatRealOps {F I : Type} (floatOps : FloatOps F I)
    (integerOps : IntegerOps I) : RealOps F F I where
  category := fun _ => .abstractFloat
  isfinite := floatOps.isfinite
  float := fun x => .ok x
  toInteger := fun _ => integerOps.ofInt 0
  toFloat := fun x => x

/-- The three IEEE `signbit` methods report the high bit of their Float16/32/64 encoding. -/
def SignbitBits : Prop :=
  (∀ x : FV .f16, signbit_Float16 x = decide (x.toBits / 2^15 = 1)) ∧
  (∀ x : FV .f32, signbit_Float32 x = decide (x.toBits / 2^31 = 1)) ∧
  (∀ x : FV .f64, signbit_Float64 x = decide (x.toBits / 2^63 = 1))

/-- `copysign` preserves magnitude and takes the sign bit from its second argument. -/
def CopysignFloatSpec : Prop :=
  (∀ x y : FV .f64,
    JuliaLean.base.float.signbit_float (copysign_Float64 x y) =
      JuliaLean.base.float.signbit_float y ∧
    JuliaLean.base.float.abs_float (copysign_Float64 x y) =
      JuliaLean.base.float.abs_float x) ∧
  (∀ x y : FV .f32,
    JuliaLean.base.float.signbit_float (copysign_Float32 x y) =
      JuliaLean.base.float.signbit_float y ∧
    JuliaLean.base.float.abs_float (copysign_Float32 x y) =
      JuliaLean.base.float.abs_float x) ∧
  (∀ {R : Type} (convert : R → FV .f32) (x : FV .f32) (y : R),
    JuliaLean.base.float.signbit_float (copysign_Float32_Real convert x y) =
      JuliaLean.base.float.signbit_float (convert y) ∧
    JuliaLean.base.float.abs_float (copysign_Float32_Real convert x y) =
      JuliaLean.base.float.abs_float x) ∧
  (∀ {R : Type} (convert : R → FV .f64) (x : FV .f64) (y : R),
    JuliaLean.base.float.signbit_float (copysign_Float64_Real convert x y) =
      JuliaLean.base.float.signbit_float (convert y) ∧
    JuliaLean.base.float.abs_float (copysign_Float64_Real convert x y) =
      JuliaLean.base.float.abs_float x)

/-- `flipsign` changes the sign bit exactly when the second argument's sign bit is set. -/
def FlipsignFloatSpec : Prop :=
  (∀ x y : FV .f64,
    JuliaLean.base.float.abs_float (flipsign_Float64 x y) =
      JuliaLean.base.float.abs_float x ∧
    JuliaLean.base.float.signbit_float (flipsign_Float64 x y) =
      (JuliaLean.base.float.signbit_float x != JuliaLean.base.float.signbit_float y)) ∧
  (∀ x y : FV .f32,
    JuliaLean.base.float.abs_float (flipsign_Float32 x y) =
      JuliaLean.base.float.abs_float x ∧
    JuliaLean.base.float.signbit_float (flipsign_Float32 x y) =
      (JuliaLean.base.float.signbit_float x != JuliaLean.base.float.signbit_float y)) ∧
  (∀ {R : Type} (convert : R → FV .f32) (x : FV .f32) (y : R),
    JuliaLean.base.float.abs_float (flipsign_Float32_Real convert x y) =
      JuliaLean.base.float.abs_float x ∧
    JuliaLean.base.float.signbit_float (flipsign_Float32_Real convert x y) =
      (JuliaLean.base.float.signbit_float x != JuliaLean.base.float.signbit_float (convert y))) ∧
  (∀ {R : Type} (convert : R → FV .f64) (x : FV .f64) (y : R),
    JuliaLean.base.float.abs_float (flipsign_Float64_Real convert x y) =
      JuliaLean.base.float.abs_float x ∧
    JuliaLean.base.float.signbit_float (flipsign_Float64_Real convert x y) =
      (JuliaLean.base.float.signbit_float x != JuliaLean.base.float.signbit_float (convert y)))

/-- `isinteger` is true exactly for finite values whose exact rational value is integral. -/
def IsintegerExact : Prop := ∀ (T : FTy) (x : FV T),
  isinteger_AbstractFloat predicateOps x =
    (x.isfinite && decide (x.toRat.1 % (x.toRat.2 : Int) = 0))

/-- `maxintfloat` is the first positive integer-valued float whose successor is inexact. -/
def MaxintfloatSpec : Prop :=
  maxintfloat_Float64.toRat = ((2^53 : Int), 1) ∧
  (∀ k : Nat, k ≤ 2^53 →
    ∃ x : FV .f64, x.isfinite = true ∧
      x.toRat.1 = (k : Int) * (x.toRat.2 : Int)) ∧
  (∀ x : FV .f64, x.isfinite = true →
    x.toRat.1 ≠ (2^53 + 1) * (x.toRat.2 : Int))


set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/- The legacy proof uses bitvector Float64 values; these bridges map it to the Base model. -/
private theorem f64_fields_bridge (x : JuliaLean.base.float.FV .f64) :
    JuliaLean.Float.F64.exponentField (JuliaLean.Promotion.Fl.toF64 x) =
        JuliaLean.Promotion.Fl.expField x ∧
    JuliaLean.Float.F64.fraction (JuliaLean.Promotion.Fl.toF64 x) =
        JuliaLean.Promotion.Fl.frac x ∧
    JuliaLean.Float.F64.signbit (JuliaLean.Promotion.Fl.toF64 x) =
        JuliaLean.Promotion.Fl.signbit x := by
  cases x with
  | mk bits =>
    have hbits : bits.val % 2 ^ 64 = bits.val := by
      apply Nat.mod_eq_of_lt
      simpa [JuliaLean.base.float.FTy.fmt, JuliaLean.Promotion.double,
        JuliaLean.Promotion.Fmt.width] using bits.isLt
    simp [JuliaLean.Promotion.Fl.toF64, JuliaLean.Promotion.Fl.toBits,
      JuliaLean.Promotion.Fl.expField, JuliaLean.Promotion.Fl.frac,
      JuliaLean.Promotion.Fl.signbit, JuliaLean.Float.F64.exponentField,
      JuliaLean.Float.F64.fraction, JuliaLean.Float.F64.signbit,
      JuliaLean.Float.F64.toBits, JuliaLean.Float.F64.ofBits,
      JuliaLean.base.float.FTy.fmt, JuliaLean.Promotion.double,
      JuliaLean.Promotion.Fmt.width, hbits]

private theorem f64_finite_bridge (x : JuliaLean.base.float.FV .f64) :
    JuliaLean.Float.F64.isfinite (JuliaLean.Promotion.Fl.toF64 x) =
      JuliaLean.Promotion.Fl.isfinite x := by
  obtain ⟨he, _, _⟩ := f64_fields_bridge x
  simp only [JuliaLean.Float.F64.isfinite, JuliaLean.Promotion.Fl.isfinite,
    JuliaLean.base.float.FTy.fmt, JuliaLean.Promotion.double,
    JuliaLean.Promotion.Fmt.emax]
  rw [he]
  have hemax : (2 ^ 11 : Nat) - 1 = 2047 := by decide
  rw [hemax]
  rfl

private theorem f64_rat_bridge (x : JuliaLean.base.float.FV .f64) :
    JuliaLean.Float.F64.toRat (JuliaLean.Promotion.Fl.toF64 x) =
      JuliaLean.Promotion.Fl.toRat x := by
  obtain ⟨he, hf, hs⟩ := f64_fields_bridge x
  have hExp (e : Nat) : (e : Int) - 1075 = (e : Int) - 1023 - 52 := by omega
  simp [JuliaLean.Float.F64.toRat, JuliaLean.Float.F64.isfinite,
    JuliaLean.Promotion.Fl.toRat, JuliaLean.Promotion.Fl.isfinite,
    JuliaLean.base.float.FTy.fmt, JuliaLean.Promotion.double,
    JuliaLean.Promotion.Fmt.bias, JuliaLean.Promotion.Fmt.emax,
    he, hf, hs, hExp]

private theorem toF64_ofF64 (x : JuliaLean.Float.F64) :
    JuliaLean.Promotion.Fl.toF64 (JuliaLean.Promotion.Fl.ofF64 x) = x := by
  cases x with
  | ofFin bits =>
    have hbits : bits.val % 2 ^ 64 = bits.val := by
      apply Nat.mod_eq_of_lt
      simpa using bits.isLt
    apply BitVec.eq_of_toNat_eq
    simp [JuliaLean.Promotion.Fl.toF64, JuliaLean.Promotion.Fl.ofF64,
      JuliaLean.Promotion.Fl.toBits, JuliaLean.Promotion.Fl.ofBits,
      JuliaLean.Float.F64.ofBits, JuliaLean.Float.F64.toBits,
      JuliaLean.Promotion.double, JuliaLean.Promotion.Fmt.width, hbits]

private theorem old_to_new_finite (x : JuliaLean.Float.F64) :
    JuliaLean.Promotion.Fl.isfinite (JuliaLean.Promotion.Fl.ofF64 x) =
      JuliaLean.Float.F64.isfinite x := by
  have h := f64_finite_bridge (JuliaLean.Promotion.Fl.ofF64 x)
  rw [toF64_ofF64] at h
  exact h.symm

private theorem old_to_new_rat (x : JuliaLean.Float.F64) :
    JuliaLean.Promotion.Fl.toRat (JuliaLean.Promotion.Fl.ofF64 x) =
      JuliaLean.Float.F64.toRat x := by
  have h := f64_rat_bridge (JuliaLean.Promotion.Fl.ofF64 x)
  rw [toF64_ofF64] at h
  exact h.symm

theorem maxintfloatSpec_proven : MaxintfloatSpec := by
  have ⟨h0, h1, h2⟩ := JuliaLean.FloatFuncs.maxintfloatSpec_proven
  constructor
  · have hbits : JuliaLean.Promotion.Fl.toF64
        JuliaLean.base.floatfuncs.maxintfloat_Float64 =
        JuliaLean.Float.F64.ofBits 0x4340000000000000 := by decide
    have hrat := f64_rat_bridge JuliaLean.base.floatfuncs.maxintfloat_Float64
    rw [hbits] at hrat
    exact hrat.symm.trans h0
  · constructor
    · intro k hk
      obtain ⟨x, hxfinite, hxrat⟩ := h1 k hk
      refine ⟨JuliaLean.Promotion.Fl.ofF64 x, ?_, ?_⟩
      · exact (old_to_new_finite x).trans hxfinite
      · simpa [JuliaLean.base.float.FTy.fmt, old_to_new_rat x] using hxrat
    · intro x hxfinite
      have hxfiniteOld : JuliaLean.Float.F64.isfinite
          (JuliaLean.Promotion.Fl.toF64 x) = true :=
        (f64_finite_bridge x).trans hxfinite
      have hxrat := f64_rat_bridge x
      intro hx
      rw [← hxrat] at hx
      exact h2 (JuliaLean.Promotion.Fl.toF64 x) hxfiniteOld hx

/-- Specialized `maxintfloat` values are the powers of two at the precision boundary. -/
def MaxintfloatIEEEFormats : Prop :=
  maxintfloat_Float16.toRat = ((2048 : Int), 1) ∧
  maxintfloat_Float32.toRat = ((16777216 : Int), 1) ∧
  maxintfloat_Float64.toRat = ((2^53 : Int), 1)

/-- All type-level maximum-exact-integer methods use the format threshold and integer cap. -/
def MaxintfloatMethods : Prop :=
  MaxintfloatIEEEFormats ∧
  (∀ {F : Type} (ops : FloatTypeOps F) (x : F),
    maxintfloat_AbstractFloat ops x = maxintfloatTypeDispatch ops) ∧
  (∀ {F I : Type} (floatType : FloatTypeOps F) (integerType : IntegerTypeOps I)
      (convert : I → F) (min : F → F → F),
    maxintfloat_AbstractFloat_Integer floatType integerType convert min =
      min (maxintfloatTypeDispatch floatType) (convert integerType.typemax)) ∧
  maxintfloat_Default.toRat = ((2^53 : Int), 1) ∧
  (∀ {A : Type} (slurp : List A),
    maxintfloat_UnionBottom slurp = .error (.methodError "maxintfloat")) ∧
  (∀ {X A : Type} (x : X) (slurp : List A),
    maxintfloat_ValueUnionBottom x slurp = .error (.methodError "maxintfloat"))

/-- Rounding a finite rational to an integer under one of Julia's seven modes. -/
def exactRoundInteger (n : Int) (d : Nat) (mode : RoundMode) : Int := Id.run do
  let q := n.tdiv (d : Int)
  let r := n.tmod (d : Int)
  let away := if n < 0 then -1 else 1
  let twice := 2 * r.natAbs
  match mode.tag with
  | .ToZero => return q
  | .Down => return if r < 0 then q - 1 else q
  | .Up => return if r > 0 then q + 1 else q
  | .FromZero => return if r = 0 then q else q + away
  | .Nearest =>
      if twice < d then return q
      if twice > d then return q + away
      return if q % 2 = 0 then q else q + away
  | .NearestTiesAway =>
      if twice < d then return q
      return q + away
  | .NearestTiesUp =>
      if twice < d then return q
      if twice > d then return q + away
      return if n < 0 then q else q + 1
  | .Other _ => return q

def RoundModesExact : Prop := ∀ (T : FTy) (ops : FloatOps (FV T) (JInt .i64))
    (x : FV T) (mode : RoundMode),
  ops.isfinite x = true →
  (∀ name : String, mode.tag ≠ .Other name) →
  let (n, d) := x.toRat
  let rounded := match mode.tag with
    | .NearestTiesAway => round_TiesAway ops x
    | .NearestTiesUp => round_TiesUp ops x
    | .FromZero => round_FromZero ops x
    | _ => ops.round x mode
  rounded.isfinite = true ∧
    rounded.signbit = x.signbit ∧
    rounded.toRat.1 = exactRoundInteger n d mode * (rounded.toRat.2 : Int)

/-- Supplying both keyword forms for decimal rounding raises `ArgumentError`. -/
def RoundKeywordConflict : Prop :=
  ∀ {R F I : Type} (realOps : RealOps R F I) (floatOps : FloatOps F I)
    (integerOps : IntegerOps I) (roundDefault : R → RoundMode → Jl R)
    (x : R) (mode : RoundMode) (digits sigdigits base : Option I),
    digits.isSome = true → sigdigits.isSome = true →
    round_Real realOps floatOps integerOps roundDefault x mode digits sigdigits base =
      .error (.argumentError "`round` cannot use both `digits` and `sigdigits` arguments.")

/-- With digit keywords, nonfinite reals are returned after conversion to their float type. -/
def RoundNonfinitePassthrough : Prop :=
  ∀ {R F I : Type} (realOps : RealOps R F I) (floatOps : FloatOps F I)
    (integerOps : IntegerOps I) (roundDefault : R → RoundMode → Jl R)
    (x : R) (mode : RoundMode) (digits sigdigits base : Option I),
    realOps.isfinite x = false →
    ((digits.isSome = true ∧ sigdigits.isSome = false) ∨
      (digits.isSome = false ∧ sigdigits.isSome = true)) →
    round_Real realOps floatOps integerOps roundDefault x mode digits sigdigits base =
      (realOps.float x).map Sum.inr

/-- `round(x; sigdigits=s)` uses `hidigit` to choose the decimal scale. -/
def FloorSigdigitsNonzero : Prop :=
  ∀ {F I : Type} (floatOps : FloatOps F I) (integerOps : IntegerOps I)
    (x : F) (base : I) (y : F),
    floatOps.isfinite x = true →
    (floatOps.eq (floatOps.ofInt 1) x = true ∨ floatOps.lt (floatOps.ofInt 1) x = true) →
    floatOps.lt x (floatOps.ofInt (10^22)) = true →
    roundSigdigits (floatRealOps floatOps integerOps) floatOps integerOps x
      RoundDown (integerOps.ofInt 1) base = .ok y →
    floatOps.iszero y = false

/-- Rounding a positive value upward to negative decimal digits reaches the requested step. -/
def CeilDigitsAbove : Prop :=
  ∀ {F I : Type} (floatOps : FloatOps F I) (integerOps : IntegerOps I)
    (x y : F) (k : Nat),
    1 ≤ k → k ≤ 22 → floatOps.isfinite x = true →
    floatOps.lt (floatOps.zero x) x = true →
    roundDigits (floatRealOps floatOps integerOps) floatOps integerOps x RoundUp
      (integerOps.ofInt (-(k : Int))) (integerOps.ofInt 10) = .ok y →
    (floatOps.eq (floatOps.powInteger (floatOps.ofInt 10) (integerOps.ofInt k)) y = true ∨
      floatOps.lt (floatOps.powInteger (floatOps.ofInt 10) (integerOps.ofInt k)) y = true)

def SigdigitsIdempotent : Prop :=
  ∀ {F I : Type} (floatOps : FloatOps F I) (integerOps : IntegerOps I)
    (x y : F) (s base : I),
    floatOps.isfinite x = true →
    roundSigdigits (floatRealOps floatOps integerOps) floatOps integerOps x
      RoundNearest s base = .ok y →
    roundSigdigits (floatRealOps floatOps integerOps) floatOps integerOps y
      RoundNearest s base = .ok y

/-- Negative-digit rounding cannot return zero for a finite input at least one requested step. -/
def RoundDigitsNonzero : Prop :=
  ∀ {F I : Type} (floatOps : FloatOps F I) (integerOps : IntegerOps I)
    (x y : F) (k : Nat),
    1 ≤ k → floatOps.isfinite x = true →
    (floatOps.eq (floatOps.ofInt ((10^k : Nat) : Int)) x = true ∨
      floatOps.lt (floatOps.ofInt ((10^k : Nat) : Int)) x = true) →
    roundDigits (floatRealOps floatOps integerOps) floatOps integerOps x RoundNearest
      (integerOps.ofInt (-(k : Int))) (integerOps.ofInt 10) = .ok y →
    floatOps.iszero y = false

/-- Floating-point `hidigit` uses the exponent in base two and floor-logarithms otherwise. -/
def HidigitSpec : Prop :=
  ∀ {F I : Type} (ops : FloatOps F I) (iops : IntegerOps I) (x : F) (base : I),
    hidigit_AbstractFloat ops iops x base =
      if ops.iszero x then .ok (iops.ofInt 0)
      else if iops.value base = 10 then
        (ops.floorInt (ops.log10 (ops.abs x))).map (fun d => iops.add (iops.ofInt 1) d)
      else if iops.value base = 2 then
        .ok (iops.ofInt (1 + ops.exponent x))
      else
        (ops.floorInt (ops.log base (ops.abs x))).map (fun d => iops.add (iops.ofInt 1) d)

/-- Numeric isapprox accepts equality, tolerance-close finite values, and optional NaN pairs. -/
def IsapproxNumberFormula {N P D C : Type} (ops : NumberApproxOps N P D C)
    (normDifference : D → C) (normValue : P → C) : Prop :=
  ∀ (x y : N) (atol rtol : C) (nans : Bool),
    (ops.equal x y = true →
      isapprox_Number ops normDifference normValue x y atol rtol nans = true) ∧
    (ops.isfinite x = true → ops.isfinite y = true →
      ops.le (normDifference (ops.sub x y))
        (ops.max atol (ops.mul rtol
          (ops.max (normValue (ops.promote x y).1)
          (normValue (ops.promote x y).2)))) = true →
      isapprox_Number ops normDifference normValue x y atol rtol nans = true) ∧
    (nans = true → ops.isnan x = true → ops.isnan y = true →
      isapprox_Number ops normDifference normValue x y atol rtol nans = true)

/-- Numeric isapprox is symmetric when promotion and absolute difference respect argument order. -/
def IsapproxSymmetric {N P D C : Type} (ops : NumberApproxOps N P D C)
    (normDifference : D → C) (normValue : P → C) : Prop :=
  ∀ (x y : N) (atol rtol : C) (nans : Bool),
    ops.equal x y = ops.equal y x →
    ops.promote x y = ((ops.promote y x).2, (ops.promote y x).1) →
    normDifference (ops.sub x y) = normDifference (ops.sub y x) →
    (∀ a b : C, ops.max a b = ops.max b a) →
    isapprox_Number ops normDifference normValue x y atol rtol nans =
      isapprox_Number ops normDifference normValue y x atol rtol nans

/-- Unequal nonfinite values do not compare approximately equal when `nans=false`. -/
def IsapproxNonfinite {N P D C : Type} (ops : NumberApproxOps N P D C)
    (normDifference : D → C) (normValue : P → C) : Prop :=
  ∀ (x y : N) (atol rtol : C),
    ops.equal x y = false → (ops.isfinite x && ops.isfinite y) = false →
    isapprox_Number ops normDifference normValue x y atol rtol false = false

/-- Integer isapprox with the absolute-value norm returns the documented formula without throwing. -/
def IntIsapproxFormula {X Y D W R B : Type} (ops : IntegerApproxOps X Y D W R B) : Prop :=
  ∀ (x : X) (y : Y) (atol rtol : R),
    ops.normIsAbs = true →
    isapprox_Integer ops x y atol rtol =
      .ok (ops.equal x y = true ∨
        ops.le (ops.normDifference (ops.uabsdiff x y))
          (ops.maxBound atol
            (ops.mulBound rtol (ops.maxValues (ops.normUabsX x) (ops.normUabsY y)))) = true)

/-- The curry and negated operators preserve their documented comparison behavior. -/
def IsapproxForwarders : Prop :=
  (∀ {N K : Type} (isapprox : N → N → K → Jl Bool) (x y : N) (kwargs : K),
    isapprox_Curried isapprox y kwargs x = isapprox x y kwargs) ∧
  (∀ {A K : Type} (approximately : A → K → Jl Bool) (args : A) (kwargs : K),
    notApproximately approximately args kwargs = (approximately args kwargs).map (!·))

/-- Relative tolerance defaults use float precision, real zero, and positive-atol zeroing. -/
def RtolDefaults : Prop :=
  (∀ {F : Type} (ops : RtolFloatOps F) (epsValue : F),
    ops.eps = .ok epsValue →
      rtoldefault_AbstractFloat ops = ops.sqrt epsValue) ∧
  rtoldefault_Real = 0 ∧
  (∀ {T A R : Type} (ops : RtolPairOps T A R) (x y : T) (atol : A),
    rtoldefault_Values ops x y atol =
      (do
        let rtolX ← ops.default (ops.realType x)
        let rtolY ← ops.default (ops.realType y)
        let rtol ← ops.max rtolX rtolY
        let zeroAtol ← ops.zeroAtol atol
        if ← ops.atolGreater atol zeroAtol then ops.zeroRtol rtol else pure rtol))
/-- `_uabsdiff` is the nonnegative exact distance between integer inputs. -/
def UabsdiffExact : Prop :=
  ∀ x y : Int,
    uabsdiff_Integer
      { less := fun a b => decide (a < b)
        subXY := fun a b => a - b
        subYX := fun a b => a - b
        leBound := fun d b => decide (d ≤ b) }
      x y = ((x - y).natAbs : Int)

/-- `splitbits` leaves 27 zero bits in `hi`, 26 in `lo`, and recombines exactly. -/
def SplitbitsSpec (truncbits : FV .f64 → Nat → FV .f64) : Prop :=
  ∀ x : FV .f64,
    x.isfinite = true →
    let (hi, lo) := splitbits_Float64 truncbits x
    hi.toBits % 2^27 = 0 ∧ lo.toBits % 2^26 = 0 ∧
      (hi.toRat.1 * (lo.toRat.2 : Int) + lo.toRat.1 * (hi.toRat.2 : Int)) *
          (x.toRat.2 : Int) =
        x.toRat.1 * ((hi.toRat.2 * lo.toRat.2 : Nat) : Int)

/-- The exact rational sum of the high and low parts equals the product. -/
def TwoMulExactSum {T : FTy} (x y hi lo : FV T) : Prop :=
  let (xn, xd) := x.toRat
  let (yn, yd) := y.toRat
  let (hn, hd) := hi.toRat
  let (ln, ld) := lo.toRat
  (hn * (ld : Int) + ln * (hd : Int)) * ((xd * yd : Nat) : Int) =
    xn * yn * ((hd * ld : Nat) : Int)

/-- Generic float `two_mul` returns exact rational parts for finite results. -/
def TwoMulNumberExact (ops : FloatFmaOps) : Prop :=
  ∀ (T : FTy) (x y : FV T),
    x.isfinite = true → y.isfinite = true →
    ∃ hi lo : FV T,
      two_mul_Number
        (fun a b => .ok (JuliaLean.base.float.mul_float a b))
        (fun a => .ok (JuliaLean.base.float.neg_float a))
        (fun a b c => .ok (fma_IEEEFloat ops a b c))
        x y = .ok (hi, lo) ∧
      hi.isfinite = true ∧ lo.isfinite = true ∧ TwoMulExactSum x y hi lo

/-- The Float64 specialization returns exact rational parts when both are finite. -/
def TwoMulFloat64Exact (ops : Float64FmaOps) : Prop :=
  ∀ x y : FV .f64,
    x.isfinite = true → y.isfinite = true →
    let (hi, lo) := two_mul_Float64 ops x y
    hi.isfinite = true → lo.isfinite = true → TwoMulExactSum x y hi lo

/-- The Float16 and Float32 specializations return exact rational parts when finite. -/
def TwoMulSmallExact (ops : FloatFmaOps) : Prop :=
  let ops16 : SmallTwoMulOps .f16 :=
    { haveFma := ops.haveFma .f16, widen := ops.fma16.widen, narrow := ops.fma16.narrow }
  let ops32 : SmallTwoMulOps .f32 :=
    { haveFma := ops.haveFma .f32, widen := ops.fma32.widen, narrow := ops.fma32.narrow }
  (∀ x y : FV .f16,
    x.isfinite = true → y.isfinite = true →
    let (hi, lo) := two_mul_Small (Or.inl rfl) ops16
      (fun a b c => fma_IEEEFloat ops a b c) x y
    hi.isfinite = true → lo.isfinite = true → TwoMulExactSum x y hi lo) ∧
  (∀ x y : FV .f32,
    x.isfinite = true → y.isfinite = true →
    let (hi, lo) := two_mul_Small (Or.inr rfl) ops32
      (fun a b c => fma_IEEEFloat ops a b c) x y
    hi.isfinite = true → lo.isfinite = true → TwoMulExactSum x y hi lo)
def TwoMulExact (ops : FloatFmaOps) : Prop :=
  TwoMulNumberExact ops ∧
    TwoMulFloat64Exact ops.fma64 ∧ TwoMulSmallExact ops

/-- A correction that loses low-order bits has an odd significand. -/
def FmaCorrectionOdd (ops : Float64FmaOps) : Prop :=
  ∀ (abhi ablo c r : FV .f64),
    abhi.isfinite = true → ablo.isfinite = true → c.isfinite = true → r.isfinite = true →
    let s := fma_correction ops abhi ablo c r
    let (an, ad) := abhi.toRat
    let (bn, bd) := ablo.toRat
    let (cn, cd) := c.toRat
    let (rn, rd) := r.toRat
    let (sn, sd) := s.toRat
    let exactNumerator :=
      an * (rd * cd * bd : Nat) - rn * (ad * cd * bd : Nat) +
        cn * (ad * rd * bd : Nat) + bn * (ad * rd * cd : Nat)
    let exactDenominator := ad * rd * cd * bd
    s.isfinite = true →
      (sn * (exactDenominator : Int) ≠ exactNumerator * (sd : Int) →
        (ops.bits s).val % 2 = 1)

/-- `fma` rounds the exact finite sum once, including its zero sign. -/
def FmaCorrect (ops : FloatFmaOps) : Prop :=
  ∀ (T : FTy) (x y z : FV T),
    x.isfinite = true → y.isfinite = true → z.isfinite = true →
    let (xn, xd) := x.toRat
    let (yn, yd) := y.toRat
    let (zn, zd) := z.toRat
    let n := xn * yn * (zd : Int) + zn * (xd : Int) * (yd : Int)
    let d := xd * yd * zd
    let zeroSign := (x.iszero || y.iszero) && z.iszero &&
      (x.signbit != y.signbit) && z.signbit
    fma_IEEEFloat ops x y z = Fl.roundRat n d zeroSign

/-! Nothing to promise: `fma@349` only declares the generic function; its IEEE method is at 464. -/

/-!
Nothing to promise: hidigit(x::Integer, base)@132: forwards to ndigits0z.
Nothing to promise: hidigit(x::Real, base)@143: converts to float and forwards to hidigit(::AbstractFloat).
Nothing to promise: fma@349: declares the generic function; the IEEE method is at 464.
-/


namespace JuliaLean.ChatGPT.Batch3.Group3

open JuliaLean JuliaLean.C JuliaLean.base.int JuliaLean.base.float JuliaLean.base.floatfuncs
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

set_option maxRecDepth 8192

/-- Reading a signed 64-bit pattern recovers the represented integer. -/
theorem floatSignFromInt64 (x : JInt .i64) : (fromJInt x).toInt = x.val := by
  have hx : -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 := x.property
  simp only [fromJInt, BitVec.toInt_ofInt, IntTy.bits, Int.bmod_def]
  split <;> omega

/-- Same-signed promotion to Int64 preserves the sign predicate of smaller types. -/
theorem floatSignIntegerValue {t : IntTy}
    (ht : t = .i16 ∨ t = .i32 ∨ t = .i64) (x : JInt t) :
    JuliaLean.base.int.signbit x = decide (x.val < 0) := by
  have hx := x.property
  have hw : wrapInt .i64 x.val = x.val := by
    apply wrapInt_of_inRange
    rcases ht with rfl | rfl | rfl <;>
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ite_true] at hx ⊢ <;> omega
  rcases ht with rfl | rfl | rfl
  all_goals
    change decide ((fromJInt (widenTo .i64 x)).toInt <
      (fromJInt (widenTo .i64 (lit .i64 0))).toInt) = decide (x.val < 0)
    rw [floatSignFromInt64, floatSignFromInt64]
    change decide (wrapInt .i64 x.val < 0) = decide (x.val < 0)
    rw [hw]

/-- The float-to-signed-integer cast exposes the signed interpretation of its bits. -/
theorem floatSignCast16 (x : FV .f16) :
    (bitcast_from_float .i16 x).val =
      ((x.toBits : Int) + 32768) % 65536 - 32768 := by
  have hb : x.toBits < 65536 := x.bits.isLt
  change wrapInt .i16 (BitVec.ofNat 16 x.toBits).toInt = _
  rw [← BitVec.ofInt_natCast, BitVec.toInt_ofInt]
  simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true, Int.bmod_def]
  split <;> omega

theorem floatSignCast32 (x : FV .f32) :
    (bitcast_from_float .i32 x).val =
      ((x.toBits : Int) + 2147483648) % 4294967296 - 2147483648 := by
  have hb : x.toBits < 4294967296 := x.bits.isLt
  change wrapInt .i32 (BitVec.ofNat 32 x.toBits).toInt = _
  rw [← BitVec.ofInt_natCast, BitVec.toInt_ofInt]
  simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true, Int.bmod_def]
  split <;> omega

theorem floatSignCast64 (x : FV .f64) :
    (bitcast_from_float .i64 x).val =
      ((x.toBits : Int) + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 := by
  have hb : x.toBits < 18446744073709551616 := x.bits.isLt
  change wrapInt .i64 (BitVec.ofNat 64 x.toBits).toInt = _
  rw [← BitVec.ofInt_natCast, BitVec.toInt_ofInt]
  simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true, Int.bmod_def]
  split <;> omega

theorem floatSign16Bits (x : FV .f16) :
    signbit_Float16 x = decide (x.toBits / 2^15 = 1) := by
  have hb : x.toBits < 65536 := x.bits.isLt
  rw [signbit_Float16, floatSignIntegerValue (Or.inl rfl), floatSignCast16]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem floatSign32Bits (x : FV .f32) :
    signbit_Float32 x = decide (x.toBits / 2^31 = 1) := by
  have hb : x.toBits < 4294967296 := x.bits.isLt
  rw [signbit_Float32, floatSignIntegerValue (Or.inr (Or.inl rfl)), floatSignCast32]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem floatSign64Bits (x : FV .f64) :
    signbit_Float64 x = decide (x.toBits / 2^63 = 1) := by
  have hb : x.toBits < 18446744073709551616 := x.bits.isLt
  rw [signbit_Float64, floatSignIntegerValue (Or.inr (Or.inr rfl)), floatSignCast64]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

end JuliaLean.ChatGPT.Batch3.Group3

namespace JuliaLean.ChatGPT.Batch3.Group3
open JuliaLean JuliaLean.Promotion JuliaLean.base.float JuliaLean.base.floatfuncs
open JuliaLean.Proofs.base.floatfuncs

/-- All three formats return exactly the top bit of their interchange encoding. -/
theorem FloatfuncsSignbitBits_proven : JuliaLean.Proofs.base.floatfuncs.SignbitBits :=
  ⟨floatSign16Bits, floatSign32Bits, floatSign64Bits⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The precision thresholds, integer caps, and bottom-type errors follow every installed method. -/
theorem FloatfuncsMaxintfloatMethods_proven :
    JuliaLean.Proofs.base.floatfuncs.MaxintfloatMethods := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by decide, by decide, JuliaLean.Proofs.base.floatfuncs.maxintfloatSpec_proven.1⟩
  · intro F ops x
    rfl
  · intro F I floatType integerType convert min
    rfl
  · exact JuliaLean.Proofs.base.floatfuncs.maxintfloatSpec_proven.1
  · intro A slurp
    rfl
  · intro X A x slurp
    rfl

end JuliaLean.ChatGPT.Batch3.Group3
end JuliaLean.Proofs.base.floatfuncs


namespace JuliaLean.ChatGPT.Batch4.Group20

open JuliaLean JuliaLean.base.float JuliaLean.base.floatfuncs
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.floatfuncs

/-- The complete tolerance contract holds for every supplied numeric interface and norms. -/
theorem isapproxNumberFormulaApplied {N P D C : Type}
    (ops : NumberApproxOps N P D C) (normDifference : D → C) (normValue : P → C) :
    IsapproxNumberFormula ops normDifference normValue := by
  intro x y atol rtol nans
  constructor
  · intro heq
    simp only [isapprox_Number, heq, Bool.true_or]
  constructor
  · intro hx hy hle
    simp only [isapprox_Number, hx, hy, hle, Bool.true_and, Bool.or_true,
      Bool.true_or]
  · intro hn hx hy
    simp only [isapprox_Number, hn, hx, hy, Bool.true_and, Bool.or_true]

/-- Unequal nonfinite inputs are rejected with NaN matching disabled. -/
theorem isapproxNonfiniteApplied {N P D C : Type}
    (ops : NumberApproxOps N P D C) (normDifference : D → C) (normValue : P → C) :
    IsapproxNonfinite ops normDifference normValue := by
  intro x y atol rtol heq hfinite
  simp only [isapprox_Number, heq, ← Bool.and_assoc, hfinite, Bool.false_and, Bool.false_or,
    Bool.or_false]

/-- floatfuncs-isapprox-forwarders: both wrappers preserve their comparisons. -/
theorem FloatfuncsIsapproxForwarders_proven : JuliaLean.Proofs.base.floatfuncs.IsapproxForwarders := by
  constructor
  · intro N K approximately x y kwargs
    rfl
  · intro A K approximately args kwargs
    rfl

/-- The selected hardware branch is exactly the model's FMA primitive. -/
theorem fmaIEEEHardware {T : FTy} (ops : FloatFmaOps) (x y z : FV T)
    (h : ops.haveFma T = true) :
    fma_IEEEFloat ops x y z = JuliaLean.C.jlFmaFloat x y z := by
  simp only [fma_IEEEFloat, h, ↓reduceIte]

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.ChatGPT.Batch4.Group20

open JuliaLean JuliaLean.base.float JuliaLean.base.floatfuncs
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

/-- Finite IEEE encodings are neither infinity nor NaN. -/
theorem group20FiniteFlags {f : Fmt} (x : Fl f) (hx : x.isfinite = true) :
    x.isnan = false ∧ x.isinf = false := by
  have he : (x.expField == f.emax) = false := by
    simpa only [Fl.isfinite, bne, Bool.not_eq_true'] using hx
  constructor <;> simp only [Fl.isnan, Fl.isinf, he, Bool.false_and]

/-- The primitive's finite branch computes a single rounded exact product and sum. -/
theorem group20FloatFmaFiniteRaw {f : Fmt} (x y z : Fl f)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true) :
    JuliaLean.C.floatFma x y z =
      Fl.roundRat
        (x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
          z.toRat.1 * ((x.toRat.2 * y.toRat.2 : Nat) : Int))
        (x.toRat.2 * y.toRat.2 * z.toRat.2)
        ((x.signbit != y.signbit) && z.signbit) := by
  obtain ⟨hxn, hxi⟩ := group20FiniteFlags x hx
  obtain ⟨hyn, hyi⟩ := group20FiniteFlags y hy
  obtain ⟨hzn, hzi⟩ := group20FiniteFlags z hz
  simp only [JuliaLean.C.floatFma, hxn, hyn, hzn, hxi, hyi, hzi,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.false_or, Bool.or_false]

/-- Swapping the finite multiplicands preserves the primitive, including its zero sign. -/
theorem group20FloatFmaFiniteComm {f : Fmt} (x y z : Fl f)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true) :
    JuliaLean.C.floatFma y x z = JuliaLean.C.floatFma x y z := by
  rw [group20FloatFmaFiniteRaw y x z hy hx hz, group20FloatFmaFiniteRaw x y z hx hy hz]
  simp only [Int.mul_comm y.toRat.1 x.toRat.1, Nat.mul_comm y.toRat.2 x.toRat.2,
    bne_comm (a := y.signbit) (b := x.signbit)]

/-- The runtime's finishing conversion leaves each supported IEEE format unchanged. -/
theorem group20FinishIEEE {T : FTy} (value : FV T) :
    JuliaLean.C.finishFloat value = value := by
  cases T <;> rfl

/-- The format-specific hardware primitive has the same exact finite expression. -/
theorem group20JlFmaFiniteRaw {T : FTy} (x y z : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true) :
    JuliaLean.C.jlFmaFloat x y z =
      Fl.roundRat
        (x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
          z.toRat.1 * ((x.toRat.2 * y.toRat.2 : Nat) : Int))
        (x.toRat.2 * y.toRat.2 * z.toRat.2)
        ((x.signbit != y.signbit) && z.signbit) := by
  rw [JuliaLean.C.jlFmaFloat, group20FloatFmaFiniteComm x y z hx hy hz]
  simp only [ite_self, group20FinishIEEE (T := T)]
  exact group20FloatFmaFiniteRaw x y z hx hy hz

/-- Once the hardware path is selected, no emulation callback affects finite FMA. -/
theorem group20HardwareFmaFiniteRaw {T : FTy} (ops : FloatFmaOps) (x y z : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true)
    (huse : ops.haveFma T = true) :
    fma_IEEEFloat ops x y z =
      Fl.roundRat
        (x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
          z.toRat.1 * ((x.toRat.2 * y.toRat.2 : Nat) : Int))
        (x.toRat.2 * y.toRat.2 * z.toRat.2)
        ((x.signbit != y.signbit) && z.signbit) := by
  simpa only [fma_IEEEFloat, huse, ↓reduceIte] using group20JlFmaFiniteRaw x y z hx hy hz

/-- Exact nonzero numerators make the exact-zero sign parameter irrelevant. -/
theorem group20RoundRatNonzeroSign {f : Fmt} (n : Int) (d : Nat) (first second : Bool)
    (hn : n ≠ 0) :
    Fl.roundRat (f := f) n d first = Fl.roundRat n d second := by
  have hn' : (n == 0) = false := beq_eq_false_iff_ne.2 hn
  simp only [Fl.roundRat, hn', Bool.false_eq_true, ↓reduceIte]

/-- The frozen FMA formula holds on the hardware path when its exact sum is nonzero. -/
theorem group20HardwareFmaFiniteNonzero {T : FTy} (ops : FloatFmaOps) (x y z : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true)
    (huse : ops.haveFma T = true)
    (hn : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
      z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int) ≠ 0) :
    fma_IEEEFloat ops x y z =
      Fl.roundRat
        (x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
          z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int))
        (x.toRat.2 * y.toRat.2 * z.toRat.2)
        ((x.iszero || y.iszero) && z.iszero &&
          (x.signbit != y.signbit) && z.signbit) := by
  have hraw := group20HardwareFmaFiniteRaw ops x y z hx hy hz huse
  have hnum : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
      z.toRat.1 * ((x.toRat.2 * y.toRat.2 : Nat) : Int) =
      x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
        z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int) := by
    simp only [Int.natCast_mul, Int.mul_assoc]
  rw [hnum] at hraw
  exact hraw.trans (group20RoundRatNonzeroSign _ _ _ _ hn)


/-- Exponent bits are the high bits of the sign-free magnitude. -/
theorem group20ExpFieldMagnitude {f : Fmt} (x : Fl f) :
    x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

/-- Fraction bits are the low bits of the sign-free magnitude. -/
theorem group20FractionMagnitude {f : Fmt} (x : Fl f) :
    x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

/-- Finite decoding has positive denominator and a signed natural numerator. -/
theorem group20FiniteDecode {f : Fmt} (x : Fl f) (hx : x.isfinite = true) :
    ∃ m d : Nat, 0 < d ∧
      x.toRat = ((if x.signbit then -(m : Int) else (m : Int)), d) ∧
      (m = 0 → x.iszero = true) := by
  let m : Nat := x.frac + if x.expField == 0 then 0 else 2 ^ f.sb
  let p : Int := if x.expField == 0 then 1 - (f.bias : Int) - f.sb
    else (x.expField : Int) - f.bias - f.sb
  have hmzero : m = 0 → x.iszero = true := by
    intro hm
    have he : x.expField = 0 := by
      by_cases he : x.expField = 0
      · exact he
      · have hbeq : (x.expField == 0) = false := beq_eq_false_iff_ne.2 he
        have hm' : x.frac + 2 ^ f.sb = 0 := by
          simpa only [m, hbeq, Bool.false_eq_true, ↓reduceIte] using hm
        have hpow : 0 < 2 ^ f.sb := Nat.two_pow_pos f.sb
        omega
    have hfrac : x.frac = 0 := by
      simpa only [m, he, beq_self_eq_true, ↓reduceIte, Nat.add_zero] using hm
    have hdiv : x.magnitude / 2 ^ f.sb = 0 :=
      (group20ExpFieldMagnitude x).symm.trans he
    have hmod : x.magnitude % 2 ^ f.sb = 0 :=
      (group20FractionMagnitude x).symm.trans hfrac
    have hmag : x.magnitude = 0 := by
      have h := (Nat.mod_add_div x.magnitude (2 ^ f.sb)).symm
      simpa only [hdiv, hmod, Nat.mul_zero, Nat.zero_add] using h
    simp only [Fl.iszero, hmag, beq_self_eq_true]
  have hraw : x.toRat =
      if p ≥ 0 then
        ((if x.signbit then -(m : Int) else (m : Int)) *
          ((2 ^ p.toNat : Nat) : Int), 1)
      else ((if x.signbit then -(m : Int) else (m : Int)), 2 ^ (-p).toNat) := by
    unfold Fl.toRat
    rw [hx] <;> rfl
  by_cases hp : p ≥ 0
  · rw [hraw, if_pos hp]
    refine ⟨m * 2 ^ p.toNat, 1, by decide, ?_, ?_⟩
    · refine Prod.ext ?_ rfl
      cases hs : x.signbit <;>
        simp only [hs, Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.neg_mul]
    · intro hzero
      apply hmzero
      rcases Nat.mul_eq_zero.1 hzero with h | h
      · exact h
      · have hpow : 0 < 2 ^ p.toNat := Nat.two_pow_pos p.toNat
        omega
  · rw [hraw, if_neg hp]
    exact ⟨m, 2 ^ (-p).toNat, Nat.two_pow_pos _, rfl, hmzero⟩

/-- Finite decoding preserves sign and detects either encoding of zero. -/
theorem group20FiniteRatSigns {f : Fmt} (x : Fl f) (hx : x.isfinite = true) :
    0 < x.toRat.2 ∧
      (x.signbit = false → 0 ≤ x.toRat.1) ∧
      (x.signbit = true → x.toRat.1 ≤ 0) ∧
      (x.toRat.1 = 0 → x.iszero = true) := by
  obtain ⟨m, d, hd, hr, hmzero⟩ := group20FiniteDecode x hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hr] using hd
  · intro hs
    simpa only [hr, hs, Bool.false_eq_true, ↓reduceIte] using Int.natCast_nonneg m
  · intro hs
    have hm : -(m : Int) ≤ 0 := by omega
    simpa only [hr, hs, ↓reduceIte] using hm
  · intro hn
    apply hmzero
    cases hs : x.signbit <;>
      simp only [hr, hs, Bool.false_eq_true, ↓reduceIte] at hn <;> omega

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.Proofs.base.floatfuncs
open JuliaLean.Registry
def entries : List Entry := [
  { id := "floatfuncs-signbit-bits", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["signbit(x::Float64)", "signbit(x::Float32)", "signbit(x::Float16)"],
    statement := "signbit reports the sign bit for every IEEE Float16, Float32, and Float64 value, including signed zeros and NaNs.",
    source := "base/floatfuncs.jl:15-17", status := .proven, prop := ``SignbitBits,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group3.FloatfuncsSignbitBits_proven },
  { id := "floatfuncs-maxintfloat-spec", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["maxintfloat(::Type{Float64})"],
    statement := "maxintfloat(Float64) is 2^53, the largest consecutive integer-valued Float64, and 2^53+1 is not representable.",
    source := "base/floatfuncs.jl:23-34 (maxintfloat docstring)", status := .proven,
    prop := ``MaxintfloatSpec, thm := some ``maxintfloatSpec_proven },
  { id := "floatfuncs-maxintfloat-methods", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["maxintfloat(::Type{Float32})", "maxintfloat(::Type{Float16})",
      "maxintfloat(x::T) where {T<:AbstractFloat}",
      "maxintfloat(::Type{S}, ::Type{T}) where {S<:AbstractFloat,T<:Integer}",
      "maxintfloat()", "maxintfloat(::Type{Union{}}, slurp...)",
      "maxintfloat(x, ::Type{Union{}}, slurp...)"],
    statement := "Float16/32/64 return their precision thresholds, integer caps take the smaller representable limit, and Union{} calls raise MethodError.",
    source := "base/floatfuncs.jl:35-49", status := .proven,
    prop := ``MaxintfloatMethods, thm := some ``JuliaLean.ChatGPT.Batch3.Group3.FloatfuncsMaxintfloatMethods_proven },
  { id := "floatfuncs-isapprox-tolerances", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isapprox(::Number, ::Number; atol, rtol, nans)"],
    statement := "isapprox accepts equality, finite pairs within the absolute or relative tolerance, and NaN pairs only when nans=true.",
    source := "base/floatfuncs.jl:166-181,230-237", status := .todo,
    prop := ``IsapproxNumberFormula, thm := none, notes := "Statement defect: IsapproxNumberFormula takes an operation record and two norms as explicit arguments, so the registered name is a function into Prop rather than a proposition. The submitted applied formula does not settle the registered unapplied property." },
  { id := "floatfuncs-isapprox-nonfinite", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isapprox(::Number, ::Number; atol, rtol, nans)"],
    statement := "Unequal nonfinite numeric values are not approximately equal when nans=false; infinity matches only itself.",
    source := "base/floatfuncs.jl:166-181,230-237", status := .todo,
    prop := ``IsapproxNonfinite },
  { id := "floatfuncs-isapprox-forwarders", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isapprox(y; kwargs...)", "≉(args...; kws...)"],
    statement := "The one-argument isapprox method returns a comparator, and ≉ negates the corresponding isapprox result.",
    source := "base/floatfuncs.jl:305-323", status := .proven,
    prop := ``IsapproxForwarders, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.FloatfuncsIsapproxForwarders_proven },
  { id := "floatfuncs-fma-exact", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["fma_emulated(::Float16, ::Float16, ::Float16)",
      "fma_emulated(::Float32, ::Float32, ::Float32)",
      "fma_emulated(::Float64, ::Float64, ::Float64)", "fma(::IEEEFloat, ::IEEEFloat, ::IEEEFloat)"],
    statement := "fma returns the correctly rounded result of the exact product-plus-sum, without intermediate rounding.",
    source := "base/floatfuncs.jl:342-349,350-361,413-466", status := .todo,
    prop := ``FmaCorrect, thm := none, notes := "Statement defect: FmaCorrect requires an explicit FloatFmaOps argument, so the registered name is a function into Prop rather than a proposition. The hardware branch has an existing proof; arbitrary software arithmetic callbacks still require a concrete Julia model or justified coherence laws. A hardware-only helper does not establish the full prose contract." }
]

end JuliaLean.Proofs.base.floatfuncs


namespace JuliaLean.ChatGPT.Batch8.Group12

open JuliaLean JuliaLean.base.float JuliaLean.base.floatfuncs
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.floatfuncs

/-- Exact acceptance criteria, including both directions of each Boolean branch. -/
theorem isapproxAcceptanceIff {N P D C : Type}
    (ops : NumberApproxOps N P D C) (normDifference : D → C) (normValue : P → C)
    (x y : N) (atol rtol : C) (nans : Bool) :
    isapprox_Number ops normDifference normValue x y atol rtol nans = true ↔
      (ops.equal x y = true ∨
        (ops.isfinite x = true ∧ ops.isfinite y = true ∧
          ops.le (normDifference (ops.sub x y))
            (ops.max atol (ops.mul rtol
              (ops.max (normValue (ops.promote x y).1)
                (normValue (ops.promote x y).2)))) = true) ∨
        (nans = true ∧ ops.isnan x = true ∧ ops.isnan y = true)) := by
  simp only [isapprox_Number, Bool.or_eq_true, Bool.and_eq_true,
    and_assoc, or_assoc]

/-- A nonfinite pair has precisely equality and optional NaN matching available. -/
theorem isapproxNonfiniteExact {N P D C : Type}
    (ops : NumberApproxOps N P D C) (normDifference : D → C) (normValue : P → C)
    (x y : N) (atol rtol : C) (nans : Bool)
    (hfinite : (ops.isfinite x && ops.isfinite y) = false) :
    isapprox_Number ops normDifference normValue x y atol rtol nans =
      (ops.equal x y || (nans && ops.isnan x && ops.isnan y)) := by
  simp only [isapprox_Number, hfinite, Bool.false_and, Bool.or_false]

/-- With NaN matching disabled, approximate equality of a nonfinite pair is equality. -/
theorem isapproxNonfiniteNoNans {N P D C : Type}
    (ops : NumberApproxOps N P D C) (normDifference : D → C) (normValue : P → C)
    (x y : N) (atol rtol : C)
    (hfinite : (ops.isfinite x && ops.isfinite y) = false) :
    isapprox_Number ops normDifference normValue x y atol rtol false = ops.equal x y := by
  rw [isapproxNonfiniteExact ops normDifference normValue x y atol rtol false hfinite]
  simp only [Bool.false_and, Bool.or_false]

/-- An accepted unequal nonfinite pair necessarily consists of enabled NaN matches. -/
theorem isapproxUnequalNonfiniteIff {N P D C : Type}
    (ops : NumberApproxOps N P D C) (normDifference : D → C) (normValue : P → C)
    (x y : N) (atol rtol : C) (nans : Bool)
    (hequal : ops.equal x y = false)
    (hfinite : (ops.isfinite x && ops.isfinite y) = false) :
    isapprox_Number ops normDifference normValue x y atol rtol nans = true ↔
      nans = true ∧ ops.isnan x = true ∧ ops.isnan y = true := by
  rw [isapproxNonfiniteExact ops normDifference normValue x y atol rtol nans hfinite]
  simp only [hequal, Bool.false_or, Bool.and_eq_true, and_assoc]

/-- For an exact zero sum, the hardware zero sign equals the stated zero sign. -/
theorem fmaExactZeroSign {T : FTy} (x y z : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true)
    (hn : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
      z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int) = 0) :
    ((x.signbit != y.signbit) && z.signbit) =
      ((x.iszero || y.iszero) && z.iszero &&
        (x.signbit != y.signbit) && z.signbit) := by
  obtain ⟨hxd, hxp, hxn, hxzero⟩ :=
    JuliaLean.ChatGPT.Batch4.Group20.group20FiniteRatSigns x hx
  obtain ⟨hyd, hyp, hyn, hyzero⟩ :=
    JuliaLean.ChatGPT.Batch4.Group20.group20FiniteRatSigns y hy
  obtain ⟨hzd, hzp, hzn, hzzero⟩ :=
    JuliaLean.ChatGPT.Batch4.Group20.group20FiniteRatSigns z hz
  cases hsign : ((x.signbit != y.signbit) && z.signbit) with
  | false =>
      simp only [Bool.and_assoc, hsign, Bool.and_false]
  | true =>
      obtain ⟨hxy, hzs⟩ := Bool.and_eq_true_iff.mp hsign
      have hprod : x.toRat.1 * y.toRat.1 ≤ 0 := by
        cases hxs : x.signbit <;> cases hys : y.signbit
        · simp only [hxs, hys, bne_self_eq_false, Bool.false_eq_true] at hxy
        · exact Int.mul_nonpos_of_nonneg_of_nonpos (hxp hxs) (hyn hys)
        · exact Int.mul_nonpos_of_nonpos_of_nonneg (hxn hxs) (hyp hys)
        · simp only [hxs, hys, bne_self_eq_false, Bool.false_eq_true] at hxy
      have hprodTerm : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg hprod (Int.natCast_nonneg _)
      have hzTerm : z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int) ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg
          (Int.mul_nonpos_of_nonpos_of_nonneg (hzn hzs) (Int.natCast_nonneg _))
          (Int.natCast_nonneg _)
      have hprodZero : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) = 0 := by omega
      have hzTermZero : z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int) = 0 := by omega
      have hzdNe : (z.toRat.2 : Int) ≠ 0 := by omega
      have hxdNe : (x.toRat.2 : Int) ≠ 0 := by omega
      have hydNe : (y.toRat.2 : Int) ≠ 0 := by omega
      have hxyZero : x.toRat.1 * y.toRat.1 = 0 :=
        (Int.mul_eq_zero.mp hprodZero).resolve_right hzdNe
      have hzZero : z.toRat.1 = 0 :=
        (Int.mul_eq_zero.mp
          ((Int.mul_eq_zero.mp hzTermZero).resolve_right hydNe)).resolve_right hxdNe
      have hxyIsZero : (x.iszero || y.iszero) = true := by
        rcases Int.mul_eq_zero.mp hxyZero with h | h
        · simp only [hxzero h, Bool.true_or]
        · simp only [hyzero h, Bool.or_true]
      simp only [hxyIsZero, hzzero hzZero, Bool.true_and, hsign]

/-- The complete finite hardware formula, including exact cancellation and signed zero. -/
theorem fmaHardwareFiniteCorrect {T : FTy} (ops : FloatFmaOps) (x y z : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) (hz : z.isfinite = true)
    (huse : ops.haveFma T = true) :
    fma_IEEEFloat ops x y z =
      Fl.roundRat
        (x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
          z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int))
        (x.toRat.2 * y.toRat.2 * z.toRat.2)
        ((x.iszero || y.iszero) && z.iszero &&
          (x.signbit != y.signbit) && z.signbit) := by
  by_cases hn : x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
      z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int) = 0
  · have hraw := JuliaLean.ChatGPT.Batch4.Group20.group20HardwareFmaFiniteRaw
      ops x y z hx hy hz huse
    rw [fmaExactZeroSign x y z hx hy hz hn] at hraw
    simpa only [Int.natCast_mul, Int.mul_assoc] using hraw
  · exact JuliaLean.ChatGPT.Batch4.Group20.group20HardwareFmaFiniteNonzero
      ops x y z hx hy hz huse hn

/-- Hardware availability for each format is sufficient for the applied FMA property. -/
theorem fmaCorrectWhenHardwareAvailable (ops : FloatFmaOps)
    (huse : ∀ T, ops.haveFma T = true) : FmaCorrect ops := by
  intro T x y z hx hy hz
  exact fmaHardwareFiniteCorrect ops x y z hx hy hz (huse T)

/-- The software branch selected by the unchanged format dispatcher. -/
def emulatedFmaByFormat {T : FTy} (ops : FloatFmaOps) (x y z : FV T) : FV T :=
  match T with
  | .f16 => fmaEmulatedSmall (Or.inl rfl) ops.fma16 x y z
  | .f32 => fmaEmulatedSmall (Or.inr rfl) ops.fma32 x y z
  | .f64 => fma_emulated_Float64 ops.fma64 x y z

/-- The remaining software obligations only concern formats without hardware FMA. -/
def FmaEmulationObligations (ops : FloatFmaOps) : Prop :=
  ∀ (T : FTy) (x y z : FV T),
    ops.haveFma T = false →
    x.isfinite = true → y.isfinite = true → z.isfinite = true →
    emulatedFmaByFormat ops x y z =
      Fl.roundRat
        (x.toRat.1 * y.toRat.1 * (z.toRat.2 : Int) +
          z.toRat.1 * (x.toRat.2 : Int) * (y.toRat.2 : Int))
        (x.toRat.2 * y.toRat.2 * z.toRat.2)
        ((x.iszero || y.iszero) && z.iszero &&
          (x.signbit != y.signbit) && z.signbit)

/-- Applied FMA correctness is equivalent to exactly the outstanding software branches. -/
theorem fmaCorrectIffEmulation (ops : FloatFmaOps) :
    FmaCorrect ops ↔ FmaEmulationObligations ops := by
  constructor
  · intro h T x y z huse hx hy hz
    have hresult := h T x y z hx hy hz
    cases T <;> simpa only [fma_IEEEFloat, huse, Bool.false_eq_true, ite_false,
      emulatedFmaByFormat] using hresult
  · intro h T x y z hx hy hz
    cases huse : ops.haveFma T with
    | true => exact fmaHardwareFiniteCorrect ops x y z hx hy hz huse
    | false =>
      have hresult := h T x y z huse hx hy hz
      cases T <;> simpa only [fma_IEEEFloat, huse, Bool.false_eq_true, ite_false,
        emulatedFmaByFormat] using hresult

end JuliaLean.ChatGPT.Batch8.Group12
