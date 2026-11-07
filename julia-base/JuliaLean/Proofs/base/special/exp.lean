import JuliaLean.base.special.exp
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.special.exp
open JuliaLean JuliaLean.Promotion JuliaLean.MathCov JuliaLean.MathCov.FP
open JuliaLean.MathFuncs (ExpBase)
open JuliaLean.base.special.exp JuliaLean.Registry

def PositiveFinite {T : FTy} (x : FV T) : Prop :=
  x.isfinite = true ∧ x.signbit = false ∧ x.iszero = false

def NegativeFinite {T : FTy} (x : FV T) : Prop :=
  x.isfinite = true ∧ x.signbit = true ∧ x.iszero = false

def ReductionThresholds : Prop :=
  magicRoundConst64.toRat.1 = 6755399441055744 * (magicRoundConst64.toRat.2 : Int) ∧
  magicRoundConst32.toRat.1 = 10485760 * (magicRoundConst32.toRat.2 : Int) ∧
  ∀ b : ExpBase,
    PositiveFinite (maxExp64 b) ∧ PositiveFinite (maxExp32 b) ∧
    NegativeFinite (minExp64 b) ∧ NegativeFinite (minExp32 b) ∧
    PositiveFinite (subnormExp64 b) ∧ PositiveFinite (subnormExp32 b) ∧
    FP.lt (subnormExp64 b) (maxExp64 b) = true ∧
    FP.lt (subnormExp32 b) (maxExp32 b) = true

def LogarithmicReductionConstants : Prop :=
  ∀ b : ExpBase,
    PositiveFinite (logBo256Inv b) ∧ NegativeFinite (logBo256U b) ∧
    PositiveFinite (logBInv32 b) ∧ NegativeFinite (logBU32 b) ∧
    NegativeFinite (logB16 b) ∧
    (match b with
      | .two => (logBo256L b).iszero = true ∧ (logBL32 b).iszero = true
      | .e | .ten => NegativeFinite (logBo256L b) ∧ NegativeFinite (logBL32 b))

def ReducedKernel64Sign : Prop :=
  ∀ (b : ExpBase) (x : F64),
    x.isfinite = true → FP.le (FP.abs x) (Fl.ofBits 0x3f70000000000000) = true →
    (expm1bKernel b x).isfinite = true ∧ (expm1bKernel b x).signbit = x.signbit

def ReducedKernel32Range : Prop :=
  ∀ (b : ExpBase) (x : F32),
    x.isfinite = true → FP.le (FP.abs x) (Fl.ofBits 0x3b800000) = true →
    (expbKernel32 b x).isfinite = true ∧
    FP.lt (FP.zero .f32) (expbKernel32 b x) = true

def TableValueRanges : Prop :=
  ∀ ind : JInt .i32,
    let (hi, lo) := tableUnpack ind
    hi.isfinite = true ∧ lo.isfinite = true ∧
    FP.le (FP.ofInt .f64 1) hi = true ∧ FP.lt hi (FP.ofInt .f64 2) = true ∧
    FP.lt (FP.zero .f64) lo = true ∧
    FP.lt lo (Fl.ofBits 0x3cc0000000000000) = true

def Exponential64Nonnegative : Prop :=
  ∀ (b : ExpBase) (x : F64), x.isnan = false →
    (expImpl64 x b).isnan = false ∧ (expImpl64 x b).signbit = false

def Exponential32Nonnegative : Prop :=
  ∀ (b : ExpBase) (x : F32), x.isnan = false →
    (expImpl32 x b).isnan = false ∧ (expImpl32 x b).signbit = false

def Exponential16Nonnegative : Prop :=
  ∀ (b : ExpBase) (x : FV .f16), x.isnan = false →
    (expImpl16 x b).isnan = false ∧ (expImpl16 x b).signbit = false

def ExtendedExponentialExceptionalValues : Prop :=
  ∀ (b : ExpBase) (x lo : F64),
    (x.isnan = true → expImpl64Lo x lo b = x) ∧
    (FP.le (maxExp64 b) x = true → expImpl64Lo x lo b = FP.inf .f64) ∧
    (FP.le x (minExp64 b) = true → expImpl64Lo x lo b = FP.zero .f64)

def FastExponentialNonnegative : Prop :=
  (∀ (b : ExpBase) (x : F64), x.isnan = false →
    (expImplFast64 x b).isnan = false ∧ (expImplFast64 x b).signbit = false) ∧
  (∀ (b : ExpBase) (x : F32), x.isnan = false →
    (expImplFast32 x b).isnan = false ∧ (expImplFast32 x b).signbit = false)

def PublicExponentialNonnegative : Prop :=
  ∀ (T : FTy) (x : FV T), x.isnan = false →
    (exp2 x).isnan = false ∧ (exp2 x).signbit = false ∧
    (exp x).isnan = false ∧ (exp x).signbit = false ∧
    (exp10 x).isnan = false ∧ (exp10 x).signbit = false

def IntegerPowerOfTwo : Prop :=
  ∀ (t : IntTy) (x : JInt t),
    (1023 < x.val → exp2Int x = FP.inf .f64) ∧
    (x.val < -1074 → exp2Int x = FP.zero .f64) ∧
    (-1074 ≤ x.val → x.val ≤ 1023 →
      let result := (exp2Int x).toRat
      if 0 ≤ x.val then result.1 = (2 ^ x.val.toNat : Int) * (result.2 : Int)
      else result.1 * (2 ^ (-x.val).toNat : Int) = (result.2 : Int))

theorem reductionThresholds_proven : ReductionThresholds := by
  refine ⟨by decide, by decide, ?_⟩
  intro b
  cases b <;> unfold PositiveFinite NegativeFinite <;> decide

theorem logarithmicReductionConstants_proven : LogarithmicReductionConstants := by
  intro b
  cases b <;> dsimp only <;> unfold PositiveFinite NegativeFinite <;> decide



open JuliaLean JuliaLean.Promotion JuliaLean.MathCov JuliaLean.MathCov.FP
open JuliaLean.base.special.exp

def Expm1ReductionConstants : Prop :=
  PositiveFinite expm1Limits.max64 ∧ NegativeFinite expm1Limits.min64 ∧
  PositiveFinite expm1Limits.max32 ∧ NegativeFinite expm1Limits.min32 ∧
  PositiveFinite expm1Limits.max16 ∧ NegativeFinite expm1Limits.min16 ∧
  PositiveFinite ln2Values.inv64 ∧ NegativeFinite ln2Values.neg64 ∧
  PositiveFinite ln2Values.inv32 ∧ NegativeFinite ln2Values.neg32

theorem expm1ReductionConstants_proven : Expm1ReductionConstants := by
  unfold Expm1ReductionConstants PositiveFinite NegativeFinite
  decide

def Expm1Small64Sign : Prop :=
  ∀ (haveFma : FTy → Bool) (x : F64),
    FP.le (Fl.ofBits 0xbfd269621134db92) x = true →
    FP.le x (Fl.ofBits 0x3fcc8ff7c79a9a22) = true →
    (expm1Small64With haveFma x).isfinite = true ∧
    (expm1Small64With haveFma x).signbit = x.signbit

def Expm1Small32Sign : Prop :=
  ∀ (haveFma : FTy → Bool) (x : F32),
    FP.le (Fl.ofBits 0xbe934b11) x = true → FP.le x (Fl.ofBits 0x3e647fbe) = true →
    (expm1Small32With haveFma x).isfinite = true ∧
    (expm1Small32With haveFma x).signbit = x.signbit

def Expm164Range : Prop :=
  ∀ (haveFma : FTy → Bool) (x : F64), x.isnan = false →
    (expm164With haveFma x).isnan = false ∧
    FP.le (FP.ofInt .f64 (-1)) (expm164With haveFma x) = true

def Expm132Range : Prop :=
  ∀ (haveFma : FTy → Bool) (x : F32), x.isnan = false →
    (expm1_32With haveFma x).isnan = false ∧
    FP.le (FP.ofInt .f32 (-1)) (expm1_32With haveFma x) = true

def Expm116Range : Prop :=
  ∀ x : FV .f16, x.isnan = false →
    (expm1_16 x).isnan = false ∧ FP.le (FP.ofInt .f16 (-1)) (expm1_16 x) = true

def PublicFastExponentialNonnegative : Prop :=
  (∀ x : F32, x.isnan = false →
    (exp2Fast32 x).isnan = false ∧ (exp2Fast32 x).signbit = false ∧
    (expFast32 x).isnan = false ∧ (expFast32 x).signbit = false ∧
    (exp10Fast32 x).isnan = false ∧ (exp10Fast32 x).signbit = false) ∧
  (∀ x : F64, x.isnan = false →
    (exp2Fast64 x).isnan = false ∧ (exp2Fast64 x).signbit = false ∧
    (expFast64 x).isnan = false ∧ (expFast64 x).signbit = false ∧
    (exp10Fast64 x).isnan = false ∧ (exp10Fast64 x).signbit = false)

open JuliaLean.Registry

def entries : List Entry := [
  { id := "exp-reduction-thresholds", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAGIC_ROUND_CONST", "MAX_EXP", "MIN_EXP", "SUBNORM_EXP"]
    statement := "The rounding offsets have their exact integer values and the exponential overflow, underflow and subnormal thresholds have the required signs and order."
    source := "base/special/exp.jl:6-33", status := .proven
    prop := ``ReductionThresholds, thm := some ``reductionThresholds_proven },
  { id := "exp-logarithmic-reduction-constants", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256INV", "LogBo256U", "LogBo256L", "LogBINV", "LogBU", "LogBL", "LogB"]
    statement := "Logarithmic range-reduction constants are finite with the expected signs, and base-two low corrections are zero."
    source := "base/special/exp.jl:36-70", status := .proven
    prop := ``LogarithmicReductionConstants, thm := some ``logarithmicReductionConstants_proven },
  { id := "exp-reduced-kernel64-sign", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1b_kernel"]
    statement := "For every finite reduced argument with magnitude at most 2^-8, the Float64 exponential-minus-one kernel is finite and has the input sign."
    source := "base/special/exp.jl:73-84", status := .todo
    prop := ``ReducedKernel64Sign },
  { id := "exp-reduced-kernel32-range", juliaFile := "base/special/exp.jl"
    juliaFns := ["expb_kernel"]
    statement := "For every finite reduced argument with magnitude at most 2^-8, the Float32 exponential kernel is positive and finite."
    source := "base/special/exp.jl:86-100", status := .todo
    prop := ``ReducedKernel32Range },
  { id := "exp-table-value-ranges", juliaFile := "base/special/exp.jl"
    juliaFns := ["table_unpack"]
    statement := "For every Int32 index, table unpacking returns a finite high component in [1,2) and a positive finite low component below 2^-51."
    source := "base/special/exp.jl:178-184", status := .todo
    prop := ``TableValueRanges },
  { id := "exp-float64-nonnegative", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(::Float64,base)"]
    statement := "For every non-NaN Float64 input and exponential base, the result is non-NaN and nonnegative."
    source := "base/special/exp.jl:207-231", status := .todo
    prop := ``Exponential64Nonnegative },
  { id := "exp-extended-exceptional-values", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(::Float64,::Float64,base)"]
    statement := "The extended Float64 exponential preserves NaN inputs and returns positive infinity or zero at the overflow and underflow thresholds, independently of the low component."
    source := "base/special/exp.jl:233-259", status := .todo
    prop := ``ExtendedExponentialExceptionalValues },
  { id := "exp-fast-nonnegative", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl_fast"]
    statement := "For every non-NaN Float32 or Float64 input and exponential base, the fast exponential result is non-NaN and nonnegative."
    source := "base/special/exp.jl:260-274,297-308", status := .todo
    prop := ``FastExponentialNonnegative },
  { id := "exp-float32-nonnegative", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(::Float32,base)"]
    statement := "For every non-NaN Float32 input and exponential base, the result is non-NaN and nonnegative."
    source := "base/special/exp.jl:276-295", status := .todo
    prop := ``Exponential32Nonnegative },
  { id := "exp-float16-nonnegative", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(::Float16,base)"]
    statement := "For every non-NaN Float16 input and exponential base, the result is non-NaN and nonnegative."
    source := "base/special/exp.jl:310-323", status := .todo
    prop := ``Exponential16Nonnegative },
  { id := "exp-public-nonnegative", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp2", "exp", "exp10"]
    statement := "For every non-NaN native floating input, public exponential functions return non-NaN nonnegative values."
    source := "base/special/exp.jl:329", status := .todo
    prop := ``PublicExponentialNonnegative },
  { id := "exp-public-fast-nonnegative", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp2_fast", "exp_fast", "exp10_fast"]
    statement := "For every non-NaN Float32 or Float64 input, public fast exponential functions return non-NaN nonnegative values."
    source := "base/special/exp.jl:330", status := .todo
    prop := ``PublicFastExponentialNonnegative },
  { id := "exp-integer-power-of-two", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp2(::BitInteger)"]
    statement := "Integer exp2 returns the exact representable power of two, positive infinity above exponent 1023, and zero below exponent -1074."
    source := "base/special/exp.jl:391-405", status := .todo
    prop := ``IntegerPowerOfTwo },
  { id := "exp-expm1-reduction-constants", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP", "MIN_EXP", "Ln2INV", "Ln2"]
    statement := "Exponential-minus-one limits and logarithm constants are finite with the required signs in every native floating format."
    source := "base/special/exp.jl:408-418", status := .proven
    prop := ``Expm1ReductionConstants, thm := some ``expm1ReductionConstants_proven },
  { id := "exp-expm1-small64-sign", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1_small(::Float64)"]
    statement := "Across its complete reduction interval, the Float64 small exponential-minus-one kernel is finite and preserves input sign with or without hardware FMA."
    source := "base/special/exp.jl:421-427", status := .todo
    prop := ``Expm1Small64Sign },
  { id := "exp-expm1-small32-sign", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1_small(::Float32)"]
    statement := "Across its complete reduction interval, the Float32 small exponential-minus-one kernel is finite and preserves input sign with or without hardware FMA."
    source := "base/special/exp.jl:428-433", status := .todo
    prop := ``Expm1Small32Sign },
  { id := "exp-expm1-float64-range", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1(::Float64)"]
    statement := "Every non-NaN Float64 input produces a non-NaN exponential-minus-one value at least -1, with either hardware-FMA setting."
    source := "base/special/exp.jl:435-459", status := .todo
    prop := ``Expm164Range },
  { id := "exp-expm1-float32-range", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1(::Float32)"]
    statement := "Every non-NaN Float32 input produces a non-NaN exponential-minus-one value at least -1, with either hardware-FMA setting."
    source := "base/special/exp.jl:461-476", status := .todo
    prop := ``Expm132Range },
  { id := "exp-expm1-float16-range", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1(::Float16)"]
    statement := "Every non-NaN Float16 input produces a non-NaN exponential-minus-one value at least -1."
    source := "base/special/exp.jl:478-492", status := .todo
    prop := ``Expm116Range }
]

end JuliaLean.Proofs.base.special.exp
