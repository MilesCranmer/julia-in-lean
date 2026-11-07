import JuliaLean.base.float
import JuliaLean.Registry.Types

/-!
Coverage models for `base/float.jl` at Julia `bbfa0ce4150`.  The three IEEE
formats use `Promotion.Fl`, whose values are complete bit patterns and whose
finite values decode to exact rationals.
-/

namespace JuliaLean.FloatIntCov.Float

open JuliaLean
open JuliaLean.Promotion


def IntegerUabsBehavior : Prop :=
  ∀ x, integerUabs x = JuliaLean.IntArith.Division.uabs x

theorem integerUabsBehavior : IntegerUabsBehavior := by
  unfold IntegerUabsBehavior
  intros
  rfl


def FloatBitTraitBehavior : Prop :=
  (∀ (T : FTy) (x : FV T), (reinterpretUnsigned x).val =
    wrapInt (uintTy T) (Int.ofNat x.toBits)) ∧
  (∀ (T : FTy) (x : FV T), (reinterpretSigned x).val =
    wrapInt (intTy T) (Int.ofNat x.toBits)) ∧
  (∀ T, signMask T = 2 ^ (T.fmt.eb + T.fmt.sb)) ∧
  (∀ T, exponentMask T = T.fmt.emax * 2 ^ T.fmt.sb) ∧
  (∀ T, exponentOne T = T.fmt.bias * 2 ^ T.fmt.sb) ∧
  (∀ T, exponentHalf T = (T.fmt.bias - 1) * 2 ^ T.fmt.sb) ∧
  (∀ T, significandMask T = 2 ^ T.fmt.sb - 1) ∧
  (∀ T (x : FV T), mantissa x = x.toBits % 2 ^ T.fmt.sb) ∧
  (∀ T, significandBits T = T.fmt.sb) ∧
  (∀ T, exponentBits T = T.fmt.eb) ∧
  (∀ T, exponentBias T = T.fmt.bias) ∧
  (∀ T, exponentMax T = (T.fmt.emax : Int) - T.fmt.bias - 1) ∧
  (∀ T, exponentRawMax T = T.fmt.emax) ∧
  (∀ T, ieee754ExponentMin T = 1 - exponentMax T) ∧
  (∀ T, exponentMin T = 1 - exponentMax T)

theorem floatBitTraitBehavior : FloatBitTraitBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def IEEEConstructorBehavior : Prop :=
  (∀ T s e m, ieee754Representation T s e m = Fl.ofBits
    ((if s then 1 else 0) * 2 ^ (T.fmt.eb + T.fmt.sb) + e * 2 ^ T.fmt.sb + m)) ∧
  (∀ T s, ieeeOmega T s = ieee754Representation T s (T.fmt.emax - 1) (significandMask T)) ∧
  (∀ T s m, ieeeNanPayload T s m = ieee754Representation T s T.fmt.emax m) ∧
  (∀ T s, ieeeNan T s = ieeeNanPayload T s (2 ^ (T.fmt.sb - 1))) ∧
  (∀ T s, ieeeInf T s = ieeeNanPayload T s 0) ∧
  (∀ T s m, ieeeSubnormal T s m = ieee754Representation T s 0 m) ∧
  (∀ T s, ieeeZero T s = ieeeSubnormal T s 0)

theorem ieeeConstructorBehavior : IEEEConstructorBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def FloatConversionBehavior : Prop :=
  (∀ (α : Type) f (x : α), float16IntegerFallback f x = Fl.convert (f x)) ∧
  (∀ T t (x : JInt t), floatOfInteger T x = ofJInt T x) ∧
  (∀ T S (x : FV S), floatConvert T S x = Fl.convert x) ∧
  (∀ t (x : JInt t), abstractFloatOfInteger x = ofJInt .f64 x) ∧
  (∀ T t, floatPromoteRule T t = T) ∧
  (∀ T, floatWiden T = match T with | .f16 => .f32 | .f32 => .f64 | .f64 => .f64) ∧
  (∀ x, boolOfFloat16 x = if Fl.eq x (Fl.zero : FV .f16) then .ok false
    else if Fl.eq x (Fl.ofInt 1 : FV .f16) then .ok true
    else .error (.inexactError "Bool"))

theorem floatConversionBehavior : FloatConversionBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def FloatDispatchBehavior : Prop :=
  (∀ (α β : Type) (f : α → β) (x : α), floatScalar f x = f x) ∧
  (∀ (α β : Type) (z : α) (f : α → β), floatNumberType z f = f z) ∧
  (∀ T, floatAbstractType T = T) ∧
  floatBottomType = none ∧
  (∀ α : Type, floatBottomError (α := α) = .error (.methodError "float"))

theorem floatDispatchBehavior : FloatDispatchBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def UnsafeTruncBehavior : Prop :=
  ∀ T t (x : FV T), (unsafeTrunc T t x).val = wrapInt t x.truncVal

theorem unsafeTruncBehavior : UnsafeTruncBehavior := by
  unfold UnsafeTruncBehavior
  intros
  rfl


def CheckedFloatIntegerDispatch : Prop :=
  (∀ T t (x : FV T), checkedTrunc T t x = truncTo T t x) ∧
  (∀ T t (x : FV T), checkedInteger T t x = toInt T t x) ∧
  (∀ T (x : FV T), roundSigned T x = truncTo T .i64 x) ∧
  (∀ T (x : FV T), roundUnsigned T x = truncTo T .u64 x)

theorem checkedFloatIntegerDispatch : CheckedFloatIntegerDispatch := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def RoundDirectionBehavior : Prop :=
  (∀ s, roundsUp s .down = false) ∧ (∀ s, roundsUp s .up = true) ∧
  (∀ s, roundsUp s .toZero = s) ∧ (∀ s, roundsUp s .fromZero = !s) ∧
  (∀ (α : Type) convert lt gt next prev n (x : α) up,
    roundConvert convert lt gt next prev n x up =
      let xt := convert n
      if up then if lt xt x then next xt else xt
      else if gt xt x then prev xt else xt)

theorem roundDirectionBehavior : RoundDirectionBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def FloatPrimitiveDispatch : Prop :=
  ∀ T (ops : PrimitiveOps T) x y z, primitiveCalls ops x y z =
    (ops.neg x, ops.add x y, ops.sub x y, ops.mul x y, ops.div x y, ops.muladd x y z,
     ops.trunc x, ops.floor x, ops.ceil x, ops.nearest x)

theorem floatPrimitiveDispatch : FloatPrimitiveDispatch := by
  unfold FloatPrimitiveDispatch
  intros
  rfl


def FloatFieldExtraction : Prop :=
  (∀ T (x : FV T), unbiasedExponent x = x.expField) ∧
  (∀ T (x : FV T), explicitMantissa x = x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb)

theorem floatFieldExtraction : FloatFieldExtraction := by
  constructor <;> intros <;> rfl


def ToFloatFieldsBehavior : Prop :=
  ∀ T n ep, toFloatFields T n ep =
    let lz : Int := leadingZeros T.fmt.width n - T.fmt.eb
    let shifted := if lz ≥ 0 then n * 2 ^ lz.toNat else n / 2 ^ (-lz).toNat
    let ep := ep - lz
    let bits := if ep ≥ 0 then
        shifted % 2 ^ T.fmt.sb + ((ep + 1).toNat * 2 ^ T.fmt.sb) % (2 ^ T.fmt.width)
      else (shifted / 2 ^ (-ep).toNat) % 2 ^ T.fmt.sb
    Fl.ofBits bits

theorem toFloatFieldsBehavior : ToFloatFieldsBehavior := by
  unfold ToFloatFieldsBehavior
  intros
  rfl


def FloatRemainderBehavior : Prop :=
  (∀ T (x y : FV T), remInternal x y =
    let a := x.toRat
    let b := y.toRat
    let q := (a.1 * (b.2 : Int)).tdiv (b.1 * (a.2 : Int))
    Fl.roundRat (a.1 * (b.2 : Int) - b.1 * (a.2 : Int) * q) (a.2 * b.2) x.signbit) ∧
  (∀ T (x y : FV T), rem x y = if x.isfinite && !x.iszero && y.isfinite && !y.iszero
    then remInternal x y else if x.isinf || y.isnan || y.iszero then Fl.nan else x) ∧
  (∀ T (x y : FV T), mod x y = if y.isinf && x.isfinite then x else
    let r := rem x y
    if r.iszero then Fl.zero y.signbit
    else if Fl.lt (Fl.zero) r != Fl.lt (Fl.zero) y then Fl.add r y else r)

theorem floatRemainderBehavior : FloatRemainderBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def FloatComparisonBehavior : Prop :=
  ∀ T (x y : FV T),
    Fl.eq x y = Fl.eq x y ∧ Fl.lt x y = Fl.lt x y ∧ Fl.le x y = Fl.le x y ∧
    Fl.isequal x y = Fl.isequal x y ∧
    fpKey x = (let i := (reinterpretSigned x).val
      if i < 0 then -(2 ^ (T.fmt.width - 1) : Int) - 1 - i else i) ∧
    Fl.isless x y = Fl.isless x y

theorem floatComparisonBehavior : FloatComparisonBehavior := by
  unfold FloatComparisonBehavior
  intros
  simp [fpKey]


def MixedComparisonDispatch : Prop :=
  ∀ T t (x : FV T) (y : JInt t), mixedComparisons x y =
    (cmpFI .eq x y, cmpFI .lt x y, cmpFI .le x y,
     cmpIF .eq y x, cmpIF .lt y x, cmpIF .le y x)

theorem mixedComparisonDispatch : MixedComparisonDispatch := by
  unfold MixedComparisonDispatch
  intros
  rfl


def FloatClassificationBehavior : Prop :=
  ∀ T (x : FV T),
    floatAbs x = Fl.ofBits x.magnitude ∧
    x.isnan = (x.expField == T.fmt.emax && x.frac != 0) ∧
    x.isfinite = (x.expField != T.fmt.emax) ∧
    x.isinf = (x.expField == T.fmt.emax && x.frac == 0)

theorem floatClassificationBehavior : FloatClassificationBehavior := by
  unfold FloatClassificationBehavior
  intro T x
  simp [floatAbs, Fl.isnan, Fl.isfinite, Fl.isinf]


def GenericClassificationBehavior : Prop :=
  (∀ (α : Type) ne (x : α), abstractIsnan ne x = ne x x) ∧
  (∀ (α : Type) sub isnan (x : α), abstractIsfinite sub isnan x = !isnan (sub x x)) ∧
  (∀ (α : Type) (x : α), genericIsnanNumber x = false) ∧
  (∀ (α : Type) decomp (x : α), genericIsfiniteReal decomp x = ((decomp x).2.2 != 0)) ∧
  (∀ x, genericIsfiniteInteger x = true) ∧
  (∀ (α : Type) p q (x : α), genericIsinfReal p q x = (!p x && !q x))

theorem genericClassificationBehavior : GenericClassificationBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def DecomposeBehavior : Prop :=
  (∀ x : Int, decomposeInteger x = (x, 0, 1)) ∧
  (∀ T (x : FV T), decompose x = if x.isnan then (0, 0, 0)
    else if x.isinf then (if x.signbit then -1 else 1, 0, 0)
    else
      let e := x.expField
      let s := x.frac + if e = 0 then 0 else 2 ^ T.fmt.sb
      ((s : Int), (e : Int) - T.fmt.bias - T.fmt.sb + if e = 0 then 1 else 0,
        if x.signbit then -1 else 1))

theorem decomposeBehavior : DecomposeBehavior := by
  constructor <;> intros <;> rfl


def PrecisionBehavior : Prop :=
  (∀ T, precision2 T = T.fmt.sb + 1) ∧
  (∀ log2 T b, precisionBase log2 T b = if b < 2 then .error (.domainError "base")
    else if b = 2 then .ok (precision2 T) else .ok (precision2 T / log2 b)) ∧
  (∀ α : Type, precisionBottom (α := α) = .error (.methodError "precision"))

theorem precisionBehavior : PrecisionBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def NextPrevFloatBehavior : Prop :=
  (∀ T (x : FV T) d, nextFloat T x d = nextFloatRaw T x (decide (d < 0)) d.natAbs) ∧
  (∀ T (x : FV T) d, prevFloat T x d = nextFloatRaw T x (decide (d > 0)) d.natAbs) ∧
  (∀ T (x : FV T), nextFloat T x = nextFloat T x 1) ∧
  (∀ T (x : FV T), prevFloat T x = nextFloat T x (-1))

theorem nextPrevFloatBehavior : NextPrevFloatBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def FloatIntegerPredicateBehavior : Prop :=
  (∀ T (x : FV T), isSubnormal x = (x.expField == 0 && x.frac != 0)) ∧
  (∀ T (x : FV T), isPow2 x = (!x.signbit && !x.iszero && x.isfinite &&
    (if x.expField = 0 then natCountOnes T.fmt.sb x.frac = 1 else x.frac = 0))) ∧
  (∀ T (x : FV T), isEvenFloat x = (x.isinteger && x.truncVal % 2 = 0)) ∧
  (∀ T (x : FV T), isOddFloat x = (x.isinteger && x.truncVal % 2 != 0))

theorem floatIntegerPredicateBehavior : FloatIntegerPredicateBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def FloatLimitBehavior : Prop :=
  (∀ T, typeMin T = Fl.inf true) ∧ (∀ T, typeMax T = Fl.inf false) ∧
  (∀ T, floatMin T = Fl.ofBits (2 ^ T.fmt.sb)) ∧ (∀ T, floatMax T = Fl.floatmax) ∧
  (∀ T, typeEps T = Fl.ofBits ((T.fmt.bias - T.fmt.sb) * 2 ^ T.fmt.sb)) ∧
  (∀ T sub (x : FV T), valueEps sub x = floatAbs (sub x (Fl.ofBits (Nat.xor x.toBits 1)))) ∧
  (∀ (α β : Type) (typeOf : α → β) (limit : β → α) (x : α),
    limitOfValue typeOf limit x = limit (typeOf x)) ∧
  (∀ (α : Type) (x : α), defaultLimit x = x) ∧
  (∀ (α : Type) name, limitBottom (α := α) name = .error (.methodError name)) ∧
  (∀ (α : Type) (finite ge : α → Bool) (fmin ld nxt zero nan abs : α → α) (x : α),
    genericEps finite ge fmin ld nxt zero nan abs x =
      if finite x then if ge (abs x) then ld x else nxt (zero x) else nan x)

theorem floatLimitBehavior : FloatLimitBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl


def FloatStorageTraitBehavior : Prop :=
  (∀ T (x : FV T), bswap x = Fl.ofBits ((List.range (T.fmt.width / 8)).foldl (fun out j =>
    out + (x.toBits / 2 ^ (8*j) % 256) * 2 ^ (8 * (T.fmt.width / 8 - 1 - j))) 0)) ∧
  (∀ T, uintTy T = match T with | .f16 => .u16 | .f32 => .u32 | .f64 => .u64) ∧
  (∀ T, intTy T = match T with | .f16 => .i16 | .f32 => .i32 | .f64 => .i64) ∧
  (∀ t, floatType t = match t with | .u16 | .i16 => .f16 | .u32 | .i32 => .f32 | _ => .f64)

theorem floatStorageTraitBehavior : FloatStorageTraitBehavior := by
  repeat' apply And.intro
  all_goals intros <;> first | rfl | (cases T <;> rfl) | (cases t <;> rfl)


def FloatCollectionBehavior : Prop :=
  (∀ (α β : Type) (f : α → β) (xs : List α), floatArray f xs = xs.map f) ∧
  (∀ (α : Type) (xs : List α), floatArrayAlready xs = xs) ∧
  (∀ (α β : Type) concrete (convert : List α → Jl (List β)) (xs : List α),
    floatArrayGeneric concrete convert xs =
    if concrete then convert xs else .error (.argumentError "abstract element type")) ∧
  (∀ (α β : Type) (f : α → β) (r : RangeModel α), floatRange f r =
    ⟨f r.start, f r.step, f r.stop, r.length, r.offset⟩)

theorem floatCollectionBehavior : FloatCollectionBehavior := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.FloatIntCov.Float
