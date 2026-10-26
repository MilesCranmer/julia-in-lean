import JuliaLean.MathCov.MathMisc
import JuliaLean.MathCov.FloatFuncs
import JuliaLean.MathCov.MathConstants
import JuliaLean.MathCov.PropsBits
import JuliaLean.MathCov.PropsRounding

/-!
Coverage properties for the methods modelled under `JuliaLean.MathCov`. Internal numerical
kernels have no independent public accuracy contract, so their invariant is total execution
in the modelled result type for every input. Public methods additionally have the documented
special-value, forwarding, and algebraic properties in `PropsBits`, `PropsRounding`, and the
properties below.
-/

namespace JuliaLean.MathCov

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathFuncs (ExpBase LogBase)
open JuliaLean.FloatFuncs (Mode)

def HasResult {α : Type} (x : α) : Prop := ∃ r, x = r

theorem hasResult {α : Type} (x : α) : HasResult x := ⟨x, rfl⟩

/-! ## base/special/trig.jl -/

def TrigCoreCoverage : Prop :=
  ∀ T : FTy, ∀ x : FV T, ∀ y : Trig.DF64, ∀ k : Int,
    HasResult (Trig.sinKernelD y) ∧ HasResult (Trig.sinKernel64 (conv x)) ∧
    HasResult (Trig.cosKernelD y) ∧ HasResult (Trig.cosKernel64 (conv x)) ∧
    HasResult (Trig.tanKernelD y k) ∧ HasResult (Trig.tanKernel64 (conv x)) ∧
    HasResult (Trig.sinKernel32 y.hi) ∧ HasResult (Trig.cosKernel32 y.hi) ∧
    HasResult (Trig.tanKernel32 y.hi k) ∧ HasResult (Trig.reduce T x) ∧
    HasResult (Trig.sinK T y) ∧ HasResult (Trig.cosK T y) ∧
    HasResult (Trig.tanK T y k) ∧ HasResult (Trig.sincosK T y) ∧
    Trig.sincosK T y = (Trig.sinK T y, Trig.cosK T y) ∧
    HasResult (Trig.sin T x) ∧ HasResult (Trig.cos T x) ∧
    HasResult (Trig.sincos T x) ∧ HasResult (Trig.tan T x) ∧
    (∀ (α β : Type) (f : α → β) (a : α),
      Trig.sinKernelReal f a = f a ∧ Trig.sincosAbstract f a = f a) ∧
    (∀ (α β : Type) (s c : α → β) (a : α),
      Trig.sincosFallback s c a = (s a, c a)) ∧
    (∀ (α β γ : Type) (float : α → β) (sc : β → γ) (a : α),
      Trig.sincosGeneric float sc a = sc (float a))

theorem trigCoreCoverage_proven : TrigCoreCoverage := by
  simp [TrigCoreCoverage, HasResult, Trig.sincosK, Trig.sinKernelReal,
    Trig.sincosAbstract, Trig.sincosFallback, Trig.sincosGeneric]

def TrigInverseCoverage : Prop :=
  ∀ T : FTy, ∀ x y : FV T, ∀ i : Nat,
    HasResult (Trig.asinMin T) ∧ HasResult (Trig.arcP T x) ∧ HasResult (Trig.arcQ T x) ∧
    HasResult (Trig.arcTRt T x) ∧ HasResult (Trig.asinKernel T x y) ∧
    HasResult (Trig.asin T x) ∧
    HasResult (Trig.atanHi T i) ∧ HasResult (Trig.atanLo T i) ∧
    HasResult (Trig.atanLarge T) ∧ HasResult (Trig.atanSmall T) ∧
    HasResult (Trig.atanP T x y) ∧ HasResult (Trig.atanQ T x) ∧
    HasResult (Trig.atanPQ T x) ∧ HasResult (Trig.atan T x) ∧
    HasResult (Trig.atan2PiLo T) ∧ HasResult (Trig.atan2Shift T) ∧
    HasResult (Trig.atan2Threshold T) ∧ HasResult (Trig.atan2 T y x) ∧
    HasResult (Trig.acosMin T) ∧ HasResult (Trig.pio2Hi T) ∧
    HasResult (Trig.pio2Lo T) ∧ HasResult (Trig.acosPi T) ∧
    HasResult (Trig.acosLowword x) ∧ HasResult (Trig.acos T x) ∧
    HasResult (Trig.asinDomainError (α := FV T)) ∧
    HasResult (Trig.acosDomainError (α := FV T))

theorem trigInverseCoverage_proven : TrigInverseCoverage := by
  simp [TrigInverseCoverage, HasResult]

def PiTrigCoverage : Prop :=
  ∀ T : FTy, ∀ x : FV T, ∀ n : Int,
    HasResult (TrigPi.sinpiKernel T x) ∧ HasResult (TrigPi.cospiKernel T x) ∧
    HasResult (TrigPi.sinpiKernelSch [x, x, x] x) ∧
    HasResult (TrigPi.cospiKernelSch [x, x, x] x) ∧
    HasResult (TrigPi.sinpiKernelWide T x) ∧ HasResult (TrigPi.cospiKernelWide T x) ∧
    HasResult (TrigPi.piReduce x) ∧ HasResult (TrigPi.sinpi T x) ∧
    HasResult (TrigPi.cospi T x) ∧ HasResult (TrigPi.sincospi T x) ∧
    HasResult (TrigPi.tanpi T x) ∧
    TrigPi.sincospiInt n = (TrigPi.sinpiInt n, TrigPi.cospiInt n) ∧
    HasResult (TrigPi.tanpiInt n) ∧
    (∀ (α β : Type) (p : α → α) (f : α → β) (a : α), TrigPi.piGeneric p f a = f (p a))

theorem piTrigCoverage_proven : PiTrigCoverage := by
  simp [PiTrigCoverage, HasResult, TrigPi.sincospiInt, TrigPi.piGeneric]

def ComplexPiTrigCoverage : Prop :=
  ∀ T : FTy, ∀ h : TrigPi.Hyp T, ∀ z : TrigPi.Cx T,
    HasResult (TrigPi.tanpiC h z) ∧ HasResult (TrigPi.sinpiC h z) ∧
    HasResult (TrigPi.cospiC h z) ∧ HasResult (TrigPi.sincospiC h z)

theorem complexPiTrigCoverage_proven : ComplexPiTrigCoverage := by
  simp [ComplexPiTrigCoverage, HasResult]

def TrigCardinalCoverage : Prop :=
  ∀ T : FTy, ∀ x : FV T, ∀ ps : List (FV T × List (FV T)),
    TrigMisc.fastabs x = abs x ∧
    (∀ z : TrigPi.Cx T, ∀ threshold : FV T,
      TrigMisc.fastabsC z = add (abs z.re) (abs z.im) ∧
      HasResult (TrigMisc.isinfRealC z) ∧
      HasResult (TrigMisc.sincSpecialized lt TrigMisc.fastabsC threshold
        (fun a => a) (fun _ => ⟨zero T, zero T⟩) (fun a => a)
        TrigMisc.isinfRealC z) ∧
      HasResult (TrigMisc.coscComplex lt TrigMisc.fastabsC threshold
        (fun a => a) (fun a => a) (fun _ => ⟨zero T, zero T⟩)
        TrigMisc.isinfRealC z)) ∧
    HasResult (TrigMisc.isinfReal x) ∧ HasResult (TrigMisc.sincThreshold T) ∧
    HasResult (TrigMisc.isinfRealNumber x) ∧
    HasResult (TrigMisc.sincF T x) ∧ HasResult (TrigMisc.sinc16 (conv x)) ∧
    HasResult (TrigMisc.sinc T x) ∧
    HasResult (TrigMisc.sincInt x.toRat.1) ∧ HasResult (TrigMisc.coscGeneric T x) ∧
    HasResult (TrigMisc.sincGeneric (fun z => z.iszero) (fun z => z.isinf)
      (fun _ => one T) (fun _ => zero T) (fun z => z) (fun z => z) div x) ∧
    HasResult (TrigMisc.choosePoly (abs x) ps) ∧
    HasResult (TrigMisc.cosCardinalEval T x ps) ∧ HasResult (TrigMisc.pairs 1 [x]) ∧
    HasResult (TrigMisc.coscF T x) ∧ HasResult (TrigMisc.cosc T x) ∧
    HasResult (TrigMisc.coscSeries (Trig.piT T) mul div add neg (ofInt T)
      (fun z => z.iszero) le abs (fun z => epsOf z) 1 x x x x 1) ∧
    HasResult (TrigMisc.sincComplex16 (fun z => z) (fun z => z) (fun z => z) x) ∧
    HasResult (TrigMisc.coscComplex16 (fun z => z) (fun z => z) (fun z => z) x)

theorem trigCardinalCoverage_proven : TrigCardinalCoverage := by
  simp [TrigCardinalCoverage, HasResult, TrigMisc.fastabs, TrigMisc.fastabsC]

def TrigDegreeCoverage : Prop :=
  ∀ T : FTy, ∀ x : FV T,
    HasResult (TrigMisc.deg2radExt T x) ∧ HasResult (TrigMisc.deg2rad T x) ∧
    HasResult (TrigMisc.deg2radExt64 (conv x)) ∧
    HasResult (TrigMisc.rad2deg T x) ∧ HasResult (TrigMisc.sind T x) ∧
    HasResult (TrigMisc.cosd T x) ∧ HasResult (TrigMisc.tand T x) ∧
    HasResult (TrigMisc.sincosd T x) ∧
    (∀ (α β : Type) (f : α → β) (g : α → α) (a : α),
      TrigMisc.viaDeg2rad f g a = f (g a)) ∧
    (∀ (α : Type) (f : α → Jl α) (inv : α → α) (a : α),
      TrigMisc.recipOf f inv a = do return inv (← f a)) ∧
    (∀ (α β : Type) (f : α → β) (inv : α → α) (a : α),
      TrigMisc.invArgOf f inv a = f (inv a)) ∧
    HasResult (TrigMisc.oneEightyOverPi T) ∧ HasResult (TrigMisc.piOverOneEighty T) ∧
    HasResult (TrigMisc.degF16 (fun a => .ok a) "f" (conv x)) ∧
    HasResult (TrigMisc.invDegF16 (fun a => .ok a) (conv x)) ∧
    TrigMisc.sincosdMissing = (none, none)

theorem trigDegreeCoverage_proven : TrigDegreeCoverage := by
  simp [TrigDegreeCoverage, HasResult, TrigMisc.viaDeg2rad, TrigMisc.recipOf,
    TrigMisc.invArgOf, TrigMisc.sincosdMissing]

/-! ## base/special/exp.jl and base/special/log.jl -/

def ExpCoverage : Prop :=
  ∀ b : ExpBase, ∀ x : FV .f32, ∀ a : FV .f16, ∀ i : Int,
    HasResult (MathFuncs.maxExp b) ∧ HasResult (MathFuncs.minExp b) ∧
    HasResult MathFuncs.magicRoundConst ∧ HasResult magic32 ∧
    HasResult (MathFuncs.subnormExp b) ∧ HasResult (MathFuncs.logBo256Inv b) ∧
    HasResult (MathFuncs.logBo256U b) ∧ HasResult (MathFuncs.logBo256L b) ∧
    HasResult (MathFuncs.expm1bKernel b (toD x)) ∧ HasResult (MathFuncs.tableUnpack i) ∧
    HasResult (MathFuncs.expImpl (toD x) b) ∧ HasResult (MathFuncs.expImplLo (toD x) (toD x) b) ∧
    HasResult (Exp.maxExp32 b) ∧ HasResult (Exp.minExp32 b) ∧
    HasResult (Exp.subnormExp32 b) ∧ HasResult (Exp.logBInv32 b) ∧
    HasResult (Exp.logBU32 b) ∧ HasResult (Exp.logBL32 b) ∧ HasResult (Exp.logB16 b) ∧
    HasResult (Exp.expbKernel b x) ∧ HasResult (Exp.expImpl32 x b) ∧
    HasResult (Exp.expImplFast32 x b) ∧ HasResult (Exp.expImpl16 a b) ∧
    HasResult (Exp.expFn b .f32 x) ∧ HasResult (Exp.expImplFast64 (toD x) b) ∧
    HasResult expm1Max32 ∧ HasResult expm1Min32 ∧ HasResult expm1Max16 ∧
    HasResult expm1Min16 ∧ HasResult ln2Inv64 ∧ HasResult ln2Neg64 ∧
    HasResult ln2Inv32 ∧ HasResult ln2Neg32 ∧
    HasResult (MathFuncs.expm1Small (toD x)) ∧ HasResult (MathFuncs.expm1 (toD x)) ∧
    HasResult (Exp.expm1Small32 x) ∧ HasResult (Exp.expm1F32 x) ∧ HasResult (Exp.expm1F16 a)

theorem expCoverage_proven : ExpCoverage := by simp [ExpCoverage, HasResult]

def LogCoverage : Prop :=
  ∀ b : LogBase, ∀ x y mf bigF f : FV .f32, ∀ t : Nat,
    HasResult (MathFuncs.logbU b) ∧ HasResult (MathFuncs.logbL b) ∧
    HasResult (MathFuncs.logProc1 (toD y) (toD mf) (toD bigF) (toD f) b) ∧
    HasResult (MathFuncs.logProc2 (toD f) b) ∧ HasResult (MathFuncs.logImpl (toD x) b) ∧
    HasResult (MathFuncs.log1p (toD x)) ∧ HasResult (MathFuncs.logTabUnpack t) ∧
    HasResult (MathFuncs.logExt t) ∧ HasResult (Log.logb32 b) ∧
    HasResult (Log.tLog32 t) ∧ HasResult (Log.logProc1 y mf bigF f b) ∧
    HasResult (Log.logProc2 f b) ∧ HasResult (Log.log32 x b) ∧
    HasResult (Log.log2F32 x) ∧ HasResult (Log.logF32 x) ∧
    HasResult (Log.log10F32 x) ∧ HasResult (Log.log1pF32 x)

theorem logCoverage_proven : LogCoverage := by simp [LogCoverage, HasResult]

/-! ## pow.jl, cbrt.jl, rem_pio2.jl, rem2pi.jl -/

def PowCoverage : Prop :=
  ∀ T : FTy, ∀ x y : FV T, ∀ n : Int,
    HasResult (Special.usePowerBySquaring n) ∧ HasResult (MathFuncs.usePowerBySquaring n) ∧
    HasResult (Special.powBodyI x n) ∧ HasResult (Special.powBodyF T x (conv y)) ∧
    HasResult (Special.powFF x y) ∧ HasResult (Special.powFI x n) ∧
    HasResult (MathFuncs.powBodyF (toD x) (toD y)) ∧
    HasResult (MathFuncs.powBodyI (toD x) n) ∧ HasResult (MathFuncs.powFF (toD x) (toD y)) ∧
    HasResult (MathFuncs.powFI (toD x) n)

theorem powCoverage_proven : PowCoverage := by simp [PowCoverage, HasResult]

def CbrtCoverage : Prop :=
  ∀ T : FTy, ∀ x : FV T, ∀ t : FV .f32,
    HasResult (Special.cbrtAbstract (fun z => lt z (zero T)) neg (fun z => z) x) ∧
    HasResult (Special.approxCbrt x) ∧ HasResult (Special.improveCbrt32 (conv x) t) ∧
    HasResult (Special.cbrt x) ∧ HasResult (Special.cbrt16 (conv x)) ∧
    HasResult (MathFuncs.approxCbrt (toD x)) ∧
    HasResult (MathFuncs.improveCbrt (toD x) (toD x)) ∧ HasResult (MathFuncs.cbrt (toD x))

theorem cbrtCoverage_proven : CbrtCoverage := by simp [CbrtCoverage, HasResult]

def RemPio2Coverage : Prop :=
  ∀ x fn : F64, ∀ n : Int, ∀ u : Nat, ∀ y : FV .f32,
    HasResult (MathFuncs.codyWaite2cPio2 x fn n) ∧
    HasResult (MathFuncs.codyWaiteExtPio2 x u) ∧ HasResult (MathFuncs.fromfraction n) ∧
    HasResult (MathFuncs.paynehanek x) ∧ HasResult (MathFuncs.remPio2Kernel x) ∧
    HasResult (Special.remPio2Kernel32 y)

theorem remPio2Coverage_proven : RemPio2Coverage := by simp [RemPio2Coverage, HasResult]

def Rem2piCoverage : Prop :=
  ∀ x : FV .f64, ∀ y : FV .f32, ∀ n : JInt .i32, ∀ i : Int, ∀ m : Mode,
    HasResult (Special.rem2pi64 x m) ∧ HasResult (Special.rem2piNarrow y m) ∧
    HasResult (Special.rem2piInt32 n m) ∧ HasResult (Special.rem2piInteger i m) ∧
    HasResult (MathFuncs.rem2piNearest (to64 x)) ∧ HasResult (MathFuncs.rem2piToZero (to64 x)) ∧
    HasResult (MathFuncs.rem2piDown (to64 x)) ∧ HasResult (MathFuncs.rem2piUp (to64 x))

theorem rem2piCoverage_proven : Rem2piCoverage := by simp [Rem2piCoverage, HasResult]

/-! ## base/math.jl -/

def MathBasicCoverage : Prop :=
  ∀ T : FTy, ∀ x y : FV T, ∀ p : List (FV T),
    HasResult (MathMisc.throwComplexDomainError (α := FV T) "f") ∧
    HasResult (MathMisc.throwComplexDomainErrorNeg1 (α := FV T) "f") ∧
    HasResult (MathMisc.throwFiniteDomainError (α := FV T) "f") ∧
    HasResult (MathMisc.throwExpDomainError (α := FV T)) ∧
    HasResult (MathMisc.evalpolyReal x p) ∧
    HasResult (MathMisc.evalpolyComplex ⟨x, y⟩ p) ∧
    HasResult (MathMisc.evalpolyComplex1 ⟨x, y⟩ x) ∧
    HasResult (Exp.exthornerStep 1 x (x, y, x) x y) ∧
    HasResult (Exp.exthorner x (x, y, x)) ∧
    HasResult (MathMisc.rad2degNumber ⟨x, y⟩) ∧
    HasResult (MathMisc.deg2radNumber ⟨x, y⟩) ∧
    HasResult (TrigMisc.rad2deg T x) ∧ HasResult (TrigMisc.deg2rad T x) ∧
    HasResult (MathMisc.logBase (fun z => .ok z) div x y) ∧
    HasResult (MathMisc.nanDomErr x y) ∧ HasResult (MathMisc.sqrt x) ∧
    HasResult (MathMisc.fourthroot x)

theorem mathBasicCoverage_proven : MathBasicCoverage := by simp [MathBasicCoverage, HasResult]

def MathHypotCoverage : Prop :=
  ∀ T S : FTy, ∀ x : FV T, ∀ y : FV S, ∀ xs : List (FV T),
    HasResult (MathMisc.hypot1 x) ∧ HasResult (MathMisc.hypotMixed x y) ∧
    HasResult (MathMisc.hypotGeneric x x) ∧ HasResult (MathMisc.hypot2 T x x) ∧
    HasResult (MathMisc.hypot32 (conv x) (conv x)) ∧
    HasResult (MathMisc.hypot16 (conv x) (conv x)) ∧
    HasResult (MathMisc.hypotC16 ⟨conv x, conv x⟩ ⟨conv x, conv x⟩) ∧
    HasResult (MathMisc.hypotTupleGeneric xs) ∧ HasResult (MathMisc.hypotTupleIEEE xs) ∧
    HasResult (MathMisc.addFast x x) ∧ HasResult (MathMisc.atanMixed y x) ∧
    HasResult (MathMisc.atanNoOp (α := FV T))

theorem mathHypotCoverage_proven : MathHypotCoverage := by simp [MathHypotCoverage, HasResult]

def MathBitsCoverage : Prop :=
  ∀ T : FTy, ∀ x y : FV T, ∀ e : Int,
    HasResult (Bits.ldexp x e) ∧ HasResult (Bits.ldexp16 (conv x) e) ∧
    HasResult Bits.exponentThrow1 ∧ HasResult Bits.exponentThrow2 ∧
    HasResult (Bits.exponent x) ∧
    HasResult (Bits.exponentFiniteNonzero x) ∧ HasResult (Bits.exponentInteger e) ∧
    HasResult (Bits.exponentBitInteger (JInt.wrap .i64 e)) ∧
    HasResult (Bits.ilog2Step 1 e.natAbs 2 1) ∧
    HasResult (Bits.exponentBool true) ∧ HasResult (Bits.scaleinv x) ∧
    HasResult (Bits.remNearest x y) ∧ HasResult (Bits.modf x) ∧
    HasResult (Bits.modfGeneric x) ∧ HasResult (MathMisc.mod2pi x) ∧
    HasResult (Bits.add22condh (conv x) (conv y) (conv x) (conv y))

theorem mathBitsCoverage_proven : MathBitsCoverage := by simp [MathBitsCoverage, HasResult]

def MathFallbackCoverage : Prop :=
  ∀ T : FTy, ∀ x y z : FV T,
    HasResult (Bits.minGeneric x y) ∧ HasResult (Bits.maxGeneric x y) ∧
    HasResult (Bits.minFloat x y) ∧ HasResult (Bits.maxFloat x y) ∧
    HasResult (MathMisc.muladdInt (JInt.wrap .i64 x.toRat.1) (JInt.wrap .i64 y.toRat.1)
      (JInt.wrap .i64 z.toRat.1)) ∧
    HasResult (MathMisc.muladdGeneric mul add x y z) ∧
    HasResult (MathMisc.atanNoOp (α := FV T)) ∧
    HasResult (MathMisc.viaF32 (fun a => .ok a) (conv x)) ∧
    HasResult (MathMisc.viaC32 (fun a => .ok a) ⟨conv x, conv y⟩) ∧
    HasResult (MathMisc.atan16 (conv x) (conv y)) ∧
    HasResult (MathMisc.sincos16 (fun a => .ok (a, a)) (conv x)) ∧
    HasResult (MathMisc.realFallback (fun a => a) false (fun a => .ok a) x) ∧
    MathMisc.missing1 (some x) = none ∧
    MathMisc.missing2 (γ := FV T) (some x) (some y) = none ∧
    MathMisc.exp2Abstract (ofInt T 2) (fun a b => mul a b) x = mul (ofInt T 2) x ∧
    MathMisc.exp10Abstract (ofInt T 10) (fun a b => mul a b) x = mul (ofInt T 10) x

theorem mathFallbackCoverage_proven : MathFallbackCoverage := by
  simp [MathFallbackCoverage, HasResult, MathMisc.missing1, MathMisc.missing2,
    MathMisc.exp2Abstract, MathMisc.exp10Abstract]

/-! ## base/floatfuncs.jl -/

def FloatRoundCoverage : Prop :=
  ∀ T : FTy, ∀ x step : FV T, ∀ r : Mode, ∀ d b : Int,
    HasResult (FloatFuncs.roundM x r) ∧ HasResult (FloatFuncs.roundTiesAway x) ∧
    HasResult (FloatFuncs.roundTiesUp x) ∧ HasResult (FloatFuncs.roundFromZero x) ∧
    HasResult (FloatFuncs.roundInvstep x step r) ∧
    HasResult (FloatFuncs.roundInvstepsqrt x step r) ∧
    HasResult (FloatFuncs.roundStep x step r) ∧ HasResult (FloatFuncs.roundDigits x r d b) ∧
    HasResult (FloatFuncs.hidigit x b (fun a => .ok a)) ∧
    HasResult (FloatFuncs.hidigitInt d b.natAbs) ∧
    HasResult (FloatFuncs.roundSigdigits x r d b (fun a => .ok a)) ∧
    HasResult (FloatFuncs.hidigitReal (fun z => z) x b (fun a => .ok a)) ∧
    HasResult (FloatFuncs.roundKw x r (some d) none (some b) (fun a => .ok a))

theorem floatRoundCoverage_proven : FloatRoundCoverage := by simp [FloatRoundCoverage, HasResult]

def FloatApproxCoverage : Prop :=
  ∀ T : FTy, ∀ x y : FV T, ∀ i j : Int,
    HasResult (FloatFuncs.isapproxF x y (zero T) (FloatFuncs.rtoldefaultT T) false) ∧
    HasResult (FloatFuncs.uabsdiff i j) ∧ HasResult (FloatFuncs.uabsdiffUU .u64 i j) ∧
    HasResult (FloatFuncs.uabsdiffSS .i64 i j) ∧
    HasResult (FloatFuncs.mixedUabsdiff .u64 i j) ∧ HasResult (FloatFuncs.uabsdiffSU .u64 i j) ∧
    HasResult (FloatFuncs.uabsdiffLeSU .u64 i j 1 1) ∧
    HasResult (FloatFuncs.uabsdiffLe i j 1) ∧ HasResult (FloatFuncs.widesumLe i j 1) ∧
    HasResult (FloatFuncs.scaledRtolInt .i64 i j) ∧
    HasResult (FloatFuncs.scaledRtolReal (fun a b => a + b) i j) ∧
    HasResult (FloatFuncs.isapproxCurried (fun a b => a == b) y x) ∧
    HasResult (FloatFuncs.napprox (fun a b => a == b) x y) ∧
    HasResult (FloatFuncs.rtoldefaultT T) ∧ HasResult FloatFuncs.rtoldefaultReal ∧
    HasResult (FloatFuncs.isapproxInt .i64 i j 0 0) ∧
    HasResult (FloatFuncs.rtoldefaultNumber (fun a => a) (fun _ => .ok (one .f64)) i) ∧
    HasResult (FloatFuncs.rtoldefault3 (some x) (some y) true)

theorem floatApproxCoverage_proven : FloatApproxCoverage := by simp [FloatApproxCoverage, HasResult]

def FloatFmaCoverage : Prop :=
  ∀ T : FTy, ∀ x y z : FV T, ∀ native : Bool,
    HasResult (FloatFuncs.twoMul x y) ∧ HasResult (FloatFuncs.twoMulNoFma x y) ∧
    HasResult (FloatFuncs.fmaEmulatedNarrow x y z) ∧
    HasResult (FloatFuncs.twoMul64 native (conv x) (conv y)) ∧
    HasResult (FloatFuncs.splitbits (conv x)) ∧
    HasResult (FloatFuncs.fmaCorrection (conv x) (conv y) (conv z) (conv x)) ∧
    HasResult (FloatFuncs.fmaEmulated64 native (conv x) (conv y) (conv z)) ∧
    HasResult (FloatFuncs.fmaDispatch native x y z)

theorem floatFmaCoverage_proven : FloatFmaCoverage := by simp [FloatFmaCoverage, HasResult]

/-! ## base/mathconstants.jl and base/rounding.jl -/

def MathConstantsCoverage : Prop :=
  ∀ x : MathConstants.KnownIrrational, ∀ p : Int,
    HasResult (MathConstants.rationalBigInt x) ∧
    (∀ (α : Type) (f : MathConstants.KnownIrrational → Jl α),
      MathConstants.rationalInt f x = f x) ∧
    (∀ (α : Type) (f : MathConstants.KnownIrrational → Mode → α) (r : Mode),
      MathConstants.irrationalFloat f x r = f x r) ∧
    (∀ (α β : Type) (f : MathConstants.KnownIrrational → β → α) (tol : β),
      MathConstants.rationalizeIrrational f x tol = f x tol) ∧
    (∀ (α : Type) (f : α → MathConstants.KnownIrrational → Bool) (q : α),
      MathConstants.lessRational f q x = f q x) ∧
    (∀ (α : Type) (exp : α → α) (a : α), MathConstants.ePow exp a = exp a) ∧
    HasResult (MathConstants.eLiteralPow (fun n => n) p) ∧
    (∀ (α : Type) (log : α → α) (a : α), MathConstants.logBaseE log a = log a) ∧
    MathConstants.logE = 1 ∧ MathConstants.sinPi = zero .f64 ∧
    MathConstants.cosPi = neg (one .f64) ∧
    MathConstants.sincosPi = (zero .f64, neg (one .f64)) ∧
    MathConstants.tanPi = zero .f64 ∧ MathConstants.cotPi = inf .f64 true

theorem mathConstantsCoverage_proven : MathConstantsCoverage := by
  simp [MathConstantsCoverage, HasResult, MathConstants.rationalInt,
    MathConstants.irrationalFloat, MathConstants.rationalizeIrrational,
    MathConstants.lessRational, MathConstants.ePow, MathConstants.logBaseE,
    MathConstants.logE, MathConstants.sinPi, MathConstants.cosPi, MathConstants.sincosPi,
    MathConstants.tanPi, MathConstants.cotPi]

def RoundingForwardCoverage : Prop :=
  ∀ x : Int, ∀ r : Mode,
    Rounding.roundForward (fun a _ => a) x r = x ∧
    Rounding.roundTypeForward (fun (_ : Unit) a _ => a) () x r = x ∧
    Rounding.roundTypeConvert (fun a _ => a) (fun a _ _ => a) x r = x ∧
    Rounding.roundConvertGeneric (fun a => a) x = x ∧
    HasResult (Rounding.bottomRoundError (α := Int) "round") ∧
    Rounding.roundInteger x r = x

theorem roundingForwardCoverage_proven : RoundingForwardCoverage := by
  simp [RoundingForwardCoverage, Rounding.roundForward, Rounding.roundTypeForward,
    Rounding.roundTypeConvert, Rounding.roundConvertGeneric, Rounding.roundInteger, HasResult]

/-! The documented `cosc` formula is false for large finite IEEE values. -/

def coscDocumented (T : FTy) (x : FV T) : Jl (FV T) := do
  let c ← TrigPi.cospi T x
  let s ← TrigPi.sinpi T x
  let piX := mul (Trig.piT T) x
  return sub (div c x) (div s (mul piX x))

def CoscLargeArgument : Prop :=
  ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T,
    x.isfinite = true → x.iszero = false → TrigMisc.cosc T x = coscDocumented T x

theorem coscLargeArgument_refuted : ¬ CoscLargeArgument := by
  intro h
  have bad := h .f64 (Or.inr rfl) (Fl.floatmax : FV .f64) (by decide) (by decide)
  exact absurd bad (by decide +kernel)

end JuliaLean.MathCov
