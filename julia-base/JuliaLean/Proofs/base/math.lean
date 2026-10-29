import JuliaLean.base.math
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.math

open JuliaLean JuliaLean.Promotion JuliaLean.base.float JuliaLean.base.math JuliaLean.Registry

abbrev FTy := JuliaLean.base.float.FTy
abbrev FV (T : FTy) := JuliaLean.base.float.FV T

/-- A result is a Julia `DomainError`. -/
def IsDomainError {α : Type} (result : Jl α) : Prop :=
  ∃ message, result = .error (.domainError message)

/-- Negative real square roots raise the documented `DomainError` message. -/
def SqrtNegativeDomainError : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x : FV T),
    flt x (fzero T) = true →
    sqrtIEEE o x = .error (.domainError
      "sqrt was called with a negative real argument but will only return a complex result if called with a complex argument. Try sqrt(Complex(x)).")

/-- Base-log calls propagate the exact error from the first failing logarithm. -/
def LogBaseDomainErrorPropagation {α : Type} (logFn : α → Jl α) (divFn : α → α → α) : Prop :=
  (∀ b x e, logFn x = .error e → logBase logFn divFn b x = .error e) ∧
  (∀ b x lx e, logFn x = .ok lx → logFn b = .error e →
    logBase logFn divFn b x = .error e)

/-- Negative real operands of `log` raise DomainError, then propagate through `log(b,x)`. -/
def LogBaseNegativeDomainError : Prop :=
  ∀ (α β γ : Type) (logFn : γ → Jl γ) (divFn : γ → γ → γ)
    (isNegative : γ → Bool) (promote : α → β → γ × γ),
    (∀ x, isNegative x = true → IsDomainError (logFn x)) →
    LogBaseDomainErrorPropagation logFn divFn ∧
    (∀ b x lx, isNegative b = true → logFn x = .ok lx →
      IsDomainError (logBase logFn divFn b x)) ∧
    (∀ b x bp xp, promote b x = (bp, xp) → isNegative xp = true →
      IsDomainError (logBaseNumber promote logFn divFn b x)) ∧
    (∀ b x bp xp lx, promote b x = (bp, xp) → isNegative xp = false →
      isNegative bp = true → logFn xp = .ok lx →
      IsDomainError (logBaseNumber promote logFn divFn b x))

/-- `fourthroot` preserves the negative-square-root `DomainError`. -/
def FourthrootNegativeDomainError : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x : FV T), flt x (fzero T) = true →
    fourthroot (sqrtIEEE o) x = .error (.domainError
      "sqrt was called with a negative real argument but will only return a complex result if called with a complex argument. Try sqrt(Complex(x)).")

/-- NaN results on non-NaN inputs raise the documented domain error. -/
def NanDomainError : Prop :=
  ∀ (T S : FTy) (out : FV T) (x : FV S),
    (fisnan out = true → fisnan x = false →
      nanDomErr out x = .error (.domainError "NaN result for non-NaN input.")) ∧
    (fisnan out = false ∨ fisnan x = true → nanDomErr out x = .ok out)

/-- Floating exponents reject zero, infinity, and NaN with their documented domain errors. -/
def ExponentFloatDomainErrors : Prop :=
  ∀ (T : FTy) (x : FV T),
    (fiszero x = true → exponentFloat x = .error (.domainError "Cannot be ±0.0.")) ∧
    ((fisnan x = true ∨ fisinf x = true) →
      exponentFloat x = .error (.domainError "Cannot be NaN or Inf."))

/-- Integer and Boolean exponents reject zero with the documented domain error. -/
def ExponentZeroDomainErrors : Prop :=
  (∀ (X U : Type) (o : IntegerExponentOps X U) (x : X), o.iszero x = true →
    exponentInteger o x = some (.error (.domainError "cannot be zero"))) ∧
  (∀ {t : IntTy} (x : JInt t), x.val = 0 →
      exponentBitInteger x = .error (.domainError "cannot be zero")) ∧
  exponentBool false = .error (.domainError "cannot be zero")

/-- Horner evaluation visits coefficients from highest degree down to the constant term. -/
def HornerSpecification {α : Type} (mul add : α → α → α) (x : α) (p : List α) : Option α :=
  match p.reverse with
  | [] => none
  | c :: cs => some (cs.foldl (fun acc coefficient => muladd mul add x acc coefficient) c)

def EvalpolyHornerOrder : Prop :=
  (∀ (α : Type) (mul add : α → α → α)
    (requireOneBased : List α → Jl Unit) (x : α) (p : List α),
    requireOneBased p = .ok () →
    (∀ generated, evalpolyTuple mul add requireOneBased generated x p =
      (match HornerSpecification mul add x p with
       | some value => .ok value
       | none => .error .boundsError)) ∧
    (evalpolyVector mul add requireOneBased x p =
      (match HornerSpecification mul add x p with
       | some value => .ok value
       | none => .error .boundsError))) ∧
  (∀ x : JuliaSyntax, ∀ p : List JuliaSyntax,
    hornerMacro x p =
      .invoke "evalpoly" "Tuple{Any, Tuple}"
        [.escaped x, .tupleSplat (p.map JuliaQuote.escaped)]) ∧
  (∀ z : JuliaSyntax, ∀ p : List JuliaSyntax,
    evalpolyMacro z p =
      .call "evalpoly" [.escaped z, .tupleSplat (p.map JuliaQuote.escaped)])

/-- Complex evaluation follows the source's descending-coefficient recurrence. -/
def ComplexHornerSpecification {T : FTy}
    (cm : FV T → Cx T → FV T → Cx T) (z : Cx T) (p : List (FV T)) : Jl (EvalpolyResult T) := Id.run do
  match p.reverse with
  | [] => return .error .boundsError
  | [c] => return .ok (.real c)
  | a :: b :: rest =>
    let x := z.re
    let y := z.im
    let r := add x x
    let s := muladd (mul (T := T)) (add (T := T)) x x (mul y y)
    let (a, b) := rest.foldl (fun (ab : FV T × FV T) coefficient =>
      let ai := ab.1
      (muladd (mul (T := T)) (add (T := T)) r ai ab.2,
       muladd (mul (T := T)) (add (T := T)) (fneg s) ai coefficient)) (a, b)
    return .ok (.complex (cm a z b))

def ComplexEvalpolyHornerOrder : Prop :=
  (∀ (T : FTy) (cm : FV T → Cx T → FV T → Cx T)
    (requireOneBased : List (FV T) → Jl Unit) (z : Cx T) (p : List (FV T)),
    requireOneBased p = .ok () →
    evalpolyComplex cm requireOneBased z p = ComplexHornerSpecification cm z p ∧
    evalpolyComplexVector cm requireOneBased z p = ComplexHornerSpecification cm z p ∧
    (∀ generated, evalpolyComplexTuple cm requireOneBased generated z p =
      ComplexHornerSpecification cm z p)) ∧
  (∀ (T : FTy) (z : Cx T) (c : FV T), evalpolyComplexOne z c = c)

/-- The empty tuple/vector is not the documented zero sum in the current source model. -/
def EvalpolyEmptyZero : Prop :=
  ∀ (mul add : FV .f64 → FV .f64 → FV .f64) (x : FV .f64),
    evalpolyTuple mul add (fun _ => pure ()) true x [] = .ok (fzero .f64) ∧
    evalpolyVector mul add (fun _ => pure ()) x [] = .ok (fzero .f64)

def IEEEFloatOpsFaithful {T : FTy} (o : IEEEOps T) : Prop :=
  o.eps = eps_float T ∧ o.floatmin = floatmin_float T ∧ o.floatmax = floatmax_float T ∧
  o.invFloatmin = div_float (fone T) (floatmin_float T) ∧
  fisfinite o.pi = true ∧ flt (fzero T) o.pi = true ∧
  (∀ x, o.sqrtLlvm x = JuliaLean.C.jlSqrtLlvm x) ∧
  (∀ x, o.trunc x = JuliaLean.C.jlTruncLlvm x) ∧
  (∀ x, o.oneunit x = fone T) ∧
  (∀ x, o.inverse x = div_float (fone T) x) ∧
  (∀ x, o.abs2 x = mul_float x x) ∧
  (∀ x y, o.greater x y = flt y x) ∧
  (∀ x y, o.addFast x y = add_float x y) ∧
  (∀ x y z, o.fma x y z = JuliaLean.C.jlFmaFloat x y z) ∧
  (∀ x y z, o.muladd x y z = JuliaLean.C.jlMuladdFloat x y z) ∧
  (∀ x y, o.rem x y = rem_IEEEFloat x y) ∧
  (∀ x y, o.flipsign x y = if y.signbit then Fl.neg x else x) ∧
  (∀ x y, o.minFloat x y = JuliaLean.C.jlMinFloat x y) ∧
  (∀ x y, o.maxFloat x y = JuliaLean.C.jlMaxFloat x y)

/-- The Float16/32/64 angle conversions preserve signed zero and non-finite classes. -/
def AngleConversionExceptionalValues : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x : FV T),
    IEEEFloatOpsFaithful o →
    (fiszero x = true →
      fsignbit (rad2degFloat (abstractFloatOpsOfIEEE o) x) = fsignbit x ∧
      fsignbit (deg2radFloat (abstractFloatOpsOfIEEE o) x) = fsignbit x) ∧
    (fisnan x = true →
      fisnan (rad2degFloat (abstractFloatOpsOfIEEE o) x) = true ∧
      fisnan (deg2radFloat (abstractFloatOpsOfIEEE o) x) = true) ∧
    (fisinf x = true →
      fisinf (rad2degFloat (abstractFloatOpsOfIEEE o) x) = true ∧
      fisinf (deg2radFloat (abstractFloatOpsOfIEEE o) x) = true)

/-- `frexp` returns a signed fraction in [1/2,1) and reconstructs each finite nonzero input. -/
def FrexpRoundTripRange : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x : FV T),
    IEEEFloatOpsFaithful o →
    fisfinite x = true → fiszero x = false →
    let parts := frexp x
    let m := parts.1
    let e := parts.2
    fle (T := T) (div (T := T) (fone T) (Fl.ofInt 2)) (fabs m) = true ∧
    flt (T := T) (fabs m) (fone T) = true ∧
    ldexp o m e = x

/-- `significand` keeps the input sign, normalizes finite nonzero values, and round-trips. -/
def SignificandRange : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x : FV T),
    IEEEFloatOpsFaithful o →
    fisfinite x = true → fiszero x = false →
    fsignbit (significand x) = fsignbit x ∧
    fle (T := T) (fone T) (fabs (significand x)) = true ∧
    flt (T := T) (fabs (significand x)) (Fl.ofInt 2) = true ∧
    ∃ e, exponentFloat x = .ok e ∧ ldexp o (significand x) e = x

/-- `exponent(x)` is the largest power-of-two exponent not exceeding `|x|`. -/
def ExponentFloatRange : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x : FV T),
    IEEEFloatOpsFaithful o →
    fisfinite x = true → fiszero x = false →
    ∃ e, exponentFloat x = .ok e ∧
      fle (T := T) (ldexp o (fone T) e) (fabs x) = true ∧
      flt (T := T) (fabs x) (ldexp o (fone T) (e + 1)) = true

def QRatLe (a b : Int × Nat) : Bool :=
  decide (a.1 * (b.2 : Int) ≤ b.1 * (a.2 : Int))

def QRatLt (a b : Int × Nat) : Bool :=
  decide (a.1 * (b.2 : Int) < b.1 * (a.2 : Int))

def QPowTwo (e : Int) : Int × Nat :=
  if 0 ≤ e then (2 ^ e.toNat, 1) else (1, 2 ^ (-e).toNat)

def QRationalMagnitude (num den : JInt .i64) : Int × Nat :=
  (num.val.natAbs, den.val.natAbs)

/-- A rational exponent is the largest power of two below the exact rational magnitude. -/
def ExponentRationalDefinition : Prop :=
  ∀ (num den : JInt .i64)
    (float : JInt .i64 × JInt .i64 → FV .f64)
    (sameType : JInt .i64 × JInt .i64 → Bool),
    0 < den.val → num.val ≠ 0 →
    (∀ n d, 0 < d.val → float (n, d) = Fl.roundRat n.val d.val.natAbs false) →
    (∀ n d, sameType (n, d) = false) →
    ∃ e, realFallback float sameType "exponent" exponentFloat (num, den) = .ok e ∧
      QRatLe (QPowTwo e) (QRationalMagnitude num den) = true ∧
      QRatLt (QRationalMagnitude num den) (QPowTwo (e + 1)) = true

def ModfPartsAndSigns : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x : FV T),
    IEEEFloatOpsFaithful o →
    (fisfinite x = true →
      let parts := modfIEEE o x
      add parts.1 parts.2 = x ∧
      fsignbit parts.1 = fsignbit x ∧ fsignbit parts.2 = fsignbit x) ∧
    (fisinf x = true →
      let parts := modfIEEE o x
      fiszero parts.1 = true ∧ fsignbit parts.1 = fsignbit x ∧ parts.2 = x)


/-- The exact nearest Float64 square root is characterized by rational midpoint squares. -/
def QAdd (a b : Int × Nat) : Int × Nat :=
  (a.1 * (b.2 : Int) + b.1 * (a.2 : Int), a.2 * b.2)

def QNeg (a : Int × Nat) : Int × Nat := (-a.1, a.2)

def QSub (a b : Int × Nat) : Int × Nat := QAdd a (QNeg b)

def QMul (a b : Int × Nat) : Int × Nat := (a.1 * b.1, a.2 * b.2)

def QHalf (a : Int × Nat) : Int × Nat := (a.1, 2 * a.2)

def QLT (a b : Int × Nat) : Bool := decide (a.1 * (b.2 : Int) < b.1 * (a.2 : Int))

def QEQ (a b : Int × Nat) : Bool := decide (a.1 * (b.2 : Int) = b.1 * (a.2 : Int))

def QAbsFloat64 (x : FV .f64) : Int × Nat :=
  ((Fl.ofBits (f := double) (Fl.magnitude x) : FV .f64)).toRat

def HypotSquared64 (x y : FV .f64) : Int × Nat :=
  QAdd (QMul (QAbsFloat64 x) (QAbsFloat64 x)) (QMul (QAbsFloat64 y) (QAbsFloat64 y))
def HypotIEEEOpsFaithful {T : FTy} (o : IEEEOps T) : Prop :=
  IEEEFloatOpsFaithful o ∧
  (∀ x y, let (product, residual) := o.twoMul x y
    QAdd product.toRat residual.toRat = QMul x.toRat y.toRat)

/-- Imported reductions preserve Boolean disjunction and propagate NaN through maximum. -/
def HypotReductionExceptional {T : FTy} (r : HypotFloatReductionOps T) : Prop :=
  (∀ (f : FV T → Bool) (xs : List (FV T)),
    JuliaLean.base.reduce.mapreduce r.iteratorEltype f r.booleanOr (.values xs) .initial =
      .ok (xs.any f)) ∧
  (∀ xs : List (FV T), xs.any fisnan = true →
    ∃ m, JuliaLean.base.reduce.maximum_f r.iteratorEltype r.reinterpretSigned
      r.maximumReducer (.values xs) .initial = .ok m ∧
      fisnan (r.reinterpretFloat m) = true)

/-- Finite `hypot` inputs with exact magnitude at most `floatmax` produce a finite result. -/
def HypotFiniteSafety64 : Prop :=
  ∀ (o64 : IEEEOps .f64) (r64 : HypotFloatReductionOps .f64)
    (promote : FV .f64 → FV .f64 → FV .f64 × FV .f64)
    (float : FV .f64 → FV .f64),
    HypotIEEEOpsFaithful o64 →
    (∀ x y, promote x y = (x, y)) → (∀ x, float x = x) →
    ∀ x y : FV .f64, fisfinite x = true → fisfinite y = true →
      let maxRat := (Fl.floatmax : FV .f64).toRat
      (QLT (HypotSquared64 x y) (QMul maxRat maxRat) ||
        QEQ (HypotSquared64 x y) (QMul maxRat maxRat)) = true →
      ∃ h, hypotTwo promote float (hypotDispatchFloat64 o64 r64) x y =
        .ok h ∧ fisfinite h = true

def HypotMidpoint64 (x y : FV .f64) : Int × Nat :=
  QHalf (QAdd x.toRat y.toRat)

def NearestHypot64 (x y h : FV .f64) : Prop := Id.run do
  let bits := h.toBits
  let maxBits := (Fl.floatmax : FV .f64).toBits
  let exact := HypotSquared64 x y
  let even := decide (bits % 2 = 0)
  let lowerOk :=
    if bits == 0 then true
    else
      let lower : FV .f64 := Fl.ofBits (bits - 1)
      let midpoint := HypotMidpoint64 lower h
      let midpointSquared := QMul midpoint midpoint
      QLT midpointSquared exact || (QEQ midpointSquared exact && even)
  let upperMidpoint :=
    if bits == maxBits then
      let lower : FV .f64 := Fl.ofBits (bits - 1)
      QAdd h.toRat (QHalf (QSub h.toRat lower.toRat))
    else
      let upper : FV .f64 := Fl.ofBits (bits + 1)
      HypotMidpoint64 h upper
  let upperSquared := QMul upperMidpoint upperMidpoint
  let upperOk := QLT exact upperSquared || (QEQ exact upperSquared && even)
  return h.signbit = false ∧ lowerOk = true ∧ upperOk = true

/-- One-argument `hypot` returns a magnitude for real and complex inputs. -/
def HypotOneFloat : Prop :=
  (∀ (α : Type) (T : FTy) (float : α → FV T) (x : α),
    (hypotOne float (fabs (T := T)) x).toBits = Fl.magnitude (float x)) ∧
  (∀ (T : FTy) (o : IEEEOps T) (z : JuliaLean.base.complex.Complex (FV T)) (h : FV T),
    HypotIEEEOpsFaithful o →
    hypotOne id (JuliaLean.base.complex.abs_Complex (hypotGeneric (hypotOpsOfIEEE o))) z = .ok h →
    fisnan h = false → h.signbit = false) ∧
  (∀ (o : IEEEOps .f64) (z : JuliaLean.base.complex.Complex (FV .f64)) (h : FV .f64),
    HypotIEEEOpsFaithful o → o.haveFma = true →
    fisfinite z.re = true → fisfinite z.im = true →
    hypotOne id (JuliaLean.base.complex.abs_Complex (hypotGeneric (hypotOpsOfIEEE o))) z = .ok h →
    fisfinite h = true → NearestHypot64 z.re z.im h)
/-- With hardware FMA, finite Float64 `hypot` is the nearest IEEE value. -/
def HypotCorrectlyRounded64 : Prop :=
  ∀ (o64 : IEEEOps .f64) (r64 : HypotFloatReductionOps .f64)
    (promote : FV .f64 → FV .f64 → FV .f64 × FV .f64)
    (float : FV .f64 → FV .f64),
    HypotIEEEOpsFaithful o64 →
    (∀ x y, promote x y = (x, y)) → (∀ x, float x = x) →
    ∀ x y h : FV .f64, o64.haveFma = true →
      fisfinite x = true → fisfinite y = true →
      hypotTwo promote float (hypotDispatchFloat64 o64 r64) x y = .ok h →
      fisfinite h = true → NearestHypot64 x y h

/-- Public Float64 `hypot` returns infinity whenever an operand is infinite. -/
def HypotInfinity64 : Prop :=
  ∀ (o64 : IEEEOps .f64) (r64 : HypotFloatReductionOps .f64)
    (promote : FV .f64 → FV .f64 → FV .f64 × FV .f64)
    (promoteMany : List (FV .f64) → List (FV .f64))
    (float : FV .f64 → FV .f64),
    HypotIEEEOpsFaithful o64 →
    HypotReductionExceptional r64 →
    (∀ x y, promote x y = (x, y)) → (∀ xs, promoteMany xs = xs) →
    (∀ x, float x = x) →
    (∀ x y : FV .f64, (fisinf x = true ∨ fisinf y = true) →
      ∃ h, hypotTwo promote float (hypotDispatchFloat64 o64 r64) x y =
        .ok h ∧ fisinf h = true) ∧
    (∀ xs : List (FV .f64), xs.any fisinf = true →
      ∃ h, hypotMany promoteMany float (hypotDispatchFloat64 o64 r64) xs =
        .ok h ∧ fisinf h = true)

/-- Float64 `hypot` ignores operand signs and returns `|x|` when the other input is zero. -/
def HypotSignAndZeroInvariant64 : Prop :=
  ∀ (o64 : IEEEOps .f64) (r64 : HypotFloatReductionOps .f64)
    (promote : FV .f64 → FV .f64 → FV .f64 × FV .f64)
    (float : FV .f64 → FV .f64),
    HypotIEEEOpsFaithful o64 →
    (∀ x y, promote x y = (x, y)) → (∀ x, float x = x) →
    (∀ x y : FV .f64, fisfinite x = true → fisfinite y = true →
      hypotTwo promote float (hypotDispatchFloat64 o64 r64) x y =
        hypotTwo promote float (hypotDispatchFloat64 o64 r64) (fneg x) y ∧
      hypotTwo promote float (hypotDispatchFloat64 o64 r64) x y =
        hypotTwo promote float (hypotDispatchFloat64 o64 r64) x (fneg y)) ∧
    (∀ x : FV .f64, fisfinite x = true →
      hypotTwo promote float (hypotDispatchFloat64 o64 r64) x (fzero .f64) =
        .ok (fabs x))

/-- Without an infinity, any NaN operand makes public Float64 `hypot` return NaN. -/
def HypotNaN64 : Prop :=
  ∀ (o64 : IEEEOps .f64) (r64 : HypotFloatReductionOps .f64)
    (promote : FV .f64 → FV .f64 → FV .f64 × FV .f64)
    (promoteMany : List (FV .f64) → List (FV .f64))
    (float : FV .f64 → FV .f64),
    HypotIEEEOpsFaithful o64 →
    HypotReductionExceptional r64 →
    (∀ x y, promote x y = (x, y)) → (∀ xs, promoteMany xs = xs) →
    (∀ x, float x = x) →
    (∀ x y : FV .f64, (fisnan x = true ∨ fisnan y = true) →
      fisinf x = false → fisinf y = false →
      ∃ h, hypotTwo promote float (hypotDispatchFloat64 o64 r64) x y =
        .ok h ∧ fisnan h = true) ∧
    (∀ xs : List (FV .f64), xs.any fisnan = true → xs.any fisinf = false →
      ∃ h, hypotMany promoteMany float (hypotDispatchFloat64 o64 r64) xs =
        .ok h ∧ fisnan h = true)

/-- Every source `hypot` overload gives infinity precedence over NaN. -/
def HypotSourceInfinityBranches : Prop :=
  (∀ (T : FTy) (o : IEEEOps T) (x y : FV T),
    HypotIEEEOpsFaithful o →
    (fisinf x = true ∨ fisinf y = true) →
    ∃ h, hypotGeneric (hypotOpsOfIEEE o) x y = .ok h ∧ fisinf h = true) ∧
  (∀ (T : FTy) (o : IEEEOps T) (r : HypotFloatReductionOps T)
      (xs : List (FV T)),
    HypotIEEEOpsFaithful o → HypotReductionExceptional r →
    xs.any fisinf = true →
    ∃ h, hypotTupleIEEE o r xs = .ok h ∧ fisinf h = true) ∧
  (∀ (o64 : IEEEOps .f64) (x y : FV .f32),
    HypotIEEEOpsFaithful o64 →
    (fisinf x = true ∨ fisinf y = true) →
    ∃ h, hypot32 o64 x y = .ok h ∧ fisinf h = true) ∧
  (∀ (o32 : IEEEOps .f32) (x y : FV .f16),
    HypotIEEEOpsFaithful o32 →
    (fisinf x = true ∨ fisinf y = true) →
    ∃ h, hypot16 o32 x y = .ok h ∧ fisinf h = true) ∧
  (∀ (o32 : GenericHypotOps (Cx .f32) (FV .f32)) (x y : Cx .f16),
    let x32 : Cx .f32 := ⟨Fl.convert x.re, Fl.convert x.im⟩
    let y32 : Cx .f32 := ⟨Fl.convert y.re, Fl.convert y.im⟩
    let axu := o32.abs x32
    let ayu := o32.abs y32
    let ax0 := o32.div axu (o32.oneunit axu)
    let ay0 := o32.div ayu (o32.oneunit ayu)
    (o32.isinf ax0 = true ∨ o32.isinf ay0 = true) →
    o32.infinity = finf .f32 →
    ∃ h, hypotComplex16 o32 x y = .ok h ∧ fisinf h = true)

def MinmaxIsless : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x y : FV T),
    IEEEFloatOpsFaithful o →
    fisnan x = false → fisnan y = false →
    minIEEE o x y = (if Fl.isless x y then x else y) ∧
    maxIEEE o x y = (if Fl.isless x y then y else x)

/-- NaN propagates to both Float16/32/64 `minmax` results. -/
def MinmaxNan : Prop :=
  ∀ (T : FTy) (o : IEEEOps T) (x y : FV T),
    IEEEFloatOpsFaithful o →
    (fisnan x = true ∨ fisnan y = true) →
    fisnan (minmaxGeneric (minIEEE o) (maxIEEE o) x y).1 = true ∧
    fisnan (minmaxGeneric (minIEEE o) (maxIEEE o) x y).2 = true

/-- Minimum and maximum choose negative and positive zero by IEEE total ordering. -/
def MinmaxSignedZero : Prop :=
  ∀ (T : FTy) (o : IEEEOps T),
    IEEEFloatOpsFaithful o →
    let positiveZero := fzero T
    let negativeZero := fneg positiveZero
    minIEEE o negativeZero positiveZero = negativeZero ∧
    maxIEEE o negativeZero positiveZero = positiveZero ∧
    minmaxGeneric (minIEEE o) (maxIEEE o) negativeZero positiveZero =
      (negativeZero, positiveZero)

/-- Generated `Missing` overloads propagate `missing` for unary and binary calls. -/
def MissingPropagation : Prop :=
  ∀ {α β γ δ : Type} (x : α) (y : β),
    missingUnary (none : Option γ) = (none : Option γ) ∧
    missingBoth (none : Option α) (none : Option β) = (none : Option γ) ∧
    missingRight x (none : Option β) = (none : Option γ) ∧
    missingLeft (none : Option α) y = (none : Option γ) ∧
    fourthrootMissing (none : Option δ) = (none : Option δ)

/- The generic AbstractFloat fallback raises the message constructed by no_op_err. -/
def AtanNoOpError : Prop :=
  ∀ {α : Type} (o : AbstractFloatOps α),
    atanNoOp o = .error (.errorException ("atan not defined for " ++ o.typeName))
def piRoundDown64 : FV .f64 :=
  Fl.ofBits (f := double) 0x400921fb54442d18

def twoPiRoundDown64 : FV .f64 :=
  Fl.ofBits (f := double) 0x401921fb54442d18

/-- `mod2pi` returns a Float64 in the exact representable part of `[0, 2π)`. -/
def Mod2PiRange : Prop :=
  ∀ (remfn : FV .f64 → RoundingMode → FV .f64) (x : FV .f64),
    fisfinite x = true →
    (∀ z, fisfinite z = true →
      fle (T := .f64) (fzero .f64) (remfn z .Down) = true ∧
      fle (T := .f64) (remfn z .Down) twoPiRoundDown64 = true) →
    let y := mod2pi remfn x
    fle (T := .f64) (fzero .f64) y = true ∧
    fle (T := .f64) y twoPiRoundDown64 = true

/-- Domain helpers reject arguments with a DomainError and include the requested function name. -/
def DomainHelperErrors : Prop :=
  (∀ {α : Type} (f : String) (x : α),
    IsDomainError (throwComplexDomainError f x) ∧
    IsDomainError (throwComplexDomainErrorNeg1 f x) ∧
    IsDomainError (throwFiniteDomainError f x)) ∧
  (∀ {α : Type} (x : α), IsDomainError (throwExpDomainError x))

/-- Compensated Horner evaluation has the constant coefficient as its value at zero. -/
def ExtendedHornerAtZero : Prop :=
  ∀ {T : FTy} (wide : T = .f32 ∨ T = .f64) (o : IEEEOps T)
    (p : FV T × FV T × FV T),
    HypotIEEEOpsFaithful o →
    fisfinite p.1 = true → fisfinite p.2.1 = true → fisfinite p.2.2 = true →
    ∃ hi lo, exthorner wide o (fzero T) p = .ok (hi, lo) ∧
      QAdd hi.toRat lo.toRat = p.1.toRat

/-- The extended-Horner loop rejects indices outside the polynomial's two remaining terms. -/
def ExtendedHornerBadIndex : Prop :=
  ∀ {T : FTy} (wide : T = .f32 ∨ T = .f64) (o : IEEEOps T)
    (i : Int) (x : FV T) (p : FV T × FV T × FV T) (hi lo : FV T),
    i ≠ 1 → i ≠ 2 →
    exthornerStep wide o i x p hi lo =
      .error (.errorException "unexpected index")

/-- Angular conversion factors are positive and approximately reciprocal. -/
def AngleFactorBounds : Prop :=
  (∀ {α : Type} (o : AbstractFloatOps α) (z : α),
    o.lt (o.ofInt 0) o.pi = true →
    (∀ x y, o.lt (o.ofInt 0) x = true → o.lt (o.ofInt 0) y = true →
      o.lt (o.ofInt 0) (o.div x y) = true) →
    o.lt (o.ofInt 0) (o.ofInt 180) = true →
    o.lt (o.ofInt 0) (oneEightyOverPi o z) = true ∧
    o.lt (o.ofInt 0) (piOverOneEighty o z) = true) ∧
  (QRatLt (57, 1) oneEightyOverPi16.toRat = true ∧
    QRatLt oneEightyOverPi16.toRat (58, 1) = true) ∧
  (QRatLt (57, 1) oneEightyOverPi32.toRat = true ∧
    QRatLt oneEightyOverPi32.toRat (58, 1) = true) ∧
  (QRatLt (1, 100) piOverOneEighty16.toRat = true ∧
    QRatLt piOverOneEighty16.toRat (1, 50) = true)

/-- IEEE ordering distinguishes signed zero and makes min/max agree with the total order. -/
def AbstractFloatOrder : Prop :=
  ∀ {T : FTy} (o : IEEEOps T) (x y : FV T),
    IEEEFloatOpsFaithful o →
    fisnan x = false → fisnan y = false →
    let a := abstractFloatOpsOfIEEE o
    islessFloat a x y = Fl.isless x y ∧
    (minGeneric a x y).bits = (if Fl.isless x y then x else y).bits ∧
    (maxGeneric a x y).bits = (if Fl.isless y x then x else y).bits

/-- Extracting and rebuilding the high word preserves that word and clears the low word. -/
def HighWordRoundTrips : Prop :=
  (∀ x : JInt .u64,
    (highwordUInt64 x).val.toNat = x.val.toNat / 2 ^ 32 ∧
    (poshighwordUInt64 x).val.toNat = (x.val.toNat / 2 ^ 32) % 2 ^ 31) ∧
  (∀ x : FV .f64,
    (highword64 (fromhighword64 (highword64 x))).val.toNat =
      (highword64 x).val.toNat ∧
    (fromhighword64 (highword64 x)).bits % 2 ^ 32 = 0 ∧
    (poshighword64 x).val.toNat = (highword64 x).val.toNat % 2 ^ 31) ∧
  (∀ x : FV .f32,
    (fromhighword32 (highword32 x)).bits = x.bits ∧
    (poshighword32 x).val.toNat = x.bits % 2 ^ 31)

/-- The scaling pair is finite, positive, and reciprocal, including subnormal inputs. -/
def ScaleInvReciprocal : Prop :=
  ∀ {T : FTy} (o : IEEEOps T) (x : FV T),
    IEEEFloatOpsFaithful o →
    let (u, v) := scaleinv o x
    fisfinite u = true ∧ fisfinite v = true ∧
    flt (fzero T) u = true ∧ flt (fzero T) v = true ∧
    QEQ (QMul u.toRat v.toRat) (1, 1) = true

/-- Nearest remainder is no larger than half the finite, nonzero modulus. -/
def NearestRemainderRange : Prop :=
  ∀ {T : FTy} (o : IEEEOps T) (x p : FV T),
    IEEEFloatOpsFaithful o →
    fisfinite x = true → fisfinite p = true → fiszero p = false →
    let r := remNearest o x p
    fisfinite r = true ∧
    QRatLe (fabs r).toRat (QHalf (fabs p).toRat) = true

/-- The generic modf method splits a finite value into an integer and a fraction of magnitude < 1. -/
def GenericModfParts : Prop :=
  ∀ {T : FTy} (o : IEEEOps T) (x : FV T),
    IEEEFloatOpsFaithful o → fisfinite x = true →
    let (fraction, integer) :=
      modfGeneric fisinf (fun _ => fzero T) (fun _ => fone T) o.trunc o.flipsign o.rem x
    QEQ (QAdd fraction.toRat integer.toRat) x.toRat = true ∧
    flt (fabs fraction) (fone T) = true ∧
    o.trunc integer = integer ∧
    fraction.signbit = x.signbit

/-- Double-double addition returns the nearest representable value of the four-term sum. -/
def Add22CondhExactSum : Prop :=
  ∀ (xh xl yh yl : FV .f64),
    fisfinite xh = true → fisfinite xl = true →
    fisfinite yh = true → fisfinite yl = true →
    fle (fabs xl) (fabs xh) = true → fle (fabs yl) (fabs yh) = true →
    let exact := QAdd (QAdd xh.toRat xl.toRat) (QAdd yh.toRat yl.toRat)
    let r := add22condh xh xl yh yl
    fisfinite r = true →
    ∀ candidate : FV .f64, fisfinite candidate = true →
      QRatLe
        (QMul (QSub r.toRat exact) (QSub r.toRat exact))
        (QMul (QSub candidate.toRat exact) (QSub candidate.toRat exact)) = true

/-- Integer multiply-add distributes over its last operand and has zero as the additive identity. -/
def GenericMuladdRingLaws : Prop :=
  ∀ a b c d : Int,
    muladd Int.mul Int.add a b (c + d) =
      muladd Int.mul Int.add a b c + d ∧
    muladd Int.mul Int.add a b 0 = a * b

/-- The generic shift algorithm computes the base-two exponent of every positive Integer value. -/
def IntegerLog2Specification : Prop :=
  ∀ {T : Type} (o : IntegerStepOps T) (magnitude : T → Nat),
    magnitude o.one = 1 →
    (∀ x y, magnitude (o.add x y) = magnitude x + magnitude y) →
    (∀ x y, magnitude (o.mul x y) = magnitude x * magnitude y) →
    (∀ x y, o.ge x y = decide (magnitude y ≤ magnitude x)) →
    (∀ x s, 0 ≤ s →
      magnitude (o.shiftRight x s) = magnitude x / 2 ^ s.toNat) →
    (∀ a b, o.checkedAdd a b = .ok (a + b)) →
    ∀ y, 0 < magnitude y →
      ∃ reduced n, ilog2Step o y (o.add o.one o.one) 1 = some (.ok (reduced, n)) ∧
        2 ^ n.toNat ≤ magnitude y ∧ magnitude y < 2 ^ (n.toNat + 1)

/-- Generic exponent uses the magnitude of either sign and rejects only zero. -/
def GenericIntegerExponentRange : Prop :=
  ∀ {X U : Type} (o : IntegerExponentOps X U) (magnitude : U → Nat),
    magnitude o.step.one = 1 →
    (∀ x y, magnitude (o.step.add x y) = magnitude x + magnitude y) →
    (∀ x y, magnitude (o.step.mul x y) = magnitude x * magnitude y) →
    (∀ x y, o.step.ge x y = decide (magnitude y ≤ magnitude x)) →
    (∀ x s, 0 ≤ s →
      magnitude (o.step.shiftRight x s) = magnitude x / 2 ^ s.toNat) →
    (∀ a b, o.step.checkedAdd a b = .ok (a + b)) →
    ∀ x, o.iszero x = false → 0 < magnitude (o.uabs x) →
      ∃ n, exponentInteger o x = some (.ok n) ∧
        2 ^ n.toNat ≤ magnitude (o.uabs x) ∧
        magnitude (o.uabs x) < 2 ^ (n.toNat + 1)

/-- The finite exponent is the unique power-of-two bin containing the input magnitude. -/
def FiniteExponentRange : Prop :=
  ∀ {T : FTy} (x : FV T),
    fisfinite x = true → fiszero x = false →
    let e := exponentFiniteNonzero x
    QRatLe (QPowTwo e) (fabs x).toRat = true ∧
    QRatLt (fabs x).toRat (QPowTwo (e + 1)) = true

/-- Float16 ldexp remains a power-of-two scaling whenever the exact result is representable. -/
def Ldexp16ExactScaling : Prop :=
  ∀ (o32 : IEEEOps .f32) (x : FV .f16) (q : Int) (expected : FV .f16),
    IEEEFloatOpsFaithful o32 →
    fisfinite x = true → fisfinite expected = true →
    QEQ expected.toRat (QMul x.toRat (QPowTwo q)) = true →
    (ldexp16 o32 x q).bits = expected.bits

/-- Real trigonometric fallbacks preserve the documented integer-argument special values. -/
def RealTrigFallbacks : Prop :=
  ∀ {α : Type} (float : α → FV .f64) (sameType : α → Bool)
    (sinpiFn cospiFn tanpiFn : FV .f64 → Jl (FV .f64))
    (sincospiFn : FV .f64 → Jl (FV .f64 × FV .f64)),
    (∀ n : Int, sinpiFn (Fl.ofInt n) = .ok (fzero .f64)) →
    (∀ n : Int, cospiFn (Fl.ofInt n) =
      .ok (if n % 2 = 0 then fone .f64 else fneg (fone .f64))) →
    (∀ n : Int, sincospiFn (Fl.ofInt n) =
      .ok (fzero .f64, if n % 2 = 0 then fone .f64 else fneg (fone .f64))) →
    (∀ n : Int, tanpiFn (Fl.ofInt n) = .ok (fzero .f64)) →
    ∀ x n, sameType x = false → float x = Fl.ofInt n →
      realFallback float sameType "sinpi" sinpiFn x = .ok (fzero .f64) ∧
      realFallback float sameType "cospi" cospiFn x =
        .ok (if n % 2 = 0 then fone .f64 else fneg (fone .f64)) ∧
      realFallback float sameType "sincospi" sincospiFn x =
        .ok (fzero .f64, if n % 2 = 0 then fone .f64 else fneg (fone .f64)) ∧
      realFallback float sameType "tanpi" tanpiFn x = .ok (fzero .f64)



/-! Nothing to promise:
sin(::Float16)@1309: forwards to the Float32 method after conversion
cos(::Float16)@1309: forwards to the Float32 method after conversion
tan(::Float16)@1309: forwards to the Float32 method after conversion
asin(::Float16)@1309: forwards to the Float32 method after conversion
acos(::Float16)@1309: forwards to the Float32 method after conversion
atan(::Float16)@1309: forwards to the Float32 method after conversion
cosh(::Float16)@1309: forwards to the Float32 method after conversion
tanh(::Float16)@1309: forwards to the Float32 method after conversion
asinh(::Float16)@1309: forwards to the Float32 method after conversion
acosh(::Float16)@1309: forwards to the Float32 method after conversion
atanh(::Float16)@1309: forwards to the Float32 method after conversion
log(::Float16)@1309: forwards to the Float32 method after conversion
log2(::Float16)@1309: forwards to the Float32 method after conversion
log10(::Float16)@1309: forwards to the Float32 method after conversion
log1p(::Float16)@1309: forwards to the Float32 method after conversion
sin(::ComplexF16)@1310: forwards to the Float32 method after conversion
cos(::ComplexF16)@1310: forwards to the Float32 method after conversion
tan(::ComplexF16)@1310: forwards to the Float32 method after conversion
asin(::ComplexF16)@1310: forwards to the Float32 method after conversion
acos(::ComplexF16)@1310: forwards to the Float32 method after conversion
atan(::ComplexF16)@1310: forwards to the Float32 method after conversion
cosh(::ComplexF16)@1310: forwards to the Float32 method after conversion
tanh(::ComplexF16)@1310: forwards to the Float32 method after conversion
asinh(::ComplexF16)@1310: forwards to the Float32 method after conversion
acosh(::ComplexF16)@1310: forwards to the Float32 method after conversion
atanh(::ComplexF16)@1310: forwards to the Float32 method after conversion
log(::ComplexF16)@1310: forwards to the Float32 method after conversion
log2(::ComplexF16)@1310: forwards to the Float32 method after conversion
log10(::ComplexF16)@1310: forwards to the Float32 method after conversion
log1p(::ComplexF16)@1310: forwards to the Float32 method after conversion
exp(::ComplexF16)@1315: forwards to the Float32 method after conversion
exp2(::ComplexF16)@1315: forwards to the Float32 method after conversion
exp10(::ComplexF16)@1315: forwards to the Float32 method after conversion
sinh(::ComplexF16)@1315: forwards to the Float32 method after conversion
atan(::Float16, ::Float16)@1319: forwards to the Float32 method after conversion
sincos(::Float16)@1320: forwards to the Float32 method after conversion
sin(::Real)@1326: forwards to the float method after float(x)
cos(::Real)@1326: forwards to the float method after float(x)
tan(::Real)@1326: forwards to the float method after float(x)
asin(::Real)@1326: forwards to the float method after float(x)
atan(::Real)@1326: forwards to the float method after float(x)
acos(::Real)@1326: forwards to the float method after float(x)
sinh(::Real)@1326: forwards to the float method after float(x)
cosh(::Real)@1326: forwards to the float method after float(x)
tanh(::Real)@1326: forwards to the float method after float(x)
asinh(::Real)@1326: forwards to the float method after float(x)
acosh(::Real)@1326: forwards to the float method after float(x)
atanh(::Real)@1326: forwards to the float method after float(x)
exp(::Real)@1326: forwards to the float method after float(x)
exp2(::Real)@1326: forwards to the float method after float(x)
exp10(::Real)@1326: forwards to the float method after float(x)
expm1(::Real)@1326: forwards to the float method after float(x)
log(::Real)@1326: forwards to the float method after float(x)
log2(::Real)@1326: forwards to the float method after float(x)
log10(::Real)@1326: forwards to the float method after float(x)
log1p(::Real)@1326: forwards to the float method after float(x)
sqrt(::Real)@1326: forwards to the float method after float(x)
rad2deg(::Real)@254: forwards to the float method after float(x)
deg2rad(::Real)@255: forwards to the float method after float(x)
rad2deg(::Number)@256: forwards to the promoted arithmetic method
deg2rad(::Number)@257: forwards to the promoted arithmetic method
rad2deg(::AbstractFloat)@254: the docstring promise is the formula itself
deg2rad(::AbstractFloat)@255: the docstring promise is the formula itself
exp2(::AbstractFloat)@1340: the docstring promise is the formula itself
exp10(::AbstractFloat)@1341: the docstring promise is the formula itself
-/

def entries : List Entry := [
  { id := "mathfuncs-hypot-correctly-rounded", juliaFile := "base/math.jl"
    juliaFns := ["hypot(::Float64, ::Float64)"]
    statement := "With hardware fma, hypot(x, y) is the binary64 value nearest to sqrt(x^2+y^2) for all finite x, y with a finite result."
    source := "base/math.jl:732-795; hypot rounding specification"
    status := .todo, prop := ``HypotCorrectlyRounded64, thm := none },
  { id := "mathfuncs-exponent-rational", juliaFile := "base/math.jl"
    juliaFns := ["exponent(::Rational)", "exponent(::Real)"]
    statement := "exponent(num//den) is the largest y with 2^y <= |num//den|, for every nonzero Rational{Int64} in lowest terms."
    source := "base/math.jl:901-907; documented largest-power definition"
    status := .todo, prop := ``ExponentRationalDefinition, thm := none },
  { id := "mathfuncs-evalpoly-empty", juliaFile := "base/math.jl"
    juliaFns := ["evalpoly(x, ::Tuple)", "evalpoly(x, ::AbstractVector)"]
    statement := "evalpoly(x, ()) is the empty sum, a zero, for every Float64 x."
    source := "base/math.jl:75-98; polynomial-evaluation specification"
    status := .todo, prop := ``EvalpolyEmptyZero, thm := none },
  { id := "mathfuncs-minmax-isless", juliaFile := "base/math.jl"
    juliaFns := ["min(::Float64, ::Float64)", "max(::Float64, ::Float64)"]
    statement := "On non-NaN Float64 arguments, min and max agree with isless (so -0.0 < 0.0)."
    source := "base/math.jl:833-839; IEEE total ordering"
    status := .todo, prop := ``MinmaxIsless, thm := none },
  { id := "mathfuncs-minmax-nan", juliaFile := "base/math.jl"
    juliaFns := ["min(::Float64, ::Float64)", "max(::Float64, ::Float64)", "minmax(::Float64, ::Float64)"]
    statement := "A NaN argument makes min, max and both parts of minmax NaN."
    source := "base/math.jl:833-839; IEEE NaN rules"
    status := .todo, prop := ``MinmaxNan, thm := none },
  { id := "mathfuncs-hypot-inf", juliaFile := "base/math.jl"
    juliaFns := ["hypot(::Float64, ::Float64)", "hypot(::Float64...)"]
    statement := "hypot of arguments including an infinity is Inf, even with NaN arguments (2 and n arguments)."
    source := "base/math.jl:732-828; IEEE infinity rules"
    status := .todo, prop := ``HypotInfinity64, thm := none },
  { id := "mathfuncs-frexp-range", juliaFile := "base/math.jl"
    juliaFns := ["frexp(::Float64)", "ldexp(::Float64, ::Int)"]
    statement := "For nonzero finite x, frexp(x) = (f, e) has |f| in [1/2, 1) and ldexp(f, e) === x."
    source := "base/math.jl:854-897; frexp and ldexp decomposition"
    status := .todo, prop := ``FrexpRoundTripRange, thm := none },
  { id := "mathfuncs-exponent-float", juliaFile := "base/math.jl"
    juliaFns := ["exponent(::Float64)"]
    statement := "For nonzero finite Float64 x, exponent(x) is the largest y with 2^y <= |x|."
    source := "base/math.jl:900-950; exponent docstring and method"
    status := .todo, prop := ``ExponentFloatRange, thm := none },
  { id := "mathfuncs-evalpoly-horner", juliaFile := "base/math.jl"
    juliaFns := ["evalpoly(x, ::Tuple)", "evalpoly(x, ::AbstractVector)", "@evalpoly", "@horner"]
    statement := "Tuple, vector and macro evaluation fold polynomial coefficients from highest degree to the constant term using Horner's recurrence."
    source := "base/math.jl:75-98,157-160,189-192"
    status := .todo, prop := ``EvalpolyHornerOrder, thm := none },
  { id := "mathfuncs-complex-evalpoly-horner", juliaFile := "base/math.jl"
    juliaFns := ["evalpoly(z::Complex, p::Tuple)", "evalpoly(z::Complex, p::AbstractVector)", "_evalpoly(z::Complex, p)"]
    statement := "Complex polynomial evaluation follows the source's descending-coefficient recurrence for every coefficient vector."
    source := "base/math.jl:100-148"
    status := .todo, prop := ``ComplexEvalpolyHornerOrder, thm := none },
  { id := "mathfuncs-rad-deg-special-values", juliaFile := "base/math.jl"
    juliaFns := ["rad2deg(::AbstractFloat)", "deg2rad(::AbstractFloat)"]
    statement := "Both angle conversions preserve signed zero, NaN, and infinity classifications for Float16, Float32, and Float64."
    source := "base/math.jl:213-255"
    status := .todo, prop := ``AngleConversionExceptionalValues, thm := none },
  { id := "mathfuncs-significand-range", juliaFile := "base/math.jl"
    juliaFns := ["significand(::Float64)", "exponent(::Float64)", "ldexp(::Float64, ::Int)"]
    statement := "For nonzero finite x, significand(x) has the sign of x, |significand(x)| in [1,2), and x == ldexp(significand(x), exponent(x))."
    source := "base/math.jl:936-950,1001-1038; significand and exponent contracts"
    status := .todo, prop := ``SignificandRange, thm := none },
  { id := "mathfuncs-hypot-sign", juliaFile := "base/math.jl"
    juliaFns := ["hypot(::Float64, ::Float64)"]
    statement := "hypot(x, y) does not depend on the signs of x and y."
    source := "base/math.jl:732-786; absolute-value normalization"
    status := .todo, prop := ``HypotSignAndZeroInvariant64, thm := none },
  { id := "mathfuncs-hypot-finite-safety", juliaFile := "base/math.jl"
    juliaFns := ["hypot(::Float64, ::Float64)"]
    statement := "For finite Float64 inputs whose exact hypotenuse is at most Float64's largest finite value, hypot returns a finite result."
    source := "base/math.jl:732-786; overflow and underflow scaling"
    status := .todo, prop := ``HypotFiniteSafety64, thm := none },
  { id := "mathfuncs-domain-errors", juliaFile := "base/math.jl"
    juliaFns := ["sqrt(::IEEEFloat)"]
    statement := "A negative real square-root argument raises DomainError."
    source := "base/math.jl:629-632"
    status := .todo, prop := ``SqrtNegativeDomainError, thm := none },
  { id := "mathfuncs-log-domain-propagation", juliaFile := "base/math.jl"
    juliaFns := ["log(b::T, x::T)", "log(b::Number, x::Number)"]
    statement := "A DomainError from log(x) or, after log(x) succeeds, log(b) propagates from the logarithm-base methods."
    source := "base/math.jl:259-304"
    status := .todo, prop := ``LogBaseNegativeDomainError, thm := none },
  { id := "mathfuncs-nan-domain-error", juliaFile := "base/math.jl"
    juliaFns := ["nan_dom_err(out, x)"]
    statement := "A NaN output for a non-NaN input raises DomainError with the documented message; other outputs pass through."
    source := "base/math.jl:399"
    status := .todo, prop := ``NanDomainError, thm := none },
  { id := "mathfuncs-modf-parts", juliaFile := "base/math.jl"
    juliaFns := ["modf(x::T) where T<:IEEEFloat"]
    statement := "For every finite IEEE input, modf's parts sum exactly to x and its fractional part has x's sign, including signed zero."
    source := "base/math.jl:1163-1170"
    status := .todo, prop := ``ModfPartsAndSigns, thm := none },
  { id := "mathfuncs-mod2pi-range", juliaFile := "base/math.jl"
    juliaFns := ["mod2pi(x)"]
    statement := "mod2pi returns the RoundDown rem2pi result in the documented interval [0,2π)."
    source := "base/math.jl:1218-1241; rem2pi rounding-mode contract"
    status := .todo, prop := ``Mod2PiRange, thm := none },

  { id := "mathfuncs-minmax-signed-zero", juliaFile := "base/math.jl"
    juliaFns := ["min(::Float64, ::Float64)", "max(::Float64, ::Float64)", "minmax(::Float64, ::Float64)"]
    statement := "For opposite signed zeros, min returns -0.0 and max returns +0.0, and minmax returns both in that order."
    source := "base/math.jl:833-839; IEEE signed-zero order"
    status := .todo, prop := ``MinmaxSignedZero, thm := none },
  { id := "mathfuncs-hypot-nan", juliaFile := "base/math.jl"
    juliaFns := ["hypot(::Float64, ::Float64)", "hypot(::Float64...)"]
    statement := "Without an infinity, any NaN argument makes every two- or many-argument Float64 hypot result NaN."
    source := "base/math.jl:732-828; NaN behavior"
    status := .todo, prop := ``HypotNaN64, thm := none },
  { id := "mathfuncs-exponent-domain-errors", juliaFile := "base/math.jl"
    juliaFns := ["exponent(::IEEEFloat)"]
    statement := "Exponent rejects signed zero with DomainError and rejects either infinity or NaN with DomainError."
    source := "base/math.jl:936-950"
    status := .todo, prop := ``ExponentFloatDomainErrors, thm := none },
  { id := "mathfuncs-exponent-zero-errors", juliaFile := "base/math.jl"
    juliaFns := ["exponent(::Integer)", "exponent(::Base.BitInteger)", "exponent(::Bool)"]
    statement := "The integer and Boolean exponent methods raise DomainError on zero."
    source := "base/math.jl:980-998"
    status := .todo, prop := ``ExponentZeroDomainErrors, thm := none },
  { id := "mathfuncs-fourthroot-domain", juliaFile := "base/math.jl"
    juliaFns := ["fourthroot(::Number)"]
    statement := "A negative real argument to fourthroot raises DomainError through sqrt."
    source := "base/math.jl:685"
    status := .todo, prop := ``FourthrootNegativeDomainError, thm := none },
  { id := "mathfuncs-hypot-one", juliaFile := "base/math.jl"
    juliaFns := ["hypot(x::Number)"]
    statement := "One-argument hypot equals the absolute value of the floating-point conversion."
    source := "base/math.jl:729"
    status := .todo, prop := ``HypotOneFloat, thm := none },
  { id := "mathfuncs-hypot-infinity-overloads", juliaFile := "base/math.jl"
    juliaFns := ["hypot(x)", "hypot(x,y)", "hypot(x,y,z...)", "_hypot(x,y)", "_hypot(::Float32,::Float32)", "_hypot(::Float16,::Float16)", "_hypot(::ComplexF16,::ComplexF16)", "_hypot(::NTuple{N,Number})", "_hypot(::NTuple{N,<:IEEEFloat})"]
    statement := "Every source hypot implementation returns positive infinity when an operand's magnitude is infinite, even when another operand is NaN."
    source := "base/math.jl:732-828,789-803"
    status := .todo, prop := ``HypotSourceInfinityBranches, thm := none },
  { id := "mathfuncs-atan-noop-error", juliaFile := "base/math.jl"
    juliaFns := ["atan(y::T, x::T) where {T<:AbstractFloat}"]
    statement := "The generic AbstractFloat atan fallback raises ErrorException with the exact no_op_err message for every selected floating-point type."
    source := "base/math.jl:831; base/promotion.jl:650"
    status := .todo, prop := ``AtanNoOpError, thm := none },
  { id := "mathfuncs-missing-propagation", juliaFile := "base/math.jl"
    juliaFns := ["$(f)(::Missing)", "$(f)(::Missing, ::Missing)", "$(f)(::Number, ::Missing)", "$(f)(::Missing, ::Number)", "fourthroot(::Missing)"]
    statement := "Generated unary, binary, and fourthroot Missing overloads return Missing."
    source := "base/math.jl:1331,1335-1337,1342"
    status := .todo, prop := ``MissingPropagation, thm := none },
]

end JuliaLean.Proofs.base.math
