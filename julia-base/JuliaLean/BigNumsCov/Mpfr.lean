import JuliaLean.BigNumsCov.Common
import JuliaLean.BigNumsCov.Raw

/-!
Coverage models for Julia's MPFR wrapper in `base/mpfr.jl` at master
`bbfa0ce4150`.  MPFR calls remain semantic primitives; the definitions below
mirror Julia's dispatch, checks, special-value branches, state selection, and
return routing.
-/

namespace JuliaLean.BigNumsCov.Mpfr

open JuliaLean
open JuliaLean.BigNumsCov

/-! ## Setup and rounding modes, lines 44-110 -/

inductive Mode where
  | nearest | toZero | up | down | fromZero | faithful
  deriving Repr, DecidableEq

inductive PublicMode where
  | nearest | toZero | up | down | fromZero | tiesAway | tiesUp
  deriving Repr, DecidableEq

def toMode : PublicMode → Jl Mode
  | .nearest => .ok .nearest
  | .toZero => .ok .toZero
  | .up => .ok .up
  | .down => .ok .down
  | .fromZero => .ok .fromZero
  | .tiesAway => .error (.methodError "convert")
  | .tiesUp => .error (.methodError "convert")

def fromMode : Mode → Jl PublicMode
  | .nearest => .ok .nearest
  | .toZero => .ok .toZero
  | .up => .ok .up
  | .down => .ok .down
  | .fromZero => .ok .fromZero
  | .faithful => .error (.argumentError "invalid MPFR rounding mode code")

def roundsToNearest (mode : Mode) : Bool := mode = .nearest

def roundsAwayFromZero (mode : Mode) (signBit : Bool) : Bool :=
  if mode = .toZero then false
  else if mode = .up then !signBit
  else if mode = .down then signBit
  else true

def oppositeRound : Mode → Mode
  | .up => .down
  | .down => .up
  | mode => mode

/-- The two MPFR version-string wrappers, lines 44-45. -/
def libraryString (primitive : Unit → String) : String := primitive ()

/-- `__init__` sets both exponent limits in order, lines 47-55. -/
def initializeExponentRange (setEmin setEmax : Int → Int) (emin emax : Int) : Int × Int :=
  (setEmin emin, setEmax emax)

def MpfrRoundingModesCorrect : Prop :=
  (∀ mode, roundsToNearest mode = true ↔ mode = .nearest) ∧
  (∀ mode sign, roundsAwayFromZero mode sign =
    if mode = .toZero then false
    else if mode = .up then !sign
    else if mode = .down then sign
    else true) ∧
  (∀ mode, oppositeRound (oppositeRound mode) = mode)

theorem mpfrRoundingModesCorrect : MpfrRoundingModesCorrect := by
  refine ⟨?_, by intros; rfl, ?_⟩
  · intro mode
    cases mode <;> decide
  · intro mode
    cases mode <;> rfl

def MpfrSetupAndRoundingCorrect : Prop :=
  MpfrRoundingModesCorrect ∧
  (∀ primitive, libraryString primitive = primitive ()) ∧
  (∀ setEmin setEmax emin emax,
    initializeExponentRange setEmin setEmax emin emax = (setEmin emin, setEmax emax))

theorem mpfrSetupAndRoundingCorrect : MpfrSetupAndRoundingCorrect := by
  exact ⟨mpfrRoundingModesCorrect, by intros; rfl, by intros; rfl⟩

/-! ## BigFloat storage and scoped rounding, lines 149-254 -/

structure BigFloatRep where
  precision : Int
  sign : Int
  exponent : Int
  words : List Nat
  deriving Repr, DecidableEq

inductive Field where
  | precision | sign | exponent | data | other
  deriving Repr, DecidableEq

inductive FieldValue where
  | scalar (x : Int) | data (x : List Nat)
  deriving Repr, DecidableEq

/-- `_BigFloat(d)` stores the supplied allocation after pointer initialization. -/
def rawBigFloat (words : List Nat) : BigFloatRep :=
  { precision := 0, sign := 1, exponent := 0, words := words }

/-- `BigFloat(; precision)` validates and initializes a positive NaN. -/
def allocateBigFloat (precision nanExponent : Int) (words : List Nat) : Jl BigFloatRep :=
  if precision < 1 then .error (.domainError "precision cannot be less than 1")
  else .ok { precision := precision, sign := 1, exponent := nanExponent, words := words }

def getField (x : BigFloatRep) : Field → Jl FieldValue
  | .precision => .ok (.scalar x.precision)
  | .sign => .ok (.scalar x.sign)
  | .exponent => .ok (.scalar x.exponent)
  | .data => .ok (.data x.words)
  | .other => .error (.argumentError "FieldError")

def setField (x : BigFloatRep) (field : Field) (value : Int) : Jl BigFloatRep :=
  match field with
  | .sign => .ok { x with sign := value }
  | .exponent => .ok { x with exponent := value }
  | _ => .error (.argumentError "FieldError")

def dataGet (x : BigFloatRep) (i : Nat) : Jl Nat :=
  if i = 0 || x.words.length < i then .error .boundsError
  else
    match x.words[i - 1]? with
    | some value => .ok value
    | none => .error .boundsError

def dataSet (x : BigFloatRep) (i value : Nat) : Jl BigFloatRep :=
  if 1 ≤ i ∧ i ≤ x.words.length then .ok { x with words := x.words.set (i - 1) value }
  else .error .boundsError

/-- `rounding_raw` gives the scoped value precedence over the global ref. -/
def roundingRaw (localMode : Option Mode) (global : Mode) : Mode := localMode.getD global

/-- The two incompatible Ref conversions throw before reaching MPFR. -/
def incompatibleRef (kind : String) : Jl String :=
  .error (.argumentError s!"{kind} not compatible with mpfr")

/-- C conversion, pointer conversion, copying, and rounding setters are direct routes. -/
def routeValue (convert : Int → Int) (x : Int) : Int := convert x
def setRawRounding (_old newMode : Mode) : Mode := newMode

def MpfrStorageCorrect : Prop :=
  (∀ words, (rawBigFloat words).words = words) ∧
  (∀ precision nanExponent words, allocateBigFloat precision nanExponent words =
    if precision < 1 then .error (.domainError "precision cannot be less than 1")
    else .ok { precision := precision, sign := 1, exponent := nanExponent, words := words }) ∧
  (∀ x, getField x .precision = .ok (.scalar x.precision)) ∧
  (∀ x value, setField x .sign value = .ok { x with sign := value }) ∧
  (∀ x i, (i = 0 ∨ x.words.length < i) → dataGet x i = .error .boundsError) ∧
  (∀ x i value, (i = 0 ∨ x.words.length < i) → dataSet x i value = .error .boundsError) ∧
  (∀ localMode global, roundingRaw localMode global = localMode.getD global) ∧
  (∀ kind, incompatibleRef kind =
    .error (.argumentError s!"{kind} not compatible with mpfr")) ∧
  (∀ convert x, routeValue convert x = convert x) ∧
  (∀ old newMode, setRawRounding old newMode = newMode)

theorem mpfrStorageCorrect : MpfrStorageCorrect := by
  refine ⟨by intro; rfl, by intros; rfl, by intro; rfl, by intros; rfl, ?_, ?_,
    by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩
  · intro x i h
    simp [dataGet]
    omega
  · intro x i value h
    simp [dataSet]
    omega

/-! ## Constructors and conversion routing, lines 299-571 -/

/-- Copy constructor, lines 302-311. -/
def copyAtPrecision (copy : BigFloatRep → Int → BigFloatRep)
    (x : BigFloatRep) (precision : Int) : BigFloatRep :=
  if precision = x.precision then x else copy x precision

inductive FloatClass where
  | finite | zero | infinity | nan
  deriving Repr, DecidableEq

/-- The manual `Float64` constructor's special exponent branch, lines 330-371. -/
def constructFloat64 (kind : FloatClass) (sign precision finiteExponent : Int)
    (finiteWords : List Nat) : BigFloatRep :=
  match kind with
  | .zero => { precision := precision, sign := sign, exponent := -1, words := [] }
  | .infinity => { precision := precision, sign := sign, exponent := -3, words := [] }
  | .nan => { precision := precision, sign := sign, exponent := -2, words := [] }
  | .finite => { precision := precision, sign := sign, exponent := finiteExponent, words := finiteWords }

/-- Rational conversion evaluates the denominator under the opposite directed mode. -/
def constructRational (divide : Int → Int → Mode → Int)
    (num den : Int) (mode : Mode) : Int :=
  divide num den (oppositeRound mode)

/-- Integer rounding, lines 449-456. -/
def roundMachineInteger (rangeFlag inRange : Bool) (value : Int) : Jl Int :=
  if rangeFlag || !inRange then .error (.inexactError "round") else .ok value

/-- BigInt rounding, lines 458-463. -/
def roundBigInteger (rangeFlag : Bool) (value : Int) : Jl Int :=
  if rangeFlag then .error (.inexactError "round") else .ok value

/-- `Bool(::BigFloat)`, lines 479-483. -/
def boolOfBigFloat (zero one : Bool) : Jl Bool :=
  if zero then .ok false else if one then .ok true else .error (.inexactError "Bool")

/-- One-line constructor, unchecked-cast, promotion, and `big` aliases. -/
def constructorRoute (convert : Int → Mode → Int → Int)
    (x : Int) (mode : Mode) (precision : Int) : Int := convert x mode precision

def integralCast (isInteger : Bool) (truncate value : Int) : Jl Int :=
  if isInteger then .ok truncate else .error (.inexactError s!"integer/{value}")

def promotedBigFloat (route : Int → Int) (x : Int) : Int := route x

inductive IeeeResult where
  | finite | zero | infinity | nan | omega
  deriving Repr, DecidableEq

/-- Special-value and overflow routing in `to_ieee754`, lines 494-547. -/
def toIeeeClass (kind : FloatClass) (hugePositive hugeNegative toZero fromZero : Bool) : IeeeResult :=
  let regular := kind = .finite
  let toInf := regular && hugePositive && !toZero
  let toZ := regular && hugeNegative && !fromZero
  if regular && !toInf && !toZ then if hugePositive then .omega else .finite
  else if kind = .zero || toZ then .zero
  else if kind = .infinity || toInf then .infinity
  else .nan

def rationalOfFloatClass (kind : FloatClass) (significand exponent sign : Int) : Jl (Int × Int) :=
  match kind with
  | .nan => .error (.argumentError "invalid rational")
  | .infinity => .ok (sign, 0)
  | .zero => .ok (0, 1)
  | .finite => .ok (significand, 2 ^ exponent.toNat)

def MpfrConstructorRoutingCorrect : Prop :=
  (∀ copy x precision, copyAtPrecision copy x precision =
    if precision = x.precision then x else copy x precision) ∧
  (∀ divide num den mode, constructRational divide num den mode =
    divide num den (oppositeRound mode)) ∧
  (∀ rangeFlag inRange value, roundMachineInteger rangeFlag inRange value =
    if rangeFlag || !inRange then .error (.inexactError "round") else .ok value) ∧
  (∀ rangeFlag value, roundBigInteger rangeFlag value =
    if rangeFlag then .error (.inexactError "round") else .ok value) ∧
  (∀ zero one, boolOfBigFloat zero one =
    if zero then .ok false else if one then .ok true else .error (.inexactError "Bool")) ∧
  (∀ convert x mode precision, constructorRoute convert x mode precision =
    convert x mode precision) ∧
  (∀ isInteger truncate value, integralCast isInteger truncate value =
    if isInteger then .ok truncate else .error (.inexactError s!"integer/{value}")) ∧
  (∀ route x, promotedBigFloat route x = route x) ∧
  (∀ kind sign precision exponent words,
    constructFloat64 kind sign precision exponent words =
      match kind with
      | .zero => { precision := precision, sign := sign, exponent := -1, words := [] }
      | .infinity => { precision := precision, sign := sign, exponent := -3, words := [] }
      | .nan => { precision := precision, sign := sign, exponent := -2, words := [] }
      | .finite => { precision := precision, sign := sign, exponent := exponent, words := words })

theorem mpfrConstructorRoutingCorrect : MpfrConstructorRoutingCorrect := by
  simp [MpfrConstructorRoutingCorrect, copyAtPrecision, constructRational,
    roundMachineInteger, roundBigInteger, boolOfBigFloat, constructorRoute,
    integralCast, promotedBigFloat, constructFloat64]

def MpfrIeeeRoutingCorrect : Prop :=
  (∀ kind hp hn tz fz, toIeeeClass kind hp hn tz fz =
    let regular := kind = .finite
    let toInf := regular && hp && !tz
    let toZ := regular && hn && !fz
    if regular && !toInf && !toZ then if hp then .omega else .finite
    else if kind = .zero || toZ then .zero
    else if kind = .infinity || toInf then .infinity
    else .nan) ∧
  (∀ s e sign, rationalOfFloatClass .finite s e sign = .ok (s, 2 ^ e.toNat))

theorem mpfrIeeeRoutingCorrect : MpfrIeeeRoutingCorrect := by
  simp [MpfrIeeeRoutingCorrect, toIeeeClass, rationalOfFloatClass]

/-! ## Arithmetic and mathematical wrappers, lines 573-985 -/

/-- Generated arithmetic with the BigInt operand converted first. -/
def mixedArithmetic (convert : Int → Int) (op : Int → Int → Int) (x y : Int) : Int :=
  op x (convert y)

/-- MPFR functions for which a new NaN from a non-NaN input is a DomainError. -/
def domainCheckedUnary (inputNan outputNan : Bool) (input output : Int) : Jl Int :=
  if inputNan then .ok input
  else if outputNan then .error (.domainError "NaN result for non-NaN input")
  else .ok output

/-- `log1p` additionally rejects inputs below -1 before calling MPFR. -/
def log1pModel (inputNan belowMinusOne outputNan : Bool) (input output : Int) : Jl Int :=
  if inputNan then .ok input
  else if belowMinusOne then .error (.domainError "log1p will only return a complex result")
  else if outputNan then .error (.domainError "NaN result for non-NaN input")
  else .ok output

/-- `minmax`, lines 897-901. -/
def minmaxModel (xNan yNan xLess : Bool) (x y : Int) : Int × Int :=
  if xNan then (x, x) else if yNan then (y, y) else if xLess then (x, y) else (y, x)

/-- `sum(::AbstractArray{BigFloat})`, lines 934-941. -/
def sumRounded (add : Int → Int → Int) (xs : List Int) : Int := xs.foldl add 0

/-- Tuple-returning and scaled wrappers preserve call order and primitive results. -/
def pairedUnary (first second : Int → Int) (x : Int) : Int × Int :=
  (first x, second x)

def scaledUnary (primitive : Int → Int → Int) (x scale : Int) : Int :=
  primitive x scale

def splitPrimitive (primitive : Int → Int × Int) (x : Int) : Int × Int :=
  primitive x

def MpfrArithmeticRoutingCorrect : Prop :=
  MpfrWrapperCorrect ∧ GeneratedFoldCorrect ∧
  (∀ convert op x y, mixedArithmetic convert op x y = op x (convert y))

theorem mpfrArithmeticRoutingCorrect : MpfrArithmeticRoutingCorrect := by
  exact ⟨mpfrWrapperCorrect, generatedFoldCorrect, by intros; rfl⟩

def MpfrTranscendentalRoutingCorrect : Prop :=
  MpfrWrapperCorrect ∧
  (∀ iNan oNan input output, domainCheckedUnary iNan oNan input output =
    if iNan then .ok input
    else if oNan then .error (.domainError "NaN result for non-NaN input")
    else .ok output) ∧
  (∀ iNan below oNan input output, log1pModel iNan below oNan input output =
    if iNan then .ok input
    else if below then .error (.domainError "log1p will only return a complex result")
    else if oNan then .error (.domainError "NaN result for non-NaN input")
    else .ok output) ∧
  (∀ xn yn less x y, minmaxModel xn yn less x y =
    if xn then (x, x) else if yn then (y, y) else if less then (x, y) else (y, x)) ∧
  (∀ add xs, sumRounded add xs = xs.foldl add 0) ∧
  (∀ first second x, pairedUnary first second x = (first x, second x)) ∧
  (∀ primitive x scale, scaledUnary primitive x scale = primitive x scale) ∧
  (∀ primitive x, splitPrimitive primitive x = primitive x)

theorem mpfrTranscendentalRoutingCorrect : MpfrTranscendentalRoutingCorrect := by
  refine ⟨mpfrWrapperCorrect, ?_⟩
  simp [domainCheckedUnary, log1pModel, minmaxModel, sumRounded, pairedUnary,
    scaledUnary, splitPrimitive]

/-! ## Comparisons, precision, and classification, lines 990-1149 -/

/-- Mixed comparison's explicit NaN ordering, lines 994-1014. -/
def compareMixed (xNan yNan : Bool) (primitive : Int) : Int :=
  if xNan then if yNan then 0 else 1 else if yNan then -1 else primitive

def numericEqual (xNan yNan : Bool) (cmp : Int) : Bool :=
  !xNan && !yNan && cmp = 0

def numericLess (xNan yNan : Bool) (cmp : Int) : Bool :=
  !xNan && !yNan && cmp < 0

def numericLessEqual (xNan yNan : Bool) (cmp : Int) : Bool :=
  !xNan && !yNan && cmp ≤ 0

def signModel (zero nan negative : Bool) (x : Int) : Int :=
  if zero || nan then x else if negative then -1 else 1

/-- `setprecision`, lines 1069-1074. -/
def setPrecision (base precision converted : Int) : Jl Int :=
  if base ≤ 1 then .error (.domainError "base cannot be less than 2")
  else if precision ≤ 0 then .error (.domainError "precision cannot be less than 1")
  else .ok converted

/-- `exponent`, lines 1087-1093. -/
def exponentModel (zero finite : Bool) (mpfrExponent : Int) : Jl Int :=
  if zero || !finite then .error (.domainError "x must be non-zero and finite")
  else .ok (mpfrExponent - 1)

def classify (exponent zeroExp nanExp infExp : Int) : FloatClass :=
  if exponent = zeroExp then .zero
  else if exponent = nanExp then .nan
  else if exponent = infExp then .infinity
  else .finite

/-- Precision conversion, maxintfloat, frexp/significand, rounding, and fixed constants. -/
def convertPrecision (base precision converted : Int) : Int :=
  if base = 2 then precision else converted

def maxIntegerFloat (power : Int → Int → Int) (precision : Int) : Int :=
  power 2 precision

def frexpRoute (primitive : Int → Int × Int) (x : Int) : Int × Int := primitive x

def significandRoute (frexp : Int → Int × Int) (multiply : Int → Int → Int)
    (x : Int) : Int := multiply (frexp x).1 2

def integerPredicate (primitive : Int → Int) (x : Int) : Bool := primitive x != 0

def roundedValue (primitive : Int → Int) (x : Int) : Int := primitive x

def isInfinite : FloatClass → Bool | .infinity => true | _ => false
def isNanClass : FloatClass → Bool | .nan => true | _ => false
def isFiniteClass (kind : FloatClass) : Bool := !isInfinite kind && !isNanClass kind
def isZeroClass : FloatClass → Bool | .zero => true | _ => false
def isOneClass (equalOne : Bool) : Bool := equalOne
def isSubnormalClass (_kind : FloatClass) : Bool := false
def isPositiveClass (kind : FloatClass) (signBit : Bool) : Bool :=
  !signBit && !isZeroClass kind && !isNanClass kind
def isNegativeClass (kind : FloatClass) (signBit : Bool) : Bool :=
  signBit && !isZeroClass kind && !isNanClass kind

def fixedBigFloat (value : Int) : Int := value

def MpfrComparisonCorrect : Prop :=
  (∀ xn yn primitive, compareMixed xn yn primitive =
    if xn then if yn then 0 else 1 else if yn then -1 else primitive) ∧
  (∀ xn yn cmp, numericEqual xn yn cmp = (!xn && !yn && cmp = 0)) ∧
  (∀ xn yn cmp, numericLess xn yn cmp = (!xn && !yn && cmp < 0)) ∧
  (∀ xn yn cmp, numericLessEqual xn yn cmp = (!xn && !yn && cmp ≤ 0)) ∧
  (∀ zero nan negative x, signModel zero nan negative x =
    if zero || nan then x else if negative then -1 else 1)

theorem mpfrComparisonCorrect : MpfrComparisonCorrect := by
  simp [MpfrComparisonCorrect, compareMixed, numericEqual, numericLess,
    numericLessEqual, signModel]

def MpfrPrecisionAndClassificationCorrect : Prop :=
  MpfrWrapperCorrect ∧
  (∀ base precision converted, setPrecision base precision converted =
    if base ≤ 1 then .error (.domainError "base cannot be less than 2")
    else if precision ≤ 0 then .error (.domainError "precision cannot be less than 1")
    else .ok converted) ∧
  (∀ zero finite exp, exponentModel zero finite exp =
    if zero || !finite then .error (.domainError "x must be non-zero and finite")
    else .ok (exp - 1)) ∧
  (∀ exp ze ne ie, classify exp ze ne ie =
    if exp = ze then .zero else if exp = ne then .nan else if exp = ie then .infinity else .finite) ∧
  (∀ base precision converted, convertPrecision base precision converted =
    if base = 2 then precision else converted) ∧
  (∀ power precision, maxIntegerFloat power precision = power 2 precision) ∧
  (∀ primitive x, frexpRoute primitive x = primitive x) ∧
  (∀ frexp multiply x, significandRoute frexp multiply x = multiply (frexp x).1 2) ∧
  (∀ primitive x, integerPredicate primitive x = (primitive x != 0)) ∧
  (∀ primitive x, roundedValue primitive x = primitive x) ∧
  (∀ kind, isInfinite kind = true ↔ kind = .infinity) ∧
  (∀ kind, isNanClass kind = true ↔ kind = .nan) ∧
  (∀ kind, isZeroClass kind = true ↔ kind = .zero) ∧
  (∀ equalOne, isOneClass equalOne = equalOne) ∧
  (∀ kind, isSubnormalClass kind = false) ∧
  (∀ kind, isFiniteClass kind = (!isInfinite kind && !isNanClass kind)) ∧
  (∀ kind signBit, isPositiveClass kind signBit =
    (!signBit && !isZeroClass kind && !isNanClass kind)) ∧
  (∀ kind signBit, isNegativeClass kind signBit =
    (signBit && !isZeroClass kind && !isNanClass kind)) ∧
  (∀ value, fixedBigFloat value = value)

theorem mpfrPrecisionAndClassificationCorrect : MpfrPrecisionAndClassificationCorrect := by
  refine ⟨mpfrWrapperCorrect, ?_⟩
  simp [setPrecision, exponentModel, classify, convertPrecision, maxIntegerFloat,
    frexpRoute, significandRoute, integerPredicate, roundedValue, isFiniteClass,
    isInfinite, isNanClass, isZeroClass, isOneClass, isSubnormalClass,
    isPositiveClass, isNegativeClass, fixedBigFloat]
  constructor
  · intro kind
    cases kind <;> decide
  constructor
  · intro kind
    cases kind <;> decide
  · intro kind
    cases kind <;> decide

/-! ## Neighbor stepping, lines 1151-1168 -/

inductive StepDirection where
  | next | previous
  deriving Repr, DecidableEq

/-- `abs(::Int)` with Julia's wrapping negation at `typemin`. -/
def absInt64 (n : JInt64) : JInt64 :=
  if n.val < 0 then -n else n

/-- The negative-count branch shared by `nextfloat!` and `prevfloat!`. -/
def redirectStep (direction : StepDirection) (n : JInt64) : StepDirection × JInt64 :=
  if n.val < 0 then
    (match direction with | .next => .previous | .previous => .next, absInt64 n)
  else (direction, n)

/-- A negative step must become nonnegative before the opposite loop starts. -/
def BigFloatStepTerminates : Prop :=
  ∀ direction n, n.val < 0 → 0 ≤ (redirectStep direction n).2.val

theorem bigFloatStepTerminates_refuted : ¬ BigFloatStepTerminates := by
  intro h
  have bad := h .next (JInt.typemin .i64) (by decide)
  have hvalue : (redirectStep .next (JInt.typemin .i64)).2.val = IntTy.i64.min := by decide
  rw [hvalue] at bad
  have hmin : IntTy.i64.min = -9223372036854775808 := by decide
  omega

/-- Non-mutating neighbor calls duplicate exactly when the count is nonzero. -/
def neighborValue (step : Int → JInt64 → Int) (duplicate : Int → Int)
    (x : Int) (n : JInt64) : Int :=
  if n.val = 0 then x else step (duplicate x) n

/-- `eps`, `floatmin`, and `floatmax`, lines 1170-1173. -/
def neighborConstant (step : Int → Int) (x : Int) : Int := step x

def MpfrNeighborDerivedCorrect : Prop :=
  (∀ step duplicate x n, neighborValue step duplicate x n =
    if n.val = 0 then x else step (duplicate x) n) ∧
  (∀ step x, neighborConstant step x = step x)

theorem mpfrNeighborDerivedCorrect : MpfrNeighborDerivedCorrect := by
  simp [MpfrNeighborDerivedCorrect, neighborValue, neighborConstant]

/-! ## Scoped precision, formatting, exponent range, and flags, lines 1200-1332 -/

/-- Generic fallback restores the old precision whether the callback succeeds or throws. -/
def withPrecision (callback : Int → Jl Int) (old new : Int) : Jl Int × Int :=
  (callback new, old)

/-- BigFloat's scoped overload writes the converted value without validating. -/
def scopedSetPrecision (callback : Int → Int) (_base _precision converted : Int) : Jl Int :=
  .ok (callback converted)

/-- The documented equivalence to the validated global setter. -/
def ScopedPrecisionValidates : Prop :=
  ∀ callback base precision converted,
    scopedSetPrecision callback base precision converted = do
      let _ ← setPrecision base precision converted
      pure (callback converted)

theorem scopedPrecisionValidates_refuted : ¬ ScopedPrecisionValidates := by
  intro h
  have bad := h (fun x => x) 2 0 0
  change (Except.ok 0 : Jl Int) =
    Except.error (.domainError "precision cannot be less than 1") at bad
  cases bad

inductive PrettyBranch where
  | fixed | scientific
  deriving Repr, DecidableEq

/-- `_prettify_bigfloat` selects fixed notation exactly for exponents -4 through 5. -/
def prettyBranch (exponent : Int) : PrettyBranch :=
  if -5 < exponent ∧ exponent < 6 then .fixed else .scientific

def checkExponentResult (ret : Int) : Jl Unit :=
  if ret = 0 then .ok () else .error (.argumentError "Invalid MPFR exponent range")

/-- The `Union{}` overload at line 1217 always throws MethodError. -/
def emptyPrecisionCall (argumentCount : Nat) : Jl Nat :=
  .error (.methodError s!"setprecision/{argumentCount}")

/-- `string_mpfr` changes only the first locale comma to a decimal point. -/
def replaceFirstComma : List Char → List Char
  | [] => []
  | ',' :: rest => '.' :: rest
  | char :: rest => char :: replaceFirstComma rest

/-- `_string` and `show` choose exactly one source formatting branch. -/
def stringRoute (finite : Bool) (floatText prettyText : String) : String :=
  if finite then prettyText else floatText

def showRoute (compact : Bool) (shortText fullText : String) : String :=
  if compact then shortText else fullText

/-- Exponent queries, setters, deepcopy, and fixed-format aliases are direct wrappers. -/
def scalarPrimitive (primitive : Unit → Int) : Int := primitive ()
def deepCopyRoute (copy : Int → Int) (x : Int) : Int := copy x

/-- `lerpi`, lines 1320-1323. -/
def lerpRoute (divide : Int → Int → Int) (fma : Int → Int → Int → Int)
    (j d a b : Int) : Int :=
  let t := divide j d
  fma t b (fma (-t) a a)

inductive Decomposed where
  | nan | infinity (sign : Int) | zero (sign : Int) | finite (significand exponent sign : Int)
  deriving Repr, DecidableEq

def decomposeModel (kind : FloatClass) (significand exponent sign : Int) : Decomposed :=
  match kind with
  | .nan => .nan
  | .infinity => .infinity sign
  | .zero => .zero sign
  | .finite => .finite significand exponent sign

def flagRaised (primitive : Int) : Bool := primitive != 0

def MpfrStateAndFormattingCorrect : Prop :=
  (∀ callback old new, withPrecision callback old new = (callback new, old)) ∧
  (∀ exponent, prettyBranch exponent =
    if -5 < exponent ∧ exponent < 6 then .fixed else .scientific) ∧
  (∀ ret, checkExponentResult ret =
    if ret = 0 then .ok () else .error (.argumentError "Invalid MPFR exponent range")) ∧
  (∀ count, emptyPrecisionCall count = .error (.methodError s!"setprecision/{count}")) ∧
  (∀ chars, replaceFirstComma chars =
    match chars with
    | [] => []
    | ',' :: rest => '.' :: rest
    | char :: rest => char :: replaceFirstComma rest) ∧
  (∀ finite floatText prettyText, stringRoute finite floatText prettyText =
    if finite then prettyText else floatText) ∧
  (∀ compact shortText fullText, showRoute compact shortText fullText =
    if compact then shortText else fullText) ∧
  (∀ primitive, scalarPrimitive primitive = primitive ()) ∧
  (∀ copy x, deepCopyRoute copy x = copy x) ∧
  (∀ divide fma j d a b, lerpRoute divide fma j d a b =
    let t := divide j d
    fma t b (fma (-t) a a)) ∧
  (∀ kind s e sign, decomposeModel kind s e sign =
    match kind with
    | .nan => .nan
    | .infinity => .infinity sign
    | .zero => .zero sign
    | .finite => .finite s e sign) ∧
  (∀ primitive, flagRaised primitive = (primitive != 0))

theorem mpfrStateAndFormattingCorrect : MpfrStateAndFormattingCorrect := by
  simp [MpfrStateAndFormattingCorrect, withPrecision, prettyBranch,
    checkExponentResult, emptyPrecisionCall, stringRoute,
    showRoute, scalarPrimitive, deepCopyRoute, lerpRoute, decomposeModel, flagRaised]
  intro chars
  cases chars with
  | nil => rfl
  | cons char rest =>
      by_cases h : char = ','
      · subst char
        rfl
      · simp [replaceFirstComma]

end JuliaLean.BigNumsCov.Mpfr
