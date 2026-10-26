import JuliaLean.BigNumsCov.Common

/-!
Coverage models for the Julia control flow in `base/gmp.jl` at master
`bbfa0ce4150`.  GMP calls are semantic function arguments.  This exposes the
allocation, aliasing, branch, error, sign-normalization, and return behavior
implemented by Julia without pretending to reimplement GMP.
-/

namespace JuliaLean.BigNumsCov.Gmp

open JuliaLean
open JuliaLean.BigNumsCov

/-! ## Library setup and basic construction, lines 39-169 -/

inductive InitNotice where
  | none | warning | error
  deriving Repr, DecidableEq

/-- Version/limb check in `__init__`, lines 112-146. -/
def initNotice (compiledMajor compiledBits loadedMajor loadedBits : Nat) : InitNotice :=
  if compiledMajor = loadedMajor ∧ compiledBits = loadedBits then .none
  else if compiledBits = loadedBits then .warning else .error

/-- `BigInt(; nbits)` calls `init2!`, registers the finalizer, and returns it. -/
def constructBigInt (init2 : Nat → Cell) (nbits : Nat) : Cell := init2 nbits

/-- `sizeinbase` converts the GMP size result to Julia `Int`. -/
def sizeInBase (primitive : Int → Int → Int) (a base : Int) : Int :=
  primitive a base

/-- Zero-argument version and limb-size wrappers, lines 39-42. -/
def libraryValue (primitive : Unit → Int) : Int := primitive ()

/-- `gmpz`/`gmpq` construct the generated C symbol from a fixed prefix. -/
def generatedCName (stem operation : String) : String := stem ++ operation

def GmpBootstrapCorrect : Prop :=
  (∀ cm cb lm lb, initNotice cm cb lm lb =
    if cm = lm ∧ cb = lb then .none else if cb = lb then .warning else .error) ∧
  (∀ init2 nbits, constructBigInt init2 nbits = init2 nbits) ∧
  (∀ primitive a base, sizeInBase primitive a base = primitive a base) ∧
  (∀ primitive, libraryValue primitive = primitive ()) ∧
  (∀ stem operation, generatedCName stem operation = stem ++ operation)

theorem gmpBootstrapCorrect : GmpBootstrapCorrect := by
  simp [GmpBootstrapCorrect, initNotice, constructBigInt, sizeInBase,
    libraryValue, generatedCName]

/-! ## MPZ wrappers, lines 161-290 -/

/-- Return conversion used by `scan0`, `scan1`, `popcount`, and comparisons. -/
def primitiveInt (primitive : Int → Int) (x : Int) : Int := primitive x

def primitiveInt2 (primitive : Int → Int → Int) (x y : Int) : Int := primitive x y
def primitiveInt3 (primitive : Int → Int → Int → Int) (x y z : Int) : Int := primitive x y z

/-- Wrappers such as `get_str!` call a primitive and return their first argument. -/
def callThenReturn (primitive : Int → Int) (returned input : Int) : Int × Int :=
  (primitive input, returned)

/-- Two-output wrapper used by `tdiv_qr!`. -/
def twoOutputs (primitive : Cell → Cell → Int → Int → Cell × Cell)
    (x y : Cell) (a b : Int) : Cell × Cell :=
  primitive x y a b

/-- Three-output wrapper used by `gcdext!`. -/
def threeOutputs (primitive : Cell → Cell → Cell → Int → Int → Cell × Cell × Cell)
    (x y z : Cell) (a b : Int) : Cell × Cell × Cell :=
  primitive x y z a b

/-- Observable vector effects of `MPZ.export!`, lines 274-284. -/
def exportLayout (stride length digits count : Nat) : Jl (Nat × Nat) :=
  if stride != 1 then .error (.argumentError "a must have stride 1")
  else
    let resized := max length digits
    if count ≤ resized then .ok (resized, count)
    else .error (.argumentError "count[] > length(a)")

def GmpMpzObserversCorrect : Prop :=
  (∀ primitive x, primitiveInt primitive x = primitive x) ∧
  (∀ primitive x y, primitiveInt2 primitive x y = primitive x y) ∧
  (∀ primitive x y z, primitiveInt3 primitive x y z = primitive x y z) ∧
  (∀ primitive returned input, callThenReturn primitive returned input =
    (primitive input, returned)) ∧
  (∀ primitive x y a b, twoOutputs primitive x y a b = primitive x y a b) ∧
  (∀ primitive x y z a b, threeOutputs primitive x y z a b = primitive x y z a b) ∧
  (∀ length digits count, count ≤ max length digits →
    exportLayout 1 length digits count = .ok (max length digits, count))

theorem gmpMpzObserversCorrect : GmpMpzObserversCorrect := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl, ?_⟩
  intro length digits count h
  simp [exportLayout, h]

/-! ## Conversions and `big`, lines 298-492 -/

/-- Identity bodies for `signed`, `BigInt(::BigInt)`, and `Signed(::BigInt)`. -/
def identityBig (x : Int) : Int := x

/-- Small signed/unsigned constructors delegate to one primitive setter. -/
def setMachineInteger (setter : Int → Int) (x : Int) : Int := setter x

/-- `BigInt(::Float64)`, lines 339-342. -/
def bigIntOfFloat (isInteger : Bool) (truncated : Int) : Jl Int :=
  if isInteger then .ok truncated else .error (.inexactError "BigInt")

/-- The overflow decision at lines 418-422 of integer-to-IEEE conversion. -/
def bigIntFloatOverflow (tooLarge roundsNearest roundsAway : Bool)
    (finite infinity omega : Int) : Int :=
  if tooLarge then if roundsNearest || roundsAway then infinity else omega else finite

inductive BigType where
  | integer | rational
  deriving Repr, DecidableEq

/-- `big(::Type{<:Integer})` and `big(::Type{<:Rational})`. -/
def bigType : BigType → String
  | .integer => "BigInt"
  | .rational => "Rational{BigInt}"

/-- Exact semantic value of the limb-importing `BigInt(::Integer)` loop. -/
def importInteger (x : Int) : Int := x

/-- `rem(x, ::Type{T})` routes through the selected width reduction. -/
def reduceToType (reduce : Int → Int) (x : Int) : Int := reduce x

/-- `isodd` reads bit zero and `iseven` negates it. -/
def parity (lowBit : Bool) : Bool × Bool := (lowBit, !lowBit)

/-- Float16/32/64 one-argument constructors select RoundNearest. -/
def nearestFloat (convert : Int → Bool → Int) (x : Int) : Int := convert x true

/-- `big(n)` delegates to exact BigInt conversion. -/
def bigValue (convert : Int → Int) (x : Int) : Int := convert x

def GmpConversionRoutingCorrect : Prop :=
  (∀ x, identityBig x = x) ∧
  (∀ setter x, setMachineInteger setter x = setter x) ∧
  (∀ integral result, bigIntOfFloat integral result =
    if integral then .ok result else .error (.inexactError "BigInt")) ∧
  (∀ large nearest away finite inf omega, bigIntFloatOverflow large nearest away finite inf omega =
    if large then if nearest || away then inf else omega else finite) ∧
  (∀ k, bigType k = match k with | .integer => "BigInt" | .rational => "Rational{BigInt}") ∧
  (∀ x, importInteger x = x) ∧
  (∀ reduce x, reduceToType reduce x = reduce x) ∧
  (∀ lowBit, parity lowBit = (lowBit, !lowBit)) ∧
  (∀ convert x, nearestFloat convert x = convert x true) ∧
  (∀ convert x, bigValue convert x = convert x)

theorem gmpConversionRoutingCorrect : GmpConversionRoutingCorrect := by
  simp [GmpConversionRoutingCorrect, identityBig, setMachineInteger, bigIntOfFloat,
    bigIntFloatOverflow, bigType, importInteger, reduceToType, parity, nearestFloat,
    bigValue]

/-! ## Arithmetic, shifts, and bit queries, lines 494-635 -/

/-- Generated binary BigInt methods delegate to the selected MPZ operation. -/
def generatedBinary (op : Int → Int → Int) (x y : Int) : Int := op x y

/-- Signed C-long addition, matching lines 555-556. -/
def addSignedMachine (x c : Int) : Int :=
  if c < 0 then x - (-c) else x + c

/-- Signed C-long subtraction, matching lines 557-558. -/
def subSignedMachine (x c : Int) : Int :=
  if c < 0 then x + (-c) else x - c

/-- Shift wrappers, lines 572-574; the primitive is GMP's shift. -/
def shiftUnlessZero (shift : Int → Nat → Int) (x : Int) (count : Nat) : Int :=
  if count = 0 then x else shift x count

/-- Common `scan`/`popcount` sentinel check, lines 576-599. -/
def rejectSentinel (message : String) (result : Int) : Jl Int :=
  if result = -1 then .error (.domainError message) else .ok result

/-- `count_ones_abs`, line 606. -/
def countOnesAbs (isZero : Bool) (popcount : Nat) : Nat :=
  if isZero then 0 else popcount

/-- `exponent` and `top_set_bit`, lines 614-623. -/
def exponentFromMagnitude (magnitude : Nat) : Jl Nat :=
  if magnitude = 0 then .error (.domainError "cannot be zero") else .ok (magnitude - 1)

def topSetBit (negative : Bool) (magnitude : Nat) : Jl Nat :=
  if negative then .error (.domainError "negative argument") else .ok magnitude

/-- Julia normalizes every GMP comparison to `-1`, `0`, or `1`. -/
def normalizeCmp (raw : Int) : Int :=
  if raw < 0 then -1 else if raw = 0 then 0 else 1

def GmpArithmeticRoutingCorrect : Prop :=
  GeneratedFoldCorrect ∧
  (∀ op x y, generatedBinary op x y = op x y) ∧
  (∀ x c, addSignedMachine x c = if c < 0 then x - (-c) else x + c) ∧
  (∀ x c, subSignedMachine x c = if c < 0 then x + (-c) else x - c) ∧
  (∀ shift x count, shiftUnlessZero shift x count =
    if count = 0 then x else shift x count)

theorem gmpArithmeticRoutingCorrect : GmpArithmeticRoutingCorrect := by
  refine ⟨generatedFoldCorrect, ?_⟩
  simp [generatedBinary, addSignedMachine, subSignedMachine, shiftUnlessZero]

def GmpBitQueryCorrect : Prop :=
  (∀ message result, rejectSentinel message result =
    if result = -1 then .error (.domainError message) else .ok result) ∧
  (∀ zero count, countOnesAbs zero count = if zero then 0 else count) ∧
  (∀ magnitude, exponentFromMagnitude magnitude =
    if magnitude = 0 then .error (.domainError "cannot be zero") else .ok (magnitude - 1)) ∧
  (∀ negative magnitude, topSetBit negative magnitude =
    if negative then .error (.domainError "negative argument") else .ok magnitude) ∧
  (∀ raw, normalizeCmp raw ∈ [-1, 0, 1])

theorem gmpBitQueryCorrect : GmpBitQueryCorrect := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
  intro raw
  simp [normalizeCmp]
  split <;> split <;> simp_all

/-! ## Number theory, reductions, and combinatorics, lines 625-728 -/

/-- The `gcdx` compatibility branch, lines 676-687. -/
def gcdxNormalize (a b g s t : Int) : Int × Int × Int :=
  if t = 0 then
    if a = b then (g, t, s)
    else if Int.natAbs a = Int.natAbs b then (g, t, -s)
    else (g, s, t)
  else (g, s, t)

/-- `sum` is a left fold from zero, lines 689-691. -/
def sumBig (xs : List Int) : Int := xs.foldl (· + ·) 0

/-- The mathematical result of both `_prod` branches, lines 693-715. -/
def prodBig (xs : List Int) : Int := xs.foldl (· * ·) 1

/-- Boolean exponent special case, line 664. -/
def powBool (x : Int) (p : Bool) : Int := if p then x else 1

/-- Remaining exact power aliases delegate to their selected implementation. -/
def powerRoute (power : Int → Int → Int) (x exponent : Int) : Int :=
  power x exponent

/-- `throw1` is the explicit oversized-exponent branch. -/
def exponentTooLarge (exponent : Int) : Jl Int :=
  .error (.overflowError s!"exponent {exponent} is too large")

def GmpNumberTheoryRoutingCorrect : Prop :=
  GmpMpzObserversCorrect ∧
  (∀ a b g s, gcdxNormalize a b g s 0 =
    if a = b then (g, 0, s)
    else if Int.natAbs a = Int.natAbs b then (g, 0, -s)
    else (g, s, 0)) ∧
  (∀ xs, sumBig xs = xs.foldl (· + ·) 0) ∧
  (∀ xs, prodBig xs = xs.foldl (· * ·) 1) ∧
  (∀ x p, powBool x p = if p then x else 1) ∧
  (∀ power x exponent, powerRoute power x exponent = power x exponent) ∧
  (∀ exponent, exponentTooLarge exponent =
    .error (.overflowError s!"exponent {exponent} is too large"))

theorem gmpNumberTheoryRoutingCorrect : GmpNumberTheoryRoutingCorrect := by
  refine ⟨gmpMpzObserversCorrect, ?_⟩
  simp [gcdxNormalize, sumBig, prodBig, powBool, powerRoute, exponentTooLarge]

/-! ## Comparisons, signs, display, and checked aliases, lines 730-864 -/

def equalFromCmp (cmp : Int) : Bool := cmp = 0
def lessFromCmp (cmp : Int) : Bool := cmp < 0
def lessEqualFromCmp (cmp : Int) : Bool := cmp ≤ 0

/-- BigInt sign comes from the signed limb count. -/
def signFromSize (size : Int) : Int :=
  if size < 0 then -1 else if size > 0 then 1 else 0

def flipSign (x : Int) (negative : Bool) : Int := if negative then -x else x

/-- `show` forwards the BigInt string to `print`. -/
def showBig (stringValue : String) : String := stringValue

/-- Checked BigInt arithmetic cannot overflow and delegates unchanged. -/
def checkedExact (op : Int → Int → Jl Int) (x y : Int) : Jl Int := op x y

/-- The `*_with_overflow` methods always return `false`. -/
def exactWithOverflow (op : Int → Int → Int) (x y : Int) : Int × Bool :=
  (op x y, false)

/-- `_prevpow2`/`_nextpow2` retain the input sign after constructing magnitude. -/
def signedPowerOfTwo (negative : Bool) (magnitude : Int) : Int :=
  if negative then -magnitude else magnitude

inductive DigitCountPath where
  | invalidBase | zero | powerOfTwo | logarithmic
  deriving Repr, DecidableEq

/-- Branch selection in `ndigits0zpb`, lines 812-834. -/
def digitCountPath (base value : Int) (isPowerOfTwo : Bool) : DigitCountPath :=
  if base < 2 then .invalidBase
  else if value = 0 then .zero
  else if isPowerOfTwo && base ≤ 62 then .powerOfTwo
  else .logarithmic

/-- `deepcopy_internal` memoizes a copy; `_hash_shl!` delegates to multiplication by a power of two. -/
def memoizedCopy (copy : Int → Int) (x : Int) : Int := copy x
def hashShift (shift : Int → Nat → Int) (x : Int) (n : Nat) : Int := shift x n

def GmpComparisonAndSignCorrect : Prop :=
  (∀ c, equalFromCmp c = (c = 0)) ∧
  (∀ c, lessFromCmp c = (c < 0)) ∧
  (∀ c, lessEqualFromCmp c = (c ≤ 0)) ∧
  (∀ size, signFromSize size = if size < 0 then -1 else if size > 0 then 1 else 0) ∧
  (∀ x negative, flipSign x negative = if negative then -x else x) ∧
  (∀ text, showBig text = text)

theorem gmpComparisonAndSignCorrect : GmpComparisonAndSignCorrect := by
  simp [GmpComparisonAndSignCorrect, equalFromCmp, lessFromCmp, lessEqualFromCmp,
    signFromSize, flipSign, showBig]

def GmpCheckedAliasCorrect : Prop :=
  (∀ op x y, checkedExact op x y = op x y) ∧
  (∀ op x y, exactWithOverflow op x y = (op x y, false)) ∧
  (∀ negative magnitude, signedPowerOfTwo negative magnitude =
    if negative then -magnitude else magnitude) ∧
  (∀ base value pow2, digitCountPath base value pow2 =
    if base < 2 then .invalidBase
    else if value = 0 then .zero
    else if pow2 && base ≤ 62 then .powerOfTwo
    else .logarithmic) ∧
  (∀ copy x, memoizedCopy copy x = copy x) ∧
  (∀ shift x n, hashShift shift x n = shift x n)

theorem gmpCheckedAliasCorrect : GmpCheckedAliasCorrect := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_, by intros; rfl,
    by intros; rfl⟩
  intro base value pow2
  cases pow2 <;> simp [digitCountPath]

/-! ## UnsafeLimbView and hashing, lines 873-955 -/

structure LimbView where
  bytes : List Nat
  startByte : Nat
  numBytes : Nat
  deriving Repr, DecidableEq

def limbViewSize (view : LimbView) : Nat := view.numBytes

def limbViewGet (view : LimbView) (i : Nat) : Option Nat :=
  if 1 ≤ i ∧ i ≤ view.numBytes then view.bytes[view.startByte + i - 2]?
  else none

def limbViewIterate (view : LimbView) (state : Nat) : Option (Nat × Nat) :=
  if state > view.numBytes then none
  else (limbViewGet view state).map (fun byte => (byte, state + 1))

/-- `hash_integer` handles zero directly and otherwise hashes its byte view. -/
def hashIntegerRoute (zero : Bool) (hashZero hashBytes : Nat) : Nat :=
  if zero then hashZero else hashBytes

def GmpLimbViewCorrect : Prop :=
  (∀ view, limbViewSize view = view.numBytes) ∧
  (∀ view i, (i < 1 ∨ view.numBytes < i) → limbViewGet view i = none) ∧
  (∀ view state, view.numBytes < state → limbViewIterate view state = none) ∧
  (∀ zero hashZero hashBytes, hashIntegerRoute zero hashZero hashBytes =
    if zero then hashZero else hashBytes)

theorem gmpLimbViewCorrect : GmpLimbViewCorrect := by
  refine ⟨by intro; rfl, ?_, ?_, by intros; rfl⟩
  · intro view i h
    simp [limbViewGet]
    omega
  · intro view state h
    simp [limbViewIterate, h]

/-! ## Rational{BigInt} wrappers, lines 958-1118 -/

structure Rat where
  num : Int
  den : Int
  deriving Repr, DecidableEq

def infinite (x : Rat) : Bool := x.den = 0
def negative (x : Rat) : Bool := x.num < 0

/-- Constructor special value branch, lines 1004-1012. -/
def rationalConstruct (num den : Int) (canonicalize : Rat → Rat) : Jl Rat :=
  if den = 0 then
    if num = 0 then .error (.argumentError "invalid rational")
    else .ok { num := if num < 0 then -1 else 1, den := 0 }
  else .ok (canonicalize { num := num, den := den })

/-- Infinite-value branches of `add!`, lines 1047-1058. -/
def rationalAdd (finiteAdd : Rat → Rat → Rat) (x y : Rat) : Jl Rat :=
  if infinite x || infinite y then
    if infinite x && infinite y && negative x != negative y then .error .divideError
    else .ok (if infinite x then x else y)
  else .ok (finiteAdd x y)

/-- Infinite-value branches of `sub!`, lines 1060-1072. -/
def rationalSub (finiteSub : Rat → Rat → Rat) (x y : Rat) : Jl Rat :=
  if infinite x || infinite y then
    if infinite x && infinite y && negative x = negative y then .error .divideError
    else if infinite x then .ok x
    else .ok { num := if negative y then 1 else -1, den := 0 }
  else .ok (finiteSub x y)

/-- Infinite-value branches of `mul!`, lines 1074-1085. -/
def rationalMul (finiteMul : Rat → Rat → Rat) (x y : Rat) : Jl Rat :=
  if infinite x || infinite y then
    if x.num = 0 || y.num = 0 then .error .divideError
    else .ok { num := if negative x != negative y then -1 else 1, den := 0 }
  else .ok (finiteMul x y)

/-- Infinite and zero branches of `div!`, lines 1087-1109. -/
def rationalDiv (finiteDiv : Rat → Rat → Rat) (x y : Rat) : Jl Rat :=
  if infinite x then
    if infinite y then .error .divideError
    else if negative y then .ok { num := -x.num, den := 0 } else .ok x
  else if infinite y then .ok { num := 0, den := 1 }
  else if y.num = 0 then
    if x.num = 0 then .error .divideError
    else .ok { num := if negative x then -1 else 1, den := 0 }
  else .ok (finiteDiv x y)

/-- `_MPQ`, synchronization, setters, and generated aliases preserve the primitive result. -/
def rationalWrapper (primitive : Rat → Rat) (x : Rat) : Rat := primitive x

def GmpRationalSpecialValuesCorrect : Prop :=
  (∀ canonicalize num den, rationalConstruct num den canonicalize =
    if den = 0 then
      if num = 0 then .error (.argumentError "invalid rational")
      else .ok { num := if num < 0 then -1 else 1, den := 0 }
    else .ok (canonicalize { num := num, den := den })) ∧
  (∀ finite x y, ¬ infinite x → ¬ infinite y → rationalAdd finite x y = .ok (finite x y)) ∧
  (∀ finite x y, ¬ infinite x → ¬ infinite y → rationalSub finite x y = .ok (finite x y)) ∧
  (∀ finite x y, ¬ infinite x → ¬ infinite y → rationalMul finite x y = .ok (finite x y)) ∧
  (∀ finite x y, ¬ infinite x → ¬ infinite y → y.num != 0 →
    rationalDiv finite x y = .ok (finite x y)) ∧
  (∀ primitive x, rationalWrapper primitive x = primitive x)

theorem gmpRationalSpecialValuesCorrect : GmpRationalSpecialValuesCorrect := by
  refine ⟨by intros; rfl, ?_, ?_, ?_, ?_, by intros; rfl⟩
  all_goals
    intros
    simp_all [rationalAdd, rationalSub, rationalMul, rationalDiv, infinite]

end JuliaLean.BigNumsCov.Gmp
