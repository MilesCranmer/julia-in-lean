import JuliaLean.base.gmp
import JuliaLean.base.int
import JuliaLean.base.div
import JuliaLean.base.intfuncs
import JuliaLean.Registry.Types

/-!
# Properties of `base/gmp.jl`

BigInt and Rational{BigInt} arithmetic, comparison, conversion and number-theoretic functions, stated over exact mathematical integers, rationals and IEEE order independently of the model bodies.
-/

namespace JuliaLean.Proofs.base.gmp

namespace Round1

open JuliaLean JuliaLean.base.gmp JuliaLean.base.float

/-- Representation consistency and realizable machine-length storage for a
live GMP integer; unused capacity is allowed and zero may have no limb storage.
The bound excludes machine length wraparound without imposing a practical RAM limit. -/
def GMPInput (x : BigInt) : Prop :=
  Valid x ∧ 0 ≤ x.alloc.val ∧ x.d.length < 2^62

/-- A mathematical integer is represented by a valid normalized GMP object,
including agreement of its limbs with its abstract numeric value. -/
def ConvRepresentsInteger (z : BigInt) (n : Int) : Prop :=
  GMPInput z ∧ z.val = n

/-- Both members of the source signed-machine union convert exactly to a valid
arbitrary-precision integer, including their most negative values.
Julia source: base/gmp.jl:333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/gmp.jl:64-88; doc/src/manual/integers-and-floating-point-numbers.md:555-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedMachineConstructionCorrect : Prop :=
  (∀ x : Clong, ConvRepresentsInteger (fromSignedLong x) x.val) ∧
  (∀ x : JInt .i32, ConvRepresentsInteger (fromInt32 x) x.val)

/-- Both members of the source unsigned-machine union convert exactly to a
valid arbitrary-precision integer without a signed-machine overflow.
Julia source: base/gmp.jl:334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/gmp.jl:64-88; doc/src/manual/integers-and-floating-point-numbers.md:555-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedMachineConstructionCorrect : Prop :=
  (∀ x : Culong, ConvRepresentsInteger (fromUnsignedLong x) x.val) ∧
  (∀ x : JInt .u32, ConvRepresentsInteger (fromUInt32 x) x.val)

def ConvFloatEqualsInteger {T : FTy} (x : FV T) (n : Int) : Prop :=
  x.isfinite = true ∧ 0 < x.toRat.2 ∧ x.toRat.1 = n * (x.toRat.2 : Int)

/-- The exact constructor's complete result contract: it succeeds exactly on
finite integral values, with normalized output, and otherwise reports InexactError. -/
def ConvExactFloatResult {T : FTy} (x : FV T) (result : Jl BigInt) : Prop :=
  match result with
  | .ok z => GMPInput z ∧ ConvFloatEqualsInteger x z.val
  | .error (.inexactError _) => ¬ ∃ n : Int, ConvFloatEqualsInteger x n
  | .error _ => False

/-- Float64 construction accepts every finite integral value exactly, including
both signed zeros, and rejects fractions, infinities and NaNs with InexactError.
Julia source: base/gmp.jl:339-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/gmp.jl:81-88; base/number.jl:9-14; base/docs/basedocs.jl:2014-2026 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def Float64ConstructionCorrect : Prop :=
  ∀ x : FV .f64, ConvExactFloatResult x (fromFloat64 x)

/-- Float16 construction preserves every exact integral input and rejects all
fractional or nonfinite inputs, using the original Float16 value as its specification.
Julia source: base/gmp.jl:344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/gmp.jl:81-88; base/number.jl:9-14; base/docs/basedocs.jl:2014-2026 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def Float16ConstructionCorrect : Prop :=
  ∀ x : FV .f16, ConvExactFloatResult x (fromFloat16 x)

/-- Float32 construction preserves every exact integral input and rejects all
fractional or nonfinite inputs, using the original Float32 value as its specification.
Julia source: base/gmp.jl:345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/gmp.jl:81-88; base/number.jl:9-14; base/docs/basedocs.jl:2014-2026 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def Float32ConstructionCorrect : Prop :=
  ∀ x : FV .f32, ConvExactFloatResult x (fromFloat32 x)

/-- A fixed-width remainder is the unique in-range representative of the
input integer's congruence class modulo the number of target values. -/
def ConvCongruentRepresentative (t : IntTy) (n : Int) (z : JInt t) : Prop :=
  t.min ≤ z.val ∧ z.val ≤ t.max ∧
  ∃ k : Int, n = z.val + k * (2 : Int)^t.bits

/-- Every signed or unsigned target at most one limb wide receives the unique
in-range integer congruent to the BigInt modulo the target's cardinality.
Julia source: base/gmp.jl:369-370 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:667-692; base/gmp.jl:51-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LimbRemainderConversionCorrect : Prop :=
  ∀ (t : IntTy) (x : BigInt), t.bits ≤ 64 → GMPInput x →
    ConvCongruentRepresentative t x.val (remLimb t x)

/-- The multi-limb fixed-width remainder has the documented congruence and
range for every built-in signed and unsigned integer target, including 128 bits.
Julia source: base/gmp.jl:372-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:10-36,667-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitRemainderConversionCorrect : Prop :=
  ∀ (t : IntTy) (x : BigInt), GMPInput x →
    ConvCongruentRepresentative t x.val (remBits t x)

/-- Oddness is exactly the existence of an odd mathematical integer value,
including negative inputs and zero.
Julia source: base/gmp.jl:384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:143-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def OddIntegerCorrect : Prop :=
  ∀ x : BigInt, GMPInput x →
    (JuliaLean.base.gmp.isodd x = true ↔ ∃ k : Int, x.val = 2*k + 1)

/-- Evenness is exactly divisibility of the mathematical integer by two,
including negative inputs and zero.
Julia source: base/gmp.jl:385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:163-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def EvenIntegerCorrect : Prop :=
  ∀ x : BigInt, GMPInput x →
    (JuliaLean.base.gmp.iseven x = true ↔ ∃ k : Int, x.val = 2*k)

def ConvExactBitsResult (t : IntTy) (n : Int) (result : Jl (JInt t)) : Prop :=
  match result with
  | .ok z => z.val = n
  | .error (.inexactError _) => n < t.min ∨ t.max < n
  | .error _ => False

/-- Conversion to any built-in unsigned integer succeeds exactly for values
within that target's range, preserving the integer, and otherwise raises InexactError.
Julia source: base/gmp.jl:387-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/docs/basedocs.jl:2014-2026; doc/src/manual/conversion-and-promotion.md:112-121; base/int.jl:18-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ExactUnsignedConversionCorrect : Prop :=
  ∀ (t : IntTy) (x : BigInt), t.signed = false → GMPInput x →
    ConvExactBitsResult t x.val (convertUnsigned t x)

/-- Conversion to any built-in signed integer succeeds exactly for values
within that target's range, including its most negative value, and otherwise raises InexactError.
Julia source: base/gmp.jl:396-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/docs/basedocs.jl:2014-2026; doc/src/manual/conversion-and-promotion.md:112-121; base/int.jl:18-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ExactSignedConversionCorrect : Prop :=
  ∀ (t : IntTy) (x : BigInt), t.signed = true → GMPInput x →
    ConvExactBitsResult t x.val (convertSigned t x)

/- Independent IEEE order/distance specification. Infinity's metric coordinate
   is one ulp past the largest finite value, as documented for conversion at
   base/rounding.jl:352-354. No source conversion or rounding kernel computes
   the expected answer. -/

def ConvRatEq (a b : Int × Nat) : Prop := a.1 * (b.2 : Int) = b.1 * (a.2 : Int)

def ConvRatLe (a b : Int × Nat) : Prop := a.1 * (b.2 : Int) ≤ b.1 * (a.2 : Int)

def ConvDistance (a b : Int × Nat) : Int × Nat :=
  (Int.ofNat ((a.1 * (b.2 : Int) - b.1 * (a.2 : Int)).natAbs), a.2 * b.2)

def ConvFloatMetric {T : FTy} (x : FV T) : Int × Nat :=
  if x.isinf then
    let magnitude : Int := Int.ofNat (2^(T.fmt.bias + 1))
    (if x.signbit then -magnitude else magnitude, 1)
  else x.toRat

def ConvFloatLeExact {T : FTy} (x : FV T) (q : Int × Nat) : Prop :=
  if x.isinf then x.signbit = true else ConvRatLe x.toRat q

def ConvExactLeFloat {T : FTy} (q : Int × Nat) (x : FV T) : Prop :=
  if x.isinf then x.signbit = false else ConvRatLe q x.toRat

def ConvFloatLe {T : FTy} (x y : FV T) : Prop :=
  if x.isinf then x.signbit = true ∨ (y.isinf = true ∧ y.signbit = false)
  else if y.isinf then y.signbit = false else ConvRatLe x.toRat y.toRat

def ConvFloatFloor {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  ConvFloatLeExact z q ∧
    ∀ y : FV T, y.isnan = false → ConvFloatLeExact y q → ConvFloatLe y z

def ConvFloatCeil {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  ConvExactLeFloat q z ∧
    ∀ y : FV T, y.isnan = false → ConvExactLeFloat q y → ConvFloatLe z y

def ConvFloatNearest {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  ∀ y : FV T, y.isnan = false →
    ConvRatLe (ConvDistance q (ConvFloatMetric z)) (ConvDistance q (ConvFloatMetric y))

def ConvFloatChoice {T : FTy} (r : RoundingMode) (n : Int) (z : FV T) : Prop :=
  z.isnan = false ∧ z.signbit = decide (n < 0) ∧
  let q : Int × Nat := (n, 1)
  match r with
  | .Down => ConvFloatFloor q z
  | .Up => ConvFloatCeil q z
  | .ToZero => if n < 0 then ConvFloatCeil q z else ConvFloatFloor q z
  | .FromZero => if n < 0 then ConvFloatFloor q z else ConvFloatCeil q z
  | .Nearest => ConvFloatNearest q z ∧
      (∀ y : FV T, y.isnan = false → ConvFloatNearest q y →
        ¬ ConvRatEq (ConvFloatMetric y) (ConvFloatMetric z) → z.toBits % 2 = 0)
  | .NearestTiesAway => ConvFloatNearest q z ∧
      (∀ y : FV T, y.isnan = false → ConvFloatNearest q y →
        ConvRatLe (ConvDistance (0, 1) (ConvFloatMetric y))
          (ConvDistance (0, 1) (ConvFloatMetric z)))
  | .NearestTiesUp => ConvFloatNearest q z ∧
      (∀ y : FV T, y.isnan = false → ConvFloatNearest q y → ConvFloatLe y z)

/-- Every IEEE target and every public rounding mode converts the exact BigInt
once to its directed or nearest representable neighbor, including ties and overflow.
Julia source: base/gmp.jl:409-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/docs/basedocs.jl:1942-1977; base/rounding.jl:25-110,352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ExplicitIEEEConversionCorrect : Prop :=
  ∀ (T : FTy) (x : BigInt) (r : RoundingMode), GMPInput x →
    ConvFloatChoice r x.val (toFloat T x r)

/-- Default Float64 conversion chooses the globally nearest representable
value to the exact BigInt, with even ties and the documented overflow threshold.
Julia source: base/gmp.jl:468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/docs/basedocs.jl:1961-1977; base/rounding.jl:352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DefaultFloat64ConversionCorrect : Prop :=
  ∀ x : BigInt, GMPInput x → ConvFloatChoice .Nearest x.val (toFloat64 x)

/-- Default Float32 conversion rounds the exact BigInt directly to the nearest
Float32, with even ties and overflow, without intermediate Float64 rounding.
Julia source: base/gmp.jl:469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/docs/basedocs.jl:1942-1958; base/gmp.jl:409-410; base/rounding.jl:352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DefaultFloat32ConversionCorrect : Prop :=
  ∀ x : BigInt, GMPInput x → ConvFloatChoice .Nearest x.val (toFloat32 x)

/-- Default Float16 conversion rounds the exact BigInt directly to the nearest
Float16, with even ties and overflow, without an intermediate wider-format rounding.
Julia source: base/gmp.jl:470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/gmp.jl:409-410; base/rounding.jl:25-110,352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DefaultFloat16ConversionCorrect : Prop :=
  ∀ x : BigInt, GMPInput x → ConvFloatChoice .Nearest x.val (toFloat16 x)

/- Independent integer specifications. These helpers do not call MPZ's
   binaryValue, unsignedValue, bitwiseInt, countBits, factorialNat or chooseLoop.
   GMPInput is supplied by the common fragment. -/

def ArithReturns (action : Jl BigInt) (contract : Int → Prop) : Prop :=
  ∃ z, action = .ok z ∧ contract z.val

def ArithDomainFailure {A : Type} (action : Jl A) : Prop :=
  ∃ message, action = .error (.domainError message)

def ArithOverflowFailure {A : Type} (action : Jl A) : Prop :=
  ∃ message, action = .error (.overflowError message)

def ArithDivides (a b : Int) : Prop := ∃ k : Int, b = a * k

def ArithRepeatedProduct (a b : Int) : Int :=
  let sum := (List.range b.natAbs).foldr (fun _ total => a + total) 0
  if b < 0 then -sum else sum

def ArithAddition (a b z : Int) : Prop :=
  z - a = b ∧ ∀ t : Int, z ≤ t ↔ b ≤ t - a

def ArithSubtraction (a b z : Int) : Prop :=
  z + b = a ∧ ∀ t : Int, z ≤ t ↔ a ≤ t + b

def ArithMultiplication (a b z : Int) : Prop := z = ArithRepeatedProduct a b

def ArithRemainderSign (r reference : Int) : Prop :=
  r = 0 ∨ (r < 0 ↔ reference < 0)

def ArithDivisionPair (mode : DivisionMode) (a b q r : Int) : Prop :=
  a = q * b + r ∧ r.natAbs < b.natAbs ∧
  match mode with
  | .toZero => ArithRemainderSign r a
  | .down => ArithRemainderSign r b
  | .up => ArithRemainderSign r (-b)

def ArithQuotient (mode : DivisionMode) (a b q : Int) : Prop :=
  ∃ r : Int, ArithDivisionPair mode a b q r

def ArithRemainder (mode : DivisionMode) (a b r : Int) : Prop :=
  ∃ q : Int, ArithDivisionPair mode a b q r

def ArithQuotientResult (action : Jl BigInt) (mode : DivisionMode) (a b : Int) : Prop :=
  if b = 0 then action = .error .divideError
  else ArithReturns action (ArithQuotient mode a b)

def ArithRemainderResult (action : Jl BigInt) (mode : DivisionMode) (a b : Int) : Prop :=
  if b = 0 then action = .error .divideError
  else ArithReturns action (ArithRemainder mode a b)

def ArithGCD (a b g : Int) : Prop :=
  0 ≤ g ∧ ArithDivides g a ∧ ArithDivides g b ∧
  ∀ d : Int, ArithDivides d a → ArithDivides d b → ArithDivides d g

def ArithLCM (a b l : Int) : Prop :=
  0 ≤ l ∧ ArithDivides a l ∧ ArithDivides b l ∧
  ∀ m : Int, ArithDivides a m → ArithDivides b m → ArithDivides l m

/-- Two's-complement bit i is the upper half of the residue modulo 2^(i+1). -/
def ArithBitBool (n : Int) (i : Nat) : Bool :=
  decide ((2 : Int)^i ≤ n % (2 : Int)^(i + 1))

def ArithBit (n : Int) (i : Nat) : Prop := ArithBitBool n i = true

def ArithNaryOperator (op : MPZ.BinaryOp) : Prop :=
  op = .add ∨ op = .mul ∨ op = .and ∨ op = .ior ∨ op = .xor

def ArithNary (op : MPZ.BinaryOp) (values : List Int) (z : Int) : Prop :=
  match op with
  | .add => z = values.foldr (fun a b => a + b) 0
  | .mul => z = values.foldr ArithRepeatedProduct 1
  | .and => ∀ i, ArithBit z i ↔ ∀ a, a ∈ values → ArithBit a i
  | .ior => ∀ i, ArithBit z i ↔ ∃ a, a ∈ values ∧ ArithBit a i
  | .xor => ∀ i, ArithBit z i ↔ (values.filter (fun a => ArithBitBool a i)).length % 2 = 1
  | _ => False

/-- A finite set of exactly the requested bit positions, without a scan kernel. -/
def ArithBitCount (hasBit : Nat → Prop) (count : Clong) : Prop :=
  0 ≤ count.val ∧ ∃ positions : List Nat, positions.Nodup ∧
    (∀ i, i ∈ positions ↔ hasBit i) ∧ count.val = (positions.length : Int)

def ArithIntegerComparison (a b : Int) (result : Clong) : Prop :=
  (result.val = -1 ∨ result.val = 0 ∨ result.val = 1) ∧
  (result.val = -1 ↔ a < b) ∧ (result.val = 0 ↔ a = b) ∧
  (result.val = 1 ↔ b < a)

def ArithIntegerFloatEqual {T : FTy} (a : Int) (b : FV T) : Prop :=
  b.isfinite = true ∧ a * (b.toRat.2 : Int) = b.toRat.1

def ArithIntegerFloatLess {T : FTy} (a : Int) (b : FV T) : Prop :=
  b.isnan = true ∨ (b.isnan = false ∧
    if b.isinf then b.signbit = false
    else a * (b.toRat.2 : Int) < b.toRat.1)

def ArithFloatIntegerLess {T : FTy} (a : FV T) (b : Int) : Prop :=
  a.isnan = false ∧
    if a.isinf then a.signbit = true
    else a.toRat.1 < b * (a.toRat.2 : Int) ∨
      (a.iszero = true ∧ a.signbit = true ∧ b = 0)

def ArithTotalComparison (less greater : Prop) (result : Clong) : Prop :=
  (result.val = -1 ∨ result.val = 0 ∨ result.val = 1) ∧
  (result.val = -1 ↔ less) ∧ (result.val = 1 ↔ greater) ∧
  (result.val = 0 ↔ ¬ less ∧ ¬ greater)

/-- An exact integer power is a finite product, independently of GMP's pow primitive. -/
def ArithPowerValue (base : Int) (exponent : Nat) : Int :=
  (List.replicate exponent base).foldr (fun a b => a * b) 1

/-- The complete public BigInt-exponent behavior, including signed negative
    powers and the explicit source resource limit with its 0/±1 exceptions. -/
def ArithBigPowerContract (x y : BigInt) (action : Jl BigInt) : Prop :=
  if y.val < 0 then
    if x.val = 1 ∨ x.val = -1 then
      ArithReturns action (fun z => z * ArithPowerValue x.val y.val.natAbs = 1)
    else ArithDomainFailure action
  else if y.val > IntTy.max .u64 ∧ 1 < x.val.natAbs then
    ArithOverflowFailure action
  else ArithReturns action (fun z => z = ArithPowerValue x.val y.val.toNat)

def ArithBoolValue (x : Bool) : Int := if x then 1 else 0

def ArithModularRepresentative (m z : Int) : Prop :=
  if m > 0 then 0 ≤ z ∧ z < m else m < z ∧ z ≤ 0

def ArithFactorial (n : Nat) : Int :=
  (List.range n).foldr (fun k total => ((k + 1 : Nat) : Int) * total) 1

def ArithFallingProduct (n : Int) (k : Nat) : Int :=
  (List.range k).foldr (fun (i : Nat) (total : Int) => (n - (i : Int)) * total) 1

def ArithBinomial (n : Int) (k : Nat) (z : Int) : Prop :=
  z * ArithFactorial k = ArithFallingProduct n k

/-- BigInt + and +% compute exact signed addition, characterized by cancellation and every integer order cut without machine wraparound.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AdditionExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (add x y) (ArithAddition x.val y.val) ∧
    ArithReturns (addWrap x y) (ArithAddition x.val y.val)

/-- BigInt - and -% compute the exact signed difference, characterized by reconstruction of the minuend and every integer order cut.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SubtractionExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (sub x y) (ArithSubtraction x.val y.val) ∧
    ArithReturns (subWrap x y) (ArithSubtraction x.val y.val)

/-- BigInt * and *% compute exact signed multiplication, characterized independently as repeated addition.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def MultiplicationExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (mul x y) (ArithMultiplication x.val y.val) ∧
    ArithReturns (mulWrap x y) (ArithMultiplication x.val y.val)

/-- BigInt mod returns the unique floored-division remainder with divisor sign and magnitude smaller than the divisor, and rejects zero divisors.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:293-308; doc/src/base/math.md:19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ModuloEuclidean : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithRemainderResult (JuliaLean.base.gmp.mod x y) .down x.val y.val

/-- BigInt rem returns the exact truncating-division remainder with dividend sign and strictly bounded magnitude, and rejects zero divisors.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:79-111; doc/src/base/math.md:20-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RemainderEuclidean : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithRemainderResult (JuliaLean.base.gmp.rem x y) .toZero x.val y.val

/-- The BigInt gcd is nonnegative, divides both inputs and is divisible by every common divisor, including the all-zero case.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:5-13; doc/src/base/math.md:278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def GreatestCommonDivisor : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (gcd x y) (ArithGCD x.val y.val)

/-- The BigInt lcm is the nonnegative common multiple dividing every common multiple, giving zero exactly when an input is zero.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:97-105; doc/src/base/math.md:279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LeastCommonMultiple : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (lcm x y) (ArithLCM x.val y.val)

/-- BigInt bitwise and obeys its truth table at every bit of the infinite two's-complement representation.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitAndExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (bitand x y) (fun z => ∀ i : Nat, ArithBit z i ↔ ArithBit x.val i ∧ ArithBit y.val i)

/-- BigInt bitwise or obeys its truth table at every bit of the infinite two's-complement representation.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitOrExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (bitor x y) (fun z => ∀ i : Nat, ArithBit z i ↔ ArithBit x.val i ∨ ArithBit y.val i)

/-- BigInt bitwise xor obeys its truth table at every bit of the infinite two's-complement representation.
Julia source: base/gmp.jl:495-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitXorExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithReturns (bitxor x y) (fun z => ∀ i : Nat, ArithBit z i ↔ (ArithBit x.val i ∧ ¬ ArithBit y.val i) ∨ (¬ ArithBit x.val i ∧ ArithBit y.val i))

/-- All three BigInt division modes return the unique integer quotient with the specified remainder direction, and every zero divisor raises DivideError.
Julia source: base/gmp.jl:505-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:5-13; base/rounding.jl:25-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DivisionModesEuclidean : Prop :=
  ∀ (x y : BigInt) (mode : DivisionMode), GMPInput x → GMPInput y →
    ArithQuotientResult (divRound x y mode) mode x.val y.val

/-- Default BigInt div is exact truncating integer division with complete zero-divisor behavior.
Julia source: base/gmp.jl:512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:5-13,151-157,198-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DefaultDivisionEuclidean : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithQuotientResult (JuliaLean.base.gmp.div x y) .toZero x.val y.val

/-- BigInt fld returns the mathematical floor of the exact quotient, with complete zero-divisor behavior.
Julia source: base/gmp.jl:513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:5-13,151-157,198-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def FloorDivisionEuclidean : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithQuotientResult (JuliaLean.base.gmp.fld x y) .down x.val y.val

/-- BigInt cld returns the mathematical ceiling of the exact quotient, with complete zero-divisor behavior.
Julia source: base/gmp.jl:514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:5-13,151-157,198-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CeilingDivisionEuclidean : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithQuotientResult (JuliaLean.base.gmp.cld x y) .up x.val y.val

/-- Invmod succeeds exactly for a nonzero modulus coprime to the input and returns its uniquely normalized modular inverse; all other inputs raise DomainError.
Julia source: base/gmp.jl:518-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:289-310; base/gmp.jl:527-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ModularInverseExact : Prop :=
  ∀ x m : BigInt, GMPInput x → GMPInput m →
    if m.val = 0 ∨ Nat.gcd x.val.natAbs m.val.natAbs ≠ 1 then
      ArithDomainFailure (invmod x m)
    else ArithReturns (invmod x m) (fun z =>
      ArithDivides m.val (x.val * z - 1) ∧ ArithModularRepresentative m.val z)

/-- All 3-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.
Julia source: base/gmp.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:666-678; doc/src/manual/mathematical-operations.md:501-503; doc/src/base/numbers.md:138-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def Commutative3Exact : Prop :=
  ∀ (op : MPZ.BinaryOp) (a b c : BigInt), ArithNaryOperator op →
    GMPInput a → GMPInput b → GMPInput c →
    ArithReturns (commutative3 op a b c) (ArithNary op [a.val, b.val, c.val])

/-- All 4-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.
Julia source: base/gmp.jl:542-542 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:666-678; doc/src/manual/mathematical-operations.md:501-503; doc/src/base/numbers.md:138-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def Commutative4Exact : Prop :=
  ∀ (op : MPZ.BinaryOp) (a b c d : BigInt), ArithNaryOperator op →
    GMPInput a → GMPInput b → GMPInput c → GMPInput d →
    ArithReturns (commutative4 op a b c d) (ArithNary op [a.val, b.val, c.val, d.val])

/-- All 5-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.
Julia source: base/gmp.jl:543-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:666-678; doc/src/manual/mathematical-operations.md:501-503; doc/src/base/numbers.md:138-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def Commutative5Exact : Prop :=
  ∀ (op : MPZ.BinaryOp) (a b c d e : BigInt), ArithNaryOperator op →
    GMPInput a → GMPInput b → GMPInput c → GMPInput d → GMPInput e →
    ArithReturns (commutative5 op a b c d e) (ArithNary op [a.val, b.val, c.val, d.val, e.val])

/-- Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedRightAddition : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsCulongMax t),
    GMPInput x → ArithAddition x.val c.val (addCulongMax dispatch x c).val

/-- Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedLeftAddition : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsCulongMax t),
    GMPInput x → ArithAddition c.val x.val (culongMaxAdd dispatch c x).val

/-- Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedRightSubtraction : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsCulongMax t),
    GMPInput x → ArithSubtraction x.val c.val (subCulongMax dispatch x c).val

/-- Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedLeftSubtraction : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsCulongMax t),
    GMPInput x → ArithSubtraction c.val x.val (culongMaxSub dispatch c x).val

/-- Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedRightAddition : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsClongMax t),
    GMPInput x → ArithAddition x.val c.val (addClongMax dispatch x c).val

/-- Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedLeftAddition : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsClongMax t),
    GMPInput x → ArithAddition c.val x.val (clongMaxAdd dispatch c x).val

/-- Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedRightSubtraction : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsClongMax t),
    GMPInput x → ArithSubtraction x.val c.val (subClongMax dispatch x c).val

/-- Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:558 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedLeftSubtraction : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsClongMax t),
    GMPInput x → ArithSubtraction c.val x.val (clongMaxSub dispatch c x).val

/-- Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedRightMultiplication : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsCulongMax t),
    GMPInput x → ArithMultiplication x.val c.val (mulCulongMax dispatch x c).val

/-- Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedLeftMultiplication : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsCulongMax t),
    GMPInput x → ArithMultiplication c.val x.val (culongMaxMul dispatch c x).val

/-- Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedRightMultiplication : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsClongMax t),
    GMPInput x → ArithMultiplication x.val c.val (mulClongMax dispatch x c).val

/-- Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.
Julia source: base/gmp.jl:563 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedLeftMultiplication : Prop :=
  ∀ (t : IntTy) (x : BigInt) (c : JInt t) (dispatch : IsClongMax t),
    GMPInput x → ArithMultiplication c.val x.val (clongMaxMul dispatch c x).val

/-- Unary BigInt negation is the exact additive inverse for every signed value.
Julia source: base/gmp.jl:569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/base/math.md:6; doc/src/manual/integers-and-floating-point-numbers.md:554-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnaryNegationInverse : Prop :=
  ∀ x : BigInt, GMPInput x →
    ArithReturns (unaryNeg x) (fun z => z + x.val = 0)

/-- BigInt complement flips every bit of its infinite two's-complement representation.
Julia source: base/gmp.jl:570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ComplementEveryBit : Prop :=
  ∀ x : BigInt, GMPInput x →
    ArithReturns (complement x) (fun z => ∀ i : Nat, ArithBit z i ↔ ¬ ArithBit x.val i)

/-- Unsigned-count BigInt left shift moves every input bit by the exact count and fills every lower position with zero.
Julia source: base/gmp.jl:572 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:715-723; doc/src/base/numbers.md:141-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LeftShiftEveryBit : Prop :=
  ∀ (x : BigInt) (count : Culong), GMPInput x →
    ∀ i : Nat, ArithBit (shiftLeft x count).val i ↔
      count.val.toNat ≤ i ∧ ArithBit x.val (i - count.val.toNat)

/-- BigInt right shift retains infinite sign extension and moves each bit by the unsigned count, including the documented BigInt >>> equivalence.
Julia source: base/gmp.jl:573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:750-758,791-815; doc/src/base/numbers.md:141-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RightShiftEveryBit : Prop :=
  ∀ (x : BigInt) (count : Culong), GMPInput x →
    ∀ i : Nat, ArithBit (shiftRight x count).val i ↔ ArithBit x.val (i + count.val.toNat)

/-- BigInt right shift retains infinite sign extension and moves each bit by the unsigned count, including the documented BigInt >>> equivalence.
Julia source: base/gmp.jl:574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:750-758,791-815; doc/src/base/numbers.md:141-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LogicalRightShiftEveryBit : Prop :=
  ∀ (x : BigInt) (count : Culong), GMPInput x →
    ∀ i : Nat, ArithBit (logicalShiftRight x count).val i ↔ ArithBit x.val (i + count.val.toNat)

/-- Trailing zeros returns the exact binary valuation of every nonzero signed integer and raises DomainError for zero.
Julia source: base/gmp.jl:576-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:490-501; doc/src/base/numbers.md:155-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TrailingZeroValuation : Prop :=
  ∀ x : BigInt, GMPInput x →
    if x.val = 0 then ArithDomainFailure (trailingZeros x)
    else ∃ count, trailingZeros x = .ok count ∧ 0 ≤ count.val ∧
      ArithDivides ((2 : Int)^count.val.toNat) (x.val) ∧
      ¬ ArithDivides ((2 : Int)^(count.val.toNat + 1)) (x.val)

/-- Trailing ones returns the exact binary valuation of x+1 and raises DomainError for the infinite all-ones value -1.
Julia source: base/gmp.jl:582-586 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:532-543; doc/src/base/numbers.md:155-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TrailingOneValuation : Prop :=
  ∀ x : BigInt, GMPInput x →
    if x.val = -1 then ArithDomainFailure (trailingOnes x)
    else ∃ count, trailingOnes x = .ok count ∧ 0 ≤ count.val ∧
      ArithDivides ((2 : Int)^count.val.toNat) (x.val + 1) ∧
      ¬ ArithDivides ((2 : Int)^(count.val.toNat + 1)) (x.val + 1)

/-- Count ones returns the cardinality of exactly the set bits of each nonnegative BigInt and raises DomainError for negative inputs with infinitely many set bits.
Julia source: base/gmp.jl:588-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:461-475; doc/src/base/numbers.md:153-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CountOnesCardinality : Prop :=
  ∀ x : BigInt, GMPInput x →
    if x.val < 0 then ArithDomainFailure (countOnes x)
    else ∃ count, countOnes x = .ok count ∧ ArithBitCount (ArithBit x.val) count

/-- Count zeros returns the cardinality of exactly the zero bits of each negative BigInt and raises DomainError for nonnegative inputs with infinitely many zero bits.
Julia source: base/gmp.jl:595-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/int.jl:503-517; doc/src/base/numbers.md:153-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CountZerosCardinality : Prop :=
  ∀ x : BigInt, GMPInput x →
    if 0 ≤ x.val then ArithDomainFailure (countZeros x)
    else ∃ count, countZeros x = .ok count ∧ ArithBitCount (fun i => ¬ ArithBit x.val i) count

/-- BigInt exponent gives the unique binary magnitude bracket for every nonzero integer and raises DomainError for zero.
Julia source: base/gmp.jl:614-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/math.jl:900-908; doc/src/base/numbers.md:87-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ExponentMagnitudeBracket : Prop :=
  ∀ x : BigInt, GMPInput x →
    if x.val = 0 then ArithDomainFailure (JuliaLean.base.gmp.exponent x)
    else ∃ e, JuliaLean.base.gmp.exponent x = .ok e ∧ 0 ≤ e.val ∧
      2^e.val.toNat ≤ x.val.natAbs ∧ x.val.natAbs < 2^(e.val.toNat + 1)

/-- BigInt divrem returns both the exact truncating quotient and remainder satisfying reconstruction, strict magnitude and dividend-sign conditions, with DivideError at zero divisors.
Julia source: base/gmp.jl:625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/div.jl:256-273,79-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DivremExactPair : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    if y.val = 0 then divrem x y = .error .divideError
    else ∃ q r, divrem x y = .ok (q, r) ∧
      ArithDivisionPair .toZero x.val y.val q.val r.val

/-- BigInt cmp returns exactly -1, 0 or 1 according to mathematical integer order.
Julia source: base/gmp.jl:628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IntegerComparisonExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y → ArithIntegerComparison x.val y.val (cmp x y)

/-- Mixed BigInt and C-word comparison is exact for every member type and every representable machine value.
Julia source: base/gmp.jl:629 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-511; base/gmp.jl:22-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignedComparisonExact : Prop :=
  ∀ (t : IntTy) (x : BigInt) (y : JInt t) (dispatch : IsClongMax t),
    GMPInput x → ArithIntegerComparison x.val y.val (cmpClongMax dispatch x y)

/-- Mixed BigInt and C-word comparison is exact for every member type and every representable machine value.
Julia source: base/gmp.jl:630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-511; base/gmp.jl:22-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedComparisonExact : Prop :=
  ∀ (t : IntTy) (x : BigInt) (y : JInt t) (dispatch : IsCulongMax t),
    GMPInput x → ArithIntegerComparison x.val y.val (cmpCulongMax dispatch x y)

/-- BigInt/IEEE cmp implements the full documented total order, with NaNs last and negative floating zero below integer zero.
Julia source: base/gmp.jl:634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:206-242,508-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IntegerFloatTotalOrder : Prop :=
  ∀ (T : FTy) (x : BigInt) (y : FV T), GMPInput x →
    ArithTotalComparison (ArithIntegerFloatLess x.val y) (ArithFloatIntegerLess y x.val) (cmpFloat x y)

/-- BigInt/IEEE cmp implements the full documented total order, with NaNs last and negative floating zero below integer zero.
Julia source: base/gmp.jl:635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:206-242,508-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def FloatIntegerTotalOrder : Prop :=
  ∀ (T : FTy) (x : BigInt) (y : FV T), GMPInput x →
    ArithTotalComparison (ArithFloatIntegerLess y x.val) (ArithIntegerFloatLess x.val y) (floatCmp y x)

/-- BigInt isqrt returns the unique nonnegative integer whose square brackets the input, and negative inputs raise DomainError.
Julia source: base/gmp.jl:637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:1283-1294; base/math.jl:634-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IntegerSquareRootBracket : Prop :=
  ∀ x : BigInt, GMPInput x →
    if x.val < 0 then ArithDomainFailure (JuliaLean.base.gmp.isqrt x)
    else ArithReturns (JuliaLean.base.gmp.isqrt x) (fun z =>
      0 ≤ z ∧ z * z ≤ x.val ∧ x.val < (z + 1) * (z + 1))

/-- Every Culong BigInt exponent is evaluated as the exact finite product, including the zero exponent and negative bases.
Julia source: base/gmp.jl:639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/promotion.jl:463-499; doc/src/manual/integers-and-floating-point-numbers.md:554-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedPowerExact : Prop :=
  ∀ (x : BigInt) (y : Culong), GMPInput x →
    (powUnsigned x y).val = ArithPowerValue x.val y.val.toNat

/-- BigInt exponentiation returns the exact integer power or inverse for bases ±1, rejects other negative powers, and retains the explicit huge-exponent OverflowError with 0/±1 exceptions.
Julia source: base/gmp.jl:663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/promotion.jl:463-499; base/gmp.jl:641-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntPowerFullDomain : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ArithBigPowerContract x y (powBigInt x y)

/-- Boolean-base BigInt powers agree with exact integer powers and reject zero to a negative power, using the actual source Bool power callee.
Julia source: base/gmp.jl:667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/promotion.jl:463-499; base/intfuncs.jl:445-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BooleanBasePowerExact : Prop :=
  ∀ (x : Bool) (y : BigInt), GMPInput y →
    let action := boolPowBigInt x y
    if y.val < 0 ∧ x = false then ArithDomainFailure action
    else ∃ z, action = .ok z ∧
      if y.val < 0 then ArithBoolValue z * ArithPowerValue (ArithBoolValue x) y.val.natAbs = 1
      else ArithBoolValue z = ArithPowerValue (ArithBoolValue x) y.val.toNat

/-- Powermod gives the uniquely normalized residue of an exact integer power or inverse power, and reports the documented division/inverse-domain errors.
Julia source: base/gmp.jl:669-672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:501-545,289-310; base/int.jl:293-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ModularPowerFullDomain : Prop :=
  ∀ x p m : BigInt, GMPInput x → GMPInput p → GMPInput m →
    if p.val < 0 ∧ (m.val = 0 ∨ Nat.gcd x.val.natAbs m.val.natAbs ≠ 1) then
      ArithDomainFailure (powermod x p m)
    else if m.val = 0 then powermod x p m = .error .divideError
    else ArithReturns (powermod x p m) (fun z =>
      ArithModularRepresentative m.val z ∧
      if p.val < 0 then ArithDivides m.val (z * ArithPowerValue x.val p.val.natAbs - 1)
      else ArithDivides m.val (ArithPowerValue x.val p.val.toNat - z))

/-- Gcdx returns a nonnegative greatest common divisor and exact Bézout coefficients, with the strict signed-coefficient bounds promised by its documentation whenever the divisor is positive.
Julia source: base/gmp.jl:676-687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:193-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ExtendedGCDExactAndMinimal : Prop :=
  ∀ a b : BigInt, GMPInput a → GMPInput b →
    let result := gcdx a b
    let g := result.1.val
    let u := result.2.1.val
    let v := result.2.2.val
    ArithGCD a.val b.val g ∧ u * a.val + v * b.val = g ∧
    (0 < g → (u.natAbs : Int) * g < (b.val.natAbs : Int) ∧
      (v.natAbs : Int) * g < (a.val.natAbs : Int))

/-- Variadic BigInt addition returns the exact sum of every argument, including the empty rest tuple, for every realizable argument count.
Julia source: base/gmp.jl:689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:666-678; base/reduce.jl:548-560; doc/src/manual/integers-and-floating-point-numbers.md:554-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def VariadicAdditionExact : Prop :=
  ∀ (x y : BigInt) (rest : List BigInt), GMPInput x → GMPInput y →
    (∀ z, z ∈ rest → GMPInput z) → rest.length + 2 < 2^62 →
    ArithReturns (addVariadic x y rest) (fun z =>
      z = (x.val :: y.val :: rest.map BigInt.val).foldr (fun a b => a + b) 0)

/-- BigInt factorial returns the exact natural-number factorial for every nonnegative input and raises DomainError for every negative input.
Julia source: base/gmp.jl:717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:1304-1312; doc/src/manual/integers-and-floating-point-numbers.md:605-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def FactorialExactNaturalDomain : Prop :=
  ∀ n : BigInt, GMPInput n →
    if n.val < 0 then ArithDomainFailure (JuliaLean.base.gmp.factorial n)
    else ArithReturns (JuliaLean.base.gmp.factorial n) (fun z => z = ArithFactorial n.val.toNat)

/-- The Culong-index BigInt binomial equals the generalized falling-factorial coefficient for every signed n, including k>n and negative n.
Julia source: base/gmp.jl:728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/intfuncs.jl:1338-1354; doc/src/base/math.md:276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsignedBinomialExact : Prop :=
  ∀ (n : BigInt) (k : Culong), GMPInput n →
    ArithBinomial n.val k.val.toNat (binomialUnsigned n k).val

/-- BigInt equality is exactly equality of the represented mathematical integers.
Julia source: base/gmp.jl:730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:109-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IntegerEqualityExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    (equal x y = true ↔ x.val = y.val)

/-- BigInt/IEEE equality compares exact numeric values, equates both floating zero signs with integer zero, and rejects every NaN and infinity.
Julia source: base/gmp.jl:733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IntegerFloatEqualityExact : Prop :=
  ∀ (T : FTy) (x : BigInt) (y : FV T), GMPInput x →
    (equalFloat x y = true ↔ ArithIntegerFloatEqual x.val y)

/-- BigInt/IEEE equality compares exact numeric values, equates both floating zero signs with integer zero, and rejects every NaN and infinity.
Julia source: base/gmp.jl:734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def FloatIntegerEqualityExact : Prop :=
  ∀ (T : FTy) (x : BigInt) (y : FV T), GMPInput x →
    (floatEqual y x = true ↔ ArithIntegerFloatEqual x.val y)

def TailIntLEFloat {T : FTy} (n : Int) (f : FV T) : Prop :=
  (f.isinf = true ∧ f.signbit = false) ∨
  (f.isfinite = true ∧ n * (f.toRat.2 : Int) ≤ f.toRat.1)

def TailFloatLEInt {T : FTy} (f : FV T) (n : Int) : Prop :=
  (f.isinf = true ∧ f.signbit = true) ∨
  (f.isfinite = true ∧ f.toRat.1 ≤ n * (f.toRat.2 : Int))

def TailIntLTFloat {T : FTy} (n : Int) (f : FV T) : Prop :=
  (f.isinf = true ∧ f.signbit = false) ∨
  (f.isfinite = true ∧ n * (f.toRat.2 : Int) < f.toRat.1)

def TailFloatLTInt {T : FTy} (f : FV T) (n : Int) : Prop :=
  (f.isinf = true ∧ f.signbit = true) ∨
  (f.isfinite = true ∧ f.toRat.1 < n * (f.toRat.2 : Int))

def TailTruncatedDivision (x y q r : Int) : Prop :=
  x = q * y + r ∧ r.natAbs < y.natAbs ∧ (r = 0 ∨ 0 < r * x)

def TailFlooredDivision (x y q r : Int) : Prop :=
  x = q * y + r ∧ r.natAbs < y.natAbs ∧ (r = 0 ∨ 0 < r * y)

def TailCeilingDivision (x y q r : Int) : Prop :=
  x = q * y + r ∧ r.natAbs < y.natAbs ∧ (r = 0 ∨ r * y < 0)

/-- BigInt zero testing agrees with its integer value, including zero with spare storage.
Julia source: base/gmp.jl:735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:25-44; base/gmp.jl:64-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntZeroClassification : Prop :=
  ∀ x : BigInt, GMPInput x → (iszero x = true ↔ x.val = 0)

/-- BigInt unit testing holds exactly for the integer one.
Julia source: base/gmp.jl:736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:47-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntOneClassification : Prop :=
  ∀ x : BigInt, GMPInput x → (isone x = true ↔ x.val = 1)

/-- BigInt strict and non-strict order are the exact integer order for every pair of valid integers.
Julia source: base/gmp.jl:738,744 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntOrderExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    (lessEqual x y = true ↔ x.val ≤ y.val) ∧
    (less x y = true ↔ x.val < y.val)

/-- Comparison with every IEEEFloat uses its exact numerical value, leaves NaN unordered, and equates signed zeros numerically.
Julia source: base/gmp.jl:741-742,747-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286; base/gmp.jl:29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntIEEEOrderExact : Prop :=
  ∀ (T : FTy) (x : BigInt) (f : FV T), GMPInput x →
    (lessEqualFloat x f = true ↔ TailIntLEFloat x.val f) ∧
    (floatLessEqual f x = true ↔ TailFloatLEInt f x.val) ∧
    (lessFloat x f = true ↔ TailIntLTFloat x.val f) ∧
    (floatLess f x = true ↔ TailFloatLTInt f x.val)

/-- BigInt positive, negative, and sign-bit predicates agree with the signed mathematical integer.
Julia source: base/gmp.jl:749-752 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:122-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntSignClassification : Prop :=
  ∀ x : BigInt, GMPInput x →
    (isnegative x = true ↔ x.val < 0) ∧
    (ispositive x = true ↔ 0 < x.val) ∧
    (signbit x = true ↔ x.val < 0)

/-- Flipping the sign by a BigInt changes exactly the sign selected by the second integer and preserves a valid value.
Julia source: base/gmp.jl:755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:242-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntFlipSignExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    let z := flipsign x y
    Valid z ∧ (if y.val < 0 then z.val + x.val = 0 else z.val = x.val)

/-- The sign of a BigInt is minus one, zero, or one exactly according to its mathematical sign.
Julia source: base/gmp.jl:757-761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:190-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntSignValue : Prop :=
  ∀ x : BigInt, GMPInput x →
    let z := sign x
    Valid z ∧ (z.val = -1 ↔ x.val < 0) ∧
    (z.val = 0 ↔ x.val = 0) ∧ (z.val = 1 ↔ 0 < x.val)

/-- Checked absolute value returns the nonnegative integer of the same magnitude without fixed-width overflow.
Julia source: base/gmp.jl:841 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:108-119; base/gmp.jl:64-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CheckedBigIntAbsolute : Prop :=
  ∀ x : BigInt, GMPInput x →
    let z := checkedAbs x
    Valid z ∧ 0 ≤ z.val ∧ z.val * z.val = x.val * x.val

/-- Checked BigInt negation succeeds with the exact additive inverse, including every extremal input layout.
Julia source: base/gmp.jl:842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:80-89; base/gmp.jl:64-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CheckedBigIntNegation : Prop :=
  ∀ x : BigInt, GMPInput x →
    ∃ z, checkedNeg x = .ok z ∧ Valid z ∧ z.val + x.val = 0

/-- Checked addition of arbitrary BigInts returns their exact sum.
Julia source: base/gmp.jl:843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:158-166; base/gmp.jl:64-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CheckedBigIntAddition : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ∃ z, checkedAdd x y = .ok z ∧ z.val - y.val = x.val ∧
      ∀ t : Int, z.val ≤ t ↔ x.val ≤ t - y.val

/-- Checked subtraction of arbitrary BigInts returns their exact difference.
Julia source: base/gmp.jl:844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:218-226; base/gmp.jl:64-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CheckedBigIntSubtraction : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ∃ z, checkedSub x y = .ok z ∧ z.val + y.val = x.val ∧
      ∀ t : Int, z.val ≤ t ↔ x.val ≤ t + y.val

/-- Checked multiplication of arbitrary BigInts returns their exact product.
Julia source: base/gmp.jl:845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:282-290; base/gmp.jl:64-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CheckedBigIntMultiplication : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ∃ z, checkedMul x y = .ok z ∧ z.val = ArithRepeatedProduct x.val y.val

/-- Checked BigInt quotient and remainder methods satisfy exact division identities and their rounding intervals, and reject a zero divisor.
Julia source: base/gmp.jl:846-850 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:312-355; base/div.jl:5-18,79-110,152-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CheckedBigIntDivision : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    if y.val = 0 then
      checkedDiv x y = .error .divideError ∧
      checkedRem x y = .error .divideError ∧
      checkedFld x y = .error .divideError ∧
      checkedMod x y = .error .divideError ∧
      checkedCld x y = .error .divideError
    else
      ∃ q r f m c,
        checkedDiv x y = .ok q ∧ checkedRem x y = .ok r ∧
        checkedFld x y = .ok f ∧ checkedMod x y = .ok m ∧
        checkedCld x y = .ok c ∧
        TailTruncatedDivision x.val y.val q.val r.val ∧
        TailFlooredDivision x.val y.val f.val m.val ∧
        TailCeilingDivision x.val y.val c.val (x.val - c.val * y.val)

/-- BigInt overflow-reporting arithmetic returns exact results and a false overflow flag for all three operations.
Julia source: base/gmp.jl:851-853 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:131-134,195-198,234-237; base/gmp.jl:64-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntOverflowReportingExact : Prop :=
  ∀ x y : BigInt, GMPInput x → GMPInput y →
    ∃ a s m,
      addWithOverflow x y = .ok (a, false) ∧ a.val - y.val = x.val ∧
      subWithOverflow x y = .ok (s, false) ∧ s.val + y.val = x.val ∧
      mulWithOverflow x y = .ok (m, false) ∧ m.val = ArithRepeatedProduct x.val y.val ∧
      (∀ t : Int, a.val ≤ t ↔ x.val ≤ t - y.val) ∧
      (∀ t : Int, s.val ≤ t ↔ x.val ≤ t + y.val)

/-- Checked BigInt powers are exact, accept negative powers of units, and report the documented source exponent-domain and exponent-cap errors.
Julia source: base/gmp.jl:858,641-663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/checked.jl:358-366; base/intfuncs.jl:385-395; base/gmp.jl:641-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CheckedBigIntPower : Prop :=
  ∀ x p : BigInt, GMPInput x → GMPInput p →
    ArithBigPowerContract x p (checkedBigPow x p)

/-- Canonical mathematical form includes finite reduced fractions and the two infinities ±1/0. -/
def TailRationalCanonical (q : MPQ.Rational) : Prop :=
  0 ≤ q.den.val ∧ Nat.gcd q.num.val.natAbs q.den.val.natAbs = 1

def TailRationalInput (q : MPQ.Rational) : Prop :=
  GMPInput q.num ∧ GMPInput q.den ∧ TailRationalCanonical q

def TailRationalLT (x y : MPQ.Rational) : Prop :=
  (x.den.val = 0 ∧ x.num.val < 0 ∧ (y.den.val ≠ 0 ∨ 0 < y.num.val)) ∨
  (y.den.val = 0 ∧ 0 < y.num.val ∧ (x.den.val ≠ 0 ∨ x.num.val < 0)) ∨
  (0 < x.den.val ∧ 0 < y.den.val ∧
    x.num.val * y.den.val < y.num.val * x.den.val)

/-- Rational{BigInt} construction produces the exact reduced ratio with nonnegative denominator, accepts signed infinities, and rejects zero over zero.
Julia source: base/gmp.jl:1004-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rational.jl:4-7,65-89; doc/src/manual/complex-and-rational-numbers.md:180-211,282-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntRationalConstruction : Prop :=
  ∀ num den : BigInt, GMPInput num → GMPInput den →
    if num.val = 0 ∧ den.val = 0 then
      ∃ msg, MPQ.construct num den = .error (.argumentError msg)
    else ∃ q, MPQ.construct num den = .ok q ∧ TailRationalCanonical q ∧
      if den.val = 0 then q.den.val = 0 ∧ (0 < q.num.val ↔ 0 < num.val)
      else 0 < q.den.val ∧ q.num.val * den.val = num.val * q.den.val

/-- Rational BigInt addition is exact on finite values and propagates the signed infinity except for opposite infinities, which throw DivideError.
Julia source: base/gmp.jl:1112 (generated +),1047-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/complex-and-rational-numbers.md:180-239,282-303; base/gmp.jl:1047-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntRationalAddition : Prop :=
  ∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if x.den.val = 0 ∧ y.den.val = 0 ∧ x.num.val * y.num.val < 0 then
      MPQ.binary .add x y = .error .divideError
    else ∃ z, MPQ.binary .add x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) =
          (x.num.val * y.den.val + y.num.val * x.den.val) * z.den.val
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (x.den.val = 0 ∧ 0 < x.num.val) ∨ (y.den.val = 0 ∧ 0 < y.num.val))

/-- Rational BigInt subtraction is exact on finite values and has the signed extended-value result except for equal infinities, which throw DivideError.
Julia source: base/gmp.jl:1112 (generated -),1060-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/complex-and-rational-numbers.md:180-242,282-303; base/gmp.jl:1060-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntRationalSubtraction : Prop :=
  ∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if x.den.val = 0 ∧ y.den.val = 0 ∧ 0 < x.num.val * y.num.val then
      MPQ.binary .sub x y = .error .divideError
    else ∃ z, MPQ.binary .sub x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) =
          (x.num.val * y.den.val - y.num.val * x.den.val) * z.den.val
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (x.den.val = 0 ∧ 0 < x.num.val) ∨ (y.den.val = 0 ∧ y.num.val < 0))

/-- Rational BigInt multiplication is exact on finite values, multiplies infinity signs, and rejects zero times infinity in either order.
Julia source: base/gmp.jl:1112 (generated *),1074-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/complex-and-rational-numbers.md:180-245,282-303; base/gmp.jl:1074-1086 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntRationalMultiplication : Prop :=
  ∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if (x.den.val = 0 ∨ y.den.val = 0) ∧ (x.num.val = 0 ∨ y.num.val = 0) then
      MPQ.binary .mul x y = .error .divideError
    else ∃ z, MPQ.binary .mul x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) = (x.num.val * y.num.val) * z.den.val
      else z.den.val = 0 ∧ (0 < z.num.val ↔ 0 < x.num.val * y.num.val)

/-- Rational BigInt division is exact on finite nonzero divisors, handles finite/infinite/zero values, and rejects zero over zero and infinity over infinity.
Julia source: base/gmp.jl:1112 (generated //),1087-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rational.jl:65-89; doc/src/manual/complex-and-rational-numbers.md:180-248,282-303; base/gmp.jl:1087-1106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntRationalDivision : Prop :=
  ∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if (x.den.val = 0 ∧ y.den.val = 0) ∨ (x.num.val = 0 ∧ y.num.val = 0) then
      MPQ.binary .div x y = .error .divideError
    else ∃ z, MPQ.binary .div x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val ∧ y.num.val ≠ 0 then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.num.val) = (x.num.val * y.den.val) * z.den.val
      else if y.den.val = 0 then z.num.val = 0 ∧ z.den.val = 1
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (0 < x.num.val ∧ 0 ≤ y.num.val) ∨ (x.num.val < 0 ∧ y.num.val < 0))

/-- Rational BigInt comparison returns exactly minus one, zero, or one according to the total order of finite ratios and the two infinities.
Julia source: base/gmp.jl:1116-1123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-511; doc/src/manual/complex-and-rational-numbers.md:180-230,282-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigIntRationalComparison : Prop :=
  ∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    let c := (MPQ.cmp x y).val
    (c = -1 ↔ TailRationalLT x y) ∧
    (c = 0 ↔ x.num.val = y.num.val ∧ x.den.val = y.den.val) ∧
    (c = 1 ↔ TailRationalLT y x)

end Round1

namespace RemainingMethodPromises
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float JuliaLean.Proofs.base.gmp.Round1

/-- Generated integer C callees have the GMP integer symbol prefix and resolve the libgmp binding in MPZ. -/
def IntegerCalleeSymbol : Prop :=
  ∀ op : String, (MPZ.gmpz op).symbol.toList.drop 7 = op.toList ∧ (MPZ.gmpz op).symbol.toList.take 7 = "__gmpz_".toList ∧ (MPZ.gmpz op).moduleName = "MPZ" ∧ (MPZ.gmpz op).binding = "libgmp"

/-- Finite-double comparison uses exact rational order without rounding the integer. -/
def DoubleComparisonExact : Prop :=
  ∀ (a : BigInt) (b : FV .f64), b.isfinite = true → ArithIntegerComparison (a.val*(b.toRat.2 : Int)) b.toRat.1 (MPZ.cmpD a b)

/-- Every supported positive-radix integer rendering parses successfully to the original integer, including negative values and zero. -/
def IntegerStringRoundtrip : Prop :=
  ∀ (x n : BigInt) (b : Cint), 2 ≤ b.val → b.val ≤ 62 → let r := MPZ.setStrBang x (MPZ.getStr b n) b; r.2.val = 0 ∧ r.1.val = n.val

/-- Every supported positive-radix integer rendering parses successfully to the original integer, including negative values and zero. -/
def StringIntegerRoundtrip : Prop :=
  ∀ (x n : BigInt) (b : Cint), 2 ≤ b.val → b.val ≤ 62 → let r := MPZ.setStrBang x (MPZ.getStr b n) b; r.2.val = 0 ∧ r.1.val = n.val

/-- Preparing writable limbs preserves the integer and prior words while reserving the requested native capacity. -/
def WritableLimbCapacity : Prop :=
  ∀ (x : BigInt) (n : Clong), 0 ≤ n.val → n.val ≤ IntTy.max .i32 → 0 ≤ x.alloc.val → let r := MPZ.limbsWrite x n; r.val = x.val ∧ n.val ≤ r.alloc.val ∧ x.d <+: r.d

/-- Finishing a written limb prefix normalizes the signed integer representation. -/
def FinishedLimbNormalization : Prop :=
  ∀ (x : BigInt) (n : Clong), 0 ≤ x.alloc.val → n.val.natAbs ≤ x.alloc.val.toNat → n.val.natAbs ≤ x.d.length → Valid (MPZ.limbsFinish x n)

/-- Setting one bit makes that bit one and leaves every other two-complement bit unchanged. -/
def SetbitPreservesOtherBits : Prop :=
  ∀ (x : BigInt) (i : Culong), ∀ j : Nat, ArithBit (MPZ.setbitBang x i).val j ↔ j = i.val.toNat ∨ ArithBit x.val j

/-- The generic constructor represents every built-in integer type exactly, including both 128-bit types. -/
def GenericIntegerConstruction : Prop :=
  ∀ (t : IntTy) (x : JInt t), ConvRepresentsInteger (fromInteger (bitIntegerInput t) x) x.val

/-- The local oversized-exponent thrower always raises OverflowError. -/
def OversizedExponentError : Prop :=
  ∀ (I : Type) (y : I), ∃ message, (bigintPowThrow1 (A := BigInt) y) = .error (.overflowError message)

open JuliaLean JuliaLean.base.gmp Round1

theorem oversizedExponentError_proven : OversizedExponentError := by
  intro I y
  exact ⟨"exponent is too large", rfl⟩

/-- A true exponent retains the input integer; a false exponent returns one. -/
def BooleanExponentIdentity : Prop :=
  ∀ (x : BigInt) (y : Bool), (powBool x y).val = (if y then x.val else 1) ∧ (y = true → powBool x y = x)

open JuliaLean JuliaLean.base.gmp Round1

theorem booleanExponentIdentity_proven : BooleanExponentIdentity := by
  intro x y
  cases y <;> simp [powBool, ofInt]

/-- The integer exponent alias preserves the complete exact-power domain and errors when instantiated with the installed Base power method. -/
def IntegerExponentAlias : Prop :=
  ∀ (x : BigInt) (y : Int), GMPInput x → ArithBigPowerContract x (ofInt y) (powInteger (fun x y => bigintPow id (fun y => decide (y%2 = 1)) y x) x y)

/-- Every built-in integer base is converted exactly before BigInt exponentiation. -/
def IntegerBaseBigintExponent : Prop :=
  ∀ (t : IntTy) (x : JInt t) (y : BigInt), GMPInput y → ArithBigPowerContract (ofInt x.val) y (integerPowBigInt (fun x => pure (fromBits x)) powBigInt x y)

/-- Mixed built-in integer modular exponentiation returns the exact modulus-signed residue after left-to-right conversions. -/
def IntegerModularExponent : Prop :=
  ∀ (t u : IntTy) (x : JInt t) (p : JInt u) (m : BigInt), GMPInput m → m.val ≠ 0 → (0 ≤ p.val ∨ Nat.gcd x.val.natAbs m.val.natAbs = 1) → ArithReturns (powermodInteger (fun x => pure (fromBits x)) (fun p => pure (fromBits p)) powermod x p m) (fun z => ArithModularRepresentative m.val z ∧ (if p.val < 0 then ∃ k : Int, z * ArithPowerValue x.val p.val.natAbs = 1 + k*m.val else ∃ k : Int, ArithPowerValue x.val p.val.toNat = z + k*m.val))

/-- Summation returns the exact mathematical sum, with zero for an empty array. -/
def SumExact : Prop :=
  ∀ xs : List BigInt, (∀ x, x ∈ xs → GMPInput x) → xs.length < 2^62 → ArithReturns (JuliaLean.base.gmp.sum xs) (fun z => z = (xs.map BigInt.val).foldr (· + ·) 0)

/-- Factorial rejects negative inputs, checks native argument conversion, and returns the exact product on the Culong domain. -/
def FactorialNativeDomain : Prop :=
  ∀ n : BigInt, GMPInput n → if n.val < 0 then ArithDomainFailure (JuliaLean.base.gmp.factorial n) else if n.val > IntTy.max .u64 then ∃ msg, JuliaLean.base.gmp.factorial n = .error (.inexactError msg) else ArithReturns (JuliaLean.base.gmp.factorial n) (fun z => z = ArithFactorial n.val.toNat)

/-- Changing sign according to any Integer signbit preserves the absolute value and a valid representation. -/
def FlipsignPreservesMagnitude : Prop :=
  ∀ (I : Type) (signbit : I → Bool) (x : BigInt) (y : I), Valid x → Valid (flipsignInteger signbit x y) ∧ (flipsignInteger signbit x y).val.natAbs = x.val.natAbs

/-- Checked generic exponentiation preserves the complete exact integer-power contract. -/
def CheckedIntegerExponent : Prop :=
  ∀ (x : BigInt) (y : Int), GMPInput x → ArithBigPowerContract x (ofInt y) (checkedPow (fun x y => bigintPow id (fun y => decide (y%2 = 1)) y x) x y)

/-- Checked exponentiation preserves exact built-in integer-base conversion and the complete BigInt-exponent contract. -/
def CheckedIntegerBaseExponent : Prop :=
  ∀ (t : IntTy) (x : JInt t) (y : BigInt), GMPInput y → ArithBigPowerContract (ofInt x.val) y (checkedIntegerPow (integerPowBigInt (fun x => pure (fromBits x)) powBigInt) x y)

/-- The allocation-saving hash shift multiplies the integer by the requested power of two. -/
def HashShiftExact : Prop :=
  ∀ (x : BigInt) (n : Culong), (hashShiftBang x n).val = x.val * (2 : Int)^n.val.toNat

open JuliaLean JuliaLean.base.gmp Round1

theorem hashShiftExact_proven : HashShiftExact := by
  intro x n
  rfl

/-- Mixed divrem converts the divisor before division and returns the exact truncated quotient and remainder. -/
def MixedDivremReconstruction : Prop :=
  ∀ (t : IntTy) (x : BigInt) (y : JInt t), GMPInput x → let action := divremInteger (fun y => pure (fromBits y)) MPZ.tdivQr x y; if y.val = 0 then action = .error .divideError else ∃ q r, action = .ok (q,r) ∧ ArithDivisionPair .toZero x.val y.val q.val r.val

/-- Array product returns the exact mathematical product, with one for an empty array and zero if any entry is zero. -/
def ArrayProductExact : Prop :=
  ∀ xs : List BigInt, (∀ x, x ∈ xs → GMPInput x) → xs.length < 2^62 → ∃ z, prodGeneric (fun xs : List BigInt => pure (xs.any iszero)) (fun _ => JInt.wrap .i64 1) (fun xs => JInt.wrap .i64 xs.length) (fun (xs : List BigInt) (i : Clong) => match xs[(i.val-1).toNat]? with | some x => pure x | none => .error .boundsError) xs = some (.ok z) ∧ z.val = (xs.map BigInt.val).foldr (· * ·) 1

/-- Both recursive product branches return the exact product of the requested valid array segment, including the empty segment. -/
def ArrayProductSegmentExact : Prop :=
  ∀ (xs : List BigInt) (lo hi : Clong), (∀ x, x ∈ xs → GMPInput x) → 1 ≤ lo.val → lo.val ≤ hi.val+1 → hi.val ≤ (xs.length : Int) → xs.length < 2^62 → ∃ z, prodRangeGeneric (fun (xs : List BigInt) (i : Clong) => match xs[(i.val-1).toNat]? with | some x => pure x | none => .error .boundsError) xs lo hi = some (.ok z) ∧ z.val = (((xs.drop (lo.val-1).toNat).take (hi.val-lo.val+1).toNat).map BigInt.val).foldr (· * ·) 1

end RemainingMethodPromises


/-! ## Registry -/
end JuliaLean.Proofs.base.gmp

section
/- Batch 4, group 6: proofs for the unchanged target declarations. -/

/- Section: Construction. -/
namespace JuliaLean.ChatGPT.Batch4.Group6

open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem cgWrapU64Nat (n : Nat) (hn : n < 2^64) :
    (JInt.wrap .u64 (n : Int)).val = (n : Int) := by
  change wrapInt .u64 (n : Int) = (n : Int)
  apply wrapInt_of_inRange
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ 18446744073709551615
  have hn' : n < 18446744073709551616 := hn
  omega

theorem cgLimbsZero : limbsOfNat 0 = [] := by
  rw [limbsOfNat]
  rfl

theorem cgOfIntZero : ofInt 0 = ⟨0, JInt.wrap .i32 0, JInt.wrap .i32 0, []⟩ := by
  simp only [ofInt, Int.natAbs_zero, cgLimbsZero, Int.ofNat_eq_natCast]
  rfl

theorem cgLimbsOne (n : Nat) (hn : n < 2^64) (hne : n ≠ 0) :
    limbsOfNat n = [JInt.wrap .u64 (n : Int)] := by
  rw [limbsOfNat, dif_neg hne, Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn,
    cgLimbsZero]
  simp only [Int.ofNat_eq_natCast]

theorem cgOfIntOne (n : Int) (hn : n.natAbs < 2^64) (hne : n ≠ 0) :
    ofInt n = ⟨n, JInt.wrap .i32 1,
      JInt.wrap .i32 (if n < 0 then -1 else 1),
      [JInt.wrap .u64 (n.natAbs : Int)]⟩ := by
  have ha : n.natAbs ≠ 0 := by omega
  unfold ofInt
  rw [cgLimbsOne n.natAbs hn ha]
  rfl

theorem cgWriteInitOne (n : Int) (hn : n.natAbs < 2^64) (hne : n ≠ 0) :
    writeValue initBigInt n = ofInt n := by
  rw [writeValue, cgOfIntOne n hn hne, initBigInt, cgOfIntZero]
  rfl

theorem cgGMPInputSmall (n : Int) (hn : n.natAbs < 2^64) :
    GMPInput (writeValue initBigInt n) := by
  by_cases hz : n = 0
  · subst n
    simp only [writeValue, initBigInt, cgOfIntZero]
    unfold GMPInput Valid
    decide
  rw [cgWriteInitOne n hn hz, cgOfIntOne n hn hz]
  have hv := cgWrapU64Nat n.natAbs hn
  by_cases hs : n < 0
  · simp only [hs, if_pos]
    change (1 ≤ 1 ∧ 1 ≤ 1 ∧
      n = -(limbMagnitude [JInt.wrap .u64 (n.natAbs : Int)] : Int) ∧
      ((-1 : Int) = 0 ↔ n = 0) ∧
      ((-1 : Int) ≠ 0 → (JInt.wrap .u64 (n.natAbs : Int)).val ≠ 0)) ∧
      0 ≤ (1 : Int) ∧ 1 < (2 : Nat)^62
    simp only [limbMagnitude, hv, Int.toNat_natCast, Nat.mul_zero, Nat.add_zero]
    omega
  · simp only [hs, if_neg]
    change (1 ≤ 1 ∧ 1 ≤ 1 ∧
      n = (limbMagnitude [JInt.wrap .u64 (n.natAbs : Int)] : Int) ∧
      ((1 : Int) = 0 ↔ n = 0) ∧
      ((1 : Int) ≠ 0 → (JInt.wrap .u64 (n.natAbs : Int)).val ≠ 0)) ∧
      0 ≤ (1 : Int) ∧ 1 < (2 : Nat)^62
    simp only [limbMagnitude, hv, Int.toNat_natCast, Nat.mul_zero, Nat.add_zero]
    omega

theorem cgRepresentsSmall (n : Int) (hn : n.natAbs < 2^64) :
    ConvRepresentsInteger (writeValue initBigInt n) n := by
  exact ⟨cgGMPInputSmall n hn, rfl⟩

theorem cgI64AbsBound (x : JInt .i64) : x.val.natAbs < 2^64 := by
  have hx := x.property
  change -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 at hx
  change x.val.natAbs < 18446744073709551616
  omega

theorem cgU64AbsBound (x : JInt .u64) : x.val.natAbs < 2^64 := by
  have hx := x.property
  change 0 ≤ x.val ∧ x.val ≤ 18446744073709551615 at hx
  change x.val.natAbs < 18446744073709551616
  omega

theorem BignumsGmpSignedMachineConstruction_proven :
    JuliaLean.Proofs.base.gmp.Round1.SignedMachineConstructionCorrect := by
  constructor
  · intro x
    exact cgRepresentsSmall x.val (cgI64AbsBound x)
  · intro x
    have hx := x.property
    change -2147483648 ≤ x.val ∧ x.val ≤ 2147483647 at hx
    have hw : (JInt.wrap .i64 x.val).val = x.val := by
      change wrapInt .i64 x.val = x.val
      apply wrapInt_of_inRange
      change -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807
      omega
    have hb : x.val.natAbs < 2^64 := by
      change x.val.natAbs < 18446744073709551616
      omega
    unfold fromInt32 MPZ.setSi MPZ.setSiBang
    rw [hw]
    exact cgRepresentsSmall x.val hb

theorem BignumsGmpUnsignedMachineConstruction_proven :
    JuliaLean.Proofs.base.gmp.Round1.UnsignedMachineConstructionCorrect := by
  constructor
  · intro x
    exact cgRepresentsSmall x.val (cgU64AbsBound x)
  · intro x
    have hx := x.property
    change 0 ≤ x.val ∧ x.val ≤ 4294967295 at hx
    have hw : (JInt.wrap .u64 x.val).val = x.val := by
      change wrapInt .u64 x.val = x.val
      apply wrapInt_of_inRange
      change 0 ≤ x.val ∧ x.val ≤ 18446744073709551615
      omega
    have hb : x.val.natAbs < 2^64 := by
      change x.val.natAbs < 18446744073709551616
      omega
    unfold fromUInt32 MPZ.setUi MPZ.setUiBang
    rw [hw]
    exact cgRepresentsSmall x.val hb

theorem cgLimbsMagnitude (n : Nat) : limbMagnitude (limbsOfNat n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      rw [cgLimbsZero]
      rfl
    rw [limbsOfNat, dif_neg hz, limbMagnitude]
    simp only [Int.ofNat_eq_natCast]
    rw [cgWrapU64Nat (n % 2^64) (Nat.mod_lt n (by decide)), Int.toNat_natCast]
    rw [ih (n / 2^64) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))]
    exact Nat.mod_add_div n (2^64)

theorem cgLimbsLengthZero (n : Nat) : (limbsOfNat n).length = 0 ↔ n = 0 := by
  by_cases hz : n = 0
  · subst n
    rw [cgLimbsZero]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  rw [limbsOfNat, dif_neg hz, List.length_cons]
  omega

theorem cgLimbsTop (n : Nat) (hne : n ≠ 0) :
    (((limbsOfNat n)[(limbsOfNat n).length - 1]?).getD (JInt.wrap .u64 0)).val ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hrec : n / 2^64 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hne) (by decide)
    by_cases hq : n / 2^64 = 0
    · have hn : n < 2^64 := (Nat.div_eq_zero_iff_lt (by decide)).mp hq
      rw [cgLimbsOne n hn hne]
      change (JInt.wrap .u64 (n : Int)).val ≠ 0
      rw [cgWrapU64Nat n hn]
      omega
    · have hl : 0 < (limbsOfNat (n / 2^64)).length := by
        have h := cgLimbsLengthZero (n / 2^64)
        omega
      rw [limbsOfNat, dif_neg hne, List.length_cons]
      have hi : (limbsOfNat (n / 2^64)).length + 1 - 1 =
          ((limbsOfNat (n / 2^64)).length - 1) + 1 := by omega
      rw [hi, List.getElem?_cons_succ]
      exact ih (n / 2^64) hrec hq

theorem cgLimbsLengthLe (k n : Nat) (hn : n < (2^64)^k) :
    (limbsOfNat n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have hz : n = 0 := by
      have hn' : n < 1 := hn
      omega
    rw [hz, cgLimbsZero]
    exact Nat.le_refl 0
  | succ k ih =>
    by_cases hz : n = 0
    · rw [hz, cgLimbsZero]
      exact Nat.zero_le _
    have hq : n / 2^64 < (2^64)^k := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa only [Nat.pow_succ] using hn
    rw [limbsOfNat, dif_neg hz, List.length_cons]
    exact Nat.succ_le_succ (ih _ hq)

theorem cgOfIntAlloc (n : Int) (hlen : (limbsOfNat n.natAbs).length < 2^31) :
    (ofInt n).alloc.val = ((limbsOfNat n.natAbs).length : Int) := by
  change wrapInt .i32 ((max (limbsOfNat n.natAbs).length 0 : Nat) : Int) = _
  rw [Nat.max_zero]
  apply wrapInt_of_inRange
  change -2147483648 ≤ ((limbsOfNat n.natAbs).length : Int) ∧
    ((limbsOfNat n.natAbs).length : Int) ≤ 2147483647
  have hlen' : (limbsOfNat n.natAbs).length < 2147483648 := hlen
  omega

theorem cgOfIntSize (n : Int) (hlen : (limbsOfNat n.natAbs).length < 2^31) :
    (ofInt n).size.val =
      (if n < 0 then -((limbsOfNat n.natAbs).length : Int)
        else ((limbsOfNat n.natAbs).length : Int)) := by
  change wrapInt .i32 (if n < 0 then -((limbsOfNat n.natAbs).length : Int)
      else ((limbsOfNat n.natAbs).length : Int)) = _
  apply wrapInt_of_inRange
  change -2147483648 ≤ (if n < 0 then -((limbsOfNat n.natAbs).length : Int)
      else ((limbsOfNat n.natAbs).length : Int)) ∧
    (if n < 0 then -((limbsOfNat n.natAbs).length : Int)
      else ((limbsOfNat n.natAbs).length : Int)) ≤ 2147483647
  have hlen' : (limbsOfNat n.natAbs).length < 2147483648 := hlen
  split <;> omega

theorem cgGMPInputOfInt (n : Int) (hlen : (limbsOfNat n.natAbs).length < 2^31) :
    GMPInput (ofInt n) := by
  by_cases hz : n = 0
  · subst n
    rw [cgOfIntZero]
    unfold GMPInput Valid
    decide
  have ha : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hl : 0 < (limbsOfNat n.natAbs).length := by
    have h := cgLimbsLengthZero n.natAbs
    omega
  have hlimit : (limbsOfNat n.natAbs).length < 2^62 := by
    have hlen' : (limbsOfNat n.natAbs).length < 2147483648 := hlen
    change (limbsOfNat n.natAbs).length < 4611686018427387904
    omega
  unfold GMPInput Valid
  rw [cgOfIntAlloc n hlen, cgOfIntSize n hlen]
  simp only [ofInt]
  by_cases hs : n < 0
  · have hls : -((limbsOfNat n.natAbs).length : Int) < 0 := by omega
    simp only [if_pos hs, if_pos hls, Int.natAbs_neg, Int.natAbs_natCast,
      Int.toNat_natCast, List.take_length]
    refine ⟨⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_⟩, ?_, hlimit⟩
    · rw [cgLimbsMagnitude]
      omega
    · constructor <;> intro h <;> omega
    · intro _
      exact cgLimbsTop n.natAbs ha
    · omega
  · have hls : ¬ ((limbsOfNat n.natAbs).length : Int) < 0 := by omega
    simp only [if_neg hs, if_neg hls, Int.natAbs_natCast, Int.toNat_natCast,
      List.take_length]
    refine ⟨⟨Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_⟩, ?_, hlimit⟩
    · rw [cgLimbsMagnitude]
      omega
    · constructor <;> intro h <;> omega
    · intro _
      exact cgLimbsTop n.natAbs ha
    · omega

theorem cgWriteInitOfInt (n : Int) (hlen : (limbsOfNat n.natAbs).length < 2^31) :
    writeValue initBigInt n = ofInt n := by
  have hn : 0 ≤ (ofInt n).alloc.val := by rw [cgOfIntAlloc n hlen]; omega
  have hw : JInt.wrap .i32 (max initBigInt.alloc.val (ofInt n).alloc.val) =
      (ofInt n).alloc := by
    apply Subtype.ext
    rw [initBigInt, cgOfIntZero]
    change wrapInt .i32 (max 0 (ofInt n).alloc.val) = (ofInt n).alloc.val
    rw [Int.max_eq_right hn]
    exact wrapInt_of_inRange .i32 _ (ofInt n).alloc.property
  dsimp only [writeValue]
  rw [hw]

theorem cgGMPInputWriteInit (n : Int)
    (hlen : (limbsOfNat n.natAbs).length < 2^31) :
    GMPInput (writeValue initBigInt n) := by
  rw [cgWriteInitOfInt n hlen]
  exact cgGMPInputOfInt n hlen

theorem cgGMPInputWriteInit1024 (n : Int) (hn : n.natAbs < 2^1024) :
    GMPInput (writeValue initBigInt n) := by
  apply cgGMPInputWriteInit
  have hn' : n.natAbs < (2^64)^16 := by simpa only [← Nat.pow_mul] using hn
  have hlen := cgLimbsLengthLe 16 n.natAbs hn'
  change (limbsOfNat n.natAbs).length < 2147483648
  omega

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: Conversion. -/
namespace JuliaLean.ChatGPT.Batch4.Group6
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem g6wrap_zero (t : IntTy) : wrapInt t 0 = 0 := by
  cases t <;> decide

theorem g6wrap_idem (t : IntTy) (a : Int) :
    wrapInt t (wrapInt t a) = wrapInt t a :=
  wrapInt_of_inRange t _ (wrapInt_bounds t a)

theorem g6jint_neg_val {t : IntTy} (a : JInt t) :
    (-a).val = wrapInt t (-a.val) := rfl

theorem g6jint_add_val {t : IntTy} (a b : JInt t) :
    (a + b).val = wrapInt t (a.val + b.val) := rfl

theorem g6jint_wrap_val (t : IntTy) (a : Int) :
    (JInt.wrap t a).val = wrapInt t a := rfl

theorem g6wrap_neg (t : IntTy) (a : Int) :
    wrapInt t (-wrapInt t a) = wrapInt t (-a) := by
  cases t <;>
    simp only [wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true,
      ↓reduceIte, Int.reducePow, Nat.reduceSub] <;> omega

theorem g6wrap_add (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a + wrapInt t b) = wrapInt t (a + b) := by
  cases t <;>
    simp only [wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true,
      ↓reduceIte, Int.reducePow, Nat.reduceSub] <;> omega

theorem g6wrap_period64 (t : IntTy) (ht : t.bits ≤ 64) (a k : Int) :
    wrapInt t (a + 18446744073709551616 * k) = wrapInt t a := by
  cases t <;>
    simp only [IntTy.bits] at ht <;>
    simp only [wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true,
      ↓reduceIte, Int.reducePow, Nat.reduceSub] <;> omega

theorem g6wrap_congruent (t : IntTy) (n : Int) :
    ConvCongruentRepresentative t n (JInt.wrap t n) := by
  refine ⟨(JInt.wrap t n).property.1, (JInt.wrap t n).property.2, ?_⟩
  cases t <;>
    simp only [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits,
      Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Int.reducePow]
  · exact ⟨(n + 128) / 256, by omega⟩
  · exact ⟨(n + 32768) / 65536, by omega⟩
  · exact ⟨(n + 2147483648) / 4294967296, by omega⟩
  · exact ⟨(n + 9223372036854775808) / 18446744073709551616, by omega⟩
  · exact ⟨(n + 170141183460469231731687303715884105728) /
      340282366920938463463374607431768211456, by omega⟩
  · exact ⟨n / 256, by omega⟩
  · exact ⟨n / 65536, by omega⟩
  · exact ⟨n / 4294967296, by omega⟩
  · exact ⟨n / 18446744073709551616, by omega⟩
  · exact ⟨n / 340282366920938463463374607431768211456, by omega⟩

theorem g6magnitude_head (ds : List Limb) (k : Nat) (hk : 0 < k) :
    ∃ r : Int, (limbMagnitude (ds.take k) : Int) =
      ((ds[0]?).getD (JInt.wrap .u64 0)).val + 18446744073709551616 * r := by
  cases ds with
  | nil => exact ⟨0, by simp only [List.take_nil]; decide⟩
  | cons a ds =>
    cases k with
    | zero => omega
    | succ k =>
      refine ⟨(limbMagnitude (ds.take k) : Int), ?_⟩
      have ha : 0 ≤ a.val := a.property.1
      change ((a.val.toNat + 18446744073709551616 * limbMagnitude (ds.take k) : Nat) : Int) =
        a.val + 18446744073709551616 * (limbMagnitude (ds.take k) : Int)
      rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg ha]
      rfl

theorem g6remLimb_val (t : IntTy) (x : BigInt) (ht : t.bits ≤ 64)
    (hx : Valid x) : (remLimb t x).val = wrapInt t x.val := by
  by_cases hs : x.size.val = 0
  · have hv : x.val = 0 := hx.2.2.2.1.mp hs
    simp only [remLimb, iszero, hs, decide_true, ↓reduceIte, hv, JInt.wrap]
  · have hk : 0 < x.size.val.natAbs := Int.natAbs_pos.mpr hs
    obtain ⟨r, hr⟩ := g6magnitude_head x.d x.size.val.natAbs hk
    have hv := hx.2.2.1
    by_cases hn : x.size.val < 0
    · simp only [hn, ↓reduceIte] at hv
      simp only [remLimb, iszero, isnegative, hs, hn, decide_false, Bool.false_eq_true, decide_true,
        ↓reduceIte]
      change wrapInt t (-wrapInt t _) = wrapInt t x.val
      rw [g6wrap_neg, hv, hr]
      rw [show -(((x.d[0]?).getD (JInt.wrap .u64 0)).val + 18446744073709551616 * r) =
        -((x.d[0]?).getD (JInt.wrap .u64 0)).val + 18446744073709551616 * (-r) by omega]
      exact (g6wrap_period64 t ht _ _).symm
    · simp only [hn, ↓reduceIte] at hv
      simp only [remLimb, iszero, isnegative, hs, hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      change wrapInt t _ = wrapInt t x.val
      rw [hv, hr]
      exact (g6wrap_period64 t ht _ _).symm

theorem BignumsGmpLimbRemainderConversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.LimbRemainderConversionCorrect := by
  intro t x ht hx
  have he : remLimb t x = JInt.wrap t x.val :=
    Subtype.ext (g6remLimb_val t x ht hx.1)
  rw [he]
  exact g6wrap_congruent t x.val

theorem g6remBits_small_val (t : IntTy) (x : BigInt) (ht : t.bits ≤ 64)
    (hx : Valid x) : (remBits t x).val = wrapInt t x.val := by
  have hw : (t.bits + 63) / 64 = 1 := by
    cases t <;> simp only [IntTy.bits] at ht ⊢ <;> omega
  by_cases hs : x.size.val = 0
  · have hv : x.val = 0 := hx.2.2.2.1.mp hs
    simp only [remBits, hs, Int.natAbs_zero, Nat.zero_min, List.range_zero,
      List.foldl_nil, isnegative, Int.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte,
      g6jint_wrap_val, hv]
  · have hn : 0 < x.size.val.natAbs := Int.natAbs_pos.mpr hs
    have hmin : min x.size.val.natAbs ((t.bits + 63) / 64) = 1 := by
      rw [hw]
      omega
    have hh : (remBits t x).val = (remLimb t x).val := by
      simp only [remBits, hmin, show List.range 1 = [0] from rfl,
        List.foldl_cons, List.foldl_nil, Nat.mul_zero, Int.pow_zero,
        Int.mul_one, remLimb, iszero, hs, decide_false, Bool.false_eq_true, ↓reduceIte]
      split <;> simp only [g6jint_neg_val, g6jint_add_val, g6jint_wrap_val,
        g6wrap_zero, Int.zero_add, g6wrap_idem]
    exact hh.trans (g6remLimb_val t x ht hx)

theorem g6magnitude_two (ds : List Limb) (k : Nat) (hk : 2 ≤ k) :
    ∃ r : Int, (limbMagnitude (ds.take k) : Int) =
      ((ds[0]?).getD (JInt.wrap .u64 0)).val +
      18446744073709551616 * ((ds[1]?).getD (JInt.wrap .u64 0)).val +
      340282366920938463463374607431768211456 * r := by
  cases ds with
  | nil => exact ⟨0, by simp only [List.take_nil]; decide⟩
  | cons a ds =>
    have ha : 0 ≤ a.val := a.property.1
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => omega
      | succ k =>
        cases ds with
        | nil =>
          refine ⟨0, ?_⟩
          change ((a.val.toNat + 18446744073709551616 * 0 : Nat) : Int) =
            a.val + 18446744073709551616 * 0 + 340282366920938463463374607431768211456 * 0
          simp only [Nat.mul_zero, Nat.add_zero, Int.mul_zero, Int.add_zero,
            Int.toNat_of_nonneg ha]
        | cons b ds =>
          have hb : 0 ≤ b.val := b.property.1
          refine ⟨(limbMagnitude (ds.take k) : Int), ?_⟩
          change ((a.val.toNat + 18446744073709551616 *
            (b.val.toNat + 18446744073709551616 * limbMagnitude (ds.take k)) : Nat) : Int) =
            a.val + 18446744073709551616 * b.val +
            340282366920938463463374607431768211456 * (limbMagnitude (ds.take k) : Int)
          simp only [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg ha,
            Int.toNat_of_nonneg hb]
          omega

theorem g6wrap_period128 (t : IntTy) (a k : Int) :
    wrapInt t (a + 340282366920938463463374607431768211456 * k) = wrapInt t a := by
  cases t <;>
    simp only [wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true,
      ↓reduceIte, Int.reducePow, Nat.reduceSub] <;> omega

theorem g6remBits_wide_val (t : IntTy) (x : BigInt) (ht : t.bits = 128)
    (hx : Valid x) : (remBits t x).val = wrapInt t x.val := by
  have hw : (t.bits + 63) / 64 = 2 := by rw [ht]
  by_cases hs : x.size.val = 0
  · have hv : x.val = 0 := hx.2.2.2.1.mp hs
    simp only [remBits, hs, Int.natAbs_zero, Nat.zero_min, List.range_zero,
      List.foldl_nil, isnegative, Int.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte,
      g6jint_wrap_val, hv]
  · have hn : 0 < x.size.val.natAbs := Int.natAbs_pos.mpr hs
    by_cases h1 : x.size.val.natAbs = 1
    · have hm : (limbMagnitude (x.d.take x.size.val.natAbs) : Int) =
          ((x.d[0]?).getD (JInt.wrap .u64 0)).val := by
        rw [h1]
        cases hd : x.d with
        | nil => rfl
        | cons a ds =>
          change ((a.val.toNat + 18446744073709551616 * 0 : Nat) : Int) = a.val
          simp only [Nat.mul_zero, Nat.add_zero, Int.toNat_of_nonneg a.property.1]
      have hmin : min x.size.val.natAbs ((t.bits + 63) / 64) = 1 := by
        rw [h1, hw]
        decide
      have hv := hx.2.2.1
      rw [hm] at hv
      by_cases hneg : x.size.val < 0 <;>
        simp only [hneg, ↓reduceIte] at hv <;>
        simp only [remBits, hmin, show List.range 1 = [0] from rfl,
          List.foldl_cons, List.foldl_nil, Nat.mul_zero, Int.pow_zero, Int.mul_one,
          isnegative, hneg, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
          g6jint_neg_val, g6jint_add_val, g6jint_wrap_val, g6wrap_zero,
          Int.zero_add, g6wrap_idem, g6wrap_neg, hv]
    · have h2 : 2 ≤ x.size.val.natAbs := by omega
      obtain ⟨r, hr⟩ := g6magnitude_two x.d x.size.val.natAbs h2
      have hmin : min x.size.val.natAbs ((t.bits + 63) / 64) = 2 := by
        rw [hw]
        omega
      have hv := hx.2.2.1
      rw [hr] at hv
      have hout : (remBits t x).val =
          if x.size.val < 0 then
            wrapInt t (-(((x.d[0]?).getD (JInt.wrap .u64 0)).val +
              18446744073709551616 * ((x.d[1]?).getD (JInt.wrap .u64 0)).val))
          else wrapInt t (((x.d[0]?).getD (JInt.wrap .u64 0)).val +
              18446744073709551616 * ((x.d[1]?).getD (JInt.wrap .u64 0)).val) := by
        simp only [remBits, hmin, show List.range 2 = [0, 1] from rfl,
          List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.mul_one,
          Int.pow_zero, Int.reducePow, Int.mul_one, isnegative]
        by_cases hneg : x.size.val < 0 <;>
          simp only [hneg, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
            g6jint_neg_val, g6jint_add_val, g6jint_wrap_val, g6wrap_zero,
            Int.zero_add, g6wrap_idem, g6wrap_add, g6wrap_neg, Int.mul_comm]
      rw [hout]
      by_cases hneg : x.size.val < 0
      · simp only [hneg, ↓reduceIte] at hv ⊢
        rw [hv]
        rw [show -(((x.d[0]?).getD (JInt.wrap .u64 0)).val +
            18446744073709551616 * ((x.d[1]?).getD (JInt.wrap .u64 0)).val +
            340282366920938463463374607431768211456 * r) =
            -(((x.d[0]?).getD (JInt.wrap .u64 0)).val +
            18446744073709551616 * ((x.d[1]?).getD (JInt.wrap .u64 0)).val) +
            340282366920938463463374607431768211456 * (-r) by omega]
        exact (g6wrap_period128 t _ _).symm
      · simp only [hneg, ↓reduceIte] at hv ⊢
        rw [hv]
        exact (g6wrap_period128 t _ _).symm

theorem g6remBits_val (t : IntTy) (x : BigInt) (hx : Valid x) :
    (remBits t x).val = wrapInt t x.val := by
  have h : t.bits ≤ 64 ∨ t.bits = 128 := by cases t <;> decide
  rcases h with h | h
  · exact g6remBits_small_val t x h hx
  · exact g6remBits_wide_val t x h hx

theorem BignumsGmpBitRemainderConversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.BitRemainderConversionCorrect := by
  intro t x hx
  have he : remBits t x = JInt.wrap t x.val := Subtype.ext (g6remBits_val t x hx.1)
  rw [he]
  exact g6wrap_congruent t x.val

theorem g6isodd_value (x : BigInt) :
    JuliaLean.base.gmp.isodd x = decide (x.val % 2 = 1) := by
  simp only [JuliaLean.base.gmp.isodd, MPZ.tstbit, bitAt, JInt.wrap, wrapInt,
    IntTy.signed, IntTy.bits, Bool.false_eq_true, ↓reduceIte,
    Int.reducePow, Int.reduceMod, Int.toNat_zero, Int.pow_zero, Int.fdiv_one]

theorem BignumsGmpOddInteger_proven :
    JuliaLean.Proofs.base.gmp.Round1.OddIntegerCorrect := by
  intro x _
  rw [g6isodd_value, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨x.val / 2, by omega⟩
  · rintro ⟨k, hk⟩
    omega

theorem BignumsGmpEvenInteger_proven :
    JuliaLean.Proofs.base.gmp.Round1.EvenIntegerCorrect := by
  intro x _
  simp only [JuliaLean.base.gmp.iseven, g6isodd_value, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro h
    exact ⟨x.val / 2, by omega⟩
  · rintro ⟨k, hk⟩
    omega

theorem g6limb_bounds (a : Limb) : 0 ≤ a.val ∧ a.val.toNat < 18446744073709551616 := by
  have h := a.property
  simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed, Bool.false_eq_true,
    ↓reduceIte, Int.reducePow] at h
  omega

theorem g6magnitude_take_upper (ds : List Limb) (n : Nat) :
    limbMagnitude (ds.take n) < 18446744073709551616 ^ n := by
  induction n generalizing ds with
  | zero => simp only [List.take_zero, limbMagnitude, Nat.pow_zero]; decide
  | succ n ih =>
    cases ds with
    | nil =>
      simp only [List.take_nil, limbMagnitude]
      exact Nat.pow_pos (by decide)
    | cons a ds =>
      have htail := ih ds
      have ha := (g6limb_bounds a).2
      simp only [List.take_succ_cons, limbMagnitude, Nat.pow_succ, Nat.reducePow]
      omega

theorem g6magnitude_take_lower (ds : List Limb) (i n : Nat) (hi : i < n)
    (hl : ((ds[i]?).getD (JInt.wrap .u64 0)).val ≠ 0) :
    18446744073709551616 ^ i ≤ limbMagnitude (ds.take n) := by
  induction i generalizing ds n with
  | zero =>
    cases ds with
    | nil => exact False.elim (hl (by simp only [List.getElem?_nil, Option.getD_none]; decide))
    | cons a ds =>
      cases n with
      | zero => omega
      | succ n =>
        change a.val ≠ 0 at hl
        have ha := (g6limb_bounds a).1
        simp only [List.take_succ_cons, limbMagnitude, Nat.pow_zero, Nat.reducePow]
        omega
  | succ i ih =>
    cases ds with
    | nil => exact False.elim (hl (by simp only [List.getElem?_nil, Option.getD_none]; decide))
    | cons a ds =>
      cases n with
      | zero => omega
      | succ n =>
        change ((ds[i]?).getD (JInt.wrap .u64 0)).val ≠ 0 at hl
        have htail := ih ds n (by omega) hl
        simp only [List.take_succ_cons, limbMagnitude, Nat.pow_succ, Nat.reducePow]
        omega

theorem g6valid_natAbs (x : BigInt) (hx : Valid x) :
    x.val.natAbs = limbMagnitude (x.d.take x.size.val.natAbs) := by
  have hv := hx.2.2.1
  rw [hv]
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

theorem g6valid_sign (x : BigInt) (hx : Valid x) :
    (x.size.val < 0 ↔ x.val < 0) ∧ (0 < x.size.val ↔ 0 < x.val) := by
  have hv := hx.2.2.1
  have hz := hx.2.2.2.1
  have hm : (0 : Int) ≤ (limbMagnitude (x.d.take x.size.val.natAbs) : Int) :=
    Int.natCast_nonneg _
  by_cases hs : x.size.val < 0 <;> simp only [hs, ↓reduceIte] at hv <;> constructor <;>
    constructor <;> intro h <;> have hzero := hz <;> omega

theorem g6valid_size_bound (x : BigInt) (hx : Valid x) (k : Nat) :
    x.size.val.natAbs ≤ k ↔ x.val.natAbs < 18446744073709551616 ^ k := by
  rw [g6valid_natAbs x hx]
  constructor
  · intro h
    have hu := g6magnitude_take_upper x.d x.size.val.natAbs
    have hp := Nat.pow_le_pow_right (by decide : 0 < 18446744073709551616) h
    omega
  · intro h
    by_cases hs : x.size.val = 0
    · simp only [hs, Int.natAbs_zero]; omega
    · have hn : 0 < x.size.val.natAbs := Int.natAbs_pos.mpr hs
      have hl := g6magnitude_take_lower x.d (x.size.val.natAbs - 1)
        x.size.val.natAbs (by omega) (hx.2.2.2.2 hs)
      by_cases hh : x.size.val.natAbs ≤ k
      · exact hh
      · have hp := Nat.pow_le_pow_right (by decide : 0 < 18446744073709551616)
          (show k ≤ x.size.val.natAbs - 1 by omega)
        omega

theorem g6unsignedLarge_spec (t : IntTy) (x : BigInt) (ht : t.signed = false)
    (hw : 64 ≤ t.bits) (hx : Valid x) :
    ConvExactBitsResult t x.val (convertUnsignedLarge t x) := by
  have htypes : t = .u64 ∨ t = .u128 := by
    cases t <;> simp only [IntTy.signed, IntTy.bits, Bool.true_eq_false,
      Bool.false_eq_true] at ht hw <;> first | exact Or.inl rfl | exact Or.inr rfl | omega
  have hsign := g6valid_sign x hx
  have habs := Int.natAbs_eq x.val
  have hsize1 := g6valid_size_bound x hx 1
  have hsize2 := g6valid_size_bound x hx 2
  rcases htypes with rfl | rfl <;>
    simp only [Nat.reducePow] at hsize1 hsize2 <;>
    unfold convertUnsignedLarge <;>
    split
  all_goals
    simp only [pure, Except.pure, ConvExactBitsResult]
  all_goals
    first
    | rw [g6remBits_val _ _ hx]
      apply wrapInt_of_inRange
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits,
        Bool.false_eq_true, ↓reduceIte, Int.reducePow]
      simp only [IntTy.bits, Nat.reduceAdd, Nat.reduceDiv] at *
      omega
    | simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits,
        Bool.false_eq_true, ↓reduceIte, Int.reducePow]
      simp only [IntTy.bits, Nat.reduceAdd, Nat.reduceDiv] at *
      omega

theorem g6signed_overflow_test (t : IntTy) (n : Int)
    (ht : t = .i64 ∨ t = .i128) (hn : n.natAbs < 2 ^ t.bits) :
    ((decide (0 < n) != decide (0 < wrapInt t n)) = true) ↔
      n < t.min ∨ t.max < n := by
  have ha := Int.natAbs_eq n
  rcases ht with rfl | rfl <;>
    simp only [IntTy.bits, Nat.reducePow] at hn <;>
    simp only [bne_iff_ne, ne_eq, decide_eq_decide, wrapInt,
      IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ↓reduceIte,
      Nat.reduceSub, Int.reducePow] <;> omega

theorem g6signedLarge_spec (t : IntTy) (x : BigInt) (ht : t.signed = true)
    (hw : 64 ≤ t.bits) (hx : Valid x) :
    ConvExactBitsResult t x.val (convertSignedLarge t x) := by
  have htypes : t = .i64 ∨ t = .i128 := by
    cases t <;> simp only [IntTy.signed, IntTy.bits, Bool.true_eq_false,
      Bool.false_eq_true] at ht hw <;> first | exact Or.inl rfl | exact Or.inr rfl | omega
  have hsign := g6valid_sign x hx
  have habs := Int.natAbs_eq x.val
  have hcount := g6valid_size_bound x hx ((t.bits + 63) / 64)
  unfold convertSignedLarge
  dsimp only
  split
  · rename_i hlarge
    simp only [pure, Except.pure, ConvExactBitsResult, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]
    rcases htypes with rfl | rfl <;>
      simp only [IntTy.bits, Nat.reduceAdd, Nat.reduceDiv, Nat.reducePow] at hcount hlarge <;>
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits,
        ↓reduceIte, Nat.reduceSub, Int.reducePow] <;> omega
  · rename_i hsmall
    have hmag : x.val.natAbs < 2 ^ t.bits := by
      have h := hcount.mp (by omega)
      rcases htypes with rfl | rfl <;>
        simp only [IntTy.bits, Nat.reduceAdd, Nat.reduceDiv, Nat.reducePow] at h ⊢ <;>
        exact h
    have hpos : ispositive x = decide (0 < x.val) := by
      unfold ispositive
      exact decide_eq_decide.mpr hsign.2
    have htest : ((ispositive x != decide ((remBits t x).val > 0)) = true) ↔
        x.val < t.min ∨ t.max < x.val := by
      rw [hpos, g6remBits_val t x hx]
      exact g6signed_overflow_test t x.val htypes hmag
    simp only [pure, Except.pure, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]
    by_cases hbad : x.val < t.min ∨ t.max < x.val
    · rw [if_pos (htest.mpr hbad)]
      exact hbad
    · rw [if_neg (fun h => hbad (htest.mp h))]
      change (remBits t x).val = x.val
      rw [g6remBits_val t x hx]
      apply wrapInt_of_inRange
      omega


theorem g6exactConvert_spec (t : IntTy) (n : Int) :
    ConvExactBitsResult t n (JInt.convert t.name t n) := by
  unfold JInt.convert
  split
  · rfl
  · simp only [ConvExactBitsResult]
    omega

theorem BignumsGmpExactUnsignedConversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.ExactUnsignedConversionCorrect := by
  intro t x ht hx
  unfold convertUnsigned
  split
  · rename_i hwidth
    have hl := g6unsignedLarge_spec .u64 x (by decide) (by decide) hx.1
    cases hconv : convertUnsignedLarge .u64 x with
    | ok a =>
      simp only [hconv, ConvExactBitsResult] at hl
      simp only [bind, Except.bind]
      rw [hl]
      exact g6exactConvert_spec t x.val
    | error e =>
      simp only [hconv, ConvExactBitsResult] at hl
      simp only [bind, Except.bind]
      cases e <;> simp only [ConvExactBitsResult] at hl ⊢ <;> try contradiction
      cases t <;> simp only [IntTy.signed, IntTy.bits, Bool.true_eq_false, Bool.false_eq_true] at ht hwidth <;>
        simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed,
          Bool.false_eq_true, ↓reduceIte, Int.reducePow] at hl ⊢ <;> omega
  · rename_i hwidth
    exact g6unsignedLarge_spec t x ht (by omega) hx.1

theorem BignumsGmpExactSignedConversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.ExactSignedConversionCorrect := by
  intro t x ht hx
  unfold convertSigned
  split
  · rename_i hwidth
    have hl := g6signedLarge_spec .i64 x (by decide) (by decide) hx.1
    cases hconv : convertSignedLarge .i64 x with
    | ok a =>
      simp only [hconv, ConvExactBitsResult] at hl
      simp only [bind, Except.bind]
      rw [hl]
      exact g6exactConvert_spec t x.val
    | error e =>
      simp only [hconv, ConvExactBitsResult] at hl
      simp only [bind, Except.bind]
      cases e <;> simp only [ConvExactBitsResult] at hl ⊢ <;> try contradiction
      cases t <;> simp only [IntTy.signed, IntTy.bits, Bool.true_eq_false, Bool.false_eq_true] at ht hwidth <;>
        simp only [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed,
          Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Int.reducePow] at hl ⊢ <;> omega
  · rename_i hwidth
    exact g6signedLarge_spec t x ht (by omega) hx.1

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: FloatConstruction. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.ChatGPT.Batch4.Group6

open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1

/-- A finite IEEE value has a positive rational denominator. -/
theorem floatConstruct_den_pos {f : Fmt} (x : Fl f) (h : x.isfinite = true) :
    0 < x.toRat.2 := by
  unfold Fl.toRat
  simp only [h, Bool.not_true, Bool.false_eq_true, ite_false]
  split <;> split <;> simp only [Nat.two_pow_pos, Nat.zero_lt_one]

/-- The constructor's integrality test and truncation characterize exact integers. -/
theorem floatConstruct_integral_iff {T : FTy} (x : FV T) (n : Int) :
    ConvFloatEqualsInteger x n ↔ x.isinteger = true ∧ x.truncVal = n := by
  constructor
  · rintro ⟨hf, hd, he⟩
    refine ⟨?_, ?_⟩
    · simp only [Fl.isinteger, hf, Bool.true_and, beq_iff_eq]
      rw [he]
      exact Int.mul_emod_left _ _
    · simp only [Fl.truncVal]
      rw [he]
      exact Int.mul_tdiv_cancel _ (by omega)
  · rintro ⟨hi, ht⟩
    simp only [Fl.isinteger, Bool.and_eq_true, beq_iff_eq] at hi
    refine ⟨hi.1, floatConstruct_den_pos x hi.1, ?_⟩
    have hdv := Int.dvd_of_emod_eq_zero hi.2
    simp only [Fl.truncVal] at ht
    rw [Int.tdiv_eq_ediv_of_dvd hdv] at ht
    rw [← ht, Int.ediv_mul_cancel hdv]

/-- The only remaining constructor obligation is normalized output storage. -/
theorem floatConstruct64_of_storage (x : FV .f64)
    (hrep : x.isinteger = true → GMPInput (writeValue initBigInt x.truncVal)) :
    ConvExactFloatResult x (fromFloat64 x) := by
  unfold fromFloat64
  split
  · rename_i hi
    change GMPInput (writeValue initBigInt x.truncVal) ∧
      ConvFloatEqualsInteger x (writeValue initBigInt x.truncVal).val
    exact ⟨hrep hi, (floatConstruct_integral_iff x x.truncVal).mpr ⟨hi, rfl⟩⟩
  · rename_i hi
    change ¬ ∃ n : Int, ConvFloatEqualsInteger x n
    rintro ⟨n, hn⟩
    exact hi ((floatConstruct_integral_iff x n).mp hn).1

/-- Every finite binary64 numerator, hence every truncated value, fits 1024 bits. -/
theorem floatConstruct64_num_bound (x : FV .f64) (hf : x.isfinite = true) :
    x.toRat.1.natAbs < 2^1024 := by
  have he : x.expField < 2048 := Nat.mod_lt _ (by decide)
  have hfrac : x.frac < 2^52 := Nat.mod_lt _ (by decide)
  have hfinite : x.expField ≠ 2047 := by
    simpa only [Fl.isfinite, bne_iff_ne, FTy.fmt, double, Fmt.emax,
      Nat.reducePow, Nat.reduceSub] using hf
  have he' : x.expField ≤ 2046 := by omega
  let m : Nat := x.frac + if x.expField == 0 then 0 else 2^52
  let p : Int := if x.expField == 0 then -1074 else (x.expField : Int)-1023-52
  have hm : m < 2^53 := by
    dsimp only [m]
    split <;> omega
  have hp : p.toNat ≤ 971 := by
    dsimp only [p]
    split <;> omega
  have hpow : 2^p.toNat ≤ 2^971 := Nat.pow_le_pow_right (by decide) hp
  have hprod : m * 2^p.toNat < 2^1024 := by
    calc
      m * 2^p.toNat < 2^53 * 2^p.toNat :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hm
      _ ≤ 2^53 * 2^971 := Nat.mul_le_mul_left _ hpow
      _ = 2^1024 := by rw [← Nat.pow_add]
  have hm' : m < 2^1024 := Nat.lt_of_lt_of_le hm
    (Nat.pow_le_pow_right (by decide) (by decide))
  unfold Fl.toRat
  simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false]
  change (if p ≥ 0 then
    ((if x.signbit then -(m : Int) else (m : Int)) * (2^p.toNat : Nat), 1)
    else (if x.signbit then -(m : Int) else (m : Int), 2^(-p).toNat)).1.natAbs < 2^1024
  split
  · cases x.signbit <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true, Int.natAbs_mul,
        Int.natAbs_neg, Int.natAbs_natCast] using hprod
  · cases x.signbit <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true, Int.natAbs_neg,
        Int.natAbs_natCast] using hm'

theorem floatConstruct64_trunc_bound (x : FV .f64) (hf : x.isfinite = true) :
    x.truncVal.natAbs < 2^1024 := by
  exact Nat.lt_of_le_of_lt (Int.natAbs_tdiv_le_natAbs _ _)
    (floatConstruct64_num_bound x hf)

/- The following local IEEE lemmas reproduce the needed widening argument using
only the imports available in the destination file. -/
namespace FloatConstructAux
open JuliaLean.Promotion.Fl
variable {f g : Fmt}

theorem width_pow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega, Nat.pow_succ, Nat.mul_comm]


theorem toBits_ofBits {f : Fmt} (v : Nat) : (Fl.ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem ofBits_toBits {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hv]

theorem ext_toBits {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  rw [← ofBits_toBits x, ← ofBits_toBits y, h]

theorem bits_split {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := width_pow f
    have h3 : x.toBits = x.bits.val := rfl
    omega
  have hW := Nat.two_pow_pos (f.eb + f.sb)
  refine ⟨?_, Nat.mod_lt _ hW⟩
  unfold Fl.signbit Fl.magnitude
  by_cases hs : x.toBits ≥ 2 ^ (f.eb + f.sb)
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_true, ↓reduceIte]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [hs]

theorem expField_eq {f : Fmt} (x : Fl f) : x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem frac_eq {f : Fmt} (x : Fl f) : x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

structure Good (f : Fmt) : Prop where
  emax_eq : f.emax = 2 * f.bias + 1
  emax_succ : f.emax + 1 = 2 ^ f.eb
  bias_pos : 1 ≤ f.bias
  sb_pos : 1 ≤ f.sb
  sb_le : f.sb ≤ f.bias

theorem good_half : (Good half) := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem good_single : (Good single) := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem good_double : (Good double) := ⟨by decide, by decide, by decide, by decide, by decide⟩

def den (f : Fmt) : Nat := 2 ^ (f.bias + f.sb - 1)
theorem den_pos (f : Fmt) : 0 < (den f) := Nat.two_pow_pos _

theorem pow_mul_eq (m a b c d : Nat) (h : a + b = c + d) : m * 2 ^ a * 2 ^ b = m * 2 ^ c * 2 ^ d := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, h]

def magKey (f : Fmt) (M : Nat) : Nat :=
  (M % 2 ^ f.sb + if M / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) * 2 ^ (M / 2 ^ f.sb - 1)

def pack (neg : Bool) (B r : Nat) : Fl f :=
  ofBits ((if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r))

theorem pack_parts (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (pack neg B r : Fl f).signbit = neg ∧ (pack neg B r : Fl f).expField = B ∧
    (pack neg B r : Fl f).frac = r ∧ (pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
  have hP := Nat.two_pow_pos f.sb
  have hM : B * 2 ^ f.sb + r < 2 ^ (f.eb + f.sb) := by
    rw [Nat.pow_add]
    have : (B + 1) * 2 ^ f.sb ≤ 2 ^ f.eb * 2 ^ f.sb := Nat.mul_le_mul_right _ hB
    rw [Nat.succ_mul] at this
    omega
  have hw := width_pow f
  have ht : (pack neg B r : Fl f).toBits =
      (if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r) := by
    unfold pack
    rw [toBits_ofBits, Nat.mod_eq_of_lt]
    rw [hw]
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, ge_iff_le, decide_eq_false_iff_not, Nat.not_le, Nat.le_add_right, decide_true] <;> omega
  have hm : (pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
    unfold magnitude
    rw [ht]
    cases neg <;> simp [Nat.mod_eq_of_lt hM]
  refine ⟨?_, ?_, ?_, hm⟩
  · unfold Fl.signbit
    rw [ht]
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, ge_iff_le, decide_eq_false_iff_not, Nat.not_le, Nat.le_add_right, decide_true] <;> omega
  · rw [expField_eq, hm, Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [frac_eq, hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

def key (x : Fl f) : Int :=
  if x.signbit then -((magKey f x.magnitude : Nat) : Int) else ((magKey f x.magnitude : Nat) : Int)

theorem isnan_of_finite {x : Fl f} (h : x.isfinite = true) : x.isnan = false := by
  simp_all [isfinite, isnan]

theorem isinf_of_finite {x : Fl f} (h : x.isfinite = true) : x.isinf = false := by
  simp_all [isfinite, isinf]

theorem toRat_cases (hf : (Good f)) (x : Fl f) (hx : x.isfinite = true) : ∃ m i j : Nat,
    x.toRat = ((if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int)),
      2 ^ j) ∧
    magKey f x.magnitude * 2 ^ j = m * 2 ^ i * (den f) ∧ m < 2 ^ (f.sb + 1) ∧
    (m ≠ 0 → j + 1 ≤ m.log2 + i + f.bias + f.sb ∧ m.log2 + i ≤ j + f.bias) := by
  have hP := Nat.two_pow_pos f.sb
  have hb := hf.bias_pos
  have hs := hf.sb_pos
  have hE := hf.emax_eq
  have hS := hf.emax_succ
  have hM := (bits_split x).2
  have hfin : x.magnitude / 2 ^ f.sb ≠ f.emax := by
    have := hx
    simp only [isfinite, bne_iff_ne, ne_eq] at this
    rw [expField_eq] at this
    exact this
  have hdiv : x.magnitude / 2 ^ f.sb < 2 ^ f.eb := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hr := Nat.mod_lt x.magnitude hP
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold toRat magKey den
  rw [expField_eq, frac_eq]
  simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  generalize x.signbit = s
  generalize x.magnitude / 2 ^ f.sb = e at *
  generalize x.magnitude % 2 ^ f.sb = r at *
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨r, 0, f.bias + f.sb - 1, ?_, ?_, by omega, ?_⟩
    · simp only [↓reduceIte, Nat.add_zero]
      split
      · exfalso; omega
      · refine Prod.ext ?_ ?_
        · cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_add, Int.natCast_pow, Int.cast_ofNat_Int, Nat.pow_zero, Nat.mul_one]
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
    · simp only [↓reduceIte, Nat.add_zero, Nat.zero_le, Nat.sub_eq_zero_of_le, Nat.pow_zero, Nat.mul_one]
    · intro hr0
      have : r.log2 < f.sb := (Nat.log2_lt hr0).2 hr
      omega
  · have he0 : e ≠ 0 := by omega
    have hne : r + 2 ^ f.sb ≠ 0 := by omega
    have hl1 : (r + 2 ^ f.sb).log2 < f.sb + 1 := (Nat.log2_lt hne).2 (by omega)
    have hl2 : f.sb ≤ (r + 2 ^ f.sb).log2 := (Nat.le_log2 hne).2 (by omega)
    simp only [he0, ↓reduceIte]
    split
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, e - f.bias - f.sb, 0, ?_, ?_, by omega, fun _ => by omega⟩
      · have ht : ((e : Int) - f.bias - f.sb).toNat = e - f.bias - f.sb := by omega
        rw [ht]
        refine Prod.ext ?_ rfl
        cases s <;> simp [Int.natCast_mul, Int.neg_mul]
      · rw [Nat.mul_one]
        conv => lhs; rw [← Nat.mul_one ((r + 2 ^ f.sb) * 2 ^ (e - 1))]
        rw [show (1 : Nat) = 2 ^ 0 from rfl]
        exact pow_mul_eq _ _ _ _ _ (by omega)
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, 0, f.bias + f.sb - e, ?_, ?_, by omega, fun _ => by omega⟩
      · refine Prod.ext ?_ ?_
        · cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_add, Int.natCast_pow, Int.cast_ofNat_Int, Nat.pow_zero, Nat.mul_one]
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
      · exact pow_mul_eq _ _ _ _ _ (by omega)

theorem toRat_key (hf : (Good f)) (x : Fl f) (hx : x.isfinite = true) :
    0 < x.toRat.2 ∧ x.toRat.1 * ((den f) : Int) = (key x) * (x.toRat.2 : Int) := by
  obtain ⟨m, i, j, hr, hk, -, -⟩ := toRat_cases hf x hx
  rw [hr]
  refine ⟨Nat.two_pow_pos j, ?_⟩
  unfold key
  dsimp only
  cases x.signbit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul, ← Int.natCast_mul, hk]


theorem log2_mul_pow (c i : Nat) (hc : c ≠ 0) : (c * 2 ^ i).log2 = c.log2 + i := by
  have hne : c * 2 ^ i ≠ 0 := Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  apply Nat.le_antisymm
  · have : c * 2 ^ i < 2 ^ (c.log2 + i + 1) := by
      rw [show c.log2 + i + 1 = (c.log2 + 1) + i by omega, Nat.pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos i)).2 Nat.lt_log2_self
    have := (Nat.log2_lt hne).2 this
    omega
  · apply (Nat.le_log2 hne).2
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hc)

theorem floorLog2Rat_pow (a j : Nat) (ha : a ≠ 0) :
    floorLog2Rat a (2 ^ j) = (a.log2 : Int) - j := by
  have h1 := Nat.log2_self_le ha
  unfold floorLog2Rat
  simp only [Nat.log2_two_pow]
  split
  · rename_i hge
    have : 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat = 2 ^ a.log2 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hc : ¬ a < 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat := by omega
    split
    · contradiction
    · rfl
  · rename_i hlt
    have : 2 ^ a.log2 * 2 ^ (-((a.log2 : Int) - j)).toNat = 2 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have := Nat.mul_le_mul_right (2 ^ (-((a.log2 : Int) - j)).toNat) h1
    have hc : ¬ a * 2 ^ (-((a.log2 : Int) - j)).toNat < 2 ^ j := by omega
    split
    · contradiction
    · rfl

theorem roundQuotient_exact (q d : Nat) (hd : 0 < d) : roundQuotient (q * d) d = q := by
  unfold roundQuotient
  rw [Nat.mul_div_cancel _ hd, Nat.mul_mod_left]
  dsimp only
  split
  · rename_i h
    simp only [Nat.mul_zero, gt_iff_lt, Nat.not_lt_zero, decide_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h <;> omega
  · rfl

theorem packRounded_normal (neg : Bool) (q : Nat) (k : Int) (h1 : 2 ^ f.sb ≤ q)
    (h2 : q < 2 ^ (f.sb + 1)) (hk2 : k + f.bias + f.sb < f.emax) :
    (packRounded neg q k : Fl f) = pack neg (k + f.bias + f.sb).toNat (q - 2 ^ f.sb) := by
  have hP := Nat.two_pow_pos f.sb
  have hq0 : (q == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hc : ¬ q ≥ 2 ^ (f.sb + 1) := by omega
  have he : ¬ k + f.bias + f.sb ≥ (f.emax : Int) := by omega
  have hm : ¬ q < 2 ^ f.sb := by omega
  unfold packRounded pack
  simp only [hq0, hc, he, hm, Bool.false_eq_true, ↓reduceIte]

theorem sig_bounds (c : Nat) (hc : c ≠ 0) (hc1 : c < 2 ^ (f.sb + 1)) :
    c.log2 ≤ f.sb ∧ 2 ^ f.sb ≤ c * 2 ^ (f.sb - c.log2) ∧
    c * 2 ^ (f.sb - c.log2) < 2 ^ (f.sb + 1) := by
  have hlc : c.log2 ≤ f.sb := by have := (Nat.log2_lt hc).2 hc1; omega
  refine ⟨hlc, ?_, ?_⟩
  · calc 2 ^ f.sb = 2 ^ c.log2 * 2 ^ (f.sb - c.log2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.log2_self_le hc)
  · calc c * 2 ^ (f.sb - c.log2) < 2 ^ (c.log2 + 1) * 2 ^ (f.sb - c.log2) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 Nat.lt_log2_self
      _ = 2 ^ (f.sb + 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega

theorem roundRat_normal (hf : (Good f)) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f) =
      pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := sig_bounds (f := f) c hc hc1
  have ha : n.natAbs ≠ 0 := by
    rw [hn]
    exact Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  have hn0 : (n == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hd : (2 ^ j == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq, Nat.pow_eq_zero, reduceCtorEq, false_and, not_false_eq_true]
  have hE : floorLog2Rat n.natAbs (2 ^ j) = ((c.log2 + i : Nat) : Int) - j := by
    rw [floorLog2Rat_pow _ _ ha, hn, log2_mul_pow c i hc]
  have hb := hf.bias_pos
  have hem := hf.emax_eq
  have hs := hf.sb_pos
  unfold roundRat
  simp only [hd, hn0, Bool.false_eq_true, ↓reduceIte]
  generalize floorLog2Rat n.natAbs (2 ^ j) = e at hE
  split
  · exfalso; omega
  split
  · exfalso; omega
  have hk : max (e - f.sb) (1 - (f.bias : Int) - f.sb) = e - f.sb := by omega
  rw [hk]
  have hpack : ∀ q : Nat, q = c * 2 ^ (f.sb - c.log2) →
      (packRounded (decide (n < 0)) q (e - f.sb) : Fl f) =
        pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
    intro q hq
    subst hq
    rw [packRounded_normal _ _ _ hq1 hq2 (by omega)]
    congr 1
    omega
  apply hpack
  by_cases hk0 : e - (f.sb : Int) ≥ 0
  · rw [ite_eq_left_iff.mpr fun h => absurd hk0 h]
    dsimp only
    have h1 : n.natAbs = c * 2 ^ (f.sb - c.log2) * (2 ^ j * 2 ^ (e - f.sb).toNat) := by
      rw [hn, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
      congr 2
      omega
    rw [h1, roundQuotient_exact _ _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))]
  · rw [ite_eq_right_iff.mpr fun h => absurd h hk0]
    dsimp only
    have h1 : n.natAbs * 2 ^ (-(e - f.sb)).toNat = c * 2 ^ (f.sb - c.log2) * 2 ^ j := by
      rw [hn]
      exact pow_mul_eq _ _ _ _ _ (by omega)
    rw [h1, roundQuotient_exact _ _ (Nat.two_pow_pos _)]

theorem pack_key (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (key (pack neg B r : Fl f)) = if neg then
      -(((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int)
      else (((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int) := by
  obtain ⟨hs, he, hfr, -⟩ := pack_parts (f := f) neg B r hB hr
  unfold key magKey
  rw [← expField_eq, ← frac_eq, hs, he, hfr]

theorem roundRat_key (hf : (Good f)) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f).isfinite = true ∧
    (key (roundRat n (2 ^ j) z : Fl f)) * ((2 ^ j : Nat) : Int) = n * ((den f) : Int) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := sig_bounds (f := f) c hc hc1
  have hem := hf.emax_eq
  have hS := hf.emax_succ
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  have hB : c.log2 + i + f.bias - j < 2 ^ f.eb := by omega
  have hr : c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb < 2 ^ f.sb := by
    generalize c * 2 ^ (f.sb - c.log2) = q at hq1 hq2 ⊢
    omega
  rw [roundRat_normal hf n c i j z hn hc0 hc1 hlo hhi]
  obtain ⟨-, he, -, -⟩ := pack_parts (f := f) (decide (n < 0)) _ _ hB hr
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  have hnz : (if c.log2 + i + f.bias - j = 0 then 0 else 2 ^ f.sb) = 2 ^ f.sb :=
    ite_eq_right_iff.mpr (by omega)
  rw [pack_key _ _ _ hB hr, hnz, Nat.sub_add_cancel hq1]
  have hpow : c * 2 ^ (f.sb - c.log2) * 2 ^ (c.log2 + i + f.bias - j - 1) * 2 ^ j =
      c * 2 ^ i * (den f) := by
    unfold den
    simp only [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rcases Int.lt_or_le n 0 with hneg | hpos
  · have hn' : n = -((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_true hneg, ↓reduceIte]
    rw [hn', Int.neg_mul, Int.neg_mul, ← Int.natCast_mul, ← Int.natCast_mul, hpow]
  · have hn' : n = ((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_false (Int.not_lt.2 hpos), Bool.false_eq_true, ↓reduceIte]
    rw [hn', ← Int.natCast_mul, ← Int.natCast_mul, hpow]

theorem zero_spec (hf : (Good f)) (s : Bool) :
    (zero s : Fl f).isfinite = true ∧ (key (zero s : Fl f)) = 0 := by
  have hz : (zero s : Fl f) = pack s 0 0 := by simp [zero, pack]
  have hS := hf.emax_succ
  have hE := hf.emax_eq
  obtain ⟨-, he, -, -⟩ := pack_parts (f := f) s 0 0 (by omega) (Nat.two_pow_pos _)
  rw [hz]
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  rw [pack_key _ _ _ (by omega) (Nat.two_pow_pos _)]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_le, Nat.sub_eq_zero_of_le, Nat.pow_zero, Nat.mul_one, Int.cast_ofNat_Int, Int.neg_zero]


theorem convert_widen_key (hf : (Good f)) (hg : (Good g)) (hne : (g == f) = false)
    (hsb : f.sb ≤ g.sb) (hbias : f.bias + f.sb ≤ g.bias) (x : Fl f) :
    (convert x : Fl g).isnan = x.isnan ∧
    (convert x : Fl g).isinf = x.isinf ∧
    (convert x : Fl g).isfinite = x.isfinite ∧
    (x.isinf = true → (convert x : Fl g).signbit = x.signbit) ∧
    (x.isfinite = true →
      (key (convert x : Fl g)) * ((den f) : Int) = (key x) * ((den g) : Int) ∧
      (convert x : Fl g).toRat.1 * (x.toRat.2 : Int) = x.toRat.1 * ((convert x : Fl g).toRat.2 : Int)) := by
  have hgS := hg.emax_succ
  have hgE := hg.emax_eq
  have hfE := hf.emax_eq
  have hPg := Nat.two_pow_pos g.sb
  have hDf : (0 : Int) < (den f) := by have := den_pos f; omega
  have hDg : (0 : Int) < (den g) := by have := den_pos g; omega
  unfold convert
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hn : x.isnan
  · cases hi : x.isinf
    · have hfin : x.isfinite = true := by simp_all [isnan, isinf, isfinite]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hrat_x := (toRat_key hf x hfin).2
      obtain ⟨m, i, j, hr, hk, hm, hrange⟩ := toRat_cases hf x hfin
      have hkey := hrat_x
      rw [hr] at hkey
      dsimp only at hkey
      have hfin_scale :
          (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g).isfinite = true ∧
          (key (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g)) * ((den f) : Int) = (key x) * ((den g) : Int) := by
        rw [hr]
        dsimp only
        by_cases hm0 : m = 0
        · subst hm0
          have hz : (roundRat (if x.signbit then -((0 * 2 ^ i : Nat) : Int)
              else ((0 * 2 ^ i : Nat) : Int)) (2 ^ j) x.signbit : Fl g) = zero x.signbit := by
            cases x.signbit <;> simp [roundRat]
          rw [hz]
          obtain ⟨hz1, hz2⟩ := zero_spec hg x.signbit
          have hkx : (key x) = 0 := by
            have h2 : ((2 ^ j : Nat) : Int) ≠ 0 := by have := Nat.two_pow_pos j; omega
            have h3 : (key x) * ((2 ^ j : Nat) : Int) = 0 := by
              rw [← hkey]; cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Int.cast_ofNat_Int, Int.neg_zero, Int.zero_mul]
            exact (Int.mul_eq_zero.1 h3).resolve_right h2
          exact ⟨hz1, by rw [hz2, hkx]; simp only [Int.zero_mul]⟩
        · obtain ⟨hlo, hhi⟩ := hrange hm0
          have hn' : (if x.signbit then -((m * 2 ^ i : Nat) : Int)
              else ((m * 2 ^ i : Nat) : Int)).natAbs = m * 2 ^ i := by
            cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg,
              Int.natAbs_natCast]
          have hm1 : m < 2 ^ (g.sb + 1) :=
            Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
          obtain ⟨h1, h2⟩ := roundRat_key (f := g) hg _ m i j x.signbit hn' (by omega) hm1
            (by omega) (by omega)
          have hj : (0 : Int) < ((2 ^ j : Nat) : Int) := by have := Nat.two_pow_pos j; omega
          refine ⟨h1, ?_⟩
          generalize (if x.signbit then -((m * 2 ^ i : Nat) : Int)
            else ((m * 2 ^ i : Nat) : Int)) = N at h2 hkey
          generalize (key (roundRat N (2 ^ j) x.signbit : Fl g)) = K at h2
          apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hj)
          calc K * ((den f) : Int) * ((2 ^ j : Nat) : Int)
              = K * ((2 ^ j : Nat) : Int) * ((den f) : Int) := by rw [Int.mul_right_comm]
            _ = N * ((den g) : Int) * ((den f) : Int) := by rw [h2]
            _ = N * ((den f) : Int) * ((den g) : Int) := by rw [Int.mul_right_comm]
            _ = (key x) * ((2 ^ j : Nat) : Int) * ((den g) : Int) := by rw [hkey]
            _ = (key x) * ((den g) : Int) * ((2 ^ j : Nat) : Int) := by rw [Int.mul_right_comm]
      obtain ⟨hg_fin, hg_scale⟩ := hfin_scale
      generalize (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g) = w at hg_fin hg_scale ⊢
      have hrat_w := (toRat_key hg w hg_fin).2
      refine ⟨isnan_of_finite hg_fin, isinf_of_finite hg_fin, by rw [hg_fin, hfin],
        fun h => False.elim h, fun _ => ⟨hg_scale, ?_⟩⟩
      apply Int.eq_of_mul_eq_mul_right (by omega : ((den g) : Int) ≠ 0)
      apply Int.eq_of_mul_eq_mul_right (by omega : ((den f) : Int) ≠ 0)
      have hstep1 : (w.toRat.1 * ((den g) : Int)) * (x.toRat.2 : Int) * ((den f) : Int) =
          ((key w) * ((den f) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by
        rw [hrat_w, Int.mul_right_comm ((key w) * (w.toRat.2 : Int)) (x.toRat.2 : Int) ((den f) : Int),
          Int.mul_right_comm (key w) (w.toRat.2 : Int) ((den f) : Int)]
      have hstep2 : (x.toRat.1 * ((den f) : Int)) * (w.toRat.2 : Int) * ((den g) : Int) =
          ((key x) * ((den g) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by
        rw [hrat_x, Int.mul_right_comm ((key x) * (x.toRat.2 : Int)) (w.toRat.2 : Int) ((den g) : Int),
          Int.mul_right_comm (key x) (x.toRat.2 : Int) ((den g) : Int),
          Int.mul_right_comm ((key x) * ((den g) : Int)) (x.toRat.2 : Int) (w.toRat.2 : Int)]
      calc w.toRat.1 * (x.toRat.2 : Int) * ((den g) : Int) * ((den f) : Int)
          = (w.toRat.1 * ((den g) : Int)) * (x.toRat.2 : Int) * ((den f) : Int) := by
            rw [Int.mul_right_comm w.toRat.1 (x.toRat.2 : Int) ((den g) : Int)]
        _ = ((key w) * ((den f) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := hstep1
        _ = ((key x) * ((den g) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by rw [hg_scale]
        _ = (x.toRat.1 * ((den f) : Int)) * (w.toRat.2 : Int) * ((den g) : Int) := hstep2.symm
        _ = x.toRat.1 * (w.toRat.2 : Int) * ((den g) : Int) * ((den f) : Int) := by
            rw [Int.mul_right_comm x.toRat.1 ((den f) : Int) (w.toRat.2 : Int),
              Int.mul_right_comm (x.toRat.1 * (w.toRat.2 : Int)) ((den f) : Int) ((den g) : Int)]
    · have hinf : (inf x.signbit : Fl g) = pack x.signbit g.emax 0 := by simp [inf, pack]
      obtain ⟨hs, he, hfr, -⟩ := pack_parts (f := g) x.signbit g.emax 0 (by omega) hPg
      simp only [Bool.false_eq_true, ↓reduceIte, hinf]
      have hpn : (pack x.signbit g.emax 0 : Fl g).isnan = false := by unfold isnan; rw [he, hfr]; simp only [BEq.rfl, bne_self_eq_false, Bool.and_false]
      have hpi : (pack x.signbit g.emax 0 : Fl g).isinf = true := by unfold isinf; rw [he, hfr]; simp only [BEq.rfl, Bool.and_self]
      have hpf : (pack x.signbit g.emax 0 : Fl g).isfinite = false := by unfold isfinite; rw [he]; simp only [bne_self_eq_false]
      have hxf : x.isfinite = false := by
        unfold isinf at hi; unfold isfinite; simp only [Bool.and_eq_true, beq_iff_eq] at hi; simp [hi.1]
      exact ⟨hpn, hpi, by rw [hpf, hxf], fun _ => hs, fun h => by rw [hxf] at h; exact Bool.noConfusion h⟩
  · have hfr : x.frac < 2 ^ f.sb := by rw [frac_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpay : x.frac * 2 ^ (g.sb - f.sb) < 2 ^ g.sb := by
      calc x.frac * 2 ^ (g.sb - f.sb) < 2 ^ f.sb * 2 ^ (g.sb - f.sb) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hfr
        _ = 2 ^ g.sb := by rw [← Nat.pow_add]; congr 1; omega
    have hhalf : 2 ^ (g.sb - 1) < 2 ^ g.sb :=
      Nat.pow_lt_pow_right (by decide) (by have := hg.sb_pos; omega)
    have hL : Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1)) < 2 ^ g.sb :=
      Nat.or_lt_two_pow hpay hhalf
    have hpk : (ofBits ((if x.signbit then 2 ^ (g.eb + g.sb) else 0) + g.emax * 2 ^ g.sb +
        Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) : Fl g) =
        pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) := by
      unfold pack; rw [Nat.add_assoc]
    obtain ⟨-, he, hfr', -⟩ := pack_parts (f := g) x.signbit g.emax _ (by omega) hL
    simp only [↓reduceIte, ite_eq_left_iff.mpr fun h => absurd hsb h, hpk]
    have hpn : (pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isnan = true := by unfold isnan; rw [he, hfr']; simp only [BEq.rfl, Nat.lor_eq, Bool.true_and, bne_iff_ne, ne_eq, Nat.or_eq_zero_iff, Nat.pow_eq_zero, reduceCtorEq, false_and, and_false, not_false_eq_true]
    have hpi : (pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isinf = false := by unfold isinf; rw [he, hfr']; simp only [BEq.rfl, Nat.lor_eq, Bool.true_and, beq_eq_false_iff_ne, ne_eq, Nat.or_eq_zero_iff, Nat.pow_eq_zero, reduceCtorEq, false_and, and_false, not_false_eq_true]
    have hpf : (pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isfinite = false := by unfold isfinite; rw [he]; simp only [bne_self_eq_false]
    have hxi : x.isinf = false := by
      unfold isnan at hn; unfold isinf; simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hn; simp [hn.1, hn.2]
    have hxf : x.isfinite = false := by
      unfold isnan at hn; unfold isfinite; simp only [Bool.and_eq_true, beq_iff_eq] at hn; simp [hn.1]
    exact ⟨hpn, by rw [hpi, hxi], by rw [hpf, hxf],
      fun h => by rw [hxi] at h; exact Bool.noConfusion h,
      fun h => by rw [hxf] at h; exact Bool.noConfusion h⟩


end FloatConstructAux

/-- Equality of finite rational values transports exact integer representation. -/
theorem floatConstruct_rat_transport {S T : FTy} (x : FV S) (y : FV T)
    (hfin : y.isfinite = x.isfinite)
    (hcross : x.isfinite = true →
      y.toRat.1 * (x.toRat.2 : Int) = x.toRat.1 * (y.toRat.2 : Int))
    (n : Int) : ConvFloatEqualsInteger x n ↔ ConvFloatEqualsInteger y n := by
  constructor
  · rintro ⟨hx, hd, hn⟩
    have hy : y.isfinite = true := hfin.trans hx
    refine ⟨hy, floatConstruct_den_pos y hy, ?_⟩
    apply Int.eq_of_mul_eq_mul_right (by omega : (x.toRat.2 : Int) ≠ 0)
    rw [hcross hx, hn, Int.mul_right_comm]
  · rintro ⟨hy, hd, hn⟩
    have hx : x.isfinite = true := hfin.symm.trans hy
    refine ⟨hx, floatConstruct_den_pos x hx, ?_⟩
    apply Int.eq_of_mul_eq_mul_right (by omega : (y.toRat.2 : Int) ≠ 0)
    rw [← hcross hx, hn, Int.mul_right_comm]

/-- Widening either smaller IEEE format to binary64 preserves exact integrality. -/
theorem floatConstruct_widen64_integral {T : FTy} (x : FV T) (n : Int) :
    ConvFloatEqualsInteger x n ↔ ConvFloatEqualsInteger (convertFloat .f64 x) n := by
  cases T
  · change ConvFloatEqualsInteger x n ↔ ConvFloatEqualsInteger (Fl.convert x : FV .f64) n
    have h := FloatConstructAux.convert_widen_key FloatConstructAux.good_half
      FloatConstructAux.good_double (by decide) (by decide) (by decide) x
    exact floatConstruct_rat_transport x _ h.2.2.1 (fun hx => (h.2.2.2.2 hx).2) n
  · change ConvFloatEqualsInteger x n ↔ ConvFloatEqualsInteger (Fl.convert x : FV .f64) n
    have h := FloatConstructAux.convert_widen_key FloatConstructAux.good_single
      FloatConstructAux.good_double (by decide) (by decide) (by decide) x
    exact floatConstruct_rat_transport x _ h.2.2.1 (fun hx => (h.2.2.2.2 hx).2) n
  · exact Iff.rfl

theorem floatConstruct_result_transport {S T : FTy} (x : FV S) (y : FV T)
    (h : ∀ n, ConvFloatEqualsInteger x n ↔ ConvFloatEqualsInteger y n)
    (action : Jl BigInt) :
    ConvExactFloatResult x action ↔ ConvExactFloatResult y action := by
  cases action with
  | ok z => exact and_congr Iff.rfl (h z.val)
  | error e =>
    cases e <;> first
    | exact Iff.rfl
    | exact not_congr (exists_congr h)

theorem floatConstruct16_of64 (h64 : Float64ConstructionCorrect) :
    Float16ConstructionCorrect := by
  intro x
  exact (floatConstruct_result_transport x (convertFloat .f64 x)
    (floatConstruct_widen64_integral x) (fromFloat16 x)).mpr (h64 _)

theorem floatConstruct32_of64 (h64 : Float64ConstructionCorrect) :
    Float32ConstructionCorrect := by
  intro x
  exact (floatConstruct_result_transport x (convertFloat .f64 x)
    (floatConstruct_widen64_integral x) (fromFloat32 x)).mpr (h64 _)

theorem BignumsGmpFloat64Construction_proven :
    JuliaLean.Proofs.base.gmp.Round1.Float64ConstructionCorrect := by
  intro x
  apply floatConstruct64_of_storage
  intro hi
  have htest := hi
  simp only [Fl.isinteger, Bool.and_eq_true] at htest
  have hf : x.isfinite = true := htest.1
  exact cgGMPInputWriteInit1024 x.truncVal (floatConstruct64_trunc_bound x hf)

theorem BignumsGmpFloat16Construction_proven :
    JuliaLean.Proofs.base.gmp.Round1.Float16ConstructionCorrect :=
  floatConstruct16_of64 BignumsGmpFloat64Construction_proven

theorem BignumsGmpFloat32Construction_proven :
    JuliaLean.Proofs.base.gmp.Round1.Float32ConstructionCorrect :=
  floatConstruct32_of64 BignumsGmpFloat64Construction_proven

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: Arithmetic. -/
namespace JuliaLean.ChatGPT.Batch4.Group6
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem arith_binary_returns (op : MPZ.BinaryOp) (x y : BigInt) (n : Int)
    (h : MPZ.binaryValue op x.val y.val = .ok n) (P : Int → Prop) (hn : P n) :
    ArithReturns (MPZ.binary op x y) P := by
  unfold ArithReturns MPZ.binary MPZ.binaryBang
  rw [h]
  exact ⟨_, rfl, hn⟩

theorem arith_addition_contract (a b : Int) : ArithAddition a b (a + b) := by
  constructor
  · omega
  · intro t; omega

theorem arith_subtraction_contract (a b : Int) : ArithSubtraction a b (a - b) := by
  constructor
  · omega
  · intro t; omega

theorem BignumsGmpAdditionExact_proven : JuliaLean.Proofs.base.gmp.Round1.AdditionExact := by
  intro x y _ _
  have h := arith_binary_returns .add x y (x.val + y.val) rfl
    (ArithAddition x.val y.val) (arith_addition_contract x.val y.val)
  exact ⟨h, h⟩

theorem BignumsGmpSubtractionExact_proven : JuliaLean.Proofs.base.gmp.Round1.SubtractionExact := by
  intro x y _ _
  have h := arith_binary_returns .sub x y (x.val - y.val) rfl
    (ArithSubtraction x.val y.val) (arith_subtraction_contract x.val y.val)
  exact ⟨h, h⟩

theorem arith_repeated_sum (a : Int) (xs : List Nat) :
    xs.foldr (fun _ total => a + total) 0 = a * (xs.length : Int) := by
  induction xs with
  | nil => simp only [List.foldr_nil, List.length_nil, Int.natCast_zero, Int.mul_zero]
  | cons n xs ih =>
    simp only [List.foldr_cons, List.length_cons, ih, Int.natCast_add, Int.natCast_one,
      Int.mul_add, Int.mul_one]
    omega

theorem arith_repeated_product (a b : Int) : ArithRepeatedProduct a b = a * b := by
  unfold ArithRepeatedProduct
  rw [arith_repeated_sum, List.length_range]
  by_cases hb : b < 0
  · rw [ite_eq_left hb, Int.ofNat_natAbs_of_nonpos (show b ≤ 0 by omega), Int.mul_neg, Int.neg_neg]
  · rw [ite_eq_right hb, Int.ofNat_natAbs_of_nonneg (show 0 ≤ b by omega)]

theorem arith_multiplication_contract (a b : Int) : ArithMultiplication a b (a * b) := by
  exact (arith_repeated_product a b).symm

theorem BignumsGmpMultiplicationExact_proven : JuliaLean.Proofs.base.gmp.Round1.MultiplicationExact := by
  intro x y _ _
  have h := arith_binary_returns .mul x y (x.val * y.val) rfl
    (ArithMultiplication x.val y.val) (arith_multiplication_contract x.val y.val)
  exact ⟨h, h⟩


theorem arith_tmod_pair (a b : Int) (hb : b ≠ 0) :
    ArithDivisionPair .toZero a b (a.tdiv b) (a.tmod b) := by
  refine ⟨(Int.tdiv_mul_add_tmod a b).symm, ?_, ?_⟩
  · rw [Int.natAbs_tmod]
    exact Nat.mod_lt _ (Int.natAbs_pos.mpr hb)
  · unfold ArithRemainderSign
    by_cases hr : a.tmod b = 0
    · exact Or.inl hr
    · right
      by_cases ha : 0 ≤ a
      · have h := Int.tmod_nonneg b ha
        omega
      · have h := Int.tmod_nonneg b (show 0 ≤ -a by omega)
        rw [Int.neg_tmod] at h
        omega

theorem arith_fmod_pair (a b : Int) (hb : b ≠ 0) :
    ArithDivisionPair .down a b (a.fdiv b) (a.fmod b) := by
  refine ⟨(Int.fdiv_mul_add_fmod a b).symm, ?_⟩
  have h0 := Int.emod_nonneg a hb
  have h1 := Int.emod_lt a hb
  unfold ArithRemainderSign
  rw [Int.fmod_eq_emod]
  simp only [Int.dvd_iff_emod_eq_zero]
  by_cases hrem : a % b = 0
  · simp only [hrem, or_true, ↓reduceIte, Int.zero_add]
    exact ⟨by omega, Or.inl (by trivial)⟩
  · by_cases hb0 : 0 ≤ b
    · simp only [hb0, true_or, ↓reduceIte, Int.add_zero]
      exact ⟨by omega, Or.inr (by omega)⟩
    · simp only [hb0, hrem, false_or, ↓reduceIte]
      exact ⟨by omega, Or.inr (by omega)⟩

theorem arith_ceiling_pair (a b : Int) (hb : b ≠ 0) :
    ArithDivisionPair .up a b (-((-a).fdiv b)) (-((-a).fmod b)) := by
  obtain ⟨heq, hbound, hsign⟩ := arith_fmod_pair (-a) b hb
  refine ⟨?_, ?_, ?_⟩
  · rw [Int.neg_mul]
    omega
  · rw [Int.natAbs_neg]
    exact hbound
  · unfold ArithRemainderSign at hsign ⊢
    rcases hsign with hzero | hneg
    · left; omega
    · by_cases hr : (-a).fmod b = 0
      · left; omega
      · right; omega

theorem arith_binary_error (op : MPZ.BinaryOp) (x y : BigInt) (e : JlError)
    (h : MPZ.binaryValue op x.val y.val = .error e) :
    MPZ.binary op x y = .error e := by
  unfold MPZ.binary MPZ.binaryBang
  rw [h]
  rfl

theorem BignumsGmpModuloEuclidean_proven : JuliaLean.Proofs.base.gmp.Round1.ModuloEuclidean := by
  intro x y _ _
  unfold ArithRemainderResult
  by_cases h : y.val = 0
  · rw [ite_eq_left h]
    exact arith_binary_error .fdivR x y .divideError (by simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte])
  · rw [ite_eq_right h]
    apply arith_binary_returns .fdivR x y (x.val - x.val.fdiv y.val * y.val)
    · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_true, or_false, false_or, true_or]
    · refine ⟨x.val.fdiv y.val, ?_⟩
      have heq : x.val - x.val.fdiv y.val * y.val = x.val.fmod y.val := by
        have := Int.fdiv_mul_add_fmod x.val y.val
        omega
      rw [heq]
      exact arith_fmod_pair x.val y.val h

theorem BignumsGmpRemainderEuclidean_proven : JuliaLean.Proofs.base.gmp.Round1.RemainderEuclidean := by
  intro x y _ _
  unfold ArithRemainderResult
  by_cases h : y.val = 0
  · rw [ite_eq_left h]
    exact arith_binary_error .tdivR x y .divideError (by simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte])
  · rw [ite_eq_right h]
    apply arith_binary_returns .tdivR x y (x.val - x.val.tdiv y.val * y.val)
    · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_true, or_false, false_or, true_or]
    · refine ⟨x.val.tdiv y.val, ?_⟩
      have heq : x.val - x.val.tdiv y.val * y.val = x.val.tmod y.val := by
        have := Int.tdiv_mul_add_tmod x.val y.val
        omega
      rw [heq]
      exact arith_tmod_pair x.val y.val h

theorem arith_divides_iff (a b : Int) : ArithDivides a b ↔ a ∣ b := Iff.rfl

theorem arith_gcd_contract (a b : Int) : ArithGCD a b (Int.gcd a b) := by
  refine ⟨Int.natCast_nonneg _, Int.gcd_dvd_left a b, Int.gcd_dvd_right a b, ?_⟩
  intro d ha hb
  exact Int.dvd_coe_gcd ha hb

theorem BignumsGmpGcdUniversal_proven : JuliaLean.Proofs.base.gmp.Round1.GreatestCommonDivisor := by
  intro x y _ _
  exact arith_binary_returns .gcd x y (Int.gcd x.val y.val) rfl
    (ArithGCD x.val y.val) (arith_gcd_contract x.val y.val)

theorem arith_lcm_contract (a b : Int) : ArithLCM a b (Int.lcm a b) := by
  refine ⟨Int.natCast_nonneg _, Int.dvd_lcm_left a b, Int.dvd_lcm_right a b, ?_⟩
  intro m ha hb
  exact Int.coe_lcm_dvd ha hb

theorem BignumsGmpLcmUniversal_proven : JuliaLean.Proofs.base.gmp.Round1.LeastCommonMultiple := by
  intro x y _ _
  apply arith_binary_returns .lcm x y (Int.lcm x.val y.val)
  · simp only [MPZ.binaryValue, Pure.pure, Except.pure, Int.lcm_eq_mul_div, Int.gcd_eq_natAbs_gcd_natAbs]
    rfl
  · exact arith_lcm_contract x.val y.val

theorem arith_division_modes (x y : BigInt) (mode : DivisionMode) :
    ArithQuotientResult (divRound x y mode) mode x.val y.val := by
  unfold ArithQuotientResult divRound
  by_cases h : y.val = 0
  · rw [ite_eq_left h]
    cases mode <;> apply arith_binary_error _ x y .divideError <;>
      simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte]
  · rw [ite_eq_right h]
    cases mode with
    | toZero =>
      apply arith_binary_returns .tdivQ x y (x.val.tdiv y.val)
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_true, or_false, false_or, true_or]
      · exact ⟨x.val.tmod y.val, arith_tmod_pair x.val y.val h⟩
    | down =>
      apply arith_binary_returns .fdivQ x y (x.val.fdiv y.val)
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_true, or_false, false_or, true_or]
      · exact ⟨x.val.fmod y.val, arith_fmod_pair x.val y.val h⟩
    | up =>
      apply arith_binary_returns .cdivQ x y (-((-x.val).fdiv y.val))
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_true, or_false, false_or, true_or]
      · exact ⟨-((-x.val).fmod y.val), arith_ceiling_pair x.val y.val h⟩

theorem BignumsGmpDivisionModes_proven : JuliaLean.Proofs.base.gmp.Round1.DivisionModesEuclidean := by
  intro x y mode _ _
  exact arith_division_modes x y mode

theorem BignumsGmpDivisionDefault_proven : JuliaLean.Proofs.base.gmp.Round1.DefaultDivisionEuclidean := by
  intro x y _ _
  exact arith_division_modes x y .toZero

theorem BignumsGmpDivisionFloor_proven : JuliaLean.Proofs.base.gmp.Round1.FloorDivisionEuclidean := by
  intro x y _ _
  exact arith_division_modes x y .down

theorem BignumsGmpDivisionCeiling_proven : JuliaLean.Proofs.base.gmp.Round1.CeilingDivisionEuclidean := by
  intro x y _ _
  exact arith_division_modes x y .up


theorem arith_culong_range {t : IntTy} (c : JInt t) (dispatch : IsCulongMax t) :
    0 ≤ c.val ∧ c.val < (2 : Int)^64 := by
  have hc := c.property
  cases t <;> simp [IsCulongMax, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at dispatch hc ⊢ <;> omega

theorem arith_clong_range {t : IntTy} (c : JInt t) (dispatch : IsClongMax t) :
    -(2 : Int)^63 ≤ c.val ∧ c.val < (2 : Int)^63 := by
  have hc := c.property
  cases t <;> simp [IsClongMax, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at dispatch hc ⊢ <;> omega

theorem arith_culong_cast {t : IntTy} (c : JInt t) (dispatch : IsCulongMax t) :
    (JInt.wrap .u64 c.val).val = c.val := by
  have h := arith_culong_range c dispatch
  change wrapInt .u64 c.val = c.val
  apply wrapInt_of_inRange
  change 0 ≤ c.val ∧ c.val ≤ (2 : Int)^64 - 1
  omega

theorem arith_nonnegative_clong_cast {t : IntTy} (c : JInt t) (dispatch : IsClongMax t)
    (hc : ¬ c.val < 0) : (JInt.wrap .u64 c.val).val = c.val := by
  have h := arith_clong_range c dispatch
  change wrapInt .u64 c.val = c.val
  apply wrapInt_of_inRange
  change 0 ≤ c.val ∧ c.val ≤ (2 : Int)^64 - 1
  omega

theorem arith_negative_clong_magnitude {t : IntTy} (c : JInt t) (dispatch : IsClongMax t)
    (hc : c.val < 0) : (-(JInt.rem .u64 c)).val = -c.val := by
  have h := arith_clong_range c dispatch
  change wrapInt .u64 (-wrapInt .u64 c.val) = -c.val
  simp only [wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true, ↓reduceIte]
  omega

theorem BignumsGmpUnsignedRightAdd_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedRightAddition := by
  intro t x c dispatch _
  change ArithAddition x.val c.val (x.val + (JInt.wrap .u64 c.val).val)
  rw [arith_culong_cast c dispatch]
  exact arith_addition_contract x.val c.val

theorem BignumsGmpUnsignedLeftAdd_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedLeftAddition := by
  intro t x c dispatch _
  change ArithAddition c.val x.val (x.val + (JInt.wrap .u64 c.val).val)
  rw [arith_culong_cast c dispatch, Int.add_comm x.val c.val]
  exact arith_addition_contract c.val x.val

theorem BignumsGmpUnsignedRightSub_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedRightSubtraction := by
  intro t x c dispatch _
  change ArithSubtraction x.val c.val (x.val - (JInt.wrap .u64 c.val).val)
  rw [arith_culong_cast c dispatch]
  exact arith_subtraction_contract x.val c.val

theorem BignumsGmpUnsignedLeftSub_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedLeftSubtraction := by
  intro t x c dispatch _
  change ArithSubtraction c.val x.val ((JInt.wrap .u64 c.val).val - x.val)
  rw [arith_culong_cast c dispatch]
  exact arith_subtraction_contract c.val x.val

theorem arith_add_clong_val {t : IntTy} (c : JInt t) (dispatch : IsClongMax t) (x : BigInt) :
    (addClongMax dispatch x c).val = x.val + c.val := by
  unfold addClongMax
  by_cases hc : c.val < 0
  · rw [ite_eq_left hc]
    change x.val - (-(JInt.rem .u64 c)).val = x.val + c.val
    rw [arith_negative_clong_magnitude c dispatch hc]
    omega
  · rw [ite_eq_right hc]
    change x.val + (JInt.wrap .u64 c.val).val = x.val + c.val
    rw [arith_nonnegative_clong_cast c dispatch hc]

theorem arith_sub_clong_val {t : IntTy} (c : JInt t) (dispatch : IsClongMax t) (x : BigInt) :
    (subClongMax dispatch x c).val = x.val - c.val := by
  unfold subClongMax
  by_cases hc : c.val < 0
  · rw [ite_eq_left hc]
    change x.val + (-(JInt.rem .u64 c)).val = x.val - c.val
    rw [arith_negative_clong_magnitude c dispatch hc]
    omega
  · rw [ite_eq_right hc]
    change x.val - (JInt.wrap .u64 c.val).val = x.val - c.val
    rw [arith_nonnegative_clong_cast c dispatch hc]

theorem arith_clong_sub_val {t : IntTy} (c : JInt t) (dispatch : IsClongMax t) (x : BigInt) :
    (clongMaxSub dispatch c x).val = c.val - x.val := by
  unfold clongMaxSub
  by_cases hc : c.val < 0
  · rw [ite_eq_left hc]
    change -(x.val + (-(JInt.rem .u64 c)).val) = c.val - x.val
    rw [arith_negative_clong_magnitude c dispatch hc]
    omega
  · rw [ite_eq_right hc]
    change (JInt.wrap .u64 c.val).val - x.val = c.val - x.val
    rw [arith_nonnegative_clong_cast c dispatch hc]

theorem BignumsGmpSignedRightAdd_proven : JuliaLean.Proofs.base.gmp.Round1.SignedRightAddition := by
  intro t x c dispatch _
  rw [arith_add_clong_val c dispatch x]
  exact arith_addition_contract x.val c.val

theorem BignumsGmpSignedLeftAdd_proven : JuliaLean.Proofs.base.gmp.Round1.SignedLeftAddition := by
  intro t x c dispatch _
  change ArithAddition c.val x.val (addClongMax dispatch x c).val
  rw [arith_add_clong_val c dispatch x, Int.add_comm x.val c.val]
  exact arith_addition_contract c.val x.val

theorem BignumsGmpSignedRightSub_proven : JuliaLean.Proofs.base.gmp.Round1.SignedRightSubtraction := by
  intro t x c dispatch _
  rw [arith_sub_clong_val c dispatch x]
  exact arith_subtraction_contract x.val c.val

theorem BignumsGmpSignedLeftSub_proven : JuliaLean.Proofs.base.gmp.Round1.SignedLeftSubtraction := by
  intro t x c dispatch _
  rw [arith_clong_sub_val c dispatch x]
  exact arith_subtraction_contract c.val x.val

theorem BignumsGmpUnsignedRightMul_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedRightMultiplication := by
  intro t x c dispatch _
  change ArithMultiplication x.val c.val (x.val * (JInt.wrap .u64 c.val).val)
  rw [arith_culong_cast c dispatch]
  exact arith_multiplication_contract x.val c.val

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: Bitwise. -/
namespace JuliaLean.ChatGPT.Batch4.Group6

open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

def bwBit (a : Int) (i : Nat) : Bool := decide ((2 : Int)^i ≤ a % (2 : Int)^(i+1))

def bwDecode (w r : Nat) : Int :=
  if 2^(w-1) ≤ r then (r : Int) - (2 : Int)^w else (r : Int)

theorem bwNatTop (n i : Nat) (h : n < 2^(i+1)) :
    n.testBit i = decide (2^i ≤ n) := by
  by_cases hn : 2^i ≤ n
  · rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hn h]
    simp only [hn, decide_true]
  · rw [Nat.testBit_lt_two_pow (by omega : n < 2^i)]
    simp only [hn, decide_false]

theorem bwNatBit (n i : Nat) : bwBit (n : Int) i = n.testBit i := by
  unfold bwBit
  change decide (((2^i : Nat) : Int) ≤ ((n % 2^(i+1) : Nat) : Int)) = n.testBit i
  simp only [Int.ofNat_le]
  have hb := Nat.testBit_mod_two_pow n (i+1) i
  simp only [Nat.lt_succ_self, decide_true, Bool.true_and] at hb
  rw [← hb, bwNatTop (n % 2^(i+1)) i (Nat.mod_lt _ (Nat.two_pow_pos _))]

theorem bwPowDvd (j w : Nat) (hj : j ≤ w) : (2 : Int)^j ∣ (2 : Int)^w := by
  refine ⟨(2 : Int)^(w-j), ?_⟩
  rw [← Int.pow_add]
  congr 1
  omega

theorem bwResidueBit (a : Int) (w i : Nat) (hi : i < w) :
    bwBit a i = ((a % (2 : Int)^w).toNat).testBit i := by
  have hp : 0 < (2 : Int)^w := Int.pow_pos (by decide)
  have hn : 0 ≤ a % (2 : Int)^w := Int.emod_nonneg _ (by omega)
  have hm := Int.emod_emod_of_dvd a (bwPowDvd (i+1) w (by omega))
  calc
    bwBit a i = bwBit (a % (2 : Int)^w) i := by
      unfold bwBit
      rw [hm]
    _ = bwBit (((a % (2 : Int)^w).toNat : Nat) : Int) i := by
      rw [Int.toNat_of_nonneg hn]
    _ = _ := bwNatBit _ _

theorem bwResidueLt (a : Int) (w : Nat) : (a % (2 : Int)^w).toNat < 2^w := by
  have hp : 0 < (2 : Int)^w := Int.pow_pos (by decide)
  have hn := Int.emod_nonneg a (by omega : (2 : Int)^w ≠ 0)
  have hl := Int.emod_lt_of_pos a hp
  change a % (2 : Int)^w < ((2^w : Nat) : Int) at hl
  omega

theorem bwHigh (a : Int) (i : Nat) (ha : a.natAbs < 2^i) :
    bwBit a i = decide (a < 0) := by
  have hp : 0 < (2 : Int)^i := Int.pow_pos (by decide)
  have habs : (a.natAbs : Int) < (2 : Int)^i := Int.ofNat_lt.mpr ha
  have hab : -(2 : Int)^i < a ∧ a < (2 : Int)^i := by omega
  unfold bwBit
  rw [Int.pow_succ]
  by_cases hn : a < 0
  · have hm : a % ((2 : Int)^i * 2) = a + (2 : Int)^i * 2 := by
      rw [← Int.add_emod_right a ((2 : Int)^i * 2)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm]
    have hb : (2 : Int)^i ≤ a + (2 : Int)^i * 2 := by omega
    simp only [hb, hn, decide_true]
  · rw [Int.emod_eq_of_lt (by omega : 0 ≤ a) (by omega : a < (2 : Int)^i * 2)]
    have hb : ¬ (2 : Int)^i ≤ a := by omega
    simp only [hb, hn, decide_false]

theorem bwDecodeMod (w r : Nat) (hr : r < 2^w) :
    bwDecode w r % (2 : Int)^w = (r : Int) := by
  have hb : (r : Int) < (2 : Int)^w := Int.ofNat_lt.mpr hr
  unfold bwDecode
  split
  · rw [Int.sub_emod_right]
    exact Int.emod_eq_of_lt (by omega) hb
  · exact Int.emod_eq_of_lt (by omega) hb

theorem bwDecodeBound (w r : Nat) (hr : r < 2^w) :
    (bwDecode w r).natAbs < 2^w := by
  have hp := Nat.two_pow_pos (w-1)
  have hp' := Nat.two_pow_pos w
  unfold bwDecode
  change (if 2^(w-1) ≤ r then (r : Int) - ((2^w : Nat) : Int) else (r : Int)).natAbs < 2^w
  split <;> omega

theorem bwDecodeNegative (w r : Nat) (hr : r < 2^w) :
    bwDecode w r < 0 ↔ 2^(w-1) ≤ r := by
  unfold bwDecode
  change (if 2^(w-1) ≤ r then (r : Int) - ((2^w : Nat) : Int) else (r : Int)) < 0 ↔ _
  split <;> omega

theorem bwDecodeLow (w r i : Nat) (hr : r < 2^w) (hi : i < w) :
    bwBit (bwDecode w r) i = r.testBit i := by
  rw [bwResidueBit _ w i hi, bwDecodeMod w r hr, Int.toNat_natCast]

theorem bwDecodeHigh (w r i : Nat) (hw : 0 < w) (hr : r < 2^w) (hi : w ≤ i) :
    bwBit (bwDecode w r) i = r.testBit (w-1) := by
  have hbound : (bwDecode w r).natAbs < 2^i :=
    Nat.lt_of_lt_of_le (bwDecodeBound w r hr) (Nat.pow_le_pow_right Nat.zero_lt_two hi)
  rw [bwHigh _ i hbound]
  simp only [bwDecodeNegative w r hr]
  have hr' : r < 2^((w-1)+1) := by
    have he : (w-1)+1 = w := by omega
    rw [he]
    exact hr
  exact (bwNatTop r (w-1) hr').symm

theorem bwOpBound (op : Nat → Nat → Nat) (f : Bool → Bool → Bool)
    (hbit : ∀ a b i, (op a b).testBit i = f (a.testBit i) (b.testBit i))
    (hz : f false false = false) (a b w : Nat) (ha : a < 2^w) (hb : b < 2^w) :
    op a b < 2^w := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hp := Nat.pow_le_pow_right Nat.zero_lt_two hi
  rw [hbit, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha hp),
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hp), hz]

theorem bwOpBits (op : Nat → Nat → Nat) (f : Bool → Bool → Bool)
    (hbit : ∀ a b i, (op a b).testBit i = f (a.testBit i) (b.testBit i))
    (hz : f false false = false) (a b : Int) (w : Nat) (hw : 0 < w)
    (ha : a.natAbs < 2^(w-1)) (hb : b.natAbs < 2^(w-1)) (i : Nat) :
    bwBit (bwDecode w (op (a % (2 : Int)^w).toNat (b % (2 : Int)^w).toNat)) i =
      f (bwBit a i) (bwBit b i) := by
  have hr := bwOpBound op f hbit hz _ _ w (bwResidueLt a w) (bwResidueLt b w)
  by_cases hi : i < w
  · rw [bwDecodeLow _ _ i hr hi, hbit,
      ← bwResidueBit a w i hi, ← bwResidueBit b w i hi]
  · have hi' : w ≤ i := by omega
    have ht : w-1 < w := by omega
    have hpow := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : w-1 ≤ i)
    rw [bwDecodeHigh _ _ i hw hr hi', hbit,
      ← bwResidueBit a w (w-1) ht, ← bwResidueBit b w (w-1) ht,
      bwHigh a (w-1) ha, bwHigh b (w-1) hb,
      bwHigh a i (Nat.lt_of_lt_of_le ha hpow),
      bwHigh b i (Nat.lt_of_lt_of_le hb hpow)]

theorem bwModelBits (op : Nat → Nat → Nat) (f : Bool → Bool → Bool)
    (hbit : ∀ a b i, (op a b).testBit i = f (a.testBit i) (b.testBit i))
    (hz : f false false = false) (a b : Int) (i : Nat) :
    ArithBitBool (bitwiseInt op a b) i = f (ArithBitBool a i) (ArithBitBool b i) := by
  let w := max a.natAbs.log2 b.natAbs.log2 + 2
  have hw : 0 < w := by dsimp only [w]; omega
  have ha : a.natAbs < 2^(w-1) := by
    have hm := Nat.le_max_left a.natAbs.log2 b.natAbs.log2
    have he : a.natAbs.log2 + 1 ≤ w-1 := by dsimp only [w]; omega
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right Nat.zero_lt_two he)
  have hb : b.natAbs < 2^(w-1) := by
    have hm := Nat.le_max_right a.natAbs.log2 b.natAbs.log2
    have he : b.natAbs.log2 + 1 ≤ w-1 := by dsimp only [w]; omega
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right Nat.zero_lt_two he)
  exact bwOpBits op f hbit hz a b w hw ha hb i

theorem bwAndBits (a b : Int) (i : Nat) :
    ArithBitBool (bitwiseInt Nat.land a b) i =
      (ArithBitBool a i && ArithBitBool b i) :=
  bwModelBits Nat.land Bool.and (fun _ _ _ => Nat.testBit_and _ _ _) rfl a b i

theorem bwOrBits (a b : Int) (i : Nat) :
    ArithBitBool (bitwiseInt Nat.lor a b) i =
      (ArithBitBool a i || ArithBitBool b i) :=
  bwModelBits Nat.lor Bool.or (fun _ _ _ => Nat.testBit_or _ _ _) rfl a b i

theorem bwXorBits (a b : Int) (i : Nat) :
    ArithBitBool (bitwiseInt Nat.xor a b) i =
      (ArithBitBool a i ^^ ArithBitBool b i) :=
  bwModelBits Nat.xor Bool.xor (fun _ _ _ => Nat.testBit_xor _ _ _) rfl a b i

theorem BignumsGmpBitandExact_proven : JuliaLean.Proofs.base.gmp.Round1.BitAndExact := by
  intro x y _ _
  refine ⟨writeValue (ofInt 0) (bitwiseInt Nat.land x.val y.val), rfl, ?_⟩
  intro i
  change ArithBitBool (bitwiseInt Nat.land x.val y.val) i = true ↔
    ArithBitBool x.val i = true ∧ ArithBitBool y.val i = true
  rw [bwAndBits, Bool.and_eq_true]

theorem BignumsGmpBitorExact_proven : JuliaLean.Proofs.base.gmp.Round1.BitOrExact := by
  intro x y _ _
  refine ⟨writeValue (ofInt 0) (bitwiseInt Nat.lor x.val y.val), rfl, ?_⟩
  intro i
  change ArithBitBool (bitwiseInt Nat.lor x.val y.val) i = true ↔
    ArithBitBool x.val i = true ∨ ArithBitBool y.val i = true
  rw [bwOrBits, Bool.or_eq_true]

theorem BignumsGmpBitxorExact_proven : JuliaLean.Proofs.base.gmp.Round1.BitXorExact := by
  intro x y _ _
  refine ⟨writeValue (ofInt 0) (bitwiseInt Nat.xor x.val y.val), rfl, ?_⟩
  intro i
  change ArithBitBool (bitwiseInt Nat.xor x.val y.val) i = true ↔
    (ArithBitBool x.val i = true ∧ ¬ ArithBitBool y.val i = true) ∨
    (¬ ArithBitBool x.val i = true ∧ ArithBitBool y.val i = true)
  rw [bwXorBits]
  cases ArithBitBool x.val i <;> cases ArithBitBool y.val i <;> decide

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: Nary. -/
namespace JuliaLean.ChatGPT.Batch4.Group6

open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem bwNaryWriteVal (out : BigInt) (n : Int) : (writeValue out n).val = n := rfl

theorem BignumsGmpNary3Exact_proven : JuliaLean.Proofs.base.gmp.Round1.Commutative3Exact := by
  intro op a b c hop _ _ _
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, rfl, ?_⟩
    simp only [ArithNary, bwNaryWriteVal, List.foldr_cons, List.foldr_nil, Int.add_zero, Int.add_assoc]
  · refine ⟨_, rfl, ?_⟩
    simp only [ArithNary, bwNaryWriteVal, List.foldr_cons, List.foldr_nil, arith_repeated_product,
      Int.mul_one, Int.mul_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwAndBits, Bool.and_eq_true, List.mem_cons,
      forall_eq_or_imp, List.not_mem_nil, false_implies, implies_true,
      and_true, and_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwOrBits, Bool.or_eq_true, List.mem_cons,
      List.not_mem_nil, or_false, or_and_right, exists_or, exists_eq_left, or_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwXorBits]
    cases ha : ArithBitBool a.val i <;> cases hb : ArithBitBool b.val i <;>
      cases hc : ArithBitBool c.val i <;>
      simp only [List.filter_cons, List.filter_nil, Bool.false_eq_true, ha, hb, hc, ↓reduceIte,
        List.length_cons, List.length_nil] <;> decide

theorem BignumsGmpNary4Exact_proven : JuliaLean.Proofs.base.gmp.Round1.Commutative4Exact := by
  intro op a b c d hop _ _ _ _
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, rfl, ?_⟩
    simp only [ArithNary, bwNaryWriteVal, List.foldr_cons, List.foldr_nil, Int.add_zero, Int.add_assoc]
  · refine ⟨_, rfl, ?_⟩
    simp only [ArithNary, bwNaryWriteVal, List.foldr_cons, List.foldr_nil, arith_repeated_product,
      Int.mul_one, Int.mul_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwAndBits, Bool.and_eq_true, List.mem_cons,
      forall_eq_or_imp, List.not_mem_nil, false_implies, implies_true,
      and_true, and_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwOrBits, Bool.or_eq_true, List.mem_cons,
      List.not_mem_nil, or_false, or_and_right, exists_or, exists_eq_left, or_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwXorBits]
    cases ha : ArithBitBool a.val i <;> cases hb : ArithBitBool b.val i <;>
      cases hc : ArithBitBool c.val i <;> cases hd : ArithBitBool d.val i <;>
      simp only [List.filter_cons, List.filter_nil, Bool.false_eq_true, ha, hb, hc, hd, ↓reduceIte,
        List.length_cons, List.length_nil] <;> decide

theorem BignumsGmpNary5Exact_proven : JuliaLean.Proofs.base.gmp.Round1.Commutative5Exact := by
  intro op a b c d e hop _ _ _ _ _
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, rfl, ?_⟩
    simp only [ArithNary, bwNaryWriteVal, List.foldr_cons, List.foldr_nil, Int.add_zero, Int.add_assoc]
  · refine ⟨_, rfl, ?_⟩
    simp only [ArithNary, bwNaryWriteVal, List.foldr_cons, List.foldr_nil, arith_repeated_product,
      Int.mul_one, Int.mul_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwAndBits, Bool.and_eq_true, List.mem_cons,
      forall_eq_or_imp, List.not_mem_nil, false_implies, implies_true,
      and_true, and_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwOrBits, Bool.or_eq_true, List.mem_cons,
      List.not_mem_nil, or_false, or_and_right, exists_or, exists_eq_left, or_assoc]
  · refine ⟨_, rfl, ?_⟩
    intro i
    simp only [ArithBit, bwNaryWriteVal, bwXorBits]
    cases ha : ArithBitBool a.val i <;> cases hb : ArithBitBool b.val i <;>
      cases hc : ArithBitBool c.val i <;> cases hd : ArithBitBool d.val i <;>
      cases he : ArithBitBool e.val i <;>
      simp only [List.filter_cons, List.filter_nil, Bool.false_eq_true, ha, hb, hc, hd, he, ↓reduceIte,
        List.length_cons, List.length_nil] <;> decide

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: Inverse. -/
namespace JuliaLean.ChatGPT.Batch4.Group6
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem g6egcdNat_spec (a b : Nat) :
    (egcdNat a b).1 = (Nat.gcd a b : Int) ∧
      (a : Int) * (egcdNat a b).2.1 + (b : Int) * (egcdNat a b).2.2 =
        (egcdNat a b).1 := by
  rw [egcdNat]
  split
  · rename_i hb
    subst b
    simp only [Nat.gcd_zero_right, Int.natCast_zero, Int.mul_one,
      Int.zero_mul, Int.add_zero, and_self]
  · rename_i hb
    have ih := g6egcdNat_spec b (a % b)
    cases he : egcdNat b (a % b) with
    | mk g st =>
      cases st with
      | mk s t =>
        simp only [he] at ih
        simp only
        constructor
        · rw [ih.1, Nat.gcd_comm a b, Nat.gcd_rec b a]
          exact congrArg Int.ofNat (Nat.gcd_comm b (a % b))
        · have hdiv : ((a % b : Nat) : Int) + (b : Int) * ((a / b : Nat) : Int) = (a : Int) :=
            congrArg Int.ofNat (Nat.mod_add_div a b)
          calc
            (a : Int) * t + (b : Int) * (s - ((a / b : Nat) : Int) * t) =
                ((a : Int) - (b : Int) * ((a / b : Nat) : Int)) * t + (b : Int) * s := by
                  simp only [Int.mul_sub, Int.sub_mul, Int.mul_assoc]
                  omega
            _ = ((a % b : Nat) : Int) * t + (b : Int) * s := by
                  rw [show (a : Int) - (b : Int) * ((a / b : Nat) : Int) =
                    ((a % b : Nat) : Int) by omega]
            _ = g := by omega
termination_by b
decreasing_by apply Nat.mod_lt; omega

theorem g6sgn_mul (a : Int) : a * sgn a = (a.natAbs : Int) := by
  have h := Int.natAbs_eq a
  unfold sgn
  split
  · simp only [Int.mul_neg, Int.mul_one]
    omega
  · split
    · simp only [Int.mul_one]
      omega
    · simp only [Int.mul_zero]
      omega

theorem g6gcdext_gcd (a b : Int) :
    (gmpGcdext a b).1 = (Nat.gcd a.natAbs b.natAbs : Int) := by
  have project_ite (p : Prop) [Decidable p] (u v : Int × Int × Int) :
      (if p then u else v).1 = if p then u.1 else v.1 := by
    by_cases hp : p <;> simp only [hp, ↓reduceIte]
  unfold gmpGcdext
  dsimp only
  simp only [project_ite, ite_self, Int.ofNat_eq_natCast]


theorem g6coprime_two_odd (n : Nat) (h : Nat.gcd n 2 = 1) : n % 2 = 1 := by
  have hrec : Nat.gcd n 2 = Nat.gcd (n % 2) 2 := by
    rw [Nat.gcd_comm n 2, Nat.gcd_rec 2 n]
  by_cases hz : n % 2 = 0
  · rw [hrec, hz, Nat.gcd_zero_left] at h
    omega
  · omega

theorem g6inverse_congruence_mod (a b s : Int) (h : b ∣ a * s - 1) :
    b ∣ a * (s % b) - 1 := by
  have hdiff := Int.mul_dvd_mul_left a (Int.dvd_emod_sub_self (x := s) (m := b))
  have hm : b ∣ a * (s % b - s) :=
    Int.dvd_trans (Int.dvd_mul_left a b) hdiff
  have hsum := Int.dvd_add h hm
  have he : a * s - 1 + a * (s % b - s) = a * (s % b) - 1 := by
    rw [Int.mul_sub]
    omega
  rw [he] at hsum
  exact hsum

theorem g6inverse_congruence_sub (a b s : Int) (h : b ∣ a * s - 1) :
    b ∣ a * (s - b) - 1 := by
  have hm : b ∣ a * b := Int.dvd_mul_left a b
  have hd := Int.dvd_sub h hm
  have he : a * s - 1 - a * b = a * (s - b) - 1 := by
    rw [Int.mul_sub]
    omega
  rw [he] at hd
  exact hd

theorem g6gcdext_inverse (a : Int) (b : Nat) (hb : 1 < b)
    (hg : Nat.gcd a.natAbs b = 1) :
    (b : Int) ∣ a * (gmpGcdext a (b : Int)).2.1 - 1 := by
  have hb0 : (b : Int) ≠ 0 := by omega
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero, Nat.gcd_zero_left] at hg
    omega
  have hne : a.natAbs ≠ b := by
    intro h
    rw [h, Nat.gcd_self] at hg
    omega
  have hsgnb : sgn (b : Int) = 1 := by
    unfold sgn
    rw [if_neg (by omega), if_pos (by omega)]
  rw [gmpGcdext]
  simp only [Int.natAbs_natCast, hg, hne, ha0, hb0, ↓reduceIte, Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one]
  split
  · rename_i hb2
    have hbeq : b = 2 := by omega
    subst b
    simp only
    rw [g6sgn_mul]
    have hodd := g6coprime_two_odd a.natAbs hg
    exact ⟨((a.natAbs / 2 : Nat) : Int), by omega⟩
  · split
    · rename_i ha2
      simp only [hsgnb, Int.mul_one]
      have haabs : a.natAbs = 2 := by omega
      have hodd : b % 2 = 1 := g6coprime_two_odd b (by
        rw [Nat.gcd_comm b 2, ← haabs]
        exact hg)
      have hab : a = 2 ∨ a = -2 := by
        have h := Int.natAbs_eq a
        omega
      have hdiv : a ∣ 1 - (b : Int) := by
        rcases hab with rfl | rfl
        · exact ⟨-((b / 2 : Nat) : Int), by omega⟩
        · exact ⟨((b / 2 : Nat) : Int), by omega⟩
      have hmul : a * (1 - (b : Int)).tdiv a = 1 - (b : Int) := by
        rw [Int.tdiv_eq_ediv_of_dvd hdiv]
        exact Int.mul_ediv_cancel_of_dvd hdiv
      exact ⟨-1, by rw [hmul, Int.mul_neg, Int.mul_one]; omega⟩
    · have he := g6egcdNat_spec a.natAbs b
      cases hev : egcdNat a.natAbs b with
      | mk g st =>
        cases st with
        | mk s t =>
          simp only [hev] at he
          have hcoeff : (a.natAbs : Int) * s + (b : Int) * t = 1 := by
            rw [he.2, he.1, hg]
            rfl
          have hbase : (b : Int) ∣ a * (s * sgn a) - 1 := by
            refine ⟨-t, ?_⟩
            rw [← Int.mul_assoc, Int.mul_right_comm a s (sgn a), g6sgn_mul,
              Int.mul_neg]
            omega
          simp only [Int.tdiv_one]
          split
          · exact g6inverse_congruence_sub a (b : Int) _
              (g6inverse_congruence_mod a (b : Int) (s * sgn a) hbase)
          · exact g6inverse_congruence_mod a (b : Int) (s * sgn a) hbase

theorem g6inv_ofInt_val (n : Int) (nbits : Nat) : (ofInt n nbits).val = n := rfl
theorem g6inv_write_val (x : BigInt) (n : Int) : (writeValue x n).val = n := rfl

theorem g6invmod_success_value (x m : BigInt) (hu : m.val.natAbs ≠ 1)
    (hm : m.val ≠ 0) (hc : Nat.gcd x.val.natAbs m.val.natAbs = 1) :
    ArithReturns (invmod x m) (fun z =>
      let r := (gmpGcdext x.val (m.val.natAbs : Int)).2.1 % (m.val.natAbs : Int)
      z = if m.val < 0 then r + m.val else r) := by
  have hu' : (m.val.natAbs : Int) ≠ 1 := by omega
  have hm' : (m.val.natAbs : Int) ≠ 0 := by
    have hn := Int.natAbs_pos.mpr hm
    omega
  have hstatus : (JInt.wrap .i32 1).val ≠ 0 := by decide
  have hg := g6gcdext_gcd x.val (m.val.natAbs : Int)
  cases he : gmpGcdext x.val (m.val.natAbs : Int) with
  | mk g st =>
    cases st with
    | mk s t =>
      simp only [he, Int.natAbs_natCast, hc] at hg
      have hg1 : g = 1 := hg
      subst g
      simp only [invmod, g6inv_ofInt_val, hu', hm, hm', ↓reduceIte,
        MPZ.invertBang, he, Int.natAbs_natCast, hstatus,
        pure, Except.pure, bind, Except.bind]
      by_cases hneg : m.val < 0
      · simp only [hneg, ↓reduceIte, MPZ.binaryInplace, MPZ.binaryBang,
          MPZ.binaryValue, pure, Except.pure, bind, Except.bind, g6inv_write_val]
        exact ⟨_, rfl, rfl⟩
      · simp only [hneg, ↓reduceIte]
        exact ⟨_, rfl, rfl⟩

theorem g6invmod_failure (x m : BigInt)
    (hc : m.val = 0 ∨ Nat.gcd x.val.natAbs m.val.natAbs ≠ 1) :
    ArithDomainFailure (invmod x m) := by
  have hu : (m.val.natAbs : Int) ≠ 1 := by
    intro hu
    have hu' : m.val.natAbs = 1 := by omega
    rcases hc with hm | hg
    · rw [hm, Int.natAbs_zero] at hu'
      omega
    · exact hg (by rw [hu', Nat.gcd_one_right])
  by_cases hm : m.val = 0
  · exact ⟨"invmod", by
      simp only [invmod, g6inv_ofInt_val]
      rw [if_neg hu, if_pos hm]
      rfl⟩
  · have hgnot : Nat.gcd x.val.natAbs m.val.natAbs ≠ 1 := hc.resolve_left hm
    have hm' : (m.val.natAbs : Int) ≠ 0 := by
      have hn := Int.natAbs_pos.mpr hm
      omega
    have hstatus : (JInt.wrap .i32 0).val = 0 := by decide
    have hg := g6gcdext_gcd x.val (m.val.natAbs : Int)
    cases he : gmpGcdext x.val (m.val.natAbs : Int) with
    | mk g st =>
      cases st with
      | mk s t =>
        simp only [he, Int.natAbs_natCast] at hg
        have hgne : g ≠ 1 := by omega
        refine ⟨"invmod", ?_⟩
        simp only [invmod, g6inv_ofInt_val, hu, hm, hm', ↓reduceIte,
          MPZ.invertBang, he, hgne, Int.natAbs_natCast, hstatus,
          pure, Except.pure, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem BignumsGmpInverseModulo_proven :
    JuliaLean.Proofs.base.gmp.Round1.ModularInverseExact := by
  intro x m _ _
  split
  · exact g6invmod_failure x m ‹_›
  · rename_i hgood
    have hm : m.val ≠ 0 := by omega
    have hg : Nat.gcd x.val.natAbs m.val.natAbs = 1 := by omega
    by_cases hu : m.val.natAbs = 1
    · have hu' : (m.val.natAbs : Int) = 1 := by omega
      have hout : invmod x m = .ok (ofInt 0) := by
        simp only [invmod, g6inv_ofInt_val, hu', ↓reduceIte, pure, Except.pure]
      refine ⟨ofInt 0, hout, ?_⟩
      have hmval : m.val = 1 ∨ m.val = -1 := by
        have hn := Int.natAbs_eq m.val
        omega
      change ArithDivides m.val (x.val * 0 - 1) ∧ ArithModularRepresentative m.val 0
      rcases hmval with h | h <;> rw [h]
      · exact ⟨⟨-1, by omega⟩, by simp only [ArithModularRepresentative]; decide⟩
      · exact ⟨⟨1, by omega⟩, by simp only [ArithModularRepresentative]; decide⟩
    · have hb : 1 < m.val.natAbs := by
        have hn := Int.natAbs_pos.mpr hm
        omega
      let r := (gmpGcdext x.val (m.val.natAbs : Int)).2.1 % (m.val.natAbs : Int)
      have hb0 : (m.val.natAbs : Int) ≠ 0 := by omega
      have hr0 : 0 ≤ r := Int.emod_nonneg _ hb0
      have hrlt : r < (m.val.natAbs : Int) := Int.emod_lt_of_pos _ (by omega)
      have hdiv : (m.val.natAbs : Int) ∣ x.val * r - 1 :=
        g6inverse_congruence_mod _ _ _ (g6gcdext_inverse x.val m.val.natAbs hb hg)
      have hrne : r ≠ 0 := by
        intro hr
        have hd : (m.val.natAbs : Int) ∣ 1 := by
          rw [hr, Int.mul_zero, Int.zero_sub] at hdiv
          exact Int.dvd_neg.mp hdiv
        have heq := Int.eq_one_of_dvd_one (by omega : (0 : Int) ≤ m.val.natAbs) hd
        omega
      obtain ⟨z, hz, hval⟩ := g6invmod_success_value x m hu hm hg
      refine ⟨z, hz, ?_⟩
      change z.val = if m.val < 0 then r + m.val else r at hval
      have hmdiv : m.val ∣ x.val * r - 1 := Int.natAbs_dvd.mp hdiv
      have hn := Int.natAbs_eq m.val
      by_cases hneg : m.val < 0
      · simp only [hneg, ↓reduceIte] at hval
        rw [hval]
        constructor
        · change m.val ∣ x.val * (r + m.val) - 1
          have hd := Int.dvd_add hmdiv (Int.dvd_mul_left x.val m.val)
          have he : x.val * r - 1 + x.val * m.val = x.val * (r + m.val) - 1 := by
            rw [Int.mul_add]
            omega
          rw [he] at hd
          exact hd
        · unfold ArithModularRepresentative
          rw [if_neg (by omega)]
          omega
      · simp only [hneg, ↓reduceIte] at hval
        rw [hval]
        constructor
        · exact hmdiv
        · unfold ArithModularRepresentative
          rw [if_pos (by omega)]
          omega

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: LimbInterval. -/
namespace JuliaLean.ChatGPT.Batch4.Group6

open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

def cgLimbWord (ds : List Limb) (i : Nat) : Nat :=
  ((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat

theorem cgTopInterval (ds : List Limb) (i : Nat) :
    (2^64)^i * (((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat) ≤
        limbMagnitude (ds.take (i+1)) ∧
      limbMagnitude (ds.take (i+1)) <
        (2^64)^i * ((((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat) + 1) := by
  induction i generalizing ds with
  | zero =>
    cases ds with
    | nil => decide
    | cons a ds =>
      change 1 * a.val.toNat ≤ a.val.toNat + 2^64 * 0 ∧
        a.val.toNat + 2^64 * 0 < 1 * (a.val.toNat + 1)
      omega
  | succ i ih =>
    cases ds with
    | nil =>
      change (2^64)^(i+1) * 0 ≤ 0 ∧ 0 < (2^64)^(i+1) * (0+1)
      simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
      exact ⟨Nat.le_refl _, Nat.pow_pos (by decide)⟩
    | cons a ds =>
      have ha := a.property
      change 0 ≤ a.val ∧ a.val ≤ 18446744073709551615 at ha
      have had : a.val.toNat < 2^64 := by
        change a.val.toNat < 18446744073709551616
        omega
      obtain ⟨hl, hu⟩ := ih ds
      simp only [List.take_succ_cons, limbMagnitude, List.getElem?_cons_succ,
        Nat.pow_succ' (m := 2^64) (n := i), Nat.mul_assoc]
      constructor
      · exact Nat.le_trans (Nat.mul_le_mul_left _ hl) (Nat.le_add_left _ _)
      · calc
          a.val.toNat + 2^64 * limbMagnitude (ds.take (i+1)) <
              2^64 + 2^64 * limbMagnitude (ds.take (i+1)) := Nat.add_lt_add_right had _
          _ = 2^64 * (limbMagnitude (ds.take (i+1)) + 1) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          _ ≤ 2^64 * ((2^64)^i *
              ((((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat) + 1)) :=
              Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hu)

theorem cgPowScale (i t : Nat) : (2^64)^i * 2^t = 2^(64*i+t) := by
  rw [← Nat.pow_mul, ← Nat.pow_add]

def cgDigitEval (base : Nat) : List Nat → Nat
  | [] => 0
  | a :: ds => a + base * cgDigitEval base ds

theorem cgDigitTakeDecomposition (base : Nat) (ds : List Nat) (i : Nat) :
    cgDigitEval base (ds.take (i+1)) = cgDigitEval base (ds.take i) +
      base^i * ((ds[i]?).getD 0) := by
  induction i generalizing ds with
  | zero =>
    cases ds with
    | nil => rfl
    | cons a ds =>
      change a + base * 0 = 0 + base^0 * a
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  | succ i ih =>
    cases ds with
    | nil =>
      change 0 = 0 + base^(i+1) * 0
      simp only [Nat.mul_zero, Nat.add_zero]
    | cons a ds =>
      change a + base * cgDigitEval base (ds.take (i+1)) =
        (a + base * cgDigitEval base (ds.take i)) + base^(i+1) * ((ds[i]?).getD 0)
      rw [ih ds, Nat.pow_succ' (m := base) (n := i)]
      simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem cgDigitEvalMap (ds : List Limb) :
    cgDigitEval (2^64) (ds.map (fun a => a.val.toNat)) = limbMagnitude ds := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    change a.val.toNat + 2^64 * cgDigitEval (2^64) (ds.map (fun a => a.val.toNat)) =
      a.val.toNat + 2^64 * limbMagnitude ds
    rw [ih]

theorem cgTakeTopDecomposition (ds : List Limb) (i : Nat) :
    limbMagnitude (ds.take (i+1)) = limbMagnitude (ds.take i) +
      (2^64)^i * (((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat) := by
  have hget : ((ds.map (fun a => a.val.toNat))[i]?).getD 0 =
      ((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat := by
    rw [List.getElem?_map]
    cases ds[i]? <;> rfl
  have h := cgDigitTakeDecomposition (2^64) (ds.map (fun a => a.val.toNat)) i
  simpa only [← List.map_take, cgDigitEvalMap, hget] using h

theorem cgTakeTopQuotient (ds : List Limb) (i : Nat) :
    limbMagnitude (ds.take (i+1)) / (2^64)^i =
      ((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat := by
  obtain ⟨hl, hu⟩ := cgTopInterval ds i
  apply Nat.div_eq_of_lt_le
  · simpa only [Nat.mul_comm] using hl
  · simpa only [Nat.mul_comm] using hu

theorem cgTakeTopRemainder (ds : List Limb) (i : Nat) :
    limbMagnitude (ds.take (i+1)) % (2^64)^i = limbMagnitude (ds.take i) := by
  have hpre : limbMagnitude (ds.take i) < (2^64)^i := by
    have hu := (cgTopInterval ds i).2
    rw [cgTakeTopDecomposition, Nat.mul_add, Nat.mul_one] at hu
    omega
  rw [cgTakeTopDecomposition, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpre]

theorem cgPowerAtPred (base i : Nat) (hi : 0 < i) :
    base^i = base^(i-1) * base := by
  calc
    base^i = base^((i-1)+1) := congrArg (fun n => base^n) (by omega)
    _ = base^(i-1) * base := Nat.pow_succ _ _

theorem cgJoinTwoBlocks (base scale low high rest : Nat) :
    (rest + scale * low) + (scale * base) * high =
      rest + scale * (low + base * high) := by
  simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

theorem cgTakeTopTwoDecomposition (ds : List Limb) (i : Nat) (hi : 0 < i) :
    limbMagnitude (ds.take (i+1)) = limbMagnitude (ds.take (i-1)) +
      (2^64)^(i-1) * (cgLimbWord ds (i-1) + 2^64 * cgLimbWord ds i) := by
  have he : (i-1)+1 = i := by omega
  have h0 := cgTakeTopDecomposition ds i
  have h1 := cgTakeTopDecomposition ds (i-1)
  rw [he] at h1
  rw [h1, cgPowerAtPred (2^64) i hi] at h0
  exact h0.trans (cgJoinTwoBlocks (2^64) ((2^64)^(i-1))
    (cgLimbWord ds (i-1)) (cgLimbWord ds i) (limbMagnitude (ds.take (i-1))))

theorem cgBlockQuotient (scale rest word d : Nat) (hs : 0 < scale) (hr : rest < scale) :
    (rest + scale * word) / (scale*d) = word / d := by
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left rest word hs,
    Nat.div_eq_of_lt hr, Nat.zero_add]

theorem cgBlockRemainder (scale rest word d : Nat) (hs : 0 < scale) (hr : rest < scale) :
    (rest + scale * word) % (scale*d) = rest + scale * (word % d) := by
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr,
    Nat.add_mul_div_left rest word hs, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem cgPowerSplit (k s : Nat) (hs : s ≤ k) : 2^k = 2^s * 2^(k-s) := by
  rw [← Nat.pow_add]
  congr 1
  omega

theorem cgWordShiftQuotient (top low k s : Nat) (hs : s ≤ k) :
    (low + 2^k * top) / 2^s = top * 2^(k-s) + low / 2^s := by
  rw [cgPowerSplit k s hs, Nat.mul_assoc,
    Nat.add_mul_div_left low (2^(k-s)*top) (Nat.two_pow_pos s)]
  rw [Nat.mul_comm (2^(k-s)) top, Nat.add_comm]

theorem cgWordShiftRemainder (top low k s : Nat) (hs : s ≤ k) :
    (low + 2^k * top) % 2^s = low % 2^s := by
  rw [cgPowerSplit k s hs, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem cgTakeTopShiftQuotient (ds : List Limb) (i s : Nat) (hi : 0 < i) (hs : s ≤ 64) :
    limbMagnitude (ds.take (i+1)) / ((2^64)^(i-1)*2^s) =
      cgLimbWord ds i * 2^(64-s) + cgLimbWord ds (i-1) / 2^s := by
  have hp : 0 < (2^64)^(i-1) := Nat.pow_pos (by decide)
  have hpre : limbMagnitude (ds.take (i-1)) < (2^64)^(i-1) := by
    rw [← cgTakeTopRemainder ds (i-1)]
    exact Nat.mod_lt _ hp
  rw [cgTakeTopTwoDecomposition ds i hi,
    cgBlockQuotient _ _ _ _ hp hpre]
  exact cgWordShiftQuotient (cgLimbWord ds i) (cgLimbWord ds (i-1)) 64 s hs

theorem cgTakeTopShiftRemainder (ds : List Limb) (i s : Nat) (hi : 0 < i) (hs : s ≤ 64) :
    limbMagnitude (ds.take (i+1)) % ((2^64)^(i-1)*2^s) =
      limbMagnitude (ds.take (i-1)) +
        (2^64)^(i-1) * (cgLimbWord ds (i-1) % 2^s) := by
  have hp : 0 < (2^64)^(i-1) := Nat.pow_pos (by decide)
  have hpre : limbMagnitude (ds.take (i-1)) < (2^64)^(i-1) := by
    rw [← cgTakeTopRemainder ds (i-1)]
    exact Nat.mod_lt _ hp
  rw [cgTakeTopTwoDecomposition ds i hi,
    cgBlockRemainder _ _ _ _ hp hpre,
    cgWordShiftRemainder _ _ 64 s hs]

theorem cgMagnitudeBitLength (ds : List Limb) (i : Nat)
    (ht : 0 < ((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat) :
    (limbMagnitude (ds.take (i+1))).log2 + 1 =
      (((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat).log2 + 1 + i*64 := by
  let top := ((ds[i]?).getD (JInt.wrap .u64 0)).val.toNat
  let mag := limbMagnitude (ds.take (i+1))
  have htop : top ≠ 0 := by dsimp only [top]; omega
  obtain ⟨hl, hu⟩ := cgTopInterval ds i
  change (2^64)^i * top ≤ mag at hl
  change mag < (2^64)^i * (top+1) at hu
  have hpow : 0 < (2^64)^i := Nat.pow_pos (by decide)
  have hmag : mag ≠ 0 := by
    have hprod := Nat.mul_pos hpow (show 0 < top by dsimp only [top]; exact ht)
    omega
  have htoplo : 2^top.log2 ≤ top := Nat.log2_self_le htop
  have htophi : top + 1 ≤ 2^(top.log2+1) := by
    have h := Nat.lt_log2_self (n := top)
    omega
  have hlo : 2^(64*i+top.log2) ≤ mag := by
    rw [← cgPowScale]
    exact Nat.le_trans (Nat.mul_le_mul_left _ htoplo) hl
  have hhi : mag < 2^((64*i+top.log2)+1) := by
    rw [Nat.add_assoc, ← cgPowScale]
    exact Nat.lt_of_lt_of_le hu (Nat.mul_le_mul_left _ htophi)
  have heq : mag.log2 = 64*i+top.log2 := (Nat.log2_eq_iff hmag).mpr ⟨hlo, hhi⟩
  change mag.log2 + 1 = top.log2 + 1 + i*64
  omega

theorem cgGMPBitLength (x : BigInt) (hx : GMPInput x) (hn : x.val ≠ 0) :
    x.val.natAbs.log2 + 1 =
      (loadLimb x (x.size.val.natAbs-1)).log2 + 1 + (x.size.val.natAbs-1)*64 := by
  have hs : x.size.val ≠ 0 := fun hz => hn (hx.1.2.2.2.1.mp hz)
  have hk : 0 < x.size.val.natAbs := Int.natAbs_pos.mpr hs
  have he : (x.size.val.natAbs-1)+1 = x.size.val.natAbs := by omega
  have ht := hx.1.2.2.2.2 hs
  have hr := ((x.d[x.size.val.natAbs-1]?).getD (JInt.wrap .u64 0)).property.1
  change 0 ≤ ((x.d[x.size.val.natAbs-1]?).getD (JInt.wrap .u64 0)).val at hr
  have htop : 0 < ((x.d[x.size.val.natAbs-1]?).getD (JInt.wrap .u64 0)).val.toNat := by omega
  have hmag : x.val.natAbs = limbMagnitude (x.d.take x.size.val.natAbs) := by
    rw [hx.1.2.2.1]
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
  have hbits := cgMagnitudeBitLength x.d (x.size.val.natAbs-1) htop
  rw [he, ← hmag] at hbits
  exact hbits

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: FloatOutput. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

namespace JuliaLean.ChatGPT.Batch4.Group6

open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1

/-- The public default routes are specializations of the explicit rounding contract. -/
theorem floatOutput64_of_explicit (h : ExplicitIEEEConversionCorrect) :
    DefaultFloat64ConversionCorrect := by
  intro x hx
  exact h .f64 x .Nearest hx

theorem floatOutput32_of_explicit (h : ExplicitIEEEConversionCorrect) :
    DefaultFloat32ConversionCorrect := by
  intro x hx
  exact h .f32 x .Nearest hx

theorem floatOutput16_of_explicit (h : ExplicitIEEEConversionCorrect) :
    DefaultFloat16ConversionCorrect := by
  intro x hx
  exact h .f16 x .Nearest hx

/-- Valid zero inputs take the source's immediate positive-zero branch. -/
theorem floatOutput_zero_value (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hz : x.val = 0) : toFloat T x r = Fl.zero false := by
  have hs : x.size.val = 0 := hx.1.2.2.2.1.mpr hz
  simp only [toFloat, hs, Int.natAbs_zero, ↓reduceIte]

/-- Every loaded limb is a nonnegative 64-bit word, including the default zero. -/
theorem floatOutput_loadLimb_lt (x : BigInt) (i : Nat) : loadLimb x i < 2^64 := by
  have h := ((x.d[i]?).getD (JInt.wrap .u64 0)).property
  change 0 ≤ ((x.d[i]?).getD (JInt.wrap .u64 0)).val ∧
    ((x.d[i]?).getD (JInt.wrap .u64 0)).val ≤ 18446744073709551615 at h
  unfold loadLimb
  omega

/-- Normalization makes the most significant used limb positive. -/
theorem floatOutput_top_pos (x : BigInt) (hx : GMPInput x) (hn : x.val ≠ 0) :
    0 < loadLimb x (x.size.val.natAbs - 1) := by
  have hs : x.size.val ≠ 0 := fun hz => hn (hx.1.2.2.2.1.mp hz)
  have ht := hx.1.2.2.2.2 hs
  have hr := ((x.d[x.size.val.natAbs - 1]?).getD (JInt.wrap .u64 0)).property.1
  change 0 ≤ ((x.d[x.size.val.natAbs - 1]?).getD (JInt.wrap .u64 0)).val at hr
  unfold loadLimb
  omega

/-- On this 64-bit ABI a nonempty top limb fills part of the only window word. -/
theorem floatOutput_fillWindow_positive (x : BigInt) (i m filled : Nat)
    (hf : 0 < filled) : fillWindow x i m filled = (m, filled, i) := by
  cases i with
  | zero => rfl
  | succ i =>
    unfold fillWindow
    rw [if_neg (by omega)]

theorem floatOutput_fillWindow_valid (x : BigInt) (hx : GMPInput x) (hn : x.val ≠ 0) :
    let top := loadLimb x (x.size.val.natAbs - 1)
    fillWindow x (x.size.val.natAbs - 1) top (if top = 0 then 0 else top.log2+1) =
      (top, top.log2+1, x.size.val.natAbs - 1) := by
  have hp := floatOutput_top_pos x hx hn
  dsimp only
  rw [if_neg (by omega)]
  exact floatOutput_fillWindow_positive _ _ _ _ (Nat.succ_pos _)

theorem floatOutput_top_width (x : BigInt) (hx : GMPInput x) (hn : x.val ≠ 0) :
    1 ≤ (loadLimb x (x.size.val.natAbs - 1)).log2 + 1 ∧
    (loadLimb x (x.size.val.natAbs - 1)).log2 + 1 ≤ 64 := by
  have hp := floatOutput_top_pos x hx hn
  have ht := floatOutput_loadLimb_lt x (x.size.val.natAbs - 1)
  have hl := (Nat.log2_lt (by omega : loadLimb x (x.size.val.natAbs - 1) ≠ 0)).mpr ht
  omega

theorem floatOutput_inf_rep (T : FTy) (negative : Bool) :
    (Fl.ofBits (ieee754_representation_inf T negative).val.toNat : FV T) = Fl.inf negative := by
  cases T <;> cases negative <;> decide

theorem floatOutput_omega_rep (T : FTy) (negative : Bool) :
    (Fl.ofBits (ieee754_representation_omega T negative).val.toNat : FV T) =
      if negative then Fl.neg Fl.floatmax else Fl.floatmax := by
  cases T <;> cases negative <;> decide

/-- The source overflow branch chooses signed infinity or the largest finite value. -/
theorem floatOutput_overflow_branch (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hn : x.val ≠ 0)
    (hb : ((loadLimb x (x.size.val.natAbs - 1)).log2 + 1 +
      (x.size.val.natAbs - 1)*64 : Nat) > (exponent_max T).val+1) :
    toFloat T x r =
      if roundsNearest r || roundsAway r (isnegative x) then Fl.inf (isnegative x)
      else if isnegative x then Fl.neg Fl.floatmax else Fl.floatmax := by
  have hs : x.size.val ≠ 0 := fun hz => hn (hx.1.2.2.2.1.mp hz)
  have hs' : x.size.val.natAbs ≠ 0 := by omega
  have ht : loadLimb x (x.size.val.natAbs - 1) ≠ 0 :=
    Nat.ne_of_gt (floatOutput_top_pos x hx hn)
  simp only [toFloat, hs', ite_false, ht, hb, ite_true]
  by_cases hr : (roundsNearest r || roundsAway r (isnegative x)) = true
  · simp only [hr, ite_true]
    exact floatOutput_inf_rep T (isnegative x)
  · simp only [hr, ite_false]
    exact floatOutput_omega_rep T (isnegative x)

/-- An exact metric coordinate has zero distance, so it is globally nearest. -/
theorem floatOutput_nearest_exact {T : FTy} (n : Int) (z : FV T)
    (hz : (ConvFloatMetric z).1 = n * ((ConvFloatMetric z).2 : Int)) :
    ConvFloatNearest (n, 1) z := by
  intro y _
  unfold ConvRatLe ConvDistance
  rw [hz]
  simp only [Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one, Int.sub_self, Int.natAbs_zero, Int.natCast_zero,
    Int.zero_mul, Nat.one_mul]
  exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

/-- A nearest candidate has the same metric value when an exact candidate exists. -/
theorem floatOutput_nearest_unique_metric {T : FTy} (n : Int) (z : FV T)
    (hzn : z.isnan = false)
    (hzd : 0 < (ConvFloatMetric z).2)
    (hz : (ConvFloatMetric z).1 = n * ((ConvFloatMetric z).2 : Int))
    (y : FV T) (hy : ConvFloatNearest (n, 1) y) :
    ConvRatEq (ConvFloatMetric y) (ConvFloatMetric z) := by
  have h := hy z hzn
  have hd : (0 : Int) < ((ConvFloatMetric z).2 : Int) := by omega
  unfold ConvRatLe ConvDistance at h
  rw [hz] at h
  simp only [Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one, Int.sub_self, Int.natAbs_zero, Int.natCast_zero,
    Int.zero_mul, Nat.one_mul] at h
  have h0 : (((n * ((ConvFloatMetric y).2 : Int) - (ConvFloatMetric y).1).natAbs : Nat) : Int) ≤ 0 :=
    (Int.mul_le_mul_right hd).mp (by simpa only [Int.zero_mul] using h)
  have hnum : (ConvFloatMetric y).1 = n * ((ConvFloatMetric y).2 : Int) := by omega
  unfold ConvRatEq
  rw [hz, hnum, Int.mul_right_comm]

/-- Exact finite results already satisfy the full default nearest/tie contract. -/
theorem floatOutput_nearest_choice_exact {T : FTy} (n : Int) (z : FV T)
    (hzn : z.isnan = false)
    (hs : z.signbit = decide (n < 0))
    (hzd : 0 < (ConvFloatMetric z).2)
    (hz : (ConvFloatMetric z).1 = n * ((ConvFloatMetric z).2 : Int)) :
    ConvFloatChoice .Nearest n z := by
  refine ⟨hzn, hs, floatOutput_nearest_exact n z hz, ?_⟩
  intro y _ hy hne
  exact False.elim (hne (floatOutput_nearest_unique_metric n z hzn hzd hz y hy))

theorem floatOutput_nearest_of_integer {T : FTy} (n : Int) (z : FV T)
    (hz : ConvFloatEqualsInteger z n)
    (hs : z.signbit = decide (n < 0)) : ConvFloatChoice .Nearest n z := by
  obtain ⟨hf, hd, he⟩ := hz
  have hn : z.isnan = false := by
    simp only [Fl.isfinite, bne_iff_ne] at hf
    simp only [Fl.isnan, beq_eq_false_iff_ne.mpr hf, Bool.false_and]
  have hi : z.isinf = false := by
    simp only [Fl.isfinite, bne_iff_ne] at hf
    simp only [Fl.isinf, beq_eq_false_iff_ne.mpr hf, Bool.false_and]
  apply floatOutput_nearest_choice_exact n z hn hs
  · simpa only [ConvFloatMetric, hi, Bool.false_eq_true, ite_false] using hd
  · simpa only [ConvFloatMetric, hi, Bool.false_eq_true, ite_false] using he

theorem floatOutput_zero_data (T : FTy) :
    (Fl.zero false : FV T).isnan = false ∧
    (Fl.zero false : FV T).isinf = false ∧
    (Fl.zero false : FV T).signbit = false ∧
    (Fl.zero false : FV T).toRat.1 = 0 ∧
    0 < (Fl.zero false : FV T).toRat.2 ∧
    (Fl.zero false : FV T).toBits = 0 := by
  cases T <;> decide

theorem floatOutput_zero_metric_num (T : FTy) :
    (ConvFloatMetric (Fl.zero false : FV T)).1 = 0 := by
  obtain ⟨_, hi, _, hn, _, _⟩ := floatOutput_zero_data T
  simp only [ConvFloatMetric, hi, Bool.false_eq_true, ite_false, hn]

theorem floatOutput_zero_metric_den (T : FTy) :
    0 < (ConvFloatMetric (Fl.zero false : FV T)).2 := by
  obtain ⟨_, hi, _, _, hd, _⟩ := floatOutput_zero_data T
  simpa only [ConvFloatMetric, hi, Bool.false_eq_true, ite_false] using hd

theorem floatOutput_zero_nearest {T : FTy} :
    ConvFloatNearest (0, 1) (Fl.zero false : FV T) := by
  apply floatOutput_nearest_exact
  rw [floatOutput_zero_metric_num, Int.zero_mul]

theorem floatOutput_zero_floor {T : FTy} :
    ConvFloatFloor (0, 1) (Fl.zero false : FV T) := by
  obtain ⟨_, hi, _, hn, hd, _⟩ := floatOutput_zero_data T
  constructor
  · simp only [ConvFloatLeExact, hi, Bool.false_eq_true, ite_false, ConvRatLe, hn,
      Int.zero_mul, Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one]
    exact Int.le_refl 0
  · intro y _ hy
    by_cases hyi : y.isinf = true
    · simp only [ConvFloatLeExact, hyi, ite_true] at hy
      simp only [ConvFloatLe, hyi, ite_true]
      exact Or.inl hy
    · have hyi' : y.isinf = false := Bool.eq_false_iff.mpr hyi
      simp only [ConvFloatLeExact, hyi', Bool.false_eq_true, ite_false, ConvRatLe,
        Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one, Int.zero_mul] at hy
      simp only [ConvFloatLe, hyi', hi, Bool.false_eq_true, ite_false, ConvRatLe, hn,
        Int.zero_mul]
      have hden : (0 : Int) < ((Fl.zero false : FV T).toRat.2 : Int) := by omega
      simpa only [Int.zero_mul] using (Int.mul_le_mul_right hden).mpr hy

theorem floatOutput_zero_ceil {T : FTy} :
    ConvFloatCeil (0, 1) (Fl.zero false : FV T) := by
  obtain ⟨_, hi, _, hn, hd, _⟩ := floatOutput_zero_data T
  constructor
  · simp only [ConvExactLeFloat, hi, Bool.false_eq_true, ite_false, ConvRatLe, hn,
      Int.zero_mul, Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one]
    exact Int.le_refl 0
  · intro y _ hy
    by_cases hyi : y.isinf = true
    · simp only [ConvExactLeFloat, hyi, ite_true] at hy
      simpa only [ConvFloatLe, hi, Bool.false_eq_true, ite_false, hyi, ite_true] using hy
    · have hyi' : y.isinf = false := Bool.eq_false_iff.mpr hyi
      simp only [ConvExactLeFloat, hyi', Bool.false_eq_true, ite_false, ConvRatLe,
        Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one, Int.zero_mul] at hy
      simp only [ConvFloatLe, hi, hyi', Bool.false_eq_true, ite_false, ConvRatLe, hn,
        Int.zero_mul]
      exact Int.mul_nonneg hy (Int.natCast_nonneg _)

/-- Every nearest candidate to zero has metric numerator zero. -/
theorem floatOutput_zero_nearest_num {T : FTy} (y : FV T)
    (hy : ConvFloatNearest (0, 1) y) : (ConvFloatMetric y).1 = 0 := by
  have h := hy (Fl.zero false) (floatOutput_zero_data T).1
  have hd := floatOutput_zero_metric_den T
  have hd' : (0 : Int) < ((ConvFloatMetric (Fl.zero false : FV T)).2 : Int) := by omega
  unfold ConvRatLe ConvDistance at h
  rw [floatOutput_zero_metric_num] at h
  simp only [Int.zero_mul, Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one, Int.zero_sub, Int.natAbs_neg,
    Int.natAbs_zero, Int.natCast_zero, Nat.one_mul] at h
  have h0 : (((ConvFloatMetric y).1.natAbs : Nat) : Int) ≤ 0 :=
    (Int.mul_le_mul_right hd').mp (by simpa only [Int.zero_mul] using h)
  omega

theorem floatOutput_zero_nearest_le {T : FTy} (y : FV T)
    (hy : ConvFloatNearest (0, 1) y) : ConvFloatLe y (Fl.zero false) := by
  have hn := floatOutput_zero_nearest_num y hy
  obtain ⟨_, hi, _, hz, _, _⟩ := floatOutput_zero_data T
  by_cases hyi : y.isinf = true
  · have hp := Nat.two_pow_pos (T.fmt.bias + 1)
    unfold ConvFloatMetric at hn
    simp only [hyi, ite_true] at hn
    cases hs : y.signbit <;>
      simp only [hs, Bool.false_eq_true, ite_false, ite_true, Int.ofNat_eq_natCast] at hn <;> omega
  · have hyi' : y.isinf = false := Bool.eq_false_iff.mpr hyi
    have hn' : y.toRat.1 = 0 := by
      simpa only [ConvFloatMetric, hyi', Bool.false_eq_true, ite_false] using hn
    simp only [ConvFloatLe, hyi', hi, Bool.false_eq_true, ite_false, ConvRatLe, hz, hn',
      Int.zero_mul, Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one]
    exact Int.le_refl 0

/-- Zero satisfies the full frozen contract for all seven public rounding modes. -/
theorem floatOutput_zero_choice (T : FTy) (r : RoundingMode) :
    ConvFloatChoice r 0 (Fl.zero false : FV T) := by
  obtain ⟨hn, _, hs, _, _, hb⟩ := floatOutput_zero_data T
  refine ⟨hn, hs, ?_⟩
  cases r with
  | ToZero => exact floatOutput_zero_floor
  | Down => exact floatOutput_zero_floor
  | Up => exact floatOutput_zero_ceil
  | Nearest =>
    refine ⟨floatOutput_zero_nearest, ?_⟩
    intro _ _ _ _
    rw [hb]
  | FromZero => exact floatOutput_zero_ceil
  | NearestTiesAway => exact ⟨floatOutput_zero_nearest, fun y _ hy => hy _ hn⟩
  | NearestTiesUp => exact ⟨floatOutput_zero_nearest,
      fun y _ hy => floatOutput_zero_nearest_le y hy⟩

theorem floatOutput_zero_correct (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hz : x.val = 0) : ConvFloatChoice r x.val (toFloat T x r) := by
  rw [floatOutput_zero_value T x r hx hz, hz]
  exact floatOutput_zero_choice T r

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: FloatWindow. -/
namespace JuliaLean.ChatGPT.Batch4.Group6

/-- Left-shifting a word exposes exactly the low unretained significand bits. -/
theorem floatWindow_rest (m p : Nat) (hp : p ≤ 64) :
    (m * 2^p) % 2^64 = (m % 2^(64-p)) * 2^p := by
  have hw : (2 : Nat)^64 = 2^(64-p) * 2^p := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hw, Nat.mul_mod_mul_right]

/-- The extracted round bit tests the upper half of the discarded window residue. -/
theorem floatWindow_round_bit (m p : Nat) (hp : p ≤ 63) :
    decide (((m * 2^p) % 2^64) / 2^63 ≠ 0) =
      decide (2^(63-p) ≤ m % 2^(64-p)) := by
  rw [floatWindow_rest m p (by omega)]
  have hh : (2 : Nat)^63 = 2^(63-p) * 2^p := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hh, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos p)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  simp only [ne_eq, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  omega

/-- The remaining bits are the residue below the round-bit position. -/
theorem floatWindow_sticky_word (m p : Nat) (hp : p ≤ 63) :
    (((m * 2^p) % 2^64) * 2) % 2^64 = (m % 2^(63-p)) * 2^(p+1) := by
  rw [floatWindow_rest m p (by omega), Nat.mul_assoc, ← Nat.pow_succ]
  rw [floatWindow_rest (m % 2^(64-p)) (p+1) (by omega)]
  rw [show 64-(p+1) = 63-p by omega]
  have hh : (2 : Nat)^(64-p) = 2^(63-p) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  rw [hh, Nat.mod_mul_right_mod]

theorem floatWindow_sticky_bit (m p : Nat) (hp : p ≤ 63) :
    decide ((((m * 2^p) % 2^64) * 2) % 2^64 ≠ 0) =
      decide (m % 2^(63-p) ≠ 0) := by
  rw [floatWindow_sticky_word m p hp]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h hn
    apply h
    rw [hn, Nat.zero_mul]
  · intro h
    exact Nat.mul_ne_zero h (Nat.ne_of_gt (Nat.two_pow_pos (p+1)))

/-- Round-bit and sticky decisions implement the ordinary midpoint comparison. -/
theorem floatWindow_nearest_increment (r half : Nat) (hh : 0 < half)
    (hr : r < 2*half) (sticky tie : Bool) :
    (decide (half ≤ r) && ((sticky || decide (r % half ≠ 0)) || tie)) =
      (decide (half < r) || (decide (r = half) && (sticky || tie))) := by
  by_cases hl : r < half
  · have hge : ¬ half ≤ r := by omega
    have hgt : ¬ half < r := by omega
    have hne : r ≠ half := by omega
    simp only [hge, hgt, hne, decide_false, Bool.false_and, Bool.false_or]
  · have hge : half ≤ r := by omega
    by_cases he : r = half
    · subst r
      simp only [Nat.le_refl, Nat.lt_irrefl, Nat.mod_self, ne_eq, not_true_eq_false,
        decide_false, decide_true, Bool.true_and, Bool.false_or, Bool.or_false]
    · have hgt : half < r := by omega
      have hm : r % half = r-half := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      have hmod : r % half ≠ 0 := by rw [hm]; omega
      have hmodb : decide (r % half ≠ 0) = true := decide_eq_true hmod
      simp only [hge, hgt, he, hmodb, decide_true, decide_false,
        Bool.or_true, Bool.true_or, Bool.true_and, Bool.false_and, Bool.and_true]

/-- The round bit and all lower bits together detect any discarded information. -/
theorem floatWindow_nonzero_bits (r half : Nat) (hh : 0 < half)
    (sticky : Bool) :
    (decide (half ≤ r) || (sticky || decide (r % half ≠ 0))) =
      (sticky || decide (r ≠ 0)) := by
  by_cases hl : r < half
  · have hge : ¬ half ≤ r := by omega
    simp only [hge, decide_false, Bool.false_or, Nat.mod_eq_of_lt hl]
  · have hge : half ≤ r := by omega
    have hr : r ≠ 0 := by omega
    have hrb : decide (r ≠ 0) = true := decide_eq_true hr
    simp only [hge, hrb, decide_true, Bool.true_or, Bool.or_true]

/-- The whole source increment kernel reduces to a residue/midpoint decision. -/
theorem floatWindow_increment (m p : Nat) (hp : p ≤ 63)
    (nearest away lowerSticky tie : Bool) :
    (let rest := (m * 2^p) % 2^64
     let roundBit := decide (rest / 2^63 ≠ 0)
     let sticky := lowerSticky || decide ((rest*2) % 2^64 ≠ 0)
     if nearest then roundBit && (sticky || tie)
     else away && (roundBit || sticky)) =
    (let residue := m % 2^(64-p)
     let half := 2^(63-p)
     if nearest then decide (half < residue) ||
       (decide (residue = half) && (lowerSticky || tie))
     else away && (lowerSticky || decide (residue ≠ 0))) := by
  dsimp only
  rw [floatWindow_round_bit m p hp, floatWindow_sticky_bit m p hp]
  have hh : (2 : Nat)^(64-p) = 2^(63-p) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hmod : m % 2^(64-p) % 2^(63-p) = m % 2^(63-p) := by
    rw [hh, Nat.mod_mul_right_mod]
  rw [← hmod]
  have hr : m % 2^(64-p) < 2*2^(63-p) := by
    have h := Nat.mod_lt m (Nat.two_pow_pos (64-p))
    rw [hh] at h
    omega
  cases nearest with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [floatWindow_nonzero_bits _ _ (Nat.two_pow_pos _) lowerSticky]
  | true =>
    simp only [ite_true]
    exact floatWindow_nearest_increment _ _ (Nat.two_pow_pos _) hr lowerSticky tie

theorem floatWindow_scaled_div (low high scale : Nat) (hs : 0 < scale)
    (hl : low < scale) : (low + scale*high) / scale = high := by
  rw [Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hl, Nat.zero_add]

theorem floatWindow_scaled_mod (low high scale radix : Nat) (hs : 0 < scale)
    (hl : low < scale) :
    (low + scale*high) % (scale*radix) = low + scale*(high % radix) := by
  rw [Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl,
    floatWindow_scaled_div low high scale hs hl]

/-- Joining the leading bits of two valid words never wraps the 64-bit window. -/
theorem floatWindow_join_bound (top next s : Nat) (hs : s ≤ 64)
    (ht : top < 2^s) (hn : next < 2^64) :
    top * 2^(64-s) + next / 2^s < 2^64 := by
  have hw : (2 : Nat)^s * 2^(64-s) = 2^64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hnext : next / 2^s < 2^(64-s) :=
    Nat.div_lt_of_lt_mul (by rw [hw]; exact hn)
  have htop : (top+1) * 2^(64-s) ≤ 2^64 := by
    rw [← hw]
    exact Nat.mul_le_mul_right _ ht
  rw [Nat.add_mul, Nat.one_mul] at htop
  omega

theorem floatWindow_shift_bound (top s : Nat) (hs : s ≤ 64)
    (ht : top < 2^s) : top * 2^(64-s) < 2^64 := by
  have h := floatWindow_join_bound top 0 s hs ht (Nat.two_pow_pos 64)
  simpa only [Nat.zero_div, Nat.add_zero] using h

theorem floatWindow_shift_sticky (word s : Nat) (hs : s ≤ 64) :
    decide ((word * 2^(64-s)) % 2^64 ≠ 0) = decide (word % 2^s ≠ 0) := by
  rw [floatWindow_rest word (64-s) (by omega), show 64-(64-s) = s by omega]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h hz
    apply h
    rw [hz, Nat.zero_mul]
  · intro h
    exact Nat.mul_ne_zero h (Nat.ne_of_gt (Nat.two_pow_pos (64-s)))

theorem floatWindow_sticky_join (low high scale : Nat) (hs : 0 < scale) :
    (decide (high ≠ 0) || decide (low ≠ 0)) = decide (low + scale*high ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h hz
    have he := Nat.add_eq_zero_iff.mp hz
    rcases h with hh | hl
    · exact hh ((Nat.mul_eq_zero.mp he.2).resolve_left (Nat.ne_of_gt hs))
    · exact hl he.1
  · intro h
    by_cases hh : high = 0
    · right
      intro hl
      apply h
      rw [hh, hl, Nat.mul_zero, Nat.add_zero]
    · exact Or.inl hh

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: FloatWindowModel. -/
set_option maxHeartbeats 4000000

namespace JuliaLean.ChatGPT.Batch4.Group6
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1

theorem floatWindow_prefix_nonzero (ds : List Limb) (n : Nat) :
    limbMagnitude (ds.take (n+1)) ≠ 0 ↔
      limbMagnitude (ds.take n) ≠ 0 ∨ ((ds[n]?).getD (JInt.wrap .u64 0)).val.toNat ≠ 0 := by
  rw [cgTakeTopDecomposition]
  constructor
  · intro h
    by_cases hm : limbMagnitude (ds.take n) = 0
    · right
      intro hl
      apply h
      rw [hm, hl, Nat.mul_zero, Nat.add_zero]
    · exact Or.inl hm
  · intro h hz
    have he := Nat.add_eq_zero_iff.mp hz
    rcases h with hm | hl
    · exact hm he.1
    · have hp : (2^64 : Nat)^n ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
      exact hl ((Nat.mul_eq_zero.mp he.2).resolve_left hp)

/-- The sticky scan is exactly nonzeroness of the unused lower limb prefix. -/
theorem floatWindow_scan (x : BigInt) (n : Nat) (initial : Bool) :
    (List.range n).foldl (fun st j => st || decide (loadLimb x j ≠ 0)) initial =
      (initial || decide (limbMagnitude (x.d.take n) ≠ 0)) := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, List.take_zero, limbMagnitude,
      ne_eq, not_true_eq_false, decide_false, Bool.or_false]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih]
    apply Bool.eq_iff_iff.mpr
    have hprefix : limbMagnitude (x.d.take (n+1)) ≠ 0 ↔
        limbMagnitude (x.d.take n) ≠ 0 ∨ loadLimb x n ≠ 0 :=
      floatWindow_prefix_nonzero x.d n
    simp only [Bool.or_eq_true, decide_eq_true_eq, hprefix]
    exact or_assoc

/-- Factor the source limb preprocessing, after its nonzero-input guard. -/
def floatWindow_limbState (x : BigInt) : Nat × Bool :=
  let i := x.size.val.natAbs - 1
  let top := loadLimb x i
  let s := top.log2+1
  let (m,filled,j,sticky) := if i > 0 ∧ s < 64 then
    (((top*2^(64-s) + loadLimb x (i-1) / 2^s) % 2^64), 64, i-1,
      decide ((loadLimb x (i-1)*2^(64-s)) % 2^64 ≠ 0))
    else (top,s,i,false)
  let sticky := (List.range j).foldl (fun st k => st || decide (loadLimb x k ≠ 0)) sticky
  ((m * 2^(64-filled)) % 2^64, sticky)

/-- Normalized preprocessing has two ordinary arithmetic cases and no word wrap. -/
theorem floatWindow_limbState_normal (x : BigInt) (hx : GMPInput x) (hn : x.val ≠ 0) :
    let i := x.size.val.natAbs - 1
    let top := loadLimb x i
    let s := top.log2+1
    floatWindow_limbState x =
      if i > 0 ∧ s < 64 then
        (top*2^(64-s) + loadLimb x (i-1) / 2^s,
          decide (loadLimb x (i-1) % 2^s ≠ 0) ||
            decide (limbMagnitude (x.d.take (i-1)) ≠ 0))
      else (top*2^(64-s), decide (limbMagnitude (x.d.take i) ≠ 0)) := by
  have hs := (floatOutput_top_width x hx hn).2
  have ht : loadLimb x (x.size.val.natAbs-1) <
      2^((loadLimb x (x.size.val.natAbs-1)).log2+1) := Nat.lt_log2_self
  have hj := floatWindow_join_bound _ _ _ hs ht
    (floatOutput_loadLimb_lt x (x.size.val.natAbs-1-1))
  have hshift := floatWindow_shift_bound _ _ hs ht
  dsimp only
  by_cases hpart : x.size.val.natAbs-1 > 0 ∧
      (loadLimb x (x.size.val.natAbs-1)).log2+1 < 64
  · simp only [floatWindow_limbState, hpart, true_and, ite_true, floatWindow_scan,
      Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt hj, floatWindow_shift_sticky _ _ hs]
  · simp only [floatWindow_limbState, hpart, ite_false, floatWindow_scan,
      Bool.false_or, Nat.mod_eq_of_lt hshift]

/-- Factor the source word rounding and encoding after its overflow guard. -/
def floatWindow_roundWord (T : FTy) (negative : Bool) (nbits m : Nat)
    (lowerSticky : Bool) (r : RoundingMode) : FV T :=
  let p := T.fmt.sb+1
  let q := m / 2^(64-p)
  let rest := (m*2^p) % 2^64
  let roundBit := decide (rest / 2^63 ≠ 0)
  let sticky := lowerSticky || decide ((rest*2) % 2^64 ≠ 0)
  let incr := if roundsNearest r then
    let tieUp := if r = .Nearest then decide (q%2 = 1)
      else if r = .NearestTiesAway then true else !negative
    roundBit && (sticky || tieUp)
    else roundsAway r negative && (roundBit || sticky)
  let signif := q % 2^T.fmt.sb
  let u := ieee754_representation T negative
    (JInt.wrap .i64 ((nbits : Int)-1+(exponent_bias T).val))
    (JInt.wrap T.uintTy (signif : Int))
  Fl.ofBits ((u.val.toNat + if incr then 1 else 0) % 2^(T.bytes*8))

theorem floatWindow_model_factorization (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hn : x.val ≠ 0)
    (hb : (((loadLimb x (x.size.val.natAbs-1)).log2+1+
      (x.size.val.natAbs-1)*64 : Nat) : Int) ≤ (exponent_max T).val+1) :
    toFloat T x r =
      floatWindow_roundWord T (isnegative x)
        ((loadLimb x (x.size.val.natAbs-1)).log2+1+(x.size.val.natAbs-1)*64)
        (floatWindow_limbState x).1 (floatWindow_limbState x).2 r := by
  have hs : x.size.val ≠ 0 := fun hz => hn (hx.1.2.2.2.1.mp hz)
  have hs' : x.size.val.natAbs ≠ 0 := by omega
  have ht : loadLimb x (x.size.val.natAbs-1) ≠ 0 :=
    Nat.ne_of_gt (floatOutput_top_pos x hx hn)
  have hw := (floatOutput_top_width x hx hn).2
  have hpow : 64-(64-((loadLimb x (x.size.val.natAbs-1)).log2+1)) =
      (loadLimb x (x.size.val.natAbs-1)).log2+1 := by omega
  have hno : ¬ (((loadLimb x (x.size.val.natAbs-1)).log2+1+
      (x.size.val.natAbs-1)*64 : Nat) : Int) > (exponent_max T).val+1 := by omega
  simp only [toFloat, hs', ht, ite_false, hno,
    floatOutput_fillWindow_positive _ _ _ _ (Nat.succ_pos _)]
  unfold floatWindow_limbState floatWindow_roundWord
  by_cases hpart : x.size.val.natAbs-1 > 0 ∧
      (loadLimb x (x.size.val.natAbs-1)).log2+1 < 64 <;>
    simp only [hpart, ite_true, ite_false, hpow] <;> rfl

/-- The window is exactly the leading 64 bits, with exact lower-bit nonzeroness. -/
theorem floatWindow_canonical (x : BigInt) (hx : GMPInput x) (hn : x.val ≠ 0) :
    floatWindow_limbState x =
      ((x.val.natAbs / 2^(x.val.natAbs.log2+1-64)) * 2^(64-(x.val.natAbs.log2+1)),
        decide (x.val.natAbs % 2^(x.val.natAbs.log2+1-64) ≠ 0)) := by
  let i := x.size.val.natAbs-1
  let top := loadLimb x i
  let s := top.log2+1
  let A := x.val.natAbs
  have hs0 : x.size.val ≠ 0 := fun hz => hn (hx.1.2.2.2.1.mp hz)
  have hicount : i+1 = x.size.val.natAbs := by
    dsimp only [i]
    have hp := Int.natAbs_pos.mpr hs0
    omega
  have hA : A = limbMagnitude (x.d.take (i+1)) := by
    rw [hicount]
    change x.val.natAbs = _
    rw [hx.1.2.2.1]
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
  have hL : A.log2+1 = s+i*64 := cgGMPBitLength x hx hn
  have hs : 1 ≤ s ∧ s ≤ 64 := floatOutput_top_width x hx hn
  have hstate := floatWindow_limbState_normal x hx hn
  change floatWindow_limbState x =
    (if i > 0 ∧ s < 64 then
      (top*2^(64-s) + loadLimb x (i-1) / 2^s,
        decide (loadLimb x (i-1) % 2^s ≠ 0) || decide (limbMagnitude (x.d.take (i-1)) ≠ 0))
     else (top*2^(64-s), decide (limbMagnitude (x.d.take i) ≠ 0))) at hstate
  change floatWindow_limbState x =
    ((A / 2^(A.log2+1-64))*2^(64-(A.log2+1)), decide (A % 2^(A.log2+1-64) ≠ 0))
  by_cases hi : i = 0
  · have htop : top = loadLimb x 0 := by dsimp only [top]; rw [hi]
    have hq := cgTakeTopQuotient x.d 0
    simp only [Nat.zero_add, Nat.pow_zero, Nat.div_one] at hq
    have ha : A = top := by
      rw [hi] at hA
      calc
        A = limbMagnitude (x.d.take 1) := hA
        _ = loadLimb x 0 := hq
        _ = top := htop.symm
    rw [hi] at hstate hL
    simp only [Nat.lt_irrefl, false_and, ite_false, List.take_zero, limbMagnitude,
      ne_eq, not_true_eq_false, decide_false] at hstate
    simp only [Nat.zero_mul, Nat.add_zero] at hL
    rw [hstate, hL, show s-64 = 0 by omega, Nat.pow_zero, Nat.div_one, Nat.mod_one, ha]
    rfl
  · have hi' : 0 < i := by omega
    have hpad : 64-(A.log2+1) = 0 := by omega
    by_cases hs64 : s = 64
    · have hD : 2^(A.log2+1-64) = (2^64)^i := by
        rw [hL, ← Nat.pow_mul]
        congr 1
        omega
      have hq := cgTakeTopQuotient x.d i
      have hr := cgTakeTopRemainder x.d i
      rw [← hA] at hq hr
      change A / (2^64)^i = top at hq
      rw [hs64] at hstate
      simp only [Nat.lt_irrefl, and_false, ite_false, Nat.sub_self, Nat.pow_zero,
        Nat.mul_one] at hstate
      rw [hstate, hD, hq, hr, hpad, Nat.pow_zero, Nat.mul_one]
    · have hslt : s < 64 := by omega
      have hD : 2^(A.log2+1-64) = (2^64)^(i-1)*2^s := by
        rw [hL, cgPowScale]
        congr 1
        omega
      have hq := cgTakeTopShiftQuotient x.d i s hi' hs.2
      have hr := cgTakeTopShiftRemainder x.d i s hi' hs.2
      rw [← hA] at hq hr
      change A / ((2^64)^(i-1)*2^s) = top*2^(64-s) + loadLimb x (i-1)/2^s at hq
      change A % ((2^64)^(i-1)*2^s) = limbMagnitude (x.d.take (i-1)) +
        (2^64)^(i-1)*(loadLimb x (i-1)%2^s) at hr
      rw [hstate, if_pos ⟨hi', hslt⟩, hD, hq, hr, hpad, Nat.pow_zero, Nat.mul_one]
      exact Prod.ext rfl (floatWindow_sticky_join _ _ _ (Nat.pow_pos (by decide)))

/-- The source bit count is the mathematical bit length of the represented integer. -/
theorem floatWindow_model_bitlength (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hn : x.val ≠ 0)
    (hb : ((x.val.natAbs.log2+1 : Nat) : Int) ≤ (exponent_max T).val+1) :
    toFloat T x r = floatWindow_roundWord T (isnegative x) (x.val.natAbs.log2+1)
      (floatWindow_limbState x).1 (floatWindow_limbState x).2 r := by
  have hbits := cgGMPBitLength x hx hn
  have hb' : (((loadLimb x (x.size.val.natAbs-1)).log2+1+
      (x.size.val.natAbs-1)*64 : Nat) : Int) ≤ (exponent_max T).val+1 := by
    rw [← hbits]
    exact hb
  have h := floatWindow_model_factorization T x r hx hn hb'
  rw [← hbits] at h
  exact h

theorem floatWindow_overflow_bitlength (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hn : x.val ≠ 0)
    (hb : ((x.val.natAbs.log2+1 : Nat) : Int) > (exponent_max T).val+1) :
    toFloat T x r =
      if roundsNearest r || roundsAway r (isnegative x) then Fl.inf (isnegative x)
      else if isnegative x then Fl.neg Fl.floatmax else Fl.floatmax := by
  apply floatOutput_overflow_branch T x r hx hn
  rw [← cgGMPBitLength x hx hn]
  exact hb

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: FloatWindowArithmetic. -/
set_option maxHeartbeats 4000000

namespace JuliaLean.ChatGPT.Batch4.Group6

/-- Quotient of the canonical word window at any IEEE precision at most 64. -/
theorem floatWindow_canonical_quotient (A L p : Nat) (hp : p ≤ 64) :
    ((A / 2^(L-64))*2^(64-L)) / 2^(64-p) =
      (A / 2^(L-p))*2^(p-L) := by
  by_cases h64 : 64 ≤ L
  · have hlp : p ≤ L := by omega
    have he : L-p = (L-64)+(64-p) := by omega
    rw [Nat.sub_eq_zero_of_le h64, Nat.sub_eq_zero_of_le hlp,
      Nat.pow_zero, Nat.mul_one, Nat.mul_one, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← he]
  · have hL64 : L ≤ 64 := by omega
    rw [Nat.sub_eq_zero_of_le hL64, Nat.pow_zero, Nat.div_one]
    by_cases hlp : p ≤ L
    · have he : 64-p = (L-p)+(64-L) := by omega
      rw [Nat.sub_eq_zero_of_le hlp, Nat.pow_zero, Nat.mul_one, he, Nat.pow_add]
      exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)
    · have hpl : L ≤ p := by omega
      have he : 64-L = (p-L)+(64-p) := by omega
      rw [Nat.sub_eq_zero_of_le hpl, Nat.pow_zero, Nat.div_one, he, Nat.pow_add,
        ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- Equality to a scaled midpoint detects both the high residue and lower zero bits. -/
theorem floatWindow_scaled_equal (low residue scale half : Nat) (hs : 0 < scale)
    (hl : low < scale) :
    low+scale*residue = scale*half ↔ residue = half ∧ low = 0 := by
  constructor
  · intro h
    have he := congrArg (fun n => n/scale) h
    rw [floatWindow_scaled_div _ _ _ hs hl, Nat.mul_div_cancel_left _ hs] at he
    exact ⟨he, by rw [he] at h; omega⟩
  · rintro ⟨rfl,rfl⟩
    exact Nat.zero_add _

theorem floatWindow_scaled_greater (low residue scale half : Nat) (hs : 0 < scale)
    (hl : low < scale) :
    scale*half < low+scale*residue ↔ half < residue ∨ (residue = half ∧ low ≠ 0) := by
  have hlt : low+scale*residue < scale*half ↔ residue < half := by
    rw [Nat.mul_comm scale half, ← Nat.div_lt_iff_lt_mul hs,
      floatWindow_scaled_div _ _ _ hs hl]
  have heq := floatWindow_scaled_equal low residue scale half hs hl
  omega

/-- Sticky bits refine a word-level midpoint exactly to the integer midpoint. -/
theorem floatWindow_scaled_midpoint (low residue scale half : Nat) (hs : 0 < scale)
    (hl : low < scale) (tie : Bool) :
    (decide (half < residue) ||
      (decide (residue = half) && (decide (low ≠ 0) || tie))) =
    (decide (scale*half < low+scale*residue) ||
      (decide (low+scale*residue = scale*half) && tie)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    floatWindow_scaled_greater low residue scale half hs hl,
    floatWindow_scaled_equal low residue scale half hs hl]
  by_cases hz : low = 0 <;>
    simp only [hz, ne_eq, not_true_eq_false, not_false_eq_true, false_or, true_or,
      and_false, and_true, false_and, true_and, or_false]

/-- Small exact integers have no discarded source bits. -/
theorem floatWindow_canonical_exact_increment (A L p : Nat) (hp : p ≤ 63)
    (hlp : L ≤ p) (nearest away tie : Bool) :
    (let m := (A / 2^(L-64))*2^(64-L)
     let rest := (m*2^p)%2^64
     let rb := decide (rest/2^63 ≠ 0)
     let sticky := decide (A%2^(L-64) ≠ 0) || decide ((rest*2)%2^64 ≠ 0)
     if nearest then rb && (sticky || tie) else away && (rb || sticky)) = false := by
  have hL64 : L ≤ 64 := by omega
  have he : 64-L = (p-L)+(64-p) := by omega
  have hm : ((A / 2^(L-64))*2^(64-L)) % 2^(64-p) = 0 := by
    rw [Nat.sub_eq_zero_of_le hL64, Nat.pow_zero, Nat.div_one, he, Nat.pow_add,
      ← Nat.mul_assoc, Nat.mul_mod_left]
  dsimp only
  rw [floatWindow_increment _ _ hp, hm, Nat.sub_eq_zero_of_le hL64,
    Nat.pow_zero, Nat.mod_one]
  have hh := Nat.two_pow_pos (63-p)
  have hh0 : ¬ 2^(63-p) < 0 := Nat.not_lt_zero _
  have hhne : ¬ (0 : Nat) = 2^(63-p) := by omega
  simp only [ne_eq, not_true_eq_false, decide_false, hh0, hhne,
    Bool.false_or, Bool.false_and, Bool.and_false]
  cases nearest <;> rfl


/-- The complete source increment is the exact integer remainder decision. -/
theorem floatWindow_canonical_increment (A L p : Nat) (hp : p ≤ 63)
    (nearest away tie : Bool) :
    (let m := (A / 2^(L-64))*2^(64-L)
     let rest := (m*2^p)%2^64
     let rb := decide (rest/2^63 ≠ 0)
     let sticky := decide (A%2^(L-64) ≠ 0) || decide ((rest*2)%2^64 ≠ 0)
     if nearest then rb && (sticky || tie) else away && (rb || sticky)) =
    (let d := 2^(L-p)
     let R := A%d
     if nearest then decide (d < 2*R) || (decide (2*R = d) && tie)
     else away && decide (R ≠ 0)) := by
  by_cases hlp : L ≤ p
  · rw [floatWindow_canonical_exact_increment A L p hp hlp]
    simp only [Nat.sub_eq_zero_of_le hlp, Nat.pow_zero, Nat.mod_one, Nat.mul_zero,
      Nat.not_lt_zero, Nat.zero_ne_one, ne_eq, not_true_eq_false, decide_false,
      Bool.false_and, Bool.or_false, Bool.and_false]
    cases nearest <;> rfl
  · dsimp only
    rw [floatWindow_increment _ _ hp]
    by_cases h64 : 64 ≤ L
    · rw [Nat.sub_eq_zero_of_le h64, Nat.pow_zero, Nat.mul_one]
      have hD : 2^(L-p) = 2^(L-64)*2^(64-p) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hD2 : 2^(L-p) = 2*(2^(L-64)*2^(63-p)) := by
        calc
          2^(L-p) = 2^((L-64)+(63-p)+1) := by congr 1; omega
          _ = (2^(L-64)*2^(63-p))*2 := by rw [Nat.pow_succ, Nat.pow_add]
          _ = 2*(2^(L-64)*2^(63-p)) := Nat.mul_comm _ _
      have hR : A%2^(L-p) = A%2^(L-64) +
          2^(L-64)*((A/2^(L-64))%2^(64-p)) := by
        rw [hD, Nat.mod_mul]
      cases nearest with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [hR, ← floatWindow_sticky_join _ _ _ (Nat.two_pow_pos (L-64)), Bool.or_comm]
      | true =>
        simp only [ite_true]
        rw [floatWindow_scaled_midpoint _ _ _ _ (Nat.two_pow_pos (L-64))
          (Nat.mod_lt A (Nat.two_pow_pos (L-64))) tie, hR, hD2]
        simp only [Nat.mul_lt_mul_left (by decide : 0 < 2),
          Nat.mul_left_cancel_iff (by decide : 0 < 2)]
    · have hL64 : L ≤ 64 := by omega
      have hwin : 2^(64-p) = 2^(L-p)*2^(64-L) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hhalf : 2^(63-p) = 2^(L-p-1)*2^(64-L) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hD2 : 2^(L-p) = 2*2^(L-p-1) := by
        rw [← Nat.pow_succ']
        congr 1
        omega
      rw [Nat.sub_eq_zero_of_le hL64, Nat.pow_zero, Nat.div_one, Nat.mod_one,
        hwin, Nat.mul_mod_mul_right, hhalf]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_or,
        Nat.mul_lt_mul_right (Nat.two_pow_pos (64-L)),
        Nat.mul_right_cancel_iff (Nat.two_pow_pos (64-L)),
        Nat.mul_ne_zero_iff, Nat.ne_of_gt (Nat.two_pow_pos (64-L)), and_true]
      rw [hD2]
      simp only [Nat.mul_lt_mul_left (by decide : 0 < 2),
        Nat.mul_left_cancel_iff (by decide : 0 < 2), not_false_eq_true, and_true]

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: FloatWindowBridge. -/
set_option maxHeartbeats 4000000

namespace JuliaLean.ChatGPT.Batch4.Group6
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1

/-- Rounding expressed only in integer quotient, remainder, and tie policy. -/
def floatWindow_roundInteger (T : FTy) (negative : Bool) (L A : Nat)
    (r : RoundingMode) : FV T :=
  let p := T.fmt.sb+1
  let d := 2^(L-p)
  let q := (A/d)*2^(p-L)
  let R := A%d
  let tieUp := if r = .Nearest then decide (q%2 = 1)
    else if r = .NearestTiesAway then true else !negative
  let incr := if roundsNearest r then
    decide (d < 2*R) || (decide (2*R = d) && tieUp)
    else roundsAway r negative && decide (R ≠ 0)
  let signif := q % 2^T.fmt.sb
  let u := ieee754_representation T negative
    (JInt.wrap .i64 ((L : Int)-1+(exponent_bias T).val))
    (JInt.wrap T.uintTy (signif : Int))
  Fl.ofBits ((u.val.toNat + if incr then 1 else 0) % 2^(T.bytes*8))

theorem floatWindow_roundWord_canonical (T : FTy) (negative : Bool)
    (L A : Nat) (r : RoundingMode) :
    floatWindow_roundWord T negative L
      ((A / 2^(L-64))*2^(64-L)) (decide (A%2^(L-64) ≠ 0)) r =
      floatWindow_roundInteger T negative L A r := by
  have hp : T.fmt.sb+1 ≤ 63 := by cases T <;> decide
  have hp64 : T.fmt.sb+1 ≤ 64 := by omega
  unfold floatWindow_roundWord floatWindow_roundInteger
  dsimp only
  rw [floatWindow_canonical_quotient A L (T.fmt.sb+1) hp64]
  rw [floatWindow_canonical_increment A L (T.fmt.sb+1) hp (roundsNearest r)
    (roundsAway r negative)
    (if r = .Nearest then decide ((A/2^(L-(T.fmt.sb+1))*2^((T.fmt.sb+1)-L))%2 = 1)
     else if r = .NearestTiesAway then true else !negative)]

/-- Complete non-overflow source reduction to exact integer quotient/remainder rounding. -/
theorem floatWindow_model_integer (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hn : x.val ≠ 0)
    (hb : ((x.val.natAbs.log2+1 : Nat) : Int) ≤ (exponent_max T).val+1) :
    toFloat T x r = floatWindow_roundInteger T (isnegative x)
      (x.val.natAbs.log2+1) x.val.natAbs r := by
  rw [floatWindow_model_bitlength T x r hx hn hb, floatWindow_canonical x hx hn]
  exact floatWindow_roundWord_canonical T (isnegative x) _ _ r

end JuliaLean.ChatGPT.Batch4.Group6

/- Section: IEEEOrder. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux
open JuliaLean JuliaLean.Promotion.Fl JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group6.FloatConstructAux

variable {f : Fmt}

theorem good_fty (T : FTy) : Good T.fmt := by
  cases T
  · exact good_half
  · exact good_single
  · exact good_double

theorem magKey_lt (f : Fmt) (M : Nat) : magKey f M < 2 ^ f.sb * 2 ^ (M / 2 ^ f.sb) := by
  have hr := Nat.mod_lt M (Nat.two_pow_pos f.sb)
  unfold magKey
  generalize M / 2 ^ f.sb = e
  generalize M % 2 ^ f.sb = r at hr
  generalize 2 ^ f.sb = P at *
  cases e with
  | zero => simpa only [↓reduceIte, Nat.add_zero, Nat.zero_sub, Nat.pow_zero, Nat.mul_one] using hr
  | succ e =>
    have hq := Nat.two_pow_pos e
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.pow_succ]
    have h1 : (r + P) * 2 ^ e < (P + P) * 2 ^ e := (Nat.mul_lt_mul_right hq).2 (by omega)
    have h2 : (P + P) * 2 ^ e = P * (2 ^ e * 2) := by
      rw [← Nat.two_mul, Nat.mul_comm 2 P, Nat.mul_assoc, Nat.mul_comm 2]
    omega

theorem magKey_ge (f : Fmt) (M : Nat) (h : M / 2 ^ f.sb ≠ 0) :
    2 ^ f.sb * 2 ^ (M / 2 ^ f.sb - 1) ≤ magKey f M := by
  unfold magKey
  rw [ite_eq_right_iff.mpr fun h0 => absurd h0 h]
  exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

theorem magKey_strictMono (f : Fmt) {a b : Nat} (h : a < b) : magKey f a < magKey f b := by
  have hab : a / 2 ^ f.sb ≤ b / 2 ^ f.sb := Nat.div_le_div_right (Nat.le_of_lt h)
  rcases Nat.lt_or_eq_of_le hab with hlt | heq
  · have h1 := magKey_lt f a
    have h2 := magKey_ge f b (Nat.pos_iff_ne_zero.1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt))
    have h3 : 2 ^ (a / 2 ^ f.sb) ≤ 2 ^ (b / 2 ^ f.sb - 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_sub_one_of_lt hlt)
    have h4 := Nat.mul_le_mul_left (2 ^ f.sb) h3
    exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h4 h2)
  · have ha := Nat.div_add_mod a (2 ^ f.sb)
    have hb := Nat.div_add_mod b (2 ^ f.sb)
    rw [heq] at ha
    have hr : a % 2 ^ f.sb < b % 2 ^ f.sb := by omega
    unfold magKey
    rw [heq]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 (by omega)

theorem magKey_le_iff (f : Fmt) (a b : Nat) : magKey f a ≤ magKey f b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases hn : a ≤ b
    · exact hn
    · have hlt := magKey_strictMono f (show b < a by omega)
      omega
  · intro h
    rcases Nat.lt_or_eq_of_le h with hlt | heq
    · exact Nat.le_of_lt (magKey_strictMono f hlt)
    · rw [heq]
      exact Nat.le_refl _

theorem inf_key_eq (hf : Good f) (x : Fl f) (hi : x.isinf = true) :
    key x = if x.signbit then -(((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int))
            else ((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int) := by
  have hE := hf.emax_eq
  have he : x.expField = f.emax := by
    unfold isinf at hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hi
    exact hi.1
  have hr : x.frac = 0 := by
    unfold isinf at hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hi
    exact hi.2
  have hmk : magKey f x.magnitude = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
    unfold magKey
    rw [← expField_eq, ← frac_eq, he, hr, Nat.zero_add,
      ite_eq_right_iff.mpr (by omega)]
  unfold key
  rw [hmk]

theorem inf_scale (hf : Good f) :
    ((2 ^ (f.bias + 1) : Nat) : Int) * ((den f) : Int) =
      ((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int) := by
  have he := hf.emax_eq
  have hb := hf.bias_pos
  have hs : 2 ^ (f.bias + 1) * den f = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
    unfold den
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hc := congrArg (fun n : Nat => (n : Int)) hs
  simpa only [Int.natCast_mul] using hc

/-- Every non-NaN metric coordinate has a positive denominator and the same fixed scale. -/
theorem metric_key {T : FTy} (x : FV T) (hx : x.isnan = false) :
    0 < (ConvFloatMetric x).2 ∧
    (ConvFloatMetric x).1 * ((den T.fmt) : Int) =
      key x * ((ConvFloatMetric x).2 : Int) := by
  by_cases hi : x.isinf = true
  · simp only [ConvFloatMetric, hi, ↓reduceIte]
    refine ⟨by decide, ?_⟩
    rw [inf_key_eq (good_fty T) x hi]
    simp only [Int.natCast_one, Int.mul_one, Int.ofNat_eq_natCast]
    have hs := inf_scale (good_fty T)
    cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul] <;> omega
  · have hf : x.isfinite = true := by
      cases h : x.isfinite <;> simp_all [Fl.isfinite, Fl.isnan, Fl.isinf]
    simp only [ConvFloatMetric, hi, ↓reduceIte]
    exact toRat_key (good_fty T) x hf

theorem rational_order_scale (a b A B d e D : Int)
    (hd : 0 < d) (he : 0 < e) (hD : 0 < D)
    (ha : A * d = a * D) (hb : B * e = b * D) :
    A ≤ B ↔ a * e ≤ b * d := by
  rw [← Int.mul_le_mul_right (Int.mul_pos hd he)]
  have ha' : A * (d * e) = (a * e) * D := by
    rw [← Int.mul_assoc, ha, Int.mul_right_comm]
  have hb' : B * (d * e) = (b * d) * D := by
    rw [Int.mul_comm d e, ← Int.mul_assoc, hb, Int.mul_right_comm]
  rw [ha', hb', Int.mul_le_mul_right hD]

def keyDistance {T : FTy} (n : Int) (x : FV T) : Int :=
  (n * ((den T.fmt) : Int) - key x).natAbs

/-- Rational absolute distance from an integer becomes an integer absolute difference. -/
theorem distance_key {T : FTy} (n : Int) (x : FV T) (hx : x.isnan = false) :
    0 < (ConvDistance (n, 1) (ConvFloatMetric x)).2 ∧
    (ConvDistance (n, 1) (ConvFloatMetric x)).1 * ((den T.fmt) : Int) =
      keyDistance n x * ((ConvDistance (n, 1) (ConvFloatMetric x)).2 : Int) := by
  obtain ⟨hd, hs⟩ := metric_key x hx
  refine ⟨?_, ?_⟩
  · simpa only [ConvDistance, Nat.one_mul] using hd
  · unfold keyDistance
    simp only [ConvDistance, Int.natCast_one, Int.mul_one, Nat.one_mul]
    have he : (n * ((ConvFloatMetric x).2 : Int) - (ConvFloatMetric x).1) * ((den T.fmt) : Int) =
        (n * ((den T.fmt) : Int) - key x) * ((ConvFloatMetric x).2 : Int) := by
      rw [Int.sub_mul, hs, Int.mul_right_comm n ((ConvFloatMetric x).2 : Int) ((den T.fmt) : Int),
        Int.sub_mul]
    have ha := congrArg Int.natAbs he
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at ha
    have hc := congrArg (fun k : Nat => (k : Int)) ha
    simpa only [Int.natCast_mul, Int.ofNat_eq_natCast] using hc

theorem distance_le_iff {T : FTy} (n : Int) (x y : FV T)
    (hx : x.isnan = false) (hy : y.isnan = false) :
    ConvRatLe (ConvDistance (n, 1) (ConvFloatMetric x))
      (ConvDistance (n, 1) (ConvFloatMetric y)) ↔ keyDistance n x ≤ keyDistance n y := by
  obtain ⟨hd, hs⟩ := distance_key n x hx
  obtain ⟨he, ht⟩ := distance_key n y hy
  exact (rational_order_scale _ _ _ _ _ _ _
    (Int.ofNat_lt.mpr hd) (Int.ofNat_lt.mpr he) (Int.ofNat_lt.mpr (den_pos _)) hs.symm ht.symm).symm

theorem nearest_iff_key {T : FTy} (n : Int) (z : FV T) (hz : z.isnan = false) :
    ConvFloatNearest (n, 1) z ↔
      ∀ y : FV T, y.isnan = false → keyDistance n z ≤ keyDistance n y := by
  constructor
  · intro h y hy
    exact (distance_le_iff n z y hz hy).mp (h y hy)
  · intro h y hy
    exact (distance_le_iff n z y hz hy).mpr (h y hy)

/-- No floating-point key lies strictly between the keys of adjacent positive encodings. -/
theorem no_key_between (f : Fmt) (M : Nat) (x : Fl f) :
    ¬ ((magKey f M : Int) < key x ∧ key x < (magKey f (M + 1) : Int)) := by
  cases hs : x.signbit
  · simp only [key, hs, Bool.false_eq_true, ↓reduceIte]
    intro h
    have hlo : M < x.magnitude := by
      by_cases hn : x.magnitude ≤ M
      · have hm := (magKey_le_iff f x.magnitude M).mpr hn
        omega
      · omega
    have hhi : x.magnitude < M + 1 := by
      by_cases hn : M + 1 ≤ x.magnitude
      · have hm := (magKey_le_iff f (M + 1) x.magnitude).mpr hn
        omega
      · omega
    omega
  · simp only [key, hs, ↓reduceIte]
    omega

theorem distance_min_of_bracket (N L U Z Y : Int) (hL : L ≤ N) (hU : N ≤ U)
    (hZL : ((N - Z).natAbs : Int) ≤ ((N - L).natAbs : Int))
    (hZU : ((N - Z).natAbs : Int) ≤ ((N - U).natAbs : Int))
    (hY : Y ≤ L ∨ U ≤ Y) : ((N - Z).natAbs : Int) ≤ ((N - Y).natAbs : Int) := by
  rcases hY with h | h <;> omega

/-- Checking the two adjacent encodings suffices for the full nearest-distance contract. -/
theorem nearest_of_adjacent {T : FTy} (n : Int) (z : FV T) (hz : z.isnan = false) (M : Nat)
    (hL : (magKey T.fmt M : Int) ≤ n * ((den T.fmt) : Int))
    (hU : n * ((den T.fmt) : Int) ≤ (magKey T.fmt (M + 1) : Int))
    (hzL : keyDistance n z ≤ ((n * ((den T.fmt) : Int) - (magKey T.fmt M : Int)).natAbs : Int))
    (hzU : keyDistance n z ≤ ((n * ((den T.fmt) : Int) - (magKey T.fmt (M + 1) : Int)).natAbs : Int)) :
    ConvFloatNearest (n, 1) z := by
  apply (nearest_iff_key n z hz).mpr
  intro y _
  have hg := no_key_between T.fmt M y
  have hY : key y ≤ (magKey T.fmt M : Int) ∨ (magKey T.fmt (M + 1) : Int) ≤ key y := by omega
  exact distance_min_of_bracket _ _ _ _ _ hL hU hzL hzU hY


theorem finite_key_lt_inf (hf : Good f) (x : Fl f) (hx : x.isfinite = true) :
    -(((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int)) < key x ∧
    key x < ((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int) := by
  have hM := (bits_split x).2
  have hP := Nat.two_pow_pos f.sb
  have hE := hf.emax_eq
  have hS := hf.emax_succ
  have hfin : x.magnitude / 2 ^ f.sb ≠ f.emax := by
    have := hx
    simp only [isfinite, bne_iff_ne, ne_eq] at this
    rw [expField_eq] at this
    exact this
  have hdiv : x.magnitude / 2 ^ f.sb < 2 ^ f.eb := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hmag_lt : x.magnitude < f.emax * 2 ^ f.sb := by
    have := Nat.div_add_mod x.magnitude (2 ^ f.sb)
    have := Nat.mod_lt x.magnitude hP
    have hle : x.magnitude / 2 ^ f.sb + 1 ≤ f.emax := by omega
    have hmul := Nat.mul_le_mul_left (2 ^ f.sb) hle
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm (2 ^ f.sb) f.emax] at hmul
    omega
  have hmk_lt := magKey_strictMono f hmag_lt
  have hmk_inf : magKey f (f.emax * 2 ^ f.sb) = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
    unfold magKey
    rw [Nat.mul_div_cancel _ hP, Nat.mul_mod_left,
      ite_eq_right_iff.mpr (by omega), Nat.zero_add]
  rw [hmk_inf] at hmk_lt
  unfold key
  generalize 2 ^ f.sb * 2 ^ (f.emax - 1) = K at hmk_lt ⊢
  generalize magKey f x.magnitude = M at hmk_lt ⊢
  cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem finite_of_not_nan_not_inf {T : FTy} (x : FV T)
    (hx : x.isnan = false) (hi : ¬ x.isinf = true) : x.isfinite = true := by
  cases h : x.isfinite <;> simp_all [Fl.isfinite, Fl.isnan, Fl.isinf]

theorem finite_rat_le_iff_key {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) :
    ConvRatLe x.toRat y.toRat ↔ key x ≤ key y := by
  obtain ⟨hd, hs⟩ := toRat_key (good_fty T) x hx
  obtain ⟨he, ht⟩ := toRat_key (good_fty T) y hy
  exact (rational_order_scale _ _ _ _ _ _ _
    (Int.ofNat_lt.mpr hd) (Int.ofNat_lt.mpr he) (Int.ofNat_lt.mpr (den_pos _)) hs.symm ht.symm).symm

/-- The independent extended IEEE order agrees with the fixed keys, including infinities. -/
theorem float_le_iff_key {T : FTy} (x y : FV T)
    (hx : x.isnan = false) (hy : y.isnan = false) :
    ConvFloatLe x y ↔ key x ≤ key y := by
  have hK : (0 : Int) < ((2 ^ T.fmt.sb * 2 ^ (T.fmt.emax - 1) : Nat) : Int) :=
    Int.ofNat_lt.mpr (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  by_cases hi : x.isinf = true
  · by_cases hj : y.isinf = true
    · simp only [ConvFloatLe, hi, hj, ↓reduceIte, true_and]
      rw [inf_key_eq (good_fty T) x hi, inf_key_eq (good_fty T) y hj]
      cases x.signbit <;> cases y.signbit <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, true_or, false_or, or_true, or_false, true_iff, false_iff] <;> omega
    · have hf := finite_of_not_nan_not_inf y hy hj
      have hb := finite_key_lt_inf (good_fty T) y hf
      simp only [ConvFloatLe, hi, hj, ↓reduceIte, false_and, or_false]
      rw [inf_key_eq (good_fty T) x hi]
      cases x.signbit <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, true_or, false_or, or_true, or_false, true_and, false_and, true_iff, false_iff] <;> omega
  · have hf := finite_of_not_nan_not_inf x hx hi
    by_cases hj : y.isinf = true
    · have hb := finite_key_lt_inf (good_fty T) x hf
      simp only [ConvFloatLe, hi, hj, ↓reduceIte]
      rw [inf_key_eq (good_fty T) y hj]
      cases y.signbit <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, true_iff, false_iff] <;> omega
    · have hg := finite_of_not_nan_not_inf y hy hj
      simp only [ConvFloatLe, hi, hj, ↓reduceIte]
      exact finite_rat_le_iff_key x y hf hg

theorem finite_le_exact_iff_key {T : FTy} (x : FV T) (hx : x.isfinite = true) (n : Int) :
    ConvFloatLeExact x (n, 1) ↔ key x ≤ n * ((den T.fmt) : Int) := by
  obtain ⟨hd, hs⟩ := toRat_key (good_fty T) x hx
  have hi := isinf_of_finite hx
  simp only [ConvFloatLeExact, hi, Bool.false_eq_true, ↓reduceIte, ConvRatLe]
  exact (rational_order_scale _ _ _ _ _ _ _ (Int.ofNat_lt.mpr hd) (by decide)
    (Int.ofNat_lt.mpr (den_pos _)) hs.symm (by simp only [Int.natCast_one, Int.mul_one])).symm

theorem finite_exact_le_iff_key {T : FTy} (x : FV T) (hx : x.isfinite = true) (n : Int) :
    ConvExactLeFloat (n, 1) x ↔ n * ((den T.fmt) : Int) ≤ key x := by
  obtain ⟨hd, hs⟩ := toRat_key (good_fty T) x hx
  have hi := isinf_of_finite hx
  simp only [ConvExactLeFloat, hi, Bool.false_eq_true, ↓reduceIte, ConvRatLe]
  exact (rational_order_scale _ _ _ _ _ _ _ (by decide) (Int.ofNat_lt.mpr hd)
    (Int.ofNat_lt.mpr (den_pos _)) (by simp only [Int.natCast_one, Int.mul_one]) hs.symm).symm

/-- A finite lower neighbor is the full directed floor when the integer lies below the next encoding. -/
theorem floor_of_adjacent {T : FTy} (n : Int) (z : FV T) (hz : z.isfinite = true) (M : Nat)
    (hkey : key z = (magKey T.fmt M : Int))
    (hL : key z ≤ n * ((den T.fmt) : Int))
    (hU : n * ((den T.fmt) : Int) < (magKey T.fmt (M + 1) : Int)) :
    ConvFloatFloor (n, 1) z := by
  refine ⟨(finite_le_exact_iff_key z hz n).mpr hL, ?_⟩
  intro y hy hyn
  apply (float_le_iff_key y z hy (isnan_of_finite hz)).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = true := by
      simpa only [ConvFloatLeExact, hi, ↓reduceIte] using hyn
    rw [inf_key_eq (good_fty T) y hi]
    simp only [hs, ↓reduceIte]
    exact Int.le_of_lt (finite_key_lt_inf (good_fty T) z hz).1
  · have hf := finite_of_not_nan_not_inf y hy hi
    have hk := (finite_le_exact_iff_key y hf n).mp hyn
    have hg := no_key_between T.fmt M y
    rw [hkey]
    omega

/-- A finite upper neighbor is the full directed ceiling when the integer lies above the previous encoding. -/
theorem ceil_of_adjacent {T : FTy} (n : Int) (z : FV T) (hz : z.isfinite = true) (M : Nat)
    (hkey : key z = (magKey T.fmt (M + 1) : Int))
    (hL : (magKey T.fmt M : Int) < n * ((den T.fmt) : Int))
    (hU : n * ((den T.fmt) : Int) ≤ key z) :
    ConvFloatCeil (n, 1) z := by
  refine ⟨(finite_exact_le_iff_key z hz n).mpr hU, ?_⟩
  intro y hy hny
  apply (float_le_iff_key z y (isnan_of_finite hz) hy).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = false := by
      simpa only [ConvExactLeFloat, hi, ↓reduceIte] using hny
    rw [inf_key_eq (good_fty T) y hi]
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact Int.le_of_lt (finite_key_lt_inf (good_fty T) z hz).2
  · have hf := finite_of_not_nan_not_inf y hy hi
    have hk := (finite_exact_le_iff_key y hf n).mp hny
    have hg := no_key_between T.fmt M y
    rw [hkey]
    omega


/-- The fixed key of a positive normal encoding is its significand times its power-of-two step. -/
theorem magKey_encode (f : Fmt) (e r : Nat) (he : 0 < e) (hr : r < 2 ^ f.sb) :
    magKey f (e * 2 ^ f.sb + r) = (2 ^ f.sb + r) * 2 ^ (e - 1) := by
  have hp := Nat.two_pow_pos f.sb
  have hd : (e * 2 ^ f.sb + r) / 2 ^ f.sb = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add]
  have hm : (e * 2 ^ f.sb + r) % 2 ^ f.sb = r := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  simp only [magKey, hd, hm, Nat.ne_of_gt he, ↓reduceIte]
  rw [Nat.add_comm r]

/-- The next key has the same step even when the significand carries into a new exponent. -/
theorem magKey_successor (f : Fmt) (e r : Nat) (he : 0 < e) (hr : r < 2 ^ f.sb) :
    magKey f (e * 2 ^ f.sb + r + 1) = (2 ^ f.sb + r + 1) * 2 ^ (e - 1) := by
  have hp := Nat.two_pow_pos f.sb
  by_cases hn : r + 1 < 2 ^ f.sb
  · rw [Nat.add_assoc, magKey_encode f e (r + 1) he hn, Nat.add_assoc]
  · have hc : r + 1 = 2 ^ f.sb := by omega
    have hm : e * 2 ^ f.sb + r + 1 = (e + 1) * 2 ^ f.sb + 0 := by
      rw [Nat.add_assoc, hc, Nat.add_mul, Nat.one_mul, Nat.add_zero]
    rw [hm, magKey_encode f (e + 1) 0 (by omega) hp]
    simp only [Nat.add_zero, Nat.add_sub_cancel]
    have hpow : 2 ^ e = 2 ^ (e - 1) * 2 := by
      calc
        2 ^ e = 2 ^ ((e - 1) + 1) := congrArg (fun k : Nat => 2 ^ k) (by omega)
        _ = 2 ^ (e - 1) * 2 := Nat.pow_succ 2 (e - 1)
    rw [hpow, Nat.mul_comm (2 ^ (e - 1)) 2, ← Nat.mul_assoc]
    congr 1
    omega

/-- For integer binades at least one precision wide, the fixed key step rescales the integer step. -/
theorem integer_step_scale (f : Fmt) (hf : Good f) (L : Nat) (hL : f.sb + 1 ≤ L) :
    2 ^ (L - (f.sb + 1)) * den f = 2 ^ (L - 1 + f.bias - 1) := by
  have hb := hf.bias_pos
  unfold den
  rw [← Nat.pow_add]
  congr 1
  omega


/-- Every non-NaN coordinate lies between the two virtual infinity coordinates. -/
theorem key_abs_bound {T : FTy} (x : FV T) (hx : x.isnan = false) :
    -((2 ^ T.fmt.sb * 2 ^ (T.fmt.emax - 1) : Nat) : Int) ≤ key x ∧
    key x ≤ ((2 ^ T.fmt.sb * 2 ^ (T.fmt.emax - 1) : Nat) : Int) := by
  by_cases hi : x.isinf = true
  · rw [inf_key_eq (good_fty T) x hi]
    cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · have hf := finite_of_not_nan_not_inf x hx hi
    have hb := finite_key_lt_inf (good_fty T) x hf
    omega

/-- The negative encodings have the same no-gap property with their order reversed. -/
theorem no_key_between_negative (f : Fmt) (M : Nat) (x : Fl f) :
    ¬ (-((magKey f (M + 1)) : Int) < key x ∧ key x < -((magKey f M) : Int)) := by
  cases hs : x.signbit
  · simp only [key, hs, Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [key, hs, ↓reduceIte]
    intro h
    have hlo : M < x.magnitude := by
      by_cases hn : x.magnitude ≤ M
      · have hm := (magKey_le_iff f x.magnitude M).mpr hn
        omega
      · omega
    have hhi : x.magnitude < M + 1 := by
      by_cases hn : M + 1 ≤ x.magnitude
      · have hm := (magKey_le_iff f (M + 1) x.magnitude).mpr hn
        omega
      · omega
    omega


/-- A signed magnitude encoding, allowing the virtual infinity endpoint. -/
def encode (T : FTy) (negative : Bool) (M : Nat) : FV T :=
  Fl.ofBits ((if negative then 2 ^ (T.fmt.eb + T.fmt.sb) else 0) + M)

theorem encode_eq_pack (T : FTy) (negative : Bool) (M : Nat) :
    encode T negative M = pack negative (M / 2 ^ T.fmt.sb) (M % 2 ^ T.fmt.sb) := by
  unfold encode pack
  rw [Nat.mul_comm (M / 2 ^ T.fmt.sb) (2 ^ T.fmt.sb), Nat.div_add_mod]

theorem encode_bound (T : FTy) (M : Nat) (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) :
    M < 2 ^ (T.fmt.eb + T.fmt.sb) := by
  have he := (good_fty T).emax_succ
  have hp := Nat.two_pow_pos T.fmt.sb
  have hm : T.fmt.emax * 2 ^ T.fmt.sb < 2 ^ T.fmt.eb * 2 ^ T.fmt.sb :=
    Nat.mul_lt_mul_of_pos_right (by omega) hp
  rw [← Nat.pow_add] at hm
  omega

theorem encode_parts (T : FTy) (negative : Bool) (M : Nat)
    (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) :
    (encode T negative M).signbit = negative ∧ (encode T negative M).magnitude = M := by
  have hb := encode_bound T M hM
  have he : M / 2 ^ T.fmt.sb < 2 ^ T.fmt.eb := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hb
  have hp := pack_parts (f := T.fmt) negative (M / 2 ^ T.fmt.sb) (M % 2 ^ T.fmt.sb)
    he (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [← encode_eq_pack] at hp
  refine ⟨hp.1, ?_⟩
  rw [hp.2.2.2, Nat.mul_comm (M / 2 ^ T.fmt.sb) (2 ^ T.fmt.sb), Nat.div_add_mod]

theorem encode_bits (T : FTy) (negative : Bool) (M : Nat)
    (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) :
    (encode T negative M).toBits = (if negative then 2 ^ (T.fmt.eb + T.fmt.sb) else 0) + M := by
  obtain ⟨hs, hm⟩ := encode_parts T negative M hM
  have hb := (bits_split (encode T negative M)).1
  rw [hs, hm] at hb
  exact hb

theorem encode_key (T : FTy) (negative : Bool) (M : Nat)
    (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) :
    key (encode T negative M) = if negative then -(magKey T.fmt M : Int) else (magKey T.fmt M : Int) := by
  obtain ⟨hs, hm⟩ := encode_parts T negative M hM
  simp only [key, hs, hm]

theorem encode_not_nan (T : FTy) (negative : Bool) (M : Nat)
    (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) : (encode T negative M).isnan = false := by
  have hm := (encode_parts T negative M hM).2
  unfold Fl.isnan
  rw [expField_eq, frac_eq, hm]
  by_cases he : M / 2 ^ T.fmt.sb = T.fmt.emax
  · have hd := Nat.div_add_mod M (2 ^ T.fmt.sb)
    rw [he, Nat.mul_comm (2 ^ T.fmt.sb) T.fmt.emax] at hd
    have hz : M % 2 ^ T.fmt.sb = 0 := by omega
    simp only [he, hz, beq_self_eq_true, bne_self_eq_false, Bool.and_false]
  · simp only [he, beq_eq_false_iff_ne.mpr he, Bool.false_and]

theorem encode_finite (T : FTy) (negative : Bool) (M : Nat)
    (hM : M < T.fmt.emax * 2 ^ T.fmt.sb) : (encode T negative M).isfinite = true := by
  have hm := (encode_parts T negative M (Nat.le_of_lt hM)).2
  have he : M / 2 ^ T.fmt.sb < T.fmt.emax :=
    Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _ ) |>.mpr hM
  unfold Fl.isfinite
  rw [expField_eq, hm]
  exact bne_iff_ne.mpr (by omega)

theorem encode_even_bits (T : FTy) (negative : Bool) (M : Nat)
    (hM : M ≤ T.fmt.emax * 2 ^ T.fmt.sb) : (encode T negative M).toBits % 2 = M % 2 := by
  rw [encode_bits T negative M hM, Nat.add_mod]
  have hs := (good_fty T).sb_pos
  have hp : 2 ^ (T.fmt.eb + T.fmt.sb) % 2 = 0 := by
    have hpow : 2 ^ (T.fmt.eb + T.fmt.sb) = 2 ^ (T.fmt.eb + T.fmt.sb - 1) * 2 := by
      rw [← Nat.pow_succ]
      congr 1
      omega
    rw [hpow, Nat.mul_mod_left]
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte, hp, Nat.zero_mod,
    Nat.zero_add, Nat.mod_mod]

end JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux

/- Section: IEEEPacking. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.IEEEPackingAux
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

theorem okOf_eq {ε α : Type} {r : Except ε α} {h : ∀ e, r ≠ .error e} {a : α}
    (hr : r = .ok a) : int.okOf r h = a := by
  cases hr
  rfl

theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2); omega

theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp only [Nat.reducePow, Int.reducePow, Nat.reduceSub, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp only [Nat.reducePow, Int.reducePow, Nat.reduceSub, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem wrapInt_val {t : IntTy} (x : JInt t) : wrapInt t x.val = x.val :=
  wrapInt_of_inRange t x.val x.property

theorem jint_eq {t : IntTy} {x y : JInt t} (h : x.val = y.val) : x = y := Subtype.ext h

theorem fromJInt_toNat {t : IntTy} (x : JInt t) :
    ((fromJInt x).toNat : Int) = x.val % ((2 ^ t.bits : Nat) : Int) := by
  simp only [fromJInt, BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := two_pow_pos_int t.bits; omega))

theorem fromJInt_toInt {t : IntTy} (x : JInt t) (h : t.signed = true) : (fromJInt x).toInt = x.val := by
  have hx := x.property
  simp only [fromJInt, BitVec.toInt_ofInt]
  cases t <;> simp_all only [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, Int.bmod_def, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Nat.reduceSub, Nat.reducePow, Int.reducePow, false_implies, implies_true] <;> split <;> omega

theorem fromJInt_toNat_unsigned {t : IntTy} (x : JInt t) (h : t.signed = false) :
    ((fromJInt x).toNat : Int) = x.val := by
  have hx := x.property
  rw [fromJInt_toNat]
  cases t <;> simp_all only [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Nat.reduceSub, Nat.reducePow, Int.reducePow, false_implies, implies_true] <;> omega

theorem toJInt_val (t : IntTy) (b : BitVec t.bits) :
    (toJInt t b).val = wrapInt t (if t.signed then b.toInt else (b.toNat : Int)) := rfl

theorem toJInt_ofInt_val (t : IntTy) (z : Int) : (toJInt t (BitVec.ofInt t.bits z)).val = wrapInt t z := by
  rw [toJInt_val]
  apply wrapInt_congr
  split
  · rw [BitVec.toInt_ofInt]
    exact Int.bmod_emod
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := two_pow_pos_int t.bits; omega)), Int.emod_emod]

theorem toJInt_ofNat_val (t : IntTy) (n : Nat) : (toJInt t (BitVec.ofNat t.bits n)).val = wrapInt t n := by
  rw [← BitVec.ofInt_natCast, toJInt_ofInt_val]

theorem toJInt_congr {t : IntTy} (b : BitVec t.bits) (z : Int)
    (h : (b.toNat : Int) = z % ((2 ^ t.bits : Nat) : Int)) : (toJInt t b).val = wrapInt t z := by
  have hb : b = BitVec.ofInt t.bits z := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    omega
  rw [hb, toJInt_ofInt_val]

theorem bitcast_val (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits = T.bits) :
    (int.bitcast T x h).val = wrapInt T x.val := by
  unfold int.bitcast
  apply toJInt_congr
  simp only [jlBitcast, BitVec.toNat_cast]
  rw [fromJInt_toNat, h]

theorem sle_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    int.sle_int x y = decide (x.val ≤ y.val) := by
  simp only [int.sle_int, jlSleInt, fromJInt_toInt x h, fromJInt_toInt y h]

def pattern {t : IntTy} (x : JInt t) : Nat := (x.val % ((2 ^ t.bits : Nat) : Int)).toNat

theorem pattern_cast {t : IntTy} (x : JInt t) : (pattern x : Int) = x.val % ((2 ^ t.bits : Nat) : Int) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := two_pow_pos_int t.bits; omega))

theorem pattern_lt {t : IntTy} (x : JInt t) : pattern x < 2 ^ t.bits := by
  have h := pattern_cast x
  have h2 := Int.emod_lt_of_pos x.val (two_pow_pos_int t.bits)
  generalize 2 ^ t.bits = M at *
  omega

theorem pattern_fromJInt {t : IntTy} (x : JInt t) : pattern x = (fromJInt x).toNat := by
  have h1 := pattern_cast x
  have h2 := fromJInt_toNat x
  omega

theorem pattern_toJInt (t : IntTy) (b : BitVec t.bits) : pattern (toJInt t b) = b.toNat := by
  have hc := pattern_cast (toJInt t b)
  rw [toJInt_val, wrapInt_emod_self] at hc
  have hb := b.isLt
  have hm : (b.toNat : Int) % ((2 ^ t.bits : Nat) : Int) = b.toNat :=
    Int.emod_eq_of_lt (by omega) (by omega)
  split at hc
  · rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_emod, hm] at hc; omega
  · rw [hm] at hc; omega

theorem val_eq_wrap_pattern {t : IntTy} (x : JInt t) : x.val = wrapInt t (pattern x) := by
  rw [← wrapInt_val x]
  apply wrapInt_congr
  rw [pattern_cast, Int.emod_emod]

theorem val_bounds {t : IntTy} (x : JInt t) :
    -((2 ^ t.bits : Nat) : Int) < x.val ∧ x.val < ((2 ^ t.bits : Nat) : Int) := by
  have hx := x.property
  cases t <;> simp_all only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Bool.false_eq_true, ↓reduceIte, Nat.reduceSub, Nat.reducePow, Int.reducePow] <;> omega

theorem pattern_of_nonneg {t : IntTy} (x : JInt t) (h : 0 ≤ x.val) : pattern x = x.val.toNat := by
  have hc := pattern_cast x
  rw [Int.emod_eq_of_lt h (val_bounds x).2] at hc
  omega

theorem val_of_unsigned_pattern {t : IntTy} (h : t.signed = false) (x : JInt t) : (pattern x : Int) = x.val := by
  have hx := x.property
  have h0 : 0 ≤ x.val := by
    have := hx.1
    cases t <;> simp_all only [IntTy.signed, IntTy.min, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, false_implies, implies_true] <;> omega
  rw [pattern_of_nonneg x h0]
  exact Int.toNat_of_nonneg h0

theorem pattern_bor {t : IntTy} (x y : JInt t) : pattern (int.bor x y) = pattern x ||| pattern y := by
  simp only [int.bor, int.or_int, jlOrInt, pattern_toJInt, BitVec.toNat_or, ← pattern_fromJInt]

theorem rem_BitInteger_Type_val (to : IntTy) {fr : IntTy} (x : JInt fr) :
    (int.rem_BitInteger_Type to x).val = wrapInt to x.val := by
  unfold int.rem_BitInteger_Type
  split
  · rename_i h
    have hlt := int.bits_lt_of_sizeofT_lt h
    unfold int.Generated.rem_trunc int.trunc_int
    rw [okOf_eq (a := BitVec.ofInt to.bits ((fromJInt x).toNat : Int))
      (by simp only [jlTruncInt, Nat.not_le.mpr hlt, ↓reduceIte, Pure.pure, Except.pure])]
    rw [toJInt_ofInt_val]
    apply wrapInt_congr
    rw [fromJInt_toNat]
    have hd : ((2 ^ to.bits : Nat) : Int) ∣ ((2 ^ fr.bits : Nat) : Int) :=
      Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (Nat.le_of_lt hlt))
    exact Int.emod_emod_of_dvd _ hd
  · split
    · rename_i h h2
      have hlt := int.bits_lt_of_sizeofT_lt h2
      split
      · rename_i hs
        unfold int.Generated.rem_sext int.sext_int
        rw [okOf_eq (a := BitVec.ofInt to.bits (fromJInt x).toInt)
          (by simp only [jlSextInt, Nat.not_le.mpr hlt, ↓reduceIte, Pure.pure, Except.pure])]
        rw [toJInt_ofInt_val, fromJInt_toInt x (by simpa only using hs)]
      · rfl
    · rename_i h h2
      exact bitcast_val to x (int.bits_eq_of_sizeofT h h2)

theorem remT_val (to : IntTy) {fr : IntTy} (x : JInt fr) : (int.remT to x).val = wrapInt to x.val := by
  unfold int.remT
  split
  · rename_i h; subst h; simp only [int.rem_same, wrapInt_val]
  · exact rem_BitInteger_Type_val to x

theorem pattern_of_cong {t : IntTy} (x : JInt t) (z : Int) (h : x.val = wrapInt t z) :
    pattern x = (z % ((2 ^ t.bits : Nat) : Int)).toNat := by
  unfold pattern
  rw [h, wrapInt_emod_self]

theorem pattern_remT_same_bits (to : IntTy) {fr : IntTy} (x : JInt fr) (hb : to.bits = fr.bits) :
    pattern (int.remT to x) = pattern x := by
  rw [pattern_of_cong _ x.val (remT_val to x), hb]
  rfl

theorem unsigned_val {t : IntTy} (x : JInt t) : (int.unsigned x).val = wrapInt t.toUnsigned x.val := by
  unfold int.unsigned
  split
  · exact bitcast_val _ x _
  · exact remT_val _ x

theorem toUnsigned_bits (t : IntTy) : t.toUnsigned.bits = t.bits := by cases t <;> rfl

theorem pattern_unsigned {t : IntTy} (x : JInt t) : pattern (int.unsigned x) = pattern x := by
  rw [pattern_of_cong _ x.val (unsigned_val x), toUnsigned_bits]; rfl

theorem pattern_shl_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (int.shl_int x y) = pattern x * 2 ^ pattern y % 2 ^ t.bits := by
  simp only [int.shl_int, jlShlInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 h) _)).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]

theorem le_zero_eq (y : JInt .i64) : int.le_BitSigned (int.lit .i64 0) y = decide (0 ≤ y.val) := by
  have h0 : (int.lit IntTy.i64 0).val = 0 := by decide
  rw [int.le_BitSigned, sle_int_eq rfl, h0]

theorem pattern_unsigned_count (y : JInt .i64) (h : 0 ≤ y.val) : pattern (int.unsigned y) = y.val.toNat := by
  rw [pattern_unsigned, pattern_of_nonneg y h]

theorem pattern_shl_Int {t : IntTy} (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (int.shl_Int x c) = pattern x * 2 ^ c.val.toNat % 2 ^ t.bits := by
  simp only [int.shl_Int, int.ifelse, le_zero_eq, decide_eq_true_iff, h, ↓reduceIte,
    int.shl_BitInteger_BitUnsigned, pattern_shl_int, pattern_unsigned_count c h]

theorem nat_or_mul_pow (a b k : Nat) (hr : a < 2 ^ k) :
    a ||| b * 2 ^ k = a + b * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  rcases Nat.lt_or_ge i k with hlt | hge
  · have h1 : (b * 2 ^ k).testBit i = false := by
      have hm : (b * 2 ^ k) % 2 ^ k = 0 := Nat.mul_mod_left b (2 ^ k)
      have htb := Nat.testBit_mod_two_pow (b * 2 ^ k) k i
      rw [hm, decide_eq_true hlt, Bool.true_and, Nat.zero_testBit] at htb
      exact htb.symm
    have h2 : (a + b * 2 ^ k).testBit i = a.testBit i := by
      have hm : (a + b * 2 ^ k) % 2 ^ k = a := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      have htb := Nat.testBit_mod_two_pow (a + b * 2 ^ k) k i
      rw [hm, decide_eq_true hlt, Bool.true_and] at htb
      exact htb.symm
    rw [h1, h2, Bool.or_false]
  · have h1 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hge))
    have hi : i = (i - k) + k := (Nat.sub_add_cancel hge).symm
    rw [h1, Bool.false_or, hi, Nat.testBit_add, Nat.testBit_add,
      Nat.mul_div_cancel _ (Nat.two_pow_pos k),
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hr, Nat.zero_add]



theorem pattern_bnot {t : IntTy} (x : JInt t) :
    pattern (int.bnot x) = 2 ^ t.bits - 1 - pattern x := by
  simp only [int.bnot, int.not_int, jlNotInt, pattern_toJInt, BitVec.toNat_not, ← pattern_fromJInt]

theorem trailing_zero_computation {t : IntTy} (x : JInt t) :
    (int.trailing_zeros x).val = wrapInt .i64 (wrapInt t
      (((List.range t.bits).find? (fun i => pattern x / 2 ^ i % 2 == 1)).getD t.bits : Nat)) := by
  unfold int.trailing_zeros
  rw [remT_val]
  unfold int.cttz_int jlCttzInt
  rw [toJInt_ofNat_val, ← pattern_fromJInt]

theorem significand_bits_value (F : FTy) : (significand_bits F).val = (F.fmt.sb : Int) := by
  unfold significand_bits int.trailing_ones_Integer
  rw [trailing_zero_computation, pattern_bnot]
  have hm : pattern (significand_mask F) = 2 ^ F.fmt.sb - 1 := by
    cases F <;> rfl
  rw [hm]
  cases F <;> decide

theorem sub_val {t : IntTy} (x y : JInt t) :
    (int.sub x y).val = wrapInt t (x.val - y.val) := by
  simp only [int.sub, int.sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add,
    toJInt_ofInt_val, Int.sub_eq_add_neg]

theorem mul_val {t : IntTy} (x y : JInt t) :
    (int.mul x y).val = wrapInt t (x.val * y.val) := by
  simp only [int.mul, int.mul_int, jlMulInt, fromJInt]
  rw [← BitVec.ofInt_mul, toJInt_ofInt_val]

theorem exponent_bits_value (F : FTy) : (exponent_bits F).val = (F.fmt.eb : Int) := by
  unfold exponent_bits
  rw [sub_val, sub_val, mul_val, significand_bits_value]
  cases F <;> rfl

theorem pattern_lshr_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (int.lshr_int x y) = pattern x / 2 ^ pattern y := by
  simp only [int.lshr_int, jlLshrInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (pattern_lt x) (Nat.pow_le_pow_right (by decide) h))).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (pattern_lt x))

theorem pattern_shr_Int_unsigned {t : IntTy} (hu : t.signed = false) (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (int.shr_Int x c) = pattern x / 2 ^ c.val.toNat := by
  simp only [int.shr_Int, int.ifelse, le_zero_eq, decide_eq_true_iff, h, ↓reduceIte,
    int.shrU, hu, Bool.false_eq_true, int.shr_BitUnsigned_BitUnsigned,
    pattern_lshr_int, pattern_unsigned_count c h]


theorem exponent_bias_value (F : FTy) : (exponent_bias F).val = (F.fmt.bias : Int) := by
  have hu : F.uintTy.signed = false := by cases F <;> rfl
  have hs : 0 ≤ (significand_bits F).val := by rw [significand_bits_value]; omega
  have hp := pattern_shr_Int_unsigned hu (exponent_one F) (significand_bits F) hs
  have hm : pattern (exponent_one F) = F.fmt.bias * 2 ^ F.fmt.sb := by
    cases F <;> rfl
  rw [significand_bits_value, Int.toNat_natCast, hm,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)] at hp
  have hv := val_of_unsigned_pattern hu (int.shr_Int (exponent_one F) (significand_bits F))
  rw [hp] at hv
  unfold exponent_bias
  rw [remT_val, ← hv]
  clear hu hs hp hm hv
  apply wrapInt_of_inRange
  cases F <;> decide

theorem exponent_raw_max_value (F : FTy) : (exponent_raw_max F).val = (F.fmt.emax : Int) := by
  have hu : F.uintTy.signed = false := by cases F <;> rfl
  have hs : 0 ≤ (significand_bits F).val := by rw [significand_bits_value]; omega
  have hp := pattern_shr_Int_unsigned hu (exponent_mask F) (significand_bits F) hs
  have hm : pattern (exponent_mask F) = F.fmt.emax * 2 ^ F.fmt.sb := by
    cases F <;> rfl
  rw [significand_bits_value, Int.toNat_natCast, hm,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)] at hp
  have hv := val_of_unsigned_pattern hu (int.shr_Int (exponent_mask F) (significand_bits F))
  rw [hp] at hv
  unfold exponent_raw_max
  rw [remT_val, ← hv]
  clear hu hs hp hm hv
  apply wrapInt_of_inRange
  cases F <;> decide

theorem exponent_max_value (F : FTy) : (exponent_max F).val = (F.fmt.bias : Int) := by
  change (int.sub (int.sub (exponent_raw_max F) (exponent_bias F)) (int.lit .i64 1)).val = _
  rw [sub_val, sub_val, exponent_raw_max_value, exponent_bias_value]
  cases F <;> decide


theorem val_of_small_pattern {t : IntTy} (x : JInt t)
    (h : pattern x < 2 ^ (t.bits - 1)) : x.val = (pattern x : Int) := by
  rw [val_eq_wrap_pattern x]
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits, Nat.reduceSub, Nat.reducePow,
    Int.reducePow, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

theorem pattern_remT_nonneg (to : IntTy) {fr : IntTy} (x : JInt fr)
    (h0 : 0 ≤ x.val) (hlt : x.val.toNat < 2 ^ to.bits) :
    pattern (int.remT to x) = x.val.toNat := by
  rw [pattern_of_cong _ x.val (remT_val to x)]
  have hi : x.val < ((2 ^ to.bits : Nat) : Int) := by omega
  rw [Int.emod_eq_of_lt h0 hi]

theorem pattern_bor_mixed_small (to : IntTy) {s t : IntTy} (a : JInt s) (b : JInt t)
    (ha : 0 ≤ a.val) (hb : 0 ≤ b.val)
    (haB : a.val.toNat < 2 ^ (s.promote t).bits)
    (hbB : b.val.toNat < 2 ^ (s.promote t).bits)
    (hsmall : a.val.toNat ||| b.val.toNat < 2 ^ ((s.promote t).bits - 1))
    (hto : a.val.toNat ||| b.val.toNat < 2 ^ to.bits) :
    pattern (int.remT to (int.binop int.bor a b)) = a.val.toNat ||| b.val.toNat := by
  have hbin : int.binop int.bor a b = int.bor (int.remT _ a) (int.remT _ b) := by
    unfold int.binop
    split <;> rfl
  rw [hbin]
  have hp : pattern (int.bor (int.remT (s.promote t) a) (int.remT _ b)) =
      a.val.toNat ||| b.val.toNat := by
    rw [pattern_bor, pattern_remT_nonneg _ a ha haB, pattern_remT_nonneg _ b hb hbB]
  have hv := val_of_small_pattern (int.bor (int.remT (s.promote t) a) (int.remT _ b))
    (by rw [hp]; exact hsmall)
  rw [hp] at hv
  rw [pattern_of_cong _ _ (remT_val _ _), hv,
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hto), Int.toNat_natCast]

theorem binop_bor_same (t : IntTy) (a b : JInt t) :
    int.remT t (int.binop int.bor a b) = int.bor a b := by
  cases t <;> rfl

theorem uintTy_unsigned (F : FTy) : F.uintTy.signed = false := by
  cases F <;> rfl

theorem uintTy_width (F : FTy) : F.uintTy.bits = F.fmt.width := by
  cases F <;> rfl

theorem prefix_count_bound (F : FTy) (s : Bool) :
    (if s then 1 else 0) * 2 ^ F.fmt.eb < 2 ^ (F.uintTy.promote IntTy.i64).bits := by
  cases F <;> cases s <;> decide

theorem exponent_fit_promote (F : FTy) :
    2 ^ F.fmt.eb ≤ 2 ^ (F.uintTy.promote IntTy.i64).bits := by
  cases F <;> decide

theorem prefix_fit_promote_sign (F : FTy) :
    2 ^ (F.fmt.eb + 1) ≤ 2 ^ ((F.uintTy.promote IntTy.i64).bits - 1) := by
  cases F <;> decide

theorem prefix_fit_uint (F : FTy) : 2 ^ (F.fmt.eb + 1) ≤ 2 ^ F.uintTy.bits := by
  cases F <;> decide

theorem prefix_sum_bound (q P : Nat) (s : Bool) (hq : q < P) :
    q + (if s then 1 else 0) * P < P * 2 := by
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero] <;> omega

theorem bool_pattern (F : FTy) (s : Bool) :
    pattern (int.ofBool F.uintTy s) = (if s then 1 else 0) := by
  cases F <;> cases s <;> rfl

theorem bool_shift_bound (F : FTy) (s : Bool) :
    (if s then 1 else 0) * 2 ^ F.fmt.eb < 2 ^ F.uintTy.bits := by
  cases F <;> cases s <;> decide

theorem exponent_prefix_abstract (F : FTy) (s : Bool) (e : JInt .i64)
    (a : JInt F.uintTy) (h0 : 0 ≤ e.val) (he : e.val.toNat < 2 ^ F.fmt.eb)
    (hpa : pattern a = (if s then 1 else 0) * 2 ^ F.fmt.eb) :
    pattern (int.remT F.uintTy (int.binop int.bor a e)) =
      e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb := by
  have huns := uintTy_unsigned F
  have hva := val_of_unsigned_pattern huns a
  have ha : 0 ≤ a.val := by
    rw [← hva]
    exact Int.natCast_nonneg _
  have hat : a.val.toNat = (if s then 1 else 0) * 2 ^ F.fmt.eb := by
    rw [← hva, Int.toNat_natCast, hpa]
  have hor : a.val.toNat ||| e.val.toNat =
      e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb := by
    rw [hat, Nat.or_comm, nat_or_mul_pow _ _ _ he]
  have hsum : e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb < 2 ^ (F.fmt.eb + 1) := by
    rw [Nat.pow_succ]
    exact prefix_sum_bound _ _ s he
  rw [pattern_bor_mixed_small F.uintTy a e ha h0, hor]
  · rw [hat]
    exact prefix_count_bound F s
  · exact Nat.lt_of_lt_of_le he (exponent_fit_promote F)
  · rw [hor]
    exact Nat.lt_of_lt_of_le hsum (prefix_fit_promote_sign F)
  · rw [hor]
    exact Nat.lt_of_lt_of_le hsum (prefix_fit_uint F)

theorem bool_shift_pattern (F : FTy) (s : Bool) :
    pattern (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) =
      (if s then 1 else 0) * 2 ^ F.fmt.eb := by
  have heb : 0 ≤ (exponent_bits F).val := by
    rw [exponent_bits_value]
    exact Int.natCast_nonneg _
  rw [pattern_shl_Int _ _ heb, exponent_bits_value, Int.toNat_natCast]
  rw [bool_pattern]
  exact Nat.mod_eq_of_lt (bool_shift_bound F s)

theorem exponent_prefix (F : FTy) (s : Bool) (e : JInt .i64)
    (h0 : 0 ≤ e.val) (he : e.val.toNat < 2 ^ F.fmt.eb) :
    pattern (int.remT F.uintTy
      (int.binop int.bor (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) e)) =
      e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb :=
  exponent_prefix_abstract F s e _ h0 he (bool_shift_pattern F s)

theorem width_pow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega,
    Nat.pow_succ, Nat.mul_comm]

theorem prefix_shift_bound (F : FTy) (s : Bool) (q : Nat) (hq : q < 2 ^ F.fmt.eb) :
    (q + (if s then 1 else 0) * 2 ^ F.fmt.eb) * 2 ^ F.fmt.sb < 2 ^ F.uintTy.bits := by
  rw [uintTy_width, width_pow, Nat.pow_add]
  have hmul := Nat.mul_lt_mul_of_pos_right hq (Nat.two_pow_pos F.fmt.sb)
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.add_mul] <;> omega

theorem pack_layout (f : Fmt) (s : Bool) (e r : Nat) :
    r + (e + (if s then 1 else 0) * 2 ^ f.eb) * 2 ^ f.sb =
      (if s then 2 ^ (f.eb + f.sb) else 0) + (e * 2 ^ f.sb + r) := by
  rw [Nat.pow_add]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.one_mul,
    Nat.add_zero, Nat.zero_add, Nat.add_mul] <;> omega

/-- The source integer packing operations place the exact sign, exponent, and fraction fields. -/
theorem ieee754_bits (F : FTy) (s : Bool) (e : JInt .i64) (m : JInt F.uintTy)
    (h0 : 0 ≤ e.val) (he : e.val.toNat < 2 ^ F.fmt.eb)
    (hm : m.val.toNat < 2 ^ F.fmt.sb) :
    (ieee754_representation F s e m).val.toNat =
      (if s then 2 ^ (F.fmt.eb + F.fmt.sb) else 0) +
        (e.val.toNat * 2 ^ F.fmt.sb + m.val.toNat) := by
  have huns := uintTy_unsigned F
  have hbw := uintTy_width F
  let a := int.remT F.uintTy
    (int.binop int.bor (int.shl_Int (int.ofBool F.uintTy s) (exponent_bits F)) e)
  have hpa : pattern a = e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb :=
    exponent_prefix F s e h0 he
  have hpm : pattern m = m.val.toNat := by
    have hv := val_of_unsigned_pattern huns m
    rw [← hv, Int.toNat_natCast]
  have hsb : (significand_bits F).val = (F.fmt.sb : Int) ∧
      (significand_bits F).val.toNat = F.fmt.sb := by
    rw [significand_bits_value]
    exact ⟨rfl, Int.toNat_natCast _⟩
  have hbound := prefix_shift_bound F s e.val.toNat he
  have hps : pattern (int.shl_Int a (significand_bits F)) =
      (e.val.toNat + (if s then 1 else 0) * 2 ^ F.fmt.eb) * 2 ^ F.fmt.sb := by
    have hs : 0 ≤ (significand_bits F).val := by
      rw [significand_bits_value]
      exact Int.natCast_nonneg _
    rw [pattern_shl_Int _ _ hs, hpa, hsb.2, Nat.mod_eq_of_lt hbound]
  have hall : pattern (ieee754_representation F s e m) =
      (if s then 2 ^ (F.fmt.eb + F.fmt.sb) else 0) +
        (e.val.toNat * 2 ^ F.fmt.sb + m.val.toNat) := by
    change pattern (int.remT F.uintTy (int.binop int.bor (int.shl_Int a (significand_bits F)) m)) = _
    rw [binop_bor_same, pattern_bor, hps, hpm, Nat.or_comm, nat_or_mul_pow _ _ _ hm]
    exact pack_layout F.fmt s e.val.toNat m.val.toNat
  have hv := val_of_unsigned_pattern huns (ieee754_representation F s e m)
  rw [← hv, Int.toNat_natCast, hall]

theorem wrap_exponent_val (F : FTy) (e : Nat) (he : e < 2 ^ F.fmt.eb) :
    (JInt.wrap .i64 (e : Int)).val = e := by
  change wrapInt .i64 (e : Int) = (e : Int)
  apply wrapInt_of_inRange .i64 (e : Int)
  cases F <;> simp only [FTy.fmt, half, single, double,
    IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Nat.reducePow, Int.reducePow,
    Nat.reduceSub, ↓reduceIte] at he ⊢ <;> omega

theorem wrap_fraction_val (F : FTy) (r : Nat) (hr : r < 2 ^ F.fmt.sb) :
    (JInt.wrap F.uintTy (r : Int)).val = r := by
  change wrapInt F.uintTy (r : Int) = (r : Int)
  apply wrapInt_of_inRange F.uintTy (r : Int)
  cases F <;> simp only [FTy.uintTy, FTy.fmt, half, single, double,
    IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, Nat.reducePow, Int.reducePow,
    Nat.reduceSub, Bool.false_eq_true, ↓reduceIte] at hr ⊢ <;> omega

/-- Packing the bounded fields used by the GMP model produces their ordinary IEEE encoding. -/
theorem ieee754_wrap_bits (F : FTy) (s : Bool) (e r : Nat)
    (he : e < 2 ^ F.fmt.eb) (hr : r < 2 ^ F.fmt.sb) :
    (ieee754_representation F s (JInt.wrap .i64 (e : Int))
      (JInt.wrap F.uintTy (r : Int))).val.toNat =
      (if s then 2 ^ (F.fmt.eb + F.fmt.sb) else 0) + (e * 2 ^ F.fmt.sb + r) := by
  have heV := wrap_exponent_val F e he
  have hrV := wrap_fraction_val F r hr
  rw [ieee754_bits F s _ _ (by rw [heV]; omega)
    (by rw [heV, Int.toNat_natCast]; exact he)
    (by rw [hrV, Int.toNat_natCast]; exact hr), heV, hrV, Int.toNat_natCast, Int.toNat_natCast]

/-- The source increment adds one to the magnitude encoding, including an exponent carry. -/
theorem ieee754_increment_bits (F : FTy) (s : Bool) (e r : Nat) (inc : Bool)
    (he : e < 2 ^ F.fmt.eb) (hr : r < 2 ^ F.fmt.sb) :
    (Fl.ofBits (((ieee754_representation F s (JInt.wrap .i64 (e : Int))
      (JInt.wrap F.uintTy (r : Int))).val.toNat + if inc then 1 else 0) % 2 ^ (F.bytes * 8)) : FV F) =
    Fl.ofBits ((if s then 2 ^ (F.fmt.eb + F.fmt.sb) else 0) +
      (e * 2 ^ F.fmt.sb + r + if inc then 1 else 0)) := by
  rw [ieee754_wrap_bits F s e r he hr]
  have hw : F.bytes * 8 = F.fmt.width := by cases F <;> rfl
  rw [hw, Nat.add_assoc]
  unfold Fl.ofBits
  apply congrArg (Fl.mk (f := F.fmt))
  apply Fin.ext
  exact Nat.mod_mod _ _

end JuliaLean.ChatGPT.Batch4.Group6.IEEEPackingAux

/- Section: FloatChoice. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.FloatChoiceAux
open JuliaLean JuliaLean.Promotion.Fl JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group6.FloatConstructAux
open JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux

/-- Equality of the independent metric is exactly equality of fixed keys. -/
theorem metric_eq_iff_key {T : FTy} (x y : FV T)
    (hx : x.isnan = false) (hy : y.isnan = false) :
    ConvRatEq (ConvFloatMetric x) (ConvFloatMetric y) ↔ key x = key y := by
  obtain ⟨hd, hs⟩ := metric_key x hx
  obtain ⟨he, ht⟩ := metric_key y hy
  have hxy := rational_order_scale _ _ _ _ _ _ _
    (Int.ofNat_lt.mpr hd) (Int.ofNat_lt.mpr he)
    (Int.ofNat_lt.mpr (den_pos _)) hs.symm ht.symm
  have hyx := rational_order_scale _ _ _ _ _ _ _
    (Int.ofNat_lt.mpr he) (Int.ofNat_lt.mpr hd)
    (Int.ofNat_lt.mpr (den_pos _)) ht.symm hs.symm
  unfold ConvRatEq
  constructor
  · intro h
    exact Int.le_antisymm (hxy.mpr (Int.le_of_eq h)) (hyx.mpr (Int.le_of_eq h.symm))
  · intro h
    exact Int.le_antisymm (hxy.mp (Int.le_of_eq h)) (hyx.mp (Int.le_of_eq h.symm))

/-- All nearest values have the same distance, including the overflow metric point. -/
theorem nearest_distance_eq {T : FTy} (n : Int) (x y : FV T)
    (hx : x.isnan = false) (hy : y.isnan = false)
    (hnx : ConvFloatNearest (n, 1) x) (hny : ConvFloatNearest (n, 1) y) :
    keyDistance n x = keyDistance n y := by
  exact Int.le_antisymm ((nearest_iff_key n x hx).mp hnx y hy)
    ((nearest_iff_key n y hy).mp hny x hx)

/-- A bracket with no representable interior point reduces global nearest rounding to two distances. -/
theorem nearest_of_neighbors {T : FTy} (n : Int) (l u z : FV T)
    (hz : z.isnan = false)
    (hL : key l ≤ n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) ≤ key u)
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ key l ∨ key u ≤ key y)
    (hlo : keyDistance n z ≤ keyDistance n l)
    (hhi : keyDistance n z ≤ keyDistance n u) :
    ConvFloatNearest (n, 1) z := by
  apply (nearest_iff_key n z hz).mpr
  intro y hy
  exact distance_min_of_bracket _ _ _ _ _ hL hU hlo hhi (hgap y hy)

/-- Every minimizer in a nonempty adjacent bracket has one of the endpoint keys. -/
theorem nearest_at_endpoint {T : FTy} (n : Int) (l u y : FV T)
    (hl : l.isnan = false) (hu : u.isnan = false) (hy : y.isnan = false)
    (hL : key l ≤ n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) ≤ key u)
    (hgap : key y ≤ key l ∨ key u ≤ key y)
    (hny : ConvFloatNearest (n, 1) y) :
    key y = key l ∨ key y = key u := by
  have hlo := (nearest_iff_key n y hy).mp hny l hl
  have hhi := (nearest_iff_key n y hy).mp hny u hu
  unfold keyDistance at hlo hhi
  rcases hgap with h | h <;> omega

/-- Distinct nearest metric values can occur only at the exact midpoint. -/
theorem distinct_nearest_midpoint {T : FTy} (n : Int) (l u z y : FV T)
    (hl : l.isnan = false) (hu : u.isnan = false)
    (hz : z.isnan = false) (hy : y.isnan = false)
    (hL : key l ≤ n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) ≤ key u)
    (hgap : ∀ v : FV T, v.isnan = false → key v ≤ key l ∨ key u ≤ key v)
    (hnz : ConvFloatNearest (n, 1) z) (hny : ConvFloatNearest (n, 1) y)
    (hne : ¬ ConvRatEq (ConvFloatMetric y) (ConvFloatMetric z)) :
    2 * (n * (den T.fmt : Int)) = key l + key u := by
  have hzk := nearest_at_endpoint n l u z hl hu hz hL hU (hgap z hz) hnz
  have hyk := nearest_at_endpoint n l u y hl hu hy hL hU (hgap y hy) hny
  have hd := nearest_distance_eq n z y hz hy hnz hny
  have hkne : key y ≠ key z := fun h => hne ((metric_eq_iff_key y z hy hz).mpr h)
  unfold keyDistance at hd
  rcases hzk with hz' | hz' <;> rcases hyk with hy' | hy' <;> omega

/-- The full ties-to-even clause follows from parity only in the midpoint case. -/
theorem nearest_choice_of_neighbors {T : FTy} (n : Int) (l u z : FV T)
    (hl : l.isnan = false) (hu : u.isnan = false) (hz : z.isnan = false)
    (hs : z.signbit = decide (n < 0))
    (hL : key l ≤ n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) ≤ key u)
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ key l ∨ key u ≤ key y)
    (hlo : keyDistance n z ≤ keyDistance n l)
    (hhi : keyDistance n z ≤ keyDistance n u)
    (heven : 2 * (n * (den T.fmt : Int)) = key l + key u → z.toBits % 2 = 0) :
    ConvFloatChoice .Nearest n z := by
  have hnz := nearest_of_neighbors n l u z hz hL hU hgap hlo hhi
  refine ⟨hz, hs, hnz, ?_⟩
  intro y hy hny hne
  exact heven (distinct_nearest_midpoint n l u z y hl hu hz hy hL hU hgap hnz hny hne)

/-- The full ties-away clause needs an absolute-magnitude choice only at a midpoint. -/
theorem nearest_away_choice_of_neighbors {T : FTy} (n : Int) (l u z : FV T)
    (hl : l.isnan = false) (hu : u.isnan = false) (hz : z.isnan = false)
    (hs : z.signbit = decide (n < 0))
    (hL : key l ≤ n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) ≤ key u)
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ key l ∨ key u ≤ key y)
    (hlo : keyDistance n z ≤ keyDistance n l)
    (hhi : keyDistance n z ≤ keyDistance n u)
    (haway : 2 * (n * (den T.fmt : Int)) = key l + key u →
      keyDistance 0 l ≤ keyDistance 0 z ∧ keyDistance 0 u ≤ keyDistance 0 z) :
    ConvFloatChoice .NearestTiesAway n z := by
  have hnz := nearest_of_neighbors n l u z hz hL hU hgap hlo hhi
  refine ⟨hz, hs, hnz, ?_⟩
  intro y hy hny
  apply (distance_le_iff 0 y z hy hz).mpr
  by_cases heq : ConvRatEq (ConvFloatMetric y) (ConvFloatMetric z)
  · have hk := (metric_eq_iff_key y z hy hz).mp heq
    unfold keyDistance
    rw [hk]
    exact Int.le_refl _
  · have hm := distinct_nearest_midpoint n l u z y hl hu hz hy hL hU hgap hnz hny heq
    have hbounds := haway hm
    have hyk := nearest_at_endpoint n l u y hl hu hy hL hU (hgap y hy) hny
    rcases hyk with hk | hk
    · simpa only [keyDistance, hk] using hbounds.1
    · simpa only [keyDistance, hk] using hbounds.2

/-- The full upward-tie clause needs the upper endpoint only at a midpoint. -/
theorem nearest_up_choice_of_neighbors {T : FTy} (n : Int) (l u z : FV T)
    (hl : l.isnan = false) (hu : u.isnan = false) (hz : z.isnan = false)
    (hs : z.signbit = decide (n < 0))
    (hL : key l ≤ n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) ≤ key u)
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ key l ∨ key u ≤ key y)
    (hlo : keyDistance n z ≤ keyDistance n l)
    (hhi : keyDistance n z ≤ keyDistance n u)
    (hup : 2 * (n * (den T.fmt : Int)) = key l + key u → key u ≤ key z) :
    ConvFloatChoice .NearestTiesUp n z := by
  have hnz := nearest_of_neighbors n l u z hz hL hU hgap hlo hhi
  refine ⟨hz, hs, hnz, ?_⟩
  intro y hy hny
  apply (float_le_iff_key y z hy hz).mpr
  by_cases heq : ConvRatEq (ConvFloatMetric y) (ConvFloatMetric z)
  · exact Int.le_of_eq ((metric_eq_iff_key y z hy hz).mp heq)
  · have hm := distinct_nearest_midpoint n l u z y hl hu hz hy hL hU hgap hnz hny heq
    have htop := hup hm
    have hyk := nearest_at_endpoint n l u y hl hu hy hL hU (hgap y hy) hny
    rcases hyk with hk | hk <;> omega

end JuliaLean.ChatGPT.Batch4.Group6.FloatChoiceAux

/- Section: FloatChoiceExtras. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.FloatChoiceAux
open JuliaLean JuliaLean.Promotion.Fl JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group6.FloatConstructAux
open JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux

/-- A finite lower endpoint of any signed gap satisfies the full floor contract. -/
theorem floor_of_gap {T : FTy} (n : Int) (z : FV T) (U : Int)
    (hz : z.isfinite = true) (hL : key z ≤ n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) < U)
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ key z ∨ U ≤ key y) :
    ConvFloatFloor (n, 1) z := by
  refine ⟨(finite_le_exact_iff_key z hz n).mpr hL, ?_⟩
  intro y hy hyn
  apply (float_le_iff_key y z hy (isnan_of_finite hz)).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = true := by
      simpa only [ConvFloatLeExact, hi, ↓reduceIte] using hyn
    rw [inf_key_eq (good_fty T) y hi]
    simp only [hs, ↓reduceIte]
    exact Int.le_of_lt (finite_key_lt_inf (good_fty T) z hz).1
  · have hf := finite_of_not_nan_not_inf y hy hi
    have hk := (finite_le_exact_iff_key y hf n).mp hyn
    have hg := hgap y hy
    omega

/-- A finite upper endpoint of any signed gap satisfies the full ceiling contract. -/
theorem ceil_of_gap {T : FTy} (n : Int) (z : FV T) (L : Int)
    (hz : z.isfinite = true) (hL : L < n * (den T.fmt : Int))
    (hU : n * (den T.fmt : Int) ≤ key z)
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ L ∨ key z ≤ key y) :
    ConvFloatCeil (n, 1) z := by
  refine ⟨(finite_exact_le_iff_key z hz n).mpr hU, ?_⟩
  intro y hy hny
  apply (float_le_iff_key z y (isnan_of_finite hz) hy).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = false := by
      simpa only [ConvExactLeFloat, hi, ↓reduceIte] using hny
    rw [inf_key_eq (good_fty T) y hi]
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact Int.le_of_lt (finite_key_lt_inf (good_fty T) z hz).2
  · have hf := finite_of_not_nan_not_inf y hy hi
    have hk := (finite_exact_le_iff_key y hf n).mp hny
    have hg := hgap y hy
    omega

/-- Uniqueness of the nearest metric coordinate settles all three nearest modes. -/
theorem nearest_modes_unique {T : FTy} (n : Int) (z : FV T)
    (hz : z.isnan = false) (hs : z.signbit = decide (n < 0))
    (hnz : ConvFloatNearest (n, 1) z)
    (hunique : ∀ y : FV T, y.isnan = false → ConvFloatNearest (n, 1) y → key y = key z) :
    ConvFloatChoice .Nearest n z ∧ ConvFloatChoice .NearestTiesAway n z ∧
      ConvFloatChoice .NearestTiesUp n z := by
  refine ⟨⟨hz, hs, hnz, ?_⟩, ⟨hz, hs, hnz, ?_⟩, ⟨hz, hs, hnz, ?_⟩⟩
  · intro y hy hny hne
    exact False.elim (hne ((metric_eq_iff_key y z hy hz).mpr (hunique y hy hny)))
  · intro y hy hny
    apply (distance_le_iff 0 y z hy hz).mpr
    unfold keyDistance
    rw [hunique y hy hny]
    exact Int.le_refl _
  · intro y hy hny
    apply (float_le_iff_key y z hy hz).mpr
    exact Int.le_of_eq (hunique y hy hny)

end JuliaLean.ChatGPT.Batch4.Group6.FloatChoiceAux

/- Section: FloatSelection. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.FloatSelectAux
open JuliaLean JuliaLean.Promotion.Fl JuliaLean.base.float JuliaLean.base.gmp
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group6.FloatConstructAux
open JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux
open JuliaLean.ChatGPT.Batch4.Group6.FloatChoiceAux

/-- A finite representation of the exact integer meets every rounding-mode contract. -/
theorem exact_key_choice {T : FTy} (n : Int) (z : FV T)
    (hz : z.isfinite = true) (hs : z.signbit = decide (n < 0))
    (hk : key z = n * (den T.fmt : Int)) (r : RoundingMode) :
    ConvFloatChoice r n z := by
  have hnz := isnan_of_finite hz
  have hfloor : ConvFloatFloor (n, 1) z := by
    refine ⟨(finite_le_exact_iff_key z hz n).mpr (Int.le_of_eq hk), ?_⟩
    intro y hy hyn
    apply (float_le_iff_key y z hy hnz).mpr
    by_cases hi : y.isinf = true
    · have hys : y.signbit = true := by
        simpa only [ConvFloatLeExact, hi, ↓reduceIte] using hyn
      rw [inf_key_eq (good_fty T) y hi, hys]
      simp only [↓reduceIte]
      exact Int.le_of_lt (finite_key_lt_inf (good_fty T) z hz).1
    · have hf := finite_of_not_nan_not_inf y hy hi
      have hle := (finite_le_exact_iff_key y hf n).mp hyn
      omega
  have hceil : ConvFloatCeil (n, 1) z := by
    refine ⟨(finite_exact_le_iff_key z hz n).mpr (Int.le_of_eq hk.symm), ?_⟩
    intro y hy hny
    apply (float_le_iff_key z y hnz hy).mpr
    by_cases hi : y.isinf = true
    · have hys : y.signbit = false := by
        simpa only [ConvExactLeFloat, hi, ↓reduceIte] using hny
      rw [inf_key_eq (good_fty T) y hi, hys]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Int.le_of_lt (finite_key_lt_inf (good_fty T) z hz).2
    · have hf := finite_of_not_nan_not_inf y hy hi
      have hle := (finite_exact_le_iff_key y hf n).mp hny
      omega
  have hnear : ConvFloatNearest (n, 1) z := by
    apply (nearest_iff_key n z hnz).mpr
    intro y _
    unfold keyDistance
    rw [hk]
    omega
  have huniq : ∀ y : FV T, y.isnan = false → ConvFloatNearest (n, 1) y → key y = key z := by
    intro y hy hny
    have hd := (nearest_iff_key n y hy).mp hny z hnz
    unfold keyDistance at hd
    rw [hk] at hd
    omega
  have hall := nearest_modes_unique n z hnz hs hnear huniq
  cases r with
  | ToZero =>
    refine ⟨hnz, hs, ?_⟩
    by_cases hn : n < 0
    · simpa only [hn, ↓reduceIte] using hceil
    · simpa only [hn, ↓reduceIte] using hfloor
  | Down => exact ⟨hnz, hs, hfloor⟩
  | Up => exact ⟨hnz, hs, hceil⟩
  | Nearest => exact hall.1
  | FromZero =>
    refine ⟨hnz, hs, ?_⟩
    by_cases hn : n < 0
    · simpa only [hn, ↓reduceIte] using hfloor
    · simpa only [hn, ↓reduceIte] using hceil
  | NearestTiesAway => exact hall.2.1
  | NearestTiesUp => exact hall.2.2

/-- A gap gives a directed floor even when its selected endpoint is negative infinity. -/
theorem floor_of_gap_extended {T : FTy} (n : Int) (z : FV T) (U : Int)
    (hz : z.isnan = false) (hfirst : ConvFloatLeExact z (n, 1))
    (hU : n * (den T.fmt : Int) < U)
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ key z ∨ U ≤ key y) :
    ConvFloatFloor (n, 1) z := by
  refine ⟨hfirst, ?_⟩
  intro y hy hyn
  apply (float_le_iff_key y z hy hz).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = true := by
      simpa only [ConvFloatLeExact, hi, ↓reduceIte] using hyn
    rw [inf_key_eq (good_fty T) y hi, hs]
    simp only [↓reduceIte]
    exact (key_abs_bound z hz).1
  · have hf := finite_of_not_nan_not_inf y hy hi
    have hk := (finite_le_exact_iff_key y hf n).mp hyn
    have hg := hgap y hy
    omega

/-- A gap gives a directed ceiling even when its selected endpoint is positive infinity. -/
theorem ceil_of_gap_extended {T : FTy} (n : Int) (z : FV T) (L : Int)
    (hz : z.isnan = false) (hfirst : ConvExactLeFloat (n, 1) z)
    (hL : L < n * (den T.fmt : Int))
    (hgap : ∀ y : FV T, y.isnan = false → key y ≤ L ∨ key z ≤ key y) :
    ConvFloatCeil (n, 1) z := by
  refine ⟨hfirst, ?_⟩
  intro y hy hny
  apply (float_le_iff_key z y hz hy).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = false := by
      simpa only [ConvExactLeFloat, hi, ↓reduceIte] using hny
    rw [inf_key_eq (good_fty T) y hi, hs]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (key_abs_bound z hz).2
  · have hf := finite_of_not_nan_not_inf y hy hi
    have hk := (finite_exact_le_iff_key y hf n).mp hny
    have hg := hgap y hy
    omega

/-- The source increment rule, expressed in an exact residue and its positive step. -/
def residueIncrement (r : RoundingMode) (negative : Bool) (q R d : Nat) : Bool :=
  if roundsNearest r then
    decide (d < 2*R) || (decide (d = 2*R) &&
      (if r = .Nearest then decide (q%2 = 1)
       else if r = .NearestTiesAway then true else !negative))
  else roundsAway r negative && decide (R ≠ 0)


theorem residue_zero (r : RoundingMode) (s : Bool) (q d : Nat) (hd : 0 < d) :
    residueIncrement r s q 0 d = false := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  cases r <;> simp only [residueIncrement, roundsNearest, roundsAway,
    Nat.mul_zero, Nat.not_lt_zero, hd0, ne_eq, not_true_eq_false,
    decide_false, Bool.false_and, Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

theorem residue_nearest_direction (r : RoundingMode) (s : Bool) (q R d : Nat)
    (hr : roundsNearest r = true) :
    (residueIncrement r s q R d = true → d ≤ 2*R) ∧
    (residueIncrement r s q R d = false → 2*R ≤ d) := by
  constructor
  · intro hi
    by_cases h : d ≤ 2*R
    · exact h
    · have hlt : ¬ d < 2*R := by omega
      have heq : ¬ d = 2*R := by omega
      simp only [residueIncrement, hr, ↓reduceIte, hlt, heq, decide_false,
        Bool.false_and, Bool.false_or] at hi
      exact False.elim (Bool.noConfusion hi)
  · intro hi
    by_cases h : 2*R ≤ d
    · exact h
    · have hlt : d < 2*R := by omega
      simp only [residueIncrement, hr, ↓reduceIte, hlt, decide_true, Bool.true_or] at hi
      exact False.elim (Bool.noConfusion hi)

theorem residue_midpoint_nearest (s : Bool) (q R d : Nat) (h : d = 2*R) :
    residueIncrement .Nearest s q R d = decide (q%2 = 1) := by
  have hn : ¬d < 2*R := by omega
  simp only [residueIncrement, roundsNearest, h, hn, Nat.lt_irrefl,
    decide_true, decide_false, Bool.false_or, Bool.true_and, ↓reduceIte]

theorem residue_midpoint_away (s : Bool) (q R d : Nat) (h : d = 2*R) :
    residueIncrement .NearestTiesAway s q R d = true := by
  have hne : RoundingMode.NearestTiesAway ≠ RoundingMode.Nearest := by decide
  have hn : ¬d < 2*R := by omega
  simp only [residueIncrement, roundsNearest, hne, h, hn, Nat.lt_irrefl,
    decide_true, decide_false, Bool.false_or, Bool.true_and, ↓reduceIte]

theorem residue_midpoint_up (s : Bool) (q R d : Nat) (h : d = 2*R) :
    residueIncrement .NearestTiesUp s q R d = !s := by
  have hne : RoundingMode.NearestTiesUp ≠ RoundingMode.Nearest := by decide
  have hne2 : RoundingMode.NearestTiesUp ≠ RoundingMode.NearestTiesAway := by decide
  have hn : ¬d < 2*R := by omega
  simp only [residueIncrement, roundsNearest, hne, hne2, h, hn, Nat.lt_irrefl,
    decide_true, decide_false, Bool.false_or, Bool.true_and, ↓reduceIte]

end JuliaLean.ChatGPT.Batch4.Group6.FloatSelectAux

/- Section: FloatSelectionMain. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.FloatSelectAux
open JuliaLean JuliaLean.Promotion.Fl JuliaLean.base.float JuliaLean.base.gmp
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group6.FloatConstructAux
open JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux
open JuliaLean.ChatGPT.Batch4.Group6.FloatChoiceAux

/-- The source-shaped residue increment selects the documented neighbor in every public mode. -/
theorem residue_choice {T : FTy} (n : Int) (a b : FV T) (M q R d : Nat)
    (hR : R < d) (ha : a.isfinite = true) (hb : b.isnan = false)
    (hsa : a.signbit = decide (n < 0)) (hsb : b.signbit = decide (n < 0))
    (hka : key a = if n < 0 then -(magKey T.fmt M : Int) else (magKey T.fmt M : Int))
    (hkb : key b = if n < 0 then -(magKey T.fmt (M+1) : Int) else (magKey T.fmt (M+1) : Int))
    (hLower : (magKey T.fmt M : Int) ≤ (n.natAbs : Int) * (den T.fmt : Int))
    (hUpper : (n.natAbs : Int) * (den T.fmt : Int) < (magKey T.fmt (M+1) : Int))
    (hZero : R = 0 ↔ (n.natAbs : Int) * (den T.fmt : Int) = (magKey T.fmt M : Int))
    (hMidLt : d < 2*R ↔ (magKey T.fmt M : Int) + (magKey T.fmt (M+1) : Int) <
      2 * ((n.natAbs : Int) * (den T.fmt : Int)))
    (hMidEq : d = 2*R ↔ (magKey T.fmt M : Int) + (magKey T.fmt (M+1) : Int) =
      2 * ((n.natAbs : Int) * (den T.fmt : Int)))
    (hpa : a.toBits % 2 = q % 2) (hpb : b.toBits % 2 = (q+1) % 2)
    (r : RoundingMode) :
    ConvFloatChoice r n (if residueIncrement r (decide (n<0)) q R d then b else a) := by
  let N : Int := (n.natAbs : Int) * (den T.fmt : Int)
  let L : Int := (magKey T.fmt M : Int)
  let U : Int := (magKey T.fmt (M+1) : Int)
  let l : FV T := if n < 0 then b else a
  let u : FV T := if n < 0 then a else b
  let z (rm : RoundingMode) : FV T :=
    if residueIncrement rm (decide (n<0)) q R d then b else a
  change key a = if n < 0 then -L else L at hka
  change key b = if n < 0 then -U else U at hkb
  change L ≤ N at hLower
  change N < U at hUpper
  change R = 0 ↔ N = L at hZero
  change d < 2*R ↔ L+U < 2*N at hMidLt
  change d = 2*R ↔ L+U = 2*N at hMidEq
  change ConvFloatChoice r n (z r)
  have hL0 : 0 ≤ L := Int.natCast_nonneg _
  have hNa : a.isnan = false := isnan_of_finite ha
  have hscaled : n * (den T.fmt : Int) = if n < 0 then -N else N := by
    by_cases hn : n < 0
    · have hnabs : (n.natAbs : Int) = -n := by omega
      simp only [N, hn, ↓reduceIte, hnabs, Int.neg_mul, Int.neg_neg]
    · have hnabs : (n.natAbs : Int) = n := by omega
      simp only [N, hn, ↓reduceIte, hnabs]
  have hln : l.isnan = false := by
    by_cases hn : n < 0 <;> simp only [l, hn, ↓reduceIte, hNa, hb]
  have hun : u.isnan = false := by
    by_cases hn : n < 0 <;> simp only [u, hn, ↓reduceIte, hNa, hb]
  have hls : l.signbit = decide (n<0) := by
    by_cases hn : n < 0 <;> simp only [l, hn, ↓reduceIte, hsa, hsb]
  have hus : u.signbit = decide (n<0) := by
    by_cases hn : n < 0 <;> simp only [u, hn, ↓reduceIte, hsa, hsb]
  have hzn (rm : RoundingMode) : (z rm).isnan = false := by
    unfold z
    split <;> assumption
  have hzs (rm : RoundingMode) : (z rm).signbit = decide (n<0) := by
    unfold z
    split <;> assumption
  have hgap : ∀ y : FV T, y.isnan = false → key y ≤ key l ∨ key u ≤ key y := by
    intro y _
    by_cases hn : n < 0
    · have hg := no_key_between_negative T.fmt M y
      change ¬ (-U < key y ∧ key y < -L) at hg
      simp only [l, u, hn, ↓reduceIte, hka, hkb]
      omega
    · have hg := no_key_between T.fmt M y
      change ¬ (L < key y ∧ key y < U) at hg
      simp only [l, u, hn, ↓reduceIte, hka, hkb]
      omega
  have hlnum : key l ≤ n * (den T.fmt : Int) := by
    by_cases hn : n < 0 <;> simp only [l, hka, hkb, hscaled, hn, ↓reduceIte] <;> omega
  have hunum : n * (den T.fmt : Int) ≤ key u := by
    by_cases hn : n < 0 <;> simp only [u, hka, hkb, hscaled, hn, ↓reduceIte] <;> omega
  by_cases hR0 : R = 0
  · have heq := hZero.mp hR0
    have hak : key a = n * (den T.fmt : Int) := by
      by_cases hn : n < 0 <;> simp only [hka, hscaled, hn, ↓reduceIte] <;> omega
    have hz : z r = a := by
      simp only [z, hR0, residue_zero r (decide (n<0)) q d (by omega), Bool.false_eq_true, ↓reduceIte]
    rw [hz]
    exact exact_key_choice n a ha hsa hak r
  · have hstrict : L < N := by omega
    have hRbool : decide (R ≠ 0) = true := decide_eq_true hR0
    have hlstrict : key l < n * (den T.fmt : Int) := by
      by_cases hn : n < 0 <;> simp only [l, hka, hkb, hscaled, hn, ↓reduceIte] <;> omega
    have hustrict : n * (den T.fmt : Int) < key u := by
      by_cases hn : n < 0 <;> simp only [u, hka, hkb, hscaled, hn, ↓reduceIte] <;> omega
    have hfirstl : ConvFloatLeExact l (n, 1) := by
      by_cases hi : l.isinf = true
      · have hn : n < 0 := by
          by_cases hn : n < 0
          · exact hn
          · have heq : l = a := by simp only [l, hn, ↓reduceIte]
            rw [heq, isinf_of_finite ha] at hi
            exact False.elim (Bool.noConfusion hi)
        simp only [ConvFloatLeExact, hi, ↓reduceIte, hls, hn, decide_true]
      · exact (finite_le_exact_iff_key l (finite_of_not_nan_not_inf l hln hi) n).mpr hlnum
    have hfirstu : ConvExactLeFloat (n, 1) u := by
      by_cases hi : u.isinf = true
      · have hn : ¬n < 0 := by
          intro hn
          have heq : u = a := by simp only [u, hn, ↓reduceIte]
          rw [heq, isinf_of_finite ha] at hi
          exact Bool.noConfusion hi
        simp only [ConvExactLeFloat, hi, ↓reduceIte, hus, hn, decide_false]
      · exact (finite_exact_le_iff_key u (finite_of_not_nan_not_inf u hun hi) n).mpr hunum
    have hfloor := floor_of_gap_extended n l (key u) hln hfirstl hustrict hgap
    have hceil := ceil_of_gap_extended n u (key l) hun hfirstu hlstrict hgap
    have hnear (rm : RoundingMode) (hr : roundsNearest rm = true) :
        ConvFloatNearest (n, 1) (z rm) := by
      have hd := residue_nearest_direction rm (decide (n<0)) q R d hr
      have hdown : residueIncrement rm (decide (n<0)) q R d = false → 2*N ≤ L+U := by
        intro hi
        have hc := hd.2 hi
        omega
      have hup : residueIncrement rm (decide (n<0)) q R d = true → L+U ≤ 2*N := by
        intro hi
        have hc := hd.1 hi
        omega
      have hdist : keyDistance n (z rm) ≤ keyDistance n l ∧
          keyDistance n (z rm) ≤ keyDistance n u := by
        cases hi : residueIncrement rm (decide (n<0)) q R d with
        | false =>
          have hc := hdown hi
          have hz : z rm = a := by simp only [z, hi, Bool.false_eq_true, ↓reduceIte]
          by_cases hn : n < 0 <;>
            simp only [keyDistance, hz, l, u, hka, hkb, hscaled, hn, ↓reduceIte] <;> omega
        | true =>
          have hc := hup hi
          have hz : z rm = b := by simp only [z, hi, ↓reduceIte]
          by_cases hn : n < 0 <;>
            simp only [keyDistance, hz, l, u, hka, hkb, hscaled, hn, ↓reduceIte] <;> omega
      exact nearest_of_neighbors n l u (z rm) (hzn rm) hlnum hunum hgap hdist.1 hdist.2
    have hmidpoint (hm : 2 * (n * (den T.fmt : Int)) = key l + key u) : d = 2*R := by
      apply hMidEq.mpr
      by_cases hn : n < 0 <;>
        simp only [l, u, hka, hkb, hscaled, hn, ↓reduceIte] at hm <;> omega
    cases r with
    | ToZero =>
      have hz : z .ToZero = a := by
        simp only [z, residueIncrement, roundsNearest, roundsAway, Bool.false_eq_true,
          ↓reduceIte, Bool.false_and]
      rw [hz]
      refine ⟨hNa, hsa, ?_⟩
      by_cases hn : n < 0
      · simpa only [u, hn, ↓reduceIte] using hceil
      · simpa only [l, hn, ↓reduceIte] using hfloor
    | Down =>
      have hz : z .Down = l := by
        by_cases hn : n < 0 <;>
          simp only [z, l, residueIncrement, roundsNearest, roundsAway, Bool.false_eq_true,
            hRbool, decide_true, hn, decide_false, ↓reduceIte, Bool.and_true, Bool.false_and, Bool.true_and]
      rw [hz]
      exact ⟨hln, hls, hfloor⟩
    | Up =>
      have hz : z .Up = u := by
        by_cases hn : n < 0 <;>
          simp only [z, u, residueIncrement, roundsNearest, roundsAway, Bool.false_eq_true,
            hRbool, decide_true, hn, decide_false, ↓reduceIte, Bool.not_true, Bool.not_false, Bool.and_true, Bool.false_and, Bool.true_and]
      rw [hz]
      exact ⟨hun, hus, hceil⟩
    | FromZero =>
      have hz : z .FromZero = b := by
        simp only [z, residueIncrement, roundsNearest, roundsAway, Bool.false_eq_true,
          hRbool, decide_true, ↓reduceIte, Bool.true_and]
      rw [hz]
      refine ⟨hb, hsb, ?_⟩
      by_cases hn : n < 0
      · simpa only [l, hn, ↓reduceIte] using hfloor
      · simpa only [u, hn, ↓reduceIte] using hceil
    | Nearest =>
      have hmin := (nearest_iff_key n (z .Nearest) (hzn .Nearest)).mp (hnear .Nearest rfl)
      apply nearest_choice_of_neighbors n l u (z .Nearest) hln hun (hzn .Nearest)
        (hzs .Nearest) hlnum hunum hgap (hmin l hln) (hmin u hun)
      intro hm
      have hm' := hmidpoint hm
      change (if residueIncrement .Nearest (decide (n<0)) q R d then b else a).toBits % 2 = 0
      rw [residue_midpoint_nearest _ _ _ _ hm']
      have hmod := Nat.mod_lt q (by decide : 0 < 2)
      by_cases hq : q%2 = 1
      · simp only [hq, decide_true, ↓reduceIte, hpb]
        omega
      · simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte, hpa]
        omega
    | NearestTiesAway =>
      have hmin := (nearest_iff_key n (z .NearestTiesAway) (hzn .NearestTiesAway)).mp
        (hnear .NearestTiesAway rfl)
      apply nearest_away_choice_of_neighbors n l u (z .NearestTiesAway) hln hun
        (hzn .NearestTiesAway) (hzs .NearestTiesAway) hlnum hunum hgap (hmin l hln) (hmin u hun)
      intro hm
      have hm' := hmidpoint hm
      have hz : z .NearestTiesAway = b := by
        simp only [z, residue_midpoint_away _ _ _ _ hm', ↓reduceIte]
      rw [hz]
      by_cases hn : n < 0 <;>
        simp only [keyDistance, l, u, hka, hkb, hn, ↓reduceIte] <;> omega
    | NearestTiesUp =>
      have hmin := (nearest_iff_key n (z .NearestTiesUp) (hzn .NearestTiesUp)).mp
        (hnear .NearestTiesUp rfl)
      apply nearest_up_choice_of_neighbors n l u (z .NearestTiesUp) hln hun
        (hzn .NearestTiesUp) (hzs .NearestTiesUp) hlnum hunum hgap (hmin l hln) (hmin u hun)
      intro hm
      have hm' := hmidpoint hm
      have hz : z .NearestTiesUp = u := by
        by_cases hn : n < 0 <;>
          simp only [z, u, residue_midpoint_up _ _ _ _ hm', hn, decide_true, decide_false,
            Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      rw [hz]
      exact Int.le_refl _

end JuliaLean.ChatGPT.Batch4.Group6.FloatSelectAux

/- Section: FloatExtremes. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.FloatExtremeAux
open JuliaLean JuliaLean.Promotion.Fl JuliaLean.base.float JuliaLean.base.gmp
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group6.FloatConstructAux
open JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux
open JuliaLean.ChatGPT.Batch4.Group6.FloatChoiceAux

def infinityKey (T : FTy) : Int := ((2 ^ T.fmt.sb * 2 ^ (T.fmt.emax - 1) : Nat) : Int)
def largestFinite (T : FTy) (s : Bool) : FV T := if s then Fl.neg Fl.floatmax else Fl.floatmax

theorem infinityKey_pos (T : FTy) : 0 < infinityKey T :=
  Int.ofNat_lt.mpr (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))

theorem inf_data (T : FTy) (s : Bool) :
    (Fl.inf s : FV T).isnan = false ∧ (Fl.inf s : FV T).isinf = true ∧
    (Fl.inf s : FV T).signbit = s ∧ (Fl.inf s : FV T).toBits % 2 = 0 := by
  cases T <;> cases s <;> decide

theorem finite_edge_data (T : FTy) (s : Bool) :
    (largestFinite T s).isfinite = true ∧ (largestFinite T s).signbit = s ∧
    (largestFinite T s).magnitude = T.fmt.emax * 2 ^ T.fmt.sb - 1 := by
  cases T <;> cases s <;> decide

theorem inf_key (T : FTy) (s : Bool) :
    key (Fl.inf s : FV T) = if s then -infinityKey T else infinityKey T := by
  rw [inf_key_eq (good_fty T) (Fl.inf s) (inf_data T s).2.1, (inf_data T s).2.2.1]
  rfl

theorem finite_edge_key (T : FTy) (s : Bool) :
    key (largestFinite T s) = if s then
      -(magKey T.fmt (T.fmt.emax * 2 ^ T.fmt.sb - 1) : Int)
      else (magKey T.fmt (T.fmt.emax * 2 ^ T.fmt.sb - 1) : Int) := by
  unfold key
  rw [(finite_edge_data T s).2.1, (finite_edge_data T s).2.2]

theorem inf_magKey (T : FTy) :
    (magKey T.fmt (T.fmt.emax * 2 ^ T.fmt.sb) : Int) = infinityKey T := by
  have he : T.fmt.emax ≠ 0 := by cases T <;> decide
  unfold magKey infinityKey
  rw [Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.mul_mod_left,
    if_neg he, Nat.zero_add]

theorem finite_edge_bounds {T : FTy} (x : FV T) (hx : x.isfinite = true) :
    key (largestFinite T true) ≤ key x ∧ key x ≤ key (largestFinite T false) := by
  have hbig : 0 < T.fmt.emax * 2 ^ T.fmt.sb := by
    exact Nat.mul_pos (by cases T <;> decide) (Nat.two_pow_pos _)
  have hnext : T.fmt.emax * 2 ^ T.fmt.sb - 1 + 1 = T.fmt.emax * 2 ^ T.fmt.sb := by omega
  have hgap := no_key_between T.fmt (T.fmt.emax * 2 ^ T.fmt.sb - 1) x
  have hneg := no_key_between_negative T.fmt (T.fmt.emax * 2 ^ T.fmt.sb - 1) x
  rw [hnext, inf_magKey T] at hgap hneg
  have hb := finite_key_lt_inf (good_fty T) x hx
  change -infinityKey T < key x ∧ key x < infinityKey T at hb
  rw [finite_edge_key, finite_edge_key]
  simp only [Bool.false_eq_true, ↓reduceIte]
  omega

/-- Beyond the positive virtual infinity point, infinity is the unique nearest coordinate. -/
theorem nearest_positive_inf {T : FTy} (n : Int)
    (hn : infinityKey T ≤ n * (den T.fmt : Int)) :
    ConvFloatNearest (n, 1) (Fl.inf false : FV T) ∧
    ∀ y : FV T, y.isnan = false → ConvFloatNearest (n, 1) y →
      key y = key (Fl.inf false : FV T) := by
  have hi := (inf_data T false).1
  have hk : key (Fl.inf false : FV T) = infinityKey T := by
    simpa only [Bool.false_eq_true, ↓reduceIte] using inf_key T false
  constructor
  · apply (nearest_iff_key n (Fl.inf false) hi).mpr
    intro y hy
    have hb := (key_abs_bound y hy).2
    change key y ≤ infinityKey T at hb
    unfold keyDistance
    rw [hk]
    omega
  · intro y hy hny
    have hd := (nearest_iff_key n y hy).mp hny (Fl.inf false) hi
    have hb := (key_abs_bound y hy).2
    change key y ≤ infinityKey T at hb
    unfold keyDistance at hd
    rw [hk] at hd ⊢
    omega

/-- Beyond the negative virtual infinity point, negative infinity is the unique nearest coordinate. -/
theorem nearest_negative_inf {T : FTy} (n : Int)
    (hn : n * (den T.fmt : Int) ≤ -infinityKey T) :
    ConvFloatNearest (n, 1) (Fl.inf true : FV T) ∧
    ∀ y : FV T, y.isnan = false → ConvFloatNearest (n, 1) y →
      key y = key (Fl.inf true : FV T) := by
  have hi := (inf_data T true).1
  have hk : key (Fl.inf true : FV T) = -infinityKey T := by
    simpa only [↓reduceIte] using inf_key T true
  constructor
  · apply (nearest_iff_key n (Fl.inf true) hi).mpr
    intro y hy
    have hb := (key_abs_bound y hy).1
    change -infinityKey T ≤ key y at hb
    unfold keyDistance
    rw [hk]
    omega
  · intro y hy hny
    have hd := (nearest_iff_key n y hy).mp hny (Fl.inf true) hi
    have hb := (key_abs_bound y hy).1
    change -infinityKey T ≤ key y at hb
    unfold keyDistance at hd
    rw [hk] at hd ⊢
    omega


/-- Above the virtual positive infinity point, the greatest finite value is the floor. -/
theorem far_positive_floor {T : FTy} (n : Int)
    (hn : infinityKey T ≤ n * (den T.fmt : Int)) :
    ConvFloatFloor (n, 1) (largestFinite T false) := by
  have hf := (finite_edge_data T false).1
  have he := (finite_key_lt_inf (good_fty T) (largestFinite T false) hf).2
  change key (largestFinite T false) < infinityKey T at he
  refine ⟨(finite_le_exact_iff_key _ hf n).mpr (by omega), ?_⟩
  intro y hy hyn
  apply (float_le_iff_key y _ hy (isnan_of_finite hf)).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = true := by
      simpa only [ConvFloatLeExact, hi, ↓reduceIte] using hyn
    rw [inf_key_eq (good_fty T) y hi]
    simp only [hs, ↓reduceIte]
    exact Int.le_of_lt (finite_key_lt_inf (good_fty T) (largestFinite T false) hf).1
  · exact (finite_edge_bounds y (finite_of_not_nan_not_inf y hy hi)).2

/-- Above the virtual positive infinity point, positive infinity is the ceiling. -/
theorem far_positive_ceil {T : FTy} (n : Int)
    (hn : infinityKey T ≤ n * (den T.fmt : Int)) :
    ConvFloatCeil (n, 1) (Fl.inf false : FV T) := by
  have hi := inf_data T false
  refine ⟨?_, ?_⟩
  · simp only [ConvExactLeFloat, hi.2.1, hi.2.2.1, ↓reduceIte]
  · intro y hy hny
    by_cases hj : y.isinf = true
    · have hs : y.signbit = false := by
        simpa only [ConvExactLeFloat, hj, ↓reduceIte] using hny
      simp only [ConvFloatLe, hi.2.1, hi.2.2.1, hj, hs, Bool.false_eq_true,
        ↓reduceIte, false_or, and_self]
    · have hf := finite_of_not_nan_not_inf y hy hj
      have hle := (finite_exact_le_iff_key y hf n).mp hny
      have hlt := (finite_key_lt_inf (good_fty T) y hf).2
      change key y < infinityKey T at hlt
      omega

/-- Below the virtual negative infinity point, negative infinity is the floor. -/
theorem far_negative_floor {T : FTy} (n : Int)
    (hn : n * (den T.fmt : Int) ≤ -infinityKey T) :
    ConvFloatFloor (n, 1) (Fl.inf true : FV T) := by
  have hi := inf_data T true
  refine ⟨?_, ?_⟩
  · simp only [ConvFloatLeExact, hi.2.1, hi.2.2.1, ↓reduceIte]
  · intro y hy hyn
    by_cases hj : y.isinf = true
    · have hs : y.signbit = true := by
        simpa only [ConvFloatLeExact, hj, ↓reduceIte] using hyn
      simp only [ConvFloatLe, hj, hs, ↓reduceIte, true_or]
    · have hf := finite_of_not_nan_not_inf y hy hj
      have hle := (finite_le_exact_iff_key y hf n).mp hyn
      have hlt := (finite_key_lt_inf (good_fty T) y hf).1
      change -infinityKey T < key y at hlt
      omega

/-- Below the virtual negative infinity point, the least finite value is the ceiling. -/
theorem far_negative_ceil {T : FTy} (n : Int)
    (hn : n * (den T.fmt : Int) ≤ -infinityKey T) :
    ConvFloatCeil (n, 1) (largestFinite T true) := by
  have hf := (finite_edge_data T true).1
  have he := (finite_key_lt_inf (good_fty T) (largestFinite T true) hf).1
  change -infinityKey T < key (largestFinite T true) at he
  refine ⟨(finite_exact_le_iff_key _ hf n).mpr (by omega), ?_⟩
  intro y hy hny
  apply (float_le_iff_key _ y (isnan_of_finite hf) hy).mpr
  by_cases hi : y.isinf = true
  · have hs : y.signbit = false := by
      simpa only [ConvExactLeFloat, hi, ↓reduceIte] using hny
    rw [inf_key_eq (good_fty T) y hi]
    simp only [hs, Bool.false_eq_true, ↓reduceIte]
    exact Int.le_of_lt (finite_key_lt_inf (good_fty T) (largestFinite T true) hf).2
  · exact (finite_edge_bounds y (finite_of_not_nan_not_inf y hy hi)).1

/-- All seven rounding modes obey the independent contract beyond positive overflow. -/
theorem far_positive_choice (T : FTy) (n : Int) (r : RoundingMode)
    (hn : infinityKey T ≤ n * (den T.fmt : Int)) :
    ConvFloatChoice r n
      (if roundsNearest r || roundsAway r false then Fl.inf false else largestFinite T false) := by
  have hpos : 0 < n := Int.pos_of_mul_pos_left
    (Int.lt_of_lt_of_le (infinityKey_pos T) hn) (Int.ofNat_lt.mpr (den_pos _))
  have hs : decide (n < 0) = false := by simp only [Int.not_lt.mpr (Int.le_of_lt hpos), decide_false]
  have hf := finite_edge_data T false
  have hi := inf_data T false
  have hfloor := far_positive_floor n hn
  have hceil := far_positive_ceil n hn
  have hnear := nearest_positive_inf n hn
  have hnall := nearest_modes_unique n (Fl.inf false : FV T) hi.1
    (hi.2.2.1.trans hs.symm) hnear.1 hnear.2
  cases r with
  | Nearest =>
    simpa only [roundsNearest, roundsAway, Bool.true_or, ↓reduceIte] using hnall.1
  | Up =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, Bool.not_false, ↓reduceIte,
      ConvFloatChoice, hs, Bool.false_eq_true, decide_true, decide_false] using And.intro hi.1 (And.intro hi.2.2.1 hceil)
  | Down =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, ↓reduceIte,
      ConvFloatChoice, hs, Bool.false_eq_true, decide_true, decide_false] using And.intro (isnan_of_finite hf.1) (And.intro hf.2.1 hfloor)
  | ToZero =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, ↓reduceIte,
      ConvFloatChoice, hs, Int.not_lt.mpr (Int.le_of_lt hpos), Bool.false_eq_true, decide_true, decide_false] using
        And.intro (isnan_of_finite hf.1) (And.intro hf.2.1 hfloor)
  | FromZero =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, ↓reduceIte,
      ConvFloatChoice, hs, Int.not_lt.mpr (Int.le_of_lt hpos), Bool.false_eq_true, decide_true, decide_false] using
        And.intro hi.1 (And.intro hi.2.2.1 hceil)
  | NearestTiesAway =>
    simpa only [roundsNearest, roundsAway, Bool.true_or, ↓reduceIte] using hnall.2.1
  | NearestTiesUp =>
    simpa only [roundsNearest, roundsAway, Bool.true_or, ↓reduceIte] using hnall.2.2

/-- All seven rounding modes obey the independent contract beyond negative overflow. -/
theorem far_negative_choice (T : FTy) (n : Int) (r : RoundingMode)
    (hn : n * (den T.fmt : Int) ≤ -infinityKey T) :
    ConvFloatChoice r n
      (if roundsNearest r || roundsAway r true then Fl.inf true else largestFinite T true) := by
  have hd : 0 < (den T.fmt : Int) := Int.ofNat_lt.mpr (den_pos _)
  have hneg : n < 0 := Int.neg_of_mul_neg_left
    (by have hp := infinityKey_pos T; omega) hd
  have hs : decide (n < 0) = true := by simp only [hneg, decide_true]
  have hf := finite_edge_data T true
  have hi := inf_data T true
  have hfloor := far_negative_floor n hn
  have hceil := far_negative_ceil n hn
  have hnear := nearest_negative_inf n hn
  have hnall := nearest_modes_unique n (Fl.inf true : FV T) hi.1
    (hi.2.2.1.trans hs.symm) hnear.1 hnear.2
  cases r with
  | Nearest =>
    simpa only [roundsNearest, roundsAway, Bool.true_or, ↓reduceIte] using hnall.1
  | Up =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, Bool.not_true, ↓reduceIte,
      ConvFloatChoice, hs, Bool.false_eq_true, decide_true, decide_false] using And.intro (isnan_of_finite hf.1) (And.intro hf.2.1 hceil)
  | Down =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, ↓reduceIte,
      ConvFloatChoice, hs, Bool.false_eq_true, decide_true, decide_false] using And.intro hi.1 (And.intro hi.2.2.1 hfloor)
  | ToZero =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, ↓reduceIte,
      ConvFloatChoice, hs, hneg, Bool.false_eq_true, decide_true, decide_false] using
        And.intro (isnan_of_finite hf.1) (And.intro hf.2.1 hceil)
  | FromZero =>
    simpa only [roundsNearest, roundsAway, Bool.false_or, ↓reduceIte,
      ConvFloatChoice, hs, hneg, Bool.false_eq_true, decide_true, decide_false] using And.intro hi.1 (And.intro hi.2.2.1 hfloor)
  | NearestTiesAway =>
    simpa only [roundsNearest, roundsAway, Bool.true_or, ↓reduceIte] using hnall.2.1
  | NearestTiesUp =>
    simpa only [roundsNearest, roundsAway, Bool.true_or, ↓reduceIte] using hnall.2.2

/-- The integer overflow threshold matches the independent metric's infinity scale. -/
theorem far_magnitude_choice (T : FTy) (n : Int) (r : RoundingMode)
    (hn : 2 ^ (T.fmt.bias + 1) ≤ n.natAbs) :
    ConvFloatChoice r n
      (if roundsNearest r || roundsAway r (decide (n < 0)) then Fl.inf (decide (n < 0))
       else largestFinite T (decide (n < 0))) := by
  have hd : 0 < (den T.fmt : Int) := Int.ofNat_lt.mpr (den_pos _)
  have hscale := inf_scale (good_fty T)
  change ((2 ^ (T.fmt.bias + 1) : Nat) : Int) * (den T.fmt : Int) = infinityKey T at hscale
  by_cases hneg : n < 0
  · have ha : (n.natAbs : Int) = -n := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    have hh : ((2 ^ (T.fmt.bias + 1) : Nat) : Int) ≤ -n := by
      have hc := Int.ofNat_le.mpr hn
      simpa only [ha] using hc
    have hm := Int.mul_le_mul_of_nonneg_right hh (Int.le_of_lt hd)
    rw [hscale, Int.neg_mul] at hm
    have hN : n * (den T.fmt : Int) ≤ -infinityKey T := by omega
    simpa only [hneg, decide_true] using far_negative_choice T n r hN
  · have ha : (n.natAbs : Int) = n := Int.ofNat_natAbs_of_nonneg (by omega)
    have hh : ((2 ^ (T.fmt.bias + 1) : Nat) : Int) ≤ n := by
      have hc := Int.ofNat_le.mpr hn
      simpa only [ha] using hc
    have hm := Int.mul_le_mul_of_nonneg_right hh (Int.le_of_lt hd)
    rw [hscale] at hm
    simpa only [hneg, decide_false] using far_positive_choice T n r hm


/-- The source exponent limit is the format's documented maximum normal exponent. -/
theorem source_exponent_max (T : FTy) : (exponent_max T).val = (T.fmt.bias : Int) := by
  cases T <;> decide

/-- The complete source overflow branch satisfies every public rounding mode. -/
theorem source_far_choice (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hm : 2 ^ (T.fmt.bias + 1) ≤ x.val.natAbs) :
    ConvFloatChoice r x.val (toFloat T x r) := by
  have hp := Nat.two_pow_pos (T.fmt.bias + 1)
  have hn : x.val ≠ 0 := by
    intro hz
    simp only [hz, Int.natAbs_zero] at hm
    omega
  have ha : x.val.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hl := (Nat.le_log2 ha).mpr hm
  have hbits := cgGMPBitLength x hx hn
  have hb : ((loadLimb x (x.size.val.natAbs - 1)).log2 + 1 +
      (x.size.val.natAbs - 1) * 64 : Nat) > (exponent_max T).val + 1 := by
    rw [← hbits, source_exponent_max]
    omega
  rw [floatOutput_overflow_branch T x r hx hn hb]
  have hs : isnegative x = decide (x.val < 0) := by
    simp only [isnegative, (g6valid_sign x hx.1).1]
  rw [hs]
  exact far_magnitude_choice T x.val r hm

end JuliaLean.ChatGPT.Batch4.Group6.FloatExtremeAux

/- Section: FloatBinade. -/
namespace JuliaLean.ChatGPT.Batch4.Group6.FloatBinadeAux
open JuliaLean JuliaLean.Promotion.Fl JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.ChatGPT.Batch4.Group6.FloatConstructAux
open JuliaLean.ChatGPT.Batch4.Group6.IEEEOrderAux

def binadeLength (A : Nat) : Nat := A.log2 + 1
def binadeStep (f : Fmt) (A : Nat) : Nat := 2 ^ (binadeLength A - (f.sb + 1))
def binadePadding (f : Fmt) (A : Nat) : Nat := 2 ^ (f.sb + 1 - binadeLength A)
def binadeQuotient (f : Fmt) (A : Nat) : Nat := A / binadeStep f A * binadePadding f A
def binadeResidue (f : Fmt) (A : Nat) : Nat := A % binadeStep f A
def binadeExponent (f : Fmt) (A : Nat) : Nat := binadeLength A - 1 + f.bias
def binadeScale (f : Fmt) (A : Nat) : Nat := 2 ^ (binadeExponent f A - 1)
def binadeMagnitude (f : Fmt) (A : Nat) : Nat :=
  binadeExponent f A * 2 ^ f.sb + binadeQuotient f A % 2 ^ f.sb

theorem binade_length_bounds (A : Nat) (ha : 0 < A) :
    2 ^ (binadeLength A - 1) ≤ A ∧ A < 2 ^ binadeLength A := by
  unfold binadeLength
  simp only [Nat.add_sub_cancel]
  exact (Nat.log2_eq_iff (Nat.ne_of_gt ha)).mp rfl

/-- Normalize an integer into exactly the requested number of binary digits. -/
theorem precision_quotient_bounds (A L p : Nat) (hL : 0 < L) (hp : 0 < p)
    (ha : 2 ^ (L-1) ≤ A) (hb : A < 2 ^ L) :
    2 ^ (p-1) ≤ A / 2 ^ (L-p) * 2 ^ (p-L) ∧
      A / 2 ^ (L-p) * 2 ^ (p-L) < 2 ^ p := by
  by_cases hpl : p ≤ L
  · have hz : p-L = 0 := Nat.sub_eq_zero_of_le hpl
    simp only [hz, Nat.pow_zero, Nat.mul_one]
    have hlow : 2 ^ (p-1) * 2 ^ (L-p) = 2 ^ (L-1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hupp : 2 ^ p * 2 ^ (L-p) = 2 ^ L := by
      rw [← Nat.pow_add]
      congr 1
      omega
    constructor
    · apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      rw [hlow]
      exact ha
    · apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      rw [hupp]
      exact hb
  · have hz : L-p = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [hz, Nat.pow_zero, Nat.div_one]
    have hlow : 2 ^ (L-1) * 2 ^ (p-L) = 2 ^ (p-1) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hupp : 2 ^ L * 2 ^ (p-L) = 2 ^ p := by
      rw [← Nat.pow_add]
      congr 1
      omega
    constructor
    · rw [← hlow]
      exact Nat.mul_le_mul_right _ ha
    · rw [← hupp]
      exact Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)

theorem binade_quotient_bounds (f : Fmt) (A : Nat) (ha : 0 < A) :
    2 ^ f.sb ≤ binadeQuotient f A ∧ binadeQuotient f A < 2 ^ (f.sb+1) := by
  have hb := binade_length_bounds A ha
  have hq := precision_quotient_bounds A (binadeLength A) (f.sb+1)
    (Nat.succ_pos _) (Nat.succ_pos _) hb.1 hb.2
  simpa only [Nat.add_sub_cancel, binadeQuotient, binadeStep, binadePadding] using hq

/-- Padding on the short side and integer spacing on the long side have the same key scale. -/
theorem binade_scale_relation (f : Fmt) (hf : Good f) (A : Nat) :
    binadePadding f A * binadeScale f A = binadeStep f A * den f := by
  have hb := hf.bias_pos
  unfold binadePadding binadeScale binadeExponent binadeStep den
  rw [← Nat.pow_add, ← Nat.pow_add]
  congr 1
  have hL : 0 < binadeLength A := Nat.succ_pos _
  omega

/-- Euclidean division gives the exact integer coordinate and discarded residue. -/
theorem binade_scaled_decomposition (f : Fmt) (hf : Good f) (A : Nat) :
    A * den f = binadeQuotient f A * binadeScale f A + binadeResidue f A * den f := by
  unfold binadeQuotient binadeResidue
  rw [Nat.mul_assoc, binade_scale_relation f hf A, ← Nat.mul_assoc]
  have h := congrArg (fun n => n * den f) (Nat.div_add_mod A (binadeStep f A))
  simpa only [Nat.add_mul, Nat.mul_comm (binadeStep f A) (A / binadeStep f A)] using h.symm

theorem binade_residue_lt (f : Fmt) (A : Nat) : binadeResidue f A < binadeStep f A :=
  Nat.mod_lt A (Nat.two_pow_pos _)

theorem binade_small_residue (f : Fmt) (A : Nat) (h : binadeLength A < f.sb+1) :
    binadeStep f A = 1 ∧ binadeResidue f A = 0 := by
  have hz : binadeLength A - (f.sb+1) = 0 := Nat.sub_eq_zero_of_le (by omega)
  simp only [binadeStep, binadeResidue, hz, Nat.pow_zero, Nat.mod_one, and_self]

theorem binade_large_scale (f : Fmt) (hf : Good f) (A : Nat)
    (h : f.sb+1 ≤ binadeLength A) : binadeScale f A = binadeStep f A * den f := by
  have hs := binade_scale_relation f hf A
  have hz : f.sb+1-binadeLength A = 0 := Nat.sub_eq_zero_of_le h
  simpa only [binadePadding, hz, Nat.pow_zero, Nat.one_mul] using hs

theorem binade_scaled_residue_lt (f : Fmt) (hf : Good f) (A : Nat) :
    binadeResidue f A * den f < binadeScale f A := by
  by_cases h : f.sb+1 ≤ binadeLength A
  · rw [binade_large_scale f hf A h]
    exact Nat.mul_lt_mul_of_pos_right (binade_residue_lt f A) (den_pos f)
  · have hz := (binade_small_residue f A (by omega)).2
    rw [hz, Nat.zero_mul]
    exact Nat.two_pow_pos _

theorem binade_midpoint_lt_scale (f : Fmt) (hf : Good f) (A : Nat) :
    binadeStep f A < 2 * binadeResidue f A ↔
      binadeScale f A < 2 * (binadeResidue f A * den f) := by
  by_cases h : f.sb+1 ≤ binadeLength A
  · rw [binade_large_scale f hf A h, ← Nat.mul_assoc,
      Nat.mul_lt_mul_right (den_pos f)]
  · have hz := binade_small_residue f A (by omega)
    rw [hz.1, hz.2, Nat.mul_zero, Nat.zero_mul, Nat.mul_zero]
    have hp : 0 < binadeScale f A := Nat.two_pow_pos _
    omega

theorem binade_midpoint_eq_scale (f : Fmt) (hf : Good f) (A : Nat) :
    binadeStep f A = 2 * binadeResidue f A ↔
      binadeScale f A = 2 * (binadeResidue f A * den f) := by
  by_cases h : f.sb+1 ≤ binadeLength A
  · rw [binade_large_scale f hf A h, ← Nat.mul_assoc,
      Nat.mul_right_cancel_iff (den_pos f)]
  · have hz := binade_small_residue f A (by omega)
    rw [hz.1, hz.2, Nat.mul_zero, Nat.zero_mul, Nat.mul_zero]
    have hp : 0 < binadeScale f A := Nat.two_pow_pos _
    omega

/-- The normalized quotient and its successor bracket the exact scaled integer. -/
theorem binade_scaled_bracket (f : Fmt) (hf : Good f) (A : Nat) :
    binadeQuotient f A * binadeScale f A ≤ A * den f ∧
      A * den f < (binadeQuotient f A + 1) * binadeScale f A := by
  have hd := binade_scaled_decomposition f hf A
  have hr := binade_scaled_residue_lt f hf A
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem binade_scaled_zero (f : Fmt) (hf : Good f) (A : Nat) :
    binadeResidue f A = 0 ↔ A * den f = binadeQuotient f A * binadeScale f A := by
  have hd := binade_scaled_decomposition f hf A
  constructor
  · intro hz
    rw [hz, Nat.zero_mul, Nat.add_zero] at hd
    exact hd
  · intro he
    by_cases hn : binadeResidue f A = 0
    · exact hn
    · have hp := Nat.mul_pos (Nat.pos_of_ne_zero hn) (den_pos f)
      omega

theorem binade_scaled_midpoint_lt (f : Fmt) (hf : Good f) (A : Nat) :
    binadeStep f A < 2 * binadeResidue f A ↔
      binadeQuotient f A * binadeScale f A +
        (binadeQuotient f A + 1) * binadeScale f A < 2 * (A * den f) := by
  have hd := binade_scaled_decomposition f hf A
  have hm := binade_midpoint_lt_scale f hf A
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem binade_scaled_midpoint_eq (f : Fmt) (hf : Good f) (A : Nat) :
    binadeStep f A = 2 * binadeResidue f A ↔
      binadeQuotient f A * binadeScale f A +
        (binadeQuotient f A + 1) * binadeScale f A = 2 * (A * den f) := by
  have hd := binade_scaled_decomposition f hf A
  have hm := binade_midpoint_eq_scale f hf A
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem binade_exponent_pos (f : Fmt) (hf : Good f) (A : Nat) :
    0 < binadeExponent f A := by
  have hb := hf.bias_pos
  unfold binadeExponent
  omega

theorem binade_exponent_bounds (f : Fmt) (hf : Good f) (A : Nat)
    (ha : 0 < A) (hmax : A < 2 ^ (f.bias+1)) :
    0 < binadeExponent f A ∧ binadeExponent f A < f.emax := by
  have hl := (Nat.log2_lt (Nat.ne_of_gt ha)).mpr hmax
  have he := hf.emax_eq
  constructor
  · exact binade_exponent_pos f hf A
  · unfold binadeExponent binadeLength
    omega

theorem binade_quotient_remainder (f : Fmt) (A : Nat) (ha : 0 < A) :
    binadeQuotient f A % 2 ^ f.sb + 2 ^ f.sb = binadeQuotient f A := by
  have hb := binade_quotient_bounds f A ha
  have hp := Nat.two_pow_pos f.sb
  have hdivlo : 1 ≤ binadeQuotient f A / 2 ^ f.sb :=
    (Nat.le_div_iff_mul_le hp).mpr (by simpa only [Nat.one_mul] using hb.1)
  have hdivhi : binadeQuotient f A / 2 ^ f.sb < 2 :=
    (Nat.div_lt_iff_lt_mul hp).mpr (by
      have hh := hb.2
      rw [Nat.pow_succ, Nat.mul_comm] at hh
      exact hh)
  have hdiv : binadeQuotient f A / 2 ^ f.sb = 1 := by omega
  have hm := Nat.div_add_mod (binadeQuotient f A) (2 ^ f.sb)
  rw [hdiv, Nat.mul_one] at hm
  omega

/-- The independent IEEE magnitude keys are exactly the scaled adjacent significands. -/
theorem binade_magnitude_keys (f : Fmt) (hf : Good f) (A : Nat) (ha : 0 < A) :
    magKey f (binadeMagnitude f A) = binadeQuotient f A * binadeScale f A ∧
      magKey f (binadeMagnitude f A + 1) = (binadeQuotient f A + 1) * binadeScale f A := by
  have he := binade_exponent_pos f hf A
  have hr := Nat.mod_lt (binadeQuotient f A) (Nat.two_pow_pos f.sb)
  have hq : 2 ^ f.sb + binadeQuotient f A % 2 ^ f.sb = binadeQuotient f A := by
    have hh := binade_quotient_remainder f A ha
    omega
  unfold binadeMagnitude binadeScale
  constructor
  · rw [magKey_encode f _ _ he hr, hq]
  · rw [magKey_successor f _ _ he hr, hq]

/-- All positive-magnitude premises for global rounding follow from integer binade arithmetic. -/
theorem binade_key_spec (f : Fmt) (hf : Good f) (A : Nat) (ha : 0 < A) :
    magKey f (binadeMagnitude f A) ≤ A * den f ∧
    A * den f < magKey f (binadeMagnitude f A + 1) ∧
    (binadeResidue f A = 0 ↔ A * den f = magKey f (binadeMagnitude f A)) ∧
    (binadeStep f A < 2 * binadeResidue f A ↔
      magKey f (binadeMagnitude f A) + magKey f (binadeMagnitude f A + 1) < 2 * (A * den f)) ∧
    (binadeStep f A = 2 * binadeResidue f A ↔
      magKey f (binadeMagnitude f A) + magKey f (binadeMagnitude f A + 1) = 2 * (A * den f)) := by
  have hk := binade_magnitude_keys f hf A ha
  rw [hk.1, hk.2]
  exact ⟨(binade_scaled_bracket f hf A).1, (binade_scaled_bracket f hf A).2,
    binade_scaled_zero f hf A, binade_scaled_midpoint_lt f hf A, binade_scaled_midpoint_eq f hf A⟩


/-- Both neighboring encodings carry exactly the source quotient's even/odd parity. -/
theorem binade_magnitude_parity (f : Fmt) (hf : Good f) (A : Nat) :
    binadeMagnitude f A % 2 = binadeQuotient f A % 2 ∧
      (binadeMagnitude f A + 1) % 2 = (binadeQuotient f A + 1) % 2 := by
  have hd : 2 ∣ 2 ^ f.sb := by
    simpa only [Nat.pow_one] using Nat.pow_dvd_pow 2 hf.sb_pos
  have he : 2 ^ f.sb % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hm : binadeMagnitude f A % 2 = binadeQuotient f A % 2 := by
    unfold binadeMagnitude
    rw [Nat.add_mod, Nat.mul_mod, he, Nat.mul_zero, Nat.zero_mod, Nat.zero_add,
      Nat.mod_mod_of_dvd _ hd, Nat.mod_mod]
  refine ⟨hm, ?_⟩
  rw [Nat.add_mod, hm, ← Nat.add_mod]

/-- Integer-cast form of the bracket, exactness, and midpoint premises used by the rounding contract. -/
theorem binade_int_key_spec (f : Fmt) (hf : Good f) (A : Nat) (ha : 0 < A) :
    (magKey f (binadeMagnitude f A) : Int) ≤ (A : Int) * (den f : Int) ∧
    (A : Int) * (den f : Int) < (magKey f (binadeMagnitude f A + 1) : Int) ∧
    (binadeResidue f A = 0 ↔ (A : Int) * (den f : Int) = (magKey f (binadeMagnitude f A) : Int)) ∧
    (binadeStep f A < 2 * binadeResidue f A ↔
      (magKey f (binadeMagnitude f A) : Int) + (magKey f (binadeMagnitude f A + 1) : Int) <
        2 * ((A : Int) * (den f : Int))) ∧
    (binadeStep f A = 2 * binadeResidue f A ↔
      (magKey f (binadeMagnitude f A) : Int) + (magKey f (binadeMagnitude f A + 1) : Int) =
        2 * ((A : Int) * (den f : Int))) := by
  have hn := binade_key_spec f hf A ha
  have htwice : (2 : Int) * ((A : Int) * (den f : Int)) = ((2 * (A * den f) : Nat) : Int) := by
    rfl
  rw [htwice]
  simp only [← Int.natCast_mul, ← Int.natCast_add, Int.ofNat_le, Int.ofNat_lt,
    Int.natCast_inj]
  exact hn

end JuliaLean.ChatGPT.Batch4.Group6.FloatBinadeAux

/- Section: FloatIEEE. -/
set_option maxHeartbeats 4000000

namespace JuliaLean.ChatGPT.Batch4.Group6
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1
open FloatConstructAux IEEEOrderAux FloatSelectAux IEEEPackingAux

/-- Validity makes the stored sign agree with the represented integer. -/
theorem floatIEEE_model_sign (x : BigInt) (hx : GMPInput x) :
    isnegative x = decide (x.val < 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [isnegative, decide_eq_true_eq]
  exact (g6valid_sign x hx.1).1

/-- Every nonzero integer in the non-overflow branch has a positive finite exponent field. -/
theorem floatIEEE_exponent_bounds (T : FTy) (L : Nat) (hL : 1 ≤ L)
    (hB : L ≤ T.fmt.bias+1) :
    0 < L-1+T.fmt.bias ∧ L-1+T.fmt.bias < T.fmt.emax := by
  have hg := good_fty T
  have hb := hg.bias_pos
  have he := hg.emax_eq
  omega

theorem floatIEEE_magnitude_bound (T : FTy) (L q : Nat) (hL : 1 ≤ L)
    (hB : L ≤ T.fmt.bias+1) :
    (L-1+T.fmt.bias)*2^T.fmt.sb + q%2^T.fmt.sb < T.fmt.emax*2^T.fmt.sb := by
  have he := (floatIEEE_exponent_bounds T L hL hB).2
  have hr := Nat.mod_lt q (Nat.two_pow_pos T.fmt.sb)
  have hm := Nat.mul_le_mul_right (2^T.fmt.sb) (Nat.succ_le_of_lt he)
  rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hm
  omega

/-- The low encoding bit is the low retained significand bit. -/
theorem floatIEEE_encoding_parity (T : FTy) (E q : Nat) :
    (E*2^T.fmt.sb + q%2^T.fmt.sb)%2 = q%2 := by
  have hs := (good_fty T).sb_pos
  have hp : 2^T.fmt.sb = 2^(T.fmt.sb-1)*2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  rw [hp, Nat.add_mod, Nat.mul_mod, Nat.mul_mod_left, Nat.mul_zero, Nat.zero_mod,
    Nat.zero_add, Nat.mod_mul_left_mod, Nat.mod_mod]

theorem floatIEEE_encoding_successor_parity (T : FTy) (E q : Nat) :
    (E*2^T.fmt.sb + q%2^T.fmt.sb+1)%2 = (q+1)%2 := by
  rw [Nat.add_mod, floatIEEE_encoding_parity, ← Nat.add_mod]

/-- Source packing selects exactly one of the adjacent signed magnitude encodings. -/
theorem floatIEEE_roundInteger_encoded (T : FTy) (negative : Bool) (L A : Nat)
    (r : RoundingMode) (hL : 1 ≤ L) (hB : L ≤ T.fmt.bias+1) :
    let d := 2^(L-(T.fmt.sb+1))
    let q := (A/d)*2^((T.fmt.sb+1)-L)
    let R := A%d
    let E := L-1+T.fmt.bias
    let M := E*2^T.fmt.sb + q%2^T.fmt.sb
    floatWindow_roundInteger T negative L A r =
      if residueIncrement r negative q R d then encode T negative (M+1)
      else encode T negative M := by
  dsimp only
  have he0 := (floatIEEE_exponent_bounds T L hL hB).2
  have he : L-1+T.fmt.bias < 2^T.fmt.eb := by
    have hemax := (good_fty T).emax_succ
    omega
  have hexp : (L : Int)-1+(exponent_bias T).val = ((L-1+T.fmt.bias : Nat) : Int) := by
    rw [exponent_bias_value]
    omega
  let d := 2^(L-(T.fmt.sb+1))
  let q := (A/d)*2^((T.fmt.sb+1)-L)
  let R := A%d
  have hincr :
      (if roundsNearest r then decide (d < 2*R) ||
        (decide (2*R = d) && (if r = .Nearest then decide (q%2 = 1)
          else if r = .NearestTiesAway then true else !negative))
       else roundsAway r negative && decide (R ≠ 0)) = residueIncrement r negative q R d := by
    unfold residueIncrement
    have ht : decide (2*R = d) = decide (d = 2*R) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact eq_comm
    rw [ht]
  unfold floatWindow_roundInteger
  dsimp only
  rw [hexp, hincr]
  rw [ieee754_increment_bits T negative (L-1+T.fmt.bias) (q%2^T.fmt.sb)
    (residueIncrement r negative q R d) he (Nat.mod_lt q (Nat.two_pow_pos _))]
  cases hi : residueIncrement r negative q R d <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero, encode] <;> rfl


open FloatBinadeAux

/-- The normalized source branch satisfies the full global rounding contract. -/
theorem floatIEEE_nonoverflow_correct (T : FTy) (x : BigInt) (r : RoundingMode)
    (hx : GMPInput x) (hn : x.val ≠ 0) (hmax : x.val.natAbs < 2^(T.fmt.bias+1)) :
    ConvFloatChoice r x.val (toFloat T x r) := by
  have hA : 0 < x.val.natAbs := Int.natAbs_pos.mpr hn
  have hL : 1 ≤ x.val.natAbs.log2+1 := by omega
  have hB : x.val.natAbs.log2+1 ≤ T.fmt.bias+1 := by
    have hlog := (Nat.log2_lt (Nat.ne_of_gt hA)).mpr hmax
    omega
  have hb : ((x.val.natAbs.log2+1 : Nat) : Int) ≤ (exponent_max T).val+1 := by
    rw [FloatExtremeAux.source_exponent_max]
    omega
  rw [floatWindow_model_integer T x r hx hn hb, floatIEEE_model_sign x hx,
    floatIEEE_roundInteger_encoded T (decide (x.val<0)) _ _ r hL hB]
  let A := x.val.natAbs
  let s := decide (x.val<0)
  let M := binadeMagnitude T.fmt A
  let q := binadeQuotient T.fmt A
  let R := binadeResidue T.fmt A
  let d := binadeStep T.fmt A
  change ConvFloatChoice r x.val
    (if residueIncrement r s q R d then encode T s (M+1) else encode T s M)
  have hM : M < T.fmt.emax*2^T.fmt.sb :=
    floatIEEE_magnitude_bound T (A.log2+1) q hL hB
  have hMle : M ≤ T.fmt.emax*2^T.fmt.sb := Nat.le_of_lt hM
  have hMnext : M+1 ≤ T.fmt.emax*2^T.fmt.sb := hM
  have hka : key (encode T s M) =
      if x.val < 0 then -(magKey T.fmt M : Int) else (magKey T.fmt M : Int) := by
    simpa only [s, decide_eq_true_eq] using encode_key T s M hMle
  have hkb : key (encode T s (M+1)) =
      if x.val < 0 then -(magKey T.fmt (M+1) : Int) else (magKey T.fmt (M+1) : Int) := by
    simpa only [s, decide_eq_true_eq] using encode_key T s (M+1) hMnext
  have hkeys := binade_int_key_spec T.fmt (good_fty T) A hA
  have hparity := binade_magnitude_parity T.fmt (good_fty T) A
  apply residue_choice x.val (encode T s M) (encode T s (M+1)) M q R d
    (binade_residue_lt T.fmt A) (encode_finite T s M hM)
    (encode_not_nan T s (M+1) hMnext) (encode_parts T s M hMle).1
    (encode_parts T s (M+1) hMnext).1 hka hkb
    hkeys.1 hkeys.2.1 hkeys.2.2.1 hkeys.2.2.2.1 hkeys.2.2.2.2
  · rw [encode_even_bits T s M hMle]
    exact hparity.1
  · rw [encode_even_bits T s (M+1) hMnext]
    exact hparity.2

/-- Every explicit IEEE conversion obeys its exact frozen global rounding contract. -/
theorem BignumsGmpExplicitIeeeConversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.ExplicitIEEEConversionCorrect := by
  intro T x r hx
  by_cases hz : x.val = 0
  · exact floatOutput_zero_correct T x r hx hz
  · by_cases hfar : 2^(T.fmt.bias+1) ≤ x.val.natAbs
    · exact FloatExtremeAux.source_far_choice T x r hx hfar
    · exact floatIEEE_nonoverflow_correct T x r hx hz (Nat.lt_of_not_ge hfar)

theorem BignumsGmpDefaultFloat64Conversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.DefaultFloat64ConversionCorrect :=
  floatOutput64_of_explicit BignumsGmpExplicitIeeeConversion_proven

theorem BignumsGmpDefaultFloat32Conversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.DefaultFloat32ConversionCorrect :=
  floatOutput32_of_explicit BignumsGmpExplicitIeeeConversion_proven

theorem BignumsGmpDefaultFloat16Conversion_proven :
    JuliaLean.Proofs.base.gmp.Round1.DefaultFloat16ConversionCorrect :=
  floatOutput16_of_explicit BignumsGmpExplicitIeeeConversion_proven

end JuliaLean.ChatGPT.Batch4.Group6
end

namespace JuliaLean.Proofs.base.gmp
end JuliaLean.Proofs.base.gmp

section
/- Component: FloatSupport.lean -/

/- Selected float widening facts restated under the required fixed imports.
   Proof derivations follow the supplied float proof file; the new names are local to this group. -/
namespace JuliaLean.ChatGPT.Batch4.Group7.PNFloat
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000

open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
variable {f g : Fmt}

theorem pnf_width_pow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega, Nat.pow_succ, Nat.mul_comm]

theorem pnf_toBits_ofBits {f : Fmt} (v : Nat) : (Fl.ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem pnf_ofBits_toBits {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hv]

theorem pnf_ext_toBits {f : Fmt} {x y : Fl f} (h : x.toBits = y.toBits) : x = y := by
  rw [← pnf_ofBits_toBits x, ← pnf_ofBits_toBits y, h]

theorem pnf_bits_split {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := pnf_width_pow f
    have h3 : x.toBits = x.bits.val := rfl
    omega
  have hW := Nat.two_pow_pos (f.eb + f.sb)
  refine ⟨?_, Nat.mod_lt _ hW⟩
  unfold Fl.signbit Fl.magnitude
  by_cases hs : x.toBits ≥ 2 ^ (f.eb + f.sb)
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_true, ↓reduceIte]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [hs]

theorem pnf_expField_eq {f : Fmt} (x : Fl f) : x.expField = x.magnitude / 2 ^ f.sb := by
  unfold Fl.expField Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem pnf_frac_eq {f : Fmt} (x : Fl f) : x.frac = x.magnitude % 2 ^ f.sb := by
  unfold Fl.frac Fl.magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

structure pnf_Good (f : Fmt) : Prop where
  emax_eq : f.emax = 2 * f.bias + 1
  emax_succ : f.emax + 1 = 2 ^ f.eb
  bias_pos : 1 ≤ f.bias
  sb_pos : 1 ≤ f.sb
  sb_le : f.sb ≤ f.bias

theorem pnf_good_half : (pnf_Good half) := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem pnf_good_single : (pnf_Good single) := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem pnf_good_double : (pnf_Good double) := ⟨by decide, by decide, by decide, by decide, by decide⟩

def pnf_den (f : Fmt) : Nat := 2 ^ (f.bias + f.sb - 1)

theorem pnf_den_pos (f : Fmt) : 0 < (pnf_den f) := Nat.two_pow_pos _

theorem pnf_good_fty (T : FTy) : (pnf_Good T.fmt) := by
  cases T
  · exact pnf_good_half
  · exact pnf_good_single
  · exact pnf_good_double

theorem pnf_pow_mul_eq (m a b c d : Nat) (h : a + b = c + d) : m * 2 ^ a * 2 ^ b = m * 2 ^ c * 2 ^ d := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, h]

def pnf_magKey (f : Fmt) (M : Nat) : Nat :=
  (M % 2 ^ f.sb + if M / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) * 2 ^ (M / 2 ^ f.sb - 1)

def pnf_pack (neg : Bool) (B r : Nat) : Fl f :=
  ofBits ((if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r))

theorem pnf_pack_parts (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (pnf_pack neg B r : Fl f).signbit = neg ∧ (pnf_pack neg B r : Fl f).expField = B ∧
    (pnf_pack neg B r : Fl f).frac = r ∧ (pnf_pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
  have hP := Nat.two_pow_pos f.sb
  have hM : B * 2 ^ f.sb + r < 2 ^ (f.eb + f.sb) := by
    rw [Nat.pow_add]
    have : (B + 1) * 2 ^ f.sb ≤ 2 ^ f.eb * 2 ^ f.sb := Nat.mul_le_mul_right _ hB
    rw [Nat.succ_mul] at this
    omega
  have hw := pnf_width_pow f
  have ht : (pnf_pack neg B r : Fl f).toBits =
      (if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r) := by
    unfold pnf_pack
    rw [pnf_toBits_ofBits, Nat.mod_eq_of_lt]
    rw [hw]
    cases neg <;> simp <;> omega
  have hm : (pnf_pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
    unfold magnitude
    rw [ht]
    cases neg <;> simp [Nat.mod_eq_of_lt hM]
  refine ⟨?_, ?_, ?_, hm⟩
  · unfold signbit
    rw [ht]
    cases neg <;> simp <;> omega
  · rw [pnf_expField_eq, hm, Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [pnf_frac_eq, hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

def pnf_key (x : Fl f) : Int :=
  if x.signbit then -((pnf_magKey f x.magnitude : Nat) : Int) else ((pnf_magKey f x.magnitude : Nat) : Int)

theorem pnf_isnan_of_finite {x : Fl f} (h : x.isfinite = true) : x.isnan = false := by
  simp_all [isfinite, isnan]

theorem pnf_isinf_of_finite {x : Fl f} (h : x.isfinite = true) : x.isinf = false := by
  simp_all [isfinite, isinf]

theorem pnf_toRat_cases (hf : (pnf_Good f)) (x : Fl f) (hx : x.isfinite = true) : ∃ m i j : Nat,
    x.toRat = ((if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int)),
      2 ^ j) ∧
    pnf_magKey f x.magnitude * 2 ^ j = m * 2 ^ i * (pnf_den f) ∧ m < 2 ^ (f.sb + 1) ∧
    (m ≠ 0 → j + 1 ≤ m.log2 + i + f.bias + f.sb ∧ m.log2 + i ≤ j + f.bias) := by
  have hP := Nat.two_pow_pos f.sb
  have hb := hf.bias_pos
  have hs := hf.sb_pos
  have hE := hf.emax_eq
  have hS := hf.emax_succ
  have hM := (pnf_bits_split x).2
  have hfin : x.magnitude / 2 ^ f.sb ≠ f.emax := by
    have := hx
    simp only [isfinite, bne_iff_ne, ne_eq] at this
    rw [pnf_expField_eq] at this
    exact this
  have hdiv : x.magnitude / 2 ^ f.sb < 2 ^ f.eb := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hr := Nat.mod_lt x.magnitude hP
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold toRat pnf_magKey pnf_den
  rw [pnf_expField_eq, pnf_frac_eq]
  simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  generalize x.signbit = s
  generalize x.magnitude / 2 ^ f.sb = e at *
  generalize x.magnitude % 2 ^ f.sb = r at *
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨r, 0, f.bias + f.sb - 1, ?_, ?_, by omega, ?_⟩
    · simp only [↓reduceIte, Nat.add_zero]
      split
      · exfalso; omega
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
    · simp
    · intro hr0
      have : r.log2 < f.sb := (Nat.log2_lt hr0).2 hr
      omega
  · have he0 : e ≠ 0 := by omega
    have hne : r + 2 ^ f.sb ≠ 0 := by omega
    have hl1 : (r + 2 ^ f.sb).log2 < f.sb + 1 := (Nat.log2_lt hne).2 (by omega)
    have hl2 : f.sb ≤ (r + 2 ^ f.sb).log2 := (Nat.le_log2 hne).2 (by omega)
    simp only [he0, ↓reduceIte]
    split
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, e - f.bias - f.sb, 0, ?_, ?_, by omega, fun _ => by omega⟩
      · have ht : ((e : Int) - f.bias - f.sb).toNat = e - f.bias - f.sb := by omega
        rw [ht]
        refine Prod.ext ?_ rfl
        cases s <;> simp [Int.natCast_mul, Int.neg_mul]
      · rw [Nat.mul_one]
        conv => lhs; rw [← Nat.mul_one ((r + 2 ^ f.sb) * 2 ^ (e - 1))]
        rw [show (1 : Nat) = 2 ^ 0 from rfl]
        exact pnf_pow_mul_eq _ _ _ _ _ (by omega)
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, 0, f.bias + f.sb - e, ?_, ?_, by omega, fun _ => by omega⟩
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
      · exact pnf_pow_mul_eq _ _ _ _ _ (by omega)

theorem pnf_toRat_key (hf : (pnf_Good f)) (x : Fl f) (hx : x.isfinite = true) :
    0 < x.toRat.2 ∧ x.toRat.1 * ((pnf_den f) : Int) = (pnf_key x) * (x.toRat.2 : Int) := by
  obtain ⟨m, i, j, hr, hk, -, -⟩ := pnf_toRat_cases hf x hx
  rw [hr]
  refine ⟨Nat.two_pow_pos j, ?_⟩
  unfold pnf_key
  dsimp only
  cases x.signbit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul, ← Int.natCast_mul, hk]

theorem pnf_log2_mul_pow (c i : Nat) (hc : c ≠ 0) : (c * 2 ^ i).log2 = c.log2 + i := by
  have hne : c * 2 ^ i ≠ 0 := Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  apply Nat.le_antisymm
  · have : c * 2 ^ i < 2 ^ (c.log2 + i + 1) := by
      rw [show c.log2 + i + 1 = (c.log2 + 1) + i by omega, Nat.pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos i)).2 Nat.lt_log2_self
    have := (Nat.log2_lt hne).2 this
    omega
  · apply (Nat.le_log2 hne).2
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hc)

theorem pnf_floorLog2Rat_pow (a j : Nat) (ha : a ≠ 0) :
    floorLog2Rat a (2 ^ j) = (a.log2 : Int) - j := by
  have h1 := Nat.log2_self_le ha
  unfold floorLog2Rat
  simp only [Nat.log2_two_pow]
  split
  · rename_i hge
    have : 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat = 2 ^ a.log2 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hc : ¬ a < 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat := by omega
    split
    · contradiction
    · rfl
  · rename_i hlt
    have : 2 ^ a.log2 * 2 ^ (-((a.log2 : Int) - j)).toNat = 2 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have := Nat.mul_le_mul_right (2 ^ (-((a.log2 : Int) - j)).toNat) h1
    have hc : ¬ a * 2 ^ (-((a.log2 : Int) - j)).toNat < 2 ^ j := by omega
    split
    · contradiction
    · rfl

theorem pnf_roundQuotient_exact (q d : Nat) (hd : 0 < d) : roundQuotient (q * d) d = q := by
  unfold roundQuotient
  rw [Nat.mul_div_cancel _ hd, Nat.mul_mod_left]
  dsimp only
  split
  · rename_i h
    simp at h <;> omega
  · rfl

theorem pnf_packRounded_normal (neg : Bool) (q : Nat) (k : Int) (h1 : 2 ^ f.sb ≤ q)
    (h2 : q < 2 ^ (f.sb + 1)) (hk2 : k + f.bias + f.sb < f.emax) :
    (packRounded neg q k : Fl f) = pnf_pack neg (k + f.bias + f.sb).toNat (q - 2 ^ f.sb) := by
  have hP := Nat.two_pow_pos f.sb
  have hq0 : (q == 0) = false := by simp; omega
  have hc : ¬ q ≥ 2 ^ (f.sb + 1) := by omega
  have he : ¬ k + f.bias + f.sb ≥ (f.emax : Int) := by omega
  have hm : ¬ q < 2 ^ f.sb := by omega
  unfold packRounded pnf_pack
  simp only [hq0, hc, he, hm, Bool.false_eq_true, ↓reduceIte]

theorem pnf_sig_bounds (c : Nat) (hc : c ≠ 0) (hc1 : c < 2 ^ (f.sb + 1)) :
    c.log2 ≤ f.sb ∧ 2 ^ f.sb ≤ c * 2 ^ (f.sb - c.log2) ∧
    c * 2 ^ (f.sb - c.log2) < 2 ^ (f.sb + 1) := by
  have hlc : c.log2 ≤ f.sb := by have := (Nat.log2_lt hc).2 hc1; omega
  refine ⟨hlc, ?_, ?_⟩
  · calc 2 ^ f.sb = 2 ^ c.log2 * 2 ^ (f.sb - c.log2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.log2_self_le hc)
  · calc c * 2 ^ (f.sb - c.log2) < 2 ^ (c.log2 + 1) * 2 ^ (f.sb - c.log2) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 Nat.lt_log2_self
      _ = 2 ^ (f.sb + 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega

theorem pnf_roundRat_normal (hf : (pnf_Good f)) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f) =
      pnf_pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := pnf_sig_bounds (f := f) c hc hc1
  have ha : n.natAbs ≠ 0 := by
    rw [hn]
    exact Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  have hn0 : (n == 0) = false := by simp; omega
  have hd : (2 ^ j == 0) = false := by simp
  have hE : floorLog2Rat n.natAbs (2 ^ j) = ((c.log2 + i : Nat) : Int) - j := by
    rw [pnf_floorLog2Rat_pow _ _ ha, hn, pnf_log2_mul_pow c i hc]
  have hb := hf.bias_pos
  have hem := hf.emax_eq
  have hs := hf.sb_pos
  unfold roundRat
  simp only [hd, hn0, Bool.false_eq_true, ↓reduceIte]
  generalize floorLog2Rat n.natAbs (2 ^ j) = e at hE
  split
  · exfalso; omega
  split
  · exfalso; omega
  have hk : max (e - f.sb) (1 - (f.bias : Int) - f.sb) = e - f.sb := by omega
  rw [hk]
  have hpack : ∀ q : Nat, q = c * 2 ^ (f.sb - c.log2) →
      (packRounded (decide (n < 0)) q (e - f.sb) : Fl f) =
        pnf_pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
    intro q hq
    subst hq
    rw [pnf_packRounded_normal _ _ _ hq1 hq2 (by omega)]
    congr 1
    omega
  apply hpack
  by_cases hk0 : e - (f.sb : Int) ≥ 0
  · rw [ite_eq_left_iff.mpr fun h => absurd hk0 h]
    dsimp only
    have h1 : n.natAbs = c * 2 ^ (f.sb - c.log2) * (2 ^ j * 2 ^ (e - f.sb).toNat) := by
      rw [hn, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
      congr 2
      omega
    rw [h1, pnf_roundQuotient_exact _ _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))]
  · rw [ite_eq_right_iff.mpr fun h => absurd h hk0]
    dsimp only
    have h1 : n.natAbs * 2 ^ (-(e - f.sb)).toNat = c * 2 ^ (f.sb - c.log2) * 2 ^ j := by
      rw [hn]
      exact pnf_pow_mul_eq _ _ _ _ _ (by omega)
    rw [h1, pnf_roundQuotient_exact _ _ (Nat.two_pow_pos _)]

theorem pnf_pack_key (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (pnf_key (pnf_pack neg B r : Fl f)) = if neg then
      -(((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int)
      else (((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int) := by
  obtain ⟨hs, he, hfr, -⟩ := pnf_pack_parts (f := f) neg B r hB hr
  unfold pnf_key pnf_magKey
  rw [← pnf_expField_eq, ← pnf_frac_eq, hs, he, hfr]

theorem pnf_roundRat_key (hf : (pnf_Good f)) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f).isfinite = true ∧
    (pnf_key (roundRat n (2 ^ j) z : Fl f)) * ((2 ^ j : Nat) : Int) = n * ((pnf_den f) : Int) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := pnf_sig_bounds (f := f) c hc hc1
  have hem := hf.emax_eq
  have hS := hf.emax_succ
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  have hB : c.log2 + i + f.bias - j < 2 ^ f.eb := by omega
  have hr : c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb < 2 ^ f.sb := by
    generalize c * 2 ^ (f.sb - c.log2) = q at hq1 hq2 ⊢
    omega
  rw [pnf_roundRat_normal hf n c i j z hn hc0 hc1 hlo hhi]
  obtain ⟨-, he, -, -⟩ := pnf_pack_parts (f := f) (decide (n < 0)) _ _ hB hr
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  have hnz : (if c.log2 + i + f.bias - j = 0 then 0 else 2 ^ f.sb) = 2 ^ f.sb :=
    ite_eq_right_iff.mpr (by omega)
  rw [pnf_pack_key _ _ _ hB hr, hnz, Nat.sub_add_cancel hq1]
  have hpow : c * 2 ^ (f.sb - c.log2) * 2 ^ (c.log2 + i + f.bias - j - 1) * 2 ^ j =
      c * 2 ^ i * (pnf_den f) := by
    unfold pnf_den
    simp only [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rcases Int.lt_or_le n 0 with hneg | hpos
  · have hn' : n = -((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_true hneg, ↓reduceIte]
    rw [hn', Int.neg_mul, Int.neg_mul, ← Int.natCast_mul, ← Int.natCast_mul, hpow]
  · have hn' : n = ((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_false (Int.not_lt.2 hpos), Bool.false_eq_true, ↓reduceIte]
    rw [hn', ← Int.natCast_mul, ← Int.natCast_mul, hpow]

theorem pnf_zero_spec (hf : (pnf_Good f)) (s : Bool) :
    (zero s : Fl f).isfinite = true ∧ (pnf_key (zero s : Fl f)) = 0 := by
  have hz : (zero s : Fl f) = pnf_pack s 0 0 := by simp [zero, pnf_pack]
  have hS := hf.emax_succ
  have hE := hf.emax_eq
  obtain ⟨-, he, -, -⟩ := pnf_pack_parts (f := f) s 0 0 (by omega) (Nat.two_pow_pos _)
  rw [hz]
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  rw [pnf_pack_key _ _ _ (by omega) (Nat.two_pow_pos _)]
  cases s <;> simp

theorem pnf_convert_widen_key (hf : (pnf_Good f)) (hg : (pnf_Good g)) (hne : (g == f) = false)
    (hsb : f.sb ≤ g.sb) (hbias : f.bias + f.sb ≤ g.bias) (x : Fl f) :
    (convert x : Fl g).isnan = x.isnan ∧
    (convert x : Fl g).isinf = x.isinf ∧
    (convert x : Fl g).isfinite = x.isfinite ∧
    (x.isinf = true → (convert x : Fl g).signbit = x.signbit) ∧
    (x.isfinite = true →
      (pnf_key (convert x : Fl g)) * ((pnf_den f) : Int) = (pnf_key x) * ((pnf_den g) : Int) ∧
      (convert x : Fl g).toRat.1 * (x.toRat.2 : Int) = x.toRat.1 * ((convert x : Fl g).toRat.2 : Int)) := by
  have hgS := hg.emax_succ
  have hgE := hg.emax_eq
  have hfE := hf.emax_eq
  have hPg := Nat.two_pow_pos g.sb
  have hDf : (0 : Int) < (pnf_den f) := by exact_mod_cast (pnf_den_pos f)
  have hDg : (0 : Int) < (pnf_den g) := by exact_mod_cast (pnf_den_pos g)
  unfold convert
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hn : x.isnan
  · cases hi : x.isinf
    · have hfin : x.isfinite = true := by simp_all [isnan, isinf, isfinite]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hrat_x := (pnf_toRat_key hf x hfin).2
      obtain ⟨m, i, j, hr, hk, hm, hrange⟩ := pnf_toRat_cases hf x hfin
      have hkey := hrat_x
      rw [hr] at hkey
      dsimp only at hkey
      have hfin_scale :
          (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g).isfinite = true ∧
          (pnf_key (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g)) * ((pnf_den f) : Int) = (pnf_key x) * ((pnf_den g) : Int) := by
        rw [hr]
        dsimp only
        by_cases hm0 : m = 0
        · subst hm0
          have hz : (roundRat (if x.signbit then -((0 * 2 ^ i : Nat) : Int)
              else ((0 * 2 ^ i : Nat) : Int)) (2 ^ j) x.signbit : Fl g) = zero x.signbit := by
            cases x.signbit <;> simp [roundRat]
          rw [hz]
          obtain ⟨hz1, hz2⟩ := pnf_zero_spec hg x.signbit
          have hkx : (pnf_key x) = 0 := by
            have h2 : ((2 ^ j : Nat) : Int) ≠ 0 := by have := Nat.two_pow_pos j; omega
            have h3 : (pnf_key x) * ((2 ^ j : Nat) : Int) = 0 := by
              rw [← hkey]; cases x.signbit <;> simp
            exact (Int.mul_eq_zero.1 h3).resolve_right h2
          exact ⟨hz1, by rw [hz2, hkx]; simp⟩
        · obtain ⟨hlo, hhi⟩ := hrange hm0
          have hn' : (if x.signbit then -((m * 2 ^ i : Nat) : Int)
              else ((m * 2 ^ i : Nat) : Int)).natAbs = m * 2 ^ i := by
            cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg,
              Int.natAbs_natCast]
          have hm1 : m < 2 ^ (g.sb + 1) :=
            Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
          obtain ⟨h1, h2⟩ := pnf_roundRat_key (f := g) hg _ m i j x.signbit hn' (by omega) hm1
            (by omega) (by omega)
          have hj : (0 : Int) < ((2 ^ j : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos j
          refine ⟨h1, ?_⟩
          generalize (if x.signbit then -((m * 2 ^ i : Nat) : Int)
            else ((m * 2 ^ i : Nat) : Int)) = N at h2 hkey
          generalize (pnf_key (roundRat N (2 ^ j) x.signbit : Fl g)) = K at h2
          apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hj)
          calc K * ((pnf_den f) : Int) * ((2 ^ j : Nat) : Int)
              = K * ((2 ^ j : Nat) : Int) * ((pnf_den f) : Int) := by rw [Int.mul_right_comm]
            _ = N * ((pnf_den g) : Int) * ((pnf_den f) : Int) := by rw [h2]
            _ = N * ((pnf_den f) : Int) * ((pnf_den g) : Int) := by rw [Int.mul_right_comm]
            _ = (pnf_key x) * ((2 ^ j : Nat) : Int) * ((pnf_den g) : Int) := by rw [hkey]
            _ = (pnf_key x) * ((pnf_den g) : Int) * ((2 ^ j : Nat) : Int) := by rw [Int.mul_right_comm]
      obtain ⟨hg_fin, hg_scale⟩ := hfin_scale
      generalize (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g) = w at hg_fin hg_scale ⊢
      have hrat_w := (pnf_toRat_key hg w hg_fin).2
      refine ⟨pnf_isnan_of_finite hg_fin, pnf_isinf_of_finite hg_fin, by rw [hg_fin, hfin],
        fun h => False.elim h, fun _ => ⟨hg_scale, ?_⟩⟩
      apply Int.eq_of_mul_eq_mul_right (by omega : ((pnf_den g) : Int) ≠ 0)
      apply Int.eq_of_mul_eq_mul_right (by omega : ((pnf_den f) : Int) ≠ 0)
      have hstep1 : (w.toRat.1 * ((pnf_den g) : Int)) * (x.toRat.2 : Int) * ((pnf_den f) : Int) =
          ((pnf_key w) * ((pnf_den f) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by
        rw [hrat_w, Int.mul_right_comm ((pnf_key w) * (w.toRat.2 : Int)) (x.toRat.2 : Int) ((pnf_den f) : Int),
          Int.mul_right_comm (pnf_key w) (w.toRat.2 : Int) ((pnf_den f) : Int)]
      have hstep2 : (x.toRat.1 * ((pnf_den f) : Int)) * (w.toRat.2 : Int) * ((pnf_den g) : Int) =
          ((pnf_key x) * ((pnf_den g) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by
        rw [hrat_x, Int.mul_right_comm ((pnf_key x) * (x.toRat.2 : Int)) (w.toRat.2 : Int) ((pnf_den g) : Int),
          Int.mul_right_comm (pnf_key x) (x.toRat.2 : Int) ((pnf_den g) : Int),
          Int.mul_right_comm ((pnf_key x) * ((pnf_den g) : Int)) (x.toRat.2 : Int) (w.toRat.2 : Int)]
      calc w.toRat.1 * (x.toRat.2 : Int) * ((pnf_den g) : Int) * ((pnf_den f) : Int)
          = (w.toRat.1 * ((pnf_den g) : Int)) * (x.toRat.2 : Int) * ((pnf_den f) : Int) := by
            rw [Int.mul_right_comm w.toRat.1 (x.toRat.2 : Int) ((pnf_den g) : Int)]
        _ = ((pnf_key w) * ((pnf_den f) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := hstep1
        _ = ((pnf_key x) * ((pnf_den g) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by rw [hg_scale]
        _ = (x.toRat.1 * ((pnf_den f) : Int)) * (w.toRat.2 : Int) * ((pnf_den g) : Int) := hstep2.symm
        _ = x.toRat.1 * (w.toRat.2 : Int) * ((pnf_den g) : Int) * ((pnf_den f) : Int) := by
            rw [Int.mul_right_comm x.toRat.1 ((pnf_den f) : Int) (w.toRat.2 : Int),
              Int.mul_right_comm (x.toRat.1 * (w.toRat.2 : Int)) ((pnf_den f) : Int) ((pnf_den g) : Int)]
    · have hinf : (inf x.signbit : Fl g) = pnf_pack x.signbit g.emax 0 := by simp [inf, pnf_pack]
      obtain ⟨hs, he, hfr, -⟩ := pnf_pack_parts (f := g) x.signbit g.emax 0 (by omega) hPg
      simp only [Bool.false_eq_true, ↓reduceIte, hinf]
      have hpn : (pnf_pack x.signbit g.emax 0 : Fl g).isnan = false := by unfold isnan; rw [he, hfr]; simp
      have hpi : (pnf_pack x.signbit g.emax 0 : Fl g).isinf = true := by unfold isinf; rw [he, hfr]; simp
      have hpf : (pnf_pack x.signbit g.emax 0 : Fl g).isfinite = false := by unfold isfinite; rw [he]; simp
      have hxf : x.isfinite = false := by
        unfold isinf at hi; unfold isfinite; simp only [Bool.and_eq_true, beq_iff_eq] at hi; simp [hi.1]
      exact ⟨hpn, hpi, by rw [hpf, hxf], fun _ => hs, fun h => by rw [hxf] at h; exact Bool.noConfusion h⟩
  · have hfr : x.frac < 2 ^ f.sb := by rw [pnf_frac_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpay : x.frac * 2 ^ (g.sb - f.sb) < 2 ^ g.sb := by
      calc x.frac * 2 ^ (g.sb - f.sb) < 2 ^ f.sb * 2 ^ (g.sb - f.sb) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hfr
        _ = 2 ^ g.sb := by rw [← Nat.pow_add]; congr 1; omega
    have hhalf : 2 ^ (g.sb - 1) < 2 ^ g.sb :=
      Nat.pow_lt_pow_right (by decide) (by have := hg.sb_pos; omega)
    have hL : Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1)) < 2 ^ g.sb :=
      Nat.or_lt_two_pow hpay hhalf
    have hpk : (ofBits ((if x.signbit then 2 ^ (g.eb + g.sb) else 0) + g.emax * 2 ^ g.sb +
        Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) : Fl g) =
        pnf_pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) := by
      unfold pnf_pack; rw [Nat.add_assoc]
    obtain ⟨-, he, hfr', -⟩ := pnf_pack_parts (f := g) x.signbit g.emax _ (by omega) hL
    simp only [↓reduceIte, ite_eq_left_iff.mpr fun h => absurd hsb h, hpk]
    have hpn : (pnf_pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isnan = true := by unfold isnan; rw [he, hfr']; simp
    have hpi : (pnf_pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isinf = false := by unfold isinf; rw [he, hfr']; simp
    have hpf : (pnf_pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isfinite = false := by unfold isfinite; rw [he]; simp
    have hxi : x.isinf = false := by
      unfold isnan at hn; unfold isinf; simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hn; simp [hn.1, hn.2]
    have hxf : x.isfinite = false := by
      unfold isnan at hn; unfold isfinite; simp only [Bool.and_eq_true, beq_iff_eq] at hn; simp [hn.1]
    exact ⟨hpn, by rw [hpi, hxi], by rw [hpf, hxf],
      fun h => by rw [hxi] at h; exact Bool.noConfusion h,
      fun h => by rw [hxf] at h; exact Bool.noConfusion h⟩

theorem pnf_okOf_eq {ε α : Type} {r : Except ε α} {h : ∀ e, r ≠ .error e} {a : α} (hr : r = .ok a) :
    int.okOf r h = a := by
  subst hr; rfl

theorem pnf_convertFloat_eq (T : FTy) {S : FTy} (x : FV S) :
    convertFloat T x = Fl.convert x := by
  cases T <;> cases S
  · simp [convertFloat, Fl.convert, pnf_ofBits_toBits]
  · simp only [convertFloat, Float16_Float32, fptrunc]
    exact pnf_okOf_eq rfl
  · simp only [convertFloat, Float16_Float64, fptrunc]
    exact pnf_okOf_eq rfl
  · simp only [convertFloat, Float32_Float16, fpext]
    exact pnf_okOf_eq rfl
  · simp [convertFloat, Fl.convert, pnf_ofBits_toBits]
  · simp only [convertFloat, Float32_Float64, fptrunc]
    exact pnf_okOf_eq rfl
  · simp only [convertFloat, Float64_Float16, fpext]
    exact pnf_okOf_eq rfl
  · simp only [convertFloat, Float64_Float32, fpext]
    exact pnf_okOf_eq rfl
  · simp [convertFloat, Fl.convert, pnf_ofBits_toBits]

theorem pnf_widen64_facts {T : FTy} (x : FV T) :
    (convertFloat .f64 x).isnan = x.isnan ∧
    (convertFloat .f64 x).isinf = x.isinf ∧
    (convertFloat .f64 x).isfinite = x.isfinite ∧
    (x.isinf = true → (convertFloat .f64 x).signbit = x.signbit) ∧
    (x.isfinite = true →
      (convertFloat .f64 x).toRat.1 * (x.toRat.2 : Int) =
        x.toRat.1 * ((convertFloat .f64 x).toRat.2 : Int)) := by
  cases T with
  | f16 =>
    rw [pnf_convertFloat_eq]
    have h := pnf_convert_widen_key pnf_good_half pnf_good_double (by decide) (by decide) (by decide) x
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun hx => (h.2.2.2.2 hx).2⟩
  | f32 =>
    rw [pnf_convertFloat_eq]
    have h := pnf_convert_widen_key pnf_good_single pnf_good_double (by decide) (by decide) (by decide) x
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun hx => (h.2.2.2.2 hx).2⟩
  | f64 =>
    exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem pnf_finite_den_pos {T : FTy} (x : FV T) (hx : x.isfinite = true) :
    0 < x.toRat.2 := (pnf_toRat_key (pnf_good_fty T) x hx).1

end JuliaLean.ChatGPT.Batch4.Group7.PNFloat


/- Component: ClassificationChecked.lean -/

section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem cl_wrap_sgn (n : Int) : (JInt.wrap .i64 (sgn n)).val = sgn n := by
  unfold sgn
  split
  · rfl
  · split <;> rfl

theorem cl_sgn_sgn (n : Int) : sgn (sgn n) = sgn n := by
  by_cases hn : n < 0
  · simp only [sgn, hn, ite_eq_left] <;> rfl
  · by_cases hp : 0 < n
    · simp only [sgn, hn, hp, ite_false, ite_true] <;> rfl
    · simp only [sgn, hn, hp, ite_false] <;> rfl

theorem cl_cmp_val (x y : BigInt) :
    (JuliaLean.base.gmp.cmp x y).val = sgn (x.val - y.val) := by
  unfold JuliaLean.base.gmp.cmp MPZ.cmp
  rw [cl_wrap_sgn, cl_wrap_sgn, cl_sgn_sgn]

theorem cl_cmp_unsigned_val (x : BigInt) (y : Culong) :
    (cmpUnsigned x y).val = sgn (x.val - y.val) := by
  unfold cmpUnsigned MPZ.cmpUi
  rw [cl_wrap_sgn, cl_wrap_sgn, cl_sgn_sgn]

theorem cl_valid_sign (x : BigInt) (hx : Valid x) :
    (x.size.val < 0 ↔ x.val < 0) ∧ (0 < x.size.val ↔ 0 < x.val) := by
  have hv := hx.2.2.1
  have hz := hx.2.2.2.1
  by_cases hn : x.size.val < 0
  · rw [ite_eq_left hn] at hv
    have hne : x.val ≠ 0 := by
      intro h
      have := hz.mpr h
      omega
    constructor <;> omega
  · rw [ite_eq_right hn] at hv
    constructor <;> omega

theorem BignumsGmpZeroClassification_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntZeroClassification := by
  intro x hx
  show decide (x.size.val = 0) = true ↔ x.val = 0
  rw [decide_eq_true_eq]
  exact hx.1.2.2.2.1

theorem BignumsGmpOneClassification_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntOneClassification := by
  intro x _hx
  unfold isone
  rw [decide_eq_true_eq, cl_cmp_unsigned_val]
  change sgn (x.val - 1) = 0 ↔ x.val = 1
  unfold sgn
  split
  · omega
  · split <;> omega

theorem BignumsGmpOrderExact_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntOrderExact := by
  intro x y _hx _hy
  unfold lessEqual less
  rw [decide_eq_true_eq, decide_eq_true_eq, cl_cmp_val]
  unfold sgn
  split
  · constructor <;> omega
  · split <;> constructor <;> omega

theorem BignumsGmpSignClassification_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntSignClassification := by
  intro x hx
  obtain ⟨hn, hp⟩ := cl_valid_sign x hx.1
  exact ⟨by simpa only [isnegative, decide_eq_true_eq] using hn,
    by simpa only [ispositive, decide_eq_true_eq] using hp,
    by simpa only [signbit, isnegative, decide_eq_true_eq] using hn⟩

theorem cl_neg_value (x : BigInt) : (neg x).val = -x.val := rfl

theorem BignumsGmpCheckedAddition_proven : JuliaLean.Proofs.base.gmp.Round1.CheckedBigIntAddition := by
  intro x y _hx _hy
  refine ⟨writeValue (ofInt 0 (64 * (1 + max x.size.val.natAbs y.size.val.natAbs)))
    (x.val + y.val), ?_, ?_, ?_⟩
  · rfl
  · change x.val + y.val - y.val = x.val
    omega
  · intro t
    change x.val + y.val ≤ t ↔ x.val ≤ t - y.val
    omega

theorem BignumsGmpCheckedSubtraction_proven : JuliaLean.Proofs.base.gmp.Round1.CheckedBigIntSubtraction := by
  intro x y _hx _hy
  refine ⟨writeValue (ofInt 0 (64 * (1 + max x.size.val.natAbs y.size.val.natAbs)))
    (x.val - y.val), ?_, ?_, ?_⟩
  · rfl
  · change x.val - y.val + y.val = x.val
    omega
  · intro t
    change x.val - y.val ≤ t ↔ x.val ≤ t + y.val
    omega

theorem cl_limb_wrap_value (n : Nat) (hn : n < 2^64) :
    (JInt.wrap .u64 (Int.ofNat n)).val = Int.ofNat n := by
  change wrapInt .u64 (n : Int) = n
  apply wrapInt_of_inRange
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ (2 : Int)^64 - 1
  omega

theorem cl_limb_wrap_nat (n : Nat) (hn : n < 2^64) :
    (JInt.wrap .u64 (Int.ofNat n)).val.toNat = n := by
  rw [cl_limb_wrap_value n hn]
  rfl

theorem cl_limb_range (l : Limb) : 0 ≤ l.val ∧ l.val < (2 : Int)^64 := by
  have h := l.property
  change 0 ≤ l.val ∧ l.val ≤ (2 : Int)^64 - 1 at h
  omega

theorem cl_magnitude_bound (ls : List Limb) : limbMagnitude ls < (2^64)^ls.length := by
  induction ls with
  | nil => decide
  | cons l ls ih =>
    have hl := cl_limb_range l
    rw [limbMagnitude, List.length_cons, Nat.pow_succ (2^64) ls.length]
    omega

theorem cl_input_magnitude (x : BigInt) (hx : Valid x) :
    x.val.natAbs = limbMagnitude (x.d.take x.size.val.natAbs) := by
  rw [hx.2.2.1]
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

theorem cl_input_magnitude_bound (x : BigInt) (hx : Valid x) :
    x.val.natAbs < (2^64)^x.size.val.natAbs := by
  rw [cl_input_magnitude x hx]
  have h := cl_magnitude_bound (x.d.take x.size.val.natAbs)
  rw [List.length_take_of_le hx.1] at h
  exact h

theorem cl_magnitude_limbs (n : Nat) : limbMagnitude (limbsOfNat n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst n
      rw [limbsOfNat]
      rfl
    · rw [limbsOfNat, dite_eq_right hn, limbMagnitude]
      rw [cl_limb_wrap_nat (n % 2^64) (Nat.mod_lt _ (by decide))]
      rw [ih (n / 2^64) (Nat.div_lt_self (by omega) (by decide))]
      omega

theorem cl_limbs_ne_nil (n : Nat) (hn : n ≠ 0) : limbsOfNat n ≠ [] := by
  rw [limbsOfNat, dite_eq_right hn]
  exact List.cons_ne_nil _ _

theorem cl_limbs_length_zero (n : Nat) : (limbsOfNat n).length = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hh := cl_magnitude_limbs n
    rw [List.eq_nil_of_length_eq_zero h] at hh
    exact hh.symm
  · intro h
    subst n
    rw [limbsOfNat]
    rfl

theorem cl_limbs_last_nonzero (n : Nat) (hn : n ≠ 0) :
    ((limbsOfNat n).getLast?.getD (JInt.wrap .u64 0)).val ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [limbsOfNat, dite_eq_right hn]
    by_cases hq : n / 2^64 = 0
    · rw [hq, limbsOfNat]
      simp only [dite_true, List.getLast?_singleton, Option.getD_some]
      rw [cl_limb_wrap_value (n % 2^64) (Nat.mod_lt _ (by decide)), Int.ofNat_eq_natCast]
      omega
    · rw [List.getLast?_cons_of_ne_nil (cl_limbs_ne_nil _ hq)]
      exact ih (n / 2^64) (Nat.div_lt_self (by omega) (by decide)) hq

theorem cl_limbs_magnitude_length (ls : List Limb) :
    (limbsOfNat (limbMagnitude ls)).length ≤ ls.length := by
  induction ls with
  | nil =>
    rw [limbMagnitude, limbsOfNat]
    exact Nat.le_refl _
  | cons l ls ih =>
    by_cases hz : limbMagnitude (l :: ls) = 0
    · rw [hz, limbsOfNat]
      exact Nat.zero_le _
    · have hl := cl_limb_range l
      have hd : limbMagnitude (l :: ls) / 2^64 = limbMagnitude ls := by
        change (l.val.toNat + 2^64 * limbMagnitude ls) / 2^64 = limbMagnitude ls
        omega
      rw [limbsOfNat, dite_eq_right hz, List.length_cons, hd, List.length_cons]
      omega

theorem cl_input_limbs_length (x : BigInt) (hx : GMPInput x) :
    (limbsOfNat x.val.natAbs).length < 2^31 := by
  have hv := hx.1.2.2.1
  have habs : x.val.natAbs = limbMagnitude (x.d.take x.size.val.natAbs) := by
    rw [hv]
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
  rw [habs]
  have hlen := cl_limbs_magnitude_length (x.d.take x.size.val.natAbs)
  have ht := List.length_take_le x.size.val.natAbs x.d
  have ha := hx.1.2.1
  have hbound := x.alloc.property
  change -(2 : Int)^31 ≤ x.alloc.val ∧ x.alloc.val ≤ (2 : Int)^31 - 1 at hbound
  omega

theorem cl_ofInt_alloc (n : Int) (h : (limbsOfNat n.natAbs).length < 2^31) :
    (ofInt n).alloc.val = (limbsOfNat n.natAbs).length := by
  change wrapInt .i32 ((max (limbsOfNat n.natAbs).length ((0 + 63) / 64) : Nat) : Int) = _
  simp only [Nat.zero_add, Nat.reduceDiv, Nat.max_zero]
  apply wrapInt_of_inRange
  change -(2 : Int)^31 ≤ ((limbsOfNat n.natAbs).length : Int) ∧
    ((limbsOfNat n.natAbs).length : Int) ≤ (2 : Int)^31 - 1
  omega

theorem cl_ofInt_size (n : Int) (h : (limbsOfNat n.natAbs).length < 2^31) :
    (ofInt n).size.val =
      if n < 0 then -((limbsOfNat n.natAbs).length : Int) else (limbsOfNat n.natAbs).length := by
  change wrapInt .i32 (if n < 0 then -((limbsOfNat n.natAbs).length : Int) else
    (limbsOfNat n.natAbs).length) = _
  apply wrapInt_of_inRange
  change -(2 : Int)^31 ≤ _ ∧ _ ≤ (2 : Int)^31 - 1
  split <;> omega

theorem cl_ofInt_valid (n : Int) (h : (limbsOfNat n.natAbs).length < 2^31) :
    Valid (ofInt n) := by
  have hz := cl_limbs_length_zero n.natAbs
  have hs : (ofInt n).size.val.natAbs = (limbsOfNat n.natAbs).length := by
    rw [cl_ofInt_size n h]
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
  have hsz : (ofInt n).size.val = 0 ↔ n = 0 := by
    rw [cl_ofInt_size n h]
    split <;> omega
  have hsn : (ofInt n).size.val < 0 ↔ n < 0 := by
    rw [cl_ofInt_size n h]
    split <;> omega
  unfold Valid
  change (ofInt n).size.val.natAbs ≤ (limbsOfNat n.natAbs).length ∧
    (ofInt n).size.val.natAbs ≤ (ofInt n).alloc.val.toNat ∧
    n = (if (ofInt n).size.val < 0 then
      -(limbMagnitude ((limbsOfNat n.natAbs).take (ofInt n).size.val.natAbs) : Int)
      else (limbMagnitude ((limbsOfNat n.natAbs).take (ofInt n).size.val.natAbs) : Int)) ∧
    ((ofInt n).size.val = 0 ↔ n = 0) ∧
    ((ofInt n).size.val ≠ 0 →
      (((limbsOfNat n.natAbs)[(ofInt n).size.val.natAbs - 1]?).getD (JInt.wrap .u64 0)).val ≠ 0)
  rw [hs, cl_ofInt_alloc n h, List.take_length, cl_magnitude_limbs]
  refine ⟨Nat.le_refl _, Nat.le_refl _, ?_, hsz, ?_⟩
  · split <;> omega
  · intro hne
    rw [← List.getLast?_eq_getElem?]
    apply cl_limbs_last_nonzero
    intro hn
    have : n = 0 := by omega
    exact hne (hsz.mpr this)

theorem cl_limbs_zero : limbsOfNat 0 = [] := by
  rw [limbsOfNat]
  exact dite_eq_left rfl

theorem cl_limbs_one_length : (limbsOfNat 1).length = 1 := by
  rw [limbsOfNat, dite_eq_right (by decide : (1 : Nat) ≠ 0)]
  have h : (1 : Nat) / 2^64 = 0 := by decide
  rw [h, cl_limbs_zero]
  rfl

theorem cl_init_alloc : initBigInt.alloc.val = 0 := by
  change wrapInt .i32 (Int.ofNat (max (limbsOfNat 0).length 0)) = 0
  rw [cl_limbs_zero]
  rfl

theorem cl_write_init_valid (n : Int) (h : (limbsOfNat n.natAbs).length < 2^31) :
    Valid (writeValue initBigInt n) := by
  have ha := cl_ofInt_alloc n h
  have hz : initBigInt.alloc.val = 0 := cl_init_alloc
  have he : writeValue initBigInt n = ofInt n := by
    unfold writeValue
    have hw : JInt.wrap .i32 (max initBigInt.alloc.val (ofInt n).alloc.val) = (ofInt n).alloc := by
      apply Subtype.ext
      change wrapInt .i32 (max initBigInt.alloc.val (ofInt n).alloc.val) = _
      rw [hz, Int.max_eq_right (by omega)]
      exact wrapInt_of_inRange _ _ (ofInt n).alloc.property
    dsimp only
    rw [hw]
  rw [he]
  exact cl_ofInt_valid n h

theorem cl_neg_valid (x : BigInt) (hx : GMPInput x) : Valid (neg x) := by
  apply cl_write_init_valid
  rw [Int.natAbs_neg]
  exact cl_input_limbs_length x hx

theorem cl_valid_one : Valid (ofInt 1) := by
  apply cl_ofInt_valid
  change (limbsOfNat 1).length < 2^31
  rw [cl_limbs_one_length]
  decide
theorem cl_valid_neg_one : Valid (neg (ofInt 1)) := by
  apply cl_write_init_valid
  change (limbsOfNat 1).length < 2^31
  rw [cl_limbs_one_length]
  decide

theorem BignumsGmpSignValue_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntSignValue := by
  intro x hx
  obtain ⟨hn, hp⟩ := cl_valid_sign x hx.1
  show Valid (sign x) ∧ _
  unfold sign isnegative ispositive
  by_cases hneg : x.size.val < 0
  · simp only [hneg, decide_true, eq_self_iff_true, ite_true]
    refine ⟨cl_valid_neg_one, ?_, ?_, ?_⟩
    all_goals
      dsimp only [neg, writeValue, ofInt]
      have := hn.mp hneg
      omega
  · simp only [hneg, decide_false, Bool.false_eq_true, ite_false]
    by_cases hpos : 0 < x.size.val
    · simp only [hpos, decide_true, eq_self_iff_true, ite_true]
      refine ⟨cl_valid_one, ?_, ?_, ?_⟩
      all_goals
        dsimp only [ofInt]
        have := hp.mp hpos
        omega
    · simp only [hpos, decide_false, Bool.false_eq_true, ite_false]
      have hz : x.val = 0 := hx.1.2.2.2.1.mp (by omega)
      refine ⟨hx.1, ?_, ?_, ?_⟩
      all_goals first | exact True.intro | omega

theorem BignumsGmpFlipsignExact_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntFlipSignExact := by
  intro x y hx hy
  obtain ⟨hn, _hp⟩ := cl_valid_sign y hy.1
  show Valid (flipsign x y) ∧ _
  unfold flipsign signbit isnegative
  by_cases hyneg : y.size.val < 0
  · simp only [hyneg, decide_true, eq_self_iff_true, ite_true, hn.mp hyneg]
    exact ⟨cl_neg_valid x hx, by change -x.val + x.val = 0; omega⟩
  · have hyval : ¬ y.val < 0 := fun h => hyneg (hn.mpr h)
    simp only [hyneg, decide_false, Bool.false_eq_true, ite_false, hyval]
    exact ⟨hx.1, True.intro⟩

theorem BignumsGmpCheckedAbsolute_proven : JuliaLean.Proofs.base.gmp.Round1.CheckedBigIntAbsolute := by
  intro x hx
  obtain ⟨hn, _hp⟩ := cl_valid_sign x hx.1
  show Valid (checkedAbs x) ∧ _
  unfold checkedAbs isnegative
  by_cases hxneg : x.size.val < 0
  · simp only [hxneg, decide_true, eq_self_iff_true, ite_true]
    refine ⟨cl_neg_valid x hx, ?_, ?_⟩
    · change 0 ≤ -x.val
      have := hn.mp hxneg
      omega
    · change -x.val * -x.val = x.val * x.val
      exact Int.neg_mul_neg _ _
  · simp only [hxneg, decide_false, Bool.false_eq_true, ite_false]
    refine ⟨hx.1, ?_, True.intro⟩
    have hyval : ¬ x.val < 0 := fun h => hxneg (hn.mpr h)
    omega

theorem BignumsGmpCheckedNegation_proven : JuliaLean.Proofs.base.gmp.Round1.CheckedBigIntNegation := by
  intro x hx
  refine ⟨neg x, rfl, cl_neg_valid x hx, ?_⟩
  change -x.val + x.val = 0
  omega

end JuliaLean.ChatGPT.Batch4.Group7


namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1

theorem cl_ieee_nan_properties {T : FTy} (f : FV T) (h : f.isnan = true) :
    f.isinf = false ∧ f.isfinite = false := by
  simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  constructor
  · simp only [Fl.isinf, h.1, beq_self_eq_true, Bool.true_and,
      beq_eq_false_iff_ne]
    exact h.2
  · simp only [Fl.isfinite, h.1, bne_self_eq_false]

theorem cl_ieee_inf_properties {T : FTy} (f : FV T) (h : f.isinf = true) :
    f.isnan = false ∧ f.isfinite = false := by
  simp only [Fl.isinf, Bool.and_eq_true, beq_iff_eq] at h
  simp only [Fl.isnan, Fl.isfinite, h.1, h.2, beq_self_eq_true, bne_self_eq_false,
    Bool.and_false, and_self]

theorem cl_ieee_finite_of_not_nan_inf {T : FTy} (f : FV T)
    (hn : f.isnan = false) (hi : f.isinf = false) : f.isfinite = true := by
  by_cases he : f.expField = T.fmt.emax
  · by_cases hf : f.frac = 0
    · have : f.isinf = true := by simp only [Fl.isinf, he, hf, beq_self_eq_true, Bool.and_self]
      rw [this] at hi
      contradiction
    · have : f.isnan = true := by
        simp only [Fl.isnan, he, beq_self_eq_true, Bool.true_and, bne_iff_ne]
        exact hf
      rw [this] at hn
      contradiction
  · simpa only [Fl.isfinite, bne_iff_ne] using he

end JuliaLean.ChatGPT.Batch4.Group7

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1

-- This exact Float64 specialization is useful independently of the widening step.
theorem cl_ieee64_cmp (x : BigInt) (f : FV .f64) :
    (cmpFloat x f).val =
      if f.isnan then -1 else if f.isinf then (if f.signbit then 1 else -1)
        else sgn (x.val * (f.toRat.2 : Int) - f.toRat.1) := by
  cases hn : f.isnan
  · simp only [cmpFloat, hn, Bool.false_eq_true, ite_false, convertFloat]
    rw [cl_wrap_sgn]
    unfold MPZ.cmpD
    cases hi : f.isinf
    · simp only [hi, Bool.false_eq_true, ite_false]
      rw [cl_wrap_sgn, cl_sgn_sgn]
    · simp only [hi, eq_self_iff_true, ite_true]
      cases hs : f.signbit <;> rfl
  · simp only [cmpFloat, hn, eq_self_iff_true, ite_true] <;> rfl

theorem cl_ieee64_order (x : BigInt) (f : FV .f64) :
    (lessEqualFloat x f = true ↔ TailIntLEFloat x.val f) ∧
    (floatLessEqual f x = true ↔ TailFloatLEInt f x.val) ∧
    (lessFloat x f = true ↔ TailIntLTFloat x.val f) ∧
    (floatLess f x = true ↔ TailFloatLTInt f x.val) := by
  cases hn : f.isnan
  · cases hi : f.isinf
    · have hf := cl_ieee_finite_of_not_nan_inf f hn hi
      simp only [lessEqualFloat, floatLessEqual, lessFloat, floatLess, hn,
        Bool.false_eq_true, ite_false, decide_eq_true_eq, cl_ieee64_cmp, hi,
        TailIntLEFloat, TailFloatLEInt, TailIntLTFloat, TailFloatLTInt,
        hf, eq_self_iff_true, false_and, true_and, false_or]
      unfold sgn
      split
      · constructor <;> (try constructor) <;> (try constructor) <;> omega
      · split <;> constructor <;> (try constructor) <;> (try constructor) <;> omega
    · have hf := (cl_ieee_inf_properties f hi).2
      cases hs : f.signbit <;>
        simp only [lessEqualFloat, floatLessEqual, lessFloat, floatLess, hn,
          Bool.false_eq_true, ite_false, decide_eq_true_eq, cl_ieee64_cmp, hi,
          eq_self_iff_true, ite_true, hs, TailIntLEFloat, TailFloatLEInt,
          TailIntLTFloat, TailFloatLTInt, hf, false_and, true_and, false_or,
          or_false] <;> decide
  · obtain ⟨hi, hf⟩ := cl_ieee_nan_properties f hn
    simp only [lessEqualFloat, floatLessEqual, lessFloat, floatLess, hn,
      eq_self_iff_true, ite_true, Bool.false_eq_true, TailIntLEFloat, TailFloatLEInt,
      TailIntLTFloat, TailFloatLTInt, hi, hf, false_and, false_or,
      iff_self, and_self]

theorem cl_rational_cross_le (n a b d e : Int) (hd : 0 < d) (he : 0 < e)
    (h : a * e = b * d) : n * d ≤ a ↔ n * e ≤ b := by
  rw [← Int.mul_le_mul_right he, Int.mul_right_comm n d e, h,
    Int.mul_le_mul_right hd]

theorem cl_rational_cross_lt (n a b d e : Int) (hd : 0 < d) (he : 0 < e)
    (h : a * e = b * d) : n * d < a ↔ n * e < b := by
  rw [← Int.mul_lt_mul_right he, Int.mul_right_comm n d e, h,
    Int.mul_lt_mul_right hd]

theorem cl_rational_cross_ge (n a b d e : Int) (hd : 0 < d) (he : 0 < e)
    (h : a * e = b * d) : a ≤ n * d ↔ b ≤ n * e := by
  rw [← Int.mul_le_mul_right he, Int.mul_right_comm n d e, h,
    Int.mul_le_mul_right hd]

theorem cl_rational_cross_gt (n a b d e : Int) (hd : 0 < d) (he : 0 < e)
    (h : a * e = b * d) : a < n * d ↔ b < n * e := by
  rw [← Int.mul_lt_mul_right he, Int.mul_right_comm n d e, h,
    Int.mul_lt_mul_right hd]

end JuliaLean.ChatGPT.Batch4.Group7

end


/- Component: ArithmeticBits.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem ab_wrap_unsigned {t : IntTy} (c : JInt t) (h : IsCulongMax t) :
    (JInt.wrap .u64 c.val).val = c.val := by
  change wrapInt .u64 c.val = c.val
  apply wrapInt_of_inRange
  rcases c.property with ⟨lo, hi⟩
  cases t <;> simp [IsCulongMax, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h lo hi ⊢ <;> omega

theorem ab_wrap_signed {t : IntTy} (c : JInt t) (h : IsClongMax t) :
    (JInt.wrap .i64 c.val).val = c.val := by
  change wrapInt .i64 c.val = c.val
  apply wrapInt_of_inRange
  rcases c.property with ⟨lo, hi⟩
  cases t <;> simp [IsClongMax, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h lo hi ⊢ <;> omega

theorem ab_repeat_sum (a : Int) (xs : List Nat) :
    xs.foldr (fun _ total => a + total) 0 = a * (xs.length : Int) := by
  induction xs with
  | nil => simp only [List.foldr_nil, List.length_nil, Int.ofNat_zero, Int.mul_zero]
  | cons x xs ih =>
    simp only [List.foldr_cons, List.length_cons, ih, Int.natCast_add, Int.natCast_one,
      Int.mul_add, Int.mul_one]
    exact Int.add_comm _ _

theorem ab_repeated_product (a b : Int) : ArithRepeatedProduct a b = a * b := by
  unfold ArithRepeatedProduct
  rw [ab_repeat_sum, List.length_range]
  by_cases hb : b < 0
  · rw [ite_eq_left hb, Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hb), Int.mul_neg, Int.neg_neg]
  · rw [ite_eq_right hb, Int.natAbs_of_nonneg (by omega)]

theorem BignumsGmpUnsignedLeftMul_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedLeftMultiplication := by
  intro t x c dispatch _
  unfold ArithMultiplication
  rw [ab_repeated_product]
  change x.val * (JInt.wrap .u64 c.val).val = c.val * x.val
  rw [ab_wrap_unsigned c dispatch, Int.mul_comm]

theorem BignumsGmpSignedRightMul_proven : JuliaLean.Proofs.base.gmp.Round1.SignedRightMultiplication := by
  intro t x c dispatch _
  unfold ArithMultiplication
  rw [ab_repeated_product]
  change x.val * (JInt.wrap .i64 c.val).val = x.val * c.val
  rw [ab_wrap_signed c dispatch]

theorem BignumsGmpSignedLeftMul_proven : JuliaLean.Proofs.base.gmp.Round1.SignedLeftMultiplication := by
  intro t x c dispatch _
  unfold ArithMultiplication
  rw [ab_repeated_product]
  change x.val * (JInt.wrap .i64 c.val).val = c.val * x.val
  rw [ab_wrap_signed c dispatch, Int.mul_comm]

theorem BignumsGmpNegationInverse_proven : JuliaLean.Proofs.base.gmp.Round1.UnaryNegationInverse := by
  intro x _
  refine ⟨writeValue initBigInt (-x.val), rfl, ?_⟩
  change -x.val + x.val = 0
  omega


theorem ab_complement_emod (a m : Int) (hm : 0 < m) :
    (-a - 1) % m = m - 1 - a % m := by
  have h0 := Int.emod_nonneg a (Int.ne_of_gt hm)
  have hlt := Int.emod_lt_of_pos a hm
  calc
    (-a - 1) % m = (m - (a + 1)) % m := by
      rw [Int.sub_emod_left]
      congr 1
      omega
    _ = (m - 1 - a) % m := by congr 1; omega
    _ = (m - 1 - a % m) % m := (Int.sub_emod_emod (m - 1) a m).symm
    _ = m - 1 - a % m := Int.emod_eq_of_lt (by omega) (by omega)

theorem ab_ediv_emod (a b c : Int) (hb : 0 < b) :
    (a / b) % c = (a % (b * c)) / b := by
  rw [Int.emod_def a (b * c), Int.mul_assoc,
    Int.sub_mul_ediv_left _ _ (Int.ne_of_gt hb),
    ← Int.ediv_ediv_of_nonneg (Int.le_of_lt hb), Int.emod_def]

theorem ab_halfbit_complement (a : Int) (i : Nat) :
    (2 : Int)^i ≤ (-a-1) % 2^(i+1) ↔ ¬ (2 : Int)^i ≤ a % 2^(i+1) := by
  have hp : 0 < (2 : Int)^i := Int.pow_pos (by decide)
  rw [ab_complement_emod a _ (Int.pow_pos (by decide)), Int.pow_succ]
  omega

theorem ab_halfbit_right (a : Int) (n i : Nat) :
    (2 : Int)^i ≤ (a / 2^n) % 2^(i+1) ↔ (2 : Int)^(i+n) ≤ a % 2^(i+n+1) := by
  have hp : 0 < (2 : Int)^n := Int.pow_pos (by decide)
  rw [ab_ediv_emod _ _ _ hp, Int.le_ediv_iff_mul_le hp,
    ← Int.pow_add, ← Int.pow_add]
  rw [show n + (i + 1) = i + n + 1 by omega]

theorem ab_halfbit_left_above (a : Int) (n j : Nat) :
    (2 : Int)^(n+j) ≤ (a * 2^n) % 2^(n+j+1) ↔ (2 : Int)^j ≤ a % 2^(j+1) := by
  have hp : 0 < (2 : Int)^n := Int.pow_pos (by decide)
  have hs : n+j+1 = n+(j+1) := by omega
  rw [hs, Int.pow_add, Int.pow_add, Int.mul_comm a,
    Int.mul_emod_mul_of_pos _ _ hp, Int.mul_le_mul_left hp]

theorem ab_halfbit_left_below (a : Int) (n i : Nat) (h : i < n) :
    ¬ (2 : Int)^i ≤ (a * 2^n) % 2^(i+1) := by
  have hp : 0 < (2 : Int)^i := Int.pow_pos (by decide)
  have hs : n = (i+1) + (n-(i+1)) := by omega
  have hf : (2 : Int)^n = 2^(i+1) * 2^(n-(i+1)) := by
    conv => lhs; rw [hs]
    rw [Int.pow_add]
  have hd : (2 : Int)^(i+1) ∣ a * 2^n := by
    rw [hf, ← Int.mul_assoc, Int.mul_comm a, Int.mul_assoc]
    exact Int.dvd_mul_right _ _
  rw [Int.emod_eq_zero_of_dvd hd]
  omega


theorem ab_halfbit_parity (a : Int) (i : Nat) :
    (2 : Int)^i ≤ a % 2^(i+1) ↔ (a / 2^i) % 2 = 1 := by
  have hp : 0 < (2 : Int)^i := Int.pow_pos (by decide)
  rw [ab_ediv_emod _ _ _ hp, ← Int.pow_succ]
  change (2 : Int)^i ≤ a % 2^(i+1) ↔ a % (2 : Int)^(i+1) / 2^i = 1
  have hu : a % (2 : Int)^(i+1) / 2^i < 2 := by
    apply (Int.ediv_lt_iff_lt_mul hp).mpr
    have := Int.emod_lt_of_pos a (Int.pow_pos (m := i+1) (by decide : (0 : Int)<2))
    rw [Int.pow_succ] at this
    omega
  have he := Int.le_ediv_iff_mul_le (a := 1) (b := a % (2 : Int)^(i+1)) hp
  simp only [Int.one_mul] at he
  omega


theorem ab_bit_iff (a : Int) (i : Nat) :
    ArithBit a i ↔ (2 : Int)^i ≤ a % 2^(i+1) := by
  exact decide_eq_true_iff

theorem ab_bit_complement (a : Int) (i : Nat) :
    ArithBit (-a-1) i ↔ ¬ ArithBit a i := by
  rw [ab_bit_iff, ab_bit_iff]
  exact ab_halfbit_complement a i

theorem ab_bitAt_iff (a : Int) (i : Nat) : bitAt a i = true ↔ ArithBit a i := by
  unfold bitAt
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.pow_nonneg (by decide)),
    decide_eq_true_eq, ab_bit_iff]
  exact (ab_halfbit_parity a i).symm

theorem BignumsGmpComplementBits_proven : JuliaLean.Proofs.base.gmp.Round1.ComplementEveryBit := by
  intro x _
  refine ⟨writeValue initBigInt (-x.val-1), rfl, ?_⟩
  intro i
  exact ab_bit_complement x.val i

theorem BignumsGmpLeftShiftBits_proven : JuliaLean.Proofs.base.gmp.Round1.LeftShiftEveryBit := by
  intro x count _ i
  have he : (shiftLeft x count).val = x.val * (2 : Int)^count.val.toNat := by
    unfold shiftLeft
    split
    · rename_i h
      simp only [h, Int.toNat_zero, Int.pow_zero, Int.mul_one]
    · rfl
  rw [he, ab_bit_iff, ab_bit_iff]
  by_cases h : count.val.toNat ≤ i
  · have hi : i = count.val.toNat + (i-count.val.toNat) := by omega
    simp only [h, true_and]
    conv => lhs; rw [hi]
    exact ab_halfbit_left_above x.val count.val.toNat (i-count.val.toNat)
  · have hn := ab_halfbit_left_below x.val count.val.toNat i (by omega)
    simp only [h, false_and, iff_false]
    exact hn

theorem BignumsGmpRightShiftBits_proven : JuliaLean.Proofs.base.gmp.Round1.RightShiftEveryBit := by
  intro x count _ i
  have he : (shiftRight x count).val = x.val / (2 : Int)^count.val.toNat := by
    unfold shiftRight
    split
    · rename_i h
      simp only [h, Int.toNat_zero, Int.pow_zero, Int.ediv_one]
    · change x.val.fdiv ((2 : Int)^count.val.toNat) = _
      exact Int.fdiv_eq_ediv_of_nonneg _ (Int.pow_nonneg (by decide))
  rw [he, ab_bit_iff, ab_bit_iff]
  exact ab_halfbit_right x.val count.val.toNat i

theorem BignumsGmpLogicalRightShiftBits_proven : JuliaLean.Proofs.base.gmp.Round1.LogicalRightShiftEveryBit := by
  exact BignumsGmpRightShiftBits_proven

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: Exponent.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem ex_magnitude_append (xs ys : List Limb) :
    limbMagnitude (xs ++ ys) = limbMagnitude xs + (2^64)^xs.length * limbMagnitude ys := by
  induction xs with
  | nil => simp only [List.nil_append, limbMagnitude, List.length_nil, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add]
  | cons x xs ih =>
    change x.val.toNat + 2^64 * limbMagnitude (xs ++ ys) =
      x.val.toNat + 2^64 * limbMagnitude xs + (2^64)^(xs.length+1) * limbMagnitude ys
    rw [ih, Nat.pow_succ (2^64) xs.length]
    simp only [Nat.mul_add, Nat.add_assoc]
    rw [Nat.mul_left_comm (2^64), Nat.mul_assoc]

theorem ex_magnitude_prefix (xs : List Limb) (n : Nat) (h : n < xs.length) :
    limbMagnitude (xs.take (n+1)) = limbMagnitude (xs.take n) +
      (2^64)^n * ((xs[n]?).getD (JInt.wrap .u64 0)).val.toNat := by
  rw [List.take_succ_eq_append_getElem h, ex_magnitude_append,
    List.length_take_of_le (by omega)]
  simp only [limbMagnitude, Nat.mul_zero, Nat.add_zero,
    List.getElem?_eq_getElem h, Option.getD_some]

theorem ex_top_bracket (xs : List Limb) (n : Nat) (h : n < xs.length)
    (htop : ((xs[n]?).getD (JInt.wrap .u64 0)).val.toNat ≠ 0) :
    let top := ((xs[n]?).getD (JInt.wrap .u64 0)).val.toNat
    (2^(64*n + top.log2) ≤ limbMagnitude (xs.take (n+1))) ∧
      limbMagnitude (xs.take (n+1)) < 2^(64*n + top.log2+1) := by
  dsimp only
  let top := ((xs[n]?).getD (JInt.wrap .u64 0)).val.toNat
  have hlo := Nat.log2_self_le htop
  have hhi := Nat.lt_log2_self (n := top)
  have hrem := cl_magnitude_bound (xs.take n)
  rw [List.length_take_of_le (by omega)] at hrem
  rw [ex_magnitude_prefix xs n h]
  have hp : 0 < (2^64)^n := Nat.pow_pos (by decide)
  constructor
  · rw [Nat.pow_add, Nat.pow_mul]
    exact Nat.le_trans (Nat.mul_le_mul_left ((2^64)^n) hlo) (Nat.le_add_left _ _)
  · have hu : limbMagnitude (xs.take n) + (2^64)^n * top <
        (2^64)^n * (top + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hv := Nat.mul_le_mul_left ((2^64)^n) (show top+1 ≤ 2^(top.log2+1) by omega)
    have he : 64*n + top.log2+1 = 64*n+(top.log2+1) := by omega
    rw [he, Nat.pow_add, Nat.pow_mul]
    exact Nat.lt_of_lt_of_le hu hv

theorem ex_top_bound (x : BigInt) (i : Nat) : loadLimb x i < 2^64 := by
  have h := (((x.d[i]?).getD (JInt.wrap .u64 0))).property
  change 0 ≤ _ ∧ _ ≤ (2 : Int)^64-1 at h
  unfold loadLimb
  omega

theorem ex_input_size_bound (x : BigInt) (hx : GMPInput x) : x.size.val.natAbs < 2^31 := by
  have h := hx.1.2.1
  have hr := x.alloc.property
  change -(2 : Int)^31 ≤ x.alloc.val ∧ x.alloc.val ≤ (2 : Int)^31-1 at hr
  omega

theorem ex_input_nonzero_size (x : BigInt) (hx : GMPInput x) (hz : x.val ≠ 0) :
    0 < x.size.val.natAbs := by
  have h := hx.1.2.2.2.1
  omega

theorem ex_input_top_nonzero (x : BigInt) (hx : GMPInput x) (hz : x.val ≠ 0) :
    loadLimb x (x.size.val.natAbs-1) ≠ 0 := by
  have hs : x.size.val ≠ 0 := by intro h; exact hz (hx.1.2.2.2.1.mp h)
  have h := hx.1.2.2.2.2 hs
  have hr := (((x.d[x.size.val.natAbs-1]?).getD (JInt.wrap .u64 0))).property
  change 0 ≤ _ ∧ _ ≤ (2 : Int)^64-1 at hr
  unfold loadLimb
  omega

theorem ex_input_top_log (x : BigInt) (hx : GMPInput x) (hz : x.val ≠ 0) :
    (loadLimb x (x.size.val.natAbs-1)).log2 < 64 := by
  exact (Nat.log2_lt (ex_input_top_nonzero x hx hz)).mpr (ex_top_bound x _)

theorem ex_magnitude_val (x : BigInt) (hx : GMPInput x) (hz : x.val ≠ 0) :
    (bitMagnitude x).val = 64*(x.size.val.natAbs-1) +
      ((loadLimb x (x.size.val.natAbs-1)).log2 : Int) + 1 := by
  have hs := ex_input_nonzero_size x hx hz
  have hb := ex_input_size_bound x hx
  have ht := ex_input_top_nonzero x hx hz
  have hl := ex_input_top_log x hx hz
  unfold bitMagnitude
  simp only [ht, ite_false]
  change wrapInt .i64 _ = _
  rw [wrapInt_of_inRange]
  · omega
  · change -(2 : Int)^63 ≤ _ ∧ _ ≤ (2 : Int)^63-1
    omega


theorem BignumsGmpExponentBracket_proven : JuliaLean.Proofs.base.gmp.Round1.ExponentMagnitudeBracket := by
  intro x hx
  by_cases hz : x.val = 0
  · simp only [hz, ite_true]
    refine ⟨"cannot be zero", ?_⟩
    have hs : x.size.val = 0 := hx.1.2.2.2.1.mpr hz
    simp only [JuliaLean.base.gmp.exponent, iszero, hs, decide_true, ite_true]
  · simp only [hz, ite_false]
    have hs := ex_input_nonzero_size x hx hz
    have hb := ex_input_size_bound x hx
    have ht := ex_input_top_nonzero x hx hz
    have hl := ex_input_top_log x hx hz
    have hsz : x.size.val ≠ 0 := by omega
    let k := 64*(x.size.val.natAbs-1)+(loadLimb x (x.size.val.natAbs-1)).log2
    let e := bitMagnitude x - JInt.wrap .i64 1
    have he : e.val = (k : Int) := by
      change wrapInt .i64 ((bitMagnitude x).val - (JInt.wrap .i64 1).val) = (k : Int)
      rw [ex_magnitude_val x hx hz, show (JInt.wrap .i64 1).val = 1 by decide]
      rw [wrapInt_of_inRange]
      · dsimp only [k]
        omega
      · change -(2 : Int)^63 ≤ _ ∧ _ ≤ (2 : Int)^63-1
        omega
    refine ⟨e, ?_, ?_, ?_⟩
    · simp only [JuliaLean.base.gmp.exponent, iszero, hsz, decide_false, ite_false]
      rfl
    · rw [he]
      omega
    · have hnt : x.size.val.natAbs-1 < x.d.length := by have := hx.1.1; omega
      have hbr := ex_top_bracket x.d (x.size.val.natAbs-1) hnt ht
      change 2^k ≤ limbMagnitude (x.d.take (x.size.val.natAbs-1+1)) ∧
        limbMagnitude (x.d.take (x.size.val.natAbs-1+1)) < 2^(k+1) at hbr
      rw [show x.size.val.natAbs-1+1=x.size.val.natAbs by omega,
        ← cl_input_magnitude x hx.1] at hbr
      rw [he]
      exact hbr

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: CountsComparisons.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7

open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Proofs.base.gmp.Round1

theorem cc_wrap_sgn (n : Int) :
    (JInt.wrap .i64 (sgn n)).val = sgn n := by
  change wrapInt .i64 (sgn n) = sgn n
  apply wrapInt_of_inRange
  unfold sgn
  split
  · decide
  · split <;> decide

theorem cc_sgn_idempotent (n : Int) : sgn (sgn n) = sgn n := by
  unfold sgn
  split <;> (try split) <;> omega

theorem cc_cmp_val (x y : BigInt) :
    (JuliaLean.base.gmp.cmp x y).val = sgn (x.val - y.val) := by
  simp only [JuliaLean.base.gmp.cmp, MPZ.cmp, cc_wrap_sgn, cc_sgn_idempotent]

theorem cc_cmpUnsigned_val (x : BigInt) (y : Culong) :
    (cmpUnsigned x y).val = sgn (x.val - y.val) := by
  simp only [cmpUnsigned, MPZ.cmpUi, cc_wrap_sgn, cc_sgn_idempotent]

theorem cc_cmpSigned_val (x : BigInt) (y : Clong) :
    (cmpSigned x y).val = sgn (x.val - y.val) := by
  simp only [cmpSigned, MPZ.cmpSi, cc_wrap_sgn, cc_sgn_idempotent]

theorem cc_comparison_of_sgn (a b : Int) (r : Clong)
    (h : r.val = sgn (a-b)) : ArithIntegerComparison a b r := by
  unfold ArithIntegerComparison
  rw [h]
  unfold sgn
  split <;> (try split) <;> omega

theorem cc_signed_range (t : IntTy) (y : JInt t) (h : IsClongMax t) :
    IntTy.min .i64 ≤ y.val ∧ y.val ≤ IntTy.max .i64 := by
  have hy := y.property
  cases t <;> simp [IsClongMax, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at h hy ⊢ <;> omega

theorem cc_unsigned_range (t : IntTy) (y : JInt t) (h : IsCulongMax t) :
    IntTy.min .u64 ≤ y.val ∧ y.val ≤ IntTy.max .u64 := by
  have hy := y.property
  cases t <;> simp [IsCulongMax, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at h hy ⊢ <;> omega

theorem BignumsGmpComparisonExact_proven : JuliaLean.Proofs.base.gmp.Round1.IntegerComparisonExact := by
  intro x y _hx _hy
  exact cc_comparison_of_sgn x.val y.val _ (cc_cmp_val x y)

theorem BignumsGmpComparisonSigned_proven : JuliaLean.Proofs.base.gmp.Round1.SignedComparisonExact := by
  intro t x y h _hx
  apply cc_comparison_of_sgn
  have hw : (JInt.wrap .i64 y.val).val = y.val :=
    wrapInt_of_inRange .i64 y.val (cc_signed_range t y h)
  simp only [cmpClongMax, MPZ.cmpSi, cc_wrap_sgn, cc_sgn_idempotent, hw]

theorem BignumsGmpComparisonUnsigned_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedComparisonExact := by
  intro t x y h _hx
  apply cc_comparison_of_sgn
  have hw : (JInt.wrap .u64 y.val).val = y.val :=
    wrapInt_of_inRange .u64 y.val (cc_unsigned_range t y h)
  simp only [cmpCulongMax, MPZ.cmpUi, cc_wrap_sgn, cc_sgn_idempotent, hw]

theorem cc_tmod_sign (a b : Int) : ArithRemainderSign (a.tmod b) a := by
  by_cases hr : a.tmod b = 0
  · exact Or.inl hr
  · right
    by_cases ha : a < 0
    · have hn := Int.tmod_nonneg b (show 0 ≤ -a by omega)
      rw [Int.neg_tmod] at hn
      omega
    · have hn := Int.tmod_nonneg b (show 0 ≤ a by omega)
      omega

theorem cc_tdiv_pair (a b : Int) (hb : b ≠ 0) :
    ArithDivisionPair .toZero a b (a.tdiv b) (a-a.tdiv b*b) := by
  have hidentity := Int.tdiv_mul_add_tmod a b
  have hr : a-a.tdiv b*b = a.tmod b := by omega
  rw [hr]
  refine ⟨hidentity.symm, ?_, cc_tmod_sign a b⟩
  rw [Int.natAbs_tmod]
  exact Nat.mod_lt _ (by omega)

theorem BignumsGmpDivremPair_proven : JuliaLean.Proofs.base.gmp.Round1.DivremExactPair := by
  intro x y _hx _hy
  by_cases hy : y.val = 0
  · simp only [hy, if_true, divrem, MPZ.tdivQr, MPZ.tdivQrBang, MPZ.binaryValue]
    simp only [hy, if_true, Except.bind, bind, pure]
  · simp only [hy, if_false]
    refine ⟨writeValue initBigInt (x.val.tdiv y.val),
      writeValue initBigInt (x.val-x.val.tdiv y.val*y.val), ?_, ?_⟩
    · simp only [divrem, MPZ.tdivQr, MPZ.tdivQrBang, MPZ.binaryValue, hy, if_false]
      rfl
    · exact cc_tdiv_pair x.val y.val hy

def cc_negative_zero : FV .f64 := JuliaLean.Promotion.Fl.zero true

set_option maxRecDepth 4096 in
theorem cc_zero_input : GMPInput (ofInt 0) := by
  have hlength : (limbsOfNat (0 : Int).natAbs).length = 0 := by
    change (limbsOfNat 0).length = 0
    rw [cl_limbs_zero]
    rfl
  have hlt : (limbsOfNat (0 : Int).natAbs).length < 2^31 := by
    rw [hlength]
    decide
  refine ⟨cl_ofInt_valid 0 hlt, ?_, ?_⟩
  · rw [cl_ofInt_alloc 0 hlt]
    exact Int.ofNat_zero_le _
  · change (limbsOfNat (0 : Int).natAbs).length < 2^62
    rw [hlength]
    decide

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 2048 in
theorem cc_negative_zero_less : ArithFloatIntegerLess cc_negative_zero 0 := by
  unfold ArithFloatIntegerLess
  decide

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 2048 in
theorem cc_cmp_negative_zero : (cmpFloat (ofInt 0) cc_negative_zero).val = 0 := by decide

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 2048 in
theorem cc_reverse_cmp_negative_zero : (floatCmp cc_negative_zero (ofInt 0)).val = 0 := by decide

theorem BignumsGmpComparisonIeee_refuted : ¬ JuliaLean.Proofs.base.gmp.Round1.IntegerFloatTotalOrder := by
  intro h
  have hc := h .f64 (ofInt 0) cc_negative_zero cc_zero_input
  have heq : (cmpFloat (ofInt 0) cc_negative_zero).val = 1 :=
    hc.2.2.1.mpr cc_negative_zero_less
  have hzero := cc_cmp_negative_zero
  omega

theorem BignumsGmpComparisonIeeeReverse_refuted : ¬ JuliaLean.Proofs.base.gmp.Round1.FloatIntegerTotalOrder := by
  intro h
  have hc := h .f64 (ofInt 0) cc_negative_zero cc_zero_input
  have heq : (floatCmp cc_negative_zero (ofInt 0)).val = -1 :=
    hc.2.1.mpr cc_negative_zero_less
  have hzero := cc_reverse_cmp_negative_zero
  omega

theorem cc_trailing_zero_failure (x : BigInt) (h : x.val = 0) :
    ArithDomainFailure (trailingZeros x) := by
  refine ⟨"`x` must be non-zero", ?_⟩
  unfold trailingZeros MPZ.scan
  rw [h]
  rfl

theorem cc_trailing_one_failure (x : BigInt) (h : x.val = -1) :
    ArithDomainFailure (trailingOnes x) := by
  refine ⟨"`x` must not be equal to -1", ?_⟩
  unfold trailingOnes MPZ.scan
  rw [h]
  rfl

theorem cc_count_ones_failure (x : BigInt) (h : x.val < 0) :
    ArithDomainFailure (countOnes x) := by
  refine ⟨"`x` cannot be negative", ?_⟩
  simp only [countOnes, MPZ.popcount, if_pos h]
  rfl

theorem cc_count_zeros_failure (x : BigInt) (h : 0 ≤ x.val) :
    ArithDomainFailure (countZeros x) := by
  refine ⟨"`x` must be negative", ?_⟩
  have hn : -x.val - 1 < 0 := by omega
  have hpop : MPZ.popcount (writeValue initBigInt (-x.val-1)) = JInt.wrap .i64 (-1) := by
    change JInt.wrap .i64 (if -x.val-1 < 0 then -1 else (countBits (-x.val-1).toNat : Int)) = _
    rw [if_pos hn]
  change (if (MPZ.popcount (writeValue initBigInt (-x.val-1))).val = -1
    then Except.error (JlError.domainError "`x` must be negative")
    else Except.ok (MPZ.popcount (writeValue initBigInt (-x.val-1)))) = _
  rw [hpop]
  rfl

theorem cc_exponent_zero_failure (x : BigInt) (hx : GMPInput x) (h : x.val = 0) :
    ArithDomainFailure (JuliaLean.base.gmp.exponent x) := by
  have hs : x.size.val = 0 := hx.1.2.2.2.1.mpr h
  refine ⟨"cannot be zero", ?_⟩
  simp only [JuliaLean.base.gmp.exponent, iszero, hs, decide_true, if_true]

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: CountsAlgorithms.lean -/
namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem cc_fold_count {α : Type} (p : α → Bool) (xs : List α) (a : Nat) :
    xs.foldl (fun c x => c + if p x then 1 else 0) a = a + (xs.filter p).length := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, List.filter_nil, List.length_nil, Nat.add_zero]
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, List.filter_cons]
    cases hp : p x <;> simp only [hp, Bool.false_eq_true, Bool.true_eq, if_false, if_true,
      List.length_cons] <;> omega

def cc_positions (n : Nat) : List Nat :=
  (List.range (n.log2+1)).filter (fun i => decide (n/2^i%2=1))

theorem cc_positions_nodup (n : Nat) : (cc_positions n).Nodup := by
  exact List.Pairwise.filter _ List.nodup_range

theorem cc_positions_mem (n i : Nat) : i ∈ cc_positions n ↔ n.testBit i = true := by
  simp only [cc_positions, List.mem_filter, List.mem_range]
  rw [← Nat.testBit_eq_decide_div_mod_eq]
  constructor
  · intro h; exact h.2
  · intro h
    refine ⟨?_, h⟩
    have hn : n ≠ 0 := by
      intro hz
      subst hz
      simp only [Nat.zero_testBit, Bool.false_eq_true] at h
    have hpow : 2^i ≤ n := Nat.ge_two_pow_of_testBit h
    have hlog : i ≤ n.log2 := (Nat.le_log2 hn).mpr hpow
    omega

theorem cc_positions_length_bound (n : Nat) : (cc_positions n).length ≤ n.log2+1 := by
  exact (by simpa only [cc_positions, List.length_range] using
    List.length_filter_le (fun i => decide (n/2^i%2=1)) (List.range (n.log2+1)))

theorem cc_nat_upper_half_bit (n i : Nat) :
    2^i ≤ n % 2^(i+1) ↔ n.testBit i = true := by
  have hm : (n % 2^(i+1)).testBit i = n.testBit i := by
    rw [Nat.testBit_mod_two_pow]
    simp only [Nat.lt_succ_self, decide_true, Bool.true_and]
  constructor
  · intro h
    rw [← hm]
    exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h
      (Nat.mod_lt _ (Nat.pow_pos (by decide)))
  · intro h
    rw [← hm] at h
    exact Nat.ge_two_pow_of_testBit h

theorem cc_arithbit_nat (n i : Nat) : ArithBit (n : Int) i ↔ n.testBit i = true := by
  unfold ArithBit ArithBitBool
  rw [decide_eq_true_eq]
  have hcast : (((2^i : Nat) : Int) ≤ ((n % 2^(i+1) : Nat) : Int)) ↔ n.testBit i = true :=
    Int.ofNat_le.trans (cc_nat_upper_half_bit n i)
  have htwo : ((2 : Nat) : Int) = (2 : Int) := rfl
  simpa only [Int.natCast_emod, Int.natCast_pow, htwo] using hcast

theorem cc_countBits_positions (n : Nat) : countBits n = (cc_positions n).length := by
  simpa only [countBits, cc_positions, decide_eq_true_eq, Nat.zero_add] using
    cc_fold_count (fun i => decide (n/2^i%2=1)) (List.range (n.log2+1)) 0

theorem cc_countBits_bound (n : Nat) : countBits n ≤ n.log2+1 := by
  rw [cc_countBits_positions]
  exact cc_positions_length_bound n

theorem cc_nat_bitcount (n : Nat) (hn : n.log2+1 < 2^63) :
    ArithBitCount (ArithBit (n : Int)) (JInt.wrap .i64 (countBits n : Int)) := by
  have hbound := cc_countBits_bound n
  have hw : (JInt.wrap .i64 (countBits n : Int)).val = (countBits n : Int) := by
    change wrapInt .i64 (countBits n : Int) = (countBits n : Int)
    apply wrapInt_of_inRange
    change -(2 : Int)^63 ≤ (countBits n : Int) ∧ (countBits n : Int) ≤ (2 : Int)^63-1
    omega
  refine ⟨?_, cc_positions n, cc_positions_nodup n, ?_, ?_⟩
  · rw [hw]
    omega
  · intro i
    exact (cc_positions_mem n i).trans (cc_arithbit_nat n i).symm
  · rw [hw, cc_countBits_positions]

theorem cc_log2_mono (a b : Nat) (h : a ≤ b) : a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · simp only [ha, Nat.log2_zero, Nat.zero_le]
  · have hb : b ≠ 0 := by omega
    exact (Nat.le_log2 hb).mpr (Nat.le_trans (Nat.log2_self_le ha) h)

-- The shared limb-magnitude helper is proved in this group's classification section.
theorem cc_input_log2_bound (x : BigInt) (hx : GMPInput x) :
    x.val.natAbs.log2 + 3 < 2^63 := by
  have hm := cl_input_magnitude_bound x hx.1
  rw [← Nat.pow_mul] at hm
  have ha := x.alloc.property
  change -(2 : Int)^31 ≤ x.alloc.val ∧ x.alloc.val ≤ (2 : Int)^31 - 1 at ha
  have hs := hx.1.2.1
  by_cases hz : x.val.natAbs = 0
  · simp only [hz, Nat.log2_zero]
    decide
  · have hlog := (Nat.log2_lt hz).mpr hm
    omega

theorem BignumsGmpCountOnesCardinality_proven : JuliaLean.Proofs.base.gmp.Round1.CountOnesCardinality := by
  intro x hx
  by_cases hneg : x.val < 0
  · simp only [hneg, if_true]
    exact cc_count_ones_failure x hneg
  · simp only [hneg, if_false]
    have hnonneg : 0 ≤ x.val := by omega
    have hlog := cc_input_log2_bound x hx
    have habs : x.val.toNat = x.val.natAbs := by omega
    have hspec := cc_nat_bitcount x.val.toNat (by rw [habs]; omega)
    rw [Int.toNat_of_nonneg hnonneg] at hspec
    let c := JInt.wrap .i64 (countBits x.val.toNat : Int)
    have hcn : 0 ≤ c.val := hspec.1
    have hc : c.val ≠ -1 := by omega
    refine ⟨c, ?_, hspec⟩
    simp only [countOnes, MPZ.popcount, if_neg hneg]
    change (if c.val = -1 then Except.error (JlError.domainError "`x` cannot be negative") else Except.ok c) = Except.ok c
    rw [if_neg hc]

theorem BignumsGmpCountZerosCardinality_proven : JuliaLean.Proofs.base.gmp.Round1.CountZerosCardinality := by
  intro x hx
  by_cases hnonneg : 0 ≤ x.val
  · simp only [hnonneg, if_true]
    exact cc_count_zeros_failure x hnonneg
  · simp only [hnonneg, if_false]
    have hcomp : 0 ≤ -x.val-1 := by omega
    have hlog := cc_input_log2_bound x hx
    have hmag : (-x.val-1).toNat ≤ x.val.natAbs := by omega
    have hlogcomp := cc_log2_mono _ _ hmag
    have hspec := cc_nat_bitcount (-x.val-1).toNat (by omega)
    rw [Int.toNat_of_nonneg hcomp] at hspec
    let c := JInt.wrap .i64 (countBits (-x.val-1).toNat : Int)
    have hcn : 0 ≤ c.val := hspec.1
    have hc : c.val ≠ -1 := by omega
    refine ⟨c, ?_, ?_⟩
    · change (if (MPZ.popcount (writeValue initBigInt (-x.val-1))).val = -1
        then Except.error (JlError.domainError "`x` must be negative")
        else Except.ok (MPZ.popcount (writeValue initBigInt (-x.val-1)))) = Except.ok c
      simp only [MPZ.popcount, writeValue, ofInt, if_neg (show ¬ -x.val-1 < 0 by omega)]
      change (if c.val = -1 then Except.error (JlError.domainError "`x` must be negative") else Except.ok c) = Except.ok c
      rw [if_neg hc]
    · obtain ⟨h0, positions, hnd, hmem, hlen⟩ := hspec
      exact ⟨h0, positions, hnd, fun i => (hmem i).trans (ab_bit_complement x.val i), hlen⟩

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: Valuations.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem cc_lowerbits_mod_zero (a : Int) (k : Nat) :
    a % (2 : Int)^k = 0 ↔ ∀ i, i < k → ¬ (2 : Int)^i ≤ a % (2 : Int)^(i+1) := by
  induction k with
  | zero =>
    simp only [Int.pow_zero, Int.emod_one]
    constructor
    · intro _ i hi; omega
    · intro _; exact True.intro
  | succ k ih =>
    have hp : 0 < (2 : Int)^k := Int.pow_pos (by decide)
    have hmodpos : 0 < (2 : Int)^(k+1) := Int.pow_pos (by decide)
    have hdvd : (2 : Int)^k ∣ (2 : Int)^(k+1) := ⟨2, by rw [Int.pow_succ]⟩
    constructor
    · intro h i hi
      have hlow : a % (2 : Int)^k = 0 := by
        have heq := Int.emod_emod_of_dvd a hdvd
        rw [h, Int.zero_emod] at heq
        exact heq.symm
      by_cases hik : i = k
      · subst i
        rw [h]
        omega
      · exact ih.mp hlow i (by omega)
    · intro h
      have hlow : a % (2 : Int)^k = 0 := ih.mpr (fun i hi => h i (by omega))
      have htop := h k (by omega)
      have hnonneg := Int.emod_nonneg a (Int.ne_of_gt hmodpos)
      have heq : (a % (2 : Int)^(k+1)) % (2 : Int)^k = 0 := by
        rw [Int.emod_emod_of_dvd a hdvd, hlow]
      rw [Int.emod_eq_of_lt hnonneg (by omega)] at heq
      exact heq

theorem cc_first_bit_valuation (a : Int) (k : Nat) (hk : ArithBit a k)
    (hprev : ∀ i, i < k → ¬ ArithBit a i) :
    ArithDivides ((2 : Int)^k) a ∧ ¬ ArithDivides ((2 : Int)^(k+1)) a := by
  have hzero : a % (2 : Int)^k = 0 := by
    apply (cc_lowerbits_mod_zero a k).mpr
    simpa only [ArithBit, ArithBitBool, decide_eq_true_eq] using hprev
  refine ⟨Int.dvd_of_emod_eq_zero hzero, ?_⟩
  intro hdvd
  have hzero2 := Int.emod_eq_zero_of_dvd hdvd
  have hpos : 0 < (2 : Int)^k := Int.pow_pos (by decide)
  simp only [ArithBit, ArithBitBool, decide_eq_true_eq, hzero2] at hk
  omega

theorem cc_log2_succ_bound (n : Nat) : (n+1).log2 ≤ n.log2+1 := by
  have hpow := Nat.lt_log2_self (n := n)
  have hpos : 0 < 2^(n.log2+1) := Nat.pow_pos (by decide)
  have hn : n+1 < 2^(n.log2+1+1) := by
    rw [Nat.pow_succ]
    omega
  have hlog := (Nat.log2_lt (show n+1 ≠ 0 by omega)).mpr hn
  omega

theorem cc_exists_bit (a : Int) (ha : a ≠ 0) :
    ∃ i, i ≤ a.natAbs.log2+1 ∧ ArithBit a i := by
  by_cases hneg : a < 0
  · let i := a.natAbs.log2+1
    have hnonneg : 0 ≤ -a-1 := by omega
    have hmag : (-a-1).toNat ≤ a.natAbs := by omega
    have hfalse : ¬ ArithBit (-a-1) i := by
      have hbit : ((-a-1).toNat).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt hmag Nat.lt_log2_self)
      have hiff := cc_arithbit_nat (-a-1).toNat i
      rw [Int.toNat_of_nonneg hnonneg, hbit] at hiff
      intro hh
      have := hiff.mp hh
      contradiction
    refine ⟨i, Nat.le_refl _, ?_⟩
    by_cases hh : ArithBit a i
    · exact hh
    · exact False.elim (hfalse ((ab_bit_complement a i).mpr hh))
  · have hnonneg : 0 ≤ a := by omega
    have habs : a.toNat = a.natAbs := by omega
    have hn : a.toNat ≠ 0 := by omega
    refine ⟨a.toNat.log2, ?_, ?_⟩
    · rw [habs]
      omega
    · have hh := (cc_arithbit_nat a.toNat a.toNat.log2).mpr (Nat.testBit_log2 hn)
      simpa only [Int.toNat_of_nonneg hnonneg] using hh

def cc_scan_value (a : Int) (wanted : Bool) : Int := if wanted then a else -a-1

theorem cc_scan_predicate (a : Int) (wanted : Bool) (i : Nat) :
    (bitAt a i == wanted) = true ↔ ArithBit (cc_scan_value a wanted) i := by
  cases wanted <;> simp only [cc_scan_value, Bool.false_eq_true, if_false, if_true,
    beq_iff_eq, Bool.eq_false_iff, ne_eq, ab_bit_complement, ab_bitAt_iff]

theorem cc_scan_exists (a : Int) (wanted : Bool) (ha : cc_scan_value a wanted ≠ 0) :
    ∃ k : Nat, scanBit a 0 wanted = (k : Int) ∧ k ≤ a.natAbs.log2+2 ∧
      ArithBit (cc_scan_value a wanted) k ∧
      (∀ i, i < k → ¬ ArithBit (cc_scan_value a wanted) i) := by
  have hmag : (cc_scan_value a wanted).natAbs ≤ a.natAbs+1 := by
    cases wanted <;> simp only [cc_scan_value, Bool.false_eq_true, Bool.true_eq, if_false, if_true] <;> omega
  have hlog := Nat.le_trans (cc_log2_mono _ _ hmag) (cc_log2_succ_bound a.natAbs)
  obtain ⟨i, hi, hbit⟩ := cc_exists_bit (cc_scan_value a wanted) ha
  let p : Nat → Bool := fun j => bitAt a j == wanted
  have hex : ∃ k, (List.range (a.natAbs.log2+3)).find? p = some k := by
    cases hf : (List.range (a.natAbs.log2+3)).find? p with
    | none =>
      have hall := List.find?_range_eq_none.mp hf
      have hn := hall i (by omega)
      have hy : p i = true := (cc_scan_predicate a wanted i).mpr hbit
      simp only [hy, Bool.not_true, Bool.false_eq_true] at hn
    | some k => exact ⟨k, rfl⟩
  obtain ⟨k, hk⟩ := hex
  obtain ⟨hpk, hkmem, hprev⟩ := List.find?_range_eq_some.mp hk
  have hkle : k ≤ a.natAbs.log2+2 := by
    have := List.mem_range.mp hkmem
    omega
  refine ⟨k, ?_, hkle, (cc_scan_predicate a wanted k).mp hpk, ?_⟩
  · simp only [scanBit, Nat.zero_max, Nat.sub_zero, Nat.zero_add]
    change (match (List.range (a.natAbs.log2+3)).find? p with
      | some j => (j : Int)
      | none => -1) = (k : Int)
    rw [hk]
  · intro j hj hh
    have hn := hprev j hj
    have hy : p j = true := (cc_scan_predicate a wanted j).mpr hh
    simp only [hy, Bool.not_true, Bool.false_eq_true] at hn

theorem cc_scan_word (x : BigInt) (wanted : Bool) (hx : GMPInput x)
    (ha : cc_scan_value x.val wanted ≠ 0) :
    ∃ count : Clong, MPZ.scan wanted x (JInt.wrap .u64 0) = count ∧
      0 ≤ count.val ∧
      ArithDivides ((2 : Int)^count.val.toNat) (cc_scan_value x.val wanted) ∧
      ¬ ArithDivides ((2 : Int)^(count.val.toNat+1)) (cc_scan_value x.val wanted) := by
  obtain ⟨k, hk, hkle, hbit, hprev⟩ := cc_scan_exists x.val wanted ha
  have hlog := cc_input_log2_bound x hx
  let c := JInt.wrap .i64 (k : Int)
  have hw : c.val = (k : Int) := by
    change wrapInt .i64 (k : Int) = (k : Int)
    apply wrapInt_of_inRange
    change -(2 : Int)^63 ≤ (k : Int) ∧ (k : Int) ≤ (2 : Int)^63-1
    omega
  refine ⟨c, ?_, ?_, ?_⟩
  · change JInt.wrap .i64 (scanBit x.val 0 wanted) = c
    rw [hk]
  · rw [hw]
    omega
  · rw [hw]
    simp only [Int.toNat_natCast]
    exact cc_first_bit_valuation _ k hbit hprev

theorem BignumsGmpTrailingZeroValuation_proven : JuliaLean.Proofs.base.gmp.Round1.TrailingZeroValuation := by
  intro x hx
  by_cases hz : x.val = 0
  · simp only [hz, if_true]
    exact cc_trailing_zero_failure x hz
  · simp only [hz, if_false]
    obtain ⟨count, hscan, hnonneg, hdiv, hnotdiv⟩ := cc_scan_word x true hx hz
    have hne : count.val ≠ -1 := by omega
    refine ⟨count, ?_, hnonneg, hdiv, hnotdiv⟩
    change (if (MPZ.scan true x (JInt.wrap .u64 0)).val = -1
      then Except.error (JlError.domainError "`x` must be non-zero")
      else Except.ok (MPZ.scan true x (JInt.wrap .u64 0))) = Except.ok count
    rw [hscan, if_neg hne]

theorem cc_divides_neg (d a : Int) : ArithDivides d (-a) ↔ ArithDivides d a := by
  exact Int.dvd_neg

theorem BignumsGmpTrailingOneValuation_proven : JuliaLean.Proofs.base.gmp.Round1.TrailingOneValuation := by
  intro x hx
  by_cases hz : x.val = -1
  · simp only [hz, if_true]
    exact cc_trailing_one_failure x hz
  · simp only [hz, if_false]
    have hcomp : cc_scan_value x.val false ≠ 0 := by
      change -x.val-1 ≠ 0
      omega
    obtain ⟨count, hscan, hnonneg, hdiv, hnotdiv⟩ := cc_scan_word x false hx hcomp
    have hne : count.val ≠ -1 := by omega
    have heq : cc_scan_value x.val false = -(x.val+1) := by
      change -x.val-1 = -(x.val+1)
      omega
    rw [heq, cc_divides_neg] at hdiv hnotdiv
    refine ⟨count, ?_, hnonneg, hdiv, hnotdiv⟩
    change (if (MPZ.scan false x (JInt.wrap .u64 0)).val = -1
      then Except.error (JlError.domainError "`x` must not be equal to -1")
      else Except.ok (MPZ.scan false x (JInt.wrap .u64 0))) = Except.ok count
    rw [hscan, if_neg hne]

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: PowersNumberTheory.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

 theorem pn_power_value (a : Int) (n : Nat) : ArithPowerValue a n = a ^ n := by
  induction n with
  | zero =>
    change 1 = a ^ 0
    rw [Int.pow_zero]
  | succ n ih =>
    change a * ArithPowerValue a n = a ^ (n + 1)
    rw [ih, Int.pow_succ]
    exact Int.mul_comm _ _

 theorem BignumsGmpPowerUnsigned_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedPowerExact := by
  intro x y _
  change x.val ^ y.val.toNat = ArithPowerValue x.val y.val.toNat
  exact (pn_power_value _ _).symm

 theorem pn_add_step (a b : BigInt) :
    MPZ.binaryInplace .add a b = .ok (writeValue a (a.val + b.val)) := rfl

 theorem pn_sum_acc (xs : List BigInt) (acc : BigInt) :
    ∃ z, xs.foldlM (MPZ.binaryInplace .add) acc = .ok z ∧
      z.val = acc.val + (xs.map BigInt.val).foldr (fun a b => a + b) 0 := by
  induction xs generalizing acc with
  | nil =>
    refine ⟨acc, rfl, ?_⟩
    change acc.val = acc.val + 0
    exact (Int.add_zero _).symm
  | cons x xs ih =>
    obtain ⟨z, hz, hv⟩ := ih (writeValue acc (acc.val + x.val))
    refine ⟨z, ?_, ?_⟩
    · simpa only [List.foldlM_cons, pn_add_step, Bind.bind, Except.bind] using hz
    · change z.val = acc.val + (x.val + (xs.map BigInt.val).foldr (fun a b => a + b) 0)
      change z.val = acc.val + x.val + (xs.map BigInt.val).foldr (fun a b => a + b) 0 at hv
      rw [hv, Int.add_assoc]

 theorem BignumsGmpVariadicAddition_proven : JuliaLean.Proofs.base.gmp.Round1.VariadicAdditionExact := by
  intro x y rest _ _ _ _
  obtain ⟨z, hz, hv⟩ := pn_sum_acc (x :: y :: rest) (ofInt 0)
  refine ⟨z, hz, ?_⟩
  change z.val = 0 + _ at hv
  simpa only [Int.zero_add, List.map_cons] using hv

 theorem pn_wrap_sgn (n : Int) : (JInt.wrap .i64 (sgn n)).val = sgn n := by
  unfold sgn
  split
  · rfl
  · split <;> rfl

theorem pn_sgn_idem (n : Int) : sgn (sgn n) = sgn n := by
  by_cases hn : n < 0
  · simp only [sgn, hn, ite_true] <;> rfl
  · by_cases hp : n > 0
    · simp only [sgn, hn, hp, ite_false, ite_true] <;> rfl
    · simp only [sgn, hn, hp, ite_false] <;> rfl

 theorem pn_cmp_value (x y : BigInt) : (cmp x y).val = sgn (x.val - y.val) := by
  change (JInt.wrap .i64 (sgn (JInt.wrap .i64 (sgn (x.val - y.val))).val)).val = _
  rw [pn_wrap_sgn, pn_wrap_sgn, pn_sgn_idem]

 theorem BignumsGmpEqualityExact_proven : JuliaLean.Proofs.base.gmp.Round1.IntegerEqualityExact := by
  intro x y _ _
  change decide ((cmp x y).val = 0) = true ↔ x.val = y.val
  rw [decide_eq_true_eq, pn_cmp_value]
  unfold sgn
  split
  · omega
  · split <;> omega

theorem pn_isodd_value (y : BigInt) : isodd y = decide (y.val % 2 = 1) := by
  change decide ((y.val.fdiv ((2 : Int)^0)) % 2 = 1) = decide (y.val % 2 = 1)
  rw [Int.pow_zero, Int.fdiv_one]

theorem pn_abs_even_iff (n : Int) : n.natAbs % 2 = 0 ↔ n % 2 = 0 := by
  cases n with
  | ofNat n => omega
  | negSucc n => omega

theorem pn_neg_one_pow (n : Nat) : (-1 : Int)^n = if n % 2 = 0 then 1 else -1 := by
  change (if n % 2 = 0 then Int.ofNat (1 ^ n) else Int.negOfNat (1 ^ n)) = _
  rw [Nat.one_pow] <;> rfl

theorem pn_negative_unit_result (x y : BigInt) (hx : x.val = -1) :
    (if isodd y then x else neg x).val = (-1 : Int)^y.val.natAbs := by
  rw [pn_isodd_value, pn_neg_one_pow]
  by_cases hr : y.val % 2 = 1
  · have he : y.val.natAbs % 2 ≠ 0 := by
      intro he
      have := (pn_abs_even_iff y.val).mp he
      omega
    simp only [hr, decide_true, ite_true, he, ite_false, hx]
  · have he : y.val.natAbs % 2 = 0 := (pn_abs_even_iff y.val).mpr (by omega)
    simp only [hr, decide_false, Bool.false_eq_true, ite_false, he, ite_true]
    change -x.val = 1
    omega

theorem pn_neg_one_pow_square (n : Nat) : (-1 : Int)^n * (-1 : Int)^n = 1 := by
  rw [pn_neg_one_pow]
  split <;> decide

theorem BignumsGmpPowerBigint_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntPowerFullDomain := by
  intro x y _ _
  unfold ArithBigPowerContract
  by_cases hp : x.val = 1
  · have ha : powBigInt x y = .ok x := by
      rw [powBigInt, bigintPow, if_pos hp] <;> rfl
    by_cases hn : y.val < 0
    · rw [if_pos hn, if_pos (Or.inl hp)]
      refine ⟨x, ha, ?_⟩
      change x.val * ArithPowerValue x.val y.val.natAbs = 1
      rw [hp, pn_power_value, Int.one_pow, Int.mul_one]
    · have he : ¬ (y.val > IntTy.max .u64 ∧ 1 < x.val.natAbs) := by rw [hp]; omega
      rw [if_neg hn, if_neg he]
      refine ⟨x, ha, ?_⟩
      change x.val = ArithPowerValue x.val y.val.toNat
      rw [hp, pn_power_value, Int.one_pow]
  · by_cases hm : x.val = -1
    · have ha : powBigInt x y = .ok (if isodd y then x else neg x) := by
        rw [powBigInt, bigintPow, if_neg hp, if_pos hm] <;> rfl
      have hv := pn_negative_unit_result x y hm
      by_cases hn : y.val < 0
      · rw [if_pos hn, if_pos (Or.inr hm)]
        refine ⟨_, ha, ?_⟩
        change (if isodd y then x else neg x).val * ArithPowerValue x.val y.val.natAbs = 1
        rw [hv, hm, pn_power_value]
        exact pn_neg_one_pow_square _
      · have he : ¬ (y.val > IntTy.max .u64 ∧ 1 < x.val.natAbs) := by rw [hm]; omega
        rw [if_neg hn, if_neg he]
        refine ⟨_, ha, ?_⟩
        change (if isodd y then x else neg x).val = ArithPowerValue x.val y.val.toNat
        rw [hv, hm, pn_power_value]
        have habs : y.val.natAbs = y.val.toNat := by omega
        rw [habs]
    · by_cases hn : y.val < 0
      · rw [if_pos hn, if_neg (by exact fun h => h.elim hp hm)]
        refine ⟨"`y` cannot be negative.", ?_⟩
        rw [powBigInt, bigintPow, if_neg hp, if_neg hm, if_pos hn] <;> rfl
      · rw [if_neg hn]
        by_cases hb : y.val > IntTy.max .u64
        · by_cases hz : x.val = 0
          · have hnot : ¬ (y.val > IntTy.max .u64 ∧ 1 < x.val.natAbs) := by rw [hz]; omega
            rw [if_neg hnot]
            refine ⟨x, ?_, ?_⟩
            · rw [powBigInt, bigintPow, if_neg hp, if_neg hm, if_neg hn, if_pos hb, if_pos hz] <;> rfl
            · have he : y.val.toNat ≠ 0 := by
                have hm0 : (0 : Int) ≤ IntTy.max .u64 := by decide
                omega
              change x.val = ArithPowerValue x.val y.val.toNat
              rw [hz, pn_power_value, Int.zero_pow he]
          · have habs : 1 < x.val.natAbs := by omega
            rw [if_pos ⟨hb, habs⟩]
            refine ⟨"exponent is too large", ?_⟩
            rw [powBigInt, bigintPow, if_neg hp, if_neg hm, if_neg hn, if_pos hb, if_neg hz] <;> rfl
        · rw [if_neg (by exact fun h => hb h.1)]
          refine ⟨powUnsigned x (JInt.wrap .u64 y.val), ?_, ?_⟩
          · rw [powBigInt, bigintPow, if_neg hp, if_neg hm, if_neg hn, if_neg hb] <;> rfl
          · have hr : (JInt.wrap .u64 y.val).val = y.val := by
              change wrapInt .u64 y.val = y.val
              apply wrapInt_of_inRange
              constructor
              · change 0 ≤ y.val
                omega
              · omega
            change x.val ^ (JInt.wrap .u64 y.val).val.toNat = ArithPowerValue x.val y.val.toNat
            rw [hr, pn_power_value]

theorem BignumsGmpPowerBoolBase_proven : JuliaLean.Proofs.base.gmp.Round1.BooleanBasePowerExact := by
  intro x y _
  dsimp only [boolPowBigInt]
  cases x with
  | false =>
    by_cases hn : y.val < 0
    · simp [hn, JuliaLean.base.intfuncs.powerBool_Integer,
        JuliaLean.base.intfuncs.throwPowerDomain_Integer, ArithDomainFailure]
    · by_cases hz : y.val = 0
      · simp [hn, hz, JuliaLean.base.intfuncs.powerBool_Integer, ArithBoolValue,
          pn_power_value, Int.pow_zero, Pure.pure, Except.pure]
      · have hp : y.val.toNat ≠ 0 := by omega
        simp [hn, hz, JuliaLean.base.intfuncs.powerBool_Integer, ArithBoolValue,
          pn_power_value, Int.zero_pow hp, Pure.pure, Except.pure]
  | true =>
    by_cases hn : y.val < 0
    · simp [hn, JuliaLean.base.intfuncs.powerBool_Integer, ArithBoolValue,
        pn_power_value, Int.one_pow, Pure.pure, Except.pure]
    · simp [hn, JuliaLean.base.intfuncs.powerBool_Integer, ArithBoolValue,
        pn_power_value, Int.one_pow, Pure.pure, Except.pure]

theorem pn_sgn_zero (n : Int) : sgn n = 0 ↔ n = 0 := by
  unfold sgn
  split
  · omega
  · split <;> omega


theorem pn_float_flags {f : JuliaLean.Promotion.Fmt} (x : JuliaLean.Promotion.Fl f) :
    x.isfinite = true ↔ x.isnan = false ∧ x.isinf = false := by
  unfold JuliaLean.Promotion.Fl.isfinite JuliaLean.Promotion.Fl.isnan JuliaLean.Promotion.Fl.isinf
  by_cases he : x.expField = f.emax <;> by_cases hm : x.frac = 0 <;> simp [he, hm]

theorem pn_float64_equality (x : BigInt) (y : JuliaLean.base.float.FV .f64) :
    equalFloat x y = true ↔ ArithIntegerFloatEqual x.val y := by
  have hflags := pn_float_flags y
  by_cases hn : y.isnan = true
  · have hf : y.isfinite = false := by
      cases h : y.isfinite
      · rfl
      · have := hflags.mp h
        simp only [hn, Bool.true_eq_false, false_and] at this
    simp only [equalFloat, hn, ite_true, ArithIntegerFloatEqual, hf,
      Bool.false_eq_true, false_and]
  · have hn' : y.isnan = false := by
      cases h : y.isnan
      · rfl
      · exact False.elim (hn h)
    by_cases hi : y.isinf = true
    · have hf : y.isfinite = false := by
        cases h : y.isfinite
        · rfl
        · have := hflags.mp h
          simp only [hi, Bool.true_eq_false, and_false] at this
      cases hs : y.signbit <;>
        simp [equalFloat, cmpFloat, hn', JuliaLean.base.float.convertFloat, MPZ.cmpD,
          hi, hs, pn_wrap_sgn, sgn, ArithIntegerFloatEqual, hf,
          JInt.wrap, wrapInt, IntTy.bits, IntTy.signed]
    · have hi' : y.isinf = false := by
        cases h : y.isinf
        · rfl
        · exact False.elim (hi h)
      have hf : y.isfinite = true := hflags.mpr ⟨hn', hi'⟩
      simp only [equalFloat, cmpFloat, hn', Bool.false_eq_true, ite_false,
        JuliaLean.base.float.convertFloat, MPZ.cmpD, hi', pn_wrap_sgn,
        pn_sgn_idem, decide_eq_true_eq, pn_sgn_zero, ArithIntegerFloatEqual,
        hf, true_and]
      omega

theorem pn_float64_reverse_equality (x : BigInt) (y : JuliaLean.base.float.FV .f64) :
    floatEqual y x = true ↔ ArithIntegerFloatEqual x.val y :=
  pn_float64_equality x y

theorem pn_foldr_product_acc (xs : List Nat) (f : Nat → Int) (acc : Int) :
    xs.foldr (fun n z => f n * z) acc = xs.foldr (fun n z => f n * z) 1 * acc := by
  induction xs with
  | nil => exact (Int.one_mul acc).symm
  | cons x xs ih =>
    simp only [List.foldr_cons, ih, Int.mul_assoc]

theorem pn_factorial_value (n : Nat) : ArithFactorial n = (factorialNat n : Int) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold ArithFactorial
    rw [List.range_succ, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil, Int.mul_one]
    rw [pn_foldr_product_acc]
    change ArithFactorial n * ((n + 1 : Nat) : Int) = (factorialNat (n + 1) : Int)
    rw [ih, factorialNat, Int.natCast_mul, Int.mul_comm]

theorem pn_binomial_zero (n : BigInt) :
    ArithBinomial n.val 0 (binomialUnsigned n (JInt.wrap .u64 0)).val := by
  change (if n.val < 0 then (-1 : Int)^0 * (chooseNat (n.val.natAbs + 0 - 1) 0 : Int)
    else (chooseNat n.val.toNat 0 : Int)) * 1 = 1
  simp only [chooseNat, chooseLoop, Int.pow_zero, Int.one_mul, Int.mul_one, ite_self, Int.natCast_one]

theorem pn_binomial_one_value (n : BigInt) :
    (binomialUnsigned n (JInt.wrap .u64 1)).val = n.val := by
  change (if n.val < 0 then (-1 : Int)^1 * (chooseNat (n.val.natAbs + 1 - 1) 1 : Int)
    else (chooseNat n.val.toNat 1 : Int)) = n.val
  simp only [chooseNat, chooseLoop, Nat.zero_add, Nat.add_sub_cancel,
    Nat.sub_zero, Nat.div_one, Nat.one_mul, Int.pow_one, Int.neg_one_mul]
  split <;> omega

theorem pn_binomial_one (n : BigInt) :
    ArithBinomial n.val 1 (binomialUnsigned n (JInt.wrap .u64 1)).val := by
  rw [pn_binomial_one_value]
  change n.val * 1 = (n.val - 0) * 1
  rw [Int.sub_zero]

def pn_counter_one : BigInt :=
  ⟨1, ⟨1, by decide⟩, ⟨1, by decide⟩, [⟨1, by decide⟩]⟩

def pn_counter_neg_one : BigInt :=
  ⟨-1, ⟨1, by decide⟩, ⟨-1, by decide⟩, [⟨1, by decide⟩]⟩

def pn_counter_two : BigInt :=
  ⟨2, ⟨1, by decide⟩, ⟨1, by decide⟩, [⟨2, by decide⟩]⟩

def pn_counter_four : BigInt :=
  ⟨4, ⟨1, by decide⟩, ⟨1, by decide⟩, [⟨4, by decide⟩]⟩

theorem pn_counter_one_valid : GMPInput pn_counter_one := by
  unfold GMPInput Valid pn_counter_one
  decide

theorem pn_counter_neg_one_valid : GMPInput pn_counter_neg_one := by
  unfold GMPInput Valid pn_counter_neg_one
  decide

theorem pn_counter_two_valid : GMPInput pn_counter_two := by
  unfold GMPInput Valid pn_counter_two
  decide

theorem pn_counter_four_valid : GMPInput pn_counter_four := by
  unfold GMPInput Valid pn_counter_four
  decide

theorem BignumsGmpIsqrtBracket_refuted : ¬ JuliaLean.Proofs.base.gmp.Round1.IntegerSquareRootBracket := by
  intro contract
  have result := contract pn_counter_neg_one pn_counter_neg_one_valid
  change ArithDomainFailure (Except.error .divideError : Jl BigInt) at result
  obtain ⟨message, impossible⟩ := result
  cases impossible

theorem BignumsGmpPowerModulo_refuted : ¬ JuliaLean.Proofs.base.gmp.Round1.ModularPowerFullDomain := by
  intro contract
  have result := contract pn_counter_two pn_counter_neg_one pn_counter_four
    pn_counter_two_valid pn_counter_neg_one_valid pn_counter_four_valid
  change ArithDomainFailure (Except.error .divideError : Jl BigInt) at result
  obtain ⟨message, impossible⟩ := result
  cases impossible

theorem BignumsGmpExtendedGcd_refuted : ¬ JuliaLean.Proofs.base.gmp.Round1.ExtendedGCDExactAndMinimal := by
  intro contract
  have result := contract pn_counter_one pn_counter_one pn_counter_one_valid pn_counter_one_valid
  have bounds := result.2.2 (by decide)
  change (0 : Int) * 1 < 1 ∧ (1 : Int) * 1 < 1 at bounds
  omega

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: FactorialRefutation.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

/-- The constructible scalar integer 2^64, in its normalized two-limb layout. -/
def pn_counter_u64_limit : BigInt :=
  ⟨18446744073709551616, ⟨2, by decide⟩, ⟨2, by decide⟩,
    [⟨0, by decide⟩, ⟨1, by decide⟩]⟩

theorem pn_counter_u64_limit_valid : GMPInput pn_counter_u64_limit := by
  unfold GMPInput Valid pn_counter_u64_limit
  decide

theorem pn_factorial_u64_limit_error :
    JuliaLean.base.gmp.factorial pn_counter_u64_limit =
      Except.error (.inexactError (IntTy.name .u64)) := by
  rfl

theorem BignumsGmpFactorialExact_refuted :
    ¬ JuliaLean.Proofs.base.gmp.Round1.FactorialExactNaturalDomain := by
  intro contract
  have result := contract pn_counter_u64_limit pn_counter_u64_limit_valid
  have hnonnegative : ¬ pn_counter_u64_limit.val < 0 := by decide
  rw [if_neg hnonnegative] at result
  obtain ⟨z, hz, _⟩ := result
  rw [pn_factorial_u64_limit_error] at hz
  cases hz

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: Binomial.lean -/

/- Assembled after PowersNumberTheory, sharing its product-fold accumulator lemma. -/
namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

def pn_pascal : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => pn_pascal n k + pn_pascal n (k + 1)

theorem pn_pascal_zero (n : Nat) : pn_pascal n 0 = 1 := by
  cases n <;> rfl

theorem pn_pascal_above (n k : Nat) (h : n < k) : pn_pascal n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp only [pn_pascal] <;> omega
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [pn_pascal, ih k (by omega), ih (k+1) (by omega)]

theorem pn_pascal_recurrence (n k : Nat) :
    (k + 1) * pn_pascal n (k + 1) = (n - k) * pn_pascal n k := by
  induction n generalizing k with
  | zero => simp only [pn_pascal, Nat.mul_zero, Nat.zero_sub, Nat.zero_mul]
  | succ n ih =>
    cases k with
    | zero =>
      have h := ih 0
      simp only [Nat.zero_add, Nat.one_mul, Nat.sub_zero, pn_pascal_zero, Nat.mul_one] at h
      simp only [pn_pascal, pn_pascal_zero, Nat.zero_add, Nat.one_mul, Nat.sub_zero, Nat.mul_one]
      omega
    | succ k =>
      by_cases h : n ≤ k
      · have h1 : pn_pascal n (k+1) = 0 := pn_pascal_above n _ (by omega)
        have h2 : pn_pascal n (k+1+1) = 0 := pn_pascal_above n _ (by omega)
        rw [pn_pascal, pn_pascal, h1, h2]
        simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero]
        have he : n+1-(k+1)=0 := by omega
        rw [he, Nat.zero_mul]
      · have h1 := ih k
        have h2 := ih (k+1)
        rw [pn_pascal, pn_pascal, Nat.mul_add, Nat.mul_add]
        have he : n+1-(k+1)=n-k := by omega
        rw [he, ← h1, h2, ← Nat.add_mul, ← Nat.add_mul]
        congr 1
        omega

theorem pn_pascal_diagonal (n k : Nat) :
    (k + 1) * pn_pascal (n+1) (k+1) = (n+1) * pn_pascal n k := by
  rw [pn_pascal, Nat.mul_add, pn_pascal_recurrence]
  by_cases h : k ≤ n
  · rw [← Nat.add_mul]
    congr 1
    omega
  · rw [pn_pascal_above n k (by omega)]
    simp only [Nat.mul_zero, Nat.add_zero]



theorem pn_chooseLoop_eq (n left i : Nat) :
    chooseLoop n left i (pn_pascal n i) = pn_pascal n (i + left) := by
  induction left generalizing i with
  | zero => simp only [chooseLoop, Nat.add_zero]
  | succ left ih =>
    rw [chooseLoop]
    have hs : pn_pascal n i * (n-i) / (i+1) = pn_pascal n (i+1) := by
      rw [Nat.mul_comm, ← pn_pascal_recurrence]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [hs, ih]
    congr 1
    omega

theorem pn_chooseNat_eq (n k : Nat) : chooseNat n k = pn_pascal n k := by
  have h := pn_chooseLoop_eq n k 0
  simpa only [chooseNat, pn_pascal_zero, Nat.zero_add] using h

theorem pn_factorial_step (n : Nat) :
    ArithFactorial (n+1) = ArithFactorial n * ((n+1 : Nat) : Int) := by
  unfold ArithFactorial
  rw [List.range_succ, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, Int.natCast_one, Int.mul_one]
  exact pn_foldr_product_acc _ _ _

theorem pn_falling_step (a : Int) (n : Nat) :
    ArithFallingProduct a (n+1) = ArithFallingProduct a n * (a - n) := by
  unfold ArithFallingProduct
  rw [List.range_succ, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, Int.natCast_one, Int.mul_one]
  exact pn_foldr_product_acc _ _ _

theorem pn_positive_binomial (n k : Nat) :
    (pn_pascal n k : Int) * ArithFactorial k = ArithFallingProduct n k := by
  induction k with
  | zero => simp only [pn_pascal_zero, ArithFactorial, ArithFallingProduct, List.range_zero,
      List.foldr_nil, Int.natCast_one, Int.mul_one]
  | succ k ih =>
    rw [pn_factorial_step, pn_falling_step, ← ih]
    by_cases hk : k ≤ n
    · have hc : ((k+1 : Nat) : Int) * (pn_pascal n (k+1) : Int) =
          ((n-k : Nat) : Int) * (pn_pascal n k : Int) := by
        exact_mod_cast pn_pascal_recurrence n k
      have hnk : ((n-k : Nat) : Int) = (n : Int) - k := Int.ofNat_sub hk
      rw [hnk] at hc
      calc
        (pn_pascal n (k+1) : Int) * (ArithFactorial k * ((k+1 : Nat) : Int))
            = (((k+1 : Nat) : Int) * (pn_pascal n (k+1) : Int)) * ArithFactorial k := by
                simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
        _ = (((n : Int)-k) * (pn_pascal n k : Int)) * ArithFactorial k := by rw [hc]
        _ = (pn_pascal n k : Int) * ArithFactorial k * ((n : Int)-k) := by
              simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    · rw [pn_pascal_above n k (by omega), pn_pascal_above n (k+1) (by omega)]
      simp only [Int.natCast_zero, Int.zero_mul]

theorem pn_negative_binomial (m k : Nat) (hm : 0 < m) :
    ((-1 : Int)^k * (pn_pascal (m+k-1) k : Int)) * ArithFactorial k =
      ArithFallingProduct (-(m : Int)) k := by
  induction k with
  | zero => simp only [pn_pascal_zero, ArithFactorial, ArithFallingProduct,
      List.range_zero, List.foldr_nil, Int.pow_zero, Int.natCast_one, Int.mul_one]
  | succ k ih =>
    rw [pn_factorial_step, pn_falling_step, Int.pow_succ]
    have htop : m + (k+1) - 1 = (m+k-1)+1 := by omega
    have hc : ((k+1 : Nat) : Int) * (pn_pascal ((m+k-1)+1) (k+1) : Int) =
        ((m+k : Nat) : Int) * (pn_pascal (m+k-1) k : Int) := by
      have h := pn_pascal_diagonal (m+k-1) k
      have he : (m+k-1)+1=m+k := by omega
      rw [he] at h
      rw [he]
      exact_mod_cast h
    rw [htop]
    calc
      (((-1 : Int)^k * -1) * (pn_pascal ((m+k-1)+1) (k+1) : Int)) *
          (ArithFactorial k * ((k+1 : Nat) : Int))
          = (-1 : Int)^k * (((k+1 : Nat) : Int) * (pn_pascal ((m+k-1)+1) (k+1) : Int)) *
              ArithFactorial k * -1 := by
                simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (-1 : Int)^k * (((m+k : Nat) : Int) * (pn_pascal (m+k-1) k : Int)) *
              ArithFactorial k * -1 := by rw [hc]
      _ = ((-1 : Int)^k * (pn_pascal (m+k-1) k : Int)) * ArithFactorial k * (-(m : Int)-k) := by
            have he : -(m : Int) - k = ((m+k : Nat) : Int) * -1 := by omega
            rw [he]
            simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = ArithFallingProduct (-(m : Int)) k * (-(m : Int)-k) := by rw [ih]

theorem BignumsGmpBinomialUnsigned_proven : JuliaLean.Proofs.base.gmp.Round1.UnsignedBinomialExact := by
  intro n k _
  unfold ArithBinomial
  change (if n.val < 0 then (-1 : Int)^k.val.toNat * (chooseNat (n.val.natAbs+k.val.toNat-1) k.val.toNat : Int)
    else (chooseNat n.val.toNat k.val.toNat : Int)) * ArithFactorial k.val.toNat = ArithFallingProduct n.val k.val.toNat
  simp only [pn_chooseNat_eq]
  split
  · rename_i hn
    have h := pn_negative_binomial n.val.natAbs k.val.toNat (by omega)
    have he : -(n.val.natAbs : Int) = n.val := by omega
    simpa only [he] using h
  · rename_i hn
    have h := pn_positive_binomial n.val.toNat k.val.toNat
    have he : (n.val.toNat : Int) = n.val := by omega
    simpa only [he] using h

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: EqualityIEEE.lean -/

/- This fragment is assembled after FloatSupport and PowersNumberTheory. -/
namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float JuliaLean.Proofs.base.gmp.Round1

 theorem pn_equalFloat_widen (x : BigInt) {T : FTy} (y : FV T) :
    equalFloat x y = equalFloat x (convertFloat .f64 y) := by
  have h := PNFloat.pnf_widen64_facts y
  unfold equalFloat cmpFloat
  have hid (z : FV .f64) : convertFloat .f64 z = z := rfl
  simp only [hid, h.1]

 theorem pn_rational_equal_scale (a n N : Int) (d D : Nat)
    (hd : 0 < d) (hD : 0 < D) (h : N * (d : Int) = n * (D : Int)) :
    a * (D : Int) = N ↔ a * (d : Int) = n := by
  rw [← Int.mul_eq_mul_right_iff (by omega : (d : Int) ≠ 0)]
  rw [h, Int.mul_right_comm a (D : Int) (d : Int)]
  exact Int.mul_eq_mul_right_iff (by omega : (D : Int) ≠ 0)

 theorem pn_integerFloatEqual_widen (a : Int) {T : FTy} (y : FV T) :
    ArithIntegerFloatEqual a (convertFloat .f64 y) ↔ ArithIntegerFloatEqual a y := by
  have h := PNFloat.pnf_widen64_facts y
  unfold ArithIntegerFloatEqual
  rw [h.2.2.1]
  by_cases hf : y.isfinite = true
  · simp only [hf, true_and]
    exact pn_rational_equal_scale a y.toRat.1 (convertFloat .f64 y).toRat.1
      y.toRat.2 (convertFloat .f64 y).toRat.2
      (PNFloat.pnf_finite_den_pos y hf)
      (PNFloat.pnf_finite_den_pos (convertFloat .f64 y) (h.2.2.1.trans hf))
      (h.2.2.2.2 hf)
  · simp only [hf, Bool.false_eq_true, false_and]

 theorem BignumsGmpEqualityIeee_proven : JuliaLean.Proofs.base.gmp.Round1.IntegerFloatEqualityExact := by
  intro T x y _
  rw [pn_equalFloat_widen, pn_float64_equality]
  exact pn_integerFloatEqual_widen x.val y

 theorem BignumsGmpEqualityIeeeReverse_proven : JuliaLean.Proofs.base.gmp.Round1.FloatIntegerEqualityExact := by
  intro T x y hx
  exact BignumsGmpEqualityIeee_proven T x y hx

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: ClassificationWidenResults.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.gmp.Round1

theorem cl_tail_widen {T : FTy} (n : Int) (f : FV T) :
    (TailIntLEFloat n (convertFloat .f64 f) ↔ TailIntLEFloat n f) ∧
    (TailFloatLEInt (convertFloat .f64 f) n ↔ TailFloatLEInt f n) ∧
    (TailIntLTFloat n (convertFloat .f64 f) ↔ TailIntLTFloat n f) ∧
    (TailFloatLTInt (convertFloat .f64 f) n ↔ TailFloatLTInt f n) := by
  obtain ⟨_hn, hi, hfin, hsign, hrat⟩ := PNFloat.pnf_widen64_facts f
  by_cases hinf : f.isinf = true
  · have hf := (cl_ieee_inf_properties f hinf).2
    have hs := hsign hinf
    simp only [TailIntLEFloat, TailFloatLEInt, TailIntLTFloat, TailFloatLTInt,
      hi, hfin, hf, hs, Bool.false_eq_true, false_and, or_false, iff_self, and_self]
  · have hi0 : f.isinf = false := Bool.eq_false_iff.mpr hinf
    by_cases hf : f.isfinite = true
    · have hgfin : (convertFloat .f64 f).isfinite = true := hfin.trans hf
      have hd : (0 : Int) < ((convertFloat .f64 f).toRat.2 : Int) := by
        have := PNFloat.pnf_finite_den_pos (convertFloat .f64 f) hgfin
        omega
      have he : (0 : Int) < (f.toRat.2 : Int) := by
        have := PNFloat.pnf_finite_den_pos f hf
        omega
      have hr := hrat hf
      simp only [TailIntLEFloat, TailFloatLEInt, TailIntLTFloat, TailFloatLTInt,
        hi, hi0, hfin, hf, Bool.false_eq_true, eq_self_iff_true,
        false_and, true_and, false_or]
      exact ⟨cl_rational_cross_le _ _ _ _ _ hd he hr,
        cl_rational_cross_ge _ _ _ _ _ hd he hr,
        cl_rational_cross_lt _ _ _ _ _ hd he hr,
        cl_rational_cross_gt _ _ _ _ _ hd he hr⟩
    · have hf0 : f.isfinite = false := Bool.eq_false_iff.mpr hf
      simp only [TailIntLEFloat, TailFloatLEInt, TailIntLTFloat, TailFloatLTInt,
        hi, hi0, hfin, hf0, Bool.false_eq_true, false_and, false_or,
        iff_self, and_self]

theorem cl_cmpFloat_widen {T : FTy} (x : BigInt) (f : FV T) :
    cmpFloat x f = cmpFloat x (convertFloat .f64 f) := by
  have hn := (PNFloat.pnf_widen64_facts f).1
  unfold cmpFloat
  rw [hn]
  rfl

theorem BignumsGmpIeeeOrderExact_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntIEEEOrderExact := by
  intro T x f _hx
  obtain ⟨h1, h2, h3, h4⟩ := cl_ieee64_order x (convertFloat .f64 f)
  obtain ⟨t1, t2, t3, t4⟩ := cl_tail_widen x.val f
  have hn := (PNFloat.pnf_widen64_facts f).1
  have hc := cl_cmpFloat_widen x f
  have a1 : lessEqualFloat x f = lessEqualFloat x (convertFloat .f64 f) := by
    simp only [lessEqualFloat, hn, hc]
  have a2 : floatLessEqual f x = floatLessEqual (convertFloat .f64 f) x := by
    simp only [floatLessEqual, hn, hc]
  have a3 : lessFloat x f = lessFloat x (convertFloat .f64 f) := by
    simp only [lessFloat, hn, hc]
  have a4 : floatLess f x = floatLess (convertFloat .f64 f) x := by
    simp only [floatLess, hn, hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a1]
    exact h1.trans t1
  · rw [a2]
    exact h2.trans t2
  · rw [a3]
    exact h3.trans t3
  · rw [a4]
    exact h4.trans t4

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: BoundedConversion.lean -/

namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

/-- The normalized GMP representation of a UInt64-range nonnegative integer uses
at most one live limb, while permitting any unused allocated limb storage. -/
theorem cc_u64_input_size (x : BigInt) (hx : GMPInput x)
    (h0 : 0 ≤ x.val) (hb : x.val ≤ IntTy.max .u64) :
    0 ≤ x.size.val ∧ x.size.val ≤ 1 := by
  have hsign := cl_valid_sign x hx.1
  have hsize0 : 0 ≤ x.size.val := by omega
  refine ⟨hsize0, ?_⟩
  by_cases hz : x.val = 0
  · have hs := hx.1.2.2.2.1.mpr hz
    omega
  · have hused := ex_input_nonzero_size x hx hz
    have hin : x.size.val.natAbs-1 < x.d.length := by have := hx.1.1; omega
    have htop := ex_input_top_nonzero x hx hz
    have hbracket := (ex_top_bracket x.d (x.size.val.natAbs-1) hin htop).1
    have hlength : x.size.val.natAbs-1+1 = x.size.val.natAbs := by omega
    rw [hlength, ← cl_input_magnitude x hx.1] at hbracket
    have hval : x.val.natAbs < 2^64 := by
      change x.val ≤ (2 : Int)^64-1 at hb
      omega
    by_cases hs : x.size.val.natAbs ≤ 1
    · omega
    · have hindex : 64 ≤ 64*(x.size.val.natAbs-1) +
          (((x.d[x.size.val.natAbs-1]?).getD (JInt.wrap .u64 0)).val.toNat).log2 := by omega
      have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hindex
      omega

theorem cc_magnitude_take_one (xs : List Limb) :
    (limbMagnitude (xs.take 1) : Int) = ((xs[0]?).getD (JInt.wrap .u64 0)).val := by
  cases xs with
  | nil => rfl
  | cons l ls =>
    change (l.val.toNat : Int) = l.val
    have hr := l.property
    change 0 ≤ l.val ∧ l.val ≤ (2 : Int)^64-1 at hr
    exact Int.toNat_of_nonneg hr.1

theorem cc_one_limb_value (x : BigInt) (hx : Valid x) (hs : x.size.val = 1) :
    ((x.d[0]?).getD (JInt.wrap .u64 0)).val = x.val := by
  have hv := hx.2.2.1
  rw [hs] at hv
  change x.val = (limbMagnitude (x.d.take 1) : Int) at hv
  rw [cc_magnitude_take_one] at hv
  exact hv.symm

set_option maxRecDepth 4096 in
theorem cc_rem_u64_zero (x : BigInt) (hs : x.size.val = 0) :
    (remBits .u64 x).val = 0 := by
  have hcount : min x.size.val.natAbs ((IntTy.u64.bits+63)/64) = 0 := by rw [hs]; rfl
  have hneg : isnegative x = false := by unfold isnegative; rw [hs]; rfl
  rw [remBits, hcount, hneg]
  rfl

set_option maxRecDepth 4096 in
theorem cc_rem_u64_one (x : BigInt) (hs : x.size.val = 1) :
    (remBits .u64 x).val = ((x.d[0]?).getD (JInt.wrap .u64 0)).val := by
  let l := (x.d[0]?).getD (JInt.wrap .u64 0)
  have hcount : min x.size.val.natAbs ((IntTy.u64.bits+63)/64) = 1 := by rw [hs]; rfl
  have hneg : isnegative x = false := by unfold isnegative; rw [hs]; rfl
  have hw : (JInt.wrap .u64 l.val).val = l.val := by
    change wrapInt .u64 l.val = l.val
    exact wrapInt_of_inRange .u64 l.val l.property
  rw [remBits, hcount, hneg]
  change (JInt.wrap .u64 (0 + (JInt.wrap .u64 (l.val * 1)).val)).val = l.val
  simp only [Int.mul_one, Int.zero_add, hw]

/-- This is a bounded conversion helper for the factorial domain analysis;
it does not replace any frozen target statement. -/
theorem cc_convert_u64_bounded (n : BigInt) (hn : GMPInput n)
    (h0 : 0 ≤ n.val) (hb : n.val ≤ IntTy.max .u64) :
    ∃ c, convertUnsigned .u64 n = Except.ok c ∧ c.val = n.val := by
  obtain ⟨hs0, hs1⟩ := cc_u64_input_size n hn h0 hb
  refine ⟨remBits .u64 n, ?_, ?_⟩
  · change convertUnsignedLarge .u64 n = Except.ok (remBits .u64 n)
    unfold convertUnsignedLarge
    have hs : 0 ≤ n.size.val ∧ n.size.val ≤ ((IntTy.u64.bits+63)/64 : Nat) := by
      change 0 ≤ n.size.val ∧ n.size.val ≤ (1 : Int)
      exact ⟨hs0, hs1⟩
    rw [if_pos hs]
    rfl
  · by_cases hz : n.size.val = 0
    · rw [cc_rem_u64_zero n hz]
      exact (hn.1.2.2.2.1.mp hz).symm
    · have hs : n.size.val = 1 := by omega
      rw [cc_rem_u64_one n hs]
      exact cc_one_limb_value n hn.1 hs

end JuliaLean.ChatGPT.Batch4.Group7


/- Component: FactorialPartial.lean -/

/- These helpers document the supported portion of the factorial contract.
   The original unrestricted target is refuted separately. -/
namespace JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem pn_factorial_negative (n : BigInt) (hn : GMPInput n) (hneg : n.val < 0) :
    JuliaLean.base.gmp.factorial n = .error (.domainError "`n` must not be negative.") := by
  have hs : n.size.val < 0 := by
    by_cases hs : n.size.val < 0
    · exact hs
    · have hv := hn.1.2.2.1
      rw [if_neg hs] at hv
      omega
  simp only [JuliaLean.base.gmp.factorial, isnegative, hs, decide_true, ite_true]
  rfl

theorem pn_factorial_bounded_success (n : BigInt) (hn : GMPInput n)
    (h0 : 0 ≤ n.val) (hb : n.val ≤ IntTy.max .u64) :
    ArithReturns (JuliaLean.base.gmp.factorial n) (fun z => z = ArithFactorial n.val.toNat) := by
  obtain ⟨c, hc, hv⟩ := cc_convert_u64_bounded n hn h0 hb
  have hs : ¬ n.size.val < 0 := by
    intro hs
    have hvalue := hn.1.2.2.1
    have hzero := hn.1.2.2.2.1
    rw [if_pos hs] at hvalue
    have hz : n.val ≠ 0 := by
      intro hz
      have := hzero.mpr hz
      omega
    omega
  refine ⟨MPZ.facUi c, ?_, ?_⟩
  · simp only [JuliaLean.base.gmp.factorial, isnegative, hs, decide_false,
      Bool.false_eq_true, ite_false, hc, Bind.bind, Except.bind]
    rfl
  · change (factorialNat c.val.toNat : Int) = ArithFactorial n.val.toNat
    rw [hv, pn_factorial_value]

end JuliaLean.ChatGPT.Batch4.Group7
end

namespace JuliaLean.ChatGPT.Batch7.Group1

open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1

theorem BignumsGmpOverflowReporting_proven :
    JuliaLean.Proofs.base.gmp.Round1.BigIntOverflowReportingExact := by
  intro x y hx hy
  obtain ⟨⟨a, ha, haddv⟩, _⟩ :=
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpAdditionExact_proven x y hx hy
  obtain ⟨⟨s, hs, hsubv⟩, _⟩ :=
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSubtractionExact_proven x y hx hy
  obtain ⟨⟨m, hm, hmulv⟩, _⟩ :=
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpMultiplicationExact_proven x y hx hy
  have haddeq : a.val - x.val = y.val := haddv.1
  have hsubeq : s.val + y.val = x.val := hsubv.1
  refine ⟨a, s, m, ?_, ?_, ?_, ?_, ?_, hmulv, ?_, ?_⟩
  · unfold addWithOverflow
    rw [ha]
    rfl
  · omega
  · unfold subWithOverflow
    rw [hs]
    rfl
  · exact hsubeq
  · unfold mulWithOverflow
    rw [hm]
    rfl
  · intro t
    omega
  · intro t
    omega

theorem BignumsGmpCheckedPower_proven :
    JuliaLean.Proofs.base.gmp.Round1.CheckedBigIntPower := by
  intro x p hx hp
  unfold checkedBigPow
  exact JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerBigint_proven x p hx hp

theorem rcBoolDecide (c : Bool) (p : Prop) [Decidable p] (h : c = true ↔ p) :
    c = decide p := by
  by_cases hp : p
  · rw [decide_eq_true hp]
    exact h.mpr hp
  · rw [decide_eq_false hp]
    cases hc : c
    · rfl
    · exact absurd (h.mp hc) hp

theorem rcIszero (b : BigInt) (hb : GMPInput b) :
    JuliaLean.base.gmp.iszero b = decide (b.val = 0) :=
  rcBoolDecide _ _ (JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpZeroClassification_proven b hb)

theorem rcIsnegative (b : BigInt) (hb : GMPInput b) :
    JuliaLean.base.gmp.isnegative b = decide (b.val < 0) :=
  rcBoolDecide _ _ (JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignClassification_proven b hb).1

theorem rcSignbit (b : BigInt) (hb : GMPInput b) :
    JuliaLean.base.gmp.signbit b = decide (b.val < 0) :=
  rcBoolDecide _ _ (JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignClassification_proven b hb).2.2

theorem rcWrap (n : Int) (h0 : -1 ≤ n) (h1 : n ≤ 1) : (JInt.wrap .i64 n).val = n := by
  change wrapInt .i64 n = n
  apply wrapInt_of_inRange
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem rcSgnBounds (n : Int) : -1 ≤ sgn n ∧ sgn n ≤ 1 := by
  unfold sgn
  split
  · omega
  · split <;> omega

theorem rcSgnNeg (n : Int) : sgn n = -1 ↔ n < 0 := by
  unfold sgn
  split
  · omega
  · split <;> omega

theorem rcSgnZero (n : Int) : sgn n = 0 ↔ n = 0 := by
  unfold sgn
  split
  · omega
  · split <;> omega

theorem rcSgnPos (n : Int) : sgn n = 1 ↔ 0 < n := by
  unfold sgn
  split
  · omega
  · split <;> omega

theorem rcUnitNum (a b : Int) (hb : b = 0) (hg : Nat.gcd a.natAbs b.natAbs = 1) :
    a = 1 ∨ a = -1 := by
  rw [hb, Int.natAbs_zero, Nat.gcd_zero_right] at hg
  rcases Int.natAbs_eq a with h | h
  · rw [hg] at h
    omega
  · rw [hg] at h
    omega

theorem rcCanonical (a b c d : Int) (hab : Nat.gcd a.natAbs b.natAbs = 1)
    (hcd : Nat.gcd c.natAbs d.natAbs = 1) (hb : 0 < b) (hd : 0 < d)
    (h : a * d = c * b) : a = c ∧ b = d := by
  have habs := congrArg Int.natAbs h
  simp only [Int.natAbs_mul] at habs
  have hbd : b.natAbs ∣ d.natAbs := by
    apply Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hab)
    rw [habs]
    exact ⟨c.natAbs, Nat.mul_comm _ _⟩
  have hdb : d.natAbs ∣ b.natAbs := by
    apply Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hcd)
    rw [← habs]
    exact ⟨a.natAbs, Nat.mul_comm _ _⟩
  have hbd' : b = d := by
    have he := congrArg Int.ofNat (Nat.dvd_antisymm hbd hdb)
    change (b.natAbs : Int) = (d.natAbs : Int) at he
    simpa only [Int.natAbs_of_nonneg (Int.le_of_lt hb),
      Int.natAbs_of_nonneg (Int.le_of_lt hd)] using he
  refine ⟨?_, hbd'⟩
  rw [hbd'] at h
  exact (Int.mul_eq_mul_right_iff (by omega)).mp h

theorem rcCmpVal (x y : MPQ.Rational) (hxn : GMPInput x.num) (hxd : GMPInput x.den)
    (hyn : GMPInput y.num) (hyd : GMPInput y.den) :
    (MPQ.cmp x y).val =
      if x.den.val = 0 ∨ y.den.val = 0 then
        if y.den.val ≠ 0 then (if x.num.val < 0 then -1 else 1)
        else if x.den.val ≠ 0 then (if y.num.val < 0 then 1 else -1)
        else sgn ((if y.num.val < 0 then 1 else 0) - (if x.num.val < 0 then 1 else 0))
      else sgn (x.num.val * y.den.val - y.num.val * x.den.val) := by
  unfold MPQ.cmp
  rw [rcIszero x.den hxd, rcIszero y.den hyd, rcSignbit x.num hxn, rcSignbit y.num hyn,
    rcIsnegative x.num hxn, rcIsnegative y.num hyn]
  by_cases h1 : x.den.val = 0 <;> by_cases h2 : y.den.val = 0 <;>
    by_cases h3 : x.num.val < 0 <;> by_cases h4 : y.num.val < 0 <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false, Bool.or_true, Bool.true_or,
      Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, ite_true, ite_false,
      Bool.false_eq_true, true_or, or_true, or_false, ne_eq,
      not_true_eq_false, not_false_eq_true] <;>
    first
    | exact rcWrap _ (by decide) (by decide)
    | exact rcWrap _ (rcSgnBounds _).1 (rcSgnBounds _).2

theorem BignumsGmpRationalComparison_proven :
    JuliaLean.Proofs.base.gmp.Round1.BigIntRationalComparison := by
  intro x y hx hy
  obtain ⟨hxn, hxd, hxd0, hxg⟩ := hx
  obtain ⟨hyn, hyd, hyd0, hyg⟩ := hy
  dsimp only
  unfold TailRationalLT
  rw [rcCmpVal x y hxn hxd hyn hyd]
  by_cases h1 : x.den.val = 0
  · have hx1 := rcUnitNum x.num.val x.den.val h1 hxg
    by_cases h2 : y.den.val = 0
    · have hy1 := rcUnitNum y.num.val y.den.val h2 hyg
      rw [ite_eq_left (Or.inl h1), ite_eq_right (fun h => h h2),
        ite_eq_right (fun h => h h1)]
      rcases hx1 with hx1 | hx1 <;> rcases hy1 with hy1 | hy1 <;>
        rw [hx1, hy1, h1, h2] <;> decide
    · rw [ite_eq_left (Or.inl h1), ite_eq_left h2]
      rcases hx1 with hx1 | hx1
      · rw [hx1, h1, ite_eq_right (by decide)]
        omega
      · rw [hx1, h1, ite_eq_left (by decide)]
        omega
  · by_cases h2 : y.den.val = 0
    · have hy1 := rcUnitNum y.num.val y.den.val h2 hyg
      rw [ite_eq_left (Or.inr h2), ite_eq_right (fun h => h h2), ite_eq_left h1]
      rcases hy1 with hy1 | hy1
      · rw [hy1, h2, ite_eq_right (by decide)]
        omega
      · rw [hy1, h2, ite_eq_left (by decide)]
        omega
    · have hxp : 0 < x.den.val := by omega
      have hyp : 0 < y.den.val := by omega
      have hPQ : x.num.val * y.den.val = y.num.val * x.den.val ↔
          (x.num.val = y.num.val ∧ x.den.val = y.den.val) := by
        constructor
        · exact rcCanonical _ _ _ _ hxg hyg hxp hyp
        · intro h
          rw [h.1, h.2]
      rw [ite_eq_right (fun h => h.elim h1 h2), rcSgnNeg, rcSgnZero, rcSgnPos, ← hPQ]
      generalize x.num.val * y.den.val = P at *
      generalize y.num.val * x.den.val = Q at *
      omega

end JuliaLean.ChatGPT.Batch7.Group1

namespace JuliaLean.ChatGPT.Batch6.Group2

/-- `checked_mul` returns the independently specified repeated-addition product. -/
theorem BignumsGmpCheckedMultiplication_proven :
    JuliaLean.Proofs.base.gmp.Round1.CheckedBigIntMultiplication := by
  intro x y hx hy
  obtain ⟨⟨z, hz, hval⟩, _⟩ :=
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpMultiplicationExact_proven x y hx hy
  exact ⟨z, by simpa [JuliaLean.base.gmp.checkedMul] using hz, hval⟩

theorem tailTruncated_local (a b : Int) (hb : b ≠ 0) :
    JuliaLean.Proofs.base.gmp.Round1.TailTruncatedDivision
      a b (a.tdiv b) (a.tmod b) := by
  obtain ⟨heq, hbound, _⟩ :=
    JuliaLean.ChatGPT.Batch4.Group6.arith_tmod_pair a b hb
  refine ⟨heq, hbound, ?_⟩
  by_cases hr : a.tmod b = 0
  · exact Or.inl hr
  · right
    by_cases ha : 0 ≤ a
    · have h := Int.tmod_nonneg b ha
      have ha0 : a ≠ 0 := by
        intro hzero
        apply hr
        subst a
        exact Int.zero_tmod b
      exact Int.mul_pos (by omega) (by omega)
    · have h := Int.tmod_nonneg b (show 0 ≤ -a by omega)
      rw [Int.neg_tmod] at h
      exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)

theorem tailFloored_local (a b : Int) (hb : b ≠ 0) :
    JuliaLean.Proofs.base.gmp.Round1.TailFlooredDivision
      a b (a.fdiv b) (a.fmod b) := by
  obtain ⟨heq, hbound, hsign⟩ :=
    JuliaLean.ChatGPT.Batch4.Group6.arith_fmod_pair a b hb
  refine ⟨heq, hbound, ?_⟩
  unfold JuliaLean.Proofs.base.gmp.Round1.ArithRemainderSign at hsign
  rcases hsign with hzero | hsign
  · exact Or.inl hzero
  · by_cases hr : a.fmod b = 0
    · exact Or.inl hr
    · right
      by_cases hneg : a.fmod b < 0
      · exact Int.mul_pos_of_neg_of_neg hneg (hsign.mp hneg)
      · have hbpos : 0 < b := by
          by_cases hbneg : b < 0
          · exact False.elim (hneg (hsign.mpr hbneg))
          · omega
        exact Int.mul_pos (by omega) hbpos

theorem tailCeiling_local (a b : Int) (hb : b ≠ 0) :
    JuliaLean.Proofs.base.gmp.Round1.TailCeilingDivision
      a b (-((-a).fdiv b)) (a - (-((-a).fdiv b)) * b) := by
  obtain ⟨heq, hbound, hsign⟩ :=
    JuliaLean.ChatGPT.Batch4.Group6.arith_ceiling_pair a b hb
  have hr : a - (-((-a).fdiv b)) * b = -((-a).fmod b) := by omega
  rw [hr]
  refine ⟨heq, hbound, ?_⟩
  unfold JuliaLean.Proofs.base.gmp.Round1.ArithRemainderSign at hsign
  rcases hsign with hzero | hsign
  · exact Or.inl hzero
  · by_cases hz : -((-a).fmod b) = 0
    · exact Or.inl hz
    · right
      by_cases hneg : -((-a).fmod b) < 0
      · have hbpos : 0 < b := by
          have : -b < 0 := hsign.mp hneg
          omega
        exact Int.mul_neg_of_neg_of_pos hneg hbpos
      · have hbneg : b < 0 := by
          by_cases hbneg : b < 0
          · exact hbneg
          · have : -((-a).fmod b) < 0 := hsign.mpr (by omega)
            omega
        exact Int.mul_neg_of_pos_of_neg (by omega) hbneg

/-- All checked division and remainder calls return exact, uniquely characterized results. -/
theorem BignumsGmpCheckedDivision_proven :
    JuliaLean.Proofs.base.gmp.Round1.CheckedBigIntDivision := by
  intro x y _ _
  by_cases hy : y.val = 0
  · rw [if_pos hy]
    constructor
    · simpa [JuliaLean.base.gmp.checkedDiv, JuliaLean.base.gmp.div,
        JuliaLean.base.gmp.divRound] using
        (JuliaLean.ChatGPT.Batch4.Group6.arith_binary_error
          .tdivQ x y .divideError (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy]))
    constructor
    · simpa [JuliaLean.base.gmp.checkedRem, JuliaLean.base.gmp.rem] using
        (JuliaLean.ChatGPT.Batch4.Group6.arith_binary_error
          .tdivR x y .divideError (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy]))
    constructor
    · simpa [JuliaLean.base.gmp.checkedFld, JuliaLean.base.gmp.fld,
        JuliaLean.base.gmp.divRound] using
        (JuliaLean.ChatGPT.Batch4.Group6.arith_binary_error
          .fdivQ x y .divideError (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy]))
    constructor
    · simpa [JuliaLean.base.gmp.checkedMod, JuliaLean.base.gmp.mod] using
        (JuliaLean.ChatGPT.Batch4.Group6.arith_binary_error
          .fdivR x y .divideError (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy]))
    · simpa [JuliaLean.base.gmp.checkedCld, JuliaLean.base.gmp.cld,
        JuliaLean.base.gmp.divRound] using
        (JuliaLean.ChatGPT.Batch4.Group6.arith_binary_error
          .cdivQ x y .divideError (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy]))
  · rw [if_neg hy]
    have htmod : x.val - x.val.tdiv y.val * y.val = x.val.tmod y.val := by
      have h := Int.tdiv_mul_add_tmod x.val y.val
      omega
    have hfmod : x.val - x.val.fdiv y.val * y.val = x.val.fmod y.val := by
      have h := Int.fdiv_mul_add_fmod x.val y.val
      omega
    obtain ⟨q, hq, hqv⟩ :=
      JuliaLean.ChatGPT.Batch4.Group6.arith_binary_returns .tdivQ x y
        (x.val.tdiv y.val)
        (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy, Pure.pure, Except.pure])
        (fun z => z = x.val.tdiv y.val) rfl
    obtain ⟨r, hr, hrv⟩ :=
      JuliaLean.ChatGPT.Batch4.Group6.arith_binary_returns .tdivR x y
        (x.val.tmod y.val)
        (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy, htmod, Pure.pure, Except.pure])
        (fun z => z = x.val.tmod y.val) rfl
    obtain ⟨f, hf, hfv⟩ :=
      JuliaLean.ChatGPT.Batch4.Group6.arith_binary_returns .fdivQ x y
        (x.val.fdiv y.val)
        (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy, Pure.pure, Except.pure])
        (fun z => z = x.val.fdiv y.val) rfl
    obtain ⟨m, hm, hmv⟩ :=
      JuliaLean.ChatGPT.Batch4.Group6.arith_binary_returns .fdivR x y
        (x.val.fmod y.val)
        (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy, hfmod, Pure.pure, Except.pure])
        (fun z => z = x.val.fmod y.val) rfl
    obtain ⟨c, hc, hcv⟩ :=
      JuliaLean.ChatGPT.Batch4.Group6.arith_binary_returns .cdivQ x y
        (-((-x.val).fdiv y.val))
        (by simp [JuliaLean.base.gmp.MPZ.binaryValue, hy, Pure.pure, Except.pure])
        (fun z => z = -((-x.val).fdiv y.val)) rfl
    refine ⟨q, r, f, m, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [JuliaLean.base.gmp.checkedDiv, JuliaLean.base.gmp.div,
        JuliaLean.base.gmp.divRound] using hq
    · simpa [JuliaLean.base.gmp.checkedRem, JuliaLean.base.gmp.rem] using hr
    · simpa [JuliaLean.base.gmp.checkedFld, JuliaLean.base.gmp.fld,
        JuliaLean.base.gmp.divRound] using hf
    · simpa [JuliaLean.base.gmp.checkedMod, JuliaLean.base.gmp.mod] using hm
    · simpa [JuliaLean.base.gmp.checkedCld, JuliaLean.base.gmp.cld,
        JuliaLean.base.gmp.divRound] using hc
    · simpa [hqv, hrv] using tailTruncated_local x.val y.val hy
    · simpa [hfv, hmv] using tailFloored_local x.val y.val hy
    · simpa [hcv] using tailCeiling_local x.val y.val hy

end JuliaLean.ChatGPT.Batch6.Group2

section

set_option maxRecDepth 4096

namespace JuliaLean.ChatGPT.Batch9.Group19

open JuliaLean JuliaLean.base.gmp JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch7.Group1
open JuliaLean.ChatGPT.Batch4.Group7

/-- Truncation by a natural divisor preserves the sign of the numerator. -/
theorem g19_tdiv_nat (n : Int) (g : Nat) :
    n.tdiv (g : Int) =
      if n < 0 then -((n.natAbs / g : Nat) : Int)
      else ((n.natAbs / g : Nat) : Int) := by
  by_cases hn : n < 0
  · rw [ite_eq_left hn]
    have he : n = -(n.natAbs : Int) := by omega
    calc
      n.tdiv (g : Int) = (-(n.natAbs : Int)).tdiv (g : Int) := congrArg (fun x => x.tdiv (g : Int)) he
      _ = -((n.natAbs / g : Nat) : Int) := by
        rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _), Int.natCast_ediv]
  · rw [ite_eq_right hn]
    have he : n = (n.natAbs : Int) := by omega
    calc
      n.tdiv (g : Int) = (n.natAbs : Int).tdiv (g : Int) := congrArg (fun x => x.tdiv (g : Int)) he
      _ = ((n.natAbs / g : Nat) : Int) := by
        rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _), Int.natCast_ediv]

theorem g19_tdiv_abs (n : Int) (g : Nat) :
    (n.tdiv (g : Int)).natAbs = n.natAbs / g := by
  rw [g19_tdiv_nat]
  split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

theorem g19_tdiv_factor (n : Int) (g : Nat) (hg : g ∣ n.natAbs) :
    n.tdiv (g : Int) * (g : Int) = n := by
  have hmul : ((n.natAbs / g : Nat) : Int) * (g : Int) = (n.natAbs : Int) := by
    rw [← Int.natCast_mul, Nat.div_mul_cancel hg]
  rw [g19_tdiv_nat]
  split
  · rw [Int.neg_mul, hmul]
    omega
  · rw [hmul]
    omega

/-- The finite GMP normalization has a positive denominator, a coprime pair,
and exactly the original quotient. -/
theorem g19_canonicalize (out : MPQ.Rational) (n d : Int) (hd : d ≠ 0) :
    ∃ q, MPQ.canonicalize out n d = .ok q ∧ TailRationalCanonical q ∧
      0 < q.den.val ∧ q.num.val * d = n * q.den.val := by
  let g := Nat.gcd n.natAbs d.natAbs
  have hdabs : 0 < d.natAbs := by omega
  have hdp : 0 < d.natAbs / g := Nat.div_gcd_pos_of_pos_right n.natAbs hdabs
  have hc : Nat.gcd (n.natAbs / g) (d.natAbs / g) = 1 :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right hdabs
  have hnfac : n.tdiv (g : Int) * (g : Int) = n :=
    g19_tdiv_factor n g (Nat.gcd_dvd_left _ _)
  have hdfac : d.tdiv (g : Int) * (g : Int) = d :=
    g19_tdiv_factor d g (Nat.gcd_dvd_right _ _)
  have heq : (sgn d * n.tdiv (g : Int)) * d =
      n * (sgn d * d.tdiv (g : Int)) := by
    calc
      (sgn d * n.tdiv (g : Int)) * d =
          (sgn d * n.tdiv (g : Int)) * (d.tdiv (g : Int) * (g : Int)) := by rw [hdfac]
      _ = (n.tdiv (g : Int) * (g : Int)) * (sgn d * d.tdiv (g : Int)) := by
        simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = n * (sgn d * d.tdiv (g : Int)) := by rw [hnfac]
  have hp : 0 < sgn d * d.tdiv (g : Int) := by
    rw [g19_tdiv_nat]
    unfold sgn
    by_cases hn : d < 0
    · rw [ite_eq_left hn, ite_eq_left hn]
      omega
    · rw [ite_eq_right hn, ite_eq_right hn, ite_eq_left (by omega : d > 0)]
      omega
  have hgcd : Nat.gcd (sgn d * n.tdiv (g : Int)).natAbs
      (sgn d * d.tdiv (g : Int)).natAbs = 1 := by
    have hs : (sgn d).natAbs = 1 := by
      unfold sgn
      split
      · rfl
      · rw [ite_eq_left (by omega : d > 0)]
        rfl
    rw [Int.natAbs_mul, Int.natAbs_mul, hs, Nat.one_mul, Nat.one_mul,
      g19_tdiv_abs, g19_tdiv_abs]
    exact hc
  refine ⟨⟨writeValue out.num (sgn d * n.tdiv (g : Int)),
      writeValue out.den (sgn d * d.tdiv (g : Int))⟩, ?_, ?_, hp, heq⟩
  · simp only [MPQ.canonicalize, hd, ite_false]
    rfl
  · exact ⟨Int.le_of_lt hp, hgcd⟩

theorem g19_setBang_values (out x : MPQ.Rational)
    (hn : GMPInput x.num) (hd : GMPInput x.den) :
    (MPQ.setBang out x).num.val = x.num.val ∧
    (MPQ.setBang out x).den.val = x.den.val := by
  simp only [MPQ.setBang, MPQ.syncRational, MPQ.rawRational, MPQ.rawPair,
    MPQ.setPair, writeValue]
  constructor
  · have hv := (cl_ofInt_valid x.num.val (cl_input_limbs_length x.num hn)).2.2.1
    rw [JuliaLean.ChatGPT.Batch4.Group6.g6inv_ofInt_val] at hv
    exact hv.symm
  · have hv := (cl_ofInt_valid x.den.val (cl_input_limbs_length x.den hd)).2.2.1
    rw [JuliaLean.ChatGPT.Batch4.Group6.g6inv_ofInt_val] at hv
    exact hv.symm

/-- bignums-gmp-rational-construction. -/
theorem BignumsGmpRationalConstruction_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntRationalConstruction := by
  intro num den hnum hden
  have hznum := rcIszero num hnum
  have hzden := rcIszero den hden
  have hsnum := rcSignbit num hnum
  by_cases hd : den.val = 0
  · by_cases hn : num.val = 0
    · rw [ite_eq_left ⟨hn, hd⟩]
      refine ⟨"invalid rational: zero // zero", ?_⟩
      simp only [MPQ.construct, hzden, hd, hznum, hn, decide_true, ite_true]
      rfl
    · rw [ite_eq_right (fun h => hn h.1)]
      refine ⟨MPQ.setPair ⟨initBigInt, initBigInt⟩ (if num.val < 0 then -1 else 1) 0, ?_, ?_, ?_⟩
      · simp only [MPQ.construct, hzden, hd, hznum, hn, hsnum,
          decide_true, decide_false, decide_eq_true_eq, Bool.false_eq_true, ite_true, ite_false]
        rfl
      · change 0 ≤ (0 : Int) ∧ Nat.gcd (if num.val < 0 then -1 else 1).natAbs 0 = 1
        split <;> decide
      · rw [ite_eq_left hd]
        change (0 : Int) = 0 ∧ (0 < (if num.val < 0 then -1 else 1) ↔ 0 < num.val)
        split <;> omega
  · rw [ite_eq_right (fun h => hd h.2)]
    obtain ⟨q, hq, hc, hp, he⟩ := g19_canonicalize
      ⟨writeValue initBigInt num.val, writeValue initBigInt den.val⟩ num.val den.val hd
    refine ⟨q, ?_, hc, ?_⟩
    · simp only [MPQ.construct, hzden, hd, decide_false, Bool.false_eq_true, ite_false,
        MPZ.unary, MPZ.unaryBang, Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [JuliaLean.ChatGPT.Batch4.Group6.bwNaryWriteVal, JuliaLean.ChatGPT.Batch4.Group6.bwNaryWriteVal]
      exact hq
    · rw [ite_eq_right hd]
      exact ⟨hp, he⟩


theorem g19_setBang_canonical (out x : MPQ.Rational)
    (hx : TailRationalInput x) : TailRationalCanonical (MPQ.setBang out x) := by
  obtain ⟨hn, hd⟩ := g19_setBang_values out x hx.1 hx.2.1
  unfold TailRationalCanonical
  rw [hn, hd]
  exact hx.2.2

theorem g19_unit_bne (a b : Int) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    (decide (a < 0) != decide (b < 0)) = decide (a * b < 0) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide

theorem g19_unit_beq (a b : Int) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    (decide (a < 0) == decide (b < 0)) = decide (0 < a * b) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide

theorem g19_unit_mul_not_neg (a b : Int) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (h : ¬ a * b < 0) : a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [ha, hb] at h ⊢ <;> first | rfl | exact False.elim (h (by decide))

/-- bignums-gmp-rational-addition. -/
theorem BignumsGmpRationalAddition_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntRationalAddition := by
  intro x y hx hy
  let out : MPQ.Rational := ⟨initBigInt, initBigInt⟩
  have zx := rcIszero x.den hx.2.1
  have zy := rcIszero y.den hy.2.1
  have nx := rcIsnegative x.num hx.1
  have ny := rcIsnegative y.num hy.1
  have vx := g19_setBang_values out x hx.1 hx.2.1
  have vy := g19_setBang_values out y hy.1 hy.2.1
  by_cases hxd : x.den.val = 0
  · by_cases hyd : y.den.val = 0
    · have ux := rcUnitNum x.num.val x.den.val hxd hx.2.2.2
      have uy := rcUnitNum y.num.val y.den.val hyd hy.2.2.2
      have hsgn := g19_unit_bne x.num.val y.num.val ux uy
      have heval : MPQ.binary .add x y =
          if x.num.val * y.num.val < 0 then .error .divideError
          else .ok (MPQ.setBang out x) := by
        simp only [MPQ.binary, MPQ.binaryBang, MPQ.addBang, zx, zy, nx, ny,
          hxd, hyd, decide_true, Bool.true_or, Bool.true_and, hsgn,
          decide_eq_true_eq, ite_true]
        rfl
      by_cases hb : x.num.val * y.num.val < 0
      · rw [ite_eq_left ⟨hxd, hyd, hb⟩, heval, ite_eq_left hb]
      · rw [ite_eq_right (fun h => hb h.2.2)]
        refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
        · rw [heval, ite_eq_right hb]
        · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
          have he := g19_unit_mul_not_neg _ _ ux uy hb
          omega
    · rw [ite_eq_right (fun h => hyd h.2.1)]
      refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
      · simp only [MPQ.binary, MPQ.binaryBang, MPQ.addBang, zx, zy, hxd, hyd,
          decide_true, decide_false, Bool.true_or, Bool.true_and, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
        omega
  · by_cases hyd : y.den.val = 0
    · rw [ite_eq_right (fun h => hxd h.1)]
      refine ⟨MPQ.setBang out y, ?_, g19_setBang_canonical out y hy, ?_⟩
      · simp only [MPQ.binary, MPQ.binaryBang, MPQ.addBang, zx, zy, hxd, hyd,
          decide_true, decide_false, Bool.false_or, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), vy.1, vy.2]
        omega
    · have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
      have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
      have hprod : x.den.val * y.den.val ≠ 0 := Int.ne_of_gt (Int.mul_pos hxp hyp)
      obtain ⟨q, hq, hc, hp, he⟩ := g19_canonicalize out
        (x.num.val * y.den.val + y.num.val * x.den.val) (x.den.val * y.den.val) hprod
      rw [ite_eq_right (fun h => hxd h.1)]
      refine ⟨q, ?_, hc, ?_⟩
      · simp only [MPQ.binary, MPQ.binaryBang, MPQ.addBang, zx, zy, hxd, hyd,
          decide_false, Bool.false_or, Bool.false_eq_true, ite_false, MPQ.arithmetic]
        exact hq
      · rw [ite_eq_left ⟨hxp, hyp⟩]
        exact ⟨hp, he⟩


theorem g19_unit_mul_not_pos (a b : Int) (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) (h : ¬ 0 < a * b) : a = -b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [ha, hb] at h ⊢ <;> first | rfl | exact False.elim (h (by decide))

theorem g19_setSi_unit (out : MPQ.Rational) (n : Int) (hn : n = 1 ∨ n = -1) :
    TailRationalCanonical (MPQ.setSiBang out (JInt.wrap .i64 n) (JInt.wrap .u64 0)) ∧
    (MPQ.setSiBang out (JInt.wrap .i64 n) (JInt.wrap .u64 0)).num.val = n ∧
    (MPQ.setSiBang out (JInt.wrap .i64 n) (JInt.wrap .u64 0)).den.val = 0 := by
  have hw := rcWrap n (by omega) (by omega)
  simp only [TailRationalCanonical, MPQ.setSiBang, MPQ.setPair, JuliaLean.ChatGPT.Batch4.Group6.bwNaryWriteVal, hw]
  change (0 ≤ (0 : Int) ∧ Nat.gcd n.natAbs 0 = 1) ∧ True ∧ (0 : Int) = 0
  rcases hn with hn | hn <;> rw [hn] <;> decide

/-- bignums-gmp-rational-subtraction. -/
theorem BignumsGmpRationalSubtraction_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntRationalSubtraction := by
  intro x y hx hy
  let out : MPQ.Rational := ⟨initBigInt, initBigInt⟩
  have zx := rcIszero x.den hx.2.1
  have zy := rcIszero y.den hy.2.1
  have nx := rcIsnegative x.num hx.1
  have ny := rcIsnegative y.num hy.1
  have vx := g19_setBang_values out x hx.1 hx.2.1
  by_cases hxd : x.den.val = 0
  · by_cases hyd : y.den.val = 0
    · have ux := rcUnitNum x.num.val x.den.val hxd hx.2.2.2
      have uy := rcUnitNum y.num.val y.den.val hyd hy.2.2.2
      have hsgn := g19_unit_beq x.num.val y.num.val ux uy
      have heval : MPQ.binary .sub x y =
          if 0 < x.num.val * y.num.val then .error .divideError
          else .ok (MPQ.setBang out x) := by
        simp only [MPQ.binary, MPQ.binaryBang, MPQ.subBang, zx, zy, nx, ny,
          hxd, hyd, decide_true, Bool.true_or, Bool.true_and, hsgn,
          decide_eq_true_eq, ite_true]
        rfl
      by_cases hb : 0 < x.num.val * y.num.val
      · rw [ite_eq_left ⟨hxd, hyd, hb⟩, heval, ite_eq_left hb]
      · rw [ite_eq_right (fun h => hb h.2.2)]
        refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
        · rw [heval, ite_eq_right hb]
        · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
          have he := g19_unit_mul_not_pos _ _ ux uy hb
          omega
    · rw [ite_eq_right (fun h => hyd h.2.1)]
      refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
      · simp only [MPQ.binary, MPQ.binaryBang, MPQ.subBang, zx, zy, hxd, hyd,
          decide_true, decide_false, Bool.true_or, Bool.true_and, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
        omega
  · by_cases hyd : y.den.val = 0
    · rw [ite_eq_right (fun h => hxd h.1)]
      let s : Int := if y.num.val < 0 then 1 else -1
      have hs : s = 1 ∨ s = -1 := by dsimp only [s]; split <;> omega
      have hq := g19_setSi_unit out s hs
      refine ⟨MPQ.setSiBang out (JInt.wrap .i64 s) (JInt.wrap .u64 0), ?_, hq.1, ?_⟩
      · simp only [MPQ.binary, MPQ.binaryBang, MPQ.subBang, zx, zy,
          rcSignbit y.num hy.1, hxd, hyd, decide_true, decide_false,
          decide_eq_true_eq, Bool.false_or, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), hq.2.1, hq.2.2]
        dsimp only [s]
        split <;> omega
    · have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
      have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
      have hprod : x.den.val * y.den.val ≠ 0 := Int.ne_of_gt (Int.mul_pos hxp hyp)
      obtain ⟨q, hq, hc, hp, he⟩ := g19_canonicalize out
        (x.num.val * y.den.val - y.num.val * x.den.val) (x.den.val * y.den.val) hprod
      rw [ite_eq_right (fun h => hxd h.1)]
      refine ⟨q, ?_, hc, ?_⟩
      · simp only [MPQ.binary, MPQ.binaryBang, MPQ.subBang, zx, zy, hxd, hyd,
          decide_false, Bool.false_or, Bool.false_eq_true, ite_false, MPQ.arithmetic]
        exact hq
      · rw [ite_eq_left ⟨hxp, hyp⟩]
        exact ⟨hp, he⟩


theorem g19_product_sign (a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) :
    (0 < (if decide (a < 0) != decide (b < 0) then (-1 : Int) else 1)) ↔
      0 < a * b := by
  by_cases han : a < 0 <;> by_cases hbn : b < 0
  · have hp := Int.mul_pos_of_neg_of_neg han hbn
    simp only [han, hbn, decide_true, Bool.true_bne, Bool.not_true,
      Bool.false_eq_true, ite_false]
    omega
  · have hp := Int.mul_neg_of_neg_of_pos han (by omega : 0 < b)
    simp only [han, hbn, decide_true, decide_false, Bool.true_bne, Bool.not_false, ite_true]
    omega
  · have hp := Int.mul_neg_of_pos_of_neg (by omega : 0 < a) hbn
    simp only [han, hbn, decide_true, decide_false, Bool.false_bne, ite_true]
    omega
  · have hp := Int.mul_pos (by omega : 0 < a) (by omega : 0 < b)
    simp only [han, hbn, decide_false, Bool.false_bne, Bool.false_eq_true, ite_false]
    omega

/-- bignums-gmp-rational-multiplication. -/
theorem BignumsGmpRationalMultiplication_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntRationalMultiplication := by
  intro x y hx hy
  let out : MPQ.Rational := ⟨initBigInt, initBigInt⟩
  let s : Int := if isnegative x.num != isnegative y.num then -1 else 1
  have hs : s = 1 ∨ s = -1 := by dsimp only [s]; split <;> omega
  have hq := g19_setSi_unit out s hs
  have heval : MPQ.binary .mul x y =
      if x.den.val = 0 ∨ y.den.val = 0 then
        if x.num.val = 0 ∨ y.num.val = 0 then .error .divideError
        else .ok (MPQ.setSiBang out (JInt.wrap .i64 s) (JInt.wrap .u64 0))
      else MPQ.canonicalize out (x.num.val * y.num.val) (x.den.val * y.den.val) := by
    simp only [MPQ.binary, MPQ.binaryBang, MPQ.mulBang, MPQ.arithmetic,
      rcIszero x.den hx.2.1, rcIszero y.den hy.2.1,
      rcIszero x.num hx.1, rcIszero y.num hy.1,
      Bool.or_eq_true, decide_eq_true_eq]
    rfl
  by_cases hinf : x.den.val = 0 ∨ y.den.val = 0
  · by_cases hz : x.num.val = 0 ∨ y.num.val = 0
    · rw [ite_eq_left ⟨hinf, hz⟩, heval, ite_eq_left hinf, ite_eq_left hz]
    · rw [ite_eq_right (fun h => hz h.2)]
      refine ⟨MPQ.setSiBang out (JInt.wrap .i64 s) (JInt.wrap .u64 0), ?_, hq.1, ?_⟩
      · rw [heval, ite_eq_left hinf, ite_eq_right hz]
      · rw [ite_eq_right (by intro h; rcases hinf with h0 | h0 <;> omega), hq.2.1, hq.2.2]
        refine ⟨rfl, ?_⟩
        dsimp only [s]
        rw [rcIsnegative x.num hx.1, rcIsnegative y.num hy.1]
        exact g19_product_sign _ _ (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
  · have hxd : x.den.val ≠ 0 := fun h => hinf (Or.inl h)
    have hyd : y.den.val ≠ 0 := fun h => hinf (Or.inr h)
    have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
    have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
    have hprod : x.den.val * y.den.val ≠ 0 := Int.ne_of_gt (Int.mul_pos hxp hyp)
    obtain ⟨q, hqc, hc, hp, he⟩ := g19_canonicalize out
      (x.num.val * y.num.val) (x.den.val * y.den.val) hprod
    rw [ite_eq_right (fun h => hinf h.1)]
    refine ⟨q, ?_, hc, ?_⟩
    · rw [heval, ite_eq_right hinf]
      exact hqc
    · rw [ite_eq_left ⟨hxp, hyp⟩]
      exact ⟨hp, he⟩


theorem g19_setSi_zero (out : MPQ.Rational) :
    TailRationalCanonical (MPQ.setSiBang out (JInt.wrap .i64 0) (JInt.wrap .u64 1)) ∧
    (MPQ.setSiBang out (JInt.wrap .i64 0) (JInt.wrap .u64 1)).num.val = 0 ∧
    (MPQ.setSiBang out (JInt.wrap .i64 0) (JInt.wrap .u64 1)).den.val = 1 := by
  change (0 ≤ (1 : Int) ∧ Nat.gcd 0 1 = 1) ∧ (0 : Int) = 0 ∧ (1 : Int) = 1
  decide

/-- bignums-gmp-rational-division. -/
theorem BignumsGmpRationalDivision_proven : JuliaLean.Proofs.base.gmp.Round1.BigIntRationalDivision := by
  intro x y hx hy
  let out : MPQ.Rational := ⟨initBigInt, initBigInt⟩
  let sp : Int := if x.num.val < 0 then -1 else 1
  let sm : Int := if x.num.val < 0 then 1 else -1
  have hsp : sp = 1 ∨ sp = -1 := by dsimp only [sp]; split <;> omega
  have hsm : sm = 1 ∨ sm = -1 := by dsimp only [sm]; split <;> omega
  have hqp := g19_setSi_unit out sp hsp
  have hqm := g19_setSi_unit out sm hsm
  have hqz := g19_setSi_zero out
  have vx := g19_setBang_values out x hx.1 hx.2.1
  have heval : MPQ.binary .div x y =
      if x.den.val = 0 then
        if y.den.val = 0 then .error .divideError
        else if ¬ y.num.val < 0 then .ok (MPQ.setBang out x)
        else .ok (MPQ.setSiBang out (JInt.wrap .i64 sm) (JInt.wrap .u64 0))
      else if y.den.val = 0 then .ok (MPQ.setSiBang out (JInt.wrap .i64 0) (JInt.wrap .u64 1))
      else if y.num.val = 0 then
        if x.num.val = 0 then .error .divideError
        else .ok (MPQ.setSiBang out (JInt.wrap .i64 sp) (JInt.wrap .u64 0))
      else MPQ.canonicalize out (x.num.val * y.den.val) (x.den.val * y.num.val) := by
    simp only [MPQ.binary, MPQ.binaryBang, MPQ.divBang, MPQ.arithmetic,
      rcIszero x.den hx.2.1, rcIszero y.den hy.2.1,
      rcIszero x.num hx.1, rcIszero y.num hy.1,
      rcIsnegative y.num hy.1, rcSignbit x.num hx.1,
      not_decide_eq_true, decide_eq_true_eq]
    rfl
  by_cases hxd : x.den.val = 0
  · have ux := rcUnitNum x.num.val x.den.val hxd hx.2.2.2
    have hxn : x.num.val ≠ 0 := by omega
    by_cases hyd : y.den.val = 0
    · rw [ite_eq_left (Or.inl ⟨hxd, hyd⟩), heval, ite_eq_left hxd, ite_eq_left hyd]
    · have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
          (x.num.val = 0 ∧ y.num.val = 0)) := by
        intro h
        rcases h with h | h
        · exact hyd h.2
        · exact hxn h.1
      rw [ite_eq_right hbad]
      by_cases hny : y.num.val < 0
      · refine ⟨MPQ.setSiBang out (JInt.wrap .i64 sm) (JInt.wrap .u64 0), ?_, hqm.1, ?_⟩
        · rw [heval, ite_eq_left hxd, ite_eq_right hyd, ite_eq_right (fun h => h hny)]
        · rw [ite_eq_right (by intro h; omega), ite_eq_right hyd, hqm.2.1, hqm.2.2]
          dsimp only [sm]
          split <;> omega
      · refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
        · rw [heval, ite_eq_left hxd, ite_eq_right hyd, ite_eq_left hny]
        · rw [ite_eq_right (by intro h; omega), ite_eq_right hyd, vx.1, vx.2]
          omega
  · by_cases hyd : y.den.val = 0
    · have uy := rcUnitNum y.num.val y.den.val hyd hy.2.2.2
      have hyn : y.num.val ≠ 0 := by omega
      have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
          (x.num.val = 0 ∧ y.num.val = 0)) := by
        intro h
        rcases h with h | h
        · exact hxd h.1
        · exact hyn h.2
      rw [ite_eq_right hbad]
      refine ⟨MPQ.setSiBang out (JInt.wrap .i64 0) (JInt.wrap .u64 1), ?_, hqz.1, ?_⟩
      · rw [heval, ite_eq_right hxd, ite_eq_left hyd]
      · rw [ite_eq_right (by intro h; omega), ite_eq_left hyd]
        exact hqz.2
    · by_cases hyn : y.num.val = 0
      · by_cases hxn : x.num.val = 0
        · rw [ite_eq_left (Or.inr ⟨hxn, hyn⟩), heval, ite_eq_right hxd,
            ite_eq_right hyd, ite_eq_left hyn, ite_eq_left hxn]
        · have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
              (x.num.val = 0 ∧ y.num.val = 0)) := by
            intro h
            rcases h with h | h
            · exact hxd h.1
            · exact hxn h.1
          rw [ite_eq_right hbad]
          refine ⟨MPQ.setSiBang out (JInt.wrap .i64 sp) (JInt.wrap .u64 0), ?_, hqp.1, ?_⟩
          · rw [heval, ite_eq_right hxd, ite_eq_right hyd, ite_eq_left hyn, ite_eq_right hxn]
          · rw [ite_eq_right (by intro h; exact h.2.2 hyn), ite_eq_right hyd, hqp.2.1, hqp.2.2]
            dsimp only [sp]
            split <;> omega
      · have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
        have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
        obtain ⟨q, hq, hc, hp, he⟩ := g19_canonicalize out
          (x.num.val * y.den.val) (x.den.val * y.num.val) (Int.mul_ne_zero hxd hyn)
        have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
            (x.num.val = 0 ∧ y.num.val = 0)) := by
          intro h
          rcases h with h | h
          · exact hxd h.1
          · exact hyn h.2
        rw [ite_eq_right hbad]
        refine ⟨q, ?_, hc, ?_⟩
        · rw [heval, ite_eq_right hxd, ite_eq_right hyd, ite_eq_right hyn]
          exact hq
        · rw [ite_eq_left ⟨hxp, hyp, hyn⟩]
          exact ⟨hp, he⟩

end JuliaLean.ChatGPT.Batch9.Group19

end

namespace JuliaLean.Proofs.base.gmp
namespace ConversionRationalPromises
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float JuliaLean.Proofs.base.gmp.Round1

/-- Boolean construction represents exactly zero or one. -/
def BooleanConstruction : Prop :=
  ∀ b : Bool, (fromBool b).val = (if b then 1 else 0) ∧ Valid (fromBool b)

section
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2 Round1

theorem booleanConstruction_proven : BooleanConstruction := by
  intro b
  cases b with
  | false =>
    exact ⟨rfl, (JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedMachineConstruction_proven.1 (JInt.wrap .u64 0)).1.1⟩
  | true =>
    exact ⟨rfl, (JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedMachineConstruction_proven.1 (JInt.wrap .u64 1)).1.1⟩
end

/-- Unsafe conversion of a finite floating value truncates toward zero. -/
def UnsafeTruncateFinite : Prop :=
  ∀ (T : FTy) (x : FV T) (h : (convertFloat .f64 x).isfinite = true), let z := unsafeTruncFloat x h; let q := x.toRat; (z.val*(q.2 : Int)-q.1).natAbs < q.2 ∧ z.val.natAbs*q.2 ≤ q.1.natAbs

/-- Generated rational C callees have the GMP rational symbol prefix and resolve the libgmp binding in MPZ. -/
def RationalCalleeSymbol : Prop :=
  ∀ op : String, (MPQ.gmpq op).symbol.toList.drop 7 = op.toList ∧ (MPQ.gmpq op).symbol.toList.take 7 = "__gmpq_".toList ∧ (MPQ.gmpq op).moduleName = "MPZ" ∧ (MPQ.gmpq op).binding = "libgmp"

/-- Raw rational construction preserves both integer operands and their signed limb counts. -/
def RawRationalPreservesValues : Prop :=
  ∀ x y : BigInt, (MPQ.rawPair x y).rat.num = x ∧ (MPQ.rawPair x y).rat.den = y ∧ (MPQ.rawPair x y).numSize = x.size ∧ (MPQ.rawPair x y).denSize = y.size

open JuliaLean JuliaLean.base.gmp Round1

theorem rawRationalPreservesValues_proven : RawRationalPreservesValues := by
  intro x y
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Empty raw rational allocation initializes both integers to zero. -/
def RawRationalEmptyZero : Prop :=
  MPQ.rawEmpty.rat.num.val = 0 ∧ MPQ.rawEmpty.rat.den.val = 0

open JuliaLean JuliaLean.base.gmp Round1

theorem rawRationalEmptyZero_proven : RawRationalEmptyZero := ⟨rfl, rfl⟩

/-- Wrapping a rational preserves its numerator and denominator without normalization. -/
def RawRationalPreservesRatio : Prop :=
  ∀ x : MPQ.Rational, (MPQ.rawRational x).rat = x

open JuliaLean JuliaLean.base.gmp Round1

theorem rawRationalPreservesRatio_proven : RawRationalPreservesRatio := by
  intro x
  rfl

/-- The same-rational fast path retains the output record; copying shared integer storage preserves both values. -/
def RawRationalAliasCopyValues : Prop :=
  ∀ (out : MPQ.RawRational) (x : MPQ.Rational) (same nn nd dn dd : Bool), ∃ r, MPQ.rawAliased out x same nn nd dn dd = .ok r ∧ (if same then r = out else r.rat.num.val = x.num.val ∧ r.rat.den.val = x.den.val)

/-- Rational assignment preserves the exact numerator and denominator, including infinities. -/
def RationalAssignmentValues : Prop :=
  ∀ out x : MPQ.Rational, Valid x.num → Valid x.den → (MPQ.setBang out x).num.val = x.num.val ∧ (MPQ.setBang out x).den.val = x.den.val

/-- Integer assignment creates that integer over denominator one. -/
def RationalIntegerAssignment : Prop :=
  ∀ (out : MPQ.Rational) (x : BigInt), Valid x → (MPQ.setZBang out x).num.val = x.val ∧ (MPQ.setZBang out x).den.val = 1

/-- Allocated rational and integer copies preserve values and assign denominator one for integers. -/
def RationalCopyAllocation : Prop :=
  (∀ x : MPQ.Rational, Valid x.num → Valid x.den → (MPQ.set x).num.val = x.num.val ∧ (MPQ.set x).den.val = x.den.val) ∧ (∀ x : BigInt, Valid x → (MPQ.setZ x).num.val = x.val ∧ (MPQ.setZ x).den.val = 1)

/-- Scalar rational setters retain the supplied numerator and denominator exactly, allowing zero over zero. -/
def RationalScalarAssignment : Prop :=
  (∀ (out : MPQ.Rational) (a b : Culong), (MPQ.setUiBang out a b).num.val = a.val ∧ (MPQ.setUiBang out a b).den.val = b.val) ∧ (∀ (out : MPQ.Rational) (a : Clong) (b : Culong), (MPQ.setSiBang out a b).num.val = a.val ∧ (MPQ.setSiBang out a b).den.val = b.val)

open JuliaLean JuliaLean.base.gmp Round1

theorem rationalScalarAssignment_proven : RationalScalarAssignment := by
  exact ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-- Allocated scalar rational setters preserve the unchecked numerator and denominator. -/
def RationalScalarAllocation : Prop :=
  (∀ a b : Culong, (MPQ.setUi a b).num.val = a.val ∧ (MPQ.setUi a b).den.val = b.val) ∧ (∀ (a : Clong) (b : Culong), (MPQ.setSi a b).num.val = a.val ∧ (MPQ.setSi a b).den.val = b.val)

open JuliaLean JuliaLean.base.gmp Round1

theorem rationalScalarAllocation_proven : RationalScalarAllocation := by
  exact ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩

/-- Rational addition obeys exact cross-multiplication and the documented infinity and divide-error cases. -/
def RationalAdditionMutation : Prop :=
  ∀ out x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if x.den.val = 0 ∧ y.den.val = 0 ∧ x.num.val * y.num.val < 0 then
      MPQ.addBang out x y = .error .divideError
    else ∃ z, MPQ.addBang out x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) =
          (x.num.val * y.den.val + y.num.val * x.den.val) * z.den.val
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (x.den.val = 0 ∧ 0 < x.num.val) ∨ (y.den.val = 0 ∧ 0 < y.num.val))

/-- Rational subtraction obeys exact cross-multiplication and the documented infinity and divide-error cases. -/
def RationalSubtractionMutation : Prop :=
  ∀ out x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if x.den.val = 0 ∧ y.den.val = 0 ∧ 0 < x.num.val * y.num.val then
      MPQ.subBang out x y = .error .divideError
    else ∃ z, MPQ.subBang out x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) =
          (x.num.val * y.den.val - y.num.val * x.den.val) * z.den.val
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (x.den.val = 0 ∧ 0 < x.num.val) ∨ (y.den.val = 0 ∧ y.num.val < 0))

/-- Rational multiplication obeys exact cross-multiplication and the documented infinity and divide-error cases. -/
def RationalMultiplicationMutation : Prop :=
  ∀ out x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if (x.den.val = 0 ∨ y.den.val = 0) ∧ (x.num.val = 0 ∨ y.num.val = 0) then
      MPQ.mulBang out x y = .error .divideError
    else ∃ z, MPQ.mulBang out x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) = (x.num.val * y.num.val) * z.den.val
      else z.den.val = 0 ∧ (0 < z.num.val ↔ 0 < x.num.val * y.num.val)

/-- Rational division obeys exact cross-multiplication and the documented infinity and divide-error cases. -/
def RationalDivisionMutation : Prop :=
  ∀ out x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if (x.den.val = 0 ∧ y.den.val = 0) ∨ (x.num.val = 0 ∧ y.num.val = 0) then
      MPQ.divBang out x y = .error .divideError
    else ∃ z, MPQ.divBang out x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val ∧ y.num.val ≠ 0 then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.num.val) = (x.num.val * y.den.val) * z.den.val
      else if y.den.val = 0 then z.num.val = 0 ∧ z.den.val = 1
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (0 < x.num.val ∧ 0 ≤ y.num.val) ∨ (x.num.val < 0 ∧ y.num.val < 0))

/-- All in-place rational operators preserve exact finite arithmetic and the documented extended-value behavior. -/
def RationalArithmeticInplace : Prop :=
  (∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if x.den.val = 0 ∧ y.den.val = 0 ∧ x.num.val * y.num.val < 0 then
      MPQ.binaryInplace .add x y = .error .divideError
    else ∃ z, MPQ.binaryInplace .add x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) =
          (x.num.val * y.den.val + y.num.val * x.den.val) * z.den.val
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (x.den.val = 0 ∧ 0 < x.num.val) ∨ (y.den.val = 0 ∧ 0 < y.num.val))) ∧
  (∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if x.den.val = 0 ∧ y.den.val = 0 ∧ 0 < x.num.val * y.num.val then
      MPQ.binaryInplace .sub x y = .error .divideError
    else ∃ z, MPQ.binaryInplace .sub x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) =
          (x.num.val * y.den.val - y.num.val * x.den.val) * z.den.val
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (x.den.val = 0 ∧ 0 < x.num.val) ∨ (y.den.val = 0 ∧ y.num.val < 0))) ∧
  (∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if (x.den.val = 0 ∨ y.den.val = 0) ∧ (x.num.val = 0 ∨ y.num.val = 0) then
      MPQ.binaryInplace .mul x y = .error .divideError
    else ∃ z, MPQ.binaryInplace .mul x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.den.val) = (x.num.val * y.num.val) * z.den.val
      else z.den.val = 0 ∧ (0 < z.num.val ↔ 0 < x.num.val * y.num.val)) ∧
  (∀ x y : MPQ.Rational, TailRationalInput x → TailRationalInput y →
    if (x.den.val = 0 ∧ y.den.val = 0) ∨ (x.num.val = 0 ∧ y.num.val = 0) then
      MPQ.binaryInplace .div x y = .error .divideError
    else ∃ z, MPQ.binaryInplace .div x y = .ok z ∧ TailRationalCanonical z ∧
      if 0 < x.den.val ∧ 0 < y.den.val ∧ y.num.val ≠ 0 then
        0 < z.den.val ∧
        z.num.val * (x.den.val * y.num.val) = (x.num.val * y.den.val) * z.den.val
      else if y.den.val = 0 then z.num.val = 0 ∧ z.den.val = 1
      else z.den.val = 0 ∧
        (0 < z.num.val ↔
          (0 < x.num.val ∧ 0 ≤ y.num.val) ∨ (x.num.val < 0 ∧ y.num.val < 0)))

/-- All allocated rational operators preserve exact finite arithmetic and the documented extended-value behavior. -/
def RationalArithmeticAllocation : Prop :=
  Round1.BigIntRationalAddition ∧ Round1.BigIntRationalSubtraction ∧ Round1.BigIntRationalMultiplication ∧ Round1.BigIntRationalDivision

open JuliaLean JuliaLean.base.gmp Round1

theorem rationalArithmeticAllocation_proven : RationalArithmeticAllocation := by
  exact ⟨JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalAddition_proven,
    JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalSubtraction_proven,
    JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalMultiplication_proven,
    JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalDivision_proven⟩

end ConversionRationalPromises

namespace MethodPromises
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float JuliaLean.Proofs.base.gmp.Round1

def BinaryResult (op : MPZ.BinaryOp) (a b : Int) (result : Jl BigInt) : Prop :=
  match op with
  | .add => ArithReturns result (ArithAddition a b)
  | .sub => ArithReturns result (ArithSubtraction a b)
  | .mul => ArithReturns result (ArithMultiplication a b)
  | .gcd => ArithReturns result (ArithGCD a b)
  | .lcm => ArithReturns result (ArithLCM a b)
  | .tdivQ => ArithQuotientResult result .toZero a b
  | .fdivQ => ArithQuotientResult result .down a b
  | .cdivQ => ArithQuotientResult result .up a b
  | .tdivR => ArithRemainderResult result .toZero a b
  | .fdivR => ArithRemainderResult result .down a b
  | .cdivR => ArithRemainderResult result .up a b
  | .and => ArithReturns result (fun z => ∀ i, ArithBit z i ↔ ArithBit a i ∧ ArithBit b i)
  | .ior => ArithReturns result (fun z => ∀ i, ArithBit z i ↔ ArithBit a i ∨ ArithBit b i)
  | .xor => ArithReturns result (fun z => ∀ i, ArithBit z i ↔ (ArithBit a i ↔ ¬ ArithBit b i))

def UnsignedResult (op : MPZ.UnsignedOp) (a : Int) (b : Culong) (z : BigInt) : Prop :=
  match op with
  | .add => z.val - a = b.val
  | .sub => z.val + b.val = a
  | .mul => z.val = ArithRepeatedProduct a b.val
  | .mul2exp => z.val = a * (2 : Int)^b.val.toNat
  | .fdivQ2exp => ∃ r, a = z.val * (2 : Int)^b.val.toNat + r ∧ 0 ≤ r ∧ r < (2 : Int)^b.val.toNat
  | .pow => z.val = ArithPowerValue a b.val.toNat
  | .bin => ArithBinomial a b.val.toNat z.val

def UnaryResult (op : MPZ.UnaryOp) (a : Int) (result : Jl BigInt) : Prop :=
  match op with
  | .neg => ArithReturns result (fun z => z + a = 0)
  | .com => ArithReturns result (fun z => ∀ i, ArithBit z i ↔ ¬ ArithBit a i)
  | .set => ArithReturns result (fun z => z = a)
  | .sqrt => if a < 0 then result = .error .divideError
    else ArithReturns result (fun z => 0 ≤ z ∧ z*z ≤ a ∧ a < (z+1)*(z+1))

def InverseResult (a b : Int) (result : Jl (BigInt × Cint)) : Prop :=
  b ≠ 0 → ∃ z status, result = .ok (z,status) ∧
    (status.val = 0 ↔ Nat.gcd a.natAbs b.natAbs ≠ 1) ∧
    (status.val ≠ 0 → 0 ≤ z.val ∧ z.val < (b.natAbs : Int) ∧ ∃ k : Int, a*z.val = 1 + k*b)

def PowerModResult (a b c : Int) (result : Jl BigInt) : Prop :=
  c ≠ 0 → (0 ≤ b ∨ Nat.gcd a.natAbs c.natAbs = 1) →
    ArithReturns result (fun z => 0 ≤ z ∧ z < (c.natAbs : Int) ∧
      if b < 0 then ∃ k : Int, z * ArithPowerValue a b.natAbs = 1 + k*c
      else ∃ k : Int, ArithPowerValue a b.toNat = z + k*c)

def GcdextResult (a b : Int) (result : BigInt × BigInt × BigInt) : Prop :=
  ArithGCD a b result.1.val ∧ a*result.2.1.val+b*result.2.2.val = result.1.val


/-- Initialization represents zero and reserves at least the requested bits. -/
def Init2Zero : Prop :=
  ∀ (x : BigInt) (n : Culong), (n.val + 63) / 64 ≤ IntTy.max .i32 → (MPZ.init2 x n).val = 0 ∧ n.val ≤ 64*(MPZ.init2 x n).alloc.val

/-- Reallocation retains every value fitting in the requested bit capacity; new allocation represents zero. -/
def Realloc2PreservesFitting : Prop :=
  ∀ (x : BigInt) (n : Culong), x.val.natAbs < 2^n.val.toNat → (MPZ.realloc2 x n).val = x.val

open JuliaLean JuliaLean.base.gmp Round1

theorem realloc2PreservesFitting_proven : Realloc2PreservesFitting := by
  intro x n h
  simp only [MPZ.realloc2, h, ↓reduceIte, ofInt]

/-- Reallocation retains every value fitting in the requested bit capacity; new allocation represents zero. -/
def ReallocZero : Prop :=
  ∀ (n : Culong), (MPZ.realloc n).val = 0

open JuliaLean JuliaLean.base.gmp Round1

theorem reallocZero_proven : ReallocZero := by
  intro n
  simp [MPZ.realloc, MPZ.realloc2, initBigInt, ofInt]

/-- The base digit count is exact or one too large, and zero needs one digit. -/
def SizeinbaseDigitBound : Prop :=
  ∀ (x : BigInt) (b : Cint) (extra : Bool), 2 ≤ b.val → b.val ≤ 62 → let d := MPZ.sizeinbase x b extra; 1 ≤ d.val ∧ x.val.natAbs < b.val.toNat^d.val.toNat ∧ (d.val ≤ 1 ∨ b.val.toNat^(d.val.toNat-2) ≤ x.val.natAbs)

/-- Every generated binary operation satisfies its exact integer, quotient/remainder, divisibility or bitwise contract. -/
def BinaryMutation : Prop :=
  ∀ (op : MPZ.BinaryOp) (x a b : BigInt), BinaryResult op a.val b.val (MPZ.binaryBang op x a b)

/-- Every generated binary operation satisfies its exact integer, quotient/remainder, divisibility or bitwise contract. -/
def BinaryAllocation : Prop :=
  ∀ (op : MPZ.BinaryOp) (a b : BigInt), BinaryResult op a.val b.val (MPZ.binary op a b)

/-- Every generated binary operation satisfies its exact integer, quotient/remainder, divisibility or bitwise contract. -/
def BinaryInplace : Prop :=
  ∀ (op : MPZ.BinaryOp) (x b : BigInt), BinaryResult op x.val b.val (MPZ.binaryInplace op x b)

/-- Inverse reports coprimality and, on success, the least nonnegative modular inverse. -/
def InverseMutation : Prop :=
  ∀ (x a b : BigInt), InverseResult a.val b.val (MPZ.invertBang x a b)

/-- Inverse reports coprimality and, on success, the least nonnegative modular inverse. -/
def InverseInplace : Prop :=
  ∀ (x b : BigInt), InverseResult x.val b.val (MPZ.invertInplace x b)

/-- Allocated inverse returns the least nonnegative inverse when it exists. -/
def InverseAllocation : Prop :=
  ∀ a b : BigInt, b.val ≠ 0 → Nat.gcd a.val.natAbs b.val.natAbs = 1 → ArithReturns (MPZ.invert a b) (fun z => 0 ≤ z ∧ z < (b.val.natAbs : Int) ∧ ∃ k : Int, a.val*z = 1+k*b.val)

/-- Generated unsigned-scalar arithmetic, shifts, powers and binomial coefficients satisfy their integer contracts. -/
def UnsignedMutation : Prop :=
  ∀ (op : MPZ.UnsignedOp) (x a : BigInt) (b : Culong), UnsignedResult op a.val b (MPZ.unsignedBang op x a b)

/-- Generated unsigned-scalar arithmetic, shifts, powers and binomial coefficients satisfy their integer contracts. -/
def UnsignedAllocation : Prop :=
  ∀ (op : MPZ.UnsignedOp) (a : BigInt) (b : Culong), UnsignedResult op a.val b (MPZ.unsigned op a b)

/-- Generated unsigned-scalar arithmetic, shifts, powers and binomial coefficients satisfy their integer contracts. -/
def UnsignedInplace : Prop :=
  ∀ (op : MPZ.UnsignedOp) (x : BigInt) (b : Culong), UnsignedResult op x.val b (MPZ.unsignedInplace op x b)

/-- Unsigned-left subtraction reconstructs the minuend without overflow. -/
def UnsignedMinusMutation : Prop :=
  ∀ (x : BigInt) (a : Culong) (b : BigInt), (MPZ.uiSubBang x a b).val + b.val = a.val

open JuliaLean JuliaLean.base.gmp Round1

theorem unsignedMinusMutation_proven : UnsignedMinusMutation := by
  intro x a b
  change a.val - b.val + b.val = a.val
  omega

/-- Unsigned-left subtraction reconstructs the minuend without overflow. -/
def UnsignedMinusAllocation : Prop :=
  ∀ (a : Culong) (b : BigInt), (MPZ.uiSub a b).val + b.val = a.val

open JuliaLean JuliaLean.base.gmp Round1

theorem unsignedMinusAllocation_proven : UnsignedMinusAllocation := by
  intro a b
  exact unsignedMinusMutation_proven initBigInt a b

/-- Signed-scalar multiplication equals exact repeated addition, including typemin. -/
def SignedMultiplyMutation : Prop :=
  ∀ (x a : BigInt) (b : Clong), (MPZ.mulSiBang x a b).val = ArithRepeatedProduct a.val b.val

open JuliaLean JuliaLean.base.gmp Round1

theorem signedMultiplyMutation_proven : SignedMultiplyMutation := by
  intro x a b
  exact (JuliaLean.ChatGPT.Batch4.Group6.arith_repeated_product a.val b.val).symm

/-- Signed-scalar multiplication equals exact repeated addition, including typemin. -/
def SignedMultiplyAllocation : Prop :=
  ∀ (a : BigInt) (b : Clong), (MPZ.mulSi a b).val = ArithRepeatedProduct a.val b.val

open JuliaLean JuliaLean.base.gmp Round1

theorem signedMultiplyAllocation_proven : SignedMultiplyAllocation := by
  intro a b
  exact signedMultiplyMutation_proven initBigInt a b

/-- Signed-scalar multiplication equals exact repeated addition, including typemin. -/
def SignedMultiplyInplace : Prop :=
  ∀ (x : BigInt) (b : Clong), (MPZ.mulSiInplace x b).val = ArithRepeatedProduct x.val b.val

open JuliaLean JuliaLean.base.gmp Round1

theorem signedMultiplyInplace_proven : SignedMultiplyInplace := by
  intro x b
  exact signedMultiplyMutation_proven x x b

/-- Negation, complement, copy and square root meet their mathematical contracts. -/
def UnaryMutation : Prop :=
  ∀ (op : MPZ.UnaryOp) (x a : BigInt), UnaryResult op a.val (MPZ.unaryBang op x a)

/-- Negation, complement, copy and square root meet their mathematical contracts. -/
def UnaryAllocation : Prop :=
  ∀ (op : MPZ.UnaryOp) (a : BigInt), UnaryResult op a.val (MPZ.unary op a)

/-- Negation, complement, copy and square root meet their mathematical contracts. -/
def UnaryInplace : Prop :=
  ∀ (op : MPZ.UnaryOp) (x : BigInt), UnaryResult op x.val (MPZ.unaryInplace op x)

/-- GMP factorial is the product of the integers from one through the argument. -/
def FactorialMutation : Prop :=
  ∀ (x : BigInt) (n : Culong), (MPZ.facUiBang x n).val = ArithFactorial n.val.toNat

open JuliaLean JuliaLean.base.gmp Round1

theorem factorialMutation_proven : FactorialMutation := by
  intro x n
  exact (JuliaLean.ChatGPT.Batch4.Group7.pn_factorial_value n.val.toNat).symm

/-- GMP factorial is the product of the integers from one through the argument. -/
def FactorialAllocation : Prop :=
  ∀ (n : Culong), (MPZ.facUi n).val = ArithFactorial n.val.toNat

open JuliaLean JuliaLean.base.gmp Round1

theorem factorialAllocation_proven : FactorialAllocation := by
  intro n
  exact factorialMutation_proven initBigInt n

/-- Scalar setters preserve integers exactly and truncate finite doubles toward zero. -/
def ScalarAssignmentMutation : Prop :=
  (∀ (x : BigInt) (a : Culong), (MPZ.setUiBang x a).val = a.val) ∧ (∀ (x : BigInt) (a : Clong), (MPZ.setSiBang x a).val = a.val) ∧ (∀ (x : BigInt) (a : FV .f64) (h : a.isfinite = true), let z := MPZ.setDBang x a h; let q := a.toRat; (z.val*(q.2 : Int)-q.1).natAbs < q.2 ∧ z.val.natAbs*(q.2 : Int) ≤ q.1.natAbs)

/-- Scalar setters preserve integers exactly and truncate finite doubles toward zero. -/
def ScalarAssignmentAllocation : Prop :=
  (∀ (a : Culong), (MPZ.setUi a).val = a.val) ∧ (∀ (a : Clong), (MPZ.setSi a).val = a.val) ∧ (∀ (a : FV .f64) (h : a.isfinite = true), let z := MPZ.setD a h; let q := a.toRat; (z.val*(q.2 : Int)-q.1).natAbs < q.2 ∧ z.val.natAbs*(q.2 : Int) ≤ q.1.natAbs)

/-- Limb population count equals the number of set bits across the requested words. -/
def LimbPopcountPointer : Prop :=
  ∀ (d : List Limb) (s : Clong), 0 ≤ s.val → s.val ≤ (d.length : Int) → 64*s.val ≤ IntTy.max .i64 → (MPZ.mpnPopcountLimbs d s).val = ((d.take s.val.toNat).flatMap (fun w => (List.range 64).filter (fun i => decide ((2 : Int)^i ≤ w.val % (2 : Int)^(i+1))))).length

/-- BigInt limb population count is the Hamming weight of its absolute value. -/
def LimbPopcountBigint : Prop :=
  ∀ a : BigInt, GMPInput a → ArithBitCount (fun i => ArithBit (a.val.natAbs : Int) i) (MPZ.mpnPopcount a)

/-- Truncated quotient and remainder reconstruct the dividend and obey the remainder sign and magnitude laws. -/
def QuotientRemainderMutation : Prop :=
  ∀ (x y a b : BigInt), if b.val = 0 then MPZ.tdivQrBang x y a b = .error .divideError else ∃ q r, MPZ.tdivQrBang x y a b = .ok (q,r) ∧ ArithDivisionPair .toZero a.val b.val q.val r.val

section
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2 Round1

theorem quotientRemainderMutation_proven : QuotientRemainderMutation := by
  intro x y a b
  by_cases hb : b.val = 0
  · simp only [hb, if_true, MPZ.tdivQrBang, MPZ.binaryValue]
    rfl
  · simp only [hb, if_false]
    refine ⟨writeValue x (a.val.tdiv b.val), writeValue y (a.val-a.val.tdiv b.val*b.val), ?_, ?_⟩
    · simp only [MPZ.tdivQrBang, MPZ.binaryValue, hb, if_false]
      rfl
    · exact JuliaLean.ChatGPT.Batch4.Group7.cc_tdiv_pair a.val b.val hb
end

/-- Truncated quotient and remainder reconstruct the dividend and obey the remainder sign and magnitude laws. -/
def QuotientRemainderAllocation : Prop :=
  ∀ (a b : BigInt), if b.val = 0 then MPZ.tdivQr a b = .error .divideError else ∃ q r, MPZ.tdivQr a b = .ok (q,r) ∧ ArithDivisionPair .toZero a.val b.val q.val r.val

section
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2 Round1

theorem quotientRemainderAllocation_proven : QuotientRemainderAllocation := by
  intro a b
  exact quotientRemainderMutation_proven initBigInt initBigInt a b
end

/-- Modular exponentiation returns the least nonnegative residue, using an inverse for negative exponents. -/
def ModularPowerMutation : Prop :=
  ∀ (x a b c : BigInt), PowerModResult a.val b.val c.val (MPZ.powmBang x a b c)

/-- Modular exponentiation returns the least nonnegative residue, using an inverse for negative exponents. -/
def ModularPowerAllocation : Prop :=
  ∀ (a b c : BigInt), PowerModResult a.val b.val c.val (MPZ.powm a b c)

/-- Modular exponentiation returns the least nonnegative residue, using an inverse for negative exponents. -/
def ModularPowerInplace : Prop :=
  ∀ (x b c : BigInt), PowerModResult x.val b.val c.val (MPZ.powmInplace x b c)

/-- Extended gcd returns a nonnegative greatest common divisor and Bezout coefficients. -/
def ExtendedGcdMutation : Prop :=
  ∀ (x y z a b : BigInt), GcdextResult a.val b.val (MPZ.gcdextBang x y z a b)

/-- Extended gcd returns a nonnegative greatest common divisor and Bezout coefficients. -/
def ExtendedGcdAllocation : Prop :=
  ∀ (a b : BigInt), GcdextResult a.val b.val (MPZ.gcdext a b)

open JuliaLean JuliaLean.base.gmp Round1
open JuliaLean.ChatGPT.Batch4.Group6

private theorem gcdext_first_coefficient_abs (a b : Int) :
    (gmpGcdext a b).2.1 = (gmpGcdext a (b.natAbs : Int)).2.1 := by
  unfold gmpGcdext
  simp only [Int.natAbs_natCast, Int.natCast_eq_zero]
  by_cases heq : a.natAbs = b.natAbs
  · simp only [heq, ↓reduceIte]
  · simp only [heq, ↓reduceIte]
    by_cases hb : b = 0
    · subst b; simp
    · have hab : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
      simp only [hb, hab, ↓reduceIte]
      by_cases ha : a = 0
      · simp only [ha, ↓reduceIte]
      · simp only [ha, ↓reduceIte]
        split
        · rfl
        · split
          · rw [g6sgn_mul, g6sgn_mul]
            simp only [Int.natAbs_natCast]
          · rfl

private theorem inverse_congruence (a b : Int) (hb : b ≠ 0)
    (hg : Nat.gcd a.natAbs b.natAbs = 1) :
    ∃ k : Int, a * ((gmpGcdext a b).2.1 % (b.natAbs : Int)) = 1 + k*b := by
  have hpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  by_cases hu : b.natAbs = 1
  · have hbunit : b = 1 ∨ b = -1 := by
      have := Int.natAbs_eq b
      omega
    rcases hbunit with rfl | rfl
    · exact ⟨-1, by simp⟩
    · exact ⟨1, by simp⟩
  · have hcoeff := g6gcdext_inverse a b.natAbs (by omega) hg
    have hmod := g6inverse_congruence_mod a (b.natAbs : Int)
      (gmpGcdext a (b.natAbs : Int)).2.1 hcoeff
    rw [← gcdext_first_coefficient_abs] at hmod
    obtain ⟨k, hk⟩ := hmod
    have hsign : b = (b.natAbs : Int) ∨ b = -(b.natAbs : Int) := by
      have := Int.natAbs_eq b
      omega
    rcases hsign with hp | hn
    · refine ⟨k, ?_⟩
      calc
        _ = 1 + (b.natAbs : Int)*k := by omega
        _ = 1 + k*b := by rw [hp]; simp only [Int.natAbs_natCast, Int.mul_comm]
    · refine ⟨-k, ?_⟩
      calc
        _ = 1 + (b.natAbs : Int)*k := by omega
        _ = 1 + (-k)*b := by
          rw [hn]
          simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.neg_mul_neg, Int.mul_comm]

theorem inverseMutation_proven : InverseMutation := by
  intro x a b hb
  have hpos : 0 < (b.val.natAbs : Int) := by
    have := Int.natAbs_pos.mpr hb
    omega
  have hg := g6gcdext_gcd a.val b.val
  cases he : gmpGcdext a.val b.val with
  | mk g st =>
    cases st with
    | mk s t =>
      simp only [he] at hg
      by_cases hcop : Nat.gcd a.val.natAbs b.val.natAbs = 1
      · have hg1 : g = 1 := by simpa only [hcop, Int.natCast_one] using hg
        have hc := inverse_congruence a.val b.val hb hcop
        simp only [he] at hc
        subst g
        refine ⟨writeValue x (s % (b.val.natAbs : Int)), JInt.wrap .i32 1, ?_, ?_, ?_⟩
        · simp [MPZ.invertBang, hb, he, hcop, Pure.pure, Except.pure]
        · change (1 : Int) = 0 ↔ _
          simp [hcop]
        · intro _
          exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hpos, hc⟩
      · have hgne : g ≠ 1 := by omega
        refine ⟨x, JInt.wrap .i32 0, ?_, ?_, ?_⟩
        · simp [MPZ.invertBang, hb, he, hgne, Pure.pure, Except.pure]
        · change (0 : Int) = 0 ↔ _
          simp [hcop]
        · intro h
          exact False.elim (h rfl)

theorem inverseInplace_proven : InverseInplace := by
  intro x b
  exact inverseMutation_proven x x b

theorem inverseAllocation_proven : InverseAllocation := by
  intro a b hb hg
  obtain ⟨z, status, hret, hstatus, hvalue⟩ := inverseMutation_proven initBigInt a b hb
  have hs : status.val ≠ 0 := by
    intro hs
    exact hstatus.mp hs hg
  exact ⟨z, by simp [MPZ.invert, hret, Functor.map, Except.map], hvalue hs⟩


open JuliaLean JuliaLean.base.gmp
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean.base.gmp.MPZ (powModNat)

private theorem powMod_value (a : Int) (n : Nat) (m : Int) :
    powModNat a n m = a ^ n % m := by
  rw [powModNat]
  split
  · rename_i h
    simp [h]
  · rename_i h
    rw [powMod_value a (n / 2) m]
    split
    · rename_i odd
      have hn : n = n / 2 + n / 2 + 1 := by omega
      conv => rhs; rw [hn]
      simp only [Int.pow_succ, Int.pow_add, Int.mul_emod, Int.emod_emod]
    · rename_i even
      have hn : n = n / 2 + n / 2 := by omega
      conv => rhs; rw [hn]
      simp only [Int.pow_add, Int.mul_emod, Int.emod_emod]
termination_by n
decreasing_by apply Nat.div_lt_self <;> omega

private theorem pow_remainder (a m : Int) (n : Nat) :
    (a % m) ^ n % m = a ^ n % m := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Int.pow_succ, Int.mul_emod, ih, Int.emod_emod]

private theorem inverse_power_remainder (a r m : Int) (n : Nat)
    (h : a * r % m = 1 % m) :
    (r ^ n * a ^ n) % m = 1 % m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Int.pow_succ, Int.pow_succ]
    have rearrange : r ^ n * r * (a ^ n * a) = (r ^ n * a ^ n) * (a * r) := by
      ac_rfl
    rw [rearrange, Int.mul_emod, ih, h]
    rw [← Int.mul_emod, Int.one_mul]

private theorem remainder_difference (x y c : Int)
    (h : x % (c.natAbs : Int) = y % (c.natAbs : Int)) : c ∣ x - y := by
  apply Int.natAbs_dvd.mp
  apply Int.dvd_of_emod_eq_zero
  rw [Int.sub_emod, h]
  simp

theorem modularPowerMutation_proven : ModularPowerMutation := by
  intro out a b c hc admissible
  let m : Int := c.val.natAbs
  have hm : 0 < m := by
    dsimp [m]
    have hp := Int.natAbs_pos.mpr hc
    omega
  have hm0 : m ≠ 0 := by omega
  by_cases hb : b.val < 0
  · have hg : Nat.gcd a.val.natAbs c.val.natAbs = 1 :=
      admissible.resolve_left (by omega)
    obtain ⟨inverse, status, run, zeroStatus, bounds⟩ :=
      inverseMutation_proven initBigInt a c hc
    have nonzeroStatus : status.val ≠ 0 := by
      intro hs
      exact zeroStatus.mp hs hg
    obtain ⟨_, _, k, hk⟩ := bounds nonzeroStatus
    let value := powModNat (inverse.val % m) b.val.natAbs m
    have value_eq : value = inverse.val ^ b.val.natAbs % m := by
      dsimp [value]
      rw [powMod_value, pow_remainder]
    refine ⟨writeValue out value, ?_, ?_⟩
    · simp only [MPZ.powmBang, hc, hb, run, nonzeroStatus, m,
        Bool.false_eq_true, if_false, if_true, bind, Except.bind, pure, Except.pure]
      rfl
    · change 0 ≤ value ∧ value < m ∧ _
      refine ⟨?_, ?_, ?_⟩
      · rw [value_eq]; exact Int.emod_nonneg _ hm0
      · rw [value_eq]; exact Int.emod_lt_of_pos _ hm
      · rw [if_pos hb, pn_power_value, JuliaLean.ChatGPT.Batch4.Group6.g6inv_write_val]
        have hcmod : c.val % m = 0 := Int.emod_eq_zero_of_dvd Int.natAbs_dvd_self
        have hi : a.val * inverse.val % m = 1 % m := by
          rw [hk, Int.add_emod, Int.mul_emod, hcmod]
          simp
        have hp := inverse_power_remainder a.val inverse.val m b.val.natAbs hi
        have he : (value * a.val ^ b.val.natAbs) % m = 1 % m := by
          rw [value_eq]
          simpa only [Int.mul_emod, Int.emod_emod] using hp
        obtain ⟨j, hj⟩ := remainder_difference _ _ c.val he
        refine ⟨j, ?_⟩
        rw [Int.mul_comm c.val j] at hj
        omega
  · have hn : b.val.natAbs = b.val.toNat := by omega
    let value := powModNat (a.val % m) b.val.natAbs m
    have value_eq : value = a.val ^ b.val.toNat % m := by
      dsimp [value]
      rw [powMod_value, pow_remainder, hn]
    refine ⟨writeValue out value, ?_, ?_⟩
    · simp only [MPZ.powmBang, hc, hb, m, if_false,
        bind, Except.bind, pure, Except.pure]
      rfl
    · change 0 ≤ value ∧ value < m ∧ _
      refine ⟨?_, ?_, ?_⟩
      · rw [value_eq]; exact Int.emod_nonneg _ hm0
      · rw [value_eq]; exact Int.emod_lt_of_pos _ hm
      · rw [if_neg hb, pn_power_value, JuliaLean.ChatGPT.Batch4.Group6.g6inv_write_val]
        have he : a.val ^ b.val.toNat % m = value % m := by
          rw [value_eq, Int.emod_emod]
        obtain ⟨j, hj⟩ := remainder_difference _ _ c.val he
        refine ⟨j, ?_⟩
        rw [Int.mul_comm c.val j] at hj
        omega

theorem modularPowerAllocation_proven : ModularPowerAllocation := by
  intro a b c
  exact modularPowerMutation_proven initBigInt a b c

theorem modularPowerInplace_proven : ModularPowerInplace := by
  intro out b c
  exact modularPowerMutation_proven out out b c

end MethodPromises

def MethodBinaryOperators : Prop :=
  Round1.AdditionExact ∧ Round1.SubtractionExact ∧ Round1.MultiplicationExact ∧ Round1.ModuloEuclidean ∧ Round1.RemainderEuclidean ∧ Round1.GreatestCommonDivisor ∧ Round1.LeastCommonMultiple ∧ Round1.BitAndExact ∧ Round1.BitOrExact ∧ Round1.BitXorExact

namespace RemainingMethodPromises
open JuliaLean JuliaLean.base.gmp Round1

theorem sumExact_proven : SumExact := by
  intro xs _ _
  obtain ⟨z, hz, hv⟩ := JuliaLean.ChatGPT.Batch4.Group7.pn_sum_acc xs (ofInt 0)
  refine ⟨z, hz, ?_⟩
  change z.val = 0 + _ at hv
  simpa only [Int.zero_add] using hv
end RemainingMethodPromises
open JuliaLean JuliaLean.base.gmp Round1

theorem methodBinaryOperators_proven : MethodBinaryOperators := by
  exact ⟨JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpAdditionExact_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSubtractionExact_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpMultiplicationExact_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpModuloEuclidean_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpRemainderEuclidean_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpGcdUniversal_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpLcmUniversal_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpBitandExact_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpBitorExact_proven,
    JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpBitxorExact_proven⟩

namespace RemainingMethodPromises
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float Round1
open JuliaLean.ChatGPT.Batch4.Group6 JuliaLean.ChatGPT.Batch4.Group7

theorem integerCalleeSymbol_proven : IntegerCalleeSymbol := by
  intro op
  simp [MPZ.gmpz, String.toList_append]

theorem doubleComparisonExact_proven : DoubleComparisonExact := by
  intro a b hb
  have hi : b.isinf = false := by
    unfold JuliaLean.Promotion.Fl.isfinite at hb
    unfold JuliaLean.Promotion.Fl.isinf
    simp only [bne_iff_ne] at hb
    simp [hb]
  apply cc_comparison_of_sgn
  simp only [MPZ.cmpD, hi, Bool.false_eq_true, ite_false]
  rw [cl_wrap_sgn]

theorem writableLimbCapacity_proven : WritableLimbCapacity := by
  intro x n hn0 hnmax hx0
  dsimp only [MPZ.limbsWrite]
  refine ⟨rfl, ?_, List.prefix_append x.d _⟩
  change n.val ≤ wrapInt .i32 (max x.alloc.val n.val)
  have hx := x.alloc.property
  change -(2 : Int)^31 ≤ x.alloc.val ∧ x.alloc.val ≤ (2 : Int)^31 - 1 at hx
  change n.val ≤ (2 : Int)^31 - 1 at hnmax
  rw [wrapInt_of_inRange]
  · omega
  · change -(2 : Int)^31 ≤ max x.alloc.val n.val ∧ max x.alloc.val n.val ≤ (2 : Int)^31 - 1
    omega

theorem valid_limbs_length (x : BigInt) (hx : Valid x) :
    (limbsOfNat x.val.natAbs).length < 2^31 := by
  have hv := hx.2.2.1
  have habs : x.val.natAbs = limbMagnitude (x.d.take x.size.val.natAbs) := by
    rw [hv]
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]
  rw [habs]
  have hlen := cl_limbs_magnitude_length (x.d.take x.size.val.natAbs)
  have ht := List.length_take_le x.size.val.natAbs x.d
  have ha := hx.2.1
  have hbound := x.alloc.property
  change -(2 : Int)^31 ≤ x.alloc.val ∧ x.alloc.val ≤ (2 : Int)^31 - 1 at hbound
  omega

theorem flipsignPreservesMagnitude_proven : FlipsignPreservesMagnitude := by
  intro I signbit x y hx
  unfold flipsignInteger
  cases signbit y with
  | false => exact ⟨hx, rfl⟩
  | true =>
    simp only [ite_true]
    have hneg_val : (neg x).val = -x.val := g6inv_write_val initBigInt (-x.val)
    refine ⟨?_, by rw [hneg_val, Int.natAbs_neg]⟩
    apply cl_write_init_valid
    rw [Int.natAbs_neg]
    exact valid_limbs_length x hx

private theorem neg_unit_val (x : BigInt) (y : Int) (hm : x.val = -1) :
    (if decide (y % 2 = 1) then x else neg x).val = (-1 : Int) ^ y.natAbs := by
  rw [pn_neg_one_pow]
  have hneg_val : (neg x).val = -x.val := g6inv_write_val initBigInt (-x.val)
  by_cases hr : y % 2 = 1
  · have he : y.natAbs % 2 ≠ 0 := by
      intro he
      have := (pn_abs_even_iff y).mp he
      omega
    simp only [hr, decide_true, ite_true, he, ite_false, hm]
  · have he : y.natAbs % 2 = 0 := (pn_abs_even_iff y).mpr (by omega)
    simp only [hr, decide_false, Bool.false_eq_true, ite_false, he, ite_true, hneg_val]
    omega

theorem integerExponentAlias_proven : IntegerExponentAlias := by
  intro x y _
  unfold ArithBigPowerContract powInteger
  have hyval : (ofInt y).val = y := rfl
  simp only [hyval]
  by_cases hp : x.val = 1
  · have ha : bigintPow id (fun y => decide (y % 2 = 1)) y x = .ok x := by
      rw [bigintPow, ite_eq_left hp] <;> rfl
    by_cases hn : y < 0
    · rw [ite_eq_left hn, ite_eq_left (Or.inl hp)]
      refine ⟨x, ha, ?_⟩
      change x.val * ArithPowerValue x.val y.natAbs = 1
      rw [hp, pn_power_value, Int.one_pow, Int.mul_one]
    · have he : ¬ (y > IntTy.max .u64 ∧ 1 < x.val.natAbs) := by rw [hp]; omega
      rw [ite_eq_right hn, ite_eq_right he]
      refine ⟨x, ha, ?_⟩
      change x.val = ArithPowerValue x.val y.toNat
      rw [hp, pn_power_value, Int.one_pow]
  · by_cases hm : x.val = -1
    · have ha : bigintPow id (fun y => decide (y % 2 = 1)) y x =
          .ok (if decide (y % 2 = 1) then x else neg x) := by
        rw [bigintPow, ite_eq_right hp, ite_eq_left hm] <;> rfl
      have hv := neg_unit_val x y hm
      by_cases hn : y < 0
      · rw [ite_eq_left hn, ite_eq_left (Or.inr hm)]
        refine ⟨_, ha, ?_⟩
        change (if decide (y % 2 = 1) then x else neg x).val * ArithPowerValue x.val y.natAbs = 1
        rw [hv, hm, pn_power_value]
        exact pn_neg_one_pow_square _
      · have he : ¬ (y > IntTy.max .u64 ∧ 1 < x.val.natAbs) := by rw [hm]; omega
        rw [ite_eq_right hn, ite_eq_right he]
        refine ⟨_, ha, ?_⟩
        change (if decide (y % 2 = 1) then x else neg x).val = ArithPowerValue x.val y.toNat
        rw [hv, hm, pn_power_value]
        have habs : y.natAbs = y.toNat := by omega
        rw [habs]
    · by_cases hn : y < 0
      · rw [ite_eq_left hn, ite_eq_right (by exact fun h => h.elim hp hm)]
        refine ⟨"`y` cannot be negative.", ?_⟩
        rw [bigintPow, ite_eq_right hp, ite_eq_right hm]
        dsimp only [id]
        rw [ite_eq_left hn] <;> rfl
      · rw [ite_eq_right hn]
        by_cases hb : y > IntTy.max .u64
        · by_cases hz : x.val = 0
          · have hnot : ¬ (y > IntTy.max .u64 ∧ 1 < x.val.natAbs) := by rw [hz]; omega
            rw [ite_eq_right hnot]
            refine ⟨x, ?_, ?_⟩
            · rw [bigintPow, ite_eq_right hp, ite_eq_right hm]
              dsimp only [id]
              rw [ite_eq_right hn, ite_eq_left hb, ite_eq_left hz] <;> rfl
            · have he : y.toNat ≠ 0 := by
                have hm0 : (0 : Int) ≤ IntTy.max .u64 := by decide
                omega
              change x.val = ArithPowerValue x.val y.toNat
              rw [hz, pn_power_value, Int.zero_pow he]
          · have habs : 1 < x.val.natAbs := by omega
            rw [ite_eq_left ⟨hb, habs⟩]
            refine ⟨"exponent is too large", ?_⟩
            rw [bigintPow, ite_eq_right hp, ite_eq_right hm]
            dsimp only [id]
            rw [ite_eq_right hn, ite_eq_left hb, ite_eq_right hz] <;> rfl
        · rw [ite_eq_right (by exact fun h => hb h.1)]
          refine ⟨powUnsigned x (JInt.wrap .u64 y), ?_, ?_⟩
          · rw [bigintPow, ite_eq_right hp, ite_eq_right hm]
            dsimp only [id]
            rw [ite_eq_right hn, ite_eq_right hb] <;> rfl
          · have hr : (JInt.wrap .u64 y).val = y := by
              change wrapInt .u64 y = y
              apply wrapInt_of_inRange
              exact ⟨by change 0 ≤ y; omega, by omega⟩
            rw [show (powUnsigned x (JInt.wrap .u64 y)).val = x.val ^ (JInt.wrap .u64 y).val.toNat from
              g6inv_write_val _ _]
            rw [hr, pn_power_value]

theorem checkedIntegerExponent_proven : CheckedIntegerExponent := by
  intro x y hx
  exact integerExponentAlias_proven x y hx

theorem factorialNativeDomain_proven : FactorialNativeDomain := by
  intro n hn
  obtain ⟨hneg_iff, _⟩ := cl_valid_sign n hn.1
  by_cases hneg : n.val < 0
  · rw [ite_eq_left hneg]
    have hisneg : isnegative n = true := by
      simpa only [isnegative, decide_eq_true_eq] using hneg_iff.mpr hneg
    exact ⟨"`n` must not be negative.", by simp [JuliaLean.base.gmp.factorial, hisneg, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]⟩
  · rw [ite_eq_right hneg]
    have hisneg : isnegative n = false := by
      simpa only [isnegative, decide_eq_false_iff_not] using fun h => hneg (hneg_iff.mp h)
    have hconv := BignumsGmpExactUnsignedConversion_proven .u64 n (by decide) hn
    by_cases hgt : n.val > IntTy.max .u64
    · rw [ite_eq_left hgt]
      cases hc : convertUnsigned .u64 n with
      | ok c =>
        rw [hc] at hconv
        have hcprop : c.val ≤ IntTy.max .u64 := c.property.2
        have hnval : c.val = n.val := hconv
        omega
      | error e =>
        rw [hc] at hconv
        cases e with
        | inexactError fn =>
          exact ⟨fn, by simp [JuliaLean.base.gmp.factorial, hisneg, hc, Bind.bind, Except.bind]⟩
        | _ => contradiction
    · rw [ite_eq_right hgt]
      cases hc : convertUnsigned .u64 n with
      | error e =>
        rw [hc] at hconv
        cases e with
        | inexactError fn =>
          dsimp only [ConvExactBitsResult] at hconv
          have hmin : IntTy.min .u64 = 0 := rfl
          omega
        | _ => contradiction
      | ok c =>
        rw [hc] at hconv
        refine ⟨MPZ.facUi c, by simp [JuliaLean.base.gmp.factorial, hisneg, hc, Bind.bind, Except.bind, Pure.pure, Except.pure], ?_⟩
        have hfac := MethodPromises.factorialAllocation_proven c
        have hcval : c.val.toNat = n.val.toNat := by rw [hconv]
        rw [← hcval]
        exact hfac

end RemainingMethodPromises

namespace ConversionRationalPromises
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float Round1
open JuliaLean.ChatGPT.Batch4.Group6 JuliaLean.ChatGPT.Batch4.Group7
open JuliaLean.ChatGPT.Batch7.Group1 JuliaLean.ChatGPT.Batch9.Group19

theorem rationalCalleeSymbol_proven : RationalCalleeSymbol := by
  intro op
  simp [MPQ.gmpq, String.toList_append]

private theorem rawAliased_abstract (copy : BigInt → Jl BigInt)
    (hcopy : ∀ a : BigInt, ∃ b : BigInt, copy a = .ok b ∧ b.val = a.val)
    (out : MPQ.RawRational) (x : MPQ.Rational) (same nn nd dn dd : Bool) :
    ∃ r,
      (do
        if same then return out
        let num ← if nn || nd then copy x.num else pure x.num
        let den ← if dn || dd then copy x.den else pure x.den
        return MPQ.rawPair num den : Jl MPQ.RawRational) = .ok r ∧
      (if same then r = out else r.rat.num.val = x.num.val ∧ r.rat.den.val = x.den.val) := by
  obtain ⟨nc, hnc, hnc_val⟩ := hcopy x.num
  obtain ⟨dc, hdc, hdc_val⟩ := hcopy x.den
  cases same with
  | true => exact ⟨out, rfl, rfl⟩
  | false =>
    cases h1 : (nn || nd) <;> cases h2 : (dn || dd)
    · exact ⟨MPQ.rawPair x.num x.den, rfl, ⟨rfl, rfl⟩⟩
    · refine ⟨MPQ.rawPair x.num dc, ?_, ⟨rfl, hdc_val⟩⟩
      change (do let num ← pure x.num; let den ← copy x.den; return MPQ.rawPair num den) = _
      rw [hdc]; rfl
    · refine ⟨MPQ.rawPair nc x.den, ?_, ⟨hnc_val, rfl⟩⟩
      change (do let num ← copy x.num; let den ← pure x.den; return MPQ.rawPair num den) = _
      rw [hnc]; rfl
    · refine ⟨MPQ.rawPair nc dc, ?_, ⟨hnc_val, hdc_val⟩⟩
      change (do let num ← copy x.num; let den ← copy x.den; return MPQ.rawPair num den) = _
      rw [hnc, hdc]; rfl

theorem rawRationalAliasCopyValues_proven : RawRationalAliasCopyValues := by
  intro out x same nn nd dn dd
  exact rawAliased_abstract (MPZ.unary .set)
    (fun a => ⟨writeValue initBigInt a.val, rfl, g6inv_write_val initBigInt a.val⟩)
    out x same nn nd dn dd

theorem rationalAssignmentValues_proven : RationalAssignmentValues := by
  intro out x hn hd
  simp only [MPQ.setBang, MPQ.syncRational, MPQ.rawRational, MPQ.rawPair, MPQ.setPair, writeValue]
  constructor
  · have hv := (cl_ofInt_valid x.num.val (RemainingMethodPromises.valid_limbs_length x.num hn)).2.2.1
    rw [g6inv_ofInt_val] at hv
    exact hv.symm
  · have hv := (cl_ofInt_valid x.den.val (RemainingMethodPromises.valid_limbs_length x.den hd)).2.2.1
    rw [g6inv_ofInt_val] at hv
    exact hv.symm

theorem rationalIntegerAssignment_proven : RationalIntegerAssignment := by
  intro out x hx
  simp only [MPQ.setZBang, MPQ.syncRational, MPQ.rawRational, MPQ.rawPair, MPQ.setPair, writeValue]
  constructor
  · have hv := (cl_ofInt_valid x.val (RemainingMethodPromises.valid_limbs_length x hx)).2.2.1
    rw [g6inv_ofInt_val] at hv
    exact hv.symm
  · have hv := cl_valid_one.2.2.1
    rw [g6inv_ofInt_val] at hv
    exact hv.symm

theorem rationalCopyAllocation_proven : RationalCopyAllocation := by
  exact ⟨fun x hn hd => rationalAssignmentValues_proven ⟨initBigInt, initBigInt⟩ x hn hd,
    fun x hx => rationalIntegerAssignment_proven ⟨initBigInt, initBigInt⟩ x hx⟩

set_option maxRecDepth 4096 in
theorem rationalAdditionMutation_proven : RationalAdditionMutation := by
  intro out x y hx hy
  have zx := rcIszero x.den hx.2.1
  have zy := rcIszero y.den hy.2.1
  have nx := rcIsnegative x.num hx.1
  have ny := rcIsnegative y.num hy.1
  have vx := g19_setBang_values out x hx.1 hx.2.1
  have vy := g19_setBang_values out y hy.1 hy.2.1
  by_cases hxd : x.den.val = 0
  · by_cases hyd : y.den.val = 0
    · have ux := rcUnitNum x.num.val x.den.val hxd hx.2.2.2
      have uy := rcUnitNum y.num.val y.den.val hyd hy.2.2.2
      have hsgn := g19_unit_bne x.num.val y.num.val ux uy
      have heval : MPQ.addBang out x y =
          if x.num.val * y.num.val < 0 then .error .divideError
          else .ok (MPQ.setBang out x) := by
        simp only [MPQ.addBang, zx, zy, nx, ny,
          hxd, hyd, decide_true, Bool.true_or, Bool.true_and, hsgn,
          decide_eq_true_eq, ite_true]
        rfl
      by_cases hb : x.num.val * y.num.val < 0
      · rw [ite_eq_left ⟨hxd, hyd, hb⟩, heval, ite_eq_left hb]
      · rw [ite_eq_right (fun h => hb h.2.2)]
        refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
        · rw [heval, ite_eq_right hb]
        · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
          have he := g19_unit_mul_not_neg _ _ ux uy hb
          omega
    · rw [ite_eq_right (fun h => hyd h.2.1)]
      refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
      · simp only [MPQ.addBang, zx, zy, hxd, hyd,
          decide_true, decide_false, Bool.true_or, Bool.true_and, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
        omega
  · by_cases hyd : y.den.val = 0
    · rw [ite_eq_right (fun h => hxd h.1)]
      refine ⟨MPQ.setBang out y, ?_, g19_setBang_canonical out y hy, ?_⟩
      · simp only [MPQ.addBang, zx, zy, hxd, hyd,
          decide_true, decide_false, Bool.false_or, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), vy.1, vy.2]
        omega
    · have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
      have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
      have hprod : x.den.val * y.den.val ≠ 0 := Int.ne_of_gt (Int.mul_pos hxp hyp)
      obtain ⟨q, hq, hc, hp, he⟩ := g19_canonicalize out
        (x.num.val * y.den.val + y.num.val * x.den.val) (x.den.val * y.den.val) hprod
      rw [ite_eq_right (fun h => hxd h.1)]
      refine ⟨q, ?_, hc, ?_⟩
      · simp only [MPQ.addBang, zx, zy, hxd, hyd,
          decide_false, Bool.false_or, Bool.false_eq_true, ite_false, MPQ.arithmetic]
        exact hq
      · rw [ite_eq_left ⟨hxp, hyp⟩]
        exact ⟨hp, he⟩

set_option maxRecDepth 4096 in
theorem rationalSubtractionMutation_proven : RationalSubtractionMutation := by
  intro out x y hx hy
  have zx := rcIszero x.den hx.2.1
  have zy := rcIszero y.den hy.2.1
  have nx := rcIsnegative x.num hx.1
  have ny := rcIsnegative y.num hy.1
  have vx := g19_setBang_values out x hx.1 hx.2.1
  by_cases hxd : x.den.val = 0
  · by_cases hyd : y.den.val = 0
    · have ux := rcUnitNum x.num.val x.den.val hxd hx.2.2.2
      have uy := rcUnitNum y.num.val y.den.val hyd hy.2.2.2
      have hsgn := g19_unit_beq x.num.val y.num.val ux uy
      have heval : MPQ.subBang out x y =
          if 0 < x.num.val * y.num.val then .error .divideError
          else .ok (MPQ.setBang out x) := by
        simp only [MPQ.subBang, zx, zy, nx, ny,
          hxd, hyd, decide_true, Bool.true_or, Bool.true_and, hsgn,
          decide_eq_true_eq, ite_true]
        rfl
      by_cases hb : 0 < x.num.val * y.num.val
      · rw [ite_eq_left ⟨hxd, hyd, hb⟩, heval, ite_eq_left hb]
      · rw [ite_eq_right (fun h => hb h.2.2)]
        refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
        · rw [heval, ite_eq_right hb]
        · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
          have he := g19_unit_mul_not_pos _ _ ux uy hb
          omega
    · rw [ite_eq_right (fun h => hyd h.2.1)]
      refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
      · simp only [MPQ.subBang, zx, zy, hxd, hyd,
          decide_true, decide_false, Bool.true_or, Bool.true_and, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), vx.1, vx.2]
        omega
  · by_cases hyd : y.den.val = 0
    · rw [ite_eq_right (fun h => hxd h.1)]
      let s : Int := if y.num.val < 0 then 1 else -1
      have hs : s = 1 ∨ s = -1 := by dsimp only [s]; split <;> omega
      have hq := g19_setSi_unit out s hs
      refine ⟨MPQ.setSiBang out (JInt.wrap .i64 s) (JInt.wrap .u64 0), ?_, hq.1, ?_⟩
      · simp only [MPQ.subBang, zx, zy,
          rcSignbit y.num hy.1, hxd, hyd, decide_true, decide_false,
          decide_eq_true_eq, Bool.false_or, Bool.false_and,
          Bool.false_eq_true, ite_true, ite_false]
        rfl
      · rw [ite_eq_right (by intro h; omega), hq.2.1, hq.2.2]
        dsimp only [s]
        split <;> omega
    · have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
      have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
      have hprod : x.den.val * y.den.val ≠ 0 := Int.ne_of_gt (Int.mul_pos hxp hyp)
      obtain ⟨q, hq, hc, hp, he⟩ := g19_canonicalize out
        (x.num.val * y.den.val - y.num.val * x.den.val) (x.den.val * y.den.val) hprod
      rw [ite_eq_right (fun h => hxd h.1)]
      refine ⟨q, ?_, hc, ?_⟩
      · simp only [MPQ.subBang, zx, zy, hxd, hyd,
          decide_false, Bool.false_or, Bool.false_eq_true, ite_false, MPQ.arithmetic]
        exact hq
      · rw [ite_eq_left ⟨hxp, hyp⟩]
        exact ⟨hp, he⟩

set_option maxRecDepth 4096 in
theorem rationalMultiplicationMutation_proven : RationalMultiplicationMutation := by
  intro out x y hx hy
  let s : Int := if isnegative x.num != isnegative y.num then -1 else 1
  have hs : s = 1 ∨ s = -1 := by dsimp only [s]; split <;> omega
  have hq := g19_setSi_unit out s hs
  have heval : MPQ.mulBang out x y =
      if x.den.val = 0 ∨ y.den.val = 0 then
        if x.num.val = 0 ∨ y.num.val = 0 then .error .divideError
        else .ok (MPQ.setSiBang out (JInt.wrap .i64 s) (JInt.wrap .u64 0))
      else MPQ.canonicalize out (x.num.val * y.num.val) (x.den.val * y.den.val) := by
    simp only [MPQ.mulBang, MPQ.arithmetic,
      rcIszero x.den hx.2.1, rcIszero y.den hy.2.1,
      rcIszero x.num hx.1, rcIszero y.num hy.1,
      Bool.or_eq_true, decide_eq_true_eq]
    rfl
  by_cases hinf : x.den.val = 0 ∨ y.den.val = 0
  · by_cases hz : x.num.val = 0 ∨ y.num.val = 0
    · rw [ite_eq_left ⟨hinf, hz⟩, heval, ite_eq_left hinf, ite_eq_left hz]
    · rw [ite_eq_right (fun h => hz h.2)]
      refine ⟨MPQ.setSiBang out (JInt.wrap .i64 s) (JInt.wrap .u64 0), ?_, hq.1, ?_⟩
      · rw [heval, ite_eq_left hinf, ite_eq_right hz]
      · rw [ite_eq_right (by intro h; rcases hinf with h0 | h0 <;> omega), hq.2.1, hq.2.2]
        refine ⟨rfl, ?_⟩
        dsimp only [s]
        rw [rcIsnegative x.num hx.1, rcIsnegative y.num hy.1]
        exact g19_product_sign _ _ (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
  · have hxd : x.den.val ≠ 0 := fun h => hinf (Or.inl h)
    have hyd : y.den.val ≠ 0 := fun h => hinf (Or.inr h)
    have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
    have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
    have hprod : x.den.val * y.den.val ≠ 0 := Int.ne_of_gt (Int.mul_pos hxp hyp)
    obtain ⟨q, hqc, hc, hp, he⟩ := g19_canonicalize out
      (x.num.val * y.num.val) (x.den.val * y.den.val) hprod
    rw [ite_eq_right (fun h => hinf h.1)]
    refine ⟨q, ?_, hc, ?_⟩
    · rw [heval, ite_eq_right hinf]
      exact hqc
    · rw [ite_eq_left ⟨hxp, hyp⟩]
      exact ⟨hp, he⟩

set_option maxRecDepth 4096 in
theorem rationalDivisionMutation_proven : RationalDivisionMutation := by
  intro out x y hx hy
  let sp : Int := if x.num.val < 0 then -1 else 1
  let sm : Int := if x.num.val < 0 then 1 else -1
  have hsp : sp = 1 ∨ sp = -1 := by dsimp only [sp]; split <;> omega
  have hsm : sm = 1 ∨ sm = -1 := by dsimp only [sm]; split <;> omega
  have hqp := g19_setSi_unit out sp hsp
  have hqm := g19_setSi_unit out sm hsm
  have hqz := g19_setSi_zero out
  have vx := g19_setBang_values out x hx.1 hx.2.1
  have heval : MPQ.divBang out x y =
      if x.den.val = 0 then
        if y.den.val = 0 then .error .divideError
        else if ¬ y.num.val < 0 then .ok (MPQ.setBang out x)
        else .ok (MPQ.setSiBang out (JInt.wrap .i64 sm) (JInt.wrap .u64 0))
      else if y.den.val = 0 then .ok (MPQ.setSiBang out (JInt.wrap .i64 0) (JInt.wrap .u64 1))
      else if y.num.val = 0 then
        if x.num.val = 0 then .error .divideError
        else .ok (MPQ.setSiBang out (JInt.wrap .i64 sp) (JInt.wrap .u64 0))
      else MPQ.canonicalize out (x.num.val * y.den.val) (x.den.val * y.num.val) := by
    simp only [MPQ.divBang, MPQ.arithmetic,
      rcIszero x.den hx.2.1, rcIszero y.den hy.2.1,
      rcIszero x.num hx.1, rcIszero y.num hy.1,
      rcIsnegative y.num hy.1, rcSignbit x.num hx.1,
      not_decide_eq_true, decide_eq_true_eq]
    rfl
  by_cases hxd : x.den.val = 0
  · have ux := rcUnitNum x.num.val x.den.val hxd hx.2.2.2
    have hxn : x.num.val ≠ 0 := by omega
    by_cases hyd : y.den.val = 0
    · rw [ite_eq_left (Or.inl ⟨hxd, hyd⟩), heval, ite_eq_left hxd, ite_eq_left hyd]
    · have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
          (x.num.val = 0 ∧ y.num.val = 0)) := by
        intro h
        rcases h with h | h
        · exact hyd h.2
        · exact hxn h.1
      rw [ite_eq_right hbad]
      by_cases hny : y.num.val < 0
      · refine ⟨MPQ.setSiBang out (JInt.wrap .i64 sm) (JInt.wrap .u64 0), ?_, hqm.1, ?_⟩
        · rw [heval, ite_eq_left hxd, ite_eq_right hyd, ite_eq_right (fun h => h hny)]
        · rw [ite_eq_right (by intro h; omega), ite_eq_right hyd, hqm.2.1, hqm.2.2]
          dsimp only [sm]
          split <;> omega
      · refine ⟨MPQ.setBang out x, ?_, g19_setBang_canonical out x hx, ?_⟩
        · rw [heval, ite_eq_left hxd, ite_eq_right hyd, ite_eq_left hny]
        · rw [ite_eq_right (by intro h; omega), ite_eq_right hyd, vx.1, vx.2]
          omega
  · by_cases hyd : y.den.val = 0
    · have uy := rcUnitNum y.num.val y.den.val hyd hy.2.2.2
      have hyn : y.num.val ≠ 0 := by omega
      have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
          (x.num.val = 0 ∧ y.num.val = 0)) := by
        intro h
        rcases h with h | h
        · exact hxd h.1
        · exact hyn h.2
      rw [ite_eq_right hbad]
      refine ⟨MPQ.setSiBang out (JInt.wrap .i64 0) (JInt.wrap .u64 1), ?_, hqz.1, ?_⟩
      · rw [heval, ite_eq_right hxd, ite_eq_left hyd]
      · rw [ite_eq_right (by intro h; omega), ite_eq_left hyd]
        exact hqz.2
    · by_cases hyn : y.num.val = 0
      · by_cases hxn : x.num.val = 0
        · rw [ite_eq_left (Or.inr ⟨hxn, hyn⟩), heval, ite_eq_right hxd,
            ite_eq_right hyd, ite_eq_left hyn, ite_eq_left hxn]
        · have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
              (x.num.val = 0 ∧ y.num.val = 0)) := by
            intro h
            rcases h with h | h
            · exact hxd h.1
            · exact hxn h.1
          rw [ite_eq_right hbad]
          refine ⟨MPQ.setSiBang out (JInt.wrap .i64 sp) (JInt.wrap .u64 0), ?_, hqp.1, ?_⟩
          · rw [heval, ite_eq_right hxd, ite_eq_right hyd, ite_eq_left hyn, ite_eq_right hxn]
          · rw [ite_eq_right (by intro h; exact h.2.2 hyn), ite_eq_right hyd, hqp.2.1, hqp.2.2]
            dsimp only [sp]
            split <;> omega
      · have hxp : 0 < x.den.val := by have := hx.2.2.1; omega
        have hyp : 0 < y.den.val := by have := hy.2.2.1; omega
        obtain ⟨q, hq, hc, hp, he⟩ := g19_canonicalize out
          (x.num.val * y.den.val) (x.den.val * y.num.val) (Int.mul_ne_zero hxd hyn)
        have hbad : ¬ ((x.den.val = 0 ∧ y.den.val = 0) ∨
            (x.num.val = 0 ∧ y.num.val = 0)) := by
          intro h
          rcases h with h | h
          · exact hxd h.1
          · exact hyn h.2
        rw [ite_eq_right hbad]
        refine ⟨q, ?_, hc, ?_⟩
        · rw [heval, ite_eq_right hxd, ite_eq_right hyd, ite_eq_right hyn]
          exact hq
        · rw [ite_eq_left ⟨hxp, hyp, hyn⟩]
          exact ⟨hp, he⟩

theorem rationalArithmeticInplace_proven : RationalArithmeticInplace := by
  exact ⟨fun x y hx hy => rationalAdditionMutation_proven x x y hx hy,
    fun x y hx hy => rationalSubtractionMutation_proven x x y hx hy,
    fun x y hx hy => rationalMultiplicationMutation_proven x x y hx hy,
    fun x y hx hy => rationalDivisionMutation_proven x x y hx hy⟩

end ConversionRationalPromises

namespace MethodPromises
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float Round1
open JuliaLean.ChatGPT.Batch4.Group6 JuliaLean.ChatGPT.Batch4.Group7

theorem init2Zero_proven : Init2Zero := by
  intro x n hn
  refine ⟨rfl, ?_⟩
  unfold MPZ.init2 ofInt
  dsimp only [Int.natAbs_zero]
  rw [cgLimbsZero]
  change n.val ≤ 64 * wrapInt .i32 (max 0 (((n.val.toNat + 63) / 64 : Nat) : Int))
  have hn0 : 0 ≤ n.val := n.property.1
  have hnat : (((n.val.toNat + 63) / 64 : Nat) : Int) = (n.val + 63) / 64 := by omega
  rw [hnat, Int.max_eq_right (by omega), wrapInt_of_inRange]
  · omega
  · change -(2 : Int)^31 ≤ (n.val + 63) / 64 ∧ (n.val + 63) / 64 ≤ (2 : Int)^31 - 1
    change (n.val + 63) / 64 ≤ (2 : Int)^31 - 1 at hn
    omega

private theorem binaryBang_returns (op : MPZ.BinaryOp) (x a b : BigInt) (n : Int)
    (h : MPZ.binaryValue op a.val b.val = .ok n) (P : Int → Prop) (hn : P n) :
    ArithReturns (MPZ.binaryBang op x a b) P := by
  unfold ArithReturns MPZ.binaryBang
  rw [h]
  exact ⟨writeValue x n, rfl, by rw [g6inv_write_val]; exact hn⟩

private theorem binaryBang_error (op : MPZ.BinaryOp) (x a b : BigInt) (e : JlError)
    (h : MPZ.binaryValue op a.val b.val = .error e) :
    MPZ.binaryBang op x a b = .error e := by
  unfold MPZ.binaryBang
  rw [h]
  rfl

theorem binaryMutation_proven : BinaryMutation := by
  intro op x a b
  cases op with
  | add =>
    exact binaryBang_returns .add x a b (a.val + b.val) rfl _ (arith_addition_contract a.val b.val)
  | sub =>
    exact binaryBang_returns .sub x a b (a.val - b.val) rfl _ (arith_subtraction_contract a.val b.val)
  | mul =>
    exact binaryBang_returns .mul x a b (a.val * b.val) rfl _ (arith_multiplication_contract a.val b.val)
  | gcd =>
    exact binaryBang_returns .gcd x a b (Int.gcd a.val b.val) rfl _ (arith_gcd_contract a.val b.val)
  | lcm =>
    apply binaryBang_returns .lcm x a b (Int.lcm a.val b.val)
    · simp only [MPZ.binaryValue, Pure.pure, Except.pure, Int.lcm_eq_mul_div, Int.gcd_eq_natAbs_gcd_natAbs]
      rfl
    · exact arith_lcm_contract a.val b.val
  | tdivQ =>
    change ArithQuotientResult (MPZ.binaryBang .tdivQ x a b) .toZero a.val b.val
    unfold ArithQuotientResult
    by_cases h : b.val = 0
    · rw [ite_eq_left h]
      exact binaryBang_error .tdivQ x a b .divideError (by simp only [MPZ.binaryValue, h, ↓reduceIte])
    · rw [ite_eq_right h]
      apply binaryBang_returns .tdivQ x a b (a.val.tdiv b.val)
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_false]
      · exact ⟨a.val.tmod b.val, arith_tmod_pair a.val b.val h⟩
  | fdivQ =>
    change ArithQuotientResult (MPZ.binaryBang .fdivQ x a b) .down a.val b.val
    unfold ArithQuotientResult
    by_cases h : b.val = 0
    · rw [ite_eq_left h]
      exact binaryBang_error .fdivQ x a b .divideError (by simp only [MPZ.binaryValue, h, ↓reduceIte])
    · rw [ite_eq_right h]
      apply binaryBang_returns .fdivQ x a b (a.val.fdiv b.val)
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_false]
      · exact ⟨a.val.fmod b.val, arith_fmod_pair a.val b.val h⟩
  | cdivQ =>
    change ArithQuotientResult (MPZ.binaryBang .cdivQ x a b) .up a.val b.val
    unfold ArithQuotientResult
    by_cases h : b.val = 0
    · rw [ite_eq_left h]
      exact binaryBang_error .cdivQ x a b .divideError (by simp only [MPZ.binaryValue, h, ↓reduceIte])
    · rw [ite_eq_right h]
      apply binaryBang_returns .cdivQ x a b (-((-a.val).fdiv b.val))
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self]
      · exact ⟨-((-a.val).fmod b.val), arith_ceiling_pair a.val b.val h⟩
  | tdivR =>
    change ArithRemainderResult (MPZ.binaryBang .tdivR x a b) .toZero a.val b.val
    unfold ArithRemainderResult
    by_cases h : b.val = 0
    · rw [ite_eq_left h]
      exact binaryBang_error .tdivR x a b .divideError (by simp only [MPZ.binaryValue, h, ↓reduceIte])
    · rw [ite_eq_right h]
      apply binaryBang_returns .tdivR x a b (a.val - a.val.tdiv b.val * b.val)
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_true, or_false]
      · refine ⟨a.val.tdiv b.val, ?_⟩
        have heq : a.val - a.val.tdiv b.val * b.val = a.val.tmod b.val := by
          have := Int.tdiv_mul_add_tmod a.val b.val; omega
        rw [heq]
        exact arith_tmod_pair a.val b.val h
  | fdivR =>
    change ArithRemainderResult (MPZ.binaryBang .fdivR x a b) .down a.val b.val
    unfold ArithRemainderResult
    by_cases h : b.val = 0
    · rw [ite_eq_left h]
      exact binaryBang_error .fdivR x a b .divideError (by simp only [MPZ.binaryValue, h, ↓reduceIte])
    · rw [ite_eq_right h]
      apply binaryBang_returns .fdivR x a b (a.val - a.val.fdiv b.val * b.val)
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_true, or_false]
      · refine ⟨a.val.fdiv b.val, ?_⟩
        have heq : a.val - a.val.fdiv b.val * b.val = a.val.fmod b.val := by
          have := Int.fdiv_mul_add_fmod a.val b.val; omega
        rw [heq]
        exact arith_fmod_pair a.val b.val h
  | cdivR =>
    change ArithRemainderResult (MPZ.binaryBang .cdivR x a b) .up a.val b.val
    unfold ArithRemainderResult
    by_cases h : b.val = 0
    · rw [ite_eq_left h]
      exact binaryBang_error .cdivR x a b .divideError (by simp only [MPZ.binaryValue, h, ↓reduceIte])
    · rw [ite_eq_right h]
      apply binaryBang_returns .cdivR x a b (a.val - (-((-a.val).fdiv b.val)) * b.val)
      · simp only [MPZ.binaryValue, Pure.pure, Except.pure, h, ↓reduceIte, reduceCtorEq, or_self, or_true]
      · refine ⟨-((-a.val).fdiv b.val), ?_⟩
        have heq : a.val - (-((-a.val).fdiv b.val)) * b.val = -((-a.val).fmod b.val) := by
          have := Int.fdiv_mul_add_fmod (-a.val) b.val
          rw [Int.neg_mul]
          omega
        rw [heq]
        exact arith_ceiling_pair a.val b.val h
  | and =>
    change ArithReturns (MPZ.binaryBang .and x a b) (fun z => ∀ i, ArithBit z i ↔ ArithBit a.val i ∧ ArithBit b.val i)
    apply binaryBang_returns .and x a b (bitwiseInt Nat.land a.val b.val) rfl
    intro i
    change ArithBitBool (bitwiseInt Nat.land a.val b.val) i = true ↔
      ArithBitBool a.val i = true ∧ ArithBitBool b.val i = true
    rw [bwAndBits, Bool.and_eq_true]
  | ior =>
    change ArithReturns (MPZ.binaryBang .ior x a b) (fun z => ∀ i, ArithBit z i ↔ ArithBit a.val i ∨ ArithBit b.val i)
    apply binaryBang_returns .ior x a b (bitwiseInt Nat.lor a.val b.val) rfl
    intro i
    change ArithBitBool (bitwiseInt Nat.lor a.val b.val) i = true ↔
      ArithBitBool a.val i = true ∨ ArithBitBool b.val i = true
    rw [bwOrBits, Bool.or_eq_true]
  | xor =>
    change ArithReturns (MPZ.binaryBang .xor x a b) (fun z => ∀ i, ArithBit z i ↔ (ArithBit a.val i ↔ ¬ ArithBit b.val i))
    apply binaryBang_returns .xor x a b (bitwiseInt Nat.xor a.val b.val) rfl
    intro i
    change ArithBitBool (bitwiseInt Nat.xor a.val b.val) i = true ↔
      (ArithBitBool a.val i = true ↔ ¬ ArithBitBool b.val i = true)
    rw [bwXorBits]
    cases ArithBitBool a.val i <;> cases ArithBitBool b.val i <;> decide

theorem binaryAllocation_proven : BinaryAllocation := by
  intro op a b
  exact binaryMutation_proven op _ a b

theorem binaryInplace_proven : BinaryInplace := by
  intro op x b
  exact binaryMutation_proven op x x b

private def UnsignedValueContract (op : MPZ.UnsignedOp) (a : Int) (b : Culong) (v : Int) : Prop :=
  match op with
  | .add => v - a = b.val
  | .sub => v + b.val = a
  | .mul => v = ArithRepeatedProduct a b.val
  | .mul2exp => v = a * (2 : Int)^b.val.toNat
  | .fdivQ2exp => ∃ r, a = v * (2 : Int)^b.val.toNat + r ∧ 0 ≤ r ∧ r < (2 : Int)^b.val.toNat
  | .pow => v = ArithPowerValue a b.val.toNat
  | .bin => ArithBinomial a b.val.toNat v

private theorem unsignedResult_eq_valueContract (op : MPZ.UnsignedOp) (a : Int) (b : Culong) (z : BigInt) :
    UnsignedResult op a b z = UnsignedValueContract op a b z.val := by
  cases op <;> rfl

private theorem unsignedBang_val (op : MPZ.UnsignedOp) (x a : BigInt) (b : Culong) :
    (MPZ.unsignedBang op x a b).val = MPZ.unsignedValue op a.val b :=
  g6inv_write_val x (MPZ.unsignedValue op a.val b)

theorem unsignedMutation_proven : UnsignedMutation := by
  intro op x a b
  rw [unsignedResult_eq_valueContract, unsignedBang_val]
  cases op with
  | add =>
    change a.val + b.val - a.val = b.val
    omega
  | sub =>
    change a.val - b.val + b.val = a.val
    omega
  | mul =>
    exact (arith_repeated_product a.val b.val).symm
  | mul2exp =>
    rfl
  | fdivQ2exp =>
    change ∃ r, a.val = a.val.fdiv ((2 : Int)^b.val.toNat) * (2 : Int)^b.val.toNat + r ∧
      0 ≤ r ∧ r < (2 : Int)^b.val.toNat
    rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.pow_nonneg (by decide))]
    have hp : (0 : Int) < 2^b.val.toNat := Int.pow_pos (by decide)
    refine ⟨a.val % (2 : Int)^b.val.toNat, ?_, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hp⟩
    have h := Int.ediv_mul_add_emod a.val ((2 : Int)^b.val.toNat)
    omega
  | pow =>
    exact (pn_power_value a.val b.val.toNat).symm
  | bin =>
    change (if a.val < 0 then (-1 : Int)^b.val.toNat * (chooseNat (a.val.natAbs+b.val.toNat-1) b.val.toNat : Int)
      else (chooseNat a.val.toNat b.val.toNat : Int)) * ArithFactorial b.val.toNat = ArithFallingProduct a.val b.val.toNat
    simp only [pn_chooseNat_eq]
    split
    · rename_i hn
      have h := pn_negative_binomial a.val.natAbs b.val.toNat (by omega)
      have he : -(a.val.natAbs : Int) = a.val := by omega
      simpa only [he] using h
    · rename_i hn
      have h := pn_positive_binomial a.val.toNat b.val.toNat
      have he : (a.val.toNat : Int) = a.val := by omega
      simpa only [he] using h

theorem unsignedAllocation_proven : UnsignedAllocation := by
  intro op a b
  exact unsignedMutation_proven op initBigInt a b

theorem unsignedInplace_proven : UnsignedInplace := by
  intro op x b
  exact unsignedMutation_proven op x x b

theorem unaryMutation_proven : UnaryMutation := by
  intro op x a
  cases op with
  | neg =>
    refine ⟨writeValue x (-a.val), rfl, ?_⟩
    rw [g6inv_write_val]
    omega
  | com =>
    refine ⟨writeValue x (-a.val - 1), rfl, ?_⟩
    rw [g6inv_write_val]
    exact fun i => ab_bit_complement a.val i
  | set =>
    refine ⟨writeValue x a.val, rfl, ?_⟩
    exact g6inv_write_val x a.val
  | sqrt =>
    change if a.val < 0 then MPZ.unaryBang .sqrt x a = .error .divideError
      else ArithReturns (MPZ.unaryBang .sqrt x a) (fun z => 0 ≤ z ∧ z * z ≤ a.val ∧ a.val < (z + 1) * (z + 1))
    by_cases h : a.val < 0
    · rw [ite_eq_left h]
      simp only [MPZ.unaryBang, h, ↓reduceIte]
    · rw [ite_eq_right h]
      refine ⟨writeValue x (Nat.sqrt a.val.toNat), by simp only [MPZ.unaryBang, h, ↓reduceIte, Pure.pure, Except.pure], ?_⟩
      rw [g6inv_write_val]
      have h1 := Nat.sqrt_le a.val.toNat
      have h2 := Nat.lt_succ_sqrt a.val.toNat
      have ha : (a.val.toNat : Int) = a.val := by omega
      refine ⟨Int.natCast_nonneg _, ?_, ?_⟩
      · have h1' : ((Nat.sqrt a.val.toNat * Nat.sqrt a.val.toNat : Nat) : Int) ≤ (a.val.toNat : Int) :=
          Int.ofNat_le.mpr h1
        simpa only [Int.natCast_mul, ha] using h1'
      · have h2' : (a.val.toNat : Int) < (((Nat.sqrt a.val.toNat + 1) * (Nat.sqrt a.val.toNat + 1) : Nat) : Int) :=
          Int.ofNat_lt.mpr h2
        simpa only [Int.natCast_mul, Int.natCast_add, Int.natCast_one, ha] using h2'

theorem unaryAllocation_proven : UnaryAllocation := by
  intro op a
  exact unaryMutation_proven op initBigInt a

theorem unaryInplace_proven : UnaryInplace := by
  intro op x
  exact unaryMutation_proven op x x

private theorem truncVal_bounds (n : Int) (d : Nat) (hd : 0 < d) :
    ((n.tdiv (d : Int) * (d : Int) - n).natAbs < d) ∧
    (n.tdiv (d : Int)).natAbs * d ≤ n.natAbs := by
  constructor
  · have hdiv := Int.tdiv_mul_add_tmod n (d : Int)
    have hsub : n.tdiv (d : Int) * (d : Int) - n = -(n.tmod (d : Int)) := by omega
    rw [hsub, Int.natAbs_neg, Int.natAbs_tmod, Int.natAbs_natCast]
    exact Nat.mod_lt _ hd
  · rw [Int.natAbs_tdiv, Int.natAbs_natCast]
    exact Nat.div_mul_le_self n.natAbs d

theorem scalarAssignmentMutation_proven : ScalarAssignmentMutation := by
  refine ⟨fun x a => g6inv_write_val x a.val, fun x a => g6inv_write_val x a.val, ?_⟩
  intro x a h
  change ((MPZ.setDBang x a h).val * (a.toRat.2 : Int) - a.toRat.1).natAbs < a.toRat.2 ∧
    ((MPZ.setDBang x a h).val.natAbs : Int) * (a.toRat.2 : Int) ≤ (a.toRat.1.natAbs : Int)
  rw [show (MPZ.setDBang x a h).val = a.truncVal from g6inv_write_val x a.truncVal]
  obtain ⟨h1, h2⟩ := truncVal_bounds a.toRat.1 a.toRat.2 (floatConstruct_den_pos a h)
  exact ⟨h1, Int.ofNat_le.mpr h2⟩

theorem scalarAssignmentAllocation_proven : ScalarAssignmentAllocation := by
  refine ⟨fun a => g6inv_write_val initBigInt a.val, fun a => g6inv_write_val initBigInt a.val, ?_⟩
  intro a h
  exact scalarAssignmentMutation_proven.2.2 initBigInt a h

end MethodPromises

namespace ConversionRationalPromises
open JuliaLean JuliaLean.base.gmp JuliaLean.base.float Round1
open JuliaLean.ChatGPT.Batch4.Group6 JuliaLean.ChatGPT.Batch4.Group7

private theorem tdiv_eq_of_cross {n1 : Int} {d1 : Nat} {n2 : Int} {d2 : Nat}
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hcross : n1 * (d2 : Int) = n2 * (d1 : Int)) :
    n1.tdiv (d1 : Int) = n2.tdiv (d2 : Int) := by
  have habs : n1.natAbs * d2 = n2.natAbs * d1 := by
    have h := congrArg Int.natAbs hcross
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h
  have hdiv : n1.natAbs / d1 = n2.natAbs / d2 := by
    rw [← Nat.mul_div_mul_right n1.natAbs d1 hd2, habs,
      Nat.mul_comm d1 d2, Nat.mul_div_mul_right n2.natAbs d2 hd1]
  rw [JuliaLean.ChatGPT.Batch9.Group19.g19_tdiv_nat n1 d1,
      JuliaLean.ChatGPT.Batch9.Group19.g19_tdiv_nat n2 d2, hdiv]
  have hneg_iff : n1 < 0 ↔ n2 < 0 := by
    constructor <;> intro hn
    · by_cases h2 : n2 < 0
      · exact h2
      · have : 0 ≤ n2 * (d1 : Int) := Int.mul_nonneg (by omega) (by omega)
        rw [← hcross] at this
        have : 0 ≤ n1 := Int.nonneg_of_mul_nonneg_left this (by omega)
        omega
    · by_cases h1 : n1 < 0
      · exact h1
      · have : 0 ≤ n1 * (d2 : Int) := Int.mul_nonneg (by omega) (by omega)
        rw [hcross] at this
        have : 0 ≤ n2 := Int.nonneg_of_mul_nonneg_left this (by omega)
        omega
  by_cases hn1 : n1 < 0
  · rw [ite_eq_left hn1, ite_eq_left (hneg_iff.mp hn1)]
  · rw [ite_eq_right hn1, ite_eq_right (fun h2 => hn1 (hneg_iff.mpr h2))]

theorem unsafeTruncateFinite_proven : UnsafeTruncateFinite := by
  intro T x h
  obtain ⟨_, _, hfin_eq, _, hcross⟩ := PNFloat.pnf_widen64_facts x
  have hxfin : x.isfinite = true := hfin_eq.symm.trans h
  have hd1 := floatConstruct_den_pos (convertFloat .f64 x) h
  have hd2 := PNFloat.pnf_finite_den_pos x hxfin
  have ht : (unsafeTruncFloat x h).val = x.toRat.1.tdiv (x.toRat.2 : Int) := by
    rw [show (unsafeTruncFloat x h).val = (convertFloat .f64 x).truncVal from
      g6inv_write_val initBigInt (convertFloat .f64 x).truncVal]
    exact tdiv_eq_of_cross hd1 hd2 (hcross hxfin)
  change ((unsafeTruncFloat x h).val * (x.toRat.2 : Int) - x.toRat.1).natAbs < x.toRat.2 ∧
    (unsafeTruncFloat x h).val.natAbs * x.toRat.2 ≤ x.toRat.1.natAbs
  rw [ht]
  exact MethodPromises.truncVal_bounds x.toRat.1 x.toRat.2 hd2

end ConversionRationalPromises

def entries : List JuliaLean.Registry.Entry := [
  { id := "gmp-binary-operators-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["($fJ)(x::BigInt, y::BigInt)"],
    statement := "All generated binary BigInt operators satisfy their exact arithmetic, quotient/remainder, gcd/lcm and two-complement bit contracts.", source := "base/gmp.jl:501-501",
    status := .proven, prop := ``MethodBinaryOperators, thm := some ``JuliaLean.Proofs.base.gmp.methodBinaryOperators_proven },
  { id := "gmp-division-modes-euclidean", juliaFile := "base/gmp.jl",
    juliaFns := ["div(x::BigInt, y::BigInt, ::typeof($r))"],
    statement := "All three BigInt division modes return the unique integer quotient with the specified remainder direction, and every zero divisor raises DivideError.", source := "base/gmp.jl:508-508",
    status := .proven, prop := ``Round1.DivisionModesEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionModes_proven },
  { id := "gmp-division-truncated", juliaFile := "base/gmp.jl",
    juliaFns := ["div(x::BigInt, y::BigInt)"],
    statement := "Default BigInt div is exact truncating integer division with complete zero-divisor behavior.", source := "base/gmp.jl:512-512",
    status := .proven, prop := ``Round1.DefaultDivisionEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionDefault_proven },
  { id := "gmp-division-floored", juliaFile := "base/gmp.jl",
    juliaFns := ["fld(x::BigInt, y::BigInt)"],
    statement := "BigInt fld returns the mathematical floor of the exact quotient, with complete zero-divisor behavior.", source := "base/gmp.jl:513-513",
    status := .proven, prop := ``Round1.FloorDivisionEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionFloor_proven },
  { id := "gmp-division-ceiling", juliaFile := "base/gmp.jl",
    juliaFns := ["cld(x::BigInt, y::BigInt)"],
    statement := "BigInt cld returns the mathematical ceiling of the exact quotient, with complete zero-divisor behavior.", source := "base/gmp.jl:514-514",
    status := .proven, prop := ``Round1.CeilingDivisionEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionCeiling_proven },
  { id := "gmp-modular-inverse-normalized", juliaFile := "base/gmp.jl",
    juliaFns := ["invmod(x::BigInt, y::BigInt)"],
    statement := "Invmod succeeds exactly for a nonzero modulus coprime to the input and returns its uniquely normalized modular inverse; all other inputs raise DomainError.", source := "base/gmp.jl:518-535",
    status := .proven, prop := ``Round1.ModularInverseExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpInverseModulo_proven },
  { id := "gmp-three-operand-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["($fJ)(a::BigInt, b::BigInt, c::BigInt)"],
    statement := "All 3-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.", source := "base/gmp.jl:541-541",
    status := .proven, prop := ``Round1.Commutative3Exact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpNary3Exact_proven },
  { id := "gmp-four-operand-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt)"],
    statement := "All 4-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.", source := "base/gmp.jl:542-542",
    status := .proven, prop := ``Round1.Commutative4Exact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpNary4Exact_proven },
  { id := "gmp-five-operand-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["($fJ)(a::BigInt, b::BigInt, c::BigInt, d::BigInt, e::BigInt)"],
    statement := "All 5-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.", source := "base/gmp.jl:543-544",
    status := .proven, prop := ``Round1.Commutative5Exact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpNary5Exact_proven },
  { id := "gmp-unsigned-right-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["+(x::BigInt, c::CulongMax)"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:549-549",
    status := .proven, prop := ``Round1.UnsignedRightAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedRightAdd_proven },
  { id := "gmp-unsigned-left-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["+(c::CulongMax, x::BigInt)"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:550-550",
    status := .proven, prop := ``Round1.UnsignedLeftAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedLeftAdd_proven },
  { id := "gmp-unsigned-right-subtraction", juliaFile := "base/gmp.jl",
    juliaFns := ["-(x::BigInt, c::CulongMax)"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:552-552",
    status := .proven, prop := ``Round1.UnsignedRightSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedRightSub_proven },
  { id := "gmp-unsigned-left-subtraction", juliaFile := "base/gmp.jl",
    juliaFns := ["-(c::CulongMax, x::BigInt)"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:553-553",
    status := .proven, prop := ``Round1.UnsignedLeftSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedLeftSub_proven },
  { id := "gmp-signed-right-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["+(x::BigInt, c::ClongMax)"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:555-555",
    status := .proven, prop := ``Round1.SignedRightAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedRightAdd_proven },
  { id := "gmp-signed-left-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["+(c::ClongMax, x::BigInt)"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:556-556",
    status := .proven, prop := ``Round1.SignedLeftAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedLeftAdd_proven },
  { id := "gmp-signed-right-subtraction", juliaFile := "base/gmp.jl",
    juliaFns := ["-(x::BigInt, c::ClongMax)"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:557-557",
    status := .proven, prop := ``Round1.SignedRightSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedRightSub_proven },
  { id := "gmp-signed-left-subtraction", juliaFile := "base/gmp.jl",
    juliaFns := ["-(c::ClongMax, x::BigInt)"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:558-558",
    status := .proven, prop := ``Round1.SignedLeftSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedLeftSub_proven },
  { id := "gmp-unsigned-right-multiplication", juliaFile := "base/gmp.jl",
    juliaFns := ["*(x::BigInt, c::CulongMax)"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:560-560",
    status := .proven, prop := ``Round1.UnsignedRightMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedRightMul_proven },
  { id := "gmp-unsigned-left-multiplication", juliaFile := "base/gmp.jl",
    juliaFns := ["*(c::CulongMax, x::BigInt)"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:561-561",
    status := .proven, prop := ``Round1.UnsignedLeftMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpUnsignedLeftMul_proven },
  { id := "gmp-signed-right-multiplication", juliaFile := "base/gmp.jl",
    juliaFns := ["*(x::BigInt, c::ClongMax)"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:562-562",
    status := .proven, prop := ``Round1.SignedRightMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignedRightMul_proven },
  { id := "gmp-signed-left-multiplication", juliaFile := "base/gmp.jl",
    juliaFns := ["*(c::ClongMax, x::BigInt)"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.", source := "base/gmp.jl:563-563",
    status := .proven, prop := ``Round1.SignedLeftMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignedLeftMul_proven },
  { id := "gmp-negation-additive-inverse", juliaFile := "base/gmp.jl",
    juliaFns := ["(-)(x::BigInt)"],
    statement := "Unary BigInt negation is the exact additive inverse for every signed value.", source := "base/gmp.jl:569-569",
    status := .proven, prop := ``Round1.UnaryNegationInverse, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpNegationInverse_proven },
  { id := "gmp-complement-every-bit", juliaFile := "base/gmp.jl",
    juliaFns := ["(~)(x::BigInt)"],
    statement := "BigInt complement flips every bit of its infinite two's-complement representation.", source := "base/gmp.jl:570-570",
    status := .proven, prop := ``Round1.ComplementEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpComplementBits_proven },
  { id := "gmp-left-shift-every-bit", juliaFile := "base/gmp.jl",
    juliaFns := ["<<(x::BigInt, c::UInt)"],
    statement := "Unsigned-count BigInt left shift moves every input bit by the exact count and fills every lower position with zero.", source := "base/gmp.jl:572-572",
    status := .proven, prop := ``Round1.LeftShiftEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpLeftShiftBits_proven },
  { id := "gmp-right-shift-every-bit", juliaFile := "base/gmp.jl",
    juliaFns := [">>(x::BigInt, c::UInt)"],
    statement := "BigInt right shift retains infinite sign extension and moves each bit by the unsigned count, including the documented BigInt >>> equivalence.", source := "base/gmp.jl:573-573",
    status := .proven, prop := ``Round1.RightShiftEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpRightShiftBits_proven },
  { id := "gmp-logical-right-shift-every-bit", juliaFile := "base/gmp.jl",
    juliaFns := [">>>(x::BigInt, c::UInt)"],
    statement := "BigInt right shift retains infinite sign extension and moves each bit by the unsigned count, including the documented BigInt >>> equivalence.", source := "base/gmp.jl:574-574",
    status := .proven, prop := ``Round1.LogicalRightShiftEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpLogicalRightShiftBits_proven },
  { id := "gmp-zero-bit-cardinality", juliaFile := "base/gmp.jl",
    juliaFns := ["count_zeros(x::BigInt)"],
    statement := "Count zeros returns the cardinality of exactly the zero bits of each negative BigInt and raises DomainError for nonnegative inputs with infinitely many zero bits.", source := "base/gmp.jl:595-599",
    status := .proven, prop := ``Round1.CountZerosCardinality, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCountZerosCardinality_proven },
  { id := "gmp-divrem-reconstruction", juliaFile := "base/gmp.jl",
    juliaFns := ["divrem(x::BigInt, y::BigInt, ::typeof(RoundToZero) = RoundToZero)"],
    statement := "BigInt divrem returns both the exact truncating quotient and remainder satisfying reconstruction, strict magnitude and dividend-sign conditions, with DivideError at zero divisors.", source := "base/gmp.jl:625-625",
    status := .proven, prop := ``Round1.DivremExactPair, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpDivremPair_proven },
  { id := "gmp-square-root-bracket", juliaFile := "base/gmp.jl",
    juliaFns := ["isqrt(x::BigInt)"],
    statement := "BigInt isqrt returns the unique nonnegative integer whose square brackets the input, and negative inputs raise DomainError.", source := "base/gmp.jl:637-637",
    status := .refuted, issue := "Searched JuliaLang/julia issues and PRs; matches #4884, #64288; see bugs/bignums-gmp-isqrt-bracket.yaml", prop := ``Round1.IntegerSquareRootBracket, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpIsqrtBracket_refuted },
  { id := "gmp-unsigned-exponent-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["^(x::BigInt, y::Culong)"],
    statement := "Every Culong BigInt exponent is evaluated as the exact finite product, including the zero exponent and negative bases.", source := "base/gmp.jl:639-639",
    status := .proven, prop := ``Round1.UnsignedPowerExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerUnsigned_proven },
  { id := "gmp-bigint-exponent-full-domain", juliaFile := "base/gmp.jl",
    juliaFns := ["^(x::BigInt , y::BigInt )"],
    statement := "BigInt exponentiation returns the exact integer power or inverse for bases \u00b11, rejects other negative powers, and retains the explicit huge-exponent OverflowError with 0/\u00b11 exceptions.", source := "base/gmp.jl:663-663",
    status := .proven, prop := ``Round1.BigIntPowerFullDomain, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerBigint_proven },
  { id := "gmp-boolean-base-exponent", juliaFile := "base/gmp.jl",
    juliaFns := ["^(x::Bool , y::BigInt )"],
    statement := "Boolean-base BigInt powers agree with exact integer powers and reject zero to a negative power, using the actual source Bool power callee.", source := "base/gmp.jl:667-667",
    status := .proven, prop := ``Round1.BooleanBasePowerExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerBoolBase_proven },
  { id := "gmp-modular-exponent-full-domain", juliaFile := "base/gmp.jl",
    juliaFns := ["powermod(x::BigInt, p::BigInt, m::BigInt)"],
    statement := "Powermod gives the uniquely normalized residue of an exact integer power or inverse power, and reports the documented division/inverse-domain errors.", source := "base/gmp.jl:669-672",
    status := .refuted, issue := "Searched JuliaLang/julia issues and PRs; matches #15350, #15448; see bugs/bignums-gmp-power-modulo.yaml", prop := ``Round1.ModularPowerFullDomain, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerModulo_refuted },
  { id := "gmp-bezout-and-minimal-coefficients", juliaFile := "base/gmp.jl",
    juliaFns := ["gcdx(a::BigInt, b::BigInt)"],
    statement := "Gcdx returns a nonnegative greatest common divisor and exact B\u00e9zout coefficients, with the strict signed-coefficient bounds promised by its documentation whenever the divisor is positive.", source := "base/gmp.jl:676-687",
    status := .refuted, issue := "Searched JuliaLang/julia issues and PRs; matches #64141, #64497; see bugs/bignums-gmp-extended-gcd.yaml", prop := ``Round1.ExtendedGCDExactAndMinimal, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpExtendedGcd_refuted },
  { id := "gmp-variadic-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["+(x::BigInt, y::BigInt, rest::BigInt...)"],
    statement := "Variadic BigInt addition returns the exact sum of every argument, including the empty rest tuple, for every realizable argument count.", source := "base/gmp.jl:689-689",
    status := .proven, prop := ``Round1.VariadicAdditionExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpVariadicAddition_proven },
  { id := "gmp-unsigned-binomial", juliaFile := "base/gmp.jl",
    juliaFns := ["binomial(n::BigInt, k::Culong)"],
    statement := "The Culong-index BigInt binomial equals the generalized falling-factorial coefficient for every signed n, including k>n and negative n.", source := "base/gmp.jl:728-728",
    status := .proven, prop := ``Round1.UnsignedBinomialExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpBinomialUnsigned_proven },
  { id := "gmp-init2-zero", juliaFile := "base/gmp.jl",
    juliaFns := ["init2!(x::BigInt, a)"],
    statement := "Initialization represents zero and reserves at least the requested bits.", source := "base/gmp.jl:164-164",
    status := .proven, prop := ``MethodPromises.Init2Zero, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.init2Zero_proven },
  { id := "gmp-realloc2-preserves-fitting", juliaFile := "base/gmp.jl",
    juliaFns := ["realloc2!(x, a)"],
    statement := "Reallocation retains every value fitting in the requested bit capacity; new allocation represents zero.", source := "base/gmp.jl:166-166",
    status := .proven, prop := ``MethodPromises.Realloc2PreservesFitting, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.realloc2PreservesFitting_proven },
  { id := "gmp-realloc-zero", juliaFile := "base/gmp.jl",
    juliaFns := ["realloc2(a)"],
    statement := "Reallocation retains every value fitting in the requested bit capacity; new allocation represents zero.", source := "base/gmp.jl:167-167",
    status := .proven, prop := ``MethodPromises.ReallocZero, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.reallocZero_proven },
  { id := "gmp-sizeinbase-digit-bound", juliaFile := "base/gmp.jl",
    juliaFns := ["sizeinbase(a::BigInt, b)"],
    statement := "The base digit count is exact or one too large, and zero needs one digit.", source := "base/gmp.jl:169-169",
    status := .todo, prop := ``MethodPromises.SizeinbaseDigitBound, thm := none },
  { id := "gmp-binary-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(x::BigInt, a::BigInt, b::BigInt)"],
    statement := "Every generated binary operation satisfies its exact integer, quotient/remainder, divisibility or bitwise contract.", source := "base/gmp.jl:179-180",
    status := .proven, prop := ``MethodPromises.BinaryMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.binaryMutation_proven },
  { id := "gmp-binary-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op(a::BigInt, b::BigInt)"],
    statement := "Every generated binary operation satisfies its exact integer, quotient/remainder, divisibility or bitwise contract.", source := "base/gmp.jl:181-181",
    status := .proven, prop := ``MethodPromises.BinaryAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.binaryAllocation_proven },
  { id := "gmp-binary-inplace", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(x::BigInt, b::BigInt)"],
    statement := "Every generated binary operation satisfies its exact integer, quotient/remainder, divisibility or bitwise contract.", source := "base/gmp.jl:182-182",
    status := .proven, prop := ``MethodPromises.BinaryInplace, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.binaryInplace_proven },
  { id := "gmp-inverse-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["invert!(x::BigInt, a::BigInt, b::BigInt)"],
    statement := "Inverse reports coprimality and, on success, the least nonnegative modular inverse.", source := "base/gmp.jl:186-187",
    status := .proven, prop := ``MethodPromises.InverseMutation, thm := some ``MethodPromises.inverseMutation_proven },
  { id := "gmp-inverse-inplace", juliaFile := "base/gmp.jl",
    juliaFns := ["invert!(x::BigInt, b::BigInt)"],
    statement := "Inverse reports coprimality and, on success, the least nonnegative modular inverse.", source := "base/gmp.jl:188-188",
    status := .proven, prop := ``MethodPromises.InverseInplace, thm := some ``MethodPromises.inverseInplace_proven },
  { id := "gmp-inverse-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["invert(a::BigInt, b::BigInt)"],
    statement := "Allocated inverse returns the least nonnegative inverse when it exists.", source := "base/gmp.jl:189-189",
    status := .proven, prop := ``MethodPromises.InverseAllocation, thm := some ``MethodPromises.inverseAllocation_proven },
  { id := "gmp-unsigned-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(x::BigInt, a::BigInt, b)"],
    statement := "Generated unsigned-scalar arithmetic, shifts, powers and binomial coefficients satisfy their integer contracts.", source := "base/gmp.jl:195-196",
    status := .proven, prop := ``MethodPromises.UnsignedMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unsignedMutation_proven },
  { id := "gmp-unsigned-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op(a::BigInt, b)"],
    statement := "Generated unsigned-scalar arithmetic, shifts, powers and binomial coefficients satisfy their integer contracts.", source := "base/gmp.jl:197-197",
    status := .proven, prop := ``MethodPromises.UnsignedAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unsignedAllocation_proven },
  { id := "gmp-unsigned-inplace", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(x::BigInt, b)"],
    statement := "Generated unsigned-scalar arithmetic, shifts, powers and binomial coefficients satisfy their integer contracts.", source := "base/gmp.jl:198-198",
    status := .proven, prop := ``MethodPromises.UnsignedInplace, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unsignedInplace_proven },
  { id := "gmp-unsigned-minus-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["ui_sub!(x::BigInt, a, b::BigInt)"],
    statement := "Unsigned-left subtraction reconstructs the minuend without overflow.", source := "base/gmp.jl:202-202",
    status := .proven, prop := ``MethodPromises.UnsignedMinusMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unsignedMinusMutation_proven },
  { id := "gmp-unsigned-minus-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["ui_sub(a, b::BigInt)"],
    statement := "Unsigned-left subtraction reconstructs the minuend without overflow.", source := "base/gmp.jl:203-203",
    status := .proven, prop := ``MethodPromises.UnsignedMinusAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unsignedMinusAllocation_proven },
  { id := "gmp-signed-multiply-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["mul_si!(x::BigInt, a::BigInt, b)"],
    statement := "Signed-scalar multiplication equals exact repeated addition, including typemin.", source := "base/gmp.jl:211-211",
    status := .proven, prop := ``MethodPromises.SignedMultiplyMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.signedMultiplyMutation_proven },
  { id := "gmp-signed-multiply-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["mul_si(a::BigInt, b)"],
    statement := "Signed-scalar multiplication equals exact repeated addition, including typemin.", source := "base/gmp.jl:212-212",
    status := .proven, prop := ``MethodPromises.SignedMultiplyAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.signedMultiplyAllocation_proven },
  { id := "gmp-signed-multiply-inplace", juliaFile := "base/gmp.jl",
    juliaFns := ["mul_si!(x::BigInt, b)"],
    statement := "Signed-scalar multiplication equals exact repeated addition, including typemin.", source := "base/gmp.jl:213-213",
    status := .proven, prop := ``MethodPromises.SignedMultiplyInplace, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.signedMultiplyInplace_proven },
  { id := "gmp-unary-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(x::BigInt, a::BigInt)"],
    statement := "Negation, complement, copy and square root meet their mathematical contracts.", source := "base/gmp.jl:219-220",
    status := .proven, prop := ``MethodPromises.UnaryMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unaryMutation_proven },
  { id := "gmp-unary-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op(a::BigInt)"],
    statement := "Negation, complement, copy and square root meet their mathematical contracts.", source := "base/gmp.jl:221-221",
    status := .proven, prop := ``MethodPromises.UnaryAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unaryAllocation_proven },
  { id := "gmp-unary-inplace", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(x::BigInt)"],
    statement := "Negation, complement, copy and square root meet their mathematical contracts.", source := "base/gmp.jl:224-224",
    status := .proven, prop := ``MethodPromises.UnaryInplace, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.unaryInplace_proven },
  { id := "gmp-factorial-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["fac_ui!(x::BigInt, a)"],
    statement := "GMP factorial is the product of the integers from one through the argument.", source := "base/gmp.jl:227-227",
    status := .proven, prop := ``MethodPromises.FactorialMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.factorialMutation_proven },
  { id := "gmp-factorial-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["fac_ui(a)"],
    statement := "GMP factorial is the product of the integers from one through the argument.", source := "base/gmp.jl:228-228",
    status := .proven, prop := ``MethodPromises.FactorialAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.factorialAllocation_proven },
  { id := "gmp-scalar-assignment-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(x::BigInt, a)"],
    statement := "Scalar setters preserve integers exactly and truncate finite doubles toward zero.", source := "base/gmp.jl:233-233",
    status := .proven, prop := ``MethodPromises.ScalarAssignmentMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.scalarAssignmentMutation_proven },
  { id := "gmp-scalar-assignment-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op(a)"],
    statement := "Scalar setters preserve integers exactly and truncate finite doubles toward zero.", source := "base/gmp.jl:234-234",
    status := .proven, prop := ``MethodPromises.ScalarAssignmentAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.scalarAssignmentAllocation_proven },
  { id := "gmp-limb-popcount-pointer", juliaFile := "base/gmp.jl",
    juliaFns := ["mpn_popcount(d::Ptr{Limb}, s::Integer)"],
    statement := "Limb population count equals the number of set bits across the requested words.", source := "base/gmp.jl:240-240",
    status := .todo, prop := ``MethodPromises.LimbPopcountPointer, thm := none },
  { id := "gmp-limb-popcount-bigint", juliaFile := "base/gmp.jl",
    juliaFns := ["mpn_popcount(a::BigInt)"],
    statement := "BigInt limb population count is the Hamming weight of its absolute value.", source := "base/gmp.jl:241-241",
    status := .todo, prop := ``MethodPromises.LimbPopcountBigint, thm := none },
  { id := "gmp-quotient-remainder-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["tdiv_qr!(x::BigInt, y::BigInt, a::BigInt, b::BigInt)"],
    statement := "Truncated quotient and remainder reconstruct the dividend and obey the remainder sign and magnitude laws.", source := "base/gmp.jl:243-247",
    status := .proven, prop := ``MethodPromises.QuotientRemainderMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.quotientRemainderMutation_proven },
  { id := "gmp-quotient-remainder-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["tdiv_qr(a::BigInt, b::BigInt)"],
    statement := "Truncated quotient and remainder reconstruct the dividend and obey the remainder sign and magnitude laws.", source := "base/gmp.jl:248-248",
    status := .proven, prop := ``MethodPromises.QuotientRemainderAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.quotientRemainderAllocation_proven },
  { id := "gmp-modular-power-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["powm!(x::BigInt, a::BigInt, b::BigInt, c::BigInt)"],
    statement := "Modular exponentiation returns the least nonnegative residue, using an inverse for negative exponents.", source := "base/gmp.jl:250-251",
    status := .proven, prop := ``MethodPromises.ModularPowerMutation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.modularPowerMutation_proven },
  { id := "gmp-modular-power-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["powm(a::BigInt, b::BigInt, c::BigInt)"],
    statement := "Modular exponentiation returns the least nonnegative residue, using an inverse for negative exponents.", source := "base/gmp.jl:252-252",
    status := .proven, prop := ``MethodPromises.ModularPowerAllocation, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.modularPowerAllocation_proven },
  { id := "gmp-modular-power-inplace", juliaFile := "base/gmp.jl",
    juliaFns := ["powm!(x::BigInt, b::BigInt, c::BigInt)"],
    statement := "Modular exponentiation returns the least nonnegative residue, using an inverse for negative exponents.", source := "base/gmp.jl:253-253",
    status := .proven, prop := ``MethodPromises.ModularPowerInplace, thm := some ``JuliaLean.Proofs.base.gmp.MethodPromises.modularPowerInplace_proven },
  { id := "gmp-extended-gcd-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["gcdext!(x::BigInt, y::BigInt, z::BigInt, a::BigInt, b::BigInt)"],
    statement := "Extended gcd returns a nonnegative greatest common divisor and Bezout coefficients.", source := "base/gmp.jl:255-259",
    status := .todo, prop := ``MethodPromises.ExtendedGcdMutation, thm := none },
  { id := "gmp-extended-gcd-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["gcdext(a::BigInt, b::BigInt)"],
    statement := "Extended gcd returns a nonnegative greatest common divisor and Bezout coefficients.", source := "base/gmp.jl:260-260",
    status := .todo, prop := ``MethodPromises.ExtendedGcdAllocation, thm := none },
  { id := "bignums-gmp-signed-machine-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt@333"],
    statement := "The entire source Union{Clong,Int32} converts to the exact mathematical integer with a normalized valid GMP representation, including typemin values",
    source := "base/gmp.jl:333; documentation: base/gmp.jl:64-88; doc/src/manual/integers-and-floating-point-numbers.md:555-568", status := .proven,
    prop := ``Round1.SignedMachineConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedMachineConstruction_proven },
  { id := "bignums-gmp-unsigned-machine-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt@334"],
    statement := "The entire source Union{Culong,UInt32} converts to the exact nonnegative mathematical integer with a normalized valid GMP representation, including values above typemax(Clong)",
    source := "base/gmp.jl:334; documentation: base/gmp.jl:64-88; doc/src/manual/integers-and-floating-point-numbers.md:555-568", status := .proven,
    prop := ``Round1.UnsignedMachineConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedMachineConstruction_proven },
  { id := "bignums-gmp-float64-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt@339"],
    statement := "BigInt(x::Float64) returns the exact finite integral value in a normalized valid GMP representation, including both zero signs, and raises InexactError exactly for fractional or nonfinite inputs",
    source := "base/gmp.jl:339-342; documentation: base/gmp.jl:81-88; base/number.jl:9-14; base/docs/basedocs.jl:2014-2026", status := .proven,
    prop := ``Round1.Float64ConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpFloat64Construction_proven },
  { id := "bignums-gmp-float16-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt@344"],
    statement := "BigInt(x::Float16) returns the exact finite integral value in a normalized valid GMP representation, including both zero signs, and raises InexactError exactly for fractional or nonfinite inputs",
    source := "base/gmp.jl:344; documentation: base/gmp.jl:81-88; base/number.jl:9-14; base/docs/basedocs.jl:2014-2026", status := .proven,
    prop := ``Round1.Float16ConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpFloat16Construction_proven },
  { id := "bignums-gmp-float32-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt@345"],
    statement := "BigInt(x::Float32) returns the exact finite integral value in a normalized valid GMP representation, including both zero signs, and raises InexactError exactly for fractional or nonfinite inputs",
    source := "base/gmp.jl:345; documentation: base/gmp.jl:81-88; base/number.jl:9-14; base/docs/basedocs.jl:2014-2026", status := .proven,
    prop := ``Round1.Float32ConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpFloat32Construction_proven },
  { id := "bignums-gmp-limb-remainder-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["rem@369"],
    statement := "For every target in SLimbMax or ULimbMax and every valid BigInt, x % T is the unique value in the target range congruent to x modulo the number of target values, with no overflow exception",
    source := "base/gmp.jl:369-370; documentation: base/int.jl:667-692; base/gmp.jl:51-58", status := .proven,
    prop := ``Round1.LimbRemainderConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpLimbRemainderConversion_proven },
  { id := "bignums-gmp-bit-remainder-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["rem@372"],
    statement := "The source multi-limb remainder implements the full congruence/range contract for every built-in signed and unsigned integer target, including Int128 and UInt128 and every sign of BigInt input",
    source := "base/gmp.jl:372-378; documentation: base/int.jl:10-36,667-692", status := .proven,
    prop := ``Round1.BitRemainderConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpBitRemainderConversion_proven },
  { id := "bignums-gmp-odd-integer", juliaFile := "base/gmp.jl",
    juliaFns := ["isodd@384"],
    statement := "isodd(x) is true exactly when the mathematical integer represented by x equals 2*k+1 for an integer k, covering positive, negative and zero values",
    source := "base/gmp.jl:384; documentation: base/int.jl:143-159", status := .proven,
    prop := ``Round1.OddIntegerCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpOddInteger_proven },
  { id := "bignums-gmp-even-integer", juliaFile := "base/gmp.jl",
    juliaFns := ["iseven@385"],
    statement := "iseven(x) is true exactly when the mathematical integer represented by x is divisible by two, covering positive, negative and zero values",
    source := "base/gmp.jl:385; documentation: base/int.jl:163-179", status := .proven,
    prop := ``Round1.EvenIntegerCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpEvenInteger_proven },
  { id := "bignums-gmp-exact-unsigned-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["::Type{T}@387"],
    statement := "Conversion of every valid BigInt to each of the five built-in BitUnsigned targets returns the identical integer exactly when it lies in the target range and otherwise raises InexactError, including all negative and oversized values",
    source := "base/gmp.jl:387-394; documentation: base/docs/basedocs.jl:2014-2026; doc/src/manual/conversion-and-promotion.md:112-121; base/int.jl:18-36", status := .proven,
    prop := ``Round1.ExactUnsignedConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpExactUnsignedConversion_proven },
  { id := "bignums-gmp-exact-signed-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["::Type{T}@396"],
    statement := "Conversion of every valid BigInt to each of the five built-in BitSigned targets returns the identical integer exactly when it lies in the target range and otherwise raises InexactError, including typemin and both overflow directions",
    source := "base/gmp.jl:396-407; documentation: base/docs/basedocs.jl:2014-2026; doc/src/manual/conversion-and-promotion.md:112-121; base/int.jl:18-36", status := .proven,
    prop := ``Round1.ExactSignedConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpExactSignedConversion_proven },
  { id := "bignums-gmp-explicit-ieee-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["::Type{T}@411"],
    statement := "Conversion of every valid BigInt to each IEEEFloat format with every public RoundingMode selects the mathematical directed neighbor or globally closest representable value with the specified tie rule, including zero, signs and overflow, with exactly one rounding of the original integer",
    source := "base/gmp.jl:409-466; documentation: base/docs/basedocs.jl:1942-1977; base/rounding.jl:25-110,352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531", status := .proven,
    prop := ``Round1.ExplicitIEEEConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpExplicitIeeeConversion_proven },
  { id := "bignums-gmp-default-float64-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["Float64@468"],
    statement := "Float64(x::BigInt) selects the globally nearest representable Float64 to the exact integer with ties to even and correct signed overflow, without intermediate wider-format rounding",
    source := "base/gmp.jl:468; documentation: base/docs/basedocs.jl:1961-1977; base/rounding.jl:352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531", status := .proven,
    prop := ``Round1.DefaultFloat64ConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDefaultFloat64Conversion_proven },
  { id := "bignums-gmp-default-float32-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["Float32@469"],
    statement := "Float32(x::BigInt) selects the globally nearest representable Float32 to the exact integer with ties to even and correct signed overflow, without intermediate wider-format rounding",
    source := "base/gmp.jl:469; documentation: base/docs/basedocs.jl:1942-1958; base/gmp.jl:409-410; base/rounding.jl:352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531", status := .proven,
    prop := ``Round1.DefaultFloat32ConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDefaultFloat32Conversion_proven },
  { id := "bignums-gmp-default-float16-conversion", juliaFile := "base/gmp.jl",
    juliaFns := ["Float16@470"],
    statement := "Float16(x::BigInt) selects the globally nearest representable Float16 to the exact integer with ties to even and correct signed overflow, without intermediate wider-format rounding",
    source := "base/gmp.jl:470; documentation: base/gmp.jl:409-410; base/rounding.jl:25-110,352-354; doc/src/manual/integers-and-floating-point-numbers.md:523-531", status := .proven,
    prop := ``Round1.DefaultFloat16ConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDefaultFloat16Conversion_proven },
  { id := "bignums-gmp-addition-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt + and +% compute exact signed addition, characterized by cancellation and every integer order cut without machine wraparound.",
    source := "base/gmp.jl:495-503; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.AdditionExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpAdditionExact_proven },
  { id := "bignums-gmp-subtraction-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt - and -% compute the exact signed difference, characterized by reconstruction of the minuend and every integer order cut.",
    source := "base/gmp.jl:495-503; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.SubtractionExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSubtractionExact_proven },
  { id := "bignums-gmp-multiplication-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt * and *% compute exact signed multiplication, characterized independently as repeated addition.",
    source := "base/gmp.jl:495-503; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.MultiplicationExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpMultiplicationExact_proven },
  { id := "bignums-gmp-modulo-euclidean", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt mod returns the unique floored-division remainder with divisor sign and magnitude smaller than the divisor, and rejects zero divisors.",
    source := "base/gmp.jl:495-503; documentation: base/int.jl:293-308; doc/src/base/math.md:19", status := .proven,
    prop := ``Round1.ModuloEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpModuloEuclidean_proven },
  { id := "bignums-gmp-remainder-euclidean", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt rem returns the exact truncating-division remainder with dividend sign and strictly bounded magnitude, and rejects zero divisors.",
    source := "base/gmp.jl:495-503; documentation: base/div.jl:79-111; doc/src/base/math.md:20-21", status := .proven,
    prop := ``Round1.RemainderEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpRemainderEuclidean_proven },
  { id := "bignums-gmp-gcd-universal", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "The BigInt gcd is nonnegative, divides both inputs and is divisible by every common divisor, including the all-zero case.",
    source := "base/gmp.jl:495-503; documentation: base/intfuncs.jl:5-13; doc/src/base/math.md:278", status := .proven,
    prop := ``Round1.GreatestCommonDivisor, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpGcdUniversal_proven },
  { id := "bignums-gmp-lcm-universal", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "The BigInt lcm is the nonnegative common multiple dividing every common multiple, giving zero exactly when an input is zero.",
    source := "base/gmp.jl:495-503; documentation: base/intfuncs.jl:97-105; doc/src/base/math.md:279", status := .proven,
    prop := ``Round1.LeastCommonMultiple, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpLcmUniversal_proven },
  { id := "bignums-gmp-bitand-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt bitwise and obeys its truth table at every bit of the infinite two's-complement representation.",
    source := "base/gmp.jl:495-503; documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101", status := .proven,
    prop := ``Round1.BitAndExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpBitandExact_proven },
  { id := "bignums-gmp-bitor-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt bitwise or obeys its truth table at every bit of the infinite two's-complement representation.",
    source := "base/gmp.jl:495-503; documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101", status := .proven,
    prop := ``Round1.BitOrExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpBitorExact_proven },
  { id := "bignums-gmp-bitxor-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@501"],
    statement := "BigInt bitwise xor obeys its truth table at every bit of the infinite two's-complement representation.",
    source := "base/gmp.jl:495-503; documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101", status := .proven,
    prop := ``Round1.BitXorExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpBitxorExact_proven },
  { id := "bignums-gmp-division-modes", juliaFile := "base/gmp.jl",
    juliaFns := ["div@508"],
    statement := "All three BigInt division modes return the unique integer quotient with the specified remainder direction, and every zero divisor raises DivideError.",
    source := "base/gmp.jl:505-509; documentation: base/div.jl:5-13; base/rounding.jl:25-76", status := .proven,
    prop := ``Round1.DivisionModesEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionModes_proven },
  { id := "bignums-gmp-division-default", juliaFile := "base/gmp.jl",
    juliaFns := ["div@512"],
    statement := "Default BigInt div is exact truncating integer division with complete zero-divisor behavior.",
    source := "base/gmp.jl:512; documentation: base/div.jl:5-13,151-157,198-203", status := .proven,
    prop := ``Round1.DefaultDivisionEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionDefault_proven },
  { id := "bignums-gmp-division-floor", juliaFile := "base/gmp.jl",
    juliaFns := ["fld@513"],
    statement := "BigInt fld returns the mathematical floor of the exact quotient, with complete zero-divisor behavior.",
    source := "base/gmp.jl:513; documentation: base/div.jl:5-13,151-157,198-203", status := .proven,
    prop := ``Round1.FloorDivisionEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionFloor_proven },
  { id := "bignums-gmp-division-ceiling", juliaFile := "base/gmp.jl",
    juliaFns := ["cld@514"],
    statement := "BigInt cld returns the mathematical ceiling of the exact quotient, with complete zero-divisor behavior.",
    source := "base/gmp.jl:514; documentation: base/div.jl:5-13,151-157,198-203", status := .proven,
    prop := ``Round1.CeilingDivisionEuclidean, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpDivisionCeiling_proven },
  { id := "bignums-gmp-inverse-modulo", juliaFile := "base/gmp.jl",
    juliaFns := ["invmod@518"],
    statement := "Invmod succeeds exactly for a nonzero modulus coprime to the input and returns its uniquely normalized modular inverse; all other inputs raise DomainError.",
    source := "base/gmp.jl:518-535; documentation: base/intfuncs.jl:289-310; base/gmp.jl:527-533", status := .proven,
    prop := ``Round1.ModularInverseExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpInverseModulo_proven },
  { id := "bignums-gmp-nary-3-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@541"],
    statement := "All 3-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.",
    source := "base/gmp.jl:541-541; documentation: base/operators.jl:666-678; doc/src/manual/mathematical-operations.md:501-503; doc/src/base/numbers.md:138-151", status := .proven,
    prop := ``Round1.Commutative3Exact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpNary3Exact_proven },
  { id := "bignums-gmp-nary-4-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@542"],
    statement := "All 4-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.",
    source := "base/gmp.jl:542-542; documentation: base/operators.jl:666-678; doc/src/manual/mathematical-operations.md:501-503; doc/src/base/numbers.md:138-151", status := .proven,
    prop := ``Round1.Commutative4Exact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpNary4Exact_proven },
  { id := "bignums-gmp-nary-5-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["$fJ@543"],
    statement := "All 5-argument BigInt sums, products and bitwise operations return their exact mathematical aggregate across the complete signed input domain.",
    source := "base/gmp.jl:543-544; documentation: base/operators.jl:666-678; doc/src/manual/mathematical-operations.md:501-503; doc/src/base/numbers.md:138-151", status := .proven,
    prop := ``Round1.Commutative5Exact, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpNary5Exact_proven },
  { id := "bignums-gmp-unsigned-right-add", juliaFile := "base/gmp.jl",
    juliaFns := ["+@549"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:549; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.UnsignedRightAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedRightAdd_proven },
  { id := "bignums-gmp-unsigned-left-add", juliaFile := "base/gmp.jl",
    juliaFns := ["+@550"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:550; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.UnsignedLeftAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedLeftAdd_proven },
  { id := "bignums-gmp-unsigned-right-sub", juliaFile := "base/gmp.jl",
    juliaFns := ["-@552"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:552; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.UnsignedRightSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedRightSub_proven },
  { id := "bignums-gmp-unsigned-left-sub", juliaFile := "base/gmp.jl",
    juliaFns := ["-@553"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:553; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.UnsignedLeftSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedLeftSub_proven },
  { id := "bignums-gmp-signed-right-add", juliaFile := "base/gmp.jl",
    juliaFns := ["+@555"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:555; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.SignedRightAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedRightAdd_proven },
  { id := "bignums-gmp-signed-left-add", juliaFile := "base/gmp.jl",
    juliaFns := ["+@556"],
    statement := "Mixed BigInt addition is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:556; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.SignedLeftAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedLeftAdd_proven },
  { id := "bignums-gmp-signed-right-sub", juliaFile := "base/gmp.jl",
    juliaFns := ["-@557"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:557; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.SignedRightSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedRightSub_proven },
  { id := "bignums-gmp-signed-left-sub", juliaFile := "base/gmp.jl",
    juliaFns := ["-@558"],
    statement := "Mixed BigInt subtraction is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:558; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.SignedLeftSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedLeftSub_proven },
  { id := "bignums-gmp-unsigned-right-mul", juliaFile := "base/gmp.jl",
    juliaFns := ["*@560"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:560; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.UnsignedRightMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedRightMul_proven },
  { id := "bignums-gmp-unsigned-left-mul", juliaFile := "base/gmp.jl",
    juliaFns := ["*@561"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:561; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.UnsignedLeftMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpUnsignedLeftMul_proven },
  { id := "bignums-gmp-signed-right-mul", juliaFile := "base/gmp.jl",
    juliaFns := ["*@562"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:562; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.SignedRightMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignedRightMul_proven },
  { id := "bignums-gmp-signed-left-mul", juliaFile := "base/gmp.jl",
    juliaFns := ["*@563"],
    statement := "Mixed BigInt multiplication is exact in the supplied operand order for every type in the source C-word integer union, including signed minima.",
    source := "base/gmp.jl:563; documentation: doc/src/manual/integers-and-floating-point-numbers.md:554-607; doc/src/base/math.md:5-30", status := .proven,
    prop := ``Round1.SignedLeftMultiplication, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignedLeftMul_proven },
  { id := "bignums-gmp-negation-inverse", juliaFile := "base/gmp.jl",
    juliaFns := ["-@569"],
    statement := "Unary BigInt negation is the exact additive inverse for every signed value.",
    source := "base/gmp.jl:569; documentation: doc/src/base/math.md:6; doc/src/manual/integers-and-floating-point-numbers.md:554-607", status := .proven,
    prop := ``Round1.UnaryNegationInverse, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpNegationInverse_proven },
  { id := "bignums-gmp-complement-bits", juliaFile := "base/gmp.jl",
    juliaFns := ["~@570"],
    statement := "BigInt complement flips every bit of its infinite two's-complement representation.",
    source := "base/gmp.jl:570; documentation: doc/src/base/numbers.md:138-151; doc/src/manual/mathematical-operations.md:86-101", status := .proven,
    prop := ``Round1.ComplementEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpComplementBits_proven },
  { id := "bignums-gmp-left-shift-bits", juliaFile := "base/gmp.jl",
    juliaFns := ["<<@572"],
    statement := "Unsigned-count BigInt left shift moves every input bit by the exact count and fills every lower position with zero.",
    source := "base/gmp.jl:572; documentation: base/operators.jl:715-723; doc/src/base/numbers.md:141-143", status := .proven,
    prop := ``Round1.LeftShiftEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpLeftShiftBits_proven },
  { id := "bignums-gmp-right-shift-bits", juliaFile := "base/gmp.jl",
    juliaFns := [">>@573"],
    statement := "BigInt right shift retains infinite sign extension and moves each bit by the unsigned count, including the documented BigInt >>> equivalence.",
    source := "base/gmp.jl:573; documentation: base/operators.jl:750-758,791-815; doc/src/base/numbers.md:141-143", status := .proven,
    prop := ``Round1.RightShiftEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpRightShiftBits_proven },
  { id := "bignums-gmp-logical-right-shift-bits", juliaFile := "base/gmp.jl",
    juliaFns := [">>>@574"],
    statement := "BigInt right shift retains infinite sign extension and moves each bit by the unsigned count, including the documented BigInt >>> equivalence.",
    source := "base/gmp.jl:574; documentation: base/operators.jl:750-758,791-815; doc/src/base/numbers.md:141-143", status := .proven,
    prop := ``Round1.LogicalRightShiftEveryBit, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpLogicalRightShiftBits_proven },
  { id := "gmp-integer-callee-symbol", juliaFile := "base/gmp.jl",
    juliaFns := ["gmpz(op::Symbol)"],
    statement := "Generated integer C callees have the GMP integer symbol prefix and resolve the libgmp binding in MPZ.", source := "base/gmp.jl:161-161",
    status := .proven, prop := ``RemainingMethodPromises.IntegerCalleeSymbol, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.integerCalleeSymbol_proven },
  { id := "gmp-double-comparison-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp_d(a::BigInt, b)"],
    statement := "Finite-double comparison uses exact rational order without rounding the integer.", source := "base/gmp.jl:265-265",
    status := .proven, prop := ``RemainingMethodPromises.DoubleComparisonExact, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.doubleComparisonExact_proven },
  { id := "gmp-integer-string-roundtrip", juliaFile := "base/gmp.jl",
    juliaFns := ["get_str!(x, a, b::BigInt)"],
    statement := "Every supported positive-radix integer rendering parses successfully to the original integer, including negative values and zero.", source := "base/gmp.jl:270-270",
    status := .todo, prop := ``RemainingMethodPromises.IntegerStringRoundtrip, thm := none },
  { id := "gmp-string-integer-roundtrip", juliaFile := "base/gmp.jl",
    juliaFns := ["set_str!(x::BigInt, a, b)"],
    statement := "Every supported positive-radix integer rendering parses successfully to the original integer, including negative values and zero.", source := "base/gmp.jl:271-271",
    status := .todo, prop := ``RemainingMethodPromises.StringIntegerRoundtrip, thm := none },
  { id := "gmp-writable-limb-capacity", juliaFile := "base/gmp.jl",
    juliaFns := ["limbs_write!(x::BigInt, a)"],
    statement := "Preparing writable limbs preserves the integer and prior words while reserving the requested native capacity.", source := "base/gmp.jl:286-286",
    status := .proven, prop := ``RemainingMethodPromises.WritableLimbCapacity, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.writableLimbCapacity_proven },
  { id := "gmp-finished-limb-normalization", juliaFile := "base/gmp.jl",
    juliaFns := ["limbs_finish!(x::BigInt, a)"],
    statement := "Finishing a written limb prefix normalizes the signed integer representation.", source := "base/gmp.jl:287-287",
    status := .todo, prop := ``RemainingMethodPromises.FinishedLimbNormalization, thm := none },
  { id := "gmp-setbit-preserves-other-bits", juliaFile := "base/gmp.jl",
    juliaFns := ["setbit!(x, a)"],
    statement := "Setting one bit makes that bit one and leaves every other two-complement bit unchanged.", source := "base/gmp.jl:289-289",
    status := .todo, prop := ``RemainingMethodPromises.SetbitPreservesOtherBits, thm := none },
  { id := "gmp-generic-integer-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::Integer)"],
    statement := "The generic constructor represents every built-in integer type exactly, including both 128-bit types.", source := "base/gmp.jl:347-364",
    status := .todo, prop := ``RemainingMethodPromises.GenericIntegerConstruction, thm := none },
  { id := "gmp-oversized-exponent-error", juliaFile := "base/gmp.jl",
    juliaFns := ["throw1(y)"],
    statement := "The local oversized-exponent thrower always raises OverflowError.", source := "base/gmp.jl:645-646",
    status := .proven, prop := ``RemainingMethodPromises.OversizedExponentError, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.oversizedExponentError_proven },
  { id := "gmp-boolean-exponent-identity", juliaFile := "base/gmp.jl",
    juliaFns := ["^(x::BigInt , y::Bool )"],
    statement := "A true exponent retains the input integer; a false exponent returns one.", source := "base/gmp.jl:664-664",
    status := .proven, prop := ``RemainingMethodPromises.BooleanExponentIdentity, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.booleanExponentIdentity_proven },
  { id := "gmp-integer-exponent-alias", juliaFile := "base/gmp.jl",
    juliaFns := ["^(x::BigInt , y::Integer)"],
    statement := "The integer exponent alias preserves the complete exact-power domain and errors when instantiated with the installed Base power method.", source := "base/gmp.jl:665-665",
    status := .proven, prop := ``RemainingMethodPromises.IntegerExponentAlias, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.integerExponentAlias_proven },
  { id := "gmp-integer-base-bigint-exponent", juliaFile := "base/gmp.jl",
    juliaFns := ["^(x::Integer, y::BigInt )"],
    statement := "Every built-in integer base is converted exactly before BigInt exponentiation.", source := "base/gmp.jl:666-666",
    status := .todo, prop := ``RemainingMethodPromises.IntegerBaseBigintExponent, thm := none },
  { id := "gmp-integer-modular-exponent", juliaFile := "base/gmp.jl",
    juliaFns := ["powermod(x::Integer, p::Integer, m::BigInt)"],
    statement := "Mixed built-in integer modular exponentiation returns the exact modulus-signed residue after left-to-right conversions.", source := "base/gmp.jl:674-674",
    status := .todo, prop := ``RemainingMethodPromises.IntegerModularExponent, thm := none },
  { id := "gmp-sum-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["sum(arr::Union{AbstractArray{BigInt}, Tuple{BigInt, Vararg{BigInt}}})"],
    statement := "Summation returns the exact mathematical sum, with zero for an empty array.", source := "base/gmp.jl:690-691",
    status := .proven, prop := ``RemainingMethodPromises.SumExact, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.sumExact_proven },
  { id := "gmp-factorial-native-domain", juliaFile := "base/gmp.jl",
    juliaFns := ["factorial(n::BigInt)"],
    statement := "Factorial rejects negative inputs, checks native argument conversion, and returns the exact product on the Culong domain.", source := "base/gmp.jl:717-717",
    status := .proven, prop := ``RemainingMethodPromises.FactorialNativeDomain, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.factorialNativeDomain_proven },
  { id := "gmp-flipsign-preserves-magnitude", juliaFile := "base/gmp.jl",
    juliaFns := ["flipsign( x::BigInt, y::Integer)"],
    statement := "Changing sign according to any Integer signbit preserves the absolute value and a valid representation.", source := "base/gmp.jl:754-754",
    status := .proven, prop := ``RemainingMethodPromises.FlipsignPreservesMagnitude, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.flipsignPreservesMagnitude_proven },
  { id := "gmp-checked-integer-exponent", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_pow(x::BigInt, p::Integer)"],
    statement := "Checked generic exponentiation preserves the complete exact integer-power contract.", source := "base/gmp.jl:856-856",
    status := .proven, prop := ``RemainingMethodPromises.CheckedIntegerExponent, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.checkedIntegerExponent_proven },
  { id := "gmp-checked-integer-base-exponent", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_pow(x::Integer, p::BigInt)"],
    statement := "Checked exponentiation preserves exact built-in integer-base conversion and the complete BigInt-exponent contract.", source := "base/gmp.jl:857-857",
    status := .todo, prop := ``RemainingMethodPromises.CheckedIntegerBaseExponent, thm := none },
  { id := "gmp-hash-shift-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["Base._hash_shl!(x::BigInt, n)"],
    statement := "The allocation-saving hash shift multiplies the integer by the requested power of two.", source := "base/gmp.jl:864-864",
    status := .proven, prop := ``RemainingMethodPromises.HashShiftExact, thm := some ``JuliaLean.Proofs.base.gmp.RemainingMethodPromises.hashShiftExact_proven },
  { id := "gmp-mixed-divrem-reconstruction", juliaFile := "base/gmp.jl",
    juliaFns := ["divrem(x::BigInt, y::Integer, ::typeof(RoundToZero) = RoundToZero)"],
    statement := "Mixed divrem converts the divisor before division and returns the exact truncated quotient and remainder.", source := "base/gmp.jl:626-626",
    status := .todo, prop := ``RemainingMethodPromises.MixedDivremReconstruction, thm := none },
  { id := "gmp-array-product-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["prod(arr::AbstractArray{BigInt})"],
    statement := "Array product returns the exact mathematical product, with one for an empty array and zero if any entry is zero.", source := "base/gmp.jl:693-696",
    status := .todo, prop := ``RemainingMethodPromises.ArrayProductExact, thm := none },
  { id := "gmp-array-product-segment-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["_prod(arr::AbstractArray{BigInt}, lo, hi)"],
    statement := "Both recursive product branches return the exact product of the requested valid array segment, including the empty segment.", source := "base/gmp.jl:697-715",
    status := .todo, prop := ``RemainingMethodPromises.ArrayProductSegmentExact, thm := none },
  { id := "bignums-gmp-trailing-zero-valuation", juliaFile := "base/gmp.jl",
    juliaFns := ["trailing_zeros@576"],
    statement := "Trailing zeros returns the exact binary valuation of every nonzero signed integer and raises DomainError for zero.",
    source := "base/gmp.jl:576-580; documentation: base/int.jl:490-501; doc/src/base/numbers.md:155-159", status := .proven,
    prop := ``Round1.TrailingZeroValuation, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpTrailingZeroValuation_proven },
  { id := "bignums-gmp-trailing-one-valuation", juliaFile := "base/gmp.jl",
    juliaFns := ["trailing_ones@582"],
    statement := "Trailing ones returns the exact binary valuation of x+1 and raises DomainError for the infinite all-ones value -1.",
    source := "base/gmp.jl:582-586; documentation: base/int.jl:532-543; doc/src/base/numbers.md:155-159", status := .proven,
    prop := ``Round1.TrailingOneValuation, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpTrailingOneValuation_proven },
  { id := "bignums-gmp-count-ones-cardinality", juliaFile := "base/gmp.jl",
    juliaFns := ["count_ones@588"],
    statement := "Count ones returns the cardinality of exactly the set bits of each nonnegative BigInt and raises DomainError for negative inputs with infinitely many set bits.",
    source := "base/gmp.jl:588-592; documentation: base/int.jl:461-475; doc/src/base/numbers.md:153-159", status := .proven,
    prop := ``Round1.CountOnesCardinality, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCountOnesCardinality_proven },
  { id := "bignums-gmp-count-zeros-cardinality", juliaFile := "base/gmp.jl",
    juliaFns := ["count_zeros@595"],
    statement := "Count zeros returns the cardinality of exactly the zero bits of each negative BigInt and raises DomainError for nonnegative inputs with infinitely many zero bits.",
    source := "base/gmp.jl:595-599; documentation: base/int.jl:503-517; doc/src/base/numbers.md:153-159", status := .proven,
    prop := ``Round1.CountZerosCardinality, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCountZerosCardinality_proven },
  { id := "bignums-gmp-exponent-bracket", juliaFile := "base/gmp.jl",
    juliaFns := ["exponent@614"],
    statement := "BigInt exponent gives the unique binary magnitude bracket for every nonzero integer and raises DomainError for zero.",
    source := "base/gmp.jl:614-617; documentation: base/math.jl:900-908; doc/src/base/numbers.md:87-90", status := .proven,
    prop := ``Round1.ExponentMagnitudeBracket, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpExponentBracket_proven },
  { id := "bignums-gmp-divrem-pair", juliaFile := "base/gmp.jl",
    juliaFns := ["divrem@625"],
    statement := "BigInt divrem returns both the exact truncating quotient and remainder satisfying reconstruction, strict magnitude and dividend-sign conditions, with DivideError at zero divisors.",
    source := "base/gmp.jl:625; documentation: base/div.jl:256-273,79-111", status := .proven,
    prop := ``Round1.DivremExactPair, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpDivremPair_proven },
  { id := "bignums-gmp-comparison-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp@628"],
    statement := "BigInt cmp returns exactly -1, 0 or 1 according to mathematical integer order.",
    source := "base/gmp.jl:628; documentation: base/operators.jl:508-511", status := .proven,
    prop := ``Round1.IntegerComparisonExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpComparisonExact_proven },
  { id := "bignums-gmp-comparison-signed", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp@629"],
    statement := "Mixed BigInt and C-word comparison is exact for every member type and every representable machine value.",
    source := "base/gmp.jl:629; documentation: base/operators.jl:508-511; base/gmp.jl:22-29", status := .proven,
    prop := ``Round1.SignedComparisonExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpComparisonSigned_proven },
  { id := "bignums-gmp-comparison-unsigned", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp@630"],
    statement := "Mixed BigInt and C-word comparison is exact for every member type and every representable machine value.",
    source := "base/gmp.jl:630; documentation: base/operators.jl:508-511; base/gmp.jl:22-29", status := .proven,
    prop := ``Round1.UnsignedComparisonExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpComparisonUnsigned_proven },
  { id := "bignums-gmp-comparison-ieee", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp@634"],
    statement := "BigInt/IEEE cmp implements the full documented total order, with NaNs last and negative floating zero below integer zero.",
    source := "base/gmp.jl:634; documentation: base/operators.jl:206-242,508-511", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64167, #64575; see bugs/bignums-gmp-comparison-ieee.yaml",
    prop := ``Round1.IntegerFloatTotalOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpComparisonIeee_refuted },
  { id := "bignums-gmp-comparison-ieee-reverse", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp@635"],
    statement := "BigInt/IEEE cmp implements the full documented total order, with NaNs last and negative floating zero below integer zero.",
    source := "base/gmp.jl:635; documentation: base/operators.jl:206-242,508-511", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64167, #64575; see bugs/bignums-gmp-comparison-ieee-reverse.yaml",
    prop := ``Round1.FloatIntegerTotalOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpComparisonIeeeReverse_refuted },
  { id := "bignums-gmp-isqrt-bracket", juliaFile := "base/gmp.jl",
    juliaFns := ["isqrt@637"],
    statement := "BigInt isqrt returns the unique nonnegative integer whose square brackets the input, and negative inputs raise DomainError.",
    source := "base/gmp.jl:637; documentation: base/intfuncs.jl:1283-1294; base/math.jl:634-646", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #4884, #64288; see bugs/bignums-gmp-isqrt-bracket.yaml",
    prop := ``Round1.IntegerSquareRootBracket, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpIsqrtBracket_refuted },
  { id := "bignums-gmp-power-unsigned", juliaFile := "base/gmp.jl",
    juliaFns := ["^@639"],
    statement := "Every Culong BigInt exponent is evaluated as the exact finite product, including the zero exponent and negative bases.",
    source := "base/gmp.jl:639; documentation: base/promotion.jl:463-499; doc/src/manual/integers-and-floating-point-numbers.md:554-607", status := .proven,
    prop := ``Round1.UnsignedPowerExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerUnsigned_proven },
  { id := "bignums-gmp-power-bigint", juliaFile := "base/gmp.jl",
    juliaFns := ["^@663"],
    statement := "BigInt exponentiation returns the exact integer power or inverse for bases ±1, rejects other negative powers, and retains the explicit huge-exponent OverflowError with 0/±1 exceptions.",
    source := "base/gmp.jl:663; documentation: base/promotion.jl:463-499; base/gmp.jl:641-661", status := .proven,
    prop := ``Round1.BigIntPowerFullDomain, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerBigint_proven },
  { id := "bignums-gmp-power-bool-base", juliaFile := "base/gmp.jl",
    juliaFns := ["^@667"],
    statement := "Boolean-base BigInt powers agree with exact integer powers and reject zero to a negative power, using the actual source Bool power callee.",
    source := "base/gmp.jl:667; documentation: base/promotion.jl:463-499; base/intfuncs.jl:445-448", status := .proven,
    prop := ``Round1.BooleanBasePowerExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerBoolBase_proven },
  { id := "bignums-gmp-power-modulo", juliaFile := "base/gmp.jl",
    juliaFns := ["powermod@669"],
    statement := "Powermod gives the uniquely normalized residue of an exact integer power or inverse power, and reports the documented division/inverse-domain errors.",
    source := "base/gmp.jl:669-672; documentation: base/intfuncs.jl:501-545,289-310; base/int.jl:293-308", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #15350, #15448; see bugs/bignums-gmp-power-modulo.yaml",
    prop := ``Round1.ModularPowerFullDomain, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpPowerModulo_refuted },
  { id := "bignums-gmp-extended-gcd", juliaFile := "base/gmp.jl",
    juliaFns := ["gcdx@676"],
    statement := "Gcdx returns a nonnegative greatest common divisor and exact Bézout coefficients, with the strict signed-coefficient bounds promised by its documentation whenever the divisor is positive.",
    source := "base/gmp.jl:676-687; documentation: base/intfuncs.jl:193-232", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64141, #64497; see bugs/bignums-gmp-extended-gcd.yaml",
    prop := ``Round1.ExtendedGCDExactAndMinimal, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpExtendedGcd_refuted },
  { id := "bignums-gmp-variadic-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["+@689"],
    statement := "Variadic BigInt addition returns the exact sum of every argument, including the empty rest tuple, for every realizable argument count.",
    source := "base/gmp.jl:689; documentation: base/operators.jl:666-678; base/reduce.jl:548-560; doc/src/manual/integers-and-floating-point-numbers.md:554-607", status := .proven,
    prop := ``Round1.VariadicAdditionExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpVariadicAddition_proven },
  { id := "bignums-gmp-factorial-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["factorial@717"],
    statement := "BigInt factorial returns the exact natural-number factorial for every nonnegative input and raises DomainError for every negative input.",
    source := "base/gmp.jl:717; documentation: base/intfuncs.jl:1304-1312; doc/src/manual/integers-and-floating-point-numbers.md:605-607", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #51488, #51497, #1397; see bugs/bignums-gmp-factorial-exact.yaml",
    prop := ``Round1.FactorialExactNaturalDomain, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpFactorialExact_refuted },
  { id := "bignums-gmp-binomial-unsigned", juliaFile := "base/gmp.jl",
    juliaFns := ["binomial@728"],
    statement := "The Culong-index BigInt binomial equals the generalized falling-factorial coefficient for every signed n, including k>n and negative n.",
    source := "base/gmp.jl:728; documentation: base/intfuncs.jl:1338-1354; doc/src/base/math.md:276", status := .proven,
    prop := ``Round1.UnsignedBinomialExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpBinomialUnsigned_proven },
  { id := "bignums-gmp-equality-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["==@730"],
    statement := "BigInt equality is exactly equality of the represented mathematical integers.",
    source := "base/gmp.jl:730; documentation: base/operators.jl:109-126", status := .proven,
    prop := ``Round1.IntegerEqualityExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpEqualityExact_proven },
  { id := "bignums-gmp-equality-ieee", juliaFile := "base/gmp.jl",
    juliaFns := ["==@733"],
    statement := "BigInt/IEEE equality compares exact numeric values, equates both floating zero signs with integer zero, and rejects every NaN and infinity.",
    source := "base/gmp.jl:733; documentation: base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.IntegerFloatEqualityExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpEqualityIeee_proven },
  { id := "bignums-gmp-equality-ieee-reverse", juliaFile := "base/gmp.jl",
    juliaFns := ["==@734"],
    statement := "BigInt/IEEE equality compares exact numeric values, equates both floating zero signs with integer zero, and rejects every NaN and infinity.",
    source := "base/gmp.jl:734; documentation: base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.FloatIntegerEqualityExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpEqualityIeeeReverse_proven },
  { id := "bignums-gmp-zero-classification", juliaFile := "base/gmp.jl",
    juliaFns := ["iszero@735"],
    statement := "Exact iszero iff mathematical value is zero, including unused allocated limbs; GMPInput is a representation/type invariant.",
    source := "base/gmp.jl:735; documentation: base/number.jl:25-44; base/gmp.jl:64-66", status := .proven,
    prop := ``Round1.BigIntZeroClassification, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpZeroClassification_proven },
  { id := "bignums-gmp-one-classification", juliaFile := "base/gmp.jl",
    juliaFns := ["isone@736"],
    statement := "Exact isone iff mathematical integer is one for every valid BigInt.",
    source := "base/gmp.jl:736; documentation: base/number.jl:47-66", status := .proven,
    prop := ``Round1.BigIntOneClassification, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpOneClassification_proven },
  { id := "bignums-gmp-order-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["<=(BigInt,BigInt)@738", "<(BigInt,BigInt)@744"],
    statement := "Both < and <= agree with exact integer order on all valid BigInt pairs.",
    source := "base/gmp.jl:738,744; documentation: doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.BigIntOrderExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpOrderExact_proven },
  { id := "bignums-gmp-ieee-order-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["<=(BigInt,CdoubleMax)@741", "<=(CdoubleMax,BigInt)@742", "<(BigInt,CdoubleMax)@747", "<(CdoubleMax,BigInt)@748"],
    statement := "Both directions of < and <= compare the exact integer with every Float16/32/64 value via independent rational cross products; includes ±Inf, every NaN payload/sign, subnormals, and numerically equal ±0.",
    source := "base/gmp.jl:741-742,747-748; documentation: doc/src/manual/mathematical-operations.md:229-286; base/gmp.jl:29", status := .proven,
    prop := ``Round1.BigIntIEEEOrderExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpIeeeOrderExact_proven },
  { id := "bignums-gmp-sign-classification", juliaFile := "base/gmp.jl",
    juliaFns := ["isnegative@749", "ispositive@750", "signbit@752"],
    statement := "isnegative/ispositive/signbit iff mathematical sign; zero is neither positive nor negative.",
    source := "base/gmp.jl:749-752; documentation: base/number.jl:122-187", status := .proven,
    prop := ``Round1.BigIntSignClassification, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignClassification_proven },
  { id := "bignums-gmp-flipsign-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["flipsign(BigInt,BigInt)@755"],
    statement := "BigInt×BigInt flipsign preserves magnitude and flips exactly when the second value is negative; includes zero and validates the unchanged-magnitude output representation.",
    source := "base/gmp.jl:755; documentation: base/number.jl:242-255", status := .proven,
    prop := ``Round1.BigIntFlipSignExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpFlipsignExact_proven },
  { id := "bignums-gmp-sign-value", juliaFile := "base/gmp.jl",
    juliaFns := ["sign@757"],
    statement := "sign returns exactly −1/0/+1 according to the integer order and a valid bounded-magnitude result.",
    source := "base/gmp.jl:757-761; documentation: base/number.jl:190-204", status := .proven,
    prop := ``Round1.BigIntSignValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignValue_proven },
  { id := "bignums-gmp-checked-absolute", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_abs@841"],
    statement := "checked_abs returns a nonnegative integer with the same square and a valid unchanged-magnitude layout; no fixed-width overflow exception.",
    source := "base/gmp.jl:841; documentation: base/checked.jl:108-119; base/gmp.jl:64-66", status := .proven,
    prop := ``Round1.CheckedBigIntAbsolute, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedAbsolute_proven },
  { id := "bignums-gmp-checked-negation", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_neg@842"],
    statement := "checked_neg returns the exact additive inverse and a valid unchanged-magnitude layout on every GMPInput.",
    source := "base/gmp.jl:842; documentation: base/checked.jl:80-89; base/gmp.jl:64-66", status := .proven,
    prop := ``Round1.CheckedBigIntNegation, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedNegation_proven },
  { id := "bignums-gmp-checked-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_add@843"],
    statement := "checked_add returns the exact integer sum, characterized by the inverse equation and all translated order cuts, without a bound on numerical output.",
    source := "base/gmp.jl:843; documentation: base/checked.jl:158-166; base/gmp.jl:64-66", status := .proven,
    prop := ``Round1.CheckedBigIntAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedAddition_proven },
  { id := "bignums-gmp-checked-subtraction", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_sub@844"],
    statement := "checked_sub returns the exact integer difference, characterized by the inverse equation and all translated order cuts, without a bound on numerical output.",
    source := "base/gmp.jl:844; documentation: base/checked.jl:218-226; base/gmp.jl:64-66", status := .proven,
    prop := ``Round1.CheckedBigIntSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedSubtraction_proven },
  { id := "bignums-gmp-checked-multiplication", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_mul@845"],
    statement := "checked_mul returns the independent signed repeated-addition product for all valid operands, rather than equating a forwarding wrapper to its callee or restating the primitive multiplication body.",
    source := "base/gmp.jl:845; documentation: base/checked.jl:282-290; base/gmp.jl:64-66", status := .proven,
    prop := ``Round1.CheckedBigIntMultiplication,
    thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedMultiplication_proven },
  { id := "bignums-gmp-checked-division", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_div@846", "Base.checked_rem@847", "Base.checked_fld@848", "Base.checked_mod@849", "Base.checked_cld@850"],
    statement := "All checked_div/rem/fld/mod/cld calls throw DivideError at zero divisor; otherwise success, exact division identities and strict remainder magnitude/sign intervals uniquely specify truncating/floor/ceiling results. Every sign combination and exact division is included.",
    source := "base/gmp.jl:846-850; documentation: base/checked.jl:312-355; base/div.jl:5-18,79-110,152-205", status := .proven,
    prop := ``Round1.CheckedBigIntDivision,
    thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedDivision_proven },
  { id := "bignums-gmp-overflow-reporting", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.add_with_overflow@851", "Base.sub_with_overflow@852", "Base.mul_with_overflow@853"],
    statement := "add/sub/mul_with_overflow return false flags AND full exact arithmetic: translated order cuts for addition/subtraction, independent signed repeated-addition product for multiplication.",
    source := "base/gmp.jl:851-853; documentation: base/checked.jl:131-134,195-198,234-237; base/gmp.jl:64-66", status := .proven,
    prop := ``Round1.BigIntOverflowReportingExact,
    thm := some ``JuliaLean.ChatGPT.Batch7.Group1.BignumsGmpOverflowReporting_proven },
  { id := "bignums-gmp-checked-power", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_pow(BigInt,BigInt)@858"],
    statement := "All BigInt exponents: independent repeated-product exactness for nonnegative exponents, inverse-unit relation for negative exponents at bases ±1, DomainError for other negative powers, explicit source OverflowError above Culong maximum for |base|>1, and complete 0/±1 exceptions.",
    source := "base/gmp.jl:858,641-663; documentation: base/checked.jl:358-366; base/intfuncs.jl:385-395; base/gmp.jl:641-661", status := .proven,
    prop := ``Round1.CheckedBigIntPower,
    thm := some ``JuliaLean.ChatGPT.Batch7.Group1.BignumsGmpCheckedPower_proven },
  { id := "bignums-gmp-rational-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["Rational{BigInt}(BigInt,BigInt)@1004"],
    statement := "Rational{BigInt} preserves the exact ratio, reduces gcd to one and makes denominator nonnegative; signed nonzero/zero becomes ±1/0; 0/0 raises ArgumentError. All signed valid integer numerators/denominators, including negative denominators, are quantified.",
    source := "base/gmp.jl:1004-1012; documentation: base/rational.jl:4-7,65-89; doc/src/manual/complex-and-rational-numbers.md:180-211,282-303", status := .proven,
    prop := ``Round1.BigIntRationalConstruction, thm := some ``JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalConstruction_proven },
  { id := "bignums-gmp-rational-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.$fJ (+,-,*,//)@1112"],
    statement := "Exact canonical rational addition by cross-multiplication for finite inputs; finite±infinity and same-sign infinities produce the correct infinity; opposite infinities raise DivideError. Full canonical Rational type domain includes ±1/0.",
    source := "base/gmp.jl:1112; documentation: doc/src/manual/complex-and-rational-numbers.md:180-239,282-303; base/gmp.jl:1047-1058", status := .proven,
    prop := ``Round1.BigIntRationalAddition, thm := some ``JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalAddition_proven },
  { id := "bignums-gmp-rational-subtraction", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.$fJ (+,-,*,//)@1112"],
    statement := "Exact canonical rational subtraction by cross-multiplication for finite inputs; all infinite differences have the correct sign except equal infinities, which raise DivideError.",
    source := "base/gmp.jl:1112; documentation: doc/src/manual/complex-and-rational-numbers.md:180-242,282-303; base/gmp.jl:1060-1072", status := .proven,
    prop := ``Round1.BigIntRationalSubtraction, thm := some ``JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalSubtraction_proven },
  { id := "bignums-gmp-rational-multiplication", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.$fJ (+,-,*,//)@1112"],
    statement := "Exact canonical rational multiplication for finite inputs; every nonzero product involving infinity has the product sign, while zero times infinity in either order raises DivideError.",
    source := "base/gmp.jl:1112; documentation: doc/src/manual/complex-and-rational-numbers.md:180-245,282-303; base/gmp.jl:1074-1086", status := .proven,
    prop := ``Round1.BigIntRationalMultiplication, thm := some ``JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalMultiplication_proven },
  { id := "bignums-gmp-rational-division", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.$fJ (+,-,*,//)@1112"],
    statement := "Exact canonical // for finite nonzero divisors; finite/infinity is0/1, nonzero/zero and infinity/finite have the specified infinity sign (including infinity/zero), and 0/0 or infinity/infinity raises DivideError.",
    source := "base/gmp.jl:1112; documentation: base/rational.jl:65-89; doc/src/manual/complex-and-rational-numbers.md:180-248,282-303; base/gmp.jl:1087-1106", status := .proven,
    prop := ``Round1.BigIntRationalDivision, thm := some ``JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalDivision_proven },
  { id := "gmp-signed-machine-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::Union{Clong,Int32})"],
    statement := "Both members of the source signed-machine union convert exactly to a valid arbitrary-precision integer, including their most negative values.", source := "base/gmp.jl:333-333",
    status := .proven, prop := ``Round1.SignedMachineConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpSignedMachineConstruction_proven },
  { id := "gmp-unsigned-machine-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::Union{Culong,UInt32})"],
    statement := "Both members of the source unsigned-machine union convert exactly to a valid arbitrary-precision integer without a signed-machine overflow.", source := "base/gmp.jl:334-334",
    status := .proven, prop := ``Round1.UnsignedMachineConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpUnsignedMachineConstruction_proven },
  { id := "gmp-float64-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::Float64)"],
    statement := "Float64 construction accepts every finite integral value exactly, including both signed zeros, and rejects fractions, infinities and NaNs with InexactError.", source := "base/gmp.jl:339-342",
    status := .proven, prop := ``Round1.Float64ConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpFloat64Construction_proven },
  { id := "gmp-float16-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::Float16)"],
    statement := "Float16 construction preserves every exact integral input and rejects all fractional or nonfinite inputs, using the original Float16 value as its specification.", source := "base/gmp.jl:344-344",
    status := .proven, prop := ``Round1.Float16ConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpFloat16Construction_proven },
  { id := "gmp-float32-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::Float32)"],
    statement := "Float32 construction preserves every exact integral input and rejects all fractional or nonfinite inputs, using the original Float32 value as its specification.", source := "base/gmp.jl:345-345",
    status := .proven, prop := ``Round1.Float32ConstructionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group6.BignumsGmpFloat32Construction_proven },
  { id := "gmp-flipsign-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["flipsign( x::BigInt, y::BigInt)"],
    statement := "Flipping the sign by a BigInt changes exactly the sign selected by the second integer and preserves a valid value.", source := "base/gmp.jl:755-755",
    status := .proven, prop := ``Round1.BigIntFlipSignExact, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpFlipsignExact_proven },
  { id := "gmp-sign-value", juliaFile := "base/gmp.jl",
    juliaFns := ["sign(x::BigInt)"],
    statement := "The sign of a BigInt is minus one, zero, or one exactly according to its mathematical sign.", source := "base/gmp.jl:757-761",
    status := .proven, prop := ``Round1.BigIntSignValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpSignValue_proven },
  { id := "gmp-checked-absolute-value", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_abs(x::BigInt)"],
    statement := "Checked absolute value returns the nonnegative integer of the same magnitude without fixed-width overflow.", source := "base/gmp.jl:841-841",
    status := .proven, prop := ``Round1.CheckedBigIntAbsolute, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedAbsolute_proven },
  { id := "gmp-checked-negation", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_neg(x::BigInt)"],
    statement := "Checked BigInt negation succeeds with the exact additive inverse, including every extremal input layout.", source := "base/gmp.jl:842-842",
    status := .proven, prop := ``Round1.CheckedBigIntNegation, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedNegation_proven },
  { id := "gmp-checked-addition", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_add(a::BigInt, b::BigInt)"],
    statement := "Checked addition of arbitrary BigInts returns their exact sum.", source := "base/gmp.jl:843-843",
    status := .proven, prop := ``Round1.CheckedBigIntAddition, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedAddition_proven },
  { id := "gmp-checked-subtraction", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_sub(a::BigInt, b::BigInt)"],
    statement := "Checked subtraction of arbitrary BigInts returns their exact difference.", source := "base/gmp.jl:844-844",
    status := .proven, prop := ``Round1.CheckedBigIntSubtraction, thm := some ``JuliaLean.ChatGPT.Batch4.Group7.BignumsGmpCheckedSubtraction_proven },
  { id := "gmp-checked-multiplication", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_mul(a::BigInt, b::BigInt)"],
    statement := "Checked multiplication of arbitrary BigInts returns their exact product.", source := "base/gmp.jl:845-845",
    status := .proven, prop := ``Round1.CheckedBigIntMultiplication, thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedMultiplication_proven },
  { id := "gmp-checked-truncating-division", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_div(a::BigInt, b::BigInt)"],
    statement := "Checked BigInt quotient and remainder methods satisfy exact division identities and their rounding intervals, and reject a zero divisor.", source := "base/gmp.jl:846-846",
    status := .proven, prop := ``Round1.CheckedBigIntDivision, thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedDivision_proven },
  { id := "gmp-checked-truncating-remainder", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_rem(a::BigInt, b::BigInt)"],
    statement := "Checked BigInt quotient and remainder methods satisfy exact division identities and their rounding intervals, and reject a zero divisor.", source := "base/gmp.jl:847-847",
    status := .proven, prop := ``Round1.CheckedBigIntDivision, thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedDivision_proven },
  { id := "gmp-checked-floored-division", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_fld(a::BigInt, b::BigInt)"],
    statement := "Checked BigInt quotient and remainder methods satisfy exact division identities and their rounding intervals, and reject a zero divisor.", source := "base/gmp.jl:848-848",
    status := .proven, prop := ``Round1.CheckedBigIntDivision, thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedDivision_proven },
  { id := "gmp-checked-modulus", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_mod(a::BigInt, b::BigInt)"],
    statement := "Checked BigInt quotient and remainder methods satisfy exact division identities and their rounding intervals, and reject a zero divisor.", source := "base/gmp.jl:849-849",
    status := .proven, prop := ``Round1.CheckedBigIntDivision, thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedDivision_proven },
  { id := "gmp-checked-ceiling-division", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_cld(a::BigInt, b::BigInt)"],
    statement := "Checked BigInt quotient and remainder methods satisfy exact division identities and their rounding intervals, and reject a zero divisor.", source := "base/gmp.jl:850-850",
    status := .proven, prop := ``Round1.CheckedBigIntDivision, thm := some ``JuliaLean.ChatGPT.Batch6.Group2.BignumsGmpCheckedDivision_proven },
  { id := "gmp-addition-overflow-report", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.add_with_overflow(a::BigInt, b::BigInt)"],
    statement := "BigInt overflow-reporting arithmetic returns exact results and a false overflow flag for all three operations.", source := "base/gmp.jl:851-851",
    status := .proven, prop := ``Round1.BigIntOverflowReportingExact, thm := some ``JuliaLean.ChatGPT.Batch7.Group1.BignumsGmpOverflowReporting_proven },
  { id := "gmp-subtraction-overflow-report", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.sub_with_overflow(a::BigInt, b::BigInt)"],
    statement := "BigInt overflow-reporting arithmetic returns exact results and a false overflow flag for all three operations.", source := "base/gmp.jl:852-852",
    status := .proven, prop := ``Round1.BigIntOverflowReportingExact, thm := some ``JuliaLean.ChatGPT.Batch7.Group1.BignumsGmpOverflowReporting_proven },
  { id := "gmp-multiplication-overflow-report", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.mul_with_overflow(a::BigInt, b::BigInt)"],
    statement := "BigInt overflow-reporting arithmetic returns exact results and a false overflow flag for all three operations.", source := "base/gmp.jl:853-853",
    status := .proven, prop := ``Round1.BigIntOverflowReportingExact, thm := some ``JuliaLean.ChatGPT.Batch7.Group1.BignumsGmpOverflowReporting_proven },
  { id := "gmp-checked-bigint-exponent", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.checked_pow(x::BigInt, p::BigInt)"],
    statement := "Checked BigInt powers are exact, accept negative powers of units, and report the documented source exponent-domain and exponent-cap errors.", source := "base/gmp.jl:858-858",
    status := .proven, prop := ``Round1.CheckedBigIntPower, thm := some ``JuliaLean.ChatGPT.Batch7.Group1.BignumsGmpCheckedPower_proven },
  { id := "gmp-rational-normalization", juliaFile := "base/gmp.jl",
    juliaFns := ["Rational{BigInt}(num::BigInt, den::BigInt)"],
    statement := "Rational{BigInt} construction produces the exact reduced ratio with nonnegative denominator, accepts signed infinities, and rejects zero over zero.", source := "base/gmp.jl:1004-1012",
    status := .proven, prop := ``Round1.BigIntRationalConstruction, thm := some ``JuliaLean.ChatGPT.Batch9.Group19.BignumsGmpRationalConstruction_proven },
  { id := "gmp-boolean-construction", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::Bool)"],
    statement := "Boolean construction represents exactly zero or one.", source := "base/gmp.jl:335-335",
    status := .proven, prop := ``ConversionRationalPromises.BooleanConstruction, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.booleanConstruction_proven },
  { id := "gmp-unsafe-truncate-finite", juliaFile := "base/gmp.jl",
    juliaFns := ["unsafe_trunc(::Type{BigInt}, x::Union{Float16,Float32,Float64})"],
    statement := "Unsafe conversion of a finite floating value truncates toward zero.", source := "base/gmp.jl:337-337",
    status := .proven, prop := ``ConversionRationalPromises.UnsafeTruncateFinite, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.unsafeTruncateFinite_proven },
  { id := "gmp-rational-callee-symbol", juliaFile := "base/gmp.jl",
    juliaFns := ["gmpq(op::Symbol)"],
    statement := "Generated rational C callees have the GMP rational symbol prefix and resolve the libgmp binding in MPZ.", source := "base/gmp.jl:964-964",
    status := .proven, prop := ``ConversionRationalPromises.RationalCalleeSymbol, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalCalleeSymbol_proven },
  { id := "gmp-raw-rational-preserves-values", juliaFile := "base/gmp.jl",
    juliaFns := ["_MPQ(x::BigInt,y::BigInt)"],
    statement := "Raw rational construction preserves both integer operands and their signed limb counts.", source := "base/gmp.jl:979-981",
    status := .proven, prop := ``ConversionRationalPromises.RawRationalPreservesValues, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rawRationalPreservesValues_proven },
  { id := "gmp-raw-rational-empty-zero", juliaFile := "base/gmp.jl",
    juliaFns := ["_MPQ()"],
    statement := "Empty raw rational allocation initializes both integers to zero.", source := "base/gmp.jl:982-982",
    status := .proven, prop := ``ConversionRationalPromises.RawRationalEmptyZero, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rawRationalEmptyZero_proven },
  { id := "gmp-raw-rational-preserves-ratio", juliaFile := "base/gmp.jl",
    juliaFns := ["_MPQ(x::Rational{BigInt})"],
    statement := "Wrapping a rational preserves its numerator and denominator without normalization.", source := "base/gmp.jl:983-983",
    status := .proven, prop := ``ConversionRationalPromises.RawRationalPreservesRatio, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rawRationalPreservesRatio_proven },
  { id := "gmp-raw-rational-alias-copy-values", juliaFile := "base/gmp.jl",
    juliaFns := ["_MPQ(zq::_MPQ, x::Rational{BigInt})"],
    statement := "The same-rational fast path retains the output record; copying shared integer storage preserves both values.", source := "base/gmp.jl:986-992",
    status := .proven, prop := ``ConversionRationalPromises.RawRationalAliasCopyValues, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rawRationalAliasCopyValues_proven },
  { id := "gmp-rational-assignment-values", juliaFile := "base/gmp.jl",
    juliaFns := ["set!(z::Rational{BigInt}, x::Rational{BigInt})"],
    statement := "Rational assignment preserves the exact numerator and denominator, including infinities.", source := "base/gmp.jl:1015-1019",
    status := .proven, prop := ``ConversionRationalPromises.RationalAssignmentValues, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalAssignmentValues_proven },
  { id := "gmp-rational-integer-assignment", juliaFile := "base/gmp.jl",
    juliaFns := ["set_z!(z::Rational{BigInt}, x::BigInt)"],
    statement := "Integer assignment creates that integer over denominator one.", source := "base/gmp.jl:1021-1025",
    status := .proven, prop := ``ConversionRationalPromises.RationalIntegerAssignment, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalIntegerAssignment_proven },
  { id := "gmp-rational-copy-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op(a::$T)"],
    statement := "Allocated rational and integer copies preserve values and assign denominator one for integers.", source := "base/gmp.jl:1029-1029",
    status := .proven, prop := ``ConversionRationalPromises.RationalCopyAllocation, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalCopyAllocation_proven },
  { id := "gmp-rational-scalar-assignment", juliaFile := "base/gmp.jl",
    juliaFns := ["$op!(z::Rational{BigInt}, a, b)"],
    statement := "Scalar rational setters retain the supplied numerator and denominator exactly, allowing zero over zero.", source := "base/gmp.jl:1037-1041",
    status := .proven, prop := ``ConversionRationalPromises.RationalScalarAssignment, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalScalarAssignment_proven },
  { id := "gmp-rational-scalar-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["$op(a, b)"],
    statement := "Allocated scalar rational setters preserve the unchecked numerator and denominator.", source := "base/gmp.jl:1042-1042",
    status := .proven, prop := ``ConversionRationalPromises.RationalScalarAllocation, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalScalarAllocation_proven },
  { id := "gmp-rational-addition-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["add!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})"],
    statement := "Rational addition obeys exact cross-multiplication and the documented infinity and divide-error cases.", source := "base/gmp.jl:1047-1058",
    status := .proven, prop := ``ConversionRationalPromises.RationalAdditionMutation, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalAdditionMutation_proven },
  { id := "gmp-rational-subtraction-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["sub!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})"],
    statement := "Rational subtraction obeys exact cross-multiplication and the documented infinity and divide-error cases.", source := "base/gmp.jl:1060-1072",
    status := .proven, prop := ``ConversionRationalPromises.RationalSubtractionMutation, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalSubtractionMutation_proven },
  { id := "gmp-rational-multiplication-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["mul!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})"],
    statement := "Rational multiplication obeys exact cross-multiplication and the documented infinity and divide-error cases.", source := "base/gmp.jl:1074-1085",
    status := .proven, prop := ``ConversionRationalPromises.RationalMultiplicationMutation, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalMultiplicationMutation_proven },
  { id := "gmp-rational-division-mutation", juliaFile := "base/gmp.jl",
    juliaFns := ["div!(z::Rational{BigInt}, x::Rational{BigInt}, y::Rational{BigInt})"],
    statement := "Rational division obeys exact cross-multiplication and the documented infinity and divide-error cases.", source := "base/gmp.jl:1087-1106",
    status := .proven, prop := ``ConversionRationalPromises.RationalDivisionMutation, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalDivisionMutation_proven },
  { id := "gmp-rational-arithmetic-inplace", juliaFile := "base/gmp.jl",
    juliaFns := ["($fC!)(x::Rational{BigInt}, y::Rational{BigInt})"],
    statement := "All in-place rational operators preserve exact finite arithmetic and the documented extended-value behavior.", source := "base/gmp.jl:1111-1111",
    status := .proven, prop := ``ConversionRationalPromises.RationalArithmeticInplace, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalArithmeticInplace_proven },
  { id := "gmp-rational-arithmetic-allocation", juliaFile := "base/gmp.jl",
    juliaFns := ["(Base.$fJ)(x::Rational{BigInt}, y::Rational{BigInt})"],
    statement := "All allocated rational operators preserve exact finite arithmetic and the documented extended-value behavior.", source := "base/gmp.jl:1112-1112",
    status := .proven, prop := ``ConversionRationalPromises.RationalArithmeticAllocation, thm := some ``JuliaLean.Proofs.base.gmp.ConversionRationalPromises.rationalArithmeticAllocation_proven },
  { id := "bignums-gmp-rational-comparison", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.cmp(Rational{BigInt},Rational{BigInt})@1116"],
    statement := "cmp returns exactly −1/0/+1 iff the independently defined extended-rational order/equality holds, for every finite/infinite pair and both infinity signs. Canonical input invariant excludes only unsafe invalid rationals such as0/0.",
    source := "base/gmp.jl:1116-1123; documentation: base/operators.jl:508-511; doc/src/manual/complex-and-rational-numbers.md:180-230,282-303", status := .proven,
    prop := ``Round1.BigIntRationalComparison,
    thm := some ``JuliaLean.ChatGPT.Batch7.Group1.BignumsGmpRationalComparison_proven }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- A realizable Julia String has a byte length representable by native Int.
This is a representation invariant, not a bound on a version component's
numeric magnitude. LibraryGlobals contains already-decoded, valid external GMP
global data; the String field retains its native byte-size requirement. -/
def ConstructibleText (text : String) : Prop :=
  text.utf8ByteSize < (2 : Nat)^63

/-- Reading the decoded GMP version global preserves its byte length and
every character. This is a stored-global observation contract, independent of
the implementation's projection expression. It covers every constructible
decoded string, including the empty string and non-ASCII strings.
Julia source: base/gmp.jl:39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Runtime representation: GMP 6.3 manual, Useful Macros and Constants, `gmp_version`.
-/
def VersionTextObservation : Prop :=
  ∀ globals : JuliaLean.base.gmp.LibraryGlobals,
    ConstructibleText globals.versionString →
    (JuliaLean.base.gmp.versionString globals).utf8ByteSize =
      globals.versionString.utf8ByteSize ∧
    ∀ position : Nat,
      (JuliaLean.base.gmp.versionString globals).toList[position]? =
        globals.versionString.toList[position]?

section
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2 Round1

theorem versionTextObservation_proven : VersionTextObservation := by
  intro globals _
  exact ⟨rfl, fun _ => rfl⟩
end

/-- A nonempty ASCII decimal word. Leading zeros and arbitrarily large
mathematical magnitudes are included. -/
def DecimalWord (digits : List Char) : Prop :=
  digits ≠ [] ∧ ∀ digit ∈ digits, '0' ≤ digit ∧ digit ≤ '9'

/-- Independent positional-value specification: each decimal digit contributes
its value times its power of ten. The installed parser instead accumulates
digits from left to right; this specification does not call that accumulator,
the regex matcher, or any version parser. -/
def DecimalMagnitude (digits : List Char) : Nat :=
  (digits.zipIdx).foldr
    (fun indexed total =>
      (indexed.1.toNat - '0'.toNat) * 10^(digits.length - indexed.2 - 1) + total) 0

/-- External GMP versions have two or three decimal components. This constructs
the textual global used by the contract, not a model of a Julia method. -/
def DecimalVersionText (major minor : List Char) (patch : Option (List Char)) : String :=
  String.ofList (major ++ ['.'] ++ minor ++
    match patch with
    | none => []
    | some digits => ['.'] ++ digits)

/-- Full mathematical result contract for a decimal GMP version: all three
numeric fields are exact UInt32 values and both identifier tuples are empty;
the only possible failure is OverflowError for an unrepresentable component.
The relation does not assume success or impose a numeric range precondition. -/
def DecimalVersionResult (major minor patch : Nat)
    (result : Jl JuliaLean.VersionNumbers.VersionNumber) : Prop :=
  match result with
  | .ok value =>
      value.major.val = (major : Int) ∧ value.minor.val = (minor : Int) ∧
      value.patch.val = (patch : Int) ∧ value.pre = [] ∧ value.build = []
  | .error (.overflowError _) =>
      (2 : Nat)^32 ≤ major ∨ (2 : Nat)^32 ≤ minor ∨ (2 : Nat)^32 ≤ patch
  | .error _ => False

/-- `version()` interprets every documented GMP `i.j` or `i.j.k` string using
the mathematical positional values of its components. Includes leading zeros,
all constructible ASCII digit lengths, omitted patch versions, and UInt32
overflow in any component. No callee-correctness premise or successful-run
hypothesis is assumed. The sole format requirements are the external GMP
global's documented decimal representation, with machine-sized text storage.
Julia source: base/gmp.jl:40; base/version.jl:49-89,115-155
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: GMP 6.3 manual, Useful Macros and Constants, `gmp_version`;
doc/src/manual/strings.md, Version Number Literals.
-/
def VersionDecimalComponents : Prop :=
  ∀ (major minor : List Char) (patch : Option (List Char))
    (limbBits : JuliaLean.base.gmp.Cint),
    DecimalWord major → DecimalWord minor →
    (∀ digits, patch = some digits → DecimalWord digits) →
    ConstructibleText (DecimalVersionText major minor patch) →
    DecimalVersionResult (DecimalMagnitude major) (DecimalMagnitude minor)
      (match patch with | none => 0 | some digits => DecimalMagnitude digits)
      (JuliaLean.base.gmp.Models2Group2.libraryVersion
        ⟨DecimalVersionText major minor patch, limbBits⟩)

/-- `major_version()` returns exactly the one-character prefix of the decoded
global, not the complete numeric major version; an empty global raises
BoundsError. Prefix witnesses characterize the result without copying the
model's match expression. Every constructible decoded string is included.
Julia source: base/gmp.jl:41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
-/
def MajorVersionPrefix : Prop :=
  ∀ globals : JuliaLean.base.gmp.LibraryGlobals,
    ConstructibleText globals.versionString →
    (JuliaLean.base.gmp.majorVersion globals = .error .boundsError ↔
      globals.versionString.toList = []) ∧
    ∀ character : Char,
      (JuliaLean.base.gmp.majorVersion globals = .ok character ↔
        ∃ suffix : List Char, globals.versionString.toList = character :: suffix)

section
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2 Round1

theorem majorVersionPrefix_proven : MajorVersionPrefix := by
  intro globals _
  unfold majorVersion versionString
  cases h : globals.versionString.toList with
  | nil => simp
  | cons c cs => simp
end

/-- Reading the C int limb-width global preserves its signed mathematical
value in native Int on the installed 64-bit Unix ABI, including both Cint
extremes. There is no restriction to the later-supported 32/64-bit settings.
Julia source: base/gmp.jl:42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: GMP 6.3 manual, Useful Macros and Constants, `mp_bits_per_limb`.
-/
def BitsPerLimbExact : Prop :=
  ∀ globals : JuliaLean.base.gmp.LibraryGlobals,
    let observed := (JuliaLean.base.gmp.libraryBitsPerLimb globals).val
    observed = globals.limbBits.val ∧
    -(2 : Int)^31 ≤ observed ∧ observed < (2 : Int)^31 ∧
    (observed < 0 ↔ globals.limbBits.val < 0)


section
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2 Round1

theorem bitsPerLimbExact_proven : BitsPerLimbExact := by
  intro globals
  have hb := globals.limbBits.property
  have h : (libraryBitsPerLimb globals).val = globals.limbBits.val := by
    change -(2 : Int)^31 ≤ globals.limbBits.val ∧ globals.limbBits.val ≤ (2 : Int)^31-1 at hb
    change wrapInt .i64 globals.limbBits.val = globals.limbBits.val
    apply wrapInt_of_inRange
    change -(2 : Int)^63 ≤ globals.limbBits.val ∧ globals.limbBits.val ≤ (2 : Int)^63-1
    omega
  rw [h]
  change -(2 : Int)^31 ≤ globals.limbBits.val ∧ globals.limbBits.val ≤ (2 : Int)^31-1 at hb
  exact ⟨rfl, hb.1, by omega, Iff.rfl⟩
end

end Models2Group2

def entriesModels2Group2Bootstrap : List Entry := [
  { id := "gmp-version-text", juliaFile := "base/gmp.jl",
    juliaFns := ["_version()"],
    statement := "The GMP version-global reader preserves the byte length and every character of the decoded, constructible external string.",
    source := "base/gmp.jl:39; GMP 6.3 manual, Useful Macros and Constants (gmp_version)",
    status := .proven, prop := ``Models2Group2.VersionTextObservation, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.versionTextObservation_proven,
    notes := "Reuses JuliaLean.base.gmp.versionString at the installed decoded-library-global boundary." },
  { id := "gmp-version-decimal-components", juliaFile := "base/gmp.jl",
    juliaFns := ["version()"],
    statement := "Every documented GMP decimal i.j or i.j.k version string produces its exact UInt32 components and empty identifiers, or OverflowError for an unrepresentable component; includes leading zeros and all constructible digit lengths.",
    source := "base/gmp.jl:40; base/version.jl:49-89,115-155; GMP 6.3 manual, Useful Macros and Constants (gmp_version)",
    status := .todo, prop := ``Models2Group2.VersionDecimalComponents, thm := none,
    notes := "Uses the installed concrete JuliaLean.VersionNumbers.parse and regex model. Format premises are the documented external GMP global representation; no numeric range or callee-correctness premise." },
  { id := "gmp-major-version-prefix", juliaFile := "base/gmp.jl",
    juliaFns := ["major_version()"],
    statement := "The major-version helper returns the first character of every constructible decoded global and raises BoundsError exactly when that string is empty.",
    source := "base/gmp.jl:41 (first-character invariant)",
    status := .proven, prop := ``Models2Group2.MajorVersionPrefix, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.majorVersionPrefix_proven,
    notes := "Reuses JuliaLean.base.gmp.majorVersion; this source helper returns a Char rather than parsing a numeric major component." },
  { id := "gmp-bits-per-limb-exact", juliaFile := "base/gmp.jl",
    juliaFns := ["bits_per_limb()"],
    statement := "The limb-width reader exactly sign-extends every Cint global to native Int on the installed 64-bit Unix ABI, preserving its signed value and Int32 bounds.",
    source := "base/gmp.jl:42; GMP 6.3 manual, Useful Macros and Constants (mp_bits_per_limb)",
    status := .proven, prop := ``Models2Group2.BitsPerLimbExact, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.bitsPerLimbExact_proven,
    notes := "Reuses JuliaLean.base.gmp.libraryBitsPerLimb; includes the entire Cint domain, not only 32 and 64." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- The initializer's independent zero/identity/frame contract. Every alias
of the supplied mutable object observes zero and an empty native allocation;
every other object header, every native limb, and unrelated represented
source-level state
are preserved. The initialized data pointer names the library's static limb,
which is readable even though no per-object limb allocation remains.
No old-field validity premise is needed: native init overwrites these fields.
Julia source: base/gmp.jl:163; GMP 6.3.0 manual section 5.1 and mpz/init.c.
The typed heap represents valid live BigInt references; external invalid-pointer
behavior lies outside Julia's BigInt-value representation invariant. The
stronger property also holds on symbolic heap images whose static dummy value
is arbitrary; real GMP 6.3 images contain 0xc1a0 at that address. Temporary
GC-root allocator bookkeeping is outside the represented state. -/
def InitIdentityZeroAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (x : InitBigIntRef),
    heap.liveObjects x.address = true →
    let result := initBang x heap
    result.1 = x ∧
    (result.2.objects x.address).value.val = 0 ∧
    (result.2.objects x.address).value.size.val = 0 ∧
    (result.2.objects x.address).value.alloc.val = 0 ∧
    (result.2.objects x.address).dataPointer = heap.dummyPointer ∧
    (∀ alias : InitBigIntRef, alias.address = x.address →
      (result.2.objects alias.address).value.val = 0 ∧
      (result.2.objects alias.address).dataPointer = heap.dummyPointer) ∧
    (∀ other : JInt .u64, other ≠ x.address →
      result.2.objects other = heap.objects other) ∧
    result.2.liveObjects = heap.liveObjects ∧
    result.2.limbs = heap.limbs ∧ result.2.rest = heap.rest ∧
    result.2.dummyPointer = heap.dummyPointer ∧
    (result.2.objects x.address).value.d = [heap.limbs heap.dummyPointer]

section
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2 Round1

theorem initIdentityZeroAndFrame_proven : InitIdentityZeroAndFrame := by
  intro Rest heap x _
  simp [initBang, initCconvert, initUnsafeConvert, initNative]
  refine ⟨rfl, ?_, ?_⟩
  · intro alias h
    simp [h]
  · intro a b h
    simp [h]
end

end JuliaLean.Proofs.base.gmp.Models2Group2


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- Independent arithmetic definition of a set bit in the infinite two's
complement representation. The remainder interval places the integer in the
upper half of a period of length 2^(position+1). Negative quotients include
negative integers without imposing a finite-width interpretation. -/
def ScanOneBit (integer : Int) (position : Nat) : Prop :=
  ∃ quotient remainder : Int,
    integer = quotient * (2 : Int)^(position + 1) + (2 : Int)^position + remainder ∧
    0 ≤ remainder ∧ remainder < (2 : Int)^position

/-- Which bit the caller asks for; this does not call a GMP bit observer. -/
def ScanMatches (integer : Int) (wanted : Bool) (position : Nat) : Prop :=
  if wanted then ScanOneBit integer position else ¬ ScanOneBit integer position

/-- A least matching position is in the requested suffix, contains the
requested bit, and has no earlier matching position in that suffix. -/
def ScanLeast (integer : Int) (wanted : Bool) (start position : Nat) : Prop :=
  start ≤ position ∧ ScanMatches integer wanted position ∧
  ∀ earlier : Nat, start ≤ earlier → earlier < position →
    ¬ ScanMatches integer wanted earlier

/-- The native signed result carries the least matching index modulo 2^64.
If no matching bit exists, it is -1. A real index 2^64-1 and the no-bit
sentinel intentionally share the same returned signed bit pattern; the two
semantic cases are distinguished by the existence of a matching bit, not by
assuming every negative result means failure. The JInt result type itself
supplies its unique signed-range representative. -/
def ScanResult (integer : Int) (wanted : Bool) (start : Nat)
    (result : JuliaLean.base.gmp.Clong) : Prop :=
  (∃ position : Nat, ScanLeast integer wanted start position ∧
    ∃ turns : Int, (position : Int) = result.val + turns * (2 : Int)^64) ∨
  (result.val = -1 ∧ ∀ position : Nat, start ≤ position →
    ¬ ScanMatches integer wanted position)

/-- For every concrete Base UInt64 start, both scan modes return the least
matching infinite two's-complement bit with the source signed reinterpretation,
or the no-bit sentinel, and preserve the entire represented heap. All UInt64
starts, including 2^63 through typemax(UInt64), are included. The only input
premises are a live BigInt reference, normalized GMP storage, and a realizable
native-Int storage extent. The expected bit relation uses an independent
arithmetic interval decomposition, never bitAt, scanBit, or another scanner.

This is the allowed concrete Base instantiation of a full generic-dispatch
model. No law is assumed for custom conversion actions; the model retains
their mutations, errors, wrong-type results, and divergence in the installed
state-and-error monad. The property depends on scanDispatch, nativeCulongConversion,
assertForeignScalar, scanNative, and the closed BigInt Ref adapters.
Julia source: base/gmp.jl:205-209; base/essentials.jl:739,742
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Native specification: GMP 6.3 manual, Integer Logic and Bit Fiddling;
GMP 6.3.0 mpz/scan0.c:43-55 and mpz/scan1.c:43-55.
-/
def ScanLeastBitAndFrame : Prop :=
  ∀ (Rest : Type)
    (heap : JuliaLean.base.gmp.Models2Group2.InitHeap Rest)
    (input : JuliaLean.base.gmp.Models2Group2.InitBigIntRef)
    (wanted : Bool) (start : JuliaLean.base.gmp.Culong),
    heap.liveObjects input.address = true →
    JuliaLean.base.gmp.Valid (heap.objects input.address).value →
    (heap.objects input.address).value.d.length < (2 : Nat)^63 →
    match JuliaLean.base.gmp.Models2Group2.scanDispatch
        (JuliaLean.base.gmp.Models2Group2.nativeCulongConversion Rest)
        wanted input start heap with
    | some (.ok (result, after)) =>
        ScanResult (heap.objects input.address).value.val wanted start.val.toNat result ∧
        after = heap
    | some (.error _) | none => False

end Models2Group2

def entriesModels2Group2Scan : List Entry := [
  { id := "gmp-scan-least-bit-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.scan1(a::BigInt, b)", "MPZ.scan0(a::BigInt, b)"],
    statement := "For every valid constructible BigInt and every concrete UInt64 start, scan1/scan0 return the least matching infinite two's-complement bit as a signed 64-bit bit pattern, or -1 when none exists, preserving the entire represented heap; high unsigned starts and the shared typemax-index/sentinel encoding are included.",
    source := "base/gmp.jl:205-209; base/essentials.jl:739,742; GMP 6.3 manual, Integer Logic and Bit Fiddling; GMP 6.3.0 mpz/scan0.c:43-55 and mpz/scan1.c:43-55",
    status := .todo, prop := ``Models2Group2.ScanLeastBitAndFrame, thm := none,
    notes := "Full untyped-second-argument model preserves both dispatch-selected conversion stages, their order, wrong-type TypeError, state on exceptions, and alias mutation before the native read. Property uses the permitted concrete native Base instance with an independent arithmetic least-bit specification. Registered dependencies: scanDispatch, nativeCulongConversion, assertForeignScalar, scanNative, initCconvert, initUnsafeConvert; finite native search reuses installed MPZ.scan." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- A finite binary support is a strictly increasing list of distinct powers
of two summing to the represented natural number. This mathematical relation
specifies Hamming weight without calling `countBits`, `bitAt`, a limb popcount,
or any source model. The sorted, distinct powers make their number the number
of nonzero binary digits, rather than an arbitrary additive decomposition. -/
def BinarySupportWeight (magnitude weight : Nat) : Prop :=
  ∃ support : List Nat,
    support.Pairwise (fun left right => left < right) ∧
    (support.map (fun position => (2 : Nat)^position)).sum = magnitude ∧
    support.length = weight

/-- `MPZ.popcount` returns -1 exactly for negative BigInts and otherwise the
number of set bits in the nonnegative integer's unique binary support. Zero
is included. For nonnegative inputs the count is bounded by 64 times the live
limb count, so the Culong-to-signed-to-native-Int conversions cannot overflow
on any valid Cint-sized GMP object. Unused storage does not affect the count.

Julia source: base/gmp.jl:238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Native source: GMP 6.3.0 gmp-h.in:1850-1860; GMP manual, Integer Logic and Bit
Fiddling (`mpz_popcount`). The native mpz wrapper handles size zero itself and
calls the positive-count-only mpn primitive only when size is positive.
-/
def MpzPopcountBinarySupport : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    JuliaLean.base.gmp.Valid input → input.d.length < (2 : Nat)^63 →
    let count := (JuliaLean.base.gmp.MPZ.popcount input).val
    (count = -1 ↔ input.val < 0) ∧
    (0 ≤ input.val →
      0 ≤ count ∧ count ≤ 64 * (input.size.val.natAbs : Int) ∧
      BinarySupportWeight input.val.toNat count.toNat)

end Models2Group2

def entriesModels2Group2Observations : List Entry := [
  { id := "gmp-mpz-popcount-binary-support", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.popcount(a::BigInt)"],
    statement := "For every constructible valid BigInt, MPZ.popcount returns -1 exactly for negative values and otherwise the number of distinct powers of two in its binary expansion, bounded by 64 times the live limb count; zero has count zero.",
    source := "base/gmp.jl:238; GMP 6.3 manual, Integer Logic and Bit Fiddling; GMP 6.3.0 gmp-h.in:1850-1860",
    status := .todo, prop := ``Models2Group2.MpzPopcountBinarySupport, thm := none,
    notes := "Reuses JuliaLean.base.gmp.MPZ.popcount unchanged. Independent finite-support specification uses distinct power-of-two summation, not countBits/bitAt. The native mpz wrapper guards zero before mpn_popcount. No coverage is claimed for the distinct unguarded mpn_popcount(::BigInt) method at line241." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- The documented absolute-value Hamming weight includes zero and either sign.
The source's zero guard avoids the positive-count precondition of native
mpn_popcount; spare limbs beyond the live prefix cannot affect the result.
The independent finite binary-support relation is shared with the registered
MPZ.popcount observation, and never calls the implementation's bit counter.
Julia source: base/gmp.jl:601-606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Native boundary: GMP 6.3.0 mpn/generic/popham.c:55-56; its result is the
Hamming weight of the live UInt64 limbs, at most 64*(2^31-1), so the UInt64
result fits the checked native Int conversion on the installed 64-bit ABI. -/
def CountOnesAbsBinarySupport : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    JuliaLean.base.gmp.Valid input → input.d.length < (2 : Nat)^63 →
    let count := (JuliaLean.base.gmp.countOnesAbs input).val
    0 ≤ count ∧ count ≤ 64 * (input.size.val.natAbs : Int) ∧
    (count = 0 ↔ input.val = 0) ∧
    BinarySupportWeight input.val.natAbs count.toNat

/-- On its explicitly documented nonzero domain, the internal helper returns
an exact binary-magnitude bracket and its unchecked one-based top-limb load
is within the live stored prefix. This does not grant the helper a behavior
on zero, which the Julia source explicitly declares undefined.

The Valid invariant bounds abs(size) by the nonnegative part of a Cint alloc,
therefore below 2^31. Hence native Cint abs cannot encounter typemin(Cint),
and promotion to Int for the product by 64 and subtraction cannot overflow.
The independent power-of-two bracket does not repeat the leading-zeros body.
Julia source: base/gmp.jl:608-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BitMagnitudeBracketAndReadSafety : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    JuliaLean.base.gmp.Valid input → input.d.length < (2 : Nat)^63 →
    input.val ≠ 0 →
    let width := (JuliaLean.base.gmp.bitMagnitude input).val
    0 < input.size.val.natAbs ∧
    input.size.val.natAbs - 1 < input.d.length ∧
    0 < width ∧ width ≤ 64 * (input.size.val.natAbs : Int) ∧
    (2 : Nat)^(width.toNat - 1) ≤ input.val.natAbs ∧
    input.val.natAbs < (2 : Nat)^width.toNat

/-- Top-set-bit returns zero for zero, the unique positive binary width for
positive BigInts, and DomainError for every negative BigInt. The specification
includes every valid constructible storage representation, including spare
limbs, and independently characterizes width by adjacent powers of two.
Julia source: base/gmp.jl:619-623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/int.jl:546-556; negative arguments are only supported for
BitSigned, which excludes BigInt. Error payload/message text is outside the
installed Jl error interface; the exception class and branch are retained. -/
def TopSetBitDomainAndWidth : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    JuliaLean.base.gmp.Valid input → input.d.length < (2 : Nat)^63 →
    if input.val < 0 then
      ∃ message, JuliaLean.base.gmp.topSetBit input = .error (.domainError message)
    else
      ∃ width : JuliaLean.base.gmp.Clong,
        JuliaLean.base.gmp.topSetBit input = .ok width ∧
        0 ≤ width.val ∧
        (width.val = 0 ↔ input.val = 0) ∧
        width.val ≤ 64 * (input.size.val.natAbs : Int) ∧
        (0 < input.val →
          (2 : Nat)^(width.val.toNat - 1) ≤ input.val.natAbs ∧
          input.val.natAbs < (2 : Nat)^width.val.toNat)

end Models2Group2

def entriesModels2Group2BitQueries : List Entry := [
  { id := "gmp-count-ones-abs-binary-support", juliaFile := "base/gmp.jl",
    juliaFns := ["count_ones_abs(x::BigInt)"],
    statement := "For every valid constructible BigInt, count_ones_abs returns the number of distinct powers of two in its absolute-value binary expansion, is zero exactly at zero, and lies between zero and 64 times the live limb count; unused storage does not affect it.",
    source := "base/gmp.jl:601-606; GMP 6.3.0 mpn/generic/popham.c:55-56; GMP manual, Low-level Functions, mpn_popcount",
    status := .todo, prop := ``Models2Group2.CountOnesAbsBinarySupport, thm := none,
    notes := "Reuses JuliaLean.base.gmp.countOnesAbs unchanged. Its zero guard avoids calling mpn_popcount with zero limbs; nonzero Valid inputs give a positive Cint-sized prefix and an Int64-sized result. Uses independently defined BinarySupportWeight from the group-specific MPZ.popcount property. Does not claim completion of the unguarded standalone mpn_popcount method at line241." },
  { id := "gmp-bit-magnitude-bracket-read-safety", juliaFile := "base/gmp.jl",
    juliaFns := ["_bit_magnitude(x::BigInt)"],
    statement := "On every valid constructible nonzero BigInt, _bit_magnitude reads an existing live top limb and returns the unique positive binary width, bounded by 64 times the live limb count and characterized by adjacent powers of two.",
    source := "base/gmp.jl:608-612; doc/src/manual/mathematical-operations.md:471-484",
    status := .todo, prop := ``Models2Group2.BitMagnitudeBracketAndReadSafety, thm := none,
    notes := "Reuses JuliaLean.base.gmp.bitMagnitude unchanged on the explicitly documented nonzero domain. Valid bounds abs(size) below 2^31; native abs, promoted multiplication by 64, and subtraction are exact, and the baseline Nat arithmetic therefore agrees throughout the complete defined domain. No behavior is claimed for the source's undefined zero call." },
  { id := "gmp-top-set-bit-domain-width", juliaFile := "base/gmp.jl",
    juliaFns := ["top_set_bit(x::BigInt)"],
    statement := "For every valid constructible BigInt, top_set_bit raises DomainError on negative values, returns zero exactly for zero, and returns the unique positive binary width for positive values, with a live-limb bound.",
    source := "base/gmp.jl:619-623; base/int.jl:546-556",
    status := .todo, prop := ``Models2Group2.TopSetBitDomainAndWidth, thm := none,
    notes := "Reuses JuliaLean.base.gmp.topSetBit and its bitMagnitude callee unchanged. The source negative check precedes the zero return and nonzero helper call. Adjacent powers characterize the result independently of leading_zeros, top-limb extraction, or another converter." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- The internal MPZ comparator classifies every pair of normalized GMP
integers by their mathematical order, with exactly the three native-Int
results -1, 0, and 1. Signed limb counts and allocation counts are already
Cint values; `Valid` bounds every limb read by the available storage and
requires a nonzero top limb, while allowing arbitrary unused storage. Both
limb snapshots have native-Int-representable lengths, as actual Julia-backed
storage must. No integer-magnitude restriction is imposed beyond these actual
representation invariants. This order specification does not use the model's
`sgn`, subtraction, or C comparison algorithm.

Julia source: base/gmp.jl:262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
GMP 6.3.0: mpz/cmp.c:35-53 and gmp-h.in:2080-2103; the actual implementation,
more specifically than the public sign-only C API, always returns -1, 0, or 1.
-/
def MpzCmpTrichotomy : Prop :=
  ∀ left right : JuliaLean.base.gmp.BigInt,
    JuliaLean.base.gmp.Valid left → JuliaLean.base.gmp.Valid right →
    left.d.length < (2 : Nat)^63 → right.d.length < (2 : Nat)^63 →
    let result := (JuliaLean.base.gmp.MPZ.cmp left right).val
    (result = -1 ↔ left.val < right.val) ∧
    (result = 0 ↔ left.val = right.val) ∧
    (result = 1 ↔ right.val < left.val)

end Models2Group2

theorem mpzCmpTrichotomy_proven : Models2Group2.MpzCmpTrichotomy := by
  intro left right _ _ _ _
  exact (JuliaLean.ChatGPT.Batch4.Group7.cc_comparison_of_sgn left.val right.val
    (JuliaLean.base.gmp.MPZ.cmp left right)
    (JuliaLean.ChatGPT.Batch4.Group7.cl_wrap_sgn _)).2

def entriesModels2Group2Cmp : List Entry := [
  { id := "gmp-mpz-cmp-trichotomy", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.cmp(a::BigInt, b::BigInt)"],
    statement := "For every pair of constructible valid GMP integer representations, MPZ.cmp returns native Int -1, 0, or 1 exactly when the first mathematical integer is less than, equal to, or greater than the second.",
    source := "base/gmp.jl:262; GMP 6.3.0 mpz/cmp.c:35-53 and gmp-h.in:2080-2103 (exact comparison-result invariant)",
    status := .proven, prop := ``Models2Group2.MpzCmpTrichotomy, thm := some ``JuliaLean.Proofs.base.gmp.mpzCmpTrichotomy_proven,
    notes := "Reuses JuliaLean.base.gmp.MPZ.cmp unchanged. Exact GMP 6.3.0 source verifies normalization to -1/0/1 even though the GMP manual only specifies the sign. Includes zero, negative values, unequal limb counts, arbitrary limb magnitudes, and unused capacity with native-Int-representable storage lengths; no new callee or correctness premise." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- Representation coherence between the canonical limb snapshot and native
heap at the object's data pointer. The scalar native comparisons read only
the first limb, and only when the signed size is +1 or -1. This is a memory
representation invariant, not a condition on any conversion callback. -/
def ScalarCmpFirstLimbCoherent {Rest : Type}
    (heap : JuliaLean.base.gmp.Models2Group2.InitHeap Rest)
    (input : JuliaLean.base.gmp.Models2Group2.InitBigIntRef) : Prop :=
  ∀ low : JuliaLean.base.gmp.Limb,
    (heap.objects input.address).value.d.head? = some low →
    heap.limbs (heap.objects input.address).dataPointer = low

/-- Every native Clong input, including typemin, is compared for equality
exactly, and the complete represented heap is preserved. The result is an
exactly widened Cint. These expectations use mathematical equality and range,
not native size subtraction, ABS_CAST, normalization, or another comparator.

No unnecessary scalar or signed-size restriction is imposed. In particular,
Cint narrowing may change the result's sign at a positive INT_MAX limb count
compared with a negative scalar, so a sign-only contract is deliberately not
asserted over the full source domain. Zero detection remains exact there.
This is the permitted concrete Base instantiation of the complete generic
wrapper; there are no assumed laws for custom conversion actions.
Julia source: base/gmp.jl:263; GMP 6.3.0 mpz/cmp_si.c:35-69.
-/
def MpzCmpSiEqualityAndFrame : Prop :=
  ∀ (Rest : Type)
    (heap : JuliaLean.base.gmp.Models2Group2.InitHeap Rest)
    (input : JuliaLean.base.gmp.Models2Group2.InitBigIntRef)
    (scalar : JuliaLean.base.gmp.Clong),
    heap.liveObjects input.address = true →
    JuliaLean.base.gmp.Valid (heap.objects input.address).value →
    (heap.objects input.address).value.d.length < (2 : Nat)^63 →
    ScalarCmpFirstLimbCoherent heap input →
    match JuliaLean.base.gmp.Models2Group2.cmpSiDispatch
        (JuliaLean.base.gmp.Models2Group2.nativeClongConversion Rest)
        input scalar heap with
    | some (.ok (result, after)) =>
        (result.val = 0 ↔ (heap.objects input.address).value.val = scalar.val) ∧
        -(2 : Int)^31 ≤ result.val ∧ result.val < (2 : Int)^31 ∧
        after = heap
    | some (.error _) | none => False

/-- Every native UInt64 input receives exactly -1/0/1 according to its
mathematical order against the represented BigInt, and the entire heap remains
unchanged. The domain includes typemax(UInt64), all BigInt signs and magnitudes,
and arbitrary unused storage satisfying the actual representation invariants.
The expected result uses independent order relations rather than sgn, numeric
subtraction, the native comparison cases, or a callee-correctness premise.
Julia source: base/gmp.jl:264; GMP 6.3.0 mpz/cmp_ui.c:35-77.
-/
def MpzCmpUiTrichotomyAndFrame : Prop :=
  ∀ (Rest : Type)
    (heap : JuliaLean.base.gmp.Models2Group2.InitHeap Rest)
    (input : JuliaLean.base.gmp.Models2Group2.InitBigIntRef)
    (scalar : JuliaLean.base.gmp.Culong),
    heap.liveObjects input.address = true →
    JuliaLean.base.gmp.Valid (heap.objects input.address).value →
    (heap.objects input.address).value.d.length < (2 : Nat)^63 →
    ScalarCmpFirstLimbCoherent heap input →
    match JuliaLean.base.gmp.Models2Group2.cmpUiDispatch
        (JuliaLean.base.gmp.Models2Group2.nativeCulongConversion Rest)
        input scalar heap with
    | some (.ok (result, after)) =>
        (result.val = -1 ↔ (heap.objects input.address).value.val < scalar.val) ∧
        (result.val = 0 ↔ (heap.objects input.address).value.val = scalar.val) ∧
        (result.val = 1 ↔ scalar.val < (heap.objects input.address).value.val) ∧
        after = heap
    | some (.error _) | none => False

end Models2Group2

theorem mpzCmpUiTrichotomyAndFrame_proven : Models2Group2.MpzCmpUiTrichotomyAndFrame := by
  intro Rest heap input scalar hlive hval hlen hcoh
  simp only [JuliaLean.base.gmp.Models2Group2.cmpUiDispatch,
    JuliaLean.base.gmp.Models2Group2.nativeCulongConversion,
    JuliaLean.base.gmp.Models2Group2.assertForeignScalar,
    JuliaLean.base.gmp.Models2Group2.initCconvert,
    JuliaLean.base.gmp.Models2Group2.initUnsafeConvert,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hlive, ↓reduceIte]
  have hw (n : Int) :
      (JInt.wrap .i64 (JInt.rem .i32 (JInt.wrap .i64 (JuliaLean.base.gmp.sgn n))).val).val =
        JuliaLean.base.gmp.sgn n := by
    unfold JuliaLean.base.gmp.sgn
    split <;> (try split) <;> rfl
  have hcmp := JuliaLean.ChatGPT.Batch4.Group7.cc_comparison_of_sgn
    (heap.objects input.address).value.val scalar.val
    (JInt.wrap .i64 (JInt.rem .i32 (JuliaLean.base.gmp.MPZ.cmpUi
      (heap.objects input.address).value scalar)).val) (hw _)
  exact ⟨hcmp.2.1, hcmp.2.2.1, hcmp.2.2.2, rfl⟩

def entriesModels2Group2ScalarCmp : List Entry := [
  { id := "gmp-mpz-cmp-si-equality-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.cmp_si(a::BigInt, b)"],
    statement := "For every valid constructible BigInt heap representation and every native Clong scalar, cmp_si detects mathematical equality exactly, returns an exactly widened Cint, and preserves the entire represented heap; typemin(Clong) and extreme signed limb counts are included.",
    source := "base/gmp.jl:263; base/essentials.jl:739,742; GMP 6.3.0 mpz/cmp_si.c:35-69; gmp-impl.h:536-538",
    status := .todo, prop := ``Models2Group2.MpzCmpSiEqualityAndFrame, thm := none,
    notes := "The full generic wrapper preserves both custom conversion stages, wrong-type TypeError, state on exceptions, divergence, and alias mutation before the native read. The property uses the concrete native Base instance. Exact native result is not normalized; full Cint narrowing prevents claiming an unconditional sign contract at extreme size differences. Dependencies: cmpSiDispatch, cmpSiNative, nativeClongConversion, ScalarConversionOps, assertForeignScalar, initCconvert, initUnsafeConvert." },
  { id := "gmp-mpz-cmp-ui-trichotomy-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.cmp_ui(a::BigInt, b)"],
    statement := "For every valid constructible BigInt heap representation and every native UInt64 scalar, cmp_ui returns -1, 0, or 1 exactly according to mathematical order and preserves the entire represented heap.",
    source := "base/gmp.jl:264; base/essentials.jl:739,742; GMP 6.3.0 mpz/cmp_ui.c:35-77",
    status := .proven, prop := ``Models2Group2.MpzCmpUiTrichotomyAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.mpzCmpUiTrichotomyAndFrame_proven,
    notes := "Full untyped-scalar dispatch uses the two conversion stages in source order and reads the heap afterward. The concrete property reuses installed MPZ.cmpUi, verified against exact GMP6.3 no-nails source, and nativeCulongConversion; no callback correctness law. Additional dependencies: cmpUiDispatch, ScalarConversionOps, assertForeignScalar, initCconvert, initUnsafeConvert." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

namespace Models2Group2

/-- Exact ordering of rational coordinates; denominators are positive for
finite Float64 values. This specification does not round or convert numbers. -/
def GetDRationalLE (left right : Int × Nat) : Prop :=
  left.1 * (right.2 : Int) ≤ right.1 * (left.2 : Int)

/-- A finite conversion toward zero is the greatest representable value at
most a nonnegative source integer, or the least representable value at least
a negative source integer. Quantification ranges over all finite binary64 bit
patterns, including subnormals and both signed zeros. This extremal-neighbor
specification does not call any integer-to-float converter or rounding kernel. -/
def GetDFiniteNeighbor (integer : Int) (result : FV .f64) : Prop :=
  result.isfinite = true ∧ 0 < result.toRat.2 ∧
  if integer < 0 then
    integer * (result.toRat.2 : Int) ≤ result.toRat.1 ∧
    ∀ candidate : FV .f64, candidate.isfinite = true →
      integer * (candidate.toRat.2 : Int) ≤ candidate.toRat.1 →
      GetDRationalLE result.toRat candidate.toRat
  else
    result.toRat.1 ≤ integer * (result.toRat.2 : Int) ∧
    ∀ candidate : FV .f64, candidate.isfinite = true →
      candidate.toRat.1 ≤ integer * (candidate.toRat.2 : Int) →
      GetDRationalLE candidate.toRat result.toRat

/-- GMP's native integer-to-double result has the integer's sign (positive
zero for zero), is never NaN, is infinite exactly at the binary64 exponent
boundary, and otherwise is the closest finite representable neighbor toward
zero. This states a mathematical order/format contract, not a conversion
algorithm or equality with another converter. -/
def GetDResult (integer : Int) (result : FV .f64) : Prop :=
  result.isnan = false ∧
  result.signbit = decide (integer < 0) ∧
  (result.isinf = true ↔ (2 : Nat)^1024 ≤ integer.natAbs) ∧
  (integer.natAbs < (2 : Nat)^1024 → GetDFiniteNeighbor integer result)

/-- The concrete native `MPZ.get_d` result obeys the independent nearest
finite neighbor/overflow contract for every normalized BigInt with a
machine-sized storage extent. No integer-magnitude bound, successful-conversion
premise, or callee-correctness law is assumed. The Cint size/capacity fields,
`Valid` storage invariant, and native-Int storage-length bound are actual
representation requirements, and retain zero and all signs, limb counts,
limb contents, and unused capacity of constructible objects.

Julia source: base/gmp.jl:272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Native specification: GMP 6.3 manual, Converting Integers (`mpz_get_d`);
GMP 6.3.0 mpz/get_d.c:35-44 and mpn/generic/get_d.c:271-277,304-308.
-/
def MpzGetDTruncationAndOverflow : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    JuliaLean.base.gmp.Valid input → input.d.length < (2 : Nat)^63 →
    GetDResult input.val (JuliaLean.base.gmp.Models2Group2.mpzGetD input)

end Models2Group2

def entriesModels2Group2GetD : List Entry := [
  { id := "gmp-mpz-get-d-truncation-overflow", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.get_d(a::BigInt)"],
    statement := "For every constructible normalized BigInt, MPZ.get_d returns the closest finite Float64 toward zero when the magnitude is below 2^1024 and signed infinity otherwise; it preserves sign, returns positive zero for zero, and never returns NaN.",
    source := "base/gmp.jl:272; GMP 6.3 manual, Converting Integers; GMP 6.3.0 mpz/get_d.c:35-44 and mpn/generic/get_d.c:271-277,304-308",
    status := .todo, prop := ``Models2Group2.MpzGetDTruncationAndOverflow, thm := none,
    notes := "Missing proof: transport BignumsGmpExplicitIeeeConversion_proven's ToZero floor/ceiling contract to GetDFiniteNeighbor, establish finiteness below 2^1024 and the exact infinity threshold, and bridge its GMPInput storage premises to this Valid/native-length domain. mpzGetD's overflow branch is signed infinity; the baseline MPZ.getD saturates instead." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2

open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- The concrete native Cint result is exactly 0 or 1 according to the
independently defined infinite two's-complement bit interval. The complete
wrapper with native Base UInt64 conversion returns that mathematical bit as
Bool and preserves every part of the represented heap. Every unsigned
position is included, especially 2^63 through typemax(UInt64), and aliases,
zero and unused storage remain in the valid constructible input domain.

ScanOneBit uses an arithmetic period/interval decomposition, never bitAt,
MPZ.tstbit, a scanner, or a law assumed of a selected conversion. The generic
model retains all untyped input/root types and their actual conversion effects;
this is its permitted concrete Base instantiation. The first conjunct also
registers the narrow native helper's exact Cint-result invariant.
Julia source: base/gmp.jl:290; GMP 6.3 manual, Integer Logic and Bit Fiddling;
GMP 6.3.0 mpz/tstbit.c:49-81
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def TstbitBitAndFrame : Prop :=
  (∀ (input : BigInt) (position : Culong),
    Valid input → input.d.length < (2 : Nat)^63 →
    match tstbitNative input position with
    | .ok result =>
      (result.val = 0 ∨ result.val = 1) ∧
      (result.val = 1 ↔ ScanOneBit input.val position.val.toNat)
    | .error _ => False) ∧
  (∀ (Rest : Type) (heap : InitHeap Rest)
    (input : InitBigIntRef) (position : Culong),
    heap.liveObjects input.address = true →
    Valid (heap.objects input.address).value →
    (heap.objects input.address).value.d.length < (2 : Nat)^63 →
    match tstbitDispatch (nativeCulongConversion Rest) input position heap with
    | some (.ok (result, after)) =>
      (result = true ↔
        ScanOneBit (heap.objects input.address).value.val position.val.toNat) ∧
      after = heap
    | some (.error _) | none => False)

end JuliaLean.Proofs.base.gmp.Models2Group2

namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

def entriesModels2Group2Tstbit : List Entry := [
  { id := "gmp-tstbit-value-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.tstbit(a::BigInt, b)"],
    statement := "For every valid constructible BigInt and every UInt64 position, the native Cint test is exactly 0 or 1 for the independent infinite two's-complement bit; the complete wrapper's concrete Base conversion instance returns that bit as Bool and preserves the entire represented heap, including high unsigned indices, zero and spare storage.",
    source := "base/gmp.jl:159,290; base/int.jl:699; doc/src/manual/calling-c-and-fortran-code.md:248-265; GMP 6.3 manual, Integer Logic and Bit Fiddling; GMP 6.3.0 mpz/tstbit.c:49-81",
    status := .todo, prop := ``Models2Group2.TstbitBitAndFrame, thm := none,
    notes := "Missing proof: show tstbitNative's native size/index conversions and beyond-storage sign extension agree with ScanOneBit's arithmetic period decomposition for every UInt64 position, then lift through tstbitDispatch/nativeCulongConversion and rem_Integer_Bool. Existing finite MPZ.tstbit alone does not establish high unsigned-index sign extension or the independent bit specification." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry JuliaLean.BootCov

namespace Models2Group2

/-- Independent representation relation for built-in integer runtime type
objects. Fixed-width types cover exactly their mathematical ranges; Bool admits
zero and one. BigInt admits any integer with a normalized, constructible GMP
representation. The relation does not inspect or call any type-return method,
conversion routine, reification adapter, or BigInt constructor. Other runtime
types, abstract types, and malformed parameterizations do not satisfy it. -/
def TypeCanStoreInteger (runtimeType : JType) (integer : Int) : Prop :=
  match runtimeType with
  | .dt name false [] =>
      if name = "BigInt" then
        ∃ value : JuliaLean.base.gmp.BigInt,
          JuliaLean.base.gmp.Valid value ∧ value.d.length < (2 : Nat)^63 ∧
          value.val = integer
      else if name = "Bool" then integer = 0 ∨ integer = 1
      else
        ∃ machineType : IntTy,
          name = machineType.name ∧ machineType.min ≤ integer ∧ integer ≤ machineType.max
  | _ => False

/-- The result can retain the entire signed and unsigned 128-bit ranges and
the two concrete, constructible values ±2^128 beyond those ranges. These
numeric observations reject every machine integer type result, without merely
asserting equality with a singleton BigInt type tag. -/
def TypeStoresWideIntegerRanges (runtimeType : JType) : Prop :=
  (∀ value : JInt .i128, TypeCanStoreInteger runtimeType value.val) ∧
  (∀ value : JInt .u128, TypeCanStoreInteger runtimeType value.val) ∧
  TypeCanStoreInteger runtimeType ((2 : Int)^128) ∧
  TypeCanStoreInteger runtimeType (-((2 : Int)^128))

/-- Every value already represented by a constructible valid BigInt remains
representable by the result type. This quantifies over the full existing
arbitrary-precision domain, rather than just bounded machine specializations. -/
def TypeStoresAllBigInts (runtimeType : JType) : Prop :=
  ∀ value : JuliaLean.base.gmp.BigInt,
    JuliaLean.base.gmp.Valid value → value.d.length < (2 : Nat)^63 →
    TypeCanStoreInteger runtimeType value.val

/-- Int128 widening preserves all machine values and supports exact addition
and subtraction of every two Int128 inputs, including extreme endpoints.
Julia source: base/gmp.jl:298; documented widening guarantee:
base/operators.jl:954-974 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def WidenInt128TypeRange : Prop :=
  let result := JuliaLean.base.gmp.Models2Group2.widenInt128TypeView
  TypeStoresWideIntegerRanges result ∧
  ∀ left right : JInt .i128,
    TypeCanStoreInteger result (left.val + right.val) ∧
    TypeCanStoreInteger result (left.val - right.val)

/-- UInt128 widening preserves the complete unsigned range, admits negative
results, and supports exact addition/subtraction for every pair, without
wrapping at either 128-bit boundary.
Julia source: base/gmp.jl:299; documented widening guarantee:
base/operators.jl:954-974 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def WidenUInt128TypeRange : Prop :=
  let result := JuliaLean.base.gmp.Models2Group2.widenUInt128TypeView
  TypeStoresWideIntegerRanges result ∧
  ∀ left right : JInt .u128,
    TypeCanStoreInteger result (left.val + right.val) ∧
    TypeCanStoreInteger result (left.val - right.val)

/-- Widening BigInt retains every constructible arbitrary-precision value and
strictly exceeds every built-in fixed-width integer range.
Julia source: base/gmp.jl:300; base/operators.jl:954-974;
doc/src/manual/integers-and-floating-point-numbers.md:555-568
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def WidenBigIntTypeRange : Prop :=
  let result := JuliaLean.base.gmp.Models2Group2.widenBigIntTypeView
  TypeStoresWideIntegerRanges result ∧ TypeStoresAllBigInts result

/-- Whatever integer runtime type selected this Base promotion rule, its
result retains every constructible BigInt and both complete 128-bit ranges,
including values beyond both fixed-width ranges. The input type is arbitrary;
no restriction to built-in integer types or correctness law is imposed.
Julia source: base/gmp.jl:472; doc/src/manual/conversion-and-promotion.md:202-216;
doc/src/manual/integers-and-floating-point-numbers.md:555-568
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def PromoteIntegerTypeRange : Prop :=
  ∀ sourceType : JType,
    let result := JuliaLean.base.gmp.Models2Group2.promoteIntegerTypeView sourceType
    TypeStoresWideIntegerRanges result ∧ TypeStoresAllBigInts result

/-- `big` on any integer runtime type yields a representation retaining the
whole constructible BigInt domain and exceeding both 128-bit integer ranges.
The source type is universally quantified, including custom selected cases.
Julia source: base/gmp.jl:489; documented type-level `big` promise:
base/number.jl:434-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BigIntegerTypeRange : Prop :=
  ∀ sourceType : JType,
    let result := JuliaLean.base.gmp.Models2Group2.bigIntegerTypeView sourceType
    TypeStoresWideIntegerRanges result ∧ TypeStoresAllBigInts result

/-- The type-level rational result has the concrete Rational shape with one
integer component type shared by numerator and denominator. That component
retains every constructible BigInt, both complete 128-bit ranges, and ±2^128.
This rejects a fixed-width component, a wrong arity, an abstract type, or an
unrelated type result. No rational arithmetic or user callee is parameterized.
Julia source: base/gmp.jl:490; base/rational.jl:4-15;
base/number.jl:434-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def BigRationalTypeRange : Prop :=
  ∀ sourceType : JType,
    match JuliaLean.base.gmp.Models2Group2.bigRationalTypeView sourceType with
    | .dt "Rational" false [component] =>
        TypeStoresWideIntegerRanges component ∧ TypeStoresAllBigInts component
    | _ => False

section
open JuliaLean JuliaLean.BootCov JuliaLean.base.gmp
open JuliaLean.ChatGPT.Batch4.Group6

private theorem bigIntStoresSmall (n : Int) (h : n.natAbs < (2 : Nat)^192) :
    TypeCanStoreInteger (.dt "BigInt" false []) n := by
  have len := cgLimbsLengthLe 3 n.natAbs h
  have small : (limbsOfNat n.natAbs).length < (2 : Nat)^31 := by omega
  refine ⟨ofInt n, (cgGMPInputOfInt n small).1, ?_, rfl⟩
  change (limbsOfNat n.natAbs).length < (2 : Nat)^63
  omega

private theorem bigIntStoresWide : TypeStoresWideIntegerRanges (.dt "BigInt" false []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro value
    apply bigIntStoresSmall
    have hv := value.property
    change -170141183460469231731687303715884105728 ≤ value.val ∧ value.val ≤ 170141183460469231731687303715884105727 at hv
    change value.val.natAbs < 6277101735386680763835789423207666416102355444464034512896
    omega
  · intro value
    apply bigIntStoresSmall
    have hv := value.property
    change 0 ≤ value.val ∧ value.val ≤ 340282366920938463463374607431768211455 at hv
    change value.val.natAbs < 6277101735386680763835789423207666416102355444464034512896
    omega
  · apply bigIntStoresSmall; decide
  · apply bigIntStoresSmall; decide

private theorem bigIntStoresExisting : TypeStoresAllBigInts (.dt "BigInt" false []) := by
  intro value valid length
  exact ⟨value, valid, length, rfl⟩

theorem widenInt128TypeRange_proven : WidenInt128TypeRange := by
  refine ⟨bigIntStoresWide, ?_⟩
  intro left right
  have hl := left.property
  have hr := right.property
  change -170141183460469231731687303715884105728 ≤ left.val ∧ left.val ≤ 170141183460469231731687303715884105727 at hl
  change -170141183460469231731687303715884105728 ≤ right.val ∧ right.val ≤ 170141183460469231731687303715884105727 at hr
  constructor <;> apply bigIntStoresSmall <;>
    change _ < 6277101735386680763835789423207666416102355444464034512896 <;> omega

theorem widenUInt128TypeRange_proven : WidenUInt128TypeRange := by
  refine ⟨bigIntStoresWide, ?_⟩
  intro left right
  have hl := left.property
  have hr := right.property
  change 0 ≤ left.val ∧ left.val ≤ 340282366920938463463374607431768211455 at hl
  change 0 ≤ right.val ∧ right.val ≤ 340282366920938463463374607431768211455 at hr
  constructor <;> apply bigIntStoresSmall <;>
    change _ < 6277101735386680763835789423207666416102355444464034512896 <;> omega

theorem widenBigIntTypeRange_proven : WidenBigIntTypeRange :=
  ⟨bigIntStoresWide, bigIntStoresExisting⟩
theorem promoteIntegerTypeRange_proven : PromoteIntegerTypeRange := by
  intro sourceType
  exact ⟨bigIntStoresWide, bigIntStoresExisting⟩
theorem bigIntegerTypeRange_proven : BigIntegerTypeRange := by
  intro sourceType
  exact ⟨bigIntStoresWide, bigIntStoresExisting⟩
theorem bigRationalTypeRange_proven : BigRationalTypeRange := by
  intro sourceType
  exact ⟨bigIntStoresWide, bigIntStoresExisting⟩
end

end Models2Group2

def entriesModels2Group2TypeViews : List Entry := [
  { id := "gmp-widen-int128-range", juliaFile := "base/gmp.jl",
    juliaFns := ["widen(::Type{Int128})"],
    statement := "The Int128 widening result represents every signed/unsigned 128-bit integer, ±2^128, and exact sums and differences of every two Int128 values.",
    source := "base/gmp.jl:298; base/operators.jl:954-974 (widen's precision and overflow guarantee)",
    status := .proven, prop := ``Models2Group2.WidenInt128TypeRange, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.widenInt128TypeRange_proven,
    notes := "Reuses widen128 true through reifyBigIntType and widenInt128TypeView into BootCov.JType; no canonical method is replaced. The numeric representation contract can reject a wrong runtime type result." },
  { id := "gmp-widen-uint128-range", juliaFile := "base/gmp.jl",
    juliaFns := ["widen(::Type{UInt128})"],
    statement := "The UInt128 widening result represents every signed/unsigned 128-bit integer, ±2^128, and exact sums and differences of every two UInt128 values, including negative differences.",
    source := "base/gmp.jl:299; base/operators.jl:954-974 (widen's precision and overflow guarantee)",
    status := .proven, prop := ``Models2Group2.WidenUInt128TypeRange, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.widenUInt128TypeRange_proven,
    notes := "Reuses widen128 false through the concrete BootCov.JType view; properties use numeric ranges and arithmetic results rather than singleton equality." },
  { id := "gmp-widen-bigint-range", juliaFile := "base/gmp.jl",
    juliaFns := ["widen(::Type{BigInt})"],
    statement := "The BigInt widening result retains every constructible normalized BigInt and all 128-bit machine values, including ±2^128 beyond those fixed-width ranges.",
    source := "base/gmp.jl:300; base/operators.jl:954-974; doc/src/manual/integers-and-floating-point-numbers.md:555-568",
    status := .proven, prop := ``Models2Group2.WidenBigIntTypeRange, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.widenBigIntTypeRange_proven,
    notes := "Reuses widenBigInt through the concrete BootCov.JType view; the full normalized constructible BigInt input domain is retained." },
  { id := "gmp-promote-integer-type-range", juliaFile := "base/gmp.jl",
    juliaFns := ["promote_rule(::Type{BigInt}, ::Type{<:Integer})"],
    statement := "For every runtime integer type selecting this Base promotion rule, its result retains every constructible BigInt, both complete 128-bit integer ranges, and ±2^128.",
    source := "base/gmp.jl:472; doc/src/manual/conversion-and-promotion.md:202-216; doc/src/manual/integers-and-floating-point-numbers.md:555-568",
    status := .proven, prop := ``Models2Group2.PromoteIntegerTypeRange, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.promoteIntegerTypeRange_proven,
    notes := "Reuses promoteRuleInteger, with arbitrary ignored JType input preserved after method selection. Includes custom and UnionAll type representations; no callback or callee law." },
  { id := "gmp-big-integer-type-range", juliaFile := "base/gmp.jl",
    juliaFns := ["big(::Type{<:Integer})"],
    statement := "For every integer runtime type selecting this Base method, big returns a type retaining every constructible BigInt, both complete 128-bit ranges, and ±2^128.",
    source := "base/gmp.jl:489; base/number.jl:434-452 (arbitrary-precision type guarantee)",
    status := .proven, prop := ``Models2Group2.BigIntegerTypeRange, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.bigIntegerTypeRange_proven,
    notes := "Reuses bigIntegerType through a concrete JType view, retaining the full arbitrary source-type domain after dispatch." },
  { id := "gmp-big-rational-type-range", juliaFile := "base/gmp.jl",
    juliaFns := ["big(::Type{<:Rational})"],
    statement := "For every rational runtime type selecting this Base method, big returns a concrete one-parameter Rational whose numerator/denominator component type retains every constructible BigInt, both complete 128-bit ranges, and ±2^128.",
    source := "base/gmp.jl:490; base/rational.jl:4-15; base/number.jl:434-452",
    status := .proven, prop := ``Models2Group2.BigRationalTypeRange, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.bigRationalTypeRange_proven,
    notes := "Reuses bigRationalType with the concrete Rational JType constructor and reifyBigIntType. No arbitrary constructor callback survives in the model; wrong component types and wrong type shapes falsify the contract." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- A raw-record preservation invariant. The scalar fields, entire limb
snapshot, and every observation of the represented object are unchanged.
No GMP Valid premise is appropriate: the identity methods do not read or
normalize the stored representation. This relation does not call any model. -/
def RawBigIntObservations (input result : JuliaLean.base.gmp.BigInt) : Prop :=
  result.val = input.val ∧ result.alloc = input.alloc ∧
  result.size = input.size ∧ result.d = input.d ∧
  ∀ (Observation : Type) (observe : JuliaLean.base.gmp.BigInt → Observation),
    observe result = observe input

/-- A concrete conversion terminates without an error, preserves every
represented object observation, and leaves the complete mutable world intact.
The contract observes a result rather than prescribing a forwarding expression
or assuming a law about any conversion callee. -/
def BigIntIdentityEffect {World : Type}
    (input : JuliaLean.base.gmp.BigInt) (before : World)
    (action : JuliaLean.base.io.M World JuliaLean.base.gmp.BigInt) : Prop :=
  match action before with
  | some (.ok (result, after)) => RawBigIntObservations input result ∧ after = before
  | some (.error _) | none => False

/-- signed on an existing BigInt preserves the full raw representation and
every represented observation. It performs no allocation or normalization.
Julia source: base/gmp.jl:302. -/
def SignedBigIntRawIdentity : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    RawBigIntObservations input (JuliaLean.base.gmp.signed input)

open JuliaLean JuliaLean.base.gmp Round1

theorem signedBigIntRawIdentity_proven : SignedBigIntRawIdentity := by
  intro input
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- The BigInt identity constructor preserves every raw field and observation,
including inconsistent stored fields; it does not rebuild the numerical value.
Julia source: base/gmp.jl:304. -/
def BigIntConstructorRawIdentity : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    RawBigIntObservations input (JuliaLean.base.gmp.fromBigInt input)

open JuliaLean JuliaLean.base.gmp Round1

theorem bigIntConstructorRawIdentity_proven : BigIntConstructorRawIdentity := by
  intro input
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Signed on an existing BigInt preserves every raw field and observation,
without copying through a numerical conversion or validating limb storage.
Julia source: base/gmp.jl:305. -/
def SignedConstructorRawIdentity : Prop :=
  ∀ input : JuliaLean.base.gmp.BigInt,
    RawBigIntObservations input (JuliaLean.base.gmp.signedBigInt input)

open JuliaLean JuliaLean.base.gmp Round1

theorem signedConstructorRawIdentity_proven : SignedConstructorRawIdentity := by
  intro input
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Over the complete concrete Base BigInt instantiation, BigInt-target rem
returns the existing raw object without changing any represented observation
or any part of the mutable world, and cannot throw or diverge. The dispatch
instance invokes the installed BigInt identity constructor; no callback law
is assumed. The generic model retains arbitrary Integer-subtype dispatch.
Julia source: base/gmp.jl:380; concrete callee base/gmp.jl:304. -/
def RemBigIntConcreteIdentity : Prop :=
  ∀ (World : Type) (before : World) (input : JuliaLean.base.gmp.BigInt),
    BigIntIdentityEffect input before
      (JuliaLean.base.gmp.Models2Group2.remBigIntDispatch
        (JuliaLean.base.gmp.Models2Group2.bigIntIdentityDispatch World) input)

open JuliaLean JuliaLean.base.gmp Round1

theorem remBigIntConcreteIdentity_proven : RemBigIntConcreteIdentity := by
  intro World before input
  exact ⟨⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, rfl⟩

/-- Over every concrete Base BigInt input, clamp to BigInt terminates without
errors, preserves all raw fields and observations, and leaves the full world
unchanged. The installed same-type numeric conversion is used. No Valid or
callee-correctness premise narrows the identity branch. The generic model also
preserves custom, nonnumeric input conversion and arbitrary effects.
Julia source: base/gmp.jl:382; concrete callee base/number.jl:6. -/
def ClampBigIntConcreteIdentity : Prop :=
  ∀ (World : Type) (before : World) (input : JuliaLean.base.gmp.BigInt),
    BigIntIdentityEffect input before
      (JuliaLean.base.gmp.Models2Group2.clampBigIntDispatch
        (JuliaLean.base.gmp.Models2Group2.bigIntIdentityDispatch World) input)

open JuliaLean JuliaLean.base.gmp Round1

theorem clampBigIntConcreteIdentity_proven : ClampBigIntConcreteIdentity := by
  intro World before input
  exact ⟨⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, rfl⟩

/-- big on an existing BigInt preserves every represented observation and the
entire world, with no errors or divergence. Its concrete conversion uses the
installed same-type numeric identity. The generic Integer method keeps open
convert dispatch and does not force the fallback BigInt(Integer) constructor.
Julia source: base/gmp.jl:492; concrete callee base/number.jl:6. -/
def BigIntegerConcreteIdentity : Prop :=
  ∀ (World : Type) (before : World) (input : JuliaLean.base.gmp.BigInt),
    BigIntIdentityEffect input before
      (JuliaLean.base.gmp.Models2Group2.bigIntegerDispatch
        (JuliaLean.base.gmp.Models2Group2.bigIntIdentityDispatch World) input)

open JuliaLean JuliaLean.base.gmp Round1

theorem bigIntegerConcreteIdentity_proven : BigIntegerConcreteIdentity := by
  intro World before input
  exact ⟨⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, rfl⟩

end Models2Group2

def entriesModels2Group2Dispatch : List Entry := [
  { id := "gmp-signed-bigint-raw-identity", juliaFile := "base/gmp.jl",
    juliaFns := ["signed(x::BigInt)"],
    statement := "signed preserves every raw BigInt field and every represented observation, including inconsistent stored representations; no reconstruction or normalization occurs.",
    source := "base/gmp.jl:302 (identity and raw-field preservation invariant)",
    status := .proven, prop := ``Models2Group2.SignedBigIntRawIdentity, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.signedBigIntRawIdentity_proven,
    notes := "Reuses JuliaLean.base.gmp.signed. No representation-validity premise is needed for an identity body." },
  { id := "gmp-bigint-constructor-raw-identity", juliaFile := "base/gmp.jl",
    juliaFns := ["BigInt(x::BigInt)"],
    statement := "The BigInt identity constructor preserves all raw fields and every represented observation without numerically reconstructing the input.",
    source := "base/gmp.jl:304 (identity and raw-field preservation invariant)",
    status := .proven, prop := ``Models2Group2.BigIntConstructorRawIdentity, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.bigIntConstructorRawIdentity_proven,
    notes := "Reuses JuliaLean.base.gmp.fromBigInt over its entire input-record domain." },
  { id := "gmp-signed-constructor-raw-identity", juliaFile := "base/gmp.jl",
    juliaFns := ["Signed(x::BigInt)"],
    statement := "The Signed identity constructor preserves all raw BigInt fields and every represented observation without normalization or a validity check.",
    source := "base/gmp.jl:305 (identity and raw-field preservation invariant)",
    status := .proven, prop := ``Models2Group2.SignedConstructorRawIdentity, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.signedConstructorRawIdentity_proven,
    notes := "Reuses JuliaLean.base.gmp.signedBigInt; malformed stored-field combinations are included." },
  { id := "gmp-rem-bigint-concrete-identity", juliaFile := "base/gmp.jl",
    juliaFns := ["rem(x::Integer, ::Type{BigInt})"],
    statement := "For every concrete Base BigInt input and mutable world, BigInt-target rem terminates successfully, preserves all raw object observations, and leaves the entire world unchanged.",
    source := "base/gmp.jl:380,304 (concrete Base identity invariant)",
    status := .proven, prop := ``Models2Group2.RemBigIntConcreteIdentity, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.remBigIntConcreteIdentity_proven,
    notes := "Full generic forwarding model permits arbitrary effect/result types and dispatch-selected constructor methods. This property uses the allowed concrete Base instantiation, calling installed fromBigInt, with no callback correctness assumptions." },
  { id := "gmp-clamp-bigint-concrete-identity", juliaFile := "base/gmp.jl",
    juliaFns := ["clamp(x, ::Type{BigInt})"],
    statement := "For every concrete Base BigInt input and mutable world, clamp to BigInt succeeds without changing any raw object observation or any world state.",
    source := "base/gmp.jl:382; base/number.jl:6 (concrete Base identity invariant)",
    status := .proven, prop := ``Models2Group2.ClampBigIntConcreteIdentity, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.clampBigIntConcreteIdentity_proven,
    notes := "Generic untyped-input forwarding retains arbitrary custom effects, errors, divergence, and return type. The property instantiates the installed same-type numeric conversion rather than postulating a conversion law." },
  { id := "gmp-big-integer-concrete-identity", juliaFile := "base/gmp.jl",
    juliaFns := ["big(n::Integer)"],
    statement := "For every concrete Base BigInt input and mutable world, big succeeds and preserves all raw object observations and the entire world.",
    source := "base/gmp.jl:492; base/number.jl:6 (concrete Base identity invariant)",
    status := .proven, prop := ``Models2Group2.BigIntegerConcreteIdentity, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.bigIntegerConcreteIdentity_proven,
    notes := "Full generic model calls convert dispatch, separately from constructor dispatch; properties use the installed concrete Base identity with no correctness laws or representation restriction." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry

namespace Models2Group2

/-- Every signed native type in ClongMax and every one of its values receives
a normalized result, with zero exactly when the mathematical inputs are equal,
and the entire represented heap is unchanged. In particular, Int64's minimum
and maximum are included. The only premises are dispatch and actual BigInt
memory/constructibility invariants. The expectation uses equality and explicit
set membership; it does not restate the native size algorithm or call sign.

GMP's native result is narrowed to Cint before sign is applied. That narrowing
can reverse sign for an extreme limb count, so an unconditional mathematical
order contract would be false for the exact source-derived model. No Julia
runtime reproduction of that enormous-size case is asserted.
Julia source: base/gmp.jl:629; base/number.jl:212;
native GMP 6.3.0 mpz/cmp_si.c:35-69. -/
def CmpClongMaxNormalizedEqualityAndFrame : Prop :=
  ∀ (Rest : Type) (t : IntTy) (dispatch : JuliaLean.base.gmp.IsClongMax t)
    (heap : JuliaLean.base.gmp.Models2Group2.InitHeap Rest)
    (input : JuliaLean.base.gmp.Models2Group2.InitBigIntRef)
    (scalar : JInt t),
    heap.liveObjects input.address = true →
    JuliaLean.base.gmp.Valid (heap.objects input.address).value →
    (heap.objects input.address).value.d.length < (2 : Nat)^63 →
    ScalarCmpFirstLimbCoherent heap input →
    match JuliaLean.base.gmp.Models2Group2.cmpClongMaxHeap
        dispatch input scalar heap with
    | some (.ok (result, after)) =>
        (result.val = -1 ∨ result.val = 0 ∨ result.val = 1) ∧
        (result.val = 0 ↔ (heap.objects input.address).value.val = scalar.val) ∧
        after = heap
    | some (.error _) | none => False

end Models2Group2

def entriesModels2Group2PublicSignedCmp : List Entry := [
  { id := "gmp-cmp-clongmax-normalized-equality-frame",
    juliaFile := "base/gmp.jl", juliaFns := ["cmp(x::BigInt, y::ClongMax)"],
    statement := "For every valid constructible BigInt heap representation, every ClongMax signed native integer type, and every scalar of that type, cmp returns -1, 0, or 1, returns zero exactly for mathematical equality, and preserves the entire represented heap.",
    source := "base/gmp.jl:629; base/number.jl:212; base/essentials.jl:739,742; GMP 6.3.0 mpz/cmp_si.c:35-69",
    status := .todo, prop := ``Models2Group2.CmpClongMaxNormalizedEqualityAndFrame,
    thm := none,
    notes := "Missing proof: characterize cmpSiNative's Cint result as zero exactly for mathematical equality using ScalarCmpFirstLimbCoherent and Valid, prove signBitInteger normalizes all nonzero results, then lift through cmpSiDispatch/nativeClongConversion/cmpClongMaxHeap. Native narrowing can reverse order at extreme limb counts, so only normalized equality and frame are asserted; the statement is unchanged." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- Independent mathematical order contract. -/
def ComparisonOrder (result : Clong) (left right : Int) : Prop :=
  (result.val = -1 ↔ left < right) ∧
  (result.val = 0 ↔ left = right) ∧
  (result.val = 1 ↔ right < left)

/-- Full valid live reference domain; source aliases may identify the same object. -/
def ComparisonHeapDomain {Rest : Type} (heap : InitHeap Rest) (x y : InitBigIntRef) : Prop :=
  heap.liveObjects x.address = true ∧ heap.liveObjects y.address = true ∧
  Valid (heap.objects x.address).value ∧ Valid (heap.objects y.address).value ∧
  (heap.objects x.address).value.d.length < 2^63 ∧
  (heap.objects y.address).value.d.length < 2^63

/-- The permitted concrete Base reference instantiation obeys independent
mathematical order and preserves every part of the represented heap. Live,
normalized inputs have native-Int-representable storage, and may alias. No
conversion or comparison correctness law is assumed. The full generic model
retains arbitrary dispatch-selected result types, effects, and errors.
Julia source: base/gmp.jl:631; base/operators.jl:505-511
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def IntegerComparisonDispatchOrder : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (x y : InitBigIntRef),
    ComparisonHeapDomain heap x y →
    match cmpIntegerDispatch (bigIntIntegerComparisonOps Rest) x y heap with
    | some (.ok (result, after)) =>
      ComparisonOrder result (heap.objects x.address).value.val
        (heap.objects y.address).value.val ∧ after = heap
    | _ => False

/-- The concrete Base reverse instantiation preserves the original operand
order and the complete represented heap, for every normalized constructible
reference pair, including aliases. The expectation uses mathematical order
rather than the source negation or a law about a selected comparator.
Julia source: base/gmp.jl:632; base/operators.jl:505-511
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def ReverseComparisonDispatchOrder : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (x y : InitBigIntRef),
    ComparisonHeapDomain heap x y →
    match integerCmpDispatch (bigIntReverseComparisonOps Rest) x y heap with
    | some (.ok (result, after)) =>
      ComparisonOrder result (heap.objects x.address).value.val
        (heap.objects y.address).value.val ∧ after = heap
    | _ => False
end JuliaLean.Proofs.base.gmp.Models2Group2

namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

namespace Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2
open JuliaLean.Proofs.base.gmp.Round1
open JuliaLean.ChatGPT.Batch4.Group6 JuliaLean.ChatGPT.Batch4.Group7

theorem integerComparisonDispatchOrder_proven : IntegerComparisonDispatchOrder := by
  intro Rest heap x y hdom
  rcases hdom with ⟨hlx, hly, hvx, hvy, hlenx, hleny⟩
  simp only [cmpIntegerDispatch, bigIntIntegerComparisonOps, bigIntegerDispatch,
    bigIntIdentityDispatch, JuliaLean.base.number.convertSame, JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hlx, hly, ↓reduceIte]
  have hcmp := cc_comparison_of_sgn
    (heap.objects x.address).value.val (heap.objects y.address).value.val
    (JuliaLean.base.gmp.cmp (heap.objects x.address).value
      (heap.objects y.address).value) (cl_cmp_val _ _)
  exact ⟨hcmp.2, rfl⟩

theorem reverseComparisonDispatchOrder_proven : ReverseComparisonDispatchOrder := by
  intro Rest heap x y hdom
  rcases hdom with ⟨hlx, hly, hvx, hvy, hlenx, hleny⟩
  simp only [integerCmpDispatch, bigIntReverseComparisonOps, cmpIntegerDispatch,
    bigIntIntegerComparisonOps, bigIntegerDispatch, bigIntIdentityDispatch,
    JuliaLean.base.number.convertSame, JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hlx, hly, ↓reduceIte]
  let a := (heap.objects x.address).value
  let b := (heap.objects y.address).value
  have hcmp : (-(JuliaLean.base.gmp.cmp b a)).val = sgn (a.val - b.val) := by
    change wrapInt .i64 (-(JuliaLean.base.gmp.cmp b a).val) = sgn (a.val - b.val)
    rw [cl_cmp_val b a]
    have hneg : -sgn (b.val - a.val) = sgn (a.val - b.val) := by
      unfold sgn
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    rw [hneg]
    exact cl_wrap_sgn _
  exact ⟨(cc_comparison_of_sgn a.val b.val _ hcmp).2, rfl⟩

end Models2Group2

def entriesModels2Group2GenericComparison : List Entry := [
  { id := "gmp-integer-comparison-dispatch-order",
    juliaFile := "base/gmp.jl", juliaFns := ["cmp(x::BigInt, y::Integer)"],
    statement := "The complete generic Integer comparison fallback, instantiated with concrete Base BigInt operations, gives exactly the mathematical order of all valid constructible inputs and preserves the complete world.",
    source := "base/gmp.jl:631; base/operators.jl:505-511; helper dependencies: IntegerComparisonOps, cmpIntegerDispatch, bigIntIntegerComparisonOps, bigIntegerDispatch, installed cmp/MPZ.cmp and base.number.convertSame; no callee laws",
    status := .proven, prop := ``Models2Group2.IntegerComparisonDispatchOrder, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.integerComparisonDispatchOrder_proven },
  { id := "gmp-reverse-comparison-dispatch-order",
    juliaFile := "base/gmp.jl", juliaFns := ["cmp(x::Integer, y::BigInt)"],
    statement := "The complete reverse generic comparison, instantiated with concrete Base BigInt comparison and native negation, gives the mathematical order of the original operands and preserves the complete world.",
    source := "base/gmp.jl:632; base/operators.jl:505-511; helper dependencies: ReverseComparisonOps, integerCmpDispatch, bigIntReverseComparisonOps, installed cmp/MPZ.cmp and JInt.neg; no callee laws",
    status := .proven, prop := ``Models2Group2.ReverseComparisonDispatchOrder, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.reverseComparisonDispatchOrder_proven }
]
end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry JuliaLean.base.float
open JuliaLean.Promotion hiding FTy FV FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

namespace Models2Group2

/-- For every valid constructible BigInt and every Float16/32/64 bit pattern,
the public comparison succeeds with -1/0/1. Every NaN sorts above the BigInt;
the two infinities have their expected orders; finite values are compared by
their exact mathematical rational value, including equality of both signed
zeros with integer zero. The finite expectation uses the original source
format, independently of the model's Cdouble widening and native comparator.
This invariant intentionally does not assert the false documented total-order
distinction between negative floating zero and integer zero.
Julia source: base/gmp.jl:634; native GMP 6.3.0 mpz/cmp_d.c:59-147. -/
def CmpFloatClassification : Prop :=
  ∀ (T : FTy) (input : JuliaLean.base.gmp.BigInt) (scalar : FV T),
    JuliaLean.base.gmp.Valid input → input.d.length < (2 : Nat)^63 →
    match JuliaLean.base.gmp.Models2Group2.cmpFloatExact input scalar with
    | .ok result =>
        (result.val = -1 ∨ result.val = 0 ∨ result.val = 1) ∧
        (scalar.isnan = true → result.val = -1) ∧
        (scalar.isinf = true →
          (scalar.signbit = true → result.val = 1) ∧
          (scalar.signbit = false → result.val = -1)) ∧
        (scalar.isfinite = true →
          let (numerator, denominator) := scalar.toRat
          (result.val = -1 ↔ input.val * (denominator : Int) < numerator) ∧
          (result.val = 0 ↔ input.val * (denominator : Int) = numerator) ∧
          (result.val = 1 ↔ numerator < input.val * (denominator : Int)))
    | .error _ => False

/-- The reversed public comparison has exact finite rational order, orders
NaNs above every BigInt, and handles both infinities and both floating zeros.
Its expectation is stated directly for the reversed mathematical operands,
without calling the forward comparison or assuming an antisymmetry law.
Julia source: base/gmp.jl:635; native GMP 6.3.0 mpz/cmp_d.c:59-147. -/
def FloatCmpClassification : Prop :=
  ∀ (T : FTy) (input : JuliaLean.base.gmp.BigInt) (scalar : FV T),
    JuliaLean.base.gmp.Valid input → input.d.length < (2 : Nat)^63 →
    match JuliaLean.base.gmp.Models2Group2.floatCmpExact scalar input with
    | .ok result =>
        (result.val = -1 ∨ result.val = 0 ∨ result.val = 1) ∧
        (scalar.isnan = true → result.val = 1) ∧
        (scalar.isinf = true →
          (scalar.signbit = true → result.val = -1) ∧
          (scalar.signbit = false → result.val = 1)) ∧
        (scalar.isfinite = true →
          let (numerator, denominator) := scalar.toRat
          (result.val = -1 ↔ numerator < input.val * (denominator : Int)) ∧
          (result.val = 0 ↔ numerator = input.val * (denominator : Int)) ∧
          (result.val = 1 ↔ input.val * (denominator : Int) < numerator))
    | .error _ => False

end Models2Group2

def entriesModels2Group2PublicFloatCmp : List Entry := [
  { id := "gmp-cmp-float-classification", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp(x::BigInt, y::CdoubleMax)"],
    statement := "For every valid constructible BigInt and every Float16/32/64 bit pattern, cmp succeeds with -1, 0, or 1; finite inputs use exact rational order including both zeros, infinities have their mathematical orders, and every NaN returns -1.",
    source := "base/gmp.jl:634; base/float.jl:345-347; base/number.jl:212; GMP 6.3.0 mpz/cmp_d.c:59-147",
    status := .todo, prop := ``Models2Group2.CmpFloatClassification, thm := none,
    notes := "Missing proof: cmpDNonNaN's widened Float16/32/64 rational comparison must agree with the original scalar.toRat, including zero's raw Cint size result and both infinities; signBitInteger must normalize it. Existing pnf_convertFloat_eq gives converter identity, not the required all-format rational-order transport. NaN guards and the existing signed-zero total-order refutation remain unchanged." },
  { id := "gmp-float-cmp-classification", juliaFile := "base/gmp.jl",
    juliaFns := ["cmp(x::CdoubleMax, y::BigInt)"],
    statement := "For every valid constructible BigInt and every Float16/32/64 bit pattern, reversed cmp succeeds with -1, 0, or 1 according to exact finite rational order and infinity order, and every NaN returns 1; both floating zeros compare equal to integer zero.",
    source := "base/gmp.jl:635; base/gmp.jl:634; GMP 6.3.0 mpz/cmp_d.c:59-147",
    status := .todo, prop := ``Models2Group2.FloatCmpClassification, thm := none,
    notes := "Missing proof: establish CmpFloatClassification, then transport its exact normalized -1/0/1 result through floatCmpExact's native Int negation to reversed rational inequalities, NaN=1 and both signed zeros. No antisymmetry assumption or change to the existing reverse total-order refutation is permitted." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2

open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2
open JuliaLean.base.float

/-- Success with the independent numerical condition and complete heap
preservation. This is not a correctness law assumed of a selected callee. -/
def PredicateHeapResult {Rest : Type}
    (action : JuliaLean.base.io.M (InitHeap Rest) Bool)
    (before : InitHeap Rest) (condition : Prop) : Prop :=
  match action before with
  | some (.ok (result, after)) => (result = true ↔ condition) ∧ after = before
  | _ => False

/-- The concrete Base instance of the complete generic relation agrees
with mathematical integer order on every valid constructible live reference
pair, including aliases, and preserves the whole represented heap. Generic
input, comparison and result types remain unrestricted in the source model;
this permitted concrete instantiation assumes no selected-callee laws.
Julia source: base/gmp.jl:731; docs: base/operators.jl:109-126;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def EqualIntegerDispatchOrderAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (left right : InitBigIntRef),
    ComparisonHeapDomain heap left right →
    PredicateHeapResult
      (equalIntegerDispatch (nativeIntegerRelationOps .equal Rest) left right)
      heap ((heap.objects left.address).value.val = (heap.objects right.address).value.val)

/-- The concrete Base instance of the complete generic relation agrees
with mathematical integer order on every valid constructible live reference
pair, including aliases, and preserves the whole represented heap. Generic
input, comparison and result types remain unrestricted in the source model;
this permitted concrete instantiation assumes no selected-callee laws.
Julia source: base/gmp.jl:732; docs: base/operators.jl:109-126;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def IntegerEqualDispatchOrderAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (left right : InitBigIntRef),
    ComparisonHeapDomain heap left right →
    PredicateHeapResult
      (integerEqualDispatch (nativeIntegerRelationOps .equal Rest) left right)
      heap ((heap.objects left.address).value.val = (heap.objects right.address).value.val)

/-- The concrete Base instance of the complete generic relation agrees
with mathematical integer order on every valid constructible live reference
pair, including aliases, and preserves the whole represented heap. Generic
input, comparison and result types remain unrestricted in the source model;
this permitted concrete instantiation assumes no selected-callee laws.
Julia source: base/gmp.jl:739; docs: base/operators.jl:109-126;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def LessEqualIntegerDispatchOrderAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (left right : InitBigIntRef),
    ComparisonHeapDomain heap left right →
    PredicateHeapResult
      (lessEqualIntegerDispatch (nativeIntegerRelationOps .lessEqual Rest) left right)
      heap ((heap.objects left.address).value.val ≤ (heap.objects right.address).value.val)

/-- The concrete Base instance of the complete generic relation agrees
with mathematical integer order on every valid constructible live reference
pair, including aliases, and preserves the whole represented heap. Generic
input, comparison and result types remain unrestricted in the source model;
this permitted concrete instantiation assumes no selected-callee laws.
Julia source: base/gmp.jl:740; docs: base/operators.jl:109-126;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def IntegerLessEqualDispatchOrderAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (left right : InitBigIntRef),
    ComparisonHeapDomain heap left right →
    PredicateHeapResult
      (integerLessEqualDispatch (nativeIntegerRelationOps .greaterEqual Rest) left right)
      heap ((heap.objects left.address).value.val ≤ (heap.objects right.address).value.val)

/-- The concrete Base instance of the complete generic relation agrees
with mathematical integer order on every valid constructible live reference
pair, including aliases, and preserves the whole represented heap. Generic
input, comparison and result types remain unrestricted in the source model;
this permitted concrete instantiation assumes no selected-callee laws.
Julia source: base/gmp.jl:745; docs: base/operators.jl:109-126;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def LessIntegerDispatchOrderAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (left right : InitBigIntRef),
    ComparisonHeapDomain heap left right →
    PredicateHeapResult
      (lessIntegerDispatch (nativeIntegerRelationOps .less Rest) left right)
      heap ((heap.objects left.address).value.val < (heap.objects right.address).value.val)

/-- The concrete Base instance of the complete generic relation agrees
with mathematical integer order on every valid constructible live reference
pair, including aliases, and preserves the whole represented heap. Generic
input, comparison and result types remain unrestricted in the source model;
this permitted concrete instantiation assumes no selected-callee laws.
Julia source: base/gmp.jl:746; docs: base/operators.jl:109-126;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def IntegerLessDispatchOrderAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (left right : InitBigIntRef),
    ComparisonHeapDomain heap left right →
    PredicateHeapResult
      (integerLessDispatch (nativeIntegerRelationOps .greater Rest) left right)
      heap ((heap.objects left.address).value.val < (heap.objects right.address).value.val)

/-- Successful Bool characterized by an independent mathematical condition. -/
def PredicateBoolResult (action : Jl Bool) (condition : Prop) : Prop :=
  ∃ result : Bool, action = .ok result ∧ (result = true ↔ condition)

/-- Interpret the input IEEE value as a rational only when finite; infinities
and NaNs cannot equal an integer. No comparison implementation occurs here. -/
def PredicateFloatEquality {T : FTy} (integer : Int) (scalar : FV T) : Prop :=
  scalar.isfinite = true ∧ scalar.toRat.1 = integer * (scalar.toRat.2 : Int)

def PredicateIntLEFloat {T : FTy} (integer : Int) (scalar : FV T) : Prop :=
  (scalar.isinf = true ∧ scalar.signbit = false) ∨
  (scalar.isfinite = true ∧ integer * (scalar.toRat.2 : Int) ≤ scalar.toRat.1)

def PredicateFloatLEInt {T : FTy} (scalar : FV T) (integer : Int) : Prop :=
  (scalar.isinf = true ∧ scalar.signbit = true) ∨
  (scalar.isfinite = true ∧ scalar.toRat.1 ≤ integer * (scalar.toRat.2 : Int))

def PredicateIntLTFloat {T : FTy} (integer : Int) (scalar : FV T) : Prop :=
  (scalar.isinf = true ∧ scalar.signbit = false) ∨
  (scalar.isfinite = true ∧ integer * (scalar.toRat.2 : Int) < scalar.toRat.1)

def PredicateFloatLTInt {T : FTy} (scalar : FV T) (integer : Int) : Prop :=
  (scalar.isinf = true ∧ scalar.signbit = true) ∨
  (scalar.isfinite = true ∧ scalar.toRat.1 < integer * (scalar.toRat.2 : Int))

/-- Both equality directions compare exact mathematical values, identify
both floating zero signs with integer zero, and return false for every NaN
sign/payload or infinity. Every valid constructible BigInt and every bit
pattern in Float16/32/64 is included, and success is part of the contract.
Julia source: base/gmp.jl:733-734; docs: base/operators.jl:109-126;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FloatPredicatesEquality : Prop :=
  ∀ (T : FTy) (input : BigInt) (scalar : FV T),
    Valid input → input.d.length < (2 : Nat)^63 →
    PredicateBoolResult (equalFloatExact input scalar)
      (PredicateFloatEquality input.val scalar) ∧
    PredicateBoolResult (floatEqualExact scalar input)
      (PredicateFloatEquality input.val scalar)

/-- Both source operand orders of < and <= give exact finite rational order,
place infinities at the ends, and leave every NaN unordered. Every bit pattern
in Float16/32/64 is quantified, including subnormals and either floating zero;
no assumption about cmp or a conversion implementation is required.
Julia source: base/gmp.jl:741-742,747-748;
doc/src/manual/mathematical-operations.md:229-286
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def FloatPredicatesOrder : Prop :=
  ∀ (T : FTy) (input : BigInt) (scalar : FV T),
    Valid input → input.d.length < (2 : Nat)^63 →
    PredicateBoolResult (lessEqualFloatExact input scalar)
      (PredicateIntLEFloat input.val scalar) ∧
    PredicateBoolResult (floatLessEqualExact scalar input)
      (PredicateFloatLEInt scalar input.val) ∧
    PredicateBoolResult (lessFloatExact input scalar)
      (PredicateIntLTFloat input.val scalar) ∧
    PredicateBoolResult (floatLessExact scalar input)
      (PredicateFloatLTInt scalar input.val)

end JuliaLean.Proofs.base.gmp.Models2Group2

namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

namespace Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2
open JuliaLean.ChatGPT.Batch4.Group7

private theorem cmp_eq_wrap_sgn (a b : BigInt) :
    JuliaLean.base.gmp.cmp a b = JInt.wrap .i64 (sgn (a.val - b.val)) :=
  Subtype.ext ((cl_cmp_val a b).trans (cl_wrap_sgn (a.val - b.val)).symm)

private theorem sgn_int_cases (a b : BigInt) :
    (a.val < b.val ∧ JuliaLean.base.gmp.cmp a b = JInt.wrap .i64 (-1)) ∨
    (a.val = b.val ∧ JuliaLean.base.gmp.cmp a b = JInt.wrap .i64 0) ∨
    (b.val < a.val ∧ JuliaLean.base.gmp.cmp a b = JInt.wrap .i64 1) := by
  rw [cmp_eq_wrap_sgn]
  rcases Int.lt_trichotomy a.val b.val with h | h | h
  · left
    exact ⟨h, by simp only [sgn, if_pos (show a.val - b.val < 0 by omega)]⟩
  · right; left
    exact ⟨h, by simp only [h, Int.sub_self, sgn, Int.lt_irrefl, ite_false]⟩
  · right; right
    exact ⟨h, by simp only [sgn, if_neg (show ¬ a.val - b.val < 0 by omega),
      if_pos (show 0 < a.val - b.val by omega)]⟩

theorem equalIntegerDispatchOrderAndFrame_proven : EqualIntegerDispatchOrderAndFrame := by
  intro Rest heap left right hdom
  rcases hdom with ⟨hll, hlr, hvl, hvr, hlenl, hlenr⟩
  simp only [PredicateHeapResult, equalIntegerDispatch,
    nativeIntegerRelationOps, cmpIntegerDispatch, bigIntIntegerComparisonOps,
    bigIntegerDispatch, bigIntIdentityDispatch, JuliaLean.base.number.convertSame,
    JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hll, hlr, ↓reduceIte]
  refine ⟨?_, rfl⟩
  rcases sgn_int_cases (heap.objects left.address).value (heap.objects right.address).value with ⟨h, hcmp⟩ | ⟨h, hcmp⟩ | ⟨h, hcmp⟩
  · rw [hcmp]; simp [show JuliaLean.base.int.eqSame (JInt.wrap .i64 (-1)) (JInt.wrap .i64 0) = false by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.eqSame (JInt.wrap .i64 0) (JInt.wrap .i64 0) = true by decide, h]
  · rw [hcmp]; simp [show JuliaLean.base.int.eqSame (JInt.wrap .i64 1) (JInt.wrap .i64 0) = false by decide]; omega

theorem integerEqualDispatchOrderAndFrame_proven : IntegerEqualDispatchOrderAndFrame := by
  intro Rest heap left right hdom
  rcases hdom with ⟨hll, hlr, hvl, hvr, hlenl, hlenr⟩
  simp only [PredicateHeapResult, integerEqualDispatch,
    nativeIntegerRelationOps, cmpIntegerDispatch, bigIntIntegerComparisonOps,
    bigIntegerDispatch, bigIntIdentityDispatch, JuliaLean.base.number.convertSame,
    JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hll, hlr, ↓reduceIte]
  refine ⟨?_, rfl⟩
  rcases sgn_int_cases (heap.objects right.address).value (heap.objects left.address).value with ⟨h, hcmp⟩ | ⟨h, hcmp⟩ | ⟨h, hcmp⟩
  · rw [hcmp]; simp [show JuliaLean.base.int.eqSame (JInt.wrap .i64 (-1)) (JInt.wrap .i64 0) = false by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.eqSame (JInt.wrap .i64 0) (JInt.wrap .i64 0) = true by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.eqSame (JInt.wrap .i64 1) (JInt.wrap .i64 0) = false by decide]; omega

theorem lessEqualIntegerDispatchOrderAndFrame_proven : LessEqualIntegerDispatchOrderAndFrame := by
  intro Rest heap left right hdom
  rcases hdom with ⟨hll, hlr, hvl, hvr, hlenl, hlenr⟩
  simp only [PredicateHeapResult, lessEqualIntegerDispatch,
    nativeIntegerRelationOps, cmpIntegerDispatch, bigIntIntegerComparisonOps,
    bigIntegerDispatch, bigIntIdentityDispatch, JuliaLean.base.number.convertSame,
    JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hll, hlr, ↓reduceIte]
  refine ⟨?_, rfl⟩
  rcases sgn_int_cases (heap.objects left.address).value (heap.objects right.address).value with ⟨h, hcmp⟩ | ⟨h, hcmp⟩ | ⟨h, hcmp⟩
  · rw [hcmp]; simp [show JuliaLean.base.int.le_BitSigned (JInt.wrap .i64 (-1)) (JInt.wrap .i64 0) = true by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.le_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 0) = true by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.le_BitSigned (JInt.wrap .i64 1) (JInt.wrap .i64 0) = false by decide]; omega

theorem integerLessEqualDispatchOrderAndFrame_proven : IntegerLessEqualDispatchOrderAndFrame := by
  intro Rest heap left right hdom
  rcases hdom with ⟨hll, hlr, hvl, hvr, hlenl, hlenr⟩
  simp only [PredicateHeapResult, integerLessEqualDispatch,
    nativeIntegerRelationOps, cmpIntegerDispatch, bigIntIntegerComparisonOps,
    bigIntegerDispatch, bigIntIdentityDispatch, JuliaLean.base.number.convertSame,
    JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hll, hlr, ↓reduceIte]
  refine ⟨?_, rfl⟩
  rcases sgn_int_cases (heap.objects right.address).value (heap.objects left.address).value with ⟨h, hcmp⟩ | ⟨h, hcmp⟩ | ⟨h, hcmp⟩
  · rw [hcmp]; simp [show JuliaLean.base.int.le_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 (-1)) = false by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.le_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 0) = true by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.le_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 1) = true by decide]; omega

theorem lessIntegerDispatchOrderAndFrame_proven : LessIntegerDispatchOrderAndFrame := by
  intro Rest heap left right hdom
  rcases hdom with ⟨hll, hlr, hvl, hvr, hlenl, hlenr⟩
  simp only [PredicateHeapResult, lessIntegerDispatch,
    nativeIntegerRelationOps, cmpIntegerDispatch, bigIntIntegerComparisonOps,
    bigIntegerDispatch, bigIntIdentityDispatch, JuliaLean.base.number.convertSame,
    JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hll, hlr, ↓reduceIte]
  refine ⟨?_, rfl⟩
  rcases sgn_int_cases (heap.objects left.address).value (heap.objects right.address).value with ⟨h, hcmp⟩ | ⟨h, hcmp⟩ | ⟨h, hcmp⟩
  · rw [hcmp]; simp [show JuliaLean.base.int.lt_BitSigned (JInt.wrap .i64 (-1)) (JInt.wrap .i64 0) = true by decide, h]
  · rw [hcmp]; simp [show JuliaLean.base.int.lt_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 0) = false by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.lt_BitSigned (JInt.wrap .i64 1) (JInt.wrap .i64 0) = false by decide]; omega

theorem integerLessDispatchOrderAndFrame_proven : IntegerLessDispatchOrderAndFrame := by
  intro Rest heap left right hdom
  rcases hdom with ⟨hll, hlr, hvl, hvr, hlenl, hlenr⟩
  simp only [PredicateHeapResult, integerLessDispatch,
    nativeIntegerRelationOps, cmpIntegerDispatch, bigIntIntegerComparisonOps,
    bigIntegerDispatch, bigIntIdentityDispatch, JuliaLean.base.number.convertSame,
    JuliaLean.base.io.liftJl,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hll, hlr, ↓reduceIte]
  refine ⟨?_, rfl⟩
  rcases sgn_int_cases (heap.objects right.address).value (heap.objects left.address).value with ⟨h, hcmp⟩ | ⟨h, hcmp⟩ | ⟨h, hcmp⟩
  · rw [hcmp]; simp [show JuliaLean.base.int.lt_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 (-1)) = false by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.lt_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 0) = false by decide]; omega
  · rw [hcmp]; simp [show JuliaLean.base.int.lt_BitSigned (JInt.wrap .i64 0) (JInt.wrap .i64 1) = true by decide, h]

end Models2Group2

def entriesModels2Group2Predicates : List Entry := [
  { id := "gmp-equal-integer-dispatch", juliaFile := "base/gmp.jl",
    juliaFns := ["==(x::BigInt, i::Integer)"],
    statement := "The complete open Integer relation, instantiated with concrete Base BigInt operations, agrees with mathematical = for every valid constructible live reference pair, including aliases, and preserves the complete heap.",
    source := "base/gmp.jl:731; base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286",
    status := .proven, prop := ``Models2Group2.EqualIntegerDispatchOrderAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.equalIntegerDispatchOrderAndFrame_proven,
    notes := "equalIntegerDispatch preserves both selected calls and their effects/errors, exact native zero argument, unrestricted comparison/result types, and no Bool assertion. Concrete nativeIntegerRelationOps reuses installed BigInt cmp and JInt relations. This property covers IntegerRelationTag/Ops and nativeIntegerRelationOps without callee assumptions." },
  { id := "gmp-integer-equal-dispatch", juliaFile := "base/gmp.jl",
    juliaFns := ["==(i::Integer, x::BigInt)"],
    statement := "The complete open Integer relation, instantiated with concrete Base BigInt operations, agrees with mathematical = for every valid constructible live reference pair, including aliases, and preserves the complete heap.",
    source := "base/gmp.jl:732; base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286",
    status := .proven, prop := ``Models2Group2.IntegerEqualDispatchOrderAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.integerEqualDispatchOrderAndFrame_proven,
    notes := "integerEqualDispatch preserves both selected calls and their effects/errors, exact native zero argument, unrestricted comparison/result types, and no Bool assertion. Concrete nativeIntegerRelationOps reuses installed BigInt cmp and JInt relations. This property covers IntegerRelationTag/Ops and nativeIntegerRelationOps without callee assumptions." },
  { id := "gmp-le-integer-dispatch", juliaFile := "base/gmp.jl",
    juliaFns := ["<=(x::BigInt, i::Integer)"],
    statement := "The complete open Integer relation, instantiated with concrete Base BigInt operations, agrees with mathematical ≤ for every valid constructible live reference pair, including aliases, and preserves the complete heap.",
    source := "base/gmp.jl:739; base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286",
    status := .proven, prop := ``Models2Group2.LessEqualIntegerDispatchOrderAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.lessEqualIntegerDispatchOrderAndFrame_proven,
    notes := "lessEqualIntegerDispatch preserves both selected calls and their effects/errors, exact native zero argument, unrestricted comparison/result types, and no Bool assertion. Concrete nativeIntegerRelationOps reuses installed BigInt cmp and JInt relations. This property covers IntegerRelationTag/Ops and nativeIntegerRelationOps without callee assumptions." },
  { id := "gmp-integer-le-dispatch", juliaFile := "base/gmp.jl",
    juliaFns := ["<=(i::Integer, x::BigInt)"],
    statement := "The complete open Integer relation, instantiated with concrete Base BigInt operations, agrees with mathematical ≤ for every valid constructible live reference pair, including aliases, and preserves the complete heap.",
    source := "base/gmp.jl:740; base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286",
    status := .proven, prop := ``Models2Group2.IntegerLessEqualDispatchOrderAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.integerLessEqualDispatchOrderAndFrame_proven,
    notes := "integerLessEqualDispatch preserves both selected calls and their effects/errors, exact native zero argument, unrestricted comparison/result types, and no Bool assertion. Concrete nativeIntegerRelationOps reuses installed BigInt cmp and JInt relations. This property covers IntegerRelationTag/Ops and nativeIntegerRelationOps without callee assumptions." },
  { id := "gmp-lt-integer-dispatch", juliaFile := "base/gmp.jl",
    juliaFns := ["<(x::BigInt, i::Integer)"],
    statement := "The complete open Integer relation, instantiated with concrete Base BigInt operations, agrees with mathematical < for every valid constructible live reference pair, including aliases, and preserves the complete heap.",
    source := "base/gmp.jl:745; base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286",
    status := .proven, prop := ``Models2Group2.LessIntegerDispatchOrderAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.lessIntegerDispatchOrderAndFrame_proven,
    notes := "lessIntegerDispatch preserves both selected calls and their effects/errors, exact native zero argument, unrestricted comparison/result types, and no Bool assertion. Concrete nativeIntegerRelationOps reuses installed BigInt cmp and JInt relations. This property covers IntegerRelationTag/Ops and nativeIntegerRelationOps without callee assumptions." },
  { id := "gmp-integer-lt-dispatch", juliaFile := "base/gmp.jl",
    juliaFns := ["<(i::Integer, x::BigInt)"],
    statement := "The complete open Integer relation, instantiated with concrete Base BigInt operations, agrees with mathematical < for every valid constructible live reference pair, including aliases, and preserves the complete heap.",
    source := "base/gmp.jl:746; base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286",
    status := .proven, prop := ``Models2Group2.IntegerLessDispatchOrderAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.integerLessDispatchOrderAndFrame_proven,
    notes := "integerLessDispatch preserves both selected calls and their effects/errors, exact native zero argument, unrestricted comparison/result types, and no Bool assertion. Concrete nativeIntegerRelationOps reuses installed BigInt cmp and JInt relations. This property covers IntegerRelationTag/Ops and nativeIntegerRelationOps without callee assumptions." },
  { id := "gmp-float-predicates-equality", juliaFile := "base/gmp.jl",
    juliaFns := ["==(x::BigInt, f::CdoubleMax)", "==(f::CdoubleMax, x::BigInt)"],
    statement := "Both BigInt/IEEE equality directions succeed exactly for equal mathematical values, identify either floating zero with integer zero, and reject every NaN or infinity over all Float16/32/64 bit patterns.",
    source := "base/gmp.jl:733-734; base/operators.jl:109-126; doc/src/manual/mathematical-operations.md:229-286",
    status := .todo, prop := ``Models2Group2.FloatPredicatesEquality, thm := none,
    notes := "Missing proof: establish CmpFloatClassification's exact finite zero characterization and nonzero infinity results, then reduce both outer NaN guards and installed int.eqSame against native zero. Both equality directions share the same forward comparator; no correctness law for that comparator is assumed." },
  { id := "gmp-float-predicates-order", juliaFile := "base/gmp.jl",
    juliaFns := ["<=(x::BigInt, f::CdoubleMax)", "<=(f::CdoubleMax, x::BigInt)", "<(x::BigInt, f::CdoubleMax)", "<(f::CdoubleMax, x::BigInt)"],
    statement := "Both operand orders of BigInt/IEEE < and <= succeed with exact rational order, infinities at the ends, every NaN unordered, and signed-zero numerical equality over every Float16/32/64 bit pattern.",
    source := "base/gmp.jl:741-742,747-748; doc/src/manual/mathematical-operations.md:229-286",
    status := .todo, prop := ``Models2Group2.FloatPredicatesOrder, thm := none,
    notes := "Missing proof: establish CmpFloatClassification, then reduce all four installed native comparisons with zero to the independent rational inequalities, retaining reversed >/>= operands and outer NaN rejection. Both floating zeros require numerical equality, independently of the separately refuted total-order promise." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- An independent mutation invariant over the complete concrete Base instance:
mathematical sign multiplication, object identity, valid output, exact storage
preservation, and every unaffected object/state observation. References may
alias. Premises are source object-liveness and representation invariants. -/
def FlipsignIdentityValueAndFrame : Prop :=
  ∀ (Rest : Type) (heap : InitHeap Rest) (x y : InitBigIntRef),
    heap.liveObjects x.address = true → heap.liveObjects y.address = true →
    Valid (heap.objects x.address).value → Valid (heap.objects y.address).value →
    (heap.objects x.address).value.d.length < 2^63 →
    (heap.objects y.address).value.d.length < 2^63 →
    match flipsignBangDispatch (bigIntSignbitDispatch Rest) x y heap with
    | some (.ok (returned, after)) =>
      let before := (heap.objects x.address).value
      let result := (after.objects x.address).value
      returned = x ∧ Valid result ∧
      result.val = (if (heap.objects y.address).value.val < 0 then -before.val else before.val) ∧
      result.val.natAbs = before.val.natAbs ∧
      result.alloc = before.alloc ∧ result.d = before.d ∧
      (after.objects x.address).dataPointer = (heap.objects x.address).dataPointer ∧
      (∀ address, address ≠ x.address → after.objects address = heap.objects address) ∧
      after.liveObjects = heap.liveObjects ∧ after.limbs = heap.limbs ∧
      after.dummyPointer = heap.dummyPointer ∧ after.rest = heap.rest ∧
      ((heap.objects y.address).value.val ≥ 0 → after = heap)
    | _ => False

open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2
open JuliaLean.ChatGPT.Batch4.Group6

private theorem negSizeVal (x : BigInt) (hx : Valid x) : (-x.size).val = -x.size.val := by
  have ha := x.alloc.property
  have hs := x.size.property
  have hcap := hx.2.1
  change -2147483648 ≤ x.alloc.val ∧ x.alloc.val ≤ 2147483647 at ha
  change -2147483648 ≤ x.size.val ∧ x.size.val ≤ 2147483647 at hs
  change wrapInt .i32 (-x.size.val) = -x.size.val
  apply wrapInt_of_inRange
  constructor
  · change -2147483648 ≤ -x.size.val
    omega
  · change -x.size.val ≤ 2147483647
    omega
private theorem flipValue (x : BigInt) (hx : Valid x) :
    let size := -x.size
    let value := { x with size := size, val := if size.val < 0 then
      -(limbMagnitude (x.d.take size.val.natAbs) : Int) else
      (limbMagnitude (x.d.take size.val.natAbs) : Int) }
    Valid value ∧ value.val = -x.val := by
  have hn := negSizeVal x hx
  have hz := hx.2.2.2.1
  have hv := hx.2.2.1
  simp only [hn, Int.natAbs_neg]
  constructor
  · simp only [Valid, hn, Int.natAbs_neg]
    refine ⟨hx.1, hx.2.1, True.intro, ?_, ?_⟩
    · by_cases hs : x.size.val = 0
      · have hval := hz.mp hs
        simp only [hs, Int.natAbs_zero, List.take_zero, limbMagnitude, Int.natCast_zero,
          Int.neg_zero, Int.lt_irrefl, ↓reduceIte]
      · have hval : x.val ≠ 0 := fun h => hs (hz.mpr h)
        have hm : limbMagnitude (x.d.take x.size.val.natAbs) ≠ 0 := by
          intro h
          simp [h] at hv
          exact hval hv
        simp only [Int.neg_eq_zero, hs, false_iff]
        split <;> omega
    · intro hs
      apply hx.2.2.2.2
      omega
  · by_cases hs : x.size.val < 0
    · have hnon : ¬ -x.size.val < 0 := by omega
      simp only [hs, hnon, ↓reduceIte] at hv ⊢
      omega
    · by_cases hz' : x.size.val = 0
      · have hval := hz.mp hz'
        simp [hz', hval, limbMagnitude]
      · have hneg : -x.size.val < 0 := by omega
        simp only [hs, hneg, ↓reduceIte] at hv ⊢
        omega

theorem flipsignIdentityValueAndFrame_proven : FlipsignIdentityValueAndFrame := by
  intro Rest heap x y _ _ hx hy _ _
  have hsign := (g6valid_sign (heap.objects y.address).value hy).1
  simp only [flipsignBangDispatch, bigIntSignbitDispatch, JuliaLean.base.io.getWorld,
    JuliaLean.base.io.setWorld, assertSignbitCondition, signbit, isnegative,
    bind, pure, Option.bind]
  by_cases hs : (heap.objects y.address).value.size.val < 0
  · simp only [hs, decide_true, ↓reduceIte]
    have hn := negSizeVal (heap.objects x.address).value hx
    have hf := flipValue (heap.objects x.address).value hx
    have hval : (heap.objects y.address).value.val < 0 := hsign.mp hs
    simp only [hn, Int.natAbs_neg] at hf
    simp only [negateSizeHeader, ↓reduceIte, hn, Int.natAbs_neg, hval]
    obtain ⟨hv, he⟩ := hf
    rw [he] at hv
    simp only [hv, he, Int.natAbs_neg, true_and, and_true]
    constructor
    · intro address h
      simp only [h, ↓reduceIte]
    · omega
  · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hval : ¬ (heap.objects y.address).value.val < 0 := fun h => hs (hsign.mpr h)
    simp [hx, hval]

end JuliaLean.Proofs.base.gmp.Models2Group2

namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

def entriesModels2Group2Flipsign : List Entry := [
  { id := "gmp-flipsign-mutation-identity-frame",
    juliaFile := "base/gmp.jl", juliaFns := ["flipsign!(x::BigInt, y::Integer)"],
    statement := "The full effectful flipsign! body, instantiated with concrete Base BigInt signbit, preserves object identity and absolute value, multiplies the sign by that of the original second operand, retains valid representation and all limb/allocation storage, and changes no unrelated object or state; operand aliases are included.",
    source := "base/gmp.jl:753,752,749; helper dependencies: SignbitDispatchOps, assertSignbitCondition, negateSizeHeader, flipsignBangDispatch, bigIntSignbitDispatch, installed signbit/isnegative",
    status := .proven, prop := ``Models2Group2.FlipsignIdentityValueAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.flipsignIdentityValueAndFrame_proven,
    notes := "Generic signbit dispatch retains effects, errors, divergence and non-Bool results; TypeError occurs at the condition. The property uses the allowed concrete Base instance, with no callee law. Current x header is read only after signbit effects. Native Cint negation wraps, and the mathematical shadow is updated without another source-visible store. Nonwrapping Cint size negation follows from Valid's allocation/size bounds; the proof retains aliasing and the complete state frame." }
]
end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry
open JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

namespace Models2Group2

/-- The actual native-domain obligation for a path that reads a limb. The
immutable view must retain a live BigInt, and the mathematically computed
wrapped address must name eight readable bytes. No ordinary index-range or
nonnegative-field assumption is added: unsafe reads at raw states are covered
whenever their addressed memory is valid. This is a memory representation
requirement from base/pointer.jl:132-151, not a result-correctness premise. -/
def LimbViewNativeReadDomain {Rest : Type} (memory : LimbViewMemory Rest)
    (view : HeapLimbView) (index : Clong) : Prop :=
  let offset := wrapInt .i64 (view.startByte.val + index.val - 2)
  let pointer := (memory.heap.objects view.bigint.address).dataPointer
  memory.heap.liveObjects view.bigint.address = true ∧
  memory.readableLimb (JInt.wrap .u64 (pointer.val + 8 * offset.tdiv 8)) = true

/-- A legitimate byte window into a canonical native BigInt representation.
All active words are readable and agree with the represented limb snapshot.
The byte window lies inside the active magnitude; its machine-valued fields
are not arbitrarily bounded below their actual storage limits. Raw views are
also covered by the public properties: this invariant is only the antecedent
of the additional exact mathematical-byte assertion. -/
def LimbViewStorageValid {Rest : Type} (memory : LimbViewMemory Rest)
    (view : HeapLimbView) : Prop :=
  let cell := memory.heap.objects view.bigint.address
  memory.heap.liveObjects view.bigint.address = true ∧
  Valid cell.value ∧ cell.value.d.length < (2 : Nat)^63 ∧
  1 ≤ view.startByte.val ∧ 0 ≤ view.numBytes.val ∧
  view.startByte.val + view.numBytes.val - 1 ≤ 8 * (cell.value.size.val.natAbs : Int) ∧
  ∀ position : Nat, position < cell.value.size.val.natAbs →
    ∃ word : Limb,
      cell.value.d[position]? = some word ∧
      memory.heap.limbs (JInt.wrap .u64 (cell.dataPointer.val + 8 * (position : Int))) = word ∧
      memory.readableLimb (JInt.wrap .u64 (cell.dataPointer.val + 8 * (position : Int))) = true

/-- Independent base-256 magnitude digit, using the whole mathematical BigInt
rather than a limb load, bit shift, machine remainder, or model helper. Its
call sites require a legitimate window and an index inside that window, so
the natural exponent is the actual nonnegative byte position. -/
def LimbViewMagnitudeByte {Rest : Type} (memory : LimbViewMemory Rest)
    (view : HeapLimbView) (index : Clong) : Int :=
  (((memory.heap.objects view.bigint.address).value.val.natAbs /
    256 ^ (view.startByte.val + index.val - 2).toNat) % 256 : Nat)

/-- Every raw view has exactly one size dimension, and that dimension retains
the stored native count, including zero, negative counts, and both Int limits.
Julia source: base/gmp.jl:880-882. -/
def LimbViewSizeShape : Prop :=
  ∀ view : HeapLimbView,
    (limbViewSizeExact view).length = 1 ∧
    (limbViewSizeExact view).head? = some view.numBytes

/-- The existing complete length observer returns the stored native count
for every raw source record; no representation validity or nonnegative-count
premise is needed because this method never reads the BigInt or its storage.
Julia source: base/gmp.jl:899-901. -/
def LimbViewLengthField : Prop :=
  ∀ view : UnsafeLimbView,
    (JuliaLean.base.gmp.limbViewLength view).val = view.numBytes.val

/-- Independent integer characterization of the indices accepted by the raw
axis. Normal nonnegative counts have their usual one-based interval. Because
axes uses unchecked_oneto, a negative raw count instead accepts either positive
indices or indices at most that count. This definition uses no machine unsigned
conversion or wrapped subtraction from the implementation. -/
def LimbViewIndexAdmitted (view : HeapLimbView) (index : Clong) : Prop :=
  if 0 ≤ view.numBytes.val then 1 ≤ index.val ∧ index.val ≤ view.numBytes.val
  else 0 < index.val ∨ index.val ≤ view.numBytes.val

/-- The closed bounds helper recognizes the independently characterized raw
axis domain for every native Int index/count, including negative counts and
wrap-sensitive indices. No restriction to well-formed byte windows is imposed.
Julia source: base/gmp.jl:885; base/abstractarray.jl:100-103,753; base/range.jl:503. -/
def LimbViewBoundsDomain : Prop :=
  ∀ (view : HeapLimbView) (index : Clong),
    limbViewInBoundsExact view index = true ↔
      LimbViewIndexAdmitted view index

/-- Native pointerref addressing agrees with mathematical byte displacement
modulo the 64-bit address space, for every pointer and every signed index.
This independent modular formula checks the intermediate index subtraction,
eight-byte multiplication, unsigned conversion, and pointer addition together.
Julia source: base/pointer.jl:151; base/gmp.jl:889. -/
def LimbViewAddressArithmetic : Prop :=
  ∀ (pointer : JInt .u64) (index : Clong),
    (limbViewLoadAddress pointer index).val =
      (pointer.val + 8 * (index.val - 1)) % (2 : Int)^64

/-- The pure unchecked adapter exposes the same independent mathematical byte
of every legitimate window, for every in-window native index. Every raw
defined read still produces an actual UInt8. The expectation uses the whole
BigInt magnitude, not an effectful getter result or a supplied correctness law.
Julia source: base/gmp.jl:887-890; base/pointer.jl:132-151. -/
def LimbViewUncheckedMagnitudeByte : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest) (view : HeapLimbView) (index : Clong),
    LimbViewNativeReadDomain memory view index →
    let byte := limbViewByteUnchecked memory.heap view index
    0 ≤ byte.val ∧ byte.val < 256 ∧
    (LimbViewStorageValid memory view → 1 ≤ index.val → index.val ≤ view.numBytes.val →
      byte.val = LimbViewMagnitudeByte memory view index)

/-- Complete getindex invariant over every raw view, index, and bounds-check
context wherever a native read is defined. An enabled rejecting check raises
BoundsError before any required live/readable-memory premise. Every defined
successful read returns a byte and preserves the entire represented memory;
no other error or divergence is introduced. For a valid byte window, each
in-window result is its independent base-256 digit of the whole magnitude.
This covers malformed stored fields and unchecked indices without pretending
that an invalid native address has a Julia error or default value.
Julia source: base/gmp.jl:884-892; base/pointer.jl:132-151. -/
def LimbViewGetindexBytesAndFrame : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest) (view : HeapLimbView)
    (index : Clong) (checkBounds : Bool),
    ((checkBounds = true ∧ ¬ LimbViewIndexAdmitted view index) ∨
      LimbViewNativeReadDomain memory view index) →
    match limbViewGetindexExact view index checkBounds memory with
    | some (.ok (byte, after)) =>
        (checkBounds = false ∨ LimbViewIndexAdmitted view index) ∧
        0 ≤ byte.val ∧ byte.val < 256 ∧ after = memory ∧
        (LimbViewStorageValid memory view → 1 ≤ index.val → index.val ≤ view.numBytes.val →
          byte.val = LimbViewMagnitudeByte memory view index)
    | some (.error (error, after)) =>
        checkBounds = true ∧ ¬ LimbViewIndexAdmitted view index ∧
        error = .jl .boundsError ∧ after = memory
    | none => False

/-- Complete iteration invariant over every raw count/state wherever a native
read is defined. Exhaustion is exactly state > num_bytes; all other states,
including zero and negatives, perform the unchecked read. The next state has
the independent mathematical successor with the sole Int-limit wrap case.
Success, exhaustion, and byte observation preserve the whole memory; no bounds
error is inserted. Valid windows additionally return their base-256 digit.
Julia source: base/gmp.jl:894-897. -/
def LimbViewIterationBytesAndFrame : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest) (view : HeapLimbView) (state : Clong),
    (view.numBytes.val < state.val ∨ LimbViewNativeReadDomain memory view state) →
    match limbViewIterateExact view state memory with
    | some (.ok (none, after)) => view.numBytes.val < state.val ∧ after = memory
    | some (.ok (some (byte, next), after)) =>
        state.val ≤ view.numBytes.val ∧
        next.val = (if state.val = (2 : Int)^63 - 1 then -(2 : Int)^63 else state.val + 1) ∧
        0 ≤ byte.val ∧ byte.val < 256 ∧ after = memory ∧
        (LimbViewStorageValid memory view → 1 ≤ state.val →
          byte.val = LimbViewMagnitudeByte memory view state)
    | some (.error _) | none => False

end Models2Group2

namespace Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

theorem limbViewSizeShape_proven : LimbViewSizeShape := by
  intro view
  exact ⟨rfl, rfl⟩

theorem limbViewLengthField_proven : LimbViewLengthField := by
  intro view
  rfl

theorem limbViewBoundsDomain_proven : LimbViewBoundsDomain := by
  intro view index
  unfold limbViewInBoundsExact LimbViewIndexAdmitted
  simp only [JuliaLean.base.abstractarray.checkindexOneTo]
  have hi := index.property
  have hn := view.numBytes.property
  change -(2 : Int)^63 ≤ index.val ∧ index.val ≤ (2 : Int)^63 - 1 at hi
  change -(2 : Int)^63 ≤ view.numBytes.val ∧ view.numBytes.val ≤ (2 : Int)^63 - 1 at hn
  change decide (wrapInt .u64 (wrapInt .i64 (index.val - 1)) <
    wrapInt .u64 view.numBytes.val) = true ↔ _
  rw [decide_eq_true_eq]
  unfold wrapInt IntTy.signed IntTy.bits
  simp only [Nat.reduceSub, Int.reducePow, Bool.false_eq_true, ite_true, ite_false]
  split <;> omega

theorem limbViewAddressArithmetic_proven : LimbViewAddressArithmetic := by
  intro pointer index
  unfold limbViewLoadAddress JuliaLean.base.pointer.ptrAddI64
    JuliaLean.base.pointer.ptrAddInteger JuliaLean.base.pointer.int64ToUInt64
    JuliaLean.base.pointer.addPtrBytes
  change wrapInt .u64 (pointer.val + wrapInt .u64 (wrapInt .i64 (8 * wrapInt .i64 (index.val - 1)))) =
    (pointer.val + 8 * (index.val - 1)) % (2 : Int)^64
  unfold wrapInt IntTy.signed IntTy.bits
  simp only [Nat.reduceSub, Int.reducePow, Bool.false_eq_true, ite_true, ite_false]
  omega

end Models2Group2

def entriesModels2Group2LimbView : List Entry := [
  { id := "gmp-limbview-size-shape", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.size(view::UnsafeLimbView)"],
    statement := "For every raw UnsafeLimbView, size returns a rank-one tuple whose sole dimension is the unchanged stored Int num_bytes, including negative values and both native limits.",
    source := "base/gmp.jl:880-882", status := .proven,
    prop := ``Models2Group2.LimbViewSizeShape, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.limbViewSizeShape_proven,
    notes := "The baseline scalar-returning size model is not reused. The new HeapLimbView retains the mutable BigInt reference; a homogeneous singleton tuple is represented by List Clong with fixed arity one." },
  { id := "gmp-limbview-getindex-bytes-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.getindex(view::UnsafeLimbView, i::Int)"],
    statement := "Over every raw view/index and enabled or elided bounds context with defined native reads, getindex raises exactly BoundsError when the enabled raw-axis check rejects the index, otherwise returns a byte, and preserves the complete memory; valid windows return the mathematical base-256 magnitude digit.",
    source := "base/gmp.jl:884-892; base/pointer.jl:132-151", status := .todo,
    prop := ``Models2Group2.LimbViewGetindexBytesAndFrame, thm := none,
    notes := "Missing proof: establish LimbViewUncheckedMagnitudeByte and equivalence of the effectful installed div/rem/shift/mask/checked UInt8 path with that adapter, including exact conversion success for all raw signed offsets; then combine LimbViewBoundsDomain with state preservation. Raw negative counts and elided bounds checks must remain in the domain." },
  { id := "gmp-limbview-iteration-bytes-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.iterate(view::UnsafeLimbView, state::Int = 1)"],
    statement := "For every raw view/state with defined native reads, iterate exhausts exactly when state exceeds num_bytes, otherwise reads without bounds checks and returns the byte with the wrapping native successor; all outcomes preserve memory and valid windows expose their mathematical magnitude digit.",
    source := "base/gmp.jl:894-897; base/gmp.jl:884-892", status := .todo,
    prop := ``Models2Group2.LimbViewIterationBytesAndFrame, thm := none,
    notes := "Missing proof: establish LimbViewGetindexBytesAndFrame with checkBounds=false, then reduce limbViewIterateExact's exhaustion branch and prove the native state+1 successor formula at typemax. The valid-window digit clause follows using state<=num_bytes; zero/negative raw states must not be excluded." },
  { id := "gmp-limbview-length-field", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.length(view::UnsafeLimbView)"],
    statement := "For every raw UnsafeLimbView record, length returns the unchanged native num_bytes field, including zero, negative counts, and both native limits.",
    source := "base/gmp.jl:899-901", status := .proven,
    prop := ``Models2Group2.LimbViewLengthField, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.limbViewLengthField_proven,
    notes := "Reuses the existing complete JuliaLean.base.gmp.limbViewLength observer; it does not inspect mutable BigInt identity or storage, so no new model is required." },
  { id := "gmp-limbview-bounds-domain", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.getindex(view::UnsafeLimbView, i::Int): checkbounds"],
    statement := "The closed UnsafeLimbView bounds helper accepts exactly 1 <= i <= num_bytes for nonnegative counts, and exactly i > 0 or i <= num_bytes for negative raw counts, over all native indices.",
    source := "base/gmp.jl:885; base/abstractarray.jl:100-103,753; base/range.jl:503",
    status := .proven, prop := ``Models2Group2.LimbViewBoundsDomain, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.limbViewBoundsDomain_proven,
    notes := "Narrow independent helper invariant. axes uses unchecked_oneto, so the stop is not clamped; checking reuses installed abstractarray.checkindexOneTo. No callback law or nonnegative-count restriction." },
  { id := "gmp-limbview-pointer-address", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.getindex(view::UnsafeLimbView, i::Int): unsafe_load"],
    statement := "For every native pointer and signed limb index, the concrete UInt64 pointerref address equals pointer + 8*(index-1) modulo 2^64.",
    source := "base/gmp.jl:889; base/pointer.jl:151", status := .proven,
    prop := ``Models2Group2.LimbViewAddressArithmetic, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.limbViewAddressArithmetic_proven,
    notes := "Narrow helper invariant covers intermediate index subtraction, multiplication, unsigned conversion and pointer addition, including all wrapping endpoints. The loaded word is separately covered by the public independent base-256 byte properties." },
  { id := "gmp-limbview-unchecked-magnitude-byte", juliaFile := "base/gmp.jl",
    juliaFns := ["Base.getindex(view::UnsafeLimbView, i::Int): unchecked byte primitive"],
    statement := "The pure unchecked native adapter returns an UInt8 on every defined native read and the exact mathematical base-256 magnitude digit at every index inside a legitimate byte window.",
    source := "base/gmp.jl:887-890; base/pointer.jl:132-151", status := .todo,
    prop := ``Models2Group2.LimbViewUncheckedMagnitudeByte, thm := none,
    notes := "Missing proof: use LimbViewStorageValid's coherent native words and Valid magnitude expansion to identify the selected byte with val.natAbs/256^offset%256; prove signed offset arithmetic does not wrap within legitimate windows and installed shift/mask yields the selected base-256 digit. The UInt8 range clause follows directly from its subtype, but does not settle the digit clause." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp

open JuliaLean JuliaLean.Registry
open JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

namespace Models2Group2

/-- Actual native source-span domain for GMP mpn comparison: nonnegative signed
count, natural UInt64 alignment, a contiguous extent that does not wrap the
address space, and every complete active limb readable. A zero count imposes no pointer, readability or
alignment condition, as explicitly allowed by GMP6.3 gmp-h.in:2080-2103.
Alignment is explicit because the existing readableLimb predicate permits
Julia unsafe_load with alignment one, while this C array requires alignment eight.
Julia source: base/gmp.jl:267; GMP6.3 gmp-h.in:2080-2103,2171-2176. -/
def MpnReadableSpan {Rest : Type} (memory : LimbViewMemory Rest)
    (pointer : JuliaLean.base.pointer.Ptr Limb) (count : Clong) : Prop :=
  0 ≤ count.val ∧
  (count.val = 0 ∨
    (pointer.address.val % 8 = 0 ∧
      pointer.address.val + 8 * count.val ≤ (2 : Int)^64 ∧
      ∀ position : Nat, position < count.val.toNat →
        memory.readableLimb
          (JInt.wrap .u64 (pointer.address.val + 8 * (position : Int))) = true))

/-- Independent mathematical radix-2^64 value of the requested native prefix.
It includes every requested coefficient, including high zero words, and does
not inspect BigInt size/sign/capacity or execute any comparator/helper loop. -/
def MpnPrefixValue {Rest : Type} (memory : LimbViewMemory Rest)
    (pointer : JuliaLean.base.pointer.Ptr Limb) (count : Nat) : Nat :=
  ((List.range count).map fun (position : Nat) =>
    (memory.heap.limbs
      (JInt.wrap .u64 (pointer.address.val + 8 * (position : Int)))).val.toNat *
        (2 : Nat)^(64 * position)).sum

/-- Exact normalized result specified only by independent mathematical order. -/
def MpnExpectedOrder (result : Cint) (left right : Nat) : Prop :=
  (result.val = -1 ∨ result.val = 0 ∨ result.val = 1) ∧
  (result.val = -1 ↔ left < right) ∧
  (result.val = 0 ↔ left = right) ∧
  (result.val = 1 ↔ right < left)

/-- For the concrete native count instance, the complete pointer wrapper
compares the two requested unsigned radix-polynomial values exactly and
preserves the complete world. Zero count works with arbitrary pointers and no
readable memory. Aliased/overlapping inputs and high zero limbs are admitted.
Julia source: base/gmp.jl:267; GMP6.3 gmp-h.in:2080-2103,2171-2176. -/
def MpnCmpPointerOrderAndFrame : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest)
    (left right : JuliaLean.base.pointer.Ptr Limb) (count : Clong),
    MpnReadableSpan memory left count → MpnReadableSpan memory right count →
    match mpnCmpPointerDispatch (mpnNativeClongConversion Rest) left right count memory with
    | some (.ok (result, after)) =>
        MpnExpectedOrder result (MpnPrefixValue memory left count.val.toNat)
          (MpnPrefixValue memory right count.val.toNat) ∧ after = memory
    | some (.error _) | none => False

/-- The BigInt overload compares the actual requested limb prefixes at the
raw data pointers, not the numeric BigInt values or signed sizes. Only its two
header reads require live objects; actual readable contiguous spans suffice
for the native comparison. No Valid/size/capacity or snapshot-coherence premise
is imposed. Every execution preserves the entire world.
Julia source: base/gmp.jl:268,267; GMP6.3 gmp-h.in:2080-2103,2171-2176. -/
def MpnCmpBigIntOrderAndFrame : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest)
    (left right : InitBigIntRef) (count : Clong),
    memory.heap.liveObjects left.address = true →
    memory.heap.liveObjects right.address = true →
    let leftPointer : JuliaLean.base.pointer.Ptr Limb :=
      ⟨(memory.heap.objects left.address).dataPointer⟩
    let rightPointer : JuliaLean.base.pointer.Ptr Limb :=
      ⟨(memory.heap.objects right.address).dataPointer⟩
    MpnReadableSpan memory leftPointer count → MpnReadableSpan memory rightPointer count →
    match mpnCmpBigIntDispatch (mpnNativeClongConversion Rest) left right count memory with
    | some (.ok (result, after)) =>
        MpnExpectedOrder result (MpnPrefixValue memory leftPointer count.val.toNat)
          (MpnPrefixValue memory rightPointer count.val.toNat) ∧ after = memory
    | some (.error _) | none => False

/-- Necessary loop/native-entry invariant. Every sufficient termination fuel
produces the independent mathematical order of the full requested prefix;
extra fuel does not alter the answer. The native entry has the same expectation.
This exposes no fuel restriction on any valid source call and assumes no law
about the loop, its adapter, or another comparator.
Julia source: base/gmp.jl:267; GMP6.3 gmp-h.in:2080-2103,2171-2176. -/
def MpnCmpNativeAndLoop : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest)
    (left right : JuliaLean.base.pointer.Ptr Limb) (count : Clong),
    MpnReadableSpan memory left count → MpnReadableSpan memory right count →
    MpnExpectedOrder (mpnCmpNative memory left right count)
      (MpnPrefixValue memory left count.val.toNat)
      (MpnPrefixValue memory right count.val.toNat) ∧
    (∀ fuel : Nat, count.val.toNat + 1 ≤ fuel →
      MpnExpectedOrder (mpnCmpLoop memory left right count fuel)
        (MpnPrefixValue memory left count.val.toNat)
        (MpnPrefixValue memory right count.val.toNat))

/-- Closed conversion fields preserve every bit of the native pointer/count
and the entire world. The generic wrappers do not assume these identities for
custom count conversions; this property applies only to the installed Base
instance. Pointer identities separately cover both concrete conversion stages.
Julia source: base/essentials.jl:739,741-743; invoked by base/gmp.jl:267. -/
def MpnCmpNativeConversions : Prop :=
  (∀ pointer : JuliaLean.base.pointer.Ptr Limb,
    (JuliaLean.base.essentials.cconvertPointer pointer).address = pointer.address ∧
    (JuliaLean.base.essentials.unsafeConvertPointerIdentity pointer).address = pointer.address) ∧
  (∀ (Rest : Type) (memory : LimbViewMemory Rest) (count : Clong),
    (mpnNativeClongConversion Rest).cconvert count memory = some (.ok (count, memory)) ∧
    (mpnNativeClongConversion Rest).unsafeConvert count memory =
      some (.ok (Sum.inl count, memory)))

end Models2Group2

namespace Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

theorem mpnCmpNativeConversions_proven : MpnCmpNativeConversions := by
  exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ _ => ⟨rfl, rfl⟩⟩

end Models2Group2

def entriesModels2Group2MpnCmp : List Entry := [
  { id := "gmp-mpn-cmp-pointer-order-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.mpn_cmp(a::Ptr{Limb}, b::Ptr{Limb}, c)"],
    statement := "For every nonnegative native Clong count and two valid contiguous readable native limb spans, the full pointer wrapper returns exactly -1,0,1 according to the independent unsigned radix-2^64 prefix values and preserves the whole world; zero count needs no readable memory.",
    source := "base/gmp.jl:267; base/essentials.jl:739,741-743; GMP6.3 gmp-h.in:2080-2103,2171-2176", status := .todo,
    prop := ``Models2Group2.MpnCmpPointerOrderAndFrame, thm := none,
    notes := "Missing proof: establish MpnCmpNativeAndLoop's radix-prefix order invariant, then unfold concrete mpnNativeClongConversion and pointer conversions to prove mpnCmpPointerDispatch returns that result without changing memory. Zero count must require no readable limbs; arbitrary generic count-conversion behavior remains unconstrained." },
  { id := "gmp-mpn-cmp-bigint-order-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.mpn_cmp(a::BigInt, b::BigInt, c)"],
    statement := "For live BigInt headers whose raw data pointers provide the requested readable native prefixes, the BigInt wrapper compares their unsigned radix-polynomial values exactly and preserves the complete world, without numeric Valid, signed-size, or capacity restrictions.",
    source := "base/gmp.jl:268,267; GMP6.3 gmp-h.in:2080-2103,2171-2176", status := .todo,
    prop := ``Models2Group2.MpnCmpBigIntOrderAndFrame, thm := none,
    notes := "Missing proof: establish MpnCmpPointerOrderAndFrame and lift it through mpnCmpBigIntDispatch's two pre-conversion data-pointer captures and getWorld. Numeric Valid/size/capacity assumptions cannot be added: the property concerns raw readable prefixes, including aliases and high zero limbs." },
  { id := "gmp-mpn-cmp-native-loop-order", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.mpn_cmp: necessary GMP native loop and entry"],
    statement := "The necessary native entry and every sufficient structural loop fuel return the exact independently specified mathematical prefix order on the complete native readable-span domain.",
    source := "base/gmp.jl:267; GMP6.3 gmp-h.in:2080-2103,2171-2176", status := .todo,
    prop := ``Models2Group2.MpnCmpNativeAndLoop, thm := none,
    notes := "Missing proof: induct on the nonnegative native count with sufficient fuel; connect wrapping predecrement/load addresses to the highest prefix coefficient, bound every lower radix-2^64 prefix below the next weight, and show the first unequal high word decides total prefix order. Equal words recurse; count zero returns zero without reads. No loop-result premise or fuel cutoff may replace this invariant." },
  { id := "gmp-mpn-cmp-native-conversions", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.mpn_cmp: necessary native pointer/count conversions"],
    statement := "Both installed concrete pointer conversion stages preserve the complete pointer address, while the native Clong conversion instance preserves every scalar bit and the entire world.",
    source := "base/gmp.jl:267; base/essentials.jl:739,741-743", status := .proven,
    prop := ``Models2Group2.MpnCmpNativeConversions, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.mpnCmpNativeConversions_proven,
    notes := "Necessary narrow conversion invariant over concrete Base instances only. Generic count conversion actions remain arbitrary effectful operations without correctness laws." }
]

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2
open JuliaLean JuliaLean.base.float JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- Independent rational order, distance and adjacent-representable rounding
contracts. Infinity's nearest metric is one ulp beyond max finite, as specified
by base/rounding.jl:352-354. These helpers never invoke a rounding/conversion
implementation. Directed choices are extremal neighbors; nearest choices
minimize exact rational distance, with the documented tie rule.
Julia source: base/rounding.jl:50-110,352-354; base/gmp.jl:409-466
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def RoundingSpecRatEq (a b : Int × Nat) : Prop := a.1 * (b.2 : Int) = b.1 * (a.2 : Int)

def RoundingSpecRatLe (a b : Int × Nat) : Prop := a.1 * (b.2 : Int) ≤ b.1 * (a.2 : Int)

def RoundingSpecDistance (a b : Int × Nat) : Int × Nat :=
  (Int.ofNat ((a.1 * (b.2 : Int) - b.1 * (a.2 : Int)).natAbs), a.2 * b.2)

def RoundingSpecFloatMetric {T : FTy} (x : FV T) : Int × Nat :=
  if x.isinf then
    let magnitude : Int := Int.ofNat (2^(T.fmt.bias + 1))
    (if x.signbit then -magnitude else magnitude, 1)
  else x.toRat

def RoundingSpecFloatLeExact {T : FTy} (x : FV T) (q : Int × Nat) : Prop :=
  if x.isinf then x.signbit = true else RoundingSpecRatLe x.toRat q

def RoundingSpecExactLeFloat {T : FTy} (q : Int × Nat) (x : FV T) : Prop :=
  if x.isinf then x.signbit = false else RoundingSpecRatLe q x.toRat

def RoundingSpecFloatLe {T : FTy} (x y : FV T) : Prop :=
  if x.isinf then x.signbit = true ∨ (y.isinf = true ∧ y.signbit = false)
  else if y.isinf then y.signbit = false else RoundingSpecRatLe x.toRat y.toRat

def RoundingSpecFloatFloor {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  RoundingSpecFloatLeExact z q ∧
    ∀ y : FV T, y.isnan = false → RoundingSpecFloatLeExact y q → RoundingSpecFloatLe y z

def RoundingSpecFloatCeil {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  RoundingSpecExactLeFloat q z ∧
    ∀ y : FV T, y.isnan = false → RoundingSpecExactLeFloat q y → RoundingSpecFloatLe z y

def RoundingSpecFloatNearest {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  ∀ y : FV T, y.isnan = false →
    RoundingSpecRatLe (RoundingSpecDistance q (RoundingSpecFloatMetric z)) (RoundingSpecDistance q (RoundingSpecFloatMetric y))

def RoundingSpecFloatChoice {T : FTy} (r : RoundingMode) (n : Int) (z : FV T) : Prop :=
  z.isnan = false ∧ z.signbit = decide (n < 0) ∧
  let q : Int × Nat := (n, 1)
  match r with
  | .Down => RoundingSpecFloatFloor q z
  | .Up => RoundingSpecFloatCeil q z
  | .ToZero => if n < 0 then RoundingSpecFloatCeil q z else RoundingSpecFloatFloor q z
  | .FromZero => if n < 0 then RoundingSpecFloatFloor q z else RoundingSpecFloatCeil q z
  | .Nearest => RoundingSpecFloatNearest q z ∧
      (∀ y : FV T, y.isnan = false → RoundingSpecFloatNearest q y →
        ¬ RoundingSpecRatEq (RoundingSpecFloatMetric y) (RoundingSpecFloatMetric z) → z.toBits % 2 = 0)
  | .NearestTiesAway => RoundingSpecFloatNearest q z ∧
      (∀ y : FV T, y.isnan = false → RoundingSpecFloatNearest q y →
        RoundingSpecRatLe (RoundingSpecDistance (0, 1) (RoundingSpecFloatMetric y))
          (RoundingSpecDistance (0, 1) (RoundingSpecFloatMetric z)))
  | .NearestTiesUp => RoundingSpecFloatNearest q z ∧
      (∀ y : FV T, y.isnan = false → RoundingSpecFloatNearest q y → RoundingSpecFloatLe y z)

/-- Native storage domain: every active limb of the mathematical snapshot
is stored at its actual wrapped UInt64 address and is readable. This is the
representation/unsafe_load requirement, not a callee law or an assumption about
conversion outputs. All valid constructible magnitudes and signs are retained;
spare storage and unrelated memory remain unrestricted. -/
def RoundingStorageValid {Rest : Type} (memory : LimbViewMemory Rest)
    (input : InitBigIntRef) : Prop :=
  let cell := memory.heap.objects input.address
  memory.heap.liveObjects input.address = true ∧
  Valid cell.value ∧ cell.value.d.length < (2 : Nat)^63 ∧
  ∀ position : Nat, position < cell.value.size.val.natAbs →
    ∃ word : Limb,
      cell.value.d[position]? = some word ∧
      memory.heap.limbs (JInt.wrap .u64 (cell.dataPointer.val + 8 * (position : Int))) = word ∧
      memory.readableLimb (JInt.wrap .u64 (cell.dataPointer.val + 8 * (position : Int))) = true

/-- All valid constructible live BigInts, all IEEE formats and all seven
Base modes succeed with the independent documented rounding choice and
preserve the complete represented heap. No query/callee correctness law is
assumed: the concrete adapter invokes the installed mode models. The generic
source model additionally retains arbitrary mode/query/operator result types,
effects, errors and final custom returns. This is its permitted concrete Base
instantiation, not a restriction of the generic model.
Julia source: base/gmp.jl:411-466; documentation: base/rounding.jl:25-110,352-354;
base/docs/basedocs.jl:1942-1977; doc/src/manual/integers-and-floating-point-numbers.md:523-531
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def ExplicitRoundingChoiceAndFrame : Prop :=
  ∀ (T : FTy) (Rest : Type) (memory : LimbViewMemory Rest)
    (input : InitBigIntRef) (mode : RoundingMode),
    RoundingStorageValid memory input →
    match explicitFloatDispatch (nativeRoundingOps T Rest) input mode memory.heap with
    | some (.ok (.inl result, after)) =>
      RoundingSpecFloatChoice mode (memory.heap.objects input.address).value.val result ∧ after = memory.heap
    | _ => False

end JuliaLean.Proofs.base.gmp.Models2Group2

namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

def entriesModels2Group2Rounding : List Entry := [
  { id := "gmp-explicit-rounding-choice-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["(::Type{T})(x::BigInt, r::RoundingMode) where T<:IEEEFloat"],
    statement := "For every live valid constructible BigInt with coherent readable active native storage, every Float16/32/64 target and all seven Base rounding modes, explicit conversion succeeds with the independently specified directed/nearest rational neighbor, correct tie and overflow behavior, positive zero at zero, and complete heap preservation.",
    source := "base/gmp.jl:411-466; base/rounding.jl:25-127,352-354; base/docs/basedocs.jl:1942-1977; doc/src/manual/integers-and-floating-point-numbers.md:523-531",
    status := .todo, prop := ``Models2Group2.ExplicitRoundingChoiceAndFrame, thm := none,
    notes := "Missing proof: connect explicitFloatDispatch/nativeRoundingOps's effectful machine window, fill/sticky scans and mode queries to the independent RoundingSpecFloatChoice. BignumsGmpExplicitIeeeConversion_proven covers the older pure toFloat path only; a storage-coherence simulation and specification transport are still required, including all seven modes, overflow and positive zero." }
]
end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2

open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- Bool remainder reports mathematical parity for every valid constructible
BigInt, preserving the entire native world. Readability is required even for
zero, because the source's eager & always evaluates unsafe_load. First-limb
coherence is needed only for nonzero values; an initialized zero's readable
dummy word may contain any bits. These are actual storage invariants, not a
restriction on the mathematical integer or a law about a dispatched callee.
Julia source: base/gmp.jl:367; unsafe_load contract: base/pointer.jl:132-151. -/
def RemBoolParityAndFrame : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest) (input : InitBigIntRef),
    memory.heap.liveObjects input.address = true →
    Valid (memory.heap.objects input.address).value →
    (memory.heap.objects input.address).value.d.length < (2 : Nat)^63 →
    memory.readableLimb (memory.heap.objects input.address).dataPointer = true →
    ((memory.heap.objects input.address).value.size.val ≠ 0 →
      ScalarCmpFirstLimbCoherent memory.heap input) →
    match remBoolHeapExact input memory with
    | some (.ok (result, after)) =>
      (result = true ↔ (memory.heap.objects input.address).value.val % 2 = 1) ∧
      after = memory
    | _ => False

/-- Narrow raw-header invariant: all signed Cint headers and all readable
UInt64 first words are retained, without a Valid premise or a mathematical
shadow-value assumption. The result's truth is characterized by nonzero
header and odd native word, and every object/pointer/limb/state is unchanged.
Julia source: base/gmp.jl:367. -/
def RemBoolRawHeaderAndFrame : Prop :=
  ∀ (Rest : Type) (memory : LimbViewMemory Rest) (input : InitBigIntRef),
    memory.heap.liveObjects input.address = true →
    memory.readableLimb (memory.heap.objects input.address).dataPointer = true →
    match remBoolHeapExact input memory with
    | some (.ok (result, after)) =>
      (result = true ↔
        (memory.heap.objects input.address).value.size.val ≠ 0 ∧
        (memory.heap.limbs (memory.heap.objects input.address).dataPointer).val % 2 = 1) ∧
      after = memory
    | _ => False

end JuliaLean.Proofs.base.gmp.Models2Group2

namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

namespace Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2
open JuliaLean.ChatGPT.Batch4.Group7

private theorem band_u64_one_eq (word : Limb) :
    (JuliaLean.base.int.binop JuliaLean.base.int.band word (JuliaLean.base.int.lit .i64 1)).val =
      if word.val % 2 = 1 then 1 else 0 := by
  have hw := word.property
  change 0 ≤ word.val ∧ word.val ≤ (2 : Int)^64 - 1 at hw
  change wrapInt .u64 (((BitVec.ofInt 64 word.val &&& BitVec.ofInt 64 (wrapInt .u64 (wrapInt .i64 1))).toNat : Nat) : Int) = _
  have h1 : BitVec.ofInt 64 (wrapInt .u64 (wrapInt .i64 1)) = 1#64 := by decide
  rw [h1, BitVec.toNat_and, BitVec.toNat_ofInt]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [Nat.and_one_is_mod]
  have hmod : (word.val % ((18446744073709551616 : Nat) : Int)).toNat % 2 =
      (word.val % 2).toNat := by omega
  rw [hmod]
  split <;>
  · unfold wrapInt IntTy.signed IntTy.bits
    dsimp only
    omega

private theorem rem_bool_word_iff (word : Limb) :
    JuliaLean.base.int.rem_Integer_Bool word = true ↔ word.val % 2 = 1 := by
  unfold JuliaLean.base.int.rem_Integer_Bool JuliaLean.base.int.Generic.rem_Integer_Bool
  dsimp only
  have hb : JuliaLean.base.int.binop JuliaLean.base.int.band word (JuliaLean.base.int.lit .i64 1) =
      if word.val % 2 = 1 then JInt.wrap .u64 1 else JInt.wrap .u64 0 := by
    apply Subtype.ext
    rw [band_u64_one_eq]
    split <;> rfl
  rw [hb]
  have hw := word.property.1
  split
  · rename_i h
    have hd : (!JuliaLean.base.int.eq (JInt.wrap .u64 1) (JuliaLean.base.int.lit .i64 0)) = true := by decide
    change (!JuliaLean.base.int.eq (JInt.wrap .u64 1) (JuliaLean.base.int.lit .i64 0)) = true ↔ _
    rw [hd]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    have hd : (!JuliaLean.base.int.eq (JInt.wrap .u64 0) (JuliaLean.base.int.lit .i64 0)) = false := by decide
    change (!JuliaLean.base.int.eq (JInt.wrap .u64 0) (JuliaLean.base.int.lit .i64 0)) = true ↔ _
    rw [hd]
    exact ⟨fun hc => by contradiction, fun hc => False.elim (h hc)⟩

theorem remBoolRawHeaderAndFrame_proven : RemBoolRawHeaderAndFrame := by
  intro Rest memory input hlive hread
  have haddr : limbViewLoadAddress (memory.heap.objects input.address).dataPointer (JInt.wrap .i64 1) =
      (memory.heap.objects input.address).dataPointer := by
    apply Subtype.ext
    rw [limbViewAddressArithmetic_proven]
    have hp := (memory.heap.objects input.address).dataPointer.property
    change 0 ≤ (memory.heap.objects input.address).dataPointer.val ∧
      (memory.heap.objects input.address).dataPointer.val ≤ (2 : Int)^64 - 1 at hp
    change ((memory.heap.objects input.address).dataPointer.val + 8 * (1 - 1)) % (2 : Int)^64 = _
    omega
  have hand (a b : Bool) : JuliaLean.base.bool.andBool a b = (a && b) := by
    cases a <;> cases b <;> decide
  have hnot (a : Bool) : JuliaLean.base.bool.notBool a = !a := by
    cases a <;> decide
  simp only [remBoolHeapExact, limbViewLoadWord, JuliaLean.base.gmp.iszero,
    hnot, hand,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure, Option.bind, Except.bind, Except.pure,
    hlive, haddr, hread, ↓reduceIte]
  refine ⟨?_, rfl⟩
  rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, rem_bool_word_iff]
  simp only [haddr]

theorem remBoolParityAndFrame_proven : RemBoolParityAndFrame := by
  intro Rest memory input hlive hval hlen hread hcoh
  have hraw := remBoolRawHeaderAndFrame_proven Rest memory input hlive hread
  cases hrun : remBoolHeapExact input memory with
  | none => rw [hrun] at hraw; exact False.elim hraw
  | some res =>
    cases res with
    | error _ => rw [hrun] at hraw; exact False.elim hraw
    | ok pair =>
      rcases pair with ⟨result, after⟩
      rw [hrun] at hraw
      refine ⟨?_, hraw.2⟩
      rw [hraw.1]
      by_cases hsz : (memory.heap.objects input.address).value.size.val = 0
      · have hval0 : (memory.heap.objects input.address).value.val = 0 := hval.2.2.2.1.mp hsz
        simp [hsz, hval0]
      · have hcoh' := hcoh hsz
        have hd_pos : 0 < (memory.heap.objects input.address).value.d.length := by
          have h1 := hval.1; omega
        cases hd : (memory.heap.objects input.address).value.d with
        | nil => rw [hd] at hd_pos; contradiction
        | cons low rest =>
          have hhead : (memory.heap.objects input.address).value.d.head? = some low := by simp [hd]
          have hlimb := hcoh' low hhead
          rw [hlimb]
          have hmag := hval.2.2.1
          have hk : ∃ k : Nat, (memory.heap.objects input.address).value.size.val.natAbs = k + 1 :=
            ⟨(memory.heap.objects input.address).value.size.val.natAbs - 1, by omega⟩
          rcases hk with ⟨k, hk⟩
          rw [hd, hk, List.take_succ_cons, limbMagnitude] at hmag
          have hlow := low.property
          change 0 ≤ low.val ∧ low.val ≤ (2 : Int)^64 - 1 at hlow
          have hval_mod : (memory.heap.objects input.address).value.val % 2 = low.val % 2 := by
            let M := limbMagnitude (rest.take k)
            have hM : ((low.val.toNat + 2 ^ 64 * M : Nat) : Int) % 2 = low.val % 2 := by omega
            have hnegM : -((low.val.toNat + 2 ^ 64 * M : Nat) : Int) % 2 =
                ((low.val.toNat + 2 ^ 64 * M : Nat) : Int) % 2 := by omega
            rw [hmag]
            change (if (memory.heap.objects input.address).value.size.val < 0 then
              -((low.val.toNat + 2 ^ 64 * M : Nat) : Int)
              else ((low.val.toNat + 2 ^ 64 * M : Nat) : Int)) % 2 = low.val % 2
            split
            · exact hnegM.trans hM
            · exact hM
          simp only [hsz, ne_eq, not_false_eq_true, true_and, hval_mod]

end Models2Group2

def entriesModels2Group2RemBool : List Entry := [
  { id := "gmp-rem-bool-parity-frame",
    juliaFile := "base/gmp.jl", juliaFns := ["rem(x::BigInt, ::Type{Bool})"],
    statement := "For every valid constructible BigInt with its required readable native first word, Bool remainder is true exactly for an odd mathematical integer and preserves the complete memory; zero includes arbitrary readable dummy-word contents.",
    source := "base/gmp.jl:367; dependencies: remBoolHeapExact, limbViewLoadWord, limbViewLoadAddress, installed iszero, bool.notBool/andBool, int.rem_Integer_Bool",
    status := .proven, prop := ``Models2Group2.RemBoolParityAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.remBoolParityAndFrame_proven,
    notes := "The source & is eager: a native first-word load occurs even for zero. Actual storage coherence and readability are representation premises. No partial short-circuit or default-limb model is used." },
  { id := "gmp-rem-bool-raw-header-frame",
    juliaFile := "base/gmp.jl", juliaFns := ["rem(x::BigInt, ::Type{Bool})"],
    statement := "Over every live raw BigInt header with a readable first native word, Bool remainder is true exactly when the signed size is nonzero and the UInt64 word is odd, independently of the stored mathematical shadow; the complete world is unchanged.",
    source := "base/gmp.jl:367; native load base/pointer.jl:151; native parity base/int.jl:699",
    status := .proven, prop := ``Models2Group2.RemBoolRawHeaderAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.remBoolRawHeaderAndFrame_proven,
    notes := "Covers every raw Cint header and UInt64 word without assuming Valid, including typemin(Cint), all-ones words and arbitrary zero dummy contents. Native readability is unconditional." }
]
end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.Models2Group2
open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- Independent positional expansion of the represented native memory view. -/
def SyncMemoryMagnitude {Rest : Type} (heap : InitHeap Rest)
    (alloc size : Cint) (pointer : Culong) : Nat :=
  (List.range (min alloc.val.toNat size.val.natAbs)).foldl
    (fun sum i => sum +
      (heap.limbs (pointer + JInt.wrap .u64 (8 * Int.ofNat i))).val.toNat * 2^(64*i)) 0

/-- Header agreement, complete allocation view, and mathematical value of that
view. The expected value is derived from native memory by positional weights,
not by the model's header-store or shadow-recomputation helpers. -/
def SyncedHeaderView {Rest : Type} (heap : InitHeap Rest) (cell : InitHeapCell)
    (alloc size : Cint) (pointer : Culong) : Prop :=
  cell.value.alloc = alloc ∧ cell.value.size = size ∧ cell.dataPointer = pointer ∧
  cell.value.d.length = alloc.val.toNat ∧
  (∀ (i : Nat) (h : i < cell.value.d.length),
    cell.value.d[i] = heap.limbs (pointer + JInt.wrap .u64 (8 * Int.ofNat i))) ∧
  cell.value.val =
    (if size.val < 0 then -(SyncMemoryMagnitude heap alloc size pointer : Int)
     else (SyncMemoryMagnitude heap alloc size pointer : Int))

/-- Narrow internal synchronization invariant, including aliased numerator and
denominator: later denominator stores determine the shared header. All other
objects, raw records, native memory and unrelated state retain identity. -/
def RationalSyncHeadersAliasesAndFrame : Prop :=
  ∀ (Rest : Type) (heap : RationalSyncHeap Rest) (source : MPQHeaderRef),
    heap.liveRawObjects source.address = true →
    let raw := heap.rawObjects source.address
    heap.integers.liveObjects raw.rat.numerator.address = true →
    heap.integers.liveObjects raw.rat.denominator.address = true →
    (heap.integers.objects raw.rat.numerator.address).value.d.length < 2^63 →
    (heap.integers.objects raw.rat.denominator.address).value.d.length < 2^63 →
    let (returned, after) := syncRationalBang heap source
    returned = raw.rat ∧
    SyncedHeaderView heap.integers (after.integers.objects raw.rat.denominator.address)
      raw.denAlloc raw.denSize raw.denPointer ∧
    (if raw.rat.numerator = raw.rat.denominator then
      SyncedHeaderView heap.integers (after.integers.objects raw.rat.numerator.address)
        raw.denAlloc raw.denSize raw.denPointer
     else
      SyncedHeaderView heap.integers (after.integers.objects raw.rat.numerator.address)
        raw.numAlloc raw.numSize raw.numPointer) ∧
    (∀ address, address ≠ raw.rat.numerator.address → address ≠ raw.rat.denominator.address →
      after.integers.objects address = heap.integers.objects address) ∧
    after.rawObjects = heap.rawObjects ∧ after.liveRawObjects = heap.liveRawObjects ∧
    after.integers.liveObjects = heap.integers.liveObjects ∧
    after.integers.limbs = heap.integers.limbs ∧
    after.integers.dummyPointer = heap.integers.dummyPointer ∧
    after.integers.rest = heap.integers.rest

section
set_option maxRecDepth 4096

open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2
open JuliaLean.ChatGPT.Batch4.Group6

private theorem syncAddress (pointer : Culong) (i : Nat) :
    pointer + JInt.wrap .u64 8 * JInt.wrap .u64 (Int.ofNat i) =
      pointer + JInt.wrap .u64 (8 * Int.ofNat i) := by
  apply congrArg (fun word : Culong => pointer + word)
  apply Subtype.ext
  change ((8 % 18446744073709551616) * ((i : Int) % 18446744073709551616)) % 18446744073709551616 =
    (8 * (i : Int)) % 18446744073709551616
  rw [← Int.mul_emod]

private theorem syncMagnitude (words : Nat → Limb) (n : Nat) :
    limbMagnitude ((List.range n).map words) =
      (List.range n).foldl (fun total i => total + (words i).val.toNat * 2^(64*i)) 0 := by
  have general (n : Nat) (acc : Nat) :
      (List.range n).foldl (fun total i => total + (words i).val.toNat * 2^(64*i)) acc =
      acc + limbMagnitude ((List.range n).map words) := by
    induction n with
    | zero => simp [limbMagnitude]
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      have hd := cgTakeTopDecomposition ((List.range (n+1)).map words) n
      have ht : (((List.range (n+1)).map words).take n) = (List.range n).map words := by
        simp [List.range_succ, List.map_append, List.take_append]
      have hi : (((List.range (n+1)).map words)[n]?).getD (JInt.wrap .u64 0) = words n := by
        simp
      have hf : (((List.range (n+1)).map words).take (n+1)) = (List.range (n+1)).map words :=
        List.take_of_length_le (by simp)
      rw [hf, ht, hi] at hd
      rw [← List.range_succ, hd, ← Nat.pow_mul]
      rw [Nat.mul_comm (words n).val.toNat]
      omega
  simpa using (general n 0).symm

private theorem syncHeaderValid {Rest : Type} (heap : InitHeap Rest)
    (cell : InitHeapCell) (alloc size : Cint) (pointer : Culong) :
    SyncedHeaderView heap
      { cell with
        value := syncValueShadow { cell.value with
          alloc := alloc, size := size,
          d := (List.range alloc.val.toNat).map fun i =>
            heap.limbs (pointer + JInt.wrap .u64 8 * JInt.wrap .u64 (Int.ofNat i)) },
        dataPointer := pointer } alloc size pointer := by
  dsimp only [SyncedHeaderView, syncValueShadow]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_range]
  · intro i hi
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    exact congrArg heap.limbs (syncAddress pointer i)
  · have hm :
        limbMagnitude ((List.map (fun i => heap.limbs
          (pointer + JInt.wrap .u64 8 * JInt.wrap .u64 (Int.ofNat i)))
          (List.range alloc.val.toNat)).take size.val.natAbs) =
          SyncMemoryMagnitude heap alloc size pointer := by
      have addresses :
          (fun i => heap.limbs
            (pointer + JInt.wrap .u64 8 * JInt.wrap .u64 (Int.ofNat i))) =
          (fun i => heap.limbs (pointer + JInt.wrap .u64 (8 * Int.ofNat i))) := by
        funext i
        exact congrArg heap.limbs (syncAddress pointer i)
      rw [addresses, ← List.map_take, List.take_range, syncMagnitude]
      simp only [SyncMemoryMagnitude, Nat.min_comm]
    rw [hm]

theorem rationalSyncHeadersAliasesAndFrame_proven : RationalSyncHeadersAliasesAndFrame := by
  intro Rest heap source _
  dsimp only
  intro _ _ _ _
  dsimp only [syncRationalBang]
  have hd := syncHeaderValid heap.integers
    (heap.integers.objects (heap.rawObjects source.address).rat.denominator.address)
    (heap.rawObjects source.address).denAlloc (heap.rawObjects source.address).denSize
    (heap.rawObjects source.address).denPointer
  have hn := syncHeaderValid heap.integers
    (heap.integers.objects (heap.rawObjects source.address).rat.numerator.address)
    (heap.rawObjects source.address).numAlloc (heap.rawObjects source.address).numSize
    (heap.rawObjects source.address).numPointer
  by_cases he : (heap.rawObjects source.address).rat.numerator =
      (heap.rawObjects source.address).rat.denominator
  · have ha := congrArg InitBigIntRef.address he
    simp only [he, syncStoreAlloc, syncStoreSize, syncStorePointer,
      syncValueShadow, ↓reduceIte]
    refine ⟨True.intro, ?_, ?_, ?_, True.intro, True.intro, True.intro,
      True.intro, True.intro, True.intro⟩
    · simpa only [SyncedHeaderView, syncValueShadow] using hd
    · simpa only [SyncedHeaderView, syncValueShadow] using hd
    · intro address _ h
      simp only [h, ↓reduceIte]
  · have ha : (heap.rawObjects source.address).rat.numerator.address ≠
        (heap.rawObjects source.address).rat.denominator.address := by
      intro h
      exact he (congrArg InitBigIntRef.mk h)
    simp only [syncStoreAlloc, syncStoreSize, syncStorePointer,
      syncValueShadow, ha, Ne.symm ha, he, ↓reduceIte]
    refine ⟨True.intro, ?_, ?_, ?_, True.intro, True.intro, True.intro,
      True.intro, True.intro, True.intro⟩
    · simpa only [SyncedHeaderView, syncValueShadow] using hd
    · simpa only [SyncedHeaderView, syncValueShadow] using hn
    · intro address hn' hd'
      simp only [hn', hd', ↓reduceIte]
end

end JuliaLean.Proofs.base.gmp.Models2Group2

namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

def entriesModels2Group2RationalSync : List Entry := [
  { id := "gmp-rational-sync-headers-alias-frame",
    juliaFile := "base/gmp.jl", juliaFns := ["MPQ.sync_rational!(xq::_MPQ)"],
    statement := "Synchronization returns the original Rational references, publishes the raw GMP numerator/denominator headers in source order, handles shared numerator and denominator by retaining the later denominator header, makes the representation shadows agree with native memory, and changes no other objects, raw records, limb memory or unrelated state.",
    source := "base/gmp.jl:994-1002; representation types: base/gmp.jl:966-977; base/rational.jl:9-15",
    status := .proven, prop := ``Models2Group2.RationalSyncHeadersAliasesAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.rationalSyncHeadersAliasesAndFrame_proven,
    notes := "The proof derives the positional native-memory expansion from the range/map limb view, normalizes wrapping pointer addresses, and composes all six stores with aliased and distinct reference cases. It preserves every unrelated map and state field and makes no constructor or normalization claim." }
]
end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp
open JuliaLean.Registry

def entriesModels2Group2Init : List Entry := [
  { id := "gmp-init-identity-zero-frame", juliaFile := "base/gmp.jl",
    juliaFns := ["MPZ.init!(x::BigInt)"],
    statement := "Native MPZ.init! returns the original mutable BigInt, sets its value, size, and allocation to zero, points it at GMP's static dummy limb, updates every alias, and preserves other object headers, limb memory, and unrelated represented source state.",
    source := "base/gmp.jl:163; base/essentials.jl:739; base/refpointer.jl:110,113; base/refvalue.jl:8,38-54; GMP 6.3.0 mpz/init.c:35-41",
    status := .proven, prop := ``Models2Group2.InitIdentityZeroAndFrame, thm := some ``JuliaLean.Proofs.base.gmp.Models2Group2.initIdentityZeroAndFrame_proven,
    notes := "Narrow internal initializer invariant. Covers Models2Group2.initBang and concrete initCconvert, initUnsafeConvert, initNative dependencies. Retains object/data-pointer identity and aliases. The temporary nonescaping RefValue root uses the installed structural allocation boundary; allocator/GC bookkeeping is outside represented state." }
]

def entriesModels2Group2 : List Entry :=
  entriesModels2Group2Bootstrap ++ entriesModels2Group2Init ++
  entriesModels2Group2Scan ++ entriesModels2Group2Observations ++
  entriesModels2Group2BitQueries ++
  entriesModels2Group2Cmp ++ entriesModels2Group2ScalarCmp ++
  entriesModels2Group2GetD ++ entriesModels2Group2Tstbit ++
  entriesModels2Group2TypeViews ++ entriesModels2Group2Dispatch ++
  entriesModels2Group2PublicSignedCmp ++ entriesModels2Group2GenericComparison ++
  entriesModels2Group2PublicFloatCmp ++ entriesModels2Group2Predicates ++
  entriesModels2Group2Flipsign ++ entriesModels2Group2LimbView ++
  entriesModels2Group2MpnCmp ++
  entriesModels2Group2Rounding ++
  entriesModels2Group2RemBool ++
  entriesModels2Group2RationalSync

end JuliaLean.Proofs.base.gmp


namespace JuliaLean.Proofs.base.gmp.MemSafetyRetired

open JuliaLean JuliaLean.base.gmp JuliaLean.base.gmp.Models2Group2

/-- The native word read by remBoolHeapExact must be readable even when the size is zero. -/
def GmpBoolRemInBounds : Prop :=
  ∀ (memory : LimbViewMemory Unit) (input : InitBigIntRef),
    memory.heap.liveObjects input.address = true →
    Valid (memory.heap.objects input.address).value →
    ∃ result, remBoolHeapExact input memory = some (.ok (result, memory)) ∧
      memory.readableLimb (limbViewLoadAddress
        (memory.heap.objects input.address).dataPointer (JInt.wrap .i64 1)) = true

private def nullZeroMemory : LimbViewMemory Unit where
  heap := {
    objects := fun _ => ⟨ofInt 0, JInt.wrap .u64 0⟩
    liveObjects := fun _ => true
    limbs := fun _ => JInt.wrap .u64 0
    dummyPointer := JInt.wrap .u64 1
    rest := () }
  readableLimb := fun address => decide (address.val ≠ 0)

theorem gmpBoolRemInBounds_refuted : ¬ GmpBoolRemInBounds := by
  intro h
  have hz : Valid (ofInt 0) := by
    simp [Valid, ofInt, limbsOfNat, limbMagnitude]
    decide
  obtain ⟨_, _, bad⟩ := h nullZeroMemory ⟨JInt.wrap .u64 1⟩ rfl hz
  have notReadable : nullZeroMemory.readableLimb
      (limbViewLoadAddress (JInt.wrap .u64 0) (JInt.wrap .i64 1)) = false := by decide
  exact Bool.noConfusion (notReadable.symm.trans bad)

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-gmp-zero-bool-rem-null", juliaFile := "base/gmp.jl"
    juliaFns := ["rem(::BigInt, ::Type{Bool})"]
    statement := "The eager Boolean remainder method reads a valid first limb for every live BigInt storage representation."
    source := "memory-safety invariant; base/gmp.jl:129,294,367"
    status := .refuted, prop := ``GmpBoolRemInBounds, thm := some ``gmpBoolRemInBounds_refuted
    issue := "none found (queries: BigInt ZERO rem Bool segfault; GMP ZERO unsafe_load rem)"
    notes := "The installed remBoolHeapExact computes a first-word load even when size is zero. A live, valid zero header with a null native limb pointer violates the installed memory-domain readability predicate. rem(Base.GMP.ZERO, Bool) terminates both tested Julia child processes with signal 11." }
]

end JuliaLean.Proofs.base.gmp.MemSafetyRetired

namespace JuliaLean.Proofs.base.gmp

namespace LegacyRetired

open JuliaLean JuliaLean.base.gmp JuliaLean.base.float
open JuliaLean.base.gmp.MPZ JuliaLean.base.gmp.MPQ

def GmpBootstrapCorrect : Prop :=
  (∀ (V : Type) (versionNumber : String → Jl V) (globals : LibraryGlobals),
      JuliaLean.base.gmp.version (V := V) versionNumber globals = (
      versionNumber (versionString globals))) ∧
  (∀ (globals : LibraryGlobals),
      JuliaLean.base.gmp.majorVersion globals = (
      match (versionString globals).toList with
      | [] => .error .boundsError
      | c :: _ => .ok c)) ∧
  (∀ (globals : LibraryGlobals),
      JuliaLean.base.gmp.libraryBitsPerLimb globals = (
      JInt.wrap .i64 globals.limbBits.val)) ∧
  (∀ (M : Type → Type) [Monad M] (E : Type) (ops : GMPInitOps M E),
      JuliaLean.base.gmp.initModule (M := M) (E := E) ops = (
      do
       ops.tryCatch (do
         let major ← ops.majorVersion
         let differs ← if major != ops.expectedMajorVersion then pure true
           else pure ((← ops.bitsPerLimb) != ops.expectedBitsPerLimb)
         if differs then
           let version ← ops.version
           let messageBits ← ops.bitsPerLimb
           let message :=
             "The dynamically loaded GMP library (v\"" ++ version ++
             "\" with __gmp_bits_per_limb == " ++ toString messageBits.val ++ ")\n" ++
             "does not correspond to the compile time version (v\"" ++ ops.buildVersion ++
             "\" with __gmp_bits_per_limb == " ++ toString ops.expectedBitsPerLimb.val ++ ").\n" ++
             "Please rebuild Julia."
           if (← ops.bitsPerLimb) != ops.expectedBitsPerLimb then ops.logError message
           else ops.warn message
         ops.callSetMemoryFunctions ops.memoryFunctions
         let library ← ops.readLibraryRuntime
         ops.writeLibraryRuntime (setMemoryFunctions library ops.memoryFunctions)
         let zero ← ops.readZero
         ops.writeZero { zero with
           alloc := JInt.wrap .i32 0
           size := JInt.wrap .i32 0
           d := [] }
         let one ← ops.readOne
         ops.writeOne { one with
           alloc := JInt.wrap .i32 1
           size := JInt.wrap .i32 1
           d := oneLimbs })
         (fun error => ops.showErrorNostdio error "WARNING: Error during initialization of module GMP")
       ops.tryCatch (do
         ops.callSetAllocOverflowFunction ops.allocationOverflowHook
         let library ← ops.readLibraryRuntime
         ops.writeLibraryRuntime (setAllocOverflowFunction library ops.allocationOverflowHook)
         ops.writeOverflowFlag true)
         (fun error => if ops.isErrorException error then pure () else ops.throw error))) ∧
  (∀ (I : Type) (value : I → Int) (nbits : I),
      JuliaLean.base.gmp.constructBigInt (I := I) value nbits = (
      do
       let nbits ← JInt.convert "UInt64" .u64 (value nbits)
       let b := MPZ.init2 initBigInt nbits
       return b)) ∧
  (∀ (op : String),
      JuliaLean.base.gmp.MPZ.gmpz op = (
      ⟨"__gmpz_" ++ op, "MPZ", "libgmp"⟩)) ∧
  (∀ (op : String),
      JuliaLean.base.gmp.MPQ.gmpq op = (
      ⟨"__gmpq_" ++ op, "MPZ", "libgmp"⟩)) ∧
  (∀ (a : BigInt) (base : Cint) (oneHigh : Bool),
      JuliaLean.base.gmp.MPZ.sizeinbase a base oneHigh = (
      let radix := base.val.toNat
      let exact := (radixDigits a.val.natAbs radix).length
      let power2 := radix > 0 ∧ Nat.land radix (radix-1) = 0
      let extra := if a.val ≠ 0 ∧ ¬power2 ∧ oneHigh then 1 else 0
      JInt.wrap .i64 ((exact+extra : Nat) : Int)))

theorem gmpBootstrapCorrect : GmpBootstrapCorrect := by
  unfold GmpBootstrapCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def WrapperAllocationCorrect : Prop :=
  (∀ (x : BigInt),
      JuliaLean.base.gmp.MPZ.init x = (
      writeValue x 0)) ∧
  (∀ (x : BigInt) (nbits : Culong),
      JuliaLean.base.gmp.MPZ.init2 x nbits = (
      ofInt 0 nbits.val.toNat)) ∧
  (∀ (x : BigInt) (nbits : Culong),
      JuliaLean.base.gmp.MPZ.realloc2 x nbits = (
      let capacity := (nbits.val.toNat + 63) / 64
      let n := if x.val.natAbs < 2^nbits.val.toNat then x.val else 0
      { (ofInt n) with alloc := JInt.wrap .i32 (capacity : Int) })) ∧
  (∀ (nbits : Culong),
      JuliaLean.base.gmp.MPZ.realloc nbits = (
      realloc2 (initBigInt) nbits)) ∧
  (∀ (op : BinaryOp) (x a b : BigInt),
      JuliaLean.base.gmp.MPZ.binaryBang op x a b = (
      do
       pure (writeValue x (← binaryValue op a.val b.val)))) ∧
  (∀ (op : BinaryOp) (a b : BigInt),
      JuliaLean.base.gmp.MPZ.binary op a b = (
      let nbits := if op = .add ∨ op = .sub then
        64 * (1 + max a.size.val.natAbs b.size.val.natAbs) else 0
      binaryBang op (ofInt 0 nbits) a b)) ∧
  (∀ (op : BinaryOp) (x b : BigInt),
      JuliaLean.base.gmp.MPZ.binaryInplace op x b = (
      binaryBang op x x b)) ∧
  (∀ (op : UnsignedOp) (x a : BigInt) (b : Culong),
      JuliaLean.base.gmp.MPZ.unsignedBang op x a b = (
      writeValue x (unsignedValue op a.val b))) ∧
  (∀ (op : UnsignedOp) (a : BigInt) (b : Culong),
      JuliaLean.base.gmp.MPZ.unsigned op a b = (
      unsignedBang op initBigInt a b)) ∧
  (∀ (op : UnsignedOp) (x : BigInt) (b : Culong),
      JuliaLean.base.gmp.MPZ.unsignedInplace op x b = (
      unsignedBang op x x b)) ∧
  (∀ (x : BigInt) (a : Culong) (b : BigInt),
      JuliaLean.base.gmp.MPZ.uiSubBang x a b = (
      writeValue x (a.val-b.val))) ∧
  (∀ (a : Culong) (b : BigInt),
      JuliaLean.base.gmp.MPZ.uiSub a b = (
      uiSubBang initBigInt a b)) ∧
  (∀ (x a : BigInt) (b : Clong),
      JuliaLean.base.gmp.MPZ.mulSiBang x a b = (
      writeValue x (a.val*b.val))) ∧
  (∀ (a : BigInt) (b : Clong),
      JuliaLean.base.gmp.MPZ.mulSi a b = (
      mulSiBang initBigInt a b)) ∧
  (∀ (x : BigInt) (b : Clong),
      JuliaLean.base.gmp.MPZ.mulSiInplace x b = (
      mulSiBang x x b)) ∧
  (∀ (op : UnaryOp) (x a : BigInt),
      JuliaLean.base.gmp.MPZ.unaryBang op x a = (
      match op with
      | .neg => pure (writeValue x (-a.val))
      | .com => pure (writeValue x (-a.val-1))
      | .set => pure (writeValue x a.val)
      | .sqrt => if a.val < 0 then .error .divideError
        else pure (writeValue x (Nat.sqrt a.val.toNat)))) ∧
  (∀ (op : UnaryOp) (a : BigInt),
      JuliaLean.base.gmp.MPZ.unary op a = (
      unaryBang op initBigInt a)) ∧
  (∀ (op : UnaryOp) (x : BigInt),
      JuliaLean.base.gmp.MPZ.unaryInplace op x = (
      unaryBang op x x)) ∧
  (∀ (x : BigInt) (a : Culong),
      JuliaLean.base.gmp.MPZ.facUiBang x a = (
      writeValue x (factorialNat a.val.toNat))) ∧
  (∀ (a : Culong),
      JuliaLean.base.gmp.MPZ.facUi a = (
      facUiBang initBigInt a)) ∧
  (∀ (x a b c : BigInt),
      JuliaLean.base.gmp.MPZ.powmBang x a b c = (
      do
       if c.val = 0 then throw .divideError
       let modulus := (c.val.natAbs : Int)
       let base ← if b.val < 0 then do
         let (inverse,status) ← invertBang initBigInt a c
         if status.val = 0 then throw .divideError
         pure inverse.val
         else pure a.val
       pure (writeValue x (powModNat (base % modulus) b.val.natAbs modulus)))) ∧
  (∀ (a b c : BigInt),
      JuliaLean.base.gmp.MPZ.powm a b c = (
      powmBang initBigInt a b c)) ∧
  (∀ (x b c : BigInt),
      JuliaLean.base.gmp.MPZ.powmInplace x b c = (
      powmBang x x b c))

theorem wrapperAllocationCorrect : WrapperAllocationCorrect := by
  unfold WrapperAllocationCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def GmpMpzObserversCorrect : Prop :=
  (∀ (a : BigInt),
      JuliaLean.base.gmp.MPZ.popcount a = (
      JInt.wrap .i64 (if a.val < 0 then -1 else (countBits a.val.toNat : Int)))) ∧
  (∀ (a : BigInt),
      JuliaLean.base.gmp.MPZ.mpnPopcount a = (
      mpnPopcountLimbs a.d (JInt.wrap .i64 a.size.val.natAbs))) ∧
  (∀ (x y a b : BigInt),
      JuliaLean.base.gmp.MPZ.tdivQrBang x y a b = (
      do
       let q ← binaryValue .tdivQ a.val b.val
       pure (writeValue x q, writeValue y (a.val-q*b.val)))) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.MPZ.tdivQr a b = (
      tdivQrBang initBigInt initBigInt a b)) ∧
  (∀ (x y z a b : BigInt),
      JuliaLean.base.gmp.MPZ.gcdextBang x y z a b = (
      let (g,s,t) := gmpGcdext a.val b.val
      (writeValue x g, writeValue y s, writeValue z t))) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.MPZ.gcdext a b = (
      gcdextBang initBigInt initBigInt initBigInt a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.MPZ.cmp a b = (
      JInt.wrap .i64 (sgn (a.val-b.val)))) ∧
  (∀ (a : BigInt) (b : Clong),
      JuliaLean.base.gmp.MPZ.cmpSi a b = (
      JInt.wrap .i64 (sgn (a.val-b.val)))) ∧
  (∀ (a : BigInt) (b : Culong),
      JuliaLean.base.gmp.MPZ.cmpUi a b = (
      JInt.wrap .i64 (sgn (a.val-b.val)))) ∧
  (∀ (a b : BigInt) (count : Clong),
      JuliaLean.base.gmp.MPZ.mpnCmp a b count = (
      mpnCmpLimbs a.d b.d count)) ∧
  (∀ (base : Cint) (b : BigInt),
      JuliaLean.base.gmp.MPZ.getStr base b = (
      let magnitude := renderMagnitude b.val.natAbs base.val.natAbs
      let magnitude := if base.val < 0 then String.ofList (magnitude.toList.map Char.toUpper) else magnitude
      (if b.val < 0 then "-" else "") ++ magnitude)) ∧
  (∀ (x : BigInt) (a : String) (base : Cint),
      JuliaLean.base.gmp.MPZ.setStrBang x a base = (
      let chars := (a.toUTF8.toList.map (fun b => Char.ofNat b.toNat)).filter (fun c => !cWhitespace c)
      let (negative,chars) := match chars with
        | '-' :: tail => (true,tail)
        | _ => (false,chars)
      let (radix,chars) := if base.val = 0 then
        match chars with
        | '0' :: 'x' :: tail | '0' :: 'X' :: tail => (16,tail)
        | '0' :: 'b' :: tail | '0' :: 'B' :: tail => (2,tail)
        | '0' :: tail => (8,if tail.isEmpty then ['0'] else tail)
        | _ => (10,chars)
        else (base.val.toNat,chars)
      match parseMagnitude chars radix with
      | none => (x, JInt.wrap .i64 (-1))
      | some n => (writeValue x (if negative then -(n : Int) else n), JInt.wrap .i64 0))) ∧
  (∀ (t : IntTy) (a : DigitVector (JInt t)) (n : BigInt) (mostSignificantFirst : Bool) (nails : Nat) (bigEndian : Bool),
      JuliaLean.base.gmp.MPZ.exportWords t a n mostSignificantFirst nails bigEndian = (
      do
       if a.stride.val ≠ 1 then throw (.julia (.argumentError "a must have stride 1"))
       let bits := t.bits-nails
       let bitLength := if n.val = 0 then 1 else n.val.natAbs.log2+1
       let ndigits := (bitLength+bits-1)/bits
       let capacity := max a.data.length ndigits
       let count := if n.val = 0 then 0 else ndigits
       let words := (List.range count).map (fun i => endianWord t bigEndian
         (n.val.natAbs / 2^(bits*i) % 2^bits))
       let words := if mostSignificantFirst then words.reverse else words
       let output := words ++ List.replicate (capacity-count) (JInt.wrap t 0)
       if count > output.length then throw .assertionError
       return ({ a with data := output }, JInt.wrap .i64 (count : Int)))) ∧
  (∀ (x : BigInt) (count : Clong),
      JuliaLean.base.gmp.MPZ.limbsWrite x count = (
      { x with
        alloc := JInt.wrap .i32 (max x.alloc.val count.val)
        d := x.d ++ List.replicate (count.val.toNat-x.d.length) (JInt.wrap .u64 0) })) ∧
  (∀ (x : BigInt) (count : Clong),
      JuliaLean.base.gmp.MPZ.limbsFinish x count = (
      let magnitude := limbMagnitude (x.d.take count.val.natAbs)
      let normalized := ofInt (if count.val < 0 then -(magnitude : Int) else magnitude)
      { normalized with alloc := x.alloc, d := x.d })) ∧
  (∀ (a : BigInt) (b : Culong),
      JuliaLean.base.gmp.MPZ.tstbit a b = (
      bitAt a.val b.val.toNat))

theorem gmpMpzObserversCorrect : GmpMpzObserversCorrect := by
  unfold GmpMpzObserversCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def GmpConversionRoutingCorrect : Prop :=
  (∀ (x : BigInt),
      JuliaLean.base.gmp.signed x = (
      x)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.fromBigInt x = (
      x)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.signedBigInt x = (
      x)) ∧
  (∀ (x : Clong),
      JuliaLean.base.gmp.fromSignedLong x = (
      MPZ.setSi x)) ∧
  (∀ (x : Culong),
      JuliaLean.base.gmp.fromUnsignedLong x = (
      MPZ.setUi x)) ∧
  (∀ (x : JInt .i32),
      JuliaLean.base.gmp.fromInt32 x = (
      MPZ.setSi (JInt.wrap .i64 x.val))) ∧
  (∀ (x : JInt .u32),
      JuliaLean.base.gmp.fromUInt32 x = (
      MPZ.setUi (JInt.wrap .u64 x.val))) ∧
  (∀ (x : FV .f64),
      JuliaLean.base.gmp.fromFloat64 x = (
      if h : x.isinteger = true then
        pure (MPZ.setD x (by
          have hh := h
          simp only [JuliaLean.Promotion.Fl.isinteger, Bool.and_eq_true] at hh
          exact hh.1))
      else .error (.inexactError "BigInt"))) ∧
  (∀ (x : FV .f16),
      JuliaLean.base.gmp.fromFloat16 x = (
      fromFloat64 (convertFloat .f64 x))) ∧
  (∀ (x : FV .f32),
      JuliaLean.base.gmp.fromFloat32 x = (
      fromFloat64 (convertFloat .f64 x))) ∧
  (∀ (I U : Type) (ops : IntegerInput I U) (x : I),
      JuliaLean.base.gmp.fromInteger (I := I) (U := U) ops x = (
      if ops.isbits x && ops.fitsLong x then fromSignedLong (ops.remLong x) else
        let nd := ops.ndigits2 x
        let z := MPZ.realloc (JInt.wrap .u64 nd.val)
        let ux := ops.unsigned (if ops.negative x then ops.negWrap x else x)
        let limbs := fillLimbs ops.lowLimb ops.shiftRight ((nd.val.toNat+63)/64) ux
        let count := Int.ofNat limbs.length
        let size := if ops.negative x then -count else count
        { z with val := if ops.negative x then -(limbMagnitude limbs : Int)
          else limbMagnitude limbs, size := JInt.wrap .i32 size, d := limbs })) ∧
  (∀ (t : IntTy) (x : BigInt),
      JuliaLean.base.gmp.remLimb t x = (
      if iszero x then JInt.wrap t 0 else
        let low := JInt.wrap t ((x.d[0]?).getD (JInt.wrap .u64 0)).val
        if isnegative x then -low else low)) ∧
  (∀ (t : IntTy) (x : BigInt),
      JuliaLean.base.gmp.remBits t x = (
      let n := min x.size.val.natAbs ((t.bits+63)/64)
      let u := (List.range n).foldl (fun u l =>
        u + JInt.wrap t (((x.d[l]?).getD (JInt.wrap .u64 0)).val * (2 : Int)^(64*l)))
        (JInt.wrap t 0)
      if isnegative x then -u else u)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.isodd x = (
      MPZ.tstbit x (JInt.wrap .u64 0))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.iseven x = (
      !isodd x)) ∧
  (∀ (T : FTy) (x : BigInt) (r : RoundingMode),
      JuliaLean.base.gmp.toFloat T x r = (
      let xsize := x.size.val.natAbs
      if xsize = 0 then JuliaLean.Promotion.Fl.zero false else
        let sb := isnegative x
        let top := loadLimb x (xsize-1)
        let s := if top = 0 then 0 else top.log2+1
        let nbits := s+(xsize-1)*64
        if (nbits : Int) > (exponent_max T).val+1 then
          let overflow := roundsNearest r || roundsAway r sb
          let u := if overflow then ieee754_representation_inf T sb
            else ieee754_representation_omega T sb
          JuliaLean.Promotion.Fl.ofBits u.val.toNat
        else
          let (m,filled,i) := fillWindow x (xsize-1) top s
          let (m,filled,i,sticky) := if i > 0 ∧ filled < 64 then
            let l := loadLimb x (i-1)
            let k := 64-filled
            ((m*2^k + l / 2^(64-k)) % 2^64,64,i-1,decide ((l*2^k)%2^64 ≠ 0))
            else (m,filled,i,false)
          let sticky := (List.range i).foldl (fun st j => st || decide (loadLimb x j ≠ 0)) sticky
          let m := (m*2^(64-filled)) % 2^64
          let p := T.fmt.sb+1
          let q := m / 2^(64-p)
          let rest := (m*2^p) % 2^64
          let roundBit := decide (rest / 2^63 ≠ 0)
          let sticky := sticky || decide ((rest*2)%2^64 ≠ 0)
          let incr := if roundsNearest r then
            let tieUp := if r = .Nearest then decide (q%2 = 1)
              else if r = .NearestTiesAway then true else !sb
            roundBit && (sticky || tieUp)
            else roundsAway r sb && (roundBit || sticky)
          let signif : Nat := q % 2^T.fmt.sb
          let u := ieee754_representation T sb
            (JInt.wrap .i64 ((nbits : Int)-1+(exponent_bias T).val))
            (JInt.wrap T.uintTy (signif : Int))
          JuliaLean.Promotion.Fl.ofBits ((u.val.toNat + if incr then 1 else 0) % 2^(T.bytes*8)))) ∧
  (∀ (n : BigInt),
      JuliaLean.base.gmp.toFloat16 n = (
      toFloat .f16 n .Nearest)) ∧
  (∀ (n : BigInt),
      JuliaLean.base.gmp.toFloat32 n = (
      toFloat .f32 n .Nearest)) ∧
  (∀ (n : BigInt),
      JuliaLean.base.gmp.toFloat64 n = (
      toFloat .f64 n .Nearest)) ∧
  (∀ (I U : Type) (ops : IntegerInput I U) (n : I),
      JuliaLean.base.gmp.bigInteger (I := I) (U := U) ops n = (
      fromInteger ops n)) ∧
  (JuliaLean.base.gmp.bigIntegerType = (
      .type)) ∧
  (∀ (R : Type) (rationalType : BigIntType → R),
      JuliaLean.base.gmp.bigRationalType (R := R) rationalType = (
      rationalType .type))

theorem gmpConversionRoutingCorrect : GmpConversionRoutingCorrect := by
  unfold GmpConversionRoutingCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def GmpArithmeticRoutingCorrect : Prop :=
  (∀ (op : MPZ.BinaryOp) (a b c : BigInt),
      JuliaLean.base.gmp.commutative3 op a b c = (
      do
       MPZ.binaryInplace op (← MPZ.binary op a b) c)) ∧
  (∀ (op : MPZ.BinaryOp) (a b c d : BigInt),
      JuliaLean.base.gmp.commutative4 op a b c d = (
      do
       MPZ.binaryInplace op (← commutative3 op a b c) d)) ∧
  (∀ (op : MPZ.BinaryOp) (a b c d e : BigInt),
      JuliaLean.base.gmp.commutative5 op a b c d e = (
      do
       MPZ.binaryInplace op (← commutative4 op a b c d) e)) ∧
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.add x y = (
      MPZ.binary .add x y)) ∧
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.sub x y = (
      MPZ.binary .sub x y)) ∧
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.mul x y = (
      MPZ.binary .mul x y)) ∧
  (∀ (x : BigInt) (c : Clong),
      JuliaLean.base.gmp.addSigned x c = (
      if c.val < 0 then subUnsigned x (-(JInt.rem .u64 c))
      else addUnsigned x (JInt.wrap .u64 c.val))) ∧
  (∀ (x : BigInt) (c : Clong),
      JuliaLean.base.gmp.subSigned x c = (
      if c.val < 0 then addUnsigned x (-(JInt.rem .u64 c))
      else subUnsigned x (JInt.wrap .u64 c.val))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.unaryNeg x = (
      MPZ.unary .neg x)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.complement x = (
      MPZ.unary .com x)) ∧
  (∀ (x : BigInt) (c : Culong),
      JuliaLean.base.gmp.shiftLeft x c = (
      if c.val = 0 then x else MPZ.unsigned .mul2exp x c)) ∧
  (∀ (x : BigInt) (c : Culong),
      JuliaLean.base.gmp.shiftRight x c = (
      if c.val = 0 then x else MPZ.unsigned .fdivQ2exp x c)) ∧
  (∀ (x : BigInt) (c : Culong),
      JuliaLean.base.gmp.logicalShiftRight x c = (
      shiftRight x c))

theorem gmpArithmeticRoutingCorrect : GmpArithmeticRoutingCorrect := by
  unfold GmpArithmeticRoutingCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def GmpBitQueryCorrect : Prop :=
  (∀ (x : BigInt),
      JuliaLean.base.gmp.trailingZeros x = (
      do
       let c := MPZ.scan true x (JInt.wrap .u64 0)
       if c.val = -1 then throw (.domainError "`x` must be non-zero")
       pure c)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.trailingOnes x = (
      do
       let c := MPZ.scan false x (JInt.wrap .u64 0)
       if c.val = -1 then throw (.domainError "`x` must not be equal to -1")
       pure c)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.countOnes x = (
      do
       let c := MPZ.popcount x
       if c.val = -1 then throw (.domainError "`x` cannot be negative")
       pure c)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.countZeros x = (
      do
       let c := MPZ.popcount (← complement x)
       if c.val = -1 then throw (.domainError "`x` must be negative")
       pure c)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.countOnesAbs x = (
      if iszero x then JInt.wrap .i64 0 else MPZ.mpnPopcount x)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.exponent x = (
      if iszero x then .error (.domainError "cannot be zero")
      else pure (bitMagnitude x - JInt.wrap .i64 1))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.topSetBit x = (
      if isnegative x then .error (.domainError "top_set_bit")
      else if iszero x then pure (JInt.wrap .i64 0) else pure (bitMagnitude x))) ∧
  (∀ x y : BigInt, (JuliaLean.base.gmp.cmp x y).val ∈ [-1, 0, 1])


theorem gmpBitQueryCorrect : GmpBitQueryCorrect := by
  unfold GmpBitQueryCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
  intro x y
  unfold JuliaLean.base.gmp.cmp sgn
  split
  · decide
  · split <;> decide

def GmpNumberTheoryRoutingCorrect : Prop :=
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.divrem x y = (
      MPZ.tdivQr x y)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.gcdx a b = (
      let (g,s,t) := MPZ.gcdext a b
      if t.val = 0 then
        if a.val = b.val then (g,t,s)
        else if a.val.natAbs = b.val.natAbs then (g,t,neg s)
        else (g,s,t)
      else (g,s,t))) ∧
  (∀ (x : BigInt) (y : Bool),
      JuliaLean.base.gmp.powBool x y = (
      if y then x else ofInt 1)) ∧
  (∀ (x : BigInt) (y : Culong),
      JuliaLean.base.gmp.powUnsigned x y = (
      MPZ.unsigned .pow x y)) ∧
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.powBigInt x y = (
      bigintPow BigInt.val isodd y x)) ∧
  (∀ (arr : List BigInt),
      JuliaLean.base.gmp.sum arr = (
      arr.foldlM (MPZ.binaryInplace .add) (ofInt 0))) ∧
  (∀ (arr : List BigInt),
      JuliaLean.base.gmp.prod arr = (
      if arr.any iszero then pure (ofInt 0) else productSegment arr)) ∧
  (∀ xs : List BigInt, ∃ result,
    JuliaLean.base.gmp.sum xs = .ok result ∧
      result.val = xs.foldl (fun total x => total + x.val) 0) ∧
  (∀ xs : List BigInt, ∃ result,
    JuliaLean.base.gmp.prod xs = .ok result ∧
      result.val = xs.foldl (fun total x => total * x.val) 1)

def GmpComparisonAndSignCorrect : Prop :=
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.equal x y = (
      decide ((JuliaLean.base.gmp.cmp x y).val = 0))) ∧
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.less x y = (
      decide ((JuliaLean.base.gmp.cmp x y).val < 0))) ∧
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.lessEqual x y = (
      decide ((JuliaLean.base.gmp.cmp x y).val ≤ 0))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.iszero x = (
      decide (x.size.val = 0))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.isone x = (
      decide ((cmpUnsigned x (JInt.wrap .u64 1)).val = 0))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.isnegative x = (
      decide (x.size.val < 0))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.ispositive x = (
      decide (x.size.val > 0))) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.signbit x = (
      isnegative x)) ∧
  (∀ (x : BigInt) (negative : Bool),
      JuliaLean.base.gmp.flipsignBang x negative = (
      if negative then { x with val := -x.val, size := -x.size } else x)) ∧
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.flipsign x y = (
      if signbit y then neg x else x)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.sign x = (
      if isnegative x then neg (ofInt 1)
      else if ispositive x then ofInt 1 else x)) ∧
  (∀ (IO : Type) (string : BigInt → Jl String) (print : IO → String → Jl IO) (io : IO) (x : BigInt),
      JuliaLean.base.gmp.showBigInt (IO := IO) string print io x = (
      do print io (← string x)))

theorem gmpComparisonAndSignCorrect : GmpComparisonAndSignCorrect := by
  unfold GmpComparisonAndSignCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def GmpCheckedAliasCorrect : Prop :=
  (∀ (x : BigInt),
      JuliaLean.base.gmp.checkedAbs x = (
      if isnegative x then neg x else x)) ∧
  (∀ (x : BigInt),
      JuliaLean.base.gmp.checkedNeg x = (
      unaryNeg x)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedAdd a b = (
      add a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedSub a b = (
      sub a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedMul a b = (
      mul a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedDiv a b = (
      div a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedRem a b = (
      rem a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedFld a b = (
      fld a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedMod a b = (
      mod a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.checkedCld a b = (
      cld a b)) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.addWithOverflow a b = (
      do return (← add a b, false))) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.subWithOverflow a b = (
      do return (← sub a b, false))) ∧
  (∀ (a b : BigInt),
      JuliaLean.base.gmp.mulWithOverflow a b = (
      do return (← mul a b, false))) ∧
  (∀ (I R : Type) (power : BigInt → I → Jl R) (x : BigInt) (p : I),
      JuliaLean.base.gmp.checkedPow power x p = power x p) ∧
  (∀ (I R : Type) (power : I → BigInt → Jl R) (x : I) (p : BigInt),
      JuliaLean.base.gmp.checkedIntegerPow power x p = power x p) ∧
  (∀ (x p : BigInt),
      JuliaLean.base.gmp.checkedBigPow x p = (
      powBigInt x p)) ∧
  (∀ (ndigits : BigInt → Jl Clong) (x : BigInt),
      JuliaLean.base.gmp.prevpow2 ndigits x = (
      do
       if -2 ≤ x.val ∧ x.val ≤ 2 then return x
       let shift := (← ndigits x) - JInt.wrap .i64 1
       return flipsignBang (shiftLeft ONE (JInt.wrap .u64 shift.val)) (signbit x))) ∧
  (∀ (ndigits : BigInt → Jl Clong) (x : BigInt),
      JuliaLean.base.gmp.nextpow2 ndigits x = (
      do
       if (countOnesAbs x).val ≤ 1 then return x
       let shift ← ndigits x
       return flipsignBang (shiftLeft ONE (JInt.wrap .u64 shift.val)) (signbit x))) ∧
  (∀ (B : Type) (value : B → Int) (pow2 : B → Bool) (log2 : B → FV .f64) (divremFloat : Clong → FV .f64 → Jl (FV .f64 × FV .f64)) (toInt : FV .f64 → Jl Clong) (eps : FV .f64 → FV .f64) (big : B → Jl BigInt) (x : BigInt) (b : B),
      JuliaLean.base.gmp.ndigits0zpb (B := B) value pow2 log2 divremFloat toInt eps big x b = (
      do
       if value b < 2 then throw (.domainError "`b` cannot be less than 2.")
       if x.size.val = 0 then return JInt.wrap .i64 0
       if pow2 b && decide (2 ≤ value b ∧ value b ≤ 62) then
         return MPZ.sizeinbase x (JInt.wrap .i32 (value b)) false
       let n := MPZ.sizeinbase x (JInt.wrap .i32 2) false
       let lb := log2 b
       let (q,r) ← divremFloat n lb
       let iq ← toInt q
       let maxerr := mul_IEEEFloat q (eps lb)
       let one : FV .f64 := JuliaLean.Promotion.Fl.roundRat 1 1 false
       if lt_IEEEFloat (sub_IEEEFloat r one) maxerr then
         let power ← bigintPow (fun x : Clong => x.val) (fun x => decide (x.val%2 = 1)) iq (← big b)
         return if x.val.natAbs ≥ power.val.toNat then iq+JInt.wrap .i64 1 else iq
       else if lt_IEEEFloat (sub_IEEEFloat lb r) maxerr then
         let power ← bigintPow (fun x : Clong => x.val) (fun x => decide (x.val%2 = 1))
           (iq+JInt.wrap .i64 1) (← big b)
         return if x.val.natAbs ≥ power.val.toNat then iq+JInt.wrap .i64 2 else iq+JInt.wrap .i64 1
       else return iq+JInt.wrap .i64 1)) ∧
  (∀ (D : Type) (getOrInsert : (Unit → Jl BigInt) → D → BigInt → Jl (BigInt × D)) (x : BigInt) (stackdict : D),
      JuliaLean.base.gmp.deepcopyInternal (D := D) getOrInsert x stackdict = (
      getOrInsert (fun _ => MPZ.unary .set x) stackdict x)) ∧
  (∀ (x : BigInt) (n : Culong),
      JuliaLean.base.gmp.hashShiftBang x n = (
      MPZ.unsignedInplace .mul2exp x n))

theorem gmpCheckedAliasCorrect : GmpCheckedAliasCorrect := by
  unfold GmpCheckedAliasCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def GmpLimbViewCorrect : Prop :=
  (∀ (view : UnsafeLimbView),
      JuliaLean.base.gmp.limbViewSize view = (
      view.numBytes)) ∧
  (∀ (view : UnsafeLimbView) (i : Clong),
      JuliaLean.base.gmp.limbViewGetindex view i = (
      do
       if i.val < 1 ∨ i.val > view.numBytes.val then throw .boundsError
       let offset := view.startByte + i - JInt.wrap .i64 2
       let limbIndex := offset.val.tdiv 8 + 1
       let byteInLimb := offset.val % 8
       let limb := loadLimb view.bigint (limbIndex-1).toNat
       return JInt.wrap .u8 ((limb / 2^(8*byteInLimb.toNat) % 256 : Nat) : Int))) ∧
  (∀ (view : UnsafeLimbView) (state : Clong),
      JuliaLean.base.gmp.limbViewIterate view state = (
      do
       if state.val > view.numBytes.val then return none
       return some (← limbViewGetindex view state, state + JInt.wrap .i64 1))) ∧
  (∀ (view : UnsafeLimbView),
      JuliaLean.base.gmp.limbViewLength view = (
      view.numBytes)) ∧
  (∀ (hashIntegerSmall : Clong → Culong → Culong) (hashBytes : UnsafeLimbView → Culong → Culong) (n : BigInt) (h : Culong),
      JuliaLean.base.gmp.hashInteger hashIntegerSmall hashBytes n h = (
      if iszero n then hashIntegerSmall (JInt.wrap .i64 0) h else
        let s := n.size
        let h := JInt.wrap .u64 (Nat.xor h.val.toNat (if s.val < 0 then 1 else 0))
        let us := s.val.natAbs
        let top := loadLimb n (us-1)
        let leadingZeroBytes := (if top = 0 then 64 else 63-top.log2)/8
        let numBytes := JInt.wrap .i64 ((8*us-leadingZeroBytes : Nat) : Int)
        let view := UnsafeLimbView.mk n (JInt.wrap .i64 1) numBytes
        hashBytes view h))

theorem gmpLimbViewCorrect : GmpLimbViewCorrect := by
  unfold GmpLimbViewCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def GmpRationalSpecialValuesCorrect : Prop :=
  (∀ (x y : BigInt),
      JuliaLean.base.gmp.MPQ.rawPair x y = (
      ⟨x.alloc,x.size,x.d,y.alloc,y.size,y.d,⟨x,y⟩⟩)) ∧
  (JuliaLean.base.gmp.MPQ.rawEmpty = (
      rawPair initBigInt initBigInt)) ∧
  (∀ (xq : RawRational),
      JuliaLean.base.gmp.MPQ.syncRational xq = (
      let n := limbMagnitude (xq.numD.take xq.numSize.val.natAbs)
      let d := limbMagnitude (xq.denD.take xq.denSize.val.natAbs)
      ⟨⟨if xq.numSize.val < 0 then -(n : Int) else n, xq.numAlloc,xq.numSize,xq.numD⟩,
       ⟨if xq.denSize.val < 0 then -(d : Int) else d, xq.denAlloc,xq.denSize,xq.denD⟩⟩)) ∧
  (∀ (num den : BigInt),
      JuliaLean.base.gmp.MPQ.construct num den = (
      do
       if iszero den then
         if iszero num then throw (.argumentError "invalid rational: zero // zero")
         return setPair ⟨initBigInt,initBigInt⟩ (if signbit num then -1 else 1) 0
       let n ← MPZ.unary .set num
       let d ← MPZ.unary .set den
       canonicalize ⟨n,d⟩ n.val d.val)) ∧
  (∀ (z x : Rational),
      JuliaLean.base.gmp.MPQ.setBang z x = (
      let zq := rawRational z
      let result := setPair zq.rat x.num.val x.den.val
      syncRational (rawRational result))) ∧
  (∀ (z : Rational) (x : BigInt),
      JuliaLean.base.gmp.MPQ.setZBang z x = (
      let zq := rawRational z
      syncRational (rawRational (setPair zq.rat x.val 1)))) ∧
  (∀ (a : Rational),
      JuliaLean.base.gmp.MPQ.set a = (
      setBang ⟨initBigInt,initBigInt⟩ a)) ∧
  (∀ (a : BigInt),
      JuliaLean.base.gmp.MPQ.setZ a = (
      setZBang ⟨initBigInt,initBigInt⟩ a)) ∧
  (∀ (z : Rational) (a b : Culong),
      JuliaLean.base.gmp.MPQ.setUiBang z a b = (
      setPair z a.val b.val)) ∧
  (∀ (z : Rational) (a : Clong) (b : Culong),
      JuliaLean.base.gmp.MPQ.setSiBang z a b = (
      setPair z a.val b.val)) ∧
  (∀ (a b : Culong),
      JuliaLean.base.gmp.MPQ.setUi a b = (
      setUiBang ⟨initBigInt,initBigInt⟩ a b)) ∧
  (∀ (a : Clong) (b : Culong),
      JuliaLean.base.gmp.MPQ.setSi a b = (
      setSiBang ⟨initBigInt,initBigInt⟩ a b)) ∧
  (∀ (z x y : Rational),
      JuliaLean.base.gmp.MPQ.addBang z x y = (
      do
       if iszero x.den || iszero y.den then
         if iszero x.den && iszero y.den && (isnegative x.num != isnegative y.num) then
           throw .divideError
         return setBang z (if iszero x.den then x else y)
       arithmetic .add z x y)) ∧
  (∀ (z x y : Rational),
      JuliaLean.base.gmp.MPQ.subBang z x y = (
      do
       if iszero x.den || iszero y.den then
         if iszero x.den && iszero y.den && (isnegative x.num == isnegative y.num) then
           throw .divideError
         if iszero x.den then return setBang z x
         return setSiBang z (JInt.wrap .i64 (if signbit y.num then 1 else -1)) (JInt.wrap .u64 0)
       arithmetic .sub z x y)) ∧
  (∀ (z x y : Rational),
      JuliaLean.base.gmp.MPQ.mulBang z x y = (
      do
       if iszero x.den || iszero y.den then
         if iszero x.num || iszero y.num then throw .divideError
         return setSiBang z (JInt.wrap .i64 (if isnegative x.num != isnegative y.num then -1 else 1))
           (JInt.wrap .u64 0)
       arithmetic .mul z x y)) ∧
  (∀ (z x y : Rational),
      JuliaLean.base.gmp.MPQ.divBang z x y = (
      do
       if iszero x.den then
         if iszero y.den then throw .divideError
         if !isnegative y.num then return setBang z x
         return setSiBang z (JInt.wrap .i64 (if signbit x.num then 1 else -1)) (JInt.wrap .u64 0)
       else if iszero y.den then return setSiBang z (JInt.wrap .i64 0) (JInt.wrap .u64 1)
       else if iszero y.num then
         if iszero x.num then throw .divideError
         return setSiBang z (JInt.wrap .i64 (if signbit x.num then -1 else 1)) (JInt.wrap .u64 0)
       arithmetic .div z x y)) ∧
  (∀ (op : Arithmetic) (z x y : Rational),
      JuliaLean.base.gmp.MPQ.binaryBang op z x y = (
      match op with
      | .add => addBang z x y
      | .sub => subBang z x y
      | .mul => mulBang z x y
      | .div => divBang z x y)) ∧
  (∀ (op : Arithmetic) (x y : Rational),
      JuliaLean.base.gmp.MPQ.binaryInplace op x y = (
      binaryBang op x x y)) ∧
  (∀ (op : Arithmetic) (x y : Rational),
      JuliaLean.base.gmp.MPQ.binary op x y = (
      binaryBang op ⟨initBigInt,initBigInt⟩ x y))

theorem gmpRationalSpecialValuesCorrect : GmpRationalSpecialValuesCorrect := by
  unfold GmpRationalSpecialValuesCorrect
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

end LegacyRetired

open JuliaLean.Registry

def entriesLegacyRetired : List Entry := MemSafetyRetired.entries ++ [
  { id := "bignumscov-gmp-bootstrap", juliaFile := "base/gmp.jl"
    juliaFns := ["version", "major_version", "bits_per_limb", "BigInt(; nbits)", "__init__", "gmpz", "sizeinbase"]
    statement := "GMP setup reports version mismatches by limb compatibility, BigInt construction returns the initialized allocation, and primitive observations return their primitive value."
    source := "base/gmp.jl:39-169"
    status := .proven, prop := ``LegacyRetired.GmpBootstrapCorrect, thm := some ``LegacyRetired.gmpBootstrapCorrect },
  { id := "bignumscov-gmp-mpz-mutation", juliaFile := "base/gmp.jl"
    juliaFns := ["init!", "init2!", "realloc2!", "generated MPZ unary/binary mutators", "fac_ui!", "powm!"]
    statement := "Every generated MPZ allocating and aliasing wrapper calls its selected primitive with the source argument order and returns the destination object."
    source := "base/gmp.jl:161-253"
    status := .proven, prop := ``LegacyRetired.WrapperAllocationCorrect, thm := some ``LegacyRetired.wrapperAllocationCorrect },
  { id := "bignumscov-gmp-mpz-observers", juliaFile := "base/gmp.jl"
    juliaFns := ["popcount", "mpn_popcount", "tdiv_qr!", "gcdext!", "cmp", "get_str!", "set_str!", "export!", "limbs_write!", "tstbit"]
    statement := "MPZ observers preserve primitive results and output order; export rejects non-unit stride, grows to the digit count, and accepts only a returned count within the resized vector."
    source := "base/gmp.jl:205-290"
    status := .proven, prop := ``LegacyRetired.GmpMpzObserversCorrect, thm := some ``LegacyRetired.gmpMpzObserversCorrect },
  { id := "bignumscov-gmp-conversion-routing", juliaFile := "base/gmp.jl"
    juliaFns := ["widen", "signed", "BigInt", "Signed", "unsafe_trunc", "Float16", "Float32", "Float64", "promote_rule", "big"]
    statement := "Identity, machine-setter, float-integrality, IEEE overflow, promotion, and big-type branches route every input to the source-specified result or error."
    source := "base/gmp.jl:298-492"
    status := .proven, prop := ``LegacyRetired.GmpConversionRoutingCorrect, thm := some ``LegacyRetired.gmpConversionRoutingCorrect },
  { id := "bignumscov-gmp-arithmetic-routing", juliaFile := "base/gmp.jl"
    juliaFns := ["generated binary BigInt operators", "mixed C-long arithmetic", "unary - and ~", "<<", ">>", ">>>"]
    statement := "Generated exact arithmetic delegates to its MPZ operation, signed machine operands take the matching add/subtract branch, and zero shifts return the original object."
    source := "base/gmp.jl:494-574"
    status := .proven, prop := ``LegacyRetired.GmpArithmeticRoutingCorrect, thm := some ``LegacyRetired.gmpArithmeticRoutingCorrect },
  { id := "bignumscov-gmp-bit-query", juliaFile := "base/gmp.jl"
    juliaFns := ["trailing_zeros", "trailing_ones", "count_ones", "count_zeros", "count_ones_abs", "_bit_magnitude", "exponent", "top_set_bit", "cmp"]
    statement := "Bit scans reject GMP's -1 sentinel as documented, zero has zero absolute population count, exponent rejects zero, top_set_bit rejects negative inputs, and cmp normalization returns only -1, 0, or 1."
    source := "base/gmp.jl:576-635"
    status := .proven, prop := ``LegacyRetired.GmpBitQueryCorrect, thm := some ``LegacyRetired.gmpBitQueryCorrect  },
  { id := "bignumscov-gmp-number-theory-routing", juliaFile := "base/gmp.jl"
    juliaFns := ["divrem", "^ aliases", "gcdx", "+ varargs", "sum", "prod", "_prod", "binomial(::BigInt,::Culong)"]
    statement := "Power aliases, gcdx's compatibility swap, sums, and both product branches preserve their mathematical results for every input."
    source := "base/gmp.jl:625-728"
    status := .todo, prop := ``LegacyRetired.GmpNumberTheoryRoutingCorrect, thm := none 
    notes := "Retired JuliaLean.BigNumsCov.Gmp.gmpNumberTheoryRoutingCorrect at a2fd59b64fda5264fda1337c1534d56a17b98872; source routing ports to the installed BigInt model, but the concrete product branches and monadic sums need a proof of the old mathematical fold results." },
  { id := "bignumscov-gmp-comparison-sign", juliaFile := "base/gmp.jl"
    juliaFns := ["==", "<=", "<", "iszero", "isone", "isnegative", "ispositive", "signbit", "flipsign!", "flipsign", "sign", "show"]
    statement := "BigInt predicates use the sign of cmp or the limb count exactly, flipsign changes sign only for a negative second operand, and sign returns -1, 0, or 1."
    source := "base/gmp.jl:730-763"
    status := .proven, prop := ``LegacyRetired.GmpComparisonAndSignCorrect, thm := some ``LegacyRetired.gmpComparisonAndSignCorrect },
  { id := "bignumscov-gmp-checked-alias", juliaFile := "base/gmp.jl"
    juliaFns := ["ndigits0zpb", "_prevpow2", "_nextpow2", "checked_*", "*_with_overflow", "deepcopy_internal", "_hash_shl!"]
    statement := "Digit-count routing follows invalid/zero/power-of-two/logarithmic branches; exact checked aliases delegate unchanged and overflow tuples always report false."
    source := "base/gmp.jl:812-864"
    status := .proven, prop := ``LegacyRetired.GmpCheckedAliasCorrect, thm := some ``LegacyRetired.gmpCheckedAliasCorrect },
  { id := "bignumscov-gmp-limb-view", juliaFile := "base/gmp.jl"
    juliaFns := ["size(::UnsafeLimbView)", "getindex(::UnsafeLimbView)", "iterate(::UnsafeLimbView)", "length(::UnsafeLimbView)", "hash_integer"]
    statement := "UnsafeLimbView reports num_bytes, rejects indices outside 1:num_bytes, and terminates iteration immediately after that range."
    source := "base/gmp.jl:873-916"
    status := .proven, prop := ``LegacyRetired.GmpLimbViewCorrect, thm := some ``LegacyRetired.gmpLimbViewCorrect },
  { id := "bignumscov-gmp-rational-special", juliaFile := "base/gmp.jl"
    juliaFns := ["_MPQ", "sync_rational!", "Rational{BigInt}", "set!", "set_z!", "set_ui", "set_si", "add!", "sub!", "mul!", "div!", "generated Rational operators"]
    statement := "Rational{BigInt} construction and arithmetic follow every zero-denominator, zero-numerator, sign, finite-primitive, and DivideError branch."
    source := "base/gmp.jl:958-1115"
    status := .proven, prop := ``LegacyRetired.GmpRationalSpecialValuesCorrect, thm := some ``LegacyRetired.gmpRationalSpecialValuesCorrect }
]

end JuliaLean.Proofs.base.gmp
