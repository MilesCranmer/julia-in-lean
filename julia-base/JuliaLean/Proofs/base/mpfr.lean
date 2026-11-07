import JuliaLean.base.mpfr
import JuliaLean.Registry.Types

/-!
# Properties of `base/mpfr.jl`

BigFloat conversion, arithmetic, comparison and classification, stated by independent rational/extended-real specifications of correct rounding.
-/

namespace JuliaLean.Proofs.base.mpfr

namespace Round1

open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float

/- Independent mathematical specification helpers.  None executes an MPFR
   wrapper, invokes its rounding kernel, or supplies an expected result to it.
   Rational pairs always have positive denominators in the predicates below. -/

def RatEq (a b : Int × Nat) : Prop :=
  a.1 * (b.2 : Int) = b.1 * (a.2 : Int)

def RatLe (a b : Int × Nat) : Prop :=
  a.1 * (b.2 : Int) ≤ b.1 * (a.2 : Int)

def RatLt (a b : Int × Nat) : Prop :=
  a.1 * (b.2 : Int) < b.1 * (a.2 : Int)

def Dyadic (m e : Int) : Int × Nat :=
  if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)

def NumericEq (a b : FP) : Prop :=
  match a, b with
  | .nan _, _ | _, .nan _ => False
  | .inf sa, .inf sb => sa = sb
  | .inf _, _ | _, .inf _ => False
  | _, _ => RatEq a.toRat b.toRat

def NumericLT (a b : FP) : Prop :=
  match a, b with
  | .nan _, _ | _, .nan _ => False
  | .inf sa, .inf sb => sa = true ∧ sb = false
  | .inf sa, _ => sa = true
  | _, .inf sb => sb = false
  | _, _ => RatLt a.toRat b.toRat

def NumericLE (a b : FP) : Prop := NumericLT a b ∨ NumericEq a b

/-- The documented total order puts NaNs last and distinguishes the two zeros. -/
def TotalLT (a b : FP) : Prop :=
  (a.isnan = false ∧ b.isnan = true) ∨
  (a.isnan = false ∧ b.isnan = false ∧
    (NumericLT a b ∨
      (a.iszero = true ∧ b.iszero = true ∧ a.signbit = true ∧ b.signbit = false)))

/-- MPFR 4.2.2 src/mpfr.h:171-177, 64-bit Unix ABI. -/
def ValidPrecision (p : Int) : Prop := 1 ≤ p ∧ p ≤ (2 : Int)^63 - 257

/-- Representation consistency, allowing unused payload bits for NaN/Inf/zero
    and every equivalent dyadic encoding of a representable finite value. -/
def ValidBigFloat (x : BigFloat) : Prop :=
  ValidPrecision x.prec.val ∧
  x.sign = (pack x.prec x.value).sign ∧
  x.exp = (pack x.prec x.value).exp ∧
  x.d.length = (x.prec.val.toNat + 63) / 64 ∧
  match x.value with
  | .nan _ | .inf _ | .zero _ => True
  | .finite m e =>
      m ≠ 0 ∧ x.d = (pack x.prec x.value).d ∧
      -(2 : Int)^62 < x.exp.val ∧ x.exp.val < (2 : Int)^62 ∧
      (m.natAbs.log2 + 1 : Int) + e = x.exp.val ∧
      ∃ k f : Int, k ≠ 0 ∧ k.natAbs < 2 ^ x.prec.val.toNat ∧
        RatEq (Dyadic m e) (Dyadic k f)

/-- Exact mathematical integral value; this is a specification predicate, not
a replacement Julia conversion. -/
def FPRepresentsInteger (x : FP) (k : Int) : Prop :=
  match x with
  | .nan _ | .inf _ => False
  | .zero _ => k = 0
  | .finite m e => RatEq (Dyadic m e) (k, 1)

/-- Nearest-integer selection, expressed by minimising the exact absolute
error; ties are specified separately and no rounding implementation is called. -/
def IntegerNearest (n : Int) (d : Nat) (k : Int) : Prop :=
  0 < d ∧ ∀ j : Int, (k * (d : Int) - n).natAbs ≤ (j * (d : Int) - n).natAbs

def IntegerChoice (r : RoundingMode) (n : Int) (d : Nat) (k : Int) : Prop :=
  0 < d ∧
  match r with
  | .Down => k * (d : Int) ≤ n ∧ n < (k + 1) * (d : Int)
  | .Up => (k - 1) * (d : Int) < n ∧ n ≤ k * (d : Int)
  | .ToZero =>
      k.natAbs * d ≤ n.natAbs ∧ n.natAbs < (k.natAbs + 1) * d ∧
      (n = 0 → k = 0) ∧ (n < 0 → k ≤ 0) ∧ (0 < n → 0 ≤ k)
  | .FromZero =>
      (n = 0 ∧ k = 0) ∨
      (0 < n ∧ (k - 1) * (d : Int) < n ∧ n ≤ k * (d : Int)) ∨
      (n < 0 ∧ k * (d : Int) ≤ n ∧ n < (k + 1) * (d : Int))
  | .Nearest => IntegerNearest n d k ∧
      (∀ j : Int, j ≠ k → IntegerNearest n d j → k % 2 = 0)
  | .NearestTiesAway => IntegerNearest n d k ∧
      (∀ j : Int, IntegerNearest n d j → j.natAbs ≤ k.natAbs)
  | .NearestTiesUp => IntegerNearest n d k ∧
      (∀ j : Int, IntegerNearest n d j → j ≤ k)

def RawIntegerChoice (r : Mode) (n : Int) (d : Nat) (k : Int) : Prop :=
  match r with
  | .nearest => IntegerChoice .Nearest n d k
  | .toZero => IntegerChoice .ToZero n d k
  | .up => IntegerChoice .Up n d k
  | .down => IntegerChoice .Down n d k
  | .fromZero => IntegerChoice .FromZero n d k
  | .faithful => IntegerChoice .Down n d k ∨ IntegerChoice .Up n d k

/-- Exactly the private MPFR tags reachable by the public RoundingMode
conversion methods at base/mpfr.jl:58-79. MPFRRoundFaithful is an internal tag,
not a documented public Julia rounding mode. -/
def PublicRawMode (r : Mode) : Prop :=
  r = .nearest ∨ r = .toZero ∨ r = .up ∨ r = .down ∨ r = .fromZero

def BigIntRoundingOutcome (x : BigFloat) (r : RoundingMode)
    (result : Jl BigInt) : Prop :=
  match result with
  | .ok z =>
      match x.value with
      | .nan _ | .inf _ => False
      | .zero _ => z.val = 0
      | .finite m e =>
          let q := Dyadic m e
          IntegerChoice r q.1 q.2 z.val
  | .error (.inexactError _) =>
      (∃ sign, x.value = .nan sign) ∨ (∃ sign, x.value = .inf sign)
  | .error _ => False

def RawBigIntRoundingOutcome (x : BigFloat) (r : Mode)
    (result : Jl BigInt) : Prop :=
  match result with
  | .ok z =>
      match x.value with
      | .nan _ | .inf _ => False
      | .zero _ => z.val = 0
      | .finite m e =>
          let q := Dyadic m e
          RawIntegerChoice r q.1 q.2 z.val
  | .error (.inexactError _) =>
      (∃ sign, x.value = .nan sign) ∨ (∃ sign, x.value = .inf sign)
  | .error _ => False

/-- Conversion to BigInt rounds every finite BigFloat to the requested integral
value and rejects both infinities and NaNs for every mode reachable through the
public RoundingMode conversion, under the ambient nearest-mode precondition
documented for round.
Julia source: base/mpfr.jl:458-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:331-355,50-110; doc/src/base/numbers.md:171-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RoundBigIntRawCorrect : Prop :=
  ∀ (x : BigFloat) (r : Mode) (s : Context),
    ValidBigFloat x → PublicRawMode r → roundingRaw s = .nearest →
    RawBigIntRoundingOutcome x r ((roundBigInt x r).run s).1

/-- The public RoundingMode overload supports every documented integer rounding
mode, including both non-even tie rules, and errors exactly on nonfinite input,
under the documented ambient nearest-mode precondition.
Julia source: base/mpfr.jl:458-468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:25-110,331-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RoundBigIntPublicCorrect : Prop :=
  ∀ (x : BigFloat) (r : RoundingMode) (s : Context),
    ValidBigFloat x → roundingRaw s = .nearest →
    BigIntRoundingOutcome x r ((roundBigIntPublic x r).run s).1

/-- An abstract Integer result of BigFloat rounding is an exact BigInt carrying
the requested rounded integer, with InexactError for nonfinite input, under
the documented ambient nearest-mode precondition.
Julia source: base/mpfr.jl:477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:331-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RoundAbstractIntegerRawCorrect : Prop :=
  ∀ (x : BigFloat) (r : Mode) (s : Context),
    ValidBigFloat x → PublicRawMode r → roundingRaw s = .nearest →
    RawBigIntRoundingOutcome x r ((roundInteger x r).run s).1

/-- Unsafe truncation to BigInt returns the integral value toward zero on every
finite input and still returns a BigInt on inputs whose conversion is unspecified.
Julia source: base/mpfr.jl:472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/float.jl:389-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UnsafeTruncBigIntCorrect : Prop :=
  ∀ (x : BigFloat) (s : Context), ValidBigFloat x →
    ∃ z, ((unsafeTruncBigInt x).run s).1 = .ok z ∧
      match x.value with
      | .nan _ | .inf _ => True
      | .zero _ => z.val = 0
      | .finite m e =>
          let q := Dyadic m e
          IntegerChoice .ToZero q.1 q.2 z.val

/-- Bool conversion succeeds precisely for the two numeric values 0 and 1,
preserving their Boolean meaning, and rejects every other BigFloat.
Julia source: base/mpfr.jl:479-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/docs/basedocs.jl:2394-2407; base/mpfr.jl:479-483; doc/src/base/numbers.md:50-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigFloatToBoolCorrect : Prop :=
  ∀ (x : BigFloat) (s : Context), ValidBigFloat x →
    match ((toBool x).run s).1 with
    | .ok b => FPRepresentsInteger x.value (if b then 1 else 0)
    | .error (.inexactError _) =>
        ¬ FPRepresentsInteger x.value 0 ∧ ¬ FPRepresentsInteger x.value 1
    | .error _ => False

/-- The exact BigInt constructor accepts exactly finite integral BigFloats and
preserves the mathematical integer, rejecting fractional and nonfinite values.
Julia source: base/mpfr.jl:484-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/gmp.jl:64-88; base/number.jl:7-15; base/mpfr.jl:484-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigFloatToBigIntCorrect : Prop :=
  ∀ (x : BigFloat) (s : Context), ValidBigFloat x →
    match ((toBigInt x).run s).1 with
    | .ok z => FPRepresentsInteger x.value z.val
    | .error (.inexactError _) => ¬ ∃ k, FPRepresentsInteger x.value k
    | .error _ => False

def PublicMPFRMode (r : RoundingMode) : Prop :=
  r = .Nearest ∨ r = .ToZero ∨ r = .Up ∨ r = .Down ∨ r = .FromZero

/-- The five public MPFR mode conversions are mutually inverse and retain
their numerical rounding direction; the internal faithful tag has no public
RoundingMode counterpart and is rejected by that conversion. The round-based
numerical observation respects its documented ambient nearest-mode precondition.
Julia source: base/mpfr.jl:75-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ModeConversionCorrect : Prop :=
  (∀ r : RoundingMode, PublicMPFRMode r →
    ∃ m, toMPFR r = .ok m ∧ toPublic m = .ok r ∧
      ∀ (x : BigFloat) (s : Context), ValidBigFloat x →
        roundingRaw s = .nearest →
        BigIntRoundingOutcome x r ((roundBigInt x m).run s).1) ∧
  (∀ m : Mode, m ≠ .faithful →
    ∃ r, toPublic m = .ok r ∧ toMPFR r = .ok m) ∧
  (∃ message, toPublic .faithful = .error (.argumentError message))

/-- The RoundToZero conversion satisfies the complete reversible public-mode
conversion contract and preserves its independently specified numerical direction
under the documented ambient nearest-mode precondition for round.
Julia source: base/mpfr.jl:75-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ToZeroModeConversionCorrect : Prop := ModeConversionCorrect

/-- The RoundUp conversion satisfies the complete reversible public-mode
conversion contract and preserves its independently specified numerical direction
under the documented ambient nearest-mode precondition for round.
Julia source: base/mpfr.jl:75-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def UpModeConversionCorrect : Prop := ModeConversionCorrect

/-- The RoundDown conversion satisfies the complete reversible public-mode
conversion contract and preserves its independently specified numerical direction
under the documented ambient nearest-mode precondition for round.
Julia source: base/mpfr.jl:75-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def DownModeConversionCorrect : Prop := ModeConversionCorrect

/-- The RoundFromZero conversion satisfies the complete reversible public-mode
conversion contract and preserves its independently specified numerical direction
under the documented ambient nearest-mode precondition for round.
Julia source: base/mpfr.jl:75-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def FromZeroModeConversionCorrect : Prop := ModeConversionCorrect

/-- Conversion back to a public RoundingMode satisfies the complete reversible
mode contract, preserves numerical direction under the documented ambient nearest
mode for round, and rejects the internal faithful tag.
Julia source: base/mpfr.jl:75-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def PublicModeConversionCorrect : Prop := ModeConversionCorrect

/-- A public rounding update changes the global default; a currently active
lexical override retains priority, and precision and exponent limits are unaffected.
Julia source: base/mpfr.jl:252-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:190-217; doc/src/manual/integers-and-floating-point-numbers.md:632-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SetRoundingObservableCorrect : Prop :=
  ∀ (r : RoundingMode) (s : Context),
    ∃ m after, (setrounding r).run s = (.ok m, after) ∧
      toPublic after.defaultRounding = .ok r ∧
      after.scopedRounding = s.scopedRounding ∧
      (rounding.run after).1 =
        (if s.scopedRounding.isSome then (rounding.run s).1 else .ok r) ∧
      after.defaultPrecision = s.defaultPrecision ∧
      after.scopedPrecision = s.scopedPrecision ∧
      after.emin = s.emin ∧ after.emax = s.emax

/-- The public setter updates the global rounding default observably through the
getter, retaining lexical override priority and preserving precision/exponent limits.
Julia source: base/mpfr.jl:252-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:190-217; doc/src/manual/integers-and-floating-point-numbers.md:632-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SetRoundingUpdateCorrect : Prop := SetRoundingObservableCorrect

/-- The reference is the public setter/getter program printed in the docstring,
with the finally restoration specified by the public implementation. It is a
specification program; the subject remains the source-mirrored withRounding. -/
def DocumentedRoundingScope {A : Type} (action : M A) (r : RoundingMode) : M A := do
  let old ← rounding
  let _ ← setrounding r
  let outcome ← tryCatch (do let value ← action; pure (.ok value))
    (fun error => pure (.error error))
  let _ ← setrounding old
  liftJl outcome

/-- Scoped setrounding has the documented saved-mode/set/callback/restore
behaviour for arbitrary callbacks, including their return value or exception
and the entire final context (so outer scopes cannot hide a changed default),
from every initial mode reachable through public rounding settings.
Julia source: base/mpfr.jl:254-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:226-245; doc/src/manual/integers-and-floating-point-numbers.md:632-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ScopedSetRoundingDocumentedCorrect : Prop :=
  ∀ (A : Type) (action : M A) (r : RoundingMode) (s : Context),
    roundingRaw s ≠ .faithful →
    (withRounding action r).run s = (DocumentedRoundingScope action r).run s

/-- The finite coordinate used to compare distances to IEEE infinity is one ulp
beyond the largest finite value, exactly as the public rounding documentation
specifies. NaNs are never passed to this specification helper. -/
def IEEMetricValue {T : FTy} (x : FV T) : Int × Nat :=
  if x.isinf then
    let magnitude : Int := Int.ofNat (2 ^ (T.fmt.bias + 1))
    (if x.signbit then -magnitude else magnitude, 1)
  else x.toRat

def RatDistance (a b : Int × Nat) : Int × Nat :=
  (Int.ofNat ((a.1 * (b.2 : Int) - b.1 * (a.2 : Int)).natAbs), a.2 * b.2)

def IEELeExact {T : FTy} (x : FV T) (q : Int × Nat) : Prop :=
  if x.isinf then x.signbit = true else RatLe x.toRat q

def ExactLeIEE {T : FTy} (q : Int × Nat) (x : FV T) : Prop :=
  if x.isinf then x.signbit = false else RatLe q x.toRat

def IEELe {T : FTy} (x y : FV T) : Prop :=
  if x.isinf then
    x.signbit = true ∨ (y.isinf = true ∧ y.signbit = false)
  else if y.isinf then y.signbit = false else RatLe x.toRat y.toRat

def IEEFloor {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  IEELeExact z q ∧
    ∀ y : FV T, y.isnan = false → IEELeExact y q → IEELe y z

def IEECeil {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  ExactLeIEE q z ∧
    ∀ y : FV T, y.isnan = false → ExactLeIEE q y → IEELe z y

def IEENearest {T : FTy} (q : Int × Nat) (z : FV T) : Prop :=
  ∀ y : FV T, y.isnan = false →
    RatLe (RatDistance q (IEEMetricValue z)) (RatDistance q (IEEMetricValue y))

def IEEFiniteChoice {T : FTy} (r : RoundingMode) (q : Int × Nat)
    (negative : Bool) (z : FV T) : Prop :=
  z.isnan = false ∧ z.signbit = negative ∧ 0 < q.2 ∧
  match r with
  | .Down => IEEFloor q z
  | .Up => IEECeil q z
  | .ToZero => if negative then IEECeil q z else IEEFloor q z
  | .FromZero => if negative then IEEFloor q z else IEECeil q z
  | .Nearest => IEENearest q z ∧
      (∀ y : FV T, y.isnan = false → IEENearest q y →
        ¬ RatEq (IEEMetricValue y) (IEEMetricValue z) → z.toBits % 2 = 0)
  | .NearestTiesAway => IEENearest q z ∧
      (∀ y : FV T, y.isnan = false → IEENearest q y →
        RatLe (RatDistance (0, 1) (IEEMetricValue y))
          (RatDistance (0, 1) (IEEMetricValue z)))
  | .NearestTiesUp => IEENearest q z ∧
      (∀ y : FV T, y.isnan = false → IEENearest q y → IEELe y z)

def IEEEConversion {T : FTy} (r : RoundingMode) (x : FP) (z : FV T) : Prop :=
  match x with
  | .nan _ => z.isnan = true
  | .inf negative => z.isinf = true ∧ z.signbit = negative
  | .zero negative => z.iszero = true ∧ z.signbit = negative
  | .finite m e => IEEFiniteChoice r (Dyadic m e) (decide (m < 0)) z

def RawIEEEConversion {T : FTy} (r : Mode) (x : FP) (z : FV T) : Prop :=
  match r with
  | .nearest => IEEEConversion .Nearest x z
  | .toZero => IEEEConversion .ToZero x z
  | .up => IEEEConversion .Up x z
  | .down => IEEEConversion .Down x z
  | .fromZero => IEEEConversion .FromZero x z
  | .faithful => IEEEConversion .Down x z ∨ IEEEConversion .Up x z

/-- Float16 conversion chooses the correct IEEE neighbour at every finite
magnitude, with all subnormal/overflow cases, signed zeros/infinities and NaNs.
Julia source: base/mpfr.jl:550 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:259-273; base/rounding.jl:25-110,352-355; doc/src/base/numbers.md:26-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ToFloat16RawCorrect : Prop :=
  ∀ (x : BigFloat) (r : Mode), ValidBigFloat x → PublicRawMode r →
    RawIEEEConversion r x.value (toFloat16 x r)

/-- Float32 conversion chooses the correct IEEE neighbour at every finite
magnitude, with all subnormal/overflow cases, signed zeros/infinities and NaNs.
Julia source: base/mpfr.jl:551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:259-273; base/rounding.jl:25-110,352-355; doc/src/base/numbers.md:26-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ToFloat32RawCorrect : Prop :=
  ∀ (x : BigFloat) (r : Mode), ValidBigFloat x → PublicRawMode r →
    RawIEEEConversion r x.value (toFloat32 x r)

/-- Float64 conversion chooses the correct IEEE neighbour at every finite
magnitude, with all subnormal/overflow cases, signed zeros/infinities and NaNs.
Julia source: base/mpfr.jl:552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/mpfr.jl:259-273; base/rounding.jl:25-110,352-355; doc/src/base/numbers.md:26-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ToFloat64RawCorrect : Prop :=
  ∀ (x : BigFloat) (r : Mode), ValidBigFloat x → PublicRawMode r →
    RawIEEEConversion r x.value (toFloat64 x r)

/-- The public Float16 rounding overload covers every documented mode and all
BigFloat magnitudes, including ties, subnormals, overflow, NaNs and signed zeros/infinities.
Julia source: base/mpfr.jl:553 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:25-110,264-286,352-355; doc/src/base/numbers.md:26-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ToFloat16PublicCorrect : Prop :=
  ∀ (x : BigFloat) (r : RoundingMode), ValidBigFloat x →
    IEEEConversion r x.value (toFloat16Public x r)

/-- The public Float32 rounding overload covers every documented mode and all
BigFloat magnitudes, including ties, subnormals, overflow, NaNs and signed zeros/infinities.
Julia source: base/mpfr.jl:554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:25-110,264-286,352-355; doc/src/base/numbers.md:26-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ToFloat32PublicCorrect : Prop :=
  ∀ (x : BigFloat) (r : RoundingMode), ValidBigFloat x →
    IEEEConversion r x.value (toFloat32Public x r)

/-- The public Float64 rounding overload covers every documented mode and all
BigFloat magnitudes, including ties, subnormals, overflow, NaNs and signed zeros/infinities.
Julia source: base/mpfr.jl:555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:25-110,264-286,352-355; doc/src/base/numbers.md:26-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ToFloat64PublicCorrect : Prop :=
  ∀ (x : BigFloat) (r : RoundingMode), ValidBigFloat x →
    IEEEConversion r x.value (toFloat64Public x r)

/- These are independent rational/extended-real specifications, not copies of
   the Julia functions under review. The statements below call only their
   source-mirrored definitions in JuliaLean.base.mpfr. -/

def ValidArithmeticBigInt (x : BigInt) : Prop :=
  JuliaLean.base.gmp.Valid x ∧ 0 ≤ x.alloc.val ∧ x.d.length < 2^62

def SignedLongFamily (t : IntTy) : Prop := t.signed = true ∧ t.bits ≤ 64

def IntegerFP (n : Int) : FP := if n = 0 then .zero false else .finite n 0

/-- minmax returns the two inputs in numeric total order with negative zero first, while any NaN input propagates to both results.
Julia source: base/mpfr.jl:897-901 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:576-590; base/math.jl:832-835; doc/src/base/math.md:200-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def MinmaxCorrect : Prop :=
  ∀ (x y : BigFloat), ValidBigFloat x → ValidBigFloat y →
    let result := JuliaLean.base.mpfr.minmax x y
    if x.value.isnan || y.value.isnan then
      ValidBigFloat result.1 ∧ ValidBigFloat result.2 ∧
      result.1.value.isnan = true ∧ result.2.value.isnan = true
    else
      (result = (x, y) ∨ result = (y, x)) ∧
      ¬ TotalLT result.2.value result.1.value

/-- BigFloat equality is exact numerical equality with all NaNs unequal and both zero signs equal.
Julia source: base/mpfr.jl:990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:109-126; doc/src/base/math.md:36-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigFloatEqualityCorrect : Prop :=
  ∀ (x y : BigFloat), ValidBigFloat x → ValidBigFloat y →
    (equal x y = true ↔ NumericEq x.value y.value)

/-- BigFloat <= is exact numerical less-or-equal, unordered for NaNs and equal for opposite signed zeros.
Julia source: base/mpfr.jl:991 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:447-455; doc/src/base/math.md:36-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigFloatLessEqualCorrect : Prop :=
  ∀ (x y : BigFloat), ValidBigFloat x → ValidBigFloat y →
    (lessEqual x y = true ↔ NumericLE x.value y.value)

/-- BigFloat < is exact numerical strict order, with NaNs unordered and opposite signed zeros never strictly ordered.
Julia source: base/mpfr.jl:992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:392-404; doc/src/base/math.md:36-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigFloatLessCorrect : Prop :=
  ∀ (x y : BigFloat), ValidBigFloat x → ValidBigFloat y →
    (less x y = true ↔ NumericLT x.value y.value)

/-- cmp returns exactly -1,0 or1 according to the documented total order, with NaNs last and negative floating zero below integer zero.
Julia source: base/mpfr.jl:994-997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:219-242,507-514; doc/src/base/math.md:44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigFloatBigIntCmpTotalOrder : Prop :=
  ∀ (x : BigFloat) (y : BigInt), ValidBigFloat x → ValidArithmeticBigInt y →
    let c := (cmpBigInt x y).val
    (c = -1 ∨ c = 0 ∨ c = 1) ∧
    (c = -1 ↔ TotalLT x.value (IntegerFP y.val)) ∧
    (c = 1 ↔ TotalLT (IntegerFP y.val) x.value) ∧
    (c = 0 ↔ ¬ TotalLT x.value (IntegerFP y.val) ∧ ¬ TotalLT (IntegerFP y.val) x.value)

/-- cmp returns exactly -1,0 or1 according to the documented total order, with NaNs last and negative floating zero below integer zero.
Julia source: base/mpfr.jl:998-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:219-242,507-514; doc/src/base/math.md:44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BigFloatSignedCmpTotalOrder : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (y : JInt t), ValidBigFloat x → SignedLongFamily t →
    let c := (cmpSigned x y).val
    (c = -1 ∨ c = 0 ∨ c = 1) ∧
    (c = -1 ↔ TotalLT x.value (IntegerFP y.val)) ∧
    (c = 1 ↔ TotalLT (IntegerFP y.val) x.value) ∧
    (c = 0 ↔ ¬ TotalLT x.value (IntegerFP y.val) ∧ ¬ TotalLT (IntegerFP y.val) x.value)

open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

def StateCmpResult (a b : FP) (c : Cint) : Prop :=
  (c.val = -1 ∨ c.val = 0 ∨ c.val = 1) ∧
  (c.val = -1 ↔ TotalLT a b) ∧
  (c.val = 1 ↔ TotalLT b a) ∧
  (c.val = 0 ↔ ¬ TotalLT a b ∧ ¬ TotalLT b a)

/-- Comparing a BigFloat with an unsigned C-long-compatible integer uses the documented total order.
Julia source: base/mpfr.jl:1002-1005 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CmpUnsignedTotalOrder : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (y : JInt t),
    JuliaLean.base.gmp.IsCulongMax t → ValidBigFloat x →
    StateCmpResult x.value (intValue y.val) (cmpUnsigned x y)

/-- Comparing a BigFloat with any fixed IEEE float uses the total order, including signed zeros and NaNs.
Julia source: base/mpfr.jl:1009-1013 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-511; base/operators.jl:206-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CmpIEEETotalOrder : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T), ValidBigFloat x →
    StateCmpResult x.value (ieeeValue y) (cmpIEEE x y)

/-- The reverse mixed floating-point comparison follows the same documented total order.
Julia source: base/mpfr.jl:1014 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:508-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IEEECmpTotalOrder : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat), ValidBigFloat y →
    StateCmpResult (ieeeValue x) y.value (ieeeCmp x y)

/-- Mixed BigFloat/IEEE equality is exact numeric equality, treating NaNs as unequal and the two zeros as equal.
Julia source: base/mpfr.jl:1018 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def EqualIEEEValue : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T), ValidBigFloat x →
    (equalIEEE x y = true ↔ NumericEq x.value (ieeeValue y))

/-- Reverse mixed equality compares exact values without converting the BigFloat to a lower precision.
Julia source: base/mpfr.jl:1019 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IEEEEqualValue : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat), ValidBigFloat y →
    (ieeeEqual x y = true ↔ NumericEq (ieeeValue x) y.value)

/-- Mixed strict comparison uses numeric order and is false if either operand is NaN.
Julia source: base/mpfr.jl:1023 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LessIEEEValue : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T), ValidBigFloat x →
    (lessIEEE x y = true ↔ NumericLT x.value (ieeeValue y))

/-- Reverse mixed strict comparison uses exact numeric order for every fixed IEEE format.
Julia source: base/mpfr.jl:1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IEEELessValue : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat), ValidBigFloat y →
    (ieeeLess x y = true ↔ NumericLT (ieeeValue x) y.value)

/-- Mixed non-strict comparison uses exact numeric order, including both infinities and both zeros.
Julia source: base/mpfr.jl:1028 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LessEqualIEEEValue : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T), ValidBigFloat x →
    (lessEqualIEEE x y = true ↔ NumericLE x.value (ieeeValue y))

/-- Reverse mixed non-strict comparison implements the full exact numeric order.
Julia source: base/mpfr.jl:1029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/mathematical-operations.md:229-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IEEELessEqualValue : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat), ValidBigFloat y →
    (ieeeLessEqual x y = true ↔ NumericLE (ieeeValue x) y.value)

/-- The sign bit reports the mathematical sign, including the signs of zero, infinities, and NaNs.
Julia source: base/mpfr.jl:1033 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:122-143; doc/src/manual/integers-and-floating-point-numbers.md:355-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def SignbitValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x → signbit x = x.value.signbit

/-- Isinteger recognizes exactly the finite values equal to a mathematical integer.
Julia source: base/mpfr.jl:1111-1113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:10-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsIntegerValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (isinteger x = true ↔ ∃ k : Int, NumericEq x.value (.finite k 0))

/-- Isinf recognizes exactly the two signed infinite values, excluding NaN and all finite values.
Julia source: base/mpfr.jl:1129-1131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/float.jl:710-714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsInfValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (isinf x = true ↔ NumericEq x.value (.inf false) ∨ NumericEq x.value (.inf true))

/-- Isnan recognizes exactly values outside the extended numeric ordering.
Julia source: base/mpfr.jl:1133-1135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/float.jl:695-700 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsNaNValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (isnan x = true ↔ ¬ NumericLE (.inf true) x.value ∧ ¬ NumericLE x.value (.inf false))

/-- Isfinite recognizes exactly the values strictly between the two infinities.
Julia source: base/mpfr.jl:1139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:69-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsFiniteValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (isfinite x = true ↔ NumericLT (.inf true) x.value ∧ NumericLT x.value (.inf false))

/-- Iszero recognizes both zero signs and no other numeric or nonnumeric value.
Julia source: base/mpfr.jl:1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:25-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsZeroValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (iszero x = true ↔ NumericEq x.value (.finite 0 0))

/-- Isone recognizes exactly the mathematical value one at every precision.
Julia source: base/mpfr.jl:1142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:47-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsOneValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (isone x = true ↔ NumericEq x.value (.finite 1 0))

/-- Ispositive recognizes exactly values strictly greater than zero, with zeros and NaNs excluded.
Julia source: base/mpfr.jl:1145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:146-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsPositiveValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (ispositive x = true ↔ NumericLT (.finite 0 0) x.value)

/-- Isnegative recognizes exactly values strictly less than zero, excluding negative zero and NaNs.
Julia source: base/mpfr.jl:1146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:168-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def IsNegativeValue : Prop :=
  ∀ x : BigFloat, ValidBigFloat x →
    (isnegative x = true ↔ NumericLT x.value (.finite 0 0))

/-- Typemax bounds every ordered BigFloat from above and is not a finite value.
Julia source: base/mpfr.jl:1148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:438-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TypemaxUpperBound : Prop :=
  ∀ (p : Clong) (x : BigFloat), ValidPrecision p.val → ValidBigFloat x →
    isinf (JuliaLean.base.mpfr.typemax p) = true ∧
    (x.value.isnan = false → lessEqual x (JuliaLean.base.mpfr.typemax p) = true)

/-- Typemin bounds every ordered BigFloat from below and is not a finite value.
Julia source: base/mpfr.jl:1149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/integers-and-floating-point-numbers.md:438-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def TypeminLowerBound : Prop :=
  ∀ (p : Clong) (x : BigFloat), ValidPrecision p.val → ValidBigFloat x →
    isinf (JuliaLean.base.mpfr.typemin p) = true ∧
    (x.value.isnan = false → lessEqual (JuliaLean.base.mpfr.typemin p) x = true)

/-- Public mode conversions and global/scoped BigFloat rounding have their documented numerical and observable effects.
Julia source: base/mpfr.jl:75-95,252-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:25-110,190-245,349-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def PublicRoundingControlsCorrect : Prop :=
  ModeConversionCorrect ∧ SetRoundingObservableCorrect ∧ ScopedSetRoundingDocumentedCorrect

/-- All three IEEE target formats honor mathematical rounding and special-value contracts in their public overloads.
Julia source: base/mpfr.jl:494-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/rounding.jl:25-110,264-286,352-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def AllIEEEFormatsCorrect : Prop :=
  ToFloat16RawCorrect ∧ ToFloat32RawCorrect ∧ ToFloat64RawCorrect ∧
  ToFloat16PublicCorrect ∧ ToFloat32PublicCorrect ∧ ToFloat64PublicCorrect

end Round1

/-! ## Registry -/
end JuliaLean.Proofs.base.mpfr

section
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.Proofs.base.mpfr.Round1

theorem cls_pack_sign (p : Clong) (v : FP) :
    (pack p v).sign = JInt.wrap .i32 (if v.signbit then -1 else 1) := by
  cases v <;> rfl

theorem cls_signbit (x : BigFloat) (hx : ValidBigFloat x) :
    signbit x = x.value.signbit := by
  unfold signbit
  rw [hx.2.1, cls_pack_sign]
  cases x.value.signbit <;> decide

theorem BignumscovMpfr1033V2_proven : JuliaLean.Proofs.base.mpfr.Round1.SignbitValue := by
  exact cls_signbit

theorem cls_finite_exp_lower (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    -(2 : Int)^62 < x.exp.val := by
  have hf := hx.2.2.2.2
  rw [hv] at hf
  exact hf.2.2.1

theorem cls_exp_ne_nan (e : Clong) (hl : -(2 : Int)^62 < e.val) :
    e ≠ specialNanExp := by
  intro he
  rw [he] at hl
  have hb : specialNanExp.val < -(2 : Int)^62 := by decide
  exact Int.lt_asymm hl hb

theorem cls_exp_ne_inf (e : Clong) (hl : -(2 : Int)^62 < e.val) :
    e ≠ specialInfExp := by
  intro he
  rw [he] at hl
  have hb : specialInfExp.val < -(2 : Int)^62 := by decide
  exact Int.lt_asymm hl hb

theorem cls_exp_ne_zero (e : Clong) (hl : -(2 : Int)^62 < e.val) :
    e ≠ specialZeroExp := by
  intro he
  rw [he] at hl
  have hb : specialZeroExp.val < -(2 : Int)^62 := by decide
  exact Int.lt_asymm hl hb

theorem cls_isnan (x : BigFloat) (hx : ValidBigFloat x) :
    isnan x = x.value.isnan := by
  have he := hx.2.2.1
  cases hv : x.value with
  | nan s => simp only [isnan, he, hv, pack, FP.isnan]; decide
  | inf s => simp only [isnan, he, hv, pack, FP.isnan]; decide
  | zero s => simp only [isnan, he, hv, pack, FP.isnan]; decide
  | finite m e =>
    have hn := cls_exp_ne_nan x.exp (cls_finite_exp_lower x hx m e hv)
    simpa only [isnan, hv, FP.isnan, beq_eq_false_iff_ne] using hn

theorem cls_isinf (x : BigFloat) (hx : ValidBigFloat x) :
    isinf x = x.value.isinf := by
  have he := hx.2.2.1
  cases hv : x.value with
  | nan s => simp only [isinf, he, hv, pack, FP.isinf]; decide
  | inf s => simp only [isinf, he, hv, pack, FP.isinf]; decide
  | zero s => simp only [isinf, he, hv, pack, FP.isinf]; decide
  | finite m e =>
    have hn := cls_exp_ne_inf x.exp (cls_finite_exp_lower x hx m e hv)
    simpa only [isinf, hv, FP.isinf, beq_eq_false_iff_ne] using hn

theorem cls_finite_mantissa_ne_zero (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) : m ≠ 0 := by
  have hf := hx.2.2.2.2
  rw [hv] at hf
  exact hf.1

theorem cls_iszero (x : BigFloat) (hx : ValidBigFloat x) :
    iszero x = x.value.iszero := by
  have he := hx.2.2.1
  cases hv : x.value with
  | nan s => simp only [iszero, he, hv, pack, FP.iszero]; decide
  | inf s => simp only [iszero, he, hv, pack, FP.iszero]; decide
  | zero s => simp only [iszero, he, hv, pack, FP.iszero]; decide
  | finite m e =>
    have hn := cls_exp_ne_zero x.exp (cls_finite_exp_lower x hx m e hv)
    have hm := cls_finite_mantissa_ne_zero x hx m e hv
    simpa only [iszero, hv, FP.iszero, hm, decide_false, beq_eq_false_iff_ne] using hn

theorem cls_isfinite (x : BigFloat) (hx : ValidBigFloat x) :
    isfinite x = (!x.value.isinf && !x.value.isnan) := by
  simp only [isfinite, cls_isinf x hx, cls_isnan x hx]

theorem BignumscovMpfr1129V2_proven : JuliaLean.Proofs.base.mpfr.Round1.IsInfValue := by
  intro x hx
  rw [cls_isinf x hx]
  cases x.value with
  | nan s => simp only [FP.isinf, NumericEq, Bool.false_eq_true, false_or]
  | inf s => cases s <;> simp only [NumericEq] <;> decide
  | zero s => simp only [FP.isinf, NumericEq, Bool.false_eq_true, false_or]
  | finite m e => simp only [FP.isinf, NumericEq, Bool.false_eq_true, false_or]

theorem BignumscovMpfr1133V2_proven : JuliaLean.Proofs.base.mpfr.Round1.IsNaNValue := by
  intro x hx
  rw [cls_isnan x hx]
  cases x.value with
  | nan s => simp only [FP.isnan, NumericLE, NumericLT, NumericEq, false_or, not_false_eq_true, and_self]
  | inf s => cases s <;> simp only [NumericLE, NumericLT, NumericEq] <;> decide
  | zero s => simp only [FP.isnan, NumericLE, NumericLT, NumericEq, Bool.false_eq_true, eq_self, true_or, false_or, not_true_eq_false, and_self]
  | finite m e => simp only [FP.isnan, NumericLE, NumericLT, NumericEq, Bool.false_eq_true, eq_self, true_or, false_or, not_true_eq_false, and_self]

theorem MpfrIsfiniteValue_proven : JuliaLean.Proofs.base.mpfr.Round1.IsFiniteValue := by
  intro x hx
  rw [cls_isfinite x hx]
  cases x.value with
  | nan s => simp only [FP.isinf, FP.isnan, Bool.not_false, Bool.not_true, Bool.true_and, NumericLT, Bool.false_eq_true, and_self]
  | inf s => cases s <;> simp only [NumericLT] <;> decide
  | zero s => simp only [FP.isinf, FP.isnan, Bool.not_false, Bool.true_and, NumericLT, and_self]
  | finite m e => simp only [FP.isinf, FP.isnan, Bool.not_false, Bool.true_and, NumericLT, and_self]

theorem cls_numeric_eq_zero (m e : Int) :
    NumericEq (.finite m e) (.finite 0 0) ↔ m = 0 := by
  unfold NumericEq RatEq FP.toRat
  simp only [Int.le_refl, ite_true, Int.toNat_zero, Int.pow_zero,
    Int.zero_mul, Int.mul_one]
  by_cases he : e ≥ 0
  · simp only [he, ite_true, Int.natCast_one, Int.mul_one]
    have hp : (2 : Int)^e.toNat ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
    simp only [Int.mul_eq_zero, hp, or_false]
  · simp only [he, ite_false, Int.natCast_one, Int.mul_one]

theorem BignumscovMpfr1141V2_proven : JuliaLean.Proofs.base.mpfr.Round1.IsZeroValue := by
  intro x hx
  rw [cls_iszero x hx]
  cases x.value with
  | nan s => simp only [FP.iszero, NumericEq, Bool.false_eq_true]
  | inf s => simp only [FP.iszero, NumericEq, Bool.false_eq_true]
  | zero s => cases s <;> simp only [NumericEq, RatEq] <;> decide
  | finite m e => simp only [FP.iszero, decide_eq_true_eq, cls_numeric_eq_zero]

theorem cls_numeric_zero_lt (m e : Int) :
    NumericLT (.finite 0 0) (.finite m e) ↔ 0 < m := by
  unfold NumericLT RatLt FP.toRat
  simp only [Int.le_refl, ite_true, Int.toNat_zero, Int.pow_zero,
    Int.zero_mul, Int.mul_one]
  by_cases he : e ≥ 0
  · simp only [he, ite_true, Int.natCast_one, Int.mul_one]
    have hp : (0 : Int) < 2^e.toNat := Int.pow_pos (by decide)
    simpa only [Int.zero_mul] using (Int.mul_lt_mul_right (b := 0) (c := m) hp)
  · simp only [he, ite_false, Int.natCast_one, Int.mul_one]

theorem cls_numeric_lt_zero (m e : Int) :
    NumericLT (.finite m e) (.finite 0 0) ↔ m < 0 := by
  unfold NumericLT RatLt FP.toRat
  simp only [Int.le_refl, ite_true, Int.toNat_zero, Int.pow_zero,
    Int.zero_mul, Int.mul_one]
  by_cases he : e ≥ 0
  · simp only [he, ite_true, Int.natCast_one, Int.mul_one]
    have hp : (0 : Int) < 2^e.toNat := Int.pow_pos (by decide)
    simpa only [Int.zero_mul] using (Int.mul_lt_mul_right (b := m) (c := 0) hp)
  · simp only [he, ite_false, Int.natCast_one, Int.mul_one]

theorem cls_nonneg_sign (x : BigFloat) :
    decide (x.sign.val ≥ 0) = !(signbit x) := by
  unfold signbit
  by_cases hn : x.sign.val < 0
  · have hp : ¬ x.sign.val ≥ 0 := by omega
    simp only [hn, hp, decide_true, decide_false, Bool.not_true]
  · have hp : x.sign.val ≥ 0 := by omega
    simp only [hn, hp, decide_true, decide_false, Bool.not_false]

theorem MpfrIspositiveValue_proven : JuliaLean.Proofs.base.mpfr.Round1.IsPositiveValue := by
  intro x hx
  unfold ispositive
  rw [cls_nonneg_sign, cls_signbit x hx, cls_iszero x hx, cls_isnan x hx]
  cases hv : x.value with
  | nan s => cases s <;> simp only [NumericLT, RatLt] <;> decide
  | inf s => cases s <;> simp only [NumericLT, RatLt] <;> decide
  | zero s => cases s <;> simp only [NumericLT, RatLt] <;> decide
  | finite m e =>
    have hm := cls_finite_mantissa_ne_zero x hx m e hv
    simp only [FP.signbit, FP.iszero, FP.isnan, hm, decide_false,
      Bool.not_false, Bool.and_true, Bool.not_eq_true', decide_eq_false_iff_not,
      cls_numeric_zero_lt]
    omega

theorem MpfrIsnegativeValue_proven : JuliaLean.Proofs.base.mpfr.Round1.IsNegativeValue := by
  intro x hx
  change (signbit x && !iszero x && !isnan x) = true ↔ _
  rw [cls_signbit x hx, cls_iszero x hx, cls_isnan x hx]
  cases hv : x.value with
  | nan s => cases s <;> simp only [NumericLT, RatLt] <;> decide
  | inf s => cases s <;> simp only [NumericLT, RatLt] <;> decide
  | zero s => cases s <;> simp only [NumericLT, RatLt] <;> decide
  | finite m e =>
    have hm := cls_finite_mantissa_ne_zero x hx m e hv
    simp only [FP.signbit, FP.iszero, FP.isnan, hm, decide_false,
      Bool.not_false, Bool.and_true, decide_eq_true_eq, cls_numeric_lt_zero]

theorem cls_isnan_typemax (p : Clong) :
    isnan (JuliaLean.base.mpfr.typemax p) = false := by
  change (specialInfExp == specialNanExp) = false
  decide

theorem cls_isnan_typemin (p : Clong) :
    isnan (JuliaLean.base.mpfr.typemin p) = false := by
  change (specialInfExp == specialNanExp) = false
  decide

theorem BignumscovMpfr1148V2_proven : JuliaLean.Proofs.base.mpfr.Round1.TypemaxUpperBound := by
  intro p x hp hx
  constructor
  · change (specialInfExp == specialInfExp) = true
    decide
  · intro hn
    unfold lessEqual
    rw [cls_isnan x hx, cls_isnan_typemax]
    cases hv : x.value with
    | nan s => simp only [hv, FP.isnan] at hn; contradiction
    | inf s => cases s <;> simp only [FP.isnan, JuliaLean.base.mpfr.typemax, pack, compareFP] <;> rfl
    | zero s => simp only [FP.isnan, JuliaLean.base.mpfr.typemax, pack, compareFP] <;> rfl
    | finite m e => simp only [FP.isnan, JuliaLean.base.mpfr.typemax, pack, compareFP] <;> rfl

theorem BignumscovMpfr1149V2_proven : JuliaLean.Proofs.base.mpfr.Round1.TypeminLowerBound := by
  intro p x hp hx
  constructor
  · change (specialInfExp == specialInfExp) = true
    decide
  · intro hn
    unfold lessEqual
    rw [cls_isnan x hx, cls_isnan_typemin]
    cases hv : x.value with
    | nan s => simp only [hv, FP.isnan] at hn; contradiction
    | inf s => cases s <;> simp only [FP.isnan, JuliaLean.base.mpfr.typemin, pack, compareFP] <;> decide
    | zero s => simp only [FP.isnan, JuliaLean.base.mpfr.typemin, pack, compareFP] <;> decide
    | finite m e => simp only [FP.isnan, JuliaLean.base.mpfr.typemin, pack, compareFP] <;> decide

theorem cls_emod_zero_iff_integer (n d : Int) :
    n % d = 0 ↔ ∃ k : Int, n = k * d := by
  constructor
  · intro h
    exact ⟨n / d, (Int.ediv_mul_cancel_of_emod_eq_zero h).symm⟩
  · intro ⟨k, hk⟩
    apply Int.emod_eq_zero_of_dvd
    exact ⟨k, by rw [hk, Int.mul_comm]⟩

theorem cls_finite_integer (m e : Int) :
    (FP.toRat (.finite m e)).1 % ((FP.toRat (.finite m e)).2 : Int) = 0 ↔
      ∃ k : Int, NumericEq (.finite m e) (.finite k 0) := by
  simp only [NumericEq, RatEq, FP.toRat, Int.le_refl, ite_true,
    Int.toNat_zero, Int.pow_zero, Int.mul_one]
  by_cases he : e ≥ 0
  · simp only [he, ite_true, Int.natCast_one, Int.mul_one]
    simpa only [Int.mul_one] using cls_emod_zero_iff_integer (m * (2 : Int)^e.toNat) 1
  · simp only [he, ite_false, Int.natCast_one, Int.mul_one]
    exact cls_emod_zero_iff_integer m ((2^(-e).toNat : Nat) : Int)

theorem MpfrIsintegerValue_proven : JuliaLean.Proofs.base.mpfr.Round1.IsIntegerValue := by
  intro x hx
  unfold isinteger
  rw [cls_isfinite x hx]
  cases x.value with
  | nan s => simp only [FP.isinf, FP.isnan, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_eq_true, eq_self, ite_true, NumericEq,
      exists_false]
  | inf s => simp only [FP.isinf, FP.isnan, Bool.not_false, Bool.not_true,
      Bool.false_and, Bool.false_eq_true, eq_self, ite_true, NumericEq,
      exists_false]
  | zero s =>
    simp only [FP.isinf, FP.isnan, Bool.not_false, Bool.true_and, Bool.not_true,
      Bool.false_eq_true, ite_false, FP.toRat, Int.zero_emod, decide_true,
      eq_self, true_iff]
    exact ⟨0, by simp [NumericEq, RatEq, FP.toRat]⟩
  | finite m e =>
    simp only [FP.isinf, FP.isnan, Bool.not_false, Bool.true_and, Bool.not_true,
      Bool.false_eq_true, ite_false, decide_eq_true_eq]
    exact cls_finite_integer m e

theorem cls_wrap_sgn (n : Int) :
    (JInt.wrap .i32 (JuliaLean.base.gmp.sgn n)).val = JuliaLean.base.gmp.sgn n := by
  unfold JuliaLean.base.gmp.sgn
  by_cases hn : n < 0
  · simp only [hn, ite_true]
    decide
  · simp only [hn, ite_false]
    by_cases hp : n > 0
    · simp only [hp, ite_true]
      decide
    · simp only [hp, ite_false]
      decide

theorem cls_sgn_zero (n : Int) : JuliaLean.base.gmp.sgn n = 0 ↔ n = 0 := by
  constructor
  · intro h
    unfold JuliaLean.base.gmp.sgn at h
    by_cases hn : n < 0
    · rw [if_pos hn] at h
      omega
    · rw [if_neg hn] at h
      by_cases hp : n > 0
      · rw [if_pos hp] at h
        omega
      · omega
  · intro h
    subst n
    rfl

theorem cls_compare_finite_one (m e : Int) :
    compareFP (.finite m e) (.finite 1 0) =
      JuliaLean.base.gmp.sgn ((FP.toRat (.finite m e)).1 -
        ((FP.toRat (.finite m e)).2 : Int)) := by
  change JuliaLean.base.gmp.sgn ((FP.toRat (.finite m e)).1 * 1 -
    1 * ((FP.toRat (.finite m e)).2 : Int)) = _
  rw [Int.mul_one, Int.one_mul]

theorem BignumscovMpfr1142V2_proven : JuliaLean.Proofs.base.mpfr.Round1.IsOneValue := by
  intro x hx
  unfold isone cmpSigned
  rw [cls_isnan x hx]
  cases hv : x.value with
  | nan s => simp only [FP.isnan, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, NumericEq]
  | inf s => cases s <;> simp only [NumericEq, RatEq] <;> decide
  | zero s => cases s <;> simp only [NumericEq, RatEq] <;> decide
  | finite m e =>
    simp only [FP.isnan, Bool.false_eq_true, ite_false, Bool.not_false,
      Bool.true_and, decide_eq_true_eq]
    change (JInt.wrap .i32 (compareFP (.finite m e) (.finite 1 0))).val = 0 ↔ _
    rw [cls_compare_finite_one, cls_wrap_sgn, cls_sgn_zero]
    change (FP.toRat (.finite m e)).1 - ((FP.toRat (.finite m e)).2 : Int) = 0 ↔
      (FP.toRat (.finite m e)).1 * 1 = 1 * ((FP.toRat (.finite m e)).2 : Int)
    rw [Int.mul_one, Int.one_mul]
    omega

theorem cls_represents_iff_numeric (v : FP) (k : Int) :
    FPRepresentsInteger v k ↔ NumericEq v (.finite k 0) := by
  cases v with
  | nan s => rfl
  | inf s => rfl
  | zero s =>
    simp only [FPRepresentsInteger, NumericEq, RatEq, FP.toRat,
      Int.le_refl, ite_true, Int.toNat_zero, Int.pow_zero, Int.natCast_one, Int.mul_one,
      Int.zero_mul]
    exact eq_comm
  | finite m e =>
    simp only [FPRepresentsInteger, NumericEq, FP.toRat, JuliaLean.Proofs.base.mpfr.Round1.Dyadic,
      Int.le_refl, ite_true, Int.toNat_zero, Int.pow_zero, Int.mul_one]

theorem cls_isinteger_represents (x : BigFloat) (hx : ValidBigFloat x) :
    isinteger x = true ↔ ∃ k : Int, FPRepresentsInteger x.value k := by
  rw [MpfrIsintegerValue_proven x hx]
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k, (cls_represents_iff_numeric x.value k).mpr hk⟩
  · intro ⟨k, hk⟩
    exact ⟨k, (cls_represents_iff_numeric x.value k).mp hk⟩

theorem cls_toRat_den_pos (v : FP) : 0 < v.toRat.2 := by
  cases v with
  | nan s => change 0 < (1 : Nat); decide
  | inf s => change 0 < (1 : Nat); decide
  | zero s => change 0 < (1 : Nat); decide
  | finite m e =>
    by_cases he : e ≥ 0
    · simpa only [FP.toRat, he, ite_true] using Nat.zero_lt_one
    · have hp : 0 < (2 : Nat)^(-e).toNat := Nat.pow_pos (by decide)
      simpa only [FP.toRat, he, ite_false] using hp

theorem cls_dyadic_den_pos (m e : Int) : 0 < (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 := by
  exact cls_toRat_den_pos (.finite m e)

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Proofs.base.mpfr.Round1

/-- A small standard context; the control counterexamples do not inspect numerical bounds. -/
def ctl_context : Context :=
  { emin := JInt.wrap .i64 (-1073741823)
    emax := JInt.wrap .i64 1073741823
    limits :=
      { eminMin := JInt.wrap .i64 (-(2^62) + 1)
        eminMax := JInt.wrap .i64 (2^62 - 1)
        emaxMin := JInt.wrap .i64 (-(2^62) + 1)
        emaxMax := JInt.wrap .i64 (2^62 - 1) } }

theorem ctl_tiesAway_setter_rejected (s : Context) :
    (setrounding .NearestTiesAway).run s = (.error (.methodError "convert"), s) := by
  rfl

theorem ctl_tiesUp_setter_rejected (s : Context) :
    (setrounding .NearestTiesUp).run s = (.error (.methodError "convert"), s) := by
  rfl

theorem BignumscovMpfr252V2_refuted :
    ¬ JuliaLean.Proofs.base.mpfr.Round1.SetRoundingObservableCorrect := by
  intro h
  obtain ⟨m, after, hr, _⟩ := h .NearestTiesAway ctl_context
  have impossible : (Except.error (JlError.methodError "convert") : Jl Mode) = .ok m :=
    congrArg Prod.fst hr
  cases impossible

theorem BignumscovMpfr253V2_refuted :
    ¬ JuliaLean.Proofs.base.mpfr.Round1.SetRoundingUpdateCorrect := by
  exact BignumscovMpfr252V2_refuted

/-- This callback uses only the global setter and the public getter. -/
def ctl_action : M RoundingMode := do
  let _ ← setrounding .Down
  rounding

theorem ctl_scope_returns_up :
    ((withRounding ctl_action .Up).run ctl_context).1 = .ok .Up := by
  rfl

theorem ctl_documented_returns_down :
    ((DocumentedRoundingScope ctl_action .Up).run ctl_context).1 = .ok .Down := by
  rfl

theorem BignumscovMpfr254V2_refuted :
    ¬ JuliaLean.Proofs.base.mpfr.Round1.ScopedSetRoundingDocumentedCorrect := by
  intro h
  have hr := h RoundingMode ctl_action .Up ctl_context (by decide)
  have impossible : (Except.ok RoundingMode.Up : Jl RoundingMode) = .ok .Down :=
    congrArg Prod.fst hr
  cases impossible

theorem BignumscovMpfrSetupRoundingV2_refuted :
    ¬ JuliaLean.Proofs.base.mpfr.Round1.PublicRoundingControlsCorrect := by
  intro h
  exact BignumscovMpfr254V2_refuted h.2.2

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Proofs.base.mpfr.Round1

theorem ri_dyadic_den_pos (m e : Int) : 0 < (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 := by
  unfold JuliaLean.Proofs.base.mpfr.Round1.Dyadic
  split
  · exact Nat.zero_lt_one
  · exact Nat.two_pow_pos _

theorem ri_round_toZero_abs (n : Int) (d : Nat) :
    (roundIntegerRat .toZero n d).natAbs = n.natAbs / d := by
  unfold roundIntegerRat increment
  by_cases hn : n < 0
  · simp only [Bool.false_and, Bool.false_eq_true, ite_false, hn, decide_true,
      ite_true, Nat.add_zero, Int.natAbs_neg, Int.natAbs_natCast]
  · simp only [Bool.false_and, Bool.false_eq_true, ite_false, hn, decide_false,
      Nat.add_zero, Int.natAbs_natCast]

theorem ri_round_toZero_sign (n : Int) (d : Nat) :
    (n = 0 → roundIntegerRat .toZero n d = 0) ∧
    (n < 0 → roundIntegerRat .toZero n d ≤ 0) ∧
    (0 < n → 0 ≤ roundIntegerRat .toZero n d) := by
  unfold roundIntegerRat increment
  simp only [Bool.false_and, Bool.false_eq_true, ite_false, Nat.add_zero]
  constructor
  · intro hn
    subst n
    simp only [Int.natAbs_zero, Nat.zero_div, Int.cast_ofNat_Int, Int.lt_irrefl,
      decide_false, Bool.false_eq_true, ite_false]
  constructor
  · intro hn
    simp only [hn, decide_true, ite_true]
    exact Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)
  · intro hn
    simp only [(show ¬ n < 0 by omega), decide_false, ite_false]
    exact Int.natCast_nonneg _

theorem ri_round_toZero_choice (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice .ToZero n d (roundIntegerRat .toZero n d) := by
  refine ⟨hd, ?_, ?_, ri_round_toZero_sign n d⟩
  · rw [ri_round_toZero_abs]
    exact Nat.div_mul_le_self n.natAbs d
  · rw [ri_round_toZero_abs, Nat.add_mul, Nat.one_mul]
    have hmod := Nat.mod_lt n.natAbs hd
    have hdecomp := Nat.div_add_mod n.natAbs d
    rw [Nat.mul_comm d (n.natAbs / d)] at hdecomp
    omega

theorem ri_unchecked_result (x : BigFloat) (r : Mode) (s : Context) :
    ((uncheckedCastBigInt x r).run s).1 =
      .ok (JuliaLean.base.gmp.ofInt (getZPrimitive s x r).value) := by
  rfl

theorem ri_nearest_bounds (n : Int) (d : Nat) (k : Int) (hd : 0 < d)
    (hlo : -(d : Int) ≤ 2 * (k * (d : Int) - n))
    (hhi : 2 * (k * (d : Int) - n) ≤ (d : Int)) : IntegerNearest n d k := by
  refine ⟨hd, ?_⟩
  intro j
  have hkabs := Int.natAbs_eq (k * (d : Int) - n)
  have hjabs := Int.natAbs_eq (j * (d : Int) - n)
  by_cases hj : j = k
  · subst j; exact Nat.le_refl _
  · by_cases hjk : j < k
    · have hmul := Int.mul_le_mul_of_nonneg_right (show j + 1 ≤ k by omega)
        (show (0 : Int) ≤ d by omega)
      rw [Int.add_mul, Int.one_mul] at hmul
      rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega
    · have hmul := Int.mul_le_mul_of_nonneg_right (show k + 1 ≤ j by omega)
        (show (0 : Int) ≤ d by omega)
      rw [Int.add_mul, Int.one_mul] at hmul
      rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega

theorem ri_nearest_unique (n : Int) (d : Nat) (k j : Int) (hd : 0 < d)
    (hlo : -(d : Int) < 2 * (k * (d : Int) - n))
    (hhi : 2 * (k * (d : Int) - n) < (d : Int))
    (hj : IntegerNearest n d j) : j = k := by
  have hjle := hj.2 k
  have hkabs := Int.natAbs_eq (k * (d : Int) - n)
  have hjabs := Int.natAbs_eq (j * (d : Int) - n)
  by_cases hjk : j = k
  · exact hjk
  · by_cases hlt : j < k
    · have hmul := Int.mul_le_mul_of_nonneg_right (show j + 1 ≤ k by omega)
        (show (0 : Int) ≤ d by omega)
      rw [Int.add_mul, Int.one_mul] at hmul
      rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega
    · have hmul := Int.mul_le_mul_of_nonneg_right (show k + 1 ≤ j by omega)
        (show (0 : Int) ≤ d by omega)
      rw [Int.add_mul, Int.one_mul] at hmul
      rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega
theorem ri_nearest_data (n : Int) (d : Nat) (hd : 0 < d) :
    let k := roundIntegerRat .nearest n d;
    -(d : Int) ≤ 2 * (k * (d : Int) - n) ∧
    2 * (k * (d : Int) - n) ≤ (d : Int) ∧
    (k % 2 = 0 ∨
      (-(d : Int) < 2 * (k * (d : Int) - n) ∧
        2 * (k * (d : Int) - n) < (d : Int))) := by
  have hmod := Nat.mod_lt n.natAbs hd
  have hdecomp := congrArg (fun a : Nat => (a : Int)) (Nat.div_add_mod n.natAbs d)
  simp only [Int.natCast_add, Int.natCast_mul] at hdecomp
  rw [Int.mul_comm (d : Int) ((n.natAbs / d : Nat) : Int)] at hdecomp
  have hpar := Nat.mod_lt (n.natAbs / d) (by decide : 0 < 2)
  unfold roundIntegerRat increment
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases hgt : 2 * (n.natAbs % d) > d <;>
    by_cases heq : 2 * (n.natAbs % d) = d <;>
    by_cases hodd : (n.natAbs / d) % 2 = 1 <;>
    by_cases hn : n < 0 <;>
    simp only [hgt, heq, hodd, hn, decide_true, decide_false,
      Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Nat.lt_irrefl,
      Bool.false_eq_true, ite_true, ite_false,
      Nat.add_zero, Int.natCast_add, Int.natCast_one, Int.neg_mul, Int.add_mul,
      Int.one_mul] <;>
    first | (have habs := Int.ofNat_natAbs_of_nonpos (show n ≤ 0 by omega); omega)
          | (have habs := Int.natAbs_of_nonneg (show 0 ≤ n by omega); omega)


theorem ri_down_data (n : Int) (d : Nat) (hd : 0 < d) :
    let k := roundIntegerRat .down n d;
    k * (d : Int) ≤ n ∧ n < (k + 1) * (d : Int) := by
  have hmod := Nat.mod_lt n.natAbs hd
  have hdecomp := congrArg (fun a : Nat => (a : Int)) (Nat.div_add_mod n.natAbs d)
  simp only [Int.natCast_add, Int.natCast_mul] at hdecomp
  rw [Int.mul_comm (d : Int) ((n.natAbs / d : Nat) : Int)] at hdecomp
  unfold roundIntegerRat increment
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases hr : n.natAbs % d = 0 <;>
    by_cases hn : n < 0 <;>
    simp only [ne_eq, hr, hn, decide_true, decide_false, not_true_eq_false, not_false_eq_true,
      Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, ite_true, ite_false,
      Nat.add_zero, Int.natCast_add, Int.natCast_one, Int.neg_mul, Int.add_mul,
      Int.one_mul] <;>
    first | (have habs := Int.ofNat_natAbs_of_nonpos (show n ≤ 0 by omega); omega)
          | (have habs := Int.natAbs_of_nonneg (show 0 ≤ n by omega); omega)

theorem ri_up_data (n : Int) (d : Nat) (hd : 0 < d) :
    let k := roundIntegerRat .up n d;
    (k - 1) * (d : Int) < n ∧ n ≤ k * (d : Int) := by
  have hmod := Nat.mod_lt n.natAbs hd
  have hdecomp := congrArg (fun a : Nat => (a : Int)) (Nat.div_add_mod n.natAbs d)
  simp only [Int.natCast_add, Int.natCast_mul] at hdecomp
  rw [Int.mul_comm (d : Int) ((n.natAbs / d : Nat) : Int)] at hdecomp
  unfold roundIntegerRat increment
  simp only [Bool.false_and, Bool.false_eq_true, ite_false]
  by_cases hr : n.natAbs % d = 0 <;>
    by_cases hn : n < 0 <;>
    simp only [ne_eq, hr, hn, decide_true, decide_false, not_true_eq_false, not_false_eq_true,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, ite_true, ite_false,
      Nat.add_zero, Int.natCast_add, Int.natCast_one, Int.neg_mul, Int.add_mul,
      Int.sub_mul, Int.one_mul] <;>
    first | (have habs := Int.ofNat_natAbs_of_nonpos (show n ≤ 0 by omega); omega)
          | (have habs := Int.natAbs_of_nonneg (show 0 ≤ n by omega); omega)

theorem ri_round_nearest_choice (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice .Nearest n d (roundIntegerRat .nearest n d) := by
  have hb := ri_nearest_data n d hd
  refine ⟨hd, ri_nearest_bounds n d _ hd hb.1 hb.2.1, ?_⟩
  intro j hj hnear
  rcases hb.2.2 with heven | hstrict
  · exact heven
  · exact False.elim (hj (ri_nearest_unique n d _ j hd hstrict.1 hstrict.2 hnear))

theorem ri_round_down_choice (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice .Down n d (roundIntegerRat .down n d) :=
  ⟨hd, ri_down_data n d hd⟩

theorem ri_round_up_choice (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice .Up n d (roundIntegerRat .up n d) :=
  ⟨hd, ri_up_data n d hd⟩

theorem ri_round_fromZero_choice (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice .FromZero n d (roundIntegerRat .fromZero n d) := by
  refine ⟨hd, ?_⟩
  by_cases hnzero : n = 0
  · left
    refine ⟨hnzero, ?_⟩
    subst n
    simp only [roundIntegerRat, increment, Int.natAbs_zero, Nat.zero_div,
      Nat.zero_mod, ne_eq, not_true_eq_false, decide_false, Bool.false_and,
      Bool.false_eq_true, ite_false, Nat.add_zero, Int.lt_irrefl, Int.natCast_zero]
  · by_cases hn : n < 0
    · right; right
      refine ⟨hn, ?_⟩
      have hk : roundIntegerRat .fromZero n d = roundIntegerRat .down n d := by
        simp only [roundIntegerRat, increment, hn, decide_true, Bool.and_true,
          Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
      rw [hk]
      exact ri_down_data n d hd
    · right; left
      refine ⟨by omega, ?_⟩
      have hk : roundIntegerRat .fromZero n d = roundIntegerRat .up n d := by
        simp only [roundIntegerRat, increment, hn, decide_false, Bool.not_false,
          Bool.and_true, Bool.false_and, Bool.false_eq_true, ite_false]
      rw [hk]
      exact ri_up_data n d hd

theorem ri_round_raw_choice (n : Int) (d : Nat) (r : Mode)
    (hd : 0 < d) (hr : PublicRawMode r) :
    RawIntegerChoice r n d (roundIntegerRat r n d) := by
  rcases hr with hr | hr | hr | hr | hr <;> subst r
  · exact ri_round_nearest_choice n d hd
  · exact ri_round_toZero_choice n d hd
  · exact ri_round_up_choice n d hd
  · exact ri_round_down_choice n d hd
  · exact ri_round_fromZero_choice n d hd

theorem ri_round_result (x : BigFloat) (r : Mode) (s : Context) :
    ((roundBigInt x r).run s).1 =
      if x.value.isnan || x.value.isinf then .error (.inexactError "round")
      else .ok (JuliaLean.base.gmp.ofInt
        (roundIntegerRat (effectiveMode s r) x.value.toRat.1 x.value.toRat.2)) := by
  rcases x with ⟨v, p, sign, exp, limbs⟩
  cases v <;> rfl

theorem ri_public_effective (r : Mode) (s : Context) (hr : PublicRawMode r) :
    effectiveMode s r = r := by
  rcases hr with hr | hr | hr | hr | hr <;> subst r <;> rfl

theorem ri_round_zero (r : Mode) : roundIntegerRat r 0 1 = 0 := by
  cases r <;> rfl

theorem BignumscovMpfr458V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.RoundBigIntRawCorrect := by
  intro x r s hx hr hs
  rw [ri_round_result]
  rw [ri_public_effective r s hr]
  cases hv : x.value with
  | nan sign =>
      simp only [FP.isnan, Bool.true_or, ite_true, RawBigIntRoundingOutcome, hv]
      exact Or.inl ⟨sign, rfl⟩
  | inf sign =>
      simp only [FP.isnan, FP.isinf, Bool.false_or, ite_true, RawBigIntRoundingOutcome, hv]
      exact Or.inr ⟨sign, rfl⟩
  | zero sign =>
      simp only [FP.isnan, FP.isinf, Bool.false_or, Bool.false_eq_true, ite_false,
        FP.toRat, ri_round_zero, RawBigIntRoundingOutcome, hv, JuliaLean.base.gmp.ofInt]
  | finite m e =>
      simp only [FP.isnan, FP.isinf, Bool.false_or, Bool.false_eq_true, ite_false,
        RawBigIntRoundingOutcome, hv, JuliaLean.base.gmp.ofInt]
      exact ri_round_raw_choice (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 r
        (ri_dyadic_den_pos m e) hr

theorem BignumscovMpfr477V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.RoundAbstractIntegerRawCorrect :=
  BignumscovMpfr458V2_proven

theorem BignumscovMpfr472V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.UnsafeTruncBigIntCorrect := by
  intro x s hx
  refine ⟨JuliaLean.base.gmp.ofInt (getZPrimitive s x .toZero).value,
    ri_unchecked_result x .toZero s, ?_⟩
  cases hv : x.value with
  | nan sign => trivial
  | inf sign => trivial
  | zero sign =>
      change (getZPrimitive s x .toZero).value = 0
      rw [getZPrimitive, hv]
      rfl
  | finite m e =>
      change IntegerChoice .ToZero (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2
        (getZPrimitive s x .toZero).value
      rw [getZPrimitive, hv]
      exact ri_round_toZero_choice (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 (ri_dyadic_den_pos m e)

theorem ri_outcome_to_public (x : BigFloat) (m : Mode) (r : RoundingMode)
    (result : Jl BigInt) (hmode : toPublic m = .ok r)
    (hout : RawBigIntRoundingOutcome x m result) : BigIntRoundingOutcome x r result := by
  cases m <;> cases hmode <;> exact hout

theorem ri_public_mode_exists (r : RoundingMode) (hr : PublicMPFRMode r) :
    ∃ m, toMPFR r = .ok m ∧ toPublic m = .ok r ∧ PublicRawMode m := by
  rcases hr with hr | hr | hr | hr | hr <;> subst r
  · exact ⟨.nearest, rfl, rfl, Or.inl rfl⟩
  · exact ⟨.toZero, rfl, rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨.up, rfl, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨.down, rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨.fromZero, rfl, rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem BignumscovMpfr75V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.ModeConversionCorrect := by
  constructor
  · intro r hr
    obtain ⟨m, hm, hback, hpublic⟩ := ri_public_mode_exists r hr
    refine ⟨m, hm, hback, ?_⟩
    intro x s hx hs
    exact ri_outcome_to_public x m r _ hback
      (BignumscovMpfr458V2_proven x m s hx hpublic hs)
  constructor
  · intro m hm
    cases m with
    | nearest => exact ⟨.Nearest, rfl, rfl⟩
    | toZero => exact ⟨.ToZero, rfl, rfl⟩
    | up => exact ⟨.Up, rfl, rfl⟩
    | down => exact ⟨.Down, rfl, rfl⟩
    | fromZero => exact ⟨.FromZero, rfl, rfl⟩
    | faithful => exact False.elim (hm rfl)
  · exact ⟨"invalid MPFR rounding mode code", rfl⟩

theorem BignumscovMpfr76V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.ToZeroModeConversionCorrect := BignumscovMpfr75V2_proven

theorem BignumscovMpfr77V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.UpModeConversionCorrect := BignumscovMpfr75V2_proven

theorem BignumscovMpfr78V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.DownModeConversionCorrect := BignumscovMpfr75V2_proven

theorem BignumscovMpfr79V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.FromZeroModeConversionCorrect := BignumscovMpfr75V2_proven

theorem BignumscovMpfr81V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.PublicModeConversionCorrect := BignumscovMpfr75V2_proven

theorem ri_toZero_exact (n : Int) (d : Nat) (h : n % (d : Int) = 0) :
    roundIntegerRat .toZero n d * (d : Int) = n := by
  have hdvd := Int.dvd_of_emod_eq_zero h
  have hnat : d ∣ n.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmul := congrArg (fun a : Nat => (a : Int)) (Nat.div_mul_cancel hnat)
  simp only [Int.natCast_mul] at hmul
  unfold roundIntegerRat increment
  simp only [Bool.false_and, Bool.false_eq_true, ite_false, Nat.add_zero]
  by_cases hn : n < 0
  · simp only [hn, decide_true, ite_true, Int.neg_mul]
    have habs := Int.ofNat_natAbs_of_nonpos (show n ≤ 0 by omega)
    omega
  · simp only [hn, decide_false, Bool.false_eq_true, ite_false]
    have habs := Int.natAbs_of_nonneg (show 0 ≤ n by omega)
    omega

theorem ri_tiesAway_error (x : BigFloat) (s : Context) :
    ((roundBigIntPublic x .NearestTiesAway).run s).1 =
      .error (.methodError "convert") := by
  rfl

theorem ri_tiesUp_error (x : BigFloat) (s : Context) :
    ((roundBigIntPublic x .NearestTiesUp).run s).1 =
      .error (.methodError "convert") := by
  rfl

def ri_zero64 : BigFloat := pack (JInt.wrap .i64 64) (.zero false)

def ri_nearestContext : Context :=
  { emin := JInt.wrap .i64 (-1073741823)
    emax := JInt.wrap .i64 1073741823
    limits :=
      { eminMin := JInt.wrap .i64 (-4611686018427387903)
        eminMax := JInt.wrap .i64 4611686018427387903
        emaxMin := JInt.wrap .i64 (-4611686018427387903)
        emaxMax := JInt.wrap .i64 4611686018427387903 } }

theorem ri_zero64_valid : ValidBigFloat ri_zero64 := by
  unfold ValidBigFloat ri_zero64
  refine ⟨?_, rfl, rfl, ?_, True.intro⟩
  · unfold ValidPrecision
    decide
  · decide

theorem BignumscovMpfr467V2_refuted :
    ¬ JuliaLean.Proofs.base.mpfr.Round1.RoundBigIntPublicCorrect := by
  intro h
  have hc := h ri_zero64 .NearestTiesAway ri_nearestContext ri_zero64_valid rfl
  change False at hc
  exact hc

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Proofs.base.mpfr.Round1

theorem ri_toBool_result (x : BigFloat) (s : Context) :
    ((JuliaLean.base.mpfr.toBool x).run s).1 =
      if iszero x then .ok false
      else if isfinite x && decide (x.value.toRat.1 = (x.value.toRat.2 : Int)) then .ok true
      else .error (.inexactError "Bool") := by
  unfold JuliaLean.base.mpfr.toBool
  cases hz : iszero x <;>
    cases ho : (isfinite x && decide (x.value.toRat.1 = (x.value.toRat.2 : Int))) <;>
    simp only [hz, ho, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem ri_one_test (x : BigFloat) (hx : ValidBigFloat x) :
    (isfinite x && decide (x.value.toRat.1 = (x.value.toRat.2 : Int))) = true ↔
      FPRepresentsInteger x.value 1 := by
  rw [cls_isfinite x hx]
  cases hv : x.value with
  | nan sign => simp only [FP.isnan, FP.isinf, Bool.not_true, Bool.not_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, FPRepresentsInteger]
  | inf sign => simp only [FP.isnan, FP.isinf, Bool.not_true, Bool.not_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, FPRepresentsInteger]
  | zero sign =>
      change (false = true ↔ (1 : Int) = 0)
      decide
  | finite m e =>
      change decide ((JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 = ((JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 : Int)) = true ↔
        RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e) (1, 1)
      simp only [decide_eq_true_eq, RatEq, Int.natCast_one, Int.mul_one, Int.one_mul]

theorem BignumscovMpfr479V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.BigFloatToBoolCorrect := by
  intro x s hx
  rw [ri_toBool_result]
  by_cases hz : iszero x = true
  · simp only [hz, ite_true]
    exact (cls_represents_iff_numeric x.value 0).mpr
      ((BignumscovMpfr1141V2_proven x hx).mp hz)
  · simp only [hz, ite_false]
    by_cases ho : (isfinite x && decide (x.value.toRat.1 = (x.value.toRat.2 : Int))) = true
    · simp only [ho, ite_true]
      exact (ri_one_test x hx).mp ho
    · simp only [ho, ite_false]
      constructor
      · intro hzero
        exact hz ((BignumscovMpfr1141V2_proven x hx).mpr
          ((cls_represents_iff_numeric x.value 0).mp hzero))
      · intro hone
        exact ho ((ri_one_test x hx).mpr hone)

theorem ri_toBigInt_result (x : BigFloat) (s : Context) :
    ((toBigInt x).run s).1 =
      if isinteger x then ((roundBigInt x .toZero).run s).1
      else .error (.inexactError "BigInt") := by
  unfold toBigInt
  cases hi : isinteger x <;>
    simp only [hi, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem BignumscovMpfr484V2_proven :
    JuliaLean.Proofs.base.mpfr.Round1.BigFloatToBigIntCorrect := by
  intro x s hx
  rw [ri_toBigInt_result]
  by_cases hi : isinteger x = true
  · simp only [hi, ite_true]
    rw [ri_round_result, ri_public_effective .toZero s (Or.inr (Or.inl rfl))]
    have hs := (cls_isinteger_represents x hx).mp hi
    cases hv : x.value with
    | nan sign =>
        obtain ⟨k, hk⟩ := hs
        simp only [hv] at hk
        exact False.elim hk
    | inf sign =>
        obtain ⟨k, hk⟩ := hs
        simp only [hv] at hk
        exact False.elim hk
    | zero sign =>
        simp only [FP.isnan, FP.isinf, Bool.false_or, Bool.false_eq_true, ite_false,
          FP.toRat, effectiveMode, ri_round_zero, JuliaLean.base.gmp.ofInt,
          FPRepresentsInteger, hv]
    | finite m e =>
        have hm : (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 % ((JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 : Int) = 0 := by
          obtain ⟨k, hk⟩ := hs
          simp only [hv] at hk
          change RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e) (k, 1) at hk
          simp only [RatEq, Int.natCast_one, Int.mul_one] at hk
          apply Int.emod_eq_zero_of_dvd
          exact ⟨k, by rw [Int.mul_comm]; exact hk⟩
        simp only [FP.isnan, FP.isinf, Bool.false_or, Bool.false_eq_true, ite_false,
          FPRepresentsInteger, hv, JuliaLean.base.gmp.ofInt]
        change (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 * 1 =
          roundIntegerRat .toZero (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 * ((JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 : Int)
        rw [Int.mul_one]
        exact (ri_toZero_exact (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).1 (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e).2 hm).symm
  · simp only [hi, ite_false]
    intro hk
    exact hi ((cls_isinteger_represents x hx).mpr hk)

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Proofs.base.mpfr.Round1

theorem ri_ieee_increment_no_discard (r : RoundingMode) (negative : Bool) (kept lost : Nat) :
    ieeeIncrement r negative kept lost 0 = false := by
  rfl

theorem ri_ieee_increment_exact (r : RoundingMode) (negative : Bool) (kept d : Nat)
    (hd : 0 < d) : ieeeIncrement r negative kept 0 d = false := by
  have hd0 : ¬ d = 0 := by omega
  have hgt : ¬ 2 * (0 : Nat) > d := by omega
  have heq : ¬ 2 * (0 : Nat) = d := by omega
  cases r <;>
    simp only [ieeeIncrement, hd0, hgt, heq, ite_false, ite_true,
      JuliaLean.base.gmp.roundsNearest, JuliaLean.base.gmp.roundsAway,
      decide_false, ne_eq, not_true_eq_false, Bool.false_or, Bool.false_and,
      Bool.and_false, Bool.false_eq_true]

/-- Numerical value of an integer significand after applying the model's IEEE
increment decision to the exact quotient and remainder. -/
def ri_ieee_integer (r : RoundingMode) (n : Int) (d : Nat) : Int :=
  let q := n.natAbs / d
  let lost := n.natAbs % d
  let negative := decide (n < 0)
  let rounded := q + if ieeeIncrement r negative q lost d then 1 else 0
  if negative then -(rounded : Int) else rounded

theorem ri_nearest_max (n : Int) (d : Nat) (k j : Int) (hd : 0 < d)
    (hlo : -(d : Int) < 2 * (k * (d : Int) - n))
    (hhi : 2 * (k * (d : Int) - n) ≤ (d : Int))
    (hj : IntegerNearest n d j) : j ≤ k := by
  by_cases hjk : j ≤ k
  · exact hjk
  · have hjle := hj.2 k
    have hkabs := Int.natAbs_eq (k * (d : Int) - n)
    have hjabs := Int.natAbs_eq (j * (d : Int) - n)
    have hmul := Int.mul_le_mul_of_nonneg_right (show k + 1 ≤ j by omega)
      (show (0 : Int) ≤ d by omega)
    rw [Int.add_mul, Int.one_mul] at hmul
    rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega

theorem ri_nearest_min (n : Int) (d : Nat) (k j : Int) (hd : 0 < d)
    (hlo : -(d : Int) ≤ 2 * (k * (d : Int) - n))
    (hhi : 2 * (k * (d : Int) - n) < (d : Int))
    (hj : IntegerNearest n d j) : k ≤ j := by
  by_cases hjk : k ≤ j
  · exact hjk
  · have hjle := hj.2 k
    have hkabs := Int.natAbs_eq (k * (d : Int) - n)
    have hjabs := Int.natAbs_eq (j * (d : Int) - n)
    have hmul := Int.mul_le_mul_of_nonneg_right (show j + 1 ≤ k by omega)
      (show (0 : Int) ≤ d by omega)
    rw [Int.add_mul, Int.one_mul] at hmul
    rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega

theorem ri_nearest_sign (n : Int) (d : Nat) (j : Int) (hj : IntegerNearest n d j) :
    (0 ≤ n → 0 ≤ j) ∧ (n ≤ 0 → j ≤ 0) := by
  have hd := hj.1
  have hj0 := hj.2 0
  simp only [Int.zero_mul, Int.zero_sub, Int.natAbs_neg] at hj0
  have hjabs := Int.natAbs_eq (j * (d : Int) - n)
  constructor
  · intro hn
    have hnabs := Int.natAbs_of_nonneg hn
    by_cases hjnonneg : 0 ≤ j
    · exact hjnonneg
    · have hmul := Int.mul_le_mul_of_nonneg_right (show j + 1 ≤ 0 by omega)
        (show (0 : Int) ≤ d by omega)
      rw [Int.add_mul, Int.one_mul, Int.zero_mul] at hmul
      rcases hjabs with hjabs | hjabs <;> omega
  · intro hn
    have hnabs := Int.ofNat_natAbs_of_nonpos hn
    by_cases hjnonpos : j ≤ 0
    · exact hjnonpos
    · have hmul := Int.mul_le_mul_of_nonneg_right (show 1 ≤ j by omega)
        (show (0 : Int) ≤ d by omega)
      rw [Int.one_mul] at hmul
      rcases hjabs with hjabs | hjabs <;> omega

theorem ri_ieee_increment_raw (r : Mode) (negative : Bool) (q lost d : Nat)
    (hd : 0 < d) (hr : PublicRawMode r) :
    ieeeIncrement (ieeeMode r) negative q lost d = increment r negative q lost d := by
  have hd0 : ¬ d = 0 := by omega
  rcases hr with hr | hr | hr | hr | hr <;> subst r <;>
    simp only [ieeeMode, ieeeIncrement, hd0, ite_false, ite_true,
      JuliaLean.base.gmp.roundsNearest, JuliaLean.base.gmp.roundsAway,
      increment, Bool.false_eq_true, Bool.true_and, Bool.false_and,
      Bool.and_true, Bool.and_false, Bool.and_comm]

theorem ri_ieee_integer_raw (r : Mode) (n : Int) (d : Nat)
    (hd : 0 < d) (hr : PublicRawMode r) :
    ri_ieee_integer (ieeeMode r) n d = roundIntegerRat r n d := by
  unfold ri_ieee_integer roundIntegerRat
  dsimp only
  rw [ri_ieee_increment_raw r _ _ _ _ hd hr] <;> rfl

theorem ri_ieee_tiesUp_data (n : Int) (d : Nat) (hd : 0 < d) :
    let k := ri_ieee_integer .NearestTiesUp n d;
    -(d : Int) < 2 * (k * (d : Int) - n) ∧
      2 * (k * (d : Int) - n) ≤ (d : Int) := by
  have hd0 : ¬ d = 0 := by omega
  have hN : RoundingMode.NearestTiesUp ≠ .Nearest := by decide
  have hA : RoundingMode.NearestTiesUp ≠ .NearestTiesAway := by decide
  have hmod := Nat.mod_lt n.natAbs hd
  have hdecomp := congrArg (fun a : Nat => (a : Int)) (Nat.div_add_mod n.natAbs d)
  simp only [Int.natCast_add, Int.natCast_mul] at hdecomp
  rw [Int.mul_comm (d : Int) ((n.natAbs / d : Nat) : Int)] at hdecomp
  unfold ri_ieee_integer ieeeIncrement
  simp only [hd0, hN, hA, ite_false, ite_true, JuliaLean.base.gmp.roundsNearest]
  by_cases hgt : 2 * (n.natAbs % d) > d <;>
    by_cases heq : 2 * (n.natAbs % d) = d <;>
    by_cases hn : n < 0 <;>
    simp only [hgt, heq, hn, decide_true, decide_false, Nat.lt_irrefl,
      Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false,
      Bool.and_true, Bool.and_false, Bool.false_eq_true, ite_true, ite_false,
      Nat.add_zero, Int.natCast_add, Int.natCast_one, Int.neg_mul, Int.add_mul,
      Int.one_mul] <;>
    first | (have habs := Int.ofNat_natAbs_of_nonpos (show n ≤ 0 by omega); omega)
          | (have habs := Int.natAbs_of_nonneg (show 0 ≤ n by omega); omega)

theorem ri_ieee_tiesAway_data (n : Int) (d : Nat) (hd : 0 < d) :
    let k := ri_ieee_integer .NearestTiesAway n d;
    -(d : Int) ≤ 2 * (k * (d : Int) - n) ∧
      2 * (k * (d : Int) - n) ≤ (d : Int) ∧
      (n < 0 → 2 * (k * (d : Int) - n) < (d : Int)) ∧
      (0 ≤ n → -(d : Int) < 2 * (k * (d : Int) - n)) := by
  by_cases hn : n < 0
  · have hneg : ¬ -n < 0 := by omega
    have heq : ri_ieee_integer .NearestTiesAway n d =
        -ri_ieee_integer .NearestTiesUp (-n) d := by
      unfold ri_ieee_integer
      simp only [hn, hneg, Int.natAbs_neg, decide_true, decide_false,
        Bool.false_eq_true, ite_true, ite_false] <;> rfl
    have hb := ri_ieee_tiesUp_data (-n) d hd
    dsimp only at hb ⊢
    rw [heq]
    simp only [Int.neg_mul, Int.sub_neg] at hb ⊢
    exact ⟨by omega, by omega, fun _ => by omega, fun h => by omega⟩
  · have heq : ri_ieee_integer .NearestTiesAway n d =
        ri_ieee_integer .NearestTiesUp n d := by
      unfold ri_ieee_integer
      simp only [hn, decide_false, Bool.false_eq_true, ite_false] <;> rfl
    have hb := ri_ieee_tiesUp_data n d hd
    dsimp only at hb ⊢
    rw [heq]
    exact ⟨Int.le_of_lt hb.1, hb.2, fun h => False.elim (hn h), fun _ => hb.1⟩

theorem ri_ieee_tiesUp_choice (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice .NearestTiesUp n d (ri_ieee_integer .NearestTiesUp n d) := by
  have hb := ri_ieee_tiesUp_data n d hd
  refine ⟨hd, ri_nearest_bounds n d _ hd (by omega) hb.2, ?_⟩
  intro j hj
  exact ri_nearest_max n d _ j hd hb.1 hb.2 hj

theorem ri_ieee_tiesAway_choice (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice .NearestTiesAway n d (ri_ieee_integer .NearestTiesAway n d) := by
  have hb := ri_ieee_tiesAway_data n d hd
  have hk := ri_nearest_bounds n d _ hd hb.1 hb.2.1
  refine ⟨hd, hk, ?_⟩
  intro j hj
  have hkabs := Int.natAbs_eq (ri_ieee_integer .NearestTiesAway n d)
  have hjabs := Int.natAbs_eq j
  by_cases hn : n < 0
  · have horder := ri_nearest_min n d _ j hd hb.1 (hb.2.2.1 hn) hj
    have hksign := (ri_nearest_sign n d _ hk).2 (by omega)
    have hjsign := (ri_nearest_sign n d _ hj).2 (by omega)
    rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega
  · have horder := ri_nearest_max n d _ j hd (hb.2.2.2 (by omega)) hb.2.1 hj
    have hksign := (ri_nearest_sign n d _ hk).1 (by omega)
    have hjsign := (ri_nearest_sign n d _ hj).1 (by omega)
    rcases hkabs with hkabs | hkabs <;> rcases hjabs with hjabs | hjabs <;> omega

theorem ri_ieee_raw_choice (r : Mode) (n : Int) (d : Nat)
    (hd : 0 < d) (hr : PublicRawMode r) :
    IntegerChoice (ieeeMode r) n d (ri_ieee_integer (ieeeMode r) n d) := by
  rw [ri_ieee_integer_raw r n d hd hr]
  have h := ri_round_raw_choice n d r hd hr
  rcases hr with hr | hr | hr | hr | hr <;> subst r <;> exact h

/-- The actual IEEE increment helper selects the mathematical integer quotient
for every one of the seven public rounding tags, including both non-even ties. -/
theorem ri_ieee_integer_choice (r : RoundingMode) (n : Int) (d : Nat) (hd : 0 < d) :
    IntegerChoice r n d (ri_ieee_integer r n d) := by
  cases r with
  | ToZero => exact ri_ieee_raw_choice .toZero n d hd (Or.inr (Or.inl rfl))
  | Down =>
      exact ri_ieee_raw_choice .down n d hd (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | Up => exact ri_ieee_raw_choice .up n d hd (Or.inr (Or.inr (Or.inl rfl)))
  | Nearest => exact ri_ieee_raw_choice .nearest n d hd (Or.inl rfl)
  | FromZero =>
      exact ri_ieee_raw_choice .fromZero n d hd (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  | NearestTiesAway => exact ri_ieee_tiesAway_choice n d hd
  | NearestTiesUp => exact ri_ieee_tiesUp_choice n d hd

/-- Quotient/remainder form of the same result, ready for the discarded-bit
numerator that occurs in the finite IEEE conversion path. -/
theorem ri_ieee_increment_choice (r : RoundingMode) (n : Int) (d kept lost : Nat)
    (hd : 0 < d) (hlost : lost < d) (hn : n.natAbs = kept * d + lost) :
    IntegerChoice r n d
      (if n < 0 then
        -((kept + if ieeeIncrement r (decide (n < 0)) kept lost d then 1 else 0 : Nat) : Int)
       else (kept + if ieeeIncrement r (decide (n < 0)) kept lost d then 1 else 0 : Nat)) := by
  have hq : n.natAbs / d = kept := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega
  have hm : n.natAbs % d = lost := by
    rw [hn, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlost]
  have h := ri_ieee_integer_choice r n d hd
  simpa only [ri_ieee_integer, hq, hm, decide_eq_true_eq] using h

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Proofs.base.mpfr.Round1

theorem ri_raw_ieee_spec {T : FTy} (r : Mode) (x : FP) (z : FV T)
    (hr : PublicRawMode r) :
    RawIEEEConversion r x z ↔ IEEEConversion (ieeeMode r) x z := by
  rcases hr with hr | hr | hr | hr | hr <;> subst r <;> rfl

/-- A proof of the generic public converter suffices for the full six-part
format contract: the five reachable raw tags are exact routes into it. -/
theorem ri_all_ieee_of_generic_public
    (h : ∀ (T : FTy) (x : BigFloat) (r : RoundingMode), ValidBigFloat x →
      IEEEConversion r x.value (toIEEE T x r)) : AllIEEEFormatsCorrect := by
  have hraw : ∀ (T : FTy) (x : BigFloat) (r : Mode), ValidBigFloat x →
      PublicRawMode r → RawIEEEConversion r x.value (toIEEERaw T x r) := by
    intro T x r hx hr
    exact (ri_raw_ieee_spec r x.value _ hr).mpr (h T x (ieeeMode r) hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x r hx hr
    exact hraw .f16 x r hx hr
  · intro x r hx hr
    exact hraw .f32 x r hx hr
  · intro x r hx hr
    exact hraw .f64 x r hx hr
  · intro x r hx
    exact h .f16 x r hx
  · intro x r hx
    exact h .f32 x r hx
  · intro x r hx
    exact h .f64 x r hx

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1

 theorem cmp_sgn_sub_eq (a b : Int) :
    JuliaLean.base.gmp.sgn (a - b) = 0 ↔ a = b := by
  unfold JuliaLean.base.gmp.sgn
  split <;> (try split) <;> omega

 theorem cmp_sgn_sub_lt (a b : Int) :
    JuliaLean.base.gmp.sgn (a - b) < 0 ↔ a < b := by
  unfold JuliaLean.base.gmp.sgn
  split <;> (try split) <;> omega

 theorem cmp_sgn_sub_le (a b : Int) :
    JuliaLean.base.gmp.sgn (a - b) ≤ 0 ↔ a < b ∨ a = b := by
  unfold JuliaLean.base.gmp.sgn
  split <;> (try split) <;> omega

 theorem cmp_sgn_sub_gt (a b : Int) :
    JuliaLean.base.gmp.sgn (a - b) > 0 ↔ b < a := by
  unfold JuliaLean.base.gmp.sgn
  split <;> (try split) <;> omega

 theorem cmp_sgn_sub_ge (a b : Int) :
    JuliaLean.base.gmp.sgn (a - b) ≥ 0 ↔ b < a ∨ a = b := by
  unfold JuliaLean.base.gmp.sgn
  split <;> (try split) <;> omega

 theorem cmp_range (x y : FP) :
    compareFP x y = -1 ∨ compareFP x y = 0 ∨ compareFP x y = 1 := by
  cases x <;> cases y <;> simp only [compareFP]
  all_goals first | omega |
    (cases ‹Bool› <;> (first | decide | (cases ‹Bool› <;> decide))) |
    (unfold JuliaLean.base.gmp.sgn; split <;> (try split) <;> omega)

 theorem cmp_wrap (x y : FP) :
    (JInt.wrap .i32 (compareFP x y)).val = compareFP x y := by
  change wrapInt .i32 (compareFP x y) = compareFP x y
  apply wrapInt_of_inRange
  have h := cmp_range x y
  change -2147483648 ≤ compareFP x y ∧ compareFP x y ≤ 2147483647
  omega

 theorem cmp_eq_semantics (x y : FP) :
    (!x.isnan && !y.isnan && decide (compareFP x y = 0)) = true ↔ NumericEq x y := by
  cases x <;> cases y
  all_goals try cases ‹Bool›
  all_goals try cases ‹Bool›
  all_goals
    simp only [FP.isnan, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, eq_self, compareFP, NumericEq, RatEq, cmp_sgn_sub_eq, decide_eq_true_eq]
  all_goals first | rfl | omega | decide +revert

 theorem cmp_lt_semantics (x y : FP) :
    (!x.isnan && !y.isnan && decide (compareFP x y < 0)) = true ↔ NumericLT x y := by
  cases x <;> cases y
  all_goals try cases ‹Bool›
  all_goals try cases ‹Bool›
  all_goals
    simp only [FP.isnan, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, eq_self, compareFP, NumericLT, RatLt, cmp_sgn_sub_lt, decide_eq_true_eq]
  all_goals first | rfl | omega | decide +revert

 theorem cmp_le_semantics (x y : FP) :
    (!x.isnan && !y.isnan && decide (compareFP x y ≤ 0)) = true ↔ NumericLE x y := by
  cases x <;> cases y
  all_goals try cases ‹Bool›
  all_goals try cases ‹Bool›
  all_goals
    simp only [FP.isnan, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, eq_self, compareFP, NumericLE, NumericLT, NumericEq, RatLt, RatEq,
      cmp_sgn_sub_le, decide_eq_true_eq, false_or]
  all_goals first | rfl | omega | decide +revert

 theorem cmp_gt_semantics (x y : FP) :
    (!x.isnan && !y.isnan && decide (compareFP x y > 0)) = true ↔ NumericLT y x := by
  cases x <;> cases y
  all_goals try cases ‹Bool›
  all_goals try cases ‹Bool›
  all_goals
    simp only [FP.isnan, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, eq_self, compareFP, NumericLT, RatLt, cmp_sgn_sub_gt, decide_eq_true_eq]
  all_goals first | rfl | omega | decide +revert

 theorem cmp_ge_semantics (x y : FP) :
    (!x.isnan && !y.isnan && decide (compareFP x y ≥ 0)) = true ↔ NumericLE y x := by
  cases x <;> cases y
  all_goals try cases ‹Bool›
  all_goals try cases ‹Bool›
  all_goals
    simp only [FP.isnan, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, eq_self, compareFP, NumericLE, NumericLT, NumericEq, RatLt, RatEq,
      cmp_sgn_sub_ge, decide_eq_true_eq, false_or]
  all_goals first | rfl | omega | decide +revert

 theorem cmp_numeric_eq_symm (x y : FP) : NumericEq x y ↔ NumericEq y x := by
  cases x <;> cases y <;> simp only [NumericEq, RatEq]
  all_goals first | rfl | exact eq_comm

 theorem cmp_numeric_lt_asymm (x y : FP) : NumericLT x y → ¬ NumericLT y x := by
  cases x <;> cases y <;> simp only [NumericLT, RatLt, false_implies]
  all_goals first | omega | (cases ‹Bool› <;> (first | decide | (cases ‹Bool› <;> decide)))

 theorem cmp_zero_numerator (x : FP) (hx : x.iszero = true) : x.toRat.1 = 0 := by
  cases x with
  | nan s => cases hx
  | inf s => cases hx
  | zero s => rfl
  | finite m e =>
      have hm : m = 0 := of_decide_eq_true hx
      subst m
      simp only [FP.toRat]
      split <;> simp only [Int.zero_mul]

 theorem cmp_zero_not_lt (x y : FP) (hx : x.iszero = true) (hy : y.iszero = true) :
    ¬ NumericLT x y := by
  have hn := cmp_zero_numerator x hx
  have hm := cmp_zero_numerator y hy
  cases x <;> cases y <;>
    simp only [FP.iszero, Bool.false_eq_true] at hx hy
  all_goals first | contradiction |
    (simp only [NumericLT, RatLt, hn, hm, Int.zero_mul, Int.lt_irrefl, not_false_eq_true])

 theorem cmp_total_asymm (x y : FP) : TotalLT x y → ¬ TotalLT y x := by
  intro hxy hyx
  unfold TotalLT at hxy hyx
  rcases hxy with hxy | hxy
  · rcases hyx with hyx | hyx
    · have h := hxy.1.symm.trans hyx.2
      cases h
    · have h := hxy.2.symm.trans hyx.1
      cases h
  · rcases hyx with hyx | hyx
    · have h := hxy.1.symm.trans hyx.2
      cases h
    · rcases hxy.2.2 with hxy | hxy
      · rcases hyx.2.2 with hyx | hyx
        · exact cmp_numeric_lt_asymm x y hxy hyx
        · exact cmp_zero_not_lt x y hyx.2.1 hyx.1 hxy
      · rcases hyx.2.2 with hyx | hyx
        · exact cmp_zero_not_lt y x hxy.2.1 hxy.1 hyx
        · have h := hxy.2.2.1.symm.trans hyx.2.2.2
          cases h

 theorem cmp_rat_den (x : FP) : 0 < x.toRat.2 := by
  cases x with
  | nan s => exact Nat.zero_lt_one
  | inf s => exact Nat.zero_lt_one
  | zero s => exact Nat.zero_lt_one
  | finite m e =>
      simp only [FP.toRat]
      split
      · exact Nat.zero_lt_one
      · exact Nat.pow_pos (by decide)

 theorem cmp_rat_eq_trans (a b c : Int × Nat) (hb : 0 < b.2)
    (hab : RatEq a b) (hbc : RatEq b c) : RatEq a c := by
  unfold RatEq at hab hbc ⊢
  apply Int.eq_of_mul_eq_mul_right (show (b.2 : Int) ≠ 0 by omega)
  calc
    (a.1 * (c.2 : Int)) * (b.2 : Int) = (a.1 * (b.2 : Int)) * (c.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (b.1 * (a.2 : Int)) * (c.2 : Int) := congrArg (fun z => z * (c.2 : Int)) hab
    _ = (b.1 * (c.2 : Int)) * (a.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (c.1 * (b.2 : Int)) * (a.2 : Int) := congrArg (fun z => z * (a.2 : Int)) hbc
    _ = (c.1 * (a.2 : Int)) * (b.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

 theorem cmp_rat_lt_right_imp (a b c : Int × Nat) (hb : 0 < b.2) (hc : 0 < c.2)
    (hbc : RatEq b c) (hab : RatLt a b) : RatLt a c := by
  unfold RatEq at hbc
  unfold RatLt at hab ⊢
  apply Int.lt_of_mul_lt_mul_right (a := (b.2 : Int)) (h := by omega)
  calc
    (a.1 * (c.2 : Int)) * (b.2 : Int) = (a.1 * (b.2 : Int)) * (c.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ < (b.1 * (a.2 : Int)) * (c.2 : Int) := Int.mul_lt_mul_of_pos_right hab (by omega)
    _ = (b.1 * (c.2 : Int)) * (a.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (c.1 * (b.2 : Int)) * (a.2 : Int) := congrArg (fun z => z * (a.2 : Int)) hbc
    _ = (c.1 * (a.2 : Int)) * (b.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

 theorem cmp_rat_lt_right (a b c : Int × Nat) (hb : 0 < b.2) (hc : 0 < c.2)
    (hbc : RatEq b c) : RatLt a b ↔ RatLt a c :=
  ⟨cmp_rat_lt_right_imp a b c hb hc hbc,
    cmp_rat_lt_right_imp a c b hc hb hbc.symm⟩

 theorem cmp_rat_eq_right (a b c : Int × Nat) (hb : 0 < b.2) (hc : 0 < c.2)
    (hbc : RatEq b c) : RatEq a b ↔ RatEq a c :=
  ⟨fun hab => cmp_rat_eq_trans a b c hb hab hbc,
    fun hac => cmp_rat_eq_trans a c b hc hac hbc.symm⟩

 theorem cmp_rat_le_iff (a b : Int × Nat) :
    RatLe a b ↔ RatLt a b ∨ RatEq a b := by
  unfold RatLe RatLt RatEq
  omega

 theorem cmp_rat_le_right (a b c : Int × Nat) (hb : 0 < b.2) (hc : 0 < c.2)
    (hbc : RatEq b c) : RatLe a b ↔ RatLe a c := by
  simp only [cmp_rat_le_iff, cmp_rat_lt_right a b c hb hc hbc,
    cmp_rat_eq_right a b c hb hc hbc]

 theorem cmp_numeric_refl (x : FP) (hx : x.isnan = false) : NumericEq x x := by
  cases x <;> simp only [FP.isnan, Bool.true_eq_false] at hx
  all_goals first | contradiction | rfl

 theorem cmp_numeric_eq_trans (x y z : FP) (hxy : NumericEq x y) (hyz : NumericEq y z) :
    NumericEq x z := by
  have hyden := cmp_rat_den y
  cases x <;> cases y <;> cases z <;> simp only [NumericEq] at hxy hyz ⊢
  all_goals first | contradiction | exact hxy.trans hyz |
    exact cmp_rat_eq_trans _ _ _ hyden hxy hyz

 theorem cmp_numeric_eq_right (x y z : FP) (hyz : NumericEq y z) :
    NumericEq x y ↔ NumericEq x z := by
  exact ⟨fun h => cmp_numeric_eq_trans x y z h hyz,
    fun h => cmp_numeric_eq_trans x z y h ((cmp_numeric_eq_symm y z).mp hyz)⟩

 theorem cmp_numeric_lt_right (x y z : FP) (hyz : NumericEq y z) :
    NumericLT x y ↔ NumericLT x z := by
  have hyden := cmp_rat_den y
  have hzden := cmp_rat_den z
  cases x <;> cases y <;> cases z <;> simp only [NumericEq, NumericLT] at hyz ⊢
  all_goals first | contradiction | rfl | (cases hyz; rfl) |
    exact cmp_rat_lt_right _ _ _ hyden hzden hyz

 theorem cmp_numeric_notnan (x y : FP) (h : NumericEq x y) :
    x.isnan = false ∧ y.isnan = false := by
  cases x <;> cases y <;> simp only [NumericEq] at h
  all_goals first | contradiction | exact ⟨rfl, rfl⟩

 theorem cmp_compareFP_right (x y z : FP) (hyz : NumericEq y z) :
    compareFP x y = compareFP x z := by
  obtain ⟨hy, hz⟩ := cmp_numeric_notnan y z hyz
  cases hx : x.isnan
  · have he1 := cmp_eq_semantics x y
    have he2 := cmp_eq_semantics x z
    have hl1 := cmp_lt_semantics x y
    have hl2 := cmp_lt_semantics x z
    simp only [hx, hy, hz, Bool.not_false, Bool.true_and, decide_eq_true_eq] at he1 he2 hl1 hl2
    have he := he1.trans ((cmp_numeric_eq_right x y z hyz).trans he2.symm)
    have hl := hl1.trans ((cmp_numeric_lt_right x y z hyz).trans hl2.symm)
    have h1 := cmp_range x y
    have h2 := cmp_range x z
    omega
  · cases x <;> simp only [FP.isnan, Bool.false_eq_true] at hx
    all_goals first | contradiction | rfl

 theorem cmp_isless_semantics_core (x y : BigFloat)
    (hcx : isnan x = x.value.isnan) (hcy : isnan y = y.value.isnan)
    (hsx : signbit x = x.value.signbit) (hsy : signbit y = y.value.signbit)
    (hx : x.value.isnan = false) (hy : y.value.isnan = false) :
    isless x y = true ↔ TotalLT x.value y.value := by
  have hl : less x y = true ↔ NumericLT x.value y.value := by
    simpa only [less, hcx, hcy] using cmp_lt_semantics x.value y.value
  cases hzx : x.value.iszero <;> cases hzy : y.value.iszero
  all_goals try
    simpa only [isless, TotalLT, hx, hy, hzx, hzy, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte, false_and, true_and, false_or, or_false,
      and_false, and_true] using hl
  have hlt := cmp_zero_not_lt x.value y.value hzx hzy
  simp only [isless, TotalLT, hx, hy, hzx, hzy, hsx, hsy, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, false_and, true_and, false_or, hlt]
  cases x.value.signbit <;> cases y.value.signbit <;> decide

 theorem cmp_ieeeValue_isnan {T : FTy} (x : FV T) : (ieeeValue x).isnan = x.isnan := by
  unfold ieeeValue
  cases hn : x.isnan <;> cases hi : x.isinf <;> cases hz : x.iszero <;> rfl

 theorem cmp_ieee_value (T : FTy) (x : BigFloat) (y : FV T)
    (hx : isnan x = false) (hy : y.isnan = false)
    (hext : NumericEq (ieeeValue (convertFloat .f64 y)) (ieeeValue y)) :
    (cmpIEEE x y).val = compareFP x.value (ieeeValue y) := by
  simp only [cmpIEEE, hx, hy, Bool.false_eq_true, ↓reduceIte]
  rw [cmp_wrap, cmp_compareFP_right x.value _ _ hext]

 def cmp_negative_zero : BigFloat := pack (JInt.wrap .i64 256) (.zero true)

 theorem cmp_negative_zero_valid : ValidBigFloat cmp_negative_zero := by
  simp only [ValidBigFloat, ValidPrecision, cmp_negative_zero, pack]
  decide

 theorem cmp_zero_total_lt : TotalLT (.zero true) (.zero false) := by
  unfold TotalLT
  exact Or.inr ⟨rfl, rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩

 theorem cmp_integer_zero_repr : JuliaLean.base.gmp.ofInt 0 =
    ⟨0, JInt.wrap .i32 0, JInt.wrap .i32 0, []⟩ := by
  have h0 : JuliaLean.base.gmp.limbsOfNat 0 = [] := by
    rw [JuliaLean.base.gmp.limbsOfNat] <;> rfl
  simp only [JuliaLean.base.gmp.ofInt, Int.natAbs_zero, h0] <;> rfl

 theorem cmp_integer_zero_valid : ValidArithmeticBigInt (JuliaLean.base.gmp.ofInt 0) := by
  rw [cmp_integer_zero_repr]
  unfold ValidArithmeticBigInt
  refine ⟨?_, ?_, ?_⟩
  · unfold JuliaLean.base.gmp.Valid
    decide
  · change (0 : Int) ≤ 0
    omega
  · change (0 : Nat) < 2 ^ 62
    exact Nat.two_pow_pos _

 theorem BignumscovMpfr994V2_refuted : ¬ JuliaLean.Proofs.base.mpfr.Round1.BigFloatBigIntCmpTotalOrder := by
  intro h
  have hc := h cmp_negative_zero (JuliaLean.base.gmp.ofInt 0)
    cmp_negative_zero_valid cmp_integer_zero_valid
  have hz : TotalLT cmp_negative_zero.value (IntegerFP (JuliaLean.base.gmp.ofInt 0).val) :=
    cmp_zero_total_lt
  have hb := hc.2.1.mpr hz
  change (0 : Int) = -1 at hb
  omega

 theorem BignumscovMpfr998V2_refuted : ¬ JuliaLean.Proofs.base.mpfr.Round1.BigFloatSignedCmpTotalOrder := by
  intro h
  have hc := h .i64 cmp_negative_zero (JInt.wrap .i64 0)
    cmp_negative_zero_valid (by unfold SignedLongFamily; decide)
  have hz : TotalLT cmp_negative_zero.value (IntegerFP (JInt.wrap .i64 0).val) :=
    cmp_zero_total_lt
  have hb := hc.2.1.mpr hz
  change (0 : Int) = -1 at hb
  omega

 theorem BignumscovMpfr1002V2_refuted : ¬ JuliaLean.Proofs.base.mpfr.Round1.CmpUnsignedTotalOrder := by
  intro h
  have hc := h .u64 cmp_negative_zero (JInt.wrap .u64 0)
    (by unfold JuliaLean.base.gmp.IsCulongMax; decide) cmp_negative_zero_valid
  have hz : TotalLT cmp_negative_zero.value (intValue (JInt.wrap .u64 0).val) :=
    cmp_zero_total_lt
  have hb := hc.2.1.mpr hz
  change (0 : Int) = -1 at hb
  omega

 theorem BignumscovMpfr1009V2_refuted : ¬ JuliaLean.Proofs.base.mpfr.Round1.CmpIEEETotalOrder := by
  intro h
  have hc := h .f64 cmp_negative_zero (Fl.zero false) cmp_negative_zero_valid
  have hz : TotalLT cmp_negative_zero.value (ieeeValue (Fl.zero false : FV .f64)) :=
    cmp_zero_total_lt
  have hb := hc.2.1.mpr hz
  change (0 : Int) = -1 at hb
  omega

 theorem BignumscovMpfr1014V2_refuted : ¬ JuliaLean.Proofs.base.mpfr.Round1.IEEECmpTotalOrder := by
  intro h
  have hc := h .f64 (Fl.zero false) cmp_negative_zero cmp_negative_zero_valid
  have hz : TotalLT cmp_negative_zero.value (ieeeValue (Fl.zero false : FV .f64)) :=
    cmp_zero_total_lt
  have hb := hc.2.2.1.mpr hz
  change (0 : Int) = 1 at hb
  omega

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1

 theorem BignumscovMpfr990V2_proven : JuliaLean.Proofs.base.mpfr.Round1.BigFloatEqualityCorrect := by
  intro x y hx hy
  simpa only [equal, cls_isnan x hx, cls_isnan y hy] using cmp_eq_semantics x.value y.value

 theorem BignumscovMpfr991V2_proven : JuliaLean.Proofs.base.mpfr.Round1.BigFloatLessEqualCorrect := by
  intro x y hx hy
  simpa only [lessEqual, cls_isnan x hx, cls_isnan y hy] using cmp_le_semantics x.value y.value

 theorem BignumscovMpfr992V2_proven : JuliaLean.Proofs.base.mpfr.Round1.BigFloatLessCorrect := by
  intro x y hx hy
  simpa only [less, cls_isnan x hx, cls_isnan y hy] using cmp_lt_semantics x.value y.value

 theorem cmp_isless_semantics (x y : BigFloat) (hx : ValidBigFloat x) (hy : ValidBigFloat y)
    (hnx : x.value.isnan = false) (hny : y.value.isnan = false) :
    isless x y = true ↔ TotalLT x.value y.value :=
  cmp_isless_semantics_core x y (cls_isnan x hx) (cls_isnan y hy)
    (cls_signbit x hx) (cls_signbit y hy) hnx hny

 theorem BignumscovMpfr897V2_proven : JuliaLean.Proofs.base.mpfr.Round1.MinmaxCorrect := by
  intro x y hx hy
  cases hnx : x.value.isnan with
  | true =>
      have hxnan : isnan x = true := (cls_isnan x hx).trans hnx
      simp only [minmax, hxnan, hnx, Bool.true_or, ↓reduceIte]
      exact ⟨hx, hx, True.intro, True.intro⟩
  | false =>
      have hxnan : isnan x = false := (cls_isnan x hx).trans hnx
      cases hny : y.value.isnan with
      | true =>
          have hynan : isnan y = true := (cls_isnan y hy).trans hny
          simp only [minmax, hxnan, hynan, hnx, hny, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte]
          exact ⟨hy, hy, True.intro, True.intro⟩
      | false =>
          have hynan : isnan y = false := (cls_isnan y hy).trans hny
          have hs := cmp_isless_semantics x y hx hy hnx hny
          cases hl : isless x y with
          | false =>
              have hnot : ¬ TotalLT x.value y.value := by
                intro h
                simpa only [hl, Bool.false_eq_true] using hs.mpr h
              simp only [minmax, hxnan, hynan, hnx, hny, hl, Bool.false_or,
                Bool.false_eq_true, ↓reduceIte]
              exact ⟨Or.inr True.intro, hnot⟩
          | true =>
              have hnot := cmp_total_asymm x.value y.value (hs.mp hl)
              simp only [minmax, hxnan, hynan, hnx, hny, hl, Bool.false_or,
                Bool.false_eq_true, ↓reduceIte]
              exact ⟨Or.inl True.intro, hnot⟩

 theorem cmp_guardedIEEE {T : FTy} (x : BigFloat) (y : FV T) (hx : ValidBigFloat x)
    (hext : y.isnan = false → NumericEq (ieeeValue (convertFloat .f64 y)) (ieeeValue y))
    (f : Int → Bool) :
    (!isnan x && !y.isnan && f (cmpIEEE x y).val) =
      (!x.value.isnan && !(ieeeValue y).isnan && f (compareFP x.value (ieeeValue y))) := by
  rw [cmp_ieeeValue_isnan, ← cls_isnan x hx]
  cases hnx : isnan x <;> cases hny : y.isnan <;>
    simp only [Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and]
  rw [cmp_ieee_value T x y hnx hny (hext hny)]

 theorem cmp_equalIEEE_of_extension {T : FTy} (x : BigFloat) (y : FV T) (hx : ValidBigFloat x)
    (hext : y.isnan = false → NumericEq (ieeeValue (convertFloat .f64 y)) (ieeeValue y)) :
    equalIEEE x y = true ↔ NumericEq x.value (ieeeValue y) := by
  unfold equalIEEE
  rw [cmp_guardedIEEE x y hx hext (fun c => decide (c = 0))]
  exact cmp_eq_semantics x.value (ieeeValue y)

 theorem cmp_ieeeEqual_of_extension {T : FTy} (x : FV T) (y : BigFloat) (hy : ValidBigFloat y)
    (hext : x.isnan = false → NumericEq (ieeeValue (convertFloat .f64 x)) (ieeeValue x)) :
    ieeeEqual x y = true ↔ NumericEq (ieeeValue x) y.value := by
  exact (cmp_equalIEEE_of_extension y x hy hext).trans (cmp_numeric_eq_symm _ _)

 theorem cmp_lessIEEE_of_extension {T : FTy} (x : BigFloat) (y : FV T) (hx : ValidBigFloat x)
    (hext : y.isnan = false → NumericEq (ieeeValue (convertFloat .f64 y)) (ieeeValue y)) :
    lessIEEE x y = true ↔ NumericLT x.value (ieeeValue y) := by
  unfold lessIEEE
  rw [cmp_guardedIEEE x y hx hext (fun c => decide (c < 0))]
  exact cmp_lt_semantics x.value (ieeeValue y)

 theorem cmp_ieeeLess_of_extension {T : FTy} (x : FV T) (y : BigFloat) (hy : ValidBigFloat y)
    (hext : x.isnan = false → NumericEq (ieeeValue (convertFloat .f64 x)) (ieeeValue x)) :
    ieeeLess x y = true ↔ NumericLT (ieeeValue x) y.value := by
  unfold ieeeLess
  rw [cmp_guardedIEEE y x hy hext (fun c => decide (c > 0))]
  exact cmp_gt_semantics y.value (ieeeValue x)

 theorem cmp_lessEqualIEEE_of_extension {T : FTy} (x : BigFloat) (y : FV T) (hx : ValidBigFloat x)
    (hext : y.isnan = false → NumericEq (ieeeValue (convertFloat .f64 y)) (ieeeValue y)) :
    lessEqualIEEE x y = true ↔ NumericLE x.value (ieeeValue y) := by
  unfold lessEqualIEEE
  rw [cmp_guardedIEEE x y hx hext (fun c => decide (c ≤ 0))]
  exact cmp_le_semantics x.value (ieeeValue y)

 theorem cmp_ieeeLessEqual_of_extension {T : FTy} (x : FV T) (y : BigFloat) (hy : ValidBigFloat y)
    (hext : x.isnan = false → NumericEq (ieeeValue (convertFloat .f64 x)) (ieeeValue x)) :
    ieeeLessEqual x y = true ↔ NumericLE (ieeeValue x) y.value := by
  unfold ieeeLessEqual
  rw [cmp_guardedIEEE y x hy hext (fun c => decide (c ≥ 0))]
  exact cmp_ge_semantics y.value (ieeeValue x)

 theorem cmp_extension_f64 (x : FV .f64) (hx : x.isnan = false) :
    NumericEq (ieeeValue (convertFloat .f64 x)) (ieeeValue x) := by
  exact cmp_numeric_refl _ ((cmp_ieeeValue_isnan x).trans hx)

 theorem cmp_equalIEEE_f64 (x : BigFloat) (y : FV .f64) (hx : ValidBigFloat x) :
    equalIEEE x y = true ↔ NumericEq x.value (ieeeValue y) :=
  cmp_equalIEEE_of_extension x y hx (cmp_extension_f64 y)

 theorem cmp_ieeeEqual_f64 (x : FV .f64) (y : BigFloat) (hy : ValidBigFloat y) :
    ieeeEqual x y = true ↔ NumericEq (ieeeValue x) y.value :=
  cmp_ieeeEqual_of_extension x y hy (cmp_extension_f64 x)

 theorem cmp_lessIEEE_f64 (x : BigFloat) (y : FV .f64) (hx : ValidBigFloat x) :
    lessIEEE x y = true ↔ NumericLT x.value (ieeeValue y) :=
  cmp_lessIEEE_of_extension x y hx (cmp_extension_f64 y)

 theorem cmp_ieeeLess_f64 (x : FV .f64) (y : BigFloat) (hy : ValidBigFloat y) :
    ieeeLess x y = true ↔ NumericLT (ieeeValue x) y.value :=
  cmp_ieeeLess_of_extension x y hy (cmp_extension_f64 x)

 theorem cmp_lessEqualIEEE_f64 (x : BigFloat) (y : FV .f64) (hx : ValidBigFloat x) :
    lessEqualIEEE x y = true ↔ NumericLE x.value (ieeeValue y) :=
  cmp_lessEqualIEEE_of_extension x y hx (cmp_extension_f64 y)

 theorem cmp_ieeeLessEqual_f64 (x : FV .f64) (y : BigFloat) (hy : ValidBigFloat y) :
    ieeeLessEqual x y = true ↔ NumericLE (ieeeValue x) y.value :=
  cmp_ieeeLessEqual_of_extension x y hy (cmp_extension_f64 x)

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1

theorem cmp_rat_le_of_eq (a b : Int × Nat) (h : RatEq a b) : RatLe a b := by
  unfold RatEq at h
  unfold RatLe
  omega

theorem cmp_iee_floor_of_rat_eq {T : FTy} (q : Int × Nat) (z : FV T)
    (hzinf : z.isinf = false) (hq : 0 < q.2) (hzden : 0 < z.toRat.2)
    (hvalue : RatEq z.toRat q) : IEEFloor q z := by
  constructor
  · simp only [IEELeExact, hzinf, Bool.false_eq_true, ite_false]
    exact cmp_rat_le_of_eq _ _ hvalue
  · intro y _ hy
    cases hyinf : y.isinf with
    | true =>
        simp only [IEELeExact, hyinf, ite_true] at hy
        simp only [IEELe, hyinf, ite_true]
        exact Or.inl hy
    | false =>
        simp only [IEELeExact, hyinf, Bool.false_eq_true, ite_false] at hy
        simp only [IEELe, hyinf, hzinf, Bool.false_eq_true, ite_false]
        exact (cmp_rat_le_right y.toRat q z.toRat hq hzden hvalue.symm).mp hy

theorem cmp_iee_ceil_of_rat_eq {T : FTy} (q : Int × Nat) (z : FV T)
    (hzinf : z.isinf = false) (hq : 0 < q.2) (hzden : 0 < z.toRat.2)
    (hvalue : RatEq z.toRat q) : IEECeil q z := by
  constructor
  · simp only [ExactLeIEE, hzinf, Bool.false_eq_true, ite_false]
    exact cmp_rat_le_of_eq _ _ hvalue.symm
  · intro y _ hy
    cases hyinf : y.isinf with
    | true =>
        simp only [ExactLeIEE, hyinf, ite_true] at hy
        simpa only [IEELe, hzinf, hyinf, Bool.false_eq_true, ite_false, ite_true] using hy
    | false =>
        simp only [ExactLeIEE, hyinf, Bool.false_eq_true, ite_false] at hy
        simp only [IEELe, hzinf, hyinf, Bool.false_eq_true, ite_false]
        have ht := cmp_rat_lt_right y.toRat q z.toRat hq hzden hvalue.symm
        unfold RatLe at hy ⊢
        unfold RatLt at ht
        omega

theorem cmp_distance_numerator_zero (a b : Int × Nat) (h : RatEq a b) :
    (RatDistance a b).1 = 0 := by
  unfold RatEq at h
  have hs : a.1 * (b.2 : Int) - b.1 * (a.2 : Int) = 0 := by omega
  simp only [RatDistance, hs, Int.natAbs_zero, Int.natCast_zero]
  rfl

theorem cmp_distance_den_pos (a b : Int × Nat) (ha : 0 < a.2) (hb : 0 < b.2) :
    0 < (RatDistance a b).2 := by
  change 0 < a.2 * b.2
  exact Nat.mul_pos ha hb

theorem cmp_iee_nearest_of_metric_eq {T : FTy} (q : Int × Nat) (z : FV T)
    (hvalue : RatEq (IEEMetricValue z) q) : IEENearest q z := by
  intro y _
  unfold RatLe
  rw [cmp_distance_numerator_zero q (IEEMetricValue z) hvalue.symm, Int.zero_mul]
  have hn : 0 ≤ (RatDistance q (IEEMetricValue y)).1 := by
    unfold RatDistance
    exact Int.natCast_nonneg _
  exact Int.mul_nonneg hn (Int.natCast_nonneg _)

theorem cmp_iee_nearest_metric_unique {T : FTy} (q : Int × Nat) (z : FV T)
    (hq : 0 < q.2) (hzden : 0 < (IEEMetricValue z).2) (hznan : z.isnan = false)
    (hvalue : RatEq (IEEMetricValue z) q) (y : FV T) (hy : IEENearest q y) :
    RatEq (IEEMetricValue y) (IEEMetricValue z) := by
  have hdpos := cmp_distance_den_pos q (IEEMetricValue z) hq hzden
  have hdposInt : (0 : Int) < (RatDistance q (IEEMetricValue z)).2 := by omega
  have hd := hy z hznan
  unfold RatLe at hd
  rw [cmp_distance_numerator_zero q (IEEMetricValue z) hvalue.symm, Int.zero_mul] at hd
  have hnum : (RatDistance q (IEEMetricValue y)).1 ≤ 0 := by
    apply (Int.mul_le_mul_right (b := (RatDistance q (IEEMetricValue y)).1)
      (c := 0) hdposInt).mp
    simpa only [Int.zero_mul] using hd
  have habs : (q.1 * ((IEEMetricValue y).2 : Int) -
      (IEEMetricValue y).1 * (q.2 : Int)).natAbs = 0 := by
    change ((q.1 * ((IEEMetricValue y).2 : Int) -
      (IEEMetricValue y).1 * (q.2 : Int)).natAbs : Int) ≤ 0 at hnum
    omega
  have hdiff := Int.natAbs_eq_zero.mp habs
  have hqy : RatEq q (IEEMetricValue y) := by
    unfold RatEq
    omega
  exact cmp_rat_eq_trans (IEEMetricValue y) q (IEEMetricValue z) hq hqy.symm hvalue.symm

theorem cmp_iee_nearest_even_of_metric_eq {T : FTy} (q : Int × Nat) (z : FV T)
    (hq : 0 < q.2) (hzden : 0 < (IEEMetricValue z).2) (hznan : z.isnan = false)
    (hvalue : RatEq (IEEMetricValue z) q) :
    IEENearest q z ∧
      (∀ y : FV T, y.isnan = false → IEENearest q y →
        ¬ RatEq (IEEMetricValue y) (IEEMetricValue z) → z.toBits % 2 = 0) := by
  constructor
  · exact cmp_iee_nearest_of_metric_eq q z hvalue
  · intro y _ hy hne
    exact False.elim (hne (cmp_iee_nearest_metric_unique q z hq hzden hznan hvalue y hy))

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1
open JuliaLean.base.gmp (limbMagnitude limbsOfNat)

theorem cls_ieee_nan_result (T : FTy) (x : BigFloat) (r : RoundingMode)
    (hx : ValidBigFloat x) (s : Bool) (hv : x.value = .nan s) :
    toIEEE T x r = Fl.ofBits (ieee754_representation_nan T s).val.toNat := by
  unfold toIEEE
  rw [cls_signbit x hx, cls_iszero x hx, cls_isinf x hx, cls_isnan x hx]
  simp only [hv, FP.signbit, FP.iszero, FP.isinf, FP.isnan, Bool.not_false,
    Bool.not_true, Bool.true_and, Bool.false_and, Bool.and_false,
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ite_false]

theorem cls_ieee_inf_result (T : FTy) (x : BigFloat) (r : RoundingMode)
    (hx : ValidBigFloat x) (s : Bool) (hv : x.value = .inf s) :
    toIEEE T x r = Fl.ofBits (ieee754_representation_inf T s).val.toNat := by
  unfold toIEEE
  rw [cls_signbit x hx, cls_iszero x hx, cls_isinf x hx, cls_isnan x hx]
  simp only [hv, FP.signbit, FP.iszero, FP.isinf, FP.isnan, Bool.not_false,
    Bool.not_true, Bool.true_and, Bool.false_and, Bool.and_false,
    Bool.false_or, Bool.or_false, Bool.false_eq_true, ite_false, ite_true]

theorem cls_ieee_zero_result (T : FTy) (x : BigFloat) (r : RoundingMode)
    (hx : ValidBigFloat x) (s : Bool) (hv : x.value = .zero s) :
    toIEEE T x r = Fl.ofBits (ieee754_representation_zero T s).val.toNat := by
  unfold toIEEE
  rw [cls_signbit x hx, cls_iszero x hx, cls_isinf x hx, cls_isnan x hx]
  simp only [hv, FP.signbit, FP.iszero, FP.isinf, FP.isnan, Bool.not_false,
    Bool.not_true, Bool.true_and, Bool.false_and, Bool.and_false,
    Bool.true_or, Bool.or_false, Bool.false_eq_true, ite_false, ite_true]

theorem cls_ieee_nan_bits (T : FTy) (s : Bool) :
    (Fl.ofBits (ieee754_representation_nan T s).val.toNat : FV T).isnan = true := by
  cases T <;> cases s <;> decide

theorem cls_ieee_inf_bits (T : FTy) (s : Bool) :
    (Fl.ofBits (ieee754_representation_inf T s).val.toNat : FV T).isinf = true ∧
    (Fl.ofBits (ieee754_representation_inf T s).val.toNat : FV T).signbit = s := by
  cases T <;> cases s <;> decide

theorem cls_ieee_zero_bits (T : FTy) (s : Bool) :
    (Fl.ofBits (ieee754_representation_zero T s).val.toNat : FV T).iszero = true ∧
    (Fl.ofBits (ieee754_representation_zero T s).val.toNat : FV T).signbit = s := by
  cases T <;> cases s <;> decide

theorem cls_ieee_nan_correct (T : FTy) (x : BigFloat) (r : RoundingMode)
    (hx : ValidBigFloat x) (s : Bool) (hv : x.value = .nan s) :
    IEEEConversion r x.value (toIEEE T x r) := by
  rw [hv]
  change (toIEEE T x r).isnan = true
  rw [cls_ieee_nan_result T x r hx s hv]
  exact cls_ieee_nan_bits T s

theorem cls_ieee_inf_correct (T : FTy) (x : BigFloat) (r : RoundingMode)
    (hx : ValidBigFloat x) (s : Bool) (hv : x.value = .inf s) :
    IEEEConversion r x.value (toIEEE T x r) := by
  rw [hv]
  change (toIEEE T x r).isinf = true ∧ (toIEEE T x r).signbit = s
  rw [cls_ieee_inf_result T x r hx s hv]
  exact cls_ieee_inf_bits T s

theorem cls_ieee_zero_correct (T : FTy) (x : BigFloat) (r : RoundingMode)
    (hx : ValidBigFloat x) (s : Bool) (hv : x.value = .zero s) :
    IEEEConversion r x.value (toIEEE T x r) := by
  rw [hv]
  change (toIEEE T x r).iszero = true ∧ (toIEEE T x r).signbit = s
  rw [cls_ieee_zero_result T x r hx s hv]
  exact cls_ieee_zero_bits T s

theorem cls_ieee_special_correct (T : FTy) (x : BigFloat) (r : RoundingMode)
    (hx : ValidBigFloat x)
    (hs : (∃ s, x.value = .nan s) ∨ (∃ s, x.value = .inf s) ∨
      (∃ s, x.value = .zero s)) :
    IEEEConversion r x.value (toIEEE T x r) := by
  rcases hs with ⟨s, hv⟩ | ⟨s, hv⟩ | ⟨s, hv⟩
  · exact cls_ieee_nan_correct T x r hx s hv
  · exact cls_ieee_inf_correct T x r hx s hv
  · exact cls_ieee_zero_correct T x r hx s hv

theorem cls_ieee_raw_special_correct (T : FTy) (x : BigFloat) (r : Mode)
    (hx : ValidBigFloat x)
    (hs : (∃ s, x.value = .nan s) ∨ (∃ s, x.value = .inf s) ∨
      (∃ s, x.value = .zero s)) :
    RawIEEEConversion r x.value (toIEEERaw T x r) := by
  cases r with
  | nearest => exact cls_ieee_special_correct T x .Nearest hx hs
  | toZero => exact cls_ieee_special_correct T x .ToZero hx hs
  | up => exact cls_ieee_special_correct T x .Up hx hs
  | down => exact cls_ieee_special_correct T x .Down hx hs
  | fromZero => exact cls_ieee_special_correct T x .FromZero hx hs
  | faithful =>
    have hh := cls_ieee_special_correct T x .FromZero hx hs
    rcases hs with ⟨s, hv⟩ | ⟨s, hv⟩ | ⟨s, hv⟩
    · apply Or.inl
      simpa only [hv, IEEEConversion, toIEEERaw, ieeeMode] using hh
    · apply Or.inl
      simpa only [hv, IEEEConversion, toIEEERaw, ieeeMode] using hh
    · apply Or.inl
      simpa only [hv, IEEEConversion, toIEEERaw, ieeeMode] using hh

theorem cls_limb_wrap_nat (n : Nat) (hn : n < 2^64) :
    (JInt.wrap .u64 (n : Int)).val.toNat = n := by
  simp only [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits, Bool.false_eq_true, ite_false]
  omega

theorem cls_limb_roundtrip (n : Nat) : limbMagnitude (limbsOfNat n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [limbsOfNat]
    split
    · next hn => subst n; rfl
    · next hn =>
      rw [limbMagnitude]
      rw [Int.ofNat_eq_natCast]
      rw [cls_limb_wrap_nat (n % 2^64) (Nat.mod_lt _ (by decide))]
      rw [ih (n / 2^64) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      exact Nat.mod_add_div n (2^64)

theorem cls_limb_append (xs ys : List Limb) :
    limbMagnitude (xs ++ ys) = limbMagnitude xs + (2^64)^xs.length * limbMagnitude ys := by
  induction xs with
  | nil => simp only [List.nil_append, limbMagnitude, List.length_nil,
      Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, limbMagnitude, List.length_cons, ih]
    rw [Nat.pow_succ (2^64) xs.length, Nat.mul_add, Nat.add_assoc,
      ← Nat.mul_assoc (2^64) ((2^64)^xs.length) (limbMagnitude ys),
      Nat.mul_comm (2^64) ((2^64)^xs.length)]

theorem cls_limb_zeros (n : Nat) :
    limbMagnitude (List.replicate n (JInt.wrap .u64 0)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, limbMagnitude, ih, Nat.mul_zero, Nat.add_zero]
    rfl

theorem cls_limb_append_zeros (xs : List Limb) (n : Nat) :
    limbMagnitude (xs ++ List.replicate n (JInt.wrap .u64 0)) = limbMagnitude xs := by
  rw [cls_limb_append, cls_limb_zeros, Nat.mul_zero, Nat.add_zero]

theorem cls_limb_pack_magnitude (p : Clong) (m e : Int) :
    limbMagnitude (pack p (.finite m e)).d =
      if m.natAbs.log2 + 1 > ((p.val.toNat+63)/64)*64 then
        m.natAbs / 2^(m.natAbs.log2+1-((p.val.toNat+63)/64)*64)
      else m.natAbs * 2^(((p.val.toNat+63)/64)*64-(m.natAbs.log2+1)) := by
  unfold pack
  rw [cls_limb_append_zeros, cls_limb_roundtrip]

theorem cls_limb_valid_magnitude (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    limbMagnitude x.d =
      if m.natAbs.log2 + 1 > ((x.prec.val.toNat+63)/64)*64 then
        m.natAbs / 2^(m.natAbs.log2+1-((x.prec.val.toNat+63)/64)*64)
      else m.natAbs * 2^(((x.prec.val.toNat+63)/64)*64-(m.natAbs.log2+1)) := by
  have hf := hx.2.2.2.2
  rw [hv] at hf
  rw [hf.2.1]
  exact cls_limb_pack_magnitude x.prec m e

theorem cls_limb_magnitude_lt (xs : List Limb) :
    limbMagnitude xs < (2^64)^xs.length := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hx := x.property
    change 0 ≤ x.val ∧ x.val ≤ (2 : Int)^64 - 1 at hx
    have hxl : x.val.toNat < 2^64 := by omega
    simp only [limbMagnitude, List.length_cons]
    rw [Nat.pow_succ (2^64) xs.length]
    omega

theorem cls_limb_valid_magnitude_width (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    limbMagnitude x.d =
      if m.natAbs.log2 + 1 > x.d.length*64 then
        m.natAbs / 2^(m.natAbs.log2+1-x.d.length*64)
      else m.natAbs * 2^(x.d.length*64-(m.natAbs.log2+1)) := by
  rw [hx.2.2.2.1]
  exact cls_limb_valid_magnitude x hx m e hv

theorem cls_limb_valid_magnitude_of_fits (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hfit : m.natAbs.log2 + 1 ≤ x.d.length*64) :
    limbMagnitude x.d = m.natAbs * 2^(x.d.length*64-(m.natAbs.log2+1)) := by
  rw [cls_limb_valid_magnitude_width x hx m e hv]
  exact if_neg (by omega)

theorem cls_limb_precision_width (x : BigFloat) (hx : ValidBigFloat x) :
    0 < x.d.length ∧ x.prec.val.toNat ≤ x.d.length*64 ∧
      x.d.length*64 < x.prec.val.toNat+64 := by
  rw [hx.2.2.2.1]
  have hp := hx.1.1
  omega

theorem cls_dyadic_scale (m e : Int) (k : Nat) :
    RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e) (JuliaLean.Proofs.base.mpfr.Round1.Dyadic (m * (2 : Int)^k) (e - (k : Int))) := by
  unfold RatEq JuliaLean.Proofs.base.mpfr.Round1.Dyadic
  by_cases he : e ≥ 0
  · by_cases hek : e - (k : Int) ≥ 0
    · simp only [he, hek, ite_true, Int.natCast_one, Int.mul_one]
      have hpow : (2 : Int)^e.toNat = (2 : Int)^k * (2 : Int)^(e-(k : Int)).toNat := by
        rw [← Int.pow_add]
        congr 1
        omega
      rw [hpow, Int.mul_assoc]
    · simp only [he, hek, ite_true, ite_false, Int.natCast_one, Int.mul_one,
        Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl]
      have hpow : (2 : Int)^k = (2 : Int)^e.toNat *
          (2 : Int)^(-(e-(k : Int))).toNat := by
        rw [← Int.pow_add]
        congr 1
        omega
      rw [hpow, Int.mul_assoc]
  · have hek : ¬ e - (k : Int) ≥ 0 := by omega
    simp only [he, hek, ite_false, Int.natCast_pow,
      show ((2 : Nat) : Int) = 2 from rfl]
    have hpow : (2 : Int)^(-(e-(k : Int))).toNat =
        (2 : Int)^k * (2 : Int)^(-e).toNat := by
      rw [← Int.pow_add]
      congr 1
      omega
    rw [hpow, Int.mul_assoc]

theorem cls_limb_width_ge_64 (x : BigFloat) (hx : ValidBigFloat x) :
    64 ≤ x.d.length*64 := by
  have h := (cls_limb_precision_width x hx).1
  omega

theorem cls_ieee_precision_bounds (T : FTy) :
    1 ≤ (precision_Type_default T).val ∧ (precision_Type_default T).val ≤ 53 := by
  cases T <;> decide

theorem cls_ieee_len_add (T : FTy) (d : Clong) :
    (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val =
      (precision_Type_default T).val + min d.val 0 := by
  have hd := d.property
  have hp := cls_ieee_precision_bounds T
  have hr : IntTy.min .i64 ≤ min d.val 0 ∧ min d.val 0 ≤ IntTy.max .i64 := by
    change -(2 : Int)^63 ≤ min d.val 0 ∧ min d.val 0 ≤ (2 : Int)^63 - 1
    change -(2 : Int)^63 ≤ d.val ∧ d.val ≤ (2 : Int)^63 - 1 at hd
    omega
  have hw : (JInt.wrap .i64 (min d.val 0)).val = min d.val 0 :=
    wrapInt_of_inRange .i64 _ hr
  change wrapInt .i64 ((precision_Type_default T).val +
    (JInt.wrap .i64 (min d.val 0)).val) = _
  rw [hw]
  apply wrapInt_of_inRange
  change -(2 : Int)^63 ≤ (precision_Type_default T).val + min d.val 0 ∧
    (precision_Type_default T).val + min d.val 0 ≤ (2 : Int)^63 - 1
  change -(2 : Int)^63 ≤ min d.val 0 ∧ min d.val 0 ≤ (2 : Int)^63 - 1 at hr
  omega

theorem cls_ieee_len_bound (T : FTy) (d : Clong) :
    (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat ≤ 53 := by
  rw [cls_ieee_len_add]
  have hp := cls_ieee_precision_bounds T
  omega

theorem cls_ieee_len_lt_width (T : FTy) (x : BigFloat) (d : Clong)
    (hx : ValidBigFloat x) :
    (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat <
      x.d.length*64 := by
  have hw := cls_limb_width_ge_64 x hx
  have hl := cls_ieee_len_bound T d
  omega

theorem cls_ieee_discarded_pos (T : FTy) (x : BigFloat) (d : Clong)
    (hx : ValidBigFloat x) :
    0 < x.d.length*64 -
      (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat := by
  have h := cls_ieee_len_lt_width T x d hx
  omega

theorem cls_ieee_discarded_ge_11 (T : FTy) (x : BigFloat) (d : Clong)
    (hx : ValidBigFloat x) :
    11 ≤ x.d.length*64 -
      (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat := by
  have hw := cls_limb_width_ge_64 x hx
  have hl := cls_ieee_len_bound T d
  omega

theorem cls_ieee_truncated_eq (T : FTy) (x : BigFloat) (d : Clong)
    (hx : ValidBigFloat x) :
    (let len := (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat
     let width := x.d.length*64
     if len ≥ width then limbMagnitude x.d * 2^(len-width)
     else limbMagnitude x.d / 2^(width-len)) =
      limbMagnitude x.d / 2^(x.d.length*64 -
        (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat) := by
  dsimp only
  exact if_neg (by have h := cls_ieee_len_lt_width T x d hx; omega)

theorem cls_ieee_rounding_total (T : FTy) (x : BigFloat) (d : Clong)
    (hx : ValidBigFloat x) :
    (let discarded := x.d.length*64 -
       (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat
     if discarded = 0 then 0 else 2^discarded) =
      2^(x.d.length*64 -
        (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat) := by
  dsimp only
  exact if_neg (by have h := cls_ieee_discarded_pos T x d hx; omega)

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.Proofs.base.mpfr.Round1

theorem cls_storage_rat_trans (a b c : Int × Nat) (hb : 0 < b.2)
    (hab : RatEq a b) (hbc : RatEq b c) : RatEq a c := by
  unfold RatEq at hab hbc ⊢
  apply Int.eq_of_mul_eq_mul_right (a := (b.2 : Int)) (by omega)
  calc
    (a.1 * (c.2 : Int)) * (b.2 : Int) = (a.1 * (b.2 : Int)) * (c.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (b.1 * (a.2 : Int)) * (c.2 : Int) := by rw [hab]
    _ = (b.1 * (c.2 : Int)) * (a.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (c.1 * (b.2 : Int)) * (a.2 : Int) := by rw [hbc]
    _ = (c.1 * (a.2 : Int)) * (b.2 : Int) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem cls_storage_dyadic_injective (m n e : Int)
    (h : RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e) (JuliaLean.Proofs.base.mpfr.Round1.Dyadic n e)) : m = n := by
  unfold RatEq JuliaLean.Proofs.base.mpfr.Round1.Dyadic at h
  by_cases he : e ≥ 0
  · simp only [he, ite_true, Int.natCast_one, Int.mul_one] at h
    exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (Int.pow_pos (by decide))) h
  · simp only [he, ite_false, Int.natCast_pow] at h
    exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (Int.pow_pos (by decide))) h

theorem cls_storage_mantissa_of_le (m e k f : Int) (hef : e ≤ f)
    (h : RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e) (JuliaLean.Proofs.base.mpfr.Round1.Dyadic k f)) :
    m = k * (2 : Int)^(f-e).toNat := by
  have hs := cls_dyadic_scale k f (f-e).toNat
  have hd : f - ((f-e).toNat : Int) = e := by omega
  rw [hd] at hs
  exact cls_storage_dyadic_injective m (k * (2 : Int)^(f-e).toNat) e
    (cls_storage_rat_trans _ _ _ (cls_dyadic_den_pos k f) h hs)

theorem cls_storage_log2_mul_pow (n k : Nat) (hn : n ≠ 0) :
    (n * 2^k).log2 = n.log2 + k := by
  induction k with
  | zero => simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
  | succ k ih =>
    have hp : n * 2^k ≠ 0 := Nat.mul_ne_zero hn (Nat.ne_of_gt (Nat.pow_pos (by decide)))
    have hm : n * (2^k * 2) = 2 * (n * 2^k) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [Nat.pow_succ, hm, Nat.log2_two_mul hp, ih]
    omega

theorem cls_storage_exponent_invariant (m e k f : Int) (hm : m ≠ 0) (hk : k ≠ 0)
    (h : RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e) (JuliaLean.Proofs.base.mpfr.Round1.Dyadic k f)) :
    (m.natAbs.log2 + 1 : Int) + e = (k.natAbs.log2 + 1 : Int) + f := by
  by_cases hef : e ≤ f
  · have hv := cls_storage_mantissa_of_le m e k f hef h
    have ha : m.natAbs = k.natAbs * 2^(f-e).toNat := by
      simpa only [Int.natAbs_mul, Int.natAbs_pow,
        show (2 : Int).natAbs = 2 from rfl] using congrArg Int.natAbs hv
    have hl := congrArg Nat.log2 ha
    rw [cls_storage_log2_mul_pow _ _ (Int.natAbs_ne_zero.mpr hk)] at hl
    omega
  · have hfe : f ≤ e := by omega
    have hv := cls_storage_mantissa_of_le k f m e hfe (by exact h.symm)
    have ha : k.natAbs = m.natAbs * 2^(e-f).toNat := by
      simpa only [Int.natAbs_mul, Int.natAbs_pow,
        show (2 : Int).natAbs = 2 from rfl] using congrArg Int.natAbs hv
    have hl := congrArg Nat.log2 ha
    rw [cls_storage_log2_mul_pow _ _ (Int.natAbs_ne_zero.mpr hm)] at hl
    omega

theorem cls_storage_discarded_divides (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hlarge : x.d.length*64 < m.natAbs.log2 + 1) :
    2^(m.natAbs.log2+1-x.d.length*64) ∣ m.natAbs := by
  have hf := hx.2.2.2.2
  rw [hv] at hf
  rcases hf with ⟨hm, hd, hlo, hhi, he, k, f, hk, hkp, hkeq⟩
  have hwidth := (cls_limb_precision_width x hx).2.1
  have hklog := (Nat.log2_lt (Int.natAbs_ne_zero.mpr hk)).mpr hkp
  have hkfits : k.natAbs.log2 + 1 ≤ x.d.length*64 := by omega
  have hexp := cls_storage_exponent_invariant m e k f hm hk hkeq
  have hef : e ≤ f := by omega
  have hdiff : m.natAbs.log2+1-x.d.length*64 ≤ (f-e).toNat := by omega
  have hmant := cls_storage_mantissa_of_le m e k f hef hkeq
  have ha : m.natAbs = k.natAbs * 2^(f-e).toNat := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow,
      show (2 : Int).natAbs = 2 from rfl] using congrArg Int.natAbs hmant
  have hprod : 2^(m.natAbs.log2+1-x.d.length*64) ∣ k.natAbs * 2^(f-e).toNat :=
    Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hdiff) k.natAbs
  simpa only [← ha] using hprod

def cls_storage_signedMag (negative : Bool) (n : Nat) : Int :=
  if negative then -(n : Int) else (n : Int)

theorem cls_storage_signedMag_mul (negative : Bool) (a b : Nat) :
    cls_storage_signedMag negative (a*b) = cls_storage_signedMag negative a * (b : Int) := by
  cases negative <;> simp only [cls_storage_signedMag, Bool.false_eq_true, ite_false,
    ite_true, Int.natCast_mul, Int.neg_mul]

theorem cls_storage_signedMag_scale (m : Int) (p : Nat) :
    cls_storage_signedMag (decide (m < 0)) (m.natAbs*p) = m * (p : Int) := by
  by_cases hm : m < 0
  · have ha : (m.natAbs : Int) = -m := Int.ofNat_natAbs_of_nonpos (by omega)
    simp only [cls_storage_signedMag, hm, decide_true, ite_true,
      Int.natCast_mul, ha, Int.neg_mul, Int.neg_neg]
  · have ha : (m.natAbs : Int) = m := Int.ofNat_natAbs_of_nonneg (by omega)
    simp only [cls_storage_signedMag, hm, decide_false, Bool.false_eq_true, ite_false,
      Int.natCast_mul, ha]

theorem cls_storage_signedMag_self (m : Int) :
    cls_storage_signedMag (decide (m < 0)) m.natAbs = m := by
  simpa only [Nat.mul_one, Int.natCast_one, Int.mul_one] using cls_storage_signedMag_scale m 1

theorem cls_storage_signedMag_div_mul (m : Int) (p : Nat) (hd : p ∣ m.natAbs) :
    cls_storage_signedMag (decide (m < 0)) (m.natAbs/p) * (p : Int) = m := by
  rw [← cls_storage_signedMag_mul, Nat.div_mul_cancel hd, cls_storage_signedMag_self]

theorem cls_storage_value_exact (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e)
      (JuliaLean.Proofs.base.mpfr.Round1.Dyadic (cls_storage_signedMag (signbit x) (JuliaLean.base.gmp.limbMagnitude x.d))
        (x.exp.val - ((x.d.length*64 : Nat) : Int))) := by
  have hf := hx.2.2.2.2
  rw [hv] at hf
  have hexp := hf.2.2.2.2.1
  have hs : signbit x = decide (m < 0) := by
    rw [cls_signbit x hx, hv]
    rfl
  rw [hs]
  by_cases hfit : m.natAbs.log2+1 ≤ x.d.length*64
  · rw [cls_limb_valid_magnitude_of_fits x hx m e hv hfit,
      cls_storage_signedMag_scale]
    have he : x.exp.val - ((x.d.length*64 : Nat) : Int) =
        e - ((x.d.length*64-(m.natAbs.log2+1) : Nat) : Int) := by omega
    rw [he]
    simpa only [Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl] using
      cls_dyadic_scale m e (x.d.length*64-(m.natAbs.log2+1))
  · have hlarge : x.d.length*64 < m.natAbs.log2+1 := by omega
    rw [cls_limb_valid_magnitude_width x hx m e hv, if_pos hlarge]
    let d := m.natAbs.log2+1-x.d.length*64
    let q := cls_storage_signedMag (decide (m < 0)) (m.natAbs/2^d)
    have hdiv : 2^d ∣ m.natAbs := cls_storage_discarded_divides x hx m e hv hlarge
    have hmul : q * (2 : Int)^d = m := by
      simpa only [Int.natCast_pow, show ((2 : Nat) : Int) = 2 from rfl] using
        cls_storage_signedMag_div_mul m (2^d) hdiv
    have he : x.exp.val - ((x.d.length*64 : Nat) : Int) = e + (d : Int) := by
      dsimp only [d]
      omega
    rw [he]
    have hscale := cls_dyadic_scale q (e + (d : Int)) d
    have hsub : e + (d : Int) - (d : Int) = e := by omega
    rw [hsub, hmul] at hscale
    exact hscale.symm

theorem cls_storage_shifted_lower (n W : Nat) (hn : n ≠ 0) (hW : 0 < W) :
    2^(W-1) ≤
      if n.log2+1 > W then n / 2^(n.log2+1-W)
      else n * 2^(W-(n.log2+1)) := by
  have hnlo := Nat.log2_self_le hn
  by_cases hlarge : W < n.log2+1
  · rw [if_pos hlarge]
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr
    rw [← Nat.pow_add]
    have he : W-1+(n.log2+1-W) = n.log2 := by omega
    rw [he]
    exact hnlo
  · rw [if_neg hlarge]
    have hh := Nat.mul_le_mul_right (2^(W-(n.log2+1))) hnlo
    rw [← Nat.pow_add] at hh
    have he : n.log2+(W-(n.log2+1)) = W-1 := by omega
    simpa only [he] using hh

theorem cls_storage_payload_range (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    2^(x.d.length*64-1) ≤ JuliaLean.base.gmp.limbMagnitude x.d ∧
      JuliaLean.base.gmp.limbMagnitude x.d < 2^(x.d.length*64) := by
  constructor
  · rw [cls_limb_valid_magnitude_width x hx m e hv]
    apply cls_storage_shifted_lower
    · exact Int.natAbs_ne_zero.mpr (cls_finite_mantissa_ne_zero x hx m e hv)
    · have hw := cls_limb_width_ge_64 x hx
      omega
  · have hu := cls_limb_magnitude_lt x.d
    simpa only [← Nat.pow_mul, Nat.mul_comm] using hu

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Proofs.base.mpfr.Round1

theorem cls_exp_format_bounds (T : FTy) :
    -1022 ≤ (exponent_min T).val ∧ (exponent_min T).val ≤ -14 ∧
    15 ≤ (exponent_max T).val ∧ (exponent_max T).val ≤ 1023 := by
  cases T <;> decide

theorem cls_exp_finite_bounds (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    -(2 : Int)^62 < x.exp.val ∧ x.exp.val < (2 : Int)^62 := by
  have hf := hx.2.2.2.2
  rw [hv] at hf
  exact ⟨hf.2.2.1, hf.2.2.2.1⟩

theorem cls_exp_ieeeExp (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    (x.exp - JInt.wrap .i64 1).val = x.exp.val - 1 := by
  have hb := cls_exp_finite_bounds x hx m e hv
  have h1 : (JInt.wrap .i64 1).val = 1 := by decide
  change wrapInt .i64 (x.exp.val - (JInt.wrap .i64 1).val) = _
  rw [h1]
  apply wrapInt_of_inRange
  change -(2 : Int)^63 ≤ x.exp.val-1 ∧ x.exp.val-1 ≤ (2 : Int)^63-1
  omega

theorem cls_exp_expDiff (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    (x.exp - JInt.wrap .i64 1 - exponent_min T).val =
      x.exp.val - 1 - (exponent_min T).val := by
  have hb := cls_exp_finite_bounds x hx m e hv
  have hf := cls_exp_format_bounds T
  change wrapInt .i64 ((x.exp-JInt.wrap .i64 1).val - (exponent_min T).val) = _
  rw [cls_exp_ieeeExp x hx m e hv]
  apply wrapInt_of_inRange
  change -(2 : Int)^63 ≤ x.exp.val-1-(exponent_min T).val ∧
    x.exp.val-1-(exponent_min T).val ≤ (2 : Int)^63-1
  omega

theorem cls_exp_diff_bounds (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    -(2 : Int)^62 < (x.exp-JInt.wrap .i64 1-exponent_min T).val ∧
      (x.exp-JInt.wrap .i64 1-exponent_min T).val < (2 : Int)^62+1024 := by
  rw [cls_exp_expDiff T x hx m e hv]
  have hb := cls_exp_finite_bounds x hx m e hv
  have hf := cls_exp_format_bounds T
  omega

theorem cls_exp_diff_plus_precision (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    (x.exp-JInt.wrap .i64 1-exponent_min T+precision_Type_default T).val =
      x.exp.val-1-(exponent_min T).val+(precision_Type_default T).val := by
  have hb := cls_exp_finite_bounds x hx m e hv
  have hf := cls_exp_format_bounds T
  have hp := cls_ieee_precision_bounds T
  change wrapInt .i64 ((x.exp-JInt.wrap .i64 1-exponent_min T).val+
    (precision_Type_default T).val) = _
  rw [cls_exp_expDiff T x hx m e hv]
  apply wrapInt_of_inRange
  change -(2 : Int)^63 ≤ x.exp.val-1-(exponent_min T).val+(precision_Type_default T).val ∧
    x.exp.val-1-(exponent_min T).val+(precision_Type_default T).val ≤ (2 : Int)^63-1
  omega

theorem cls_exp_lenValue (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    (max (precision_Type_default T + JInt.wrap .i64
      (min (x.exp-JInt.wrap .i64 1-exponent_min T).val 0)).val 0).toNat =
      (max ((precision_Type_default T).val+
        min (x.exp.val-1-(exponent_min T).val) 0) 0).toNat := by
  rw [cls_ieee_len_add, cls_exp_expDiff T x hx m e hv]

theorem cls_exp_fieldValue (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    (JInt.wrap .i64
      (max (x.exp-JInt.wrap .i64 1-exponent_min T).val 0 +
        if decide ((x.exp-JInt.wrap .i64 1-exponent_min T).val ≥ 0) then 1 else 0)).val =
      max (x.exp.val-1-(exponent_min T).val) 0 +
        if decide (x.exp.val-1-(exponent_min T).val ≥ 0) then 1 else 0 := by
  rw [cls_exp_expDiff T x hx m e hv]
  have hb := cls_exp_finite_bounds x hx m e hv
  have hf := cls_exp_format_bounds T
  change wrapInt .i64 _ = _
  apply wrapInt_of_inRange
  change -(2 : Int)^63 ≤ _ ∧ _ ≤ (2 : Int)^63-1
  by_cases hn : x.exp.val-1-(exponent_min T).val ≥ 0 <;>
    simp only [hn, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;>
    omega

end JuliaLean.ChatGPT.Batch4.Group3


namespace JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Proofs.base.mpfr.Round1
open JuliaLean.base.gmp (limbMagnitude)

theorem cls_quant_precision (T : FTy) :
    (precision_Type_default T).val = (T.fmt.sb+1 : Nat) := by
  cases T <;> decide

theorem cls_quant_reconstruct (A D : Nat) :
    A = (A / 2^D) * 2^D + A % 2^D := by
  have h := Nat.div_add_mod A (2^D)
  simpa only [Nat.mul_comm] using h.symm

theorem cls_quant_remainder_bound (A D : Nat) : A % 2^D < 2^D :=
  Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem cls_quant_quotient_lt (A W L : Nat) (hLW : L ≤ W) (hA : A < 2^W) :
    A / 2^(W-L) < 2^L := by
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
  rw [← Nat.pow_add]
  have h : L+(W-L) = W := by omega
  simpa only [h] using hA

theorem cls_quant_quotient_lower (A W L : Nat) (hL : 0 < L) (hLW : L ≤ W)
    (hA : 2^(W-1) ≤ A) : 2^(L-1) ≤ A / 2^(W-L) := by
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr
  rw [← Nat.pow_add]
  have h : L-1+(W-L) = W-1 := by omega
  simpa only [h] using hA

theorem cls_quant_quotient_zero (A W : Nat) (hA : A < 2^W) :
    A / 2^W = 0 ∧ A % 2^W = A := by
  exact ⟨Nat.div_eq_of_lt hA, Nat.mod_eq_of_lt hA⟩

theorem cls_quant_len_normal (T : FTy) (d : Clong) (hd : 0 ≤ d.val) :
    (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat =
      T.fmt.sb+1 := by
  rw [cls_ieee_len_add, cls_quant_precision]
  omega

theorem cls_quant_len_subnormal (T : FTy) (d : Clong) (hd : d.val < 0) :
    (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat ≤
      T.fmt.sb := by
  rw [cls_ieee_len_add, cls_quant_precision]
  omega

theorem cls_quant_normal_kept (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (d : Clong) (hd : 0 ≤ d.val) :
    let L := (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat
    2^T.fmt.sb ≤ limbMagnitude x.d / 2^(x.d.length*64-L) ∧
      limbMagnitude x.d / 2^(x.d.length*64-L) < 2^(T.fmt.sb+1) := by
  dsimp only
  have hL := cls_quant_len_normal T d hd
  have hLW := cls_ieee_len_lt_width T x d hx
  have hA := cls_storage_payload_range x hx m e hv
  rw [hL] at hLW ⊢
  constructor
  · have hl := cls_quant_quotient_lower (limbMagnitude x.d) (x.d.length*64)
      (T.fmt.sb+1) (by omega) (by omega) hA.1
    simpa only [Nat.add_sub_cancel] using hl
  · exact cls_quant_quotient_lt _ _ _ (by omega) hA.2

theorem cls_quant_subnormal_kept (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (d : Clong) (hd : d.val < 0) :
    let L := (max (precision_Type_default T + JInt.wrap .i64 (min d.val 0)).val 0).toNat
    limbMagnitude x.d / 2^(x.d.length*64-L) < 2^T.fmt.sb := by
  dsimp only
  have hL := cls_quant_len_subnormal T d hd
  have hLW := cls_ieee_len_lt_width T x d hx
  have hA := (cls_storage_payload_range x hx m e hv).2
  have hq := cls_quant_quotient_lt (limbMagnitude x.d) (x.d.length*64) _
    (Nat.le_of_lt hLW) hA
  exact Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) hL)

theorem cls_quant_normal_mask (B q b : Nat) (hlo : 2^b ≤ q) (hhi : q < 2^(b+1)) :
    (B+1)*2^b + q%2^b = B*2^b+q := by
  have hq : q-2^b < 2^b := by
    rw [Nat.pow_succ] at hhi
    omega
  rw [Nat.mod_eq_sub_mod hlo, Nat.mod_eq_of_lt hq, Nat.add_mul, Nat.one_mul]
  omega

theorem cls_quant_increment_range (q L : Nat) (increment : Bool) (hq : q < 2^L) :
    q + (if increment then 1 else 0) ≤ 2^L := by
  cases increment <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end JuliaLean.ChatGPT.Batch4.Group3
end

namespace JuliaLean.Proofs.base.mpfr
end JuliaLean.Proofs.base.mpfr


set_option Elab.async false



set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

open JuliaLean.ChatGPT.Batch4.Group3

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.base.int

def pattern {t : IntTy} (x : JInt t) : Nat := (x.val % ((2 ^ t.bits : Nat) : Int)).toNat

theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp at h ⊢ <;> omega

theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem wrapInt_val {t : IntTy} (x : JInt t) : wrapInt t x.val = x.val :=
  wrapInt_of_inRange t x.val x.property

theorem jint_eq {t : IntTy} {x y : JInt t} (h : x.val = y.val) : x = y := Subtype.ext h

theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2); omega

theorem fromJInt_toNat {t : IntTy} (x : JInt t) :
    ((fromJInt x).toNat : Int) = x.val % ((2 ^ t.bits : Nat) : Int) := by
  simp only [fromJInt, BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := two_pow_pos_int t.bits; omega))

theorem fromJInt_toInt {t : IntTy} (x : JInt t) (h : t.signed = true) : (fromJInt x).toInt = x.val := by
  have hx := x.property
  simp only [fromJInt, BitVec.toInt_ofInt]
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, Int.bmod_def] <;> split <;> omega

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

theorem add_int_val {t : IntTy} (x y : JInt t) : (add_int x y).val = wrapInt t (x.val + y.val) := by
  simp only [add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add, toJInt_ofInt_val]

theorem sub_int_val {t : IntTy} (x y : JInt t) : (sub_int x y).val = wrapInt t (x.val - y.val) := by
  simp only [sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, toJInt_ofInt_val, Int.sub_eq_add_neg]

theorem eq_int_eq {t : IntTy} (x y : JInt t) : eq_int x y = decide (x.val = y.val) := by
  simp only [eq_int, jlEqInt]
  by_cases h : x.val = y.val
  · simp [fromJInt, show x = y from jint_eq h]
  · have : fromJInt x ≠ fromJInt y := by
      intro hb
      apply h
      rw [← wrapInt_val x, ← wrapInt_val y, ← toJInt_ofInt_val, ← toJInt_ofInt_val]
      exact congrArg (fun b => (toJInt t b).val) hb
    simp [h, this]

theorem slt_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    slt_int x y = decide (x.val < y.val) := by
  simp [slt_int, jlSltInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem sle_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    sle_int x y = decide (x.val ≤ y.val) := by
  simp [sle_int, jlSleInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem okOf_eq {ε α : Type} {r : Except ε α} {h : ∀ e, r ≠ .error e} {a : α} (hr : r = .ok a) :
    okOf r h = a := by
  subst hr; rfl

theorem bitcast_val (T : IntTy) {t : IntTy} (x : JInt t) (h : t.bits = T.bits) :
    (bitcast T x h).val = wrapInt T x.val := by
  unfold bitcast
  apply toJInt_congr
  simp only [jlBitcast, BitVec.toNat_cast]
  rw [fromJInt_toNat, h]

theorem rem_BitInteger_Type_val (to : IntTy) {fr : IntTy} (x : JInt fr) :
    (rem_BitInteger_Type to x).val = wrapInt to x.val := by
  unfold rem_BitInteger_Type
  split
  · rename_i h
    have hlt := bits_lt_of_sizeofT_lt h
    unfold Generated.rem_trunc trunc_int
    rw [okOf_eq (a := BitVec.ofInt to.bits ((fromJInt x).toNat : Int)) (by simp [jlTruncInt, Nat.not_le.mpr hlt, pure, Except.pure])]
    rw [toJInt_ofInt_val]
    apply wrapInt_congr
    rw [fromJInt_toNat]
    have hd : ((2 ^ to.bits : Nat) : Int) ∣ ((2 ^ fr.bits : Nat) : Int) := by
      exact Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (Nat.le_of_lt hlt))
    exact Int.emod_emod_of_dvd _ hd
  · split
    · rename_i h h2
      have hlt := bits_lt_of_sizeofT_lt h2
      split
      · rename_i hs
        unfold Generated.rem_sext sext_int
        rw [okOf_eq (a := BitVec.ofInt to.bits (fromJInt x).toInt) (by simp [jlSextInt, Nat.not_le.mpr hlt, pure, Except.pure])]
        rw [toJInt_ofInt_val, fromJInt_toInt x (by simpa using hs)]
      · rfl
    · rename_i h h2
      have heq := bits_eq_of_sizeofT h h2
      exact bitcast_val to x heq

theorem remT_val (to : IntTy) {fr : IntTy} (x : JInt fr) : (remT to x).val = wrapInt to x.val := by
  unfold remT
  split
  · rename_i h
    subst h
    simp [rem_same, wrapInt_val]
  · exact rem_BitInteger_Type_val to x

theorem unsigned_BitSigned_val {t : IntTy} (x : JInt t) :
    (unsigned_BitSigned x).val = wrapInt t.toUnsigned x.val := bitcast_val _ x _

theorem unsigned_val {t : IntTy} (x : JInt t) : (unsigned x).val = wrapInt t.toUnsigned x.val := by
  unfold unsigned
  split
  · exact unsigned_BitSigned_val x
  · exact remT_val _ x

theorem widenTo_val (T : IntTy) {S : IntTy} (x : JInt S) : (widenTo T x).val = wrapInt T x.val := rfl

theorem widen_promote_left {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) :
    wrapInt (s.promote t) x.val = x.val := by
  have hx := x.property
  cases s <;> cases t <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
    omega

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
  · rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_emod, hm] at hc
    omega
  · rw [hm] at hc
    omega

theorem val_eq_wrap_pattern {t : IntTy} (x : JInt t) : x.val = wrapInt t (pattern x) := by
  rw [← wrapInt_val x]
  apply wrapInt_congr
  rw [pattern_cast, Int.emod_emod]

theorem val_bounds {t : IntTy} (x : JInt t) :
    -((2 ^ t.bits : Nat) : Int) < x.val ∧ x.val < ((2 ^ t.bits : Nat) : Int) := by
  have hx := x.property
  cases t <;> simp_all [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem pattern_of_nonneg {t : IntTy} (x : JInt t) (h : 0 ≤ x.val) : pattern x = x.val.toNat := by
  have hc := pattern_cast x
  rw [Int.emod_eq_of_lt h (val_bounds x).2] at hc
  omega

theorem pattern_of_cong {t : IntTy} (x : JInt t) (z : Int) (h : x.val = wrapInt t z) :
    pattern x = (z % ((2 ^ t.bits : Nat) : Int)).toNat := by
  unfold pattern
  rw [h, wrapInt_emod_self]

theorem toUnsigned_bits (t : IntTy) : t.toUnsigned.bits = t.bits := by cases t <;> rfl

theorem pattern_unsigned {t : IntTy} (x : JInt t) : pattern (unsigned x) = pattern x := by
  rw [pattern_of_cong _ x.val (unsigned_val x), toUnsigned_bits]
  rfl

theorem val_of_unsigned_pattern {t : IntTy} (h : t.signed = false) (x : JInt t) : (pattern x : Int) = x.val := by
  have hx := x.property
  have h0 : 0 ≤ x.val := by
    have := hx.1
    cases t <;> simp_all [IntTy.signed, IntTy.min]
  rw [pattern_of_nonneg x h0]
  exact Int.toNat_of_nonneg h0

theorem pattern_band {t : IntTy} (x y : JInt t) : pattern (band x y) = pattern x &&& pattern y := by
  simp only [band, and_int, jlAndInt, pattern_toJInt, BitVec.toNat_and, ← pattern_fromJInt]

theorem pattern_shl_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (shl_int x y) = pattern x * 2 ^ pattern y % 2 ^ t.bits := by
  simp only [shl_int, jlShlInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 h) _)).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]

theorem pattern_lshr_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (lshr_int x y) = pattern x / 2 ^ pattern y := by
  simp only [lshr_int, jlLshrInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (pattern_lt x) (Nat.pow_le_pow_right (by decide) h))).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (pattern_lt x))

theorem le_zero_eq (y : JInt .i64) : le_BitSigned (lit .i64 0) y = decide (0 ≤ y.val) := by
  have h0 : (lit IntTy.i64 0).val = 0 := by decide
  rw [le_BitSigned, sle_int_eq rfl, h0]

theorem pattern_unsigned_count (y : JInt .i64) (h : 0 ≤ y.val) : pattern (unsigned y) = y.val.toNat := by
  rw [pattern_unsigned, pattern_of_nonneg y h]

theorem pattern_shl_Int {t : IntTy} (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (shl_Int x c) = pattern x * 2 ^ c.val.toNat % 2 ^ t.bits := by
  simp only [shl_Int, ifelse, le_zero_eq, decide_eq_true_eq, h, ite_true, shl_BitInteger_BitUnsigned,
    pattern_shl_int, pattern_unsigned_count c h]

end JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport

theorem Fmt.width_pow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega, Nat.pow_succ, Nat.mul_comm]

end JuliaLean.ChatGPT.Batch5.Group4.Widen

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen.Fl
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport
open JuliaLean.ChatGPT.Batch5.Group4.Widen
variable {f g : Fmt}

theorem toBits_ofBits {f : Fmt} (v : Nat) : (Fl.ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem ofBits_toBits {f : Fmt} (x : Fl f) : Fl.ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [Fl.ofBits, Fl.toBits, Nat.mod_eq_of_lt hv]

theorem bits_split {f : Fmt} (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := Fmt.width_pow f
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

end JuliaLean.ChatGPT.Batch5.Group4.Widen.Fl

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport

theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2); omega

theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp at h ⊢ <;> omega

theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

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
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, Int.bmod_def] <;> split <;> omega

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

theorem slt_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    int.slt_int x y = decide (x.val < y.val) := by
  simp only [int.slt_int, jlSltInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem sle_int_eq {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    int.sle_int x y = decide (x.val ≤ y.val) := by
  simp only [int.sle_int, jlSleInt, fromJInt_toInt x h, fromJInt_toInt y h]

theorem eq_int_eq {t : IntTy} (x y : JInt t) : int.eq_int x y = decide (x.val = y.val) := by
  simp only [int.eq_int, jlEqInt]
  by_cases h : x.val = y.val
  · simp [fromJInt, show x = y from jint_eq h]
  · have : fromJInt x ≠ fromJInt y := by
      intro hb; apply h
      rw [← wrapInt_val x, ← wrapInt_val y, ← toJInt_ofInt_val, ← toJInt_ofInt_val]
      exact congrArg (fun b => (toJInt t b).val) hb
    simp [h, this]

theorem fty_intTy_signed (T : FTy) : T.intTy.signed = true := by cases T <;> rfl

theorem fty_uintTy_signed (T : FTy) : T.uintTy.signed = false := by cases T <;> rfl

theorem isnan_IEEEFloat_eq {T : FTy} (x : FV T) : isnan_IEEEFloat x = x.isnan := by
  unfold isnan_IEEEFloat isnan_AbstractFloat eq_IEEEFloat eq_float jlEqFloat Fl.eq
  cases hx : x.isnan <;> simp [Fl.iszero, hx]

theorem reinterpret_Unsigned_val {T : FTy} (x : FV T) :
    (reinterpret_Unsigned x).val = (x.toBits : Int) := by
  have hlt := x.bits.isLt
  have hbits : x.toBits = x.bits.val := rfl
  cases T
  · change (toJInt IntTy.u16 (BitVec.ofNat IntTy.u16.bits x.toBits)).val = _
    rw [toJInt_ofNat_val]; simp [FTy.fmt, half, Fmt.width] at hlt; simp [wrapInt, IntTy.signed, IntTy.bits]; omega
  · change (toJInt IntTy.u32 (BitVec.ofNat IntTy.u32.bits x.toBits)).val = _
    rw [toJInt_ofNat_val]; simp [FTy.fmt, single, Fmt.width] at hlt; simp [wrapInt, IntTy.signed, IntTy.bits]; omega
  · change (toJInt IntTy.u64 (BitVec.ofNat IntTy.u64.bits x.toBits)).val = _
    rw [toJInt_ofNat_val]; simp [FTy.fmt, double, Fmt.width] at hlt; simp [wrapInt, IntTy.signed, IntTy.bits]; omega

theorem reinterpret_Signed_val {T : FTy} (x : FV T) :
    (reinterpret_Signed x).val =
      if x.signbit then (x.magnitude : Int) - ((2 ^ (T.fmt.eb + T.fmt.sb) : Nat) : Int) else (x.magnitude : Int) := by
  obtain ⟨hsplit, hmag⟩ := Fl.bits_split x
  cases T
  · change (toJInt IntTy.i16 (BitVec.ofNat IntTy.i16.bits x.toBits)).val = _
    rw [toJInt_ofNat_val, hsplit]
    cases x.signbit <;> simp [FTy.fmt, half, wrapInt, IntTy.signed, IntTy.bits] at hmag ⊢ <;> omega
  · change (toJInt IntTy.i32 (BitVec.ofNat IntTy.i32.bits x.toBits)).val = _
    rw [toJInt_ofNat_val, hsplit]
    cases x.signbit <;> simp [FTy.fmt, single, wrapInt, IntTy.signed, IntTy.bits] at hmag ⊢ <;> omega
  · change (toJInt IntTy.i64 (BitVec.ofNat IntTy.i64.bits x.toBits)).val = _
    rw [toJInt_ofNat_val, hsplit]
    cases x.signbit <;> simp [FTy.fmt, double, wrapInt, IntTy.signed, IntTy.bits] at hmag ⊢ <;> omega

theorem signbit_float_eq {T : FTy} (x : FV T) : signbit_float x = x.signbit := by
  have hval : (reinterpret_Int_Float T.intTy x).val = (reinterpret_Signed x).val := by
    cases T <;> rfl
  have hmag := (Fl.bits_split x).2
  have hp := (reinterpret_Signed x).property
  have hmin : IntTy.i64.min ≤ T.intTy.min := by cases T <;> decide
  have hmax : T.intTy.max ≤ IntTy.i64.max := by cases T <;> decide
  have hw : wrapInt .i64 (reinterpret_Signed x).val = (reinterpret_Signed x).val :=
    wrapInt_of_inRange .i64 _ ⟨Int.le_trans hmin hp.1, Int.le_trans hp.2 hmax⟩
  have hw0 : wrapInt .i64 0 = 0 := by decide
  have hlt : int.lt (reinterpret_Int_Float T.intTy x) (int.lit .i64 0) =
      decide ((reinterpret_Signed x).val < 0) := by
    cases T <;>
      change int.slt_int (int.widenTo .i64 (reinterpret_Int_Float _ x)) (int.widenTo .i64 (int.lit .i64 0)) = _ <;>
      rw [slt_int_eq rfl] <;>
      simp only [int.widenTo, int.lit, JInt.wrap, hval, hw, hw0]
  simp only [signbit_float, int.signbit, fty_intTy_signed, ↓reduceIte, int.signbit_Integer,
    int.Generic.signbit_Integer, hlt, reinterpret_Signed_val]
  cases x.signbit <;> simp only [↓reduceIte, Bool.false_eq_true, decide_eq_true_eq,
    decide_eq_false_iff_not] <;> omega

structure Fmt.Good (f : Fmt) : Prop where
  emax_eq : f.emax = 2 * f.bias + 1
  emax_succ : f.emax + 1 = 2 ^ f.eb
  bias_pos : 1 ≤ f.bias
  sb_pos : 1 ≤ f.sb
  sb_le : f.sb ≤ f.bias

theorem good_half : (Fmt.Good half) := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem good_single : (Fmt.Good single) := ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem good_double : (Fmt.Good double) := ⟨by decide, by decide, by decide, by decide, by decide⟩

def Fmt.den (f : Fmt) : Nat := 2 ^ (f.bias + f.sb - 1)

theorem Fmt.den_pos (f : Fmt) : 0 < (Fmt.den f) := Nat.two_pow_pos _

theorem good_fty (T : FTy) : (Fmt.Good T.fmt) := by
  cases T
  · exact good_half
  · exact good_single
  · exact good_double

theorem pow_mul_eq (m a b c d : Nat) (h : a + b = c + d) : m * 2 ^ a * 2 ^ b = m * 2 ^ c * 2 ^ d := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, h]

def magKey (f : Fmt) (M : Nat) : Nat :=
  (M % 2 ^ f.sb + if M / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) * 2 ^ (M / 2 ^ f.sb - 1)

end JuliaLean.ChatGPT.Batch5.Group4.Widen

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen.Fl
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport
open JuliaLean.ChatGPT.Batch5.Group4.Widen
variable {f g : Fmt}

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
  have hw := Fmt.width_pow f
  have ht : (pack neg B r : Fl f).toBits =
      (if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r) := by
    unfold pack
    rw [toBits_ofBits, Nat.mod_eq_of_lt]
    rw [hw]
    cases neg <;> simp <;> omega
  have hm : (pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
    unfold magnitude
    rw [ht]
    cases neg <;> simp [Nat.mod_eq_of_lt hM]
  refine ⟨?_, ?_, ?_, hm⟩
  · unfold signbit
    rw [ht]
    cases neg <;> simp <;> omega
  · rw [expField_eq, hm, Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [frac_eq, hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

def key (x : Fl f) : Int :=
  if x.signbit then -((magKey f x.magnitude : Nat) : Int) else ((magKey f x.magnitude : Nat) : Int)

theorem isnan_of_finite {x : Fl f} (h : x.isfinite = true) : x.isnan = false := by
  simp_all [isfinite, isnan]

theorem isinf_of_finite {x : Fl f} (h : x.isfinite = true) : x.isinf = false := by
  simp_all [isfinite, isinf]

theorem toRat_cases (hf : (Fmt.Good f)) (x : Fl f) (hx : x.isfinite = true) : ∃ m i j : Nat,
    x.toRat = ((if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int)),
      2 ^ j) ∧
    magKey f x.magnitude * 2 ^ j = m * 2 ^ i * (Fmt.den f) ∧ m < 2 ^ (f.sb + 1) ∧
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
  unfold toRat magKey Fmt.den
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
        exact pow_mul_eq _ _ _ _ _ (by omega)
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, 0, f.bias + f.sb - e, ?_, ?_, by omega, fun _ => by omega⟩
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
      · exact pow_mul_eq _ _ _ _ _ (by omega)

theorem toRat_key (hf : (Fmt.Good f)) (x : Fl f) (hx : x.isfinite = true) :
    0 < x.toRat.2 ∧ x.toRat.1 * ((Fmt.den f) : Int) = (key x) * (x.toRat.2 : Int) := by
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
    simp at h <;> omega
  · rfl

theorem packRounded_normal (neg : Bool) (q : Nat) (k : Int) (h1 : 2 ^ f.sb ≤ q)
    (h2 : q < 2 ^ (f.sb + 1)) (hk2 : k + f.bias + f.sb < f.emax) :
    (packRounded neg q k : Fl f) = pack neg (k + f.bias + f.sb).toNat (q - 2 ^ f.sb) := by
  have hP := Nat.two_pow_pos f.sb
  have hq0 : (q == 0) = false := by simp; omega
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

theorem roundRat_normal (hf : (Fmt.Good f)) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f) =
      pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := sig_bounds (f := f) c hc hc1
  have ha : n.natAbs ≠ 0 := by
    rw [hn]
    exact Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  have hn0 : (n == 0) = false := by simp; omega
  have hd : (2 ^ j == 0) = false := by simp
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

theorem roundRat_key (hf : (Fmt.Good f)) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f).isfinite = true ∧
    (key (roundRat n (2 ^ j) z : Fl f)) * ((2 ^ j : Nat) : Int) = n * ((Fmt.den f) : Int) := by
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
      c * 2 ^ i * (Fmt.den f) := by
    unfold Fmt.den
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

theorem zero_spec (hf : (Fmt.Good f)) (s : Bool) :
    (zero s : Fl f).isfinite = true ∧ (key (zero s : Fl f)) = 0 := by
  have hz : (zero s : Fl f) = pack s 0 0 := by simp [zero, pack]
  have hS := hf.emax_succ
  have hE := hf.emax_eq
  obtain ⟨-, he, -, -⟩ := pack_parts (f := f) s 0 0 (by omega) (Nat.two_pow_pos _)
  rw [hz]
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  rw [pack_key _ _ _ (by omega) (Nat.two_pow_pos _)]
  cases s <;> simp

theorem convert_widen_key (hf : (Fmt.Good f)) (hg : (Fmt.Good g)) (hne : (g == f) = false)
    (hsb : f.sb ≤ g.sb) (hbias : f.bias + f.sb ≤ g.bias) (x : Fl f) :
    (convert x : Fl g).isnan = x.isnan ∧
    (convert x : Fl g).isinf = x.isinf ∧
    (convert x : Fl g).isfinite = x.isfinite ∧
    (x.isinf = true → (convert x : Fl g).signbit = x.signbit) ∧
    (x.isfinite = true →
      (key (convert x : Fl g)) * ((Fmt.den f) : Int) = (key x) * ((Fmt.den g) : Int) ∧
      (convert x : Fl g).toRat.1 * (x.toRat.2 : Int) = x.toRat.1 * ((convert x : Fl g).toRat.2 : Int)) := by
  have hgS := hg.emax_succ
  have hgE := hg.emax_eq
  have hfE := hf.emax_eq
  have hPg := Nat.two_pow_pos g.sb
  have hDf : (0 : Int) < (Fmt.den f) := by exact_mod_cast (Fmt.den_pos f)
  have hDg : (0 : Int) < (Fmt.den g) := by exact_mod_cast (Fmt.den_pos g)
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
          (key (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g)) * ((Fmt.den f) : Int) = (key x) * ((Fmt.den g) : Int) := by
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
          obtain ⟨h1, h2⟩ := roundRat_key (f := g) hg _ m i j x.signbit hn' (by omega) hm1
            (by omega) (by omega)
          have hj : (0 : Int) < ((2 ^ j : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos j
          refine ⟨h1, ?_⟩
          generalize (if x.signbit then -((m * 2 ^ i : Nat) : Int)
            else ((m * 2 ^ i : Nat) : Int)) = N at h2 hkey
          generalize (key (roundRat N (2 ^ j) x.signbit : Fl g)) = K at h2
          apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hj)
          calc K * ((Fmt.den f) : Int) * ((2 ^ j : Nat) : Int)
              = K * ((2 ^ j : Nat) : Int) * ((Fmt.den f) : Int) := by rw [Int.mul_right_comm]
            _ = N * ((Fmt.den g) : Int) * ((Fmt.den f) : Int) := by rw [h2]
            _ = N * ((Fmt.den f) : Int) * ((Fmt.den g) : Int) := by rw [Int.mul_right_comm]
            _ = (key x) * ((2 ^ j : Nat) : Int) * ((Fmt.den g) : Int) := by rw [hkey]
            _ = (key x) * ((Fmt.den g) : Int) * ((2 ^ j : Nat) : Int) := by rw [Int.mul_right_comm]
      obtain ⟨hg_fin, hg_scale⟩ := hfin_scale
      generalize (roundRat x.toRat.1 x.toRat.2 x.signbit : Fl g) = w at hg_fin hg_scale ⊢
      have hrat_w := (toRat_key hg w hg_fin).2
      refine ⟨isnan_of_finite hg_fin, isinf_of_finite hg_fin, by rw [hg_fin, hfin],
        fun h => False.elim h, fun _ => ⟨hg_scale, ?_⟩⟩
      apply Int.eq_of_mul_eq_mul_right (by omega : ((Fmt.den g) : Int) ≠ 0)
      apply Int.eq_of_mul_eq_mul_right (by omega : ((Fmt.den f) : Int) ≠ 0)
      have hstep1 : (w.toRat.1 * ((Fmt.den g) : Int)) * (x.toRat.2 : Int) * ((Fmt.den f) : Int) =
          ((key w) * ((Fmt.den f) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by
        rw [hrat_w, Int.mul_right_comm ((key w) * (w.toRat.2 : Int)) (x.toRat.2 : Int) ((Fmt.den f) : Int),
          Int.mul_right_comm (key w) (w.toRat.2 : Int) ((Fmt.den f) : Int)]
      have hstep2 : (x.toRat.1 * ((Fmt.den f) : Int)) * (w.toRat.2 : Int) * ((Fmt.den g) : Int) =
          ((key x) * ((Fmt.den g) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by
        rw [hrat_x, Int.mul_right_comm ((key x) * (x.toRat.2 : Int)) (w.toRat.2 : Int) ((Fmt.den g) : Int),
          Int.mul_right_comm (key x) (x.toRat.2 : Int) ((Fmt.den g) : Int),
          Int.mul_right_comm ((key x) * ((Fmt.den g) : Int)) (x.toRat.2 : Int) (w.toRat.2 : Int)]
      calc w.toRat.1 * (x.toRat.2 : Int) * ((Fmt.den g) : Int) * ((Fmt.den f) : Int)
          = (w.toRat.1 * ((Fmt.den g) : Int)) * (x.toRat.2 : Int) * ((Fmt.den f) : Int) := by
            rw [Int.mul_right_comm w.toRat.1 (x.toRat.2 : Int) ((Fmt.den g) : Int)]
        _ = ((key w) * ((Fmt.den f) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := hstep1
        _ = ((key x) * ((Fmt.den g) : Int)) * (w.toRat.2 : Int) * (x.toRat.2 : Int) := by rw [hg_scale]
        _ = (x.toRat.1 * ((Fmt.den f) : Int)) * (w.toRat.2 : Int) * ((Fmt.den g) : Int) := hstep2.symm
        _ = x.toRat.1 * (w.toRat.2 : Int) * ((Fmt.den g) : Int) * ((Fmt.den f) : Int) := by
            rw [Int.mul_right_comm x.toRat.1 ((Fmt.den f) : Int) (w.toRat.2 : Int),
              Int.mul_right_comm (x.toRat.1 * (w.toRat.2 : Int)) ((Fmt.den f) : Int) ((Fmt.den g) : Int)]
    · have hinf : (inf x.signbit : Fl g) = pack x.signbit g.emax 0 := by simp [inf, pack]
      obtain ⟨hs, he, hfr, -⟩ := pack_parts (f := g) x.signbit g.emax 0 (by omega) hPg
      simp only [Bool.false_eq_true, ↓reduceIte, hinf]
      have hpn : (pack x.signbit g.emax 0 : Fl g).isnan = false := by unfold isnan; rw [he, hfr]; simp
      have hpi : (pack x.signbit g.emax 0 : Fl g).isinf = true := by unfold isinf; rw [he, hfr]; simp
      have hpf : (pack x.signbit g.emax 0 : Fl g).isfinite = false := by unfold isfinite; rw [he]; simp
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
        Fl g).isnan = true := by unfold isnan; rw [he, hfr']; simp
    have hpi : (pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isinf = false := by unfold isinf; rw [he, hfr']; simp
    have hpf : (pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isfinite = false := by unfold isfinite; rw [he]; simp
    have hxi : x.isinf = false := by
      unfold isnan at hn; unfold isinf; simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hn; simp [hn.1, hn.2]
    have hxf : x.isfinite = false := by
      unfold isnan at hn; unfold isfinite; simp only [Bool.and_eq_true, beq_iff_eq] at hn; simp [hn.1]
    exact ⟨hpn, by rw [hpi, hxi], by rw [hpf, hxf],
      fun h => by rw [hxi] at h; exact Bool.noConfusion h,
      fun h => by rw [hxf] at h; exact Bool.noConfusion h⟩

end JuliaLean.ChatGPT.Batch5.Group4.Widen.Fl

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport

theorem okOf_eq {ε α : Type} {r : Except ε α} {h : ∀ e, r ≠ .error e} {a : α} (hr : r = .ok a) :
    int.okOf r h = a := by
  subst hr; rfl

theorem convertFloat_eq (T : FTy) {S : FTy} (x : FV S) :
    convertFloat T x = Fl.convert x := by
  cases T <;> cases S
  · simp [convertFloat, Fl.convert, Fl.ofBits_toBits]
  · simp only [convertFloat, Float16_Float32, fptrunc]
    exact okOf_eq rfl
  · simp only [convertFloat, Float16_Float64, fptrunc]
    exact okOf_eq rfl
  · simp only [convertFloat, Float32_Float16, fpext]
    exact okOf_eq rfl
  · simp [convertFloat, Fl.convert, Fl.ofBits_toBits]
  · simp only [convertFloat, Float32_Float64, fptrunc]
    exact okOf_eq rfl
  · simp only [convertFloat, Float64_Float16, fpext]
    exact okOf_eq rfl
  · simp only [convertFloat, Float64_Float32, fpext]
    exact okOf_eq rfl
  · simp [convertFloat, Fl.convert, Fl.ofBits_toBits]

end JuliaLean.ChatGPT.Batch5.Group4.Widen

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen.TruncProofs
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.ChatGPT.Batch5.Group4.Widen.IntSupport

def mantissaNat {T : FTy} (x : FV T) : Nat :=
  x.frac + if x.expField = 0 then 0 else 2 ^ T.fmt.sb

theorem mag_decomp {T : FTy} (x : FV T) :
    x.magnitude = x.expField * 2 ^ T.fmt.sb + x.frac ∧ x.frac < 2 ^ T.fmt.sb := by
  rw [Fl.expField_eq, Fl.frac_eq]
  have h := Nat.div_add_mod x.magnitude (2 ^ T.fmt.sb)
  exact ⟨by rw [Nat.mul_comm]; exact h.symm, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem bitvec_and_mask (w a b : Nat) :
    BitVec.ofNat w a &&& BitVec.ofNat w (2 ^ b - 1) = BitVec.ofNat w (a % 2 ^ b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_and, hi, decide_true, Bool.true_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Bool.and_comm]

theorem bitvec_or_pow (w r b : Nat) (hr : r < 2 ^ b) :
    BitVec.ofNat w r ||| BitVec.ofNat w (2 ^ b) = BitVec.ofNat w (r + 2 ^ b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_or, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i b with hlt | hge
  · have h1 : (2 ^ b).testBit i = false := by rw [Nat.testBit_two_pow]; simp [Nat.ne_of_gt hlt]
    have hm_mod : (r + 2 ^ b) % 2 ^ b = r := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]
    have htb := Nat.testBit_mod_two_pow (r + 2 ^ b) b i
    rw [hm_mod, decide_eq_true hlt, Bool.true_and] at htb
    rw [h1, ← htb, Bool.or_false]
  · rcases Nat.eq_or_lt_of_le hge with h_eq | hgt
    · rw [← h_eq]
      have h1 : (2 ^ b).testBit b = true := by rw [Nat.testBit_two_pow]; simp
      have h2 : (r + 2 ^ b).testBit b = true := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rw [Nat.add_div_right _ (Nat.two_pow_pos b), Nat.div_eq_of_lt hr]; rfl
      rw [h1, h2, Bool.or_true]
    · have hpow : r + 2 ^ b < 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
      have hle : 2 ^ (b + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega),
        Nat.testBit_lt_two_pow (by omega)]; rfl

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
  cases t <;> simp_all [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega

theorem pattern_of_nonneg {t : IntTy} (x : JInt t) (h : 0 ≤ x.val) : pattern x = x.val.toNat := by
  have hc := pattern_cast x
  rw [Int.emod_eq_of_lt h (val_bounds x).2] at hc
  omega

theorem val_of_unsigned_pattern {t : IntTy} (h : t.signed = false) (x : JInt t) : (pattern x : Int) = x.val := by
  have hx := x.property
  have h0 : 0 ≤ x.val := by
    have := hx.1
    cases t <;> simp_all [IntTy.signed, IntTy.min]
  rw [pattern_of_nonneg x h0]
  exact Int.toNat_of_nonneg h0

theorem val_of_signed_small_pattern {t : IntTy} (x : JInt t) (h : pattern x < 2 ^ (t.bits - 1)) :
    x.val = (pattern x : Int) := by
  rw [val_eq_wrap_pattern x]
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits, Nat.reduceSub, Nat.reducePow] at h ⊢ <;> omega

theorem pattern_band {t : IntTy} (x y : JInt t) : pattern (int.band x y) = pattern x &&& pattern y := by
  simp only [int.band, int.and_int, jlAndInt, pattern_toJInt, BitVec.toNat_and, ← pattern_fromJInt]

theorem pattern_bor {t : IntTy} (x y : JInt t) : pattern (int.bor x y) = pattern x ||| pattern y := by
  simp only [int.bor, int.or_int, jlOrInt, pattern_toJInt, BitVec.toNat_or, ← pattern_fromJInt]

theorem sub_int_val {t : IntTy} (x y : JInt t) : (int.sub x y).val = wrapInt t (x.val - y.val) := by
  simp only [int.sub, int.sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, toJInt_ofInt_val, Int.sub_eq_add_neg]

theorem add_int_val {t : IntTy} (x y : JInt t) : (int.add x y).val = wrapInt t (x.val + y.val) := by
  simp only [int.add, int.add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add, toJInt_ofInt_val]

theorem rem_BitInteger_Type_val (to : IntTy) {fr : IntTy} (x : JInt fr) :
    (int.rem_BitInteger_Type to x).val = wrapInt to x.val := by
  unfold int.rem_BitInteger_Type
  split
  · rename_i h
    have hlt := int.bits_lt_of_sizeofT_lt h
    unfold int.Generated.rem_trunc int.trunc_int
    rw [okOf_eq (a := BitVec.ofInt to.bits ((fromJInt x).toNat : Int))
      (by simp [jlTruncInt, Nat.not_le.mpr hlt, pure, Except.pure])]
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
          (by simp [jlSextInt, Nat.not_le.mpr hlt, pure, Except.pure])]
        rw [toJInt_ofInt_val, fromJInt_toInt x (by simpa using hs)]
      · rfl
    · rename_i h h2
      exact bitcast_val to x (int.bits_eq_of_sizeofT h h2)

theorem remT_val (to : IntTy) {fr : IntTy} (x : JInt fr) : (int.remT to x).val = wrapInt to x.val := by
  unfold int.remT
  split
  · rename_i h; subst h; simp [int.rem_same, wrapInt_val]
  · exact rem_BitInteger_Type_val to x

theorem pattern_of_cong {t : IntTy} (x : JInt t) (z : Int) (h : x.val = wrapInt t z) :
    pattern x = (z % ((2 ^ t.bits : Nat) : Int)).toNat := by
  unfold pattern
  rw [h, wrapInt_emod_self]

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

theorem pattern_lshr_int {t u : IntTy} (x : JInt t) (y : JInt u) :
    pattern (int.lshr_int x y) = pattern x / 2 ^ pattern y := by
  simp only [int.lshr_int, jlLshrInt, ← pattern_fromJInt]
  split
  · rename_i h
    rw [pattern_toJInt, BitVec.toNat_ofNat, Nat.zero_mod]
    exact (Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (pattern_lt x) (Nat.pow_le_pow_right (by decide) h))).symm
  · rw [pattern_toJInt, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (pattern_lt x))

theorem le_zero_eq (y : JInt .i64) : int.le_BitSigned (int.lit .i64 0) y = decide (0 ≤ y.val) := by
  have h0 : (int.lit IntTy.i64 0).val = 0 := by decide
  rw [int.le_BitSigned, sle_int_eq rfl, h0]

theorem pattern_unsigned_count (y : JInt .i64) (h : 0 ≤ y.val) : pattern (int.unsigned y) = y.val.toNat := by
  rw [pattern_unsigned, pattern_of_nonneg y h]

theorem pattern_shl_Int {t : IntTy} (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (int.shl_Int x c) = pattern x * 2 ^ c.val.toNat % 2 ^ t.bits := by
  simp only [int.shl_Int, int.ifelse, le_zero_eq, decide_eq_true_iff, h, ↓reduceIte,
    int.shl_BitInteger_BitUnsigned, pattern_shl_int, pattern_unsigned_count c h]

theorem pattern_shr_Int_unsigned {t : IntTy} (hu : t.signed = false) (x : JInt t) (c : JInt .i64) (h : 0 ≤ c.val) :
    pattern (int.shr_Int x c) = pattern x / 2 ^ c.val.toNat := by
  simp only [int.shr_Int, int.ifelse, le_zero_eq, decide_eq_true_iff, h, ↓reduceIte,
    int.shrU, hu, Bool.false_eq_true, int.shr_BitUnsigned_BitUnsigned,
    pattern_lshr_int, pattern_unsigned_count c h]

theorem nat_and_mask (a b : Nat) : a &&& (2 ^ b - 1) = a % 2 ^ b := by
  have h := congrArg BitVec.toNat (bitvec_and_mask (max a.log2 b + 2) a b)
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat] at h
  have hlt1 : (a &&& (2 ^ b - 1)) < 2 ^ (max a.log2 b + 2) := by
    have : a &&& (2 ^ b - 1) ≤ 2 ^ b - 1 := Nat.and_le_right
    have : 2 ^ b < 2 ^ (max a.log2 b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have hlt2 : a % 2 ^ b < 2 ^ (max a.log2 b + 2) := by
    have := Nat.mod_lt a (Nat.two_pow_pos b)
    have : 2 ^ b < 2 ^ (max a.log2 b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  have h1 : (a % 2 ^ (max a.log2 b + 2)) &&& ((2 ^ b - 1) % 2 ^ (max a.log2 b + 2)) =
      a &&& (2 ^ b - 1) := by
    have ha : a < 2 ^ (max a.log2 b + 2) := by
      by_cases h0 : a = 0
      · subst h0; exact Nat.two_pow_pos _
      · calc a < 2 ^ (a.log2 + 1) := Nat.lt_log2_self
          _ ≤ 2 ^ (max a.log2 b + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    have hb : 2 ^ b - 1 < 2 ^ (max a.log2 b + 2) := by
      have : 2 ^ b < 2 ^ (max a.log2 b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [h1, Nat.mod_eq_of_lt hlt2] at h
  exact h

theorem nat_or_pow (r b : Nat) (hr : r < 2 ^ b) : (r ||| 2 ^ b) = r + 2 ^ b := by
  have h := congrArg BitVec.toNat (bitvec_or_pow (b + 2) r b hr)
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat] at h
  have hp : 2 ^ b < 2 ^ (b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsum : r + 2 ^ b < 2 ^ (b + 2) := by
    calc r + 2 ^ b < 2 ^ b + 2 ^ b := by omega
      _ = 2 ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_two]
      _ < 2 ^ (b + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hsum] at h
  exact h

theorem pattern_reinterpret_Unsigned {T : FTy} (x : FV T) :
    pattern (reinterpret_Unsigned x) = x.toBits := by
  have hv := reinterpret_Unsigned_val x
  have hlt := x.bits.isLt
  have hbits : x.toBits = x.bits.val := rfl
  rw [← val_of_unsigned_pattern (fty_uintTy_signed T)] at hv
  omega

theorem widenTo_val (T : IntTy) {S : IntTy} (x : JInt S) : (int.widenTo T x).val = wrapInt T x.val := rfl

theorem widen_promote_left {s t : IntTy} (h : s.signed = t.signed) (x : JInt s) :
    wrapInt (s.promote t) x.val = x.val := by
  have hx := x.property
  cases s <;> cases t <;> simp_all [IntTy.promote, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, wrapInt] <;>
    omega

def width (t : IntTy) : Nat := if t.signed then t.bits - 1 else t.bits

theorem isnan_iff_mag {T : FTy} (x : FV T) :
    x.isnan = true ↔ T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude := by
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hP := Nat.two_pow_pos T.fmt.sb
  have hM := (Fl.bits_split x).2
  have hS := (good_fty T).emax_succ
  have hdiv : x.expField < 2 ^ T.fmt.eb := by
    rw [Fl.expField_eq]
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  constructor
  · rintro ⟨he, hfr⟩
    rw [hm, he]; omega
  · intro hgt
    have he : x.expField = T.fmt.emax := by
      rcases Nat.lt_or_ge x.expField T.fmt.emax with hlt | hge
      · have : (x.expField + 1) * 2 ^ T.fmt.sb ≤ T.fmt.emax * 2 ^ T.fmt.sb :=
          Nat.mul_le_mul_right _ hlt
        rw [Nat.succ_mul] at this
        omega
      · omega
    exact ⟨he, by rw [hm, he] at hgt; omega⟩

end JuliaLean.ChatGPT.Batch5.Group4.Widen.TruncProofs

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen
open JuliaLean JuliaLean.C JuliaLean.base JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Promotion.Fl
open JuliaLean.ChatGPT.Batch5.Group4.Widen.TruncProofs

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

theorem nat_and_shiftRight (a b k : Nat) :
    (a &&& b) / 2 ^ k = (a / 2 ^ k) &&& (b / 2 ^ k) := by
  simp only [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib]

theorem finishFloat_eq {T : FTy} (v : FV T) : finishFloat v = v := by
  unfold finishFloat
  have : (T.fmt == bfloat) = false := by cases T <;> decide
  rw [this]; rfl

theorem quietFloat_isnan {T : FTy} (x : FV T) (hx : x.isnan = true) :
    (quietFloat x).isnan = true := by
  have hmag_gt : T.fmt.emax * 2 ^ T.fmt.sb < x.magnitude := (isnan_iff_mag x).mp hx
  rw [isnan_iff_mag]
  unfold quietFloat Fl.magnitude
  change ((x.toBits ||| 2 ^ (T.fmt.sb - 1)) % 2 ^ T.fmt.width) % 2 ^ (T.fmt.eb + T.fmt.sb) > _
  have h1 := x.bits.isLt
  have h2 : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.width := by
    apply Nat.pow_lt_pow_right (by decide); unfold Fmt.width; omega
  have hor_lt : (x.toBits ||| 2 ^ (T.fmt.sb - 1)) < 2 ^ T.fmt.width :=
    Nat.or_lt_two_pow h1 h2
  rw [Nat.mod_eq_of_lt hor_lt]
  have hmod_or : (x.toBits ||| 2 ^ (T.fmt.sb - 1)) % 2 ^ (T.fmt.eb + T.fmt.sb) =
      x.magnitude ||| 2 ^ (T.fmt.sb - 1) := by
    apply Nat.eq_of_testBit_eq; intro i
    have hlt_sb : T.fmt.sb - 1 < T.fmt.eb + T.fmt.sb := by
      have : 0 < T.fmt.sb := by cases T <;> decide
      omega
    have hpow_lt : 2 ^ (T.fmt.sb - 1) < 2 ^ (T.fmt.eb + T.fmt.sb) :=
      Nat.pow_lt_pow_right (by decide) hlt_sb
    rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_or]
    unfold Fl.magnitude
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < T.fmt.eb + T.fmt.sb
    · simp [hi]
    · have : (2 ^ (T.fmt.sb - 1)).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hpow_lt (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, this]
  rw [hmod_or]
  obtain ⟨hm, hf⟩ := mag_decomp x
  have hP := Nat.two_pow_pos T.fmt.sb
  have hexp : x.expField = T.fmt.emax := by
    unfold Fl.isnan at hx; simp only [Bool.and_eq_true, beq_iff_eq] at hx; exact hx.1
  have hpow_sb : 2 ^ (T.fmt.sb - 1) < 2 ^ T.fmt.sb := by cases T <;> decide
  have hor_split : (x.magnitude ||| 2 ^ (T.fmt.sb - 1)) =
      (x.frac ||| 2 ^ (T.fmt.sb - 1)) + T.fmt.emax * 2 ^ T.fmt.sb := by
    rw [hm, hexp, Nat.add_comm, ← nat_or_mul_pow _ _ _ hf, Nat.or_assoc,
      Nat.or_comm (T.fmt.emax * 2 ^ T.fmt.sb), ← Nat.or_assoc,
      nat_or_mul_pow _ _ _ (Nat.or_lt_two_pow hf hpow_sb)]
  have hpos_or : 0 < (x.frac ||| 2 ^ (T.fmt.sb - 1)) := by
    apply Classical.byContradiction; intro hle
    have h0 : (x.frac ||| 2 ^ (T.fmt.sb - 1)) = 0 := by omega
    have htb := congrArg (fun n : Nat => n.testBit (T.fmt.sb - 1)) h0
    simp [Nat.testBit_or] at htb
  omega

theorem isinf_IEEEFloat_eq {T : FTy} (x : FV T) :
    isinf_IEEEFloat x = x.isinf := by
  unfold isinf_IEEEFloat egal_float abs_IEEEFloat abs_float jlAbsFloat unaryFloat oftype_float inf_float
  rw [finishFloat_eq]
  have hinf_bits : (Fl.inf false : FV T).toBits = T.fmt.emax * 2 ^ T.fmt.sb := by
    cases T <;> decide
  have habs_bits : ∀ y : FV T, (Fl.ofBits y.magnitude : FV T).toBits = y.magnitude := by
    intro y
    rw [Fl.toBits_ofBits, Nat.mod_eq_of_lt (by have := (Fl.bits_split y).2; rw [Fmt.width_pow]; omega)]
  rw [hinf_bits, habs_bits]
  by_cases hnan : x.isnan = true
  · have hnot_inf : x.isinf = false := by
      unfold Fl.isnan at hnan; unfold Fl.isinf
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hnan
      simp [hnan.1, hnan.2]
    rw [hnot_inf]
    have hq_nan : (if T.fmt == half && x.isnan then quietFloat x else x).isnan = true := by
      split
      · exact quietFloat_isnan x hnan
      · exact hnan
    have hm_gt : T.fmt.emax * 2 ^ T.fmt.sb < (if T.fmt == half && x.isnan then quietFloat x else x).magnitude :=
      (isnan_iff_mag _).mp hq_nan
    rw [beq_eq_false_iff_ne]; omega
  · have hnan' : x.isnan = false := Bool.eq_false_iff.mpr hnan
    simp only [hnan', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hm, hf⟩ := mag_decomp x
    have hP := Nat.two_pow_pos T.fmt.sb
    rw [hm]
    unfold Fl.isinf
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h
      have he : x.expField = T.fmt.emax := by
        rcases Nat.lt_trichotomy x.expField T.fmt.emax with hlt | h_eq | hgt
        · have : (x.expField + 1) * 2 ^ T.fmt.sb ≤ T.fmt.emax * 2 ^ T.fmt.sb :=
            Nat.mul_le_mul_right _ hlt
          rw [Nat.succ_mul] at this; omega
        · exact h_eq
        · have : (T.fmt.emax + 1) * 2 ^ T.fmt.sb ≤ x.expField * 2 ^ T.fmt.sb :=
            Nat.mul_le_mul_right _ hgt
          rw [Nat.succ_mul] at this; omega
      exact ⟨he, by rw [he] at h; omega⟩
    · rintro ⟨h_eq, h0⟩; rw [h_eq, h0]; omega

theorem eq_int_same_eq {t : IntTy} (x y : JInt t) :
    int.eq x y = decide (x.val = y.val) := by
  rw [int.eq, if_pos rfl]
  unfold int.eqPromote int.promoteSameSign int.eqSame
  rw [eq_int_eq, widenTo_val, widenTo_val,
    IntSupport.widen_promote_left (s := t) (t := t) rfl x,
    IntSupport.widen_promote_left (s := t) (t := t) rfl y]

theorem decompose_spec (T : FTy) (x : FV T) :
    (x.isnan = true →
      (decompose x).1.val = 0 ∧ (decompose x).2.1.val = 0 ∧ (decompose x).2.2.val = 0) ∧
    (x.isinf = true →
      (decompose x).1.val = (if x.signbit then -1 else 1) ∧
      (decompose x).2.1.val = 0 ∧ (decompose x).2.2.val = 0) ∧
    (x.isfinite = true →
      (decompose x).1.val = (mantissaNat x : Int) ∧
      (decompose x).2.1.val = (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
                               else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) ∧
      (decompose x).2.2.val = (if x.signbit then -1 else 1) ∧
      x.toRat = ((decompose x).2.2.val * (decompose x).1.val *
                   (if 0 ≤ (decompose x).2.1.val then (2 ^ (decompose x).2.1.val.toNat : Nat) else 1),
                 if 0 ≤ (decompose x).2.1.val then 1 else 2 ^ (-(decompose x).2.1.val).toNat)) := by
  have hnan_eq := isnan_IEEEFloat_eq x
  have hinf_eq := isinf_IEEEFloat_eq x
  have hsign_eq := signbit_float_eq x
  refine ⟨?_, ?_, ?_⟩
  · intro hnan
    cases T <;>
      simp only [decompose, decompose_Float16, decompose_Float32, decompose_Float64,
        hnan_eq, hnan, ↓reduceIte] <;> decide
  · intro hinf
    have hnan : x.isnan = false := by
      unfold Fl.isinf at hinf; unfold Fl.isnan
      simp only [Bool.and_eq_true, beq_iff_eq] at hinf
      simp [hinf.1, hinf.2]
    have hx_eq : x = Fl.inf x.signbit := by
      generalize hs : x.signbit = s
      rw [← Fl.ofBits_toBits x, (Fl.bits_split x).1, hs]
      obtain ⟨hm, _⟩ := mag_decomp x
      unfold Fl.isinf at hinf
      simp only [Bool.and_eq_true, beq_iff_eq] at hinf
      rw [hm, hinf.1, hinf.2]
      rfl
    have hlt0 : lt_FI (Fl.inf x.signbit : FV T) (int.lit .i64 0) = x.signbit := by
      cases T <;> cases x.signbit <;> decide
    cases T <;>
      simp only [decompose, decompose_Float16, decompose_Float32, decompose_Float64,
        hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte] <;>
      rw [hx_eq, hlt0] <;>
      cases x.signbit <;> decide
  · intro hfin
    have hnan : x.isnan = false := Fl.isnan_of_finite hfin
    have hinf : x.isinf = false := Fl.isinf_of_finite hfin
    have hpat_n : pattern (reinterpret_Unsigned x) = x.toBits :=
      pattern_reinterpret_Unsigned x
    have hf : x.frac < 2 ^ T.fmt.sb := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hexp_lt : x.expField < 2 ^ T.fmt.eb := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hT_facts :
        T.uintTy.signed = false ∧
        T.intTy.bits = T.uintTy.bits ∧
        T.fmt.sb < T.uintTy.bits ∧
        T.fmt.sb + 1 ≤ T.intTy.bits - 1 ∧
        T.intTy.bits - 1 ≤ 63 ∧
        2 ^ T.fmt.eb ≤ 2048 ∧
        T.fmt.bias + T.fmt.sb ≤ 1075 ∧
        pattern (int.ofBool T.intTy false) = 0 ∧
        pattern (int.ofBool T.intTy true) = 1 := by
      clear hnan_eq hinf_eq hsign_eq hfin hnan hinf hpat_n hf hexp_lt x
      cases T <;> decide
    obtain ⟨huns, hbits_eq, hsb_lt_u, hsb_le_i, hi_le_63, heb_2048, hbs_1075, hpat_b_false, hpat_b_true⟩ := hT_facts
    have h_exp : ∀ (mask : JInt T.uintTy) (sb : JInt .i64),
        pattern mask = (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb →
        sb.val = (T.fmt.sb : Int) →
        (int.remT .i64 (int.shr_Int (int.band (reinterpret_Unsigned x) mask) sb)).val =
          (x.expField : Int) := by
      intro mask sb hmask hsb
      have hsb0 : 0 ≤ sb.val := by omega
      have hpat_shr : pattern (int.shr_Int (int.band (reinterpret_Unsigned x) mask) sb) = x.expField := by
        rw [pattern_shr_Int_unsigned huns _ _ hsb0, pattern_band, hpat_n, hmask, hsb]
        change (x.toBits &&& (2 ^ T.fmt.eb - 1) * 2 ^ T.fmt.sb) / 2 ^ T.fmt.sb = x.expField
        rw [nat_and_shiftRight, Nat.mul_div_cancel _ (Nat.two_pow_pos _), nat_and_mask]
        rfl
      have hval_shr : (int.shr_Int (int.band (reinterpret_Unsigned x) mask) sb).val = (x.expField : Int) := by
        rw [← val_of_unsigned_pattern huns, hpat_shr]
      rw [remT_val, hval_shr]
      apply wrapInt_of_inRange
      simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
    have h_s : ∀ (smask : JInt T.uintTy) (sb bias_sb e : JInt .i64),
        pattern smask = 2 ^ T.fmt.sb - 1 →
        sb.val = (T.fmt.sb : Int) →
        bias_sb.val = (T.fmt.bias + T.fmt.sb : Nat) →
        e.val = (x.expField : Int) →
        (int.remT .i64 (int.bor (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask))
          (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb))).val =
          (mantissaNat x : Int) ∧
        (int.add (int.sub e bias_sb)
          (int.ofBool .i64 (int.eq e (int.lit .i64 0)))).val =
          (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
           else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) := by
      intro smask sb bias_sb e hsm hsb hbs he
      have heq0 : int.eq e (int.lit .i64 0) = decide (x.expField = 0) := by
        rw [eq_int_same_eq, he]
        have : (int.lit .i64 0).val = 0 := rfl
        rw [this]; apply decide_eq_decide.mpr; omega
      have hpat_s0 : pattern (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask)) = x.frac := by
        rw [pattern_of_cong _ _ (remT_val T.intTy _)]
        change ((int.band (reinterpret_Unsigned x) smask).val % ((2 ^ T.intTy.bits : Nat) : Int)).toNat = x.frac
        rw [hbits_eq, ← pattern_cast, pattern_band, hpat_n, hsm, nat_and_mask]
        rfl
      have hpat_shl : pattern (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb) =
          if x.expField = 0 then 0 else 2 ^ T.fmt.sb := by
        rw [heq0, pattern_shl_Int _ _ (by omega)]
        have hsb_nat : sb.val.toNat = T.fmt.sb := by omega
        rw [hsb_nat]
        by_cases hx0 : x.expField = 0
        · simp only [hx0, decide_true, Bool.not_true, ↓reduceIte]
          rw [hpat_b_false, Nat.zero_mul, Nat.zero_mod]
        · simp only [hx0, decide_false, Bool.not_false, ↓reduceIte]
          have hpow_lt : 2 ^ T.fmt.sb < 2 ^ T.intTy.bits :=
            Nat.pow_lt_pow_right (by decide) (by omega)
          rw [hpat_b_true, Nat.one_mul, Nat.mod_eq_of_lt hpow_lt]
      have hpat_bor : pattern (int.bor (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask))
          (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb)) = mantissaNat x := by
        rw [pattern_bor, hpat_s0, hpat_shl]
        unfold mantissaNat
        by_cases hx0 : x.expField = 0
        · simp [hx0]
        · simp only [hx0, ↓reduceIte]
          exact nat_or_pow x.frac T.fmt.sb hf
      have hm_lt : mantissaNat x < 2 ^ (T.intTy.bits - 1) := by
        unfold mantissaNat
        have h1 : 2 ^ (T.fmt.sb + 1) ≤ 2 ^ (T.intTy.bits - 1) :=
          Nat.pow_le_pow_right (by decide) hsb_le_i
        rw [Nat.pow_succ] at h1
        split <;> omega
      have hs_val : (int.bor (int.remT T.intTy (int.band (reinterpret_Unsigned x) smask))
          (int.shl_Int (int.ofBool T.intTy (!(int.eq e (int.lit .i64 0)))) sb)).val = (mantissaNat x : Int) := by
        rw [val_of_signed_small_pattern _ (by rw [hpat_bor]; exact hm_lt), hpat_bor]
      refine ⟨?_, ?_⟩
      · rw [remT_val, hs_val]
        apply wrapInt_of_inRange
        have hm_63 : mantissaNat x < 2 ^ 63 :=
          Nat.lt_of_lt_of_le hm_lt (Nat.pow_le_pow_right (by decide) hi_le_63)
        simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
      · rw [add_int_val, sub_int_val, he, hbs, heq0]
        have hofb : ∀ b : Bool, (int.ofBool .i64 b).val = if b then 1 else 0 := by intro b; cases b <;> rfl
        rw [hofb]
        have hsub_val : wrapInt .i64 ((x.expField : Int) - (T.fmt.bias + T.fmt.sb : Nat)) =
            (x.expField : Int) - (T.fmt.bias + T.fmt.sb : Nat) := by
          apply wrapInt_of_inRange; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
        rw [hsub_val]
        by_cases hx0 : x.expField = 0
        · simp only [hx0, decide_true, ↓reduceIte]
          rw [wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
          omega
        · simp only [hx0, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)]
          omega
    have hnum_pow_den :
        (decompose x).1.val = (mantissaNat x : Int) ∧
        (decompose x).2.1.val = (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
                                 else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) ∧
        (decompose x).2.2.val = (if x.signbit then -1 else 1) := by
      clear huns hbits_eq hsb_lt_u hsb_le_i hi_le_63 heb_2048 hbs_1075 hpat_b_false hpat_b_true hpat_n hf hexp_lt hfin
      cases T
      · have he16 := h_exp (int.lit .u16 0x7c00) (int.lit .i64 10) rfl rfl
        obtain ⟨hs16, hp16⟩ := h_s (int.lit .u16 0x03ff) (int.lit .i64 10) (int.lit .i64 25) _ rfl rfl rfl he16
        dsimp only [decompose, decompose_Float16, reinterpret_Unsigned] at hs16 hp16 ⊢
        simp only [hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs16, hp16, ?_⟩
        rw [hsign_eq]; cases x.signbit <;> rfl
      · have he32 := h_exp (int.lit .u32 0x7f800000) (int.lit .i64 23) rfl rfl
        obtain ⟨hs32, hp32⟩ := h_s (int.lit .u32 0x007fffff) (int.lit .i64 23) (int.lit .i64 150) _ rfl rfl rfl he32
        dsimp only [decompose, decompose_Float32, reinterpret_Unsigned] at hs32 hp32 ⊢
        simp only [hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs32, hp32, ?_⟩
        rw [hsign_eq]; cases x.signbit <;> rfl
      · have he64 := h_exp (int.lit .u64 0x7ff0000000000000) (int.lit .i64 52) rfl rfl
        obtain ⟨hs64, hp64⟩ := h_s (int.lit .u64 0x000fffffffffffff) (int.lit .i64 52) (int.lit .i64 1075) _ rfl rfl rfl he64
        dsimp only [decompose, decompose_Float64, reinterpret_Unsigned] at hs64 hp64 ⊢
        simp only [hnan_eq, hinf_eq, hnan, hinf, Bool.false_eq_true, ↓reduceIte]
        have hs64' : (int.bor (int.remT .i64 (int.band (reinterpret_Unsigned_Float64 x) (int.lit .u64 0x000fffffffffffff)))
            (int.shl_Int (int.ofBool .i64 (!(int.eq (int.remT .i64 (int.shr_Int (int.band (reinterpret_Unsigned_Float64 x) (int.lit .u64 0x7ff0000000000000)) (int.lit .i64 52))) (int.lit .i64 0)))) (int.lit .i64 52))).val =
            (mantissaNat x : Int) := by
          dsimp [FTy.intTy, FTy.uintTy, int.remT, int.rem_same] at hs64 ⊢; exact hs64
        refine ⟨hs64', hp64, ?_⟩
        rw [hsign_eq]; cases x.signbit <;> rfl
    obtain ⟨h1, h2, h3⟩ := hnum_pow_den
    refine ⟨h1, h2, h3, ?_⟩
    rw [h1, h2, h3]
    unfold Fl.toRat mantissaNat
    simp only [hfin, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
    generalize (if x.expField = 0 then 1 - (T.fmt.bias : Int) - (T.fmt.sb : Int)
      else (x.expField : Int) - (T.fmt.bias : Int) - (T.fmt.sb : Int)) = p
    generalize x.frac + (if x.expField = 0 then 0 else 2 ^ T.fmt.sb) = m
    cases x.signbit <;> split <;> simp

end JuliaLean.ChatGPT.Batch5.Group4.Widen


namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1

/-- Widening an IEEE operand to Float64 preserves all relevant exact data. -/
theorem mix_ws_widen_data {T : FTy} (x : FV T) :
    (convertFloat .f64 x).isnan = x.isnan ∧
    (convertFloat .f64 x).isinf = x.isinf ∧
    (convertFloat .f64 x).isfinite = x.isfinite ∧
    (x.isinf = true → (convertFloat .f64 x).signbit = x.signbit) ∧
    (x.isfinite = true →
      RatEq (convertFloat .f64 x).toRat x.toRat) := by
  cases T with
  | f16 =>
    rw [Widen.convertFloat_eq]
    have h := Widen.Fl.convert_widen_key Widen.good_half Widen.good_double
      (by decide) (by decide) (by decide) x
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun hf => (h.2.2.2.2 hf).2⟩
  | f32 =>
    rw [Widen.convertFloat_eq]
    have h := Widen.Fl.convert_widen_key Widen.good_single Widen.good_double
      (by decide) (by decide) (by decide) x
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun hf => (h.2.2.2.2 hf).2⟩
  | f64 =>
    exact ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem mix_ws_finite_of_not_special {T : FTy} (x : FV T)
    (hn : x.isnan = false) (hi : x.isinf = false) : x.isfinite = true := by
  unfold Fl.isnan at hn
  unfold Fl.isinf at hi
  unfold Fl.isfinite
  by_cases h : x.expField = T.fmt.emax
  · simp only [h, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at hn
    simp only [h, hn, beq_self_eq_true, Bool.true_and] at hi
    cases hi
  · exact bne_iff_ne.mpr h

theorem mix_ws_zero_rat_num {T : FTy} (x : FV T)
    (hz : x.iszero = true) : x.toRat.1 = 0 := by
  have hm : x.magnitude = 0 := by
    exact beq_iff_eq.mp hz
  have he : x.expField = 0 := by rw [Widen.Fl.expField_eq, hm, Nat.zero_div]
  have hf : x.frac = 0 := by rw [Widen.Fl.frac_eq, hm, Nat.zero_mod]
  unfold Fl.toRat
  rw [he, hf]
  cases x.isfinite <;> cases x.signbit <;>
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_false, ite_true, beq_self_eq_true, Nat.zero_add, Int.natCast_zero,
      Int.neg_zero, Int.zero_mul]
  all_goals split <;> rfl

/-- The source-mirrored decompose wrapper agrees with the independent IEEE rational decoder. -/
theorem mix_ws_ieee_value_rat {T : FTy} (x : FV T)
    (hf : x.isfinite = true) : RatEq (ieeeValue x).toRat x.toRat := by
  have hn := Widen.Fl.isnan_of_finite hf
  have hi := Widen.Fl.isinf_of_finite hf
  unfold ieeeValue
  simp only [hn, hi, Bool.false_eq_true, ite_false]
  by_cases hz : x.iszero = true
  · rw [hz]
    simp only [ite_true, FP.toRat, RatEq, Int.zero_mul, Int.natCast_one, Int.mul_one]
    exact (mix_ws_zero_rat_num x hz).symm
  · simp only [hz, Bool.false_eq_true, ite_false]
    have hd := (Widen.decompose_spec T x).2.2 hf
    have heq : (FP.finite ((decompose x).1.val * (decompose x).2.2.val)
        (decompose x).2.1.val).toRat = x.toRat := by
      rw [hd.2.2.2]
      by_cases he : 0 ≤ (decompose x).2.1.val
      · simpa only [FP.toRat, he, ite_true, Int.natCast_pow, Int.cast_ofNat_Int] using
          congrArg (fun z : Int => (z * 2 ^ (decompose x).2.1.val.toNat, (1 : Nat)))
            (Int.mul_comm (decompose x).1.val (decompose x).2.2.val)
      · simpa only [FP.toRat, he, ite_false, Int.natCast_one, Int.mul_one] using
          congrArg (fun z : Int => (z, 2 ^ (-(decompose x).2.1.val).toNat))
            (Int.mul_comm (decompose x).1.val (decompose x).2.2.val)
    rw [heq]
    rfl

/-- Finite IEEE inputs become finite (possibly signed-zero) MPFR values. -/
theorem mix_ws_ieee_value_finite {T : FTy} (x : FV T)
    (hf : x.isfinite = true) :
    (ieeeValue x).isnan = false ∧ (ieeeValue x).isinf = false := by
  have hn := Widen.Fl.isnan_of_finite hf
  have hi := Widen.Fl.isinf_of_finite hf
  simp only [ieeeValue, hn, hi, Bool.false_eq_true, ite_false]
  split <;> exact ⟨rfl, rfl⟩

/-- Exact value preservation needed by all six mixed BigFloat/IEEE comparison targets. -/
theorem mix_ws_ieee_widen_exact {T : FTy} (x : FV T) (hn : x.isnan = false) :
    NumericEq (ieeeValue (convertFloat .f64 x)) (ieeeValue x) := by
  obtain ⟨hwn, hwi, hwf, hws, hwr⟩ := mix_ws_widen_data x
  by_cases hi : x.isinf = true
  · simp only [ieeeValue, hwn, hn, hwi, hi, Bool.false_eq_true, ite_false,
      ite_true, NumericEq]
    exact hws hi
  · have hi' : x.isinf = false := Bool.eq_false_iff.mpr hi
    have hf := mix_ws_finite_of_not_special x hn hi'
    have hwf' : (convertFloat .f64 x).isfinite = true := hwf.trans hf
    have h1 := mix_ws_ieee_value_rat (convertFloat .f64 x) hwf'
    have h2 := hwr hf
    have h3 := mix_ws_ieee_value_rat x hf
    have h12 := cmp_rat_eq_trans _ _ _
      ((Widen.Fl.toRat_key (Widen.good_fty .f64) (convertFloat .f64 x) hwf').1) h1 h2
    obtain ⟨hfn, hfi⟩ := mix_ws_ieee_value_finite x hf
    obtain ⟨hwfn, hwfi⟩ := mix_ws_ieee_value_finite (convertFloat .f64 x) hwf'
    have h13 : RatEq (ieeeValue (convertFloat .f64 x)).toRat (ieeeValue x).toRat :=
      cmp_rat_eq_trans _ _ _
        ((Widen.Fl.toRat_key (Widen.good_fty T) x hf).1) h12 h3.symm
    cases hv : ieeeValue x <;> cases hwv : ieeeValue (convertFloat .f64 x) <;>
      simp only [hv, hwv, FP.isnan, FP.isinf] at hfn hfi hwfn hwfi <;>
      simp only [hv, hwv, NumericEq] <;> first | simpa only [hv, hwv] using h13 | contradiction

end JuliaLean.ChatGPT.Batch5.Group4


namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean.Proofs.base.mpfr.Round1

 theorem BignumscovMpfr1018V2_proven : JuliaLean.Proofs.base.mpfr.Round1.EqualIEEEValue := by
  intro T x y hx
  exact cmp_equalIEEE_of_extension x y hx (mix_ws_ieee_widen_exact y)

 theorem BignumscovMpfr1019V2_proven : JuliaLean.Proofs.base.mpfr.Round1.IEEEEqualValue := by
  intro T x y hy
  exact cmp_ieeeEqual_of_extension x y hy (mix_ws_ieee_widen_exact x)

 theorem BignumscovMpfr1023V2_proven : JuliaLean.Proofs.base.mpfr.Round1.LessIEEEValue := by
  intro T x y hx
  exact cmp_lessIEEE_of_extension x y hx (mix_ws_ieee_widen_exact y)

 theorem BignumscovMpfr1024V2_proven : JuliaLean.Proofs.base.mpfr.Round1.IEEELessValue := by
  intro T x y hy
  exact cmp_ieeeLess_of_extension x y hy (mix_ws_ieee_widen_exact x)

 theorem BignumscovMpfr1028V2_proven : JuliaLean.Proofs.base.mpfr.Round1.LessEqualIEEEValue := by
  intro T x y hx
  exact cmp_lessEqualIEEE_of_extension x y hx (mix_ws_ieee_widen_exact y)

 theorem BignumscovMpfr1029V2_proven : JuliaLean.Proofs.base.mpfr.Round1.IEEELessEqualValue := by
  intro T x y hy
  exact cmp_ieeeLessEqual_of_extension x y hy (mix_ws_ieee_widen_exact x)

end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

theorem cv_finite_den_pos {T : FTy} (z : FV T) (hz : z.isfinite = true) :
    0 < z.toRat.2 := by
  simp only [Fl.toRat, hz, Bool.not_true, Bool.false_eq_true, ite_false]
  split <;> split
  all_goals first | exact Nat.zero_lt_one | exact Nat.two_pow_pos _

theorem cv_finite_of_ordered {T : FTy} (z : FV T)
    (hn : z.isnan = false) (hi : z.isinf = false) : z.isfinite = true := by
  unfold Fl.isnan at hn
  unfold Fl.isinf at hi
  unfold Fl.isfinite
  by_cases h : z.expField = T.fmt.emax
  · simp only [h, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at hn
    simp only [h, hn, beq_self_eq_true, Bool.true_and] at hi
    cases hi
  · exact bne_iff_ne.mpr h

theorem cv_metric_den_pos {T : FTy} (z : FV T) (hn : z.isnan = false) :
    0 < (IEEMetricValue z).2 := by
  cases hi : z.isinf
  · simp only [IEEMetricValue, hi, Bool.false_eq_true, ite_false]
    exact cv_finite_den_pos z (cv_finite_of_ordered z hn hi)
  · simp only [IEEMetricValue, hi, ite_true]
    exact Nat.zero_lt_one

theorem cv_distance_eq_right (q a b : Int × Nat) (hab : RatEq a b) :
    RatEq (RatDistance q a) (RatDistance q b) := by
  have hc : (q.1 * (a.2 : Int) - a.1 * (q.2 : Int)) * (b.2 : Int) =
      (q.1 * (b.2 : Int) - b.1 * (q.2 : Int)) * (a.2 : Int) := by
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have he : a.1 * (b.2 : Int) * (q.2 : Int) =
        b.1 * (a.2 : Int) * (q.2 : Int) := congrArg (fun z => z * (q.2 : Int)) hab
    simp only [Int.ofNat_eq_natCast, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at he
    rw [he]
  have hn := congrArg Int.natAbs hc
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn
  have hi := congrArg (fun n : Nat => (n : Int)) hn
  simp only [Int.natCast_mul] at hi
  unfold RatEq RatDistance
  simp only [Int.natCast_mul]
  calc
    _ = (((q.1 * (a.2 : Int) - a.1 * (q.2 : Int)).natAbs : Int) *
        (b.2 : Int)) * (q.2 : Int) := by
          simp only [Int.ofNat_eq_natCast, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (((q.1 * (b.2 : Int) - b.1 * (q.2 : Int)).natAbs : Int) *
        (a.2 : Int)) * (q.2 : Int) := congrArg (fun z => z * (q.2 : Int)) hi
    _ = _ := by simp only [Int.ofNat_eq_natCast, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem cv_rat_le_left (a b c : Int × Nat) (ha : 0 < a.2) (hb : 0 < b.2)
    (hab : RatEq a b) : RatLe a c ↔ RatLe b c := by
  have h := cmp_rat_lt_right c a b ha hb hab
  unfold RatLe RatLt at *
  omega

theorem cv_exact_choice_except_tiesUp {T : FTy} (q : Int × Nat) (s : Bool)
    (z : FV T) (hq : 0 < q.2) (hzn : z.isnan = false)
    (hzi : z.isinf = false) (hzs : z.signbit = s)
    (heq : RatEq z.toRat q) (r : RoundingMode) (hr : r ≠ .NearestTiesUp) :
    IEEFiniteChoice r q s z := by
  have hzd := cv_finite_den_pos z (cv_finite_of_ordered z hzn hzi)
  have hmetric : IEEMetricValue z = z.toRat := by
    simp only [IEEMetricValue, hzi, Bool.false_eq_true, ite_false]
  have hm : RatEq (IEEMetricValue z) q := by rw [hmetric]; exact heq
  have hf := cmp_iee_floor_of_rat_eq q z hzi hq hzd heq
  have hc := cmp_iee_ceil_of_rat_eq q z hzi hq hzd heq
  refine ⟨hzn, hzs, hq, ?_⟩
  cases r with
  | Down => exact hf
  | Up => exact hc
  | ToZero => cases s <;> assumption
  | FromZero => cases s <;> assumption
  | Nearest =>
    exact cmp_iee_nearest_even_of_metric_eq q z hq (cv_metric_den_pos z hzn) hzn hm
  | NearestTiesAway =>
    refine ⟨cmp_iee_nearest_of_metric_eq q z hm, ?_⟩
    intro y _ hy
    have he := cmp_iee_nearest_metric_unique q z hq (cv_metric_den_pos z hzn) hzn hm y hy
    exact cmp_rat_le_of_eq _ _ (cv_distance_eq_right (0, 1) _ _ he)
  | NearestTiesUp => exact False.elim (hr rfl)

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

theorem cv_distance_symm (a b : Int × Nat) : RatDistance a b = RatDistance b a := by
  have h : a.1 * (b.2 : Int) - b.1 * (a.2 : Int) =
      -(b.1 * (a.2 : Int) - a.1 * (b.2 : Int)) := by omega
  simp only [RatDistance, h, Int.natAbs_neg, Nat.mul_comm]

theorem cv_distance_eq_left (a b y : Int × Nat) (hab : RatEq a b) :
    RatEq (RatDistance a y) (RatDistance b y) := by
  rw [cv_distance_symm a y, cv_distance_symm b y]
  exact cv_distance_eq_right y a b hab

theorem cv_distance_congr (a b x y : Int × Nat)
    (hb : 0 < b.2) (hx : 0 < x.2) (hab : RatEq a b) (hxy : RatEq x y) :
    RatEq (RatDistance a x) (RatDistance b y) :=
  cmp_rat_eq_trans _ _ _ (cmp_distance_den_pos b x hb hx)
    (cv_distance_eq_left a b x hab) (cv_distance_eq_right b x y hxy)

theorem cv_rat_le_congr (a b x y : Int × Nat)
    (ha : 0 < a.2) (hb : 0 < b.2) (hx : 0 < x.2) (hy : 0 < y.2)
    (hab : RatEq a b) (hxy : RatEq x y) : RatLe a x ↔ RatLe b y := by
  exact (cv_rat_le_left a b x ha hb hab).trans (cmp_rat_le_right b x y hx hy hxy)

theorem cv_distance_scaled (n z : Int) (k d : Nat) :
    RatEq (RatDistance (n, k*d) (z, d)) (((z*(k : Int)-n).natAbs : Int), k*d) := by
  have h : n*(d : Int) - z*((k*d : Nat) : Int) = -(z*(k : Int)-n)*(d : Int) := by
    simp only [Int.natCast_mul, Int.neg_mul, Int.sub_mul, Int.mul_assoc]
    omega
  unfold RatEq RatDistance
  dsimp only
  rw [h, Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem cv_distance_scaled_le (n z y : Int) (k d : Nat) (hk : 0 < k) (hd : 0 < d) :
    RatLe (RatDistance (n, k*d) (z, d)) (RatDistance (n, k*d) (y, d)) ↔
      (z*(k : Int)-n).natAbs ≤ (y*(k : Int)-n).natAbs := by
  have hkd : 0 < k*d := Nat.mul_pos hk hd
  have hzden : 0 < (RatDistance (n, k*d) (z, d)).2 :=
    cmp_distance_den_pos _ _ hkd hd
  have hyden : 0 < (RatDistance (n, k*d) (y, d)).2 :=
    cmp_distance_den_pos _ _ hkd hd
  rw [cv_rat_le_congr _ _ _ _ hzden hkd hyden hkd
    (cv_distance_scaled n z k d) (cv_distance_scaled n y k d)]
  unfold RatLe
  dsimp only
  have hc : (0 : Int) < (k*d : Nat) := by omega
  rw [Int.mul_le_mul_right hc]
  omega

theorem cv_floor_congr {T : FTy} (a b : Int × Nat) (z : FV T)
    (ha : 0 < a.2) (hb : 0 < b.2) (hab : RatEq a b) :
    IEEFloor a z ↔ IEEFloor b z := by
  have he : ∀ y : FV T, IEELeExact y a ↔ IEELeExact y b := by
    intro y
    unfold IEELeExact
    split
    · rfl
    · exact cmp_rat_le_right y.toRat a b ha hb hab
  unfold IEEFloor
  simp only [he]

theorem cv_ceil_congr {T : FTy} (a b : Int × Nat) (z : FV T)
    (ha : 0 < a.2) (hb : 0 < b.2) (hab : RatEq a b) :
    IEECeil a z ↔ IEECeil b z := by
  have he : ∀ y : FV T, ExactLeIEE a y ↔ ExactLeIEE b y := by
    intro y
    unfold ExactLeIEE
    split
    · rfl
    · exact cv_rat_le_left a b y.toRat ha hb hab
  unfold IEECeil
  simp only [he]

theorem cv_nearest_congr {T : FTy} (a b : Int × Nat) (z : FV T)
    (ha : 0 < a.2) (hb : 0 < b.2) (hab : RatEq a b) (hz : z.isnan = false) :
    IEENearest a z ↔ IEENearest b z := by
  have hzd := cv_metric_den_pos z hz
  have he : ∀ y : FV T, y.isnan = false →
      (RatLe (RatDistance a (IEEMetricValue z)) (RatDistance a (IEEMetricValue y)) ↔
       RatLe (RatDistance b (IEEMetricValue z)) (RatDistance b (IEEMetricValue y))) := by
    intro y hy
    have hyd := cv_metric_den_pos y hy
    exact cv_rat_le_congr _ _ _ _
      (cmp_distance_den_pos _ _ ha hzd) (cmp_distance_den_pos _ _ hb hzd)
      (cmp_distance_den_pos _ _ ha hyd) (cmp_distance_den_pos _ _ hb hyd)
      (cv_distance_eq_left a b _ hab) (cv_distance_eq_left a b _ hab)
  constructor
  · intro h y hy
    exact (he y hy).mp (h y hy)
  · intro h y hy
    exact (he y hy).mpr (h y hy)

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

theorem cv_choice_congr_forward {T : FTy} (r : RoundingMode)
    (a b : Int × Nat) (s : Bool) (z : FV T)
    (ha : 0 < a.2) (hb : 0 < b.2) (hab : RatEq a b)
    (h : IEEFiniteChoice r a s z) : IEEFiniteChoice r b s z := by
  rcases h with ⟨hzn, hzs, _, hm⟩
  refine ⟨hzn, hzs, hb, ?_⟩
  cases r with
  | Down => exact (cv_floor_congr a b z ha hb hab).mp hm
  | Up => exact (cv_ceil_congr a b z ha hb hab).mp hm
  | ToZero =>
    cases s
    · exact (cv_floor_congr a b z ha hb hab).mp hm
    · exact (cv_ceil_congr a b z ha hb hab).mp hm
  | FromZero =>
    cases s
    · exact (cv_ceil_congr a b z ha hb hab).mp hm
    · exact (cv_floor_congr a b z ha hb hab).mp hm
  | Nearest =>
    refine ⟨(cv_nearest_congr a b z ha hb hab hzn).mp hm.1, ?_⟩
    intro y hy hnear hne
    exact hm.2 y hy ((cv_nearest_congr a b y ha hb hab hy).mpr hnear) hne
  | NearestTiesAway =>
    refine ⟨(cv_nearest_congr a b z ha hb hab hzn).mp hm.1, ?_⟩
    intro y hy hnear
    exact hm.2 y hy ((cv_nearest_congr a b y ha hb hab hy).mpr hnear)
  | NearestTiesUp =>
    refine ⟨(cv_nearest_congr a b z ha hb hab hzn).mp hm.1, ?_⟩
    intro y hy hnear
    exact hm.2 y hy ((cv_nearest_congr a b y ha hb hab hy).mpr hnear)

theorem cv_choice_congr {T : FTy} (r : RoundingMode)
    (a b : Int × Nat) (s : Bool) (z : FV T)
    (ha : 0 < a.2) (hb : 0 < b.2) (hab : RatEq a b) :
    IEEFiniteChoice r a s z ↔ IEEFiniteChoice r b s z :=
  ⟨cv_choice_congr_forward r a b s z ha hb hab,
   cv_choice_congr_forward r b a s z hb ha hab.symm⟩

end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64

theorem cv_enc_carry_pack (f : Fmt) (s : Bool) (B q : Nat) :
    (Fl.ofBits ((if s then 2^(f.eb+f.sb) else 0) + (B*2^f.sb+q)) : Fl f) =
      Widen.Fl.pack s (B+q/2^f.sb) (q%2^f.sb) := by
  have hh : (B+q/2^f.sb)*2^f.sb + q%2^f.sb = B*2^f.sb+q := by
    rw [Nat.add_mul, Nat.add_assoc, Nat.mul_comm (q/2^f.sb) (2^f.sb), Nat.div_add_mod]
  unfold Widen.Fl.pack
  rw [hh]

theorem cv_enc_carry_parts (f : Fmt) (s : Bool) (B q : Nat)
    (hb : B+q/2^f.sb < 2^f.eb) :
    let z : Fl f := Fl.ofBits ((if s then 2^(f.eb+f.sb) else 0) + (B*2^f.sb+q))
    z.signbit = s ∧ z.expField = B+q/2^f.sb ∧
      z.frac = q%2^f.sb ∧ z.magnitude = B*2^f.sb+q := by
  dsimp only
  rw [cv_enc_carry_pack]
  have hh := Widen.Fl.pack_parts (f := f) s (B+q/2^f.sb) (q%2^f.sb) hb
    (Nat.mod_lt _ (Nat.pow_pos (by decide)))
  refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
  rw [hh.2.2.2, Nat.add_mul, Nat.add_assoc,
    Nat.mul_comm (q/2^f.sb) (2^f.sb), Nat.div_add_mod]

theorem cv_enc_low_bit (T : FTy) (s : Bool) (B q : Nat) :
    (Fl.ofBits ((if s then 2^(T.fmt.eb+T.fmt.sb) else 0) +
      (B*2^T.fmt.sb+q)) : FV T).toBits % 2 = q % 2 := by
  unfold Fl.toBits Fl.ofBits
  cases T <;> cases s <;>
    simp only [FTy.fmt, half, single, double, Fmt.width,
      Bool.false_eq_true, ite_false, ite_true] <;> omega

end JuliaLean.ChatGPT.Batch5.Group4


namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.ChatGPT.Batch5.Group4.Widen.TruncProofs

theorem cv_pack_binop_bor {s t : IntTy} (x : JInt s) (y : JInt t) :
    int.binop int.bor x y =
      int.bor (int.remT (s.promote t) x) (int.remT (s.promote t) y) := by
  unfold int.binop int.op_Integer
  split <;> rfl

theorem cv_pack_rem_pattern {s : IntTy} (t : IntTy) (x : JInt s)
    (h0 : 0 ≤ x.val) (hr : t.min ≤ x.val ∧ x.val ≤ t.max) :
    pattern (int.remT t x) = x.val.toNat := by
  have hv : (int.remT t x).val = x.val := by
    rw [remT_val, wrapInt_of_inRange t x.val hr]
  rw [pattern_of_nonneg _ (by rw [hv]; exact h0), hv]

theorem cv_pack_bor_same (t : IntTy) (a b : JInt t) :
    int.remT t (int.binop int.bor a b) = int.bor a b := by
  cases t <;>
    simp [int.remT, int.rem_same, int.binop, IntTy.promote, IntTy.signed]

theorem cv_pack_increment_bits (T : FTy) (u : JInt T.uintTy) (increment : Bool)
    (hb : u.val.toNat + (if increment then 1 else 0) < 2^T.uintTy.bits) :
    (u + JInt.wrap T.uintTy (if increment then 1 else 0)).val.toNat =
      u.val.toNat + (if increment then 1 else 0) := by
  have hu := u.property
  have hty : T.uintTy.signed = false := by cases T <;> rfl
  have hmin : T.uintTy.min = 0 := by cases T <;> rfl
  have hmax : T.uintTy.max = (2^T.uintTy.bits : Int)-1 := by cases T <;> rfl
  have hi : (JInt.wrap T.uintTy (if increment then 1 else 0)).val =
      if increment then 1 else 0 := by cases T <;> cases increment <;> decide
  have hu0 : 0 ≤ u.val := by omega
  have hv : (u + JInt.wrap T.uintTy (if increment then 1 else 0)).val =
      u.val + (if increment then 1 else 0) := by
    change wrapInt T.uintTy (u.val +
      (JInt.wrap T.uintTy (if increment then 1 else 0)).val) = _
    rw [hi]
    apply wrapInt_of_inRange
    have hc : ((2^T.uintTy.bits : Nat) : Int) = (2 : Int)^T.uintTy.bits :=
      Int.natCast_pow 2 T.uintTy.bits
    cases increment <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hb ⊢ <;> omega
  rw [hv]
  cases increment <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

def cv_diff (T : FTy) (x : BigFloat) : Clong :=
  x.exp - JInt.wrap .i64 1 - exponent_min T

def cv_len (T : FTy) (x : BigFloat) : Nat :=
  (max (precision_Type_default T + JInt.wrap .i64 (min (cv_diff T x).val 0)).val 0).toNat

def cv_discard (T : FTy) (x : BigFloat) : Nat := x.d.length * 64 - cv_len T x

def cv_kept (T : FTy) (x : BigFloat) : Nat := limbMagnitude x.d / 2 ^ cv_discard T x

def cv_lost (T : FTy) (x : BigFloat) : Nat := limbMagnitude x.d % 2 ^ cv_discard T x

def cv_rounded (T : FTy) (x : BigFloat) (r : RoundingMode) : Nat :=
  cv_kept T x + if ieeeIncrement r (signbit x) (cv_kept T x) (cv_lost T x)
    (2 ^ cv_discard T x) then 1 else 0

def cv_base (T : FTy) (x : BigFloat) : Nat := (max (cv_diff T x).val 0).toNat

theorem cv_discard_pos (T : FTy) (x : BigFloat) (hx : ValidBigFloat x) :
    0 < cv_discard T x := cls_ieee_discarded_pos T x (cv_diff T x) hx

theorem cv_kept_bounds (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    (0 ≤ (cv_diff T x).val → 2^T.fmt.sb ≤ cv_kept T x ∧
      cv_kept T x < 2^(T.fmt.sb+1)) ∧
    ((cv_diff T x).val < 0 → cv_kept T x < 2^T.fmt.sb) := by
  constructor
  · intro hd
    exact cls_quant_normal_kept T x hx m e hv (cv_diff T x) hd
  · intro hd
    exact cls_quant_subnormal_kept T x hx m e hv (cv_diff T x) hd

theorem cv_finite_classification (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    iszero x = false ∧ isinf x = false ∧ isnan x = false ∧
      signbit x = decide (m < 0) := by
  have hm := cls_finite_mantissa_ne_zero x hx m e hv
  rw [cls_iszero x hx, cls_isinf x hx, cls_isnan x hx, cls_signbit x hx, hv]
  simp only [FP.iszero, FP.isinf, FP.isnan, FP.signbit, hm, decide_false, and_self]

theorem cv_main_range_flags (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : x.exp.val - 1 ≤ (exponent_max T).val)
    (hlo : 0 ≤ x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val) :
    decide ((exponent_max T).val < (x.exp-JInt.wrap .i64 1).val) = false ∧
      decide ((cv_diff T x + precision_Type_default T).val < 0) = false := by
  constructor
  · rw [cls_exp_ieeeExp x hx m e hv]
    exact decide_eq_false (by omega)
  · unfold cv_diff
    rw [cls_exp_diff_plus_precision T x hx m e hv]
    exact decide_eq_false (by omega)

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

theorem cv_format_relations (T : FTy) :
    1 ≤ T.fmt.sb ∧ 3 ≤ T.fmt.emax ∧ T.fmt.emax ≤ 2047 ∧
    (exponent_max T).val - (exponent_min T).val = (T.fmt.emax : Int) - 2 ∧
    T.uintTy.bits = T.fmt.width := by
  cases T <;> decide

theorem cv_base_bound (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : x.exp.val - 1 ≤ (exponent_max T).val) :
    cv_base T x ≤ T.fmt.emax - 2 := by
  have hd := cls_exp_expDiff T x hx m e hv
  have hf := cv_format_relations T
  change (cv_diff T x).val = _ at hd
  unfold cv_base
  omega

theorem cv_field_value (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : x.exp.val - 1 ≤ (exponent_max T).val) :
    let E := JInt.wrap .i64 (max (cv_diff T x).val 0 +
      if decide ((cv_diff T x).val ≥ 0) then 1 else 0)
    0 ≤ E.val ∧ E.val.toNat = cv_base T x +
      (if decide ((cv_diff T x).val ≥ 0) then 1 else 0) ∧
      E.val.toNat < 2^T.fmt.eb := by
  have hb := cv_base_bound T x hx m e hv hhi
  have hf := cv_format_relations T
  have hM : T.fmt.emax < 2^T.fmt.eb := by
    unfold Fmt.emax
    have hp := Nat.two_pow_pos T.fmt.eb
    omega
  have hvv : (JInt.wrap .i64 (max (cv_diff T x).val 0 +
      if decide ((cv_diff T x).val ≥ 0) then 1 else 0)).val =
      max (cv_diff T x).val 0 +
      if decide ((cv_diff T x).val ≥ 0) then 1 else 0 := by
    change wrapInt .i64 _ = _
    apply wrapInt_of_inRange
    change -(2 : Int)^63 ≤ _ ∧ _ ≤ (2 : Int)^63-1
    unfold cv_base at hb
    cases decide ((cv_diff T x).val ≥ 0) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  dsimp only
  rw [hvv]
  unfold cv_base at *
  cases decide ((cv_diff T x).val ≥ 0) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem cv_significand_value (T : FTy) (q : Nat) :
    (JInt.wrap T.uintTy ((q % 2^T.fmt.sb : Nat) : Int)).val.toNat = q % 2^T.fmt.sb := by
  have hq := Nat.mod_lt q (Nat.two_pow_pos T.fmt.sb)
  have hr : T.uintTy.min ≤ ((q % 2^T.fmt.sb : Nat) : Int) ∧
      ((q % 2^T.fmt.sb : Nat) : Int) ≤ T.uintTy.max := by
    cases T <;> simp only [FTy.fmt, FTy.uintTy, half, single, double, IntTy.min, IntTy.max,
      IntTy.signed, IntTy.bits, Bool.false_eq_true, ite_false] at * <;> omega
  change (wrapInt T.uintTy _).toNat = _
  rw [wrapInt_of_inRange T.uintTy _ hr, Int.toNat_natCast]

theorem cv_masked_base (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    (cv_base T x + (if decide ((cv_diff T x).val ≥ 0) then 1 else 0))*2^T.fmt.sb +
      cv_kept T x % 2^T.fmt.sb = cv_base T x * 2^T.fmt.sb + cv_kept T x := by
  have hk := cv_kept_bounds T x hx m e hv
  by_cases hd : 0 ≤ (cv_diff T x).val
  · simp only [hd, decide_true, ite_true]
    exact cls_quant_normal_mask _ _ _ (hk.1 hd).1 (hk.1 hd).2
  · have hd' : (cv_diff T x).val < 0 := by omega
    simp only [hd, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero,
      Nat.mod_eq_of_lt (hk.2 hd')]

theorem cv_rounded_magnitude_bound (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hhi : x.exp.val - 1 ≤ (exponent_max T).val) :
    cv_base T x * 2^T.fmt.sb + cv_rounded T x r ≤ T.fmt.emax * 2^T.fmt.sb := by
  have hb := cv_base_bound T x hx m e hv hhi
  have hk := cv_kept_bounds T x hx m e hv
  have hp := Nat.two_pow_pos T.fmt.sb
  have hf := cv_format_relations T
  by_cases hd : 0 ≤ (cv_diff T x).val
  · have hq := (hk.1 hd).2
    have hm := Nat.mul_le_mul_right (2^T.fmt.sb) hb
    have hsplit : (T.fmt.emax-2) * 2^T.fmt.sb + 2 * 2^T.fmt.sb =
        T.fmt.emax * 2^T.fmt.sb := by
      rw [← Nat.add_mul]
      congr 1
      omega
    unfold cv_rounded
    rw [Nat.pow_succ] at hq
    split <;> omega
  · have hd' : (cv_diff T x).val < 0 := by omega
    have hq := hk.2 hd'
    have hbase : cv_base T x = 0 := by unfold cv_base; omega
    have hmul := Nat.mul_le_mul_right (2^T.fmt.sb) (show 1 ≤ T.fmt.emax by omega)
    rw [Nat.one_mul] at hmul
    unfold cv_rounded
    rw [hbase, Nat.zero_mul, Nat.zero_add]
    split <;> omega

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

/-- Every magnitude at or below the infinity code decodes with the chosen sign
    and is not a NaN; the endpoint is exactly infinity. -/
theorem cv_ordered_pack (T : FTy) (s : Bool) (M : Nat)
    (hM : M ≤ T.fmt.emax * 2^T.fmt.sb) :
    let z : FV T := Fl.ofBits ((if s then 2^(T.fmt.eb+T.fmt.sb) else 0) + M)
    z.signbit = s ∧ z.magnitude = M ∧ z.isnan = false ∧
      (z.isinf = true ↔ M = T.fmt.emax * 2^T.fmt.sb) := by
  have hp := Nat.two_pow_pos T.fmt.sb
  have he : T.fmt.emax < 2^T.fmt.eb := by
    unfold Fmt.emax
    have ht := Nat.two_pow_pos T.fmt.eb
    omega
  have hb : M / 2^T.fmt.sb < 2^T.fmt.eb := by
    have hbound := Nat.div_le_div_right (c := 2^T.fmt.sb) hM
    rw [Nat.mul_div_cancel _ hp] at hbound
    omega
  have hrepr : M = M / 2^T.fmt.sb * 2^T.fmt.sb + M%2^T.fmt.sb := by
    have h := Nat.div_add_mod M (2^T.fmt.sb)
    simpa only [Nat.mul_comm] using h.symm
  have hh := Widen.Fl.pack_parts (f := T.fmt) s (M/2^T.fmt.sb) (M%2^T.fmt.sb)
    hb (Nat.mod_lt _ hp)
  have heq : (Fl.ofBits ((if s then 2^(T.fmt.eb+T.fmt.sb) else 0) + M) : FV T) =
      Widen.Fl.pack s (M/2^T.fmt.sb) (M%2^T.fmt.sb) := by
    unfold Widen.Fl.pack
    rw [← hrepr]
  dsimp only
  rw [heq]
  refine ⟨hh.1, ?_, ?_, ?_⟩
  · rw [hh.2.2.2]
    exact hrepr.symm
  · unfold Fl.isnan
    rw [hh.2.1, hh.2.2.1]
    by_cases hE : M / 2^T.fmt.sb = T.fmt.emax
    · have hr : M%2^T.fmt.sb = 0 := by
        rw [hE] at hrepr
        omega
      simp only [hE, hr, beq_self_eq_true, bne_self_eq_false, Bool.and_false]
    · simp only [beq_eq_false_iff_ne.mpr hE, Bool.false_and]
  · unfold Fl.isinf
    rw [hh.2.1, hh.2.2.1]
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h
      rw [h.1, h.2, Nat.add_zero] at hrepr
      exact hrepr
    · intro h
      rw [h, Nat.mul_div_cancel _ hp, Nat.mul_mod_left]
      exact ⟨rfl, rfl⟩

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

theorem cv_scale_exponent (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hlo : 0 ≤ x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val) :
    x.exp.val - (cv_len T x : Int) + ((T.fmt.bias+T.fmt.sb-1 : Nat) : Int) =
      (cv_base T x : Int) := by
  have hd := cls_exp_expDiff T x hx m e hv
  have hlen := cls_ieee_len_add T (cv_diff T x)
  have hp := cls_quant_precision T
  have hemin : (exponent_min T).val = 1 - (T.fmt.bias : Int) := by
    cases T <;> decide
  have hbias : 1 ≤ T.fmt.bias := by cases T <;> decide
  change (cv_diff T x).val = _ at hd
  unfold cv_len cv_base
  rw [hlen, hp]
  rw [hp] at hlo
  omega

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1

theorem magKey_zero (f : Fmt) : magKey f 0 = 0 := by simp [magKey]

theorem magKey_lt (f : Fmt) (M : Nat) : magKey f M < 2 ^ f.sb * 2 ^ (M / 2 ^ f.sb) := by
  have hr := Nat.mod_lt M (Nat.two_pow_pos f.sb)
  unfold magKey
  generalize M / 2 ^ f.sb = e
  generalize M % 2 ^ f.sb = r at hr
  generalize 2 ^ f.sb = P at *
  cases e with
  | zero => simpa using hr
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
  rw [if_neg h]
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

theorem magKey_cases (f : Fmt) (a : Nat) :
    (a = 0 ∧ magKey f a = 0) ∨ (0 < a ∧ 0 < magKey f a) := by
  rcases Nat.eq_zero_or_pos a with h | h
  · exact Or.inl ⟨h, h ▸ magKey_zero f⟩
  · exact Or.inr ⟨h, magKey_zero f ▸ magKey_strictMono f h⟩

theorem magKey_mono (f : Fmt) {a b : Nat} (h : a ≤ b) : magKey f a ≤ magKey f b := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Nat.le_of_lt (magKey_strictMono f h)
  · rw [h]
    exact Nat.le_refl _

theorem magKey_le_iff (f : Fmt) (a b : Nat) : magKey f a ≤ magKey f b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases hab : a ≤ b
    · exact hab
    · have hba := magKey_strictMono f (Nat.lt_of_not_ge hab)
      omega
  · exact magKey_mono f

theorem magKey_lt_iff (f : Fmt) (a b : Nat) : magKey f a < magKey f b ↔ a < b := by
  constructor
  · intro h
    by_cases hab : a < b
    · exact hab
    · have hba := magKey_mono f (Nat.le_of_not_gt hab)
      omega
  · exact magKey_strictMono f

theorem magKey_inj (f : Fmt) (a b : Nat) : magKey f a = magKey f b ↔ a = b := by
  constructor
  · intro h
    have hab := (magKey_le_iff f a b).mp (Nat.le_of_eq h)
    have hba := (magKey_le_iff f b a).mp (Nat.le_of_eq h.symm)
    omega
  · intro h
    rw [h]

theorem magKey_adjacent (f : Fmt) (M y : Nat) :
    magKey f y ≤ magKey f M ∨ magKey f (M + 1) ≤ magKey f y := by
  by_cases h : y ≤ M
  · exact Or.inl (magKey_mono f h)
  · exact Or.inr (magKey_mono f (by omega))

theorem magKey_parts (f : Fmt) (B r : Nat) (hr : r < 2 ^ f.sb) :
    magKey f (B * 2 ^ f.sb + r) =
      (r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) := by
  have hd : (B * 2 ^ f.sb + r) / 2 ^ f.sb = B := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hr, Nat.zero_add]
  have hm : (B * 2 ^ f.sb + r) % 2 ^ f.sb = r := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr]
  unfold magKey
  rw [hd, hm]

theorem magKey_carry (f : Fmt) (B q : Nat) :
    magKey f (B * 2 ^ f.sb + q) =
      (q % 2 ^ f.sb + if B + q / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) *
        2 ^ (B + q / 2 ^ f.sb - 1) := by
  have hparts : B * 2 ^ f.sb + q =
      (B + q / 2 ^ f.sb) * 2 ^ f.sb + q % 2 ^ f.sb := by
    rw [Nat.add_mul, Nat.add_assoc, Nat.div_add_mod']
  rw [hparts]
  exact magKey_parts f _ _ (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem magKey_step (f : Fmt) (M : Nat) :
    magKey f (M + 1) = magKey f M + 2 ^ (M / 2 ^ f.sb - 1) := by
  let P := 2 ^ f.sb
  let B := M / P
  let r := M % P
  have hP : 0 < P := Nat.two_pow_pos _
  have hr : r < P := Nat.mod_lt M hP
  have hM : M = B * P + r := by
    have h := Nat.div_add_mod M P
    change P * B + r = M at h
    rw [Nat.mul_comm P B] at h
    exact h.symm
  have hbase := magKey_parts f B r hr
  change magKey f (B * P + r) = (r + if B = 0 then 0 else P) * 2 ^ (B - 1) at hbase
  change magKey f (M + 1) = magKey f M + 2 ^ (B - 1)
  by_cases hnext : r + 1 < P
  · have hMnext : M + 1 = B * P + (r + 1) := by omega
    rw [hMnext, magKey_parts f B (r + 1) hnext, hM, hbase]
    rw [show r + 1 + (if B = 0 then 0 else P) =
      (r + if B = 0 then 0 else P) + 1 by omega, Nat.add_mul, Nat.one_mul]
  · have hrP : r + 1 = P := by omega
    have hMnext : M + 1 = (B + 1) * P + 0 := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hMnext, magKey_parts f (B + 1) 0 hP, hM, hbase]
    cases B with
    | zero =>
        simp only [Nat.zero_add, Nat.zero_sub, Nat.sub_self, Nat.pow_zero,
          Nat.mul_one, Nat.reduceAdd, ite_true, ite_false, Nat.one_ne_zero]
        omega
    | succ b =>
        simp only [Nat.succ_ne_zero, Nat.add_one_ne_zero, ite_false, Nat.zero_add,
          Nat.succ_sub_one, Nat.add_sub_cancel]
        calc P * 2 ^ (b + 1) = (P + P) * 2 ^ b := by
              rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul]
              omega
          _ = (r + P + 1) * 2 ^ b := by congr 1; omega
          _ = (r + P) * 2 ^ b + 2 ^ b := by rw [Nat.add_mul, Nat.one_mul]

theorem magKey_floor_index (f : Fmt) (M : Nat) (n d : Int) (hd : 0 ≤ d)
    (hhi : n < (magKey f (M + 1) : Int) * d) :
    ∀ y : Nat, (magKey f y : Int) * d ≤ n → y ≤ M := by
  intro y hy
  by_cases hyM : y ≤ M
  · exact hyM
  · have hkey := magKey_mono f (show M + 1 ≤ y by omega)
    have hscale := Int.mul_le_mul_of_nonneg_right
      (show (magKey f (M + 1) : Int) ≤ (magKey f y : Int) by omega) hd
    omega

theorem magKey_ceil_index (f : Fmt) (M : Nat) (n d : Int) (hd : 0 ≤ d)
    (hlo : (magKey f M : Int) * d < n) :
    ∀ y : Nat, n ≤ (magKey f y : Int) * d → M + 1 ≤ y := by
  intro y hy
  by_cases hyM : M + 1 ≤ y
  · exact hyM
  · have hkey := magKey_mono f (show y ≤ M by omega)
    have hscale := Int.mul_le_mul_of_nonneg_right
      (show (magKey f y : Int) ≤ (magKey f M : Int) by omega) hd
    omega

theorem magKey_nearest_lower (f : Fmt) (M : Nat) (n d : Int) (hd : 0 ≤ d)
    (hlo : (magKey f M : Int) * d ≤ n)
    (hmid : 2 * n ≤ ((magKey f M : Int) + (magKey f (M + 1) : Int)) * d) :
    ∀ y : Nat, ((magKey f M : Int) * d - n).natAbs ≤
      ((magKey f y : Int) * d - n).natAbs := by
  rw [Int.add_mul] at hmid
  intro y
  have hbase := Int.natAbs_eq ((magKey f M : Int) * d - n)
  have hother := Int.natAbs_eq ((magKey f y : Int) * d - n)
  rcases magKey_adjacent f M y with hy | hy
  · have hscale := Int.mul_le_mul_of_nonneg_right
      (show (magKey f y : Int) ≤ (magKey f M : Int) by omega) hd
    rcases hbase with hbase | hbase <;> rcases hother with hother | hother <;> omega
  · have hscale := Int.mul_le_mul_of_nonneg_right
      (show (magKey f (M + 1) : Int) ≤ (magKey f y : Int) by omega) hd
    rcases hbase with hbase | hbase <;> rcases hother with hother | hother <;> omega

theorem magKey_nearest_upper (f : Fmt) (M : Nat) (n d : Int) (hd : 0 ≤ d)
    (hhi : n ≤ (magKey f (M + 1) : Int) * d)
    (hmid : ((magKey f M : Int) + (magKey f (M + 1) : Int)) * d ≤ 2 * n) :
    ∀ y : Nat, ((magKey f (M + 1) : Int) * d - n).natAbs ≤
      ((magKey f y : Int) * d - n).natAbs := by
  rw [Int.add_mul] at hmid
  intro y
  have hbase := Int.natAbs_eq ((magKey f (M + 1) : Int) * d - n)
  have hother := Int.natAbs_eq ((magKey f y : Int) * d - n)
  rcases magKey_adjacent f M y with hy | hy
  · have hscale := Int.mul_le_mul_of_nonneg_right
      (show (magKey f y : Int) ≤ (magKey f M : Int) by omega) hd
    rcases hbase with hbase | hbase <;> rcases hother with hother | hother <;> omega
  · have hscale := Int.mul_le_mul_of_nonneg_right
      (show (magKey f (M + 1) : Int) ≤ (magKey f y : Int) by omega) hd
    rcases hbase with hbase | hbase <;> rcases hother with hother | hother <;> omega

theorem magKey_nearest_only_neighbors (f : Fmt) (M y : Nat) (n d : Int) (hd : 0 < d)
    (hlo : (magKey f M : Int) * d ≤ n)
    (hhi : n ≤ (magKey f (M + 1) : Int) * d)
    (hmin : ∀ z : Nat, ((magKey f y : Int) * d - n).natAbs ≤
      ((magKey f z : Int) * d - n).natAbs) :
    y = M ∨ y = M + 1 := by
  have hay := Int.natAbs_eq ((magKey f y : Int) * d - n)
  by_cases hylo : y < M
  · have hkey := magKey_strictMono f hylo
    have hscale := Int.mul_lt_mul_of_pos_right
      (show (magKey f y : Int) < (magKey f M : Int) by omega) hd
    have hdist := hmin M
    have hab := Int.natAbs_eq ((magKey f M : Int) * d - n)
    rcases hay with hay | hay <;> rcases hab with hab | hab <;> omega
  · by_cases hyhi : M + 1 < y
    · have hkey := magKey_strictMono f hyhi
      have hscale := Int.mul_lt_mul_of_pos_right
        (show (magKey f (M + 1) : Int) < (magKey f y : Int) by omega) hd
      have hdist := hmin (M + 1)
      have hab := Int.natAbs_eq ((magKey f (M + 1) : Int) * d - n)
      rcases hay with hay | hay <;> rcases hab with hab | hab <;> omega
    · omega

theorem magKey_nearest_max (f : Fmt) (M : Nat) (n d : Int) (hd : 0 ≤ d)
    (hhi : (magKey f M : Int) * d ≤ n) :
    ∀ y : Nat, y ≤ M → ((magKey f M : Int) * d - n).natAbs ≤
      ((magKey f y : Int) * d - n).natAbs := by
  intro y hy
  have hkey := magKey_mono f hy
  have hscale := Int.mul_le_mul_of_nonneg_right
    (show (magKey f y : Int) ≤ (magKey f M : Int) by omega) hd
  have hbase := Int.natAbs_eq ((magKey f M : Int) * d - n)
  have hother := Int.natAbs_eq ((magKey f y : Int) * d - n)
  rcases hbase with hbase | hbase <;> rcases hother with hother | hother <;> omega

theorem magKey_nearest_signed (f : Fmt) (M : Nat) (n d : Int)
    (hn : 0 ≤ n) (hd : 0 ≤ d)
    (hmin : ∀ y : Nat, ((magKey f M : Int) * d - n).natAbs ≤
      ((magKey f y : Int) * d - n).natAbs) :
    ∀ (negative : Bool) (y : Nat), ((magKey f M : Int) * d - n).natAbs ≤
      ((if negative then -(magKey f y : Int) else (magKey f y : Int)) * d - n).natAbs := by
  intro negative y
  cases negative
  · exact hmin y
  · have hzero := hmin 0
    rw [magKey_zero] at hzero
    simp only [Int.natCast_zero, Int.zero_mul, Int.zero_sub, Int.natAbs_neg] at hzero
    have hprod : 0 ≤ (magKey f y : Int) * d :=
      Int.mul_nonneg (by omega) hd
    have hother := Int.natAbs_eq (-(magKey f y : Int) * d - n)
    have hnabs := Int.natAbs_eq n
    simp only [ite_true]
    rw [Int.neg_mul] at hother ⊢
    rcases hother with hother | hother <;> rcases hnabs with hnabs | hnabs <;> omega

theorem magKey_negative_min_zero (f : Fmt) (y : Nat) (n d : Int)
    (hn : 0 ≤ n) (hd : 0 < d)
    (hmin : (-(magKey f y : Int) * d - n).natAbs ≤ n.natAbs) : y = 0 := by
  by_cases hy : y = 0
  · exact hy
  · have hkey := magKey_strictMono f (show 0 < y by omega)
    rw [magKey_zero] at hkey
    have hprod := Int.mul_pos (show 0 < (magKey f y : Int) by omega) hd
    have ha := Int.natAbs_eq (-(magKey f y : Int) * d - n)
    have hb := Int.natAbs_eq n
    rw [Int.neg_mul] at ha hmin
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

theorem magKey_nearest_signed_max (f : Fmt) (M : Nat) (n d : Int)
    (hd : 0 ≤ d) (hhi : (magKey f M : Int) * d ≤ n) :
    ∀ (negative : Bool) (y : Nat), y ≤ M →
      ((magKey f M : Int) * d - n).natAbs ≤
      ((if negative then -(magKey f y : Int) else (magKey f y : Int)) * d - n).natAbs := by
  intro negative y hy
  cases negative
  · exact magKey_nearest_max f M n d hd hhi y hy
  · have hmprod : 0 ≤ (magKey f M : Int) * d := Int.mul_nonneg (by omega) hd
    have hyprod : 0 ≤ (magKey f y : Int) * d := Int.mul_nonneg (by omega) hd
    have hbase := Int.natAbs_eq ((magKey f M : Int) * d - n)
    have hother := Int.natAbs_eq (-(magKey f y : Int) * d - n)
    simp only [ite_true]
    rw [Int.neg_mul] at hother ⊢
    rcases hbase with hbase | hbase <;> rcases hother with hother | hother <;> omega

theorem magKey_nearest_lower_unique (f : Fmt) (M y : Nat) (n d : Int)
    (hd : 0 < d) (hlo : (magKey f M : Int) * d ≤ n)
    (hmid : 2 * n < ((magKey f M : Int) + (magKey f (M + 1) : Int)) * d)
    (hmin : ∀ z : Nat, ((magKey f y : Int) * d - n).natAbs ≤
      ((magKey f z : Int) * d - n).natAbs) : y = M := by
  rw [Int.add_mul] at hmid
  have hhi : n ≤ (magKey f (M + 1) : Int) * d := by omega
  rcases magKey_nearest_only_neighbors f M y n d hd hlo hhi hmin with hy | hy
  · exact hy
  · subst y
    have hdist := hmin M
    have hloabs := Int.natAbs_eq ((magKey f M : Int) * d - n)
    have hhiabs := Int.natAbs_eq ((magKey f (M + 1) : Int) * d - n)
    rcases hloabs with hloabs | hloabs <;> rcases hhiabs with hhiabs | hhiabs <;> omega

theorem magKey_nearest_upper_unique (f : Fmt) (M y : Nat) (n d : Int)
    (hd : 0 < d) (hhi : n ≤ (magKey f (M + 1) : Int) * d)
    (hmid : ((magKey f M : Int) + (magKey f (M + 1) : Int)) * d < 2 * n)
    (hmin : ∀ z : Nat, ((magKey f y : Int) * d - n).natAbs ≤
      ((magKey f z : Int) * d - n).natAbs) : y = M + 1 := by
  rw [Int.add_mul] at hmid
  have hlo : (magKey f M : Int) * d ≤ n := by omega
  rcases magKey_nearest_only_neighbors f M y n d hd hlo hhi hmin with hy | hy
  · subst y
    have hdist := hmin (M + 1)
    have hloabs := Int.natAbs_eq ((magKey f M : Int) * d - n)
    have hhiabs := Int.natAbs_eq ((magKey f (M + 1) : Int) * d - n)
    rcases hloabs with hloabs | hloabs <;> rcases hhiabs with hhiabs | hhiabs <;> omega
  · exact hy

theorem magKey_neighbors_tie (f : Fmt) (M : Nat) (n d : Int)
    (hlo : (magKey f M : Int) * d ≤ n)
    (hhi : n ≤ (magKey f (M + 1) : Int) * d) :
    ((magKey f M : Int) * d - n).natAbs = ((magKey f (M + 1) : Int) * d - n).natAbs ↔
      2 * n = ((magKey f M : Int) + (magKey f (M + 1) : Int)) * d := by
  rw [Int.add_mul]
  have hloabs := Int.natAbs_eq ((magKey f M : Int) * d - n)
  have hhiabs := Int.natAbs_eq ((magKey f (M + 1) : Int) * d - n)
  rcases hloabs with hloabs | hloabs <;> rcases hhiabs with hhiabs | hhiabs <;> omega

end JuliaLean.ChatGPT.Batch5.Group4.Widen

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen.Fl
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1
open JuliaLean.Promotion.Fl
variable {f : Fmt}

theorem finite_key_lt_inf (hf : (Fmt.Good f)) (x : Fl f) (hx : x.isfinite = true) :
    -(((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int)) < (key x) ∧
    (key x) < ((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int) := by
  have hM := (bits_split x).2
  have hP := Nat.two_pow_pos f.sb
  have hE := hf.emax_eq
  have hS := hf.emax_succ
  have hfin : x.magnitude / 2 ^ f.sb ≠ f.emax := by
    have := hx; simp only [isfinite, bne_iff_ne, ne_eq] at this
    rw [expField_eq] at this; exact this
  have hdiv : x.magnitude / 2 ^ f.sb < 2 ^ f.eb := by
    apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add, Nat.add_comm]; exact hM
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

theorem inf_key_eq (hf : (Fmt.Good f)) (x : Fl f) (hi : x.isinf = true) :
    (key x) = if x.signbit then -(((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int))
            else ((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int) := by
  have hE := hf.emax_eq
  have he : x.expField = f.emax := by
    unfold isinf at hi; simp only [Bool.and_eq_true, beq_iff_eq] at hi; exact hi.1
  have hr : x.frac = 0 := by
    unfold isinf at hi; simp only [Bool.and_eq_true, beq_iff_eq] at hi; exact hi.2
  have hmk : magKey f x.magnitude = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
    unfold magKey
    rw [← expField_eq, ← frac_eq, he, hr, Nat.zero_add,
      ite_eq_right_iff.mpr (by omega)]
  unfold key
  rw [hmk]

theorem notnan_key_bounds (hf : Fmt.Good f) (x : Fl f) (hx : x.isnan = false) :
    -(((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int)) ≤ key x ∧
    key x ≤ ((2 ^ f.sb * 2 ^ (f.emax - 1) : Nat) : Int) := by
  cases hfin : x.isfinite
  · have he : x.expField = f.emax := by
      simpa only [isfinite, bne_eq_false_iff_eq] using hfin
    have hr : x.frac = 0 := by
      simpa only [isnan, he, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] using hx
    have hi : x.isinf = true := by
      simp only [isinf, he, hr, beq_self_eq_true, Bool.true_and]
    rw [inf_key_eq hf x hi]
    cases hs : x.signbit <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at * <;> omega
  · have h := finite_key_lt_inf hf x hfin
    exact ⟨Int.le_of_lt h.1, Int.le_of_lt h.2⟩

theorem magnitude_inf_key (hf : Fmt.Good f) :
    magKey f (f.emax * 2 ^ f.sb) = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
  have he : f.emax ≠ 0 := by have h := hf.emax_eq; omega
  have h := magKey_parts f f.emax 0 (Nat.two_pow_pos f.sb)
  simpa only [Nat.add_zero, he, ite_false, Nat.zero_add] using h

theorem notnan_magnitude_le_inf (hf : Fmt.Good f) (x : Fl f) (hx : x.isnan = false) :
    x.magnitude ≤ f.emax * 2 ^ f.sb := by
  apply (magKey_le_iff f _ _).mp
  rw [magnitude_inf_key hf]
  have hb := notnan_key_bounds hf x hx
  unfold key at hb
  cases hs : x.signbit <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hb <;> omega

theorem finite_magnitude_lt_inf (hf : Fmt.Good f) (x : Fl f) (hx : x.isfinite = true) :
    x.magnitude < f.emax * 2 ^ f.sb := by
  apply (magKey_lt_iff f _ _).mp
  rw [magnitude_inf_key hf]
  have hb := finite_key_lt_inf hf x hx
  unfold key at hb
  cases hs : x.signbit <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hb <;> omega

end JuliaLean.ChatGPT.Batch5.Group4.Widen.Fl

namespace JuliaLean.ChatGPT.Batch5.Group4.Widen
open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1

theorem metric_infinity_scale (f : Fmt) (hf : Fmt.Good f) :
    (2 ^ (f.bias + 1) : Nat) * Fmt.den f = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
  unfold Fmt.den
  rw [← Nat.pow_add, ← Nat.pow_add]
  congr 1
  have he := hf.emax_eq
  have hb := hf.bias_pos
  have hs := hf.sb_pos
  omega

theorem ieeeMetric_data {T : FTy} (x : FV T) (hn : x.isnan = false) :
    0 < (IEEMetricValue x).2 ∧
    RatEq (IEEMetricValue x) (Fl.key x, Fmt.den T.fmt) := by
  by_cases hi : x.isinf = true
  · have hk := Fl.inf_key_eq (good_fty T) x hi
    have hp := congrArg (fun n : Nat => (n : Int))
      (metric_infinity_scale T.fmt (good_fty T))
    rw [Int.natCast_mul] at hp
    simp only [IEEMetricValue, hi, ite_true]
    refine ⟨Nat.zero_lt_one, ?_⟩
    unfold RatEq
    rw [hk]
    cases hs : x.signbit
    · simpa only [hs, Bool.false_eq_true, ite_false, Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one] using hp
    · simpa only [hs, ite_true, Int.ofNat_eq_natCast, Int.natCast_one, Int.mul_one, Int.neg_mul] using
        congrArg (fun n : Int => -n) hp
  · have hi' : x.isinf = false := Bool.eq_false_iff.mpr hi
    have hf := mix_ws_finite_of_not_special x hn hi'
    simp only [IEEMetricValue, hi, ite_false]
    exact Fl.toRat_key (good_fty T) x hf

theorem ieeeMetric_key {T : FTy} (x : FV T) (hn : x.isnan = false) :
    RatEq (IEEMetricValue x) (Fl.key x, Fmt.den T.fmt) :=
  (ieeeMetric_data x hn).2

theorem finite_ratLe_key {T : FTy} (x y : FV T)
    (hx : x.isfinite = true) (hy : y.isfinite = true) :
    RatLe x.toRat y.toRat ↔ Fl.key x ≤ Fl.key y := by
  obtain ⟨hdx, hrx⟩ := Fl.toRat_key (good_fty T) x hx
  obtain ⟨hdy, hry⟩ := Fl.toRat_key (good_fty T) y hy
  have hD : 0 < Fmt.den T.fmt := Fmt.den_pos _
  have hright := JuliaLean.ChatGPT.Batch4.Group3.cmp_rat_le_right
    x.toRat y.toRat (Fl.key y, Fmt.den T.fmt) hdy hD hry
  rw [hright]
  change x.toRat.1 * (Fmt.den T.fmt : Int) ≤ Fl.key y * (x.toRat.2 : Int) ↔ _
  rw [hrx]
  exact Int.mul_le_mul_right (show (0 : Int) < x.toRat.2 by omega)

end JuliaLean.ChatGPT.Batch5.Group4.Widen

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

/-- Increasing a normal significand through its final carry has exactly the
    same numerical scale on either side of the exponent boundary. -/
theorem cv_normal_key (f : Fmt) (B q : Nat)
    (hlo : 2^f.sb ≤ q) (hhi : q ≤ 2^(f.sb+1)) :
    Widen.magKey f (B*2^f.sb+q) = q*2^B := by
  let P := 2^f.sb
  have hp : 0 < P := Nat.two_pow_pos _
  have hqlo : P ≤ q := hlo
  have hqhi : q ≤ 2*P := by simpa only [Nat.pow_succ, Nat.mul_comm] using hhi
  by_cases hcarry : q = 2*P
  · have hb : B*P+q = (B+2)*P+0 := by
      rw [Nat.add_mul]
      omega
    change Widen.magKey f (B*P+q) = q*2^B
    rw [hb, Widen.magKey_parts f (B+2) 0 (by exact hp)]
    simp only [show B+2 ≠ 0 by omega, ite_false,
      Nat.zero_add, show B+2-1 = B+1 by omega, Nat.pow_succ]
    rw [hcarry]
    simp only [P, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · have hfrac : q-P < P := by omega
    have hb : B*P+q = (B+1)*P+(q-P) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    change Widen.magKey f (B*P+q) = q*2^B
    rw [hb, Widen.magKey_parts f (B+1) (q-P) hfrac]
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    have hnum : q-P+2^f.sb = q := by dsimp only [P] at hqlo; omega
    rw [hnum]

theorem cv_small_key (f : Fmt) (q : Nat) (hq : q ≤ 2^f.sb) :
    Widen.magKey f q = q := by
  by_cases heq : q = 2^f.sb
  · rw [heq]
    have h := cv_normal_key f 0 (2^f.sb) (Nat.le_refl _) (by
      exact Nat.pow_le_pow_right (by decide) (by omega))
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.mul_one] using h
  · have hlt : q < 2^f.sb := by omega
    have h := Widen.magKey_parts f 0 q hlt
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.zero_sub,
      Nat.pow_zero, Nat.mul_one, ite_true, Nat.add_zero] using h

theorem cv_main_magnitude_key (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode) :
    Widen.magKey T.fmt (cv_base T x*2^T.fmt.sb + cv_rounded T x r) =
      cv_rounded T x r * 2^(cv_base T x) := by
  have hk := cv_kept_bounds T x hx m e hv
  by_cases hd : 0 ≤ (cv_diff T x).val
  · apply cv_normal_key
    · have h := (hk.1 hd).1
      unfold cv_rounded
      split <;> omega
    · have h := (hk.1 hd).2
      exact cls_quant_increment_range _ _ _ h
  · have hd' : (cv_diff T x).val < 0 := by omega
    have hbase : cv_base T x = 0 := by unfold cv_base; omega
    have h := hk.2 hd'
    have hr : cv_rounded T x r ≤ 2^T.fmt.sb := cls_quant_increment_range _ _ _ h
    rw [hbase, Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.mul_one]
    exact cv_small_key T.fmt _ hr

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

theorem cv_adjacent_keys (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    Widen.magKey T.fmt (cv_base T x*2^T.fmt.sb + cv_kept T x) =
      cv_kept T x*2^(cv_base T x) ∧
    Widen.magKey T.fmt (cv_base T x*2^T.fmt.sb + cv_kept T x+1) =
      (cv_kept T x+1)*2^(cv_base T x) := by
  have hk := cv_kept_bounds T x hx m e hv
  by_cases hd : 0 ≤ (cv_diff T x).val
  · constructor
    · exact cv_normal_key T.fmt _ _ (hk.1 hd).1 (Nat.le_of_lt (hk.1 hd).2)
    · rw [Nat.add_assoc]
      exact cv_normal_key T.fmt _ _ (by have h := (hk.1 hd).1; omega)
        (by have h := (hk.1 hd).2; omega)
  · have hd' : (cv_diff T x).val < 0 := by omega
    have hbase : cv_base T x = 0 := by unfold cv_base; omega
    have h := hk.2 hd'
    rw [hbase, Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.mul_one]
    exact ⟨cv_small_key T.fmt _ (Nat.le_of_lt h), cv_small_key T.fmt _ (by omega)⟩

theorem cv_left_index_lt_inf (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : x.exp.val - 1 ≤ (exponent_max T).val) :
    cv_base T x*2^T.fmt.sb + cv_kept T x < T.fmt.emax*2^T.fmt.sb := by
  have hb := cv_base_bound T x hx m e hv hhi
  have hk := cv_kept_bounds T x hx m e hv
  have hp := Nat.two_pow_pos T.fmt.sb
  have hf := cv_format_relations T
  by_cases hd : 0 ≤ (cv_diff T x).val
  · have hq := (hk.1 hd).2
    rw [Nat.pow_succ] at hq
    have hm := Nat.mul_le_mul_right (2^T.fmt.sb) hb
    have hsplit : (T.fmt.emax-2)*2^T.fmt.sb + 2*2^T.fmt.sb =
        T.fmt.emax*2^T.fmt.sb := by
      rw [← Nat.add_mul]
      congr 1
      omega
    omega
  · have hd' : (cv_diff T x).val < 0 := by omega
    have hbase : cv_base T x = 0 := by unfold cv_base; omega
    have hq := hk.2 hd'
    have hm := Nat.mul_le_mul_right (2^T.fmt.sb) (show 1 ≤ T.fmt.emax by omega)
    rw [Nat.one_mul] at hm
    rw [hbase, Nat.zero_mul, Nat.zero_add]
    omega

theorem cv_quotient_remainder (T : FTy) (x : BigFloat) :
    limbMagnitude x.d = cv_kept T x*2^cv_discard T x+cv_lost T x ∧
    cv_lost T x < 2^cv_discard T x := by
  constructor
  · exact cls_quant_reconstruct _ _
  · exact cls_quant_remainder_bound _ _

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

theorem cv_metric_equal_keys {T : FTy} (y z : FV T)
    (hy : y.isnan = false) (hz : z.isnan = false)
    (heq : RatEq (IEEMetricValue y) (IEEMetricValue z)) :
    Widen.Fl.key y = Widen.Fl.key z := by
  have hdy := Widen.ieeeMetric_data y hy
  have hdz := Widen.ieeeMetric_data z hz
  have h1 : RatEq (Widen.Fl.key y, Widen.Fmt.den T.fmt) (IEEMetricValue z) :=
    cmp_rat_eq_trans _ _ _ hdy.1 hdy.2.symm heq
  have h2 : RatEq (Widen.Fl.key y, Widen.Fmt.den T.fmt)
      (Widen.Fl.key z, Widen.Fmt.den T.fmt) :=
    cmp_rat_eq_trans _ _ _ hdz.1 h1 hdz.2
  have hd := Widen.Fmt.den_pos T.fmt
  exact Int.eq_of_mul_eq_mul_right (a := (Widen.Fmt.den T.fmt : Int)) (by omega) h2

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

/-- All nearest comparisons, including both infinities, reduce to integer
    absolute distances in one common denominator. -/
theorem cv_nearest_key {T : FTy} (z : FV T) (hz : z.isnan = false)
    (n : Int) (K : Nat) (hK : 0 < K) :
    IEENearest (n, K*Widen.Fmt.den T.fmt) z ↔
      ∀ y : FV T, y.isnan = false →
        (Widen.Fl.key z*(K : Int)-n).natAbs ≤ (Widen.Fl.key y*(K : Int)-n).natAbs := by
  let q : Int × Nat := (n, K*Widen.Fmt.den T.fmt)
  have hD := Widen.Fmt.den_pos T.fmt
  have hq : 0 < q.2 := Nat.mul_pos hK hD
  have hzd := Widen.ieeeMetric_data z hz
  have he : ∀ y : FV T, y.isnan = false →
      (RatLe (RatDistance q (IEEMetricValue z)) (RatDistance q (IEEMetricValue y)) ↔
        (Widen.Fl.key z*(K : Int)-n).natAbs ≤ (Widen.Fl.key y*(K : Int)-n).natAbs) := by
    intro y hy
    have hyd := Widen.ieeeMetric_data y hy
    have hzdist := cv_distance_eq_right q _ _ hzd.2
    have hydist := cv_distance_eq_right q _ _ hyd.2
    have hh := cv_rat_le_congr _ _ _ _
      (cmp_distance_den_pos q _ hq hzd.1) (cmp_distance_den_pos q _ hq hD)
      (cmp_distance_den_pos q _ hq hyd.1) (cmp_distance_den_pos q _ hq hD) hzdist hydist
    exact hh.trans (cv_distance_scaled_le n (Widen.Fl.key z) (Widen.Fl.key y)
      K (Widen.Fmt.den T.fmt) hK hD)
  constructor
  · intro h y hy
    exact (he y hy).mp (h y hy)
  · intro h y hy
    exact (he y hy).mpr (h y hy)

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

def cv_lower_integer (s : Bool) (q : Nat) : Int :=
  if s then -((q+1 : Nat) : Int) else (q : Int)

def cv_point (T : FTy) (s : Bool) (M : Nat) : FV T :=
  Fl.ofBits ((if s then 2^(T.fmt.eb+T.fmt.sb) else 0)+M)

theorem cv_main_endpoints (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : x.exp.val - 1 ≤ (exponent_max T).val) :
    let M := cv_base T x*2^T.fmt.sb+cv_kept T x
    let p0 := cv_point T (signbit x) M
    let p1 := cv_point T (signbit x) (M+1)
    p0.isnan = false ∧ p1.isnan = false ∧
    Widen.Fl.key p0 = cls_storage_signedMag (signbit x) (cv_kept T x)*(2^cv_base T x : Nat) ∧
    Widen.Fl.key p1 = cls_storage_signedMag (signbit x) (cv_kept T x+1)*(2^cv_base T x : Nat) := by
  have hidx := cv_left_index_lt_inf T x hx m e hv hhi
  have h0 := cv_ordered_pack T (signbit x) _ (Nat.le_of_lt hidx)
  have h1 := cv_ordered_pack T (signbit x) _ (show
      cv_base T x*2^T.fmt.sb+cv_kept T x+1 ≤ T.fmt.emax*2^T.fmt.sb by omega)
  have hk := cv_adjacent_keys T x hx m e hv
  dsimp only
  refine ⟨h0.2.2.1, h1.2.2.1, ?_, ?_⟩
  · change Widen.Fl.key (Fl.ofBits _) = _
    unfold Widen.Fl.key
    rw [h0.1, h0.2.1, hk.1]
    cases hs : signbit x <;>
      simp only [hs, cls_storage_signedMag, Bool.false_eq_true, ite_false, ite_true,
        Int.natCast_mul, Int.neg_mul]
  · change Widen.Fl.key (Fl.ofBits _) = _
    unfold Widen.Fl.key
    rw [h1.1, h1.2.1, hk.2]
    cases hs : signbit x <;>
      simp only [hs, cls_storage_signedMag, Bool.false_eq_true, ite_false, ite_true,
        Int.natCast_mul, Int.neg_mul]

theorem cv_signed_quotient_interval (s : Bool) (A K q lost : Nat)
    (hK : 0 < K) (hdecomp : A = q*K+lost) (hlo : 0 < lost) (hhi : lost < K) :
    cv_lower_integer s q * (K : Int) < cls_storage_signedMag s A ∧
      cls_storage_signedMag s A < (cv_lower_integer s q+1)*(K : Int) := by
  have hc := congrArg (fun n : Nat => (n : Int)) hdecomp
  simp only [Int.natCast_add, Int.natCast_mul] at hc
  cases s <;>
    simp only [cv_lower_integer, cls_storage_signedMag, Bool.false_eq_true,
      ite_false, ite_true, Int.natCast_add, Int.natCast_one, Int.neg_mul,
      Int.add_mul, Int.one_mul] <;> omega

/-- The signed IEEE keys have no values strictly inside a pair of consecutive
    magnitude codes, with the correct order on both sides of zero. -/
theorem cv_signed_key_gap (T : FTy) (s : Bool) (M : Nat) (y : FV T) :
    Widen.Fl.key y ≤ (if s then -(Widen.magKey T.fmt (M+1) : Int) else (Widen.magKey T.fmt M : Int)) ∨
      (if s then -(Widen.magKey T.fmt M : Int) else (Widen.magKey T.fmt (M+1) : Int)) ≤ Widen.Fl.key y := by
  have hg := Widen.magKey_adjacent T.fmt M y.magnitude
  unfold Widen.Fl.key
  cases s <;> cases hs : y.signbit <;>
    simp only [hs, Bool.false_eq_true, ite_false, ite_true] at *
  all_goals rcases hg with hg | hg <;> omega

theorem cv_signed_key_gap_scaled (T : FTy) (s : Bool) (M q step : Nat)
    (hk0 : Widen.magKey T.fmt M = q*step)
    (hk1 : Widen.magKey T.fmt (M+1) = (q+1)*step) (y : FV T) :
    Widen.Fl.key y ≤ cv_lower_integer s q*(step : Int) ∨
      (cv_lower_integer s q+1)*(step : Int) ≤ Widen.Fl.key y := by
  have h := cv_signed_key_gap T s M y
  rw [hk0, hk1] at h
  cases s <;>
    simp only [cv_lower_integer, Bool.false_eq_true, ite_false, ite_true,
      Int.natCast_mul, Int.natCast_add, Int.natCast_one, Int.neg_mul,
      Int.add_mul, Int.one_mul] at h ⊢ <;> omega

theorem cv_signedMag_abs (s : Bool) (n : Nat) :
    (cls_storage_signedMag s n).natAbs = n := by
  cases s <;> simp only [cls_storage_signedMag, Bool.false_eq_true, ite_false,
    ite_true, Int.natAbs_neg, Int.natAbs_natCast]

theorem cv_interval_scale (lo n lower upper : Int) (K step : Nat)
    (hK : 0 < K) (hstep : 0 < step)
    (hlo : lo*(K : Int) < n) (hhi : n < (lo+1)*(K : Int))
    (hleft : lower ≤ lo*(step : Int)) (hright : (lo+1)*(step : Int) ≤ upper) :
    lower*(K : Int) < n*(step : Int) ∧ n*(step : Int) < upper*(K : Int) := by
  have hKi : (0 : Int) ≤ K := by omega
  have hsi : (0 : Int) < step := by omega
  constructor
  · calc
      lower*(K : Int) ≤ (lo*(step : Int))*(K : Int) := Int.mul_le_mul_of_nonneg_right hleft hKi
      _ = (lo*(K : Int))*(step : Int) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ < n*(step : Int) := Int.mul_lt_mul_of_pos_right hlo hsi
  · calc
      n*(step : Int) < ((lo+1)*(K : Int))*(step : Int) := Int.mul_lt_mul_of_pos_right hhi hsi
      _ = ((lo+1)*(step : Int))*(K : Int) := by simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ ≤ upper*(K : Int) := Int.mul_le_mul_of_nonneg_right hright hKi

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

/-- A common positive grid scale factors out of each integer rounding error. -/
theorem ch_scaled_error (i n : Int) (K step : Nat) :
    (i * (step : Int) * (K : Int) - n * (step : Int)).natAbs =
      (i * (K : Int) - n).natAbs * step := by
  have h : i * (step : Int) * (K : Int) - n * (step : Int) =
      (i * (K : Int) - n) * (step : Int) := by
    simp only [Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [h, Int.natAbs_mul, Int.natAbs_natCast]

/-- Beating the two bracketing keys suffices to beat every ordered IEEE value. -/
theorem ch_nearest_key {T : FTy} (z : FV T) (hz : z.isnan = false)
    (L U N : Int) (K : Nat) (hK : 0 < K)
    (hL : L * (K : Int) ≤ N) (hU : N ≤ U * (K : Int))
    (hlo : (Widen.Fl.key z * (K : Int) - N).natAbs ≤ (L * (K : Int) - N).natAbs)
    (hhi : (Widen.Fl.key z * (K : Int) - N).natAbs ≤ (U * (K : Int) - N).natAbs)
    (hgap : ∀ y : FV T, y.isnan = false → Widen.Fl.key y ≤ L ∨ U ≤ Widen.Fl.key y) :
    IEENearest (N, K * Widen.Fmt.den T.fmt) z := by
  apply (cv_nearest_key z hz N K hK).mpr
  intro y hy
  have hay := Int.natAbs_eq (Widen.Fl.key y * (K : Int) - N)
  rcases hgap y hy with hyL | hUy
  · have hmul := Int.mul_le_mul_of_nonneg_right hyL (show (0 : Int) ≤ K by omega)
    have haL := Int.natAbs_eq (L * (K : Int) - N)
    rcases hay with hay | hay <;> rcases haL with haL | haL <;> omega
  · have hmul := Int.mul_le_mul_of_nonneg_right hUy (show (0 : Int) ≤ K by omega)
    have haU := Int.natAbs_eq (U * (K : Int) - N)
    rcases hay with hay | hay <;> rcases haU with haU | haU <;> omega

/-- Any global nearest rival has one of the two actual adjacent keys. -/
theorem ch_nearest_rival_key {T : FTy} (lower upper y : FV T)
    (hlower : lower.isnan = false) (hupper : upper.isnan = false) (hy : y.isnan = false)
    (L U N : Int) (K : Nat) (hK : 0 < K)
    (hL : L * (K : Int) ≤ N) (hU : N ≤ U * (K : Int))
    (hkeyL : Widen.Fl.key lower = L) (hkeyU : Widen.Fl.key upper = U)
    (hgap : ∀ w : FV T, w.isnan = false → Widen.Fl.key w ≤ L ∨ U ≤ Widen.Fl.key w)
    (hnear : IEENearest (N, K * Widen.Fmt.den T.fmt) y) :
    Widen.Fl.key y = L ∨ Widen.Fl.key y = U := by
  have hkeys := (cv_nearest_key y hy N K hK).mp hnear
  have hay := Int.natAbs_eq (Widen.Fl.key y * (K : Int) - N)
  rcases hgap y hy with hyL | hUy
  · by_cases he : Widen.Fl.key y = L
    · exact Or.inl he
    · have hmul := Int.mul_lt_mul_of_pos_right (show Widen.Fl.key y < L by omega)
        (show (0 : Int) < K by omega)
      have hmin := hkeys lower hlower
      rw [hkeyL] at hmin
      have hab := Int.natAbs_eq (L * (K : Int) - N)
      rcases hay with hay | hay <;> rcases hab with hab | hab <;> omega
  · by_cases he : Widen.Fl.key y = U
    · exact Or.inr he
    · have hmul := Int.mul_lt_mul_of_pos_right (show U < Widen.Fl.key y by omega)
        (show (0 : Int) < K by omega)
      have hmin := hkeys upper hupper
      rw [hkeyU] at hmin
      have hab := Int.natAbs_eq (U * (K : Int) - N)
      rcases hay with hay | hay <;> rcases hab with hab | hab <;> omega

/-- Equal common-denominator keys give equal IEEE metric values. -/
theorem ch_metric_eq_of_key {T : FTy} (y z : FV T)
    (hy : y.isnan = false) (hz : z.isnan = false) (hkey : Widen.Fl.key y = Widen.Fl.key z) :
    RatEq (IEEMetricValue y) (IEEMetricValue z) := by
  have h1 := Widen.ieeeMetric_key y hy
  have h2 := Widen.ieeeMetric_key z hz
  rw [hkey] at h1
  exact cmp_rat_eq_trans _ _ _ (Widen.Fmt.den_pos T.fmt) h1 h2.symm

/-- Distance from zero orders absolute common-denominator keys. -/
theorem ch_zero_distance_key {T : FTy} (y z : FV T)
    (hy : y.isnan = false) (hz : z.isnan = false) :
    RatLe (RatDistance (0, 1) (IEEMetricValue y)) (RatDistance (0, 1) (IEEMetricValue z)) ↔
      (Widen.Fl.key y).natAbs ≤ (Widen.Fl.key z).natAbs := by
  have hD := Widen.Fmt.den_pos T.fmt
  have hyd := Widen.ieeeMetric_data y hy
  have hzd := Widen.ieeeMetric_data z hz
  have hye := cv_distance_eq_right (0, 1) _ _ hyd.2
  have hze := cv_distance_eq_right (0, 1) _ _ hzd.2
  rw [cv_rat_le_congr _ _ _ _
    (cmp_distance_den_pos (0, 1) _ Nat.zero_lt_one hyd.1)
    (cmp_distance_den_pos (0, 1) _ Nat.zero_lt_one hD)
    (cmp_distance_den_pos (0, 1) _ Nat.zero_lt_one hzd.1)
    (cmp_distance_den_pos (0, 1) _ Nat.zero_lt_one hD) hye hze]
  unfold RatLe RatDistance
  simp only [Int.natCast_one, Int.zero_mul, Int.mul_one, Int.zero_sub, Int.natAbs_neg,
    Nat.one_mul, Int.ofNat_eq_natCast]
  rw [Int.mul_le_mul_right (show (0 : Int) < Widen.Fmt.den T.fmt by omega)]
  omega

/-- A tied IEEE endpoint inherits the complete integer nearest property. -/
theorem ch_integer_nearest_of_rival {T : FTy} (z y : FV T)
    (hz : z.isnan = false) (hy : y.isnan = false)
    (n i j : Int) (K step : Nat) (hstep : 0 < step)
    (hzkey : Widen.Fl.key z = i * (step : Int))
    (hykey : Widen.Fl.key y = j * (step : Int))
    (hint : IntegerNearest n K i)
    (hynear : IEENearest (n * (step : Int), K * Widen.Fmt.den T.fmt) y) :
    IntegerNearest n K j := by
  have hdist := ((cv_nearest_key y hy _ K hint.1).mp hynear) z hz
  rw [hzkey, hykey, ch_scaled_error, ch_scaled_error] at hdist
  have hle := (Nat.mul_le_mul_right_iff hstep).mp hdist
  exact ⟨hint.1, fun k => Nat.le_trans hle (hint.2 k)⟩

/-- Toward-zero integer rounding is upward on negative inputs. -/
theorem ch_toZero_negative (n i : Int) (K : Nat) (hn : n < 0)
    (h : IntegerChoice .ToZero n K i) : IntegerChoice .Up n K i := by
  rcases h with ⟨hK, hlo, hhi, hzero, hneg, hpos⟩
  have hi : i ≤ 0 := hneg hn
  have hnabs : (n.natAbs : Int) = -n := by have h := Int.natAbs_eq n; omega
  have hiabs : (i.natAbs : Int) = -i := by have h := Int.natAbs_eq i; omega
  have hloI := Int.ofNat_le.mpr hlo
  have hhiI := Int.ofNat_lt.mpr hhi
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one, hnabs, hiabs,
    Int.neg_mul, Int.add_mul, Int.one_mul] at hloI hhiI
  refine ⟨hK, ?_, ?_⟩
  · simp only [Int.sub_mul, Int.one_mul]
    omega
  · omega

/-- Toward-zero integer rounding is downward on positive inputs. -/
theorem ch_toZero_positive (n i : Int) (K : Nat) (hn : 0 < n)
    (h : IntegerChoice .ToZero n K i) : IntegerChoice .Down n K i := by
  rcases h with ⟨hK, hlo, hhi, hzero, hneg, hpos⟩
  have hi : 0 ≤ i := hpos hn
  have hnabs : (n.natAbs : Int) = n := by have h := Int.natAbs_eq n; omega
  have hiabs : (i.natAbs : Int) = i := by have h := Int.natAbs_eq i; omega
  have hloI := Int.ofNat_le.mpr hlo
  have hhiI := Int.ofNat_lt.mpr hhi
  simp only [Int.natCast_mul, Int.natCast_add, Int.natCast_one, hnabs, hiabs] at hloI hhiI
  exact ⟨hK, hloI, hhiI⟩

/-- Away-from-zero integer rounding is downward on negative inputs. -/
theorem ch_fromZero_negative (n i : Int) (K : Nat) (hn : n < 0)
    (h : IntegerChoice .FromZero n K i) : IntegerChoice .Down n K i := by
  rcases h with ⟨hK, hzero | hpos | hneg⟩
  · omega
  · omega
  · exact ⟨hK, hneg.2⟩

/-- Away-from-zero integer rounding is upward on positive inputs. -/
theorem ch_fromZero_positive (n i : Int) (K : Nat) (hn : 0 < n)
    (h : IntegerChoice .FromZero n K i) : IntegerChoice .Up n K i := by
  rcases h with ⟨hK, hzero | hpos | hneg⟩
  · omega
  · exact ⟨hK, hpos.2⟩
  · omega

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

/-- The two adjacent magnitude encodings can be put in numerical order for
    either sign, including signed zero and the infinity endpoint. -/
theorem cv_main_ordered_endpoints (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : x.exp.val - 1 ≤ (exponent_max T).val) :
    ∃ lower upper : FV T,
      lower.isnan = false ∧ upper.isnan = false ∧
      Widen.Fl.key lower = cv_lower_integer (signbit x) (cv_kept T x) *
        (2 ^ cv_base T x : Nat) ∧
      Widen.Fl.key upper = (cv_lower_integer (signbit x) (cv_kept T x) + 1) *
        (2 ^ cv_base T x : Nat) := by
  have hp := cv_main_endpoints T x hx m e hv hhi
  dsimp only at hp
  cases hs : signbit x with
  | false =>
    simp only [hs] at hp
    refine ⟨cv_point T false (cv_base T x * 2 ^ T.fmt.sb + cv_kept T x),
      cv_point T false (cv_base T x * 2 ^ T.fmt.sb + cv_kept T x + 1),
      hp.1, hp.2.1, ?_, ?_⟩
    · simpa only [hs, cv_lower_integer, cls_storage_signedMag, Bool.false_eq_true,
        ite_false] using hp.2.2.1
    · simpa only [hs, cv_lower_integer, cls_storage_signedMag, Bool.false_eq_true,
        ite_false, Int.natCast_add, Int.natCast_one] using hp.2.2.2
  | true =>
    simp only [hs] at hp
    refine ⟨cv_point T true (cv_base T x * 2 ^ T.fmt.sb + cv_kept T x + 1),
      cv_point T true (cv_base T x * 2 ^ T.fmt.sb + cv_kept T x),
      hp.2.1, hp.1, ?_, ?_⟩
    · simpa only [hs, cv_lower_integer, cls_storage_signedMag, ite_true] using hp.2.2.2
    · have he : cv_lower_integer true (cv_kept T x) + 1 = -(cv_kept T x : Int) := by
        simp only [cv_lower_integer, ite_true, Int.natCast_add, Int.natCast_one]
        omega
      rw [he]
      simpa only [cls_storage_signedMag, ite_true] using hp.2.2.1

end JuliaLean.ChatGPT.Batch5.Group4



set_option Elab.async false

namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- Classification of every valid finite input, including noncanonical dyadic presentations. -/
theorem ext_finite_flags (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) :
    iszero x = false ∧ isinf x = false ∧ isnan x = false ∧
      signbit x = decide (m < 0) := by
  have hm := cls_finite_mantissa_ne_zero x hx m e hv
  rw [cls_iszero x hx, cls_isinf x hx, cls_isnan x hx, cls_signbit x hx, hv]
  simp only [FP.iszero, FP.isinf, FP.isnan, FP.signbit, hm, decide_false, and_self]

/-- The high-exponent branch cannot simultaneously be a strict underflow branch. -/
theorem ext_high_flags (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : (exponent_max T).val < x.exp.val - 1) :
    decide ((exponent_max T).val < (x.exp - JInt.wrap .i64 1).val) = true ∧
      decide ((x.exp-JInt.wrap .i64 1-exponent_min T+precision_Type_default T).val < 0) = false := by
  have hf := cls_exp_format_bounds T
  have hp := cls_ieee_precision_bounds T
  constructor
  · rw [cls_exp_ieeeExp x hx m e hv]
    exact decide_eq_true hhi
  · rw [cls_exp_diff_plus_precision T x hx m e hv]
    exact decide_eq_false (by omega)

/-- Above the highest finite binade, the actual branch selects infinity or the largest finite value. -/
theorem ext_high_result (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hhi : (exponent_max T).val < x.exp.val - 1) :
    toIEEE T x r =
      if JuliaLean.base.gmp.roundsNearest r || JuliaLean.base.gmp.roundsAway r (signbit x) then
        Fl.ofBits (ieee754_representation_inf T (signbit x)).val.toNat
      else Fl.ofBits (ieee754_representation_omega T (signbit x)).val.toNat := by
  obtain ⟨hz, hi, hn, _⟩ := ext_finite_flags x hx m e hv
  obtain ⟨hh, hl⟩ := ext_high_flags T x hx m e hv hhi
  cases hr : JuliaLean.base.gmp.roundsNearest r <;>
    cases ha : JuliaLean.base.gmp.roundsAway r (signbit x) <;>
    simp only [toIEEE, hz, hi, hn, hh, hl, hr, ha,
      Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
      Bool.and_true, Bool.and_false, Bool.false_or, Bool.true_or,
      Bool.or_false, Bool.or_true, Bool.false_eq_true, ite_false, ite_true]

/-- The largest finite encoding has the correct sign and the code immediately before infinity. -/
theorem ext_omega_bits (T : FTy) (s : Bool) :
    let z : FV T := Fl.ofBits (ieee754_representation_omega T s).val.toNat
    z.isfinite = true ∧ z.signbit = s ∧
      z.magnitude = T.fmt.emax * 2^T.fmt.sb - 1 := by
  cases T <;> cases s <;> decide

/-- Strict underflow gives a negative exponent difference and a zero retained-bit count. -/
theorem ext_low_flags (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0) :
    decide ((exponent_max T).val < (x.exp - JInt.wrap .i64 1).val) = false ∧
    decide ((x.exp-JInt.wrap .i64 1-exponent_min T+precision_Type_default T).val < 0) = true ∧
    (x.exp-JInt.wrap .i64 1-exponent_min T).val < 0 ∧
    (max (precision_Type_default T + JInt.wrap .i64
      (min (x.exp-JInt.wrap .i64 1-exponent_min T).val 0)).val 0).toNat = 0 := by
  have hf := cls_exp_format_bounds T
  have hp := cls_ieee_precision_bounds T
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cls_exp_ieeeExp x hx m e hv]
    exact decide_eq_false (by omega)
  · rw [cls_exp_diff_plus_precision T x hx m e hv]
    exact decide_eq_true hlo
  · rw [cls_exp_expDiff T x hx m e hv]
    omega
  · rw [cls_exp_lenValue T x hx m e hv]
    omega

/-- All nearest modes take the signed-zero branch strictly below half the least subnormal. -/
theorem ext_low_nearest_zero (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0)
    (hr : JuliaLean.base.gmp.roundsNearest r = true) :
    toIEEE T x r = Fl.ofBits (ieee754_representation_zero T (signbit x)).val.toNat := by
  obtain ⟨hz, hi, hn, _⟩ := ext_finite_flags x hx m e hv
  obtain ⟨hh, hl, _, _⟩ := ext_low_flags T x hx m e hv hlo
  simp only [toIEEE, hz, hi, hn, hh, hl, hr,
    Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.false_or, Bool.true_or,
    Bool.or_false, Bool.or_true, Bool.false_eq_true, ite_false, ite_true]

/-- Every directed mode pointing toward zero takes the signed-zero strict-underflow branch. -/
theorem ext_low_toward_zero (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0)
    (hr : JuliaLean.base.gmp.roundsNearest r = false)
    (ha : JuliaLean.base.gmp.roundsAway r (signbit x) = false) :
    toIEEE T x r = Fl.ofBits (ieee754_representation_zero T (signbit x)).val.toNat := by
  obtain ⟨hz, hi, hn, _⟩ := ext_finite_flags x hx m e hv
  obtain ⟨hh, hl, _, _⟩ := ext_low_flags T x hx m e hv hlo
  simp only [toIEEE, hz, hi, hn, hh, hl, hr, ha,
    Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.false_or, Bool.true_or,
    Bool.or_false, Bool.or_true, Bool.false_eq_true, ite_false, ite_true]

/-- The signed least subnormal, stated directly by its IEEE bit pattern. -/
def ext_min_subnormal (T : FTy) (s : Bool) : FV T :=
  Fl.ofBits ((if s then 2^(T.fmt.eb+T.fmt.sb) else 0) + 1)

/-- Incrementing an encoded signed zero produces the corresponding least subnormal. -/
theorem ext_zero_increment (T : FTy) (s : Bool) :
    (Fl.ofBits ((ieee754_representation T s (JInt.wrap .i64 0)
      (JInt.wrap T.uintTy 0) + JInt.wrap T.uintTy 1).val.toNat) : FV T) =
      ext_min_subnormal T s := by
  cases T <;> cases s <;> decide

/-- The least-subnormal pattern is finite, nonzero, and retains its requested sign. -/
theorem ext_min_subnormal_bits (T : FTy) (s : Bool) :
    (ext_min_subnormal T s).isfinite = true ∧
      (ext_min_subnormal T s).iszero = false ∧
      (ext_min_subnormal T s).signbit = s ∧
      (ext_min_subnormal T s).magnitude = 1 := by
  cases T <;> cases s <;> decide

/-- Directed rounding away from zero increments the zero retained quotient of a tiny input. -/
theorem ext_low_away_subnormal (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0)
    (hr : JuliaLean.base.gmp.roundsNearest r = false)
    (ha : JuliaLean.base.gmp.roundsAway r (signbit x) = true) :
    toIEEE T x r = ext_min_subnormal T (signbit x) := by
  obtain ⟨hz, hi, hn, _⟩ := ext_finite_flags x hx m e hv
  obtain ⟨hh, hl, hd, hlen⟩ := ext_low_flags T x hx m e hv hlo
  have hw := cls_limb_width_ge_64 x hx
  obtain ⟨hmaglo, hmaghi⟩ := cls_storage_payload_range x hx m e hv
  have hmagpos : 0 < limbMagnitude x.d := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hmaglo
  have hmagzero : limbMagnitude x.d ≠ 0 := by omega
  have hnorm : decide ((x.exp-JInt.wrap .i64 1-exponent_min T).val ≥ 0) = false :=
    decide_eq_false (by omega)
  have hbase : max (x.exp-JInt.wrap .i64 1-exponent_min T).val 0 = 0 := by omega
  have hwzero : x.d.length*64 ≠ 0 := by omega
  have hwidth : ¬ (0 : Nat) ≥ x.d.length*64 := by omega
  have hpow : 2^(x.d.length*64) ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos _)
  have hinc : ieeeIncrement r (signbit x) 0 (limbMagnitude x.d) (2^(x.d.length*64)) = true := by
    simp only [ieeeIncrement, hpow, ite_false, hr, Bool.false_eq_true,
      ha, hmagzero, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
  simp only [toIEEE, hz, hi, hn, hh, hl, hr, ha, hlen, hnorm, hbase,
    Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.false_or, Bool.true_or,
    Bool.or_false, Bool.or_true, Bool.false_eq_true, ite_false, ite_true,
    hwidth, Nat.sub_zero, Nat.div_eq_of_lt hmaghi, Nat.mod_eq_of_lt hmaghi,
    hwzero, hinc, Nat.zero_mod, Int.zero_add]
  exact ext_zero_increment T (signbit x)

/-- Strict underflow is exhausted by signed zero and directed-away least-subnormal output. -/
theorem ext_low_result (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0) :
    toIEEE T x r =
      if !JuliaLean.base.gmp.roundsNearest r && JuliaLean.base.gmp.roundsAway r (signbit x)
      then ext_min_subnormal T (signbit x)
      else Fl.ofBits (ieee754_representation_zero T (signbit x)).val.toNat := by
  cases hr : JuliaLean.base.gmp.roundsNearest r
  · cases ha : JuliaLean.base.gmp.roundsAway r (signbit x)
    · simp only [hr, ha, Bool.not_false, Bool.and_false, Bool.false_eq_true, ite_false]
      exact ext_low_toward_zero T x hx m e hv r hlo hr ha
    · simp only [hr, ha, Bool.not_false, Bool.true_and, ite_true]
      exact ext_low_away_subnormal T x hx m e hv r hlo hr ha
  · simp only [hr, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    exact ext_low_nearest_zero T x hx m e hv r hlo hr

/-- The binade beginning at half the least subnormal is not captured by strict-underflow shortcuts. -/
theorem ext_boundary_not_low (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (he : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val = 0) :
    decide ((x.exp-JInt.wrap .i64 1-exponent_min T+precision_Type_default T).val < 0) = false := by
  rw [cls_exp_diff_plus_precision T x hx m e hv, he]
  rfl

/-- Exact infinity metadata used by the high-exponent branch. -/
theorem ext_inf_data (T : FTy) (s : Bool) :
    let z : FV T := Fl.ofBits (ieee754_representation_inf T s).val.toNat
    z.isnan = false ∧ z.signbit = s ∧ z.magnitude = T.fmt.emax * 2^T.fmt.sb := by
  cases T <;> cases s <;> decide

/-- Exact finite-limit metadata used by the directed high-exponent branch. -/
theorem ext_omega_data (T : FTy) (s : Bool) :
    let z : FV T := Fl.ofBits (ieee754_representation_omega T s).val.toNat
    z.isnan = false ∧ z.signbit = s ∧ z.magnitude = T.fmt.emax * 2^T.fmt.sb - 1 := by
  cases T <;> cases s <;> decide

/-- Exact zero metadata used by strict-underflow branches. -/
theorem ext_zero_data (T : FTy) (s : Bool) :
    let z : FV T := Fl.ofBits (ieee754_representation_zero T s).val.toNat
    z.isnan = false ∧ z.signbit = s ∧ z.magnitude = 0 := by
  cases T <;> cases s <;> decide

/-- Exact least-subnormal metadata used by directed-away strict underflow. -/
theorem ext_min_subnormal_data (T : FTy) (s : Bool) :
    (ext_min_subnormal T s).isnan = false ∧
      (ext_min_subnormal T s).signbit = s ∧ (ext_min_subnormal T s).magnitude = 1 := by
  cases T <;> cases s <;> decide

/-- High-exponent output is non-NaN and preserves sign with its exact terminal magnitude code. -/
theorem ext_high_output_data (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hhi : (exponent_max T).val < x.exp.val - 1) :
    (toIEEE T x r).isnan = false ∧
      (toIEEE T x r).signbit = decide (m < 0) ∧
      (toIEEE T x r).magnitude =
        if JuliaLean.base.gmp.roundsNearest r || JuliaLean.base.gmp.roundsAway r (signbit x)
        then T.fmt.emax * 2^T.fmt.sb else T.fmt.emax * 2^T.fmt.sb - 1 := by
  have hs := (ext_finite_flags x hx m e hv).2.2.2
  rw [ext_high_result T x hx m e hv r hhi]
  cases hmode : JuliaLean.base.gmp.roundsNearest r || JuliaLean.base.gmp.roundsAway r (signbit x)
  · simp only [Bool.false_eq_true, ite_false]
    have h := ext_omega_data T (signbit x)
    exact ⟨h.1, h.2.1.trans hs, h.2.2⟩
  · simp only [ite_true]
    have h := ext_inf_data T (signbit x)
    exact ⟨h.1, h.2.1.trans hs, h.2.2⟩

/-- Strict-underflow output is non-NaN and preserves sign with magnitude code zero or one. -/
theorem ext_low_output_data (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0) :
    (toIEEE T x r).isnan = false ∧
      (toIEEE T x r).signbit = decide (m < 0) ∧
      (toIEEE T x r).magnitude =
        if !JuliaLean.base.gmp.roundsNearest r && JuliaLean.base.gmp.roundsAway r (signbit x)
        then 1 else 0 := by
  have hs := (ext_finite_flags x hx m e hv).2.2.2
  rw [ext_low_result T x hx m e hv r hlo]
  cases hmode : !JuliaLean.base.gmp.roundsNearest r && JuliaLean.base.gmp.roundsAway r (signbit x)
  · simp only [Bool.false_eq_true, ite_false]
    have h := ext_zero_data T (signbit x)
    exact ⟨h.1, h.2.1.trans hs, h.2.2⟩
  · simp only [ite_true]
    have h := ext_min_subnormal_data T (signbit x)
    exact ⟨h.1, h.2.1.trans hs, h.2.2⟩

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def exc_infinity (T : FTy) (s : Bool) : FV T :=
  Fl.ofBits (ieee754_representation_inf T s).val.toNat

def exc_limit (T : FTy) (s : Bool) : FV T :=
  Fl.ofBits (ieee754_representation_omega T s).val.toNat

def exc_infKey (T : FTy) : Nat := 2^T.fmt.sb * 2^(T.fmt.emax-1)

def exc_limitKey (T : FTy) : Nat :=
  Widen.magKey T.fmt (T.fmt.emax*2^T.fmt.sb-1)

theorem exc_infKey_pos (T : FTy) : 0 < exc_infKey T :=
  Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem exc_limitKey_lt (T : FTy) : exc_limitKey T < exc_infKey T := by
  have he : 0 < T.fmt.emax := by cases T <;> decide
  have hp : 0 < T.fmt.emax*2^T.fmt.sb := Nat.mul_pos he (Nat.two_pow_pos _)
  have h := Widen.magKey_strictMono T.fmt (show
    T.fmt.emax*2^T.fmt.sb-1 < T.fmt.emax*2^T.fmt.sb by omega)
  rw [Widen.Fl.magnitude_inf_key (Widen.good_fty T)] at h
  exact h

/-- The largest finite magnitudes bound every finite IEEE key, including
    both signs and both zero encodings. -/
theorem exc_finite_key_bounds {T : FTy} (z : FV T) (hz : z.isfinite = true) :
    -(exc_limitKey T : Int) ≤ Widen.Fl.key z ∧
      Widen.Fl.key z ≤ (exc_limitKey T : Int) := by
  have hm := Widen.Fl.finite_magnitude_lt_inf (Widen.good_fty T) z hz
  have hk := Widen.magKey_mono T.fmt
    (show z.magnitude ≤ T.fmt.emax*2^T.fmt.sb-1 by omega)
  change Widen.magKey T.fmt z.magnitude ≤ exc_limitKey T at hk
  unfold Widen.Fl.key
  cases z.signbit <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- Finite IEEE comparison against an arbitrary common-denominator rational.
    There is no artificial infinity-coordinate restriction. -/
theorem exc_finite_le_key {T : FTy} (z : FV T) (hz : z.isfinite = true)
    (n : Int) (K : Nat) :
    RatLe z.toRat (n, K*Widen.Fmt.den T.fmt) ↔
      Widen.Fl.key z * (K : Int) ≤ n := by
  have hd := Widen.Fl.toRat_key (Widen.good_fty T) z hz
  rw [cv_rat_le_left z.toRat (Widen.Fl.key z, Widen.Fmt.den T.fmt)
    (n, K*Widen.Fmt.den T.fmt) hd.1 (Widen.Fmt.den_pos _) hd.2]
  unfold RatLe
  dsimp only
  have hD : (0 : Int) < Widen.Fmt.den T.fmt := by
    have h := Widen.Fmt.den_pos T.fmt
    omega
  simpa only [Int.natCast_mul, Int.mul_assoc] using
    (Int.mul_le_mul_right (b := Widen.Fl.key z*(K : Int)) (c := n) hD)

theorem exc_key_le_finite {T : FTy} (z : FV T) (hz : z.isfinite = true)
    (n : Int) (K : Nat) :
    RatLe (n, K*Widen.Fmt.den T.fmt) z.toRat ↔
      n ≤ Widen.Fl.key z * (K : Int) := by
  have hd := Widen.Fl.toRat_key (Widen.good_fty T) z hz
  rw [cmp_rat_le_right (n, K*Widen.Fmt.den T.fmt) z.toRat
    (Widen.Fl.key z, Widen.Fmt.den T.fmt) hd.1 (Widen.Fmt.den_pos _) hd.2]
  unfold RatLe
  dsimp only
  have hD : (0 : Int) < Widen.Fmt.den T.fmt := by
    have h := Widen.Fmt.den_pos T.fmt
    omega
  simpa only [Int.natCast_mul, Int.mul_assoc] using
    (Int.mul_le_mul_right (b := n) (c := Widen.Fl.key z*(K : Int)) hD)

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4

open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

/-- A valid high-exponent payload lies beyond the infinity metric endpoint
    in the same exact integer coordinates used for the finite branch. -/
theorem exc_high_scaled_bound (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hhi : (exponent_max T).val < x.exp.val-1) :
    exc_infKey T * 2^(cv_discard T x) ≤
      limbMagnitude x.d * 2^(cv_base T x) := by
  have hd := cls_exp_expDiff T x hx m e hv
  change (cv_diff T x).val = x.exp.val-1-(exponent_min T).val at hd
  have he := cls_exp_format_bounds T
  have hf := cv_format_relations T
  have hnormal : 0 ≤ (cv_diff T x).val := by omega
  have hbase : T.fmt.emax-1 ≤ cv_base T x := by
    unfold cv_base
    omega
  have hkept := ((cv_kept_bounds T x hx m e hv).1 hnormal).1
  have hquot : cv_kept T x * 2^(cv_discard T x) ≤ limbMagnitude x.d := by
    unfold cv_kept
    exact Nat.div_mul_le_self _ _
  have hsmall := Nat.mul_le_mul_right (2^(cv_discard T x)) hkept
  have hA := Nat.le_trans hsmall hquot
  have hpow := Nat.pow_le_pow_right (show 1 ≤ (2 : Nat) by decide) hbase
  calc
    exc_infKey T * 2^(cv_discard T x) =
        (2^T.fmt.sb * 2^(cv_discard T x)) * 2^(T.fmt.emax-1) := by
          simp only [exc_infKey, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ limbMagnitude x.d * 2^(cv_base T x) := Nat.mul_le_mul hA hpow

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3
open JuliaLean.base.gmp (limbMagnitude)

def uf_inc (r : RoundingMode) (s : Bool) : Bool :=
  !JuliaLean.base.gmp.roundsNearest r && JuliaLean.base.gmp.roundsAway r s

def uf_selected (r : RoundingMode) (s : Bool) : Nat := if uf_inc r s then 1 else 0

theorem uf_increment (r : RoundingMode) (s : Bool) (A K : Nat)
    (hA : 0 < A) (hhalf : 2*A < K) : ieeeIncrement r s 0 A K = uf_inc r s := by
  have hK : K ≠ 0 := by omega
  have hgt : ¬2*A > K := by omega
  have heq : ¬2*A = K := by omega
  have hAz : A ≠ 0 := by omega
  unfold ieeeIncrement uf_inc
  simp only [hK, ite_false, hgt, heq, decide_false, Bool.false_and,
    Bool.false_or, hAz, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
  cases JuliaLean.base.gmp.roundsNearest r <;> rfl

theorem uf_integer_choice (r : RoundingMode) (s : Bool) (A K : Nat)
    (hA : 0 < A) (hhalf : 2*A < K) :
    IntegerChoice r (cls_storage_signedMag s A) K (cls_storage_signedMag s (uf_selected r s)) := by
  have hK : 0 < K := by omega
  have hAK : A < K := by omega
  have hs : decide (cls_storage_signedMag s A < 0) = s := by
    cases s <;> simp only [cls_storage_signedMag, Bool.false_eq_true, ite_false,
      ite_true, decide_eq_false_iff_not, decide_eq_true_eq] <;> omega
  have h := ri_ieee_integer_choice r (cls_storage_signedMag s A) K hK
  simp only [ri_ieee_integer] at h
  rw [cv_signedMag_abs, hs, Nat.div_eq_of_lt hAK, Nat.mod_eq_of_lt hAK,
    uf_increment r s A K hA hhalf, Nat.zero_add] at h
  exact h

def uf_shift (T : FTy) (x : BigFloat) : Nat :=
  (((x.d.length*64 : Nat) : Int) - x.exp.val - ((T.fmt.bias+T.fmt.sb-1 : Nat) : Int)).toNat

theorem uf_shift_bound (T : FTy) (x : BigFloat)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0) :
    x.d.length*64+1 ≤ uf_shift T x ∧
    x.exp.val - ((x.d.length*64 : Nat) : Int) =
      -((uf_shift T x + (T.fmt.bias+T.fmt.sb-1) : Nat) : Int) := by
  have he : (exponent_min T).val = 1-(T.fmt.bias : Int) := by cases T <;> decide
  have hp := cls_quant_precision T
  have hb : 1 ≤ T.fmt.bias := by cases T <;> decide
  rw [he, hp] at hlo
  unfold uf_shift
  omega

/-- Strict underflow places the normalized limb numerator below half of the
discarded-bit denominator in least-subnormal coordinates. -/
theorem uf_payload_half (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0) :
    0 < limbMagnitude x.d ∧ 2*limbMagnitude x.d < 2^uf_shift T x := by
  have hA := cls_storage_payload_range x hx m e hv
  have hS := (uf_shift_bound T x hlo).1
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hS
  rw [Nat.pow_succ] at hpow
  have htwice := Nat.mul_lt_mul_of_pos_left hA.2 (show 0 < 2 by decide)
  refine ⟨Nat.lt_of_lt_of_le (Nat.two_pow_pos _) hA.1, ?_⟩
  rw [Nat.mul_comm (2^(x.d.length*64)) 2] at hpow
  exact Nat.lt_of_lt_of_le htwice hpow

theorem uf_scaled_input (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0) :
    RatEq (JuliaLean.Proofs.base.mpfr.Round1.Dyadic m e)
      (cls_storage_signedMag (signbit x) (limbMagnitude x.d),
        2^uf_shift T x*Widen.Fmt.den T.fmt) := by
  have hs := cls_storage_value_exact x hx m e hv
  have hb := uf_shift_bound T x hlo
  rw [hb.2] at hs
  have hneg : ¬ -((uf_shift T x+(T.fmt.bias+T.fmt.sb-1) : Nat) : Int) ≥ 0 := by omega
  simpa only [JuliaLean.Proofs.base.mpfr.Round1.Dyadic, hneg, ite_false,
    Int.neg_neg, Int.toNat_natCast, Nat.pow_add, Widen.Fmt.den] using hs

theorem uf_zero_point (T : FTy) (s : Bool) :
    (Fl.ofBits (ieee754_representation_zero T s).val.toNat : FV T) = cv_point T s 0 := by
  let z : FV T := Fl.ofBits (ieee754_representation_zero T s).val.toNat
  have hd := ext_zero_data T s
  have hb : z.toBits = (if s then 2^(T.fmt.eb+T.fmt.sb) else 0)+0 := by
    rw [(Widen.Fl.bits_split z).1, hd.2.1, hd.2.2]
  calc
    z = Fl.ofBits z.toBits := (Widen.Fl.ofBits_toBits z).symm
    _ = cv_point T s 0 := congrArg (fun n => (Fl.ofBits n : FV T)) hb

theorem uf_low_result_point (T : FTy) (x : BigFloat) (hx : ValidBigFloat x)
    (m e : Int) (hv : x.value = .finite m e) (r : RoundingMode)
    (hlo : x.exp.val - 1 - (exponent_min T).val + (precision_Type_default T).val < 0) :
    toIEEE T x r = cv_point T (signbit x) (uf_selected r (signbit x)) := by
  rw [ext_low_result T x hx m e hv r hlo]
  change (if uf_inc r (signbit x) then ext_min_subnormal T (signbit x)
    else Fl.ofBits (ieee754_representation_zero T (signbit x)).val.toNat) = _
  cases h : uf_inc r (signbit x)
  · simp only [Bool.false_eq_true, ite_false, uf_selected, h]
    exact uf_zero_point T (signbit x)
  · simp only [ite_true, uf_selected, h]
    rfl

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.ChatGPT.Batch5.Group4
open JuliaLean JuliaLean.base.float JuliaLean.base.mpfr
open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.Proofs.base.mpfr.Round1 JuliaLean.ChatGPT.Batch4.Group3

end JuliaLean.ChatGPT.Batch5.Group4

namespace JuliaLean.Proofs.base.mpfr

open JuliaLean.Registry
open JuliaLean JuliaLean.base.gmp

def MixedRightConversionFailure : Prop :=
  ∀ (t : IntTy) (dispatch : IsClongMax t ∨ IsCulongMax t)
    (x : BigInt) (y : JInt t) (before after : JuliaLean.base.mpfr.Context) (error : JlError),
    (JuliaLean.base.mpfr.abstractFloatBigInt x).run before = (.error error, after) →
    (divideMixedRightMPFR dispatch x y).run before = (.error error, after)

def MixedLeftConversionFailure : Prop :=
  ∀ (t : IntTy) (dispatch : IsClongMax t ∨ IsCulongMax t)
    (x : JInt t) (y : BigInt) (before after : JuliaLean.base.mpfr.Context) (error : JlError),
    (JuliaLean.base.mpfr.abstractFloatBigInt y).run before = (.error error, after) →
    (divideMixedLeftMPFR dispatch x y).run before = (.error error, after)

theorem mixedRightConversionFailure_proven : MixedRightConversionFailure := by
  intro t dispatch x y before after error failure
  simp [divideMixedRightMPFR, divideMixedRightM, Bind.bind, failure]

theorem mixedLeftConversionFailure_proven : MixedLeftConversionFailure := by
  intro t dispatch x y before after error failure
  simp [divideMixedLeftMPFR, divideMixedLeftM, Bind.bind, failure]

def entries : List JuliaLean.Registry.Entry := [
  { id := "gmp-mixed-right-conversion-failure", juliaFile := "base/gmp.jl",
    juliaFns := ["/(x::BigInt, y::Union{ClongMax,CulongMax})"],
    statement := "Mixed BigInt/machine floating division retains every exception and final MPFR state from converting its BigInt numerator, before division.",
    source := "base/gmp.jl:565; base/mpfr.jl:418,627-643",
    status := .proven, prop := ``MixedRightConversionFailure, thm := some ``mixedRightConversionFailure_proven },
  { id := "gmp-mixed-left-conversion-failure", juliaFile := "base/gmp.jl",
    juliaFns := ["/(x::Union{ClongMax,CulongMax}, y::BigInt)"],
    statement := "Mixed machine/BigInt floating division retains every exception and final MPFR state from converting its BigInt denominator, before division.",
    source := "base/gmp.jl:566; base/mpfr.jl:418,632-648",
    status := .proven, prop := ``MixedLeftConversionFailure, thm := some ``mixedLeftConversionFailure_proven },
  { id := "bignumscov-mpfr-75-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["convert@75", "convert@76", "convert@77", "convert@78", "convert@79", "convert@81"],
    statement := "Each of the five supported public/MPFR mode conversions is reversible and preserves its mathematical integer-rounding direction under the documented ambient nearest-mode precondition for round (base/rounding.jl:349-350); conversion of the internal faithful tag to a public mode rejects it with ArgumentError",
    source := "base/mpfr.jl:75-95; documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350", status := .proven,
    prop := ``Round1.ModeConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr75V2_proven },
  { id := "bignumscov-mpfr-76-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["convert@75", "convert@76", "convert@77", "convert@78", "convert@79", "convert@81"],
    statement := "Each of the five supported public/MPFR mode conversions is reversible and preserves its mathematical integer-rounding direction under the documented ambient nearest-mode precondition for round (base/rounding.jl:349-350); conversion of the internal faithful tag to a public mode rejects it with ArgumentError",
    source := "base/mpfr.jl:75-95; documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350", status := .proven,
    prop := ``Round1.ToZeroModeConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr76V2_proven },
  { id := "bignumscov-mpfr-77-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["convert@75", "convert@76", "convert@77", "convert@78", "convert@79", "convert@81"],
    statement := "Each of the five supported public/MPFR mode conversions is reversible and preserves its mathematical integer-rounding direction under the documented ambient nearest-mode precondition for round (base/rounding.jl:349-350); conversion of the internal faithful tag to a public mode rejects it with ArgumentError",
    source := "base/mpfr.jl:75-95; documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350", status := .proven,
    prop := ``Round1.UpModeConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr77V2_proven },
  { id := "bignumscov-mpfr-78-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["convert@75", "convert@76", "convert@77", "convert@78", "convert@79", "convert@81"],
    statement := "Each of the five supported public/MPFR mode conversions is reversible and preserves its mathematical integer-rounding direction under the documented ambient nearest-mode precondition for round (base/rounding.jl:349-350); conversion of the internal faithful tag to a public mode rejects it with ArgumentError",
    source := "base/mpfr.jl:75-95; documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350", status := .proven,
    prop := ``Round1.DownModeConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr78V2_proven },
  { id := "bignumscov-mpfr-79-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["convert@75", "convert@76", "convert@77", "convert@78", "convert@79", "convert@81"],
    statement := "Each of the five supported public/MPFR mode conversions is reversible and preserves its mathematical integer-rounding direction under the documented ambient nearest-mode precondition for round (base/rounding.jl:349-350); conversion of the internal faithful tag to a public mode rejects it with ArgumentError",
    source := "base/mpfr.jl:75-95; documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350", status := .proven,
    prop := ``Round1.FromZeroModeConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr79V2_proven },
  { id := "bignumscov-mpfr-81-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["convert@75", "convert@76", "convert@77", "convert@78", "convert@79", "convert@81"],
    statement := "Each of the five supported public/MPFR mode conversions is reversible and preserves its mathematical integer-rounding direction under the documented ambient nearest-mode precondition for round (base/rounding.jl:349-350); conversion of the internal faithful tag to a public mode rejects it with ArgumentError",
    source := "base/mpfr.jl:75-95; documentation: base/mpfr.jl:58-73; base/rounding.jl:25-110,349-350", status := .proven,
    prop := ``Round1.PublicModeConversionCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr81V2_proven },
  { id := "bignumscov-mpfr-252-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["rounding@252", "setrounding@253"],
    statement := "Public setrounding updates the global default to the requested public mode; a lexical override retains priority in rounding(BigFloat), and precision/exponent limits do not change",
    source := "base/mpfr.jl:252-253; documentation: base/rounding.jl:190-217; doc/src/manual/integers-and-floating-point-numbers.md:632-650", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64178, #26935; see bugs/bignumscov-mpfr-252-v2.yaml",
    prop := ``Round1.SetRoundingObservableCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr252V2_refuted },
  { id := "bignumscov-mpfr-253-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["rounding@252", "setrounding@253"],
    statement := "Public setrounding updates the global default to the requested public mode; a lexical override retains priority in rounding(BigFloat), and precision/exponent limits do not change",
    source := "base/mpfr.jl:252-253; documentation: base/rounding.jl:190-217; doc/src/manual/integers-and-floating-point-numbers.md:632-650", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64178, #26935; see bugs/bignumscov-mpfr-253-v2.yaml",
    prop := ``Round1.SetRoundingUpdateCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr253V2_refuted },
  { id := "bignumscov-mpfr-254-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["setrounding@254"],
    statement := "Scoped setrounding agrees, for arbitrary callbacks and both returns and exceptions from every publicly reachable initial rounding mode, with the documented public old-mode/set/callback/finally-restore program, including the entire final Context so an outer lexical scope cannot hide a changed default",
    source := "base/mpfr.jl:254-255; documentation: base/rounding.jl:226-245; doc/src/manual/integers-and-floating-point-numbers.md:632-650", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #51277, #51362; see bugs/bignumscov-mpfr-254-v2.yaml",
    prop := ``Round1.ScopedSetRoundingDocumentedCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr254V2_refuted },
  { id := "bignumscov-mpfr-458-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["round@458"],
    statement := "Under the documented ambient nearest-mode precondition (base/rounding.jl:349-350), round(BigInt,x,r) returns the mathematically rounded integer for every finite BigFloat and rejects infinities/NaNs with InexactError, covering every private mode reachable from the public RoundingMode conversion (the internal faithful tag is not public API)",
    source := "base/mpfr.jl:458-463; documentation: base/rounding.jl:331-355,50-110; doc/src/base/numbers.md:171-183", status := .proven,
    prop := ``Round1.RoundBigIntRawCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr458V2_proven },
  { id := "bignumscov-mpfr-467-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["round@458", "round@467"],
    statement := "Under the documented ambient nearest-mode precondition (base/rounding.jl:349-350), the public BigInt rounding overload supports all seven documented explicit RoundingMode tags, returns the correct integral value for every finite input and raises InexactError exactly for nonfinite input",
    source := "base/mpfr.jl:458-468; documentation: base/rounding.jl:25-110,331-355", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64178; see bugs/bignumscov-mpfr-467-v2.yaml",
    prop := ``Round1.RoundBigIntPublicCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr467V2_refuted },
  { id := "bignumscov-mpfr-472-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["unsafe_trunc@472"],
    statement := "unsafe_trunc(BigInt,x) truncates every finite value toward zero and returns a BigInt even for nonfinite inputs whose numeric value is unspecified",
    source := "base/mpfr.jl:472; documentation: base/float.jl:389-406", status := .proven,
    prop := ``Round1.UnsafeTruncBigIntCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr472V2_proven },
  { id := "bignumscov-mpfr-477-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["round@477"],
    statement := "Under the documented ambient nearest-mode precondition (base/rounding.jl:349-350), round(Integer,x,r::MPFRRoundingMode) returns the mathematically correct BigInt rounded value on every finite input and raises InexactError for infinities or NaNs for every mode reachable from public RoundingMode conversion",
    source := "base/mpfr.jl:477; documentation: base/rounding.jl:331-355", status := .proven,
    prop := ``Round1.RoundAbstractIntegerRawCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr477V2_proven },
  { id := "bignumscov-mpfr-479-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["Bool@479"],
    statement := "Bool(x) succeeds exactly for numeric zero and one, returns the matching Boolean and raises InexactError for every other BigFloat, including nonfinite values",
    source := "base/mpfr.jl:479-483; documentation: base/docs/basedocs.jl:2394-2407; base/mpfr.jl:479-483; doc/src/base/numbers.md:50-55", status := .proven,
    prop := ``Round1.BigFloatToBoolCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr479V2_proven },
  { id := "bignumscov-mpfr-484-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["BigInt@484"],
    statement := "BigInt(x) preserves every finite integral BigFloat exactly and raises InexactError precisely when no mathematical integer equals x",
    source := "base/mpfr.jl:484-487; documentation: base/gmp.jl:64-88; base/number.jl:7-15; base/mpfr.jl:484-487", status := .proven,
    prop := ``Round1.BigFloatToBigIntCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr484V2_proven },
  { id := "bignumscov-mpfr-550-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["Float16@550"],
    statement := "Float16(x,r) correctly selects the directed or nearest IEEE representable value over the entire BigFloat range, including ties, subnormal/underflow and overflow, preserving signed zeros/infinities and NaN classification; raw mode tags range over the five reachable public conversions at base/mpfr.jl:58-79",
    source := "base/mpfr.jl:550; documentation: base/mpfr.jl:259-273; base/rounding.jl:25-110,352-355; doc/src/base/numbers.md:26-54", status := .todo,
    prop := ``Round1.ToFloat16RawCorrect, thm := none },
  { id := "bignumscov-mpfr-551-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["Float32@551"],
    statement := "Float32(x,r) correctly selects the directed or nearest IEEE representable value over the entire BigFloat range, including ties, subnormal/underflow and overflow, preserving signed zeros/infinities and NaN classification; raw mode tags range over the five reachable public conversions at base/mpfr.jl:58-79",
    source := "base/mpfr.jl:551; documentation: base/mpfr.jl:259-273; base/rounding.jl:25-110,352-355; doc/src/base/numbers.md:26-54", status := .todo,
    prop := ``Round1.ToFloat32RawCorrect, thm := none },
  { id := "bignumscov-mpfr-552-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["Float64@552"],
    statement := "Float64(x,r) correctly selects the directed or nearest IEEE representable value over the entire BigFloat range, including ties, subnormal/underflow and overflow, preserving signed zeros/infinities and NaN classification; raw mode tags range over the five reachable public conversions at base/mpfr.jl:58-79",
    source := "base/mpfr.jl:552; documentation: base/mpfr.jl:259-273; base/rounding.jl:25-110,352-355; doc/src/base/numbers.md:26-54", status := .todo,
    prop := ``Round1.ToFloat64RawCorrect, thm := none },
  { id := "bignumscov-mpfr-553-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["Float16@553"],
    statement := "The public Float16 conversion handles every RoundingMode over every valid BigFloat, selecting its exact ordered neighbour or global nearest IEEE value with the requested tie rule and covering NaN classification, signed zeros/infinities, subnormals, underflow and overflow",
    source := "base/mpfr.jl:553; documentation: base/rounding.jl:25-110,264-286,352-355; doc/src/base/numbers.md:26-54", status := .todo,
    prop := ``Round1.ToFloat16PublicCorrect, thm := none },
  { id := "bignumscov-mpfr-554-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["Float32@554"],
    statement := "The public Float32 conversion handles every RoundingMode over every valid BigFloat, selecting its exact ordered neighbour or global nearest IEEE value with the requested tie rule and covering NaN classification, signed zeros/infinities, subnormals, underflow and overflow",
    source := "base/mpfr.jl:554; documentation: base/rounding.jl:25-110,264-286,352-355; doc/src/base/numbers.md:26-54", status := .todo,
    prop := ``Round1.ToFloat32PublicCorrect, thm := none },
  { id := "bignumscov-mpfr-555-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["Float64@555"],
    statement := "The public Float64 conversion handles every RoundingMode over every valid BigFloat, selecting its exact ordered neighbour or global nearest IEEE value with the requested tie rule and covering NaN classification, signed zeros/infinities, subnormals, underflow and overflow",
    source := "base/mpfr.jl:555; documentation: base/rounding.jl:25-110,264-286,352-355; doc/src/base/numbers.md:26-54", status := .todo,
    prop := ``Round1.ToFloat64PublicCorrect, thm := none },
  { id := "bignumscov-mpfr-897-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["minmax@897"],
    statement := "minmax returns the two inputs in numeric total order with negative zero first, while any NaN input propagates to both results.",
    source := "base/mpfr.jl:897-901; documentation: base/operators.jl:576-590; base/math.jl:832-835; doc/src/base/math.md:200-203", status := .proven,
    prop := ``Round1.MinmaxCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr897V2_proven },
  { id := "bignumscov-mpfr-990-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["==@990"],
    statement := "BigFloat equality is exact numerical equality with all NaNs unequal and both zero signs equal.",
    source := "base/mpfr.jl:990; documentation: base/operators.jl:109-126; doc/src/base/math.md:36-44", status := .proven,
    prop := ``Round1.BigFloatEqualityCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr990V2_proven },
  { id := "bignumscov-mpfr-991-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["<=@991"],
    statement := "BigFloat <= is exact numerical less-or-equal, unordered for NaNs and equal for opposite signed zeros.",
    source := "base/mpfr.jl:991; documentation: base/operators.jl:447-455; doc/src/base/math.md:36-44", status := .proven,
    prop := ``Round1.BigFloatLessEqualCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr991V2_proven },
  { id := "bignumscov-mpfr-992-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["<@992"],
    statement := "BigFloat < is exact numerical strict order, with NaNs unordered and opposite signed zeros never strictly ordered.",
    source := "base/mpfr.jl:992; documentation: base/operators.jl:392-404; doc/src/base/math.md:36-44", status := .proven,
    prop := ``Round1.BigFloatLessCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr992V2_proven },
  { id := "bignumscov-mpfr-994-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["cmp@994"],
    statement := "cmp returns exactly -1,0 or1 according to the documented total order, with NaNs last and negative floating zero below integer zero.",
    source := "base/mpfr.jl:994-997; documentation: base/operators.jl:219-242,507-514; doc/src/base/math.md:44", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64167, #64575; see bugs/bignumscov-mpfr-994-v2.yaml",
    prop := ``Round1.BigFloatBigIntCmpTotalOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr994V2_refuted },
  { id := "bignumscov-mpfr-998-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["cmp@998"],
    statement := "cmp returns exactly -1,0 or1 according to the documented total order, with NaNs last and negative floating zero below integer zero.",
    source := "base/mpfr.jl:998-1001; documentation: base/operators.jl:219-242,507-514; doc/src/base/math.md:44", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64167, #64575; see bugs/bignumscov-mpfr-998-v2.yaml",
    prop := ``Round1.BigFloatSignedCmpTotalOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr998V2_refuted },
  { id := "bignumscov-mpfr-1002-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["cmp@1002"],
    statement := "For every BigFloat and every UInt8/16/32/64 operand, cmp returns -1, 0 or 1 according to the documented total order, including NaNs and signed zero against integer zero.",
    source := "base/mpfr.jl:1002-1005; documentation: base/operators.jl:508-511", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64167, #64575; see bugs/bignumscov-mpfr-1002-v2.yaml",
    prop := ``Round1.CmpUnsignedTotalOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1002V2_refuted },
  { id := "bignumscov-mpfr-1009-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["cmp@1009"],
    statement := "For every Float16/32/64 partner, cmp follows total order: NaNs last, negative zero before positive zero, exact finite and infinite comparison. RELEASE BUG: cmp(BigFloat(-0.0),0.0)==0 while isless(BigFloat(-0.0),0.0)==true, confirmed Julia 1.13.2 commit 45b6d15e34bbd2003a31acce0b1847b63dad029c; target pinned runtime not tested.",
    source := "base/mpfr.jl:1009-1013; documentation: base/operators.jl:508-511; base/operators.jl:206-218", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64167, #64575; see bugs/bignumscov-mpfr-1009-v2.yaml",
    prop := ``Round1.CmpIEEETotalOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1009V2_refuted },
  { id := "bignumscov-mpfr-1014-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["cmp@1014"],
    statement := "The reverse Float16/32/64 versus BigFloat cmp returns -1/0/1 in the documented total order, including both zero signs and NaNs. The signed-zero defect is the reverse of the confirmed cmp(BigFloat(-0.0),0.0) case.",
    source := "base/mpfr.jl:1014; documentation: base/operators.jl:508-511", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #64167, #64575; see bugs/bignumscov-mpfr-1014-v2.yaml",
    prop := ``Round1.IEEECmpTotalOrder, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1014V2_refuted },
  { id := "bignumscov-mpfr-1018-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["==@1018"],
    statement := "BigFloat == Float16/32/64 iff their exact numeric values agree; opposite zero signs are equal, NaNs are never equal, infinities compare by sign.",
    source := "base/mpfr.jl:1018; documentation: doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.EqualIEEEValue, thm := some ``JuliaLean.ChatGPT.Batch5.Group4.BignumscovMpfr1018V2_proven },
  { id := "bignumscov-mpfr-1019-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["==@1019"],
    statement := "Float16/32/64 == BigFloat iff their exact values agree, with all finite/special cases and no preliminary rounding of BigFloat.",
    source := "base/mpfr.jl:1019; documentation: doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.IEEEEqualValue, thm := some ``JuliaLean.ChatGPT.Batch5.Group4.BignumscovMpfr1019V2_proven },
  { id := "bignumscov-mpfr-1023-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["<@1023"],
    statement := "BigFloat < Float16/32/64 iff strict exact numeric order holds; unordered NaNs and equal signed zeros give false.",
    source := "base/mpfr.jl:1023; documentation: doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.LessIEEEValue, thm := some ``JuliaLean.ChatGPT.Batch5.Group4.BignumscovMpfr1023V2_proven },
  { id := "bignumscov-mpfr-1024-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["<@1024"],
    statement := "Float16/32/64 < BigFloat iff strict exact numeric order holds, including infinities, zeros and NaNs.",
    source := "base/mpfr.jl:1024; documentation: doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.IEEELessValue, thm := some ``JuliaLean.ChatGPT.Batch5.Group4.BignumscovMpfr1024V2_proven },
  { id := "bignumscov-mpfr-1028-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["<=@1028"],
    statement := "BigFloat <= Float16/32/64 iff exact less-than or numeric equality holds, and is false for either NaN.",
    source := "base/mpfr.jl:1028; documentation: doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.LessEqualIEEEValue, thm := some ``JuliaLean.ChatGPT.Batch5.Group4.BignumscovMpfr1028V2_proven },
  { id := "bignumscov-mpfr-1029-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["<=@1029"],
    statement := "Float16/32/64 <= BigFloat iff exact less-than or numeric equality holds, and is false for either NaN.",
    source := "base/mpfr.jl:1029; documentation: doc/src/manual/mathematical-operations.md:229-286", status := .proven,
    prop := ``Round1.IEEELessEqualValue, thm := some ``JuliaLean.ChatGPT.Batch5.Group4.BignumscovMpfr1029V2_proven },
  { id := "bignumscov-mpfr-1033-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["signbit@1033"],
    statement := "The sign bit agrees with the sign of the independently represented FP value, including signed zeros, infinities and NaNs; coherent storage is the type invariant.",
    source := "base/mpfr.jl:1033; documentation: base/number.jl:122-143; doc/src/manual/integers-and-floating-point-numbers.md:355-371", status := .proven,
    prop := ``Round1.SignbitValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1033V2_proven },
  { id := "mpfr-isinteger-value", juliaFile := "base/mpfr.jl",
    juliaFns := ["isinteger@1111"],
    statement := "Isinteger is true exactly when the finite value equals a mathematical integer; covers both zeros, negative values, infinities and NaNs.",
    source := "base/mpfr.jl:1111-1113; documentation: base/number.jl:10-21", status := .proven,
    prop := ``Round1.IsIntegerValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.MpfrIsintegerValue_proven },
  { id := "bignumscov-mpfr-1129-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["isinf@1129"],
    statement := "Isinf is true exactly at the two signed infinite numeric values, excluding every finite value and NaN.",
    source := "base/mpfr.jl:1129-1131; documentation: base/float.jl:710-714", status := .proven,
    prop := ``Round1.IsInfValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1129V2_proven },
  { id := "bignumscov-mpfr-1133-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["isnan@1133"],
    statement := "Isnan is true exactly when neither lower nor upper comparison with the extended real endpoints orders the represented value; this states semantic classification, not the exponent-tag test.",
    source := "base/mpfr.jl:1133-1135; documentation: base/float.jl:695-700", status := .proven,
    prop := ``Round1.IsNaNValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1133V2_proven },
  { id := "mpfr-isfinite-value", juliaFile := "base/mpfr.jl",
    juliaFns := ["isfinite@1139"],
    statement := "Isfinite is true exactly for values strictly between negative and positive infinity in independent numeric order, including both zeros.",
    source := "base/mpfr.jl:1139; documentation: base/number.jl:69-82", status := .proven,
    prop := ``Round1.IsFiniteValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.MpfrIsfiniteValue_proven },
  { id := "bignumscov-mpfr-1141-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["iszero@1141"],
    statement := "Iszero is true exactly for numeric zero, irrespective of its sign, and false for nonzero finite values and all nonfinite values.",
    source := "base/mpfr.jl:1141; documentation: base/number.jl:25-44", status := .proven,
    prop := ``Round1.IsZeroValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1141V2_proven },
  { id := "bignumscov-mpfr-1142-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["isone@1142"],
    statement := "Isone is true exactly for mathematical one at any precision, excluding all special values.",
    source := "base/mpfr.jl:1142; documentation: base/number.jl:47-66", status := .proven,
    prop := ``Round1.IsOneValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1142V2_proven },
  { id := "mpfr-ispositive-value", juliaFile := "base/mpfr.jl",
    juliaFns := ["ispositive@1145"],
    statement := "Ispositive is true exactly for values mathematically greater than zero, including positive infinity and excluding both zeros and NaNs.",
    source := "base/mpfr.jl:1145; documentation: base/number.jl:146-165", status := .proven,
    prop := ``Round1.IsPositiveValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.MpfrIspositiveValue_proven },
  { id := "mpfr-isnegative-value", juliaFile := "base/mpfr.jl",
    juliaFns := ["isnegative@1146"],
    statement := "Isnegative is true exactly for values mathematically less than zero, including negative infinity and excluding negative zero and NaNs.",
    source := "base/mpfr.jl:1146; documentation: base/number.jl:168-187", status := .proven,
    prop := ``Round1.IsNegativeValue, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.MpfrIsnegativeValue_proven },
  { id := "bignumscov-mpfr-1148-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["typemax@1148"],
    statement := "Typemax is an infinite value that is an upper bound under the actual BigFloat <= model for every non-NaN input, at every valid stored precision.",
    source := "base/mpfr.jl:1148; documentation: doc/src/manual/integers-and-floating-point-numbers.md:438-449", status := .proven,
    prop := ``Round1.TypemaxUpperBound, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1148V2_proven },
  { id := "bignumscov-mpfr-1149-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["typemin@1149"],
    statement := "Typemin is an infinite value that is a lower bound under the actual BigFloat <= model for every non-NaN input, at every valid stored precision.",
    source := "base/mpfr.jl:1149; documentation: doc/src/manual/integers-and-floating-point-numbers.md:438-449", status := .proven,
    prop := ``Round1.TypeminLowerBound, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfr1149V2_proven },
  { id := "bignumscov-mpfr-setup-rounding-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["version", "patches", "__init__", "convert rounding modes", "rounds_to_nearest", "rounds_away_from_zero", "tie_breaker_is_to_even"],
    statement := "The publicly reachable rounding-mode conversions preserve numerical direction, with round-based observations respecting its documented ambient-nearest precondition; setting BigFloat rounding is observed by rounding(BigFloat), and scoped setting has the documented save/set/callback/restore behavior, including returned value, exceptions and final state from every publicly reachable initial rounding mode. Internal __init__ and private rounding traits are no longer registry subjects.",
    source := "base/mpfr.jl:75-95,252-255; documentation: base/rounding.jl:25-110,190-245,349-350", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #51277, #51362; see bugs/bignumscov-mpfr-setup-rounding-v2.yaml",
    prop := ``Round1.PublicRoundingControlsCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group3.BignumscovMpfrSetupRoundingV2_refuted },
  { id := "bignumscov-mpfr-ieee-routing-v2", juliaFile := "base/mpfr.jl",
    juliaFns := ["to_ieee754", "Float16", "Float32", "Float64", "promote_rule", "big", "Rational{BigInt}"],
    statement := "Conversion from every valid BigFloat to Float16, Float32 and Float64 selects the mathematical nearest/directed IEEE neighbor, with correct ties, gradual underflow, overflow, signed zero and infinities, and NaN classification; both public RoundingMode and publicly reachable raw-mode overloads are included.",
    source := "base/mpfr.jl:494-555; documentation: base/rounding.jl:25-110,264-286,352-355", status := .todo,
    prop := ``Round1.AllIEEEFormatsCorrect, thm := none,
    notes := "Open proof: connect the central finite normal/subnormal/overflow branch of toIEEE to IEEEConversion, then apply ri_all_ieee_of_generic_public. Existing special-value, storage, underflow-selection and high-exponent-bound lemmas remain available." }
]

end JuliaLean.Proofs.base.mpfr

namespace JuliaLean.Proofs.base.mpfr

namespace LegacyRetired

open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float

def Version44 : Prop :=
  ∀ globals : LibraryVersion,
    JuliaLean.base.mpfr.version
      (fun text => JuliaLean.VersionNumbers.parse text.toList) globals =
    JuliaLean.VersionNumbers.parse globals.versionString.toList

theorem version44_proven : Version44 := by unfold Version44; intros; rfl

def Patches45 : Prop :=
  ∀ (globals : LibraryVersion),
    JuliaLean.base.mpfr.patches globals = (
    globals.patchesString.splitOn " ")

theorem patches45_proven : Patches45 := by unfold Patches45; intros; rfl

def Init47 : Prop :=
  ∀ (showError : JlError → Unit) (state : Context),
    ((initModule (fun error => pure (showError error))).run state).1 = .ok ()

def Convert75 : Prop := toMPFR .Nearest = .ok .nearest

theorem convert75_proven : Convert75 := by unfold Convert75; intros; rfl

def Convert76 : Prop := toMPFR .ToZero = .ok .toZero

theorem convert76_proven : Convert76 := by unfold Convert76; intros; rfl

def Convert77 : Prop := toMPFR .Up = .ok .up

theorem convert77_proven : Convert77 := by unfold Convert77; intros; rfl

def Convert78 : Prop := toMPFR .Down = .ok .down

theorem convert78_proven : Convert78 := by unfold Convert78; intros; rfl

def Convert79 : Prop := toMPFR .FromZero = .ok .fromZero

theorem convert79_proven : Convert79 := by unfold Convert79; intros; rfl

def Convert81 : Prop :=
  ∀ mode : Mode, toPublic mode =
    match mode with
    | .nearest => .ok .Nearest
    | .toZero => .ok .ToZero
    | .up => .ok .Up
    | .down => .ok .Down
    | .fromZero => .ok .FromZero
    | .faithful => .error (.argumentError "invalid MPFR rounding mode code")

theorem convert81_proven : Convert81 := by intro mode; cases mode <;> rfl

def TieBreaker110 : Prop :=
  ∀ (_r : Mode),
    JuliaLean.base.mpfr.tieBreakerEven _r = (
    true)

theorem tieBreaker110_proven : TieBreaker110 := by unfold TieBreaker110; intros; rfl

def BigFloat154 : Prop :=
  ∀ (I : Type) (ops : IntegerPrecision I) (precision : I),
    JuliaLean.base.mpfr.constructInteger (I := I) ops precision = (
    do
     if ← ops.lessOne precision then throw (.domainError "`precision` cannot be less than 1.")
     let cPrecision ← ops.ccallClong precision
     let _nb := customGetSize cPrecision
     let allocated := pack cPrecision (.nan false)
     let precision ← ops.clong precision
     pure { allocated with prec := precision })

theorem bigFloat154_proven : BigFloat154 := by unfold BigFloat154; intros; rfl

def Getproperty183 : Prop :=
  ∀ (x : BigFloat) (field : String),
    JuliaLean.base.mpfr.getproperty x field = (
    if field = "prec" then pure (.precision x.prec)
    else if field = "sign" then pure (.sign x.sign)
    else if field = "exp" then pure (.exponent x.exp)
    else if field = "d" then pure (.data x.d)
    else .error (.fieldError field))

theorem getproperty183_proven : Getproperty183 := by unfold Getproperty183; intros; rfl

def Setproperty201 : Prop :=
  ∀ (x : BigFloat) (field : String) (v : Int),
    JuliaLean.base.mpfr.setproperty x field v = (
    if field = "sign" then do
      let v ← (JInt.convert "Int32" .i32 v).mapError StorageError.julia
      pure (setpropertySign x v)
    else if field = "exp" then do
      let v ← (JInt.convert "Int64" .i64 v).mapError StorageError.julia
      pure (setpropertyExp x v)
    else .error (.fieldError field))

theorem setproperty201_proven : Setproperty201 := by unfold Setproperty201; intros; rfl

def UnsafeConvert214 : Prop :=
  JuliaLean.base.mpfr.incompatiblePointerRef = (
    .error .incompatibleRef)

theorem unsafeConvert214_proven : UnsafeConvert214 := by unfold UnsafeConvert214; intros; rfl

def UnsafeConvert215 : Prop :=
  JuliaLean.base.mpfr.incompatibleValueRef = (
    .error .incompatibleRef)

theorem unsafeConvert215_proven : UnsafeConvert215 := by unfold UnsafeConvert215; intros; rfl

def Cconvert216 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.cconvertBigFloat x = (
    x.d)

theorem cconvert216_proven : Cconvert216 := by unfold Cconvert216; intros; rfl

def Cconvert217 : Prop :=
  ∀ (N : Type) (convert : N → Jl BigFloat) (x : N),
    JuliaLean.base.mpfr.cconvertNumber (N := N) convert x = (
    do
     return (← convert x).d)

theorem cconvert217_proven : Cconvert217 := by unfold Cconvert217; intros; rfl

def Cconvert218 : Prop :=
  ∀ (Reference : Type) (dereference : Reference → BigFloat) (reference : Reference),
    cconvertRef (dereference reference) = (dereference reference).d

theorem cconvert218_proven : Cconvert218 := by unfold Cconvert218; intros; rfl

def UnsafeConvert219 : Prop :=
  ∀ (Memory LimbPointer PointerPointer BigFloatRef Order : Type) (ops : BigFloatPointerOps Memory LimbPointer PointerPointer BigFloatRef Order) (x : BigFloatData Memory),
    JuliaLean.base.mpfr.unsafeConvertBigFloatRef (Memory := Memory) (LimbPointer := LimbPointer) (PointerPointer := PointerPointer) (BigFloatRef := BigFloatRef) (Order := Order) ops x = (
    do
     let d := x.d
     let p := ops.memoryToLimbPointer d
     let dptrptr := ops.addPointerOffset (ops.toPointerPointer p) ops.offsetD
     let dptr := ops.addLimbOffset p ops.offsetP
     let _ ← ops.preserve d (fun _ => do
       let current ← ops.unsafeLoadPointer dptrptr ops.monotonic
       if !ops.pointerEqual current dptr then
         ops.unsafeStorePointer dptrptr dptr ops.monotonic
       else pure ())
     pure (ops.bigFloatRef p))

theorem unsafeConvert219_proven : UnsafeConvert219 := by unfold UnsafeConvert219; intros; rfl

def UnsafeConvert229 : Prop :=
  ∀ (Memory LimbPointer PointerPointer BigFloatRef Order : Type) (ops : BigFloatPointerOps Memory LimbPointer PointerPointer BigFloatRef Order) (fd : BigFloatData Memory),
    JuliaLean.base.mpfr.unsafeConvertBigFloatLimbPtr (Memory := Memory) (LimbPointer := LimbPointer) (PointerPointer := PointerPointer) (BigFloatRef := BigFloatRef) (Order := Order) ops fd = (
    do
     let p := ops.memoryToLimbPointer fd.d
     pure (ops.addLimbOffset p ops.offsetP))

theorem unsafeConvert229_proven : UnsafeConvert229 := by unfold UnsafeConvert229; intros; rfl

def Setindex230 : Prop :=
  ∀ (limbs : List Limb) (v : Limb) (i : Clong),
    JuliaLean.base.mpfr.dataSetindex limbs v i = (
    if i.val < 1 ∨ i.val > (limbs.length : Nat) then .error .boundsError
    else pure (limbs.set (i.val-1).toNat v))

theorem setindex230_proven : Setindex230 := by unfold Setindex230; intros; rfl

def Getindex236 : Prop :=
  ∀ (limbs : List Limb) (i : Clong),
    JuliaLean.base.mpfr.dataGetindex limbs i = (
    if i.val < 1 ∨ i.val > (limbs.length : Nat) then .error .boundsError
    else match limbs[(i.val-1).toNat]? with
      | some l => pure l
      | none => .error .boundsError)

theorem getindex236_proven : Getindex236 := by unfold Getindex236; intros; rfl

def Length241 : Prop :=
  ∀ (limbs : List Limb),
    JuliaLean.base.mpfr.dataLength limbs = (
    JInt.wrap .i64 (limbs.length : Int))

theorem length241_proven : Length241 := by unfold Length241; intros; rfl

def Copyto242 : Prop :=
  ∀ (limbs source : List Limb),
    JuliaLean.base.mpfr.dataCopyto limbs source = (
    if source.length > limbs.length then .error .boundsError
    else pure (source ++ limbs.drop source.length))

theorem copyto242_proven : Copyto242 := by unfold Copyto242; intros; rfl

def SetroundingRaw247 : Prop :=
  ∀ (r : Mode),
    JuliaLean.base.mpfr.setroundingRaw r = (
    do
     let state ← readContext
     writeContext { state with defaultRounding := r }
     pure r)

theorem setroundingRaw247_proven : SetroundingRaw247 := by unfold SetroundingRaw247; intros; rfl

def SetroundingRaw248 : Prop :=
  ∀ (A : Type) (action : M A) (r : Mode),
    JuliaLean.base.mpfr.withRoundingRaw action r = (
    ⟨fun state =>
     let previous := state.scopedRounding
     let (result,after) := action.run { state with scopedRounding := some r }
     (result,{ after with scopedRounding := previous })⟩)

theorem setroundingRaw248_proven : SetroundingRaw248 := by unfold SetroundingRaw248; intros; rfl

def Rounding252 : Prop :=
  JuliaLean.base.mpfr.rounding = (
    do liftJl (toPublic (roundingRaw (← readContext))))

theorem rounding252_proven : Rounding252 := by unfold Rounding252; intros; rfl

def Setrounding253 : Prop :=
  ∀ (r : RoundingMode),
    JuliaLean.base.mpfr.setrounding r = (
    do setroundingRaw (← liftJl (toMPFR r)))

theorem setrounding253_proven : Setrounding253 := by unfold Setrounding253; intros; rfl

def Setrounding254 : Prop :=
  ∀ (A : Type) (action : M A) (r : RoundingMode),
    JuliaLean.base.mpfr.withRounding action r = (
    do
     withRoundingRaw action (← liftJl (toMPFR r)))

theorem setrounding254_proven : Setrounding254 := by unfold Setrounding254; intros; rfl

def Widen299 : Prop :=
  JuliaLean.base.mpfr.widenFloat64 = (
    .type)

theorem widen299_proven : Widen299 := by unfold Widen299; intros; rfl

def Widen300 : Prop :=
  JuliaLean.base.mpfr.widenBigFloat = (
    .type)

theorem widen300_proven : Widen300 := by unfold Widen300; intros; rfl

def BigFloat302 : Prop :=
  ∀ (x : BigFloat) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromBigFloat x r precision = (
    do
     if precision = x.prec.val then return x
     let z ← constructInteger valuePrecision precision
     applyPrimitive (setPrimitive (← readContext) z.prec x.value r))

theorem bigFloat302_proven : BigFloat302 := by unfold BigFloat302; intros; rfl

def Duplicate313 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.duplicate x = (
    do
     let z ← constructInteger (bitsPrecision .i64) x.prec
     applyPrimitive (setPrimitive (← readContext) z.prec x.value .nearest))

theorem duplicate313_proven : Duplicate313 := by unfold Duplicate313; intros; rfl

def BigFloat322 : Prop :=
  ∀ (t : IntTy) (x : JInt t) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromLong (t := t) x r precision = (
    do
     let z ← constructInteger valuePrecision precision
     applyPrimitive (setPrimitive (← readContext) z.prec (intValue x.val) r))

theorem bigFloat322_proven : BigFloat322 := by unfold BigFloat322; intros; rfl

def BigFloat330 : Prop :=
  ∀ (x : FV .f64) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromFloat64 x r precision = (
    do
     let z ← constructInteger valuePrecision precision
     if precision ≤ 52 then
       let z ← applyPrimitive (setPrimitive (← readContext) z.prec (ieeeValue x) r)
       if x.isnan && (x.signbit != z.value.signbit) then
         return pack z.prec (.nan x.signbit)
       return z
     return pack z.prec (ieeeValue x))

theorem bigFloat330_proven : BigFloat330 := by unfold BigFloat330; intros; rfl

def BigFloat374 : Prop :=
  ∀ (x : BigInt) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromBigInt x r precision = (
    do
     let z ← constructInteger valuePrecision precision
     applyPrimitive (setPrimitive (← readContext) z.prec (intValue x.val) r))

theorem bigFloat374_proven : BigFloat374 := by unfold BigFloat374; intros; rfl

def BigFloat380 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : I) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromInteger (I := I) (U := U) ops x r precision = (
    fromBigInt (JuliaLean.base.gmp.fromInteger ops x) r precision)

theorem bigFloat380_proven : BigFloat380 := by unfold BigFloat380; intros; rfl

def BigFloat382 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : I) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromInteger (I := I) (U := U) ops x r precision = (
    fromBigInt (JuliaLean.base.gmp.fromInteger ops x) r precision)

theorem bigFloat382_proven : BigFloat382 := by unfold BigFloat382; intros; rfl

def BigFloat385 : Prop :=
  ∀ (t : IntTy) (x : JInt t) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromSmallSigned (t := t) x r precision = (
    do
     let x ← liftJl (JInt.convert "Int64" .i64 x.val)
     fromLong x r precision)

theorem bigFloat385_proven : BigFloat385 := by unfold BigFloat385; intros; rfl

def BigFloat387 : Prop :=
  ∀ (t : IntTy) (x : JInt t) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromSmallUnsigned (t := t) x r precision = (
    do
     let x ← liftJl (JInt.convert "UInt64" .u64 x.val)
     fromLong x r precision)

theorem bigFloat387_proven : BigFloat387 := by unfold BigFloat387; intros; rfl

def BigFloat390 : Prop :=
  ∀ (T : FTy) (x : FV T) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromSmallFloat (T := T) x r precision = (
    fromFloat64 (convertFloat .f64 x) r precision)

theorem bigFloat390_proven : BigFloat390 := by unfold BigFloat390; intros; rfl

def BigFloat393 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : JuliaLean.base.rational.Rational I) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromRational (I := I) (U := U) ops x r precision = (
    do
     let rden := oppositeRound r
     let previous := (← readContext).scopedPrecision
     let p ← liftJl (JInt.convert "Int64" .i64 precision)
     let state ← readContext
     writeContext { state with scopedPrecision := some p }
     let action : M BigFloat := withRoundingRaw (do
       let n ← fromInteger ops x.num r precision
       let d ← fromInteger ops x.den rden precision
       arithmetic .div n d) r
     let result ← tryCatch (do let value ← action; pure (.ok value)) (fun error => pure (.error error))
     let after ← readContext
     writeContext { after with scopedPrecision := previous }
     liftJl result)

theorem bigFloat393_proven : BigFloat393 := by unfold BigFloat393; intros; rfl

def Opposite401 : Prop :=
  ∀ (r : Mode),
    JuliaLean.base.mpfr.oppositeRound r = (
    if r = .up then .down else if r = .down then .up else r)

theorem opposite401_proven : Opposite401 := by unfold Opposite401; intros; rfl

def Tryparse407 : Prop :=
  ∀ (space : Char → Bool) (s : String) (base precision : Int) (rounding : Mode) (localePoint : Char) (state : Context),
    JuliaLean.base.mpfr.tryparse space s base precision rounding localePoint state = (
    let chars := s.toList
    let s := if chars.getLast?.any space then String.ofList ((chars.reverse.dropWhile space).reverse) else s
    let (constructed, state) := (constructInteger valuePrecision precision).run state
    match constructed with
    | .error error => pure (.error error,state)
    | .ok z =>
      if s.toList.contains (Char.ofNat 0) then
        pure (.error (.argumentError "embedded NULs are not allowed in C strings"),state)
      else if base ≠ 0 ∧ !(2 ≤ base ∧ base ≤ 62) then .error .invalidBase
      else match parseExact s base.toNat localePoint with
        | none => pure (.ok none,state)
        | some exact =>
          let result := roundExact state z.prec rounding exact
          pure (.ok (some result.value),{ state with flags := state.flags.merge result.flags }))

theorem tryparse407_proven : Tryparse407 := by unfold Tryparse407; intros; rfl

def BigFloat414 : Prop :=
  ∀ (S : Type) (parse : S → Int → Mode → M BigFloat) (x : S) (r : Mode) (precision : Int),
    JuliaLean.base.mpfr.fromString (S := S) parse x r precision = (
    parse x precision r)

theorem bigFloat414_proven : BigFloat414 := by unfold BigFloat414; intros; rfl

def Rational417 : Prop :=
  ∀ (R : Type) (convert : BigFloat → Jl R) (x : BigFloat),
    JuliaLean.base.mpfr.rationalBigFloat (R := R) convert x = (
    convert x)

theorem rational417_proven : Rational417 := by unfold Rational417; intros; rfl

def AbstractFloat418 : Prop :=
  ∀ (x : BigInt),
    JuliaLean.base.mpfr.abstractFloatBigInt x = (
    do
     let state ← readContext
     fromBigInt x (roundingRaw state) (precisionType state).val)

theorem abstractFloat418_proven : AbstractFloat418 := by unfold AbstractFloat418; intros; rfl

def Float420 : Prop :=
  JuliaLean.base.mpfr.floatBigIntType = (
    .type)

theorem float420_proven : Float420 := by unfold Float420; intros; rfl

def BigFloat422 : Prop :=
  ∀ (R : Type) (construct : R → Mode → Int → M BigFloat) (x : R) (r : RoundingMode) (precision : Int),
    JuliaLean.base.mpfr.fromRealPublic (R := R) construct x r precision = (
    do
     construct x (← liftJl (toMPFR r)) precision)

theorem bigFloat422_proven : BigFloat422 := by unfold BigFloat422; intros; rfl

def BigFloat424 : Prop :=
  ∀ (S : Type) (construct : S → Mode → Int → M BigFloat) (x : S) (r : RoundingMode) (precision : Int),
    JuliaLean.base.mpfr.fromStringPublic (S := S) construct x r precision = (
    do
     construct x (← liftJl (toMPFR r)) precision)

theorem bigFloat424_proven : BigFloat424 := by unfold BigFloat424; intros; rfl

def Unchecked428 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (r : RoundingMode),
    JuliaLean.base.mpfr.uncheckedCastBitsPublic t x r = (
    do
     uncheckedCastBits t x (← liftJl (toMPFR r)))

theorem unchecked428_proven : Unchecked428 := by unfold Unchecked428; intros; rfl

def Unchecked430 : Prop :=
  ∀ (x : BigFloat) (mode : Mode),
    uncheckedCastBits .i64 x mode = (do
      let state ← readContext
      applyIntegerPrimitive (getCIntegerPrimitive state .i64 x mode))

theorem unchecked430_proven : Unchecked430 := by unfold Unchecked430; intros; rfl

def Unchecked434 : Prop :=
  ∀ (x : BigFloat) (mode : Mode),
    uncheckedCastBits .u64 x mode = (do
      let state ← readContext
      applyIntegerPrimitive (getCIntegerPrimitive state .u64 x mode))

theorem unchecked434_proven : Unchecked434 := by unfold Unchecked434; intros; rfl

def Unchecked438 : Prop :=
  ∀ (x : BigFloat) (r : Mode),
    JuliaLean.base.mpfr.uncheckedCastBigInt x r = (
    do
     let state ← readContext
     let value ← applyIntegerPrimitive (getZPrimitive state x r)
     return JuliaLean.base.gmp.ofInt value)

theorem unchecked438_proven : Unchecked438 := by unfold Unchecked438; intros; rfl

def Unchecked444 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (r : Mode),
    JuliaLean.base.mpfr.uncheckedCastBits t x r = (
    do
     let state ← readContext
     if t = .i64 ∨ t = .u64 then
       applyIntegerPrimitive (getCIntegerPrimitive state t x r)
     else
       let ct := if t.signed then IntTy.i64 else IntTy.u64
       if t.max < ct.max then applyIntegerPrimitive (getCIntegerPrimitive state ct x r)
       else applyIntegerPrimitive (getZPrimitive state x r))

theorem unchecked444_proven : Unchecked444 := by unfold Unchecked444; intros; rfl

def Round449 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (r : Mode),
    JuliaLean.base.mpfr.roundBits t x r = (
    do
     clearFlags
     let result ← uncheckedCastBits t x r
     if hadRange (← readContext) || !(t.min ≤ result ∧ result ≤ t.max) then
       throw (.inexactError "round")
     return JInt.wrap t result)

theorem round449_proven : Round449 := by unfold Round449; intros; rfl

def Round458 : Prop :=
  ∀ (x : BigFloat) (r : Mode),
    JuliaLean.base.mpfr.roundBigInt x r = (
    do
     clearFlags
     let result ← uncheckedCastBigInt x r
     if hadRange (← readContext) then throw (.inexactError "round")
     return result)

theorem round458_proven : Round458 := by unfold Round458; intros; rfl

def Invoke465 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (r : RoundingMode),
    JuliaLean.base.mpfr.roundBitsPublic t x r = (
    do
     roundBits t x (← liftJl (toMPFR r)))

theorem invoke465_proven : Invoke465 := by unfold Invoke465; intros; rfl

def Invoke467 : Prop :=
  ∀ (x : BigFloat) (r : RoundingMode),
    JuliaLean.base.mpfr.roundBigIntPublic x r = (
    do
     roundBigInt x (← liftJl (toMPFR r)))

theorem invoke467_proven : Invoke467 := by unfold Invoke467; intros; rfl

def Unsafe471 : Prop :=
  ∀ (t : IntTy) (x : BigFloat),
    JuliaLean.base.mpfr.unsafeTruncBits t x = (
    do
     return JInt.wrap t (← uncheckedCastBits t x .toZero))

theorem unsafe471_proven : Unsafe471 := by unfold Unsafe471; intros; rfl

def Unsafe472 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.unsafeTruncBigInt x = (
    uncheckedCastBigInt x .toZero)

theorem unsafe472_proven : Unsafe472 := by unfold Unsafe472; intros; rfl

def Round474 : Prop :=
  ∀ (t : IntTy) (x : BigFloat),
    JuliaLean.base.mpfr.roundBitsDefault t x = (
    do
     roundBits t x (roundingRaw (← readContext)))

theorem round474_proven : Round474 := by unfold Round474; intros; rfl

def Round476 : Prop :=
  ∀ (x : BigFloat) (r : RoundingMode),
    JuliaLean.base.mpfr.roundBigIntPublic x r = (
    do
     roundBigInt x (← liftJl (toMPFR r)))

theorem round476_proven : Round476 := by unfold Round476; intros; rfl

def Round477 : Prop :=
  ∀ (x : BigFloat) (r : Mode),
    JuliaLean.base.mpfr.roundInteger x r = (
    roundBigInt x r)

theorem round477_proven : Round477 := by unfold Round477; intros; rfl

def Bool479 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.toBool x = (
    do
     if iszero x then return false
     let (n,d) := x.value.toRat
     if isfinite x && decide (n = (d : Int)) then return true
     throw (.inexactError "Bool"))

theorem bool479_proven : Bool479 := by unfold Bool479; intros; rfl

def BigInt484 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.toBigInt x = (
    do
     if !isinteger x then throw (.inexactError "BigInt")
     roundBigInt x .toZero)

theorem bigInt484_proven : BigInt484 := by unfold BigInt484; intros; rfl

def Convert489 : Prop :=
  ∀ (t : IntTy) (x : BigFloat),
    JuliaLean.base.mpfr.toBits t x = (
    do
     if !isinteger x then throw (.inexactError t.name)
     roundBits t x .toZero)

theorem convert489_proven : Convert489 := by unfold Convert489; intros; rfl

def ToIeee494 : Prop :=
  ∀ (T : FTy) (x : BigFloat) (mode : RoundingMode),
    let result := toIEEE T x mode
    result.isfinite = true ∨ result.isinf = true ∨ result.isnan = true

def Float550 : Prop :=
  ∀ (x : BigFloat) (rm : Mode),
    JuliaLean.base.mpfr.toFloat16 x rm = (
    toIEEERaw .f16 x rm)

theorem float550_proven : Float550 := by unfold Float550; intros; rfl

def Float551 : Prop :=
  ∀ (x : BigFloat) (rm : Mode),
    JuliaLean.base.mpfr.toFloat32 x rm = (
    toIEEERaw .f32 x rm)

theorem float551_proven : Float551 := by unfold Float551; intros; rfl

def Float552 : Prop :=
  ∀ (x : BigFloat) (rm : Mode),
    JuliaLean.base.mpfr.toFloat64 x rm = (
    toIEEERaw .f64 x rm)

theorem float552_proven : Float552 := by unfold Float552; intros; rfl

def Float553 : Prop :=
  ∀ (x : BigFloat) (rm : RoundingMode),
    JuliaLean.base.mpfr.toFloat16Public x rm = (
    toIEEE .f16 x rm)

theorem float553_proven : Float553 := by unfold Float553; intros; rfl

def Float554 : Prop :=
  ∀ (x : BigFloat) (rm : RoundingMode),
    JuliaLean.base.mpfr.toFloat32Public x rm = (
    toIEEE .f32 x rm)

theorem float554_proven : Float554 := by unfold Float554; intros; rfl

def Float555 : Prop :=
  ∀ (x : BigFloat) (rm : RoundingMode),
    JuliaLean.base.mpfr.toFloat64Public x rm = (
    toIEEE .f64 x rm)

theorem float555_proven : Float555 := by unfold Float555; intros; rfl

def Promote557 : Prop :=
  JuliaLean.base.mpfr.promoteBigFloatReal = (
    .type)

theorem promote557_proven : Promote557 := by unfold Promote557; intros; rfl

def Promote558 : Prop :=
  JuliaLean.base.mpfr.promoteBigIntAbstractFloat = (
    .type)

theorem promote558_proven : Promote558 := by unfold Promote558; intros; rfl

def Promote559 : Prop :=
  JuliaLean.base.mpfr.promoteBigFloatAbstractFloat = (
    .type)

theorem promote559_proven : Promote559 := by unfold Promote559; intros; rfl

def Big561 : Prop :=
  JuliaLean.base.mpfr.bigAbstractFloatType = (
    .type)

theorem big561_proven : Big561 := by unfold Big561; intros; rfl

def Big563 : Prop :=
  ∀ (F : Type) (convert : F → Jl BigFloat) (x : F),
    JuliaLean.base.mpfr.bigAbstractFloat (F := F) convert x = (
    convert x)

theorem big563_proven : Big563 := by unfold Big563; intros; rfl

def Rational565 : Prop :=
  ∀ (F R : Type) (isnan isinf iszero : F → Bool) (precision exponent : F → M Clong) (copysignOne : F → M BigInt) (ldexp : F → Clong → M F) (toBigInt : F → M BigInt) (rational : BigInt → BigInt → M R) (x : F),
    JuliaLean.base.mpfr.rationalAbstractFloat (F := F) (R := R) isnan isinf iszero precision exponent copysignOne ldexp toBigInt rational x = (
    do
     if isnan x then return ← rational (JuliaLean.base.gmp.ofInt 0) (JuliaLean.base.gmp.ofInt 0)
     if isinf x then return ← rational (← copysignOne x) (JuliaLean.base.gmp.ofInt 0)
     if iszero x then return ← rational (JuliaLean.base.gmp.ofInt 0) (JuliaLean.base.gmp.ofInt 1)
     let s := JInt.wrap .i64 (max ((← precision x)-(← exponent x)).val 0)
     let num ← toBigInt (← ldexp x s)
     let den := JuliaLean.base.gmp.shiftLeft (JuliaLean.base.gmp.ofInt 1) (JInt.wrap .u64 s.val)
     rational num den)

theorem rational565_proven : Rational565 := by unfold Rational565; intros; rfl

def Reverse589 : Prop :=
  ∀ (t : IntTy) (operation : BinaryOp) (scalar : JInt t) (x : BigFloat),
    (operation = .add ∨ operation = .mul) →
    integerArithmetic operation scalar x = arithmeticInteger operation x scalar

def Reverse597 : Prop :=
  ∀ (t : IntTy) (operation : BinaryOp) (scalar : JInt t) (x : BigFloat),
    (operation = .add ∨ operation = .mul) →
    integerArithmetic operation scalar x = arithmeticInteger operation x scalar

def Reverse605 : Prop :=
  ∀ (T : FTy) (operation : BinaryOp) (scalar : FV T) (x : BigFloat),
    (operation = .add ∨ operation = .mul) →
    ieeeArithmetic operation scalar x = arithmeticIEEE operation x scalar

def Reverse613 : Prop :=
  ∀ (op : BinaryOp) (c : BigInt) (x : BigFloat),
    JuliaLean.base.mpfr.bigIntCommutative op c x = (
    arithmeticBigInt op x c)

theorem reverse613_proven : Reverse613 := by unfold Reverse613; intros; rfl

def Inv678 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.inv x = (
    integerArithmetic .div (JInt.wrap .i64 1) x)

theorem inv678_proven : Inv678 := by unfold Inv678; intros; rfl

def Muladd686 : Prop :=
  ∀ (x y z : BigFloat),
    JuliaLean.base.mpfr.muladd x y z = (
    fma x y z)

theorem muladd686_proven : Muladd686 := by unfold Muladd686; intros; rfl

def Div690 : Prop :=
  ∀ (x y : BigFloat),
    JuliaLean.base.mpfr.div x y = (
    do
     let z ← binaryCall .div ⟨x.value,false⟩ ⟨y.value,false⟩ .toZero
     truncateOutput z)

theorem div690_proven : Div690 := by unfold Div690; intros; rfl

def Div698 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (c : JInt t),
    JuliaLean.base.mpfr.divInteger (t := t) x c = (
    do
     let z ← binaryCall .div ⟨x.value,false⟩ (.ofInt c.val) .toZero
     truncateOutput z)

theorem div698_proven : Div698 := by unfold Div698; intros; rfl

def Div704 : Prop :=
  ∀ (t : IntTy) (c : JInt t) (x : BigFloat),
    JuliaLean.base.mpfr.integerDiv (t := t) c x = (
    do
     let z ← binaryCall .div (.ofInt c.val) ⟨x.value,false⟩ .toZero
     truncateOutput z)

theorem div704_proven : Div704 := by unfold Div704; intros; rfl

def Div712 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (c : JInt t),
    JuliaLean.base.mpfr.divInteger (t := t) x c = (
    do
     let z ← binaryCall .div ⟨x.value,false⟩ (.ofInt c.val) .toZero
     truncateOutput z)

theorem div712_proven : Div712 := by unfold Div712; intros; rfl

def Div718 : Prop :=
  ∀ (t : IntTy) (c : JInt t) (x : BigFloat),
    JuliaLean.base.mpfr.integerDiv (t := t) c x = (
    do
     let z ← binaryCall .div (.ofInt c.val) ⟨x.value,false⟩ .toZero
     truncateOutput z)

theorem div718_proven : Div718 := by unfold Div718; intros; rfl

def Div726 : Prop :=
  ∀ (T : FTy) (x : BigFloat) (c : FV T),
    JuliaLean.base.mpfr.divIEEE (T := T) x c = (
    do
     let z ← binaryCall .div ⟨x.value,false⟩ ⟨ieeeValue (convertFloat .f64 c),false⟩ .toZero
     truncateOutput z)

theorem div726_proven : Div726 := by unfold Div726; intros; rfl

def Div732 : Prop :=
  ∀ (T : FTy) (c : FV T) (x : BigFloat),
    JuliaLean.base.mpfr.ieeeDiv (T := T) c x = (
    do
     let z ← binaryCall .div ⟨ieeeValue (convertFloat .f64 c),false⟩ ⟨x.value,false⟩ .toZero
     truncateOutput z)

theorem div732_proven : Div732 := by unfold Div732; intros; rfl

def Div740 : Prop :=
  ∀ (x : BigFloat) (c : BigInt),
    JuliaLean.base.mpfr.divBigInt x c = (
    do
     let z ← binaryCall .div ⟨x.value,false⟩ (.ofInt c.val) .toZero
     truncateOutput z)

theorem div740_proven : Div740 := by unfold Div740; intros; rfl

def Sqrt781 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.sqrt x = (
    do
     if isnan x then return x
     let z ← fresh
     let state ← readContext
     let z ← applyPrimitive (sqrtPrimitive state z.prec (roundingRaw state) x)
     if isnan z then throw (.domainError "NaN result for non-NaN input")
     return z)

theorem sqrt781_proven : Sqrt781 := by unfold Sqrt781; intros; rfl

def Sqrt789 : Prop :=
  ∀ (x : BigInt),
    JuliaLean.base.mpfr.sqrtBigInt x = (
    do
     let state ← readContext
     sqrt (← fromBigInt x (roundingRaw state) (precisionType state).val))

theorem sqrt789_proven : Sqrt789 := by unfold Sqrt789; intros; rfl

def Power815 : Prop :=
  ∀ (I U : Type) (value : I → Int) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : BigFloat) (y : I),
    JuliaLean.base.mpfr.powInteger (I := I) (U := U) value ops x y = (
    if IntTy.min .i64 ≤ value y ∧ value y ≤ IntTy.max .i64 then
      powLong x (JInt.wrap .i64 (value y))
    else powBigInt x (JuliaLean.base.gmp.fromInteger ops y))

theorem power815_proven : Power815 := by unfold Power815; intros; rfl

def Power816 : Prop :=
  ∀ (I U : Type) (value : I → Int) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : BigFloat) (y : I),
    JuliaLean.base.mpfr.powUnsigned (I := I) (U := U) value ops x y = (
    if 0 ≤ value y ∧ value y ≤ IntTy.max .u64 then powLong x (JInt.wrap .u64 (value y))
    else powBigInt x (JuliaLean.base.gmp.fromInteger ops y))

theorem power816_proven : Power816 := by unfold Power816; intros; rfl

def SincosFast826 : Prop :=
  ∀ (ops : AnalyticOps) (v : BigFloat),
    JuliaLean.base.mpfr.sincosFast ops v = (
    do
     let s ← fresh
     let c ← fresh
     let state ← readContext
     let (sineResult, cosineResult) :=
       ops.sincos state s.prec c.prec (roundingRaw state) v
     let s ← applyPrimitive sineResult
     let c ← applyPrimitive cosineResult
     pure (s, c))

theorem sincosFast826_proven : SincosFast826 := by unfold SincosFast826; intros; rfl

def Sincos832 : Prop :=
  ∀ (ops : AnalyticOps) (v : BigFloat),
    JuliaLean.base.mpfr.sincos ops v = (
    sincosFast ops v)

theorem sincos832_proven : Sincos832 := by unfold Sincos832; intros; rfl

def BigLn2835 : Prop :=
  ∀ (ops : AnalyticOps),
    JuliaLean.base.mpfr.bigLn2 ops = (
    do
     let state ← readContext
     constantWithPrecision ops .log2 (precisionType state).val (roundingRaw state))

theorem bigLn2835_proven : BigLn2835 := by unfold BigLn2835; intros; rfl

def Ldexp841 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (n : JInt t),
    JuliaLean.base.mpfr.ldexpLong (t := t) x n = (
    do
     let z ← fresh
     let value := match x.value with
       | .finite m e => FP.finite m (e+n.val)
       | v => v
     let state ← readContext
     applyPrimitive (setPrimitive state z.prec value (roundingRaw state)))

theorem ldexp841_proven : Ldexp841 := by unfold Ldexp841; intros; rfl

def Ldexp846 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (n : JInt t),
    JuliaLean.base.mpfr.ldexpLong (t := t) x n = (
    do
     let z ← fresh
     let value := match x.value with
       | .finite m e => FP.finite m (e+n.val)
       | v => v
     let state ← readContext
     applyPrimitive (setPrimitive state z.prec value (roundingRaw state)))

theorem ldexp846_proven : Ldexp846 := by unfold Ldexp846; intros; rfl

def Ldexp851 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (n : JInt t),
    JuliaLean.base.mpfr.ldexpSignedMax (t := t) x n = (
    ldexpLong x (JInt.wrap .i64 n.val))

theorem ldexp851_proven : Ldexp851 := by unfold Ldexp851; intros; rfl

def Ldexp852 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (n : JInt t),
    JuliaLean.base.mpfr.ldexpUnsignedMax (t := t) x n = (
    ldexpLong x (JInt.wrap .u64 n.val))

theorem ldexp852_proven : Ldexp852 := by unfold Ldexp852; intros; rfl

def Ldexp853 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (exp2 : BigFloat → M BigFloat) (x : BigFloat) (n : I),
    JuliaLean.base.mpfr.ldexpInteger (I := I) (U := U) ops exp2 x n = (
    do
     let state ← readContext
     let exponent ← fromInteger ops n (roundingRaw state) (precisionType state).val
     let power ← exp2 exponent
     arithmetic .mul x power)

theorem ldexp853_proven : Ldexp853 := by unfold Ldexp853; intros; rfl

def Factorial855 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.factorial x = (
    do
     if decide (compareFP x.value (intValue 0) < 0) && !isnan x || !isinteger x then
       throw (.domainError "Must be a non-negative integer")
     let ui ← toBits .u64 x
     let z ← fresh
     let state ← readContext
     applyPrimitive (roundRat state z.prec (roundingRaw state)
       (JuliaLean.base.gmp.factorialNat ui.val.toNat) 1))

theorem factorial855_proven : Factorial855 := by unfold Factorial855; intros; rfl

def Logarithm872 : Prop :=
  ∀ (ops : AnalyticOps) (name : String) (kernel : MPFRUnaryKernel) (x : BigFloat),
    JuliaLean.base.mpfr.logarithmKernel ops name kernel x = (
    do
     if !isnan x && compareFP x.value (intValue 0) < 0 then
       throw (.domainError (name ++ " was called with a negative real argument but " ++
         "will only return a complex result if called with a complex argument. Try " ++
         name ++ "(complex(x))."))
     unaryKernel ops kernel x)

theorem logarithm872_proven : Logarithm872 := by unfold Logarithm872; intros; rfl

def Log1p884 : Prop :=
  ∀ (ops : AnalyticOps) (x : BigFloat),
    JuliaLean.base.mpfr.log1p ops x = (
    do
     if !isnan x && compareFP x.value (intValue (-1)) < 0 then
       throw (.domainError "log1p was called with a real argument < -1 but will only return a complex result if called with a complex argument. Try log1p(complex(x)).")
     let z ← fresh
     let state ← readContext
     applyPrimitive (ops.unary .log1p state z.prec (roundingRaw state) x))

theorem log1p884_proven : Log1p884 := by unfold Log1p884; intros; rfl

def Minmax897 : Prop :=
  ∀ (x y : BigFloat),
    JuliaLean.base.mpfr.minmax x y = (
    if isnan x then (x,x) else if isnan y then (y,y)
    else if isless x y then (x,y) else (y,x))

theorem minmax897_proven : Minmax897 := by unfold Minmax897; intros; rfl

def Extrema903 : Prop :=
  ∀ (x y : BigFloat × BigFloat),
    JuliaLean.base.mpfr.extremaRf x y = (
    let (x1,x2) := x
    let (y1,y2) := y
    if isnan x1 then x else if isnan y1 then y
    else (if isless x1 y1 then x1 else y1, if isless x2 y2 then y2 else x2))

theorem extrema903_proven : Extrema903 := by unfold Extrema903; intros; rfl

def Modf912 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.modf x = (
    do
     let zint ← fresh
     let zfloat ← fresh
     let state ← readContext
     let integral := match x.value with
       | .nan s => specialResult zint.prec (.nan s) { nan := true }
       | .inf s => specialResult zint.prec (.inf s)
       | .zero s => specialResult zint.prec (.zero s)
       | .finite _ _ =>
         let (n,d) := x.value.toRat
         roundRat state zint.prec (roundingRaw state) (n.tdiv (d : Int)) 1 (signbit x)
     let zint ← applyPrimitive integral
     let result := match x.value with
       | .nan s => specialResult zfloat.prec (.nan s) { nan := true }
       | .inf s | .zero s => specialResult zfloat.prec (.zero s)
       | .finite _ _ =>
         let (n,d) := x.value.toRat
         let integer := n.tdiv (d : Int)
         roundRat state zfloat.prec (roundingRaw state) (n-integer*(d : Int)) d (signbit x)
     let zfloat ← applyPrimitive result
     return (zfloat,zint))

theorem modf912_proven : Modf912 := by unfold Modf912; intros; rfl

def Rem2pi932 : Prop :=
  ∀ (bigPi : M BigFloat) (remRound : BigFloat → BigFloat → RoundingMode → M BigFloat) (x : BigFloat) (r : RoundingMode),
    JuliaLean.base.mpfr.rem2pi bigPi remRound x r = (
    do
     let twicePi ← integerArithmetic .mul (JInt.wrap .i64 2) (← bigPi)
     remRound x twicePi r)

theorem rem2pi932_proven : Rem2pi932 := by unfold Rem2pi932; intros; rfl

def CheckedUnary946 : Prop :=
  ∀ (ops : AnalyticOps) (kernel : MPFRUnaryKernel) (x : BigFloat),
    JuliaLean.base.mpfr.trigonometricKernel ops kernel x = (
    do
     if isnan x then return x
     let value ← unaryKernel ops kernel x
     if isnan value then throw (.domainError "NaN result for non-NaN input.")
     pure value)

theorem checkedUnary946_proven : CheckedUnary946 := by unfold CheckedUnary946; intros; rfl

def Degree966 : Prop :=
  ∀ (ops : AnalyticOps) (kernel : MPFRDegreeUnaryKernel) (x : BigFloat),
    JuliaLean.base.mpfr.degreeUnaryKernel ops kernel x = (
    do
     if isnan x then return x
     let z ← fresh
     let state ← readContext
     let value ← applyPrimitive (ops.degreeUnary kernel state z.prec (roundingRaw state)
       (JInt.wrap .u64 360) x)
     if isnan value then throw (.domainError "NaN result for non-NaN input.")
     pure value)

theorem degree966_proven : Degree966 := by unfold Degree966; intros; rfl

def Degree973 : Prop :=
  ∀ (ops : AnalyticOps) (kernel : MPFRDegreeUnaryKernel) (x : BigFloat),
    JuliaLean.base.mpfr.degreeUnaryKernel ops kernel x = (
    do
     if isnan x then return x
     let z ← fresh
     let state ← readContext
     let value ← applyPrimitive (ops.degreeUnary kernel state z.prec (roundingRaw state)
       (JInt.wrap .u64 360) x)
     if isnan value then throw (.domainError "NaN result for non-NaN input.")
     pure value)

theorem degree973_proven : Degree973 := by unfold Degree973; intros; rfl

def Atand982 : Prop :=
  ∀ (ops : AnalyticOps) (y x : BigFloat),
    JuliaLean.base.mpfr.atand ops y x = (
    do
     let z ← fresh
     let state ← readContext
     applyPrimitive
       (ops.degreeBinary .atan2u state z.prec (roundingRaw state) (JInt.wrap .u64 360) y x))

theorem atand982_proven : Atand982 := by unfold Atand982; intros; rfl

def Equal990 : Prop :=
  ∀ (x y : BigFloat),
    JuliaLean.base.mpfr.equal x y = (
    !isnan x && !isnan y && decide (compareFP x.value y.value = 0))

theorem equal990_proven : Equal990 := by unfold Equal990; intros; rfl

def LessEqual991 : Prop :=
  ∀ (x y : BigFloat),
    JuliaLean.base.mpfr.lessEqual x y = (
    !isnan x && !isnan y && decide (compareFP x.value y.value ≤ 0))

theorem lessEqual991_proven : LessEqual991 := by unfold LessEqual991; intros; rfl

def Less992 : Prop :=
  ∀ (x y : BigFloat),
    JuliaLean.base.mpfr.less x y = (
    !isnan x && !isnan y && decide (compareFP x.value y.value < 0))

theorem less992_proven : Less992 := by unfold Less992; intros; rfl

def Cmp994 : Prop :=
  ∀ (x : BigFloat) (y : BigInt),
    JuliaLean.base.mpfr.cmpBigInt x y = (
    if isnan x then JInt.wrap .i32 1 else JInt.wrap .i32 (compareFP x.value (intValue y.val)))

theorem cmp994_proven : Cmp994 := by unfold Cmp994; intros; rfl

def Cmp998 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (y : JInt t),
    JuliaLean.base.mpfr.cmpSigned (t := t) x y = (
    if isnan x then JInt.wrap .i32 1 else JInt.wrap .i32 (compareFP x.value (intValue y.val)))

theorem cmp998_proven : Cmp998 := by unfold Cmp998; intros; rfl

def Cmp1002 : Prop :=
  ∀ (t : IntTy) (x : BigFloat) (y : JInt t),
    JuliaLean.base.mpfr.cmpUnsigned (t := t) x y = (
    if isnan x then JInt.wrap .i32 1 else JInt.wrap .i32 (compareFP x.value (intValue y.val)))

theorem cmp1002_proven : Cmp1002 := by unfold Cmp1002; intros; rfl

def Cmp1006 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : BigFloat) (y : I),
    JuliaLean.base.mpfr.cmpInteger (I := I) (U := U) ops x y = (
    cmpBigInt x (JuliaLean.base.gmp.fromInteger ops y))

theorem cmp1006_proven : Cmp1006 := by unfold Cmp1006; intros; rfl

def Cmp1007 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : I) (y : BigFloat),
    JuliaLean.base.mpfr.integerCmp (I := I) (U := U) ops x y = (
    -(cmpInteger ops y x))

theorem cmp1007_proven : Cmp1007 := by unfold Cmp1007; intros; rfl

def Cmp1009 : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T),
    JuliaLean.base.mpfr.cmpIEEE (T := T) x y = (
    if isnan x then JInt.wrap .i32 (if y.isnan then 0 else 1)
    else if y.isnan then JInt.wrap .i32 (-1)
    else JInt.wrap .i32 (compareFP x.value (ieeeValue (convertFloat .f64 y))))

theorem cmp1009_proven : Cmp1009 := by unfold Cmp1009; intros; rfl

def Cmp1014 : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat),
    JuliaLean.base.mpfr.ieeeCmp (T := T) x y = (
    -(cmpIEEE y x))

theorem cmp1014_proven : Cmp1014 := by unfold Cmp1014; intros; rfl

def Eq1016 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : BigFloat) (y : I),
    JuliaLean.base.mpfr.equalInteger (I := I) (U := U) ops x y = (
    !isnan x && decide ((cmpInteger ops x y).val = 0))

theorem eq1016_proven : Eq1016 := by unfold Eq1016; intros; rfl

def Eq1017 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : I) (y : BigFloat),
    JuliaLean.base.mpfr.integerEqual (I := I) (U := U) ops x y = (
    equalInteger ops y x)

theorem eq1017_proven : Eq1017 := by unfold Eq1017; intros; rfl

def Eq1018 : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T),
    JuliaLean.base.mpfr.equalIEEE (T := T) x y = (
    !isnan x && !y.isnan && decide ((cmpIEEE x y).val = 0))

theorem eq1018_proven : Eq1018 := by unfold Eq1018; intros; rfl

def Eq1019 : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat),
    JuliaLean.base.mpfr.ieeeEqual (T := T) x y = (
    equalIEEE y x)

theorem eq1019_proven : Eq1019 := by unfold Eq1019; intros; rfl

def Lt1021 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : BigFloat) (y : I),
    JuliaLean.base.mpfr.lessInteger (I := I) (U := U) ops x y = (
    !isnan x && decide ((cmpInteger ops x y).val < 0))

theorem lt1021_proven : Lt1021 := by unfold Lt1021; intros; rfl

def Lt1022 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : I) (y : BigFloat),
    JuliaLean.base.mpfr.integerLess (I := I) (U := U) ops x y = (
    !isnan y && decide ((cmpInteger ops y x).val > 0))

theorem lt1022_proven : Lt1022 := by unfold Lt1022; intros; rfl

def Lt1023 : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T),
    JuliaLean.base.mpfr.lessIEEE (T := T) x y = (
    !isnan x && !y.isnan && decide ((cmpIEEE x y).val < 0))

theorem lt1023_proven : Lt1023 := by unfold Lt1023; intros; rfl

def Lt1024 : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat),
    JuliaLean.base.mpfr.ieeeLess (T := T) x y = (
    !isnan y && !x.isnan && decide ((cmpIEEE y x).val > 0))

theorem lt1024_proven : Lt1024 := by unfold Lt1024; intros; rfl

def Le1026 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : BigFloat) (y : I),
    JuliaLean.base.mpfr.lessEqualInteger (I := I) (U := U) ops x y = (
    !isnan x && decide ((cmpInteger ops x y).val ≤ 0))

theorem le1026_proven : Le1026 := by unfold Le1026; intros; rfl

def Le1027 : Prop :=
  ∀ (I U : Type) (ops : JuliaLean.base.gmp.IntegerInput I U) (x : I) (y : BigFloat),
    JuliaLean.base.mpfr.integerLessEqual (I := I) (U := U) ops x y = (
    !isnan y && decide ((cmpInteger ops y x).val ≥ 0))

theorem le1027_proven : Le1027 := by unfold Le1027; intros; rfl

def Le1028 : Prop :=
  ∀ (T : FTy) (x : BigFloat) (y : FV T),
    JuliaLean.base.mpfr.lessEqualIEEE (T := T) x y = (
    !isnan x && !y.isnan && decide ((cmpIEEE x y).val ≤ 0))

theorem le1028_proven : Le1028 := by unfold Le1028; intros; rfl

def Le1029 : Prop :=
  ∀ (T : FTy) (x : FV T) (y : BigFloat),
    JuliaLean.base.mpfr.ieeeLessEqual (T := T) x y = (
    !isnan y && !x.isnan && decide ((cmpIEEE y x).val ≥ 0))

theorem le1029_proven : Le1029 := by unfold Le1029; intros; rfl

def Signbit1033 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.signbit x = (
    decide (x.sign.val < 0))

theorem signbit1033_proven : Signbit1033 := by unfold Signbit1033; intros; rfl

def Sign1035 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.sign x = (
    do
     let c := cmpSigned x (JInt.wrap .i64 0)
     if c.val = 0 || isnan x then return x
     let one ← fromLong (JInt.wrap .i64 1) (roundingRaw (← readContext))
       (precisionType (← readContext)).val
     if c.val < 0 then neg one else pure one)

theorem sign1035_proven : Sign1035 := by unfold Sign1035; intros; rfl

def Precision1041 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.precisionValue x = (
    x.prec)

theorem precision1041_proven : Precision1041 := by unfold Precision1041; intros; rfl

def Precision1044 : Prop :=
  ∀ (B : Type) (precision : BigFloat → B → Jl Clong) (x : BigFloat) (base : B),
    JuliaLean.base.mpfr.precision (B := B) precision x base = (
    precision x base)

theorem precision1044_proven : Precision1044 := by unfold Precision1044; intros; rfl

def ConvertPrecision1047 : Prop :=
  ∀ (P B R : Type) (baseIsTwo : B → Bool) (log2 : B → R) (multiply : P → R → Jl R) (ceilInt : R → Jl Clong) (asClong : P → Jl Clong) (precision : P) (base : B),
    JuliaLean.base.mpfr.convertPrecisionFromBase (P := P) (B := B) (R := R) baseIsTwo log2 multiply ceilInt asClong precision base = (
    if baseIsTwo base then asClong precision else do ceilInt (← multiply precision (log2 base)))

theorem convertPrecision1047_proven : ConvertPrecision1047 := by unfold ConvertPrecision1047; intros; rfl

def TypePrecision1050 : Prop :=
  ∀ (state : Context),
    JuliaLean.base.mpfr.precisionType state = (
    state.scopedPrecision.getD state.defaultPrecision)

theorem typePrecision1050_proven : TypePrecision1050 := by unfold TypePrecision1050; intros; rfl

def Setprecision1069 : Prop :=
  ∀ (P B : Type) (valueP : P → Int) (valueB : B → Int) (convertPrecision : P → B → Jl Clong) (precision : P) (base : B),
    JuliaLean.base.mpfr.setprecision (P := P) (B := B) valueP valueB convertPrecision precision base = (
    do
     if valueB base ≤ 1 then throw (.domainError "`base` cannot be less than 2.")
     if valueP precision ≤ 0 then throw (.domainError "`precision` cannot be less than 1.")
     let converted ← liftJl (convertPrecision precision base)
     let state ← readContext
     writeContext { state with defaultPrecision := converted }
     pure precision)

theorem setprecision1069_proven : Setprecision1069 := by unfold Setprecision1069; intros; rfl

def Setprecision1076 : Prop :=
  ∀ (P B : Type) (valueP : P → Int) (valueB : B → Int) (convertPrecision : P → B → Jl Clong) (precision : P) (base : B),
    JuliaLean.base.mpfr.setprecisionDefault (P := P) (B := B) valueP valueB convertPrecision precision base = (
    setprecision valueP valueB convertPrecision precision base)

theorem setprecision1076_proven : Setprecision1076 := by unfold Setprecision1076; intros; rfl

def Maxint1078 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.maxintfloatValue x = (
    do
     let state ← readContext
     let two ← fromLong (JInt.wrap .i64 2) (roundingRaw state) (precisionType state).val
     powLong two x.prec)

theorem maxint1078_proven : Maxint1078 := by unfold Maxint1078; intros; rfl

def Maxint1079 : Prop :=
  JuliaLean.base.mpfr.maxintfloatType = (
    do
     let state ← readContext
     let two ← fromLong (JInt.wrap .i64 2) (roundingRaw state) (precisionType state).val
     powLong two (precisionType (← readContext)))

theorem maxint1079_proven : Maxint1079 := by unfold Maxint1079; intros; rfl

def Copysign1081 : Prop :=
  ∀ (x y : BigFloat),
    JuliaLean.base.mpfr.copysign x y = (
    do
     let z ← fresh
     let value := if x.value.signbit == y.value.signbit then x.value else x.value.neg
     let state ← readContext
     applyPrimitive (setPrimitive state z.prec value (roundingRaw state)))

theorem copysign1081_proven : Copysign1081 := by unfold Copysign1081; intros; rfl

def Exponent1087 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.exponent x = (
    if iszero x || !isfinite x then .error (.domainError "`x` must be non-zero and finite.")
    else pure (x.exp-JInt.wrap .i64 1))

theorem exponent1087_proven : Exponent1087 := by unfold Exponent1087; intros; rfl

def Frexp1095 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.frexp x = (
    do
     let z ← fresh
     let state ← readContext
     let e := if iszero x then JInt.wrap .i64 0 else x.exp
     let scaled := match x.value with
       | .finite m scale => FP.finite m (scale-e.val)
       | v => v
     let z ← applyPrimitive (setPrimitive state z.prec scaled (roundingRaw state))
     return (z,e))

theorem frexp1095_proven : Frexp1095 := by unfold Frexp1095; intros; rfl

def Significand1102 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.significand x = (
    do
     let (z,_) ← frexp x
     let state ← readContext
     applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) .mul ⟨z.value,false⟩ (.ofInt 2)))

theorem significand1102_proven : Significand1102 := by unfold Significand1102; intros; rfl

def Round1121 : Prop :=
  ∀ (x : BigFloat) (r : RoundingMode),
    JuliaLean.base.mpfr.roundValue x r = (
    do
     let z ← fresh
     let mode ← liftJl (if r = .NearestTiesAway then pure Mode.nearest else toMPFR r)
     applyPrimitive (integerRoundPrimitive (← readContext) z.prec mode (r == .NearestTiesAway) x))

theorem round1121_proven : Round1121 := by unfold Round1121; intros; rfl

def Isinf1129 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.isinf x = (
    x.exp == specialInfExp)

theorem isinf1129_proven : Isinf1129 := by unfold Isinf1129; intros; rfl

def Isnan1133 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.isnan x = (
    x.exp == specialNanExp)

theorem isnan1133_proven : Isnan1133 := by unfold Isnan1133; intros; rfl

def Iszero1141 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.iszero x = (
    x.exp == specialZeroExp)

theorem iszero1141_proven : Iszero1141 := by unfold Iszero1141; intros; rfl

def Isone1142 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.isone x = (
    !isnan x && decide ((cmpSigned x (JInt.wrap .i64 1)).val = 0))

theorem isone1142_proven : Isone1142 := by unfold Isone1142; intros; rfl

def Typemax1148 : Prop :=
  ∀ (precision : Clong),
    JuliaLean.base.mpfr.typemax precision = (
    pack precision (.inf false))

theorem typemax1148_proven : Typemax1148 := by unfold Typemax1148; intros; rfl

def Typemin1149 : Prop :=
  ∀ (precision : Clong),
    JuliaLean.base.mpfr.typemin precision = (
    pack precision (.inf true))

theorem typemin1149_proven : Typemin1149 := by unfold Typemin1149; intros; rfl

def Nextfloat1151 : Prop :=
  ∀ (I : Type) (negative : I → Bool) (abs : I → I) (value : I → Int) (x : BigFloat) (n : I) (state : Context),
    JuliaLean.base.mpfr.nextfloatBang (I := I) negative abs value x n state = (
    match directionAndCount negative abs value true n with
    | none => none
    | some (.error e) => some (.error e,state)
    | some (.ok (up,count)) => some ((repeatNext count up x).run state))

theorem nextfloat1151_proven : Nextfloat1151 := by unfold Nextfloat1151; intros; rfl

def Prevfloat1159 : Prop :=
  ∀ (I : Type) (negative : I → Bool) (abs : I → I) (value : I → Int) (x : BigFloat) (n : I) (state : Context),
    JuliaLean.base.mpfr.prevfloatBang (I := I) negative abs value x n state = (
    match directionAndCount negative abs value false n with
    | none => none
    | some (.error e) => some (.error e,state)
    | some (.ok (up,count)) => some ((repeatNext count up x).run state))

theorem prevfloat1159_proven : Prevfloat1159 := by unfold Prevfloat1159; intros; rfl

def Nextfloat1167 : Prop :=
  ∀ (I : Type) (negative : I → Bool) (abs : I → I) (value : I → Int) (x : BigFloat) (n : I) (state : Context),
    JuliaLean.base.mpfr.nextfloat (I := I) negative abs value x n state = (
    if value n = 0 then some (.ok x,state) else
      let (copy,state) := (duplicate x).run state
      match copy with
      | .error e => some (.error e,state)
      | .ok x => nextfloatBang negative abs value x n state)

theorem nextfloat1167_proven : Nextfloat1167 := by unfold Nextfloat1167; intros; rfl

def Prevfloat1168 : Prop :=
  ∀ (I : Type) (negative : I → Bool) (abs : I → I) (value : I → Int) (x : BigFloat) (n : I) (state : Context),
    JuliaLean.base.mpfr.prevfloat (I := I) negative abs value x n state = (
    if value n = 0 then some (.ok x,state) else
      let (copy,state) := (duplicate x).run state
      match copy with
      | .error e => some (.error e,state)
      | .ok x => prevfloatBang negative abs value x n state)

theorem prevfloat1168_proven : Prevfloat1168 := by unfold Prevfloat1168; intros; rfl

def Eps1170 : Prop :=
  JuliaLean.base.mpfr.epsType = (
    do
     let state ← readContext
     let one ← fromLong (JInt.wrap .i64 1) (roundingRaw state) (precisionType state).val
     let next ← nextfloatOne one
     let state ← readContext
     let one ← fromLong (JInt.wrap .i64 1) (roundingRaw state) (precisionType state).val
     arithmetic .sub next one)

theorem eps1170_proven : Eps1170 := by unfold Eps1170; intros; rfl

def Floatmin1172 : Prop :=
  JuliaLean.base.mpfr.floatmin = (
    do
     let state ← readContext
     let zero ← fromLong (JInt.wrap .i64 0) (roundingRaw state) (precisionType state).val
     nextfloatOne zero)

theorem floatmin1172_proven : Floatmin1172 := by unfold Floatmin1172; intros; rfl

def Floatmax1173 : Prop :=
  JuliaLean.base.mpfr.floatmax = (
    do
     let state ← readContext
     let infinity := pack (precisionType state) (.inf false)
     prevfloatOne infinity)

theorem floatmax1173_proven : Floatmax1173 := by unfold Floatmax1173; intros; rfl

def Setprecision1214 : Prop :=
  ∀ (A : Type) (P B : Type) (convertPrecision : P → B → Jl Clong) (action : M A) (prec : P) (base : B),
    JuliaLean.base.mpfr.withPrecision (P := P) (B := B) convertPrecision action prec base = (
    do
     let converted ← liftJl (convertPrecision prec base)
     let body : M A := ⟨fun state =>
       let previous := state.scopedPrecision
       let (result,after) := action.run { state with scopedPrecision := some converted }
       (result,{ after with scopedPrecision := previous })⟩
     body)

theorem setprecision1214_proven : Setprecision1214 := by unfold Setprecision1214; intros; rfl

def Setprecision1217 : Prop :=
  ∀ (A : Type),
    JuliaLean.base.mpfr.setprecisionBottom (A := A) = (
    throw (.methodError "setprecision"))

theorem setprecision1217_proven : Setprecision1217 := by unfold Setprecision1217; intros; rfl

def Setprecision1219 : Prop :=
  ∀ (A : Type) (P B : Type) (convertPrecision : P → B → Jl Clong) (action : M A) (prec : P) (base : B),
    JuliaLean.base.mpfr.withPrecisionDefault (P := P) (B := B) convertPrecision action prec base = (
    withPrecision convertPrecision action prec base)

theorem setprecision1219_proven : Setprecision1219 := by unfold Setprecision1219; intros; rfl

def StringMpfr1221 : Prop :=
  ∀ (World Ref Ptr : Type) (ops : MPFRStringOps World Ref Ptr) (world : World) (x : BigFloat) (format : String),
    JuliaLean.base.mpfr.stringMpfr (World := World) (Ref := Ref) (Ptr := Ptr) ops world x format = (
    let (world, pc) := ops.newPointerRef world
    let (world, n) := ops.asprintf world pc format x
    let (world, pointer) := ops.readPointerRef world pc
    let world := replaceNativeComma ops world pointer 1 n.val.toNat
    let (world, text) := ops.unsafeString world pointer
    let world := ops.freeString world pointer
    (world, text))

theorem stringMpfr1221_proven : StringMpfr1221 := by unfold StringMpfr1221; intros; rfl

def Prettify1239 : Prop :=
  ∀ (s : String),
    JuliaLean.base.mpfr.prettifyBigFloat s = (
    do
     let fields := s.splitOn "e"
     let mantissa ← match fields[0]? with | some s => pure s | none => throw (.julia .boundsError)
     let expstr ← match fields[1]? with | some s => pure s | none => throw (.julia .boundsError)
     let mantissa := if mantissa.toList.contains '.' then mantissa else mantissa ++ "."
     let mantissa := String.ofList ((mantissa.toList.reverse.dropWhile (· == '0')).reverse)
     let mantissa := if mantissa.toList.getLast? == some '.' then mantissa ++ "0" else mantissa
     let expo ← match parseSignedDecimal expstr.toList with
       | none => throw (.julia (.argumentError "invalid exponent"))
       | some n =>
         if IntTy.min .i64 ≤ n ∧ n ≤ IntTy.max .i64 then pure n
         else throw (.julia (.argumentError "invalid exponent"))
     if -5 < expo ∧ expo < 6 then
       if expo = 0 then return mantissa
       let fields := mantissa.splitOn "."
       let intPart ← match fields[0]? with | some s => pure s | none => throw (.julia .boundsError)
       let frac ← match fields[1]? with | some s => pure s | none => throw (.julia .boundsError)
       if expo > 0 then
         if expo.toNat < frac.length then
           return intPart ++ String.ofList (frac.toList.take expo.toNat) ++ "." ++
             String.ofList (frac.toList.drop expo.toNat)
         else return intPart ++ frac ++ String.ofList (List.replicate (expo.toNat-frac.length) '0') ++ ".0"
       else
         let negative := intPart.toList.head? == some '-'
         let intPart := if negative then String.ofList (intPart.toList.dropWhile (· == '-')) else intPart
         if intPart.length ≠ 1 then throw .assertionError
         return (if negative then "-" else "") ++ "0." ++
           String.ofList (List.replicate (-expo-1).toNat '0') ++ intPart ++
           (if frac = "0" then "" else frac)
     return mantissa ++ "e" ++ toString expo)

theorem prettify1239_proven : Prettify1239 := by unfold Prettify1239; intros; rfl

def String1267 : Prop :=
  ∀ (World Ref Ptr : Type) (ops : MPFRStringOps World Ref Ptr) (nonfiniteString : FV .f64 → Jl String) (mode : Mode) (world : World) (x : BigFloat) (format : String),
    JuliaLean.base.mpfr.stringWithFormat (World := World) (Ref := Ref) (Ptr := Ptr) ops nonfiniteString mode world x format = (
    if !isfinite x then
      (world, (nonfiniteString (toFloat64 x mode)).mapError FormattingError.julia)
    else
      let (world, text) := stringMpfr ops world x format
      (world, prettifyBigFloat text))

theorem string1267_proven : String1267 := by unfold String1267; intros; rfl

def String1271 : Prop :=
  ∀ (World Ref Ptr : Type) (ops : MPFRStringOps World Ref Ptr) (nonfiniteString : FV .f64 → Jl String) (mode : Mode) (world : World) (x : BigFloat),
    JuliaLean.base.mpfr.stringWithDefaultFormat (World := World) (Ref := Ref) (Ptr := Ptr) ops nonfiniteString mode world x = (
    stringWithFormat ops nonfiniteString mode world x "%Re")

theorem string1271_proven : String1271 := by unfold String1271; intros; rfl

def String1272 : Prop :=
  ∀ (I World Ref Ptr : Type) (integerString : I → String) (ops : MPFRStringOps World Ref Ptr) (nonfiniteString : FV .f64 → Jl String) (mode : Mode) (world : World) (x : BigFloat) (precision : I),
    JuliaLean.base.mpfr.stringWithPrecision (I := I) (World := World) (Ref := Ref) (Ptr := Ptr) integerString ops nonfiniteString mode world x precision = (
    stringWithFormat ops nonfiniteString mode world x
      ("%." ++ integerString precision ++ "Re"))

theorem string1272_proven : String1272 := by unfold String1272; intros; rfl

def String1274 : Prop :=
  ∀ (World Ref Ptr : Type) (ops : MPFRStringOps World Ref Ptr) (nonfiniteString : FV .f64 → Jl String) (mode : Mode) (world : World) (b : BigFloat),
    JuliaLean.base.mpfr.stringBigFloat (World := World) (Ref := Ref) (Ptr := Ptr) ops nonfiniteString mode world b = (
    stringWithDefaultFormat ops nonfiniteString mode world b)

theorem string1274_proven : String1274 := by unfold String1274; intros; rfl

def Print1276 : Prop :=
  ∀ (IO : Type) (nonfiniteString : FV .f64 → Jl String) (print : IO → String → Jl IO) (io : IO) (b : BigFloat),
    JuliaLean.base.mpfr.printBigFloat (IO := IO) nonfiniteString print io b = (
    do
     (print io (← stringValue nonfiniteString b)).mapError FormattingError.julia)

theorem print1276_proven : Print1276 := by unfold Print1276; intros; rfl

def Show1277 : Prop :=
  ∀ (IO : Type) (nonfiniteString : FV .f64 → Jl String) (compact : IO → Jl Bool) (print : IO → String → Jl IO) (io : IO) (b : BigFloat),
    JuliaLean.base.mpfr.showBigFloat (IO := IO) nonfiniteString compact print io b = (
    do
     if ← (compact io).mapError FormattingError.julia then
       (print io (← stringScientific nonfiniteString b ⟨some 5⟩)).mapError FormattingError.julia
     else (print io (← stringValue nonfiniteString b)).mapError FormattingError.julia)

theorem show1277_proven : Show1277 := by unfold Show1277; intros; rfl

def SetEmax1295 : Prop :=
  ∀ (x : Clong),
    JuliaLean.base.mpfr.setEmax x = (
    do
     let state ← readContext
     if state.limits.emaxMin.val ≤ x.val ∧ x.val ≤ state.limits.emaxMax.val then
       writeContext { state with emax := x }
     else liftJl (checkExponentErr (JInt.wrap .i32 1)))

theorem setEmax1295_proven : SetEmax1295 := by unfold SetEmax1295; intros; rfl

def SetEmin1296 : Prop :=
  ∀ (x : Clong),
    JuliaLean.base.mpfr.setEmin x = (
    do
     let state ← readContext
     if state.limits.eminMin.val ≤ x.val ∧ x.val ≤ state.limits.eminMax.val then
       writeContext { state with emin := x }
     else liftJl (checkExponentErr (JInt.wrap .i32 1)))

theorem setEmin1296_proven : SetEmin1296 := by unfold SetEmin1296; intros; rfl

def Deepcopy1298 : Prop :=
  ∀ (D : Type) (getOrInsert : D → BigFloat → (Unit → M BigFloat) → M (BigFloat × D)) (x : BigFloat) (stackdict : D),
    JuliaLean.base.mpfr.deepcopyInternal (D := D) getOrInsert x stackdict = (
    getOrInsert stackdict x (fun _ => pure { x with d := x.d.map id }))

theorem deepcopy1298_proven : Deepcopy1298 := by unfold Deepcopy1298; intros; rfl

def Decompose1307 : Prop :=
  ∀ (x : BigFloat),
    JuliaLean.base.mpfr.decompose x = (
    if isnan x then (JuliaLean.base.gmp.ofInt 0,JInt.wrap .i64 0,JInt.wrap .i64 0)
    else if isinf x then (JuliaLean.base.gmp.ofInt x.sign.val,JInt.wrap .i64 0,JInt.wrap .i64 0)
    else if x.value.iszero then (JuliaLean.base.gmp.ofInt 0,JInt.wrap .i64 0,JInt.wrap .i64 x.sign.val)
    else
      let nlimbs := (x.prec.val+63).tdiv 64
      let bytes := JInt.wrap .i64 (nlimbs*8)
      let s := JuliaLean.base.gmp.ofInt (JuliaLean.base.gmp.limbMagnitude (x.d.take nlimbs.toNat))
      (s,x.exp-JInt.wrap .i64 (8*bytes.val),JInt.wrap .i64 x.sign.val))

theorem decompose1307_proven : Decompose1307 := by unfold Decompose1307; intros; rfl

def ClearFlags1326 : Prop :=
  JuliaLean.base.mpfr.clearFlags = (
    do
     let state ← readContext
     writeContext { state with flags := {} })

theorem clearFlags1326_proven : ClearFlags1326 := by unfold ClearFlags1326; intros; rfl

def HadUnderflow1327 : Prop :=
  ∀ (state : Context),
    JuliaLean.base.mpfr.hadUnderflow state = (
    state.flags.underflow)

theorem hadUnderflow1327_proven : HadUnderflow1327 := by unfold HadUnderflow1327; intros; rfl

def HadOverflow1328 : Prop :=
  ∀ (state : Context),
    JuliaLean.base.mpfr.hadOverflow state = (
    state.flags.overflow)

theorem hadOverflow1328_proven : HadOverflow1328 := by unfold HadOverflow1328; intros; rfl

def HadDivzero1329 : Prop :=
  ∀ (state : Context),
    JuliaLean.base.mpfr.hadDivbyzero state = (
    state.flags.divbyzero)

theorem hadDivzero1329_proven : HadDivzero1329 := by unfold HadDivzero1329; intros; rfl

def HadNan1330 : Prop :=
  ∀ (state : Context),
    JuliaLean.base.mpfr.hadNan state = (
    state.flags.nan)

theorem hadNan1330_proven : HadNan1330 := by unfold HadNan1330; intros; rfl

def HadInexact1331 : Prop :=
  ∀ (state : Context),
    JuliaLean.base.mpfr.hadInexact state = (
    state.flags.inexact)

theorem hadInexact1331_proven : HadInexact1331 := by unfold HadInexact1331; intros; rfl

def HadRange1332 : Prop :=
  ∀ (state : Context),
    JuliaLean.base.mpfr.hadRange state = (
    state.flags.range)

theorem hadRange1332_proven : HadRange1332 := by unfold HadRange1332; intros; rfl

theorem init47_proven : Init47 := by
  intro showError state
  dsimp [initModule, tryCatch, tryCatchThe, MonadExceptOf.tryCatch]
  cases ((do
    setEmin (getEminMin (← readContext))
    setEmax (getEmaxMax (← readContext))).run state).1 <;> rfl

theorem toIeee494_proven : ToIeee494 := by
  intro T x mode
  dsimp only
  let v := toIEEE T x mode
  change v.isfinite = true ∨ v.isinf = true ∨ v.isnan = true
  unfold JuliaLean.Promotion.Fl.isfinite JuliaLean.Promotion.Fl.isinf JuliaLean.Promotion.Fl.isnan
  by_cases he : v.expField = T.fmt.emax <;> by_cases hf : v.frac = 0 <;> simp [he, hf]

theorem reverse589_proven : Reverse589 := by
  intro t operation scalar x h
  unfold integerArithmetic
  simp [h]

theorem reverse597_proven : Reverse597 := by
  exact reverse589_proven

theorem reverse605_proven : Reverse605 := by
  intro T operation scalar x h
  unfold ieeeArithmetic
  simp [h]


end LegacyRetired

open JuliaLean.Registry

def entriesLegacyRetired : List Entry := [
  { id := "bignumscov-mpfr-44", juliaFile := "base/mpfr.jl"
    juliaFns := ["version()"]
    statement := "version() applies the VersionNumber parser to the MPFR library version string."
    source := "base/mpfr.jl:44-44", status := .proven
    prop := ``LegacyRetired.Version44, thm := some ``LegacyRetired.version44_proven },
  { id := "bignumscov-mpfr-45", juliaFile := "base/mpfr.jl"
    juliaFns := ["patches()"]
    statement := "patches() splits the MPFR library patch-name string on spaces and returns the resulting names."
    source := "base/mpfr.jl:45-45", status := .proven
    prop := ``LegacyRetired.Patches45, thm := some ``LegacyRetired.patches45_proven },
  { id := "bignumscov-mpfr-47", juliaFile := "base/mpfr.jl"
    juliaFns := ["__init__()"]
    statement := "The __init__ method at base/mpfr.jl:47-56 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:47-56", status := .proven
    prop := ``LegacyRetired.Init47, thm := some ``LegacyRetired.init47_proven 
    notes := "Retired JuliaLean.BigNumsCov.MpfrFaithful.init47_proven at a2fd59b64fda5264fda1337c1534d56a17b98872; The installed exponent setters and error handler are effectful Context operations; the old pure callback proof does not establish their result contract." },
  { id := "bignumscov-mpfr-75", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Nearest})"]
    statement := "The convert method at base/mpfr.jl:75-75 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:75-75", status := .proven
    prop := ``LegacyRetired.Convert75, thm := some ``LegacyRetired.convert75_proven },
  { id := "bignumscov-mpfr-76", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:ToZero})"]
    statement := "The convert method at base/mpfr.jl:76-76 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:76-76", status := .proven
    prop := ``LegacyRetired.Convert76, thm := some ``LegacyRetired.convert76_proven },
  { id := "bignumscov-mpfr-77", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Up})"]
    statement := "The convert method at base/mpfr.jl:77-77 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:77-77", status := .proven
    prop := ``LegacyRetired.Convert77, thm := some ``LegacyRetired.convert77_proven },
  { id := "bignumscov-mpfr-78", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:Down})"]
    statement := "The convert method at base/mpfr.jl:78-78 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:78-78", status := .proven
    prop := ``LegacyRetired.Convert78, thm := some ``LegacyRetired.convert78_proven },
  { id := "bignumscov-mpfr-79", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{MPFRRoundingMode}, ::RoundingMode{:FromZero})"]
    statement := "The convert method at base/mpfr.jl:79-79 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:79-79", status := .proven
    prop := ``LegacyRetired.Convert79, thm := some ``LegacyRetired.convert79_proven },
  { id := "bignumscov-mpfr-81", juliaFile := "base/mpfr.jl"
    juliaFns := ["convert(::Type{RoundingMode}, r::MPFRRoundingMode)"]
    statement := "The convert method at base/mpfr.jl:81-95 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:81-95", status := .proven
    prop := ``LegacyRetired.Convert81, thm := some ``LegacyRetired.convert81_proven },
  { id := "bignumscov-mpfr-110", juliaFile := "base/mpfr.jl"
    juliaFns := ["tie_breaker_is_to_even(::MPFRRoundingMode)"]
    statement := "The tie_breaker_is_to_even method at base/mpfr.jl:110-110 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:110-110", status := .proven
    prop := ``LegacyRetired.TieBreaker110, thm := some ``LegacyRetired.tieBreaker110_proven },
  { id := "bignumscov-mpfr-154", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:154-171 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:154-171", status := .proven
    prop := ``LegacyRetired.BigFloat154, thm := some ``LegacyRetired.bigFloat154_proven },
  { id := "bignumscov-mpfr-183", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.getproperty(x::BigFloat, s::Symbol)"]
    statement := "The Base.getproperty method at base/mpfr.jl:183-197 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:183-197", status := .proven
    prop := ``LegacyRetired.Getproperty183, thm := some ``LegacyRetired.getproperty183_proven },
  { id := "bignumscov-mpfr-201", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.setproperty!(x::BigFloat, s::Symbol, v)"]
    statement := "The Base.setproperty! method at base/mpfr.jl:201-211 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:201-211", status := .proven
    prop := ``LegacyRetired.Setproperty201, thm := some ``LegacyRetired.setproperty201_proven },
  { id := "bignumscov-mpfr-214", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ref{BigFloat}}, x::Ptr{BigFloat})"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:214-214 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:214-214", status := .proven
    prop := ``LegacyRetired.UnsafeConvert214, thm := some ``LegacyRetired.unsafeConvert214_proven },
  { id := "bignumscov-mpfr-215", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ref{BigFloat}}, x::Ref{BigFloat})"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:215-215 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:215-215", status := .proven
    prop := ``LegacyRetired.UnsafeConvert215, thm := some ``LegacyRetired.unsafeConvert215_proven },
  { id := "bignumscov-mpfr-216", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.cconvert(::Type{Ref{BigFloat}}, x::BigFloat)"]
    statement := "The Base.cconvert method at base/mpfr.jl:216-216 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:216-216", status := .proven
    prop := ``LegacyRetired.Cconvert216, thm := some ``LegacyRetired.cconvert216_proven },
  { id := "bignumscov-mpfr-217", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.cconvert(::Type{Ref{BigFloat}}, x::Number)"]
    statement := "The Base.cconvert method at base/mpfr.jl:217-217 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:217-217", status := .proven
    prop := ``LegacyRetired.Cconvert217, thm := some ``LegacyRetired.cconvert217_proven },
  { id := "bignumscov-mpfr-218", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.cconvert(::Type{Ref{BigFloat}}, x::Ref{BigFloat})"]
    statement := "The Base.cconvert method at base/mpfr.jl:218-218 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:218-218", status := .proven
    prop := ``LegacyRetired.Cconvert218, thm := some ``LegacyRetired.cconvert218_proven },
  { id := "bignumscov-mpfr-219", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ref{BigFloat}}, x::BigFloatData)"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:219-228 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:219-228", status := .proven
    prop := ``LegacyRetired.UnsafeConvert219, thm := some ``LegacyRetired.unsafeConvert219_proven },
  { id := "bignumscov-mpfr-229", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.unsafe_convert(::Type{Ptr{Limb}}, fd::BigFloatData)"]
    statement := "The Base.unsafe_convert method at base/mpfr.jl:229-229 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:229-229", status := .proven
    prop := ``LegacyRetired.UnsafeConvert229, thm := some ``LegacyRetired.unsafeConvert229_proven },
  { id := "bignumscov-mpfr-230", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.setindex!(fd::BigFloatData, v, i)"]
    statement := "The Base.setindex! method at base/mpfr.jl:230-235 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:230-235", status := .proven
    prop := ``LegacyRetired.Setindex230, thm := some ``LegacyRetired.setindex230_proven },
  { id := "bignumscov-mpfr-236", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.getindex(fd::BigFloatData, i)"]
    statement := "The Base.getindex method at base/mpfr.jl:236-240 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:236-240", status := .proven
    prop := ``LegacyRetired.Getindex236, thm := some ``LegacyRetired.getindex236_proven },
  { id := "bignumscov-mpfr-241", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.length(fd::BigFloatData)"]
    statement := "The Base.length method at base/mpfr.jl:241-241 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:241-241", status := .proven
    prop := ``LegacyRetired.Length241, thm := some ``LegacyRetired.length241_proven },
  { id := "bignumscov-mpfr-242", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.copyto!(fd::BigFloatData, limbs)"]
    statement := "The Base.copyto! method at base/mpfr.jl:242-242 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:242-242", status := .proven
    prop := ``LegacyRetired.Copyto242, thm := some ``LegacyRetired.copyto242_proven },
  { id := "bignumscov-mpfr-247", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding_raw(::Type{BigFloat}, r::MPFRRoundingMode)"]
    statement := "The setrounding_raw method at base/mpfr.jl:247-247 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:247-247", status := .proven
    prop := ``LegacyRetired.SetroundingRaw247, thm := some ``LegacyRetired.setroundingRaw247_proven },
  { id := "bignumscov-mpfr-248", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding_raw(f::Function, ::Type{BigFloat}, r::MPFRRoundingMode)"]
    statement := "The setrounding_raw method at base/mpfr.jl:248-250 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:248-250", status := .proven
    prop := ``LegacyRetired.SetroundingRaw248, thm := some ``LegacyRetired.setroundingRaw248_proven },
  { id := "bignumscov-mpfr-252", juliaFile := "base/mpfr.jl"
    juliaFns := ["rounding(::Type{BigFloat})"]
    statement := "The rounding method at base/mpfr.jl:252-252 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:252-252", status := .proven
    prop := ``LegacyRetired.Rounding252, thm := some ``LegacyRetired.rounding252_proven },
  { id := "bignumscov-mpfr-253", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding(::Type{BigFloat}, r::RoundingMode)"]
    statement := "The setrounding method at base/mpfr.jl:253-253 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:253-253", status := .proven
    prop := ``LegacyRetired.Setrounding253, thm := some ``LegacyRetired.setrounding253_proven },
  { id := "bignumscov-mpfr-254", juliaFile := "base/mpfr.jl"
    juliaFns := ["setrounding(f::Function, ::Type{BigFloat}, r::RoundingMode)"]
    statement := "The setrounding method at base/mpfr.jl:254-255 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:254-255", status := .proven
    prop := ``LegacyRetired.Setrounding254, thm := some ``LegacyRetired.setrounding254_proven },
  { id := "bignumscov-mpfr-299", juliaFile := "base/mpfr.jl"
    juliaFns := ["widen(::Type{Float64})"]
    statement := "The widen method at base/mpfr.jl:299-299 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:299-299", status := .proven
    prop := ``LegacyRetired.Widen299, thm := some ``LegacyRetired.widen299_proven },
  { id := "bignumscov-mpfr-300", juliaFile := "base/mpfr.jl"
    juliaFns := ["widen(::Type{BigFloat})"]
    statement := "The widen method at base/mpfr.jl:300-300 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:300-300", status := .proven
    prop := ``LegacyRetired.Widen300, thm := some ``LegacyRetired.widen300_proven },
  { id := "bignumscov-mpfr-302", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:302-311 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:302-311", status := .proven
    prop := ``LegacyRetired.BigFloat302, thm := some ``LegacyRetired.bigFloat302_proven },
  { id := "bignumscov-mpfr-313", juliaFile := "base/mpfr.jl"
    juliaFns := ["_duplicate(x::BigFloat)"]
    statement := "The _duplicate method at base/mpfr.jl:313-317 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:313-317", status := .proven
    prop := ``LegacyRetired.Duplicate313, thm := some ``LegacyRetired.duplicate313_proven },
  { id := "bignumscov-mpfr-322", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::($fC), r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:322-326 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:322-326", status := .proven
    prop := ``LegacyRetired.BigFloat322, thm := some ``LegacyRetired.bigFloat322_proven },
  { id := "bignumscov-mpfr-330", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Float64, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:330-372 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:330-372", status := .proven
    prop := ``LegacyRetired.BigFloat330, thm := some ``LegacyRetired.bigFloat330_proven },
  { id := "bignumscov-mpfr-374", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::BigInt, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:374-378 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:374-378", status := .proven
    prop := ``LegacyRetired.BigFloat374, thm := some ``LegacyRetired.bigFloat374_proven },
  { id := "bignumscov-mpfr-380", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Integer; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:380-381 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:380-381", status := .proven
    prop := ``LegacyRetired.BigFloat380, thm := some ``LegacyRetired.bigFloat380_proven },
  { id := "bignumscov-mpfr-382", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Integer, r::MPFRRoundingMode; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:382-383 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:382-383", status := .proven
    prop := ``LegacyRetired.BigFloat382, thm := some ``LegacyRetired.bigFloat382_proven },
  { id := "bignumscov-mpfr-385", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Union{Bool,Int8,Int16,Int32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:385-386 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:385-386", status := .proven
    prop := ``LegacyRetired.BigFloat385, thm := some ``LegacyRetired.bigFloat385_proven },
  { id := "bignumscov-mpfr-387", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Union{UInt8,UInt16,UInt32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:387-388 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:387-388", status := .proven
    prop := ``LegacyRetired.BigFloat387, thm := some ``LegacyRetired.bigFloat387_proven },
  { id := "bignumscov-mpfr-390", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Union{Float16,Float32}, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:390-391 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:390-391", status := .proven
    prop := ``LegacyRetired.BigFloat390, thm := some ``LegacyRetired.bigFloat390_proven },
  { id := "bignumscov-mpfr-393", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Rational, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:393-400 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:393-400", status := .proven
    prop := ``LegacyRetired.BigFloat393, thm := some ``LegacyRetired.bigFloat393_proven },
  { id := "bignumscov-mpfr-401", juliaFile := "base/mpfr.jl"
    juliaFns := ["_opposite_round(r::MPFRRoundingMode)"]
    statement := "The _opposite_round method at base/mpfr.jl:401-405 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:401-405", status := .proven
    prop := ``LegacyRetired.Opposite401, thm := some ``LegacyRetired.opposite401_proven },
  { id := "bignumscov-mpfr-407", juliaFile := "base/mpfr.jl"
    juliaFns := ["tryparse(::Type{BigFloat}, s::AbstractString; base::Integer=0, precision::Integer=_precision_with_base_2(BigFloat), rounding::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The tryparse method at base/mpfr.jl:407-412 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:407-412", status := .proven
    prop := ``LegacyRetired.Tryparse407, thm := some ``LegacyRetired.tryparse407_proven },
  { id := "bignumscov-mpfr-414", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::AbstractString, r::MPFRRoundingMode=rounding_raw(BigFloat); precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:414-415 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:414-415", status := .proven
    prop := ``LegacyRetired.BigFloat414, thm := some ``LegacyRetired.bigFloat414_proven },
  { id := "bignumscov-mpfr-417", juliaFile := "base/mpfr.jl"
    juliaFns := ["Rational(x::BigFloat)"]
    statement := "The Rational method at base/mpfr.jl:417-417 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:417-417", status := .proven
    prop := ``LegacyRetired.Rational417, thm := some ``LegacyRetired.rational417_proven },
  { id := "bignumscov-mpfr-418", juliaFile := "base/mpfr.jl"
    juliaFns := ["AbstractFloat(x::BigInt)"]
    statement := "The AbstractFloat method at base/mpfr.jl:418-418 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:418-418", status := .proven
    prop := ``LegacyRetired.AbstractFloat418, thm := some ``LegacyRetired.abstractFloat418_proven },
  { id := "bignumscov-mpfr-420", juliaFile := "base/mpfr.jl"
    juliaFns := ["float(::Type{BigInt})"]
    statement := "The float method at base/mpfr.jl:420-420 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:420-420", status := .proven
    prop := ``LegacyRetired.Float420, thm := some ``LegacyRetired.float420_proven },
  { id := "bignumscov-mpfr-422", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::Real, r::RoundingMode; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:422-423 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:422-423", status := .proven
    prop := ``LegacyRetired.BigFloat422, thm := some ``LegacyRetired.bigFloat422_proven },
  { id := "bignumscov-mpfr-424", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigFloat(x::AbstractString, r::RoundingMode; precision::Integer=_precision_with_base_2(BigFloat))"]
    statement := "The BigFloat method at base/mpfr.jl:424-425 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:424-425", status := .proven
    prop := ``LegacyRetired.BigFloat424, thm := some ``LegacyRetired.bigFloat424_proven },
  { id := "bignumscov-mpfr-428", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(T, x::BigFloat, r::RoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:428-428 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:428-428", status := .proven
    prop := ``LegacyRetired.Unchecked428, thm := some ``LegacyRetired.unchecked428_proven },
  { id := "bignumscov-mpfr-430", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{Int64}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:430-432 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:430-432", status := .proven
    prop := ``LegacyRetired.Unchecked430, thm := some ``LegacyRetired.unchecked430_proven },
  { id := "bignumscov-mpfr-434", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{UInt64}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:434-436 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:434-436", status := .proven
    prop := ``LegacyRetired.Unchecked434, thm := some ``LegacyRetired.unchecked434_proven },
  { id := "bignumscov-mpfr-438", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{BigInt}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The _unchecked_cast method at base/mpfr.jl:438-442 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:438-442", status := .proven
    prop := ``LegacyRetired.Unchecked438, thm := some ``LegacyRetired.unchecked438_proven },
  { id := "bignumscov-mpfr-444", juliaFile := "base/mpfr.jl"
    juliaFns := ["_unchecked_cast(::Type{T}, x::BigFloat, r::MPFRRoundingMode) where T<:Union{Signed, Unsigned}"]
    statement := "The _unchecked_cast method at base/mpfr.jl:444-447 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:444-447", status := .proven
    prop := ``LegacyRetired.Unchecked444, thm := some ``LegacyRetired.unchecked444_proven },
  { id := "bignumscov-mpfr-449", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{T}, x::BigFloat, r::Union{RoundingMode, MPFRRoundingMode}) where T<:Union{Signed, Unsigned}"]
    statement := "The round method at base/mpfr.jl:449-456 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:449-456", status := .proven
    prop := ``LegacyRetired.Round449, thm := some ``LegacyRetired.round449_proven },
  { id := "bignumscov-mpfr-458", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{BigInt}, x::BigFloat, r::Union{RoundingMode, MPFRRoundingMode})"]
    statement := "The round method at base/mpfr.jl:458-463 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:458-463", status := .proven
    prop := ``LegacyRetired.Round458, thm := some ``LegacyRetired.round458_proven },
  { id := "bignumscov-mpfr-465", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{T}, x::BigFloat, r::RoundingMode) where T<:Union{Signed, Unsigned}"]
    statement := "The round method at base/mpfr.jl:465-466 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:465-466", status := .proven
    prop := ``LegacyRetired.Invoke465, thm := some ``LegacyRetired.invoke465_proven },
  { id := "bignumscov-mpfr-467", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{BigInt}, x::BigFloat, r::RoundingMode)"]
    statement := "The round method at base/mpfr.jl:467-468 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:467-468", status := .proven
    prop := ``LegacyRetired.Invoke467, thm := some ``LegacyRetired.invoke467_proven },
  { id := "bignumscov-mpfr-471", juliaFile := "base/mpfr.jl"
    juliaFns := ["unsafe_trunc(::Type{T}, x::BigFloat) where {T<:Integer}"]
    statement := "The unsafe_trunc method at base/mpfr.jl:471-471 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:471-471", status := .proven
    prop := ``LegacyRetired.Unsafe471, thm := some ``LegacyRetired.unsafe471_proven },
  { id := "bignumscov-mpfr-472", juliaFile := "base/mpfr.jl"
    juliaFns := ["unsafe_trunc(::Type{BigInt}, x::BigFloat)"]
    statement := "The unsafe_trunc method at base/mpfr.jl:472-472 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:472-472", status := .proven
    prop := ``LegacyRetired.Unsafe472, thm := some ``LegacyRetired.unsafe472_proven },
  { id := "bignumscov-mpfr-474", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{T}, x::BigFloat) where T<:Integer"]
    statement := "The round method at base/mpfr.jl:474-474 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:474-474", status := .proven
    prop := ``LegacyRetired.Round474, thm := some ``LegacyRetired.round474_proven },
  { id := "bignumscov-mpfr-476", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{Integer}, x::BigFloat, r::RoundingMode)"]
    statement := "The round method at base/mpfr.jl:476-476 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:476-476", status := .proven
    prop := ``LegacyRetired.Round476, thm := some ``LegacyRetired.round476_proven },
  { id := "bignumscov-mpfr-477", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(::Type{Integer}, x::BigFloat, r::MPFRRoundingMode)"]
    statement := "The round method at base/mpfr.jl:477-477 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:477-477", status := .proven
    prop := ``LegacyRetired.Round477, thm := some ``LegacyRetired.round477_proven },
  { id := "bignumscov-mpfr-479", juliaFile := "base/mpfr.jl"
    juliaFns := ["Bool(x::BigFloat)"]
    statement := "The Bool method at base/mpfr.jl:479-483 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:479-483", status := .proven
    prop := ``LegacyRetired.Bool479, thm := some ``LegacyRetired.bool479_proven },
  { id := "bignumscov-mpfr-484", juliaFile := "base/mpfr.jl"
    juliaFns := ["BigInt(x::BigFloat)"]
    statement := "The BigInt method at base/mpfr.jl:484-487 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:484-487", status := .proven
    prop := ``LegacyRetired.BigInt484, thm := some ``LegacyRetired.bigInt484_proven },
  { id := "bignumscov-mpfr-489", juliaFile := "base/mpfr.jl"
    juliaFns := ["(::Type{T})(x::BigFloat) where T<:Integer"]
    statement := "The (::Type{T}) method at base/mpfr.jl:489-492 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:489-492", status := .proven
    prop := ``LegacyRetired.Convert489, thm := some ``LegacyRetired.convert489_proven },
  { id := "bignumscov-mpfr-494", juliaFile := "base/mpfr.jl"
    juliaFns := ["to_ieee754(::Type{T}, x::BigFloat, rm) where {T<:AbstractFloat}"]
    statement := "The to_ieee754 method at base/mpfr.jl:494-548 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:494-548", status := .proven
    prop := ``LegacyRetired.ToIeee494, thm := some ``LegacyRetired.toIeee494_proven 
    notes := "Retired JuliaLean.BigNumsCov.MpfrFaithful.toIeee494_proven at a2fd59b64fda5264fda1337c1534d56a17b98872; The old five-way result tag must be related to the installed IEEE bit-pattern classification." },
  { id := "bignumscov-mpfr-550", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float16(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The Float16 method at base/mpfr.jl:550-550 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:550-550", status := .proven
    prop := ``LegacyRetired.Float550, thm := some ``LegacyRetired.float550_proven },
  { id := "bignumscov-mpfr-551", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float32(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The Float32 method at base/mpfr.jl:551-551 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:551-551", status := .proven
    prop := ``LegacyRetired.Float551, thm := some ``LegacyRetired.float551_proven },
  { id := "bignumscov-mpfr-552", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float64(x::BigFloat, r::MPFRRoundingMode=rounding_raw(BigFloat))"]
    statement := "The Float64 method at base/mpfr.jl:552-552 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:552-552", status := .proven
    prop := ``LegacyRetired.Float552, thm := some ``LegacyRetired.float552_proven },
  { id := "bignumscov-mpfr-553", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float16(x::BigFloat, r::RoundingMode)"]
    statement := "The Float16 method at base/mpfr.jl:553-553 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:553-553", status := .proven
    prop := ``LegacyRetired.Float553, thm := some ``LegacyRetired.float553_proven },
  { id := "bignumscov-mpfr-554", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float32(x::BigFloat, r::RoundingMode)"]
    statement := "The Float32 method at base/mpfr.jl:554-554 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:554-554", status := .proven
    prop := ``LegacyRetired.Float554, thm := some ``LegacyRetired.float554_proven },
  { id := "bignumscov-mpfr-555", juliaFile := "base/mpfr.jl"
    juliaFns := ["Float64(x::BigFloat, r::RoundingMode)"]
    statement := "The Float64 method at base/mpfr.jl:555-555 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:555-555", status := .proven
    prop := ``LegacyRetired.Float555, thm := some ``LegacyRetired.float555_proven },
  { id := "bignumscov-mpfr-557", juliaFile := "base/mpfr.jl"
    juliaFns := ["promote_rule(::Type{BigFloat}, ::Type{<:Real})"]
    statement := "The promote_rule method at base/mpfr.jl:557-557 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:557-557", status := .proven
    prop := ``LegacyRetired.Promote557, thm := some ``LegacyRetired.promote557_proven },
  { id := "bignumscov-mpfr-558", juliaFile := "base/mpfr.jl"
    juliaFns := ["promote_rule(::Type{BigInt}, ::Type{<:AbstractFloat})"]
    statement := "The promote_rule method at base/mpfr.jl:558-558 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:558-558", status := .proven
    prop := ``LegacyRetired.Promote558, thm := some ``LegacyRetired.promote558_proven },
  { id := "bignumscov-mpfr-559", juliaFile := "base/mpfr.jl"
    juliaFns := ["promote_rule(::Type{BigFloat}, ::Type{<:AbstractFloat})"]
    statement := "The promote_rule method at base/mpfr.jl:559-559 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:559-559", status := .proven
    prop := ``LegacyRetired.Promote559, thm := some ``LegacyRetired.promote559_proven },
  { id := "bignumscov-mpfr-561", juliaFile := "base/mpfr.jl"
    juliaFns := ["big(::Type{<:AbstractFloat})"]
    statement := "The big method at base/mpfr.jl:561-561 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:561-561", status := .proven
    prop := ``LegacyRetired.Big561, thm := some ``LegacyRetired.big561_proven },
  { id := "bignumscov-mpfr-563", juliaFile := "base/mpfr.jl"
    juliaFns := ["big(x::AbstractFloat)"]
    statement := "The big method at base/mpfr.jl:563-563 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:563-563", status := .proven
    prop := ``LegacyRetired.Big563, thm := some ``LegacyRetired.big563_proven },
  { id := "bignumscov-mpfr-565", juliaFile := "base/mpfr.jl"
    juliaFns := ["Rational{BigInt}(x::AbstractFloat)"]
    statement := "The Rational{BigInt} method at base/mpfr.jl:565-571 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:565-571", status := .proven
    prop := ``LegacyRetired.Rational565, thm := some ``LegacyRetired.rational565_proven },
  { id := "bignumscov-mpfr-589", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::CulongMax, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:589-589 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:589-589", status := .proven
    prop := ``LegacyRetired.Reverse589, thm := some ``LegacyRetired.reverse589_proven 
    notes := "Retired JuliaLean.BigNumsCov.MpfrFaithful.reverse589_proven at a2fd59b64fda5264fda1337c1534d56a17b98872; The old arbitrary callback reversal needs commutativity of the installed exact arithmetic and rounding kernels." },
  { id := "bignumscov-mpfr-597", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::ClongMax, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:597-597 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:597-597", status := .proven
    prop := ``LegacyRetired.Reverse597, thm := some ``LegacyRetired.reverse597_proven 
    notes := "Retired JuliaLean.BigNumsCov.MpfrFaithful.reverse597_proven at a2fd59b64fda5264fda1337c1534d56a17b98872; The old arbitrary callback reversal needs commutativity of the installed exact arithmetic and rounding kernels." },
  { id := "bignumscov-mpfr-605", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::CdoubleMax, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:605-605 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:605-605", status := .proven
    prop := ``LegacyRetired.Reverse605, thm := some ``LegacyRetired.reverse605_proven 
    notes := "Retired JuliaLean.BigNumsCov.MpfrFaithful.reverse605_proven at a2fd59b64fda5264fda1337c1534d56a17b98872; The old arbitrary callback reversal needs commutativity of the installed IEEE conversion, arithmetic and rounding kernels." },
  { id := "bignumscov-mpfr-613", juliaFile := "base/mpfr.jl"
    juliaFns := ["($fJ)(c::BigInt, x::BigFloat)"]
    statement := "The $fJ method at base/mpfr.jl:613-613 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:613-613", status := .proven
    prop := ``LegacyRetired.Reverse613, thm := some ``LegacyRetired.reverse613_proven },
  { id := "bignumscov-mpfr-678", juliaFile := "base/mpfr.jl"
    juliaFns := ["inv(x::BigFloat)"]
    statement := "The inv method at base/mpfr.jl:678-678 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:678-678", status := .proven
    prop := ``LegacyRetired.Inv678, thm := some ``LegacyRetired.inv678_proven },
  { id := "bignumscov-mpfr-686", juliaFile := "base/mpfr.jl"
    juliaFns := ["muladd(x::BigFloat, y::BigFloat, z::BigFloat)"]
    statement := "The muladd method at base/mpfr.jl:686-686 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:686-686", status := .proven
    prop := ``LegacyRetired.Muladd686, thm := some ``LegacyRetired.muladd686_proven },
  { id := "bignumscov-mpfr-690", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, y::BigFloat)"]
    statement := "The div method at base/mpfr.jl:690-695 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:690-695", status := .proven
    prop := ``LegacyRetired.Div690, thm := some ``LegacyRetired.div690_proven },
  { id := "bignumscov-mpfr-698", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::CulongMax)"]
    statement := "The div method at base/mpfr.jl:698-703 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:698-703", status := .proven
    prop := ``LegacyRetired.Div698, thm := some ``LegacyRetired.div698_proven },
  { id := "bignumscov-mpfr-704", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(c::CulongMax, x::BigFloat)"]
    statement := "The div method at base/mpfr.jl:704-709 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:704-709", status := .proven
    prop := ``LegacyRetired.Div704, thm := some ``LegacyRetired.div704_proven },
  { id := "bignumscov-mpfr-712", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::ClongMax)"]
    statement := "The div method at base/mpfr.jl:712-717 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:712-717", status := .proven
    prop := ``LegacyRetired.Div712, thm := some ``LegacyRetired.div712_proven },
  { id := "bignumscov-mpfr-718", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(c::ClongMax, x::BigFloat)"]
    statement := "The div method at base/mpfr.jl:718-723 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:718-723", status := .proven
    prop := ``LegacyRetired.Div718, thm := some ``LegacyRetired.div718_proven },
  { id := "bignumscov-mpfr-726", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::CdoubleMax)"]
    statement := "The div method at base/mpfr.jl:726-731 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:726-731", status := .proven
    prop := ``LegacyRetired.Div726, thm := some ``LegacyRetired.div726_proven },
  { id := "bignumscov-mpfr-732", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(c::CdoubleMax, x::BigFloat)"]
    statement := "The div method at base/mpfr.jl:732-737 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:732-737", status := .proven
    prop := ``LegacyRetired.Div732, thm := some ``LegacyRetired.div732_proven },
  { id := "bignumscov-mpfr-740", juliaFile := "base/mpfr.jl"
    juliaFns := ["div(x::BigFloat, c::BigInt)"]
    statement := "The div method at base/mpfr.jl:740-745 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:740-745", status := .proven
    prop := ``LegacyRetired.Div740, thm := some ``LegacyRetired.div740_proven },
  { id := "bignumscov-mpfr-781", juliaFile := "base/mpfr.jl"
    juliaFns := ["sqrt(x::BigFloat)"]
    statement := "The sqrt method at base/mpfr.jl:781-787 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:781-787", status := .proven
    prop := ``LegacyRetired.Sqrt781, thm := some ``LegacyRetired.sqrt781_proven },
  { id := "bignumscov-mpfr-789", juliaFile := "base/mpfr.jl"
    juliaFns := ["sqrt(x::BigInt)"]
    statement := "The sqrt method at base/mpfr.jl:789-789 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:789-789", status := .proven
    prop := ``LegacyRetired.Sqrt789, thm := some ``LegacyRetired.sqrt789_proven },
  { id := "bignumscov-mpfr-815", juliaFile := "base/mpfr.jl"
    juliaFns := ["^(x::BigFloat, y::Integer)"]
    statement := "The ^ method at base/mpfr.jl:815-815 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:815-815", status := .proven
    prop := ``LegacyRetired.Power815, thm := some ``LegacyRetired.power815_proven },
  { id := "bignumscov-mpfr-816", juliaFile := "base/mpfr.jl"
    juliaFns := ["^(x::BigFloat, y::Unsigned)"]
    statement := "The ^ method at base/mpfr.jl:816-816 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:816-816", status := .proven
    prop := ``LegacyRetired.Power816, thm := some ``LegacyRetired.power816_proven },
  { id := "bignumscov-mpfr-826", juliaFile := "base/mpfr.jl"
    juliaFns := ["sincos_fast(v::BigFloat)"]
    statement := "The sincos_fast method at base/mpfr.jl:826-831 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:826-831", status := .proven
    prop := ``LegacyRetired.SincosFast826, thm := some ``LegacyRetired.sincosFast826_proven },
  { id := "bignumscov-mpfr-832", juliaFile := "base/mpfr.jl"
    juliaFns := ["sincos(v::BigFloat)"]
    statement := "The sincos method at base/mpfr.jl:832-832 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:832-832", status := .proven
    prop := ``LegacyRetired.Sincos832, thm := some ``LegacyRetired.sincos832_proven },
  { id := "bignumscov-mpfr-835", juliaFile := "base/mpfr.jl"
    juliaFns := ["big_ln2()"]
    statement := "The big_ln2 method at base/mpfr.jl:835-839 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:835-839", status := .proven
    prop := ``LegacyRetired.BigLn2835, thm := some ``LegacyRetired.bigLn2835_proven },
  { id := "bignumscov-mpfr-841", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::Clong)"]
    statement := "The ldexp method at base/mpfr.jl:841-845 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:841-845", status := .proven
    prop := ``LegacyRetired.Ldexp841, thm := some ``LegacyRetired.ldexp841_proven },
  { id := "bignumscov-mpfr-846", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::Culong)"]
    statement := "The ldexp method at base/mpfr.jl:846-850 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:846-850", status := .proven
    prop := ``LegacyRetired.Ldexp846, thm := some ``LegacyRetired.ldexp846_proven },
  { id := "bignumscov-mpfr-851", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::ClongMax)"]
    statement := "The ldexp method at base/mpfr.jl:851-851 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:851-851", status := .proven
    prop := ``LegacyRetired.Ldexp851, thm := some ``LegacyRetired.ldexp851_proven },
  { id := "bignumscov-mpfr-852", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::CulongMax)"]
    statement := "The ldexp method at base/mpfr.jl:852-852 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:852-852", status := .proven
    prop := ``LegacyRetired.Ldexp852, thm := some ``LegacyRetired.ldexp852_proven },
  { id := "bignumscov-mpfr-853", juliaFile := "base/mpfr.jl"
    juliaFns := ["ldexp(x::BigFloat, n::Integer)"]
    statement := "The ldexp method at base/mpfr.jl:853-853 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:853-853", status := .proven
    prop := ``LegacyRetired.Ldexp853, thm := some ``LegacyRetired.ldexp853_proven },
  { id := "bignumscov-mpfr-855", juliaFile := "base/mpfr.jl"
    juliaFns := ["factorial(x::BigFloat)"]
    statement := "The factorial method at base/mpfr.jl:855-863 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:855-863", status := .proven
    prop := ``LegacyRetired.Factorial855, thm := some ``LegacyRetired.factorial855_proven },
  { id := "bignumscov-mpfr-872", juliaFile := "base/mpfr.jl"
    juliaFns := ["$f(x::BigFloat)"]
    statement := "The $f method at base/mpfr.jl:872-881 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:872-881", status := .proven
    prop := ``LegacyRetired.Logarithm872, thm := some ``LegacyRetired.logarithm872_proven },
  { id := "bignumscov-mpfr-884", juliaFile := "base/mpfr.jl"
    juliaFns := ["log1p(x::BigFloat)"]
    statement := "The log1p method at base/mpfr.jl:884-893 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:884-893", status := .proven
    prop := ``LegacyRetired.Log1p884, thm := some ``LegacyRetired.log1p884_proven },
  { id := "bignumscov-mpfr-897", juliaFile := "base/mpfr.jl"
    juliaFns := ["minmax(x::BigFloat, y::BigFloat)"]
    statement := "The minmax method at base/mpfr.jl:897-901 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:897-901", status := .proven
    prop := ``LegacyRetired.Minmax897, thm := some ``LegacyRetired.minmax897_proven },
  { id := "bignumscov-mpfr-903", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base._extrema_rf(x::NTuple{2,BigFloat}, y::NTuple{2,BigFloat})"]
    statement := "The Base._extrema_rf method at base/mpfr.jl:903-910 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:903-910", status := .proven
    prop := ``LegacyRetired.Extrema903, thm := some ``LegacyRetired.extrema903_proven },
  { id := "bignumscov-mpfr-912", juliaFile := "base/mpfr.jl"
    juliaFns := ["modf(x::BigFloat)"]
    statement := "The modf method at base/mpfr.jl:912-917 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:912-917", status := .proven
    prop := ``LegacyRetired.Modf912, thm := some ``LegacyRetired.modf912_proven },
  { id := "bignumscov-mpfr-932", juliaFile := "base/mpfr.jl"
    juliaFns := ["rem2pi(x::BigFloat, r::RoundingMode)"]
    statement := "The rem2pi method at base/mpfr.jl:932-932 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:932-932", status := .proven
    prop := ``LegacyRetired.Rem2pi932, thm := some ``LegacyRetired.rem2pi932_proven },
  { id := "bignumscov-mpfr-946", juliaFile := "base/mpfr.jl"
    juliaFns := ["($f)(x::BigFloat)"]
    statement := "The $f method at base/mpfr.jl:946-952 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:946-952", status := .proven
    prop := ``LegacyRetired.CheckedUnary946, thm := some ``LegacyRetired.checkedUnary946_proven },
  { id := "bignumscov-mpfr-966", juliaFile := "base/mpfr.jl"
    juliaFns := ["($(Symbol(f,:d)))(x::BigFloat)"]
    statement := "The $(Symbol(f,:d)) method at base/mpfr.jl:966-972 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:966-972", status := .proven
    prop := ``LegacyRetired.Degree966, thm := some ``LegacyRetired.degree966_proven },
  { id := "bignumscov-mpfr-973", juliaFile := "base/mpfr.jl"
    juliaFns := ["($(Symbol(:a,f,:d)))(x::BigFloat)"]
    statement := "The $(Symbol(:a,f,:d)) method at base/mpfr.jl:973-979 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:973-979", status := .proven
    prop := ``LegacyRetired.Degree973, thm := some ``LegacyRetired.degree973_proven },
  { id := "bignumscov-mpfr-982", juliaFile := "base/mpfr.jl"
    juliaFns := ["atand(y::BigFloat, x::BigFloat)"]
    statement := "The atand method at base/mpfr.jl:982-986 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:982-986", status := .proven
    prop := ``LegacyRetired.Atand982, thm := some ``LegacyRetired.atand982_proven },
  { id := "bignumscov-mpfr-990", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::BigFloat, y::BigFloat)"]
    statement := "The == method at base/mpfr.jl:990-990 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:990-990", status := .proven
    prop := ``LegacyRetired.Equal990, thm := some ``LegacyRetired.equal990_proven },
  { id := "bignumscov-mpfr-991", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::BigFloat, y::BigFloat)"]
    statement := "The <= method at base/mpfr.jl:991-991 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:991-991", status := .proven
    prop := ``LegacyRetired.LessEqual991, thm := some ``LegacyRetired.lessEqual991_proven },
  { id := "bignumscov-mpfr-992", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::BigFloat, y::BigFloat)"]
    statement := "The < method at base/mpfr.jl:992-992 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:992-992", status := .proven
    prop := ``LegacyRetired.Less992, thm := some ``LegacyRetired.less992_proven },
  { id := "bignumscov-mpfr-994", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::BigInt)"]
    statement := "The cmp method at base/mpfr.jl:994-997 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:994-997", status := .proven
    prop := ``LegacyRetired.Cmp994, thm := some ``LegacyRetired.cmp994_proven },
  { id := "bignumscov-mpfr-998", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::ClongMax)"]
    statement := "The cmp method at base/mpfr.jl:998-1001 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:998-1001", status := .proven
    prop := ``LegacyRetired.Cmp998, thm := some ``LegacyRetired.cmp998_proven },
  { id := "bignumscov-mpfr-1002", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::CulongMax)"]
    statement := "The cmp method at base/mpfr.jl:1002-1005 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1002-1005", status := .proven
    prop := ``LegacyRetired.Cmp1002, thm := some ``LegacyRetired.cmp1002_proven },
  { id := "bignumscov-mpfr-1006", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::Integer)"]
    statement := "The cmp method at base/mpfr.jl:1006-1006 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1006-1006", status := .proven
    prop := ``LegacyRetired.Cmp1006, thm := some ``LegacyRetired.cmp1006_proven },
  { id := "bignumscov-mpfr-1007", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::Integer, y::BigFloat)"]
    statement := "The cmp method at base/mpfr.jl:1007-1007 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1007-1007", status := .proven
    prop := ``LegacyRetired.Cmp1007, thm := some ``LegacyRetired.cmp1007_proven },
  { id := "bignumscov-mpfr-1009", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::BigFloat, y::CdoubleMax)"]
    statement := "The cmp method at base/mpfr.jl:1009-1013 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1009-1013", status := .proven
    prop := ``LegacyRetired.Cmp1009, thm := some ``LegacyRetired.cmp1009_proven },
  { id := "bignumscov-mpfr-1014", juliaFile := "base/mpfr.jl"
    juliaFns := ["cmp(x::CdoubleMax, y::BigFloat)"]
    statement := "The cmp method at base/mpfr.jl:1014-1014 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1014-1014", status := .proven
    prop := ``LegacyRetired.Cmp1014, thm := some ``LegacyRetired.cmp1014_proven },
  { id := "bignumscov-mpfr-1016", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::BigFloat, y::Integer)"]
    statement := "The == method at base/mpfr.jl:1016-1016 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1016-1016", status := .proven
    prop := ``LegacyRetired.Eq1016, thm := some ``LegacyRetired.eq1016_proven },
  { id := "bignumscov-mpfr-1017", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::Integer, y::BigFloat)"]
    statement := "The == method at base/mpfr.jl:1017-1017 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1017-1017", status := .proven
    prop := ``LegacyRetired.Eq1017, thm := some ``LegacyRetired.eq1017_proven },
  { id := "bignumscov-mpfr-1018", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::BigFloat, y::CdoubleMax)"]
    statement := "The == method at base/mpfr.jl:1018-1018 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1018-1018", status := .proven
    prop := ``LegacyRetired.Eq1018, thm := some ``LegacyRetired.eq1018_proven },
  { id := "bignumscov-mpfr-1019", juliaFile := "base/mpfr.jl"
    juliaFns := ["==(x::CdoubleMax, y::BigFloat)"]
    statement := "The == method at base/mpfr.jl:1019-1019 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1019-1019", status := .proven
    prop := ``LegacyRetired.Eq1019, thm := some ``LegacyRetired.eq1019_proven },
  { id := "bignumscov-mpfr-1021", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::BigFloat, y::Integer)"]
    statement := "The < method at base/mpfr.jl:1021-1021 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1021-1021", status := .proven
    prop := ``LegacyRetired.Lt1021, thm := some ``LegacyRetired.lt1021_proven },
  { id := "bignumscov-mpfr-1022", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::Integer, y::BigFloat)"]
    statement := "The < method at base/mpfr.jl:1022-1022 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1022-1022", status := .proven
    prop := ``LegacyRetired.Lt1022, thm := some ``LegacyRetired.lt1022_proven },
  { id := "bignumscov-mpfr-1023", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::BigFloat, y::CdoubleMax)"]
    statement := "The < method at base/mpfr.jl:1023-1023 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1023-1023", status := .proven
    prop := ``LegacyRetired.Lt1023, thm := some ``LegacyRetired.lt1023_proven },
  { id := "bignumscov-mpfr-1024", juliaFile := "base/mpfr.jl"
    juliaFns := ["<(x::CdoubleMax, y::BigFloat)"]
    statement := "The < method at base/mpfr.jl:1024-1024 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1024-1024", status := .proven
    prop := ``LegacyRetired.Lt1024, thm := some ``LegacyRetired.lt1024_proven },
  { id := "bignumscov-mpfr-1026", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::BigFloat, y::Integer)"]
    statement := "The <= method at base/mpfr.jl:1026-1026 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1026-1026", status := .proven
    prop := ``LegacyRetired.Le1026, thm := some ``LegacyRetired.le1026_proven },
  { id := "bignumscov-mpfr-1027", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::Integer, y::BigFloat)"]
    statement := "The <= method at base/mpfr.jl:1027-1027 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1027-1027", status := .proven
    prop := ``LegacyRetired.Le1027, thm := some ``LegacyRetired.le1027_proven },
  { id := "bignumscov-mpfr-1028", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::BigFloat, y::CdoubleMax)"]
    statement := "The <= method at base/mpfr.jl:1028-1028 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1028-1028", status := .proven
    prop := ``LegacyRetired.Le1028, thm := some ``LegacyRetired.le1028_proven },
  { id := "bignumscov-mpfr-1029", juliaFile := "base/mpfr.jl"
    juliaFns := ["<=(x::CdoubleMax, y::BigFloat)"]
    statement := "The <= method at base/mpfr.jl:1029-1029 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1029-1029", status := .proven
    prop := ``LegacyRetired.Le1029, thm := some ``LegacyRetired.le1029_proven },
  { id := "bignumscov-mpfr-1033", juliaFile := "base/mpfr.jl"
    juliaFns := ["signbit(x::BigFloat)"]
    statement := "The signbit method at base/mpfr.jl:1033-1033 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1033-1033", status := .proven
    prop := ``LegacyRetired.Signbit1033, thm := some ``LegacyRetired.signbit1033_proven },
  { id := "bignumscov-mpfr-1035", juliaFile := "base/mpfr.jl"
    juliaFns := ["sign(x::BigFloat)"]
    statement := "The sign method at base/mpfr.jl:1035-1039 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1035-1039", status := .proven
    prop := ``LegacyRetired.Sign1035, thm := some ``LegacyRetired.sign1035_proven },
  { id := "bignumscov-mpfr-1041", juliaFile := "base/mpfr.jl"
    juliaFns := ["_precision_with_base_2(x::BigFloat)"]
    statement := "The _precision_with_base_2 method at base/mpfr.jl:1041-1043 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1041-1043", status := .proven
    prop := ``LegacyRetired.Precision1041, thm := some ``LegacyRetired.precision1041_proven },
  { id := "bignumscov-mpfr-1044", juliaFile := "base/mpfr.jl"
    juliaFns := ["precision(x::BigFloat; base::Integer=2)"]
    statement := "The precision method at base/mpfr.jl:1044-1044 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1044-1044", status := .proven
    prop := ``LegacyRetired.Precision1044, thm := some ``LegacyRetired.precision1044_proven },
  { id := "bignumscov-mpfr-1047", juliaFile := "base/mpfr.jl"
    juliaFns := ["_convert_precision_from_base(precision::Integer, base::Integer)"]
    statement := "The _convert_precision_from_base method at base/mpfr.jl:1047-1048 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1047-1048", status := .proven
    prop := ``LegacyRetired.ConvertPrecision1047, thm := some ``LegacyRetired.convertPrecision1047_proven },
  { id := "bignumscov-mpfr-1050", juliaFile := "base/mpfr.jl"
    juliaFns := ["_precision_with_base_2(::Type{BigFloat})"]
    statement := "The _precision_with_base_2 method at base/mpfr.jl:1050-1051 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1050-1051", status := .proven
    prop := ``LegacyRetired.TypePrecision1050, thm := some ``LegacyRetired.typePrecision1050_proven },
  { id := "bignumscov-mpfr-1069", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(::Type{BigFloat}, precision::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1069-1074 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1069-1074", status := .proven
    prop := ``LegacyRetired.Setprecision1069, thm := some ``LegacyRetired.setprecision1069_proven },
  { id := "bignumscov-mpfr-1076", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(precision::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1076-1076 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1076-1076", status := .proven
    prop := ``LegacyRetired.Setprecision1076, thm := some ``LegacyRetired.setprecision1076_proven },
  { id := "bignumscov-mpfr-1078", juliaFile := "base/mpfr.jl"
    juliaFns := ["maxintfloat(x::BigFloat)"]
    statement := "The maxintfloat method at base/mpfr.jl:1078-1078 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1078-1078", status := .proven
    prop := ``LegacyRetired.Maxint1078, thm := some ``LegacyRetired.maxint1078_proven },
  { id := "bignumscov-mpfr-1079", juliaFile := "base/mpfr.jl"
    juliaFns := ["maxintfloat(::Type{BigFloat})"]
    statement := "The maxintfloat method at base/mpfr.jl:1079-1079 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1079-1079", status := .proven
    prop := ``LegacyRetired.Maxint1079, thm := some ``LegacyRetired.maxint1079_proven },
  { id := "bignumscov-mpfr-1081", juliaFile := "base/mpfr.jl"
    juliaFns := ["copysign(x::BigFloat, y::BigFloat)"]
    statement := "The copysign method at base/mpfr.jl:1081-1085 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1081-1085", status := .proven
    prop := ``LegacyRetired.Copysign1081, thm := some ``LegacyRetired.copysign1081_proven },
  { id := "bignumscov-mpfr-1087", juliaFile := "base/mpfr.jl"
    juliaFns := ["exponent(x::BigFloat)"]
    statement := "The exponent method at base/mpfr.jl:1087-1093 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1087-1093", status := .proven
    prop := ``LegacyRetired.Exponent1087, thm := some ``LegacyRetired.exponent1087_proven },
  { id := "bignumscov-mpfr-1095", juliaFile := "base/mpfr.jl"
    juliaFns := ["frexp(x::BigFloat)"]
    statement := "The frexp method at base/mpfr.jl:1095-1100 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1095-1100", status := .proven
    prop := ``LegacyRetired.Frexp1095, thm := some ``LegacyRetired.frexp1095_proven },
  { id := "bignumscov-mpfr-1102", juliaFile := "base/mpfr.jl"
    juliaFns := ["significand(x::BigFloat)"]
    statement := "The significand method at base/mpfr.jl:1102-1109 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1102-1109", status := .proven
    prop := ``LegacyRetired.Significand1102, thm := some ``LegacyRetired.significand1102_proven },
  { id := "bignumscov-mpfr-1121", juliaFile := "base/mpfr.jl"
    juliaFns := ["round(x::BigFloat, ::RoundingMode{$(QuoteNode(R))})"]
    statement := "The round method at base/mpfr.jl:1121-1125 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1121-1125", status := .proven
    prop := ``LegacyRetired.Round1121, thm := some ``LegacyRetired.round1121_proven },
  { id := "bignumscov-mpfr-1129", juliaFile := "base/mpfr.jl"
    juliaFns := ["isinf(x::BigFloat)"]
    statement := "The isinf method at base/mpfr.jl:1129-1131 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1129-1131", status := .proven
    prop := ``LegacyRetired.Isinf1129, thm := some ``LegacyRetired.isinf1129_proven },
  { id := "bignumscov-mpfr-1133", juliaFile := "base/mpfr.jl"
    juliaFns := ["isnan(x::BigFloat)"]
    statement := "The isnan method at base/mpfr.jl:1133-1135 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1133-1135", status := .proven
    prop := ``LegacyRetired.Isnan1133, thm := some ``LegacyRetired.isnan1133_proven },
  { id := "bignumscov-mpfr-1141", juliaFile := "base/mpfr.jl"
    juliaFns := ["iszero(x::BigFloat)"]
    statement := "The iszero method at base/mpfr.jl:1141-1141 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1141-1141", status := .proven
    prop := ``LegacyRetired.Iszero1141, thm := some ``LegacyRetired.iszero1141_proven },
  { id := "bignumscov-mpfr-1142", juliaFile := "base/mpfr.jl"
    juliaFns := ["isone(x::BigFloat)"]
    statement := "The isone method at base/mpfr.jl:1142-1142 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1142-1142", status := .proven
    prop := ``LegacyRetired.Isone1142, thm := some ``LegacyRetired.isone1142_proven },
  { id := "bignumscov-mpfr-1148", juliaFile := "base/mpfr.jl"
    juliaFns := ["typemax(::Type{BigFloat})"]
    statement := "The typemax method at base/mpfr.jl:1148-1148 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1148-1148", status := .proven
    prop := ``LegacyRetired.Typemax1148, thm := some ``LegacyRetired.typemax1148_proven },
  { id := "bignumscov-mpfr-1149", juliaFile := "base/mpfr.jl"
    juliaFns := ["typemin(::Type{BigFloat})"]
    statement := "The typemin method at base/mpfr.jl:1149-1149 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1149-1149", status := .proven
    prop := ``LegacyRetired.Typemin1149, thm := some ``LegacyRetired.typemin1149_proven },
  { id := "bignumscov-mpfr-1151", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat!(x::BigFloat, n::Integer=1)"]
    statement := "The nextfloat! method at base/mpfr.jl:1151-1157 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1151-1157", status := .proven
    prop := ``LegacyRetired.Nextfloat1151, thm := some ``LegacyRetired.nextfloat1151_proven },
  { id := "bignumscov-mpfr-1159", juliaFile := "base/mpfr.jl"
    juliaFns := ["prevfloat!(x::BigFloat, n::Integer=1)"]
    statement := "The prevfloat! method at base/mpfr.jl:1159-1165 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1159-1165", status := .proven
    prop := ``LegacyRetired.Prevfloat1159, thm := some ``LegacyRetired.prevfloat1159_proven },
  { id := "bignumscov-mpfr-1167", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat(x::BigFloat, n::Integer=1)"]
    statement := "The nextfloat method at base/mpfr.jl:1167-1167 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1167-1167", status := .proven
    prop := ``LegacyRetired.Nextfloat1167, thm := some ``LegacyRetired.nextfloat1167_proven },
  { id := "bignumscov-mpfr-1168", juliaFile := "base/mpfr.jl"
    juliaFns := ["prevfloat(x::BigFloat, n::Integer=1)"]
    statement := "The prevfloat method at base/mpfr.jl:1168-1168 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1168-1168", status := .proven
    prop := ``LegacyRetired.Prevfloat1168, thm := some ``LegacyRetired.prevfloat1168_proven },
  { id := "bignumscov-mpfr-1170", juliaFile := "base/mpfr.jl"
    juliaFns := ["eps(::Type{BigFloat})"]
    statement := "The eps method at base/mpfr.jl:1170-1170 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1170-1170", status := .proven
    prop := ``LegacyRetired.Eps1170, thm := some ``LegacyRetired.eps1170_proven },
  { id := "bignumscov-mpfr-1172", juliaFile := "base/mpfr.jl"
    juliaFns := ["floatmin(::Type{BigFloat})"]
    statement := "The floatmin method at base/mpfr.jl:1172-1172 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1172-1172", status := .proven
    prop := ``LegacyRetired.Floatmin1172, thm := some ``LegacyRetired.floatmin1172_proven },
  { id := "bignumscov-mpfr-1173", juliaFile := "base/mpfr.jl"
    juliaFns := ["floatmax(::Type{BigFloat})"]
    statement := "The floatmax method at base/mpfr.jl:1173-1173 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1173-1173", status := .proven
    prop := ``LegacyRetired.Floatmax1173, thm := some ``LegacyRetired.floatmax1173_proven },
  { id := "bignumscov-mpfr-1214", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(f::Function, ::Type{BigFloat}, prec::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1214-1216 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1214-1216", status := .proven
    prop := ``LegacyRetired.Setprecision1214, thm := some ``LegacyRetired.setprecision1214_proven },
  { id := "bignumscov-mpfr-1217", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(f, ::Type{Union{}}, slurp...; kwargs...)"]
    statement := "setprecision(f, Union{}, args...; kwargs...) throws a MethodError."
    source := "base/mpfr.jl:1217-1217", status := .proven
    prop := ``LegacyRetired.Setprecision1217, thm := some ``LegacyRetired.setprecision1217_proven },
  { id := "bignumscov-mpfr-1219", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(f::Function, prec::Integer; base::Integer=2)"]
    statement := "The setprecision method at base/mpfr.jl:1219-1219 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1219-1219", status := .proven
    prop := ``LegacyRetired.Setprecision1219, thm := some ``LegacyRetired.setprecision1219_proven },
  { id := "bignumscov-mpfr-1221", juliaFile := "base/mpfr.jl"
    juliaFns := ["string_mpfr(x::BigFloat, fmt::String)"]
    statement := "The string_mpfr method at base/mpfr.jl:1221-1237 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1221-1237", status := .proven
    prop := ``LegacyRetired.StringMpfr1221, thm := some ``LegacyRetired.stringMpfr1221_proven },
  { id := "bignumscov-mpfr-1239", juliaFile := "base/mpfr.jl"
    juliaFns := ["_prettify_bigfloat(s::String)::String"]
    statement := "The _prettify_bigfloat method at base/mpfr.jl:1239-1265 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1239-1265", status := .proven
    prop := ``LegacyRetired.Prettify1239, thm := some ``LegacyRetired.prettify1239_proven },
  { id := "bignumscov-mpfr-1267", juliaFile := "base/mpfr.jl"
    juliaFns := ["_string(x::BigFloat, fmt::String)::String"]
    statement := "The _string method at base/mpfr.jl:1267-1270 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1267-1270", status := .proven
    prop := ``LegacyRetired.String1267, thm := some ``LegacyRetired.string1267_proven },
  { id := "bignumscov-mpfr-1271", juliaFile := "base/mpfr.jl"
    juliaFns := ["_string(x::BigFloat)"]
    statement := "The _string method at base/mpfr.jl:1271-1271 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1271-1271", status := .proven
    prop := ``LegacyRetired.String1271, thm := some ``LegacyRetired.string1271_proven },
  { id := "bignumscov-mpfr-1272", juliaFile := "base/mpfr.jl"
    juliaFns := ["_string(x::BigFloat, k::Integer)"]
    statement := "The _string method at base/mpfr.jl:1272-1272 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1272-1272", status := .proven
    prop := ``LegacyRetired.String1272, thm := some ``LegacyRetired.string1272_proven },
  { id := "bignumscov-mpfr-1274", juliaFile := "base/mpfr.jl"
    juliaFns := ["string(b::BigFloat)"]
    statement := "The string method at base/mpfr.jl:1274-1274 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1274-1274", status := .proven
    prop := ``LegacyRetired.String1274, thm := some ``LegacyRetired.string1274_proven },
  { id := "bignumscov-mpfr-1276", juliaFile := "base/mpfr.jl"
    juliaFns := ["print(io::IO, b::BigFloat)"]
    statement := "The print method at base/mpfr.jl:1276-1276 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1276-1276", status := .proven
    prop := ``LegacyRetired.Print1276, thm := some ``LegacyRetired.print1276_proven },
  { id := "bignumscov-mpfr-1277", juliaFile := "base/mpfr.jl"
    juliaFns := ["show(io::IO, b::BigFloat)"]
    statement := "The show method at base/mpfr.jl:1277-1283 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1277-1283", status := .proven
    prop := ``LegacyRetired.Show1277, thm := some ``LegacyRetired.show1277_proven },
  { id := "bignumscov-mpfr-1295", juliaFile := "base/mpfr.jl"
    juliaFns := ["set_emax!(x)"]
    statement := "The set_emax! method at base/mpfr.jl:1295-1295 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1295-1295", status := .proven
    prop := ``LegacyRetired.SetEmax1295, thm := some ``LegacyRetired.setEmax1295_proven },
  { id := "bignumscov-mpfr-1296", juliaFile := "base/mpfr.jl"
    juliaFns := ["set_emin!(x)"]
    statement := "The set_emin! method at base/mpfr.jl:1296-1296 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1296-1296", status := .proven
    prop := ``LegacyRetired.SetEmin1296, thm := some ``LegacyRetired.setEmin1296_proven },
  { id := "bignumscov-mpfr-1298", juliaFile := "base/mpfr.jl"
    juliaFns := ["Base.deepcopy_internal(x::BigFloat, stackdict::IdDict)"]
    statement := "The Base.deepcopy_internal method at base/mpfr.jl:1298-1305 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1298-1305", status := .proven
    prop := ``LegacyRetired.Deepcopy1298, thm := some ``LegacyRetired.deepcopy1298_proven },
  { id := "bignumscov-mpfr-1307", juliaFile := "base/mpfr.jl"
    juliaFns := ["decompose(x::BigFloat)::Tuple{BigInt, Int, Int}"]
    statement := "The decompose method at base/mpfr.jl:1307-1318 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1307-1318", status := .proven
    prop := ``LegacyRetired.Decompose1307, thm := some ``LegacyRetired.decompose1307_proven },
  { id := "bignumscov-mpfr-1326", juliaFile := "base/mpfr.jl"
    juliaFns := ["clear_flags()"]
    statement := "The clear_flags method at base/mpfr.jl:1326-1326 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1326-1326", status := .proven
    prop := ``LegacyRetired.ClearFlags1326, thm := some ``LegacyRetired.clearFlags1326_proven },
  { id := "bignumscov-mpfr-1327", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_underflow()"]
    statement := "The had_underflow method at base/mpfr.jl:1327-1327 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1327-1327", status := .proven
    prop := ``LegacyRetired.HadUnderflow1327, thm := some ``LegacyRetired.hadUnderflow1327_proven },
  { id := "bignumscov-mpfr-1328", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_overflow()"]
    statement := "The had_overflow method at base/mpfr.jl:1328-1328 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1328-1328", status := .proven
    prop := ``LegacyRetired.HadOverflow1328, thm := some ``LegacyRetired.hadOverflow1328_proven },
  { id := "bignumscov-mpfr-1329", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_divbyzero()"]
    statement := "The had_divbyzero method at base/mpfr.jl:1329-1329 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1329-1329", status := .proven
    prop := ``LegacyRetired.HadDivzero1329, thm := some ``LegacyRetired.hadDivzero1329_proven },
  { id := "bignumscov-mpfr-1330", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_nan()"]
    statement := "The had_nan method at base/mpfr.jl:1330-1330 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1330-1330", status := .proven
    prop := ``LegacyRetired.HadNan1330, thm := some ``LegacyRetired.hadNan1330_proven },
  { id := "bignumscov-mpfr-1331", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_inexact_exception()"]
    statement := "The had_inexact_exception method at base/mpfr.jl:1331-1331 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1331-1331", status := .proven
    prop := ``LegacyRetired.HadInexact1331, thm := some ``LegacyRetired.hadInexact1331_proven },
  { id := "bignumscov-mpfr-1332", juliaFile := "base/mpfr.jl"
    juliaFns := ["had_range_exception()"]
    statement := "The had_range_exception method at base/mpfr.jl:1332-1332 follows its own source branches, checks, calls, and return behavior for every allowed input."
    source := "base/mpfr.jl:1332-1332", status := .proven
    prop := ``LegacyRetired.HadRange1332, thm := some ``LegacyRetired.hadRange1332_proven }
]

end JuliaLean.Proofs.base.mpfr

namespace JuliaLean.Proofs.base.mpfr.LegacyRetired

open JuliaLean JuliaLean.base.mpfr

/-- The shared negative-count branch must make progress toward a nonnegative
native Int count before either neighboring-value loop can start. -/
def BigFloatStepTerminates : Prop :=
  ∀ (up : Bool) (n : JInt .i64), n.val < 0 →
    0 ≤ (JuliaLean.base.int.abs n).val ∧
    directionAndCount JuliaLean.base.int.signbit JuliaLean.base.int.abs
      (fun value : JInt .i64 => value.val) up n =
    directionAndCount JuliaLean.base.int.signbit JuliaLean.base.int.abs
      (fun value : JInt .i64 => value.val) (!up) (JuliaLean.base.int.abs n)

theorem bigFloatStepTerminates_refuted : ¬ BigFloatStepTerminates := by
  intro h
  have bad := (h true (JInt.typemin .i64) (by decide)).1
  have hvalue : (JuliaLean.base.int.abs (JInt.typemin .i64)).val =
      -9223372036854775808 := by decide
  rw [hvalue] at bad
  omega

/-- The callback sees the requested converted precision only after the same
base/precision validation performed by the documented global-setter sequence. -/
def ScopedPrecisionValidates : Prop :=
  ∀ (callback : Clong → Int) (base precision : Int) (converted : Clong) (state : Context),
    ((withPrecision (fun (_ : Int) (_ : Int) => .ok converted)
      (do let current ← readContext; pure (callback (precisionType current)))
      precision base).run state).1 =
    ((do
      let _ ← setprecision (fun x : Int => x) (fun x : Int => x)
        (fun (_ : Int) (_ : Int) => .ok converted) precision base
      pure (callback converted)).run state).1

theorem scopedPrecisionValidates_refuted : ¬ ScopedPrecisionValidates := by
  intro h
  let zero : Clong := JInt.wrap .i64 0
  let state : Context :=
    { emin := zero, emax := zero,
      limits := ⟨zero, zero, zero, zero⟩ }
  have bad := h (fun x => x.val) 2 0 zero state
  change (Except.ok 0 : Jl Int) =
    Except.error (.domainError "`precision` cannot be less than 1.") at bad
  cases bad

end JuliaLean.Proofs.base.mpfr.LegacyRetired

namespace JuliaLean.Proofs.base.mpfr

namespace LegacyRetired

open JuliaLean JuliaLean.base.mpfr JuliaLean.base.float

def MpfrSetupAndRoundingCorrect : Prop :=
  Version44 ∧
  Patches45 ∧
  Init47 ∧
  Convert75 ∧
  Convert76 ∧
  Convert77 ∧
  Convert78 ∧
  Convert79 ∧
  Convert81 ∧
  TieBreaker110 ∧
  (∀ (r : Mode),
    JuliaLean.base.mpfr.roundsToNearest r = (
    r == .nearest)) ∧
  (∀ (r : Mode) (negative : Bool),
    JuliaLean.base.mpfr.roundsAway r negative = (
    if r = .toZero then false else if r = .up then !negative
    else if r = .down then negative else true)) ∧
  (∀ (r : Mode),
    JuliaLean.base.mpfr.oppositeRound r = (
    if r = .up then .down else if r = .down then .up else r))

def MpfrStorageCorrect : Prop :=
  Getproperty183 ∧
  Setproperty201 ∧
  UnsafeConvert214 ∧
  UnsafeConvert215 ∧
  Cconvert216 ∧
  Cconvert217 ∧
  Cconvert218 ∧
  UnsafeConvert219 ∧
  UnsafeConvert229 ∧
  Setindex230 ∧
  Getindex236 ∧
  Length241 ∧
  Copyto242 ∧
  SetroundingRaw247 ∧
  SetroundingRaw248 ∧
  Rounding252 ∧
  Setrounding253 ∧
  Setrounding254 ∧
  (∀ (state : Context),
    JuliaLean.base.mpfr.roundingRaw state = (
    state.scopedRounding.getD state.defaultRounding))

theorem mpfrStorageCorrect : MpfrStorageCorrect := by
  unfold MpfrStorageCorrect
  exact ⟨getproperty183_proven, setproperty201_proven, unsafeConvert214_proven, unsafeConvert215_proven, cconvert216_proven, cconvert217_proven, cconvert218_proven, unsafeConvert219_proven, unsafeConvert229_proven, setindex230_proven, getindex236_proven, length241_proven, copyto242_proven, setroundingRaw247_proven, setroundingRaw248_proven, rounding252_proven, setrounding253_proven, setrounding254_proven, by intros; rfl⟩

def MpfrConstructorRoutingCorrect : Prop :=
  Widen299 ∧
  Widen300 ∧
  BigFloat302 ∧
  Duplicate313 ∧
  BigFloat322 ∧
  BigFloat330 ∧
  BigFloat374 ∧
  BigFloat380 ∧
  BigFloat382 ∧
  BigFloat385 ∧
  BigFloat387 ∧
  BigFloat390 ∧
  BigFloat393 ∧
  Opposite401 ∧
  Tryparse407 ∧
  BigFloat414 ∧
  Rational417 ∧
  AbstractFloat418 ∧
  Float420 ∧
  BigFloat422 ∧
  BigFloat424 ∧
  Unchecked428 ∧
  Unchecked430 ∧
  Unchecked434 ∧
  Unchecked438 ∧
  Unchecked444 ∧
  Round449 ∧
  Round458 ∧
  Invoke465 ∧
  Invoke467 ∧
  Unsafe471 ∧
  Unsafe472 ∧
  Round474 ∧
  Round476 ∧
  Round477 ∧
  Bool479 ∧
  BigInt484 ∧
  Convert489

theorem mpfrConstructorRoutingCorrect : MpfrConstructorRoutingCorrect := by
  unfold MpfrConstructorRoutingCorrect
  exact ⟨widen299_proven, widen300_proven, bigFloat302_proven, duplicate313_proven, bigFloat322_proven, bigFloat330_proven, bigFloat374_proven, bigFloat380_proven, bigFloat382_proven, bigFloat385_proven, bigFloat387_proven, bigFloat390_proven, bigFloat393_proven, opposite401_proven, tryparse407_proven, bigFloat414_proven, rational417_proven, abstractFloat418_proven, float420_proven, bigFloat422_proven, bigFloat424_proven, unchecked428_proven, unchecked430_proven, unchecked434_proven, unchecked438_proven, unchecked444_proven, round449_proven, round458_proven, invoke465_proven, invoke467_proven, unsafe471_proven, unsafe472_proven, round474_proven, round476_proven, round477_proven, bool479_proven, bigInt484_proven, convert489_proven⟩

def MpfrIeeeRoutingCorrect : Prop :=
  ToIeee494 ∧
  Float550 ∧
  Float551 ∧
  Float552 ∧
  Float553 ∧
  Float554 ∧
  Float555 ∧
  Promote557 ∧
  Promote558 ∧
  Promote559 ∧
  Big561 ∧
  Big563 ∧
  Rational565

def MpfrArithmeticRoutingCorrect : Prop :=
  Reverse589 ∧
  Reverse597 ∧
  Reverse605 ∧
  Reverse613 ∧
  Inv678 ∧
  Muladd686 ∧
  Div690 ∧
  Div698 ∧
  Div704 ∧
  Div712 ∧
  Div718 ∧
  Div726 ∧
  Div732 ∧
  Div740 ∧
  (∀ (op : BinaryOp) (x y : BigFloat),
    JuliaLean.base.mpfr.arithmetic op x y = (
    do
     binaryCall op ⟨x.value,false⟩ ⟨y.value,false⟩ (roundingRaw (← readContext)))) ∧
  (∀ (t : IntTy) (op : BinaryOp) (x : BigFloat) (c : JInt t),
    JuliaLean.base.mpfr.arithmeticInteger (t := t) op x c = (
    do
     binaryCall op ⟨x.value,false⟩ (.ofInt c.val) (roundingRaw (← readContext)))) ∧
  (∀ (T : FTy) (op : BinaryOp) (x : BigFloat) (c : FV T),
    JuliaLean.base.mpfr.arithmeticIEEE (T := T) op x c = (
    do
     binaryCall op ⟨x.value,false⟩ ⟨ieeeValue (convertFloat .f64 c),false⟩ (roundingRaw (← readContext)))) ∧
  (∀ (op : BinaryOp) (x : BigFloat) (c : BigInt),
    JuliaLean.base.mpfr.arithmeticBigInt op x c = (
    do
     binaryCall op ⟨x.value,false⟩ (.ofInt c.val) (roundingRaw (← readContext)))) ∧
  (∀ (c : BigInt) (x : BigFloat),
    JuliaLean.base.mpfr.bigIntSub c x = (
    do
     binaryCall .sub (.ofInt c.val) ⟨x.value,false⟩ (roundingRaw (← readContext)))) ∧
  (∀ (x y z : BigFloat),
    JuliaLean.base.mpfr.fma x y z = (
    do
     let output ← fresh
     let state ← readContext
     applyPrimitive (fmaPrimitive state output.prec (roundingRaw state) x y z))) ∧
  (∀ (op : BinaryOp) (a b c : BigFloat),
    JuliaLean.base.mpfr.commutative3 op a b c = (
    do
     let z ← arithmetic op a b
     let state ← readContext
     applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) op ⟨z.value,false⟩ ⟨c.value,false⟩))) ∧
  (∀ (op : BinaryOp) (a b c d : BigFloat),
    JuliaLean.base.mpfr.commutative4 op a b c d = (
    do
     let z ← commutative3 op a b c
     let state ← readContext
     applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) op ⟨z.value,false⟩ ⟨d.value,false⟩))) ∧
  (∀ (op : BinaryOp) (a b c d e : BigFloat),
    JuliaLean.base.mpfr.commutative5 op a b c d e = (
    do
     let z ← commutative4 op a b c d
     let state ← readContext
     applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) op ⟨z.value,false⟩ ⟨e.value,false⟩))) ∧
  (∀ (x : BigFloat),
    JuliaLean.base.mpfr.neg x = (
    do
     let z ← fresh
     let state ← readContext
     applyPrimitive (setPrimitive state z.prec x.value.neg (roundingRaw state))))

def MpfrTranscendentalRoutingCorrect : Prop :=
  Sqrt781 ∧
  Sqrt789 ∧
  Power815 ∧
  Power816 ∧
  SincosFast826 ∧
  Sincos832 ∧
  BigLn2835 ∧
  Ldexp841 ∧
  Ldexp846 ∧
  Ldexp851 ∧
  Ldexp852 ∧
  Ldexp853 ∧
  Factorial855 ∧
  Logarithm872 ∧
  Log1p884 ∧
  Minmax897 ∧
  Extrema903 ∧
  Modf912 ∧
  Rem2pi932 ∧
  CheckedUnary946 ∧
  Degree966 ∧
  Degree973 ∧
  Atand982 ∧
  (∀ (ops : AnalyticOps) (x y : BigFloat),
    JuliaLean.base.mpfr.powReal ops x y = (
    do
     let z ← fresh
     let state ← readContext
     applyPrimitive (ops.binary .pow state z.prec (roundingRaw state) x y))) ∧
  (∀ (ops : AnalyticOps) (kernel : MPFRUnaryKernel) (x : BigFloat),
    JuliaLean.base.mpfr.unaryKernel ops kernel x = (
    do
     let z ← fresh
     let state ← readContext
     applyPrimitive (ops.unary kernel state z.prec (roundingRaw state) x))) ∧
  (∀ (x y : BigFloat),
    JuliaLean.base.mpfr.hypot x y = (
    do
     let z ← fresh
     let state ← readContext
     if isinf x || isinf y then return ← applyPrimitive (specialResult z.prec (.inf false))
     if isnan x || isnan y then
       return ← applyPrimitive (specialResult z.prec (.nan false) { nan := true })
     let (a,b) := x.value.toRat
     let (c,d) := y.value.toRat
     applyPrimitive (sqrtRatPrimitive state z.prec (roundingRaw state)
       (a.natAbs^2*d^2+c.natAbs^2*b^2) (b^2*d^2)))) ∧
  (∀ (x y : BigFloat),
    JuliaLean.base.mpfr.rem x y = (
    do
     let z ← fresh
     let state ← readContext
     applyPrimitive (remainderPrimitive state z.prec (roundingRaw state) false x y))) ∧
  (∀ (x y : BigFloat),
    JuliaLean.base.mpfr.remNearest x y = (
    do
     let z ← fresh
     let state ← readContext
     applyPrimitive (remainderPrimitive state z.prec (roundingRaw state) true x y))) ∧
  (∀ (arr : List BigFloat),
    JuliaLean.base.mpfr.sum arr = (
    do
     let state ← readContext
     let init ← fromLong (JInt.wrap .i64 0) (roundingRaw state) (precisionType state).val
     arr.foldlM (fun z i => do
       let state ← readContext
       applyPrimitive (binaryPrimitive state z.prec (roundingRaw state) .add ⟨z.value,false⟩ ⟨i.value,false⟩)) init)) ∧
  (∀ (ops : AnalyticOps) (y x : BigFloat),
    JuliaLean.base.mpfr.atan ops y x = (
    do
     let z ← fresh
     let state ← readContext
     applyPrimitive (ops.binary .atan2 state z.prec (roundingRaw state) y x)))

theorem mpfrTranscendentalRoutingCorrect : MpfrTranscendentalRoutingCorrect := by
  unfold MpfrTranscendentalRoutingCorrect
  exact ⟨sqrt781_proven, sqrt789_proven, power815_proven, power816_proven, sincosFast826_proven, sincos832_proven, bigLn2835_proven, ldexp841_proven, ldexp846_proven, ldexp851_proven, ldexp852_proven, ldexp853_proven, factorial855_proven, logarithm872_proven, log1p884_proven, minmax897_proven, extrema903_proven, modf912_proven, rem2pi932_proven, checkedUnary946_proven, degree966_proven, degree973_proven, atand982_proven, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def MpfrComparisonCorrect : Prop :=
  Equal990 ∧
  LessEqual991 ∧
  Less992 ∧
  Cmp994 ∧
  Cmp998 ∧
  Cmp1002 ∧
  Cmp1006 ∧
  Cmp1007 ∧
  Cmp1009 ∧
  Cmp1014 ∧
  Eq1016 ∧
  Eq1017 ∧
  Eq1018 ∧
  Eq1019 ∧
  Lt1021 ∧
  Lt1022 ∧
  Lt1023 ∧
  Lt1024 ∧
  Le1026 ∧
  Le1027 ∧
  Le1028 ∧
  Le1029 ∧
  Signbit1033 ∧
  Sign1035

theorem mpfrComparisonCorrect : MpfrComparisonCorrect := by
  unfold MpfrComparisonCorrect
  exact ⟨equal990_proven, lessEqual991_proven, less992_proven, cmp994_proven, cmp998_proven, cmp1002_proven, cmp1006_proven, cmp1007_proven, cmp1009_proven, cmp1014_proven, eq1016_proven, eq1017_proven, eq1018_proven, eq1019_proven, lt1021_proven, lt1022_proven, lt1023_proven, lt1024_proven, le1026_proven, le1027_proven, le1028_proven, le1029_proven, signbit1033_proven, sign1035_proven⟩

def MpfrPrecisionAndClassificationCorrect : Prop :=
  Precision1041 ∧
  Precision1044 ∧
  ConvertPrecision1047 ∧
  TypePrecision1050 ∧
  Setprecision1069 ∧
  Setprecision1076 ∧
  Maxint1078 ∧
  Maxint1079 ∧
  Copysign1081 ∧
  Exponent1087 ∧
  Frexp1095 ∧
  Significand1102 ∧
  Round1121 ∧
  Isinf1129 ∧
  Isnan1133 ∧
  Iszero1141 ∧
  Isone1142 ∧
  Typemax1148 ∧
  Typemin1149 ∧
  (∀ (x : BigFloat),
    JuliaLean.base.mpfr.isinteger x = (
    if !isfinite x then false else
      let (n,d) := x.value.toRat
      decide (n % (d : Int) = 0))) ∧
  (∀ (_x : BigFloat),
    JuliaLean.base.mpfr.issubnormal _x = (
    false)) ∧
  (∀ (x : BigFloat),
    JuliaLean.base.mpfr.isfinite x = (
    !isinf x && !isnan x)) ∧
  (∀ (x : BigFloat),
    JuliaLean.base.mpfr.ispositive x = (
    decide (x.sign.val ≥ 0) && !iszero x && !isnan x)) ∧
  (∀ (x : BigFloat),
    JuliaLean.base.mpfr.isnegative x = (
    decide (x.sign.val < 0) && !iszero x && !isnan x))

theorem mpfrPrecisionAndClassificationCorrect : MpfrPrecisionAndClassificationCorrect := by
  unfold MpfrPrecisionAndClassificationCorrect
  exact ⟨precision1041_proven, precision1044_proven, convertPrecision1047_proven, typePrecision1050_proven, setprecision1069_proven, setprecision1076_proven, maxint1078_proven, maxint1079_proven, copysign1081_proven, exponent1087_proven, frexp1095_proven, significand1102_proven, round1121_proven, isinf1129_proven, isnan1133_proven, iszero1141_proven, isone1142_proven, typemax1148_proven, typemin1149_proven, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩

def MpfrNeighborDerivedCorrect : Prop :=
  Nextfloat1167 ∧
  Prevfloat1168 ∧
  Eps1170 ∧
  Floatmin1172 ∧
  Floatmax1173

theorem mpfrNeighborDerivedCorrect : MpfrNeighborDerivedCorrect := by
  unfold MpfrNeighborDerivedCorrect
  exact ⟨nextfloat1167_proven, prevfloat1168_proven, eps1170_proven, floatmin1172_proven, floatmax1173_proven⟩

def MpfrStateAndFormattingCorrect : Prop :=
  Setprecision1214 ∧
  Setprecision1217 ∧
  Setprecision1219 ∧
  StringMpfr1221 ∧
  Prettify1239 ∧
  String1267 ∧
  String1271 ∧
  String1272 ∧
  String1274 ∧
  Print1276 ∧
  Show1277 ∧
  SetEmax1295 ∧
  SetEmin1296 ∧
  Deepcopy1298 ∧
  Decompose1307 ∧
  ClearFlags1326 ∧
  HadUnderflow1327 ∧
  HadOverflow1328 ∧
  HadDivzero1329 ∧
  HadNan1330 ∧
  HadInexact1331 ∧
  HadRange1332 ∧
  (∀ (A : Type) (P : Type) (warn : M Unit) (precision : M P) (setPrecision : P → M Unit) (prec : P) (action : M A),
    JuliaLean.base.mpfr.withPrecisionFallback (P := P) warn precision setPrecision prec action = (
    do
     warn
     let old ← precision
     setPrecision prec
     let result ← tryCatch (do let value ← action; pure (.ok value)) (fun error => pure (.error error))
     setPrecision old
     liftJl result)) ∧
  (∀ (state : Context),
    JuliaLean.base.mpfr.getEmin state = (
    state.emin)) ∧
  (∀ (state : Context),
    JuliaLean.base.mpfr.getEmax state = (
    state.emax)) ∧
  (∀ (state : Context),
    JuliaLean.base.mpfr.getEminMin state = (
    state.limits.eminMin)) ∧
  (∀ (state : Context),
    JuliaLean.base.mpfr.getEminMax state = (
    state.limits.eminMax)) ∧
  (∀ (state : Context),
    JuliaLean.base.mpfr.getEmaxMin state = (
    state.limits.emaxMin)) ∧
  (∀ (state : Context),
    JuliaLean.base.mpfr.getEmaxMax state = (
    state.limits.emaxMax)) ∧
  (∀ (J D : Type) (convertJ : J → M BigFloat) (divideD : BigFloat → D → M BigFloat) (j : J) (d : D) (a b : BigFloat),
    JuliaLean.base.mpfr.lerpi (J := J) (D := D) convertJ divideD j d a b = (
    do
     let t ← divideD (← convertJ j) d
     let inside ← fma (← neg t) a a
     fma t b inside))

theorem mpfrStateAndFormattingCorrect : MpfrStateAndFormattingCorrect := by
  unfold MpfrStateAndFormattingCorrect
  exact ⟨setprecision1214_proven, setprecision1217_proven, setprecision1219_proven, stringMpfr1221_proven, prettify1239_proven, string1267_proven, string1271_proven, string1272_proven, string1274_proven, print1276_proven, show1277_proven, setEmax1295_proven, setEmin1296_proven, deepcopy1298_proven, decompose1307_proven, clearFlags1326_proven, hadUnderflow1327_proven, hadOverflow1328_proven, hadDivzero1329_proven, hadNan1330_proven, hadInexact1331_proven, hadRange1332_proven, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩


theorem mpfrSetupAndRoundingCorrect_proven : MpfrSetupAndRoundingCorrect := by
  unfold MpfrSetupAndRoundingCorrect
  exact ⟨version44_proven, patches45_proven, init47_proven,
    convert75_proven, convert76_proven, convert77_proven, convert78_proven,
    convert79_proven, convert81_proven, tieBreaker110_proven,
    by intros; rfl, by intros; rfl, by intros; rfl⟩

theorem mpfrIeeeRoutingCorrect_proven : MpfrIeeeRoutingCorrect := by
  unfold MpfrIeeeRoutingCorrect
  exact ⟨toIeee494_proven, float550_proven, float551_proven, float552_proven,
    float553_proven, float554_proven, float555_proven, promote557_proven,
    promote558_proven, promote559_proven, big561_proven, big563_proven, rational565_proven⟩

theorem mpfrArithmeticRoutingCorrect_proven : MpfrArithmeticRoutingCorrect := by
  unfold MpfrArithmeticRoutingCorrect
  exact ⟨reverse589_proven, reverse597_proven, reverse605_proven, reverse613_proven,
    inv678_proven, muladd686_proven, div690_proven, div698_proven,
    div704_proven, div712_proven, div718_proven, div726_proven,
    div732_proven, div740_proven,
    by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl⟩

end LegacyRetired

open JuliaLean.Registry

def entriesLegacyAggregates : List Entry := [
  { id := "bignumscov-mpfr-setup-rounding", juliaFile := "base/mpfr.jl"
    juliaFns := ["version", "patches", "__init__", "convert rounding modes", "rounds_to_nearest", "rounds_away_from_zero", "tie_breaker_is_to_even"]
    statement := "MPFR setup calls both exponent setters, mode conversions accept exactly the five MPFR modes, and direction predicates follow sign and mode."
    source := "base/mpfr.jl:44-110"
    status := .proven, prop := ``LegacyRetired.MpfrSetupAndRoundingCorrect, thm := some ``LegacyRetired.mpfrSetupAndRoundingCorrect_proven 
    notes := "Retired JuliaLean.BigNumsCov.Mpfr.mpfrSetupAndRoundingCorrect at a2fd59b64fda5264fda1337c1534d56a17b98872; The installed exponent setters and error handler are effectful Context operations; the old pure callback proof does not establish their result contract." },
  { id := "bignumscov-mpfr-storage", juliaFile := "base/mpfr.jl"
    juliaFns := ["_BigFloat", "BigFloat(; precision)", "getproperty", "setproperty!", "unsafe_convert", "cconvert", "BigFloatData indexing", "rounding_raw", "setrounding"]
    statement := "BigFloat property access, permitted mutation, checked data indexing, pointer-routing wrappers, and scoped rounding selection follow the source branches for all inputs."
    source := "base/mpfr.jl:149-255"
    status := .proven, prop := ``LegacyRetired.MpfrStorageCorrect, thm := some ``LegacyRetired.mpfrStorageCorrect },
  { id := "bignumscov-mpfr-constructors", juliaFile := "base/mpfr.jl"
    juliaFns := ["widen", "BigFloat constructors", "_duplicate", "_opposite_round", "Rational", "AbstractFloat", "float", "unchecked casts", "round", "unsafe_trunc", "Bool", "BigInt"]
    statement := "BigFloat construction, copy precision, directed rational conversion, integer casts, range checks, Bool conversion, and constructor routing return the source-selected value or error."
    source := "base/mpfr.jl:299-493"
    status := .proven, prop := ``LegacyRetired.MpfrConstructorRoutingCorrect, thm := some ``LegacyRetired.mpfrConstructorRoutingCorrect },
  { id := "bignumscov-mpfr-ieee-routing", juliaFile := "base/mpfr.jl"
    juliaFns := ["to_ieee754", "Float16", "Float32", "Float64", "promote_rule", "big", "Rational{BigInt}"]
    statement := "BigFloat conversion to fixed IEEE formats selects finite, zero, infinity, omega, or NaN according to special-value, exponent, and rounding-direction branches."
    source := "base/mpfr.jl:494-571"
    status := .proven, prop := ``LegacyRetired.MpfrIeeeRoutingCorrect, thm := some ``LegacyRetired.mpfrIeeeRoutingCorrect_proven 
    notes := "Retired JuliaLean.BigNumsCov.Mpfr.mpfrIeeeRoutingCorrect at a2fd59b64fda5264fda1337c1534d56a17b98872; The old five-way result tag must be related to the installed IEEE bit-pattern classification." },
  { id := "bignumscov-mpfr-arithmetic", juliaFile := "base/mpfr.jl"
    juliaFns := ["generated + - * /", "inv", "fma", "muladd", "div", "generated 3-5 argument operations", "unary -"]
    statement := "Allocating MPFR unary, binary, ternary, mixed-operand, and generated left-fold wrappers preserve primitive selection, argument order, and return value."
    source := "base/mpfr.jl:573-779"
    status := .proven, prop := ``LegacyRetired.MpfrArithmeticRoutingCorrect, thm := some ``LegacyRetired.mpfrArithmeticRoutingCorrect_proven 
    notes := "Retired JuliaLean.BigNumsCov.Mpfr.mpfrArithmeticRoutingCorrect at a2fd59b64fda5264fda1337c1534d56a17b98872; The old arbitrary callback reversal needs commutativity of the installed exact arithmetic and rounding kernels. The old arbitrary callback reversal needs commutativity of the installed IEEE conversion, arithmetic and rounding kernels." },
  { id := "bignumscov-mpfr-transcendentals", juliaFile := "base/mpfr.jl"
    juliaFns := ["sqrt", "^", "generated unary functions", "sincos", "ldexp", "factorial", "hypot", "log1p", "minmax", "_extrema_rf", "modf", "rem", "rem2pi", "sum", "trigonometric and degree functions"]
    statement := "MPFR mathematical wrappers preserve primitive arguments, return input NaNs, reject newly produced NaNs, take log1p's real-domain branch, and preserve minmax and sum ordering."
    source := "base/mpfr.jl:781-985"
    status := .proven, prop := ``LegacyRetired.MpfrTranscendentalRoutingCorrect, thm := some ``LegacyRetired.mpfrTranscendentalRoutingCorrect },
  { id := "bignumscov-mpfr-comparisons", juliaFile := "base/mpfr.jl"
    juliaFns := ["==", "<", "<=", "cmp", "signbit", "sign"]
    statement := "BigFloat comparisons follow the explicit NaN ordering and unordered numeric predicates, and sign preserves zeros and NaNs while returning unit sign otherwise."
    source := "base/mpfr.jl:990-1039"
    status := .proven, prop := ``LegacyRetired.MpfrComparisonCorrect, thm := some ``LegacyRetired.mpfrComparisonCorrect },
  { id := "bignumscov-mpfr-precision-classification", juliaFile := "base/mpfr.jl"
    juliaFns := ["precision", "_precision_with_base_2", "_convert_precision_from_base", "setprecision", "maxintfloat", "copysign", "exponent", "frexp", "significand", "isinteger", "round", "isinf", "isnan", "issubnormal", "isfinite", "iszero", "isone", "ispositive", "isnegative", "typemax", "typemin"]
    statement := "Precision validation rejects invalid bases and precisions, exponent rejects zero and nonfinite values, and BigFloat classification follows the three special exponent codes."
    source := "base/mpfr.jl:1041-1149"
    status := .proven, prop := ``LegacyRetired.MpfrPrecisionAndClassificationCorrect, thm := some ``LegacyRetired.mpfrPrecisionAndClassificationCorrect },
  { id := "bignumscov-nextfloat-typemin", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat!", "prevfloat!", "nextfloat", "prevfloat"]
    statement := "Every negative Int step count becomes nonnegative before nextfloat! or prevfloat! starts the opposite-direction loop."
    source := "nextfloat/prevfloat docstrings base/float.jl:848-869; base/mpfr.jl:1151-1168"
    status := .refuted, prop := ``LegacyRetired.BigFloatStepTerminates, thm := some ``LegacyRetired.bigFloatStepTerminates_refuted
    issue := "none found (queries: nextfloat typemin BigFloat; prevfloat typemin BigFloat; nextfloat! hang; PR nextfloat typemin BigFloat; PR prevfloat typemin BigFloat)"
    notes := "Both Julia 1.13.2 and master hang: abs(typemin(Int)) wraps, so nextfloat! and prevfloat! call each other forever." },
  { id := "bignumscov-mpfr-neighbor-derived", juliaFile := "base/mpfr.jl"
    juliaFns := ["nextfloat", "prevfloat", "eps", "floatmin", "floatmax"]
    statement := "For nonnegative counts, zero-step neighbor calls preserve identity, nonzero calls duplicate before mutation, and the three constants delegate to their documented one-step neighbor operation."
    source := "base/mpfr.jl:1167-1173"
    status := .proven, prop := ``LegacyRetired.MpfrNeighborDerivedCorrect, thm := some ``LegacyRetired.mpfrNeighborDerivedCorrect },
  { id := "bignumscov-scoped-setprecision-validation", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision(::Function,::Type{BigFloat},::Integer; base)", "setprecision(::Function,::Integer; base)"]
    statement := "Callback-scoped BigFloat setprecision rejects invalid bases and precisions before running the callback, as its documented equivalent global-setter sequence does."
    source := "setprecision callback docstring base/mpfr.jl:1175-1183; validation base/mpfr.jl:1069-1073; scoped implementation base/mpfr.jl:1214-1219"
    status := .refuted, prop := ``LegacyRetired.ScopedPrecisionValidates, thm := some ``LegacyRetired.scopedPrecisionValidates_refuted
    issue := "none found (queries: setprecision BigFloat scoped validation; setprecision BigFloat DomainError; PR setprecision BigFloat scoped validation; PR setprecision BigFloat DomainError)"
    notes := "Both Julia 1.13.2 and master accept precision 0 and base 1 when the callback returns without allocating BigFloat." },
  { id := "bignumscov-mpfr-state-formatting", juliaFile := "base/mpfr.jl"
    juliaFns := ["setprecision callback forms", "string_mpfr", "_prettify_bigfloat", "_string", "string", "print", "show", "get/set exponent range", "deepcopy_internal", "decompose", "lerpi", "flag functions"]
    statement := "Scoped precision restores the prior value, formatting selects fixed notation only for exponents -4 through 5, exponent setters check their status, decomposition follows special classes, and flag wrappers test nonzero."
    source := "base/mpfr.jl:1200-1332"
    status := .proven, prop := ``LegacyRetired.MpfrStateAndFormattingCorrect, thm := some ``LegacyRetired.mpfrStateAndFormattingCorrect }
]

end JuliaLean.Proofs.base.mpfr
