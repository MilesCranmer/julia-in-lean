import JuliaLean.base.intfuncs
import JuliaLean.Registry.Types

/-!
# Specifications of `base/intfuncs.jl`

Every entry is `.todo`: this phase states the documented contracts on the source models.
Mathematical integers, divisibility, powers, polynomial evaluation, and numeral decoding below
are specification vocabulary. They do not call the algorithms being specified. The laws for
external callees describe division, GMP arithmetic, square-root rounding, and logarithm seeds.
-/

namespace JuliaLean.Proofs.base.intfuncs

open JuliaLean JuliaLean.base.intfuncs JuliaLean.Registry

private def domainError {A : Type} : Jl A → Prop
  | .error (.domainError _) => True
  | _ => False

private def overflowError {A : Type} : Jl A → Prop
  | .error (.overflowError _) => True
  | _ => False

private def argumentError {A : Type} : Jl A → Prop
  | .error (.argumentError _) => True
  | _ => False
private def inexactError {A : Type} : Jl A → Prop
  | .error (.inexactError _) => True
  | _ => False


private def divideError {A : Type} : Jl A → Prop
  | .error .divideError => True
  | _ => False

def fits (t : IntTy) (z : Int) : Prop := t.min ≤ z ∧ z ≤ t.max

instance (t : IntTy) (z : Int) : Decidable (fits t z) :=
  inferInstanceAs (Decidable (t.min ≤ z ∧ z ≤ t.max))

def ExactOrOverflow {t : IntTy} (result : Jl (JInt t)) (z : Int) : Prop :=
  if fits t z then ∃ r, result = .ok r ∧ r.val = z else overflowError result

def gcdMath (a b : Int) : Int := (Nat.gcd a.natAbs b.natAbs : Int)
def lcmMath (a b : Int) : Int := (Nat.lcm a.natAbs b.natAbs : Int)

def ModInverse (a m y : Int) : Prop := m ≠ 0 ∧ (a * y - 1) % m = 0 ∧ y.tdiv m = 0

def InverseResult (a m : Int) (result : Jl Int) : Prop :=
  if m = 0 ∨ gcdMath a m ≠ 1 then domainError result
  else ∃ y, result = .ok y ∧ ModInverse a m y

def ModularPower (x p m y : Int) : Prop :=
  if p ≥ 0 then y = x ^ p.toNat % m
  else ∃ inverse, ModInverse x m inverse ∧ y = inverse ^ p.natAbs % m

/-- Only promises of callees defined outside `intfuncs.jl` occur here. -/
def NumberLaws (c : NumberCallees) : Prop :=
  (∀ (s t : IntTy) (a : JInt s) (b : JInt t),
    c.mixedMod a b = if b.val = 0 then .error .divideError else .ok (a.val % b.val)) ∧
  (∀ a b : Int, ∃ g u v, c.gmpGcdx a b = .ok (g, u, v) ∧
    g = gcdMath a b ∧ a * u + b * v = g) ∧
  (∀ x p m : Int, m ≠ 0 → (p < 0 → gcdMath x m = 1) →
    ∃ y, c.gmpPowermod x p m = .ok y ∧ ModularPower x p m y) ∧
  (∀ x p : Int, divideError (c.gmpPowermod x p 0))

def quotientType (a b : IntTy) : IntTy :=
  if a.signed = b.signed then a.promote b
  else if a.signed then (a.toUnsigned.promote b.toUnsigned).toSigned
  else (a.toUnsigned.promote b.toUnsigned).toUnsigned

/-- Julia's mixed quotient returns the type-correct floor, ceiling, or truncated quotient. -/
def QuotientLaws (c : DigitCallees) : Prop :=
  ∀ (a b : IntTy) (up down : Bool) (x y : Int),
    fits a x → fits b y → y ≠ 0 →
    ¬ (a.signed = true ∧ x = a.min ∧ y = -1) →
    c.quotient a b up down x y = .ok
      (wrapInt (quotientType a b) (if up then -(x / (-y)) else if down then x / y else x.tdiv y))

/-- Horner evaluation of digits in least-significant-first order. -/
def evalpoly (base : Int) : List Int → Int
  | [] => 0
  | d :: ds => d + base * evalpoly base ds

def DigitRange (n base : Int) (ds : List Int) : Prop :=
  ∀ d ∈ ds, d.natAbs < base.natAbs ∧
    (base < 0 → 0 ≤ d) ∧ (base > 0 → (n < 0 → d ≤ 0) ∧ (0 ≤ n → 0 ≤ d))

def DigitCount (n base pad count : Int) : Prop :=
  0 ≤ count ∧ pad ≤ count ∧
  (∃ ds : List Int, (ds.length : Int) = count ∧ evalpoly base ds = n ∧ DigitRange n base ds) ∧
  (∀ ds : List Int, evalpoly base ds = n → DigitRange n base ds →
    count ≤ max pad (ds.length : Int))

private def digitValue (base : Int) (ch : Nat) : Option Int :=
  if 48 ≤ ch ∧ ch ≤ 57 then some (ch - 48 : Nat)
  else if base.natAbs ≤ 36 ∧ 97 ≤ ch ∧ ch ≤ 122 then some (ch - 97 + 10 : Nat)
  else if 36 < base.natAbs ∧ 65 ≤ ch ∧ ch ≤ 90 then some (ch - 65 + 10 : Nat)
  else if 36 < base.natAbs ∧ 97 ≤ ch ∧ ch ≤ 122 then some (ch - 97 + 36 : Nat)
  else none

private def decodeUnsigned (base : Int) (bytes : List Nat) : Option Int :=
  bytes.foldlM (fun n ch => do
    let d ← digitValue base ch
    if 0 ≤ d ∧ d < (base.natAbs : Int) then some (n * base + d) else none) 0

def decodeNumeral (base : Int) (bytes : List Nat) : Option Int :=
  match bytes with
  | 45 :: rest => if base > 0 then (decodeUnsigned base rest).map Int.neg else none
  | _ => decodeUnsigned base bytes

private def digitCharacterCode (base digit : Int) : Nat :=
  if digit < 10 then 48 + digit.toNat
  else if base.natAbs ≤ 36 then 97 + (digit - 10).toNat
  else if digit < 36 then 65 + (digit - 10).toNat
  else 97 + (digit - 36).toNat

private def digitsForBase (base : Int) (digits : List Int) : Prop :=
  ∀ d ∈ digits, 0 ≤ d ∧ d < base.natAbs

private def numeralBytes (base : Int) (digits : List Int) : List Nat :=
  digits.reverse.map (digitCharacterCode base)
def StringRepresentation (n base pad : Int) (bytes : List Nat) : Prop :=
  2 ≤ base.natAbs ∧ base.natAbs ≤ 62 ∧
  let negative := base > 0 ∧ n < 0
  let value := if negative then -n else n
  ∃ digits : List Int,
    digitsForBase base digits ∧ evalpoly base digits = value ∧
    (∀ other : List Int, digitsForBase base other → evalpoly base other = value →
      digits.length ≤ other.length) ∧
    (digits.length : Int) ≥ max 0 pad ∧
    bytes = (if negative then [45] else []) ++
      numeralBytes base (digits ++ List.replicate (max 0 pad - (digits.length : Int)).toNat 0)

def BufferSafe (b : Buffer) : Prop :=
  (∀ i ∈ b.writes, 1 ≤ i ∧ i ≤ (b.bytes.length : Int)) ∧
  (∀ r ∈ b.tableReads, 1 ≤ r.1 ∧ r.1 ≤ (r.2 : Int))

def factorialMath : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorialMath n

private def chooseMath : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chooseMath n k + chooseMath n (k + 1)

def binomialMath (n k : Int) : Int :=
  if k < 0 then 0
  else if n ≥ 0 then (chooseMath n.toNat k.toNat : Int)
  else (-1 : Int) ^ k.toNat * (chooseMath (k - n - 1).toNat k.toNat : Int)

/-! ## Greatest common divisors and least common multiples -/

def GcdExact : Prop := ∀ (t : IntTy) (a b : JInt t),
  ExactOrOverflow (gcd_BitInteger a b) (gcdMath a.val b.val)

def GcdGenericExact : Prop := ∀ a b : Int,
  gcd_Integer bigOps a b = .ok (gcdMath a b)

def GcdTypeminOverflow : Prop := ∀ t : IntTy, t.signed = true →
  overflowError (gcd_BitInteger (JuliaLean.base.int.typemin t) (JuliaLean.base.int.typemin t))

def LcmExact : Prop := ∀ (t : IntTy) (a b : JInt t),
  ExactOrOverflow (lcmBits a b) (lcmMath a.val b.val)

def LcmGenericExact : Prop := ∀ a b : Int,
  lcm_Integer bigOps (gcd_Integer bigOps) a b = .ok (lcmMath a b)

def MixedLcmRepresentable : Prop := ∀ (s t : IntTy) (a : JInt s) (b : JInt t),
  fits (s.promote t) (lcmMath a.val b.val) →
  ∃ r, lcmMixedBits a b = .ok r ∧ r.val = lcmMath a.val b.val

def MixedGcdRepresentable : Prop := ∀ (s t : IntTy) (a : JInt s) (b : JInt t),
  fits (s.promote t) (gcdMath a.val b.val) →
  ∃ r, gcdMixedBits a b = .ok r ∧ r.val = gcdMath a.val b.val

private def gcdArrayExpected (t : IntTy) : Nat → List (JInt t) → Jl (JInt t)
  | g, [] => .ok (JuliaLean.base.int.lit t (g : Int))
  | g, x :: xs =>
      let next := Nat.gcd g x.val.natAbs
      if fits t (next : Int) then
        if next = 1 then .ok (JuliaLean.base.int.lit t 1)
        else gcdArrayExpected t next xs
      else .error (.overflowError "")

private def lcmArrayMath : List Int → Int
  | [] => 1
  | x :: xs => xs.foldl (fun acc next => lcmMath acc next) x.natAbs
def GcdArrayRepresentable : Prop := ∀ (t : IntTy) (xs : List (JInt t)),
  gcd_Array_Integer (bitsOps t) gcd_BitInteger xs = gcdArrayExpected t 0 xs

def GcdArrayRealExact : Prop := ∀ (xs : List Int)
    (reduce : ArrayReduceCallees (List Int) Int),
  (∀ ys init, reduce.withInit (gcd_Integer bigOps) ys init =
    .ok (ys.foldl gcdMath init)) →
  gcd_Array_Real ⟨reduce, gcd_Integer bigOps, 0⟩ xs =
    .ok (xs.foldl gcdMath 0)
def GcdUnaryExact : Prop := ∀ (t : IntTy) (x : JInt t),
  ExactOrOverflow (gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits x) (x.val.natAbs : Int) ∧
  ExactOrOverflow (lcm_Unary (gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits) x) (x.val.natAbs : Int)

def AbsDifferenceExact : Prop :=
  (∀ (t : IntTy) (x y : JInt t), t.signed = false →
    (absdiff_Unsigned maxBits minBits JuliaLean.base.int.sub x y).1.val = ((x.val - y.val).natAbs : Int)) ∧
  (∀ (t : IntTy) (x y : JInt t), t.signed = true → fits t (x.val - y.val) →
    fits t ((x.val - y.val).natAbs : Int) →
    (absdiff_Signed JuliaLean.base.int.sub JuliaLean.base.int.abs x y).1.val = ((x.val - y.val).natAbs : Int))

def BinaryGcdExact : Prop := ∀ (t : IntTy) (a b : JInt t) (nonzero : b.val ≠ 0)
    (firstNotMin : t.signed = true → a.val ≠ t.min),
  (binaryGcd a b nonzero firstNotMin).val = gcdMath a.val b.val

/-! ## Extended gcd and inverses -/

def GcdxBezout : Prop := ∀ (t : IntTy) (a b : JInt t),
  if fits t (gcdMath a.val b.val) then
    ∃ d u v, gcdxBits a b = .ok (d, u, v) ∧
      d.val = gcdMath a.val b.val ∧
      (if t.signed then a.val * u.val + b.val * v.val = d.val
       else (a.val * u.val + b.val * v.val - d.val) % (2 ^ t.bits : Int) = 0) ∧
      ((a.val = 0 ∧ b.val = 0) → d.val = 0 ∧ u.val = 0 ∧ v.val = 0)
  else domainError (gcdxBits a b)

def GcdxStrictBounds : Prop := ∀ (t : IntTy) (a b : JInt t),
  t.signed = true → a.val ≠ 0 → b.val ≠ 0 →
  if fits t (gcdMath a.val b.val) then
    ∃ d u v, gcdxBits a b = .ok (d, u, v) ∧
      u.val * a.val + v.val * b.val = d.val ∧
      u.val.natAbs < (b.val.tdiv d.val).natAbs ∧
      v.val.natAbs < (a.val.tdiv d.val).natAbs
  else domainError (gcdxBits a b)

def GcdxUnrepresentable : Prop := ∀ (t : IntTy) (a b : JInt t),
  ¬ fits t (gcdMath a.val b.val) → domainError (gcdxBits a b)

def GcdxNaryBezout : Prop := ∀ (t : IntTy) (a b : JInt t) (cs : List (JInt t)),
  let args := a :: b :: cs
  let prefixesFit := ∀ (k : Nat), 2 ≤ k → k ≤ args.length →
    fits t (((args.take k).foldl (fun (g : Nat) x => Nat.gcd g x.val.natAbs) 0 : Nat) : Int)
  let computation :=
    gcdx_Nary gcdxBits
      (gcdx_Unary (gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits)
        (fun x => decide (x.val < 0)) (fun _ => JuliaLean.base.int.lit t 1) JuliaLean.base.int.neg)
      JuliaLean.base.int.mul a b cs
  (prefixesFit →
    ∃ (d u v : JInt t) (rest : List (JInt t)),
      computation = .ok (d, u, v, rest) ∧
      let us := u :: v :: rest
      us.length = cs.length + 2 ∧
      d.val = ((args.foldl (fun (g : Nat) x => Nat.gcd g x.val.natAbs) 0 : Nat) : Int) ∧
      (let total := (args.zip us).foldl (fun z pair => z + pair.1.val * pair.2.val) 0
       if t.signed then total = d.val else (total - d.val) % (2 ^ t.bits : Int) = 0)) ∧
    (¬ prefixesFit → domainError computation)

def InvmodAllWidths : Prop := ∀ c : NumberCallees, NumberLaws c →
  ∀ (s t : IntTy) (n : JInt s) (m : JInt t), InverseResult n.val m.val (invmodBits c n m)

def RingInverseUnsigned : Prop := ∀ (t : IntTy) (n : JInt t), t.signed = false →
  if n.val % 2 = 0 then domainError (invmod_Ring n)
  else ∃ y, invmod_Ring n = .ok y ∧ (JuliaLean.base.int.mul n y).val = 1

def RingInverseSigned : Prop := ∀ (t : IntTy) (n : JInt t), t.signed = true →
  if n.val % 2 = 0 then domainError (invmod_Ring n)
  else ∃ y, invmod_Ring n = .ok y ∧ (JuliaLean.base.int.mul n y).val = 1

def RingInverseType : Prop := ∀ (s t : IntTy) (n : JInt s),
  if n.val % 2 = 0 then domainError (invmod_Type (JuliaLean.base.int.remT t) invmod_Ring n)
  else ∃ y, invmod_Type (JuliaLean.base.int.remT t) invmod_Ring n = .ok y ∧
    (n.val * y.val - 1) % (2 ^ t.bits : Int) = 0

/-! ## Powers and powers of two -/

def IntegerPowerExact : Prop := ∀ (t e : IntTy) (x : JInt t) (p : JInt e), 0 ≤ p.val →
  ∃ y, powerBits x p = .ok y ∧ y.val = wrapInt t (x.val ^ p.val.toNat)

def IntegerPowerNegative : Prop := ∀ (t e : IntTy) (x : JInt t) (p : JInt e), p.val < 0 →
  if x.val = 1 ∨ (JuliaLean.base.int.neg x).val = 1 then
    ∃ y, powerBits x p = .ok y ∧ y.val = if p.val % 2 = 0 then 1 else x.val
  else domainError (powerBits x p)

def BigIntegerPowerExact : Prop := ∀ x p : Int, 0 ≤ p → powerBig x p = .ok (x ^ p.toNat)

def BoolPowerExact : Prop := ∀ (e : IntTy) (x : Bool) (p : JInt e),
  if p.val < 0 ∧ x = false then domainError (powerBool_Integer Subtype.val x p)
  else ∃ result, powerBool_Integer Subtype.val x p = .ok result ∧
    result = (List.range p.val.toNat).foldl (fun acc _ => acc && x) true

def LiteralPowerExact : Prop := ∀ (t : IntTy) (x : JInt t),
  (literalPow_Zero (fun _ => JuliaLean.base.int.lit t 1) x).val = 1 ∧
  (literalPow_One x).val = x.val ∧
  (literalPow_Two (fun x y => pure (JuliaLean.base.int.mul x y)) x).map Subtype.val =
    .ok (wrapInt t (x.val ^ 2)) ∧
  (literalPow_Three (fun x y => pure (JuliaLean.base.int.mul x y)) x).map Subtype.val =
    .ok (wrapInt t (x.val ^ 3))

def PowermodNonnegative : Prop := ∀ c : NumberCallees, NumberLaws c →
  ∀ (s e t : IntTy) (x : JInt s) (p : JInt e) (m : JInt t), 0 ≤ p.val → m.val ≠ 0 →
  ∃ y, powermodBits c x p m = .ok y ∧ y.val = x.val ^ p.val.toNat % m.val

def PowermodNegative : Prop := ∀ c : NumberCallees, NumberLaws c →
  ∀ (s e t : IntTy) (x : JInt s) (p : JInt e) (m : JInt t), p.val < 0 → m.val ≠ 0 → gcdMath x.val m.val = 1 →
  ∃ y, powermodBits c x p m = .ok y ∧ ModularPower x.val p.val m.val y.val

def PowermodTypeminResidue : Prop := ∀ c : NumberCallees, NumberLaws c →
  ∀ (t : IntTy) (x : JInt t), t.signed = true → x.val % 2 ≠ 0 →
  (powermodBits c x (JuliaLean.base.int.typemin t) (JuliaLean.base.int.typemin t)).map Subtype.val = .ok (t.min + 1)

def PowermodZeroModulus : Prop := ∀ c : NumberCallees, NumberLaws c →
  ∀ (s e t : IntTy) (x : JInt s) (p : JInt e), 0 ≤ p.val →
  divideError (powermodBits c x p (JuliaLean.base.int.lit t 0))

def IsPowerTwoExact : Prop := ∀ (t : IntTy) (x : JInt t),
  ispow2Bits x = true ↔ ∃ k : Nat, x.val = (2 : Int) ^ k

def NextpowLowerBound : Prop := ∀ (t : IntTy) (log : JInt .i64 → JInt t → Jl Int)
    (x : JInt t) (r : Int), 0 < x.val →
  nextpowBits log (JuliaLean.base.int.lit .i64 2) x = .ok r → x.val ≤ r

def PrevpowTwoExact : Prop := ∀ (t : IntTy) (x : JInt t), 1 ≤ x.val →
  ∃ k : Nat, (prevpow2Bits x).val = (2 : Int) ^ k ∧
    (prevpow2Bits x).val ≤ x.val ∧ x.val < 2 * (prevpow2Bits x).val

/-- The ceiling-log callee is permitted its documented last-bit rounding error. -/
def CeilLogLaw {a x : IntTy} (log : JInt a → JInt x → Jl Int) : Prop :=
  ∀ (base : JInt a) (input : JInt x) (k : Nat), base.val > 1 → input.val > 1 →
    (∀ j : Nat, j < k → base.val ^ j < input.val) → input.val ≤ base.val ^ k →
    ∃ n, log base input = .ok n ∧ 1 ≤ n ∧ (n = (k : Int) - 1 ∨ n = k ∨ n = (k : Int) + 1)

def NextpowExact : Prop := ∀ (a x : IntTy) (log : JInt a → JInt x → Jl Int), CeilLogLaw log →
  ∀ (base : JInt a) (input : JInt x),
  if input.val ≤ 0 ∨ base.val ≤ 1 then domainError (nextpowBits log base input)
  else if base.val ≠ 2 ∧ input.val > a.max then domainError (nextpowBits log base input)
  else
    ((∃ k : Nat, fits (if base.val = 2 then x else a) (base.val ^ k) ∧ input.val ≤ base.val ^ k) →
      ∃ y k, nextpowBits log base input = .ok y ∧ y = base.val ^ k ∧ input.val ≤ y ∧
        ∀ j : Nat, j < k → base.val ^ j < input.val) ∧
    ((¬ ∃ k : Nat, fits (if base.val = 2 then x else a) (base.val ^ k) ∧ input.val ≤ base.val ^ k) →
      overflowError (nextpowBits log base input))


/-! ## Digit counts, extraction, formatting, and bit representations -/

def NegativeBaseTypeminBehavior : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ b : IntTy, b.signed = true → ∀ x : JInt b.toUnsigned,
  0 < x.val → x.val ≤ -(JuliaLean.base.int.typemin b).val →
  ndigitsZeroBits c x (JuliaLean.base.int.typemin b) = .ok (JuliaLean.base.int.lit .i64 2) ∧
  ndigitsBits c x (JuliaLean.base.int.typemin b) (JuliaLean.base.int.lit .i64 1) = .ok 2

def SignedTypeminBaseBehavior : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (b p : IntTy) (x : JInt b) (pad : JInt p), b.signed = true →
  let count : Int := if x.val < 0 then 2 else if x.val = 0 then 0 else 1
  ndigitsZeroBits c x (JuliaLean.base.int.typemin b) = .ok (JuliaLean.base.int.lit .i64 count) ∧
  ndigitsBits c x (JuliaLean.base.int.typemin b) pad = .ok (max pad.val count)

def LargeBaseSingleDigit : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t b : IntTy) (x : JInt t) (base : JInt b),
  base.val > 1 → 0 < x.val → x.val < base.val →
  if fits .i64 base.val then
    ndigitsZeroBits c x base = .ok (JuliaLean.base.int.lit .i64 1)
  else inexactError (ndigitsZeroBits c x base)

def NdigitsExact : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t b p : IntTy) (x : JInt t) (base : JInt b) (pad : JInt p),
  ((base.val < -1 ∧ (b.signed = false ∨ base.val ≠ b.min)) ∨
    (base.val > 1 ∧ fits .i64 base.val)) →
  ∃ count, ndigitsBits c x base pad = .ok count ∧ DigitCount x.val base.val pad.val count

def NdigitsZeroAndDomain : Prop := ∀ c : DigitCallees,
  ∀ (t b p : IntTy) (base : JInt b) (pad : JInt p) (x : JInt t),
  ((-1 ≤ base.val ∧ base.val ≤ 1) → domainError (ndigitsZeroBits c x base)) ∧
  ((-1 ≤ base.val ∧ base.val ≤ 1) → domainError (ndigitsBits c x base pad)) ∧
  ((base.val < -1 ∨ base.val > 1) →
    ndigitsZeroBits c (JuliaLean.base.int.lit t 0) base = .ok (JuliaLean.base.int.lit .i64 0)) ∧
  ((base.val < -1 ∨ base.val > 1) →
    ndigitsBits c (JuliaLean.base.int.lit t 0) base pad = .ok (max pad.val 0)) ∧
  ((base.val > 1 ∧ ¬ fits .i64 base.val ∧ x.val ≠ 0) →
    inexactError (ndigitsBits c x base pad)) ∧
  ((base.val > 1 ∧ ¬ fits .i64 base.val ∧ x.val = 0) →
    ndigitsBits c x base pad = .ok (max pad.val 0))

def DigitsRoundtrip : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t b p : IntTy) (n : JInt t) (base : JInt b) (pad : JInt p),
  (base.val < -1 ∨ base.val > 1) →
  if base.val > 1 ∧ ¬ fits .i64 base.val ∧ n.val ≠ 0 then
    inexactError (digitsBits c b n base pad)
  else if pad.val > IntTy.max .i64 then inexactError (digitsBits c b n base pad)
  else if b.signed = true ∧ base.val = b.min then domainError (digitsBits c b n base pad)
  else ∃ a, digitsBits c b n base pad = .ok a ∧ evalpoly base.val (a.values.map Subtype.val) = n.val ∧
    DigitCount n.val base.val pad.val a.values.length ∧ DigitRange n.val base.val (a.values.map Subtype.val)

def DigitsFillLowOrder : Prop := ∀ (t b e : IntTy) (n : JInt t) (base : JInt b)
    (before after : Vector (JInt e)), digitsBangBits before n base = .ok after →
  after.first = before.first ∧ after.values.length = before.values.length ∧
  (∃ q : Int, evalpoly base.val (after.values.map Subtype.val) + base.val ^ before.values.length * q = n.val) ∧
  DigitRange n.val base.val (after.values.map Subtype.val)

def DigitsValidBase : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t : IntTy) (n : JInt t) (base : JInt .i64),
  (base.val ≤ -2 ∨ base.val ≥ 2) →
  if base.val = IntTy.min .i64 then domainError (digitsBits c .i64 n base (JuliaLean.base.int.lit .i64 1))
  else ∃ a, digitsBits c .i64 n base (JuliaLean.base.int.lit .i64 1) = .ok a ∧
    evalpoly base.val (a.values.map Subtype.val) = n.val
def DigitsErrors : Prop := ∀ (t b e : IntTy) (n : JInt t) (base : JInt b)
    (a : Vector (JInt e)),
  (((-1 ≤ base.val ∧ base.val ≤ 1) ∨
    (b.signed = true ∧ base.val = b.min)) → domainError (digitsBangBits a n base)) ∧
  ((b.signed = false ∨ base.val ≠ b.min) →
    (((base.val.natAbs : Int) - 1 > e.max ∧ 2 ≤ (base.val.natAbs : Int)) →
      argumentError (digitsBangBits a n base)))

def StringRoundtrip : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t b p : IntTy) (n : JInt t) (base : JInt b) (pad : JInt p), 2 ≤ base.val → base.val ≤ 62 →
  let effectivePad := min (max pad.val (IntTy.min .i64)) (IntTy.max .i64)
  if n.val < 0 ∧ effectivePad = IntTy.max .i64 then inexactError (stringBits c n base pad)
  else ∃ s, stringBits c n base pad = .ok s ∧
    StringRepresentation n.val base.val effectivePad s.bytes

def StringNegativeBase : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t b p : IntTy) (n : JInt t) (base : JInt b) (pad : JInt p),
  -62 ≤ base.val → base.val ≤ -2 →
  let effectivePad := min (max pad.val (IntTy.min .i64)) (IntTy.max .i64)
  if fits t.toSigned n.val then
    ∃ s, stringBits c n base pad = .ok s ∧
      StringRepresentation n.val base.val effectivePad s.bytes
  else stringBits c n base pad = .error (.inexactError t.toSigned.name)

def FormattingWriterResult (result : Jl Buffer) (value base pad : Int) (neg : Bool) : Prop :=
  if neg = true ∧ pad = IntTy.max .i64 then inexactError result
  else ∃ s, result = .ok s ∧ StringRepresentation value base pad s.bytes
def BaseStringPositive : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t b : IntTy) (n : JInt t) (base : JInt b) (pad : JInt64) (neg : Bool),
  2 ≤ base.val → base.val ≤ 62 → 0 ≤ n.val → (neg = false ∨ 0 < n.val) →
  FormattingWriterResult (formatBase c base n pad neg)
    (if neg then -n.val else n.val) base.val pad.val neg

def BitstringExact : Prop := ∀ (t : IntTy) (x : JInt t), ∃ s,
  bitstringBits x = .ok s ∧ s.bytes.length = t.bits ∧
  (∀ j : Nat, j < t.bits → s.bytes[j]? = some (if (x.val % (2 ^ t.bits : Int)).toNat.testBit (t.bits - 1 - j) then 49 else 48))

def FormattingMemorySafe : Prop :=
  (∀ c : DigitCallees, QuotientLaws c →
    ∀ (t b p : IntTy) (n : JInt t) (base : JInt b) (pad : JInt p),
    2 ≤ base.val → base.val ≤ 62 →
    ∃ s, stringBits c n base pad = .ok s ∧ BufferSafe s) ∧
  (∀ c : DigitCallees, QuotientLaws c →
    ∀ (t b p : IntTy) (n : JInt t) (base : JInt b) (pad : JInt p),
    -62 ≤ base.val → base.val ≤ -2 → fits t.toSigned n.val →
    ∃ s, stringBits c n base pad = .ok s ∧ BufferSafe s) ∧
  (∀ (t : IntTy) (n : JInt t) (s : Buffer),
    bitstringBits n = .ok s → BufferSafe s)

private def decodeBoolString : String → Option Bool
  | "true" => some true
  | "false" => some false
  | _ => none

def BoolStrings : Prop := ∀ b : Bool,
  decodeBoolString (string_Bool b) = some b ∧
    ∀ b', string_Bool b = string_Bool b' → b = b'

/-! ## Square roots, factorials, binomial coefficients, and clamping -/

def SqrtLaw (sqrt : {t : IntTy} → JInt t → Jl (JuliaLean.base.float.FV .f64)) : Prop :=
  ∀ (t : IntTy) (x : JInt t),
    (x.val < 0 → domainError (sqrt x)) ∧
    (0 ≤ x.val → sqrt x = .ok (JuliaLean.C.jlSqrtLlvm (JuliaLean.base.float.floatOfInt .f64 x)))

def IsqrtFloor : Prop := ∀ sqrt, SqrtLaw sqrt → ∀ (t : IntTy) (x : JInt t),
  if x.val < 0 then domainError (isqrtBits sqrt x)
  else ∃ r, isqrtBits sqrt x = .ok r ∧ r.val ≥ 0 ∧
    r.val * r.val ≤ x.val ∧ x.val < (r.val + 1) * (r.val + 1)

def FactorialFallbackNoOverflow : Prop := ∀ (t : IntTy) (n : JInt t),
  (n.val < 0 → domainError (factorialFallbackBits n)) ∧
  (0 ≤ n.val → fits t (factorialMath n.val.toNat : Int) →
    ∃ r, factorialFallbackBits n = .ok r ∧ r.val = (factorialMath n.val.toNat : Int))

def FactorialGenericBig : Prop := ∀ n : Int,
  if n < 0 then domainError (factorial_Integer id pure (fun x y => pure (x * y)) n)
  else factorial_Integer id pure (fun x y => pure (x * y)) n = .ok (factorialMath n.toNat : Int)

def BinomialExactAndOverflow : Prop := ∀ (t : IntTy) (n k : JInt t),
  ExactOrOverflow (binomialBits n k) (binomialMath n.val k.val)

def BinomialNonnegativeEdges : Prop := ∀ (t : IntTy) (n k : JInt t), 0 ≤ n.val →
  (k.val < 0 → (binomialBits n k).map Subtype.val = .ok 0) ∧
  (n.val < k.val → (binomialBits n k).map Subtype.val = .ok 0) ∧
  (k.val = 0 → (binomialBits n k).map Subtype.val = .ok 1)
def BinomialMixedExact : Prop := ∀ (s k : IntTy) (n : JInt s) (r : JInt k),
  match promoteBits n r with
  | .error e => binomialMixedBits n r = .error e
  | .ok (n', r') =>
      n'.val = n.val ∧ r'.val = r.val ∧
      ExactOrOverflow (binomialMixedBits n r) (binomialMath n.val r.val)

structure ClampOrderOps (X L H O T : Type) where
  projectX : X → O
  projectLo : L → O
  projectHi : H → O
  lt : O → O → Prop
  less : O → O → Bool
  lessSpec : ∀ x y, less x y = true ↔ lt x y
  irrefl : ∀ x, ¬ lt x x
  transitive : ∀ x y z, lt x y → lt y z → lt x z
  total : ∀ x y, lt x y ∨ x = y ∨ lt y x
  convertX : X → Jl T
  convertLo : L → Jl T
  convertHi : H → Jl T

def ClampExact : Prop := ∀ (X L H O T : Type)
    (order : ClampOrderOps X L H O T) (x : X) (lo : L) (hi : H),
  clamp (fun x hi => order.less (order.projectHi hi) (order.projectX x))
    (fun x lo => order.less (order.projectX x) (order.projectLo lo))
    order.convertX order.convertLo order.convertHi x lo hi =
      if order.less (order.projectHi hi) (order.projectX x) then order.convertHi hi
      else if order.less (order.projectX x) (order.projectLo lo) then order.convertLo lo
      else order.convertX x


def ClampTypeExact : Prop := ∀ (t : IntTy) (X : Type)
    (gt : X → JInt t → Bool) (lt : X → JInt t → Bool)
    (convert : X → Jl (JInt t)) (x : X),
  clamp_Type (JuliaLean.base.int.typemin t) (JuliaLean.base.int.typemax t)
    gt lt convert x =
      if gt x (JuliaLean.base.int.typemax t) then .ok (JuliaLean.base.int.typemax t)
      else if lt x (JuliaLean.base.int.typemin t) then .ok (JuliaLean.base.int.typemin t)
      else convert x

def ClampBangExact : Prop := ∀ {A Axis Index V L H : Type} [DecidableEq Index]
    (index : JuliaLean.base.arraymath.ArrayIndexOps Id A Axis)
    (eachindex : JuliaLean.base.arraymath.ArrayIndexOps Id A Axis → A → Jl (List Index))
    (getindex : A → Index → Jl V) (setindex : A → Index → V → Jl A)
    (clamp : V → L → H → Jl V) (x : A) (lo : L) (hi : H)
    (indices : List Index),
  eachindex index x = .ok indices →
  indices.Nodup →
  (∀ v, ∃ clamped, clamp v lo hi = .ok clamped) →
  (∀ a i, i ∈ indices → ∃ value, getindex a i = .ok value) →
  (∀ a i v, i ∈ indices → ∃ updated, setindex a i v = .ok updated) →
  (∀ a i v updated, i ∈ indices → setindex a i v = .ok updated →
    index.axes updated = index.axes a ∧
    getindex updated i = .ok v ∧
    ∀ j, j ≠ i → getindex updated j = getindex a j) →
  ∃ y, clampBang index eachindex getindex setindex clamp x lo hi = .ok y ∧
    index.axes y = index.axes x ∧
    (∀ i, i ∈ indices →
      ∃ value clamped, getindex x i = .ok value ∧
        clamp value lo hi = .ok clamped ∧ getindex y i = .ok clamped) ∧
    (∀ i, i ∉ indices → getindex y i = getindex x i)

def GcdLcmNaryExact : Prop :=
  (∀ xs : List Int, ∀ a b : Int,
    gcd_Nary (gcd_Integer bigOps) (gcd_Unary_Integer bigOps.checkedAbs) a b xs =
      .ok ((a :: b :: xs).foldl gcdMath 0)) ∧
  (∀ xs : List Int, ∀ a b : Int,
    lcm_Nary (lcm_Integer bigOps (gcd_Integer bigOps))
      (lcm_Unary (gcd_Unary_Integer bigOps.checkedAbs)) a b xs =
      .ok ((a :: b :: xs).foldl lcmMath 1))

def LcmArrayExact : Prop := ∀ (t : IntTy) (xs : List (JInt t))
    (reduce : ArrayReduceCallees (List (JInt t)) (JInt t)),
  (∀ ys, 2 ≤ ys.length →
    ExactOrOverflow (reduce.withoutInit lcmBits ys) (lcmArrayMath (ys.map Subtype.val))) →
  ExactOrOverflow
    (lcm_Array_Real
      ({ length := List.length
         isInteger := true
         one := JuliaLean.base.int.lit t 1
         elementType := "Integer"
         abs := JuliaLean.base.checked.checkedAbsBits
         only := fun ys => match ys with | [x] => .ok x | _ => .error .boundsError
         reduce := reduce
         lcm := lcmBits } : LcmArrayCallees (List (JInt t)) (JInt t)) xs)
    (lcmArrayMath (xs.map Subtype.val))

def LcmArrayRealSemantics : Prop := ∀ (A R : Type)
    (c : LcmArrayCallees A R) (xs : A),
  lcm_Array_Real c xs =
    if c.length xs = 0 then
      if c.isInteger then .ok c.one else .error (.argumentError ("lcm has no identity for " ++ c.elementType))
    else if c.length xs = 1 then (c.only xs).bind c.abs
    else c.reduce.withoutInit c.lcm xs

def RationalUnaryGcd : Prop := ∀ (R : Type) (num den : R → Int)
    (ratio : Int → Int → Jl R),
  (∀ n d : Int, 0 < d → ∃ r, ratio n d = .ok r ∧ 0 < den r ∧ num r * d = n * den r) →
  ∀ a : R, 0 < den a → ∃ r,
    gcd_Unary_Rational num den bigOps.checkedAbs ratio a = .ok r ∧
    num r * den a = (num a).natAbs * den r ∧ 0 ≤ num r ∧ 0 < den r

def BezoutUpdateRing : Prop := ∀ (t : IntTy) (s0 q s1 : JInt t),
  (gcdxUpdate_Unsigned JuliaLean.base.int.subWrap JuliaLean.base.int.mulWrap s0 q s1).val =
    wrapInt t (s0.val - q.val * s1.val) ∧
  (gcdxUpdate JuliaLean.base.int.sub JuliaLean.base.int.mul s0 q s1).val =
    wrapInt t (s0.val - q.val * s1.val)

def BezoutCoefficient : Prop := ∀ (t : IntTy) (n m : JInt t),
  if gcdMath n.val m.val = 1 then
    ∃ x, bezoutCoef gcdxBits (fun g => decide (g.val = 1)) n m = .ok x ∧
      (n.val * x.val - 1) % m.val = 0
  else domainError (bezoutCoef gcdxBits (fun g => decide (g.val = 1)) n m)


def NextpowSeedCorrection : Prop := NextpowExact ∧
  ∀ (a x : IntTy) (log : JInt a → JInt x → Jl Int)
    (base : JInt a) (input : JInt x) (n : Int) (k : Nat),
  base.val > 2 → input.val > 1 → input.val ≤ a.max → n > 0 →
  log base input = .ok n →
  (n + 1 = (k : Int) ∨ n = k ∨ n = (k : Int) + 1) →
  (∀ j : Nat, j < k → base.val ^ j < input.val) → input.val ≤ base.val ^ k →
  (∀ j ∈ [n - 1, n, n + 1], fits a (base.val ^ j.toNat)) →
  nextpowBits log base input = .ok (base.val ^ k)

def FloorLogLaw {a x : IntTy} (log : JInt a → JInt x → Jl Int) : Prop :=
  ∀ (base : JInt a) (input : JInt x) (k : Nat), base.val > 1 → input.val ≥ 1 →
    base.val ^ k ≤ input.val → input.val < base.val ^ (k + 1) →
    ∃ n, log base input = .ok n ∧ 0 ≤ n ∧ (n = (k : Int) - 1 ∨ n = k ∨ n = (k : Int) + 1)

def PrevpowExact : Prop := ∀ (a x : IntTy) (log : JInt a → JInt x → Jl Int), FloorLogLaw log →
  ∀ (base : JInt a) (input : JInt x),
  if input.val < 1 ∨ base.val ≤ 1 then domainError (prevpowBits log base input)
  else if base.val ≠ 2 ∧ input.val > a.max then domainError (prevpowBits log base input)
  else ∃ y k, prevpowBits log base input = .ok y ∧ y = base.val ^ k ∧
    y ≤ input.val ∧ input.val < base.val ^ (k + 1)

private def floatPowerLe {A X : JuliaLean.base.float.FTy}
    (a : JuliaLean.base.float.FV A) (k : Nat) (x : JuliaLean.base.float.FV X) : Prop :=
  a.toRat.1 ^ k * (x.toRat.2 : Int) ≤ x.toRat.1 * (a.toRat.2 : Int) ^ k

def FloatLogLaw (log : JuliaLean.base.float.FV .f32 → JuliaLean.base.float.FV .f64 → Jl Int) : Prop :=
  ∀ a x k, a.isfinite = true → x.isfinite = true →
    JuliaLean.Promotion.Fl.lt (JuliaLean.Promotion.Fl.ofInt 1) a = true →
    JuliaLean.Promotion.Fl.le (JuliaLean.Promotion.Fl.ofInt 1) x = true →
    floatPowerLe a k x → ¬ floatPowerLe a (k + 1) x →
    ∃ n, log a x = .ok n ∧ 0 ≤ n ∧ (n = (k : Int) - 1 ∨ n = k ∨ n = (k : Int) + 1)

def PrevpowFloat32Bound : Prop := ∀ log, FloatLogLaw log →
  ∀ (a : JuliaLean.base.float.FV .f32) (x : JuliaLean.base.float.FV .f64),
  a.isfinite = true → x.isfinite = true →
  if JuliaLean.Promotion.Fl.le a (JuliaLean.base.float.one_float .f32) = true ∨
      JuliaLean.Promotion.Fl.lt x (JuliaLean.base.float.one_float .f64) = true ∨
      JuliaLean.Promotion.Fl.lt
        (JuliaLean.base.float.convertFloat .f64
          (JuliaLean.base.float.typemax_Float32)) x = true
  then domainError (prevpowFloat32 log a x)
  else ∃ r, prevpowFloat32 log a x = .ok r ∧
    JuliaLean.Promotion.Fl.le (JuliaLean.base.float.convertFloat .f64 r) x = true



def SplitSignExact : Prop := ∀ (t : IntTy) (n : JInt t),
  let pair := splitSign_Integer JuliaLean.base.int.abs JuliaLean.base.int.unsigned Subtype.val n
  pair.1.val = (n.val.natAbs : Int) ∧ (pair.2 = true ↔ n.val < 0)

def DecimalDigitCount : Prop := ∀ (t : IntTy) (n : JInt t), t.signed = false →
  ∃ count, decimalBits n = .ok count ∧ DigitCount n.val 10 0 count.val

def TopBitGeneric : Prop := ∀ n : Int, 0 ≤ n →
  if n = 0 then topSetBit_Integer (fun n => decide (n = 0))
    (fun n => pure ((n.natAbs.log2 : Int))) n = .ok 0
  else ∃ r, topSetBit_Integer (fun n => decide (n = 0))
    (fun n => pure ((n.natAbs.log2 : Int))) n = .ok r ∧
    1 ≤ r ∧ (2 : Int) ^ (r - 1).toNat ≤ n ∧ n < (2 : Int) ^ r.toNat

def FormattingWriters : Prop := ∀ c : DigitCallees, QuotientLaws c →
  ∀ (t : IntTy) (n : JInt t) (pad : JInt64) (neg : Bool),
  t.signed = false → (neg = false ∨ 0 < n.val) →
  let signedValue := if neg then -n.val else n.val
  (FormattingWriterResult (formatBin n pad neg) signedValue 2 pad.val neg) ∧
  (FormattingWriterResult (formatOct n pad neg) signedValue 8 pad.val neg) ∧
  (FormattingWriterResult (formatDec c n pad neg) signedValue 10 pad.val neg) ∧
  (FormattingWriterResult (formatHex n pad neg) signedValue 16 pad.val neg)

def DecimalAppendResult (n length pos : Int) (before : Buffer) (result : Jl (Buffer × JInt64)) : Prop :=
  ∃ after next, result = .ok (after, next) ∧
    next.val = pos + length ∧ after.bytes.length = before.bytes.length ∧
    decodeNumeral 10 ((after.bytes.drop (pos - 1).toNat).take length.toNat) = some n ∧
    (∀ i ∈ after.writes.drop before.writes.length, pos ≤ i ∧ i < pos + length) ∧
    (∀ j : Nat, j < before.bytes.length → ((j : Int) + 1 < pos ∨ pos + length ≤ (j : Int) + 1) →
      after.bytes[j]? = before.bytes[j]?)

def AppendDecimalDigits : Prop := ∀ (t : IntTy) (n : JInt t) (length pos : JInt64) (before : Buffer),
  t.signed = false → 0 ≤ length.val → 1 ≤ pos.val →
  pos.val + length.val - 1 ≤ before.bytes.length → (before.bytes.length : Int) ≤ IntTy.max .i64 →
  n.val < 10 ^ length.val.toNat →
  DecimalAppendResult n.val length.val pos.val before
    (appendCDigits Subtype.val unsignedDivrem length n before pos)

private def numeratorProduct (n d : Int) (k : Nat) : Int :=
  ((List.range k).map (fun (j : Nat) => n - (j : Int) * d)).foldl Int.mul 1

structure GeneralizedBinomialOps (N I : Type) where
  num : N → Int
  den : N → Int
  callees : BinomialNumberCallees N I N

def GeneralizedBinomialPolynomial : Prop := ∀ (N I : Type)
    (ops : GeneralizedBinomialOps N I),
  (∀ x, 0 < ops.den x) →
  (∀ x, ops.num (ops.callees.zero x) = 0 ∧
    ops.num (ops.callees.oneunit x) = ops.den (ops.callees.oneunit x)) →
  (∀ i, ops.callees.value (ops.callees.one i) = 1) →
  (∀ x j, ops.num (ops.callees.subIndex x j) * ops.den x =
    (ops.num x - j * ops.den x) * ops.den (ops.callees.subIndex x j)) →
  (∀ x i, 0 < ops.callees.value i →
    ∃ r, ops.callees.div x i = .ok r ∧
      ops.num r * (ops.den x * ops.callees.value i) = ops.num x * ops.den r) →
  (∀ x k, ops.callees.value k < 0 →
    ∃ r, ops.callees.div (ops.callees.zero x) (ops.callees.one k) = .ok r ∧ ops.num r = 0) →
  (∀ x k init, 0 ≤ ops.callees.value k →
    ops.callees.div (ops.callees.oneunit x) (ops.callees.one k) = .ok init →
    ∃ r, ops.callees.prod
      (fun i => ops.callees.div (ops.callees.subIndex x (ops.callees.value i - 1)) i)
      (ops.callees.oneTo k) init = .ok r ∧
        ops.num r * ((factorialMath (ops.callees.value k).toNat : Int) *
          ops.den x ^ (ops.callees.value k).toNat) =
          numeratorProduct (ops.num x) (ops.den x) (ops.callees.value k).toNat * ops.den r) →
  ∀ x k,
    if ops.callees.value k < 0 then
      ∃ r, binomial_Number ops.callees x k = .ok r ∧ ops.num r = 0
    else
      ∃ r, binomial_Number ops.callees x k = .ok r ∧
        ops.num r * ((factorialMath (ops.callees.value k).toNat : Int) *
          ops.den x ^ (ops.callees.value k).toNat) =
          numeratorProduct (ops.num x) (ops.den x) (ops.callees.value k).toNat * ops.den r

def GcdxUnaryBezout : Prop := ∀ (t : IntTy) (a : JInt t),
  fits t (a.val.natAbs : Int) → ∃ d u,
    gcdx_Unary (gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits)
      (fun x => decide (x.val < 0)) (fun _ => JuliaLean.base.int.lit t 1)
      JuliaLean.base.int.neg a = .ok (d, u) ∧
    d.val = (a.val.natAbs : Int) ∧
    (if t.signed then a.val * u.val = d.val else (a.val * u.val - d.val) % (2 ^ t.bits : Int) = 0)

def GcdxMixedBezout : Prop := ∀ (s t : IntTy) (a : JInt s) (b : JInt t),
  fits (s.promote t) (gcdMath a.val b.val) → ∃ d u v,
    gcdxMixedBits a b = .ok (d, u, v) ∧ d.val = gcdMath a.val b.val ∧
    (if (s.promote t).signed then a.val * u.val + b.val * v.val = d.val
     else (a.val * u.val + b.val * v.val - d.val) % (2 ^ (s.promote t).bits : Int) = 0)

def BoolUnsignedPower : Prop := ∀ (t : IntTy) (x : Bool) (p : JInt t),
  t.signed = false →
  powerBool_Unsigned (fun p => decide (p.val = 0)) x p =
    (List.range p.val.toNat).foldl (fun acc _ => acc && x) true

def LiteralInverseSquare : Prop := ∀ (N : Type) (num den : N → Int)
    (inv : N → Jl N) (mul : N → N → Jl N),
  (∀ x, 0 < den x) →
  (∀ x, num x ≠ 0 → ∃ r, inv x = .ok r ∧ num r * num x = den r * den x) →
  (∀ x y, ∃ r, mul x y = .ok r ∧ num r * (den x * den y) = num x * num y * den r) →
  ∀ x, num x ≠ 0 → ∃ r,
    literalPow_NegTwo inv mul x = .ok r ∧ num r * num x ^ 2 = den r * den x ^ 2

def ModularOptimizationSafe : Prop := ∀ (t : IntTy) (m : JInt t), t.signed = false → 0 < m.val →
  powermodMILegal_Unsigned (hasTypeMax true true) (JuliaLean.base.int.typemax t)
    (fun x y => decide (x.val ≤ y.val))
    (fun x n => JuliaLean.base.int.lshr_int x (JuliaLean.base.int.lit .i64 n)) (t.bits / 8) m = true →
  ∀ a b : Int, 0 ≤ a → a < m.val → 0 ≤ b → b < m.val → fits t (a * b)

def BoolDigitCounts : Prop := ∀ (B : Type) (baseValue : B → Int)
    (x : Bool) (base : B),
  ((baseValue base > 1) →
    DigitCount (if x then 1 else 0) (baseValue base) 0
      (ndigitsPositive_Bool x base).val) ∧
  ((baseValue base < -1) →
    DigitCount (if x then 1 else 0) (baseValue base) 0
      (ndigitsNegative_Bool x base).val)

def HasTypeMaxSpec : Prop :=
  (∀ maxApplicable minApplicable : Bool,
    hasTypeMax maxApplicable minApplicable = true ↔
      maxApplicable = true ∧ minApplicable = true) ∧
  hasTypeMax_Bottom = false ∧
  (∀ (Tail R : Type) (slurp : Tail),
    hasTypeMax_Bottom_Extra (Tail := Tail) (R := R) slurp = (.error (.methodError "hastypemax") : Jl R))

def DecimalInputDigitCount : Prop := ∀ (t : IntTy) (x : JInt t),
  ∃ count,
    (if t.signed then
      ndigitsDecimal_Signed JuliaLean.base.int.abs JuliaLean.base.int.unsigned decimalBits x
     else ndigitsDecimal_Unsigned decimalBits x) = .ok count ∧
    DigitCount x.val 10 0 count.val

def DefaultDecimalGeneric : Prop := ∀ (I B X : Type) (value : I → Int)
    (baseValue : B → Int) (toInt : B → Jl JInt64) (abs : I → I)
    (isBitInteger : Bool) (unsigned lift : I → X) (xvalue : X → Int)
    (topBit leadingZeros bytes : X → Nat) (decimal : X → Jl JInt64)
    (div : X → JInt64 → Jl X) (ispow2 : JInt64 → Bool)
    (trailingZeros : JInt64 → Nat) (ten : B),
  baseValue ten = 10 →
  (∀ x, ∃ count,
    ndigitsPositive value toInt abs isBitInteger unsigned lift xvalue
      topBit leadingZeros bytes decimal div ispow2 trailingZeros x ten = .ok count ∧
      DigitCount (value x) 10 0 count.val) ∧
  (∀ x, ∃ count,
    ndigitsDecimal_Integer ten
      (ndigitsPositive value toInt abs isBitInteger unsigned lift xvalue
        topBit leadingZeros bytes decimal div ispow2 trailingZeros) x = .ok count ∧
      DigitCount (value x) 10 0 count.val)

def AppendNineDigitsSpec : Prop := ∀ (t : IntTy) (n : JInt t) (pos : JInt64) (before : Buffer),
  t.signed = false → n.val < 10^9 → 1 ≤ pos.val →
  pos.val + 8 ≤ before.bytes.length → (before.bytes.length : Int) ≤ IntTy.max .i64 →
  DecimalAppendResult n.val 9 pos.val before
    (appendNineDigits Subtype.val (appendCDigits Subtype.val unsignedDivrem) n before pos)

def AppendFastSpec : Prop := ∀ (t : IntTy) (n : JInt t) (length pos : JInt64) (before : Buffer),
  t.signed = false → 0 ≤ length.val → n.val < 10 ^ length.val.toNat → 1 ≤ pos.val →
  pos.val + length.val - 1 ≤ before.bytes.length → (before.bytes.length : Int) ≤ IntTy.max .i64 →
  DecimalAppendResult n.val length.val pos.val before
    (appendCDigitsFast Subtype.val unsignedDivrem (JuliaLean.base.int.remT .u64)
      (appendCDigits Subtype.val unsignedDivrem)
      (appendNineDigits Subtype.val (appendCDigits Subtype.val unsignedDivrem)) length n before pos)

def FormattingMemorySafeFull : Prop :=
  FormattingMemorySafe ∧ AppendDecimalDigits ∧ AppendNineDigitsSpec ∧ AppendFastSpec

def PrimitiveBitstring : Prop := ∀ (A : Type) (bits : Nat) (pattern : A → Nat)
    (bitcast zext trunc : A → Nat) (shift : A → Nat → A),
  (∀ x, pattern x < 2 ^ bits) →
  (∀ x, (if bits = 8 then bitcast x else if bits < 8 then zext x else trunc x) = pattern x % 256) →
  (∀ x k, pattern (shift x k) = pattern x / 2^k) →
  ∀ x, ∃ s, bitstring true bits bitcast zext trunc shift x = .ok s ∧ s.bytes.length = bits ∧
    ∀ j : Nat, j < bits → s.bytes[j]? = some (if (pattern x).testBit (bits - 1 - j) then 49 else 48)


/-! Nothing to promise:
gcd@155, gcd@156, lcm@157, lcm@158: dispatch-only argument ordering and promotion.
gcd@159, lcm@160, gcdx@261: promotion followed by the corresponding arithmetic method.
gcd@166: forwards the array to reduce with the documented identity.
gcdx@282: swaps the two arguments and the two coefficients.
invmod@370: forwards a remainder-to-type conversion to the ring inverse.
^@450, ^@451: forwards to power_by_squaring.
literal_pow@460: calls the supplied function with the literal exponent.
literal_pow@474, literal_pow@478, literal_pow@479: forwards to inv or the floating-point power method.
literal_pow@483: selects the typed Float64 or inverse-power callee for a negative literal.
_powermod_mi_legal@581: disables an optional optimization for general Integer types.
ispow2@622: checks the real-valued predicate and forwards to the real-part overload.
split_sign@1073: returns the existing unsigned magnitude and a false sign flag.
powermod@587: forwards the modulus converted to BigInt and converts the result back.
clamp@1533: forwards the range's first and last endpoints.
gcd@163, lcm@164, gcdx@262: unsupported Real fallbacks only report MethodError.
invmod@371, clamp@1493: bottom-type extra-argument fallbacks only report MethodError.
throw_domerr_powbysq@385, @388, @393: shared error helpers have no behavior beyond the caller's DomainError contract.
bitstring@1140: nonprimitive inputs have no representation contract; primitive formatting is specified below.
-/

def RationalUnaryAllWidths : Prop := RationalUnaryGcd ∧
  ∀ (t : IntTy) (R : Type) (num den : R → JInt t) (ratio : JInt t → JInt t → Jl R),
  (∀ n d : JInt t, 0 < d.val → ∃ r, ratio n d = .ok r ∧ 0 < (den r).val ∧
    (num r).val * d.val = n.val * (den r).val) →
  ∀ a : R, 0 < (den a).val →
  if fits t ((num a).val.natAbs : Int) then ∃ r,
    gcd_Unary_Rational num den JuliaLean.base.checked.checkedAbsBits ratio a = .ok r ∧
    (num r).val * (den a).val = ((num a).val.natAbs : Int) * (den r).val ∧ 0 ≤ (num r).val
  else overflowError (gcd_Unary_Rational num den JuliaLean.base.checked.checkedAbsBits ratio a)

def NumberPowerTwo : Prop := ∀ (N : Type) (t : IntTy) (isreal : N → Bool)
    (real : N → JInt t) (imaginary : N → Int),
  (∀ x, isreal x = true ↔ imaginary x = 0) →
  ∀ x, ispow2_Number isreal real ispow2Bits x = true ↔
    imaginary x = 0 ∧ ∃ k : Nat, (real x).val = (2 : Int) ^ k


private def entry (id : String) (juliaFns : List String) (statement source : String) (prop : Lean.Name) : Entry :=
  { id, juliaFile := "base/intfuncs.jl", juliaFns, statement, source, status := .todo, prop, thm := none }

def entries : List Entry := [
  entry "intarith-number-gcd-typemin-overflow" ["gcd"]
    "Every signed width rejects the unrepresentable gcd(typemin,typemin)."
    "base/intfuncs.jl:53-66" ``GcdTypeminOverflow,
  entry "intarith-number-lcm-mixed-typemin" ["lcm(::Unsigned,::Signed)"]
    "A representable mixed UInt16/Int8 lcm returns its mathematical result."
    "base/intfuncs.jl:100-104,146-160" ``MixedLcmRepresentable,
  entry "intarith-number-gcdx-strict-bounds" ["gcdx"]
    "For signed nonzero inputs with representable gcd, gcdx satisfies the exact Bezout identity and documented strict coefficient bounds; unrepresentable gcds raise DomainError."
    "base/intfuncs.jl:196-198,228-230" ``GcdxStrictBounds,
  entry "intarith-number-invmod-ring-uint8" ["invmod(::UInt8)", "invmod(n,UInt8)"]
    "All unsigned-width odd inputs have a multiplicative inverse; all even inputs throw DomainError."
    "base/intfuncs.jl:347-357,370-382" ``RingInverseUnsigned,
  entry "intarith-number-invmod-ring-int8" ["invmod(::Int8)", "invmod(n,Int8)"]
    "All signed-width odd inputs have a multiplicative inverse; all even inputs throw DomainError."
    "base/intfuncs.jl:347-357,370-382" ``RingInverseSigned,
  entry "intarith-number-invmod-byte-range" ["invmod"]
    "At every source and modulus width and sign, invmod returns a modular inverse in the documented truncated-division range exactly for a nonzero coprime modulus, and otherwise throws DomainError."
    "base/intfuncs.jl:292-294,309" ``InvmodAllWidths,
  entry "intarith-number-invmod-uint128-range" ["invmod"]
    "At every source and modulus width and sign, invmod returns a modular inverse in the documented truncated-division range exactly for a nonzero coprime modulus, and otherwise throws DomainError."
    "base/intfuncs.jl:292-294,328-332; base/gmp.jl:676-687" ``InvmodAllWidths,
  entry "intarith-number-powermod-int128-typemin" ["powermod"]
    "At every signed width, every odd residue raised to the typemin exponent modulo typemin returns typemin plus one."
    "base/intfuncs.jl:504,587; base/gmp.jl:669-674" ``PowermodTypeminResidue,
  entry "intarith-number-powermod-typemin-negative" ["powermod"]
    "At every signed width, every odd residue raised to the typemin exponent modulo typemin returns typemin plus one."
    "base/intfuncs.jl:504,530-537" ``PowermodTypeminResidue,
  entry "intarith-number-powermod-negative-modulus" ["powermod", "multiplicativeinverse"]
    "For x,p in 0:7 and modulus in -7:-1, powermod equals exact exponentiation followed by floored mod."
    "base/intfuncs.jl:504,542-578" ``PowermodNonnegative,
  entry "intarith-powers-nextpow-overflow" ["nextpow", "_nextpow2"]
    "For positive integer x, a successful nextpow(2,x) is not less than x."
    "base/intfuncs.jl:627-631" ``NextpowLowerBound,
  entry "intarith-powers-negative-base-typemin" ["ndigits", "ndigits0znb"]
    "At every signed width, unsigned values through the magnitude of typemin return two digits for ndigits0znb and ndigits when the base is typemin."
    "base/intfuncs.jl:746-758,874" ``NegativeBaseTypeminBehavior,
  entry "intfuncs-ndigits-signed-typemin-base" ["ndigits0z(x::Integer, b::Integer)", "ndigits(x::Integer; base::Integer=10, pad::Integer=1)"]
    "With a signed input and same-type typemin base, ndigits0z returns zero for zero, one for positive values, and two for negative values; ndigits returns max(pad, count)."
    "base/intfuncs.jl:746-758,829-838,874" ``SignedTypeminBaseBehavior,
  entry "intarith-powers-large-base" ["ndigits", "ndigits0zpb"]
    "For positive values below a positive base, ndigits0zpb returns one when the base converts to Int64, and InexactError otherwise."
    "base/intfuncs.jl:764-786" ``LargeBaseSingleDigit,
  entry "intarith-powers-log-seed-correction" ["nextpow"]
    "An integer nextpow log seed at most one exponent away yields the mathematically smallest power not below x, when the three computed candidate powers are exact and increasing."
    "base/intfuncs.jl:629-630,657-669" ``NextpowSeedCorrection,
  entry "intarith-powers-isqrt-uint8" ["isqrt"]
    "At every integer width and sign, isqrt rejects negative inputs and otherwise returns the nonnegative integer r satisfying r*r <= n < (r+1)*(r+1)."
    "base/intfuncs.jl:1284-1293" ``IsqrtFloor,
  entry "intfuncs-string-positive-format" ["string(::Integer; base, pad)"]
    "At every integer width, positive bases produce the exact numeral with padding clamped to Int64; a negative value with maximum padding raises InexactError."
    "base/intfuncs.jl:1047-1070,1101-1109" ``StringRoundtrip,
  entry "intfuncs-base-string-positive" ["Base._base"]
    "For positive bases from 2 through 62, _base formats nonnegative values with any Int padding and optional sign; maximum padding with a sign raises InexactError."
    "base/intfuncs.jl:1047-1070" ``BaseStringPositive,
  entry "parseprint-digits-fill-low-order" ["digits!", "digits"]
    "When digits!(a, n; base) succeeds, it fills length(a) digits of magnitude below |base| (nonnegative for negative bases) whose value sum(a[k]*base^(k-1)) is congruent to n modulo base^length(a)."
    "base/intfuncs.jl:1172-1174, 1224-1228" ``DigitsFillLowOrder,
  entry "parseprint-digits-typemin-base" ["digits!", "digits"]
    "digits returns the exact digits for every Int64 base outside [-1,0,1], except typemin(Int64), which raises DomainError."
    "base/intfuncs.jl:1249-1281" ``DigitsValidBase,
  entry "parseprint-string-negative-base-unsigned" ["string(::Integer; base, pad)", "Base._base"]
    "For bases -62 through -2, string formats inputs that fit the corresponding signed type and returns InexactError when an unsigned value cannot be converted to that type."
    "base/intfuncs.jl:1047-1070,1101-1109" ``StringNegativeBase,
  entry "mathfuncs-prevpow-float32-overflow" ["prevpow(::Float32, ::Float64)"]
    "For finite inputs, prevpow raises DomainError when the base is at most one, the input is below one, or the input exceeds Float32 range; otherwise its result is no greater than the input."
    "base/intfuncs.jl:694-713 (prevpow docstring: the largest a^n not greater than x)" ``PrevpowFloat32Bound,
  entry "memsafety-intfuncs-formatting" ["bin", "oct", "append_c_digits", "append_nine_digits", "dec", "hex", "_base", "bitstring"]
    "Every integer formatter store and table access stays within its allocated buffer or source table."
    "base/intfuncs.jl:878-1165; JuliaLean.ParsePrint.IntPrint source model" ``FormattingMemorySafeFull,
  entry "combinatorics-binomial-typemin" ["binomial(::T, ::T) where T<:Integer"]
    "For every fixed-width integer type, binomial returns the exact generalized coefficient when representable and OverflowError exactly otherwise."
    "base/intfuncs.jl:1339-1402 (binomial docstring and implementation)" ``BinomialExactAndOverflow,
  entry "combinatorics-binomial-nonnegative-edges" ["binomial(::T, ::T) where T<:Integer"]
    "For every nonnegative fixed-width n, binomial(n,k) is zero for k<0 or k>n and one for k=0."
    "base/intfuncs.jl:1342-1349,1377,1385-1386" ``BinomialNonnegativeEdges,
  entry "intfuncs-binomial-mixed-exact" ["binomial(n::Integer, k::Integer)"]
    "For fixed-width mixed inputs, promotion errors propagate; successful value-preserving promotion returns the exact generalized coefficient or OverflowError."
    "base/intfuncs.jl:1373" ``BinomialMixedExact,
  entry "intfuncscov-gcd-mixed-typemin" ["_promote_mixed_signs", "gcd(::Signed,::Unsigned)", "gcd(::Unsigned,::Signed)", "lcm(::Signed,::Unsigned)", "gcdx(::Signed,::Unsigned)", "gcdx(::Unsigned,::Signed)"]
    "A signed typemin and same-width unsigned value have a representable gcd, lcm, and Bezout result in their promoted type."
    "base/intfuncs.jl:8,100,146-160,192-198,276-284" ``MixedGcdRepresentable,
  entry "intfuncscov-gcd-array-typemin" ["gcd(::AbstractArray{<:Integer})"]
    "Array gcd reduces from left to right, stops at one, and propagates overflow at the first unrepresentable prefix even if later values would reduce the final gcd."
    "base/intfuncs.jl:178-187" ``GcdArrayRepresentable,
  entry "intfuncs-gcd-array-real" ["gcd(abc::AbstractArray{<:Real})"]
    "The real-array fallback reduces from zero with gcd; for arbitrary-precision integer values, the result is their mathematical gcd."
    "base/intfuncs.jl:166" ``GcdArrayRealExact,
  entry "intfuncs-gcd-exact" ["gcd(a::T, b::T) where T<:BitInteger"]
    "At every BitInteger width and sign, gcd returns the nonnegative mathematical greatest common divisor, including both zero cases, or OverflowError exactly when it cannot be represented."
    "base/intfuncs.jl:53-64" ``GcdExact,
  entry "intfuncs-gcd-generic" ["gcd(a::T, b::T) where T<:Integer"]
    "The generic Euclidean gcd computes the mathematical gcd for arbitrary-precision integers of either sign."
    "base/intfuncs.jl:44-51" ``GcdGenericExact,
  entry "intfuncs-lcm-exact" ["lcm(a::T, b::T) where T<:Integer"]
    "At every BitInteger width and sign, lcm returns the nonnegative mathematical least common multiple, or OverflowError exactly when it cannot be represented; a zero argument gives zero."
    "base/intfuncs.jl:136-144" ``LcmExact,
  entry "intfuncs-lcm-generic" ["lcm(a::T, b::T) where T<:Integer"]
    "The generic lcm computes the mathematical least common multiple on arbitrary-precision integers of either sign."
    "base/intfuncs.jl:136-144" ``LcmGenericExact,
  entry "intfuncs-gcd-lcm-unary" ["gcd(a::Integer)", "lcm(a::Union{Integer,Rational})"]
    "Unary gcd and lcm return the exact magnitude or OverflowError when the positive magnitude is unrepresentable."
    "base/intfuncs.jl:152,154" ``GcdUnaryExact,
  entry "intfuncs-gcd-rational-unary" ["gcd(a::Rational)"]
    "Unary rational gcd returns the nonnegative magnitude of the rational, with checked numerator overflow, for fixed-width and arbitrary-precision components."
    "base/intfuncs.jl:153" ``RationalUnaryAllWidths,
  entry "intfuncs-absdiff" ["absdiff(x::T,y::T) where {T<:Unsigned}", "absdiff(x::T,y::T) where {T<:Signed}"]
    "absdiff returns the mathematical nonnegative difference for unsigned inputs, and for signed inputs when the difference and its magnitude are representable."
    "base/intfuncs.jl:68-71,72-75" ``AbsDifferenceExact,
  entry "intfuncs-binary-gcd" ["_gcd(ain::T, bin::T) where T<:BitInteger"]
    "The binary gcd loop returns the mathematical gcd on the nonzero, non-typemin-first domain supplied by its public caller."
    "base/intfuncs.jl:80-95" ``BinaryGcdExact,
  entry "intfuncs-gcd-lcm-nary" ["gcd(a::Real, b::Real, c::Real...)", "lcm(a::Real, b::Real, c::Real...)"]
    "N-ary gcd and lcm compute the mathematical gcd and lcm of the whole argument list with exact arbitrary-precision arithmetic."
    "base/intfuncs.jl:161,162" ``GcdLcmNaryExact,
  entry "intfuncs-lcm-array" ["lcm(abc::AbstractArray{<:Real})"]
    "Integer array lcm returns one for empty input, checked absolute value for a singleton, and the exact mathematical lcm or OverflowError for a larger reduction."
    "base/intfuncs.jl:167-176" ``LcmArrayExact,
  entry "intfuncs-lcm-array-real" ["lcm(abc::AbstractArray{<:Real})"]
    "Real array lcm returns one for empty integer arrays, errors for empty non-integer arrays, takes absolute value for a singleton, and delegates larger arrays to reduce."
    "base/intfuncs.jl:167-176" ``LcmArrayRealSemantics,
  entry "intfuncs-gcdx-bezout" ["gcdx(a::T, b::T) where {T<:Integer}"]
    "gcdx returns the mathematical nonnegative gcd and coefficients satisfying Bezout exactly for signed integers, and modulo the type modulus for unsigned integers."
    "base/intfuncs.jl:235-260" ``GcdxBezout,
  entry "intfuncs-gcdx-unrepresentable" ["gcdx(a::T, b::T) where {T<:Integer}"]
    "gcdx throws DomainError when the positive gcd is not representable in the input type."
    "base/intfuncs.jl:235-260" ``GcdxUnrepresentable,
  entry "intfuncs-gcdx-unary" ["gcdx(a::Real)"]
    "Unary gcdx returns the magnitude and a coefficient that reconstructs that magnitude, including zero."
    "base/intfuncs.jl:263" ``GcdxUnaryBezout,
  entry "intfuncs-gcdx-nary" ["gcdx(a::Real, b::Real, cs::Real...)"]
    "When each left-to-right gcd prefix fits, n-ary gcdx returns one coefficient per argument and a Bezout identity; the first unrepresentable prefix raises DomainError."
    "base/intfuncs.jl:264-274" ``GcdxNaryBezout,
  entry "intfuncs-gcdx-mixed" ["gcdx(a::Signed, b::Unsigned)", "gcdx(a::Unsigned, b::Signed)"]
    "Mixed-sign gcdx returns the mathematical gcd and valid Bezout coefficients in the promoted type whenever the gcd fits."
    "base/intfuncs.jl:276-281,282-285" ``GcdxMixedBezout,
  entry "intfuncs-bezout-update" ["_gcdx_update(s0::T, q::T, s1::T) where {T<:Unsigned}", "_gcdx_update(s0, q, s1)"]
    "The coefficient update is subtraction of the coefficient product modulo the integer type modulus at every width and sign."
    "base/intfuncs.jl:189,190" ``BezoutUpdateRing,
  entry "intfuncs-bezout-coefficient" ["_bezout_coef(n, m)"]
    "The Bezout coefficient helper returns an inverse coefficient for coprime inputs and throws DomainError for a non-unit gcd."
    "base/intfuncs.jl:337-341" ``BezoutCoefficient,
  entry "intfuncs-ring-inverse-type" ["invmod(n::Integer, ::Type{T}) where {T<:BitInteger}"]
    "The type-modulus inverse exists exactly for odd inputs and satisfies multiplication congruence modulo two to the target width, for every source and target width and sign."
    "base/intfuncs.jl:370" ``RingInverseType,
  entry "intfuncs-power-exact" ["power_by_squaring(x_, p::Integer; mul=*)", "^(x::T, p::T) where {T<:Integer}", "^(x::Number, p::Integer)"]
    "Every nonnegative fixed-width integer exponent produces the exact integer power reduced to the base type modulus, at every width and sign."
    "base/intfuncs.jl:399-443,450,451" ``IntegerPowerExact,
  entry "intfuncs-power-negative" ["power_by_squaring(x_, p::Integer; mul=*)"]
    "Negative exponents accept the multiplicative units with their parity-dependent result and otherwise throw DomainError."
    "base/intfuncs.jl:399-443" ``IntegerPowerNegative,
  entry "intfuncs-power-generic" ["power_by_squaring(x_, p::Integer; mul=*)"]
    "Generic exponentiation computes the exact mathematical power for arbitrary-precision integers and every nonnegative integer exponent."
    "base/intfuncs.jl:399-443" ``BigIntegerPowerExact,
  entry "intfuncs-bool-power" ["power_by_squaring(x::Bool, p::Integer)"]
    "Boolean powers equal repeated Boolean multiplication from true for nonnegative exponents; negative powers return true for true and raise DomainError for false."
    "base/intfuncs.jl:445-448" ``BoolPowerExact,
  entry "intfuncs-bool-unsigned-power" ["power_by_squaring(x::Bool, p::Unsigned)"]
    "Unsigned Boolean powers equal repeated Boolean multiplication from true at every unsigned width."
    "base/intfuncs.jl:444" ``BoolUnsignedPower,
  entry "intfuncs-literal-powers" ["literal_pow(::typeof(^), x::HWNumber, ::Val{0})", "literal_pow(::typeof(^), x::HWNumber, ::Val{1})", "literal_pow(::typeof(^), x::HWNumber, ::Val{2})", "literal_pow(::typeof(^), x::HWNumber, ::Val{3})"]
    "The literal exponents zero through three produce the mathematical power in the fixed-width integer ring."
    "base/intfuncs.jl:470,471,472,473" ``LiteralPowerExact,
  entry "intfuncs-literal-inverse-square" ["literal_pow(::typeof(^), x::HWNumber, ::Val{-2})"]
    "The negative-two literal power has the reciprocal-square value under the documented exact inverse and multiplication interfaces."
    "base/intfuncs.jl:475" ``LiteralInverseSquare,
  entry "intfuncs-powermod-negative" ["powermod(x::Integer, p::Integer, m::T) where T<:Integer"]
    "For a nonzero modulus and coprime base, negative modular powers exist and equal exact exponentiation of a modular inverse at every width and sign, including typemin exponents."
    "base/intfuncs.jl:524-579" ``PowermodNegative,
  entry "intfuncs-powermod-zero-modulus" ["powermod(x::Integer, p::Integer, m::T) where T<:Integer", "powermod(x::Integer, p::Integer, m::Union{Int128,UInt128})"]
    "Nonnegative modular powers reject a zero modulus with DivideError at every width and sign."
    "base/intfuncs.jl:524-579,587" ``PowermodZeroModulus,
  entry "intfuncs-modular-optimization-safe" ["_powermod_mi_legal(mm::T) where {T<:Unsigned}"]
    "Whenever the unsigned modular-power optimization is enabled, every product of residues below the modulus fits the original unsigned type."
    "base/intfuncs.jl:582-584" ``ModularOptimizationSafe,
  entry "intfuncs-ispow2" ["ispow2(x::Integer)"]
    "The integer power-of-two predicate is true exactly for positive integer powers of two, at every BitInteger width and sign."
    "base/intfuncs.jl:624" ``IsPowerTwoExact,
  entry "intfuncs-number-ispow2" ["ispow2(x::Number)"]
    "For numbers with an integer real part, the power-of-two predicate holds exactly when the imaginary part is zero and the real part is a positive power of two."
    "base/intfuncs.jl:622" ``NumberPowerTwo,
  entry "intfuncs-nextpow-exact" ["_nextpow2(x::Unsigned)", "_nextpow2(x::Integer)", "nextpow(a::Real, x::Real)"]
    "nextpow returns the least nonnegative power not below a positive input, rejects inputs beyond a non-binary base type with DomainError, and reports an unrepresentable result with OverflowError."
    "base/intfuncs.jl:589,590,649-669" ``NextpowExact,
  entry "intfuncs-prevpow-exact" ["_prevpow2(x::Unsigned)", "_prevpow2(x::Integer)", "prevpow(a::T, x::Real) where T <: Real"]
    "prevpow returns the greatest nonnegative power not above an input at least one, or the documented DomainError when the non-binary base type cannot cover the input."
    "base/intfuncs.jl:591,592,694-713" ``PrevpowExact,
  entry "intfuncs-prevpow-two" ["_prevpow2(x::Unsigned)", "_prevpow2(x::Integer)"]
    "The base-two predecessor is the unique power of two no greater than the positive input and with its successor greater than the input, at every width and sign."
    "base/intfuncs.jl:591,592" ``PrevpowTwoExact,
  entry "intfuncs-ndigits" ["ndigits0znb(x::Integer, b::Integer)", "ndigits0zpb(x::Integer, b::Integer)", "ndigits0z(x::Integer, b::Integer)", "ndigits(x::Integer; base::Integer=10, pad::Integer=1)"]
    "For all widths and signs, ndigits gives the minimal padded digit count when its signed-base magnitude and Int64 conversion are representable; the typemin and conversion-error cases are specified separately."
    "base/intfuncs.jl:746-758,764-796,829-838,874" ``NdigitsExact,
  entry "intfuncs-ndigits-zero-domain" ["ndigits0z(x::Integer, b::Integer)", "ndigits(x::Integer; base::Integer=10, pad::Integer=1)"]
    "ndigits0z returns zero for zero in every valid base; ndigits returns max(pad,0). Both reject bases -1, 0, and 1 with DomainError, and nonzero positive-base inputs whose base does not fit Int64 raise InexactError."
    "base/intfuncs.jl:829-838,874" ``NdigitsZeroAndDomain,
  entry "intfuncs-decimal-count" ["bit_ndigits0z(x::Base.BitUnsigned64)", "bit_ndigits0z(x::UInt128)"]
    "Both decimal-table implementations return the mathematically minimal decimal digit count, including zero, at every unsigned width."
    "base/intfuncs.jl:725-729,730-737" ``DecimalDigitCount,
  entry "intfuncs-decimal-input-count" ["ndigits0z(x::BitSigned)", "ndigits0z(x::BitUnsigned)"]
    "Default decimal digit counting counts the magnitude of signed or unsigned inputs, including signed typemin."
    "base/intfuncs.jl:739,740" ``DecimalInputDigitCount,
  entry "intfuncs-decimal-generic" ["ndigits0z(x::Integer)"]
    "The generic default-base method returns the exact minimal decimal digit count for every Integer, including arbitrary-precision values."
    "base/intfuncs.jl:741" ``DefaultDecimalGeneric,
  entry "intfuncs-bool-digit-count" ["ndigits0znb(x::Bool, b::Integer)", "ndigits0zpb(x::Bool, b::Integer)"]
    "Both Boolean digit counters return the minimal count for every valid positive or negative base: zero for false and one for true."
    "base/intfuncs.jl:761,798" ``BoolDigitCounts,
  entry "intfuncs-top-set-bit" ["top_set_bit(x::Integer)"]
    "The generic top-set-bit result is zero for zero and otherwise the exponent interval that contains the nonnegative integer."
    "base/intfuncs.jl:842" ``TopBitGeneric,
  entry "intfuncs-digits-roundtrip" ["digits(n::Integer; base::Integer = 10, pad::Integer = 1)", "digits(T::Type{<:Integer}, n::Integer; base::Integer = 10, pad::Integer = 1)", "digits!(a::AbstractVector{T}, n::Integer; base::Integer = 10) where T<:Integer"]
    "For valid bases, digits returns the exact least-significant-first digits; their evaluation is n and their count is minimal subject to pad. Signed typemin bases raise DomainError; positive base or length conversion can raise InexactError."
    "base/intfuncs.jl:1207-1208,1210-1212,1249-1281" ``DigitsRoundtrip,
  entry "intfuncs-digits-errors" ["digits!(a::AbstractVector{T}, n::Integer; base::Integer = 10) where T<:Integer"]
    "digits! rejects bases -1, 0, 1, and signed typemin with DomainError, and rejects an element type too small for the base with ArgumentError."
    "base/intfuncs.jl:1249-1281" ``DigitsErrors,
  entry "intfuncs-formatting-writers" ["bin(x::Unsigned, pad::Int, neg::Bool)", "oct(x::Unsigned, pad::Int, neg::Bool)", "dec(x::Unsigned, pad::Int, neg::Bool)", "hex(x::Unsigned, pad::Int, neg::Bool)"]
    "For every Int padding value, these writers return the exact numeral for nonnegative magnitudes and nonzero negative-sign cases; negative padding adds no zeros, and maximum padding with a sign raises InexactError."
    "base/intfuncs.jl:878-903,905-920,983-1018,1020-1042" ``FormattingWriters,
  entry "intfuncs-append-decimal" ["append_c_digits(olength::Int, digits::Unsigned, buf, pos::Int)"]
    "append_c_digits writes exactly the requested padded decimal segment, preserves bytes outside that segment, returns the following position, and keeps stores inside the segment."
    "base/intfuncs.jl:938-952" ``AppendDecimalDigits,
  entry "intfuncs-append-nine-digits" ["append_nine_digits(digits::Unsigned, buf, pos::Int)"]
    "append_nine_digits writes exactly nine decimal digits, including nine zeros for zero, and advances the position by nine without changing other bytes."
    "base/intfuncs.jl:954-963" ``AppendNineDigitsSpec,
  entry "intfuncs-append-fast" ["append_c_digits_fast(olength::Int, digits::Unsigned, buf, pos::Int)"]
    "The chunked decimal append produces exactly the same decimal segment, position, and unchanged surrounding bytes for every unsigned width."
    "base/intfuncs.jl:965-980" ``AppendFastSpec,
  entry "intfuncs-split-sign" ["split_sign(n::Integer)"]
    "Splitting an integer sign produces its exact unsigned magnitude and a true sign flag exactly for negative inputs, including typemin."
    "base/intfuncs.jl:1072" ``SplitSignExact,
  entry "intfuncs-bool-string" ["string(b::Bool)"]
    "The Boolean string encoder round-trips through the canonical true/false decoder and assigns distinct strings to the two values."
    "base/intfuncs.jl:1121" ``BoolStrings,
  entry "intfuncs-bitstring" ["bitstring(x::T) where {T}"]
    "Every fixed-width integer bitstring has exactly the type width and gives every two's-complement bit in most-significant-first order."
    "base/intfuncs.jl:1140-1167" ``BitstringExact,
  entry "intfuncs-bitstring-primitive" ["bitstring(x::T) where {T}"]
    "For every primitive type and bit width, bitstring gives every representation bit in most-significant-first order under the bitcast, extension, truncation, and logical-shift interfaces."
    "base/intfuncs.jl:1140-1167" ``PrimitiveBitstring,
  entry "intfuncs-factorial" ["factorial(n::Integer)"]
    "The generic factorial fallback rejects negative inputs with DomainError and returns the exact product when it fits typeof(n*n); its result has that type. BitInteger table overflow is specified in base/combinatorics.jl."
    "base/intfuncs.jl:1330-1337" ``FactorialFallbackNoOverflow,
  entry "intfuncs-factorial-generic" ["factorial(n::Integer)"]
    "The generic integer factorial computes the exact arbitrary-precision product for nonnegative inputs and throws DomainError for negative inputs."
    "base/intfuncs.jl:1330-1337" ``FactorialGenericBig,
  entry "intfuncs-generalized-binomial" ["binomial(x::Number, k::Integer)"]
    "For exact rational arithmetic, generalized binomial is zero for negative k and otherwise equals the falling product divided by k factorial under the product reducer's law."
    "base/intfuncs.jl:1428-1433" ``GeneralizedBinomialPolynomial,
  entry "intfuncs-clamp" ["clamp(x::X, lo::L, hi::H) where {X,L,H}"]
    "Over a common total order, clamp returns hi when x > hi, lo when x < lo, and x otherwise, converting the selected value to the promoted type."
    "base/intfuncs.jl:1461-1464" ``ClampExact,
  entry "intfuncs-clamp-type" ["clamp(x, ::Type{T}) where {T<:Integer}"]
    "For any input type, type clamp returns typemax above the target range, typemin below it, and converts the input otherwise."
    "base/intfuncs.jl:1485-1492" ``ClampTypeExact,
  entry "intfuncs-clamp-bang" ["clamp!(x::AbstractArray, lo, hi)"]
    "In-place clamp preserves array axes and changes only indices returned by eachindex, assigning each visited value its interval-clamped result."
    "base/intfuncs.jl:1518-1523" ``ClampBangExact,
  entry "intfuncs-hastypemax" ["hastypemax(::Type{T})", "hastypemax(::Type{Union{}})", "hastypemax(::Type{Union{}}, slurp...)"]
    "hastypemax tests applicability of both typemax and typemin, returns false for Union{}, and raises MethodError when extra arguments are passed with Union{}."
    "base/intfuncs.jl:1219-1221" ``HasTypeMaxSpec
]

end JuliaLean.Proofs.base.intfuncs
