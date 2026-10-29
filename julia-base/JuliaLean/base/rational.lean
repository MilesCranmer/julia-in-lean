import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.checked

/-!
# Model of `base/rational.jl`

Typed source-ordered rational method models, generic over their integer
component and external numeric operations. The continued-fraction loop returns
`some` on termination; `none` denotes divergence. Calls into generic numeric, complex, I/O, and
string methods are explicit parameters, so this module does not assume their
Julia dispatch implementations.
-/

namespace JuliaLean.base.rational

open JuliaLean
-- Core.JlError retains only the String component of an InexactError payload.
@[simp] def inexactErrorCore {X : Type} (name : String) (_target : Type) (_value : X) : JlError :=
  .inexactError name

def checkedAdd {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  JuliaLean.base.checked.checkedAddBits x y

def checkedSub {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  JuliaLean.base.checked.checkedSubBits x y

def checkedMul {t : IntTy} (x y : JInt t) : Jl (JInt t) :=
  JuliaLean.base.checked.checkedMulBits x y

def checkedNeg {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  JuliaLean.base.checked.checkedNegBits x

def checkedAbs {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  JuliaLean.base.checked.checkedAbsBits x
private def promoteIntegerPair {t s : IntTy} (x : JInt t) (y : JInt s) :
    Jl (JInt (t.promote s) × JInt (t.promote s)) := do
  let xp ← JInt.convert (t.promote s) x.val
  let yp ← JInt.convert (t.promote s) y.val
  pure (xp, yp)

def checkedAddMixed {t s : IntTy} (x : JInt t) (y : JInt s) :=
  JuliaLean.base.checked.checkedAddPromoted promoteIntegerPair checkedAdd x y

def checkedSubMixed {t s : IntTy} (x : JInt t) (y : JInt s) :=
  JuliaLean.base.checked.checkedSubPromoted promoteIntegerPair checkedSub x y

def checkedMulMixed {t s : IntTy} (x : JInt t) (y : JInt s) :=
  JuliaLean.base.checked.checkedMulPromoted promoteIntegerPair checkedMul x y

/-- The component type is the `IntTy` index; the pair itself is intentionally
unrestricted because `unsafe_rational` does not validate its representation. -/
@[ext] structure Rational (T : Type) where
  num : T
  den : T
  deriving DecidableEq, Repr, Inhabited

abbrev Rat (t : IntTy) := Rational (JInt t)

def bwand (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | _, _ => false

def bwor (a b : Bool) : Bool :=
  match a, b with
  | false, false => false
  | _, _ => true


/--
Julia source: base/rational.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
numerator(x::Rational) = x.num
```
-/
def numeratorRationalSource {T : Type} (x : Rational T) : T := x.num

/--
Julia source: base/rational.jl:384-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
denominator(x::Rational) = x.den
```
-/
def denominatorRationalSource {T : Type} (x : Rational T) : T := x.den

inductive Rounding where
  | toZero | down | up | nearest | nearestAway | nearestUp | fromZero
  deriving Repr, DecidableEq

def roundValue {t : IntTy} (x y : JInt t) (mode : Rounding) : Jl (JInt t) := do
  let q ← JInt.div x y
  match mode with
  | .toZero => pure q
  | .down => JInt.fld x y
  | .up => JInt.cld x y
  | .nearest | .nearestAway | .nearestUp | .fromZero => do
      let r ← JInt.remInt x y
      let negative := decide ((x.val < 0) ≠ (y.val < 0))
      let away := JInt.wrap t (q.val + if negative then -1 else 1)
      if mode = .fromZero then
        if r.val = 0 then pure q else pure away
      else
        let twice := 2 * r.val.natAbs
        let den := y.val.natAbs
        if twice < den then pure q
        else if twice > den then pure away
        else if mode = .nearestAway then pure away
        else if mode = .nearestUp then
          if negative then pure q else pure away
        else if q.val % 2 = 0 then pure q else pure away

def float64RationalRatio (x : JuliaLean.base.float.FV .f64) : Int × Nat :=
  let (significand, exponent, sign) := JuliaLean.base.float.decompose_Float64 x
  let n := significand.val * sign.val
  let scale := 2 ^ exponent.val.natAbs
  if exponent.val < 0 then (n, scale) else (n * Int.ofNat scale, 1)

def Normalized {t : IntTy} (x : Rat t) : Prop :=
  0 ≤ x.den.val ∧ Nat.gcd x.num.val.natAbs x.den.val.natAbs = 1

def unsignedInf : Rat .u8 := ⟨JInt.lit .u8 1, JInt.lit .u8 0⟩

def unsignedOne : Rat .u8 := ⟨JInt.lit .u8 1, JInt.lit .u8 1⟩

structure ComplexValue (α : Type) where
  re : α
  im : α

private def floatDivToZero (x y : JuliaLean.base.float.FV .f64) : JuliaLean.base.float.FV .f64 :=
  JuliaLean.base.float.round_Nearest_llvm
    (JuliaLean.base.float.sub_IEEEFloat
      (JuliaLean.base.float.div_IEEEFloat x y)
      (JuliaLean.base.float.div_IEEEFloat (JuliaLean.base.float.rem_IEEEFloat x y) y))

private def floatCld (x y : JuliaLean.base.float.FV .f64) : JuliaLean.base.float.FV .f64 :=
  JuliaLean.base.float.round_Nearest_llvm
    (JuliaLean.base.float.sub_IEEEFloat
      (JuliaLean.base.float.div_IEEEFloat x y)
      (JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.mod_AbstractFloat x (JuliaLean.base.float.neg_IEEEFloat y)) y))

def rationalizeCaught : JlError → Bool
  | .inexactError _ | .overflowError _ => true
  | _ => false

/- The type-level promotion rule from Rational to an integer;
`base/rational.jl:230`. -/
def promoteRuleRatInt {α β γ : Type} (promote : α → β) (rationalType : β → γ) (t : α) : γ :=
  rationalType (promote t)

/-! ## Generic `Integer` interface for `Rational{T<:Integer}` (`BitInteger`, `BigInt`, `Bool`) -/

/-- Operations of an integer component type `T<:Integer` used by `base/rational.jl`. -/
structure RatIntOps (T : Type) where
  typeName : String
  isUnsignedOrBool : Bool
  hasTypeMax : Bool
  zero : T
  one : T
  minusOne : T
  typemin : T
  typemax : T
  iszero : T → Bool
  isone : T → Bool
  isodd : T → Bool
  signbit : T → Bool
  sign : T → T
  uplus : T → T
  negWrap : T → T
  neg : T → Jl T
  absWrap : T → T
  uabs : T → Nat
  checkedNeg : T → Jl T
  checkedAbs : T → Jl T
  checkedAdd : T → T → Jl T
  checkedSub : T → T → Jl T
  checkedMul : T → T → Jl T
  addWrap : T → T → T
  subWrap : T → T → T
  mulWrap : T → T → T
  divToZero : T → T → Jl T
  fld : T → T → Jl T
  cld : T → T → Jl T
  rem : T → T → Jl T
  mod : T → T → Jl T
  divRound : T → T → Rounding → Jl T
  eq : T → T → Bool
  lt : T → T → Bool
  le : T → T → Bool
  toInt : T → Int
  fromInt : Int → Jl T

/-- Mixed-type integer promotion interface between `TX` and `TY` into `P = promote_type(TX, TY)`. -/
inductive LazyStringPart (τ : Type) where
  | lit (s : String)
  | val (v : τ)
  deriving Repr, DecidableEq

structure LazyString (τ : Type) where
  parts : List (LazyStringPart τ)
  deriving Repr, DecidableEq

def LazyString.build {τ : Type} (parts : List (LazyStringPart τ)) : LazyString τ := ⟨parts⟩

def LazyString.render {τ : Type} (showVal : τ → String) (s : LazyString τ) : String :=
  String.join (s.parts.map fun
    | .lit str => str
    | .val v => showVal v)

structure RatPromoteOps (TX TY P : Type) where
  opsX : RatIntOps TX
  opsY : RatIntOps TY
  opsP : RatIntOps P
  convertXP : TX → Jl P
  convertYP : TY → Jl P
  promotePX : P → TX → Jl (P × P)
  promote : TX → TY → Jl (P × P)
  checkedMulXP : TX → P → Jl P
  checkedMulYP : TY → P → Jl P
  checkedMulPX : P → TX → Jl P
  checkedMulPY : P → TY → Jl P
  checkedMulXY : TX → TY → Jl P
  mulWrapXP : TX → P → P
  mulWrapYP : TY → P → P

/-- `BitInteger` (`JInt t`) instance of `RatIntOps`. -/
def jintOps (t : IntTy) : RatIntOps (JInt t) where
  typeName := t.name
  isUnsignedOrBool := !t.signed
  hasTypeMax := true
  zero := JInt.lit t 0
  one := JInt.lit t 1
  minusOne := JInt.lit t (-1)
  typemin := JInt.typemin t
  typemax := JInt.typemax t
  iszero x := x.val == 0
  isone x := x.val == 1
  isodd x := x.val % 2 != 0
  signbit x := decide (x.val < 0)
  sign x := JInt.lit t (if x.val < 0 then -1 else if x.val > 0 then 1 else 0)
  uplus x := x
  negWrap x := -x
  neg x := if t.signed then .ok (-x) else if x.val != 0 then .error (.overflowError "cannot negate unsigned number") else .ok x
  absWrap x := JuliaLean.base.int.abs x
  uabs x := (JuliaLean.base.float.uabs x).val.toNat
  checkedNeg := checkedNeg
  checkedAbs := checkedAbs
  checkedAdd := checkedAdd
  checkedSub := checkedSub
  checkedMul := checkedMul
  addWrap x y := x + y
  subWrap x y := x - y
  mulWrap x y := x * y
  divToZero := JInt.div
  fld := JInt.fld
  cld := JInt.cld
  rem := JInt.remInt
  mod := JInt.mod
  divRound := roundValue
  eq x y := x.val == y.val
  lt x y := decide (x.val < y.val)
  le x y := decide (x.val ≤ y.val)
  toInt x := x.val
  fromInt n := JInt.convert t n

/-- Unbounded `Int` (`BigInt`) instance of `RatIntOps`. -/
def bigIntOps : RatIntOps Int where
  typeName := "BigInt"
  isUnsignedOrBool := false
  hasTypeMax := false
  zero := 0
  one := 1
  minusOne := -1
  typemin := 0
  typemax := 0
  iszero x := x == 0
  isone x := x == 1
  isodd x := x % 2 != 0
  signbit x := decide (x < 0)
  sign x := if x < 0 then -1 else if x > 0 then 1 else 0
  uplus x := x
  negWrap x := -x
  neg x := .ok (-x)
  absWrap x := (x.natAbs : Int)
  uabs x := x.natAbs
  checkedNeg x := .ok (-x)
  checkedAbs x := .ok (x.natAbs : Int)
  checkedAdd x y := .ok (x + y)
  checkedSub x y := .ok (x - y)
  checkedMul x y := .ok (x * y)
  addWrap x y := x + y
  subWrap x y := x - y
  mulWrap x y := x * y
  divToZero x y := if y = 0 then .error .divideError else .ok (x.tdiv y)
  fld x y := if y = 0 then .error .divideError else .ok (x.fdiv y)
  cld x y := if y = 0 then .error .divideError else .ok (-((-x).fdiv y))
  rem x y := if y = 0 then .error .divideError else .ok (x.tmod y)
  mod x y := if y = 0 then .error .divideError else .ok (x.fmod y)
  divRound x y mode :=
    if y = 0 then .error .divideError
    else match mode with
      | .toZero => .ok (x.tdiv y)
      | .down => .ok (x.fdiv y)
      | .up => .ok (-((-x).fdiv y))
      | _ => .ok (x.tdiv y)
  eq x y := x == y
  lt x y := decide (x < y)
  le x y := decide (x ≤ y)
  toInt x := x
  fromInt n := .ok n

/-- Homogeneous promotion instance for any `RatIntOps T`. -/
def samePromoteOps {T : Type} (ops : RatIntOps T) : RatPromoteOps T T T where
  opsX := ops
  opsY := ops
  opsP := ops
  convertXP x := .ok x
  convertYP y := .ok y
  promotePX n d := .ok (n, d)
  promote x y := .ok (x, y)
  checkedMulXP := ops.checkedMul
  checkedMulYP := ops.checkedMul
  checkedMulPX := ops.checkedMul
  checkedMulPY := ops.checkedMul
  checkedMulXY := ops.checkedMul
  mulWrapXP := ops.mulWrap
  mulWrapYP := ops.mulWrap

/-- Mixed-width `BitInteger` promotion instance (`JInt t`, `JInt s` -> `JInt (t.promote s)`). -/
def jintPromoteOps (t s : IntTy) : RatPromoteOps (JInt t) (JInt s) (JInt (t.promote s)) where
  opsX := jintOps t
  opsY := jintOps s
  opsP := jintOps (t.promote s)
  convertXP x := JInt.convert (t.promote s) x.val
  convertYP y := JInt.convert (t.promote s) y.val
  promotePX n d := do
    let d ← JInt.convert (t.promote s) d.val
    pure (n, d)
  promote := promoteIntegerPair
  checkedMulXP x y := checkedMul (JInt.wrap (t.promote s) x.val) y
  checkedMulYP y x := checkedMul (JInt.wrap (t.promote s) y.val) x
  checkedMulPX x y := checkedMul x (JInt.wrap (t.promote s) y.val)
  checkedMulPY x y := checkedMul x (JInt.wrap (t.promote s) y.val)
  checkedMulXY := checkedMulMixed
  mulWrapXP x y := JInt.wrap (t.promote s) x.val * y
  mulWrapYP y x := JInt.wrap (t.promote s) y.val * x

/-! ## Source-mirrored methods of `base/rational.jl` -/
/--
Julia source: base/rational.jl:9-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Rational{T<:Integer} <: Real
    num::T
    den::T

    # Unexported inner constructor of Rational that bypasses all checks
    global unsafe_rational(::Type{T}, num, den) where {T} = new{T}(num, den)
end
```
-/
def unsafeRationalTypeSource {m : Type → Type} [Monad m] (T : Type) {A B : Type}
    (convertNum : A → m T) (convertDen : B → m T)
    (num : A) (den : B) : m (Rational T) := do
  let n ← convertNum num
  let d ← convertDen den
  return ⟨n, d⟩


/--
Julia source: base/rational.jl:17-17 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_rational(num::T, den::T) where {T<:Integer} = unsafe_rational(T, num, den)
```
-/
def unsafeRationalSameSource {T : Type} (num den : T) : Rational T :=
  unsafeRationalTypeSource (m := Id) T id id num den


def zeroRat64 : Rat .i64 := unsafeRationalSameSource (JInt.lit .i64 0) (JInt.lit .i64 1)

/--
Julia source: base/rational.jl:18-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_rational(num::Integer, den::Integer) = unsafe_rational(promote(num, den)...)
```
-/
def unsafeRationalPromoteSource {A B P : Type}
    (promote : A → B → Jl (P × P)) (num : A) (den : B) : Jl (Rational P) := do
  let (n, d) ← promote num den
  return unsafeRationalSameSource n d

/--
Julia source: base/rational.jl:20-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checked_den(::Type{T}, num::T, den::T) where T<:Integer
    if signbit(den)
        den = checked_neg(den)
        num = checked_neg(num)
    end
    return unsafe_rational(T, num, den)
end
```
-/
def checkedDenTypeSource (T : Type) (ops : RatIntOps T) (num den : T) : Jl (Rational T) := do
  if ops.signbit den then
    let den ← ops.checkedNeg den
    let num ← ops.checkedNeg num
    return unsafeRationalTypeSource (m := Id) T id id num den
  else
    return unsafeRationalTypeSource (m := Id) T id id num den

/--
Julia source: base/rational.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_den(num::T, den::T) where T<:Integer = checked_den(T, num, den)
```
-/
def checkedDenSameSource {T : Type} (ops : RatIntOps T) (num den : T) : Jl (Rational T) :=
  checkedDenTypeSource T ops num den

/--
Julia source: base/rational.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
checked_den(num::Integer, den::Integer) = checked_den(promote(num, den)...)
```
-/
def checkedDenPromoteSource {A B P : Type} (prom : RatPromoteOps A B P)
    (num : A) (den : B) : Jl (Rational P) := do
  let (n, d) ← prom.promote num den
  checkedDenSameSource prom.opsP n d

/--
Julia source: base/rational.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline __throw_rational_argerror_zero(T) = throw(ArgumentError(LazyString("invalid rational: zero(", T, ")//zero(", T, ")")))
```
-/
def throwRationalZeroSource {τ ε α : Type}
    (argumentError : LazyString τ → ε) (T : τ) : Except ε α :=
  .error (argumentError (LazyString.build
    [.lit "invalid rational: zero(", .val T, .lit ")//zero(", .val T, .lit ")"]))

/--
Julia source: base/rational.jl:59-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer}
    g = gcd(uabs(x), uabs(y))
    div(x,g), div(y,g)
end
```
-/
def divgcdSource {TX TY UX UY G : Type}
    (uabsX : TX → UX) (uabsY : TY → UY) (gcd : UX → UY → G)
    (divX : TX → G → Jl TX) (divY : TY → G → Jl TY)
    (x : TX) (y : TY) : Jl (TX × TY) := do
  let g := gcd (uabsX x) (uabsY y)
  let qx ← divX x g
  let qy ← divY y g
  return (qx, qy)

/--
Julia source: base/rational.jl:31-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Rational{T}(num::Integer, den::Integer) where T<:Integer
    iszero(den) && iszero(num) && __throw_rational_argerror_zero(T)
    if T <: Union{Unsigned, Bool}
        # Throw InexactError if the result is negative.
        if !iszero(num) && (signbit(den) ⊻ signbit(num))
            throw(InexactError(:Rational, Rational{T}, num, den))
        end
        unum = uabs(num)
        uden = uabs(den)
        r_unum, r_uden = divgcd(unum, uden)
        return unsafe_rational(T, promote(T(r_unum), T(r_uden))...)
    else
        r_num, r_den = divgcd(num, den)
        return checked_den(T, promote(T(r_num), T(r_den))...)
    end
end
```
-/
def constructSource (T : Type) {NX DX UN UD : Type}
    (opsT : RatIntOps T) (iszeroN : NX → Bool) (iszeroD : DX → Bool)
    (signbitN : NX → Bool) (signbitD : DX → Bool)
    (uabsN : NX → UN) (uabsD : DX → UD)
    (divgcdU : UN → UD → Jl (UN × UD))
    (convertUN : UN → Jl T) (convertUD : UD → Jl T)
    (divgcdS : NX → DX → Jl (NX × DX))
    (convertN : NX → Jl T) (convertD : DX → Jl T)
    (promoteT : T → T → T × T)
    (num : NX) (den : DX)
    (inexactError : Type → (NX × DX) → JlError) : Jl (Rational T) := do
  if iszeroD den && iszeroN num then
    throwRationalZeroSource (fun s => JlError.argumentError (s.render id)) opsT.typeName
  else if opsT.isUnsignedOrBool then
    if !iszeroN num && xor (signbitD den) (signbitN num) then
      throw (inexactError (Rational T) (num, den))
    let unum := uabsN num
    let uden := uabsD den
    let (rUnum, rUden) ← divgcdU unum uden
    let tn ← convertUN rUnum
    let td ← convertUD rUden
    let (pn, pd) := promoteT tn td
    return unsafeRationalTypeSource (m := Id) T id id pn pd
  else
    let (rNum, rDen) ← divgcdS num den
    let tn ← convertN rNum
    let td ← convertD rDen
    let (pn, pd) := promoteT tn td
    checkedDenTypeSource T opsT pn pd

/--
Julia source: base/rational.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Rational(n::T, d::T) where {T<:Integer} = Rational{T}(n, d)
```
-/
def rationalSameSource {T U : Type}
    (opsT : RatIntOps T) (uabs : T → U)
    (divgcdU : U → U → Jl (U × U)) (convertU : U → Jl T)
    (divgcdS : T → T → Jl (T × T)) (promoteT : T → T → T × T)
    (n d : T) : Jl (Rational T) :=
  constructSource T opsT opsT.iszero opsT.iszero opsT.signbit opsT.signbit
    uabs uabs divgcdU convertU convertU divgcdS (fun x => .ok x) (fun x => .ok x) promoteT n d (inexactErrorCore "Rational")

/--
Julia source: base/rational.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Rational(n::Integer, d::Integer) = Rational(promote(n, d)...)
```
-/
def rationalPromoteSource {A B P : Type} (promote : A → B → Jl (P × P))
    (rationalSame : P → P → Jl (Rational P)) (n : A) (d : B) : Jl (Rational P) := do
  let (np, dp) ← promote n d
  rationalSame np dp

/--
Julia source: base/rational.jl:50-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Rational(n::Integer) = unsafe_rational(n, one(n))
```
-/
def rationalFromIntegerGeneric {α β : Type}
    (unsafeRationalSameSource : α → α → β) (one : α → α) (n : α) : β :=
  unsafeRationalSameSource n (one n)

/--
Julia source: base/rational.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
//(n::Integer,  d::Integer) = Rational(n,d)
```
-/
def exactDivideIntsSource {A B P : Type}
    (rational : A → B → Jl (Rational P)) (n : A) (d : B) : Jl (Rational P) :=
  rational n d

/--
Julia source: base/rational.jl:93-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function //(x::Rational, y::Integer)
    xn, yn = divgcd(promote(x.num, y)...)
    # If x is infinite, the denominator below is zero and cannot carry the
    # sign of y, so apply that sign to the numerator instead.
    if iszero(x.den) && signbit(yn)
        xn = checked_neg(xn)
    end
    checked_den(xn, checked_mul(x.den, yn))
end
```
-/
def divRatIntSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (x : Rational TX) (y : TY) : Jl (Rational P) := do
  let (xnumP, yP) ← prom.promote x.num y
  let (xn, yn) ← divgcd xnumP yP
  let xn ← if prom.opsX.iszero x.den && prom.opsP.signbit yn then prom.opsP.checkedNeg xn else pure xn
  let den ← prom.checkedMulXP x.den yn
  checkedDenSameSource prom.opsP xn den

/--
Julia source: base/rational.jl:102-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function //(x::Integer,  y::Rational)
    xn, yn = divgcd(promote(x, y.num)...)
    checked_den(checked_mul(xn, y.den), yn)
end
```
-/
def divIntRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (x : TX) (y : Rational TY) : Jl (Rational P) := do
  let (xP, ynumP) ← prom.promote x y.num
  let (xn, yn) ← divgcd xP ynumP
  let num ← prom.checkedMulPY xn y.den
  checkedDenSameSource prom.opsP num yn

/--
Julia source: base/rational.jl:106-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function //(x::Rational, y::Rational)
    xn,yn = divgcd(promote(x.num, y.num)...)
    xd,yd = divgcd(promote(x.den, y.den)...)
    # See the comment in `//(::Rational, ::Integer)`.
    if iszero(xd) && signbit(yn)
        xn = checked_neg(xn)
    end
    checked_den(checked_mul(xn, yd), checked_mul(xd, yn))
end
```
-/
def divRatRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xnumP, ynumP) ← prom.promote x.num y.num
  let (xn, yn) ← divgcd xnumP ynumP
  let (xdenP, ydenP) ← prom.promote x.den y.den
  let (xd, yd) ← divgcd xdenP ydenP
  let xn ← if prom.opsP.iszero xd && prom.opsP.signbit yn then prom.opsP.checkedNeg xn else pure xn
  let num ← prom.opsP.checkedMul xn yd
  let den ← prom.opsP.checkedMul xd yn
  checkedDenSameSource prom.opsP num den

/--
Julia source: base/rational.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
//(x::Complex, y::Real) = complex(real(x)//y, imag(x)//y)
```
-/
def exactDivideComplexReal {C α β γ δ : Type} (divide : α → β → Jl γ)
    (complex : γ → γ → δ) (real imag : C → α) (x : C) (y : β) : Jl δ := do
  let re ← divide (real x) y
  let im ← divide (imag x) y
  pure (complex re im)

/--
Julia source: base/rational.jl:120-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _complex_exact_inv(y::Complex)
    c, d = reim(y)
    num = if (isinf(c) | isinf(d))
        conj(zero(y))
    else
        conj(y)
    end
    num, abs2(y)
end
```
-/
def complexExactInvSource {α β γ : Type} (reim : β → α × α) (isinf : α → Bool)
    (zero conj : β → β) (abs2 : β → γ) (y : β) : β × γ :=
  let (c, d) := reim y
  let num := if bwor (isinf c) (isinf d) then conj (zero y) else conj y
  (num, abs2 y)

/--
Julia source: base/rational.jl:129-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _complex_exact_inv(y::Complex{<:Integer})
    c, d = reim(y)
    c_r, d_r = divgcd(c, d)
    abs2y_r = checked_add(checked_mul(c, c_r), checked_mul(d, d_r))
    num = complex(c_r, checked_neg(d_r))
    num, abs2y_r
end
```
-/
def complexExactInvIntegerSource {T α β : Type}
    (reim : α → T × T) (divgcd : T → T → Jl (T × T))
    (checkedMul checkedAdd : T → T → Jl T)
    (checkedNeg : T → Jl T) (complex : T → T → β)
    (y : α) : Jl (β × T) := do
  let (c, d) := reim y
  let (cR, dR) ← divgcd c d
  let c2 ← checkedMul c cR
  let d2 ← checkedMul d dR
  let abs2YR ← checkedAdd c2 d2
  let negDR ← checkedNeg dR
  let num := complex cR negDR
  pure (num, abs2YR)

/--
Julia source: base/rational.jl:137-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function //(x::Number, y::Complex)
    num, den = _complex_exact_inv(y)
    (x * num) // den
end
```
-/
def divideNumberComplexSource {α β γ δ ε ζ : Type}
    (reim : β → γ × γ) (isinf : γ → Bool) (zero conj : β → β) (abs2 : β → δ)
    (mul : α → β → ε) (divide : ε → δ → Jl ζ) (x : α) (y : β) : Jl ζ := do
  let (num, den) := complexExactInvSource reim isinf zero conj abs2 y
  divide (mul x num) den

/--
Julia source: base/rational.jl:141-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function //(x::Integer, y::Complex{<:Integer})
    complex(x) // y
end
```
-/
def divideIntegerComplexSource {I C Y R : Type}
    (complex : I → C) (divide : C → Y → Jl R) (x : I) (y : Y) : Jl R :=
  divide (complex x) y

/--
Julia source: base/rational.jl:144-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function //(x::Complex{<:Integer}, y::Complex{<:Integer})
    a, b, c, d = promote(reim(x)..., reim(y)...)
    c_r, d_r = divgcd(c, d)
    abs2y_r = checked_add(checked_mul(c, c_r), checked_mul(d, d_r))
    complex(
        checked_add(checked_mul(a, c_r), checked_mul(b, d_r)),
        checked_add(checked_mul(b, c_r), checked_neg(checked_mul(a, d_r)))
    )//abs2y_r
end
```
-/
def divideComplexIntegersSource {X Y IX IY P C R : Type}
    (reimX : X → IX × IX) (reimY : Y → IY × IY)
    (promote4 : IX → IX → IY → IY → Jl (P × P × P × P))
    (divgcd : P → P → Jl (P × P))
    (checkedMul checkedAdd : P → P → Jl P) (checkedNeg : P → Jl P)
    (complex : P → P → C) (divide : C → P → Jl R)
    (x : X) (y : Y) : Jl R := do
  let (xr, xi) := reimX x
  let (yr, yi) := reimY y
  let (a, b, c, d) ← promote4 xr xi yr yi
  let (cR, dR) ← divgcd c d
  let c2 ← checkedMul c cR
  let d2 ← checkedMul d dR
  let abs2YR ← checkedAdd c2 d2
  let ac ← checkedMul a cR
  let bd ← checkedMul b dR
  let re ← checkedAdd ac bd
  let bc ← checkedMul b cR
  let ad ← checkedMul a dR
  let negAD ← checkedNeg ad
  let im ← checkedAdd bc negAD
  divide (complex re im) abs2YR

/--
Julia source: base/rational.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
//(X::AbstractArray, y::Number) = X .// y
```
-/
def divideArraySource {α β γ : Type} (broadcast : α → β → γ) (x : α) (y : β) : γ :=
  broadcast x y

/--
Julia source: base/rational.jl:156-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, x::Rational)
    show(io, numerator(x))

    if isone(denominator(x)) && nonnothing_nonmissing_typeinfo(io) <: Rational
        return
    end

    print(io, "//")
    show(io, denominator(x))
end
```
-/
def showRationalSource {T α : Type} {m : Type → Type} [Monad m]
    (showValue : α → T → m Unit) (print : α → String → m Unit)
    (isone : T → Bool) (typedRational : α → Bool)
    (io : α) (x : Rational T) : m Unit := do
  showValue io (numeratorRationalSource x)
  if isone (denominatorRationalSource x) && typedRational io then
    pure ()
  else
    print io "//"
    showValue io (denominatorRationalSource x)

/--
Julia source: base/rational.jl:167-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::IO, ::Type{Rational{T}}) where T<:Integer
    r = read(s,T)
    i = read(s,T)
    r//i
end
```
-/
def readRationalSource {T τ α : Type} {m : Type → Type} [Monad m]
    (read : α → τ → m T) (exactDivide : T → T → m (Rational T))
    (io : α) (targetType : τ) : m (Rational T) := do
  let r ← read io targetType
  let i ← read io targetType
  exactDivide r i

/--
Julia source: base/rational.jl:172-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::IO, z::Rational)
    write(s,numerator(z),denominator(z))
end
```
-/
def writeRationalSource {T α β : Type}
    (write : α → T → T → Jl β) (io : α) (z : Rational T) : Jl β :=
  write io (numeratorRationalSource z) (denominatorRationalSource z)

/--
Julia source: base/rational.jl:175-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse(::Type{Rational{T}}, s::AbstractString) where T<:Integer
    ss = split(s, '/'; limit = 2)
    if isone(length(ss))
        return Rational{T}(parse(T, s))
    end
    @inbounds ns, ds = ss[1], ss[2]
    if startswith(ds, '/')
        ds = chop(ds; head = 1, tail = 0)
    end
    n = parse(T, ns)
    d = parse(T, ds)
    return n//d
end
```
-/
def parseRationalSource {T τ α : Type}
    (split : α → Char → Nat → List α) (length : List α → Nat)
    (isone : Nat → Bool) (getOneBased : List α → Nat → Jl α)
    (startswith : α → Char → Bool) (chop : α → α)
    (parse : τ → α → Jl T) (rationalSingle : T → Jl (Rational T))
    (exactDivide : T → T → Jl (Rational T))
    (target : τ) (s : α) : Jl (Rational T) := do
  let ss := split s '/' 2
  if isone (length ss) then
    let n ← parse target s
    rationalSingle n
  else
    let ns ← getOneBased ss 1
    let mut ds ← getOneBased ss 2
    if startswith ds '/' then
      ds := chop ds
    let n ← parse target ns
    let d ← parse target ds
    exactDivide n d

/--
Julia source: base/rational.jl:190-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Rational{T}(x::Rational) where T<:Integer
    unsafe_rational(T, convert(T, x.num), convert(T, x.den))
end
```
-/
def convertRatSource (T : Type) {S : Type}
    (convert : S → Jl T) (x : Rational S) : Jl (Rational T) := do
  let n ← convert x.num
  let d ← convert x.den
  return unsafeRationalTypeSource (m := Id) T id id n d

/--
Julia source: base/rational.jl:193-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Rational{T}(x::Integer) where T<:Integer
    unsafe_rational(T, T(x), T(one(x)))
end
```
-/
def rationalIntAsSource (T : Type) {I : Type}
    (convert : I → Jl T) (one : I → I) (x : I) : Jl (Rational T) := do
  let n ← convert x
  let d ← convert (one x)
  return unsafeRationalTypeSource (m := Id) T id id n d

/--
Julia source: base/rational.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Rational(x::Rational) = x
```
-/
def rationalIdentitySource {T : Type} (x : Rational T) : Rational T := x

/--
Julia source: base/rational.jl:199-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Bool(x::Rational) = x==0 ? false : x==1 ? true :
    throw(InexactError(:Bool, Bool, x)) # to resolve ambiguity
```
-/
def boolOfRatSource {T : Type}
    (eqZero eqOne : Rational T → Bool) (x : Rational T)
    (inexactError : String → Type → Rational T → JlError) : Jl Bool :=
  if eqZero x then .ok false
  else if eqOne x then .ok true
  else .error (inexactError "Bool" (Bool) x)

/--
Julia source: base/rational.jl:201-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::Rational) where {T<:Integer} = (isinteger(x) ? convert(T, x.num)::T :
    throw(InexactError(nameof(T), T, x)))
```
-/
def intOfRatSource (T : Type) {S : Type}
    (nameOfT : String) (isinteger : Rational S → Bool)
    (convert : S → Jl T) (x : Rational S)
    (inexactError : String → Type → Rational S → JlError) : Jl T :=
  if isinteger x then convert x.num
  else .error (inexactError nameOfT T x)

/--
Julia source: base/rational.jl:204-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
AbstractFloat(x::Rational) = (float(x.num)/float(x.den))::AbstractFloat
```
-/
def abstractFloatRatSource {T F : Type}
    (float : T → F) (div : F → F → F) (x : Rational T) : F :=
  div (float x.num) (float x.den)

/--
Julia source: base/rational.jl:205-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (::Type{T})(x::Rational{S}) where T<:AbstractFloat where S
    P = promote_type(T,S)
    convert(T, convert(P,x.num)/convert(P,x.den))::T
end
```
-/
def floatConvertRatSource (T : Type) {S P : Type}
    (convertP : S → P) (divP : P → P → P) (convertT : P → T)
    (x : Rational S) : T :=
  convertT (divP (convertP x.num) (convertP x.den))

def isSmallFloat16RatComponent : IntTy → Bool
  | .i16 | .i32 | .i64 | .u16 | .u32 | .u64 => true
  | _ => false

def is128RatComponent : IntTy → Bool
  | .i128 | .u128 => true
  | _ => false

/--
Julia source: base/rational.jl:211-212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float16(x::Rational{<:Union{Int16,Int32,Int64,UInt16,UInt32,UInt64}}) =
    Float16(Float32(x))
```
-/
def float16OfRationalSmallSource {t : IntTy}
    (_h : isSmallFloat16RatComponent t = true) (x : Rat t) : JuliaLean.base.float.FV .f16 :=
  JuliaLean.base.float.convertFloat .f16
    (floatConvertRatSource (JuliaLean.base.float.FV .f32)
      (JuliaLean.base.float.floatOfInt .f32)
      JuliaLean.base.float.div_IEEEFloat
      (JuliaLean.base.float.convertFloat .f32) x)

/--
Julia source: base/rational.jl:213-214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float16(x::Rational{<:Union{Int128,UInt128}}) =
    Float16(Float64(x)) # UInt128 overflows Float32, include Int128 for consistency
```
-/
def float16OfRational128Source {t : IntTy}
    (_h : is128RatComponent t = true) (x : Rat t) : JuliaLean.base.float.FV .f16 :=
  JuliaLean.base.float.convertFloat .f16
    (floatConvertRatSource (JuliaLean.base.float.FV .f64)
      (JuliaLean.base.float.floatOfInt .f64)
      JuliaLean.base.float.div_IEEEFloat
      (JuliaLean.base.float.convertFloat .f64) x)

/--
Julia source: base/rational.jl:215-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Float32(x::Rational{<:Union{Int128,UInt128}}) =
    Float32(Float64(x)) # UInt128 overflows Float32, include Int128 for consistency
```
-/
def float32OfRational128Source {t : IntTy}
    (_h : is128RatComponent t = true) (x : Rat t) : JuliaLean.base.float.FV .f32 :=
  JuliaLean.base.float.convertFloat .f32
    (floatConvertRatSource (JuliaLean.base.float.FV .f64)
      (JuliaLean.base.float.floatOfInt .f64)
      JuliaLean.base.float.div_IEEEFloat
      (JuliaLean.base.float.convertFloat .f64) x)

/--
Julia source: base/rational.jl:218-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Rational{T}(x::AbstractFloat) where T<:Integer
    r = rationalize(T, x, tol=0)
    x == convert(typeof(x), r) || throw(InexactError(:Rational, Rational{T}, x))
    r
end
```
-/
def rationalOfFloatSource {m : Type → Type} [Monad m] [MonadExceptOf JlError m] (T : Type) {F : Type}
    (rationalizeZero : F → m (Rational T))
    (convertTypeofX : Rational T → F)
    (eqF : F → F → Bool) (x : F)
    (inexactError : String → Type → F → JlError) : m (Rational T) := do
  let r ← rationalizeZero x
  if eqF x (convertTypeofX r) then
    return r
  else
    throw (inexactError "Rational" (Rational T) x)

/--
Julia source: base/rational.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Rational(x::Float64) = Rational{Int64}(x)
```
-/
def rationalFloat64Source {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {F64 : Type}
    (rationalInt64 : F64 → m (Rat .i64)) (x : F64) : m (Rat .i64) :=
  rationalInt64 x

/--
Julia source: base/rational.jl:224-224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Rational(x::Float32) = Rational{Int}(x)
```
-/
def rationalFloat32Source {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {F32 : Type}
    (rationalInt64 : F32 → m (Rat .i64)) (x : F32) : m (Rat .i64) :=
  rationalInt64 x

/--
Julia source: base/rational.jl:226-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(q::Rational) = unsafe_rational(big(numerator(q)), big(denominator(q)))
```
-/
def bigRationalSource {T B : Type} (big : T → B) (q : Rational T) : Rational B :=
  unsafeRationalSameSource (big (numeratorRationalSource q)) (big (denominatorRationalSource q))

/--
Julia source: base/rational.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
big(z::Complex{<:Rational{<:Integer}}) = Complex{Rational{BigInt}}(z)
```
-/
def bigComplexRationalSource {T C : Type}
    (complexRationalBigInt : ComplexValue (Rational T) → C)
    (z : ComplexValue (Rational T)) : C :=
  complexRationalBigInt z

/--
Julia source: base/rational.jl:230-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:Integer} = Rational{promote_type(T,S)}
```
-/
def promoteRuleRatIntSource {α β γ δ : Type}
    (promoteType : α → β → γ) (rationalType : γ → δ) (T : α) (S : β) : δ :=
  rationalType (promoteType T S)

/--
Julia source: base/rational.jl:231-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Rational{T}}, ::Type{Rational{S}}) where {T<:Integer,S<:Integer} = Rational{promote_type(T,S)}
```
-/
def promoteRuleRatRatSource {α β γ δ : Type}
    (promoteType : α → β → γ) (rationalType : γ → δ) (T : α) (S : β) : δ :=
  rationalType (promoteType T S)

/--
Julia source: base/rational.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:AbstractFloat} = promote_type(T,S)
```
-/
def promoteRuleRatFloatSource {α β γ : Type}
    (promoteType : α → β → γ) (T : α) (S : β) : γ :=
  promoteType T S

/--
Julia source: base/rational.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
widen(::Type{Rational{T}}) where {T} = Rational{widen(T)}
```
-/
def widenRatTypeSource {α β γ : Type} (widen : α → β) (rationalType : β → γ) (t : α) : γ :=
  rationalType (widen t)

/--
Julia source: base/rational.jl:236-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline __throw_negate_unsigned() = throw(OverflowError("cannot negate unsigned number"))
```
-/
def throwNegateUnsignedSource {m : Type → Type} [MonadExceptOf JlError m] : m α :=
  throw (.overflowError "cannot negate unsigned number")

/--
Julia source: base/rational.jl:256-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rationalize(::Type{T}, x::AbstractFloat, tol::Real) where T<:Integer
    tol < 0 && throw(ArgumentError("Tolerance can not be negative. tol=$tol"))
    T<:Unsigned && x < 0 && __throw_negate_unsigned()
    isnan(x) && return T(x)//one(T)
    isinf(x) && return unsafe_rational(x < 0 ? -one(T) : one(T), zero(T))

    p,  q  = (x < 0 ? -one(T) : one(T)), zero(T)
    pp, qq = zero(T), one(T)

    x = abs(x)
    a = trunc(x)
    r = x-a
    y = one(x)
    tolx = oftype(x, tol)
    nt, t, tt = tolx, zero(tolx), tolx

    # compute the successive convergents of the continued fraction
    #  np // nq = (p*a + pp) // (q*a + qq)
    while r > nt
        try
            ia = convert(T,a)
            np = checked_add(checked_mul(ia,p),pp)
            nq = checked_add(checked_mul(ia,q),qq)
            p, pp = np, p
            q, qq = nq, q
        catch e
            isa(e,InexactError) || isa(e,OverflowError) || rethrow()
            (a ≤ 2 || ((-p == p) && (p < 0))) && return p // q
            # find best semiconvergent that fits in T
            ia_p = iszero(p) ? typemax(T) : fld(typemax(T) - abs(pp), abs(p))
            ia_q = iszero(q) ? typemax(T) : fld(typemax(T) - qq, q)
            ia = min(ia_p, ia_q)
            return ia > a/2 ? (ia*p + pp) // (ia*q + qq) : p // q
        end

        # naive approach of using
        #   x = 1/r; a = trunc(x); r = x - a
        # is inexact, so we store x as x/y
        x, y = y, r
        a, r = divrem(x,y)

        # maintain
        # x0 = (p + (-1)^i * r) / q
        t, tt = nt, t
        nt = a*t+tt
    end

    # find optimal semiconvergent
    # smallest a such that x-a*y < a*t+tt
    a_min = cld(x-tt,y+t)
    try
        ia = convert(T,a_min)
        np = checked_add(checked_mul(ia,p),pp)
        nq = checked_add(checked_mul(ia,q),qq)
        return np // nq
    catch e
        isa(e,InexactError) || isa(e,OverflowError) || rethrow()
        (a ≤ 2 || ((-p == p) && (p < 0))) && return p // q
        ia_p = iszero(p) ? typemax(T) : fld(typemax(T) - abs(pp), abs(p))
        ia_q = iszero(q) ? typemax(T) : fld(typemax(T) - qq, q)
        ia = min(ia_p, ia_q)
        return ia > a/2 ? (ia*p + pp) // (ia*q + qq) : p // q
    end
end
```
-/
structure GenericRatState (T F : Type) where
  x : F
  y : F
  a : F
  r : F
  nt : F
  tval : F
  tt : F
  p : T
  q : T
  pp : T
  qq : T

def genericConvergentStep {T F : Type} (ops : RatIntOps T)
    (convertTF : F → Jl T) (a : F) (p q pp qq : T) : Jl (T × T) := do
  let ia ← convertTF a
  let np ← ops.checkedAdd (← ops.checkedMul ia p) pp
  let nq ← ops.checkedAdd (← ops.checkedMul ia q) qq
  pure (np, nq)

def genericSemiconvergent {T F : Type} (ops : RatIntOps T)
    (leTwo : F → Bool) (gtHalf : T → F → Bool)
    (exactDivide : T → T → Jl (Rational T))
    (a : F) (p q pp qq : T) : Jl (Rational T) := do
  if leTwo a || (ops.eq (ops.negWrap p) p && ops.signbit p) then
    exactDivide p q
  else
    let maxT := ops.typemax
    let iaP ← if ops.iszero p then pure maxT else
      ops.fld (ops.subWrap maxT (ops.absWrap pp)) (ops.absWrap p)
    let iaQ ← if ops.iszero q then pure maxT else
      ops.fld (ops.subWrap maxT qq) q
    let ia := if ops.le iaP iaQ then iaP else iaQ
    if gtHalf ia a then
      exactDivide (ops.addWrap (ops.mulWrap ia p) pp) (ops.addWrap (ops.mulWrap ia q) qq)
    else
      exactDivide p q

def genericRationalizeWhile {T F : Type} (ops : RatIntOps T)
    (gtF : F → F → Bool) (subF addF mulF cldF : F → F → F)
    (divremF : F → F → F × F) (convertTF : F → Jl T)
    (leTwo : F → Bool) (gtHalf : T → F → Bool)
    (exactDivide : T → T → Jl (Rational T))
    (s : GenericRatState T F) : Option (Jl (Rational T)) :=
  if gtF s.r s.nt then
    match genericConvergentStep ops convertTF s.a s.p s.q s.pp s.qq with
    | .ok (np, nq) =>
      let x := s.y
      let y := s.r
      let (a, r) := divremF x y
      let tt := s.tval
      let tval := s.nt
      let nt := addF (mulF a tval) tt
      genericRationalizeWhile ops gtF subF addF mulF cldF divremF convertTF leTwo gtHalf exactDivide
        ⟨x, y, a, r, nt, tval, tt, np, nq, s.p, s.q⟩
    | .error e =>
      if rationalizeCaught e then
        some (genericSemiconvergent ops leTwo gtHalf exactDivide s.a s.p s.q s.pp s.qq)
      else some (.error e)
  else
    let amin := cldF (subF s.x s.tt) (addF s.y s.tval)
    match genericConvergentStep ops convertTF amin s.p s.q s.pp s.qq with
    | .ok (np, nq) => some (exactDivide np nq)
    | .error e =>
      if rationalizeCaught e then
        some (genericSemiconvergent ops leTwo gtHalf exactDivide s.a s.p s.q s.pp s.qq)
      else some (.error e)
partial_fixpoint

/-- A finite observation of the unbounded loop; none means no result was observed. -/
def genericRationalizeSteps {T F : Type} (ops : RatIntOps T)
    (gtF : F → F → Bool) (subF addF mulF cldF : F → F → F)
    (divremF : F → F → F × F) (convertTF : F → Jl T)
    (leTwo : F → Bool) (gtHalf : T → F → Bool)
    (exactDivide : T → T → Jl (Rational T))
    (fuel : Nat) (s : GenericRatState T F) : Option (Jl (Rational T)) :=
  match fuel with
  | 0 => none
  | fuel + 1 => if gtF s.r s.nt then
    match genericConvergentStep ops convertTF s.a s.p s.q s.pp s.qq with
    | .ok (np, nq) =>
      let x := s.y
      let y := s.r
      let (a, r) := divremF x y
      let tt := s.tval
      let tval := s.nt
      let nt := addF (mulF a tval) tt
      genericRationalizeSteps ops gtF subF addF mulF cldF divremF convertTF leTwo gtHalf exactDivide
        fuel ⟨x, y, a, r, nt, tval, tt, np, nq, s.p, s.q⟩
    | .error e =>
      if rationalizeCaught e then
        some (genericSemiconvergent ops leTwo gtHalf exactDivide s.a s.p s.q s.pp s.qq)
      else some (.error e)
  else
    let amin := cldF (subF s.x s.tt) (addF s.y s.tval)
    match genericConvergentStep ops convertTF amin s.p s.q s.pp s.qq with
    | .ok (np, nq) => some (exactDivide np nq)
    | .error e =>
      if rationalizeCaught e then
        some (genericSemiconvergent ops leTwo gtHalf exactDivide s.a s.p s.q s.pp s.qq)
      else some (.error e)

def rationalizeAbstractFloatSource (T : Type) {F Tol : Type}
    (ops : RatIntOps T) (ltZeroTol : Tol → Bool)
    (ltZeroF isnanF isinfF : F → Bool)
    (absF truncF zeroF oneF : F → F) (oftypeF : F → Tol → F)
    (gtF : F → F → Bool) (subF addF mulF cldF : F → F → F)
    (divremF : F → F → F × F) (convertTF : F → Jl T)
    (leTwo : F → Bool) (gtHalf : T → F → Bool)
    (exactDivide : T → T → Jl (Rational T))
    (x : F) (tol : Tol) (showTol : Tol → String) : ExceptT JlError Option (Rational T) := do
  if ltZeroTol tol then
    throw (.argumentError ("Tolerance can not be negative. tol=" ++ showTol tol))
  if ops.isUnsignedOrBool && ltZeroF x then
    some throwNegateUnsignedSource
  if isnanF x then
    let tx ← some (convertTF x)
    some (exactDivide tx ops.one)
  else if isinfF x then
    return unsafeRationalSameSource (if ltZeroF x then ops.minusOne else ops.one) ops.zero
  else
    let p := if ltZeroF x then ops.minusOne else ops.one
    let q := ops.zero
    let pp := ops.zero
    let qq := ops.one
    let xAbs := absF x
    let a := truncF xAbs
    let r := subF xAbs a
    let y := oneF xAbs
    let tolx := oftypeF xAbs tol
    let nt := tolx
    let tval := zeroF tolx
    let tt := tolx
    genericRationalizeWhile ops gtF subF addF mulF cldF divremF convertTF leTwo gtHalf exactDivide
      ⟨xAbs, y, a, r, nt, tval, tt, p, q, pp, qq⟩

/--
Julia source: base/rational.jl:320-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(::Type{T}, x::AbstractFloat; tol::Real = eps(x)) where {T<:Integer} = rationalize(T, x, tol)
```
-/
def rationalizeFloatDefaultSource {τ α β γ : Type} (eps : α → β)
    (rationalize : τ → α → β → γ) (t : τ) (x : α) : γ :=
  rationalize t x (eps x)

/--
Julia source: base/rational.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(x::Real; kvs...) = rationalize(Int, x; kvs...)
```
-/
def rationalizeRealSourceMethod {α β γ : Type} (rationalize : IntTy → α → β → γ)
    (x : α) (kvs : β) : γ :=
  rationalize .i64 x kvs

/--
Julia source: base/rational.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(::Type{T}, x::Complex; kvs...) where {T<:Integer} = Complex(rationalize(T, x.re; kvs...), rationalize(T, x.im; kvs...))
```
-/
def rationalizeComplexTypedSource {m : Type → Type} [Monad m] {τ α β γ δ : Type}
    (rationalize : τ → α → β → m γ) (complex : γ → γ → δ)
    (t : τ) (z : ComplexValue α) (kvs : β) : m δ := do
  let re ← rationalize t z.re kvs
  let im ← rationalize t z.im kvs
  pure (complex re im)

/--
Julia source: base/rational.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(x::Complex; kvs...) = Complex(rationalize(Int, x.re; kvs...), rationalize(Int, x.im; kvs...))
```
-/
def rationalizeComplexDefaultSource {m : Type → Type} [Monad m] {α β γ δ : Type}
    (rationalize : IntTy → α → β → m γ) (complex : γ → γ → δ)
    (z : ComplexValue α) (kvs : β) : m δ := do
  let re ← rationalize .i64 z.re kvs
  let im ← rationalize .i64 z.im kvs
  pure (complex re im)

/--
Julia source: base/rational.jl:326-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rationalize(::Type{T}, x::Rational, tol::Real) where {T<:Integer}
    T<:Unsigned && x < 0 && __throw_negate_unsigned()
    if !hastypemax(T) || (typemin(T) ≤ x.num ≤ typemax(T) && x.den ≤ typemax(T))
        return Rational{T}(x)
    end
    isfinite(float(x)) && tol ≥ eps(float(x))/2 || throw(InexactError(:rationalize, Rational{T}, x))
    return rationalize(T, float(x), tol)
end
```
-/
def rationalizeRatToleranceGeneric {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {T S F Tol : Type}
    (isUnsignedT hasTypeMaxT : Bool) (ltZero : Rational S → Bool)
    (inBoundsNum leMaxDen : S → Bool)
    (convertRatT : Rational S → m (Rational T))
    (floatX : Rational S → F) (isfinite : F → Bool)
    (epsHalf : F → F) (tolGe : Tol → F → Bool)
    (rationalizeFloat : F → Tol → m (Rational T))
    (x : Rational S) (tol : Tol)
    (inexactError : String → Type → Rational S → JlError) : m (Rational T) := do
  if isUnsignedT && ltZero x then
    throwNegateUnsignedSource
  if !hasTypeMaxT || (inBoundsNum x.num && leMaxDen x.den) then
    convertRatT x
  else if isfinite (floatX x) && tolGe tol (epsHalf (floatX x)) then
    rationalizeFloat (floatX x) tol
  else
    throw (inexactError "rationalize" (Rational T) x)

/--
Julia source: base/rational.jl:324-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(::Type{T}, x::Rational; tol::Real = eps(float(x))) where {T<:Integer} = rationalize(T, x, tol)
```
-/
def rationalizeRatTypedDefaultSource {τ S F Tol R : Type}
    (float : Rational S → F) (eps : F → Tol)
    (rationalize : τ → Rational S → Tol → R)
    (T : τ) (x : Rational S) : R :=
  rationalize T x (eps (float x))

/--
Julia source: base/rational.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(x::Rational{T}; kvs...) where {T<:Integer} = rationalize(T, x; kvs...)
```
-/
def rationalizeRatSource {τ T K R : Type}
    (typeOfT : Rational T → τ) (rationalize : τ → Rational T → K → R)
    (x : Rational T) (kvs : K) : R :=
  rationalize (typeOfT x) x kvs

/--
Julia source: base/rational.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(x::Integer; kvs...) = Rational(x)
```
-/
def rationalizeIntegerGeneric {α κ β : Type} (rational : α → β) (x : α) (_kvs : κ) : β :=
  rational x

/--
Julia source: base/rational.jl:335-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rationalize(::Type{T}, x::Integer; kvs...) where {T<:Integer}
    T<:Unsigned && x < 0 && __throw_negate_unsigned()
    if Base.hastypemax(T) # BigInt doesn't
        x < typemin(T) && return unsafe_rational(-one(T), zero(T))
        x > typemax(T) && return unsafe_rational(one(T), zero(T))
    end
    return Rational{T}(x)
end
```
-/
def rationalizeIntegerTypedSource (T : Type) {I K : Type}
    (opsT : RatIntOps T) (ltZero ltMin gtMax : I → Bool)
    (convertT : I → Jl T) (oneI : I → I)
    (x : I) (_kvs : K) : Jl (Rational T) := do
  if opsT.isUnsignedOrBool && ltZero x then
    throwNegateUnsignedSource
  if opsT.hasTypeMax then
    if ltMin x then
      return unsafeRationalSameSource opsT.minusOne opsT.zero
    if gtMax x then
      return unsafeRationalSameSource opsT.one opsT.zero
    rationalIntAsSource T convertT oneI x
  else
    rationalIntAsSource T convertT oneI x

/--
Julia source: base/rational.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rationalize(::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(rationalize, (Union{}, slurp...)))
```
-/
def rationalizeUnionBottomSource {Args β γ : Type} (slurp : Args) (_kwargs : β) :
    Except (String × (Type × Args)) γ :=
  .error ("rationalize", (Empty, slurp))

/--
Julia source: base/rational.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
numerator(x::Union{Integer,Complex{<:Integer}}) = x
```
-/
def numeratorIntegerOrComplex {α : Type} (x : α) : α := x


/--
Julia source: base/rational.jl:362-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function numerator(z::Complex{<:Rational})
    den = denominator(z)
    reim = (real(z), imag(z))
    result = checked_mul.(numerator.(reim), div.(den, denominator.(reim)))
    complex(result...)
end
```
-/
def numeratorComplexSource {T Z C : Type}
    (real imag : Z → Rational T) (lcm : T → T → Jl T)
    (divide checkedMul : T → T → Jl T) (complex : T → T → C)
    (z : Z) : Jl C := do
  let den ← lcm (denominatorRationalSource (real z)) (denominatorRationalSource (imag z))
  let re := real z
  let im := imag z
  let numRe := numeratorRationalSource re
  let denRe := denominatorRationalSource re
  let qRe ← divide den denRe
  let nRe ← checkedMul numRe qRe
  let numIm := numeratorRationalSource im
  let denIm := denominatorRationalSource im
  let qIm ← divide den denIm
  let nIm ← checkedMul numIm qIm
  pure (complex nRe nIm)

/--
Julia source: base/rational.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
denominator(x::Union{Integer,Complex{<:Integer}}) = one(x)
```
-/
def denominatorIntegerOrComplex {α : Type} (one : α → α) (x : α) : α := one x


/--
Julia source: base/rational.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
denominator(z::Complex{<:Rational}) = lcm(denominator(real(z)), denominator(imag(z)))
```
-/
def denominatorComplexSource {T Z L : Type}
    (real imag : Z → Rational T) (lcm : T → T → L) (z : Z) : L :=
  lcm (denominatorRationalSource (real z)) (denominatorRationalSource (imag z))

/--
Julia source: base/rational.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sign(x::Rational) = oftype(x, sign(x.num))
```
-/
def signRatSource {T : Type}
    (oftype : Rational T → T → Rational T) (sign : T → T) (x : Rational T) : Rational T :=
  oftype x (sign x.num)

/--
Julia source: base/rational.jl:388-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
signbit(x::Rational) = signbit(x.num)
```
-/
def signbitRatSource {T : Type} (signbit : T → Bool) (x : Rational T) : Bool :=
  signbit x.num

/--
Julia source: base/rational.jl:390-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abs(x::Rational) = unsafe_rational(checked_abs(x.num), x.den)
```
-/
def absRatSource {T : Type} (checkedAbs : T → Jl T) (x : Rational T) : Jl (Rational T) := do
  let n ← checkedAbs x.num
  return unsafeRationalSameSource n x.den

/--
Julia source: base/rational.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Rational{T}}) where {T<:Signed} = unsafe_rational(T, -one(T), zero(T))
```
-/
def typeminSignedRatSource (T : Type) (one zero : T) (neg : T → T) : Rational T :=
  unsafeRationalTypeSource (m := Id) T id id (neg one) zero

/--
Julia source: base/rational.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemin(::Type{Rational{T}}) where {T<:Integer} = unsafe_rational(T, zero(T), one(T))
```
-/
def typeminOtherRatSource (T : Type) (zero one : T) : Rational T :=
  unsafeRationalTypeSource (m := Id) T id id zero one

/--
Julia source: base/rational.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typemax(::Type{Rational{T}}) where {T<:Integer} = unsafe_rational(T, one(T), zero(T))
```
-/
def typemaxRatSource (T : Type) (one zero : T) : Rational T :=
  unsafeRationalTypeSource (m := Id) T id id one zero

/--
Julia source: base/rational.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinteger(x::Rational) = x.den == 1
```
-/
def isIntegerRatSource {T : Type} (eqOne : T → Bool) (x : Rational T) : Bool :=
  eqOne x.den

/--
Julia source: base/rational.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ispow2(x::Rational) = ispow2(x.num) & ispow2(x.den)
```
-/
def isPow2RatSource {T : Type} (ispow2 : T → Bool) (x : Rational T) : Bool :=
  bwand (ispow2 x.num) (ispow2 x.den)

/--
Julia source: base/rational.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(x::Rational) = unsafe_rational(+x.num, x.den)
```
-/
def unaryPlusRatSource {T : Type} (uplus : T → T) (x : Rational T) : Rational T :=
  unsafeRationalSameSource (uplus x.num) x.den

/--
Julia source: base/rational.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(x::Rational) = unsafe_rational(-x.num, x.den)
```
-/
def negRatSource {T : Type} (neg : T → Jl T) (x : Rational T) : Jl (Rational T) := do
  let n ← neg x.num
  return unsafeRationalSameSource n x.den

/--
Julia source: base/rational.jl:406-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline __throw_rational_numerator_typemin(T) = throw(OverflowError(LazyString("rational numerator is typemin(", T, ")")))
```
-/
def throwNumeratorTypeminSource {τ ε α : Type}
    (overflowError : LazyString τ → ε) (T : τ) : Except ε α :=
  .error (overflowError (LazyString.build [.lit "rational numerator is typemin(", .val T, .lit ")"]))

/--
Julia source: base/rational.jl:402-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(x::Rational{T}) where T<:BitSigned
    x.num == typemin(T) && __throw_rational_numerator_typemin(T)
    unsafe_rational(-x.num, x.den)
end
```
-/
def negBitSignedSource {t : IntTy} (_h : t.signed = true) (x : Rat t) : Jl (Rat t) := do
  if x.num == JInt.typemin t then
    throwNumeratorTypeminSource (fun s => JlError.overflowError (s.render IntTy.name)) t
  else
    return unsafeRationalSameSource (-x.num) x.den

/--
Julia source: base/rational.jl:408-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(x::Rational{T}) where T<:Unsigned
    x.num != zero(T) && __throw_negate_unsigned()
    x
end
```
-/
def negUnsignedSource {T : Type} (zero : T) (ne : T → T → Bool) (x : Rational T) : Jl (Rational T) := do
  if ne x.num zero then
    throwNegateUnsignedSource
  else
    return x

/--
Julia source: base/rational.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-%(x::Rational) = unsafe_rational(-%(x.num), x.den)
```
-/
def negWrapRatSource {T : Type} (negWrap : T → T) (x : Rational T) : Rational T :=
  unsafeRationalSameSource (negWrap x.num) x.den

/--
Julia source: base/rational.jl:415-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function +(x::Rational, y::Rational)
    xp, _ = promote(x, y)::NTuple{2,Rational}
    if isinf(x) && x == y
        return xp
    end
    xd, yd = divgcd(promote(x.den, y.den)...)
    Rational(checked_add(checked_mul(x.num, yd), checked_mul(y.num, xd)), checked_mul(x.den, yd))
end
```
-/
def addRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (promoteRat : Rational TX → Rational TY → Jl (Rational P × Rational P))
    (isinfX : Rational TX → Bool) (eqXY : Rational TX → Rational TY → Bool)
    (divgcd : P → P → Jl (P × P)) (rationalP : P → P → Jl (Rational P))
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xp, _) ← promoteRat x y
  if isinfX x && eqXY x y then
    return xp
  else
    let (xdenP, ydenP) ← prom.promote x.den y.den
    let (xd, yd) ← divgcd xdenP ydenP
    let a ← prom.checkedMulXP x.num yd
    let b ← prom.checkedMulYP y.num xd
    let n ← prom.opsP.checkedAdd a b
    let d ← prom.checkedMulXP x.den yd
    rationalP n d

/--
Julia source: base/rational.jl:424-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function +%(x::Rational, y::Rational)
    xp, yp = promote(x, y)::NTuple{2,Rational}
    if isinf(x) && x == y
        return xp
    end
    xd, yd = divgcd(promote(x.den, y.den)...)
    Rational(+%(*%(x.num,yd), *%(y.num,xd)), *%(x.den,yd))
end
```
-/
def addWrapRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (promoteRat : Rational TX → Rational TY → Jl (Rational P × Rational P))
    (isinfX : Rational TX → Bool) (eqXY : Rational TX → Rational TY → Bool)
    (divgcd : P → P → Jl (P × P)) (rationalP : P → P → Jl (Rational P))
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xp, _) ← promoteRat x y
  if isinfX x && eqXY x y then
    return xp
  else
    let (xdenP, ydenP) ← prom.promote x.den y.den
    let (xd, yd) ← divgcd xdenP ydenP
    let n := prom.opsP.addWrap (prom.mulWrapXP x.num yd) (prom.mulWrapYP y.num xd)
    let d := prom.mulWrapXP x.den yd
    rationalP n d

/--
Julia source: base/rational.jl:433-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -(x::Rational, y::Rational)
    xp, _ = promote(x, y)::NTuple{2,Rational}
    if isinf(x) && x == -y
        return xp
    end
    xd, yd = divgcd(promote(x.den, y.den)...)
    Rational(checked_sub(checked_mul(x.num, yd), checked_mul(y.num, xd)), checked_mul(x.den, yd))
end
```
-/
def subRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (promoteRat : Rational TX → Rational TY → Jl (Rational P × Rational P))
    (isinfX : Rational TX → Bool) (negY : Rational TY → Jl (Rational TY))
    (eqXY : Rational TX → Rational TY → Bool)
    (divgcd : P → P → Jl (P × P)) (rationalP : P → P → Jl (Rational P))
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xp, _) ← promoteRat x y
  let isSameInf ←
    if isinfX x then
      let ny ← negY y
      pure (eqXY x ny)
    else
      pure false
  if isSameInf then
    return xp
  else
    let (xdenP, ydenP) ← prom.promote x.den y.den
    let (xd, yd) ← divgcd xdenP ydenP
    let a ← prom.checkedMulXP x.num yd
    let b ← prom.checkedMulYP y.num xd
    let n ← prom.opsP.checkedSub a b
    let d ← prom.checkedMulXP x.den yd
    rationalP n d

/--
Julia source: base/rational.jl:442-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function -%(x::Rational, y::Rational)
    xp, yp = promote(x, y)::NTuple{2,Rational}
    if isinf(x) && x == -y
        return xp
    end
    xd, yd = divgcd(promote(x.den, y.den)...)
    Rational(-%(*%(x.num, yd), *%(y.num, xd)), *%(x.den, yd))
end
```
-/
def subWrapRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (promoteRat : Rational TX → Rational TY → Jl (Rational P × Rational P))
    (isinfX : Rational TX → Bool) (negY : Rational TY → Jl (Rational TY))
    (eqXY : Rational TX → Rational TY → Bool)
    (divgcd : P → P → Jl (P × P)) (rationalP : P → P → Jl (Rational P))
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xp, _) ← promoteRat x y
  let isSameInf ←
    if isinfX x then
      let ny ← negY y
      pure (eqXY x ny)
    else
      pure false
  if isSameInf then
    return xp
  else
    let (xdenP, ydenP) ← prom.promote x.den y.den
    let (xd, yd) ← divgcd xdenP ydenP
    let n := prom.opsP.subWrap (prom.mulWrapXP x.num yd) (prom.mulWrapYP y.num xd)
    let d := prom.mulWrapXP x.den yd
    rationalP n d

/--
Julia source: base/rational.jl:451-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op,chop) in ((:rem,:rem), (:mod,:mod))
    @eval begin
        function ($op)(x::Rational, y::Rational)
            xd, yd = divgcd(promote(x.den, y.den)...)
            Rational(($chop)(checked_mul(x.num,yd), checked_mul(y.num,xd)), checked_mul(x.den,yd))
        end
    end
end
```
-/
def remRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (rationalP : P → P → Jl (Rational P))
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xdenP, ydenP) ← prom.promote x.den y.den
  let (xd, yd) ← divgcd xdenP ydenP
  let a ← prom.checkedMulXP x.num yd
  let b ← prom.checkedMulYP y.num xd
  let n ← prom.opsP.rem a b
  let d ← prom.checkedMulXP x.den yd
  rationalP n d

/--
Julia source: base/rational.jl:451-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op,chop) in ((:rem,:rem), (:mod,:mod))
    @eval begin
        function ($op)(x::Rational, y::Rational)
            xd, yd = divgcd(promote(x.den, y.den)...)
            Rational(($chop)(checked_mul(x.num,yd), checked_mul(y.num,xd)), checked_mul(x.den,yd))
        end
    end
end
```
-/
def modRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (rationalP : P → P → Jl (Rational P))
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xdenP, ydenP) ← prom.promote x.den y.den
  let (xd, yd) ← divgcd xdenP ydenP
  let a ← prom.checkedMulXP x.num yd
  let b ← prom.checkedMulYP y.num xd
  let n ← prom.opsP.mod a b
  let d ← prom.checkedMulXP x.den yd
  rationalP n d

/--
Julia source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op,chop) in ((:+,:checked_add), (:-,:checked_sub), (:rem,:rem), (:mod,:mod))
    @eval begin
        function ($op)(x::Rational, y::Integer)
            unsafe_rational(($chop)(x.num, checked_mul(x.den, y)), x.den)
        end
    end
end
```
-/
def rationalIntegerOpSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (chop : TX → P → Jl P) (x : Rational TX) (y : TY) : Jl (Rational P) := do
  let d ← prom.checkedMulXY x.den y
  let n ← chop x.num d
  unsafeRationalPromoteSource prom.promotePX n x.den

/--
Julia source: base/rational.jl:467-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op,chop) in ((:+,:checked_add), (:-,:checked_sub))
    @eval begin
        function ($op)(y::Integer, x::Rational)
            unsafe_rational(($chop)(checked_mul(x.den, y), x.num), x.den)
        end
    end
end
```
-/
def integerRationalOpSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (chop : P → TX → Jl P) (y : TY) (x : Rational TX) : Jl (Rational P) := do
  let a ← prom.checkedMulXY x.den y
  let n ← chop a x.num
  unsafeRationalPromoteSource prom.promotePX n x.den

/--
Julia source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (op,chop) in ((:rem,:rem), (:mod,:mod))
    @eval begin
        function ($op)(y::Integer, x::Rational)
            Rational(($chop)(checked_mul(x.den, y), x.num), x.den)
        end
    end
end
```
-/
def integerRationalRemainderSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (chop : P → TX → Jl P) (rationalP : P → TX → Jl (Rational P))
    (y : TY) (x : Rational TX) : Jl (Rational P) := do
  let a ← prom.checkedMulXY x.den y
  let n ← chop a x.num
  rationalP n x.den

/--
Julia source: base/rational.jl:482-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function *(x::Rational, y::Rational)
    xn, yd = divgcd(promote(x.num, y.den)...)
    xd, yn = divgcd(promote(x.den, y.num)...)
    unsafe_rational(checked_mul(xn, yn), checked_mul(xd, yd))
end
```
-/
def mulRatRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  let (xnumP, ydenP) ← prom.promote x.num y.den
  let (xn, yd) ← divgcd xnumP ydenP
  let (xdenP, ynumP) ← prom.promote x.den y.num
  let (xd, yn) ← divgcd xdenP ynumP
  let n ← prom.opsP.checkedMul xn yn
  let d ← prom.opsP.checkedMul xd yd
  return unsafeRationalSameSource n d

/--
Julia source: base/rational.jl:487-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function *(x::Rational, y::Integer)
    xd, yn = divgcd(promote(x.den, y)...)
    unsafe_rational(checked_mul(x.num, yn), xd)
end
```
-/
def mulRatIntSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (x : Rational TX) (y : TY) : Jl (Rational P) := do
  let (xdenP, yP) ← prom.promote x.den y
  let (xd, yn) ← divgcd xdenP yP
  let n ← prom.checkedMulXP x.num yn
  return unsafeRationalSameSource n xd

/--
Julia source: base/rational.jl:491-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function *(y::Integer, x::Rational)
    yn, xd = divgcd(promote(y, x.den)...)
    unsafe_rational(checked_mul(yn, x.num), xd)
end
```
-/
def mulIntRatSource {TX TY P : Type} (prom : RatPromoteOps TX TY P)
    (divgcd : P → P → Jl (P × P)) (y : TY) (x : Rational TX) : Jl (Rational P) := do
  let (xdenP, yP) ← prom.promote x.den y
  let (yn, xd) ← divgcd yP xdenP
  let n ← prom.checkedMulPX yn x.num
  return unsafeRationalSameSource n xd

/--
Julia source: base/rational.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function *(x::Bool, y::T)::promote_type(Bool,T) where T<:Rational
    return ifelse(x, y, copysign(zero(y), y))
end
```
-/
def boolMulRatSource {T : Type}
    (ifelse : Bool → Rational T → Rational T → Rational T)
    (zero : Rational T → Rational T) (copysign : Rational T → Rational T → Rational T)
    (x : Bool) (y : Rational T) : Rational T :=
  ifelse x y (copysign (zero y) y)

/--
Julia source: base/rational.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
*(y::Rational, x::Bool) = x * y
```
-/
def mulRatBoolSource {α β : Type} (mul : Bool → α → β) (y : α) (x : Bool) : β :=
  mul x y

/--
Julia source: base/rational.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(x::Rational, y::Union{Rational, Integer}) = x//y
```
-/
def slashRationalUnionSource {T Y R : Type}
    (exactDivide : Rational T → Y → R) (x : Rational T) (y : Y) : R :=
  exactDivide x y

/--
Julia source: base/rational.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
/(x::Integer, y::Rational) = x//y
```
-/
def slashIntegerRationalSource {X T R : Type}
    (exactDivide : X → Rational T → R) (x : X) (y : Rational T) : R :=
  exactDivide x y

/--
Julia source: base/rational.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
inv(x::Rational{T}) where {T} = checked_den(x.den, x.num)
```
-/
def invRatSource {T : Type} (ops : RatIntOps T) (x : Rational T) : Jl (Rational T) :=
  checkedDenSameSource ops x.den x.num

/--
Julia source: base/rational.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fma(x::Rational, y::Rational, z::Rational) = x*y+z
```
-/
def fmaRatSource {TX TY TZ P Q : Type}
    (mul : Rational TX → Rational TY → Jl (Rational P))
    (add : Rational P → Rational TZ → Jl (Rational Q))
    (x : Rational TX) (y : Rational TY) (z : Rational TZ) : Jl (Rational Q) := do
  let xy ← mul x y
  add xy z

/--
Julia source: base/rational.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Rational, y::Rational) = (x.den == y.den) & (x.num == y.num)
```
-/
def eqRatSource {TX TY : Type}
    (eqDen : TX → TY → Bool) (eqNum : TX → TY → Bool)
    (x : Rational TX) (y : Rational TY) : Bool :=
  bwand (eqDen x.den y.den) (eqNum x.num y.num)

/--
Julia source: base/rational.jl:508-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::Rational, y::Rational) = x.den == y.den ? x.num < y.num :
                               widemul(x.num,y.den) < widemul(x.den,y.num)
```
-/
def ltRatSource {TX TY WX WY : Type}
    (eqDen : TX → TY → Bool) (ltNum : TX → TY → Bool)
    (widemulXY : TX → TY → WX) (widemulYX : TX → TY → WY)
    (ltWide : WX → WY → Bool)
    (x : Rational TX) (y : Rational TY) : Bool :=
  if eqDen x.den y.den then
    ltNum x.num y.num
  else
    ltWide (widemulXY x.num y.den) (widemulYX x.den y.num)

/--
Julia source: base/rational.jl:510-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Rational, y::Rational) = x.den == y.den ? x.num <= y.num :
                               widemul(x.num,y.den) <= widemul(x.den,y.num)
```
-/
def leRatSource {TX TY WX WY : Type}
    (eqDen : TX → TY → Bool) (leNum : TX → TY → Bool)
    (widemulXY : TX → TY → WX) (widemulYX : TX → TY → WY)
    (leWide : WX → WY → Bool)
    (x : Rational TX) (y : Rational TY) : Bool :=
  if eqDen x.den y.den then
    leNum x.num y.num
  else
    leWide (widemulXY x.num y.den) (widemulYX x.den y.num)

/--
Julia source: base/rational.jl:514-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Rational, y::Integer ) = (x.den == 1) & (x.num == y)
```
-/
def eqRatIntSource {T I : Type}
    (eqOne : T → Bool) (eqNum : T → I → Bool)
    (x : Rational T) (y : I) : Bool :=
  bwand (eqOne x.den) (eqNum x.num y)

/--
Julia source: base/rational.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Integer , y::Rational) = y == x
```
-/
def eqIntRatSource {I T : Type}
    (eqOne : T → Bool) (eqNum : T → I → Bool)
    (x : I) (y : Rational T) : Bool :=
  eqRatIntSource eqOne eqNum y x

/--
Julia source: base/rational.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::Rational, y::Integer ) = x.num < widemul(x.den,y)
```
-/
def ltRatIntSource {T I W : Type}
    (widemul : T → I → W) (lt : T → W → Bool)
    (x : Rational T) (y : I) : Bool :=
  lt x.num (widemul x.den y)

/--
Julia source: base/rational.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::Integer , y::Rational) = widemul(x,y.den) < y.num
```
-/
def ltIntRatSource {I T W : Type}
    (widemul : I → T → W) (lt : W → T → Bool)
    (x : I) (y : Rational T) : Bool :=
  lt (widemul x y.den) y.num

/--
Julia source: base/rational.jl:518-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Rational, y::Integer ) = x.num <= widemul(x.den,y)
```
-/
def leRatIntSource {T I W : Type}
    (widemul : T → I → W) (le : T → W → Bool)
    (x : Rational T) (y : I) : Bool :=
  le x.num (widemul x.den y)

/--
Julia source: base/rational.jl:519-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Integer , y::Rational) = widemul(x,y.den) <= y.num
```
-/
def leIntRatSource {I T W : Type}
    (widemul : I → T → W) (le : W → T → Bool)
    (x : I) (y : Rational T) : Bool :=
  le (widemul x y.den) y.num

/--
Julia source: base/rational.jl:521-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(x::AbstractFloat, q::Rational)
    if isfinite(x)
        (count_ones(q.den) == 1) && (ldexp(x, top_set_bit(q.den-1)) == q.num)
    else
        x == q.num/q.den
    end
end
```
-/
def eqFloatRatSource {F T C B G : Type}
    (isfinite : F → Bool) (countOnes : T → C) (eqOneC : C → Bool)
    (subOne : T → T) (topSetBit : T → B) (ldexp : F → B → F)
    (eqFI : F → T → Bool) (div : T → T → G) (eqFF : F → G → Bool)
    (x : F) (q : Rational T) : Bool :=
  if isfinite x then
    eqOneC (countOnes q.den) && eqFI (ldexp x (topSetBit (subOne q.den))) q.num
  else
    eqFF x (div q.num q.den)

/--
Julia source: base/rational.jl:529-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(q::Rational, x::AbstractFloat) = x == q
```
-/
def eqRatFloatSource {F T C B G : Type}
    (isfinite : F → Bool) (countOnes : T → C) (eqOneC : C → Bool)
    (subOne : T → T) (topSetBit : T → B) (ldexp : F → B → F)
    (eqFI : F → T → Bool) (div : T → T → G) (eqFF : F → G → Bool)
    (q : Rational T) (x : F) : Bool :=
  eqFloatRatSource isfinite countOnes eqOneC subOne topSetBit ldexp eqFI div eqFF x q

/--
Julia source: base/rational.jl:531-580 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for rel in (:<,:<=,:cmp)
    for (Tx,Ty) in ((Rational,AbstractFloat), (AbstractFloat,Rational))
        @eval function ($rel)(x::$Tx, y::$Ty)
            if isnan(x)
                $(rel === :cmp ? :(return isnan(y) ? 0 : 1) :
                                :(return false))
            end
            if isnan(y)
                $(rel === :cmp ? :(return -1) :
                                :(return false))
            end

            xn, xp, xd = decompose(x)
            yn, yp, yd = decompose(y)

            if xd < 0
                xn = -xn
                xd = -xd
            end
            if yd < 0
                yn = -yn
                yd = -yd
            end

            xc, yc = widemul(xn,yd), widemul(yn,xd)
            xs, ys = sign(xc), sign(yc)

            if xs != ys
                return ($rel)(xs,ys)
            elseif xs == 0
                # both are zero or ±Inf
                return ($rel)(xn,yn)
            end

            xb, yb = ndigits0z(xc,2) + xp, ndigits0z(yc,2) + yp

            if xb == yb
                xc, yc = promote(xc,yc)
                if xp > yp
                    xc = (xc<<(xp-yp))
                else
                    yc = (yc<<(yp-xp))
                end
                return ($rel)(xc,yc)
            else
                return xc > 0 ? ($rel)(xb,yb) : ($rel)(yb,xb)
            end
        end
    end
end
```
-/
def rationalFloatRelationSource {α β γ : Type}
    (isnanX : α → Bool) (isnanY : β → Bool) (onNanX : β → γ) (onNanY : γ)
    (decomposeX : α → Int × Int × Int) (decomposeY : β → Int × Int × Int)
    (widemul : Int → Int → Int) (sign : Int → Int)
    (ndigits0z : Int → Int → Int) (promote : Int → Int → Int × Int)
    (shiftLeft : Int → Int → Int) (rel : Int → Int → γ) (x : α) (y : β) : γ :=
  if isnanX x then onNanX y
  else if isnanY y then onNanY
  else
    let (xn, xp, xd) := decomposeX x
    let (yn, yp, yd) := decomposeY y
    let (xn, xd) := if xd < 0 then (-xn, -xd) else (xn, xd)
    let (yn, yd) := if yd < 0 then (-yn, -yd) else (yn, yd)
    let xc := widemul xn yd
    let yc := widemul yn xd
    let xs := sign xc
    let ys := sign yc
    if xs != ys then rel xs ys
    else if xs = 0 then rel xn yn
    else
      let xb := ndigits0z xc 2 + xp
      let yb := ndigits0z yc 2 + yp
      if xb = yb then
        let (xc, yc) := promote xc yc
        if xp > yp then rel (shiftLeft xc (xp - yp)) yc
        else rel xc (shiftLeft yc (yp - xp))
      else if xc > 0 then rel xb yb else rel yb xb

/--
Julia source: base/rational.jl:583-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(z::Complex , x::Rational) = isreal(z) & (real(z) == x)
```
-/
def eqComplexRatSource {α β : Type} (isreal : α → Bool) (real : α → β)
    (eq : β → β → Bool) (z : α) (x : β) : Bool :=
  bwand (isreal z) (eq (real z) x)

/--
Julia source: base/rational.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Rational, z::Complex ) = isreal(z) & (real(z) == x)
```
-/
def eqRatComplexSource {α β : Type} (isreal : α → Bool) (real : α → β)
    (eq : β → β → Bool) (x : β) (z : α) : Bool :=
  bwand (isreal z) (eq (real z) x)

/--
Julia source: base/rational.jl:586-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Rational, y::Integer, r::RoundingMode)
    xn,yn = divgcd(x.num,y)
    div(xn, checked_mul(x.den,yn), r)
end
```
-/
def divRationalIntegerRoundedSource {TX TY P Q : Type}
    (divgcd : TX → TY → Jl (TX × TY))
    (checkedMul : TX → TY → Jl P)
    (div : TX → P → Rounding → Jl Q)
    (x : Rational TX) (y : TY) (r : Rounding) : Jl Q := do
  let (xn, yn) ← divgcd x.num y
  let d ← checkedMul x.den yn
  div xn d r

/--
Julia source: base/rational.jl:590-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Integer, y::Rational, r::RoundingMode)
    xn,yn = divgcd(x,y.num)
    div(checked_mul(xn,y.den), yn, r)
end
```
-/
def divIntegerRationalRoundedSource {TX TY P Q : Type}
    (divgcd : TX → TY → Jl (TX × TY))
    (checkedMul : TX → TY → Jl P)
    (div : P → TY → Rounding → Jl Q)
    (x : TX) (y : Rational TY) (r : Rounding) : Jl Q := do
  let (xn, yn) ← divgcd x y.num
  let n ← checkedMul xn y.den
  div n yn r

/--
Julia source: base/rational.jl:594-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function div(x::Rational, y::Rational, r::RoundingMode)
    xn,yn = divgcd(x.num,y.num)
    xd,yd = divgcd(x.den,y.den)
    div(checked_mul(xn,yd), checked_mul(xd,yn), r)
end
```
-/
def divRationalRationalRoundedSource {TX TY P Q R : Type}
    (divgcdNum : TX → TY → Jl (TX × TY))
    (divgcdDen : TX → TY → Jl (TX × TY))
    (checkedMulN : TX → TY → Jl P)
    (checkedMulD : TX → TY → Jl Q)
    (div : P → Q → Rounding → Jl R)
    (x : Rational TX) (y : Rational TY) (r : Rounding) : Jl R := do
  let (xn, yn) ← divgcdNum x.num y.num
  let (xd, yd) ← divgcdDen x.den y.den
  let n ← checkedMulN xn yd
  let d ← checkedMulD xd yn
  div n d r

inductive RationalInvokeTarget where
  | tupleRationalRationalRoundingMode
  deriving DecidableEq, Repr

/--
Julia source: base/rational.jl:602-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div(x::T, y::T, r::RoundingMode) where {T<:Rational} =
    invoke(div, Tuple{Rational, Rational, RoundingMode}, x, y, r)
```
-/
def divCompatibilitySource {T R : Type}
    (div : Rational T → Rational T → Rounding → R)
    (invoke : (Rational T → Rational T → Rounding → R) → RationalInvokeTarget →
      Rational T → Rational T → Rounding → R)
    (x y : Rational T) (r : Rounding) : R :=
  invoke div .tupleRationalRationalRoundingMode x y r

/--
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
    @eval begin
        div(x::$S, y::$T) = div(x, y, RoundToZero)
        fld(x::$S, y::$T) = div(x, y, RoundDown)
        cld(x::$S, y::$T) = div(x, y, RoundUp)
    end
end
```
-/
def divDefaultSource {α β γ : Type} (div : α → β → Rounding → γ) (x : α) (y : β) : γ :=
  div x y .toZero

/--
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
    @eval begin
        div(x::$S, y::$T) = div(x, y, RoundToZero)
        fld(x::$S, y::$T) = div(x, y, RoundDown)
        cld(x::$S, y::$T) = div(x, y, RoundUp)
    end
end
```
-/
def fldDefaultSource {α β γ : Type} (div : α → β → Rounding → γ) (x : α) (y : β) : γ :=
  div x y .down

/--
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
    @eval begin
        div(x::$S, y::$T) = div(x, y, RoundToZero)
        fld(x::$S, y::$T) = div(x, y, RoundDown)
        cld(x::$S, y::$T) = div(x, y, RoundUp)
    end
end
```
-/
def cldDefaultSource {α β γ : Type} (div : α → β → Rounding → γ) (x : α) (y : β) : γ :=
  div x y .up

/--
Julia source: base/rational.jl:612-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
round(x::Rational, r::RoundingMode=RoundNearest) = round(typeof(x), x, r)
```
-/
def roundRatDefaultSource {T τ R : Type}
    (typeof : Rational T → τ) (round : τ → Rational T → Rounding → R)
    (x : Rational T) (r : Rounding := .nearest) : R :=
  round (typeof x) x r

/--
Julia source: base/rational.jl:614-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function round(::Type{T}, x::Rational{Tr}, r::RoundingMode=RoundNearest) where {T,Tr}
    if iszero(denominator(x)) && !(T <: Integer)
        return convert(T, copysign(unsafe_rational(one(Tr), zero(Tr)), numerator(x)))
    end
    convert(T, div(numerator(x), denominator(x), r))
end
```
-/
def roundRatTypedSource (T : Type) {Tr Q : Type}
    (iszero : Tr → Bool) (targetIsInteger : Bool)
    (one zero : Tr) (copysign : Rational Tr → Tr → Rational Tr)
    (convertInf : Rational Tr → Jl T)
    (div : Tr → Tr → Rounding → Jl Q)
    (convertQuot : Q → Jl T)
    (x : Rational Tr) (r : Rounding := .nearest) : Jl T := do
  if iszero (denominatorRationalSource x) && !targetIsInteger then
    convertInf (copysign (unsafeRationalSameSource one zero) (numeratorRationalSource x))
  else
    let q ← div (numeratorRationalSource x) (denominatorRationalSource x) r
    convertQuot q

/--
Julia source: base/rational.jl:621-626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function round(::Type{T}, x::Rational{Bool}, ::RoundingMode=RoundNearest) where T
    if denominator(x) == false && (T <: Integer)
        throw(DivideError())
    end
    convert(T, x)
end
```
-/
def roundBoolRationalSource (T : Type) (targetIsInteger : Bool)
    (convert : Rational Bool → Jl T) (x : Rational Bool)
    (_r : Rounding := .nearest) : Jl T :=
  if denominatorRationalSource x == false && targetIsInteger then
    .error .divideError
  else
    convert x

abbrev roundBoolRational {α β : Type} (denominatorFalse targetIsInteger : Bool)
    (convert : α → Jl β) (x : α) : Jl β :=
  if denominatorFalse && targetIsInteger then .error .divideError else convert x

/--
Julia source: base/rational.jl:628-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ^(x::Rational, n::Integer)
    n >= 0 ? power_by_squaring(x,n) : power_by_squaring(inv(x),-n)
end
```
-/
def powRationalIntegerGeneric {T N R : Type}
    (geZero : N → Bool) (neg : N → N)
    (inverse : Rational T → Jl (Rational T))
    (powerBySquaring : Rational T → N → Jl R)
    (x : Rational T) (n : N) : Jl R := do
  if geZero n then
    powerBySquaring x n
  else
    let invX ← inverse x
    powerBySquaring invX (neg n)

def powRationalIntegerSource {t s : IntTy}
    (powerBySquaring : Rat t → JInt s → Jl (Rat t))
    (x : Rat t) (n : JInt s) : Jl (Rat t) :=
  powRationalIntegerGeneric (fun m => decide (m.val ≥ 0)) (fun m => -m) (invRatSource (jintOps t)) powerBySquaring x n

/--
Julia source: base/rational.jl:632-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::Number, y::Rational) = x^(y.num/y.den)
```
-/
def powNumberRationalSource {T α β γ : Type}
    (divide : T → T → β) (power : α → β → γ) (x : α) (y : Rational T) : γ :=
  power x (divide y.num y.den)

/--
Julia source: base/rational.jl:633-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::T, y::Rational) where {T<:AbstractFloat} = x^convert(T,y)
```
-/
def powFloatRationalSource {T α β : Type}
    (convert : Rational T → α) (power : β → α → β) (x : β) (y : Rational T) : β :=
  power x (convert y)

/--
Julia source: base/rational.jl:634-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex{T}, p::Rational) where {T<:Real} = z^convert(typeof(one(T)^p), p)
```
-/
def powComplexRationalSource {T α β γ δ : Type}
    (onePower : Rational T → β) (typeOf : β → γ) (convert : γ → Rational T → δ)
    (power : α → δ → α) (z : α) (p : Rational T) : α :=
  power z (convert (typeOf (onePower p)) p)

/--
Julia source: base/rational.jl:636-636 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex{<:Rational}, n::Bool) = n ? z : one(z) # to resolve ambiguity
```
-/
def powComplexRationalBoolSource {α : Type} (one : α → α) (z : α) (n : Bool) : α :=
  if n then z else one z

/--
Julia source: base/rational.jl:637-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ^(z::Complex{<:Rational}, n::Integer)
    n >= 0 ? power_by_squaring(z,n) : power_by_squaring(inv(z),-n)
end
```
-/
def powComplexRationalIntegerGeneric {Z N R : Type}
    (geZero : N → Bool) (neg : N → N)
    (inverse : Z → Jl Z) (powerBySquaring : Z → N → Jl R)
    (z : Z) (n : N) : Jl R := do
  if geZero n then
    powerBySquaring z n
  else
    let invZ ← inverse z
    powerBySquaring invZ (neg n)

def powComplexRationalIntegerSource {α : Type} {t : IntTy}
    (inverse : α → Jl α) (powerBySquaring : α → JInt t → Jl α)
    (z : α) (n : JInt t) : Jl α :=
  powComplexRationalIntegerGeneric (fun m => decide (m.val ≥ 0)) (fun m => -m) inverse powerBySquaring z n

/--
Julia source: base/rational.jl:641-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iszero(x::Rational) = iszero(numerator(x))
```
-/
def isZeroRationalSource {T : Type} (iszero : T → Bool) (x : Rational T) : Bool :=
  iszero (numeratorRationalSource x)

/--
Julia source: base/rational.jl:642-642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isone(x::Rational) = isone(numerator(x)) & isone(denominator(x))
```
-/
def isOneRationalSource {T : Type} (isone : T → Bool) (x : Rational T) : Bool :=
  bwand (isone (numeratorRationalSource x)) (isone (denominatorRationalSource x))

/--
Julia source: base/rational.jl:644-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lerpi(j::Integer, d::Integer, a::Rational, b::Rational)
    ((d-j)*a)/d + (j*b)/d
end
```
-/
def lerpiSource {J D TA TB DSub Left QLeft Right QRight R : Type}
    (sub : D → J → DSub) (mulLeft : DSub → Rational TA → Jl Left)
    (divLeft : Left → D → Jl QLeft) (mulRight : J → Rational TB → Jl Right)
    (divRight : Right → D → Jl QRight) (add : QLeft → QRight → Jl R)
    (j : J) (d : D) (a : Rational TA) (b : Rational TB) : Jl R := do
  let lmul ← mulLeft (sub d j) a
  let ldiv ← divLeft lmul d
  let rmul ← mulRight j b
  let rdiv ← divRight rmul d
  add ldiv rdiv

/--
Julia source: base/rational.jl:648-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
float(::Type{Rational{T}}) where {T<:Integer} = float(T)
```
-/
def floatTypeSource {τ α : Type} (float : τ → α) (T : τ) : α := float T

/--
Julia source: base/rational.jl:650-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcd(x::Rational, y::Rational)
    if isinf(x) != isinf(y)
        throw(ArgumentError("gcd is not defined between infinite and finite numbers"))
    end
    unsafe_rational(gcd(x.num, y.num), lcm(x.den, y.den))
end
```
-/
def gcdRationalSource {TX TY P : Type}
    (isinfX : Rational TX → Bool) (isinfY : Rational TY → Bool)
    (gcd : TX → TY → Jl P) (lcm : TX → TY → Jl P)
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  if isinfX x != isinfY y then
    throw (.argumentError "gcd is not defined between infinite and finite numbers")
  let n ← gcd x.num y.num
  let d ← lcm x.den y.den
  pure (unsafeRationalSameSource n d)

/--
Julia source: base/rational.jl:656-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lcm(x::Rational, y::Rational)
    if isinf(x) != isinf(y)
        throw(ArgumentError("lcm is not defined between infinite and finite numbers"))
    end
    return unsafe_rational(lcm(x.num, y.num), gcd(x.den, y.den))
end
```
-/
def lcmRationalSource {TX TY P : Type}
    (isinfX : Rational TX → Bool) (isinfY : Rational TY → Bool)
    (lcm : TX → TY → Jl P) (gcd : TX → TY → Jl P)
    (x : Rational TX) (y : Rational TY) : Jl (Rational P) := do
  if isinfX x != isinfY y then
    throw (.argumentError "lcm is not defined between infinite and finite numbers")
  let n ← lcm x.num y.num
  let d ← gcd x.den y.den
  pure (unsafeRationalSameSource n d)

/--
Julia source: base/rational.jl:662-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gcdx(x::Rational, y::Rational)
    c = gcd(x, y)
    if iszero(c.num)
        a, b = zero(c.num), c.num
    elseif iszero(c.den)
        a = ifelse(iszero(x.den), one(c.den), c.den)
        b = ifelse(iszero(y.den), one(c.den), c.den)
    else
        idiv(x, c) = div(x.num, c.num) * div(c.den, x.den)
        _, a, b = gcdx(idiv(x, c), idiv(y, c))
    end
    c, a, b
end
```
-/
def gcdxRationalSource {TX TY P Q : Type}
    (isinfX : Rational TX → Bool) (isinfY : Rational TY → Bool)
    (integerGcd : TX → TY → Jl P) (integerLcm : TX → TY → Jl P)
    (iszero : P → Bool) (zero one : P → P)
    (iszeroX : TX → Bool) (iszeroY : TY → Bool)
    (ifelse : Bool → P → P → P)
    (divNX : TX → P → Jl Q) (divDX : P → TX → Jl Q)
    (divNY : TY → P → Jl Q) (divDY : P → TY → Jl Q)
    (mulQ : Q → Q → Q)
    (gcdx : Q → Q → Jl (Q × P × P))
    (x : Rational TX) (y : Rational TY) :
    Jl (Rational P × P × P) := do
  let c ← gcdRationalSource isinfX isinfY integerGcd integerLcm x y
  if iszero c.num then
    pure (c, zero c.num, c.num)
  else if iszero c.den then
    let a := ifelse (iszeroX x.den) (one c.den) c.den
    let b := ifelse (iszeroY y.den) (one c.den) c.den
    pure (c, a, b)
  else
    let xNum ← divNX x.num c.num
    let xDen ← divDX c.den x.den
    let idivX := mulQ xNum xDen
    let yNum ← divNY y.num c.num
    let yDen ← divDY c.den y.den
    let idivY := mulQ yNum yDen
    let (_, a, b) ← gcdx idivX idivY
    pure (c, a, b)

/--
Julia source: base/rational.jl:678-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
decompose(x::Rational) = numerator(x), 0, denominator(x)
```
-/
def decomposeSource {T : Type} (x : Rational T) : T × JInt .i64 × T :=
  (numeratorRationalSource x, JInt.lit .i64 0, denominatorRationalSource x)

/--
Julia source: base/rational.jl:679-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hash(x::Rational{<:BitInteger64}, h::UInt)
    num, den = Base.numerator(x), Base.denominator(x)
    den == 1 && return hash(num, h)
    den == 0 && return hash(ifelse(num > 0, Inf, -Inf), h)
    if isodd(den) # since den != 1, this rational can't be a Float64
        pow = trailing_zeros(num)
        num >>= pow
        h = hash_integer(den, h)
    else
        pow = trailing_zeros(den)
        den >>= pow
        pow = -pow
        if den == 1
            if uabs(num) < UInt64(maxintfloat(Float64))
                return hash(ldexp(Float64(num),pow),h)
            end
        else
            h = hash_integer(den, h)
        end
    end
    h = hash_integer(pow, h)
    h = hash_integer((pow > 0) ? (num << (pow % 8)) : num, h)
    return h
end
```
-/
def hashRational64Source {t : IntTy} (_h64 : t ≠ .i128 ∧ t ≠ .u128)
    (hashInt : JInt t → JInt .u64 → JInt .u64)
    (hashFloat : JuliaLean.base.float.FV .f64 → JInt .u64 → JInt .u64)
    (hashInteger : {u : IntTy} → JInt u → JInt .u64 → JInt .u64)
    (ldexp : JuliaLean.base.float.FV .f64 → JInt .i64 → JuliaLean.base.float.FV .f64)
    (maxintfloat : JuliaLean.base.float.FV .f64 → JInt .u64)
    (isodd : JInt t → Bool) (trailingZeros : JInt t → JInt .i64)
    (shiftRight shiftLeft : JInt t → JInt .i64 → JInt t)
    (x : Rat t) (seed : JInt .u64) : JInt .u64 := Id.run do
  let mut num := numeratorRationalSource x
  let mut den := denominatorRationalSource x
  let mut h := seed
  if den.val == 1 then return hashInt num h
  if den.val == 0 then
    let posInf := JuliaLean.base.float.inf_float .f64
    let negInf := JuliaLean.base.float.neg_IEEEFloat posInf
    return hashFloat (JuliaLean.base.int.ifelse (decide (num.val > 0)) posInf negInf) h
  let mut pow : JInt .i64 := JInt.lit .i64 0
  if isodd den then
    pow := trailingZeros num
    num := shiftRight num pow
    h := hashInteger den h
  else
    pow := trailingZeros den
    den := shiftRight den pow
    pow := -pow
    if den.val == 1 then
      let unum := JuliaLean.base.int.widenTo .u64 (JuliaLean.base.float.uabs num)
      if JuliaLean.base.int.lt_BitUnsigned unum (maxintfloat (JuliaLean.base.float.one_float .f64)) then
        return hashFloat (ldexp (JuliaLean.base.float.floatOfInt .f64 num) pow) h
    else
      h := hashInteger den h
  h := hashInteger pow h
  let reducedNum := if pow.val > 0 then shiftLeft num (JInt.wrap .i64 (pow.val.tmod 8)) else num
  h := hashInteger reducedNum h
  return h


/--
Julia source: base/rational.jl:707-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(r::AbstractUnitRange{T}) where T<:Rational
    @inline
    f = first(r)
    l = last(r)
    return div(l.num - f.num + f.den, f.den)
end
```
-/
def lengthRationalRangeSource {R T D A Q : Type}
    (first last : R → Rational T) (sub : T → T → D)
    (add : D → T → A) (div : A → T → Jl Q) (r : R) : Jl Q := do
  let f := first r
  let l := last r
  div (add (sub l.num f.num) f.den) f.den

/--
Julia source: base/rational.jl:713-720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function checked_length(r::AbstractUnitRange{T}) where T<:Rational
    f = first(r)
    l = last(r)
    if isempty(r)
        return f.num - f.num
    end
    return div(checked_add(checked_sub(l.num, f.num), f.den), f.den)
end
```
-/
def checkedLengthRationalRangeSource {R T Q : Type}
    (first last : R → Rational T) (isempty : R → Bool)
    (sub : T → T → Q) (checkedSub : T → T → Jl T)
    (checkedAdd : T → T → Jl T) (div : T → T → Jl Q)
    (r : R) : Jl Q := do
  let f := first r
  let l := last r
  if isempty r then
    return sub f.num f.num
  else
    let diff ← checkedSub l.num f.num
    let sum ← checkedAdd diff f.den
    div sum f.den

def decomposeRatInt {t : IntTy} (q : Rat t) : Int × Int × Int :=
  let (n, p, d) := decomposeSource q
  (n.val, p.val, d.val)

def decomposeF64Int (x : JuliaLean.base.float.FV .f64) : Int × Int × Int :=
  let (n, p, d) := JuliaLean.base.float.decompose_Float64 x
  (n.val, p.val, d.val)

def intSign (x : Int) : Int :=
  if x < 0 then -1 else if x > 0 then 1 else 0

def intNdigits0z2 (x _ : Int) : Int :=
  if x = 0 then 0 else Int.ofNat (x.natAbs.log2 + 1)

def intShiftLeft (x s : Int) : Int :=
  x * Int.ofNat (2 ^ s.toNat)

def intCmp (a b : Int) : Int :=
  if a < b then -1 else if b < a then 1 else 0

def cmpRatFloatSource {t : IntTy} (q : Rat t) (x : JuliaLean.base.float.FV .f64) : Int :=
  rationalFloatRelationSource (fun _ => false) JuliaLean.base.float.isnan_IEEEFloat
    (fun y => if JuliaLean.base.float.isnan_IEEEFloat y then 0 else 1) (-1)
    decomposeRatInt decomposeF64Int (· * ·) intSign intNdigits0z2 Prod.mk intShiftLeft
    intCmp q x

def cmpFloatRatSource {t : IntTy} (x : JuliaLean.base.float.FV .f64) (q : Rat t) : Int :=
  rationalFloatRelationSource JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
    (fun _ => 1) (-1)
    decomposeF64Int decomposeRatInt (· * ·) intSign intNdigits0z2 Prod.mk intShiftLeft
    intCmp x q

def ltRatFloatSource {t : IntTy} (q : Rat t) (x : JuliaLean.base.float.FV .f64) : Bool :=
  rationalFloatRelationSource (fun _ => false) JuliaLean.base.float.isnan_IEEEFloat
    (fun _ => false) false
    decomposeRatInt decomposeF64Int (· * ·) intSign intNdigits0z2 Prod.mk intShiftLeft
    (fun a b => decide (a < b)) q x

def ltFloatRatSource {t : IntTy} (x : JuliaLean.base.float.FV .f64) (q : Rat t) : Bool :=
  rationalFloatRelationSource JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
    (fun _ => false) false
    decomposeF64Int decomposeRatInt (· * ·) intSign intNdigits0z2 Prod.mk intShiftLeft
    (fun a b => decide (a < b)) x q

def leRatFloatSource {t : IntTy} (q : Rat t) (x : JuliaLean.base.float.FV .f64) : Bool :=
  rationalFloatRelationSource (fun _ => false) JuliaLean.base.float.isnan_IEEEFloat
    (fun _ => false) false
    decomposeRatInt decomposeF64Int (· * ·) intSign intNdigits0z2 Prod.mk intShiftLeft
    (fun a b => decide (a ≤ b)) q x

def leFloatRatSource {t : IntTy} (x : JuliaLean.base.float.FV .f64) (q : Rat t) : Bool :=
  rationalFloatRelationSource JuliaLean.base.float.isnan_IEEEFloat (fun _ => false)
    (fun _ => false) false
    decomposeF64Int decomposeRatInt (· * ·) intSign intNdigits0z2 Prod.mk intShiftLeft
    (fun a b => decide (a ≤ b)) x q


/-- Concrete integer calls used when instantiating the source constructor. -/
abbrev rationalBitsSource {t : IntTy} : JInt t → JInt t → Jl (Rat t) :=
  (rationalSameSource (jintOps t) JuliaLean.base.float.uabs (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (fun a => JInt.convert t a.val) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) Prod.mk)

abbrev rationalizeF64 (t : IntTy) (x tol : JuliaLean.base.float.FV .f64)
    (showTol : JuliaLean.base.float.FV .f64 → String) : ExceptT JlError Option (Rat t) :=
  let zeroF := JuliaLean.base.float.zero_float .f64
  let two := JuliaLean.base.float.floatOfInt .f64 (JInt.lit .i64 2)
  rationalizeAbstractFloatSource (JInt t) (jintOps t)
    (fun w => JuliaLean.base.float.lt_IEEEFloat w zeroF)
    (fun w => JuliaLean.base.float.lt_IEEEFloat w zeroF)
    JuliaLean.base.float.isnan_IEEEFloat JuliaLean.base.float.isinf_IEEEFloat
    JuliaLean.base.float.abs_IEEEFloat JuliaLean.base.float.round_ToZero_llvm
    (fun _ => zeroF) (fun _ => JuliaLean.base.float.one_float .f64) (fun _ w => w)
    (fun r nt => JuliaLean.base.float.lt_IEEEFloat nt r)
    JuliaLean.base.float.sub_IEEEFloat JuliaLean.base.float.add_IEEEFloat
    JuliaLean.base.float.mul_IEEEFloat floatCld
    (fun u v => (floatDivToZero u v, JuliaLean.base.float.rem_IEEEFloat u v))
    (JuliaLean.base.float.intOfFloat t)
    (fun a => JuliaLean.base.float.le_IEEEFloat a two)
    (fun ia a => JuliaLean.base.float.lt_IEEEFloat
      (JuliaLean.base.float.div_IEEEFloat a two)
      (JuliaLean.base.float.floatOfInt .f64 ia))
    (exactDivideIntsSource rationalBitsSource) x tol showTol

abbrev rationalOfF64 (t : IntTy) (x : JuliaLean.base.float.FV .f64)
    (showTol : JuliaLean.base.float.FV .f64 → String) : ExceptT JlError Option (Rat t) :=
  rationalOfFloatSource (JInt t)
    (fun f => rationalizeF64 t f (JuliaLean.base.float.zero_float .f64) showTol)
    (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat)
    JuliaLean.base.float.eq_IEEEFloat x inexactErrorCore

def rationalizeRatToleranceSource {s : IntTy} {α : Type}
    (hasTypeMax : IntTy → Bool) (tolToF64 : α → JuliaLean.base.float.FV .f64)
    (toleranceEnough : α → JuliaLean.base.float.FV .f64 → Bool)
    (isfinite : JuliaLean.base.float.FV .f64 → Bool)
    (eps half : JuliaLean.base.float.FV .f64 → JuliaLean.base.float.FV .f64)
    (target : IntTy) (x : Rat s) (tol : α)
    (showTol : JuliaLean.base.float.FV .f64 → String) : ExceptT JlError Option (Rat target) :=
  rationalizeRatToleranceGeneric (!target.signed) (hasTypeMax target)
    (fun r => ltRatIntSource (fun d m => d.val * m.val) (fun n w => decide (n.val < w)) r (JInt.lit s 0))
    (fun n => decide (target.min ≤ n.val) && decide (n.val ≤ target.max))
    (fun d => decide (d.val ≤ target.max))
    (fun r => some (convertRatSource (JInt target) (fun v => JInt.convert target v.val) r))
    (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat)
    isfinite (fun f => half (eps f)) toleranceEnough
    (fun f t => rationalizeF64 target f (tolToF64 t) showTol) x tol inexactErrorCore


/-- Fixed-width integer instantiation of Julia's rational rounding method. -/
abbrev roundBitsSource {t : IntTy} (target : IntTy) (x : Rat t) (mode : Rounding) : Jl (JInt target) :=
  roundRatTypedSource (JInt target) (jintOps t).iszero true
    (jintOps t).one (jintOps t).zero (fun q _ => q) (fun _ => .error .divideError)
    roundValue (fun n => JInt.convert target n.val) x mode

/-- Concrete same-width instantiation of the source complex integer quotient. -/
abbrev complexIntegerQuotientSource {t : IntTy} (x y : ComplexValue (JInt t)) : Jl (ComplexValue (Rat t)) :=
  divideComplexIntegersSource (fun z => (z.re,z.im)) (fun z => (z.re,z.im))
    (fun a b c d => .ok (a,b,c,d)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))
    checkedMul checkedAdd checkedNeg ComplexValue.mk
    (exactDivideComplexReal (exactDivideIntsSource rationalBitsSource) ComplexValue.mk ComplexValue.re ComplexValue.im) x y

/-- Same-width integer/rational instantiation of the interpolation source method. -/
abbrev lerpiBitsSource {t : IntTy} (j d : JInt t) (a b : Rat t) : Jl (Rat t) :=
  lerpiSource (fun d j => d - j)
    (mulIntRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))))
    (slashRationalUnionSource (divRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))))
    (mulIntRatSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))))
    (slashRationalUnionSource (divRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))))
    (addRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a,b))
      (fun q => decide (q.den.val = 0)) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource) j d a b

end JuliaLean.base.rational
