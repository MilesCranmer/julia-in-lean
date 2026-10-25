import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.IntArith.Checked
import JuliaLean.IntArith.NumberTheory
import JuliaLean.IntArith.Division

namespace JuliaLean.IntArith.Rational

open JuliaLean
open JuliaLean.IntArith.Checked

private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- `Rational{T}` and `unsafe_rational`; base/rational.jl:9-18. -/
structure Rat (t : IntTy) where
  num : JInt t
  den : JInt t
  deriving DecidableEq

/-- `numerator`; base/rational.jl:361. -/
def numerator {t} (x : Rat t) : JInt t := x.num

/-- `denominator`; base/rational.jl:384. -/
def denominator {t} (x : Rat t) : JInt t := x.den

/-- `checked_den`, negating the denominator before the numerator; base/rational.jl:20-28. -/
def checkedDen {t} (num den : JInt t) : Jl (Rat t) := do
  if den.val < 0 then
    let den ← checkedNeg den
    let num ← checkedNeg num
    return ⟨num, den⟩
  else return ⟨num, den⟩

/-- Division by an unsigned gcd, preserving the dividend's type, including
`typemin`; base/int.jl:275 and base/rational.jl:59-62. The unsigned quotient
is cast to signed before `flipsign`, and finally to the original type. -/
private def divUnsigned {t u} (x : JInt t) (g : JInt u) : Jl (JInt t) := do
  let p := IntTy.promote t.toUnsigned u
  let q ← JInt.div (JInt.wrap p (NumberTheory.uabs x).val) (JInt.wrap p g.val)
  let signedQ := JInt.wrap p.toSigned q.val
  let signedQ := if x.val < 0 then -signedQ else signedQ
  return JInt.wrap t signedQ.val

/-- `divgcd`, with an unsigned gcd and original component types;
base/rational.jl:59-62. -/
def divgcd {t u} (x : JInt t) (y : JInt u) : Jl (JInt t × JInt u) := do
  let p := IntTy.promote t.toUnsigned u.toUnsigned
  let g ← NumberTheory.gcd (JInt.wrap p (NumberTheory.uabs x).val)
    (JInt.wrap p (NumberTheory.uabs y).val)
  let a ← divUnsigned x g
  let b ← divUnsigned y g
  return (a, b)

/-- `Rational{T}(num,den)`, including the unsigned sign check, reduction
before conversion, and checked sign normalization after conversion;
base/rational.jl:30-46. Inputs may have types different from `T`. -/
def construct (t : IntTy) {s u} (num : JInt s) (den : JInt u) : Jl (Rat t) := do
  if den.val = 0 ∧ num.val = 0 then
    throw (.argumentError "")
  if !t.signed then
    if num.val ≠ 0 ∧ ¬ (den.val < 0 ↔ num.val < 0) then
      throw (.inexactError "Rational")
    let (n, d) ← divgcd (NumberTheory.uabs num) (NumberTheory.uabs den)
    let n ← JInt.convert t n.val
    let d ← JInt.convert t d.val
    return ⟨n, d⟩
  else
    let (n, d) ← divgcd num den
    let n ← JInt.convert t n.val
    let d ← JInt.convert t d.val
    checkedDen n d

/-- `//(::T,::T)` and `Rational(n,d)`; base/rational.jl:48-49,91. -/
def ofInts {t} (num den : JInt t) : Jl (Rat t) := construct t num den

/-- `Rational(n)`; base/rational.jl:50. -/
def ofInt {t} (num : JInt t) : Rat t := ⟨num, JInt.lit t 1⟩

/-- `Rational{T}(x::Rational)`; base/rational.jl:190-192. -/
def convertRat (t : IntTy) {s} (x : Rat s) : Jl (Rat t) := do
  let n ← JInt.convert t x.num.val
  let d ← JInt.convert t x.den.val
  return ⟨n, d⟩

/-- Unary rational `+`; base/rational.jl:399. -/
def pos {t} (x : Rat t) : Rat t := ⟨x.num, x.den⟩

/-- Rational equality compares components without promotion;
base/rational.jl:507. -/
def eq {t s} (x : Rat t) (y : Rat s) : Bool :=
  decide (x.den.val = y.den.val) && decide (x.num.val = y.num.val)

/-- `widemul`: fixed-width widened multiplication below 128 bits;
BigInt multiplication at 128 bits. Mixed signedness converts the widened
unsigned factor to signed; base/int.jl:911-924 and base/operators.jl:975. -/
private def widemul {t s} (x : JInt t) (y : JInt s) : Int :=
  match NumberTheory.widen t, NumberTheory.widen s with
  | some a, some b =>
    let a := if t.signed != s.signed then a.toSigned else a
    let b := if t.signed != s.signed then b.toSigned else b
    let p := IntTy.promote a b
    ((JInt.wrap p x.val) * (JInt.wrap p y.val)).val
  | _, _ => x.val * y.val

/-- `<`, with the equal-denominator branch essential for opposite infinities;
base/rational.jl:508-509. -/
def lt {t s} (x : Rat t) (y : Rat s) : Bool :=
  if x.den.val = y.den.val then decide (x.num.val < y.num.val)
  else decide (widemul x.num y.den < widemul x.den y.num)

/-- `<=`; base/rational.jl:510-511. -/
def le {t s} (x : Rat t) (y : Rat s) : Bool :=
  if x.den.val = y.den.val then decide (x.num.val ≤ y.num.val)
  else decide (widemul x.num y.den ≤ widemul x.den y.num)

/-- Generic `cmp`, through `isless(::Real,::Real)`;
base/operators.jl:505,526. -/
def cmp {t s} (x : Rat t) (y : Rat s) : JInt .i64 :=
  JInt.lit .i64 (if lt x y then -1 else if lt y x then 1 else 0)

/-- Rational/integer comparisons; base/rational.jl:514-519. -/
def eqInt {t s} (x : Rat t) (y : JInt s) : Bool :=
  decide (x.den.val = 1) && decide (x.num.val = y.val)

/-- Rational/integer `<`; base/rational.jl:516. -/
def ltInt {t s} (x : Rat t) (y : JInt s) : Bool := decide (x.num.val < widemul x.den y)

/-- Integer/rational `<`; base/rational.jl:517. -/
def intLt {t s} (x : JInt t) (y : Rat s) : Bool := decide (widemul x y.den < y.num.val)

/-- Rational/integer `<=`; base/rational.jl:518. -/
def leInt {t s} (x : Rat t) (y : JInt s) : Bool := decide (x.num.val ≤ widemul x.den y)

/-- Integer/rational `<=`; base/rational.jl:519. -/
def intLe {t s} (x : JInt t) (y : Rat s) : Bool := decide (widemul x y.den ≤ y.num.val)

/-- Signed and unsigned rational negation; base/rational.jl:402-411. -/
def neg {t} (x : Rat t) : Jl (Rat t) := do
  if t.signed then
    if x.num.val = t.min then throw (.overflowError "")
    return ⟨-x.num, x.den⟩
  else
    if x.num.val ≠ 0 then throw (.overflowError "")
    return x

/-- `abs`, preserving the denominator and checking the numerator;
base/rational.jl:390. -/
def abs {t} (x : Rat t) : Jl (Rat t) := do
  let n ← checkedAbs x.num
  return ⟨n, x.den⟩

/-- Same-component-type `+`; base/rational.jl:415-422. -/
def add {t} (x y : Rat t) : Jl (Rat t) := do
  if x.den.val = 0 ∧ eq x y = true then return x
  let (xd, yd) ← divgcd x.den y.den
  let a ← checkedMul x.num yd
  let b ← checkedMul y.num xd
  let n ← checkedAdd a b
  let d ← checkedMul x.den yd
  ofInts n d

/-- Same-component-type `-`, evaluating `-y` only when x is infinite;
base/rational.jl:433-440. -/
def sub {t} (x y : Rat t) : Jl (Rat t) := do
  if x.den.val = 0 then
    let ny ← neg y
    if eq x ny then return x
  let (xd, yd) ← divgcd x.den y.den
  let a ← checkedMul x.num yd
  let b ← checkedMul y.num xd
  let n ← checkedSub a b
  let d ← checkedMul x.den yd
  ofInts n d

/-- `*`, cancelling both cross gcds before checked multiplication;
base/rational.jl:482-486. -/
def mul {t} (x y : Rat t) : Jl (Rat t) := do
  let (xn, yd) ← divgcd x.num y.den
  let (xd, yn) ← divgcd x.den y.num
  let n ← checkedMul xn yn
  let d ← checkedMul xd yd
  return ⟨n, d⟩

/-- Rational `//` and `/`, including master's infinite-sign correction;
base/rational.jl:106-115,501. -/
def div {t} (x y : Rat t) : Jl (Rat t) := do
  let (xn, yn) ← divgcd x.num y.num
  let (xd, yd) ← divgcd x.den y.den
  let xn ← if xd.val = 0 ∧ yn.val < 0 then checkedNeg xn else pure xn
  let n ← checkedMul xn yd
  let d ← checkedMul xd yn
  checkedDen n d

/-- `inv`; base/rational.jl:503. -/
def inv {t} (x : Rat t) : Jl (Rat t) := checkedDen x.den x.num

/-- `rem(::Rational,::Rational)`; base/rational.jl:451-458. -/
def rem {t} (x y : Rat t) : Jl (Rat t) := do
  let (xd, yd) ← divgcd x.den y.den
  let a ← checkedMul x.num yd
  let b ← checkedMul y.num xd
  let n ← JInt.remInt a b
  let d ← checkedMul x.den yd
  ofInts n d

/-- `mod(::Rational,::Rational)`; base/rational.jl:451-458. -/
def mod {t} (x y : Rat t) : Jl (Rat t) := do
  let (xd, yd) ← divgcd x.den y.den
  let a ← checkedMul x.num yd
  let b ← checkedMul y.num xd
  let n ← JInt.mod a b
  let d ← checkedMul x.den yd
  ofInts n d

/-- Rational/integer `+,-,rem,mod` share this source branch;
base/rational.jl:460-466. -/
def withInt {t} (op : JInt t → JInt t → Jl (JInt t)) (x : Rat t) (y : JInt t) : Jl (Rat t) := do
  let b ← checkedMul x.den y
  let n ← op x.num b
  return ⟨n, x.den⟩

/-- Integer/rational `+,-`; base/rational.jl:467-473. -/
def intWith {t} (op : JInt t → JInt t → Jl (JInt t)) (y : JInt t) (x : Rat t) : Jl (Rat t) := do
  let a ← checkedMul x.den y
  let n ← op a x.num
  return ⟨n, x.den⟩

/-- Integer/rational `rem,mod`; base/rational.jl:474-480. -/
def intRemainder {t} (op : JInt t → JInt t → Jl (JInt t)) (y : JInt t) (x : Rat t) : Jl (Rat t) := do
  let a ← checkedMul x.den y
  let n ← op a x.num
  ofInts n x.den

/-- Rational/integer `*`; base/rational.jl:487-490. -/
def mulInt {t} (x : Rat t) (y : JInt t) : Jl (Rat t) := do
  let (xd, yn) ← divgcd x.den y
  let n ← checkedMul x.num yn
  return ⟨n, xd⟩

/-- Integer/rational `*`; base/rational.jl:491-494. -/
def intMul {t} (y : JInt t) (x : Rat t) : Jl (Rat t) := do
  let (yn, xd) ← divgcd y x.den
  let n ← checkedMul yn x.num
  return ⟨n, xd⟩

/-- Rational/integer `//` and `/`, including master's infinity sign branch;
base/rational.jl:93-101,501. -/
def divInt {t} (x : Rat t) (y : JInt t) : Jl (Rat t) := do
  let (xn, yn) ← divgcd x.num y
  let xn ← if x.den.val = 0 ∧ yn.val < 0 then checkedNeg xn else pure xn
  let d ← checkedMul x.den yn
  checkedDen xn d

/-- Integer/rational `//` and `/`; base/rational.jl:102-105,502. -/
def intDiv {t} (x : JInt t) (y : Rat t) : Jl (Rat t) := do
  let (xn, yn) ← divgcd x y.num
  let n ← checkedMul xn y.den
  checkedDen n yn

/-- Rounding modes accepted by integer `div`; base/div.jl:326-373,415-416. -/
inductive Rounding where
  | toZero | down | up | nearest | nearestAway | nearestUp | fromZero
  deriving DecidableEq

/-- Integer rounding mirrors every sign and tie branch of `divrem`, using
wrapping intermediates, including the explicit signed half-divisor;
base/div.jl:326-373,409-416,421,460-474. -/
def roundedDiv {t} (x y : JInt t) (mode : Rounding) : Jl (JInt t) := do
  match mode with
  | .toZero => JInt.div x y
  | .down => JInt.fld x y
  | .up => JInt.cld x y
  | .fromZero => if x.val < 0 ↔ y.val < 0 then JInt.cld x y else JInt.fld x y
  | .nearest | .nearestAway | .nearestUp =>
    let q ← JInt.div x y
    let r := x - q * y
    let half ← JInt.div y (JInt.lit t 2)
    let oddY := decide (y.val % 2 ≠ 0)
    let evenQ := decide (q.val % 2 = 0)
    let tie : Bool := match mode with
      | .nearest => oddY || evenQ
      | .nearestAway => oddY
      | _ => if x.val < 0 ↔ y.val < 0 then oddY else true
    let c := JInt.lit t (if tie then 1 else 0)
    if x.val ≥ 0 then
      if y.val ≥ 0 then return if r ≥ half + c then q + JInt.lit t 1 else q
      else return if r ≥ -half + c then q - JInt.lit t 1 else q
    else
      if y.val ≥ 0 then
        let shalf := JInt.wrap t.toSigned half.val
        let threshold := -shalf - JInt.lit t.toSigned (if tie then 1 else 0)
        return if r.val ≤ threshold.val then q - JInt.lit t 1 else q
      else return if r ≤ half - c then q + JInt.lit t 1 else q

/-- Rational `div` with a rounding mode; base/rational.jl:594-598. -/
def quotient {t} (x y : Rat t) (mode : Rounding := .toZero) : Jl (JInt t) := do
  let (xn, yn) ← divgcd x.num y.num
  let (xd, yd) ← divgcd x.den y.den
  let a ← checkedMul xn yd
  let b ← checkedMul xd yn
  roundedDiv a b mode

/-- Rational/integer rounded `div`; base/rational.jl:586-589. -/
def quotientInt {t} (x : Rat t) (y : JInt t) (mode : Rounding := .toZero) : Jl (JInt t) := do
  let (xn, yn) ← divgcd x.num y
  let b ← checkedMul x.den yn
  roundedDiv xn b mode

/-- Integer/rational rounded `div`; base/rational.jl:590-593. -/
def intQuotient {t} (x : JInt t) (y : Rat t) (mode : Rounding := .toZero) : Jl (JInt t) := do
  let (xn, yn) ← divgcd x y.num
  let a ← checkedMul xn y.den
  roundedDiv a yn mode

/-- `fld`; base/rational.jl:604-609. -/
def fld {t} (x y : Rat t) : Jl (JInt t) := quotient x y .down

/-- `cld`; base/rational.jl:604-609. -/
def cld {t} (x y : Rat t) : Jl (JInt t) := quotient x y .up

/-- Integer-target `round`, with division performed in the rational's
component type before conversion; base/rational.jl:614-619. -/
def round (target : IntTy) {t} (x : Rat t) (mode : Rounding := .nearest) : Jl (JInt target) := do
  let n ← roundedDiv x.num x.den mode
  JInt.convert target n.val

/-- Integer-target `floor`; base/rational.jl:614-619, base/rounding.jl:486. -/
def floor (target : IntTy) {t} (x : Rat t) : Jl (JInt target) := round target x .down

/-- Integer-target `ceil`; base/rational.jl:614-619, base/rounding.jl:487. -/
def ceil (target : IntTy) {t} (x : Rat t) : Jl (JInt target) := round target x .up

/-- Integer-target `trunc`; base/rational.jl:614-619, base/rounding.jl:485. -/
def trunc (target : IntTy) {t} (x : Rat t) : Jl (JInt target) := round target x .toZero
/-- `Rational(n,d)` first promotes unlike the explicit typed constructor;
base/rational.jl:49,91. -/
def ofMixedInts {t s} (num : JInt t) (den : JInt s) : Jl (Rat (t.promote s)) := do
  let n ← JInt.convert (t.promote s) num.val
  let d ← JInt.convert (t.promote s) den.val
  ofInts n d

/-- Mixed `+` promotes whole rationals before the infinity test;
base/rational.jl:415-422. -/
def addMixed {t s} (x : Rat t) (y : Rat s) : Jl (Rat (t.promote s)) := do
  let xp ← convertRat (t.promote s) x
  let yp ← convertRat (t.promote s) y
  if x.den.val = 0 ∧ eq x y = true then return xp
  let (xd, yd) ← divgcd xp.den yp.den
  let a ← checkedMul xp.num yd
  let b ← checkedMul yp.num xd
  let n ← checkedAdd a b
  let d ← checkedMul xp.den yd
  ofInts n d

/-- Mixed `-` promotes whole rationals first, but negates the original
unpromoted y in the infinity test; base/rational.jl:433-440. -/
def subMixed {t s} (x : Rat t) (y : Rat s) : Jl (Rat (t.promote s)) := do
  let xp ← convertRat (t.promote s) x
  let yp ← convertRat (t.promote s) y
  if x.den.val = 0 then
    let ny ← neg y
    if eq x ny then return xp
  let (xd, yd) ← divgcd xp.den yp.den
  let a ← checkedMul xp.num yd
  let b ← checkedMul yp.num xd
  let n ← checkedSub a b
  let d ← checkedMul xp.den yd
  ofInts n d

/-- Mixed multiplication promotes and reduces the first cross pair before
converting the second cross pair; base/rational.jl:482-486. -/
def mulMixed {t s} (x : Rat t) (y : Rat s) : Jl (Rat (t.promote s)) := do
  let a ← JInt.convert (t.promote s) x.num.val
  let b ← JInt.convert (t.promote s) y.den.val
  let (xn, yd) ← divgcd a b
  let c ← JInt.convert (t.promote s) x.den.val
  let d ← JInt.convert (t.promote s) y.num.val
  let (xd, yn) ← divgcd c d
  let n ← checkedMul xn yn
  let d ← checkedMul xd yd
  return ⟨n, d⟩

/-- Mixed `//` and `/` promote numerator pairs, reduce, then promote the
denominator pairs; base/rational.jl:106-115,501. -/
def divMixed {t s} (x : Rat t) (y : Rat s) : Jl (Rat (t.promote s)) := do
  let a ← JInt.convert (t.promote s) x.num.val
  let b ← JInt.convert (t.promote s) y.num.val
  let (xn, yn) ← divgcd a b
  let c ← JInt.convert (t.promote s) x.den.val
  let d ← JInt.convert (t.promote s) y.den.val
  let (xd, yd) ← divgcd c d
  let xn ← if xd.val = 0 ∧ yn.val < 0 then checkedNeg xn else pure xn
  let n ← checkedMul xn yd
  let d ← checkedMul xd yn
  checkedDen n d

/-- Mixed rational remainders promote denominator pairs before checked
numerator multiplication; base/rational.jl:451-458. -/
def remainderMixed {t s} (op : JInt (t.promote s) → JInt (t.promote s) → Jl (JInt (t.promote s)))
    (x : Rat t) (y : Rat s) : Jl (Rat (t.promote s)) := do
  let c ← JInt.convert (t.promote s) x.den.val
  let d ← JInt.convert (t.promote s) y.den.val
  let (xd, yd) ← divgcd c d
  let xn ← JInt.convert (t.promote s) x.num.val
  let a ← checkedMul xn yd
  let yn ← JInt.convert (t.promote s) y.num.val
  let b ← checkedMul yn xd
  let n ← op a b
  let d ← checkedMul c yd
  ofInts n d

/-- Mixed rational `rem`; base/rational.jl:451-458. -/
def remMixed {t s} (x : Rat t) (y : Rat s) := remainderMixed JInt.remInt x y

/-- Mixed rational `mod`; base/rational.jl:451-458. -/
def modMixed {t s} (x : Rat t) (y : Rat s) := remainderMixed JInt.mod x y

/-- Mixed rational rounded quotients preserve original types through both
`divgcd` calls and promote only at checked multiplication;
base/rational.jl:594-598. -/
def quotientMixed {t s} (x : Rat t) (y : Rat s) (mode : Rounding := .toZero) :
    Jl (JInt (t.promote s)) := do
  let (xn, yn) ← divgcd x.num y.num
  let (xd, yd) ← divgcd x.den y.den
  let a ← checkedMulMixed xn yd
  let b ← checkedMulMixed xd yn
  roundedDiv a b mode

/-- Mixed rational `fld`; base/rational.jl:604-609. -/
def fldMixed {t s} (x : Rat t) (y : Rat s) := quotientMixed x y .down

/-- Mixed rational `cld`; base/rational.jl:604-609. -/
def cldMixed {t s} (x : Rat t) (y : Rat s) := quotientMixed x y .up


/-- Mixed scalar methods can return a signed remainder type even when
arithmetic promotion is unsigned; base/rational.jl:17-18,460-480. -/
structure AnyRat where
  ty : IntTy
  value : Rat ty

/-- Runtime-typed `unsafe_rational(num,den)` performs checked promotion;
base/rational.jl:17-18. -/
private def unsafeValues (n d : Division.Value) : Jl AnyRat := do
  let p := n.ty.promote d.ty
  let n ← JInt.convert p n.int.val
  let d ← JInt.convert p d.int.val
  return ⟨p, ⟨n, d⟩⟩

/-- Runtime-typed `Rational(num,den)` promotes before normalization;
base/rational.jl:48-49. -/
private def constructValues (n d : Division.Value) : Jl AnyRat := do
  let p := n.ty.promote d.ty
  let n ← JInt.convert p n.int.val
  let d ← JInt.convert p d.int.val
  let r ← ofInts n d
  return ⟨p, r⟩

/-- Runtime-typed `checked_den(num,den)`; base/rational.jl:27-28. -/
private def checkedDenValues (n d : Division.Value) : Jl AnyRat := do
  let p := n.ty.promote d.ty
  let n ← JInt.convert p n.int.val
  let d ← JInt.convert p d.int.val
  let r ← checkedDen n d
  return ⟨p, r⟩

/-- Checked scalar arithmetic promotes before operating; base/checked.jl:26-28. -/
private def checkedValues (op : {t : IntTy} → JInt t → JInt t → Jl (JInt t))
    (a b : Division.Value) : Jl Division.Value := do
  let p := a.ty.promote b.ty
  let a ← JInt.convert p a.int.val
  let b ← JInt.convert p b.int.val
  return Division.pack (← op a b)

/-- Mixed rational/integer `+,-,rem,mod`, retaining mixed division result
types through the final unsafe constructor; base/rational.jl:460-466. -/
def withIntMixed {t s} (op : Division.Value → Division.Value → Jl Division.Value)
    (x : Rat t) (y : JInt s) : Jl AnyRat := do
  let b ← checkedMulMixed x.den y
  let n ← op (Division.pack x.num) (Division.pack b)
  unsafeValues n (Division.pack x.den)

/-- Mixed rational/integer `+`; base/rational.jl:460-466. -/
def addIntMixed {t s} (x : Rat t) (y : JInt s) :=
  withIntMixed (checkedValues @checkedAdd) x y

/-- Mixed rational/integer `-`; base/rational.jl:460-466. -/
def subIntMixed {t s} (x : Rat t) (y : JInt s) :=
  withIntMixed (checkedValues @checkedSub) x y

/-- Mixed rational/integer `rem`; base/rational.jl:460-466. -/
def remIntMixed {t s} (x : Rat t) (y : JInt s) := withIntMixed Division.rem x y

/-- Mixed rational/integer `mod`; base/rational.jl:460-466. -/
def modIntMixed {t s} (x : Rat t) (y : JInt s) := withIntMixed Division.mod x y

/-- Mixed integer/rational `+,-`; base/rational.jl:467-473. -/
def intWithMixed {t s} (op : Division.Value → Division.Value → Jl Division.Value)
    (y : JInt s) (x : Rat t) : Jl AnyRat := do
  let a ← checkedMulMixed x.den y
  let n ← op (Division.pack a) (Division.pack x.num)
  unsafeValues n (Division.pack x.den)

/-- Mixed integer/rational `+`; base/rational.jl:467-473. -/
def intAddMixed {t s} (y : JInt s) (x : Rat t) :=
  intWithMixed (checkedValues @checkedAdd) y x

/-- Mixed integer/rational `-`; base/rational.jl:467-473. -/
def intSubMixed {t s} (y : JInt s) (x : Rat t) :=
  intWithMixed (checkedValues @checkedSub) y x

/-- Mixed integer/rational `rem,mod`, normalizing the final pair;
base/rational.jl:474-480. -/
def intRemainderMixed {t s} (op : Division.Value → Division.Value → Jl Division.Value)
    (y : JInt s) (x : Rat t) : Jl AnyRat := do
  let a ← checkedMulMixed x.den y
  let n ← op (Division.pack a) (Division.pack x.num)
  constructValues n (Division.pack x.den)

/-- Mixed integer/rational `rem`; base/rational.jl:474-480. -/
def intRemMixed {t s} (y : JInt s) (x : Rat t) := intRemainderMixed Division.rem y x

/-- Mixed integer/rational `mod`; base/rational.jl:474-480. -/
def intModMixed {t s} (y : JInt s) (x : Rat t) := intRemainderMixed Division.mod y x

/-- Mixed rational/integer `*`, promoting only the denominator/integer
pair before cancellation; base/rational.jl:487-490. -/
def mulIntMixed {t s} (x : Rat t) (y : JInt s) : Jl AnyRat := do
  let d ← JInt.convert (t.promote s) x.den.val
  let n ← JInt.convert (t.promote s) y.val
  let (xd, yn) ← divgcd d n
  let n ← checkedValues @checkedMul (Division.pack x.num) (Division.pack yn)
  unsafeValues n (Division.pack xd)

/-- Mixed integer/rational `*`, preserving the reversed promotion order;
base/rational.jl:491-494. -/
def intMulMixed {t s} (y : JInt s) (x : Rat t) : Jl AnyRat := do
  let n ← JInt.convert (s.promote t) y.val
  let d ← JInt.convert (s.promote t) x.den.val
  let (yn, xd) ← divgcd n d
  let n ← checkedValues @checkedMul (Division.pack yn) (Division.pack x.num)
  unsafeValues n (Division.pack xd)

/-- Mixed rational/integer `//` and `/`; base/rational.jl:93-101,501. -/
def divIntMixed {t s} (x : Rat t) (y : JInt s) : Jl AnyRat := do
  let n ← JInt.convert (t.promote s) x.num.val
  let d ← JInt.convert (t.promote s) y.val
  let (xn, yn) ← divgcd n d
  let xn ← if x.den.val = 0 ∧ yn.val < 0 then checkedNeg xn else pure xn
  let d ← checkedValues @checkedMul (Division.pack x.den) (Division.pack yn)
  checkedDenValues (Division.pack xn) d

/-- Mixed integer/rational `//` and `/`; base/rational.jl:102-105,502. -/
def intDivMixed {t s} (x : JInt t) (y : Rat s) : Jl AnyRat := do
  let n ← JInt.convert (t.promote s) x.val
  let d ← JInt.convert (t.promote s) y.num.val
  let (xn, yn) ← divgcd n d
  let n ← checkedValues @checkedMul (Division.pack xn) (Division.pack y.den)
  checkedDenValues n (Division.pack yn)

/-- Mixed rational/integer `div,fld,cld`, passing Division.div/fld/cld
respectively. Cancellation retains original types; base/rational.jl:586-589,604-609. -/
def quotientIntMixed {t s} (op : Division.Value → Division.Value → Jl Division.Value)
    (x : Rat t) (y : JInt s) : Jl Division.Value := do
  let (xn, yn) ← divgcd x.num y
  let d ← checkedMulMixed x.den yn
  op (Division.pack xn) (Division.pack d)

/-- Mixed integer/rational `div,fld,cld`; base/rational.jl:590-593,604-609. -/
def intQuotientMixed {t s} (op : Division.Value → Division.Value → Jl Division.Value)
    (x : JInt t) (y : Rat s) : Jl Division.Value := do
  let (xn, yn) ← divgcd x y.num
  let n ← checkedMulMixed xn y.den
  op (Division.pack n) (Division.pack yn)

/-- Normalized representation: nonnegative denominator and coprime components. -/
def Normalized {t} (x : Rat t) : Prop :=
  0 ≤ x.den.val ∧ Nat.gcd x.num.val.natAbs x.den.val.natAbs = 1

instance {t} (x : Rat t) : Decidable (Normalized x) :=
  inferInstanceAs (Decidable (0 ≤ x.den.val ∧ Nat.gcd x.num.val.natAbs x.den.val.natAbs = 1))

/-- Infinity minus a finite unsigned rational preserves infinity. -/
def InfinitySub : Prop := ∀ (t : IntTy) (x y : Rat t),
  Normalized x → Normalized y → x.num.val > 0 → x.den.val = 0 → y.den.val > 0 →
  sub x y = .ok x

private def unsignedInf : Rat .u8 := ⟨JInt.lit .u8 1, JInt.lit .u8 0⟩
private def unsignedOne : Rat .u8 := ofInt (JInt.lit .u8 1)

theorem infinitySub_refuted : ¬ InfinitySub := by
  intro h
  have bad := h .u8 unsignedInf unsignedOne (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have actual : sub unsignedInf unsignedOne = .error (.overflowError "") := by decide
  rw [actual] at bad
  cases bad

/-- If the reduced, positive-denominator representation fits T, constructing
from wider integer components succeeds. -/
def NormalizeBeforeConvert : Prop := ∀ (t s : IntTy) (n d : JInt s) (x : Rat t),
  Normalized x → x.den.val > 0 → d.val ≠ 0 →
  n.val * x.den.val = x.num.val * d.val → construct t n d = .ok x

theorem normalizeBeforeConvert_refuted : ¬ NormalizeBeforeConvert := by
  intro h
  have bad := h .i8 .i16 (JInt.lit .i16 128) (JInt.lit .i16 (-1))
    (ofInt (JInt.lit .i8 (-128))) (by decide) (by decide) (by decide) (by decide)
  have actual : construct .i8 (JInt.lit .i16 128) (JInt.lit .i16 (-1)) =
      .error (.inexactError "Int8") := by decide +kernel
  rw [actual] at bad
  cases bad

/-- Every integer-target rounding mode rejects zero-denominator rationals. -/
def InfiniteRoundingRejected : Prop := ∀ (t target : IntTy) (x : Rat t) (mode : Rounding),
  x.den.val = 0 → round target x mode = .error .divideError

theorem infiniteRoundingRejected_proven : InfiniteRoundingRejected := by
  intro t target x mode h
  cases mode <;> simp [round, roundedDiv, JInt.div, JInt.fld, JInt.cld, h,
    Bind.bind, Except.bind]

/-- Truncation of every finite normalized rational is the mathematical
truncating quotient, without overflow, for all ten component types. -/
def TruncExact : Prop := ∀ (t : IntTy) (x : Rat t),
  0 < x.den.val → ∃ z, trunc t x = .ok z ∧ z.val = x.num.val.tdiv x.den.val

theorem truncExact_proven : TruncExact := by
  intro t x hd
  have hz : t.min ≤ 0 ∧ 0 ≤ t.max := by cases t <;> decide
  have hb : t.min ≤ x.num.val.tdiv x.den.val ∧ x.num.val.tdiv x.den.val ≤ t.max := by
    have hn := x.num.property
    by_cases hs : 0 ≤ x.num.val
    · have hlo := Int.tdiv_le_tdiv hd hs
      have hhi := Int.tdiv_le_self x.den.val hs
      simp only [Int.zero_tdiv] at hlo
      omega
    · have hlo := Int.tdiv_le_self x.den.val (by omega : 0 ≤ -x.num.val)
      rw [Int.neg_tdiv] at hlo
      have hhi := Int.tdiv_le_tdiv hd (by omega : x.num.val ≤ 0)
      simp only [Int.zero_tdiv] at hhi
      omega
  let z : JInt t := ⟨x.num.val.tdiv x.den.val, hb⟩
  refine ⟨z, ?_, rfl⟩
  have hw : JInt.wrap t (x.num.val.tdiv x.den.val) = z := by
    apply Subtype.ext
    exact wrapInt_of_inRange t _ hb
  have he : ¬ (t.signed = true ∧ x.num.val = t.min ∧ x.den.val = -1) := by omega
  simp [trunc, round, roundedDiv, JInt.div, Int.ne_of_gt hd, he, hw, JInt.convert, hb, z,
    Bind.bind, Except.bind]

/-- A successful arithmetic result is normalized and represents the specified
exact ratio. Infinite results must carry the numerator's sign. -/
private def exactResult (r : Jl (Rat .i8)) (n d : Int) : Bool :=
  match r with
  | .error _ => false
  | .ok z => decide (Normalized z ∧ z.num.val * d = n * z.den.val ∧
      (d = 0 → z.den.val = 0 ∧ 0 < z.num.val * n))

/-- Finite input grid includes negative and zero numerators and nontrivial
cross gcds. The reference calculations use mathematical integers only. -/
private def smallArithmeticCase (a b c d : Fin 4) : Bool :=
  match ofInts (JInt.lit .i8 ((a.val : Int) - 2)) (JInt.lit .i8 ((b.val : Int) + 1)),
      ofInts (JInt.lit .i8 ((c.val : Int) - 2)) (JInt.lit .i8 ((d.val : Int) + 1)) with
  | .ok x, .ok y =>
    let crossX := x.num.val * y.den.val
    let crossY := y.num.val * x.den.val
    exactResult (add x y) (crossX + crossY) (x.den.val * y.den.val) &&
    exactResult (sub x y) (crossX - crossY) (x.den.val * y.den.val) &&
    exactResult (mul x y) (x.num.val * y.num.val) (x.den.val * y.den.val) &&
    (if x.num.val = 0 ∧ y.num.val = 0 then decide (div x y = .error .divideError)
     else exactResult (div x y) crossX (x.den.val * y.num.val)) &&
    decide (lt x y = decide (crossX < crossY)) &&
    decide (eq x y = decide (crossX = crossY))
  | _, _ => false

/-- Exact arithmetic and order for all 256 pairs of finite rationals generated
by numerators -2..1 and denominators 1..4, including unreduced inputs. -/
def SmallArithmetic : Prop := ∀ a b c d : Fin 4, smallArithmeticCase a b c d = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem smallArithmetic_proven : SmallArithmetic := by
  unfold SmallArithmetic
  decide +kernel

/-- Whole-rational conversion errors occur before addition or subtraction
arithmetic, including the infinity shortcuts. -/
def MixedConversionFirst : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s) (e : JlError),
  convertRat (t.promote s) x = .error e →
  addMixed x y = .error e ∧ subMixed x y = .error e

theorem mixedConversionFirst_proven : MixedConversionFirst := by
  intro t s x y e h
  simp [addMixed, subMixed, h, Bind.bind, Except.bind]

def entries : List JuliaLean.Registry.Entry := [
  { id := "intarith-rational-infinity-sub", juliaFile := "base/rational.jl"
    juliaFns := ["-(::Rational,::Rational)", "-(::Rational{<:Unsigned})"]
    statement := "Subtracting a finite unsigned rational from positive infinity preserves infinity."
    source := "invariant: +infinity minus a finite value is +infinity"
    status := .refuted, prop := ``InfinitySub, thm := some ``infinitySub_refuted
    issue := "none found (issues/PR queries: Rational unsigned infinity subtraction; rational infinity; rational unsigned). Related PR #16111 introduced the infinity special case."
    notes := "Both release and master eagerly negate finite unsigned y in the infinity special case and throw OverflowError. The checked '-' branch is unchanged; master additionally supplies explicit wrapping '-%'." },
  { id := "intarith-rational-normalize-before-convert", juliaFile := "base/rational.jl"
    juliaFns := ["Rational{T}(::Integer,::Integer)"]
    statement := "Construction succeeds whenever the normalized reduced rational fits the target component type."
    source := "base/rational.jl:3-7; https://docs.julialang.org/en/v1/manual/complex-and-rational-numbers/#Rational-Numbers: reduced to lowest terms such that the denominator is non-negative"
    status := .refuted, prop := ``NormalizeBeforeConvert, thm := some ``normalizeBeforeConvert_refuted
    issue := "none found (issues/PR queries: Rational typemin constructor InexactError; Rational Int8 constructor; rational normalization; Rational typemin; rational constructor negative). Related PR #31090 concerns unary negation."
    notes := "SEMANTICS CANDIDATE: Rational{Int8}(Int16(128),Int16(-1)) throws InexactError although -128//1 fits. Reading normalization as preceding target conversion predicts success; reading the typed constructor as requiring reduced pre-normalization components to fit permits this exception. The Rational docstring promises typed components and checked overflow, not explicit conversion order. Same behavior and constructor in release and master." },
  { id := "intarith-rational-infinite-rounding", juliaFile := "base/rational.jl"
    juliaFns := ["round", "floor", "ceil", "trunc"]
    statement := "Rounding infinite rationals to any BitInteger throws DivideError for all rounding modes."
    source := "base/rational.jl:614-619; integer division by zero"
    status := .proven, prop := ``InfiniteRoundingRejected, thm := some ``infiniteRoundingRejected_proven
    notes := "Unchanged in release and master." },
  { id := "intarith-rational-trunc-exact", juliaFile := "base/rational.jl"
    juliaFns := ["trunc", "round(::Type{T},::Rational,RoundToZero)"]
    statement := "Every positive-denominator rational truncates exactly to its mathematical quotient in its component type, including typemin numerators."
    source := "base/rational.jl:614-619; base/div.jl:5-13"
    status := .proven, prop := ``TruncExact, thm := some ``truncExact_proven
    notes := "All finite numerators and positive denominators of all ten BitInteger types; unchanged in release and master." }
  , { id := "intarith-rational-mixed-conversion-first", juliaFile := "base/rational.jl"
      juliaFns := ["+(::Rational,::Rational)", "-(::Rational,::Rational)"]
      statement := "Mixed rational addition and subtraction propagate conversion errors before infinity shortcuts or arithmetic."
      source := "base/rational.jl:416,434"
      status := .proven, prop := ``MixedConversionFirst, thm := some ``mixedConversionFirst_proven
      notes := "All 100 component-type pairs; release and master both promote before checking infinity." }
  , { id := "intarith-rational-small-arithmetic", juliaFile := "base/rational.jl"
      juliaFns := ["Rational", "+", "-", "*", "/", "<", "=="]
      statement := "All 256 pairs generated by numerators -2..1 and denominators 1..4 have exact normalized arithmetic and mathematical comparison; 0/0 is rejected."
      source := "Rational Numbers manual exact-ratio arithmetic and normalized unique form"
      status := .proven, prop := ``SmallArithmetic, thm := some ``smallArithmetic_proven
      notes := "Includes negative numerators, zero, nontrivial cancellation, equal and unequal denominators, and division producing signed infinities. Master // additionally corrects signs for an already infinite dividend, a branch absent in release and not reached by these finite dividends." }
]

end JuliaLean.IntArith.Rational
