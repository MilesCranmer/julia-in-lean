import JuliaLean.base.hashing
import JuliaLean.base.abstractarray
import JuliaLean.base.essentials
import JuliaLean.base.range
import JuliaLean.base.complex
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.checked
import JuliaLean.base.div
import JuliaLean.base.number
import JuliaLean.base.operators
import JuliaLean.base.promotion
import JuliaLean.base.intfuncs

namespace JuliaLean.IntArith.Rational

open JuliaLean
open JuliaLean.IntArith.Checked


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

/-- `divgcd`, with an unsigned gcd and original component types;
base/rational.jl:59-62. -/
def divgcd {t u} (x : JInt t) (y : JInt u) : Jl (JInt t × JInt u) := do
  let p := IntTy.promote t.toUnsigned u.toUnsigned
  let g ← NumberTheory.gcd (JInt.wrap p (NumberTheory.uabs x).val)
    (JInt.wrap p (NumberTheory.uabs y).val)
  let a ← divUnsigned NumberTheory.uabs x g
  let b ← divUnsigned NumberTheory.uabs y g
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
    let n ← JInt.convert (t.name) t n.val
    let d ← JInt.convert (t.name) t d.val
    return ⟨n, d⟩
  else
    let (n, d) ← divgcd num den
    let n ← JInt.convert (t.name) t n.val
    let d ← JInt.convert (t.name) t d.val
    checkedDen n d

/-- `//(::T,::T)` and `Rational(n,d)`; base/rational.jl:48-49,91. -/
def ofInts {t} (num den : JInt t) : Jl (Rat t) := construct t num den

/-- `Rational(n)`; base/rational.jl:50. -/
def ofInt {t} (num : JInt t) : Rat t := ⟨num, JInt.lit t 1⟩

/-- `Rational{T}(x::Rational)`; base/rational.jl:190-192. -/
def convertRat (t : IntTy) {s} (x : Rat s) : Jl (Rat t) := do
  let n ← JInt.convert (t.name) t x.num.val
  let d ← JInt.convert (t.name) t x.den.val
  return ⟨n, d⟩

/-- Unary rational `+`; base/rational.jl:399. -/
def pos {t} (x : Rat t) : Rat t := ⟨x.num, x.den⟩

/-- Rational equality compares components without promotion;
base/rational.jl:507. -/
def eq {t s} (x : Rat t) (y : Rat s) : Bool :=
  decide (x.den.val = y.den.val) && decide (x.num.val = y.num.val)

/-- `<`, with the equal-denominator branch essential for opposite infinities;
base/rational.jl:508-509. -/
def lt {t s} (x : Rat t) (y : Rat s) : Bool :=
  if x.den.val = y.den.val then decide (x.num.val < y.num.val)
  else decide (widemul x.num y.den < widemul x.den y.num)

/-- `<=`; base/rational.jl:510-511. -/
def le {t s} (x : Rat t) (y : Rat s) : Bool :=
  if x.den.val = y.den.val then decide (x.num.val ≤ y.num.val)
  else decide (widemul x.num y.den ≤ widemul x.den y.num)

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
  JInt.convert (target.name) target n.val

/-- Integer-target `floor`; base/rational.jl:614-619, base/rounding.jl:486. -/
def floor (target : IntTy) {t} (x : Rat t) : Jl (JInt target) := round target x .down

/-- Integer-target `ceil`; base/rational.jl:614-619, base/rounding.jl:487. -/
def ceil (target : IntTy) {t} (x : Rat t) : Jl (JInt target) := round target x .up

/-- Integer-target `trunc`; base/rational.jl:614-619, base/rounding.jl:485. -/
def trunc (target : IntTy) {t} (x : Rat t) : Jl (JInt target) := round target x .toZero
/-- `Rational(n,d)` first promotes unlike the explicit typed constructor;
base/rational.jl:49,91. -/
def ofMixedInts {t s} (num : JInt t) (den : JInt s) : Jl (Rat (t.promote s)) := do
  let n ← JInt.convert ((t.promote s).name) (t.promote s) num.val
  let d ← JInt.convert ((t.promote s).name) (t.promote s) den.val
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
  let a ← JInt.convert ((t.promote s).name) (t.promote s) x.num.val
  let b ← JInt.convert ((t.promote s).name) (t.promote s) y.den.val
  let (xn, yd) ← divgcd a b
  let c ← JInt.convert ((t.promote s).name) (t.promote s) x.den.val
  let d ← JInt.convert ((t.promote s).name) (t.promote s) y.num.val
  let (xd, yn) ← divgcd c d
  let n ← checkedMul xn yn
  let d ← checkedMul xd yd
  return ⟨n, d⟩

/-- Mixed `//` and `/` promote numerator pairs, reduce, then promote the
denominator pairs; base/rational.jl:106-115,501. -/
def divMixed {t s} (x : Rat t) (y : Rat s) : Jl (Rat (t.promote s)) := do
  let a ← JInt.convert ((t.promote s).name) (t.promote s) x.num.val
  let b ← JInt.convert ((t.promote s).name) (t.promote s) y.num.val
  let (xn, yn) ← divgcd a b
  let c ← JInt.convert ((t.promote s).name) (t.promote s) x.den.val
  let d ← JInt.convert ((t.promote s).name) (t.promote s) y.den.val
  let (xd, yd) ← divgcd c d
  let xn ← if xd.val = 0 ∧ yn.val < 0 then checkedNeg xn else pure xn
  let n ← checkedMul xn yd
  let d ← checkedMul xd yn
  checkedDen n d

/-- Mixed rational remainders promote denominator pairs before checked
numerator multiplication; base/rational.jl:451-458. -/
def remainderMixed {t s} (op : JInt (t.promote s) → JInt (t.promote s) → Jl (JInt (t.promote s)))
    (x : Rat t) (y : Rat s) : Jl (Rat (t.promote s)) := do
  let c ← JInt.convert ((t.promote s).name) (t.promote s) x.den.val
  let d ← JInt.convert ((t.promote s).name) (t.promote s) y.den.val
  let (xd, yd) ← divgcd c d
  let xn ← JInt.convert ((t.promote s).name) (t.promote s) x.num.val
  let a ← checkedMul xn yd
  let yn ← JInt.convert ((t.promote s).name) (t.promote s) y.num.val
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
  let n ← JInt.convert (p.name) p n.int.val
  let d ← JInt.convert (p.name) p d.int.val
  return ⟨p, ⟨n, d⟩⟩

/-- Runtime-typed `Rational(num,den)` promotes before normalization;
base/rational.jl:48-49. -/
private def constructValues (n d : Division.Value) : Jl AnyRat := do
  let p := n.ty.promote d.ty
  let n ← JInt.convert (p.name) p n.int.val
  let d ← JInt.convert (p.name) p d.int.val
  let r ← ofInts n d
  return ⟨p, r⟩

/-- Runtime-typed `checked_den(num,den)`; base/rational.jl:27-28. -/
private def checkedDenValues (n d : Division.Value) : Jl AnyRat := do
  let p := n.ty.promote d.ty
  let n ← JInt.convert (p.name) p n.int.val
  let d ← JInt.convert (p.name) p d.int.val
  let r ← checkedDen n d
  return ⟨p, r⟩

/-- Checked scalar arithmetic promotes before operating; base/checked.jl:26-28. -/
private def checkedValues (op : {t : IntTy} → JInt t → JInt t → Jl (JInt t))
    (a b : Division.Value) : Jl Division.Value := do
  let p := a.ty.promote b.ty
  let a ← JInt.convert (p.name) p a.int.val
  let b ← JInt.convert (p.name) p b.int.val
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
def remIntMixed {t s} (x : Rat t) (y : JInt s) := withIntMixed (Division.rem Division.promotedRem) x y

/-- Mixed rational/integer `mod`; base/rational.jl:460-466. -/
def modIntMixed {t s} (x : Rat t) (y : JInt s) := withIntMixed (Division.mod (Division.rem Division.promotedRem)) x y

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
def intRemMixed {t s} (y : JInt s) (x : Rat t) := intRemainderMixed (Division.rem Division.promotedRem) y x

/-- Mixed integer/rational `mod`; base/rational.jl:474-480. -/
def intModMixed {t s} (y : JInt s) (x : Rat t) := intRemainderMixed (Division.mod (Division.rem Division.promotedRem)) y x

/-- Mixed rational/integer `*`, promoting only the denominator/integer
pair before cancellation; base/rational.jl:487-490. -/
def mulIntMixed {t s} (x : Rat t) (y : JInt s) : Jl AnyRat := do
  let d ← JInt.convert ((t.promote s).name) (t.promote s) x.den.val
  let n ← JInt.convert ((t.promote s).name) (t.promote s) y.val
  let (xd, yn) ← divgcd d n
  let n ← checkedValues @checkedMul (Division.pack x.num) (Division.pack yn)
  unsafeValues n (Division.pack xd)

/-- Mixed integer/rational `*`, preserving the reversed promotion order;
base/rational.jl:491-494. -/
def intMulMixed {t s} (y : JInt s) (x : Rat t) : Jl AnyRat := do
  let n ← JInt.convert ((s.promote t).name) (s.promote t) y.val
  let d ← JInt.convert ((s.promote t).name) (s.promote t) x.den.val
  let (yn, xd) ← divgcd n d
  let n ← checkedValues @checkedMul (Division.pack yn) (Division.pack x.num)
  unsafeValues n (Division.pack xd)

/-- Mixed rational/integer `//` and `/`; base/rational.jl:93-101,501. -/
def divIntMixed {t s} (x : Rat t) (y : JInt s) : Jl AnyRat := do
  let n ← JInt.convert ((t.promote s).name) (t.promote s) x.num.val
  let d ← JInt.convert ((t.promote s).name) (t.promote s) y.val
  let (xn, yn) ← divgcd n d
  let xn ← if x.den.val = 0 ∧ yn.val < 0 then checkedNeg xn else pure xn
  let d ← checkedValues @checkedMul (Division.pack x.den) (Division.pack yn)
  checkedDenValues (Division.pack xn) d

/-- Mixed integer/rational `//` and `/`; base/rational.jl:102-105,502. -/
def intDivMixed {t s} (x : JInt t) (y : Rat s) : Jl AnyRat := do
  let n ← JInt.convert ((t.promote s).name) (t.promote s) x.val
  let d ← JInt.convert ((t.promote s).name) (t.promote s) y.num.val
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

end JuliaLean.IntArith.Rational

namespace JuliaLean.Promotion

open JuliaLean.Float
open JuliaLean.IntArith.Rational



/-- `x << n` on the wide product type: `Int128` (`wrap`) when `wide128`, else `BigInt`. -/
def wideShl (wide128 : Bool) (x : Int) (n : Int) : Int :=
  if wide128 then (if n ≥ 128 then 0 else wrapInt .i128 (x * 2 ^ n.toNat)) else x * 2 ^ n.toNat

/-- The pair to which `rel` is finally applied, after the NaN checks;
`base/rational.jl:543-571`. `widemul` of a `Rational{T}` component with an `Int` component
is `Int128` for `T` of at most 64 bits and `BigInt` otherwise (`base/int.jl:923-924`). -/
def relPair (wide128 : Bool) (x y : Int × Int × Int) : Int × Int :=
  let (xn, xp, xd) := x
  let (yn, yp, yd) := y
  let (xn, xd) := if xd < 0 then (-xn, -xd) else (xn, xd)
  let (yn, yd) := if yd < 0 then (-yn, -yd) else (yn, yd)
  let xc := xn * yd
  let yc := yn * xd
  let xs := xc.sign
  let ys := yc.sign
  if xs != ys then (xs, ys)
  else if xs == 0 then (xn, yn)
  else
    let xb := ndigits2 xc + xp
    let yb := ndigits2 yc + yp
    if xb == yb then
      if xp > yp then (wideShl wide128 xc (xp - yp), yc) else (xc, wideShl wide128 yc (yp - xp))
    else if xc > 0 then (xb, yb) else (yb, xb)

/-- `decompose(x::Rational)`; `base/rational.jl:678`. -/
def decomposeR {t : IntTy} (x : Rat t) : Int × Int × Int := (x.num.val, 0, x.den.val)

def wide (t : IntTy) : Bool := t.bits ≤ 64

/-- `<(x::Rational, y::AbstractFloat)` and `<=`; `base/rational.jl:531-574`. -/
def ltRF {f : Fmt} {t : IntTy} (x : Rat t) (y : Fl f) : Bool :=
  if y.isnan then false else let p := relPair (wide t) (decomposeR x) (decomposeF y); decide (p.1 < p.2)
def leRF {f : Fmt} {t : IntTy} (x : Rat t) (y : Fl f) : Bool :=
  if y.isnan then false else let p := relPair (wide t) (decomposeR x) (decomposeF y); decide (p.1 ≤ p.2)
def ltFR {f : Fmt} {t : IntTy} (x : Fl f) (y : Rat t) : Bool :=
  if x.isnan then false else let p := relPair (wide t) (decomposeF x) (decomposeR y); decide (p.1 < p.2)
def leFR {f : Fmt} {t : IntTy} (x : Fl f) (y : Rat t) : Bool :=
  if x.isnan then false else let p := relPair (wide t) (decomposeF x) (decomposeR y); decide (p.1 ≤ p.2)


/-- `cmp(x::AbstractFloat, y::Rational)`; `base/rational.jl:531-574`. -/
def cmpFR {f : Fmt} {t : IntTy} (x : Fl f) (y : Rat t) : Int :=
  if x.isnan then 1
  else let p := relPair (wide t) (decomposeF x) (decomposeR y); icmp p.1 p.2

/-- `cmp(x::Rational, y::AbstractFloat)`; `base/rational.jl:531-574`. -/
def cmpRF {f : Fmt} {t : IntTy} (x : Rat t) (y : Fl f) : Int :=
  if y.isnan then -1
  else let p := relPair (wide t) (decomposeR x) (decomposeF y); icmp p.1 p.2

/-- `signbit(x::Rational) = signbit(x.num)`; `base/rational.jl:388`. -/
def signbitR {t : IntTy} (x : Rat t) : Bool := decide (x.num.val < 0)


end JuliaLean.Promotion
namespace JuliaLean.Promotion

open JuliaLean.Float
open JuliaLean.IntArith.Rational


/-- `hash(x::Rational{<:BitInteger64}, h)`; `base/rational.jl:679-701`. -/
def hashRat64 {t : IntTy} (x : Rat t) (h : HTerm) : HTerm :=
  let num := x.num.val
  let den := x.den.val
  if den == 1 then (if t == .u64 then .u64 num.toNat h else hashI64 num h)
  else if den == 0 then hashF64 (Fl.inf (decide (num ≤ 0))) h
  else
    let tail (pow num : Int) (h : HTerm) : HTerm :=
      let h := HTerm.int pow h
      HTerm.int (if pow > 0 then wrapInt t (num * 2 ^ (pow % 8).toNat) else num) h
    if den % 2 == 1 then
      let pow := trailingZeros num
      tail pow (num / 2 ^ pow) (HTerm.int den h)
    else
      let pz := trailingZeros den
      let den := den / 2 ^ pz
      let pow : Int := -(pz : Int)
      if den == 1 then
        if num.natAbs < 2 ^ 53 then hashExactF64 num pow h
        else tail pow num h
      else tail pow num (HTerm.int den h)

/-- Julia numbers of the modelled types. -/
inductive Num where
  | int (t : IntTy) (x : JInt t)
  | flt (T : FTy) (x : FV T)
  | rat (t : IntTy) (x : Rat t)

/-- `hash(x, h)` dispatch. -/
def hashNum : Num → HTerm → HTerm
  | .int t x, h =>
    match t with
    | .i128 | .u128 => hashReal t (x.val, 0, 1) h
    | .u64 => .u64 x.val.toNat h
    | _ => hashI64 x.val h
  | .flt .f64 x, h => hashF64 x h
  | .flt .f32 x, h => hashF32 x h
  | .flt .f16 x, h => hashF16 x h
  | .rat t x, h =>
    match t with
    | .i128 | .u128 => hashReal t (decomposeR x) h
    | _ => hashRat64 x h

end JuliaLean.Promotion
namespace JuliaLean.Promotion

open JuliaLean.Float
open JuliaLean.IntArith.Rational
open JuliaLean.IntArith.Checked

/-- `abs(x)` on a `BitInteger`, wrapping at `typemin`; `base/int.jl:181-183`. -/
def jabs {t : IntTy} (x : JInt t) : JInt t := if x.val < 0 then -x else x

/-- `min(a, b)` on one integer type. -/
def jmin {t : IntTy} (a b : JInt t) : JInt t := if b.val < a.val then b else a

/-- Errors caught by the `try` blocks of `rationalize`: `InexactError` and `OverflowError`;
`base/rational.jl:282,309`. -/
def caught : JlError → Bool
  | .inexactError _ | .overflowError _ => true
  | _ => false

/-- Best semiconvergent fallback after a failed step; `base/rational.jl:283-288,310-315`. -/
def semiconvergent {t : IntTy} (a : F64) (p q pp qq : JInt t) : Jl (Rat t) :=
  if F64.le a (F64.ofInt 2) || ((-p).val == p.val && p.val < 0) then ofInts p q
  else do
    let tmax := JInt.typemax t
    let iaP ← if p.val == 0 then pure tmax else JInt.fld (tmax - jabs pp) (jabs p)
    let iaQ ← if q.val == 0 then pure tmax else JInt.fld (tmax - qq) q
    let ia := jmin iaP iaQ
    if cmpFI .lt (T := .f64) (Fl.ofF64 (F64.div a (F64.ofInt 2))) ia then
      ofInts (ia * p + pp) (ia * q + qq)
    else ofInts p q

/-- One convergent step inside `try`; `base/rational.jl:276-280`. -/
def convergentStep {t : IntTy} (a : F64) (p q pp qq : JInt t) : Jl (JInt t × JInt t) := do
  let ia ← F64.int t a
  let np ← checkedAdd (← checkedMul ia p) pp
  let nq ← checkedAdd (← checkedMul ia q) qq
  return (np, nq)

/-- Loop state `(x, y, a, r, nt, t, tt, p, q, pp, qq)` of `base/rational.jl:262-304`. -/
structure RState (t : IntTy) where
  x : F64
  y : F64
  a : F64
  r : F64
  nt : F64
  t1 : F64
  tt : F64
  p : JInt t
  q : JInt t
  pp : JInt t
  qq : JInt t

/-- Either a returned result or the next loop state. -/
inductive Step (t : IntTy) where
  | done (r : Jl (Rat t))
  | next (s : RState t)

/-- The continued-fraction loop; `base/rational.jl:273-304`. Each iteration either returns
or performs one `divrem`; `fuel` bounds the number of iterations. -/
def ratLoop {t : IntTy} : Nat → RState t → Step t
  | 0, s => .next s
  | fuel + 1, s =>
    if F64.lt s.nt s.r then
      match convergentStep s.a s.p s.q s.pp s.qq with
      | .error e => if caught e then .done (semiconvergent s.a s.p s.q s.pp s.qq) else .done (.error e)
      | .ok (np, nq) =>
        let x := s.y
        let y := s.r
        let a := F64.divInteger x y .RoundToZero
        let r := F64.rem x y
        let tt := s.t1
        let t1 := s.nt
        let nt := F64.add (F64.mul a t1) tt
        ratLoop fuel ⟨x, y, a, r, nt, t1, tt, np, nq, s.p, s.q⟩
    else .next s

/-- `rationalize(T, x, tol=0)`; `base/rational.jl:256-319`. A binary64 continued fraction
has fewer than 1500 terms, which bounds the loop. -/
def rationalize (t : IntTy) (x : F64) : Jl (Rat t) := do
  if !t.signed && F64.lt x (F64.zero false) then throw (.overflowError "cannot negate unsigned number")
  if F64.isnan x then
    return (← ofInts (← F64.int t x) (JInt.lit t 1))
  if F64.isinf x then return ⟨JInt.lit t (if F64.lt x (F64.zero false) then -1 else 1), JInt.lit t 0⟩
  let p := JInt.lit t (if F64.lt x (F64.zero false) then -1 else 1)
  let x := F64.abs x
  let a := F64.trunc x
  let s : RState t := ⟨x, F64.one, a, F64.sub x a, F64.zero false, F64.zero false,
    F64.zero false, p, JInt.lit t 0, JInt.lit t 0, JInt.lit t 1⟩
  match ratLoop 1500 s with
  | .done r => r
  | .next s =>
    let aMin := F64.cld (F64.sub s.x s.tt) (F64.add s.y s.t1)
    let attempt : Jl (Rat t) := do
      let (np, nq) ← convergentStep aMin s.p s.q s.pp s.qq
      ofInts np nq
    match attempt with
    | .error e => if caught e then semiconvergent s.a s.p s.q s.pp s.qq else .error e
    | .ok r => .ok r

/-- `Float64(x::Rational{S})`: `Float64(num)/Float64(den)`; `base/rational.jl:196-199`. -/
def ratToF64 {t : IntTy} (r : Rat t) : F64 := F64.div (F64.ofJInt r.num) (F64.ofJInt r.den)

/-- `Rational{T}(x::Float64)`; `base/rational.jl:217-221`. -/
def rationalOfF64 (t : IntTy) (x : F64) : Jl (Rat t) := do
  let r ← rationalize t x
  if F64.eq x (ratToF64 r) then return r
  throw (.inexactError "Rational")

end JuliaLean.Promotion
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
  let xp ← JInt.convert ((t.promote s).name) (t.promote s) x.val
  let yp ← JInt.convert ((t.promote s).name) (t.promote s) y.val
  pure (xp, yp)

def promoteIntegerPairYX {t s : IntTy} (y : JInt s) (x : JInt t) :
    Jl (JInt (t.promote s) × JInt (t.promote s)) := do
  let yp ← JInt.convert ((t.promote s).name) (t.promote s) y.val
  let xp ← JInt.convert ((t.promote s).name) (t.promote s) x.val
  pure (yp, xp)

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


def sourceRoundingMode : Rounding → JuliaLean.base.float.RoundingMode
  | .toZero => .ToZero
  | .down => .Down
  | .up => .Up
  | .fromZero => .FromZero
  | .nearest => .Nearest
  | .nearestAway => .NearestTiesAway
  | .nearestUp => .NearestTiesUp
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
  divRound x y r := JuliaLean.base.div.divBitIntegerMode x y (sourceRoundingMode r)
  eq x y := x.val == y.val
  lt x y := decide (x.val < y.val)
  le x y := decide (x.val ≤ y.val)
  toInt x := x.val
  fromInt n := JInt.convert (t.name) t n

/-- Unbounded `Int` adapter for `RatIntOps`. Real `BigInt` (`base/gmp.jl`) is not yet mirrored;
non-directed rounding modes are not fabricated here. -/
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
      | _ => .error (.methodError "div")
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
  convertXP x := JInt.convert ((t.promote s).name) (t.promote s) x.val
  convertYP y := JInt.convert ((t.promote s).name) (t.promote s) y.val
  promotePX n d := do
    let d ← JInt.convert ((t.promote s).name) (t.promote s) d.val
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
def complexExactInvSource {α β ν γ : Type} (reim : β → α × α) (isinf : α → Bool)
    (zero : β → Jl β) (conj : β → Jl ν) (abs2 : β → Jl γ) (y : β) : Jl (ν × γ) := do
  let (c, d) := reim y
  let num ← if bwor (isinf c) (isinf d) then do
    let z ← zero y
    conj z
  else
    conj y
  let den ← abs2 y
  return (num, den)

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
def divideNumberComplexSource {X C N D P R : Type}
    (inverse : C → Jl (N × D)) (mul : X → N → Jl P)
    (divide : P → D → Jl R) (x : X) (y : C) : Jl R := do
  let (num, den) ← inverse y
  let prod ← mul x num
  divide prod den

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
def parseRationalSource {m : Type → Type} [Monad m]
    {T τ S F C L : Type}
    (split : S → Char → Nat → m (List F))
    (length : List F → m L) (isone : L → m Bool)
    (getOneBased : List F → JInt .i64 → m F)
    (startswith : F → Char → m Bool)
    (chop : F → Nat → Nat → m C)
    (parseOriginal : τ → S → m T)
    (parseFragment : τ → F → m T)
    (parseChopped : τ → C → m T)
    (rationalSingle : T → m (Rational T))
    (exactDivide : T → T → m (Rational T))
    (target : τ) (s : S) : m (Rational T) := do
  let ss ← split s '/' 2
  if ← isone (← length ss) then
    let n ← parseOriginal target s
    rationalSingle n
  else
    let ns ← getOneBased ss (JInt.lit .i64 1)
    let ds ← getOneBased ss (JInt.lit .i64 2)
    let denominatorText ←
      if ← startswith ds '/' then
        pure (Sum.inr (← chop ds 1 0))
      else pure (Sum.inl ds)
    let n ← parseFragment target ns
    let d ← match denominatorText with
      | .inl text => parseFragment target text
      | .inr text => parseChopped target text
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
def bigRationalSource {m : Type → Type} [Monad m] {T B : Type}
    (big : T → m B) (q : Rational T) : m (Rational B) := do
  let n ← big (numeratorRationalSource q)
  let d ← big (denominatorRationalSource q)
  return unsafeRationalSameSource n d

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
def signRatSource {T S R : Type}
    (oftype : Rational T → S → Jl (Rational R)) (sign : T → Jl S)
    (x : Rational T) : Jl (Rational R) := do
  let s ← sign x.num
  oftype x s

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
    (promoteYX : TY → TX → Jl (P × P))
    (divgcd : P → P → Jl (P × P)) (y : TY) (x : Rational TX) : Jl (Rational P) := do
  let (yP, xdenP) ← promoteYX y x.den
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
    (zero : Rational T → Jl (Rational T))
    (copysign : Rational T → Rational T → Jl (Rational T))
    (x : Bool) (y : Rational T) : Jl (Rational T) := do
  let signedZero ← copysign (← zero y) y
  pure (ifelse x y signedZero)

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

-- Source: base/rational.jl:514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def eqRatIntMethod {m : Type → Type} [Monad m] {T I A B R : Type}
    (equalDen : T → JInt .i64 → m A) (equalNum : T → I → m B)
    (bitAnd : A → B → m R) (x : Rational T) (y : I) : m R := do
  let a ← equalDen x.den (JInt.lit .i64 1)
  let b ← equalNum x.num y
  bitAnd a b

-- Source: base/rational.jl:515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def eqIntRatMethod {I T R : Type} (equal : Rational T → I → R)
    (x : I) (y : Rational T) : R := equal y x

-- Source: base/rational.jl:516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def ltRatIntMethod {m : Type → Type} [Monad m] {T I W R : Type}
    (widemul : T → I → m W) (less : T → W → m R)
    (x : Rational T) (y : I) : m R := do
  let product ← widemul x.den y
  less x.num product

-- Source: base/rational.jl:517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def ltIntRatMethod {m : Type → Type} [Monad m] {I T W R : Type}
    (widemul : I → T → m W) (less : W → T → m R)
    (x : I) (y : Rational T) : m R := do
  let product ← widemul x y.den
  less product y.num

-- Source: base/rational.jl:518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def leRatIntMethod {m : Type → Type} [Monad m] {T I W R : Type}
    (widemul : T → I → m W) (lessEqual : T → W → m R)
    (x : Rational T) (y : I) : m R := do
  let product ← widemul x.den y
  lessEqual x.num product

-- Source: base/rational.jl:519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def leIntRatMethod {m : Type → Type} [Monad m] {I T W R : Type}
    (widemul : I → T → m W) (lessEqual : W → T → m R)
    (x : I) (y : Rational T) : m R := do
  let product ← widemul x y.den
  lessEqual product y.num

-- Source: base/rational.jl:529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def eqRatFloatMethod {T F R : Type} (equal : F → Rational T → R)
    (q : Rational T) (x : F) : R := equal x q

-- Source: base/rational.jl:583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def eqComplexRatMethod {m : Type → Type} [Monad m] {C P Q A B R : Type}
    (isreal : C → m A) (real : C → m P) (equal : P → Q → m B)
    (bitAnd : A → B → m R) (z : C) (x : Q) : m R := do
  let a ← isreal z
  let re ← real z
  let b ← equal re x
  bitAnd a b

-- Source: base/rational.jl:584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def eqRatComplexMethod {m : Type → Type} [Monad m] {C P Q A B R : Type}
    (isreal : C → m A) (real : C → m P) (equal : P → Q → m B)
    (bitAnd : A → B → m R) (x : Q) (z : C) : m R := do
  let a ← isreal z
  let re ← real z
  let b ← equal re x
  bitAnd a b

-- Source: base/rational.jl:632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def powNumberRationalMethod {m : Type → Type} [Monad m] {T X D R : Type}
    (divide : T → T → m D) (power : X → D → m R)
    (x : X) (y : Rational T) : m R := do
  let exponent ← divide y.num y.den
  power x exponent

-- Source: base/rational.jl:633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def powFloatRationalMethod {m : Type → Type} [Monad m] {T X E R : Type}
    (convert : Rational T → m E) (power : X → E → m R)
    (x : X) (y : Rational T) : m R := do
  let exponent ← convert y
  power x exponent

-- Source: base/rational.jl:634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def powComplexRationalMethod {m : Type → Type} [Monad m]
    {T Target One P TypeRep E Z R : Type}
    (one : Target → m One) (powerOne : One → Rational T → m P)
    (typeOf : P → TypeRep) (convert : TypeRep → Rational T → m E)
    (power : Z → E → m R) (target : Target) (z : Z) (p : Rational T) : m R := do
  let unit ← one target
  let onePower ← powerOne unit p
  let exponent ← convert (typeOf onePower) p
  power z exponent

-- Source: base/rational.jl:642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def isOneRationalMethod {m : Type → Type} [Monad m] {T A R : Type}
    (isone : T → m A) (bitAnd : A → A → m R) (x : Rational T) : m R := do
  let a ← isone (numeratorRationalSource x)
  let b ← isone (denominatorRationalSource x)
  bitAnd a b

-- Source: base/rational.jl:644-646 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def lerpiMethod {m : Type → Type} [Monad m] {J D TA TB DS L QL R QR Out : Type}
    (sub : D → J → m DS) (mulLeft : DS → Rational TA → m L)
    (divLeft : L → D → m QL) (mulRight : J → Rational TB → m R)
    (divRight : R → D → m QR) (add : QL → QR → m Out)
    (j : J) (d : D) (a : Rational TA) (b : Rational TB) : m Out := do
  let difference ← sub d j
  let left ← mulLeft difference a
  let qleft ← divLeft left d
  let right ← mulRight j b
  let qright ← divRight right d
  add qleft qright


def eqRatIntSource {T I : Type}
    (eqOne : T → Bool) (eqNum : T → I → Bool)
    (x : Rational T) (y : I) : Bool :=
  eqRatIntMethod (m := Id) (fun den _ => eqOne den) eqNum bwand x y

/--
Julia source: base/rational.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Integer , y::Rational) = y == x
```
-/
def eqIntRatSource {I T : Type}
    (eqOne : T → Bool) (eqNum : T → I → Bool)
    (x : I) (y : Rational T) : Bool :=
  eqIntRatMethod (eqRatIntSource eqOne eqNum) x y

/--
Julia source: base/rational.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::Rational, y::Integer ) = x.num < widemul(x.den,y)
```
-/
def ltRatIntSource {T I W : Type}
    (widemul : T → I → W) (lt : T → W → Bool)
    (x : Rational T) (y : I) : Bool :=
  ltRatIntMethod (m := Id) widemul lt x y

/--
Julia source: base/rational.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<( x::Integer , y::Rational) = widemul(x,y.den) < y.num
```
-/
def ltIntRatSource {I T W : Type}
    (widemul : I → T → W) (lt : W → T → Bool)
    (x : I) (y : Rational T) : Bool :=
  ltIntRatMethod (m := Id) widemul lt x y

/--
Julia source: base/rational.jl:518-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Rational, y::Integer ) = x.num <= widemul(x.den,y)
```
-/
def leRatIntSource {T I W : Type}
    (widemul : T → I → W) (le : T → W → Bool)
    (x : Rational T) (y : I) : Bool :=
  leRatIntMethod (m := Id) widemul le x y

/--
Julia source: base/rational.jl:519-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
<=(x::Integer , y::Rational) = widemul(x,y.den) <= y.num
```
-/
def leIntRatSource {I T W : Type}
    (widemul : I → T → W) (le : W → T → Bool)
    (x : I) (y : Rational T) : Bool :=
  leIntRatMethod (m := Id) widemul le x y

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
def eqFloatRatSource {F T S C B G : Type}
    (isfinite : F → Bool) (countOnes : T → C) (eqOneC : C → Bool)
    (subOne : T → S) (topSetBit : S → B) (ldexp : F → B → F)
    (eqFI : F → T → Bool) (div : T → T → G) (eqFF : F → G → Bool)
    (x : F) (q : Rational T) : Bool :=
  if isfinite x then
    eqOneC (countOnes q.den) && eqFI (ldexp x (topSetBit (subOne q.den))) q.num
  else eqFF x (div q.num q.den)

/--
Julia source: base/rational.jl:529-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(q::Rational, x::AbstractFloat) = x == q
```
-/
def eqRatFloatSource {F T S C B G : Type}
    (isfinite : F → Bool) (countOnes : T → C) (eqOneC : C → Bool)
    (subOne : T → S) (topSetBit : S → B) (ldexp : F → B → F)
    (eqFI : F → T → Bool) (div : T → T → G) (eqFF : F → G → Bool)
    (q : Rational T) (x : F) : Bool :=
  eqRatFloatMethod (eqFloatRatSource isfinite countOnes eqOneC subOne topSetBit ldexp eqFI div eqFF) q x

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
def rationalFloatRelationSource
    {m : Type → Type} [Monad m]
    {X Y NX EX DX NY EY DY CX CY SX SY IX IY BX BY
      P ShiftX ShiftY R : Type}
    (cmpMode : Bool)
    (nanZero nanOne nanMinusOne relationFalse : R)
    (isnanX : X → m Bool) (isnanY : Y → m Bool)
    (decomposeX : X → m (NX × EX × DX))
    (decomposeY : Y → m (NY × EY × DY))
    (negativeDX : DX → m Bool) (negativeDY : DY → m Bool)
    (negNX : NX → m NX) (negDX : DX → m DX)
    (negNY : NY → m NY) (negDY : DY → m DY)
    (widemulXY : NX → DY → m CX)
    (widemulYX : NY → DX → m CY)
    (signX : CX → m SX) (signY : CY → m SY)
    (differentSigns : SX → SY → m Bool) (zeroSignX : SX → m Bool)
    (relSigns : SX → SY → m R) (relNumerators : NX → NY → m R)
    (ndigitsX : CX → JInt .i64 → m IX)
    (ndigitsY : CY → JInt .i64 → m IY)
    (addExponentX : IX → EX → m BX) (addExponentY : IY → EY → m BY)
    (sameBits : BX → BY → m Bool)
    (promoteProducts : CX → CY → m (P × P))
    (greaterExponent : EX → EY → m Bool)
    (subtractExponentXY : EX → EY → m ShiftX)
    (subtractExponentYX : EY → EX → m ShiftY)
    (shiftX : P → ShiftX → m P) (shiftY : P → ShiftY → m P)
    (relProducts : P → P → m R) (positiveProductX : CX → m Bool)
    (relBitsXY : BX → BY → m R) (relBitsYX : BY → BX → m R)
    (x : X) (y : Y) : m R := do
  if ← isnanX x then
    if cmpMode then
      if ← isnanY y then pure nanZero else pure nanOne
    else pure relationFalse
  else if ← isnanY y then
    if cmpMode then pure nanMinusOne else pure relationFalse
  else
    let (xn,xp,xd) ← decomposeX x
    let (yn,yp,yd) ← decomposeY y
    let (xn,xd) ← if ← negativeDX xd then
      let xn ← negNX xn
      let xd ← negDX xd
      pure (xn,xd)
    else pure (xn,xd)
    let (yn,yd) ← if ← negativeDY yd then
      let yn ← negNY yn
      let yd ← negDY yd
      pure (yn,yd)
    else pure (yn,yd)
    let xc ← widemulXY xn yd
    let yc ← widemulYX yn xd
    let xs ← signX xc
    let ys ← signY yc
    if ← differentSigns xs ys then relSigns xs ys
    else if ← zeroSignX xs then relNumerators xn yn
    else
      let xb ← addExponentX (← ndigitsX xc (JInt.lit .i64 2)) xp
      let yb ← addExponentY (← ndigitsY yc (JInt.lit .i64 2)) yp
      if ← sameBits xb yb then
        let (xc,yc) ← promoteProducts xc yc
        if ← greaterExponent xp yp then
          let xc ← shiftX xc (← subtractExponentXY xp yp)
          relProducts xc yc
        else
          let yc ← shiftY yc (← subtractExponentYX yp xp)
          relProducts xc yc
      else if ← positiveProductX xc then relBitsXY xb yb
      else relBitsYX yb xb

def ltRationalAbstractFloatSource
    {m : Type → Type} [Monad m]
    {T F NX EX DX NY EY DY CX CY SX SY IX IY BX BY P ShiftX ShiftY : Type}
    (isnanX : Rational T → m Bool) (isnanY : F → m Bool)
    (decomposeX : Rational T → m (NX × EX × DX)) (decomposeY : F → m (NY × EY × DY))
    (negativeDX : DX → m Bool) (negativeDY : DY → m Bool)
    (negNX : NX → m NX) (negDX : DX → m DX)
    (negNY : NY → m NY) (negDY : DY → m DY)
    (widemulXY : NX → DY → m CX) (widemulYX : NY → DX → m CY)
    (signX : CX → m SX) (signY : CY → m SY)
    (differentSigns : SX → SY → m Bool) (zeroSignX : SX → m Bool)
    (ltSigns : SX → SY → m Bool) (ltNumerators : NX → NY → m Bool)
    (ndigitsX : CX → JInt .i64 → m IX) (ndigitsY : CY → JInt .i64 → m IY)
    (addExponentX : IX → EX → m BX) (addExponentY : IY → EY → m BY)
    (sameBits : BX → BY → m Bool) (promoteProducts : CX → CY → m (P × P))
    (greaterExponent : EX → EY → m Bool)
    (subtractExponentXY : EX → EY → m ShiftX) (subtractExponentYX : EY → EX → m ShiftY)
    (shiftX : P → ShiftX → m P) (shiftY : P → ShiftY → m P)
    (ltProducts : P → P → m Bool) (positiveProductX : CX → m Bool)
    (ltBitsXY : BX → BY → m Bool) (ltBitsYX : BY → BX → m Bool)
    (x : Rational T) (y : F) : m Bool :=
  rationalFloatRelationSource false false false false false isnanX isnanY
    decomposeX decomposeY negativeDX negativeDY negNX negDX negNY negDY
    widemulXY widemulYX signX signY differentSigns zeroSignX ltSigns ltNumerators
    ndigitsX ndigitsY addExponentX addExponentY sameBits promoteProducts greaterExponent
    subtractExponentXY subtractExponentYX shiftX shiftY ltProducts positiveProductX
    ltBitsXY ltBitsYX x y

def ltAbstractFloatRationalSource
    {m : Type → Type} [Monad m]
    {F T NX EX DX NY EY DY CX CY SX SY IX IY BX BY P ShiftX ShiftY : Type}
    (isnanX : F → m Bool) (isnanY : Rational T → m Bool)
    (decomposeX : F → m (NX × EX × DX)) (decomposeY : Rational T → m (NY × EY × DY))
    (negativeDX : DX → m Bool) (negativeDY : DY → m Bool)
    (negNX : NX → m NX) (negDX : DX → m DX)
    (negNY : NY → m NY) (negDY : DY → m DY)
    (widemulXY : NX → DY → m CX) (widemulYX : NY → DX → m CY)
    (signX : CX → m SX) (signY : CY → m SY)
    (differentSigns : SX → SY → m Bool) (zeroSignX : SX → m Bool)
    (ltSigns : SX → SY → m Bool) (ltNumerators : NX → NY → m Bool)
    (ndigitsX : CX → JInt .i64 → m IX) (ndigitsY : CY → JInt .i64 → m IY)
    (addExponentX : IX → EX → m BX) (addExponentY : IY → EY → m BY)
    (sameBits : BX → BY → m Bool) (promoteProducts : CX → CY → m (P × P))
    (greaterExponent : EX → EY → m Bool)
    (subtractExponentXY : EX → EY → m ShiftX) (subtractExponentYX : EY → EX → m ShiftY)
    (shiftX : P → ShiftX → m P) (shiftY : P → ShiftY → m P)
    (ltProducts : P → P → m Bool) (positiveProductX : CX → m Bool)
    (ltBitsXY : BX → BY → m Bool) (ltBitsYX : BY → BX → m Bool)
    (x : F) (y : Rational T) : m Bool :=
  rationalFloatRelationSource false false false false false isnanX isnanY
    decomposeX decomposeY negativeDX negativeDY negNX negDX negNY negDY
    widemulXY widemulYX signX signY differentSigns zeroSignX ltSigns ltNumerators
    ndigitsX ndigitsY addExponentX addExponentY sameBits promoteProducts greaterExponent
    subtractExponentXY subtractExponentYX shiftX shiftY ltProducts positiveProductX
    ltBitsXY ltBitsYX x y

def leRationalAbstractFloatSource
    {m : Type → Type} [Monad m]
    {T F NX EX DX NY EY DY CX CY SX SY IX IY BX BY P ShiftX ShiftY : Type}
    (isnanX : Rational T → m Bool) (isnanY : F → m Bool)
    (decomposeX : Rational T → m (NX × EX × DX)) (decomposeY : F → m (NY × EY × DY))
    (negativeDX : DX → m Bool) (negativeDY : DY → m Bool)
    (negNX : NX → m NX) (negDX : DX → m DX)
    (negNY : NY → m NY) (negDY : DY → m DY)
    (widemulXY : NX → DY → m CX) (widemulYX : NY → DX → m CY)
    (signX : CX → m SX) (signY : CY → m SY)
    (differentSigns : SX → SY → m Bool) (zeroSignX : SX → m Bool)
    (leSigns : SX → SY → m Bool) (leNumerators : NX → NY → m Bool)
    (ndigitsX : CX → JInt .i64 → m IX) (ndigitsY : CY → JInt .i64 → m IY)
    (addExponentX : IX → EX → m BX) (addExponentY : IY → EY → m BY)
    (sameBits : BX → BY → m Bool) (promoteProducts : CX → CY → m (P × P))
    (greaterExponent : EX → EY → m Bool)
    (subtractExponentXY : EX → EY → m ShiftX) (subtractExponentYX : EY → EX → m ShiftY)
    (shiftX : P → ShiftX → m P) (shiftY : P → ShiftY → m P)
    (leProducts : P → P → m Bool) (positiveProductX : CX → m Bool)
    (leBitsXY : BX → BY → m Bool) (leBitsYX : BY → BX → m Bool)
    (x : Rational T) (y : F) : m Bool :=
  rationalFloatRelationSource false false false false false isnanX isnanY
    decomposeX decomposeY negativeDX negativeDY negNX negDX negNY negDY
    widemulXY widemulYX signX signY differentSigns zeroSignX leSigns leNumerators
    ndigitsX ndigitsY addExponentX addExponentY sameBits promoteProducts greaterExponent
    subtractExponentXY subtractExponentYX shiftX shiftY leProducts positiveProductX
    leBitsXY leBitsYX x y

def leAbstractFloatRationalSource
    {m : Type → Type} [Monad m]
    {F T NX EX DX NY EY DY CX CY SX SY IX IY BX BY P ShiftX ShiftY : Type}
    (isnanX : F → m Bool) (isnanY : Rational T → m Bool)
    (decomposeX : F → m (NX × EX × DX)) (decomposeY : Rational T → m (NY × EY × DY))
    (negativeDX : DX → m Bool) (negativeDY : DY → m Bool)
    (negNX : NX → m NX) (negDX : DX → m DX)
    (negNY : NY → m NY) (negDY : DY → m DY)
    (widemulXY : NX → DY → m CX) (widemulYX : NY → DX → m CY)
    (signX : CX → m SX) (signY : CY → m SY)
    (differentSigns : SX → SY → m Bool) (zeroSignX : SX → m Bool)
    (leSigns : SX → SY → m Bool) (leNumerators : NX → NY → m Bool)
    (ndigitsX : CX → JInt .i64 → m IX) (ndigitsY : CY → JInt .i64 → m IY)
    (addExponentX : IX → EX → m BX) (addExponentY : IY → EY → m BY)
    (sameBits : BX → BY → m Bool) (promoteProducts : CX → CY → m (P × P))
    (greaterExponent : EX → EY → m Bool)
    (subtractExponentXY : EX → EY → m ShiftX) (subtractExponentYX : EY → EX → m ShiftY)
    (shiftX : P → ShiftX → m P) (shiftY : P → ShiftY → m P)
    (leProducts : P → P → m Bool) (positiveProductX : CX → m Bool)
    (leBitsXY : BX → BY → m Bool) (leBitsYX : BY → BX → m Bool)
    (x : F) (y : Rational T) : m Bool :=
  rationalFloatRelationSource false false false false false isnanX isnanY
    decomposeX decomposeY negativeDX negativeDY negNX negDX negNY negDY
    widemulXY widemulYX signX signY differentSigns zeroSignX leSigns leNumerators
    ndigitsX ndigitsY addExponentX addExponentY sameBits promoteProducts greaterExponent
    subtractExponentXY subtractExponentYX shiftX shiftY leProducts positiveProductX
    leBitsXY leBitsYX x y

def cmpRationalAbstractFloatSource
    {m : Type → Type} [Monad m]
    {T F R NX EX DX NY EY DY CX CY SX SY IX IY BX BY P ShiftX ShiftY : Type}
    (nanZero nanOne nanMinusOne relationFalse : R)
    (isnanX : Rational T → m Bool) (isnanY : F → m Bool)
    (decomposeX : Rational T → m (NX × EX × DX)) (decomposeY : F → m (NY × EY × DY))
    (negativeDX : DX → m Bool) (negativeDY : DY → m Bool)
    (negNX : NX → m NX) (negDX : DX → m DX)
    (negNY : NY → m NY) (negDY : DY → m DY)
    (widemulXY : NX → DY → m CX) (widemulYX : NY → DX → m CY)
    (signX : CX → m SX) (signY : CY → m SY)
    (differentSigns : SX → SY → m Bool) (zeroSignX : SX → m Bool)
    (cmpSigns : SX → SY → m R) (cmpNumerators : NX → NY → m R)
    (ndigitsX : CX → JInt .i64 → m IX) (ndigitsY : CY → JInt .i64 → m IY)
    (addExponentX : IX → EX → m BX) (addExponentY : IY → EY → m BY)
    (sameBits : BX → BY → m Bool) (promoteProducts : CX → CY → m (P × P))
    (greaterExponent : EX → EY → m Bool)
    (subtractExponentXY : EX → EY → m ShiftX) (subtractExponentYX : EY → EX → m ShiftY)
    (shiftX : P → ShiftX → m P) (shiftY : P → ShiftY → m P)
    (cmpProducts : P → P → m R) (positiveProductX : CX → m Bool)
    (cmpBitsXY : BX → BY → m R) (cmpBitsYX : BY → BX → m R)
    (x : Rational T) (y : F) : m R :=
  rationalFloatRelationSource true nanZero nanOne nanMinusOne relationFalse isnanX isnanY
    decomposeX decomposeY negativeDX negativeDY negNX negDX negNY negDY
    widemulXY widemulYX signX signY differentSigns zeroSignX cmpSigns cmpNumerators
    ndigitsX ndigitsY addExponentX addExponentY sameBits promoteProducts greaterExponent
    subtractExponentXY subtractExponentYX shiftX shiftY cmpProducts positiveProductX
    cmpBitsXY cmpBitsYX x y

def cmpAbstractFloatRationalSource
    {m : Type → Type} [Monad m]
    {F T R NX EX DX NY EY DY CX CY SX SY IX IY BX BY P ShiftX ShiftY : Type}
    (nanZero nanOne nanMinusOne relationFalse : R)
    (isnanX : F → m Bool) (isnanY : Rational T → m Bool)
    (decomposeX : F → m (NX × EX × DX)) (decomposeY : Rational T → m (NY × EY × DY))
    (negativeDX : DX → m Bool) (negativeDY : DY → m Bool)
    (negNX : NX → m NX) (negDX : DX → m DX)
    (negNY : NY → m NY) (negDY : DY → m DY)
    (widemulXY : NX → DY → m CX) (widemulYX : NY → DX → m CY)
    (signX : CX → m SX) (signY : CY → m SY)
    (differentSigns : SX → SY → m Bool) (zeroSignX : SX → m Bool)
    (cmpSigns : SX → SY → m R) (cmpNumerators : NX → NY → m R)
    (ndigitsX : CX → JInt .i64 → m IX) (ndigitsY : CY → JInt .i64 → m IY)
    (addExponentX : IX → EX → m BX) (addExponentY : IY → EY → m BY)
    (sameBits : BX → BY → m Bool) (promoteProducts : CX → CY → m (P × P))
    (greaterExponent : EX → EY → m Bool)
    (subtractExponentXY : EX → EY → m ShiftX) (subtractExponentYX : EY → EX → m ShiftY)
    (shiftX : P → ShiftX → m P) (shiftY : P → ShiftY → m P)
    (cmpProducts : P → P → m R) (positiveProductX : CX → m Bool)
    (cmpBitsXY : BX → BY → m R) (cmpBitsYX : BY → BX → m R)
    (x : F) (y : Rational T) : m R :=
  rationalFloatRelationSource true nanZero nanOne nanMinusOne relationFalse isnanX isnanY
    decomposeX decomposeY negativeDX negativeDY negNX negDX negNY negDY
    widemulXY widemulYX signX signY differentSigns zeroSignX cmpSigns cmpNumerators
    ndigitsX ndigitsY addExponentX addExponentY sameBits promoteProducts greaterExponent
    subtractExponentXY subtractExponentYX shiftX shiftY cmpProducts positiveProductX
    cmpBitsXY cmpBitsYX x y

/--
Julia source: base/rational.jl:583-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(z::Complex , x::Rational) = isreal(z) & (real(z) == x)
```
-/
def eqComplexRatSource {C R Q : Type} (isreal : C → Bool) (real : C → R)
    (eq : R → Q → Bool) (z : C) (x : Q) : Bool :=
  eqComplexRatMethod (m := Id) isreal real eq bwand z x

/--
Julia source: base/rational.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
==(x::Rational, z::Complex ) = isreal(z) & (real(z) == x)
```
-/
def eqRatComplexSource {C R Q : Type} (isreal : C → Bool) (real : C → R)
    (eq : R → Q → Bool) (x : Q) (z : C) : Bool :=
  eqRatComplexMethod (m := Id) isreal real eq bwand x z

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
def roundRatTypedSource (T : Type) {Tr CS Q : Type}
    (iszero : Tr → Bool) (targetIsInteger : Bool)
    (one zero : Tr) (copysign : Rational Tr → Tr → Jl CS)
    (convertInf : CS → Jl T)
    (div : Tr → Tr → Rounding → Jl Q)
    (convertQuot : Q → Jl T)
    (x : Rational Tr) (r : Rounding := .nearest) : Jl T := do
  if iszero (denominatorRationalSource x) && !targetIsInteger then
    let signedInf ← copysign (unsafeRationalSameSource one zero) (numeratorRationalSource x)
    convertInf signedInf
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
  powNumberRationalMethod (m := Id) divide power x y

/--
Julia source: base/rational.jl:633-633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(x::T, y::Rational) where {T<:AbstractFloat} = x^convert(T,y)
```
-/
def powFloatRationalSource {T α β : Type}
    (convert : Rational T → α) (power : β → α → β) (x : β) (y : Rational T) : β :=
  powFloatRationalMethod (m := Id) convert power x y

/--
Julia source: base/rational.jl:634-634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
^(z::Complex{T}, p::Rational) where {T<:Real} = z^convert(typeof(one(T)^p), p)
```
-/
def powComplexRationalSource {T α β γ δ : Type}
    (onePower : Rational T → β) (typeOf : β → γ) (convert : γ → Rational T → δ)
    (power : α → δ → α) (z : α) (p : Rational T) : α :=
  powComplexRationalMethod (m := Id) (fun _ : Unit => ()) (fun _ q => onePower q)
    typeOf convert power () z p

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
def isZeroRationalSource {T R : Type} (iszero : T → R) (x : Rational T) : R :=
  iszero (numeratorRationalSource x)

/--
Julia source: base/rational.jl:642-642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isone(x::Rational) = isone(numerator(x)) & isone(denominator(x))
```
-/
def isOneRationalSource {T : Type} (isone : T → Bool) (x : Rational T) : Bool :=
  isOneRationalMethod (m := Id) isone bwand x

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
    (j : J) (d : D) (a : Rational TA) (b : Rational TB) : Jl R :=
  lerpiMethod (fun d j => pure (sub d j)) mulLeft divLeft mulRight divRight add j d a b

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
inductive RationalGcdxCoefficients (P A B : Type) where
  | direct : P → P → RationalGcdxCoefficients P A B
  | computed : A → B → RationalGcdxCoefficients P A B

def gcdxRationalSource {TX TY P NX DX NY DY QX QY G A B : Type}
    (isinfX : Rational TX → Bool) (isinfY : Rational TY → Bool)
    (integerGcd : TX → TY → Jl P) (integerLcm : TX → TY → Jl P)
    (iszero : P → Bool) (zero one : P → P)
    (iszeroX : TX → Bool) (iszeroY : TY → Bool)
    (ifelse : Bool → P → P → P)
    (divNX : TX → P → Jl NX) (divDX : P → TX → Jl DX)
    (divNY : TY → P → Jl NY) (divDY : P → TY → Jl DY)
    (mulX : NX → DX → Jl QX) (mulY : NY → DY → Jl QY)
    (gcdx : QX → QY → Jl (G × A × B))
    (x : Rational TX) (y : Rational TY) :
    Jl (Rational P × RationalGcdxCoefficients P A B) := do
  let c ← gcdRationalSource isinfX isinfY integerGcd integerLcm x y
  if iszero c.num then
    pure (c,.direct (zero c.num) c.num)
  else if iszero c.den then
    let a := ifelse (iszeroX x.den) (one c.den) c.den
    let b := ifelse (iszeroY y.den) (one c.den) c.den
    pure (c,.direct a b)
  else
    let xNum ← divNX x.num c.num
    let xDen ← divDX c.den x.den
    let idivX ← mulX xNum xDen
    let yNum ← divNY y.num c.num
    let yDen ← divDY c.den y.den
    let idivY ← mulY yNum yDen
    let (_,a,b) ← gcdx idivX idivY
    pure (c,.computed a b)

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
def lengthRationalRangeSource {m : Type → Type} [Monad m] {R T D A Q : Type}
    (first last : R → m (Rational T)) (sub : T → T → D)
    (add : D → T → A) (div : A → T → m Q) (r : R) : m Q := do
  let f ← first r
  let l ← last r
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
def checkedLengthRationalRangeSource {m : Type → Type} [Monad m] {R T Q : Type}
    (first last : R → m (Rational T)) (isempty : R → m Bool)
    (sub : T → T → Q) (checkedSub checkedAdd : T → T → m T)
    (div : T → T → m Q) (r : R) : m Q := do
  let f ← first r
  let l ← last r
  if ← isempty r then pure (sub f.num f.num)
  else
    let diff ← checkedSub l.num f.num
    let sum ← checkedAdd diff f.den
    div sum f.den

def intSign (x : Int) : Int :=
  if x < 0 then -1 else if x > 0 then 1 else 0

def intCmp (a b : Int) : Int :=
  if a < b then -1 else if b < a then 1 else 0

def widemulBitIntI64 {t : IntTy} (x : JInt t) (y : JInt .i64) : Jl (JInt .i128) :=
  match JuliaLean.base.int.widenType t with
  | some wt =>
    if t.signed then do
      let p ← JuliaLean.base.number.widemul
        (fun a : JInt t => JInt.convert (wt.name) wt a.val)
        (fun b : JInt .i64 => JInt.convert (IntTy.i128.name) .i128 b.val)
        (fun a b => .ok (JuliaLean.base.int.binop JuliaLean.base.int.mulSame a b)) x y
      JInt.convert (IntTy.i128.name) .i128 p.val
    else
      let p := JuliaLean.base.int.widemul_Unsigned_Signed
        (JuliaLean.base.int.widenTo wt) (JuliaLean.base.int.widenTo .i128) x y
      JInt.convert (IntTy.i128.name) .i128 p.val
  | none => .error (.methodError "widen")

def widemulI64BitInt {t : IntTy} (x : JInt .i64) (y : JInt t) : Jl (JInt .i128) :=
  match JuliaLean.base.int.widenType t with
  | some wt =>
    if t.signed then do
      let p ← JuliaLean.base.number.widemul
        (fun a : JInt .i64 => JInt.convert (IntTy.i128.name) .i128 a.val)
        (fun b : JInt t => JInt.convert (wt.name) wt b.val)
        (fun a b => .ok (JuliaLean.base.int.binop JuliaLean.base.int.mulSame a b)) x y
      JInt.convert (IntTy.i128.name) .i128 p.val
    else
      let p := JuliaLean.base.int.widemul_Signed_Unsigned
        (JuliaLean.base.int.widenTo .i128) (JuliaLean.base.int.widenTo wt) x y
      JInt.convert (IntTy.i128.name) .i128 p.val
  | none => .error (.methodError "widen")

def signBitInteger {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  if t.signed then
    JuliaLean.base.number.signReal
      (fun _ => .ok (JInt.lit t 0))
      (fun a b => .ok (JuliaLean.base.int.lt a b))
      (fun a b => .ok (JuliaLean.base.int.lt b a))
      (fun _ => .ok (JInt.lit t 1))
      (fun _ n => JInt.convert (t.name) t n)
      (fun _ a => .ok a)
      JuliaLean.base.int.ifelse x
  else
    JuliaLean.base.number.signUnsigned
      (fun _ => .ok (JInt.lit t 0))
      (fun a b => .ok (JuliaLean.base.int.lt b a))
      (fun _ => .ok (JInt.lit t 1))
      (fun _ n => JInt.convert (t.name) t n)
      JuliaLean.base.int.ifelse x

def signBool (x : Bool) : Jl Bool := .ok x

def signBitRationalSource {t : IntTy} (x : Rat t) : Jl (Rat t) :=
  signRatSource
    (fun _ s => convertRatSource (JInt t) (fun v => JInt.convert (t.name) t v.val)
      (rationalFromIntegerGeneric unsafeRationalSameSource (fun _ => JInt.lit t 1) s))
    signBitInteger x

private def rationalDigitCallees : JuliaLean.base.intfuncs.DigitCallees where
  quotient t b _ _ x y := do
    let (a, d) := JuliaLean.base.int.promoteSameSign (JInt.lit t x) (JInt.lit b y)
    let q ← JuliaLean.base.int.divSame a d
    pure q.val

def ndigits0zBitInteger {t b : IntTy} (x : JInt t) (base : JInt b) : Jl (JInt .i64) :=
  JuliaLean.base.intfuncs.ndigitsZeroBits rationalDigitCallees x base

def promoteSamePair {α : Type} (x y : α) : Jl (α × α) :=
  match JuliaLean.base.promotion.promoteSameType x y [] with
  | [a, b] => .ok (a, b)
  | _ => .error (.methodError "promote")

def cmpBitIntegers {s u : IntTy} (x : JInt s) (y : JInt u) : JInt .i64 :=
  JInt.lit .i64 (JuliaLean.base.operators.cmpInteger JuliaLean.base.int.lt JuliaLean.base.int.lt x y)

def cmpRatFloatSource {t : IntTy} {f : JuliaLean.base.float.FTy}
    (q : Rat t) (x : JuliaLean.base.float.FV f) : Jl (JInt .i64) :=
  cmpRationalAbstractFloatSource
    (JInt.lit .i64 0) (JInt.lit .i64 1) (JInt.lit .i64 (-1)) (JInt.lit .i64 0)
    (fun _ => .ok false) (fun y => .ok (JuliaLean.base.float.isnan_IEEEFloat y))
    (fun a => .ok (decomposeSource a)) (fun b => .ok (JuliaLean.base.float.decompose b))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (jintOps t).neg (jintOps t).neg (jintOps .i64).neg (jintOps .i64).neg
    widemulBitIntI64 widemulI64BitInt signBitInteger signBitInteger
    (fun a b => .ok (!JuliaLean.base.int.eq a b))
    (fun s => .ok (JuliaLean.base.int.eq s (JInt.lit .i64 0)))
    (fun a b => .ok (cmpBitIntegers a b)) (fun a b => .ok (cmpBitIntegers a b))
    ndigits0zBitInteger ndigits0zBitInteger
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.eq a b)) promoteSamePair
    (fun a b => .ok (JuliaLean.base.int.lt b a))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun a b => .ok (cmpBitIntegers a b))
    (fun w => .ok (JuliaLean.base.int.lt (JInt.lit .i64 0) w))
    (fun a b => .ok (cmpBitIntegers a b)) (fun a b => .ok (cmpBitIntegers a b)) q x

def cmpFloatRatSource {t : IntTy} {f : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV f) (q : Rat t) : Jl (JInt .i64) :=
  cmpAbstractFloatRationalSource
    (JInt.lit .i64 0) (JInt.lit .i64 1) (JInt.lit .i64 (-1)) (JInt.lit .i64 0)
    (fun a => .ok (JuliaLean.base.float.isnan_IEEEFloat a)) (fun _ => .ok false)
    (fun a => .ok (JuliaLean.base.float.decompose a)) (fun b => .ok (decomposeSource b))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (jintOps .i64).neg (jintOps .i64).neg (jintOps t).neg (jintOps t).neg
    widemulI64BitInt widemulBitIntI64 signBitInteger signBitInteger
    (fun a b => .ok (!JuliaLean.base.int.eq a b))
    (fun s => .ok (JuliaLean.base.int.eq s (JInt.lit .i64 0)))
    (fun a b => .ok (cmpBitIntegers a b)) (fun a b => .ok (cmpBitIntegers a b))
    ndigits0zBitInteger ndigits0zBitInteger
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.eq a b)) promoteSamePair
    (fun a b => .ok (JuliaLean.base.int.lt b a))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun a b => .ok (cmpBitIntegers a b))
    (fun w => .ok (JuliaLean.base.int.lt (JInt.lit .i64 0) w))
    (fun a b => .ok (cmpBitIntegers a b)) (fun a b => .ok (cmpBitIntegers a b)) x q

def ltRatFloatSource {t : IntTy} {f : JuliaLean.base.float.FTy}
    (q : Rat t) (x : JuliaLean.base.float.FV f) : Jl Bool :=
  ltRationalAbstractFloatSource
    (fun _ => .ok false) (fun y => .ok (JuliaLean.base.float.isnan_IEEEFloat y))
    (fun a => .ok (decomposeSource a)) (fun b => .ok (JuliaLean.base.float.decompose b))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (jintOps t).neg (jintOps t).neg (jintOps .i64).neg (jintOps .i64).neg
    widemulBitIntI64 widemulI64BitInt signBitInteger signBitInteger
    (fun a b => .ok (!JuliaLean.base.int.eq a b))
    (fun s => .ok (JuliaLean.base.int.eq s (JInt.lit .i64 0)))
    (fun a b => .ok (JuliaLean.base.int.lt a b)) (fun a b => .ok (JuliaLean.base.int.lt a b))
    ndigits0zBitInteger ndigits0zBitInteger
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.eq a b)) promoteSamePair
    (fun a b => .ok (JuliaLean.base.int.lt b a))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun a b => .ok (JuliaLean.base.int.lt a b))
    (fun w => .ok (JuliaLean.base.int.lt (JInt.lit .i64 0) w))
    (fun a b => .ok (JuliaLean.base.int.lt a b)) (fun a b => .ok (JuliaLean.base.int.lt a b)) q x

def ltFloatRatSource {t : IntTy} {f : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV f) (q : Rat t) : Jl Bool :=
  ltAbstractFloatRationalSource
    (fun a => .ok (JuliaLean.base.float.isnan_IEEEFloat a)) (fun _ => .ok false)
    (fun a => .ok (JuliaLean.base.float.decompose a)) (fun b => .ok (decomposeSource b))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (jintOps .i64).neg (jintOps .i64).neg (jintOps t).neg (jintOps t).neg
    widemulI64BitInt widemulBitIntI64 signBitInteger signBitInteger
    (fun a b => .ok (!JuliaLean.base.int.eq a b))
    (fun s => .ok (JuliaLean.base.int.eq s (JInt.lit .i64 0)))
    (fun a b => .ok (JuliaLean.base.int.lt a b)) (fun a b => .ok (JuliaLean.base.int.lt a b))
    ndigits0zBitInteger ndigits0zBitInteger
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.eq a b)) promoteSamePair
    (fun a b => .ok (JuliaLean.base.int.lt b a))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun a b => .ok (JuliaLean.base.int.lt a b))
    (fun w => .ok (JuliaLean.base.int.lt (JInt.lit .i64 0) w))
    (fun a b => .ok (JuliaLean.base.int.lt a b)) (fun a b => .ok (JuliaLean.base.int.lt a b)) x q

def leRatFloatSource {t : IntTy} {f : JuliaLean.base.float.FTy}
    (q : Rat t) (x : JuliaLean.base.float.FV f) : Jl Bool :=
  leRationalAbstractFloatSource
    (fun _ => .ok false) (fun y => .ok (JuliaLean.base.float.isnan_IEEEFloat y))
    (fun a => .ok (decomposeSource a)) (fun b => .ok (JuliaLean.base.float.decompose b))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (jintOps t).neg (jintOps t).neg (jintOps .i64).neg (jintOps .i64).neg
    widemulBitIntI64 widemulI64BitInt signBitInteger signBitInteger
    (fun a b => .ok (!JuliaLean.base.int.eq a b))
    (fun s => .ok (JuliaLean.base.int.eq s (JInt.lit .i64 0)))
    (fun a b => .ok (JuliaLean.base.int.le a b)) (fun a b => .ok (JuliaLean.base.int.le a b))
    ndigits0zBitInteger ndigits0zBitInteger
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.eq a b)) promoteSamePair
    (fun a b => .ok (JuliaLean.base.int.lt b a))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun a b => .ok (JuliaLean.base.int.le a b))
    (fun w => .ok (JuliaLean.base.int.lt (JInt.lit .i64 0) w))
    (fun a b => .ok (JuliaLean.base.int.le a b)) (fun a b => .ok (JuliaLean.base.int.le a b)) q x

def leFloatRatSource {t : IntTy} {f : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV f) (q : Rat t) : Jl Bool :=
  leAbstractFloatRationalSource
    (fun a => .ok (JuliaLean.base.float.isnan_IEEEFloat a)) (fun _ => .ok false)
    (fun a => .ok (JuliaLean.base.float.decompose a)) (fun b => .ok (decomposeSource b))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (fun d => .ok (JuliaLean.base.int.lt d (JInt.lit .i64 0)))
    (jintOps .i64).neg (jintOps .i64).neg (jintOps t).neg (jintOps t).neg
    widemulI64BitInt widemulBitIntI64 signBitInteger signBitInteger
    (fun a b => .ok (!JuliaLean.base.int.eq a b))
    (fun s => .ok (JuliaLean.base.int.eq s (JInt.lit .i64 0)))
    (fun a b => .ok (JuliaLean.base.int.le a b)) (fun a b => .ok (JuliaLean.base.int.le a b))
    ndigits0zBitInteger ndigits0zBitInteger
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.add a b))
    (fun a b => .ok (JuliaLean.base.int.eq a b)) promoteSamePair
    (fun a b => .ok (JuliaLean.base.int.lt b a))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun a b => .ok (JuliaLean.base.int.sub a b))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun v s => .ok (JuliaLean.base.int.shl_Int v s))
    (fun a b => .ok (JuliaLean.base.int.le a b))
    (fun w => .ok (JuliaLean.base.int.lt (JInt.lit .i64 0) w))
    (fun a b => .ok (JuliaLean.base.int.le a b)) (fun a b => .ok (JuliaLean.base.int.le a b)) x q

/-- Concrete integer calls used when instantiating the source constructor. -/
abbrev rationalBitsSource {t : IntTy} : JInt t → JInt t → Jl (Rat t) :=
  (rationalSameSource (jintOps t) JuliaLean.base.float.uabs (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) (fun a => JInt.convert (t.name) t a.val) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) Prod.mk)

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
    (fun r => some (convertRatSource (JInt target) (fun v => JInt.convert (target.name) target v.val) r))
    (abstractFloatRatSource JuliaLean.base.float.float_BitInteger JuliaLean.base.float.div_IEEEFloat)
    isfinite (fun f => half (eps f)) toleranceEnough
    (fun f t => rationalizeF64 target f (tolToF64 t) showTol) x tol inexactErrorCore


/-- Native `copysign(x::Rational{T}, y::T)` using `JuliaLean.base.number.copysign`. -/
def copysignRatBitInt {t : IntTy} (x : Rat t) (y : JInt t) : Jl (Rat t) :=
  JuliaLean.base.number.copysign
    (fun q => .ok (signbitRatSource (jintOps t).signbit q))
    (fun n => .ok ((jintOps t).signbit n))
    (if h : t.signed = true then negBitSignedSource h
     else negUnsignedSource (jintOps t).zero (fun a b => decide (a.val ≠ b.val)))
    (fun q => .ok (unaryPlusRatSource (jintOps t).uplus q))
    JuliaLean.base.int.ifelse x y

/-- Fixed-width integer instantiation of Julia's rational rounding method. -/
abbrev roundBitsSource {t : IntTy} (target : IntTy) (x : Rat t) (mode : Rounding) : Jl (JInt target) :=
  roundRatTypedSource (JInt target) (jintOps t).iszero true
    (jintOps t).one (jintOps t).zero copysignRatBitInt (fun _ => .error .divideError)
    (fun a b r => JuliaLean.base.div.divBitIntegerMode a b (sourceRoundingMode r))
    (fun n => JInt.convert (target.name) target n.val) x mode

def promoteFTy (f1 f2 : JuliaLean.base.float.FTy) : JuliaLean.base.float.FTy :=
  ((JuliaLean.base.float.promote_rule_float f1 f2).or
    (JuliaLean.base.float.promote_rule_float f2 f1)).getD f1

/-- Heterogeneous IEEE float equality via `promotion.equalNumber` (`base/promotion.jl:516`). -/
def equalIEEEFloatPromoted {f1 f2 : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV f1) (y : JuliaLean.base.float.FV f2) : Bool :=
  JuliaLean.base.promotion.equalNumber (m := Id)
    (fun a b => (JuliaLean.base.float.convertFloat (promoteFTy f1 f2) a,
                 JuliaLean.base.float.convertFloat (promoteFTy f1 f2) b))
    JuliaLean.base.float.eq_IEEEFloat x y

/-- Heterogeneous IEEE float `<=` via `promotion.lessEqualNumber` (`base/promotion.jl:518`). -/
def lessEqualIEEEFloatPromoted {f1 f2 : JuliaLean.base.float.FTy}
    (x : JuliaLean.base.float.FV f1) (y : JuliaLean.base.float.FV f2) : Bool :=
  JuliaLean.base.promotion.lessEqualNumber (m := Id)
    (fun a b => (JuliaLean.base.float.convertFloat (promoteFTy f1 f2) a,
                 JuliaLean.base.float.convertFloat (promoteFTy f1 f2) b))
    JuliaLean.base.float.le_IEEEFloat x y
/-- Heterogeneous float-vs-integer `<=` via `promotion.lessEqualNumber` (`base/promotion.jl:518`). -/
def lessEqualFloat64BitIntPromoted {t : IntTy}
    (x : JuliaLean.base.float.FV .f64) (y : JInt t) : Bool :=
  JuliaLean.base.promotion.lessEqualNumber (m := Id)
    (fun a b => (a, JuliaLean.base.float.floatOfInt .f64 b))
    JuliaLean.base.float.le_IEEEFloat x y

/-- Concrete same-width instantiation of the source complex integer quotient. -/
abbrev complexIntegerQuotientSource {t : IntTy} (x y : ComplexValue (JInt t)) : Jl (ComplexValue (Rat t)) :=
  divideComplexIntegersSource (fun z => (z.re,z.im)) (fun z => (z.re,z.im))
    (fun a b c d =>
      match JuliaLean.base.promotion.promoteSameType a b [c, d] with
      | [x1, x2, x3, x4] => .ok (x1, x2, x3, x4)
      | _ => .error (.methodError "promote"))
    (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))
    checkedMul checkedAdd checkedNeg ComplexValue.mk
    (exactDivideComplexReal (exactDivideIntsSource rationalBitsSource) ComplexValue.mk ComplexValue.re ComplexValue.im) x y

/-- Concrete mixed-width instantiation of the source complex integer quotient (`P10b`). -/
abbrev complexIntegerQuotientMixedSource {tx ty : IntTy}
    (x : ComplexValue (JInt tx)) (y : ComplexValue (JInt ty)) :
    Jl (ComplexValue (Rat (((tx.promote tx).promote ty).promote ty))) :=
  divideComplexIntegersSource (fun z => (z.re,z.im)) (fun z => (z.re,z.im))
    JuliaLean.base.promotion.promoteFourBitIntegers
    (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd
      (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int))))
      (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))
    checkedMul checkedAdd checkedNeg ComplexValue.mk
    (exactDivideComplexReal (exactDivideIntsSource rationalBitsSource) ComplexValue.mk ComplexValue.re ComplexValue.im) x y

/-- Same-width integer/rational instantiation of the interpolation source method. -/
abbrev lerpiBitsSource {t : IntTy} (j d : JInt t) (a b : Rat t) : Jl (Rat t) :=
  lerpiSource (fun d j => d - j)
    (mulIntRatSource (samePromoteOps (jintOps t)) (samePromoteOps (jintOps t)).promote (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))))
    (slashRationalUnionSource (divRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))))
    (mulIntRatSource (samePromoteOps (jintOps t)) (samePromoteOps (jintOps t)).promote (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))))
    (slashRationalUnionSource (divRatIntSource (samePromoteOps (jintOps t)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int)))))))
    (addRatSource (samePromoteOps (jintOps t)) (fun a b => .ok (a,b))
      (fun q => decide (q.den.val = 0)) (eqRatSource (fun a b : JInt _ => a.val == b.val) (fun a b : JInt _ => a.val == b.val)) (divgcdSource (fun u : JInt _ => u.val.natAbs) (fun v : JInt _ => v.val.natAbs) Nat.gcd (fun u g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if u.val < 0 then -((u.val.natAbs / g : Nat) : Int) else ((u.val.natAbs / g : Nat) : Int)))) (fun v g => if g = 0 then .error .divideError else .ok (JInt.wrap _ (if v.val < 0 then -((v.val.natAbs / g : Nat) : Int) else ((v.val.natAbs / g : Nat) : Int))))) rationalBitsSource) j d a b

def divgcdBits {t : IntTy} : JInt t → JInt t → Jl (JInt t × JInt t) :=
  divgcdSource JuliaLean.base.float.uabs JuliaLean.base.float.uabs
    JuliaLean.base.intfuncs.gcd_BitInteger
    (fun x dg => do JuliaLean.base.intfuncs.divByUnsigned t x (← dg))
    (fun y dg => do JuliaLean.base.intfuncs.divByUnsigned t y (← dg))

def rationalConstructNonzero {t : IntTy} (num den : JInt t) : Jl (Rat t) := do
  if !t.signed then
    let numZero ← JuliaLean.base.intfuncs.bitsIszeroCall num
    if !numZero && xor (JuliaLean.base.int.signbit den) (JuliaLean.base.int.signbit num) then
      .error (inexactErrorCore "Rational" (Rat t) (num,den))
    else
      let (un,ud) ← divgcdBits (JuliaLean.base.float.uabs num) (JuliaLean.base.float.uabs den)
      let n ← JuliaLean.base.int.convert t un
      let d ← JuliaLean.base.int.convert t ud
      let (n,d) := JuliaLean.base.intfuncs.promoteSamePair n d
      unsafeRationalTypeSource (JInt t) (JuliaLean.base.int.convert t)
        (JuliaLean.base.int.convert t) n d
  else
    let (rn,rd) ← divgcdBits num den
    let n ← JuliaLean.base.int.convert t rn
    let d ← JuliaLean.base.int.convert t rd
    let (n,d) := JuliaLean.base.intfuncs.promoteSamePair n d
    checkedDenTypeSource (JInt t)
      { jintOps t with
        signbit := JuliaLean.base.int.signbit
        checkedNeg := JuliaLean.base.checked.checkedNegBits } n d

def rationalSameBitsSource {t : IntTy} (num den : JInt t) : Jl (Rat t) := do
  let denZero ← JuliaLean.base.intfuncs.bitsIszeroCall den
  if denZero then
    let numZero ← JuliaLean.base.intfuncs.bitsIszeroCall num
    if numZero then
      throwRationalZeroSource (fun s => JlError.argumentError (s.render id)) t.name
    else rationalConstructNonzero num den
  else rationalConstructNonzero num den

end JuliaLean.base.rational

namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- Native heterogeneous `divgcd`, with the source's return-tuple conversions
after both quotient calls. Julia source: base/rational.jl:59-62.
All arithmetic is dispatched to the installed machine-integer models. -/
-- Source: base/rational.jl:59-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer}
--     g = gcd(uabs(x), uabs(y))
--     div(x,g), div(y,g)
-- end
-- /Source
def divgcdMixed {t s : IntTy} (x : JInt t) (y : JInt s) :
    Jl (JInt t × JInt s) := do
  let ux := JuliaLean.base.float.uabs x
  let uy := JuliaLean.base.float.uabs y
  let (a, b) := JuliaLean.base.int.promoteSameSign ux uy
  let g ← JuliaLean.base.intfuncs.gcd_BitInteger a b
  let qx ← JuliaLean.base.div.divBitIntegerMixedMode x g .ToZero
  let qy ← JuliaLean.base.div.divBitIntegerMixedMode y g .ToZero
  let rx ← JuliaLean.base.int.convert t qx
  let ry ← JuliaLean.base.int.convert s qy
  pure (rx, ry)

/-- A concrete native complex quotient, needed by the preceding integer/complex
forwarder. Julia source: base/rational.jl:144-152. Four-argument promotion,
unsigned gcd intermediates and all checked operations use existing callees.
The older `complexIntegerQuotientMixedSource` remains unchanged. -/
-- Source: base/rational.jl:144-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function //(x::Complex{<:Integer}, y::Complex{<:Integer})
--     a, b, c, d = promote(reim(x)..., reim(y)...)
--     c_r, d_r = divgcd(c, d)
--     abs2y_r = checked_add(checked_mul(c, c_r), checked_mul(d, d_r))
--     complex(
--         checked_add(checked_mul(a, c_r), checked_mul(b, d_r)),
--         checked_add(checked_mul(b, c_r), checked_neg(checked_mul(a, d_r)))
--     )//abs2y_r
-- end
-- /Source
def complexIntegerQuotient {t s : IntTy}
    (x : JuliaLean.base.complex.Complex (JInt t))
    (y : JuliaLean.base.complex.Complex (JInt s)) :
    Jl (JuliaLean.base.complex.Complex
      (Rat (((t.promote t).promote s).promote s))) :=
  divideComplexIntegersSource
    (JuliaLean.base.complex.reim JuliaLean.base.complex.real_Complex
      JuliaLean.base.complex.imag_Complex)
    (JuliaLean.base.complex.reim JuliaLean.base.complex.real_Complex
      JuliaLean.base.complex.imag_Complex)
    JuliaLean.base.promotion.promoteFourBitIntegers
    divgcdMixed
    JuliaLean.base.checked.checkedMulBits JuliaLean.base.checked.checkedAddBits
    JuliaLean.base.checked.checkedNegBits
    (JuliaLean.base.complex.complexOfPromoted JuliaLean.base.intfuncs.promoteSamePair)
    (exactDivideComplexReal (exactDivideIntsSource rationalSameBitsSource)
      (JuliaLean.base.complex.complexOfPromoted JuliaLean.base.intfuncs.promoteSamePair)
      JuliaLean.base.complex.real_Complex JuliaLean.base.complex.imag_Complex) x y

/-- Integer/complex exact division, with the real-to-complex constructor closed
over the source integer zero and checked field conversions.
Julia source: base/rational.jl:141-143. -/
-- Source: base/rational.jl:141-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function //(x::Integer, y::Complex{<:Integer})
--     complex(x) // y
-- end
-- /Source
def integerComplexQuotient {t s : IntTy} (x : JInt t)
    (y : JuliaLean.base.complex.Complex (JInt s)) :
    Jl (JuliaLean.base.complex.Complex
      (Rat (((t.promote t).promote s).promote s))) := do
  let z ← JuliaLean.base.complex.complex_Real
    (fun v => pure (JuliaLean.base.int.zero v))
    (JuliaLean.base.complex.constructTypedComplex
      (JuliaLean.base.int.convert t) (JuliaLean.base.int.convert t)) x
  complexIntegerQuotient z y

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- Native integer components divided by a native integer scalar, including
different widths and signedness. Each scalar quotient dispatches through the
existing integer promotion and concrete rational constructor. The real quotient
is completed before evaluation of the imaginary quotient; the final complex
constructor uses the existing same-type promotion implementation.
Julia source: base/rational.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
The homogeneous proof-local Round4.cdiv remains unchanged. -/
-- Source: base/rational.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- //(x::Complex, y::Real) = complex(real(x)//y, imag(x)//y)
-- /Source
def complexIntegerScalarQuotient {t s : IntTy}
    (x : JuliaLean.base.complex.Complex (JInt t)) (y : JInt s) :
    Jl (JuliaLean.base.complex.Complex (Rat (t.promote s))) :=
  exactDivideComplexReal
    (exactDivideIntsSource
      (rationalPromoteSource (jintPromoteOps t s).promote rationalSameBitsSource))
    (JuliaLean.base.complex.complexOfPromoted JuliaLean.base.intfuncs.promoteSamePair)
    JuliaLean.base.complex.real_Complex JuliaLean.base.complex.imag_Complex x y

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean
/-- Concrete infinity predicate for native rationals. The generic Real method
uses the actual Number isnan method and Real isfinite method, whose decompose
call selects the rational numerator/exponent/denominator tuple. The final
comparison with native Int64 zero uses installed heterogeneous integer equality.
Julia source: base/float.jl:716-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:716-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinf(x::Real) = !isnan(x) & !isfinite(x)
-- /Source
def nativeRationalIsInfinite {t : IntTy} (x : Rat t) : Bool :=
  JuliaLean.base.float.isinf_Real JuliaLean.base.float.isnan_Number
    (JuliaLean.base.float.isfinite_Real decomposeSource
      (fun den zero => !(JuliaLean.base.int.eq den zero))) x

/-- Closed native rational unary-negation dispatch, needed by complex conjugation.
Signed numerator-typemin and unsigned nonzero errors retain their actual
source methods. This is a dependency binding, not a replacement of those methods.
Julia source: base/rational.jl:402-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:402-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Rational{T}) where T<:BitSigned
--     x.num == typemin(T) && __throw_rational_numerator_typemin(T)
--     unsafe_rational(-x.num, x.den)
-- end
-- @noinline __throw_rational_numerator_typemin(T) = throw(OverflowError(LazyString("rational numerator is typemin(", T, ")")))
-- 
-- function -(x::Rational{T}) where T<:Unsigned
--     x.num != zero(T) && __throw_negate_unsigned()
--     x
-- end
-- /Source
def nativeRationalNegation {t : IntTy} (x : Rat t) : Jl (Rat t) :=
  if h : t.signed = true then negBitSignedSource h x
  else negUnsignedSource (jintOps t).zero
    (fun a b => !(JuliaLean.base.int.eq a b)) x

/-- Homogeneous native rational addition dependency. Actual same-type promotion,
Real infinity detection, component equality, native divgcd, checked arithmetic
and the concrete normalizing constructor close every called operation.
The existing proof-local Round4.add is not imported into the model.
Julia source: base/rational.jl:415-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:415-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function +(x::Rational, y::Rational)
--     xp, _ = promote(x, y)::NTuple{2,Rational}
--     if isinf(x) && x == y
--         return xp
--     end
--     xd, yd = divgcd(promote(x.den, y.den)...)
--     Rational(checked_add(checked_mul(x.num, yd), checked_mul(y.num, xd)), checked_mul(x.den, yd))
-- end
-- /Source
def nativeRationalAddition {t : IntTy} (x y : Rat t) : Jl (Rat t) :=
  addRatSource (samePromoteOps (jintOps t))
    (fun a b => pure (JuliaLean.base.intfuncs.promoteSamePair a b))
    nativeRationalIsInfinite
    (eqRatSource JuliaLean.base.int.eq JuliaLean.base.int.eq)
    divgcdMixed rationalSameBitsSource x y

/-- Homogeneous native rational multiplication dependency. Cross-cancellation
and checked products use actual native callees; no mixed promotion field that
wraps before checking is used. Existing source bodies remain unchanged.
Julia source: base/rational.jl:482-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:482-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function *(x::Rational, y::Rational)
--     xn, yd = divgcd(promote(x.num, y.den)...)
--     xd, yn = divgcd(promote(x.den, y.num)...)
--     unsafe_rational(checked_mul(xn, yn), checked_mul(xd, yd))
-- end
-- /Source
def nativeRationalMultiplication {t : IntTy} (x y : Rat t) : Jl (Rat t) :=
  mulRatRatSource (samePromoteOps (jintOps t)) divgcdMixed x y

/-- Homogeneous native exact rational division dependency. Both numerator and
denominator cancellation, the signed-infinity numerator correction, and
ordered checked-denominator normalization are retained. This binding is also
needed by the native complex inverse used by integer exponentiation.
Julia source: base/rational.jl:106-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:106-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function //(x::Rational, y::Rational)
--     xn,yn = divgcd(promote(x.num, y.num)...)
--     xd,yd = divgcd(promote(x.den, y.den)...)
--     # See the comment in `//(::Rational, ::Integer)`.
--     if iszero(xd) && signbit(yn)
--         xn = checked_neg(xn)
--     end
--     checked_den(checked_mul(xn, yd), checked_mul(xd, yn))
-- end
-- /Source
def nativeRationalExactDivision {t : IntTy} (x y : Rat t) : Jl (Rat t) :=
  divRatRatSource (samePromoteOps (jintOps t)) divgcdMixed x y

/-- Concrete zero of a complex value with native rational fields. oftype converts
the Int64 literal zero through the real-to-typed-complex constructor, then
through the actual Rational integer constructor for each field. This closes
zero of the complex object; the separate scalar zero dependency is already
available as middleZeroNativeRational. Dependencies: base/complex.jl:42 and
base/rational.jl:193-195.
Julia source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- zero(x::Number) = oftype(x,0)
-- /Source
def nativeComplexRationalZero {t : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) :=
  let component := rationalIntAsSource (JInt t) (JuliaLean.base.int.convert t)
    (fun _ : JInt .i64 => (jintOps .i64).one)
  JuliaLean.base.number.zeroValue
    (fun (_ : JuliaLean.base.complex.Complex (Rat t)) literal =>
      JuliaLean.base.number.convertNumber
        (JuliaLean.base.complex.Complex_T_Real
          (JuliaLean.base.complex.constructTypedComplex component component))
        (JInt.lit .i64 literal)) z

/-- Concrete native-rational complex conjugation dependency. Imaginary-field
negation is evaluated before the source Complex constructor, whose homogeneous promotion uses the installed implementation.
Julia source: base/complex.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- conj(z::Complex) = Complex(real(z),-imag(z))
-- /Source
def nativeComplexRationalConjugate {t : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) :=
  JuliaLean.base.complex.conj_ComplexM nativeRationalNegation
    (JuliaLean.base.complex.Complex_Real_Real
      (fun a b => pure (JuliaLean.base.intfuncs.promoteSamePair a b))) z

/-- Concrete squared magnitude for native-rational complex values. The real
square completes first, then the imaginary square, then rational addition.
All finite/infinite values and every arithmetic failure retain this order.
Julia source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abs2(z::Complex) = real(z)*real(z) + imag(z)*imag(z)
-- /Source
def nativeComplexRationalAbs2 {t : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) : Jl (Rat t) :=
  JuliaLean.base.complex.abs2_ComplexM
    nativeRationalMultiplication nativeRationalAddition z

/-- Closed internal exact-inverse helper for Complex{Rational{JInt t}}. Both
infinity predicates are evaluated; the infinite branch conjugates an actually
constructed complex zero. The denominator is still computed from the original
input, after the selected conjugation completes, so finite companion-field
overflow and other errors are not erased by the infinite branch.
The bundled generic shell has no existing concrete rational-component closure.
Julia source: base/rational.jl:120-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:120-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _complex_exact_inv(y::Complex)
--     c, d = reim(y)
--     num = if (isinf(c) | isinf(d))
--         conj(zero(y))
--     else
--         conj(y)
--     end
--     num, abs2(y)
-- end
-- /Source
def complexRationalExactInverse {t : IntTy}
    (y : JuliaLean.base.complex.Complex (Rat t)) :
    Jl (JuliaLean.base.complex.Complex (Rat t) × Rat t) :=
  complexExactInvSource
    (JuliaLean.base.complex.reim JuliaLean.base.complex.real_Complex
      JuliaLean.base.complex.imag_Complex)
    nativeRationalIsInfinite nativeComplexRationalZero
    nativeComplexRationalConjugate nativeComplexRationalAbs2 y

/-- Native rational scalar divided exactly by a native-rational complex value.
The internal inverse is completed before scalar multiplication. Each product
promotes to t.promote s; the later componentwise exact division retains its
actual further promotion with the denominator's type s. Only the valid promote
and homogeneous checked-operation fields of jintPromoteOps are used here.
The real product precedes the imaginary product, then the real quotient precedes
the imaginary quotient. All errors propagate from their actual callees.
Julia source: base/rational.jl:137-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:137-140 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function //(x::Number, y::Complex)
--     num, den = _complex_exact_inv(y)
--     (x * num) // den
-- end
-- /Source
def rationalComplexQuotient {t s : IntTy} (x : Rat t)
    (y : JuliaLean.base.complex.Complex (Rat s)) :
    Jl (JuliaLean.base.complex.Complex (Rat ((t.promote s).promote s))) :=
  divideNumberComplexSource complexRationalExactInverse
    (JuliaLean.base.complex.mul_Real_ComplexM
      (mulRatRatSource (jintPromoteOps t s) divgcdMixed))
    (exactDivideComplexReal
      (divRatRatSource (jintPromoteOps (t.promote s) s) divgcdMixed)
      (JuliaLean.base.complex.complexOfPromoted JuliaLean.base.intfuncs.promoteSamePair)
      JuliaLean.base.complex.real_Complex JuliaLean.base.complex.imag_Complex) x y

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean JuliaLean.base.promotion

/-- Type metadata for the concrete built-in integer portion of the signatures at
`base/rational.jl:230-234`: `none` is `Bool`, and `some t` is the native integer `t`.
This only translates existing primitive type tags; it performs no numeric conversion.
Arbitrary user-defined Integer types and BigInt inputs are not represented by this domain. -/
-- Source: base/rational.jl:230-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:Integer} = Rational{promote_type(T,S)}
-- /Source
def primitiveIntegerType : Option IntTy → PType
  | none => primitivePType .bool
  | some t => primitivePType (.int t)

/-- The result type constructor used at `base/rational.jl:230-234`.
The Base module's Rational identity and its single component parameter are retained;
this is metadata for the existing PType representation, not a second Rational value model. -/
-- Source: base/rational.jl:9-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Rational{T<:Integer} <: Real
--     num::T
--     den::T
--
--     # Unexported inner constructor of Rational that bypasses all checks
--     global unsafe_rational(::Type{T}, num, den) where {T} = new{T}(num, den)
-- end
-- /Source
def rationalType (component : PType) : PType :=
  .data ⟨"Base", "Rational"⟩ "Rational" [component] (some pPromotionReal)

/-- `base/rational.jl:230`, on Bool and all ten native integer component types.
The callee is the existing recursive primitive `promote_type` dispatcher, including
both-direction promotion rules; `none` in the result has its existing divergence meaning. -/
-- Source: base/rational.jl:230-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:Integer} = Rational{promote_type(T,S)}
-- /Source
def promoteRuleRationalInteger (t s : Option IntTy) : Option PType :=
  promoteRuleRatIntSource
    (fun a b => primitivePromoteType (primitiveIntegerType a) (primitiveIntegerType b))
    (fun result => result.map rationalType) t s

/-- `base/rational.jl:231`, on Bool and all ten native integer component types.
The existing source method is closed over actual primitive promotion and PType construction. -/
-- Source: base/rational.jl:231-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Rational{T}}, ::Type{Rational{S}}) where {T<:Integer,S<:Integer} = Rational{promote_type(T,S)}
-- /Source
def promoteRuleRationalRational (t s : Option IntTy) : Option PType :=
  promoteRuleRatRatSource
    (fun a b => primitivePromoteType (primitiveIntegerType a) (primitiveIntegerType b))
    (fun result => result.map rationalType) t s

/-- `base/rational.jl:232`, on Bool/native-integer rational components and IEEE float types.
BigFloat and user-defined AbstractFloat promotion are outside this concrete domain. -/
-- Source: base/rational.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:AbstractFloat} = promote_type(T,S)
-- /Source
def promoteRuleRationalFloat (t : Option IntTy) (f : JuliaLean.base.float.FTy) : Option PType :=
  promoteRuleRatFloatSource
    (fun a b => primitivePromoteType (primitiveIntegerType a) (primitivePType (.float b))) t f

/-- The type-only 128-bit widening result needed by `base/rational.jl:234`.
`base/gmp.jl:298-299` returns the GMP module's BigInt type. This local metadata adapter
adds no BigInt values, arithmetic, allocation, or aliasing semantics. -/
-- Source: base/gmp.jl:298-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Int128})  = BigInt
-- widen(::Type{UInt128}) = BigInt
-- /Source
def bigIntegerType : PType :=
  .data ⟨"Base.GMP", "BigInt"⟩ "BigInt" [] (some pPromotionSigned)

/-- Concrete type-level `widen` dependency of `base/rational.jl:234`.
The eight native widths below 128 use the existing `base.int.widenType` calls;
the two 128-bit cases use their documented BigInt type result. Bool reaches the
existing `base.operators.widenTypeError` fallback and throws MethodError. -/
-- Source: base/int.jl:911-918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Int8}) = Int16
-- widen(::Type{Int16}) = Int32
-- widen(::Type{Int32}) = Int64
-- widen(::Type{Int64}) = Int128
-- widen(::Type{UInt8}) = UInt16
-- widen(::Type{UInt16}) = UInt32
-- widen(::Type{UInt32}) = UInt64
-- widen(::Type{UInt64}) = UInt128
-- /Source
-- Source: base/gmp.jl:298-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Int128})  = BigInt
-- widen(::Type{UInt128}) = BigInt
-- /Source
-- Source: base/operators.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(x::Type{T}) where {T} = throw(MethodError(widen, (T,)))
-- /Source
def widenIntegerType (t : Option IntTy) : Jl PType :=
  match t with
  | none => JuliaLean.base.operators.widenTypeError
      (fun _ : PType => .error (.methodError "widen")) (primitivePType .bool)
  | some t =>
      match JuliaLean.base.int.widenType t with
      | some w => .ok (primitivePType (.int w))
      | none => .ok bigIntegerType

/-- `base/rational.jl:234`, retaining the component widening failure before
constructing a Rational type and retaining BigInt for 128-bit components. -/
-- Source: base/rational.jl:234-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widen(::Type{Rational{T}}) where {T} = Rational{widen(T)}
-- /Source
def widenRational (t : Option IntTy) : Jl PType :=
  widenRatTypeSource widenIntegerType (fun result => result.map rationalType) t

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- Closed native integer callee required by `base/rational.jl:322-323`.
This is an adapter to the existing `base/rational.jl:335-342` model, not a
replacement implementation. Native comparisons retain the input and target
integer types. Its keyword payload is passed unchanged and ignored by that callee.
The target domain is all ten BitInteger types; Bool targets are not represented. -/
-- Source: base/rational.jl:335-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function rationalize(::Type{T}, x::Integer; kvs...) where {T<:Integer}
--     T<:Unsigned && x < 0 && __throw_negate_unsigned()
--     if Base.hastypemax(T) # BigInt doesn't
--         x < typemin(T) && return unsafe_rational(-one(T), zero(T))
--         x > typemax(T) && return unsafe_rational(one(T), zero(T))
--     end
--     return Rational{T}(x)
-- end
-- /Source
def rationalizeIntegerForComplex {s : IntTy} {K : Type} (t : IntTy)
    (x : JInt s) (kwargs : K) : Jl (Rat t) :=
  rationalizeIntegerTypedSource (JInt t) (jintOps t)
    (fun n => JuliaLean.base.int.lt n (JInt.lit .i64 0))
    (fun n => JuliaLean.base.int.lt n (JInt.typemin t))
    (fun n => JuliaLean.base.int.lt (JInt.typemax t) n)
    (JuliaLean.base.int.convert t) (fun _ => (jintOps s).one) x kwargs

/-- `base/rational.jl:322`, for Complex values with native integer components.
Real-component rationalization precedes imaginary-component rationalization;
the actual homogeneous Complex constructor is run only after both succeed.
The nested result only adapts the existing source template's pure constructor slot
to the existing fallible Complex constructor, without changing call order.
The typed target is fixed by `t`, so the source template receives a Unit token. -/
-- Source: base/rational.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(::Type{T}, x::Complex; kvs...) where {T<:Integer} = Complex(rationalize(T, x.re; kvs...), rationalize(T, x.im; kvs...))
-- /Source
def rationalizeComplexIntegersTyped {s : IntTy} {K : Type} (t : IntTy)
    (z : JuliaLean.base.complex.Complex (JInt s)) (kwargs : K) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) := do
  let construction ← rationalizeComplexTypedSource
    (fun (_ : Unit) (x : JInt s) kvs => rationalizeIntegerForComplex t x kvs)
    (fun re im => JuliaLean.base.complex.Complex_Real_Real promoteSamePair re im)
    () (⟨z.re, z.im⟩ : ComplexValue (JInt s)) kwargs
  construction

/-- `base/rational.jl:323`, for Complex values with native integer components.
Both components use Julia Int (Int64 on the bundled model's platform), including
the typed integer callee's saturation to rational infinity outside the Int64 range. -/
-- Source: base/rational.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Complex; kvs...) = Complex(rationalize(Int, x.re; kvs...), rationalize(Int, x.im; kvs...))
-- /Source
def rationalizeComplexIntegersDefault {s : IntTy} {K : Type}
    (z : JuliaLean.base.complex.Complex (JInt s)) (kwargs : K) :
    Jl (JuliaLean.base.complex.Complex (Rat .i64)) := do
  let construction ← rationalizeComplexDefaultSource
    (fun (_ : IntTy) (x : JInt s) kvs => rationalizeIntegerForComplex .i64 x kvs)
    (fun re im => JuliaLean.base.complex.Complex_Real_Real promoteSamePair re im)
    (⟨z.re, z.im⟩ : ComplexValue (JInt s)) kwargs
  construction

/-- The `one(x)` call required by the source334→source50 path.
`base/number.jl:405-406` invokes the actual native conversion of the Int literal 1.
The type tag is statically fixed by the JInt index, so its runtime token is Unit. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
def oneNativeInteger {t : IntTy} (x : JInt t) : Jl (JInt t) :=
  JuliaLean.base.number.oneValue (fun _ : JInt t => ())
    (fun _ => JuliaLean.base.number.oneType
      (fun (_ : Unit) n => JuliaLean.base.int.convert t (JInt.lit .i64 n)) ()) x

/-- Bool's `one(x)` dependency on the source334→source50 path, through the
existing `base/number.jl:405-406` and `base/bool.jl:170` definitions. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
-- Source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Bool(x::Real) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))
-- /Source
def oneBoolean (x : Bool) : Jl Bool :=
  JuliaLean.base.number.oneValue (fun _ : Bool => ())
    (fun _ => JuliaLean.base.number.oneType
      (fun (_ : Unit) n => JuliaLean.base.bool.boolFromReal
        (fun (a : JInt .i64) b => .ok (JuliaLean.base.int.eq a (JInt.lit .i64 b)))
        (JInt.lit .i64 n)) ()) x

/-- `base/rational.jl:334`, for every native integer width and every keyword payload.
The more-specific Integer method preserves the original component type. Its
source50 constructor evaluates the concrete `one` callee once before the pure
existing constructor template consumes that already-computed value. -/
-- Source: base/rational.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Integer; kvs...) = Rational(x)
-- /Source
def rationalizeIntegerKeywords {t : IntTy} {K : Type}
    (x : JInt t) (kwargs : K) : Jl (Rat t) :=
  rationalizeIntegerGeneric
    (fun n => do
      let d ← oneNativeInteger n
      pure (rationalFromIntegerGeneric unsafeRationalSameSource (fun _ => d) n)) x kwargs

/-- `base/rational.jl:334`, for Bool with arbitrary keyword payloads.
The ordinary Rational constructor returns Rational{Bool}; it does not first
promote Bool to Julia Int. The actual Bool conversion of one is used. -/
-- Source: base/rational.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Integer; kvs...) = Rational(x)
-- /Source
def rationalizeBooleanKeywords {K : Type}
    (x : Bool) (kwargs : K) : Jl (Rational Bool) :=
  rationalizeIntegerGeneric
    (fun n => do
      let d ← oneBoolean n
      pure (rationalFromIntegerGeneric unsafeRationalSameSource (fun _ => d) n)) x kwargs

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- Concrete `one` dependency for a complex value with native integer fields.
The static type token represents Complex{JInt t}. Converting the source Int64
literal one calls the existing real-to-typed-complex constructor, which supplies
the Int64 zero and converts the real field before the imaginary field.
Julia source: base/number.jl:405-406; base/complex.jl:42.
No caller supplies a numeric operation. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
def oneNativeComplexInteger {t : IntTy}
    (x : JuliaLean.base.complex.Complex (JInt t)) :
    Jl (JuliaLean.base.complex.Complex (JInt t)) :=
  JuliaLean.base.number.oneValue
    (fun _ : JuliaLean.base.complex.Complex (JInt t) => ())
    (fun _ => JuliaLean.base.number.oneType
      (fun (_ : Unit) literal =>
        JuliaLean.base.number.convertNumber
          (JuliaLean.base.complex.Complex_T_Real
            (JuliaLean.base.complex.constructTypedComplex
              (JuliaLean.base.int.convert t) (JuliaLean.base.int.convert t)))
          (JInt.lit .i64 literal)) ()) x

/-- Native integer denominator, retaining the input's component type.
The actual `one` call is evaluated once; the existing source template then
consumes that computed value. The concrete dependency oneNativeInteger was
introduced earlier for rationalize at base/rational.jl:334.
Julia source: base/rational.jl:383-383. -/
-- Source: base/rational.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- denominator(x::Union{Integer,Complex{<:Integer}}) = one(x)
-- /Source
def denominatorNativeInteger {t : IntTy} (x : JInt t) : Jl (JInt t) := do
  let result ← oneNativeInteger x
  pure (denominatorIntegerOrComplex (fun _ => result) x)

/-- Bool denominator, using the earlier concrete Bool `one` conversion.
The result retains Bool rather than promoting to a native integer.
Julia source: base/rational.jl:383-383. -/
-- Source: base/rational.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- denominator(x::Union{Integer,Complex{<:Integer}}) = one(x)
-- /Source
def denominatorBoolean (x : Bool) : Jl Bool := do
  let result ← oneBoolean x
  pure (denominatorIntegerOrComplex (fun _ => result) x)

/-- Native complex-integer denominator, with the concrete typed-complex
construction used by `one`. Both fields retain the original native component
type and all constructor calls occur before returning the source result.
Julia source: base/rational.jl:383-383. -/
-- Source: base/rational.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- denominator(x::Union{Integer,Complex{<:Integer}}) = one(x)
-- /Source
def denominatorNativeComplexInteger {t : IntTy}
    (x : JuliaLean.base.complex.Complex (JInt t)) :
    Jl (JuliaLean.base.complex.Complex (JInt t)) := do
  let result ← oneNativeComplexInteger x
  pure (denominatorIntegerOrComplex (fun _ => result) x)

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- The bottom target has no constructible rational values and rejects every positional/keyword tuple.
The shared error type records the exception class and function name; Julia's tuple payload is outside that existing error representation.
Julia source: base/rational.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(::Type{Union{}}, slurp...; kwargs...) = throw(MethodError(rationalize, (Union{}, slurp...)))
-- /Source
def rationalizeBottom {Args Kw Result : Type} (_slurp : Args) (_kwargs : Kw) : Jl Result :=
  .error (.methodError "rationalize")

/-- Concrete dependency adapter for promotion of an Int64 numerator and Bool denominator.
The result type is statically Int64 by base/bool.jl:6; conversion uses the installed
identity and Bool-to-Int64 methods in source argument order. The enclosing
`promote`/`not_sametype` calls are included at each use below.
Julia source: base/promotion.jl:397-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/promotion.jl:397-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _promote(x::T, y::S) where {T,S}
--     @inline
--     R = promote_type(T, S)
--     return (convert(R, x), convert(R, y))
-- end
-- /Source
def middlePromoteInt64Bool (n : JInt .i64) (d : Bool) :
    Jl (JInt .i64 × JInt .i64) :=
  JuliaLean.base.promotion.promoteTwoValues
    (JuliaLean.base.promotion.promotePairValues
      (fun (_ : JInt .i64) (_ : Bool) =>
        pure (JuliaLean.base.promotion.primitivePType (.int .i64)))
      (fun _ a => pure (JuliaLean.base.number.convertSame a))
      (fun _ b => pure (JuliaLean.base.int.ofBool .i64 b)))
    (fun before after => JuliaLean.base.promotion.notSameTypeDifferent before after) n d

/-- The Bool-component case of unary rational plus.
The installed Bool unary plus returns Int64 (base/bool.jl:140), so the
denominator is promoted before constructing the result. No normalization is introduced.
Julia source: base/rational.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Rational) = unsafe_rational(+x.num, x.den)
-- /Source
def unaryPlusBoolRational (x : Rational Bool) : Jl (Rat .i64) :=
  unsafeRationalPromoteSource middlePromoteInt64Bool
    (JuliaLean.base.bool.posBool x.num) x.den

/-- The Bool-component case of generic unary rational minus.
Bool selects the generic Rational method, then -Bool returns Int64
(base/bool.jl:142). Promotion retains the original Boolean denominator
as an Int64 component.
Julia source: base/rational.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::Rational) = unsafe_rational(-x.num, x.den)
-- /Source
def unaryMinusBoolRational (x : Rational Bool) : Jl (Rat .i64) :=
  unsafeRationalPromoteSource middlePromoteInt64Bool
    (JuliaLean.base.bool.negBool x.num) x.den

/-- The Bool-component case of wrapping rational negation.
The installed Bool -% method returns Int64 (base/bool.jl:143); the
unsafe constructor therefore promotes the denominator to Int64.
Julia source: base/rational.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(x::Rational) = unsafe_rational(-%(x.num), x.den)
-- /Source
def wrappingMinusBoolRational (x : Rational Bool) : Jl (Rat .i64) :=
  unsafeRationalPromoteSource middlePromoteInt64Bool
    (JuliaLean.base.bool.negWrapBool x.num) x.den

/-- Concrete dependency instance of zero on a rational with native integer components.
The literal supplied by zeroValue is the Julia Int64 literal zero. Converting it
to the rational type invokes the installed integer constructor, including both
component conversions. The Int argument of zeroValue represents its fixed source
literal only; no unbounded arithmetic replaces a machine operation.
Julia source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- zero(x::Number) = oftype(x,0)
-- /Source
def middleZeroNativeRational {t : IntTy} (x : Rat t) : Jl (Rat t) :=
  JuliaLean.base.number.zeroValue
    (fun (_ : Rat t) literal =>
      JuliaLean.base.number.convertNumber
        (rationalIntAsSource (JInt t) (JuliaLean.base.int.convert t)
          (fun (_ : JInt .i64) => (jintOps .i64).one))
        (JInt.lit .i64 literal)) x

/-- Concrete dependency instance of copysign for native rational arguments.
The installed number.copysign eagerly evaluates ordinary negation and unary plus
before ifelse, including unsigned negation errors. The caller passes an actual
constructed zero, but this adapter preserves the complete native behavior.
Julia source: base/number.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/number.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copysign(x::Real, y::Real) = ifelse(signbit(x)!=signbit(y), -x, +x)
-- /Source
def middleCopysignNativeRational {t : IntTy} (x y : Rat t) : Jl (Rat t) :=
  JuliaLean.base.number.copysign
    (fun q => pure (signbitRatSource JuliaLean.base.int.signbit q))
    (fun q => pure (signbitRatSource JuliaLean.base.int.signbit q))
    (if h : t.signed = true then negBitSignedSource h
     else negUnsignedSource (jintOps t).zero
       (fun a b => !(JuliaLean.base.int.eq a b)))
    (fun q => pure (unaryPlusRatSource JuliaLean.base.operators.unaryPlusNumber q))
    JuliaLean.base.int.ifelse x y

/-- Concrete dependency instance of Bool construction on Int64.
Both literal comparisons use the installed native heterogeneous equality
method; errors retain the existing Bool InexactError class and function name.
Julia source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Bool(x::Real) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))
-- /Source
def middleBoolFromInt64 (x : JInt .i64) : Jl Bool :=
  JuliaLean.base.bool.boolFromReal
    (fun n literal => pure (JuliaLean.base.int.eq n (JInt.lit .i64 literal))) x

/-- Concrete dependency instance of zero on Rational Bool.
As in the native case, converting the Int64 zero calls the actual rational
integer constructor, here with Bool component conversion.
Julia source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/number.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- zero(x::Number) = oftype(x,0)
-- /Source
def middleZeroBoolRational (x : Rational Bool) : Jl (Rational Bool) :=
  JuliaLean.base.number.zeroValue
    (fun (_ : Rational Bool) literal =>
      JuliaLean.base.number.convertNumber
        (rationalIntAsSource Bool middleBoolFromInt64
          (fun (_ : JInt .i64) => (jintOps .i64).one))
        (JInt.lit .i64 literal)) x

/-- Concrete dependency instance of copysign for Bool-component rationals.
Both unary operations produce Rational Int64, and both execute before ifelse.
The separate result type preserves Julia's Bool arithmetic promotion.
Julia source: base/number.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/number.jl:271-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copysign(x::Real, y::Real) = ifelse(signbit(x)!=signbit(y), -x, +x)
-- /Source
def middleCopysignBoolRational (x y : Rational Bool) : Jl (Rat .i64) :=
  JuliaLean.base.number.copysign
    (fun q => pure (signbitRatSource JuliaLean.base.bool.signbitBool q))
    (fun q => pure (signbitRatSource JuliaLean.base.bool.signbitBool q))
    unaryMinusBoolRational unaryPlusBoolRational
    JuliaLean.base.int.ifelse x y

/-- Bool strong-zero multiplication for all ten native rational component types.
The installed source body evaluates zero and copysign even when the Bool is true.
The annotated promote_type(Bool,Rational{t}) result is the same rational type,
so its final conversion uses convertSame. No numeric callbacks are supplied by callers.
Julia source: base/rational.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function *(x::Bool, y::T)::promote_type(Bool,T) where T<:Rational
--     return ifelse(x, y, copysign(zero(y), y))
-- end
-- /Source
def boolTimesNativeRational {t : IntTy} (x : Bool) (y : Rat t) : Jl (Rat t) := do
  let result ← boolMulRatSource JuliaLean.base.int.ifelse
    middleZeroNativeRational middleCopysignNativeRational x y
  pure (JuliaLean.base.number.convertSame result)

/-- Bool strong-zero multiplication for Rational Bool.
The copysign result has Rational Int64 components, while the true arm retains
Rational Bool. A sum records the runtime type selected by eager ifelse. The
annotated return conversion is applied after selection, converting each Int64
component to Bool on the false branch; the true branch selects convert identity.
Julia source: base/rational.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function *(x::Bool, y::T)::promote_type(Bool,T) where T<:Rational
--     return ifelse(x, y, copysign(zero(y), y))
-- end
-- /Source
def boolTimesBoolRational (x : Bool) (y : Rational Bool) : Jl (Rational Bool) := do
  let zero ← middleZeroBoolRational y
  let signedZero ← middleCopysignBoolRational zero y
  let result : Sum (Rational Bool) (Rat .i64) :=
    JuliaLean.base.int.ifelse x (.inl y) (.inr signedZero)
  match result with
  | .inl same => pure (JuliaLean.base.number.convertSame same)
  | .inr changed =>
      JuliaLean.base.number.convertNumber
        (convertRatSource Bool
          (fun n => JuliaLean.base.number.convertNumber middleBoolFromInt64 n)) changed

/-- Native rational right multiplication by Bool uses the concrete strong-zero method.
Julia source: base/rational.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(y::Rational, x::Bool) = x * y
-- /Source
def nativeRationalTimesBool {t : IntTy} (y : Rat t) (x : Bool) : Jl (Rat t) :=
  mulRatBoolSource boolTimesNativeRational y x

/-- Bool-component rational right multiplication by Bool uses the concrete strong-zero method.
Julia source: base/rational.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(y::Rational, x::Bool) = x * y
-- /Source
def boolRationalTimesBool (y : Rational Bool) (x : Bool) : Jl (Rational Bool) :=
  mulRatBoolSource boolTimesBoolRational y x

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- Concrete same-signedness native remainder callee. Native promotion only widens
within one signedness family, then remSame selects the actual width-specific
intrinsic. This helper is called only with same-sign types, including the
unsigned arguments constructed by the mixed signed/unsigned source methods.
Julia source: base/promotion.jl:520-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/promotion.jl:520-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::Real, y::Real) = rem(promote(x,y)...)
-- /Source
def remainderSameSign {a b : IntTy} (x : JInt a) (y : JInt b) :
    Jl (JInt (a.promote b)) := do
  let (px, py) := JuliaLean.base.int.promoteSameSign x y
  JuliaLean.base.int.remSame px py

/-- Return-type calculation for the native rem dispatcher, not an arithmetic
model. Same-sign operands promote as in base/promotion.jl:520; mixed operands
retain the signedness selected by these two source methods.
Julia source: base/int.jl:278-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/int.jl:278-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::BitSigned, y::Unsigned) = flipsign(signed(rem(unsigned(abs(x)), y)), x)
-- rem(x::Unsigned, y::BitSigned) = rem(x, unsigned(abs(y)))
-- /Source
def remainderRemResultTy (a b : IntTy) : IntTy :=
  if a.signed == b.signed then a.promote b
  else if a.signed then (a.toUnsigned.promote b).toSigned
  else a.promote b.toUnsigned

/-- Concrete heterogeneous remainder dispatch over all ten native integer types.
The two mixed cases call the installed source methods, whose only numerical
callback is closed over remainderSameSign. In particular a negative signed
dividend is not converted to the unsigned divisor type before remainder.
The same-sign branch uses the actual primitive remainder after widening.
Julia source: base/int.jl:278-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/int.jl:278-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rem(x::BitSigned, y::Unsigned) = flipsign(signed(rem(unsigned(abs(x)), y)), x)
-- rem(x::Unsigned, y::BitSigned) = rem(x, unsigned(abs(y)))
-- /Source
def remainderRemNative {a b : IntTy} (x : JInt a) (y : JInt b) :
    Jl (JInt (remainderRemResultTy a b)) :=
  let rec dispatch (sameSign signedLeft : Bool) :
      Jl (JInt (if sameSign then a.promote b
        else if signedLeft then (a.toUnsigned.promote b).toSigned
        else a.promote b.toUnsigned)) :=
    match sameSign, signedLeft with
    | true, _ => remainderSameSign x y
    | false, true => JuliaLean.base.int.rem_BitSigned_Unsigned remainderSameSign x y
    | false, false => JuliaLean.base.int.rem_Unsigned_BitSigned remainderSameSign x y
  dispatch (a.signed == b.signed) a.signed

/-- Return-type calculation for the native mod dispatcher. In the mixed cases,
the signed/unsigned conversions and unchecked additions determine a type
which need not be promote_type of the original operands.
Julia source: base/int.jl:342-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/int.jl:342-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function mod(x::BitSigned, y::Unsigned)
--     remval = rem(x, y) # correct iff  remval>=0
--     # the addition re-wraps the negative remainder into the unsigned domain
--     return unsigned(remval +% (remval<zero(remval))*y)
-- end
-- function mod(x::Unsigned, y::Signed)
--     remval =  signed(rem(x, y)) #remval>0 so correct iff y>0 or remval==0
--     return remval + (!iszero(remval) && y<zero(y))*y
-- end
-- mod(x::T, y::T) where {T<:Unsigned} = rem(x, y)
-- /Source
def remainderModResultTy (a b : IntTy) : IntTy :=
  if a.signed == b.signed then a.promote b
  else if a.signed then ((a.toUnsigned.promote b).toSigned.promote b).toUnsigned
  else (a.promote b.toUnsigned).toSigned.promote b

/-- Concrete heterogeneous modulo dispatch. All three installed base.div
entry points already supply the native rem and fld callees; no operation
is accepted from this adapter's caller. The return type follows the
actual source result instead of silently converting to the input promotion type.
Same-sign mod is the native fallback at base/int.jl:335-341 or :351.
Julia source: base/int.jl:342-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/int.jl:342-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function mod(x::BitSigned, y::Unsigned)
--     remval = rem(x, y) # correct iff  remval>=0
--     # the addition re-wraps the negative remainder into the unsigned domain
--     return unsigned(remval +% (remval<zero(remval))*y)
-- end
-- function mod(x::Unsigned, y::Signed)
--     remval =  signed(rem(x, y)) #remval>0 so correct iff y>0 or remval==0
--     return remval + (!iszero(remval) && y<zero(y))*y
-- end
-- mod(x::T, y::T) where {T<:Unsigned} = rem(x, y)
-- /Source
def remainderModNative {a b : IntTy} (x : JInt a) (y : JInt b) :
    Jl (JInt (remainderModResultTy a b)) :=
  let rec dispatch (sameSign signedLeft : Bool) :
      Jl (JInt (if sameSign then a.promote b
        else if signedLeft then ((a.toUnsigned.promote b).toSigned.promote b).toUnsigned
        else (a.promote b.toUnsigned).toSigned.promote b)) :=
    match sameSign, signedLeft with
    | true, _ => JuliaLean.base.div.modMixedSameSign x y
    | false, true => JuliaLean.base.div.modMixedSignedUnsigned x y
    | false, false => JuliaLean.base.div.modMixedUnsignedSigned x y
  dispatch (a.signed == b.signed) a.signed

/-- The rem member of the generated Rational/Integer loop, on all native
component types. The checked denominator product is formed first. The
heterogeneous remainder retains its actual signedness, and only then does
unsafe_rational promote it with the original denominator. The other
generated members remain separate methods; the native + and - instances
already exist in the frozen Round21 declarations.
Julia source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub), (:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(x::Rational, y::Integer)
--             unsafe_rational(($chop)(x.num, checked_mul(x.den, y)), x.den)
--         end
--     end
-- end
-- /Source
def rationalRemIntegerNative {t s : IntTy} (x : Rat t) (y : JInt s) :
    Jl (Rat ((remainderRemResultTy t (t.promote s)).promote t)) := do
  let product ← JuliaLean.base.checked.checkedMulMixedBits x.den y
  let numerator ← remainderRemNative x.num product
  unsafeRationalPromoteSource JuliaLean.base.checked.promoteBits numerator x.den

/-- The mod member of the generated Rational/Integer loop. The whole generating
loop is retained for source identity. Native heterogeneous modulo is applied
before promoting the result with the original denominator; no normalization
is added to this unsafe constructor path.
Julia source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub), (:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(x::Rational, y::Integer)
--             unsafe_rational(($chop)(x.num, checked_mul(x.den, y)), x.den)
--         end
--     end
-- end
-- /Source
def rationalModIntegerNative {t s : IntTy} (x : Rat t) (y : JInt s) :
    Jl (Rat ((remainderModResultTy t (t.promote s)).promote t)) := do
  let product ← JuliaLean.base.checked.checkedMulMixedBits x.den y
  let numerator ← remainderModNative x.num product
  unsafeRationalPromoteSource JuliaLean.base.checked.promoteBits numerator x.den

/-- The rem member of the generated Integer/Rational loop, on every native
type pair. This path calls the normalizing Rational constructor after
heterogeneous remainder, unlike the Rational/Integer unsafe constructor.
All source-ordered promotion, overflow and zero-division errors propagate.
Julia source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             Rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
def integerRemRationalNative {t s : IntTy} (y : JInt s) (x : Rat t) :
    Jl (Rat ((remainderRemResultTy (t.promote s) t).promote t)) := do
  let product ← JuliaLean.base.checked.checkedMulMixedBits x.den y
  let numerator ← remainderRemNative product x.num
  rationalPromoteSource JuliaLean.base.checked.promoteBits
    rationalSameBitsSource numerator x.den

/-- The mod member of the generated Integer/Rational loop. The actual modulo
result type is retained through its promotion with the denominator and
the normalizing Rational constructor. In particular the modulo result
can be signed even when the preceding checked product is unsigned.
Julia source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
-- Source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             Rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
def integerModRationalNative {t s : IntTy} (y : JInt s) (x : Rat t) :
    Jl (Rat ((remainderModResultTy (t.promote s) t).promote t)) := do
  let product ← JuliaLean.base.checked.checkedMulMixedBits x.den y
  let numerator ← remainderModNative product x.num
  rationalPromoteSource JuliaLean.base.checked.promoteBits
    rationalSameBitsSource numerator x.den

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- Native integer-component complex equality with a rational, closing
`isreal`, `real`, and both native integer equality calls. Both Boolean
operands are evaluated by the installed eager `bwand` source model.
Julia source: base/rational.jl:583. -/
-- Source: base/rational.jl:583-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(z::Complex , x::Rational) = isreal(z) & (real(z) == x)
-- /Source
def eqNativeComplexRational {t s : IntTy}
    (z : JuliaLean.base.complex.Complex (JInt t)) (x : Rat s) : Bool :=
  eqComplexRatSource
    (JuliaLean.base.complex.isreal_Complex (jintOps t).iszero)
    JuliaLean.base.complex.real_Complex
    (eqIntRatSource
      (fun d => JuliaLean.base.int.eq d (JInt.lit .i64 1))
      JuliaLean.base.int.eq)
    z x

/-- The reverse ambiguity-resolving equality method keeps the source's
complex-first component comparison and eager Boolean conjunction.
Julia source: base/rational.jl:584. -/
-- Source: base/rational.jl:584-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::Rational, z::Complex ) = isreal(z) & (real(z) == x)
-- /Source
def eqRationalNativeComplex {t s : IntTy}
    (x : Rat s) (z : JuliaLean.base.complex.Complex (JInt t)) : Bool :=
  eqRatComplexSource
    (JuliaLean.base.complex.isreal_Complex (jintOps t).iszero)
    JuliaLean.base.complex.real_Complex
    (eqIntRatSource
      (fun d => JuliaLean.base.int.eq d (JInt.lit .i64 1))
      JuliaLean.base.int.eq)
    x z

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean JuliaLean.base.rational

/-!
Concrete native rounded rational division. `divgcdMixed` is the earlier,
source-backed helper from this group. Every callee here is an existing
implementation, and the result types retain Julia's mixed integer dispatch.
These definitions cover all ten native BitInteger types, all seven rounding
modes, finite values and rational infinities. They do not model BigInt, Bool,
or user-defined Integer extensions.
-/

/-- Native `div(::Rational, ::Integer, ::RoundingMode)`. The gcd quotient
pair retains the two original component types; only the checked denominator
product promotes. The final division keeps its actual mixed-signedness type.
Julia source: base/rational.jl:586-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:586-589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function div(x::Rational, y::Integer, r::RoundingMode)
--     xn,yn = divgcd(x.num,y)
--     div(xn, checked_mul(x.den,yn), r)
-- end
-- /Source
def roundedRatInteger {t s : IntTy} (x : Rat t) (y : JInt s)
    (r : Rounding) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy t (t.promote s))) := do
  let (xn, yn) ← divgcdMixed x.num y
  let d ← JuliaLean.base.checked.checkedMulMixedBits x.den yn
  JuliaLean.base.div.divBitIntegerMixedMode xn d (sourceRoundingMode r)

/-- Native `div(::Integer, ::Rational, ::RoundingMode)`. The checked
numerator product precedes the final mixed integer division.
Julia source: base/rational.jl:590-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:590-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function div(x::Integer, y::Rational, r::RoundingMode)
--     xn,yn = divgcd(x,y.num)
--     div(checked_mul(xn,y.den), yn, r)
-- end
-- /Source
def roundedIntegerRat {t s : IntTy} (x : JInt t) (y : Rat s)
    (r : Rounding) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy (t.promote s) s)) := do
  let (xn, yn) ← divgcdMixed x y.num
  let n ← JuliaLean.base.checked.checkedMulMixedBits xn y.den
  JuliaLean.base.div.divBitIntegerMixedMode n yn (sourceRoundingMode r)

/-- Closed native binding of `div(::Rational, ::Rational, ::RoundingMode)`.
The generic source body already exists as `divRationalRationalRoundedSource`;
its frozen concrete proof-local instance cannot be imported by the model.
This binding uses that existing body and actual native callees.
Julia source: base/rational.jl:594-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:594-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function div(x::Rational, y::Rational, r::RoundingMode)
--     xn,yn = divgcd(x.num,y.num)
--     xd,yd = divgcd(x.den,y.den)
--     div(checked_mul(xn,yd), checked_mul(xd,yn), r)
-- end
-- /Source
def roundedRatRat {t s : IntTy} (x : Rat t) (y : Rat s)
    (r : Rounding) : Jl (JInt (t.promote s)) :=
  divRationalRationalRoundedSource divgcdMixed divgcdMixed
    JuliaLean.base.checked.checkedMulMixedBits
    JuliaLean.base.checked.checkedMulMixedBits
    (fun n d mode => JuliaLean.base.div.divBitIntegerMode n d (sourceRoundingMode mode))
    x y r

/-- Native same-component compatibility overload. The source `invoke`
selects the generic Rational/Rational method above; it does not redispatch
through this same-component overload. The native result type `t.promote t`
is the same Julia integer type as `t`.
Julia source: base/rational.jl:602-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:602-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- div(x::T, y::T, r::RoundingMode) where {T<:Rational} =
--     invoke(div, Tuple{Rational, Rational, RoundingMode}, x, y, r)
-- /Source
def roundedSameRat {t : IntTy} (x y : Rat t) (r : Rounding) :
    Jl (JInt (t.promote t)) :=
  roundedRatRat x y r

/-- Native generated `div` forwarding for the `RatInteger` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultDivRatInteger {t s : IntTy} (x : Rat t) (y : JInt s) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy t (t.promote s))) :=
  roundedRatInteger x y .toZero

/-- Native generated `div` forwarding for the `IntegerRat` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultDivIntegerRat {t s : IntTy} (x : JInt t) (y : Rat s) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy (t.promote s) s)) :=
  roundedIntegerRat x y .toZero

/-- Native generated `div` forwarding for the `RatRat` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultDivRatRat {t s : IntTy} (x : Rat t) (y : Rat s) :
    Jl (JInt (t.promote s)) :=
  roundedRatRat x y .toZero

/-- Native generated `fld` forwarding for the `RatInteger` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultFldRatInteger {t s : IntTy} (x : Rat t) (y : JInt s) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy t (t.promote s))) :=
  roundedRatInteger x y .down

/-- Native generated `fld` forwarding for the `IntegerRat` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultFldIntegerRat {t s : IntTy} (x : JInt t) (y : Rat s) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy (t.promote s) s)) :=
  roundedIntegerRat x y .down

/-- Native generated `fld` forwarding for the `RatRat` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultFldRatRat {t s : IntTy} (x : Rat t) (y : Rat s) :
    Jl (JInt (t.promote s)) :=
  roundedRatRat x y .down

/-- Native generated `cld` forwarding for the `RatInteger` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultCldRatInteger {t s : IntTy} (x : Rat t) (y : JInt s) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy t (t.promote s))) :=
  roundedRatInteger x y .up

/-- Native generated `cld` forwarding for the `IntegerRat` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultCldIntegerRat {t s : IntTy} (x : JInt t) (y : Rat s) :
    Jl (JInt (JuliaLean.base.div.divMixedResultTy (t.promote s) s)) :=
  roundedIntegerRat x y .up

/-- Native generated `cld` forwarding for the `RatRat` pair.
The complete generator context is retained; only the indicated specialization
is bound by this declaration.
Julia source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:604-610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (S, T) in ((Rational, Integer), (Integer, Rational), (Rational, Rational))
--     @eval begin
--         div(x::$S, y::$T) = div(x, y, RoundToZero)
--         fld(x::$S, y::$T) = div(x, y, RoundDown)
--         cld(x::$S, y::$T) = div(x, y, RoundUp)
--     end
-- end
-- /Source
def defaultCldRatRat {t s : IntTy} (x : Rat t) (y : Rat s) :
    Jl (JInt (t.promote s)) :=
  roundedRatRat x y .up

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean JuliaLean.base.rational

/-!
Closed native bindings for the remaining assigned methods. The only native
values are existing `JInt` values, existing rational and complex structures,
and existing IEEE floating values. These bindings provide no caller-supplied
operations. Integer and user extension families outside the bundled native
representations remain explicitly outside this partial completion.
-/

/-- Concrete native Rational-to-IEEE dispatch needed by the infinity branch
of `round`. Each branch calls the existing source model, including the
Float16/Float32 specializations for wide integer components. This is a closed
dispatch adapter; the conversion algorithms are reused.
Julia source: base/rational.jl:205-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:205-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (::Type{T})(x::Rational{S}) where T<:AbstractFloat where S
--     P = promote_type(T,S)
--     convert(T, convert(P,x.num)/convert(P,x.den))::T
-- end
--  # avoid spurious overflow (#52394).  (Needed for UInt16 or larger;
--  # we also include Int16 for consistency of accuracy.)
-- Float16(x::Rational{<:Union{Int16,Int32,Int64,UInt16,UInt32,UInt64}}) =
--     Float16(Float32(x))
-- Float16(x::Rational{<:Union{Int128,UInt128}}) =
--     Float16(Float64(x)) # UInt128 overflows Float32, include Int128 for consistency
-- Float32(x::Rational{<:Union{Int128,UInt128}}) =
--     Float32(Float64(x)) # UInt128 overflows Float32, include Int128 for consistency
-- /Source
def remainingToIEEE {t : IntTy} :
    (f : JuliaLean.base.float.FTy) → Rat t → JuliaLean.base.float.FV f
  | .f16, q =>
      if h : isSmallFloat16RatComponent t = true then float16OfRationalSmallSource h q
      else if h : is128RatComponent t = true then float16OfRational128Source h q
      else floatConvertRatSource (JuliaLean.base.float.FV .f16)
        (JuliaLean.base.float.floatOfInt .f16) JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.convertFloat .f16) q
  | .f32, q =>
      if h : is128RatComponent t = true then float32OfRational128Source h q
      else floatConvertRatSource (JuliaLean.base.float.FV .f32)
        (JuliaLean.base.float.floatOfInt .f32) JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.convertFloat .f32) q
  | .f64, q =>
      floatConvertRatSource (JuliaLean.base.float.FV .f64)
        (JuliaLean.base.float.floatOfInt .f64) JuliaLean.base.float.div_IEEEFloat
        (JuliaLean.base.float.convertFloat .f64) q

/-- Concrete native Rational target of typed `round`, including infinities.
This target binding is also the dependency of the source-612 default-return
method below. Existing integer-target `roundBitsSource` remains unchanged.
`copysignRatBitInt` preserves the eager source evaluation of unary negation.
Julia source: base/rational.jl:614-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:614-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(::Type{T}, x::Rational{Tr}, r::RoundingMode=RoundNearest) where {T,Tr}
--     if iszero(denominator(x)) && !(T <: Integer)
--         return convert(T, copysign(unsafe_rational(one(Tr), zero(Tr)), numerator(x)))
--     end
--     convert(T, div(numerator(x), denominator(x), r))
-- end
-- /Source
def roundNativeRational {s : IntTy} (target : IntTy) (x : Rat s)
    (mode : Rounding := .nearest) : Jl (Rat target) :=
  roundRatTypedSource (Rat target) (jintOps s).iszero false
    (jintOps s).one (jintOps s).zero copysignRatBitInt
    (convertRatSource (JInt target) (JuliaLean.base.int.convert target))
    (fun a b r => JuliaLean.base.div.divBitIntegerMode a b (sourceRoundingMode r))
    (rationalIntAsSource (JInt target) (JuliaLean.base.int.convert target)
      (fun _ : JInt s => JInt.lit s 1)) x mode

/-- Native same-type default return of rational `round`. The type tag is
`Unit` because the Lean component type is statically fixed; the selected
callee is the concrete native Rational target, not a callback boundary.
Julia source: base/rational.jl:612-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:612-612 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- round(x::Rational, r::RoundingMode=RoundNearest) = round(typeof(x), x, r)
-- /Source
def roundNativeDefault {t : IntTy} (x : Rat t)
    (mode : Rounding := .nearest) : Jl (Rat t) :=
  roundRatDefaultSource (fun _ : Rat t => ())
    (fun _ q r => roundNativeRational t q r) x mode

/-- Typed rational `round` to each represented IEEE target. Both the
finite integer quotient conversion and the signed-infinity conversion use
the existing concrete native implementations. No finite-only precondition
removes the infinity/error branch.
Julia source: base/rational.jl:614-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:614-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function round(::Type{T}, x::Rational{Tr}, r::RoundingMode=RoundNearest) where {T,Tr}
--     if iszero(denominator(x)) && !(T <: Integer)
--         return convert(T, copysign(unsafe_rational(one(Tr), zero(Tr)), numerator(x)))
--     end
--     convert(T, div(numerator(x), denominator(x), r))
-- end
-- /Source
def roundNativeIEEE {s : IntTy} (target : JuliaLean.base.float.FTy)
    (x : Rat s) (mode : Rounding := .nearest) : Jl (JuliaLean.base.float.FV target) :=
  roundRatTypedSource (JuliaLean.base.float.FV target) (jintOps s).iszero false
    (jintOps s).one (jintOps s).zero copysignRatBitInt
    (fun q => .ok (remainingToIEEE target q))
    (fun a b r => JuliaLean.base.div.divBitIntegerMode a b (sourceRoundingMode r))
    (fun n => .ok (JuliaLean.base.float.floatOfInt target n)) x mode

/-- The actual `one(x)` dispatch for a native rational, needed by
`power_by_squaring`. It calls the existing value/type dispatch and native
rational integer constructor, rather than assuming the answer is a supplied
constant. The literal at this Julia call site is native `Int64`.
Julia source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
def remainingOneRatRun (t : IntTy) (x : Rat t) : Jl (Rat t) :=
  JuliaLean.base.number.oneValue (fun _ : Rat t => ())
    (fun _ => JuliaLean.base.number.oneType
      (fun (_ : Unit) n => rationalIntAsSource (JInt t) (JuliaLean.base.int.convert t)
        (fun _ : JInt .i64 => JInt.lit .i64 1) (JInt.lit .i64 n)) ()) x

/-- Pure interface adapter required by the existing `powerBySquaring`
model. The internal proof only eliminates the impossible error constructor
for converting the literal one to any of the ten native integer types; it
does not establish any public numerical property. The returned value is
obtained from the actual `one(x)` call above.
Julia source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
def remainingOneRat (t : IntTy) (x : Rat t) : Rat t :=
  JuliaLean.base.int.okOf (remainingOneRatRun t x)
    (by intro e h; cases t <;> cases h)

/-- Concrete native integer exponentiation for a rational. Both signs
of the exponent are covered. Reciprocal evaluation precedes wrapped exponent
negation; the existing `powerBySquaring` retains its eager initial `x*x`,
including errors even when the exponent is zero or one. All arithmetic and
error callees are actual bundled implementations.
Julia source: base/rational.jl:628-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:628-630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ^(x::Rational, n::Integer)
--     n >= 0 ? power_by_squaring(x,n) : power_by_squaring(inv(x),-n)
-- end
-- /Source
def powerNativeRational {t s : IntTy} (x : Rat t) (n : JInt s) : Jl (Rat t) :=
  let ops : RatIntOps (JInt t) :=
    { jintOps t with
      checkedNeg := JuliaLean.base.checked.checkedNegBits
      checkedAbs := JuliaLean.base.checked.checkedAbsBits
      checkedAdd := JuliaLean.base.checked.checkedAddBits
      checkedSub := JuliaLean.base.checked.checkedSubBits
      checkedMul := JuliaLean.base.checked.checkedMulBits }
  let mul := mulRatRatSource (samePromoteOps ops) divgcdMixed
  let neg : Rat t → Jl (Rat t) :=
    if h : t.signed = true then negBitSignedSource h
    else negUnsignedSource (JInt.lit t 0)
      (fun a b => !(JuliaLean.base.int.eq a b))
  powRationalIntegerGeneric
    (fun k => JuliaLean.base.int.le (JInt.lit .i64 0) k)
    JuliaLean.base.int.neg (invRatSource ops)
    (fun q k => JuliaLean.base.intfuncs.powerBySquaring
      (JuliaLean.base.intfuncs.bitsOps s)
      mul true
      (fun q => .ok (JuliaLean.base.number.convertSame q))
      (fun q => .ok (JuliaLean.base.number.convertSame q))
      (fun q => .ok (JuliaLean.base.number.convertSame q))
      JuliaLean.base.number.copy (remainingOneRat t) neg
      (isOneRationalSource ops.isone) mul true q k
      JuliaLean.base.intfuncs.throwPowerDomain_Any) x n

/-- Concrete `one(z)` for a complex number with native rational
components. The source `convert(T,1)` calls the actual Complex-from-Real
constructor, then converts real and imaginary fields in that order.
Dependencies: base/complex.jl:42 and base/rational.jl:193-195.
Julia source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
def remainingOneComplexRat {t : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) :=
  let component := rationalIntAsSource (JInt t) (JuliaLean.base.int.convert t)
    (fun _ : JInt .i64 => JInt.lit .i64 1)
  JuliaLean.base.number.oneValue
    (fun _ : JuliaLean.base.complex.Complex (Rat t) => ())
    (fun _ => JuliaLean.base.number.oneType
      (fun (_ : Unit) n => JuliaLean.base.number.convertNumber
        (JuliaLean.base.complex.Complex_T_Real
          (JuliaLean.base.complex.constructTypedComplex component component))
        (JInt.lit .i64 n)) ()) z

/-- Boolean exponentiation of a complex rational. The false branch
calls the concrete source `one(z)` chain and propagates its conversion
errors; the true branch preserves the input value.
Julia source: base/rational.jl:636-636 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:636-636 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ^(z::Complex{<:Rational}, n::Bool) = n ? z : one(z) # to resolve ambiguity
-- /Source
def powerNativeComplexBool {t : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) (n : Bool) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) :=
  if n then .ok z else remainingOneComplexRat z

/-- Native `float` type conversion for a rational component type.
The `float(T)` callee is the existing Number-type method, which computes
the type of `float(zero(T))`; the native value conversion is the actual
`float_BitInteger` method. This binding covers all ten native component
types, and makes no claim about BigInt or custom Integer types.
Julia source: base/rational.jl:648-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:648-648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- float(::Type{Rational{T}}) where {T<:Integer} = float(T)
-- /Source
def floatNativeRationalType (t : IntTy) : JuliaLean.base.float.FTy :=
  floatTypeSource
    (fun s : IntTy => JuliaLean.base.float.float_Type_Number
      (fun _ : Unit => JInt.lit s 0) JuliaLean.base.float.float_BitInteger
      (fun _ : JuliaLean.base.float.FV .f64 => JuliaLean.base.float.FTy.f64)) t

/-- Concrete first-element access for the existing native rational
UnitRange representation. Local interfaces select the actual field access
and same-type Number conversion, without exporting callback parameters.
Julia source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- /Source
def remainingRangeFirst {t : IntTy}
    (r : JuliaLean.base.range.UnitRange (Rat t)) : JuliaLean.base.range.JlX (Rat t) :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.UnitRange (Rat t)) (Rat t) := {}
  letI : JuliaLean.base.range.JFieldStart (JuliaLean.base.range.UnitRange (Rat t)) (Rat t) :=
    ⟨fun q => q.start⟩
  letI : JuliaLean.base.range.JConvert (Rat t) (Rat t) :=
    ⟨fun q => .ok (JuliaLean.base.number.convertSame q)⟩
  JuliaLean.base.range.first_OrdinalRange r

/-- Concrete last-element access for the existing native rational
UnitRange representation, preserving the source conversion call.
Julia source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
def remainingRangeLast {t : IntTy}
    (r : JuliaLean.base.range.UnitRange (Rat t)) : JuliaLean.base.range.JlX (Rat t) :=
  letI : JuliaLean.base.range.JEltype (JuliaLean.base.range.UnitRange (Rat t)) (Rat t) := {}
  letI : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.UnitRange (Rat t)) (Rat t) :=
    ⟨fun q => q.stop⟩
  letI : JuliaLean.base.range.JConvert (Rat t) (Rat t) :=
    ⟨fun q => .ok (JuliaLean.base.number.convertSame q)⟩
  JuliaLean.base.range.last_OrdinalRange r

/-- Native rational UnitRange length for all ten component types.
The actual stored start/stop representation, accessors, wrapping subtraction
and addition, and integer division are used. No normalization or finite-only
restriction is inserted into the executable method.
Julia source: base/rational.jl:707-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:707-712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T<:Rational
--     @inline
--     f = first(r)
--     l = last(r)
--     return div(l.num - f.num + f.den, f.den)
-- end
-- /Source
def lengthNativeRationalRange {t : IntTy}
    (r : JuliaLean.base.range.UnitRange (Rat t)) : JuliaLean.base.range.JlX (JInt t) :=
  lengthRationalRangeSource remainingRangeFirst remainingRangeLast
    JuliaLean.base.int.sub JuliaLean.base.int.add
    (fun a b => JuliaLean.base.range.liftJl
      (JuliaLean.base.div.divBitIntegerMode a b .ToZero)) r

/-- Actual same-component native widening multiplication needed by
`isempty` on rational UnitRanges. The witness is a concrete type-dispatch
restriction: it exists exactly for the eight native types up through 64
bits. The two 128-bit types require unavailable BigInt widening. The small
internal proof only adapts the known total native calls to the existing
pure comparison interface; it assumes no numerical correctness law.
Julia source: base/number.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- widemul(x::Number, y::Number) = widen(x)*widen(y)
-- /Source
def remainingRangeWidemul {t w : IntTy}
    (_wide : JuliaLean.base.int.widenType t = some w) (x y : JInt t) : JInt w :=
  JuliaLean.base.int.okOf
    (JuliaLean.base.number.widemul
      (fun a : JInt t => .ok (JuliaLean.base.int.widenTo w a))
      (fun b : JInt t => .ok (JuliaLean.base.int.widenTo w b))
      (fun a b => .ok (JuliaLean.base.int.mulSame a b)) x y)
    (by intro e h; cases h)

/-- Closed same-component rational comparison needed by the actual
range isempty method. Equal-denominator and widened-product branches are
both retained, including comparisons involving infinity. The supported
types are stated by the native widen dispatch witness, not by a finite-value
precondition or an assumed comparison law.
Julia source: base/rational.jl:508-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:508-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- <( x::Rational, y::Rational) = x.den == y.den ? x.num < y.num :
--                                widemul(x.num,y.den) < widemul(x.den,y.num)
-- /Source
def remainingRangeLess {t w : IntTy}
    (wide : JuliaLean.base.int.widenType t = some w) (x y : Rat t) : Bool :=
  ltRatSource JuliaLean.base.int.eq JuliaLean.base.int.lt
    (remainingRangeWidemul wide) (remainingRangeWidemul wide)
    JuliaLean.base.int.lt x y

/-- Concrete existing `isempty(AbstractUnitRange)` call for native
rational UnitRanges. It rereads first and last as Julia does; it does not
substitute an arbitrary predicate or assume that a range is nonempty.
Julia source: base/range.jl:711-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/range.jl:711-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isempty(r::AbstractUnitRange) = first(r) > last(r)
-- /Source
def remainingRangeIsEmpty {t w : IntTy}
    (wide : JuliaLean.base.int.widenType t = some w)
    (r : JuliaLean.base.range.UnitRange (Rat t)) : JuliaLean.base.range.JlX Bool :=
  letI : JuliaLean.base.range.JFirst (JuliaLean.base.range.UnitRange (Rat t)) (Rat t) :=
    ⟨remainingRangeFirst⟩
  letI : JuliaLean.base.range.JLast (JuliaLean.base.range.UnitRange (Rat t)) (Rat t) :=
    ⟨remainingRangeLast⟩
  letI : JuliaLean.base.range.JLt (Rat t) (Rat t) := ⟨remainingRangeLess wide⟩
  JuliaLean.base.range.isempty_AbstractUnitRange r

/-- Native checked length of a rational UnitRange with components
of at most 64 bits, through actual access, isempty, checked arithmetic and
division callees. Empty ranges return the wrapping self-subtraction before
any checked numerator arithmetic. Infinite and overflow inputs are retained
in this represented domain. Int128/UInt128 comparison requires the unavailable
BigInt widening implementation and is explicitly not covered by this binding.
Julia source: base/rational.jl:713-720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:713-720 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checked_length(r::AbstractUnitRange{T}) where T<:Rational
--     f = first(r)
--     l = last(r)
--     if isempty(r)
--         return f.num - f.num
--     end
--     return div(checked_add(checked_sub(l.num, f.num), f.den), f.den)
-- end
-- /Source
def checkedLengthNativeRationalRange {t w : IntTy}
    (wide : JuliaLean.base.int.widenType t = some w)
    (r : JuliaLean.base.range.UnitRange (Rat t)) : JuliaLean.base.range.JlX (JInt t) :=
  checkedLengthRationalRangeSource remainingRangeFirst remainingRangeLast
    (remainingRangeIsEmpty wide) JuliaLean.base.int.sub
    (fun a b => JuliaLean.base.range.liftJl (JuliaLean.base.checked.checkedSubBits a b))
    (fun a b => JuliaLean.base.range.liftJl (JuliaLean.base.checked.checkedAddBits a b))
    (fun a b => JuliaLean.base.range.liftJl
      (JuliaLean.base.div.divBitIntegerMode a b .ToZero)) r

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean JuliaLean.base.rational

/-!
Source-637 native complex-rational integer powers. The shared concrete native
rational arithmetic below is provided by this group's earlier source-120
inverse dependency section, and its actual one(z) dispatch by the source-636
section. No callback or callee-correctness input is exposed by these models.
-/

/-- Concrete same-component native rational subtraction, needed by
complex multiplication. Homogeneous rational promotion is an actual call
to the existing promote-same implementation. Every arithmetic callee and
the final rational constructor are existing concrete native methods.
Julia source: base/rational.jl:433-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:433-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Rational, y::Rational)
--     xp, _ = promote(x, y)::NTuple{2,Rational}
--     if isinf(x) && x == -y
--         return xp
--     end
--     xd, yd = divgcd(promote(x.den, y.den)...)
--     Rational(checked_sub(checked_mul(x.num, yd), checked_mul(y.num, xd)), checked_mul(x.den, yd))
-- end
-- /Source
def nativeRationalSubtraction {t : IntTy} (x y : Rat t) : Jl (Rat t) :=
  subRatSource (samePromoteOps (jintOps t))
    (fun a b => pure (JuliaLean.base.intfuncs.promoteSamePair a b))
    nativeRationalIsInfinite nativeRationalNegation
    (eqRatSource JuliaLean.base.int.eq JuliaLean.base.int.eq)
    divgcdMixed rationalSameBitsSource x y

/-- Concrete native rational flipsign dependency of complex inverse.
The ordinary negation and unary plus are both evaluated before ifelse,
including the unsigned-negation and signed-typemin errors of the source.
Julia source: base/number.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- flipsign(x::Real, y::Real) = ifelse(signbit(y), -x, +x) # the + is for type-stability on Bool
-- /Source
def complexPowerNativeFlipsign {t : IntTy} (x y : Rat t) : Jl (Rat t) :=
  JuliaLean.base.number.flipsign
    (fun q => .ok (signbitRatSource JuliaLean.base.int.signbit q))
    nativeRationalNegation
    (fun q => .ok (unaryPlusRatSource JuliaLean.base.operators.unaryPlusNumber q))
    JuliaLean.base.int.ifelse x y

/-- Concrete native complex-rational multiplication. The reused
monadic source body evaluates both real products and their subtraction
before either imaginary product and their addition. Checked native
rational operations can fail at each of those exact source points.
Julia source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:294-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(z::Complex, w::Complex) = Complex(real(z) * real(w) - imag(z) * imag(w),
--                                     real(z) * imag(w) + imag(z) * real(w))
-- /Source
def nativeComplexRationalMultiplication {t : IntTy}
    (z w : JuliaLean.base.complex.Complex (Rat t)) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) :=
  JuliaLean.base.complex.mul_ComplexM nativeRationalMultiplication
    nativeRationalSubtraction nativeRationalAddition z w

/-- Concrete complex inverse for native rational components, needed
by the negative exponent branch. Infinite components select the actual
zero/copysign/flipsign calls. Finite components evaluate conjugate
construction before both squares, addition and componentwise division.
The scalar slash method is source501 forwarding to concrete source106
exact rational division; no IEEE approximation is substituted.
Julia source: base/complex.jl:283-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/complex.jl:283-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function inv(z::Complex)
--     c, d = reim(z)
--     (isinf(c) | isinf(d)) && return complex(copysign(zero(c), c), flipsign(-zero(d), d))
--     complex(c, -d)/(c * c + d * d)
-- end
-- /Source
def complexPowerNativeInverse {t : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) :=
  let construct := JuliaLean.base.complex.complex_Real_Real
    (fun a b : Rat t => pure (JuliaLean.base.intfuncs.promoteSamePair a b))
  JuliaLean.base.complex.inv_ComplexM nativeRationalIsInfinite
    middleZeroNativeRational nativeRationalNegation
    middleCopysignNativeRational complexPowerNativeFlipsign construct
    nativeRationalNegation construct
    nativeRationalMultiplication nativeRationalAddition
    (JuliaLean.base.complex.div_Complex_RealM
      (slashRationalUnionSource nativeRationalExactDivision)) z

/-- Pure adapter for the existing powerBySquaring one interface.
The value comes from the actual one(z) dispatch already closed for source636.
The internal proof only eliminates errors from converting the fixed literals
zero and one for the ten native types; it proves no public property.
Julia source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/number.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- one(::Type{T}) where {T<:Number} = convert(T,1)
-- one(x::T) where {T<:Number} = one(T)
-- /Source
def complexPowerNativeOne {t : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) :
    JuliaLean.base.complex.Complex (Rat t) :=
  JuliaLean.base.int.okOf (remainingOneComplexRat z)
    (by intro e h; cases t <;> cases h)

/-- Native complex rational integer power, with every native
component and exponent type. The source negative branch evaluates inverse
before wrapped exponent negation. The actual powerBySquaring implementation
retains its eager initial square, fixed-type conversion, copy, one, unary
negation, isone, repeated multiplications and domain error. Neither branch
accepts supplied arithmetic or a correctness hypothesis.
Julia source: base/rational.jl:637-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:637-639 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function ^(z::Complex{<:Rational}, n::Integer)
--     n >= 0 ? power_by_squaring(z,n) : power_by_squaring(inv(z),-n)
-- end
-- /Source
def powerNativeComplexInteger {t s : IntTy}
    (z : JuliaLean.base.complex.Complex (Rat t)) (n : JInt s) :
    Jl (JuliaLean.base.complex.Complex (Rat t)) :=
  powComplexRationalIntegerGeneric
    (fun k => JuliaLean.base.int.le (JInt.lit .i64 0) k)
    JuliaLean.base.int.neg complexPowerNativeInverse
    (fun q k => JuliaLean.base.intfuncs.powerBySquaring
      (JuliaLean.base.intfuncs.bitsOps s)
      nativeComplexRationalMultiplication true
      (fun q => .ok (JuliaLean.base.number.convertSame q))
      (fun q => .ok (JuliaLean.base.number.convertSame q))
      (fun q => .ok (JuliaLean.base.number.convertSame q))
      JuliaLean.base.number.copy complexPowerNativeOne
      (JuliaLean.base.complex.neg_ComplexM nativeRationalNegation)
      (JuliaLean.base.complex.isone_Complex
        (isOneRationalSource (jintOps t).isone)
        (isZeroRationalSource (jintOps t).iszero))
      nativeComplexRationalMultiplication true q k
      JuliaLean.base.intfuncs.throwPowerDomain_Any) z n

end JuliaLean.base.rational.Models1Group20


namespace JuliaLean.base.rational.Models1Group20

open JuliaLean

/-- The actual type of the local idiv result: its two heterogeneous integer
quotients can have different signedness, and ordinary multiplication promotes
those types with wrapping conversion. This metadata performs no arithmetic.
Julia source: base/rational.jl:670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:670-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         idiv(x, c) = div(x.num, c.num) * div(c.den, x.den)
-- /Source
def gcdxIdivResultTy (input common : IntTy) : IntTy :=
  (JuliaLean.base.div.divMixedResultTy input common).promote
    (JuliaLean.base.div.divMixedResultTy common input)

/-- The coefficient type selected by integer gcdx after both local idiv calls.
It can differ from the rational gcd's component type. This only records the
existing native promotion dispatch and is not an arithmetic implementation.
Julia source: base/rational.jl:671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:671-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         _, a, b = gcdx(idiv(x, c), idiv(y, c))
-- /Source
def gcdxComputedCoefficientTy (t s : IntTy) : IntTy :=
  (gcdxIdivResultTy t (t.promote s)).promote
    (gcdxIdivResultTy s (t.promote s))

/-- The existing branch-tagged representation preserves the runtime difference
between the direct zero/infinity coefficients and coefficients returned by the
nested integer gcdx. Julia source: base/rational.jl:662-674. -/
-- Source: base/rational.jl:662-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcdx(x::Rational, y::Rational)
--     c = gcd(x, y)
--     if iszero(c.num)
--         a, b = zero(c.num), c.num
--     elseif iszero(c.den)
--         a = ifelse(iszero(x.den), one(c.den), c.den)
--         b = ifelse(iszero(y.den), one(c.den), c.den)
--     else
--         idiv(x, c) = div(x.num, c.num) * div(c.den, x.den)
--         _, a, b = gcdx(idiv(x, c), idiv(y, c))
--     end
--     c, a, b
-- end
-- /Source
abbrev NativeRationalGcdxResult (t s : IntTy) :=
  Rat (t.promote s) × RationalGcdxCoefficients
    (JInt (t.promote s))
    (JInt (gcdxComputedCoefficientTy t s))
    (JInt (gcdxComputedCoefficientTy t s))

/-- Closed isinf dependency for native rationals. It uses the installed generic
Real implementation, Number isnan, rational decomposition and native comparison;
there is no user-supplied infinity predicate or numerical callback.
Julia source: base/float.jl:703,706,716; base/rational.jl:678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/float.jl:703-703 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isnan(x::Number) = false
-- /Source
-- Source: base/float.jl:706-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isfinite(x::Real) = decompose(x)[3] != 0
-- /Source
-- Source: base/float.jl:716-716 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinf(x::Real) = !isnan(x) & !isfinite(x)
-- /Source
def gcdxNativeInfinity {t : IntTy} (x : Rat t) : Bool :=
  JuliaLean.base.float.isinf_Real JuliaLean.base.float.isnan_Number
    (JuliaLean.base.float.isfinite_Real decomposeSource
      (fun a b => !(JuliaLean.base.int.eq a b))) x

/-- Source662 closed over all native width and signedness pairs. The original
body and every numerical dependency are existing source models. Integer gcd
runs before denominator lcm; zero and infinity return coefficients in the
rational component type. The finite branch preserves each heterogeneous div
result type, unchecked wrapping multiplication, and integer gcdx dispatch.
The direct/computed sum retains coefficient types instead of silently coercing
them to the rational gcd's component type.
Julia source: base/rational.jl:662-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Documentation: base/intfuncs.jl:194-234. -/
-- Source: base/rational.jl:662-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcdx(x::Rational, y::Rational)
--     c = gcd(x, y)
--     if iszero(c.num)
--         a, b = zero(c.num), c.num
--     elseif iszero(c.den)
--         a = ifelse(iszero(x.den), one(c.den), c.den)
--         b = ifelse(iszero(y.den), one(c.den), c.den)
--     else
--         idiv(x, c) = div(x.num, c.num) * div(c.den, x.den)
--         _, a, b = gcdx(idiv(x, c), idiv(y, c))
--     end
--     c, a, b
-- end
-- /Source
def gcdxRationalNative {t s : IntTy} (x : Rat t) (y : Rat s) :
    Jl (NativeRationalGcdxResult t s) :=
  gcdxRationalSource gcdxNativeInfinity gcdxNativeInfinity
    JuliaLean.base.intfuncs.gcdMixedBits JuliaLean.base.intfuncs.lcmMixedBits
    (jintOps (t.promote s)).iszero
    (fun _ => (jintOps (t.promote s)).zero)
    (fun _ => (jintOps (t.promote s)).one)
    (jintOps t).iszero (jintOps s).iszero JuliaLean.base.int.ifelse
    (fun a b => JuliaLean.base.div.divBitIntegerMixedMode a b .ToZero)
    (fun a b => JuliaLean.base.div.divBitIntegerMixedMode a b .ToZero)
    (fun a b => JuliaLean.base.div.divBitIntegerMixedMode a b .ToZero)
    (fun a b => JuliaLean.base.div.divBitIntegerMixedMode a b .ToZero)
    (fun a b => .ok (JuliaLean.base.int.binop JuliaLean.base.int.mulSame a b))
    (fun a b => .ok (JuliaLean.base.int.binop JuliaLean.base.int.mulSame a b))
    JuliaLean.base.intfuncs.gcdxMixedBits x y

/-- Standalone concrete binding of the nested source670 method. The first
integer division finishes before the second, then ordinary machine
multiplication wraps in its actual promoted type. Neither checked multiplication
nor a normalization constructor is substituted for the source expression.
The full enclosing source block records the lexical method context.
Julia source: base/rational.jl:662-674, local method at 670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/rational.jl:662-674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function gcdx(x::Rational, y::Rational)
--     c = gcd(x, y)
--     if iszero(c.num)
--         a, b = zero(c.num), c.num
--     elseif iszero(c.den)
--         a = ifelse(iszero(x.den), one(c.den), c.den)
--         b = ifelse(iszero(y.den), one(c.den), c.den)
--     else
--         idiv(x, c) = div(x.num, c.num) * div(c.den, x.den)
--         _, a, b = gcdx(idiv(x, c), idiv(y, c))
--     end
--     c, a, b
-- end
-- /Source
def gcdxIdivNative {t p : IntTy} (x : Rat t) (c : Rat p) :
    Jl (JInt (gcdxIdivResultTy t p)) := do
  let n ← JuliaLean.base.div.divBitIntegerMixedMode x.num c.num .ToZero
  let d ← JuliaLean.base.div.divBitIntegerMixedMode c.den x.den .ToZero
  pure (JuliaLean.base.int.binop JuliaLean.base.int.mulSame n d)

end JuliaLean.base.rational.Models1Group20



namespace JuliaLean.base.rational.Models2Group10

open JuliaLean
open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Field-conversion dispatch for the unchecked inner constructor. The
accepted/rejected tag records the runtime membership of the returned value
in the requested integer component type, rather than assuming a conversion
law. The monad retains arbitrary effects, errors, aliases, and divergence.
This refines the existing unsafeRationalTypeSource conversion interface.
Source reference: base/rational.jl:14. -/
-- Source: base/rational.jl:9-15 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct Rational{T<:Integer} <: Real
--     num::T
--     den::T
-- 
--     # Unexported inner constructor of Rational that bypasses all checks
--     global unsafe_rational(::Type{T}, num, den) where {T} = new{T}(num, den)
-- end
-- /Source
structure UnsafeRationalOps (m : Type → Type) (A B T NotT : Type) where
  convertNum : A → m (TypeAssertion T NotT)
  convertDen : B → m (TypeAssertion T NotT)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean
open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Effectful refinement of the signbit/checkedNeg fields used from the
installed RatIntOps interface, together with the selected typed unsafe
constructor calls. T is the unfixed Integer component type. Neg retains the
actual checked_neg result type and may be a tagged carrier; R is unrestricted
because this method has no return annotation. Both unsafe fields pass the
original type argument T, with original or negated components respectively.
Those calls can select methods specialized on T or the components, so they
remain dispatch leaves. Concrete Base instantiations use the actual typed
constructor model, never a substitute for its known behavior.
Source reference: base/rational.jl:20-26. -/
-- Source: base/rational.jl:20-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checked_den(::Type{T}, num::T, den::T) where T<:Integer
--     if signbit(den)
--         den = checked_neg(den)
--         num = checked_neg(num)
--     end
--     return unsafe_rational(T, num, den)
-- end
-- /Source
structure CheckedDenOps (m : Type → Type) (T Neg NotBool R : Type) where
  signbit : T → m (TypeAssertion Bool NotBool)
  checkedNeg : T → m Neg
  unsafeOriginal : T → T → m R
  unsafeNegated : Neg → Neg → m R

/-- Check the denominator sign before any negation or construction. The
condition performs its own Bool assertion. In the negative branch the
denominator is negated before the numerator, and then the selected typed
unsafe constructor receives numerator before denominator. The method's
branch and both checked_neg calls are explicit; neither is a callback.
T<:Integer is the method's dispatch invariant. Arbitrary selected callee
results, effects, errors and type-changing negations remain represented.
Source reference: base/rational.jl:20-26. -/
-- Source: base/rational.jl:20-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checked_den(::Type{T}, num::T, den::T) where T<:Integer
--     if signbit(den)
--         den = checked_neg(den)
--         num = checked_neg(num)
--     end
--     return unsafe_rational(T, num, den)
-- end
-- /Source
def checkedDenTyped {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {T Neg NotBool R : Type}
    (ops : CheckedDenOps m T Neg NotBool R) (num den : T) : m R := do
  if ← assertType (← ops.signbit den) then
    let negativeDen ← ops.checkedNeg den
    let negativeNum ← ops.checkedNeg num
    ops.unsafeNegated negativeNum negativeDen
  else
    ops.unsafeOriginal num den

/-- The typed checked_den overload selected on the unfixed component T.
The type argument is T, and the two value arguments retain their order.
A selected custom overload need not return a Rational. This dispatch leaf
is distinct from the same-type forwarding method's own body below.
Source reference: base/rational.jl:27. -/
-- Source: base/rational.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checked_den(num::T, den::T) where T<:Integer = checked_den(T, num, den)
-- /Source
structure CheckedDenSameOps (m : Type → Type) (T R : Type) where
  checkedTyped : T → T → m R

/-- Forward to the typed overload selected on T at this call. Concrete Base
instances bind the leaf to checkedDenTyped, while selected custom methods
retain their own results, errors and effects without a correctness law.
Source reference: base/rational.jl:27. -/
-- Source: base/rational.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checked_den(num::T, den::T) where T<:Integer = checked_den(T, num, den)
-- /Source
def checkedDenSame {m : Type → Type} [Monad m] {T R : Type}
    (ops : CheckedDenSameOps m T R) (num den : T) : m R :=
  ops.checkedTyped num den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean

/-- Selected Rational{T} constructor dispatch for the outer same-type
Rational method. T is an arbitrary Integer component representation, not a
fixed native Base type. The constructor is a distinct callee from this outer
method; its errors, state effects and unrestricted return type are retained.
Concrete native instantiations call the installed rationalSameBitsSource.
Source reference: base/rational.jl:48. -/
-- Source: base/rational.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Rational(n::T, d::T) where {T<:Integer} = Rational{T}(n, d)
-- /Source
structure RationalSameOps (m : Type → Type) (T R : Type) where
  constructTyped : T → T → m R

/-- The same-type outer constructor invokes the selected Rational{T}
constructor once with the original numerator and denominator. No numerical
normalization or constructor-correctness law is assumed at the open Integer
dispatch boundary. Julia source: base/rational.jl:48. -/
-- Source: base/rational.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Rational(n::T, d::T) where {T<:Integer} = Rational{T}(n, d)
-- /Source
def rationalSameInteger {m : Type → Type} [Monad m] {T R : Type}
    (ops : RationalSameOps m T R) (num den : T) : m R :=
  ops.constructTyped num den

/-- Open Integer dispatch for one and the subsequently selected unsafe
constructor. The result type B of one need not be the input carrier A, and
the final return type R is unrestricted. Mutable effects, exceptions and
aliasing remain in m. Julia source: base/rational.jl:50. -/
-- Source: base/rational.jl:50-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Rational(n::Integer) = unsafe_rational(n, one(n))
-- /Source
structure RationalFromIntegerOps (m : Type → Type) (A B R : Type) where
  one : A → m B
  constructUnsafe : A → B → m R

/-- Evaluate one on the original integer, then pass that original integer
and the obtained value to the selected unsafe constructor. This preserves
type-changing one methods and all effects/error points.
Source reference: base/rational.jl:50. -/
-- Source: base/rational.jl:50-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Rational(n::Integer) = unsafe_rational(n, one(n))
-- /Source
def rationalFromInteger {m : Type → Type} [Monad m] {A B R : Type}
    (ops : RationalFromIntegerOps m A B R) (num : A) : m R := do
  let unit ← ops.one num
  ops.constructUnsafe num unit

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean
open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Selected return-tuple conversion: the known Base tuple method or a
method selected on types not fixed by divgcd. Selection precedes all Base
identity and element-membership shortcuts. A selected custom method can
return a different type or fail; the caller still asserts its return type.
Source reference: base/essentials.jl:652-667; base/rational.jl:59. -/
-- Source: base/essentials.jl:652-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T) where {T<:Tuple} = x
-- function convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}
--     # First see if there could be any conversion of the input type that'd be a subtype of the output.
--     # If not, we'll throw an explicit MethodError (otherwise, it might throw a typeassert).
--     if typeintersect(NTuple{N,Any}, T) === Union{}
--         _tuple_error(T, x)
--     end
--     function cvt1(n)
--         @inline
--         Tn = fieldtype(T, n)
--         xn = getfield(x, n, #=boundscheck=#false)
--         xn isa Tn && return xn
--         return convert(Tn, xn)
--     end
--     return ntuple(cvt1, Val(N))::NTuple{N,Any}
-- end
-- /Source
inductive TupleReturnMethod where
  | base | custom
  deriving DecidableEq, BEq

/-- The two element conversions selected on the unfixed original Integer
types and actual quotient types. Accepted tags mean runtime membership in
the target type, not merely numeric representability. Rejected carriers
retain arbitrary outside-target values, including malformed conversion
results. Neither conversion is assumed pure or correct.
Source reference: base/essentials.jl:660-664. -/
-- Source: base/essentials.jl:652-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T) where {T<:Tuple} = x
-- function convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}
--     # First see if there could be any conversion of the input type that'd be a subtype of the output.
--     # If not, we'll throw an explicit MethodError (otherwise, it might throw a typeassert).
--     if typeintersect(NTuple{N,Any}, T) === Union{}
--         _tuple_error(T, x)
--     end
--     function cvt1(n)
--         @inline
--         Tn = fieldtype(T, n)
--         xn = getfield(x, n, #=boundscheck=#false)
--         xn isa Tn && return xn
--         return convert(Tn, xn)
--     end
--     return ntuple(cvt1, Val(N))::NTuple{N,Any}
-- end
-- /Source
structure TupleElementOps (m : Type → Type)
    (X Y OtherX OtherY : Type) where
  convertX : OtherX → m (TypeAssertion X OtherX)
  convertY : OtherY → m (TypeAssertion Y OtherY)

/-- Full dispatch boundary for convert(Tuple{TX,TY}, quotients). Custom
selection receives the original tagged quotient pair, even if both values
already belong to the target types. The known Base branch below is actual
fixed-arity tuple traversal, not a callback. OtherTuple retains any custom
result outside the requested two-element tuple type.
Source reference: base/essentials.jl:652-667; base/rational.jl:59. -/
-- Source: base/essentials.jl:652-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T) where {T<:Tuple} = x
-- function convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}
--     # First see if there could be any conversion of the input type that'd be a subtype of the output.
--     # If not, we'll throw an explicit MethodError (otherwise, it might throw a typeassert).
--     if typeintersect(NTuple{N,Any}, T) === Union{}
--         _tuple_error(T, x)
--     end
--     function cvt1(n)
--         @inline
--         Tn = fieldtype(T, n)
--         xn = getfield(x, n, #=boundscheck=#false)
--         xn isa Tn && return xn
--         return convert(Tn, xn)
--     end
--     return ntuple(cvt1, Val(N))::NTuple{N,Any}
-- end
-- /Source
structure TupleReturnOps (m : Type → Type)
    (X Y OtherX OtherY OtherTuple : Type) where
  elements : TupleElementOps m X Y OtherX OtherY
  selected : TypeAssertion X OtherX → TypeAssertion Y OtherY → TupleReturnMethod
  custom : TypeAssertion X OtherX → TypeAssertion Y OtherY →
    m (TypeAssertion (X × Y) OtherTuple)

/-- Necessary concrete arity-two specialization of Base tuple conversion
and the enclosing divgcd return assertion. The installed tuple identity
model handles an already matching pair. Otherwise cvt1 skips accepted
elements and converts rejected elements in order, just as ntuple with
Val(2) visits the two fields. Both conversions finish before either target
membership assertion: cvt1 itself returns convert's value unchecked, and
its NTuple{2,Any} assertion cannot reject an element type. The later
Tuple{TX,TY} return assertion belongs to divgcd.

This helper is internal to divgcd's return boundary. The tuple arity is
exactly two, and its target types are inhabited by the actual arguments
x and y, so typeintersect(NTuple{2,Any}, Tuple{TX,TY}) is nonempty. Field
indices 1 and 2 are in range and Val(2) has no negative-length branch.
There is no assumed conversion law and no supplied traversal callback.
Source reference: base/essentials.jl:652-667; base/ntuple.jl:65-73;
base/rational.jl:59-62. -/
-- Source: base/essentials.jl:652-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T) where {T<:Tuple} = x
-- function convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}
--     # First see if there could be any conversion of the input type that'd be a subtype of the output.
--     # If not, we'll throw an explicit MethodError (otherwise, it might throw a typeassert).
--     if typeintersect(NTuple{N,Any}, T) === Union{}
--         _tuple_error(T, x)
--     end
--     function cvt1(n)
--         @inline
--         Tn = fieldtype(T, n)
--         xn = getfield(x, n, #=boundscheck=#false)
--         xn isa Tn && return xn
--         return convert(Tn, xn)
--     end
--     return ntuple(cvt1, Val(N))::NTuple{N,Any}
-- end
-- /Source
-- Source: base/ntuple.jl:65-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function ntuple(f::F, ::Val{N}) where {F,N}
--     (N::Int >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", N)))
--     if @generated
--         :(@ntuple $N i -> f(i))
--     else
--         Tuple(f(i) for i = 1:(N::Int))
--     end
-- end
-- 
-- /Source
-- Source: base/rational.jl:59-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer}
--     g = gcd(uabs(x), uabs(y))
--     div(x,g), div(y,g)
-- end
-- /Source
def convertReturnTupleBase {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {X Y OtherX OtherY : Type}
    (ops : TupleElementOps m X Y OtherX OtherY)
    (qx : TypeAssertion X OtherX) (qy : TypeAssertion Y OtherY) :
    m (X × Y) := do
  match qx, qy with
  | .accepted x, .accepted y =>
      pure (JuliaLean.base.essentials.convertTupleIdentity (x, y))
  | _, _ =>
      let cx ← match qx with
        | .accepted x => pure (.accepted x)
        | .rejected raw => ops.convertX raw
      let cy ← match qy with
        | .accepted y => pure (.accepted y)
        | .rejected raw => ops.convertY raw
      let x ← assertType cx
      let y ← assertType cy
      pure (x, y)

/-- Select the whole-tuple conversion before any Base identity shortcut.
The custom call keeps the original tags and its final target-tuple check;
the Base selection executes the actual specialization above. This is a
return-boundary helper, not a callback for divgcd's own body.
Source reference: base/essentials.jl:652-667; base/rational.jl:59. -/
-- Source: base/essentials.jl:652-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T) where {T<:Tuple} = x
-- function convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}
--     # First see if there could be any conversion of the input type that'd be a subtype of the output.
--     # If not, we'll throw an explicit MethodError (otherwise, it might throw a typeassert).
--     if typeintersect(NTuple{N,Any}, T) === Union{}
--         _tuple_error(T, x)
--     end
--     function cvt1(n)
--         @inline
--         Tn = fieldtype(T, n)
--         xn = getfield(x, n, #=boundscheck=#false)
--         xn isa Tn && return xn
--         return convert(Tn, xn)
--     end
--     return ntuple(cvt1, Val(N))::NTuple{N,Any}
-- end
-- /Source
-- Source: base/rational.jl:59-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer}
--     g = gcd(uabs(x), uabs(y))
--     div(x,g), div(y,g)
-- end
-- /Source
def convertReturnTuple {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {X Y OtherX OtherY OtherTuple : Type}
    (ops : TupleReturnOps m X Y OtherX OtherY OtherTuple)
    (qx : TypeAssertion X OtherX) (qy : TypeAssertion Y OtherY) :
    m (X × Y) := do
  match ops.selected qx qy with
  | .base => convertReturnTupleBase ops.elements qx qy
  | .custom => assertType (← ops.custom qx qy)

/-- Effectful refinement of the installed divgcdSource dispatch interface.
X and Y represent the respective unfixed Integer input types; UX, UY and
G retain the actual uabs and gcd result types, including tagged carriers
when custom results vary at runtime. Division results keep their target
membership tags until both divisions finish. All leaves are genuine
calls dispatched on types this method does not fix. Concrete Base
instantiations use installed arithmetic and conversion implementations.
Source reference: base/rational.jl:59-62. -/
-- Source: base/rational.jl:59-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer}
--     g = gcd(uabs(x), uabs(y))
--     div(x,g), div(y,g)
-- end
-- /Source
structure DivgcdOps (m : Type → Type)
    (X Y UX UY G OtherX OtherY OtherTuple : Type) where
  uabsX : X → m UX
  uabsY : Y → m UY
  gcd : UX → UY → m G
  divX : X → G → m (TypeAssertion X OtherX)
  divY : Y → G → m (TypeAssertion Y OtherY)
  returnOps : TupleReturnOps m X Y OtherX OtherY OtherTuple

/-- Compute magnitudes left to right, then their selected gcd, then both
quotients left to right, and only then convert and assert the annotated
return tuple. The Integer dispatch invariant is on X and Y; no native
width, same-type, successful-conversion or callee-correctness restriction
is imposed. Every selected exception retains its original throw point.
Source reference: base/rational.jl:59-62. -/
-- Source: base/rational.jl:59-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function divgcd(x::TX, y::TY)::Tuple{TX, TY} where {TX<:Integer, TY<:Integer}
--     g = gcd(uabs(x), uabs(y))
--     div(x,g), div(y,g)
-- end
-- /Source
def divgcd {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {X Y UX UY G OtherX OtherY OtherTuple : Type}
    (ops : DivgcdOps m X Y UX UY G OtherX OtherY OtherTuple)
    (x : X) (y : Y) : m (X × Y) := do
  let ux ← ops.uabsX x
  let uy ← ops.uabsY y
  let g ← ops.gcd ux uy
  let qx ← ops.divX x g
  let qy ← ops.divY y g
  convertReturnTuple ops.returnOps qx qy

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean

/-- Selected Rational constructor dispatch at the Integer exact-division
method. Both Integer types are unfixed, so the selected constructor retains
arbitrary effects, exceptions and return type R. This callee is distinct
from // itself; no exact-division body or recursion is supplied as a callback.
Native instantiations use the actual installed constructor composition.
Source reference: base/rational.jl:91. -/
-- Source: base/rational.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- //(n::Integer,  d::Integer) = Rational(n,d)
-- /Source
structure ExactIntegerOps (m : Type → Type) (A B R : Type) where
  rational : A → B → m R

/-- Exact division of two Integers calls the selected Rational constructor
once with the original numerator and denominator, preserving all dispatch
effects and outcomes. Julia source: base/rational.jl:91. -/
-- Source: base/rational.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- //(n::Integer,  d::Integer) = Rational(n,d)
-- /Source
def exactDivideIntegers {m : Type → Type} [Monad m] {A B R : Type}
    (ops : ExactIntegerOps m A B R) (num : A) (den : B) : m R :=
  ops.rational num den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean
open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected exact division of an unfixed Real component by an unfixed
Real scalar, and selected complex construction from the actual quotient
values. Q may be a tagged carrier when division changes result type at
runtime, and R is unrestricted because the source has no return assertion.
Concrete Complex field access is not a dispatch callback. T and Y obey
the source Real representation invariants; their values may include
mutable handles whose aliases and effects live in m's world.
Source reference: base/rational.jl:116. -/
-- Source: base/rational.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- //(x::Complex, y::Real) = complex(real(x)//y, imag(x)//y)
-- /Source
structure ComplexRealOps (m : Type → Type) (T Y Q R : Type) where
  divide : T → Y → m Q
  complex : Q → Q → m R

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Selected operations on the unfixed Real component T and its Complex
container. P retains the actual isinf return values; only the result of
selected | is asserted as Bool. Z retains the selected zero result type,
and N may tag different conjugation result types across branches. D is
the actual squared-magnitude result. Because Complex{T}'s component is
unfixed, selected zero/conj/abs2 methods can have custom behavior; concrete
Base instantiations bind them to the installed actual implementations.
Source reference: base/rational.jl:120-128. -/
-- Source: base/rational.jl:120-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _complex_exact_inv(y::Complex)
--     c, d = reim(y)
--     num = if (isinf(c) | isinf(d))
--         conj(zero(y))
--     else
--         conj(y)
--     end
--     num, abs2(y)
-- end
-- /Source
structure ComplexInverseOps (m : Type → Type) (T P NotBool Z N D : Type) where
  isinf : T → m P
  bitOr : P → P → m (TypeAssertion Bool NotBool)
  zero : JuliaLean.base.complex.Complex T → m Z
  conjOriginal : JuliaLean.base.complex.Complex T → m N
  conjZero : Z → m N
  abs2 : JuliaLean.base.complex.Complex T → m D

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- The fixed function object passed by X .// y: Julia's scalar //.
This token preserves function identity for broadcasted dispatch; it is not
an arbitrary caller-supplied function or a replacement scalar algorithm.
The selected broadcast machinery interprets that exact function object.
Source reference: base/rational.jl:154; base/broadcast.jl:859. -/
-- Source: base/rational.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- //(X::AbstractArray, y::Number) = X .// y
-- /Source
inductive ExactDivisionBroadcastFunction where
  | exactDivision
  deriving DecidableEq, BEq

/-- The two genuine dispatch boundaries of the dotted expression. A
represents the original AbstractArray handle with its actual Julia axes
and storage in the effect world; Y represents the Number scalar. B is the
actual result of selected broadcasted, including custom eager results,
and R is the unrestricted selected materialize result. Neither the array
subtype, broadcast style, lazy-result type nor allocation target is fixed
by this method. No array is replaced with an unrestricted Lean list.

These fields are distinct selected Julia calls. Shape discovery, indexing,
allocation, element evaluation and custom eager behavior belong to their
selected implementations; this record does not replace the assigned
method's own composition with a single broadcast callback. The function
argument remains the fixed // token, and both original input handles are
forwarded unchanged with all state and exceptions.
Source reference: base/rational.jl:154; base/broadcast.jl:859,921-922;
doc/src/manual/interfaces.md:648-659. -/
-- Source: base/rational.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- //(X::AbstractArray, y::Number) = X .// y
-- /Source
-- Source: base/broadcast.jl:859-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast(f::Tf, As::Vararg{Any,N}) where {Tf,N} = materialize(broadcasted(f, As...))
-- /Source
structure ArrayExactDivisionOps (m : Type → Type) (A Y B R : Type) where
  broadcasted : ExactDivisionBroadcastFunction → A → Y → m B
  materialize : B → m R

/-- Execute the actual dotted-call composition: construct/evaluate the
selected broadcasted call with //, X and y, then materialize that exact
result. The second call sees all first-call effects and does not run after
its failure. A custom eager result or zero-dimensional scalar result is
retained without forced array allocation or a result-type assertion.

The pinned manual describes dot lowering through broadcasted and custom
style dispatch; the Base broadcast body records the materialize composition.
No known tuple traversal or array-allocation body occurs in this wrapper,
and no such behavior is replaced by a callback here. Concrete broadcasting
instances must bind these leaves to their actual selected implementations.
Source reference: base/rational.jl:154; base/broadcast.jl:859;
doc/src/manual/functions.md:1099-1105,1167-1169;
doc/src/manual/interfaces.md:648-659. -/
-- Source: base/rational.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- //(X::AbstractArray, y::Number) = X .// y
-- /Source
-- Source: base/broadcast.jl:859-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast(f::Tf, As::Vararg{Any,N}) where {Tf,N} = materialize(broadcasted(f, As...))
-- /Source
def exactDivideArray {m : Type → Type} [Monad m] {A Y B R : Type}
    (ops : ArrayExactDivisionOps m A Y B R) (array : A) (scalar : Y) : m R := do
  let broadcastValue ← ops.broadcasted .exactDivision array scalar
  ops.materialize broadcastValue

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected scalar read and exact division for an unfixed IO stream and
Integer component-type descriptor. Target represents the component T of
the valid Rational{T} type argument. Value retains each actual read return,
possibly with runtime tags; the source does not assert that a custom read
returned T. The selected quotient's actual result carrier R is unrestricted.
Stream may be a shared handle whose aliases and cursor/buffer effects live
in the monadic world. No endianness conversion is inserted.
Source reference: base/rational.jl:167-171; base/io.jl:237-243. -/
-- Source: base/rational.jl:167-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function read(s::IO, ::Type{Rational{T}}) where T<:Integer
--     r = read(s,T)
--     i = read(s,T)
--     r//i
-- end
-- /Source
structure RationalReadOps (m : Type → Type) (Stream Target Value R : Type) where
  readComponent : Stream → Target → m Value
  exactDivide : Value → Value → m R

/-- Read numerator then denominator from the same stream using the same
component type descriptor, retaining the first read's effects for the
second. Only after both succeed, exactly divide their actual unasserted
return values in that order. The method does not restore the stream on
failure, convert either read value, or assert the final result's type.
Source reference: base/rational.jl:167-171. -/
-- Source: base/rational.jl:167-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function read(s::IO, ::Type{Rational{T}}) where T<:Integer
--     r = read(s,T)
--     i = read(s,T)
--     r//i
-- end
-- /Source
def readRationalValue {m : Type → Type} [Monad m]
    {Stream Target Value R : Type}
    (ops : RationalReadOps m Stream Target Value R)
    (stream : Stream) (target : Target) : m R := do
  let numerator ← ops.readComponent stream target
  let denominator ← ops.readComponent stream target
  ops.exactDivide numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- The selected variadic write on an unfixed IO stream and Rational
component type. Its result R is unrestricted because this source method
has no return assertion. State and errors include any partial output or
cursor changes. This is the actual three-argument selected write call,
not an assumed decomposition into two independently selected scalar writes.
Source reference: base/rational.jl:172-174; base/io.jl:266-280. -/
-- Source: base/rational.jl:172-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function write(s::IO, z::Rational)
--     write(s,numerator(z),denominator(z))
-- end
-- /Source
structure RationalWriteOps (m : Type → Type) (Stream T R : Type) where
  writeComponents : Stream → T → T → m R

/-- Obtain the stored Rational numerator and denominator through their
installed concrete selectors, then invoke selected variadic write once on
the original stream in numerator/denominator argument order. Raw stored
fields, including noncanonical pairs, pass through unchanged. The selected
write's exact result and all successful or failing IO effects are retained.
Source reference: base/rational.jl:172-174,361,384. -/
-- Source: base/rational.jl:172-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function write(s::IO, z::Rational)
--     write(s,numerator(z),denominator(z))
-- end
-- /Source
def writeRationalValue {m : Type → Type} [Monad m] {Stream T R : Type}
    (ops : RationalWriteOps m Stream T R)
    (stream : Stream) (value : Rational T) : m R :=
  ops.writeComponents stream
    (numeratorRationalSource value) (denominatorRationalSource value)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Caller indexing context, retaining the source @inbounds annotation.
It does not assert that every selected bounds check is disabled: actual
behavior depends on the selected method, inlining and global bounds-check
configuration. An inbounds-context selected getindex may still throw.
Source reference: base/rational.jl:180;
doc/src/devdocs/boundscheck.md:11-36,126. -/
-- Source: base/rational.jl:175-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse(::Type{Rational{T}}, s::AbstractString) where T<:Integer
--     ss = split(s, '/'; limit = 2)
--     if isone(length(ss))
--         return Rational{T}(parse(T, s))
--     end
--     @inbounds ns, ds = ss[1], ss[2]
--     if startswith(ds, '/')
--         ds = chop(ds; head = 1, tail = 0)
--     end
--     n = parse(T, ns)
--     d = parse(T, ds)
--     return n//d
-- end
-- /Source
inductive RationalParseIndexContext where
  | ordinary | inbounds
  deriving DecidableEq, BEq

/-- Selected parsing operations for an unfixed AbstractString input and
valid Rational Integer component descriptor. Parts and Length retain the
actual split/length return carriers without list, indexing or integer
assumptions. Piece and Chopped may differ; every parse result is unasserted,
and R can tag different constructor/quotient result types. The same parsePiece
leaf handles both unchanged fragments. split's final argument is its limit
keyword; chop's final arguments are its head and tail keywords in that order.
Char represents the fixed source Unicode slash literal. Native constants
use the packet's I64 convention. The context tag is caller metadata only.
Source reference: base/rational.jl:175-187. -/
-- Source: base/rational.jl:175-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse(::Type{Rational{T}}, s::AbstractString) where T<:Integer
--     ss = split(s, '/'; limit = 2)
--     if isone(length(ss))
--         return Rational{T}(parse(T, s))
--     end
--     @inbounds ns, ds = ss[1], ss[2]
--     if startswith(ds, '/')
--         ds = chop(ds; head = 1, tail = 0)
--     end
--     n = parse(T, ns)
--     d = parse(T, ds)
--     return n//d
-- end
-- /Source
structure RationalParseOps (m : Type → Type)
    (Target Text Parts Length Piece Chopped OriginalValue PieceValue ChoppedValue
      NotOne NotSlash R : Type) where
  split : Text → Char → JInt .i64 → m Parts
  length : Parts → m Length
  isone : Length → m (TypeAssertion Bool NotOne)
  getindex : RationalParseIndexContext → Parts → JInt .i64 → m Piece
  startswith : Piece → Char → m (TypeAssertion Bool NotSlash)
  chop : Piece → JInt .i64 → JInt .i64 → m Chopped
  parseOriginal : Target → Text → m OriginalValue
  parsePiece : Target → Piece → m PieceValue
  parseChopped : Target → Chopped → m ChoppedValue
  constructTyped : Target → OriginalValue → m R
  divideOriginal : PieceValue → PieceValue → m R
  divideChopped : PieceValue → ChoppedValue → m R

/-- Split with limit two, test the actual selected length through isone,
and assert only its condition result as Bool. The singleton branch parses
the original text and calls the typed constructor with the original target.
Otherwise both annotated indices are evaluated in order before startswith;
an accepted true condition completes chop before numerator parsing. The
numerator parse precedes the appropriate unchanged/chopped denominator
parse and selected quotient. Sum retains a type-changing chop result.
Only source condition results are asserted; length and parse returns are
never asserted or coerced. Every selected effect and throw point is retained.
Source reference: base/rational.jl:175-187. -/
-- Source: base/rational.jl:175-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function parse(::Type{Rational{T}}, s::AbstractString) where T<:Integer
--     ss = split(s, '/'; limit = 2)
--     if isone(length(ss))
--         return Rational{T}(parse(T, s))
--     end
--     @inbounds ns, ds = ss[1], ss[2]
--     if startswith(ds, '/')
--         ds = chop(ds; head = 1, tail = 0)
--     end
--     n = parse(T, ns)
--     d = parse(T, ds)
--     return n//d
-- end
-- /Source
def parseRationalValue {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m]
    {Target Text Parts Length Piece Chopped OriginalValue PieceValue ChoppedValue
      NotOne NotSlash R : Type}
    (ops : RationalParseOps m Target Text Parts Length Piece Chopped
      OriginalValue PieceValue ChoppedValue NotOne NotSlash R)
    (target : Target) (text : Text) : m R := do
  let parts ← ops.split text '/' (JInt.lit .i64 2)
  let count ← ops.length parts
  let singleton ← assertType (← ops.isone count)
  if singleton then
    let parsed ← ops.parseOriginal target text
    ops.constructTyped target parsed
  else
    let numeratorText ← ops.getindex .inbounds parts (JInt.lit .i64 1)
    let denominatorText ← ops.getindex .inbounds parts (JInt.lit .i64 2)
    let hasSlash ← assertType (← ops.startswith denominatorText '/')
    let adjusted : Sum Piece Chopped ← if hasSlash then do
        let chopped ← ops.chop denominatorText (JInt.lit .i64 1) (JInt.lit .i64 0)
        pure (.inr chopped)
      else pure (.inl denominatorText)
    let numerator ← ops.parsePiece target numeratorText
    match adjusted with
    | .inl denominator => do
        let parsed ← ops.parsePiece target denominator
        ops.divideOriginal numerator parsed
    | .inr denominator => do
        let parsed ← ops.parseChopped target denominator
        ops.divideChopped numerator parsed

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected conversion and typed unsafe construction on unfixed Integer
source/target types. Target is the original valid Integer descriptor;
Converted may tag arbitrary actual values, including wrong-target returns.
No assertion is added by this body. Final construction retains arbitrary
result R and effects. Julia source: base/rational.jl:190-192. -/
-- Source: base/rational.jl:190-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Rational{T}(x::Rational) where T<:Integer
--     unsafe_rational(T, convert(T, x.num), convert(T, x.den))
-- end
-- /Source
structure RationalConvertOps (m : Type → Type)
    (Target Source Converted R : Type) where
  convert : Target → Source → m Converted
  store : Target → Converted → Converted → m R

/-- Convert numerator then denominator, then call selected unsafe storage
with both actual values and original target. No normalization or assertion
is inserted. The final constructor may convert/assert fields again; those
effects are not collapsed into the explicit preceding conversions.
Source reference: base/rational.jl:190-192. -/
-- Source: base/rational.jl:190-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Rational{T}(x::Rational) where T<:Integer
--     unsafe_rational(T, convert(T, x.num), convert(T, x.den))
-- end
-- /Source
def convertRationalValue {m : Type → Type} [Monad m]
    {Target Source Converted R : Type}
    (ops : RationalConvertOps m Target Source Converted R)
    (target : Target) (x : Rational Source) : m R := do
  let numerator ← ops.convert target x.num
  let denominator ← ops.convert target x.den
  ops.store target numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected target constructors, one(x), and typed unsafe storage.
Input conversion, one, its conversion and storage retain distinct carriers
and arbitrary effects. Target is the original valid Integer descriptor.
No success/type-preservation law is assumed. Source: base/rational.jl:193-195. -/
-- Source: base/rational.jl:193-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Rational{T}(x::Integer) where T<:Integer
--     unsafe_rational(T, T(x), T(one(x)))
-- end
-- /Source
structure TypedRationalIntegerOps (m : Type → Type)
    (Target Input Num One Den R : Type) where
  constructInput : Target → Input → m Num
  one : Input → m One
  constructOne : Target → One → m Den
  store : Target → Num → Den → m R

/-- Complete T(x) before one(x), then T(one(x)) before unsafe storage.
Both constructors receive original T; one receives original x. The source
adds no return-value assertion, and storage may perform further field
conversions. Julia source: base/rational.jl:193-195. -/
-- Source: base/rational.jl:193-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function Rational{T}(x::Integer) where T<:Integer
--     unsafe_rational(T, T(x), T(one(x)))
-- end
-- /Source
def rationalFromIntegerAs {m : Type → Type} [Monad m]
    {Target Input Num One Den R : Type}
    (ops : TypedRationalIntegerOps m Target Input Num One Den R)
    (target : Target) (x : Input) : m R := do
  let numerator ← ops.constructInput target x
  let oneValue ← ops.one x
  let denominator ← ops.constructOne target oneValue
  ops.store target numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Equality is selected on the unfixed Rational component type. Its actual
result is tagged for the source condition's Bool assertion; arbitrary
state changes, exceptions and non-Bool returns remain represented. The
second operand is the actual native Int literal, not a replacement value
of the component type. Julia source: base/rational.jl:199-200. -/
-- Source: base/rational.jl:199-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Bool(x::Rational) = x==0 ? false : x==1 ? true :
--     throw(InexactError(:Bool, Bool, x)) # to resolve ambiguity
-- /Source
structure RationalBoolOps (m : Type → Type) (T NotBool : Type) where
  equal : Rational T → JInt .i64 → m (TypeAssertion Bool NotBool)

/-- Compare with native Int zero before considering native Int one.
Each conditional checks the selected equality result as Bool at that
point. The known InexactError is constructed only after both comparisons
return false; the installed error carrier retains its class and function
name. No error-constructor implementation is supplied as a callback.
Source reference: base/rational.jl:199-200; base/boot.jl:539-543. -/
-- Source: base/rational.jl:199-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Bool(x::Rational) = x==0 ? false : x==1 ? true :
--     throw(InexactError(:Bool, Bool, x)) # to resolve ambiguity
-- /Source
def boolFromRational {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {T NotBool : Type}
    (ops : RationalBoolOps m T NotBool) (x : Rational T) : m Bool := do
  let isZero ← assertType (← ops.equal x (JInt.lit .i64 0))
  if isZero then
    pure false
  else
    let isOne ← assertType (← ops.equal x (JInt.lit .i64 1))
    if isOne then
      pure true
    else
      throw (.julia (inexactErrorCore "Bool" Bool x))

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Selected operations for conversion to an unfixed Integer target.
Target preserves the original runtime type descriptor; accepted conversion
values in T represent membership in that descriptor's type. Predicate and
conversion returns retain their actual type-assertion tags. The name result
uses the documented Symbol protocol, represented by String as in the
installed error carrier. Contract-violating custom nonsymbol nameof
returns are outside this result protocol; no nonexistent name assertion
is inserted. Julia source: base/rational.jl:201-202;
base/runtime_internals.jl:470-488. -/
-- Source: base/rational.jl:201-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(x::Rational) where {T<:Integer} = (isinteger(x) ? convert(T, x.num)::T :
--     throw(InexactError(nameof(T), T, x)))
-- /Source
structure IntegerFromRationalOps (m : Type → Type)
    (Target S T NotBool NotT : Type) where
  isInteger : Rational S → m (TypeAssertion Bool NotBool)
  convert : Target → S → m (TypeAssertion T NotT)
  nameof : Target → m String

/-- Evaluate and assert the integrality condition before choosing a branch.
Only the integral branch converts the original numerator and performs the
explicit returned-value assertion. Only the other branch obtains the
original target's name before constructing and throwing known InexactError.
The existing error representation retains class and function name while
erasing the target/value payload; all selected-call effects are preserved.
Source reference: base/rational.jl:201-202; base/boot.jl:539-543. -/
-- Source: base/rational.jl:201-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(x::Rational) where {T<:Integer} = (isinteger(x) ? convert(T, x.num)::T :
--     throw(InexactError(nameof(T), T, x)))
-- /Source
def integerFromRational {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {Target S T NotBool NotT : Type}
    (ops : IntegerFromRationalOps m Target S T NotBool NotT)
    (target : Target) (x : Rational S) : m T := do
  let integral ← assertType (← ops.isInteger x)
  if integral then
    assertType (← ops.convert target x.num)
  else
    let name ← ops.nameof target
    throw (.julia (inexactErrorCore name T x))

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Selected float and division on an unfixed Rational Integer component
type. Converted may be a tagged carrier for different actual float-call
return types, including non-floating custom returns. AF represents all
values belonging to AbstractFloat in the chosen runtime representation;
NotFloat retains other division results for the actual final assertion.
The same selected float method receives numerator and denominator in turn.
No intermediate is asserted to be floating and no numerical law is assumed.
Source reference: base/rational.jl:204. -/
-- Source: base/rational.jl:204-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- AbstractFloat(x::Rational) = (float(x.num)/float(x.den))::AbstractFloat
-- /Source
structure RationalAbstractFloatOps (m : Type → Type)
    (T Converted AF NotFloat : Type) where
  floatValue : T → m Converted
  divide : Converted → Converted → m (TypeAssertion AF NotFloat)

/-- Finish numerator float conversion before reading/converting the
denominator; divide the two actual results, then perform the known Core
AbstractFloat assertion. Earlier effects and exceptions survive unchanged,
including effects of a division that successfully returns a wrong type.
The fixed Rational field reads and installed assertType are not callbacks.
Source reference: base/rational.jl:204. -/
-- Source: base/rational.jl:204-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- AbstractFloat(x::Rational) = (float(x.num)/float(x.den))::AbstractFloat
-- /Source
def abstractFloatRational {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {T Converted AF NotFloat : Type}
    (ops : RationalAbstractFloatOps m T Converted AF NotFloat)
    (x : Rational T) : m AF := do
  let numerator ← ops.floatValue x.num
  let denominator ← ops.floatValue x.den
  assertType (← ops.divide numerator denominator)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Selected operations for an unfixed AbstractFloat target T and Rational
component type S. Target and Source retain the actual type-argument
descriptors corresponding to the represented result F and component S.
Promoted retains the actual promote_type return, including an unexpected
non-type custom value; the source inserts no assertion on P. Converted and
Quotient likewise retain arbitrary selected intermediate return types.
Only the final conversion result is tagged against the original T.
Both promoted conversions share one selected method. No promotion,
conversion, numerical, purity or success law is imposed on any leaf.
Source reference: base/rational.jl:205-208. -/
-- Source: base/rational.jl:205-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (::Type{T})(x::Rational{S}) where T<:AbstractFloat where S
--     P = promote_type(T,S)
--     convert(T, convert(P,x.num)/convert(P,x.den))::T
-- end
-- /Source
structure RationalTypedFloatOps (m : Type → Type)
    (Target Source S Promoted Converted Quotient F NotF : Type) where
  promoteType : Target → Source → m Promoted
  convertPromoted : Promoted → S → m Converted
  divide : Converted → Converted → m Quotient
  convertTarget : Target → Quotient → m (TypeAssertion F NotF)

/-- Compute the selected promotion before reading/converting the stored
numerator, then convert the denominator with that same actual P. Divide
the two raw results, convert the quotient using the original target, and
perform the installed final ::T assertion. The component descriptor is
the method's S type argument, not a recomputed value-dependent typeof.
All effects, exceptions, changed return types and alias handles survive
at their original source positions. No extra intermediate assertion or
implicit return conversion is inserted.
Source reference: base/rational.jl:205-208. -/
-- Source: base/rational.jl:205-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (::Type{T})(x::Rational{S}) where T<:AbstractFloat where S
--     P = promote_type(T,S)
--     convert(T, convert(P,x.num)/convert(P,x.den))::T
-- end
-- /Source
def typedFloatRational {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m]
    {Target Source S Promoted Converted Quotient F NotF : Type}
    (ops : RationalTypedFloatOps m Target Source S Promoted Converted Quotient F NotF)
    (target : Target) (source : Source) (x : Rational S) : m F := do
  let promoted ← ops.promoteType target source
  let numerator ← ops.convertPromoted promoted x.num
  let denominator ← ops.convertPromoted promoted x.den
  let quotient ← ops.divide numerator denominator
  assertType (← ops.convertTarget target quotient)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected big on the unfixed Integer component, followed by selected
unsafe_rational on the actual converted values. B may tag changing runtime
return types and R is unrestricted because this body has no assertion.
Integer/BigInt values may be real mutable handles into m's world; no Lean
Int or list representation is substituted for GMP objects or allocation.
Source reference: base/rational.jl:226. -/
-- Source: base/rational.jl:226-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(q::Rational) = unsafe_rational(big(numerator(q)), big(denominator(q)))
-- /Source
structure RationalBigOps (m : Type → Type) (T B R : Type) where
  big : T → m B
  unsafeRational : B → B → m R

/-- Read the actual numerator and complete its selected big conversion,
then read and convert the actual denominator. Only after both succeed is
the selected unsafe constructor called with their exact results in order.
Concrete installed Rational selectors remain explicit, with no numerical,
normalization, purity, allocation or alias-preservation law imposed on the
selected callees. Julia source: base/rational.jl:226,361,384. -/
-- Source: base/rational.jl:226-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(q::Rational) = unsafe_rational(big(numerator(q)), big(denominator(q)))
-- /Source
def bigRational {m : Type → Type} [Monad m] {T B R : Type}
    (ops : RationalBigOps m T B R) (q : Rational T) : m R := do
  let numerator ← ops.big (numeratorRationalSource q)
  let denominator ← ops.big (denominatorRationalSource q)
  ops.unsafeRational numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- The fixed type object named by this call is exactly
Complex{Rational{Base.GMP.BigInt}}. This token preserves that descriptor's
identity without pretending that metadata implements GMP values,
allocation or conversion. Julia source: base/rational.jl:228. -/
-- Source: base/rational.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(z::Complex{<:Rational{<:Integer}}) = Complex{Rational{BigInt}}(z)
-- /Source
inductive BigComplexRationalTarget where
  | complexRationalBigInt

/-- The target constructor is selected on the unfixed input component T,
which represents an arbitrary Integer type. Its fixed target is explicit,
its argument is the actual installed Complex/Rational value, and its result
and effects are unrestricted. This is a distinct constructor call, not a
parameter implementing big itself. No closed native/GMP specialization is
claimed. Julia source: base/rational.jl:228. -/
-- Source: base/rational.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(z::Complex{<:Rational{<:Integer}}) = Complex{Rational{BigInt}}(z)
-- /Source
structure BigComplexRationalOps (m : Type → Type) (T R : Type) where
  construct : BigComplexRationalTarget →
    JuliaLean.base.complex.Complex (Rational T) → m R

/-- Invoke the selected fixed-target constructor on the original z.
The pinned body contains no component big calls, selector calls or result
assertion; all such work belongs to the separately selected constructor.
Custom input dispatch, type-changing returns, errors, mutations and aliases
therefore survive this one-call wrapper unchanged.
Source reference: base/rational.jl:228. -/
-- Source: base/rational.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- big(z::Complex{<:Rational{<:Integer}}) = Complex{Rational{BigInt}}(z)
-- /Source
def bigComplexRational {m : Type → Type} [Monad m] {T R : Type}
    (ops : BigComplexRationalOps m T R)
    (z : JuliaLean.base.complex.Complex (Rational T)) : m R :=
  ops.construct .complexRationalBigInt z

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- The selected promote_type call on an unfixed Integer component type
descriptor and an unfixed AbstractFloat type descriptor. Descriptor carriers
may retain tagged custom type objects; the result R is unrestricted because
the source neither applies a type constructor nor asserts its return type.
Source reference: base/rational.jl:232. -/
-- Source: base/rational.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:AbstractFloat} = promote_type(T,S)
-- /Source
structure RationalFloatPromotionOps (m : Type → Type)
    (IntegerType FloatType R : Type) where
  promoteType : IntegerType → FloatType → m R

/-- Forward the original Rational component descriptor T and original
AbstractFloat descriptor S to their selected promote_type implementation.
This method returns that exact value with its effects and errors. No fixed
Core type application or extra result assertion occurs in this body.
Source reference: base/rational.jl:232. -/
-- Source: base/rational.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_rule(::Type{Rational{T}}, ::Type{S}) where {T<:Integer,S<:AbstractFloat} = promote_type(T,S)
-- /Source
def promoteRationalFloatType {m : Type → Type} [Monad m]
    {IntegerType FloatType R : Type}
    (ops : RationalFloatPromotionOps m IntegerType FloatType R)
    (componentType : IntegerType) (floatType : FloatType) : m R :=
  ops.promoteType componentType floatType

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected typed scalar rationalize on an unfixed Real input. Keywords
represents the already-collected immutable keyword bundle described by
the language's NamedTuple/Pairs protocol; its values may contain mutable
handles. It is data passed unchanged, not an arbitrary iterable or code
implementing keyword collection. R may retain any actual selected result.
Source reference: base/rational.jl:321;
doc/src/manual/functions.md:849-860. -/
-- Source: base/rational.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Real; kvs...) = rationalize(Int, x; kvs...)
-- /Source
structure RationalizeRealDefaultOps (m : Type → Type) (X Keywords R : Type) where
  rationalize : IntTy → X → Keywords → m R

/-- Forward the original Real value and complete keyword payload to the
distinct typed scalar method with Julia Int, represented by Int64 on the
packet platform. Any selected tolerance/default evaluation, arithmetic,
allocation, error and result belongs to that callee and retains its effects.
This body introduces no default tolerance or result assertion.
Source reference: base/rational.jl:321. -/
-- Source: base/rational.jl:321-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Real; kvs...) = rationalize(Int, x; kvs...)
-- /Source
def rationalizeRealDefault {m : Type → Type} [Monad m] {X Keywords R : Type}
    (ops : RationalizeRealDefaultOps m X Keywords R)
    (x : X) (keywords : Keywords) : m R :=
  ops.rationalize .i64 x keywords

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected scalar rationalization for the unfixed Real component and
Integer target, then selected Complex construction from the actual scalar
results. Converted may tag different runtime result types and R remains
unrestricted. Keywords is the already-collected immutable NamedTuple/Pairs
payload, with any contained mutable handles retained; it is not code or an
arbitrary iterable. Julia source: base/rational.jl:322;
doc/src/manual/functions.md:849-860. -/
-- Source: base/rational.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(::Type{T}, x::Complex; kvs...) where {T<:Integer} = Complex(rationalize(T, x.re; kvs...), rationalize(T, x.im; kvs...))
-- /Source
structure RationalizeComplexOps (m : Type → Type)
    (Target Component Keywords Converted R : Type) where
  rationalize : Target → Component → Keywords → m Converted
  construct : Converted → Converted → m R

/-- Complete real-component rationalization before reading/rationalizing
the imaginary component, forwarding the original target and complete
keyword payload to each scalar call. Only then call selected Complex
construction on the two actual results in order. The source uses concrete
immutable Complex fields and adds no result assertion, normalization,
tolerance evaluation or conversion beyond those selected calls.
Source reference: base/rational.jl:322; base/complex.jl:13-16. -/
-- Source: base/rational.jl:322-322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(::Type{T}, x::Complex; kvs...) where {T<:Integer} = Complex(rationalize(T, x.re; kvs...), rationalize(T, x.im; kvs...))
-- /Source
def rationalizeComplexAs {m : Type → Type} [Monad m]
    {Target Component Keywords Converted R : Type}
    (ops : RationalizeComplexOps m Target Component Keywords Converted R)
    (target : Target) (z : JuliaLean.base.complex.Complex Component)
    (keywords : Keywords) : m R := do
  let realResult ← ops.rationalize target z.re keywords
  let imaginaryResult ← ops.rationalize target z.im keywords
  ops.construct realResult imaginaryResult

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Default complex rationalization explicitly performs the two scalar
calls with Julia Int (Int64 on the packet platform), retaining the original
keyword bundle for each. It then calls selected Complex construction on
the actual ordered results. It does not dispatch through the separate
typed-Complex wrapper or insert defaults/assertions absent from source.
The shared operations keep unfixed Real components, changing result types,
arbitrary effects and aliases. Julia source: base/rational.jl:323;
doc/src/manual/functions.md:849-860. -/
-- Source: base/rational.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Complex; kvs...) = Complex(rationalize(Int, x.re; kvs...), rationalize(Int, x.im; kvs...))
-- /Source
def rationalizeComplexDefault {m : Type → Type} [Monad m]
    {Component Keywords Converted R : Type}
    (ops : RationalizeComplexOps m IntTy Component Keywords Converted R)
    (z : JuliaLean.base.complex.Complex Component) (keywords : Keywords) : m R := do
  let realResult ← ops.rationalize .i64 z.re keywords
  let imaginaryResult ← ops.rationalize .i64 z.im keywords
  ops.construct realResult imaginaryResult

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected callees for rationalization with the declared `tol::Real`
keyword. Target represents the original Integer type descriptor, F the
documented floating conversion result, and Tol the documented Real epsilon or supplied
tolerance. Tagged carriers retain type changes. No numeric, purity or
success law is imposed; F may retain tagged AbstractFloat families and final R is unrestricted.

The entry boundary is the declared typed-keyword method: provided tolerance
values are Real, successful float follows its documented floating-result
protocol, and successful eps follows its documented Real ulp-result protocol.
Raw unknown/wrong-typed keyword sorter inputs, nonfloating float returns and
non-Real eps returns are outside that boundary; no lowering check is invented.
Source reference: base/rational.jl:324; base/float.jl:355-367,1086-1129;
doc/src/manual/functions.md:828-857; doc/src/devdocs/functions.md:126-190. -/
-- Source: base/rational.jl:324-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(::Type{T}, x::Rational; tol::Real = eps(float(x))) where {T<:Integer} = rationalize(T, x, tol)
-- /Source
structure RationalDefaultToleranceOps (m : Type → Type)
    (Target S F Tol R : Type) where
  floatValue : Rational S → m F
  epsilon : F → m Tol
  rationalize : Target → Rational S → Tol → m R

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected typed rationalization on the unfixed original Integer component
T, Rational input and collected keyword bundle. ComponentType represents the
actual method type argument corresponding to S, not a type recomputed from
fields. Keywords is the already-collected immutable NamedTuple/Pairs payload,
including mutable handles in its values. R is unrestricted.
Source reference: base/rational.jl:325; doc/src/manual/functions.md:849-860. -/
-- Source: base/rational.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Rational{T}; kvs...) where {T<:Integer} = rationalize(T, x; kvs...)
-- /Source
structure RationalizeRationalKeywordsOps (m : Type → Type)
    (ComponentType S Keywords R : Type) where
  rationalize : ComponentType → Rational S → Keywords → m R

/-- Forward the original component type argument, complete raw Rational
value and complete keywords once to the distinct typed rationalize overload.
Selected defaults, tolerance checks, conversions and errors occur inside
that callee at this call position. No identity shortcut, normalization,
typeof callback or new keyword evaluation is inserted.
Source reference: base/rational.jl:325. -/
-- Source: base/rational.jl:325-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Rational{T}; kvs...) where {T<:Integer} = rationalize(T, x; kvs...)
-- /Source
def rationalizeRationalKeywords {m : Type → Type} [Monad m]
    {ComponentType S Keywords R : Type}
    (ops : RationalizeRationalKeywordsOps m ComponentType S Keywords R)
    (componentType : ComponentType) (x : Rational S) (keywords : Keywords) : m R :=
  ops.rationalize componentType x keywords

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean
open JuliaLean.base.promotion (PType pHasAncestorName)
open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Concrete specialization of the fixed Core subtype query to parameterless
Unsigned, on the declared Integer-target domain. Datatypes follow their
actual nominal superchain, unions require both arms, and left UnionAlls bind
variable identities. A bound variable uses its upper bound; a free variable
is a singleton and does not subtype Unsigned. Contained datatype parameters
do not enter matching because the fixed RHS has no parameters.

The metadata projection has actual canonical names/superchains and faithful
TypeVar identities. Internal TypeApp/Intersect are not admitted runtime static
parameters. TypeEq/TypeEgal instances are type objects, outside Integer.
Core evidence: src/subtype.c:1250-1258,1271-1320,1901-2121,3666-4027;
TypeEgal validation src/jltypes.c:3294-3311. This is not generic pSubtype.
Source reference: base/rational.jl:327. -/
-- Source: base/rational.jl:326-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function rationalize(::Type{T}, x::Rational, tol::Real) where {T<:Integer}
--     T<:Unsigned && x < 0 && __throw_negate_unsigned()
--     if !hastypemax(T) || (typemin(T) ≤ x.num ≤ typemax(T) && x.den ≤ typemax(T))
--         return Rational{T}(x)
--     end
--     isfinite(float(x)) && tol ≥ eps(float(x))/2 || throw(InexactError(:rationalize, Rational{T}, x))
--     return rationalize(T, float(x), tol)
-- end
-- /Source
def integerTargetUnsignedProjection (bound : List Nat) : PType → Bool
  | .bottom => true
  | target@(.data ..) => pHasAncestorName target ⟨"Core", "Unsigned"⟩
  | .union left right =>
      integerTargetUnsignedProjection bound left &&
      integerTargetUnsignedProjection bound right
  | .unionAll (.typeVar id _) body =>
      integerTargetUnsignedProjection (id :: bound) body
  | .typeVar id upper =>
      bound.contains id && integerTargetUnsignedProjection bound upper
  | _ => false

/-- Runtime view of an admitted Integer target. original retains its complete
identity, lower bounds and custom metadata for selected callees. The PType
projection only erases data irrelevant to the fixed initial nominal query;
it must describe the same valid runtime type graph, not an arbitrary flag.
That consistency is a representation invariant, not a callee correctness law.
Source reference: base/rational.jl:326-327. -/
-- Source: base/rational.jl:326-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function rationalize(::Type{T}, x::Rational, tol::Real) where {T<:Integer}
--     T<:Unsigned && x < 0 && __throw_negate_unsigned()
--     if !hastypemax(T) || (typemin(T) ≤ x.num ≤ typemax(T) && x.den ≤ typemax(T))
--         return Rational{T}(x)
--     end
--     isfinite(float(x)) && tol ≥ eps(float(x))/2 || throw(InexactError(:rationalize, Rational{T}, x))
--     return rationalize(T, float(x), tol)
-- end
-- /Source
structure IntegerTargetView (Target : Type) where
  original : Target
  nominalProjection : PType

/-- Selected operations on unfixed target/component/tolerance types. The
hastypemax result H is unasserted and reaches its selected ! operation. Bounds,
epsilon and division can change type. Every guard retains the actual Bool
assertion, and typemax/float operations are reused at each source occurrence.
F obeys float's documented floating-result protocol, with tagged custom
AbstractFloat families; this makes final positional floating rationalize a
distinct dispatch target rather than recursion into the present Rational
method. Other selected intermediate carriers and final R are unrestricted.
Source reference: base/rational.jl:326-333; base/float.jl:355-367. -/
-- Source: base/rational.jl:326-333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function rationalize(::Type{T}, x::Rational, tol::Real) where {T<:Integer}
--     T<:Unsigned && x < 0 && __throw_negate_unsigned()
--     if !hastypemax(T) || (typemin(T) ≤ x.num ≤ typemax(T) && x.den ≤ typemax(T))
--         return Rational{T}(x)
--     end
--     isfinite(float(x)) && tol ≥ eps(float(x))/2 || throw(InexactError(:rationalize, Rational{T}, x))
--     return rationalize(T, float(x), tol)
-- end
-- /Source
structure RationalToleranceOps (m : Type → Type)
    (Target S Tol H Min Max F Epsilon Half NotBool R : Type) where
  lessThanZero : Rational S → JInt .i64 → m (TypeAssertion Bool NotBool)
  hasTypeMax : Target → m H
  logicalNot : H → m (TypeAssertion Bool NotBool)
  minimum : Target → m Min
  maximum : Target → m Max
  lowerBound : Min → S → m (TypeAssertion Bool NotBool)
  upperBound : S → Max → m (TypeAssertion Bool NotBool)
  constructTyped : Target → Rational S → m R
  floatValue : Rational S → m F
  isFinite : F → m (TypeAssertion Bool NotBool)
  epsilon : F → m Epsilon
  divideByTwo : Epsilon → JInt .i64 → m Half
  enoughTolerance : Tol → Half → m (TypeAssertion Bool NotBool)
  rationalizeFloat : Target → F → Tol → m R

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- The selected Rational constructor depends on the unfixed Integer input
type. Its complete effects, exception and actual result are retained. This
is a constructor call distinct from rationalize; it is not the wrapper's
own implementation. Julia source: base/rational.jl:334. -/
-- Source: base/rational.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Integer; kvs...) = Rational(x)
-- /Source
structure RationalizeIntegerDefaultOps (m : Type → Type) (X R : Type) where
  construct : X → m R

/-- Call selected Rational construction once on the original Integer.
The source intentionally ignores its complete already-collected immutable
keyword bundle. Keywords represents that NamedTuple/Pairs data protocol,
including any contained mutable handles; this body does not iterate it,
forward it, evaluate a tolerance or add a result assertion.
Source reference: base/rational.jl:334; doc/src/manual/functions.md:849-860. -/
-- Source: base/rational.jl:334-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- rationalize(x::Integer; kvs...) = Rational(x)
-- /Source
def rationalizeIntegerDefault {m : Type → Type} [Monad m]
    {X Keywords R : Type} (ops : RationalizeIntegerDefaultOps m X R)
    (x : X) (_keywords : Keywords) : m R :=
  ops.construct x

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected one on the unfixed admitted Integer or Complex-of-Integer input.
X may tag all admitted families and retain mutable Integer handles; R is
unrestricted because the source adds no assertion.
Source reference: base/rational.jl:383. -/
-- Source: base/rational.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- denominator(x::Union{Integer,Complex{<:Integer}}) = one(x)
-- /Source
structure IntegerLikeDenominatorOps (m : Type → Type) (X R : Type) where
  one : X → m R

/-- Invoke selected one on the complete original input. Its errors, effects
and type-changing result remain at this call. No literal one is substituted
and no component is inspected. Julia source: base/rational.jl:383. -/
-- Source: base/rational.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- denominator(x::Union{Integer,Complex{<:Integer}}) = one(x)
-- /Source
def denominatorIntegerLike {m : Type → Type} [Monad m] {X R : Type}
    (ops : IntegerLikeDenominatorOps m X R) (x : X) : m R :=
  ops.one x

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected lcm on the unfixed stored Integer denominator values. T can
be a tagged runtime-value carrier for heterogeneous Integer families when
the Complex component is an abstract Rational type. R is unrestricted.
Source reference: base/rational.jl:385. -/
-- Source: base/rational.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- denominator(z::Complex{<:Rational}) = lcm(denominator(real(z)), denominator(imag(z)))
-- /Source
structure ComplexRationalDenominatorOps (m : Type → Type) (T R : Type) where
  lcm : T → T → m R

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected numerator sign and oftype on unfixed Integer/Rational types.
Signed retains the actual sign result, including a changing runtime type;
R is unrestricted because this method adds no return assertion. The
selected oftype is a distinct callee on original Rational{S} and Signed,
not a callback implementing sign's own body or a claimed closed fallback.
Source reference: base/rational.jl:387; base/essentials.jl:718. -/
-- Source: base/rational.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sign(x::Rational) = oftype(x, sign(x.num))
-- /Source
structure RationalSignOps (m : Type → Type) (S Signed R : Type) where
  sign : S → m Signed
  oftype : Rational S → Signed → m R

/-- Read the actual numerator, complete its selected sign call, then call
selected oftype with the complete original Rational and actual result.
The known generic oftype fallback has an isa shortcut followed, if needed,
by conversion and assertion; those operations are not guessed or reordered
here, because this source call still dispatches on unfixed types. No
normalization, denominator sign adjustment or outer assertion is inserted.
Source reference: base/rational.jl:387; base/essentials.jl:718. -/
-- Source: base/rational.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- sign(x::Rational) = oftype(x, sign(x.num))
-- /Source
def signRational {m : Type → Type} [Monad m] {S Signed R : Type}
    (ops : RationalSignOps m S Signed R) (x : Rational S) : m R := do
  let signed ← ops.sign x.num
  ops.oftype x signed

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected signbit on the unfixed Integer component. R retains its
actual result type because this Rational wrapper has no Bool assertion.
Arbitrary effects, exceptions and mutable handles remain represented.
Source reference: base/rational.jl:388. -/
-- Source: base/rational.jl:388-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- signbit(x::Rational) = signbit(x.num)
-- /Source
structure RationalSignbitOps (m : Type → Type) (S R : Type) where
  signbit : S → m R

/-- Forward the actual numerator to its selected signbit method once.
The denominator is unused, and no condition check, normalization or result
assertion is added to the unannotated source body.
Source reference: base/rational.jl:388. -/
-- Source: base/rational.jl:388-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- signbit(x::Rational) = signbit(x.num)
-- /Source
def signbitRational {m : Type → Type} [Monad m] {S R : Type}
    (ops : RationalSignbitOps m S R) (x : Rational S) : m R :=
  ops.signbit x.num

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected checked_abs on the unfixed Integer numerator, then selected
unsafe_rational on its actual result and original denominator. Absolute
may change runtime type, and the final result R is unrestricted. All
selected state, errors and aliases are retained.
Source reference: base/rational.jl:390. -/
-- Source: base/rational.jl:390-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abs(x::Rational) = unsafe_rational(checked_abs(x.num), x.den)
-- /Source
structure RationalAbsOps (m : Type → Type) (S Absolute R : Type) where
  checkedAbs : S → m Absolute
  unsafeRational : Absolute → S → m R

/-- Complete the selected checked numerator absolute value before reading
the actual denominator for selected unsafe construction. Both fields come
from the original raw Rational; no denominator absolute value, checked_den,
normalization, result assertion or pure-storage shortcut is introduced.
The source's changing intermediate and final types remain explicit.
Source reference: base/rational.jl:390. -/
-- Source: base/rational.jl:390-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- abs(x::Rational) = unsafe_rational(checked_abs(x.num), x.den)
-- /Source
def absRational {m : Type → Type} [Monad m] {S Absolute R : Type}
    (ops : RationalAbsOps m S Absolute R) (x : Rational S) : m R := do
  let numerator ← ops.checkedAbs x.num
  ops.unsafeRational numerator x.den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected one, unary minus, zero and typed unsafe construction for an
unfixed Signed component type. Target is the original component type
descriptor from Rational{T}; the value carriers may retain different
runtime types and mutable handles, and R is unrestricted.
Source reference: base/rational.jl:392. -/
-- Source: base/rational.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typemin(::Type{Rational{T}}) where {T<:Signed} = unsafe_rational(T, -one(T), zero(T))
-- /Source
structure RationalSignedMinimumOps (m : Type → Type)
    (Target One Neg Zero R : Type) where
  one : Target → m One
  negate : One → m Neg
  zero : Target → m Zero
  unsafeRational : Target → Neg → Zero → m R

/-- Evaluate one(T), negate that actual result, then evaluate zero(T).
Only after these calls finish, invoke the distinct typed unsafe constructor
with the original T and both actual values. No source-absent overflow check,
normalization, native constant, conversion or return assertion is inserted.
Source reference: base/rational.jl:392. -/
-- Source: base/rational.jl:392-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typemin(::Type{Rational{T}}) where {T<:Signed} = unsafe_rational(T, -one(T), zero(T))
-- /Source
def rationalSignedMinimum {m : Type → Type} [Monad m]
    {Target One Neg Zero R : Type}
    (ops : RationalSignedMinimumOps m Target One Neg Zero R) (target : Target) : m R := do
  let unit ← ops.one target
  let numerator ← ops.negate unit
  let denominator ← ops.zero target
  ops.unsafeRational target numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected zero, one and typed unsafe construction for the Integer
fallback typemin method. Target retains the original component type
descriptor. Actual Zero/One results and final R can change runtime type;
all selected effects and errors are retained. Julia source: base/rational.jl:393. -/
-- Source: base/rational.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typemin(::Type{Rational{T}}) where {T<:Integer} = unsafe_rational(T, zero(T), one(T))
-- /Source
structure RationalIntegerMinimumOps (m : Type → Type)
    (Target Zero One R : Type) where
  zero : Target → m Zero
  one : Target → m One
  unsafeRational : Target → Zero → One → m R

/-- The Integer fallback evaluates zero(T) before one(T), then supplies
the original T and actual ordered results to typed unsafe construction.
This is the body of the declared Integer method, without adding the
separate Signed method's dispatch or assuming T is a native unsigned type.
Source reference: base/rational.jl:393. -/
-- Source: base/rational.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typemin(::Type{Rational{T}}) where {T<:Integer} = unsafe_rational(T, zero(T), one(T))
-- /Source
def rationalIntegerMinimum {m : Type → Type} [Monad m]
    {Target Zero One R : Type}
    (ops : RationalIntegerMinimumOps m Target Zero One R) (target : Target) : m R := do
  let numerator ← ops.zero target
  let denominator ← ops.one target
  ops.unsafeRational target numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected one, zero and typed unsafe construction for an unfixed
Integer component type. Target is the original type descriptor; actual
intermediate and final results, effects and errors remain unrestricted.
Source reference: base/rational.jl:394. -/
-- Source: base/rational.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typemax(::Type{Rational{T}}) where {T<:Integer} = unsafe_rational(T, one(T), zero(T))
-- /Source
structure RationalIntegerMaximumOps (m : Type → Type)
    (Target One Zero R : Type) where
  one : Target → m One
  zero : Target → m Zero
  unsafeRational : Target → One → Zero → m R

/-- Evaluate one(T) and then zero(T), retaining their actual returned
values, before selected typed unsafe construction with the original T.
No normalized infinity, constant replacement, extra conversion or return
assertion is presumed by this body. Julia source: base/rational.jl:394. -/
-- Source: base/rational.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- typemax(::Type{Rational{T}}) where {T<:Integer} = unsafe_rational(T, one(T), zero(T))
-- /Source
def rationalIntegerMaximum {m : Type → Type} [Monad m]
    {Target One Zero R : Type}
    (ops : RationalIntegerMaximumOps m Target One Zero R) (target : Target) : m R := do
  let numerator ← ops.one target
  let denominator ← ops.zero target
  ops.unsafeRational target numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Equality selected on the unfixed stored Integer denominator and the
actual Julia Int literal one. R is unrestricted: this source expression
has no Boolean assertion. Julia source: base/rational.jl:396. -/
-- Source: base/rational.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(x::Rational) = x.den == 1
-- /Source
structure RationalIsIntegerOps (m : Type → Type) (T R : Type) where
  equal : T → JInt .i64 → m R

/-- Compare the actual raw stored denominator with native Int64 one. The
numerator is neither read nor reduced; selected result/effects are retained.
Source reference: base/rational.jl:396. -/
-- Source: base/rational.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- isinteger(x::Rational) = x.den == 1
-- /Source
def isintegerRational {m : Type → Type} [Monad m] {T R : Type}
    (ops : RationalIsIntegerOps m T R) (x : Rational T) : m R :=
  ops.equal x.den (JInt.lit .i64 1)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected ispow2 on unfixed Integer components, followed by selected
bitwise & on their actual results. Predicate may tag different return
types; R is unrestricted. Neither intermediate result nor the outer result
is asserted to be Bool by this source body.
Source reference: base/rational.jl:397. -/
-- Source: base/rational.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Rational) = ispow2(x.num) & ispow2(x.den)
-- /Source
structure RationalPow2Ops (m : Type → Type) (S Predicate R : Type) where
  ispow2 : S → m Predicate
  bitAnd : Predicate → Predicate → m R

/-- Evaluate numerator ispow2, then denominator ispow2 eagerly, then
selected & with their actual values in order. A false or non-Bool first
value does not suppress the second call. Only a selected exception stops
evaluation, and no source-absent Bool check is introduced.
Source reference: base/rational.jl:397. -/
-- Source: base/rational.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ispow2(x::Rational) = ispow2(x.num) & ispow2(x.den)
-- /Source
def ispow2Rational {m : Type → Type} [Monad m] {S Predicate R : Type}
    (ops : RationalPow2Ops m S Predicate R) (x : Rational S) : m R := do
  let numerator ← ops.ispow2 x.num
  let denominator ← ops.ispow2 x.den
  ops.bitAnd numerator denominator

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected unary plus on the unfixed Integer numerator and selected
unsafe construction with its actual result and original denominator.
Positive may change runtime type, including Bool's Int64 result; R is
unrestricted and both calls retain arbitrary effects and exceptions.
Source reference: base/rational.jl:399; base/bool.jl:140. -/
-- Source: base/rational.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Rational) = unsafe_rational(+x.num, x.den)
-- /Source
structure RationalPlusOps (m : Type → Type) (S Positive R : Type) where
  plus : S → m Positive
  unsafeRational : Positive → S → m R

/-- Complete selected numerator unary plus, then call the selected unsafe
constructor with its actual result and the original raw denominator.
No identity shortcut, same-type assumption, pure storage, normalization
or return assertion is inserted. Julia source: base/rational.jl:399. -/
-- Source: base/rational.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Rational) = unsafe_rational(+x.num, x.den)
-- /Source
def plusRational {m : Type → Type} [Monad m] {S Positive R : Type}
    (ops : RationalPlusOps m S Positive R) (x : Rational S) : m R := do
  let numerator ← ops.plus x.num
  ops.unsafeRational numerator x.den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected unary minus on an unfixed Integer numerator, followed by
selected unsafe construction with its actual result and original
denominator. Negated and R may change runtime type, including Bool's
Int64-producing negation. Julia source: base/rational.jl:400;
base/bool.jl:142. -/
-- Source: base/rational.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::Rational) = unsafe_rational(-x.num, x.den)
-- /Source
structure RationalNegateOps (m : Type → Type) (S Negated R : Type) where
  negate : S → m Negated
  unsafeRational : Negated → S → m R

/-- The declared generic negation body evaluates selected numerator minus
before selected unsafe construction with the unchanged raw denominator.
It does not insert the separate BitSigned method's typemin check or the
Unsigned method's zero test, and does not claim native dispatch selects
this generic method over those overloads. Effects and actual result types
are unrestricted. Julia source: base/rational.jl:400. -/
-- Source: base/rational.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -(x::Rational) = unsafe_rational(-x.num, x.den)
-- /Source
def negateRational {m : Type → Type} [Monad m] {S Negated R : Type}
    (ops : RationalNegateOps m S Negated R) (x : Rational S) : m R := do
  let numerator ← ops.negate x.num
  ops.unsafeRational numerator x.den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Selected zero and inequality on the unfixed Unsigned component type.
Target is the original T descriptor. Zero may change runtime type, and
the actual inequality result is tagged for the source's Bool condition.
State changes, errors, non-Bool returns and mutable handles are retained.
Source reference: base/rational.jl:408-411. -/
-- Source: base/rational.jl:408-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Rational{T}) where T<:Unsigned
--     x.num != zero(T) && __throw_negate_unsigned()
--     x
-- end
-- /Source
structure RationalUnsignedNegationOps (m : Type → Type)
    (Target S Zero NotBool : Type) where
  zero : Target → m Zero
  notEqual : S → Zero → m (TypeAssertion Bool NotBool)

/-- Retain the actual numerator handle, evaluate zero(T), and apply
selected != to those actual values. The lazy condition asserts Bool.
True invokes the installed fixed unsigned-negation throw, with only an
exception-channel lift; false returns the complete original Rational.
No negation, storage, denominator check or zero-result coercion is added.
Source reference: base/rational.jl:408-411,236. -/
-- Source: base/rational.jl:408-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function -(x::Rational{T}) where T<:Unsigned
--     x.num != zero(T) && __throw_negate_unsigned()
--     x
-- end
-- /Source
def negateUnsignedRational {m : Type → Type} [Monad m]
    [MonadExceptOf ArrayError m] {Target S Zero NotBool : Type}
    (ops : RationalUnsignedNegationOps m Target S Zero NotBool)
    (target : Target) (x : Rational S) : m (Rational S) := do
  let numerator := x.num
  let zero ← ops.zero target
  let different ← assertType (← ops.notEqual numerator zero)
  if different then
    match (throwNegateUnsignedSource : Jl (Rational S)) with
    | .ok value => pure value
    | .error error => throw (.julia error)
  else
    pure x

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected wrapping unary minus on the unfixed Integer numerator,
followed by selected unsafe construction on the actual changed result
and original denominator. Negated may differ from S, as it does for Bool;
R is unrestricted and both calls retain arbitrary effects and errors.
Source reference: base/rational.jl:413; base/bool.jl:143. -/
-- Source: base/rational.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(x::Rational) = unsafe_rational(-%(x.num), x.den)
-- /Source
structure RationalWrappingNegationOps (m : Type → Type) (S Negated R : Type) where
  wrappingNegate : S → m Negated
  unsafeRational : Negated → S → m R

/-- Complete selected -% on the actual numerator before unsafe construction
with its result and the original raw denominator. This is the wrapping
operator's own body; no ordinary unsigned/Signed negation guard, checked
negation, same-type storage shortcut or return assertion is inserted.
Source reference: base/rational.jl:413. -/
-- Source: base/rational.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- -%(x::Rational) = unsafe_rational(-%(x.num), x.den)
-- /Source
def wrappingNegateRational {m : Type → Type} [Monad m] {S Negated R : Type}
    (ops : RationalWrappingNegationOps m S Negated R) (x : Rational S) : m R := do
  let numerator ← ops.wrappingNegate x.num
  ops.unsafeRational numerator x.den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

/-- Actual runtime result categories, shared by the early promoted return and
selected constructor. A constructor may return rational too; these are not
branch labels. P can be a tagged Integer-component universe retaining actual
Rational component descriptors, and Other represents non-Rational values.
Source reference: base/rational.jl:415-422. -/
-- Source: base/rational.jl:415-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function +(x::Rational, y::Rational)
--     xp, _ = promote(x, y)::NTuple{2,Rational}
--     if isinf(x) && x == y
--         return xp
--     end
--     xd, yd = divgcd(promote(x.den, y.den)...)
--     Rational(checked_add(checked_mul(x.num, yd), checked_mul(y.num, xd)), checked_mul(x.den, yd))
-- end
-- /Source
inductive RationalArithmeticValue (P Other : Type) where
  | rational (value : Rational P)
  | other (value : Other)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (assertType)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

open JuliaLean.base.abstractarray (ArrayError)
open JuliaLean.base.abstractarray.Models1Group1 (TypeAssertion assertType)

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- The two fixed operator identities from the source generator; these are
not selected numeric implementations. Julia source: base/rational.jl:451-458. -/
-- Source: base/rational.jl:451-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(x::Rational, y::Rational)
--             xd, yd = divgcd(promote(x.den, y.den)...)
--             Rational(($chop)(checked_mul(x.num,yd), checked_mul(y.num,xd)), checked_mul(x.den,yd))
--         end
--     end
-- end
-- /Source
inductive RationalRemainderOperator where
  | rem | mod
  deriving DecidableEq, BEq, Repr

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Compile-time index: public + and - select checked_add/checked_sub;
rem and mod retain their heterogeneous dispatch. The token identifies the
generated callee, not another Julia argument. Source: base/rational.jl:460-466. -/
-- Source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub), (:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(x::Rational, y::Integer)
--             unsafe_rational(($chop)(x.num, checked_mul(x.den, y)), x.den)
--         end
--     end
-- end
-- /Source
inductive RationalIntegerOperation where
  | checkedAdd
  | checkedSubtract
  | remainder
  | modulus

/-- Selected product, generated operation and unsafe construction. Separate
carriers retain actual changing types without promotion or callee laws.
Source reference: base/rational.jl:460-466. -/
-- Source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub), (:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(x::Rational, y::Integer)
--             unsafe_rational(($chop)(x.num, checked_mul(x.den, y)), x.den)
--         end
--     end
-- end
-- /Source
structure RationalIntegerScalarOps (m : Type → Type)
    (S Y Product Numerator R : Type) where
  checkedMul : S → Y → m Product
  combine : RationalIntegerOperation → S → Product → m Numerator
  unsafeRational : Numerator → S → m R

/-- Retain the original numerator, finish checked denominator/scalar product,
apply the generated operation with numerator first and product second, then
construct with its actual result and original denominator. No promotion or
same-signedness substitution. Julia source: base/rational.jl:462-464. -/
-- Source: base/rational.jl:460-466 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub), (:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(x::Rational, y::Integer)
--             unsafe_rational(($chop)(x.num, checked_mul(x.den, y)), x.den)
--         end
--     end
-- end
-- /Source
def rationalIntegerScalar {m : Type → Type} [Monad m]
    {S Y Product Numerator R : Type}
    (ops : RationalIntegerScalarOps m S Y Product Numerator R)
    (operation : RationalIntegerOperation) (x : Rational S) (y : Y) : m R := do
  let originalNumerator := x.num
  let product ← ops.checkedMul x.den y
  let numerator ← ops.combine operation originalNumerator product
  ops.unsafeRational numerator x.den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Fixed generated checked operator identities; they are not arbitrary
operator names or numeric implementations. Julia source: base/rational.jl:467-473. -/
-- Source: base/rational.jl:467-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             unsafe_rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
inductive IntegerRationalCheckedOperator where
  | add | sub
  deriving DecidableEq, BEq, Repr

/-- Selected checked multiplication, checked add/sub and unsafe construction
on unfixed Integer types. Product, Num and R retain actual heterogeneous
runtime results, with no premature promotion or type-preservation law.
Source reference: base/rational.jl:469-471; generator467-473. -/
-- Source: base/rational.jl:467-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             unsafe_rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
structure IntegerRationalCheckedOps (m : Type → Type)
    (X Y Product Num R : Type) where
  checkedMultiply : X → Y → m Product
  checkedCombine : IntegerRationalCheckedOperator → Product → X → m Num
  unsafeRational : Num → X → m R

/-- Generated addition evaluates checked_mul(x.den,y) before checked_add
with the original numerator, then unsafe construction with the unchanged
raw denominator. No assumed promotion, normalization or pure storage.
Source reference: base/rational.jl:469-471; generator467-473. -/
-- Source: base/rational.jl:467-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             unsafe_rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
def addIntegerRationalChecked {m : Type → Type} [Monad m]
    {X Y Product Num R : Type}
    (ops : IntegerRationalCheckedOps m X Y Product Num R)
    (y : Y) (x : Rational X) : m R := do
  let product ← ops.checkedMultiply x.den y
  let numerator ← ops.checkedCombine .add product x.num
  ops.unsafeRational numerator x.den

/-- Generated subtraction uses the distinct checked_sub token and preserves
product-first operand order, including any type-changing selected result.
Source reference: base/rational.jl:469-471; generator467-473. -/
-- Source: base/rational.jl:467-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:+,:checked_add), (:-,:checked_sub))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             unsafe_rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
def subtractIntegerRationalChecked {m : Type → Type} [Monad m]
    {X Y Product Num R : Type}
    (ops : IntegerRationalCheckedOps m X Y Product Num R)
    (y : Y) (x : Rational X) : m R := do
  let product ← ops.checkedMultiply x.den y
  let numerator ← ops.checkedCombine .sub product x.num
  ops.unsafeRational numerator x.den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected checked multiplication, heterogeneous rem/mod and normal
Rational construction. The fixed rem/mod identities reuse the generator
token from source453; Product/Num/R remain unrestricted runtime carriers.
In particular no common promoted type is presumed for remainder operands
or return values. Julia source: base/rational.jl:476-478; generator474-480. -/
-- Source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             Rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
structure IntegerRationalRemainderOps (m : Type → Type)
    (X Y Product Num R : Type) where
  checkedMultiply : X → Y → m Product
  remainder : RationalRemainderOperator → Product → X → m Num
  rational : Num → X → m R

/-- Generated rem evaluates the actual checked denominator product first,
then selected rem(product,x.num), then the normal selected Rational
constructor on that result and original raw denominator.
Source reference: base/rational.jl:476-478; generator474-480. -/
-- Source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             Rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
def remIntegerRational {m : Type → Type} [Monad m]
    {X Y Product Num R : Type}
    (ops : IntegerRationalRemainderOps m X Y Product Num R)
    (y : Y) (x : Rational X) : m R := do
  let product ← ops.checkedMultiply x.den y
  let numerator ← ops.remainder .rem product x.num
  ops.rational numerator x.den

/-- Generated mod preserves its fixed operator identity and actual operand
order. Normal Rational construction is retained, not replaced by unsafe
storage or an assumed normalized result. All selected effects may fail.
Source reference: base/rational.jl:476-478; generator474-480. -/
-- Source: base/rational.jl:474-480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (op,chop) in ((:rem,:rem), (:mod,:mod))
--     @eval begin
--         function ($op)(y::Integer, x::Rational)
--             Rational(($chop)(checked_mul(x.den, y), x.num), x.den)
--         end
--     end
-- end
-- /Source
def modIntegerRational {m : Type → Type} [Monad m]
    {X Y Product Num R : Type}
    (ops : IntegerRationalRemainderOps m X Y Product Num R)
    (y : Y) (x : Rational X) : m R := do
  let product ← ops.checkedMultiply x.den y
  let numerator ← ops.remainder .mod product x.num
  ops.rational numerator x.den

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected Bool-left multiplication remains open on the unfixed Rational component. The actual Bool and complete Rational retain their identities; R and effects are unrestricted.
Source reference: base/rational.jl:500. -/
-- Source: base/rational.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(y::Rational, x::Bool) = x * y
-- /Source
structure RationalBoolRightOps (m : Type → Type) (T R : Type) where
  multiply : Bool → Rational T → m R

/-- Reverse the two original arguments once and call the distinct Bool-left method. Its eager strong-zero behavior, return annotation, errors and effects belong to the selected callee; this wrapper introduces no shortcut or assertion.
Source reference: base/rational.jl:500. -/
-- Source: base/rational.jl:500-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- *(y::Rational, x::Bool) = x * y
-- /Source
def multiplyRationalBoolRight {m : Type → Type} [Monad m] {T R : Type}
    (ops : RationalBoolRightOps m T R) (y : Rational T) (x : Bool) : m R :=
  ops.multiply x y

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected exact division on unfixed Rational/Integer families. Divisor represents the admitted union, including tagged runtime Rational and Integer values and mutable handles. R remains unrestricted.
Source reference: base/rational.jl:501. -/
-- Source: base/rational.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::Rational, y::Union{Rational, Integer}) = x//y
-- /Source
structure RationalSlashUnionOps (m : Type → Type) (T Divisor R : Type) where
  exactDivide : Rational T → Divisor → m R

/-- Forward both complete original operands in their original order to the distinct // overload. No floating conversion, normalization, return assertion or extra division is introduced.
Source reference: base/rational.jl:501. -/
-- Source: base/rational.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::Rational, y::Union{Rational, Integer}) = x//y
-- /Source
def slashRationalUnion {m : Type → Type} [Monad m] {T Divisor R : Type}
    (ops : RationalSlashUnionOps m T Divisor R) (x : Rational T) (y : Divisor) : m R :=
  ops.exactDivide x y

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected exact division on an unfixed Integer and Rational component type, retaining the actual operand handles, changed result types, state and errors.
Source reference: base/rational.jl:502. -/
-- Source: base/rational.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::Integer, y::Rational) = x//y
-- /Source
structure IntegerRationalSlashOps (m : Type → Type) (X T R : Type) where
  exactDivide : X → Rational T → m R

/-- Call the distinct // method exactly once on original Integer then original Rational. No reciprocal, promotion, numeric result or source-absent assertion is substituted.
Source reference: base/rational.jl:502. -/
-- Source: base/rational.jl:502-502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- /(x::Integer, y::Rational) = x//y
-- /Source
def slashIntegerRational {m : Type → Type} [Monad m] {X T R : Type}
    (ops : IntegerRationalSlashOps m X T R) (x : X) (y : Rational T) : m R :=
  ops.exactDivide x y

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected two-argument checked_den on unfixed Integer component values. The source does not pass a type descriptor or assert a return type; R and all effects remain unrestricted.
Source reference: base/rational.jl:503. -/
-- Source: base/rational.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inv(x::Rational{T}) where {T} = checked_den(x.den, x.num)
-- /Source
structure RationalInverseOps (m : Type → Type) (T R : Type) where
  checkedDen : T → T → m R

/-- Read the actual stored denominator and numerator in that order and pass them to selected checked_den. No explicit typed constructor, ordinary division, normalization shortcut or local zero check is added.
Source reference: base/rational.jl:503. -/
-- Source: base/rational.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- inv(x::Rational{T}) where {T} = checked_den(x.den, x.num)
-- /Source
def inverseRational {m : Type → Type} [Monad m] {T R : Type}
    (ops : RationalInverseOps m T R) (x : Rational T) : m R :=
  ops.checkedDen x.den x.num

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected multiplication and addition on unfixed Rational components.
The intermediate Product and final R are unrestricted because the source
performs no assertions. Each call retains arbitrary effects and errors;
there is no fused arithmetic or rounding-law assumption.
Source reference: base/rational.jl:505. -/
-- Source: base/rational.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fma(x::Rational, y::Rational, z::Rational) = x*y+z
-- /Source
structure RationalFmaOps (m : Type → Type) (X Y Z Product R : Type) where
  multiply : Rational X → Rational Y → m Product
  add : Product → Rational Z → m R

/-- Finish selected multiplication of original x and y, then add its actual
result to original z. This explicitly retains both calls and their order,
without replacing them with a fused primitive or forcing a Rational result.
Source reference: base/rational.jl:505. -/
-- Source: base/rational.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- fma(x::Rational, y::Rational, z::Rational) = x*y+z
-- /Source
def fmaRationals {m : Type → Type} [Monad m] {X Y Z Product R : Type}
    (ops : RationalFmaOps m X Y Z Product R)
    (x : Rational X) (y : Rational Y) (z : Rational Z) : m R := do
  let product ← ops.multiply x y
  ops.add product z

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational.Models2Group10

/-- Selected equality on the unfixed two Integer component types, reused
for denominator and numerator pairs, followed by selected &. Compared tags
all actual changing comparison-result types; R is unrestricted. There is
no Bool assertion in this source body. Julia source: base/rational.jl:507. -/
-- Source: base/rational.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::Rational, y::Rational) = (x.den == y.den) & (x.num == y.num)
-- /Source
structure RationalEqualityOps (m : Type → Type) (X Y Compared R : Type) where
  equal : X → Y → m Compared
  bitAnd : Compared → Compared → m R

/-- Compare original denominators first, then original numerators eagerly,
then call selected & on the actual ordered results. False/non-Bool first
results do not suppress numerator equality; only a selected failure stops.
Raw pairs are never normalized or compared by a substituted cross product.
Source reference: base/rational.jl:507. -/
-- Source: base/rational.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(x::Rational, y::Rational) = (x.den == y.den) & (x.num == y.num)
-- /Source
def equalRationals {m : Type → Type} [Monad m] {X Y Compared R : Type}
    (ops : RationalEqualityOps m X Y Compared R)
    (x : Rational X) (y : Rational Y) : m R := do
  let denominators ← ops.equal x.den y.den
  let numerators ← ops.equal x.num y.num
  ops.bitAnd denominators numerators

end JuliaLean.base.rational.Models2Group10

namespace JuliaLean.base.rational
open JuliaLean.base.complex.Models2Group9 (SelfDispatch SelfCall)
open scoped Lean.Order

-- Source: base/rational.jl:583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def eqComplexRatFull {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {C P Q A B R : Type}
    (isreal : C → m A) (real : C → m P) (equal : P → Q → m B)
    (bitAnd : A → B → m R) (self : SelfDispatch (P × Q) (C × Q) R B)
    (z : C) (x : Q) : m R :=
  eqComplexRatMethod isreal real
    (fun re q => match self.classify (re, q) with
      | .selectedOther => equal re q
      | .inherited (nextZ, nextX) => do
          let result ← eqComplexRatFull isreal real equal bitAnd self nextZ nextX
          pure (self.embedReturn result))
    bitAnd z x
partial_fixpoint monotonicity by
  unfold eqComplexRatMethod
  dsimp only
  repeat' (first | assumption | monotonicity)

-- Source: base/rational.jl:632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def powNumberRationalFull {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {T X D R : Type}
    (divide : T → T → m D) (power : X → D → m R)
    (target : X → D → SelfCall (X × Rational T)) (x : X) (y : Rational T) : m R :=
  powNumberRationalMethod divide
    (fun base exponent => match target base exponent with
      | .selectedOther => power base exponent
      | .inherited (nextX, nextY) =>
          powNumberRationalFull divide power target nextX nextY)
    x y
partial_fixpoint monotonicity by
  unfold powNumberRationalMethod
  dsimp only
  repeat' (first | assumption | monotonicity)

-- Source: base/rational.jl:633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def powFloatRationalFull {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {T X E R : Type}
    (convert : Rational T → m E) (power : X → E → m R)
    (target : X → E → SelfCall (X × Rational T)) (x : X) (y : Rational T) : m R :=
  powFloatRationalMethod convert
    (fun base exponent => match target base exponent with
      | .selectedOther => power base exponent
      | .inherited (nextX, nextY) =>
          powFloatRationalFull convert power target nextX nextY)
    x y
partial_fixpoint monotonicity by
  unfold powFloatRationalMethod
  dsimp only
  repeat' (first | assumption | monotonicity)

-- Source: base/rational.jl:634 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def powComplexRationalFull {m : Type → Type} [Monad m]
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    {T Target One P TypeRep E Z R : Type}
    (one : Target → m One) (powerOne : One → Rational T → m P)
    (typeOf : P → TypeRep) (convert : TypeRep → Rational T → m E)
    (power : Z → E → m R)
    (selfOne : SelfDispatch (One × Rational T) (Target × Z × Rational T) R P)
    (target : Z → E → SelfCall (Target × Z × Rational T))
    (t : Target) (z : Z) (p : Rational T) : m R :=
  powComplexRationalMethod one
    (fun unit exponent => match selfOne.classify (unit, exponent) with
      | .selectedOther => powerOne unit exponent
      | .inherited (nextT, nextZ, nextP) => do
          let result ← powComplexRationalFull one powerOne typeOf convert power selfOne target
            nextT nextZ nextP
          pure (selfOne.embedReturn result))
    typeOf convert
    (fun base exponent => match target base exponent with
      | .selectedOther => power base exponent
      | .inherited (nextT, nextZ, nextP) =>
          powComplexRationalFull one powerOne typeOf convert power selfOne target nextT nextZ nextP)
    t z p
partial_fixpoint monotonicity by
  unfold powComplexRationalMethod
  dsimp only
  repeat' (first | assumption | monotonicity)

end JuliaLean.base.rational

namespace JuliaLean.NumbersCov

open JuliaLean

namespace RationalModel

open JuliaLean.IntArith.Rational

structure MathRat where
  num : Int
  den : Int
  deriving DecidableEq, Repr

structure Pair (α : Type) where
  re : α
  im : α
  deriving DecidableEq, Repr

/-- `unsafe_rational` inner and same-type outer constructors;
`base/rational.jl:14,17`. -/
def unsafeRat {t : IntTy} (num den : JInt t) : Rat t := ⟨num, den⟩

def unsafeMixed {t s} (num : JInt t) (den : JInt s) : Jl AnyRat := do
  let p := t.promote s
  let n ← JInt.convert (p.name) p num.val
  let d ← JInt.convert (p.name) p den.val
  return ⟨p, ⟨n, d⟩⟩

def checkedDenMixed {t s} (num : JInt t) (den : JInt s) : Jl AnyRat := do
  let p := t.promote s
  let n ← JInt.convert (p.name) p num.val
  let d ← JInt.convert (p.name) p den.val
  let r ← checkedDen n d
  return ⟨p, r⟩

/-- `__throw_rational_argerror_zero`; `base/rational.jl:30`. -/
def throwZero (typeName : String) : Jl α := .error (.argumentError typeName)

/-- `Bool(::Rational)` and integer conversion; `base/rational.jl:199-202`. -/
def boolOfRat {t} (x : Rat t) : Jl Bool :=
  if x.num.val = 0 && x.den.val = 1 then .ok false
  else if x.num.val = 1 && x.den.val = 1 then .ok true
  else .error (.inexactError "Bool")

def intOfRat (target : IntTy) {t} (x : Rat t) : Jl (JInt target) :=
  if x.den.val = 1 then JInt.convert (target.name) target x.num.val
  else .error (.inexactError target.name)

def numeratorIntegral (x : α) : α := x
def denominatorIntegral (one : α → α) (x : α) : α := one x

/-- Complex rational accessors; the caller supplies checked multiplication,
division and lcm exactly as Julia dispatches them; `base/rational.jl:362-367,385`. -/
def numeratorComplex (numerator denominator : α → β) (checkedMul : β → β → β)
    (div : β → β → β) (complex : β → β → γ) (real imag : α → α) (z : α)
    (commonDen : β) : γ :=
  let r := real z
  let i := imag z
  complex (checkedMul (numerator r) (div commonDen (denominator r)))
    (checkedMul (numerator i) (div commonDen (denominator i)))

def denominatorComplex (denominator : α → β) (lcm : β → β → β)
    (real imag : α → α) (z : α) : β :=
  lcm (denominator (real z)) (denominator (imag z))

/-- Observable Rational display; `base/rational.jl:156-165`. -/
def showRat (render : α → String) (isOne : α → Bool) (typeInfoRational : Bool)
    (num den : α) : String :=
  if isOne den && typeInfoRational then render num else render num ++ "//" ++ render den

/-- Binary read/write preserve numerator then denominator order;
`base/rational.jl:167-174`. -/
def readPair (read : Unit → α × α) : α × α := read ()
def writePair (write : α → α → β) (num den : α) : β := write num den

/-- Rational parsing after `split('/', limit=2)`; `base/rational.jl:175-187`.
The split primitive supplies the exact one- or two-part result. -/
def parseParts (parse : String → α) (construct : α → α → β) (parts : List String) : Option β :=
  match parts with
  | [n] => some (construct (parse n) (parse "1"))
  | n :: d :: _ =>
      let d := if d.startsWith "/" then (d.drop 1).toString else d
      some (construct (parse n) (parse d))
  | _ => none

/-- Exact complex inverse helper; `base/rational.jl:120-135`. -/
def complexExactInv (isinf : α → Bool) (zero _neg conj : Pair α → Pair α)
    (abs2 : Pair α → α) (z : Pair α) : Pair α × α :=
  let n := if isinf z.re || isinf z.im then conj (zero z) else conj z
  (n, abs2 z)

/-- Integer specialization of `_complex_exact_inv`; `base/rational.jl:129-135`. -/
def complexExactInvInt {t} (z : Pair (JInt t)) : Jl (Pair (JInt t) × JInt t) := do
  let p ← divgcd z.re z.im
  let c ← JuliaLean.IntArith.Checked.checkedMul z.re p.1
  let d ← JuliaLean.IntArith.Checked.checkedMul z.im p.2
  let den ← JuliaLean.IntArith.Checked.checkedAdd c d
  let ni ← JuliaLean.IntArith.Checked.checkedNeg p.2
  return (⟨p.1, ni⟩, den)

/-- Generic exact division by Complex; `base/rational.jl:137-152`. -/
def divByComplex (exactInv : Pair α → Pair α × β)
    (mul : γ → Pair α → δ) (ratDiv : δ → β → ε)
    (x : γ) (y : Pair α) : ε :=
  let p := exactInv y
  ratDiv (mul x p.1) p.2

def complexDivReal (ratDiv : α → β → γ) (z : Pair α) (y : β) : Pair γ :=
  ⟨ratDiv z.re y, ratDiv z.im y⟩

def complexIntDiv {t} (x y : Pair (JInt t)) : Jl (Pair (Rat t)) := do
  let p ← divgcd y.re y.im
  let c2 ← JuliaLean.IntArith.Checked.checkedMul y.re p.1
  let d2 ← JuliaLean.IntArith.Checked.checkedMul y.im p.2
  let den ← JuliaLean.IntArith.Checked.checkedAdd c2 d2
  let ac ← JuliaLean.IntArith.Checked.checkedMul x.re p.1
  let bd ← JuliaLean.IntArith.Checked.checkedMul x.im p.2
  let nr ← JuliaLean.IntArith.Checked.checkedAdd ac bd
  let bc ← JuliaLean.IntArith.Checked.checkedMul x.im p.1
  let ad ← JuliaLean.IntArith.Checked.checkedMul x.re p.2
  let nad ← JuliaLean.IntArith.Checked.checkedNeg ad
  let ni ← JuliaLean.IntArith.Checked.checkedAdd bc nad
  return ⟨← ofInts nr den, ← ofInts ni den⟩

def arrayExactDiv (broadcast : α → β → γ) (xs : α) (y : β) : γ := broadcast xs y

/-- Integer `rationalize` overload. The keyword tolerance is accepted but not
read by the Julia body; `base/rational.jl:334-342`. -/
def rationalizeInteger (t : IntTy) (x _tol : Int) : MathRat :=
  if x < t.min then ⟨-1, 0⟩
  else if t.max < x then ⟨1, 0⟩
  else ⟨x, 1⟩

def rationalizeIntegerDefault (x : Int) : MathRat := ⟨x, 1⟩

/-- Rational accessors and predicates; `base/rational.jl:360-397,641-642`. -/
def signbit {t} (x : Rat t) : Bool := x.num.val < 0
def isinteger {t} (x : Rat t) : Bool := x.den.val == 1
def iszero {t} (x : Rat t) : Bool := x.num.val == 0
def isone {t} (x : Rat t) : Bool := x.num.val == 1 && x.den.val == 1
def decompose {t} (x : Rat t) : Int × Int × Int := (x.num.val, 0, x.den.val)

def sign {t} (x : Rat t) : Rat t :=
  ⟨JInt.lit t (if x.num.val < 0 then -1 else if x.num.val > 0 then 1 else 0),
   JInt.lit t 1⟩

def ispow2 {t} (ispow2 : JInt t → Bool) (x : Rat t) : Bool :=
  ispow2 x.num && ispow2 x.den

def negUnchecked {t} (x : Rat t) : Rat t := ⟨-x.num, x.den⟩
def negWrap {t} (x : Rat t) : Rat t := ⟨-x.num, x.den⟩

/-- Explicit wrapping rational addition and subtraction; `base/rational.jl:424-449`. -/
def addWrap {t} (x y : Rat t) : Jl (Rat t) := do
  if x.den.val = 0 ∧ eq x y = true then return x
  let p ← divgcd x.den y.den
  ofInts (x.num * p.2 + y.num * p.1) (x.den * p.2)

def subWrap {t} (x y : Rat t) : Jl (Rat t) := do
  if x.den.val = 0 then
    let ny := negUnchecked y
    if eq x ny then return x
  let p ← divgcd x.den y.den
  ofInts (x.num * p.2 - y.num * p.1) (x.den * p.2)

def boolMul {t} (b : Bool) (x : Rat t) : Rat t :=
  if b then x
  else ⟨JInt.lit t 0, JInt.lit t 1⟩

def fma {t} (x y z : Rat t) : Jl (Rat t) := do
  let p ← mul x y
  add p z

/-- Promotion and widening of rational component types;
`base/rational.jl:230-234`. -/
def promoteComponent (promote : α → β → γ) (rationalType : γ → δ) (t : α) (s : β) : δ :=
  rationalType (promote t s)
def widenType (widen : α → β) (rationalType : β → γ) (t : α) : γ := rationalType (widen t)
def floatType (float : α → β) (t : α) : β := float t
def throwNegateUnsigned : Jl α := .error (.overflowError "cannot negate unsigned number")
def bottomRationalize : Jl α := .error (.methodError "rationalize")

/-- Rational/complex equality ambiguity methods; `base/rational.jl:583-584`. -/
def eqComplex (isreal : Pair α → Bool) (eq : α → β → Bool)
    (z : Pair α) (x : β) : Bool := isreal z && eq z.re x

/-- `==(::AbstractFloat,::Rational)`; `base/rational.jl:521-527`. -/
def eqFloat (isfinite : α → Bool) (countOnes : β → Nat)
    (ldexp : α → Int → α) (topBit : β → Int) (eqFloatInt : α → γ → Bool)
    (divide : γ → β → α) (eqFloat : α → α → Bool)
    (x : α) (num : γ) (den : β) : Bool :=
  if isfinite x then countOnes den == 1 && eqFloatInt (ldexp x (topBit den)) num
  else eqFloat x (divide num den)

/-- Componentwise rationalization wrappers; `base/rational.jl:320-343`. -/
def rationalizeComplex (rationalize : α → β) (z : Pair α) : Pair β :=
  ⟨rationalize z.re, rationalize z.im⟩

/-- Generic power forwarding wrappers; `base/rational.jl:628-639`. -/
def powerRationalExponent (div : α → α → β) (pow : γ → β → δ)
    (x : γ) (num den : α) : δ := pow x (div num den)
def powerBool (one : Pair α → Pair α)
    (z : Pair α) (n : Bool) : Pair α := if n then z else one z

def powerInteger (nonnegative : Int → Bool) (pow : α → Int → α)
    (inverse : α → α) (x : α) (n : Int) : α :=
  if nonnegative n then pow x n else pow (inverse x) (-n)

def convertVia (first : α → β) (second : β → γ) (x : α) : γ := second (first x)
def bigRat (big : α → β) (unsafeCtor : β → β → γ) (num den : α) : γ :=
  unsafeCtor (big num) (big den)

/-- Rational-input rationalize branch at `base/rational.jl:326-333`; booleans
are the observable results of the source range and tolerance predicates. -/
def rationalizeRat (convert : α → Jl β) (rationalizeFloat : Unit → Jl β) (x : α)
    (unsignedNegative fits toleranceSufficient : Bool) : Jl β :=
  if unsignedNegative then .error (.overflowError "cannot negate unsigned number")
  else if fits then convert x
  else if toleranceSufficient then rationalizeFloat ()
  else .error (.inexactError "rationalize")

def roundBool (targetIsInteger denominatorFalse : Bool) (convert : α → Jl β)
    (x : α) : Jl β :=
  if denominatorFalse && targetIsInteger then .error .divideError else convert x

/-- Linear rational interpolation; `base/rational.jl:644-646`. -/
def lerpi (sub mul div add : α → α → α) (j d a b : α) : α :=
  add (div (mul (sub d j) a) d) (div (mul j b) d)

/-- Rational gcd/lcm shapes; `base/rational.jl:650-661`. -/
def gcd (gcd lcm : α → α → α) (x y : α × α) : α × α :=
  (gcd x.1 y.1, lcm x.2 y.2)
def lcm (gcd lcm : α → α → α) (x y : α × α) : α × α :=
  (lcm x.1 y.1, gcd x.2 y.2)

/-- Rational gcd/lcm and extended gcd; `base/rational.jl:650-674`. -/
def gcdRat {t} (x y : Rat t) : Jl (Rat t) := do
  if (x.den.val = 0) != (y.den.val = 0) then
    throw (.argumentError "gcd finite/infinite")
  let n ← JuliaLean.IntArith.NumberTheory.gcd x.num y.num
  let d ← JuliaLean.IntArith.NumberTheory.lcm x.den y.den
  return ⟨n, d⟩

def lcmRat {t} (x y : Rat t) : Jl (Rat t) := do
  if (x.den.val = 0) != (y.den.val = 0) then
    throw (.argumentError "lcm finite/infinite")
  let n ← JuliaLean.IntArith.NumberTheory.lcm x.num y.num
  let d ← JuliaLean.IntArith.NumberTheory.gcd x.den y.den
  return ⟨n, d⟩

def idivRat {t} (x c : Rat t) : Jl (JInt t) := do
  let a ← JInt.div x.num c.num
  let b ← JInt.div c.den x.den
  return a * b

def gcdxRat {t} (x y : Rat t) : Jl (Rat t × JInt t × JInt t) := do
  let c ← gcdRat x y
  if c.num.val = 0 then return (c, JInt.lit t 0, c.num)
  if c.den.val = 0 then
    return (c, if x.den.val = 0 then JInt.lit t 1 else c.den,
      if y.den.val = 0 then JInt.lit t 1 else c.den)
  let ix ← idivRat x c
  let iy ← idivRat y c
  let g ← JuliaLean.IntArith.NumberTheory.gcdx ix iy
  return (c, g.2.1, g.2.2)

/-- `typemin` and `typemax` rational values; `base/rational.jl:392-394`. -/
def typemin (t : IntTy) : Rat t :=
  if t.signed then ⟨JInt.lit t (-1), JInt.lit t 0⟩
  else ⟨JInt.lit t 0, JInt.lit t 1⟩
def typemax (t : IntTy) : Rat t := ⟨JInt.lit t 1, JInt.lit t 0⟩

/-- Rational range `length`; `base/rational.jl:707-712`. -/
def rangeLength {t} (first last : Rat t) : Jl (JInt t) := do
  let d ← JInt.div (last.num - first.num + first.den) first.den
  return d

/-- `checked_length`; `base/rational.jl:713-720`. -/
def checkedRangeLength {t} (first last : Rat t) (empty : Bool) : Jl (JInt t) :=
  if empty then .ok (first.num - first.num)
  else do
    let d ← JuliaLean.IntArith.Checked.checkedSub last.num first.num
    let n ← JuliaLean.IntArith.Checked.checkedAdd d first.den
    JInt.div n first.den

end RationalModel

end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Rational

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows
open JuliaLean.IntArith.Rational

def m14 {t} (n d : JInt t) := RationalModel.unsafeRat n d
def m17 := @m14
def m18 {t s} (n : JInt t) (d : JInt s) := RationalModel.unsafeMixed n d
def m20 {t} (n d : JInt t) := checkedDen n d
def m27 := @m20
def m28 {t s} (n : JInt t) (d : JInt s) := RationalModel.checkedDenMixed n d
def m30 (name : String) : Jl α := RationalModel.throwZero name
def m48 {t} (n d : JInt t) := ofInts n d
def m49 {t s} (n : JInt t) (d : JInt s) := ofMixedInts n d
def m50 {t} (n : JInt t) := ofInt n
def m59 {t s} (x : JInt t) (y : JInt s) := divgcd x y
def m91 := @m48
def m93 {t} (x : Rat t) (y : JInt t) := divInt x y
def m102 {t} (x : JInt t) (y : Rat t) := intDiv x y
def m106 {t} (x y : Rat t) := div x y
def m116 (ratDiv : α → β → γ) (z : RationalModel.Pair α) y :=
  RationalModel.complexDivReal ratDiv z y
def m120 (isinf : α → Bool) (zero conj : RationalModel.Pair α → RationalModel.Pair α)
    (abs2 : RationalModel.Pair α → α) z :=
  RationalModel.complexExactInv isinf zero id conj abs2 z
def m129 := @RationalModel.complexExactInvInt
def m137 (exactInv : RationalModel.Pair α → RationalModel.Pair α × β)
    (mul : γ → RationalModel.Pair α → δ) (ratDiv : δ → β → ε) x y :=
  RationalModel.divByComplex exactInv mul ratDiv x y
def m141 {t} (x : JInt t) (y : RationalModel.Pair (JInt t)) :=
  RationalModel.complexIntDiv ⟨x, JInt.lit t 0⟩ y
def m144 := @RationalModel.complexIntDiv
def m154 (broadcast : α → β → γ) x y := RationalModel.arrayExactDiv broadcast x y
def m156 (render : α → String) (one : α → Bool) typed n d :=
  RationalModel.showRat render one typed n d
def m167 (read : Unit → α × α) := RationalModel.readPair read
def m172 (write : α → α → β) n d := RationalModel.writePair write n d
def m175 (parse : String → α) (construct : α → α → β) parts :=
  RationalModel.parseParts parse construct parts
def m190 (target : IntTy) (x : Rat s) := convertRat target x
def m193 (target : IntTy) (x : Int) : Jl (Rat target) := do
  let n ← JInt.convert (target.name) target x
  return ⟨n, JInt.lit target 1⟩
def m197 (x : Rat t) := x
def m199 := @RationalModel.boolOfRat
def m201 := @RationalModel.intOfRat
def m204 {t} (x : Rat t) := JuliaLean.Promotion.ratToF64 x
def m205 (promote : A → B → P) (convertA : P → A → C) (convertB : P → B → C)
    (div : C → C → C) (out : C → D) t s n d :=
  let p := promote t s
  out (div (convertA p n) (convertB p d))
def m211 (to32 : α → β) (to16 : β → γ) x := to16 (to32 x)
def m213 (to64 : α → β) (to16 : β → γ) x := to16 (to64 x)
def m223 := @JuliaLean.Promotion.rationalOfF64
def m224 (convert : α → β) x := convert x
def m226 (big : α → β) (unsafeCtor : β → β → γ) n d := unsafeCtor (big n) (big d)
def m228 (convert : α → β) z := convert z
def m230 (promote : α → β → γ) (ratType : γ → δ) t s := ratType (promote t s)
def m231 := @m230
def m232 (promote : α → β → γ) t s := promote t s
def m234 (widen : α → β) (ratType : β → γ) t := ratType (widen t)
def m236 : Jl α := .error (.overflowError "cannot negate unsigned number")
def m321 (rationalize : α → β) x := rationalize x
def m322 (rationalize : α → β) (z : RationalModel.Pair α) :=
  RationalModel.rationalizeComplex rationalize z
def m323 := @m322
def m324 (rationalize : α → β → γ) x tol := rationalize x tol
def m325 (rationalize : α → β) x := rationalize x
def m326 (convert : α → Jl β) (ratFloat : Unit → Jl β) x un fit tol :=
  RationalModel.rationalizeRat convert ratFloat x un fit tol
def m334 (x : Int) := RationalModel.rationalizeIntegerDefault x
def m343 : Jl α := .error (.methodError "rationalize")
def m360 (x : α) := RationalModel.numeratorIntegral x
def m361 := @numerator
def m362 (num den : α → β) (mul div : β → β → β) (complex : β → β → γ)
    (real imag : α → α) z common :=
  RationalModel.numeratorComplex num den mul div complex real imag z common
def m383 (one : α → α) x := RationalModel.denominatorIntegral one x
def m384 := @denominator
def m385 (den : α → β) (lcm : β → β → β) (real imag : α → α) z :=
  RationalModel.denominatorComplex den lcm real imag z
def m628 (nonneg : Int → Bool) (pow : α → Int → α) (inv : α → α) x n :=
  RationalModel.powerInteger nonneg pow inv x n
def m632 (div : α → α → β) (pow : γ → β → δ) x n d :=
  RationalModel.powerRationalExponent div pow x n d
def m633 := @m632
def m634 (convert : α → β) (pow : γ → β → δ) z p := pow z (convert p)
def m636 (one : RationalModel.Pair α → RationalModel.Pair α) z n :=
  RationalModel.powerBool one z n
def m637 (power : α → Int → α) (inv : α → α) x n :=
  if n ≥ 0 then power x n else power (inv x) (-n)
def m641 {t} (x : Rat t) := RationalModel.iszero x
def m642 {t} (x : Rat t) := RationalModel.isone x
def m644 (sub mul div add : α → α → α) j d a b := RationalModel.lerpi sub mul div add j d a b
def m648 (float : α → β) t := float t
def m387 {t} (x : Rat t) := RationalModel.sign x
def m388 {t} (x : Rat t) := RationalModel.signbit x
def m390 := @abs
def m392 (t : IntTy) := RationalModel.typemin t
def m393 := m392
def m394 (t : IntTy) := RationalModel.typemax t
def m396 {t} (x : Rat t) := RationalModel.isinteger x
def m397 {t} (pow2 : JInt t → Bool) (x : Rat t) := RationalModel.ispow2 pow2 x
def m399 := @pos
def m400 := @RationalModel.negUnchecked
def m402 := @neg
def m406 (name : String) : Jl α := .error (.overflowError name)
def m408 := @neg
def m413 := @RationalModel.negWrap
def m424 := @RationalModel.addWrap
def m442 := @RationalModel.subWrap
def m453 {t} (op : JInt t → JInt t → Jl (JInt t)) (x y : Rat t) :=
  do
    let p ← divgcd x.den y.den
    let a ← JuliaLean.IntArith.Checked.checkedMul x.num p.2
    let b ← JuliaLean.IntArith.Checked.checkedMul y.num p.1
    let n ← op a b
    let d ← JuliaLean.IntArith.Checked.checkedMul x.den p.2
    ofInts n d
def m462 := @withInt
def m469 := @intWith
def m476 := @intRemainder
def m482 := @mul
def m487 := @mulInt
def m491 := @intMul
def m497 := @RationalModel.boolMul
def m500 {t} (x : Rat t) b := RationalModel.boolMul b x
def m501 := @divInt
def m502 := @intDiv
def m503 := @inv
def m505 := @RationalModel.fma
def m507 := @eq
def m508 := @lt
def m510 := @le
def m514 := @eqInt
def m515 {t s} (x : JInt t) (y : Rat s) := eqInt y x
def m516 := @ltInt
def m517 := @intLt
def m518 := @leInt
def m519 := @intLe
def m521 := @RationalModel.eqFloat
def m529 (eq : α → β → Bool) x y := eq y x
def m533 (rel : α → β → γ) x y := rel x y
def m583 := @RationalModel.eqComplex
def m584 := @RationalModel.eqComplex
def m586 := @quotientInt
def m590 := @intQuotient
def m594 := @quotient
def m602 := @quotient
def m606 := @quotientMixed
def m607 := @fldMixed
def m608 := @cldMixed
def m612 {t} (x : Rat t) mode := round t x mode
def m614 := @round
def m621 := @RationalModel.roundBool
def m650 := @RationalModel.gcdRat
def m656 := @RationalModel.lcmRat
def m662 := @RationalModel.gcdxRat
def m670 := @RationalModel.idivRat
def m678 := @RationalModel.decompose
def m679 := @JuliaLean.Promotion.hashRat64
def m707 := @RationalModel.rangeLength
def m713 := @RationalModel.checkedRangeLength

end JuliaLean.NumbersCov.Rows.Rational
