import JuliaLean.Promotion.Compare
import JuliaLean.IntArith.Rational

/-!
`Rational`/`AbstractFloat` comparison and conversion at master `bbfa0ce4150`:
`decompose` (`base/float.jl:747-778`), `==`, `<`, `<=`, `cmp`
(`base/rational.jl:521-574`), `isequal`/`isless` (`base/operators.jl:201-242`), and
`Tf(x::Rational)` (`base/rational.jl:195-207`).
-/

namespace JuliaLean.Promotion

open JuliaLean.Float
open JuliaLean.IntArith.Rational

/-- `decompose(x)` for an `IEEEFloat`; `base/float.jl:747-778`. -/
def decomposeF {f : Fmt} (x : Fl f) : Int × Int × Int :=
  if x.isnan then (0, 0, 0)
  else if x.isinf then (if x.signbit then -1 else 1, 0, 0)
  else
    let e := x.expField
    let s : Int := x.frac + if e == 0 then 0 else 2 ^ f.sb
    (s, (e : Int) - (f.bias + f.sb) + (if e == 0 then 1 else 0), if x.signbit then -1 else 1)

/-- Number of binary digits of `|n|`, `ndigits0z(n, 2)`; `base/intfuncs.jl:764-772`. -/
def ndigits2 (n : Int) : Int := if n == 0 then 0 else (n.natAbs.log2 + 1 : Nat)

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

/-- `cmp(a, b)` on integers, `base/operators.jl:537`. -/
def icmp (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

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

/-- `isless(x::AbstractFloat, y::Real)`; `base/operators.jl:242`. -/
def islessFR {f : Fmt} {t : IntTy} (x : Fl f) (y : Rat t) : Bool :=
  (!x.isnan && (x.signbit && !signbitR y)) || ltFR x y

/-- `isless(x::Real, y::AbstractFloat)`; `base/operators.jl:241`. -/
def islessRF {f : Fmt} {t : IntTy} (x : Rat t) (y : Fl f) : Bool :=
  (y.isnan || (signbitR x && !y.signbit)) || ltRF x y

end JuliaLean.Promotion
