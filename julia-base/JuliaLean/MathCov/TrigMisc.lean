import JuliaLean.MathCov.TrigPi

/-!
`sinc`, `cosc`, the reciprocal and inverse-reciprocal functions, `deg2rad_ext` and the
degree-based functions of `base/special/trig.jl:1217-1610` (Julia master `bbfa0ce4150`),
and `rad2deg`/`deg2rad` with their constants (`base/math.jl:213-257`).
-/

namespace JuliaLean.MathCov.TrigMisc

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathCov.Trig (nth horner DF64)
open JuliaLean.MathCov.TrigPi (Cx)

/-- `fastabs(x::Number) = abs(x)`, `fastabs(z::Complex) = abs(real(z)) + abs(imag(z))`;
`base/special/trig.jl:1217-1218`. -/
def fastabs {T : FTy} (x : FV T) : FV T := abs x
def fastabsC {T : FTy} (z : Cx T) : FV T := add (abs z.re) (abs z.im)

/-- `isinf_real(x::Real) = isinf(x)`, `isinf_real(x::Complex) = isinf(real(x)) &&
isfinite(imag(x))`, `isinf_real(x::Number) = false`; `base/special/trig.jl:1221-1223`. -/
def isinfReal {T : FTy} (x : FV T) : Bool := x.isinf
def isinfRealC {T : FTy} (z : Cx T) : Bool := z.re.isinf && z.im.isfinite
def isinfRealNumber {α : Type} (_x : α) : Bool := false

/-- `_sinc_threshold(T)`; `base/special/trig.jl:1237-1238`. -/
def sincThreshold : (T : FTy) → FV T | .f32 => sincThr32 | _ => conv sincThr64

/-- `_sinc(x::T)` for `T = Float32, Float64`; `base/special/trig.jl:1239-1240`. The
polynomial coefficients are `T(1)`, `-T(pi)^2/6`, `T(pi)^4/120`, all in `T`. -/
def sincF (T : FTy) (x : FV T) : Jl (FV T) := do
  if lt (fastabs x) (sincThreshold T) then
    let p := Trig.piT T
    let p2 := mul p p
    let c2 := neg (div p2 (ofInt T 6))
    let c4 := div (mul p2 p2) (ofInt T 120)
    return horner (mul x x) [one T, c2, c4]
  else if isinfReal x then return zero T
  else
    let s ← TrigPi.sinpi T x
    return div s (mul (Trig.piT T) x)

/-- `_sinc(x::Float16) = Float16(_sinc(Float32(x)))`; `base/special/trig.jl:1241`. -/
def sinc16 (x : FV .f16) : Jl (FV .f16) := do return conv (← sincF .f32 (conv x))

/-- `sinc(x::Number) = _sinc(float(x))` for a float `x`; `base/special/trig.jl:1234`. -/
def sinc (T : FTy) (x : FV T) : Jl (FV T) :=
  match T, x with
  | .f16, x => sinc16 x
  | T, x => sincF T x

/-- `sinc(x::Integer) = iszero(x) ? one(x) : zero(x)`; `base/special/trig.jl:1235`. -/
def sincInt (x : Int) : Int := if x == 0 then 1 else 0

/-- Generic `_sinc(x::Number) = iszero(x) ? one(x) : isinf_real(x) ? zero(x) :
sinpi(x)/(pi*x)` over a number type with its operations; `base/special/trig.jl:1236`. -/
def sincGeneric {α : Type} (iszero isinfR : α → Bool) (one0 zero0 : α → α)
    (sinpi piMul : α → α) (divα : α → α → α) (x : α) : α :=
  if iszero x then one0 x else if isinfR x then zero0 x else divα (sinpi x) (piMul x)

/-- The specialized Float32/Float64 real-or-complex `_sinc` branch, parameterized by its
arithmetic; `base/special/trig.jl:1239-1240`. -/
def sincSpecialized {α β : Type} (ltβ : β → β → Bool) (fastabs : α → β) (threshold : β)
    (poly zero quotient : α → α) (isinfReal : α → Bool) (x : α) : α :=
  if ltβ (fastabs x) threshold then poly x else if isinfReal x then zero x else quotient x

/-- `_sinc(x::ComplexF16) = ComplexF16(_sinc(ComplexF32(x)))`;
`base/special/trig.jl:1242`. -/
def sincComplex16 {α β : Type} (convert32 : α → β) (convert16 : β → α)
    (sinc32 : β → β) (x : α) : α := convert16 (sinc32 (convert32 x))

/-- `_cosc_generic(x) = (pi_x*cospi(x)-sinpi(x))/(pi_x*x)` with `pi_x = pi*x`;
`base/special/trig.jl:1255-1258`. -/
def coscGeneric (T : FTy) (x : FV T) : Jl (FV T) := do
  let piX := mul (Trig.piT T) x
  let c ← TrigPi.cospi T x
  let s ← TrigPi.sinpi T x
  return div (sub (mul piX c) s) (mul piX x)

/-- `_cos_cardinal_eval(x, polynomials)` with the nested `choose_poly` for 2 and 4
polynomials; `base/special/trig.jl:1333-1366`. `pols` lists `(bound, coefficients)`. -/
def choosePoly {T : FTy} (a : FV T) (pols : List (FV T × List (FV T))) : List (FV T) :=
  match pols with
  | [(b1, p0), (_, p1)] => if le a b1 then p0 else p1
  | [(b1, p0), (b2, p1), (b3, p2), (_, p3)] =>
    if le a b2 then (if le a b1 then p0 else p1) else (if le a b3 then p2 else p3)
  | _ => []

def cosCardinalEval (T : FTy) (x : FV T) (pols : List (FV T × List (FV T))) : Jl (FV T) :=
  let a := abs x
  match pols.getLast? with
  | some (bEnd, _) =>
    if le a bEnd then .ok (mul x (horner (mul x x) (choosePoly a pols)))
    else if x.isinf then .ok (zero T)
    else coscGeneric T x
  | none => if x.isinf then .ok (zero T) else coscGeneric T x

/-- Pairs `(b, p)` from the flattened `_cosc_f32`/`_cosc_f64` tables. -/
def pairs {T : FTy} (n : Nat) : List (FV T) → List (FV T × List (FV T))
  | [] => []
  | b :: rest => (b, rest.take n) :: pairs n (rest.drop n)
termination_by l => l.length
decreasing_by simp; omega

/-- `_cosc(x::Union{Float32, Float64})`; `base/special/trig.jl:1384-1391`. -/
def coscF (T : FTy) (x : FV T) : Jl (FV T) :=
  match T with
  | .f32 => cosCardinalEval .f32 x (pairs 4 cosc32)
  | .f64 => cosCardinalEval .f64 x (pairs 6 cosc64)
  | .f16 => .ok x

/-- `_cosc(x::Float16) = Float16(_cosc(Float32(x)))`; `cosc(x::Number) = _cosc(float(x))`;
`base/special/trig.jl:1254,1401`. -/
def cosc (T : FTy) (x : FV T) : Jl (FV T) :=
  match T, x with
  | .f16, x => do return conv (← coscF .f32 (conv x))
  | T, x => coscF T x

/-- The `ComplexF32` and `ComplexF64` `_cosc` branch, parameterized by complex arithmetic;
`base/special/trig.jl:1395-1400`. -/
def coscComplex {α β : Type} (ltβ : β → β → Bool) (fastabs : α → β) (threshold : β)
    (poly generic zero : α → α) (isinfReal : α → Bool) (x : α) : α :=
  if ltβ (fastabs x) threshold then poly x else if isinfReal x then zero x else generic x

/-- `_cosc(x::ComplexF16) = ComplexF16(_cosc(ComplexF32(x)))`;
`base/special/trig.jl:1402`. -/
def coscComplex16 {α β : Type} (convert32 : α → β) (convert16 : β → α)
    (cosc32 : β → β) (x : α) : α := convert16 (cosc32 (convert32 x))

/-- The generic `_cosc(x::Number)` series for `|x| < 0.5`, otherwise `_cosc_generic`;
`base/special/trig.jl:1259-1281`, over a number type with the needed operations.
`fuel` bounds the series loop. -/
def coscSeries {α : Type} (pi : α) (mulα divα addα : α → α → α) (negα : α → α) (ofNat : Int → α)
    (iszero : α → Bool) (leα : α → α → Bool) (fabs eps : α → α) : Nat → α → α → α → α → Nat → α
  | 0, s, _, _, _, _ => mulα pi s
  | fuel + 1, s, term, pi2x2, e, n =>
    let n := n + 1
    let term := mulα term (divα pi2x2 (mulα (ofNat (1 - 2 * n)) (ofNat (2 * n - 2))))
    let ds := divα term (ofNat (1 + 2 * n))
    let s := addα s ds
    if leα (fabs ds) e then mulα pi s
    else coscSeries pi mulα divα addα negα ofNat iszero leα fabs eps fuel s term pi2x2 e n

/-- `sec(z) = inv(cos(z))`, `csc`, `cot`, the hyperbolic and degree versions, for any
function `f` of the generated loop; `base/special/trig.jl:1404-1433`. -/
def recipOf {α : Type} (f : α → Jl α) (invα : α → α) (z : α) : Jl α := do
  return invα (← f z)

/-- `asec(y) = acos(inv(y))` and the other inverse functions of the generated loop;
`base/special/trig.jl:1435-1452`. -/
def invArgOf {α β : Type} (f : α → β) (invα : α → α) (y : α) : β := f (invα y)

/-- `deg2rad_ext(x::Float64)`: `x*π/180` as a double-double; `base/special/trig.jl:1456-1469`. -/
def deg2radExt64 (x : FV .f64) : DF64 :=
  let m := nth deg2radExt 0
  let mHi := nth deg2radExt 1
  let mLo := nth deg2radExt 2
  let u := mul (nth deg2radExt 3) x
  let xHi := sub u (sub u x)
  let xLo := sub x xHi
  let yHi := mul m x
  let yLo := add (mul xHi mLo) (add (mul xLo mHi) (add (sub (mul xHi mHi) yHi) (mul xLo mLo)))
  ⟨yHi, yLo⟩

/-- `deg2rad(z::AbstractFloat) = z * _pi_over_180(z)`; `base/math.jl:216-223,253`. -/
def deg2rad (T : FTy) (z : FV T) : FV T :=
  match T with
  | .f16 => mul z deg2rad16
  | .f32 => mul z deg2rad32
  | .f64 => mul z deg2rad64

/-- `rad2deg(z::AbstractFloat) = z * _180_over_pi(z)`; `base/math.jl:213-222,238`. -/
def rad2deg (T : FTy) (z : FV T) : FV T :=
  match T with
  | .f16 => mul z rad2deg16
  | .f32 => mul z rad2deg32
  | .f64 => mul z rad2deg64

/-- `_180_over_pi(z) = 180 / oftype(z, pi)`, `_pi_over_180(z) = oftype(z, pi) / 180` for a
float type without a specialised constant; `base/math.jl:213-218`. -/
def oneEightyOverPi (T : FTy) : FV T := div (ofInt T 180) (Trig.piT T)
def piOverOneEighty (T : FTy) : FV T := div (Trig.piT T) (ofInt T 180)

/-- `deg2rad_ext(x::Float32) = DoubleFloat32(deg2rad(Float64(x)))`, `deg2rad_ext(x::Float64)`;
`base/special/trig.jl:1456-1470`. The result is the kernel argument. -/
def deg2radExt (T : FTy) (x : FV T) : DF64 :=
  match T with
  | .f32 => ⟨deg2rad .f64 (conv x), zero .f64⟩
  | _ => deg2radExt64 (conv x)

/-- `sin_kernel`/`cos_kernel` on a `deg2rad_ext` argument. -/
def sinKd (T : FTy) (y : DF64) : FV T := Trig.sinK T y
def cosKd (T : FTy) (y : DF64) : FV T := Trig.cosK T y

/-- `sign(x)` of a float. -/
abbrev signF {T : FTy} (x : FV T) : FV T := Trig.signF x

/-- `sind(x::Real)` for `x::T`, `T = Float32, Float64`; `base/special/trig.jl:1473-1502`.
`rem(x, 360)` is the float remainder. -/
def sind (T : FTy) (x : FV T) : Jl (FV T) :=
  if x.isinf then Trig.finiteDomainError "sind"
  else if x.isnan then .ok x
  else
    let c (n : Int) : FV T := ofInt T n
    let rx := copysign (FloatIntCov.Float.rem x (c 360)) x
    let arx := abs rx
    if eq rx (zero T) then .ok rx
    else if lt arx (c 45) then .ok (sinKd T (deg2radExt T rx))
    else if le arx (c 135) then .ok (copysign (cosKd T (deg2radExt T (sub (c 90) arx))) rx)
    else if eq arx (c 180) then .ok (copysign (zero T) rx)
    else if lt arx (c 225) then .ok (sinKd T (deg2radExt T (mul (sub (c 180) arx) (signF rx))))
    else if le arx (c 315) then .ok (neg (copysign (cosKd T (deg2radExt T (sub (c 270) arx))) rx))
    else .ok (sinKd T (deg2radExt T (sub rx (copysign (c 360) rx))))

/-- `cosd(x::Real)`; `base/special/trig.jl:1504-1528`. -/
def cosd (T : FTy) (x : FV T) : Jl (FV T) :=
  if x.isinf then Trig.finiteDomainError "cosd"
  else if x.isnan then .ok x
  else
    let c (n : Int) : FV T := ofInt T n
    let rx := abs (FloatIntCov.Float.rem x (c 360))
    if le rx (c 45) then .ok (cosKd T (deg2radExt T rx))
    else if lt rx (c 135) then .ok (sinKd T (deg2radExt T (sub (c 90) rx)))
    else if le rx (c 225) then .ok (neg (cosKd T (deg2radExt T (sub (c 180) rx))))
    else if lt rx (c 315) then .ok (sinKd T (deg2radExt T (sub rx (c 270))))
    else .ok (cosKd T (deg2radExt T (sub (c 360) rx)))

/-- `tand(x::Real) = sind(x) / cosd(x)`; `base/special/trig.jl:1530`. -/
def tand (T : FTy) (x : FV T) : Jl (FV T) := do return div (← sind T x) (← cosd T x)

/-- `sincosd(x) = (sind(x), cosd(x))`; `base/special/trig.jl:1543`. -/
def sincosd (T : FTy) (x : FV T) : Jl (FV T × FV T) := do return (← sind T x, ← cosd T x)

/-- `sind(x::Float16)` and the other two: `isinf(x) ? throw_finite_domainerror(...) :
Float16(f(Float32(x)))`; `base/special/trig.jl:1604-1606`. -/
def degF16 (f : FV .f32 → Jl (FV .f32)) (name : String) (x : FV .f16) : Jl (FV .f16) :=
  if x.isinf then Trig.finiteDomainError name else do return conv (← f (conv x))

/-- `($fd)(x) = ($f)(deg2rad.(x))`, the generic fallback of `sind`, `cosd`, `tand`;
`base/special/trig.jl:1549-1566`. -/
def viaDeg2rad {α β : Type} (f : α → β) (d2r : α → α) (x : α) : β := f (d2r x)

/-- `asind(x) = rad2deg.(asin(x))` and the other generated inverse-degree functions,
`atand(y)`, `atand(y, x)`; `base/special/trig.jl:1568-1601`. -/
def viaRad2deg {α β : Type} (f : α → Jl β) (r2d : β → β) (x : α) : Jl β := do return r2d (← f x)

/-- `asind(x::Float16)` etc.: `Float16(f(Float32(x)))`; `base/special/trig.jl:1607-1610`. -/
def invDegF16 (f : FV .f32 → Jl (FV .f32)) (x : FV .f16) : Jl (FV .f16) := do
  return conv (← f (conv x))

/-- `sincosd(::Missing) = (missing, missing)`; `base/special/trig.jl:1547`. -/
def sincosdMissing : Option Unit × Option Unit := (none, none)

end JuliaLean.MathCov.TrigMisc
