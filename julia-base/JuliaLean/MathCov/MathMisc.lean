import JuliaLean.MathCov.TrigMisc
import JuliaLean.MathFuncs.Basic

/-!
The remaining methods of `base/math.jl` at Julia master `bbfa0ce4150`: the error
helpers, the complex `evalpoly`, `log(b, x)`, `nan_dom_err`, `sqrt`, `fourthroot`, the
`hypot` family, the `atan` and `muladd` fallbacks, and the method-generating loops for
`Float16`, `ComplexF16`, `Real` and `Missing` arguments.
-/

namespace JuliaLean.MathCov.MathMisc

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathCov.TrigPi (Cx)

/-- `throw_complex_domainerror(f, x)`, `throw_complex_domainerror_neg1(f, x)`,
`throw_finite_domainerror(f, x)` and `throw_exp_domainerror(x)` all throw `DomainError`;
`base/math.jl:32-48`. -/
def throwComplexDomainError {α : Type} (f : String) : Jl α := .error (.domainError f)
def throwComplexDomainErrorNeg1 {α : Type} (f : String) : Jl α := .error (.domainError f)
def throwFiniteDomainError {α : Type} (f : String) : Jl α := .error (.domainError f)
def throwExpDomainError {α : Type} : Jl α := .error (.domainError "Exponentiation yielding a complex result requires a complex argument.")

/-- `_evalpoly(x, p)` for a real `x` and coefficient vector `p`; `base/math.jl:90-98`.
`p[end]` of an empty vector throws `BoundsError`. The `@horner` macro expands to
`invoke(evalpoly, Tuple{Any, Tuple}, x, p)`, the same Horner loop (`base/math.jl:157-160`),
and `@evalpoly(z, p...)` to `evalpoly(z, (p...,))` (`base/math.jl:189-192`). -/
def evalpolyReal {T : FTy} (x : FV T) (p : List (FV T)) : Jl (FV T) :=
  if p.isEmpty then .error .boundsError else .ok (Exp.horner x p)

/-- `muladd(z::Complex, x::Real, y::Real)` and `muladd(x::Real, z::Complex, y::Real)`:
`Complex(muladd(real(z), x, y), imag(z)*x)`; `base/complex.jl`. -/
def muladdCR {T : FTy} (a : FV T) (z : Cx T) (b : FV T) : Cx T := ⟨muladd z.re a b, mul z.im a⟩

/-- `_evalpoly(z::Complex, p)` for real coefficients (the Goertzel-style recurrence);
`base/math.jl:130-148`. The generated `evalpoly(z::Complex, p::Tuple)` (`base/math.jl:100-124`)
unrolls the same recurrence, and `evalpoly(z::Complex, p::Tuple{<:Any}) = p[1]`
(`base/math.jl:125`). -/
def evalpolyComplex {T : FTy} (z : Cx T) (p : List (FV T)) : Jl (Cx T) :=
  match p.reverse with
  | [] => .error .boundsError
  | [c] => .ok ⟨c, zero T⟩
  | a :: b :: rest =>
    let x := z.re
    let y := z.im
    let r := add x x
    let s := muladd x x (mul y y)
    let (a, b) := rest.foldl (fun (ab : FV T × FV T) pi =>
      let ai := ab.1
      (muladd r ai ab.2, muladd (neg s) ai pi)) (a, b)
    .ok (muladdCR a z b)

/-- `evalpoly(z::Complex, p::Tuple{<:Any}) = p[1]`, a real coefficient as is. -/
def evalpolyComplex1 {T : FTy} (_z : Cx T) (c : FV T) : FV T := c

/-- `rad2deg(z::Real) = rad2deg(float(z))`, `deg2rad(z::Real)`, and for other numbers
`rad2deg(z) = (z/pi)*180`, `deg2rad(z) = (z*pi)/180`; `base/math.jl:254-257`. -/
def rad2degNumber {T : FTy} (z : Cx T) : Cx T :=
  let p := Trig.piT T
  ⟨mul (div z.re p) (ofInt T 180), mul (div z.im p) (ofInt T 180)⟩
def deg2radNumber {T : FTy} (z : Cx T) : Cx T :=
  let p := Trig.piT T
  ⟨div (mul z.re p) (ofInt T 180), div (mul z.im p) (ofInt T 180)⟩

/-- `log(b::T, x::T) = log(x)/log(b)` for a float type with its `log`; `base/math.jl:259`.
`log(b::Number, x::Number) = log(promote(b,x)...)` (`base/math.jl:304`). -/
def logBase {α : Type} (logf : α → Jl α) (divα : α → α → α) (b x : α) : Jl α := do
  return divα (← logf x) (← logf b)

/-- `nan_dom_err(out, x)`; `base/math.jl:399`. -/
def nanDomErr {T S : FTy} (out : FV T) (x : FV S) : Jl (FV T) :=
  if out.isnan && !x.isnan then .error (.domainError "NaN result for non-NaN input.") else .ok out

/-- `sqrt(x::IEEEFloat)`; `base/math.jl:629-632`. -/
def sqrt {T : FTy} (x : FV T) : Jl (FV T) :=
  if lt x (zero T) then throwComplexDomainError "sqrt" else .ok (sqrtLlvm x)

/-- `fourthroot(x::Number) = sqrt(sqrt(x))`; `base/math.jl:685`. -/
def fourthroot {T : FTy} (x : FV T) : Jl (FV T) := do sqrt (← sqrt x)

/-- `hypot(x::Number) = abs(float(x))`; `base/math.jl:729`. -/
def hypot1 {T : FTy} (x : FV T) : FV T := abs x

/-- `_hypot(x, y)` for real floats `x`, `y` of type `T` on a machine with fma;
`base/math.jl:732-786`. -/
def hypotGeneric {T : FTy} (x y : FV T) : FV T := Id.run do
  let mut axu := abs x
  let ayu := abs y
  let mut ax := axu
  let mut ay := ayu
  if ax.isinf || ay.isinf then return inf T
  if lt ax ay then
    axu := ayu
    let t := ax
    ax := ay
    ay := t
  let epsT' := epsT T
  if le ay (mul ax (sqrtLlvm (div epsT' (ofInt T 2)))) then return axu
  let mut scale := mul epsT' (sqrtLlvm (floatminT T))
  if lt (sqrtLlvm (div (floatmaxT T) (ofInt T 2))) ax then
    ax := mul ax scale
    ay := mul ay scale
    scale := div (one T) scale
  else if lt ay (sqrtLlvm (floatminT T)) then
    ax := div ax scale
    ay := div ay scale
  else scale := one T
  let mut h := sqrtLlvm (muladd ax ax (mul ay ay))
  let hsquared := mul h h
  let axsquared := mul ax ax
  h := sub h (div (sub (add (fma (neg ay) ay (sub hsquared axsquared)) (fma h h (neg hsquared)))
    (fma ax ax (neg axsquared))) (mul (ofInt T 2) h))
  return mul (mul h scale) (one T)

/-- `_hypot(x::Float32, y::Float32)`; `base/math.jl:789-795`. -/
def hypot32 (x y : FV .f32) : FV .f32 :=
  if x.isinf || y.isinf then inf .f32
  else
    let x' : FV .f64 := conv x
    let y' : FV .f64 := conv y
    conv (sqrtLlvm (muladd x' x' (mul y' y')))

/-- `_hypot(x::Float16, y::Float16)`; `base/math.jl:796-802`. -/
def hypot16 (x y : FV .f16) : FV .f16 :=
  if x.isinf || y.isinf then inf .f16
  else
    let x' : FV .f32 := conv x
    let y' : FV .f32 := conv y
    conv (sqrtLlvm (muladd x' x' (mul y' y')))

/-- `abs(z::Complex) = hypot(real(z), imag(z))` for `ComplexF32`. -/
def absC32 (z : Cx .f32) : FV .f32 := hypot32 z.re z.im

/-- `_hypot(x::ComplexF16, y::ComplexF16) = Float16(_hypot(ComplexF32(x), ComplexF32(y)))`,
where the complex generic `_hypot` starts from `abs` of each argument; `base/math.jl:803`. -/
def hypotC16 (x y : Cx .f16) : FV .f16 :=
  conv (hypotGeneric (absC32 ⟨conv x.re, conv x.im⟩) (absC32 ⟨conv y.re, conv y.im⟩))

/-- `hypot(x, y)` on the two-argument IEEE method of the promoted type;
`base/math.jl:730` with `_hypot` at `base/math.jl:732,789,796`. -/
def hypot2 : (T : FTy) → FV T → FV T → FV T
  | .f16, x, y => hypot16 x y
  | .f32, x, y => hypot32 x y
  | .f64, x, y => of64 (MathFuncs.hypot (to64 x) (to64 y))

/-- `hypot(x::Number, y::Number) = _hypot(float.(promote(x, y))...)` for floats of two
formats: both are converted (exactly) to the wider one; `base/math.jl:730`. -/
def promoteTy (T S : FTy) : FTy :=
  match T, S with
  | .f64, _ | _, .f64 => .f64
  | .f32, _ | _, .f32 => .f32
  | _, _ => .f16
def hypotMixed {T S : FTy} (x : FV T) (y : FV S) : FV (promoteTy T S) :=
  hypot2 (promoteTy T S) (conv x) (conv y)

/-- `_hypot(x::NTuple{N,<:Number})` for real floats; `base/math.jl:805-814`. -/
def hypotTupleGeneric {T : FTy} (xs : List (FV T)) : FV T :=
  let maxabs := xs.foldl (fun m v => if lt m (abs v) || (abs v).isnan then abs v else m) (zero T)
  if maxabs.isnan && xs.any (·.isinf) then inf T
  else if maxabs.iszero || maxabs.isinf then maxabs
  else mul maxabs (sqrtLlvm (xs.foldl (fun s v => let q := div v maxabs; add s (mul q q)) (zero T)))

/-- `_hypot(x::NTuple{N,<:IEEEFloat})`, with `add_fast` an ordinary addition (it is
`add_float_fast`, whose only licence is reassociation); `base/math.jl:816-828`. -/
def hypotTupleIEEE {T : FTy} (xs : List (FV T)) : FV T :=
  let xs := xs.map abs
  if xs.any (fun v => eq v (inf T)) then inf T
  else
    let maxabs : FV T := Fl.ofBits (xs.foldl (fun m v => Nat.max m v.toBits) 0)
    if !(lt (zero T) maxabs) then maxabs
    else
      let (scale, invscale) := Bits.scaleinv maxabs
      match xs.map (fun v => let q := mul v invscale; mul q q) with
      | [] => maxabs
      | q :: qs => mul scale (sqrtLlvm (qs.foldl add q))

/-- `add_fast(x, y)`; `base/math.jl:826`. -/
def addFast {T : FTy} (x y : FV T) : FV T := add x y

/-- `atan(y::Real, x::Real) = atan(promote(float(y), float(x))...)`; `base/math.jl:830`. -/
def atanMixed {T S : FTy} (y : FV T) (x : FV S) : FV (promoteTy T S) :=
  match promoteTy T S with
  | .f16 => conv (Trig.atan2 .f32 (conv y) (conv x))
  | U => Trig.atan2 U (conv y) (conv x)

/-- `atan(y::T, x::T) where {T<:AbstractFloat} = Base.no_op_err("atan", T)` for a float type
without its own method; `base/math.jl:831`. -/
def atanNoOp {α : Type} : Jl α := .error (.methodError "atan")

/-- `muladd(x, y, z) = x*y+z` for a fixed-width integer type; `base/math.jl:1265`. -/
def muladdInt {t : IntTy} (x y z : JInt t) : JInt t := JInt.wrap t (wrapInt t (x.val * y.val) + z.val)

/-- Generic `muladd(x,y,z) = x*y+z`; `base/math.jl:1265`. -/
def muladdGeneric {α : Type} (mul add : α → α → α) (x y z : α) : α := add (mul x y) z

/-- `$func(a::Float16) = Float16($func(Float32(a)))` for the fifteen functions of the loop;
`base/math.jl:1306-1312`. -/
def viaF32 (f : FV .f32 → Jl (FV .f32)) (a : FV .f16) : Jl (FV .f16) := do
  return conv (← f (conv a))

/-- `$func(a::ComplexF16) = ComplexF16($func(ComplexF32(a)))`; `base/math.jl:1310,1315`. -/
def viaC32 (f : Cx .f32 → Jl (Cx .f32)) (a : Cx .f16) : Jl (Cx .f16) := do
  let r ← f ⟨conv a.re, conv a.im⟩
  return ⟨conv r.re, conv r.im⟩

/-- `atan(a::Float16, b::Float16) = Float16(atan(Float32(a), Float32(b)))`; `base/math.jl:1319`. -/
def atan16 (a b : FV .f16) : FV .f16 := conv (Trig.atan2 .f32 (conv a) (conv b))

/-- `sincos(a::Float16) = Float16.(sincos(Float32(a)))`; `base/math.jl:1320`. -/
def sincos16 (f : FV .f32 → Jl (FV .f32 × FV .f32))
    (a : FV .f16) : Jl (FV .f16 × FV .f16) := do
  let r ← f (conv a)
  return (conv r.1, conv r.2)

/-- `($f)(x::Real)`: `xf = float(x)`; a float `x` already of type `float(x)` has no method
(`MethodError`); otherwise `f(xf)`; `base/math.jl:1326-1330`. -/
def realFallback {α β : Type} (float : α → β) (isFloat : Bool) (f : β → Jl β) (x : α) : Jl β :=
  if isFloat then .error (.methodError "f") else f (float x)

/-- `f(::Missing) = missing` and the two-argument `Missing` methods; `base/math.jl:1331-1337`. -/
def missing1 {α : Type} (_x : Option α) : Option α := none
def missing2 {α β γ : Type} (_x : Option α) (_y : Option β) : Option γ := none

/-- `exp2(x::AbstractFloat) = 2^x` and `exp10(x::AbstractFloat) = 10^x` for a float type with
power `pow`; `base/math.jl:1340-1341`. -/
def exp2Abstract {α : Type} (two : α) (pow : α → α → α) (x : α) : α := pow two x
def exp10Abstract {α : Type} (ten : α) (pow : α → α → α) (x : α) : α := pow ten x

/-- `mod2pi(x) = rem2pi(x, RoundDown)`; `base/math.jl:1241`. -/
def mod2pi {T : FTy} (x : FV T) : FV T :=
  match T, x with
  | .f64, x => Special.rem2pi64 x .Down
  | _, x => Special.rem2piNarrow x .Down

end JuliaLean.MathCov.MathMisc
