import JuliaLean.base.floatfuncs
import JuliaLean.base.special.rem_pio2
import JuliaLean.base.float
import JuliaLean.base.special.exp
import JuliaLean.base.range

/-!
# Source-mirrored model of `base/special/trig.jl`

Typed Float32/Float64 kernels and typed models of the remaining trigonometric methods. Float
operations come from the shared IEEE arithmetic model. Argument reduction is supplied by the
`rem_pio2_kernel` interface from `base/special/rem_pio2.jl`, whose documented contract returns a
quadrant and a double-double remainder, with positive quadrant for positive input and negative
quadrant for nonpositive input.
-/

namespace JuliaLean.base.special.trig

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov JuliaLean.MathCov.FP JuliaLean.MathCov.C


open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- `l[i]` (zero-based) of a constant table. -/
def nth {T : FTy} (l : List (FV T)) (i : Nat) : FV T := l.getD i (nan T)

def h64 : FV .f64 := lit .f64 0x3fe0000000000000
def one64 : FV .f64 := one .f64
def two64 : FV .f64 := ofInt .f64 2

/-- `@horner(x, c...)`, i.e. `evalpoly`; `base/math.jl:157-160`. -/
abbrev horner {T : FTy} := @Exp.horner T


/-! ## Float64 kernels, `base/special/trig.jl:68-81,134-149,234-334` -/

/-- `sin_kernel(y::DoubleFloat64)`. -/
def sinKernelD (y : DF64) : FV .f64 :=
  let y2 := mul y.hi y.hi
  let y4 := mul y2 y2
  let r := add (horner y2 [nth DS 1, nth DS 2, nth DS 3]) (mul (mul y2 y4) (horner y2 [nth DS 4, nth DS 5]))
  let y3 := mul y2 y.hi
  sub y.hi (sub (sub (mul y2 (sub (mul h64 y.lo) (mul y3 r))) y.lo) (mul y3 (nth DS 0)))

/-- `sin_kernel(y::Float64)`. -/
def sinKernel64 (y : FV .f64) : FV .f64 :=
  let y2 := mul y y
  let y4 := mul y2 y2
  let r := add (horner y2 [nth DS 1, nth DS 2, nth DS 3]) (mul (mul y2 y4) (horner y2 [nth DS 4, nth DS 5]))
  let y3 := mul y2 y
  add y (mul y3 (add (nth DS 0) (mul y2 r)))

/-- `cos_kernel(y::DoubleFloat64)`. -/
def cosKernelD (y : DF64) : FV .f64 :=
  let y2 := mul y.hi y.hi
  let y4 := mul y2 y2
  let r := add (mul y2 (horner y2 [nth DC 0, nth DC 1, nth DC 2])) (mul (mul y4 y4) (horner y2 [nth DC 3, nth DC 4, nth DC 5]))
  let halfY2 := mul h64 y2
  let w := sub one64 halfY2
  add w (add (sub (sub one64 w) halfY2) (sub (mul y2 r) (mul y.hi y.lo)))

/-- `cos_kernel(y::Float64)`. -/
def cosKernel64 (y : FV .f64) : FV .f64 :=
  let y2 := mul y y
  let y4 := mul y2 y2
  let r := add (mul y2 (horner y2 [nth DC 0, nth DC 1, nth DC 2])) (mul (mul y4 y4) (horner y2 [nth DC 3, nth DC 4, nth DC 5]))
  let halfY2 := mul h64 y2
  let w := sub one64 halfY2
  add w (add (sub (sub one64 w) halfY2) (mul y2 r))

/-- Clear the low 32 bits: `reinterpret(Float64, (reinterpret(UInt64, x) >> 32) << 32)`. -/
def clearLow (x : FV .f64) : FV .f64 := Fl.ofBits (x.toBits / 2 ^ 32 * 2 ^ 32)

/-- `tan_kernel(y::DoubleFloat64, k)`. -/
def tanKernelD (y : DF64) (k : Int) : FV .f64 :=
  let big := le (nth tanMisc64 0) (abs y.hi)
  let (yhi, ylo) :=
    if big then
      let (yhi, ylo) := if lt y.hi (zero .f64) then (neg y.hi, neg y.lo) else (y.hi, y.lo)
      (add (sub (nth tanMisc64 1) yhi) (sub (nth tanMisc64 2) ylo), zero .f64)
    else (y.hi, y.lo)
  let y2 := mul yhi yhi
  let y4 := mul y2 y2
  let r := horner y4 (tanT64.take 6)
  let v := mul y2 (horner y4 (tanT64.drop 6))
  let y3 := mul y2 yhi
  let r := add ylo (mul y2 (add (mul y3 (add r v)) ylo))
  let r := add r (mul (nth tanMisc64 3) y3)
  let px := add yhi r
  let kf : FV .f64 := ofInt .f64 k
  if big then
    mul (if y.hi.signbit then neg one64 else one64)
      (sub kf (mul two64 (sub yhi (sub (div (mul px px) (add kf px)) r))))
  else if k == 1 then px
  else
    let px0 := clearLow px
    let v := sub r (sub px0 yhi)
    let a := div (neg one64) px
    let t := clearLow a
    let s := add one64 (mul t px0)
    add t (mul a (add s (mul t v)))

/-- `tan_kernel(y::Float64) = tan_kernel(DoubleFloat64(y, 0.0), 1)`. -/
def tanKernel64 (y : FV .f64) : FV .f64 := tanKernelD ⟨y, zero .f64⟩ 1

/-! ## Float32 kernels, `base/special/trig.jl:84-93,152-160,336-351`. `DoubleFloat32(x)`
holds `Float64(x)`. -/

/-- `sin_kernel(y::DoubleFloat32)`; `sin_kernel(x::Float32)` applies it to `Float64(x)`. -/
def sinKernel32 (hi : FV .f64) : FV .f32 :=
  let z := mul hi hi
  let w := mul z z
  let r := horner z [nth sinK32 2, nth sinK32 3]
  let s := mul z hi
  conv (add (add hi (mul s (horner z [nth sinK32 0, nth sinK32 1]))) (mul (mul s w) r))

/-- `cos_kernel(y::DoubleFloat32)`; `cos_kernel(x::Float32)` applies it to `Float64(x)`. -/
def cosKernel32 (hi : FV .f64) : FV .f32 :=
  let y2 := mul hi hi
  let y4 := mul y2 y2
  let r := horner y2 [nth cosK32 2, nth cosK32 3]
  conv (add (add (add one64 (mul y2 (nth cosK32 0))) (mul y4 (nth cosK32 1))) (mul (mul y4 y2) r))

/-- `tan_kernel(y::DoubleFloat32, k)`; `tan_kernel(y::Float32)` is `k = 1`. -/
def tanKernel32 (hi : FV .f64) (k : Int) : FV .f32 :=
  let y2 := mul hi hi
  let r := horner y2 [nth tanK32 0, nth tanK32 1]
  let t := horner y2 [nth tanK32 2, nth tanK32 3]
  let y4 := mul y2 y2
  let y3 := mul y2 hi
  let u := horner y2 [nth tanK32 4, nth tanK32 5]
  let py := add (add hi (mul y3 u)) (mul (mul y3 y4) (add t (mul y4 r)))
  if k == 1 then conv py else conv (div (neg one64) py)

/-! ## The public functions, generic over `T ∈ {Float32, Float64}` -/

/-- Reduced argument: `n` and the kernel argument (`DoubleFloat64` or `DoubleFloat32`). -/
def reduce : (T : FTy) → FV T → Int × DF64
  | .f32, x => let (n, y) := Special.remPio2Kernel32 x; (n, ⟨y, zero .f64⟩)
  | _, x => let (n, hi, lo) := MathFuncs.remPio2Kernel (toD x); (n, ⟨Fl.ofF64 hi, Fl.ofF64 lo⟩)

/-- `sin_kernel`, `cos_kernel` on a reduced argument. -/
def sinK : (T : FTy) → DF64 → FV T
  | .f32, y => conv (sinKernel32 y.hi)
  | _, y => conv (sinKernelD y)
def cosK : (T : FTy) → DF64 → FV T
  | .f32, y => conv (cosKernel32 y.hi)
  | _, y => conv (cosKernelD y)
/-- `sin_kernel(x)`, `cos_kernel(x)`, `tan_kernel(x)` on an unreduced `x::T`. -/
def sinK1 : (T : FTy) → FV T → FV T
  | .f32, x => conv (sinKernel32 (conv x))
  | _, x => conv (sinKernel64 (conv x))
def cosK1 : (T : FTy) → FV T → FV T
  | .f32, x => conv (cosKernel32 (conv x))
  | _, x => conv (cosKernel64 (conv x))
def tanK : (T : FTy) → DF64 → Int → FV T
  | .f32, y, k => conv (tanKernel32 y.hi k)
  | _, y, k => conv (tanKernelD y k)
def tanK1 : (T : FTy) → FV T → FV T
  | .f32, x => conv (tanKernel32 (conv x) 1)
  | _, x => conv (tanKernel64 (conv x))

/-- `T(pi)/4`, `sqrt(eps(T))`, `sqrt(eps(T)/T(2.0))`, `sqrt(eps(T))/2`. -/
def piO4 : (T : FTy) → FV T | .f32 => conv piOver4_32 | _ => conv piOver4_64
def sqrtEps : (T : FTy) → FV T | .f32 => conv sqrtEps32 | _ => conv sqrtEps64
def sqrtHalfEps : (T : FTy) → FV T | .f32 => conv sqrtHalfEps32 | _ => conv sqrtHalfEps64
def halfSqrtEps : (T : FTy) → FV T | .f32 => conv halfSqrtEps32 | _ => conv halfSqrtEps64

/-- `throw_finite_domainerror(f, x)`; `base/math.jl:40-42`. -/
def finiteDomainError {α : Type} (f : String) : Jl α := .error (.domainError f)

/--
Julia source: base/special/trig.jl:28-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sin(x::T) where T<:Union{Float32, Float64}
    absx = abs(x)
    if absx < T(pi)/4 #|x| ~<= pi/4, no need for reduction
        if absx < sqrt(eps(T))
            return x
        end
        return sin_kernel(x)
    elseif isnan(x)
        return x
    elseif isinf(x)
        return throw_finite_domainerror(:sin, x)
    end
    n, y = rem_pio2_kernel(x)
    n = n&3
    if n == 0
        return sin_kernel(y)
    elseif n == 1
        return cos_kernel(y)
    elseif n == 2
        return -sin_kernel(y)
    else
        return -cos_kernel(y)
    end
end
```
-/
def sin (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if lt absx (piO4 T) then
    if lt absx (sqrtEps T) then .ok x else .ok (sinK1 T x)
  else if x.isnan then .ok x
  else if x.isinf then finiteDomainError "sin"
  else
    let (n, y) := reduce T x
    let n := n % 4
    .ok (if n == 0 then sinK T y else if n == 1 then cosK T y
      else if n == 2 then neg (sinK T y) else neg (cosK T y))

/--
Julia source: base/special/trig.jl:96-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cos(x::T) where T<:Union{Float32, Float64}
    absx = abs(x)
    if absx < T(pi)/4
        if absx < sqrt(eps(T)/T(2.0))
            return T(1.0)
        end
        return cos_kernel(x)
    elseif isnan(x)
        return x
    elseif isinf(x)
        return throw_finite_domainerror(:cos, x)
    else
        n, y = rem_pio2_kernel(x)
        n = n&3
        if n == 0
            return cos_kernel(y)
        elseif n == 1
            return -sin_kernel(y)
        elseif n == 2
            return -cos_kernel(y)
        else
            return sin_kernel(y)
        end
    end
end
```
-/
def cos (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if lt absx (piO4 T) then
    if lt absx (sqrtHalfEps T) then .ok (one T) else .ok (cosK1 T x)
  else if x.isnan then .ok x
  else if x.isinf then finiteDomainError "cos"
  else
    let (n, y) := reduce T x
    let n := n % 4
    .ok (if n == 0 then cosK T y else if n == 1 then neg (sinK T y)
      else if n == 2 then neg (cosK T y) else sinK T y)

/--
Julia source: base/special/trig.jl:211-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline sincos_kernel(y::Union{Float32, Float64, DoubleFloat32, DoubleFloat64}) = (sin_kernel(y), cos_kernel(y))
```
-/
def sincosK (T : FTy) (y : DF64) : FV T × FV T := (sinK T y, cosK T y)
def sincosK1 (T : FTy) (x : FV T) : FV T × FV T := (sinK1 T x, cosK1 T x)

/--
Julia source: base/special/trig.jl:174-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sincos(x::T) where T<:Union{Float32, Float64}
    if abs(x) < T(pi)/4
        if x == zero(T)
            return x, one(T)
        end
        return sincos_kernel(x)
    elseif isnan(x)
        return x, x
    elseif isinf(x)
        return throw_finite_domainerror(:sincos, x)
    end
    n, y = rem_pio2_kernel(x)
    n = n&3
    # calculate both kernels at the reduced y...
    si, co = sincos_kernel(y)
    # ... and use the same selection scheme as above: (sin, cos, -sin, -cos) for
    # sin and (cos, -sin, -cos, sin) for cos
    if n == 0
        return si, co
    elseif n == 1
        return co, -si
    elseif n == 2
        return -si, -co
    else
        return -co, si
    end
end
```
-/
def sincos (T : FTy) (x : FV T) : Jl (FV T × FV T) :=
  if lt (abs x) (piO4 T) then
    if eq x (zero T) then .ok (x, one T) else .ok (sincosK1 T x)
  else if x.isnan then .ok (x, x)
  else if x.isinf then finiteDomainError "sincos"
  else
    let (n, y) := reduce T x
    let n := n % 4
    let (si, co) := sincosK T y
    .ok (if n == 0 then (si, co) else if n == 1 then (co, neg si)
      else if n == 2 then (neg si, neg co) else (neg co, si))

/--
Julia source: base/special/trig.jl:202-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sincos(x::AbstractFloat) = sincos(x)
```
-/
def sincosAbstract {α β : Type} (sincos : α → β) (x : α) : β := sincos x

/--
Julia source: base/special/trig.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sincos(x) = (sin(x), cos(x))
```
-/
def sincosFallback {α β : Type} (sin cos : α → β) (x : α) : β × β := (sin x, cos x)

/--
Julia source: base/special/trig.jl:205-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos(x) = _sincos(float(x))
```
-/
def sincosGeneric {α β γ : Type} (float : α → β) (sincos : β → γ) (x : α) : γ :=
  sincos (float x)

/--
Julia source: base/special/trig.jl:214-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tan(x::T) where T<:Union{Float32, Float64}
    absx = abs(x)
    if absx < T(pi)/4
        if absx < sqrt(eps(T))/2 # first order dominates, but also allows tan(-0)=-0
            return x
        end
        return tan_kernel(x)
    elseif isnan(x)
        return x
    elseif isinf(x)
        return throw_finite_domainerror(:tan, x)
    end
    n, y = rem_pio2_kernel(x)
    if iseven(n)
        return tan_kernel(y,1)
    else
        return tan_kernel(y,-1)
    end
end
```
-/
def tan (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if lt absx (piO4 T) then
    if lt absx (halfSqrtEps T) then .ok x else .ok (tanK1 T x)
  else if x.isnan then .ok x
  else if x.isinf then finiteDomainError "tan"
  else
    let (n, y) := reduce T x
    .ok (if n % 2 == 0 then tanK T y 1 else tanK T y (-1))

/--
Julia source: base/special/trig.jl:354-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sin_kernel(x::Real) = sin(x)
cos_kernel(x::Real) = cos(x)
tan_kernel(x::Real) = tan(x)
sincos_kernel(x::Real) = sincos(x)
```
-/
def sinKernelReal {α β : Type} (sin : α → β) (x : α) : β := sin x
def cosKernelReal {α β : Type} (cos : α → β) (x : α) : β := cos x
def tanKernelReal {α β : Type} (tan : α → β) (x : α) : β := tan x
def sincosKernelReal {α β : Type} (sincos : α → β) (x : α) : β := sincos x
/-! ## asin, `base/special/trig.jl:361-450` -/

/-- `arc_p`, `arc_q`, `arc_tRt` for `Float64` and `Float32`. -/
def arcP : (T : FTy) → FV T → FV T
  | .f32, t => mul t (horner t arcP32)
  | .f64, t => mul t (horner t arcP64)
  | .f16, t => t
def arcQ : (T : FTy) → FV T → FV T
  | .f32, t => horner t arcQ32
  | .f64, t => horner t arcQ64
  | .f16, t => t
def arcTRt (T : FTy) (t : FV T) : FV T := div (arcP T t) (arcQ T t)

/-- `asin_kernel(t::Float64, x::Float64)`. -/
def asinKernel64 (t x : FV .f64) : FV .f64 :=
  let pio2Lo := nth asinMisc64 0
  let s := sqrtLlvm t
  let tRt := arcTRt .f64 t
  if le (nth asinMisc64 1) (abs x) then
    flipsign (sub (nth asinMisc64 2) (sub (mul two64 (add s (mul s tRt))) pio2Lo)) x
  else
    let s0 := clearLow s
    let c := div (sub t (mul s0 s0)) (add s s0)
    let p := sub (mul (mul two64 s) tRt) (sub pio2Lo (mul two64 c))
    let q := sub (nth asinMisc64 3) (mul two64 s0)
    flipsign (sub (nth asinMisc64 3) (sub p q)) x

/-- `asin_kernel(t::Float32, x::Float32)`. -/
def asinKernel32 (t x : FV .f32) : FV .f32 :=
  let s := sqrtLlvm (conv t : FV .f64)
  let tRt := arcTRt .f32 t
  flipsign (conv (sub (nth asinMisc64 2) (mul two64 (add s (mul s (conv tRt))))) : FV .f32) x

def asinKernel : (T : FTy) → FV T → FV T → FV T
  | .f32, t, x => asinKernel32 t x
  | _, t, x => conv (asinKernel64 (conv t) (conv x))

/--
Julia source: base/special/trig.jl:361-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ASIN_X_MIN_THRESHOLD(::Type{Float32}) = 2.0f0^-12
ASIN_X_MIN_THRESHOLD(::Type{Float64}) = sqrt(eps(Float64))
```
-/
def asinMin : (T : FTy) → FV T | .f32 => conv asinMin32 | _ => conv asinMin64

/--
Julia source: base/special/trig.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline asin_domain_error(x) = throw(DomainError(x, "asin(x) is not defined for |x| > 1."))
```
-/
def asinDomainError {α : Type} : Jl α := .error (.domainError "asin(x) is not defined for |x| > 1.")

/-- `asin(x::T) where T<:Union{Float32, Float64}`. -/
def asin (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if le (one T) absx then
    if eq absx (one T) then .ok (flipsign (div (piT T) (ofInt T 2)) x) else asinDomainError
  else if lt absx (div (one T) (ofInt T 2)) then
    if lt absx (asinMin T) then .ok x
    else .ok (muladd x (arcTRt T (mul x x)) x)
  else
    let t := div (sub (one T) absx) (ofInt T 2)
    .ok (asinKernel T t x)
where
  piT : (T : FTy) → FV T | .f32 => piT32 | .f64 => piT64 | .f16 => conv piT32

/-! ## atan, `base/special/trig.jl:453-554` -/

def atanHi : (T : FTy) → Nat → FV T | .f32, i => nth atanHi32 i | _, i => conv (nth atanHi64 i)
def atanLo : (T : FTy) → Nat → FV T | .f32, i => nth atanLo32 i | _, i => conv (nth atanLo64 i)
def atanLarge : (T : FTy) → FV T | .f32 => atanLarge32 | _ => conv atanLarge64
def atanSmall : (T : FTy) → FV T | .f32 => atanSmall32 | _ => conv atanSmall64
def atanBreak : (T : FTy) → Nat → FV T | .f32, i => nth atanBreaks32 i | _, i => conv (nth atanBreaks64 i)

/-- `atan_p(z, w)`, `atan_q(w)`, `atan_pq(x)`. -/
def atanP : (T : FTy) → FV T → FV T → FV T
  | .f32, z, w => mul z (horner w atanP32)
  | _, z, w => conv (mul (conv z : FV .f64) (horner (conv w) atanP64))
def atanQ : (T : FTy) → FV T → FV T
  | .f32, w => mul w (horner w atanQ32)
  | _, w => conv (mul (conv w : FV .f64) (horner (conv w) atanQ64))
def atanPQ (T : FTy) (x : FV T) : FV T × FV T :=
  let x2 := mul x x
  let x4 := mul x2 x2
  (atanP T x2 x4, atanQ T x4)

/-- `sign(x)` for a float. -/
def signF {T : FTy} (x : FV T) : FV T :=
  if x.isnan || x.iszero then x else copysign (one T) x

/-- `atan(x::T) where T<:Union{Float32, Float64}`. -/
def atan (T : FTy) (x : FV T) : FV T :=
  let absx := abs x
  if le (atanLarge T) absx then copysign (atanBreak T 5) x
  else if lt absx (atanBreak T 0) then
    if lt absx (atanSmall T) then x
    else
      let (p, q) := atanPQ T x
      sub x (mul x (add p q))
  else
    let xsign := signF x
    let two := ofInt T 2
    let (hi, lo, x) :=
      if lt absx (atanBreak T 2) then
        if lt absx (atanBreak T 1) then
          (atanHi T 0, atanLo T 0, div (sub (mul two absx) (one T)) (add two absx))
        else (atanHi T 1, atanLo T 1, div (sub absx (one T)) (add absx (one T)))
      else if lt absx (atanBreak T 3) then
        (atanHi T 2, atanLo T 2, div (sub absx (atanBreak T 4)) (add (one T) (mul (atanBreak T 4) absx)))
      else (atanHi T 3, atanLo T 3, div (neg (one T)) absx)
    let (p, q) := atanPQ T x
    let z := sub hi (sub (sub (mul x (add p q)) lo) x)
    copysign z xsign

/--
Julia source: base/special/trig.jl:556-562 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ATAN2_PI_LO(::Type{Float32}) = -8.7422776573f-08
ATAN2_RATIO_BIT_SHIFT(::Type{Float32}) = 23
ATAN2_RATIO_THRESHOLD(::Type{Float32}) = 26

ATAN2_PI_LO(::Type{Float64}) = 1.2246467991473531772E-16
ATAN2_RATIO_BIT_SHIFT(::Type{Float64}) = 20
ATAN2_RATIO_THRESHOLD(::Type{Float64}) = 60
```
-/
def atan2PiLo : (T : FTy) → FV T | .f32 => atan2PiLo32 | _ => conv atan2PiLo64
def atan2Shift : FTy → Nat | .f32 => 23 | _ => 20
def atan2Threshold : FTy → Int | .f32 => 26 | _ => 60
def piT : (T : FTy) → FV T | .f32 => piT32 | _ => conv piT64
def piO2T : (T : FTy) → FV T | .f32 => piOver2T32 | _ => conv piOver2T64
def piO4T : (T : FTy) → FV T | .f32 => piOver4T32 | _ => conv piOver4T64
def threePiO4T : (T : FTy) → FV T | .f32 => threePiOver4T32 | _ => conv threePiOver4T64

/-- `poshighword` of either format. -/
def poshw {T : FTy} (x : FV T) : Nat :=
  if T = .f32 then x.toBits % 2 ^ 31 else Bits.poshighwordU64 x.toBits

/--
Julia source: base/special/trig.jl:564-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function atan(y::T, x::T) where T<:Union{Float32, Float64}
    # Method :
    #    M1) Reduce y to positive by atan2(y,x)=-atan2(-y,x).
    #    M2) Reduce x to positive by (if x and y are unexceptional):
    #        ARG (x+iy) = arctan(y/x)          ... if x > 0,
    #        ARG (x+iy) = pi - arctan[y/(-x)]   ... if x < 0,
    #
    # Special cases:
    #
    #    S1) ATAN2((anything), NaN ) is NaN;
    #    S2) ATAN2(NAN , (anything) ) is NaN;
    #    S3) ATAN2(+-0, +(anything but NaN)) is +-0  ;
    #    S4) ATAN2(+-0, -(anything but NaN)) is +-pi ;
    #    S5) ATAN2(+-(anything but 0 and NaN), 0) is +-pi/2;
    #    S6) ATAN2(+-(anything but INF and NaN), +INF) is +-0 ;
    #    S7) ATAN2(+-(anything but INF and NaN), -INF) is +-pi;
    #    S8) ATAN2(+-INF,+INF ) is +-pi/4 ;
    #    S9) ATAN2(+-INF,-INF ) is +-3pi/4;
    #    S10) ATAN2(+-INF, (anything but,0,NaN, and INF)) is +-pi/2;
    if isnan(x) | isnan(y) # S1 or S2
        return isnan(x) ? x : y
    end

    if x == T(1.0) # then y/x = y and x > 0, see M2
        return atan(y)
    end
    # generate an m ∈ {0, 1, 2, 3} to branch off of
    m = 2*signbit(x) + 1*signbit(y)

    if iszero(y)
        if m == 0 || m == 1
            return y # atan(+-0, +anything) = +-0
        elseif m == 2
            return T(pi) # atan(+0, -anything) = pi
        elseif m == 3
            return -T(pi) # atan(-0, -anything) =-pi
        end
    elseif iszero(x)
        return flipsign(T(pi)/2, y)
    end

    if isinf(x)
        if isinf(y)
            if m == 0
                return T(pi)/4  # atan(+Inf), +Inf))
            elseif m == 1
                return -T(pi)/4 # atan(-Inf), +Inf))
            elseif m == 2
                return 3*T(pi)/4 # atan(+Inf, -Inf)
            elseif m == 3
                return -3*T(pi)/4 # atan(-Inf,-Inf)
            end
        else
            if m == 0
                return zero(T)  # atan(+...,+Inf) */
            elseif m == 1
                return -zero(T) # atan(-...,+Inf) */
            elseif m == 2
                return T(pi)    # atan(+...,-Inf) */
            elseif m == 3
                return -T(pi)   # atan(-...,-Inf) */
            end
        end
    end

    # x wasn't Inf, but y is
    isinf(y) && return copysign(T(pi)/2, y)

    ypw = poshighword(y)
    xpw = poshighword(x)
    # compute y/x for Float32
    k = reinterpret(Int32, ypw -% xpw)>>ATAN2_RATIO_BIT_SHIFT(T)

    if k > ATAN2_RATIO_THRESHOLD(T) # |y/x| >  threshold
        z=T(pi)/2+T(0.5)*ATAN2_PI_LO(T)
        m&=1;
    elseif x<0 && k < -ATAN2_RATIO_THRESHOLD(T) # 0 > |y|/x > threshold
        z = zero(T)
    else #safe to do y/x
        z = atan(abs(y/x))
    end

    if m == 0
        return z # atan(+,+)
    elseif m == 1
        return -z # atan(-,+)
    elseif m == 2
        return T(pi)-(z-ATAN2_PI_LO(T)) # atan(+,-)
    else # default case m == 3
        return (z-ATAN2_PI_LO(T))-T(pi) # atan(-,-)
    end
end
```
-/
def atan2 (T : FTy) (y x : FV T) : FV T := Id.run do
  if x.isnan || y.isnan then return (if x.isnan then x else y)
  if eq x (one T) then return atan T y
  let mut m : Nat := 2 * (if x.signbit then 1 else 0) + (if y.signbit then 1 else 0)
  if y.iszero then
    if m == 0 || m == 1 then return y
    else if m == 2 then return piT T
    else return neg (piT T)
  else if x.iszero then return flipsign (piO2T T) y
  if x.isinf then
    if y.isinf then
      return (if m == 0 then piO4T T else if m == 1 then neg (piO4T T)
        else if m == 2 then threePiO4T T else neg (threePiO4T T))
    else
      return (if m == 0 then zero T else if m == 1 then zero T true
        else if m == 2 then piT T else neg (piT T))
  if y.isinf then return copysign (piO2T T) y
  let k : Int := (wrapInt .i32 ((poshw y + 2 ^ 32 - poshw x) % 2 ^ 32)).fdiv (2 ^ atan2Shift T)
  let mut z := zero T
  if k > atan2Threshold T then
    z := add (piO2T T) (mul (div (one T) (ofInt T 2)) (atan2PiLo T))
    m := m % 2
  else if lt x (zero T) && k < -atan2Threshold T then z := zero T
  else z := atan T (abs (div y x))
  return (if m == 0 then z else if m == 1 then neg z
    else if m == 2 then sub (piT T) (sub z (atan2PiLo T))
    else sub (sub z (atan2PiLo T)) (piT T))

/-! ## acos, `base/special/trig.jl:657-722` -/

def acosMin : (T : FTy) → FV T | .f32 => acosMin32 | _ => conv acosMin64
def pio2Hi : (T : FTy) → FV T | .f32 => pio2Hi32 | _ => conv pio2Hi64
def pio2Lo : (T : FTy) → FV T | .f32 => pio2Lo32 | _ => conv pio2Lo64
def acosPi : (T : FTy) → FV T | .f32 => acosPi32 | _ => conv acosPi64
/-- `ACOS_CORRECT_LOWWORD(T, x)`. -/
def acosLowword {T : FTy} (x : FV T) : FV T :=
  if T = .f32 then Fl.ofBits (x.toBits / 2 ^ 12 * 2 ^ 12) else Fl.ofBits (x.toBits / 2 ^ 32 * 2 ^ 32)

/--
Julia source: base/special/trig.jl:668-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline acos_domain_error(x) = throw(DomainError(x, "acos(x) not defined for |x| > 1"))
```
-/
def acosDomainError {α : Type} : Jl α := .error (.domainError "acos(x) not defined for |x| > 1")

/-- `acos(x::T) where T <: Union{Float32, Float64}`. -/
def acos (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if le (one T) absx then
    if eq absx (one T) then .ok (if lt (zero T) x then zero T else piT T) else acosDomainError
  else if lt absx (div (one T) (ofInt T 2)) then
    if lt absx (acosMin T) then .ok (piO2T T)
    else .ok (sub (pio2Hi T) (sub x (sub (pio2Lo T) (mul x (arcTRt T (mul x x))))))
  else
    let z := mul (sub (one T) absx) (div (one T) (ofInt T 2))
    let zRz := arcTRt T z
    let s := sqrtLlvm z
    if lt x (zero T) then
      .ok (sub (acosPi T) (mul (ofInt T 2) (add s (sub (mul zRz s) (pio2Lo T)))))
    else
      let df := acosLowword s
      let c := div (sub z (mul df df)) (add s df)
      .ok (mul (ofInt T 2) (add df (add (mul zRz s) c)))



open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
/--
Julia source: base/special/trig.jl:771-783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cospi_kernel(x::AbstractFloat, sch)
    x² = x * x
    c₀ = sch.c₀
    (c₂, c₂_lo) = sch.c₂
    rest = sch.rest
    c₂ = -c₂
    c₂_lo = -c₂_lo
    r = evalpoly(x², rest) * x²
    a_x² = c₂ * x²
    a_x²_lo = muladd(c₂_lo, x², muladd(c₂, x², -a_x²))
    w = c₀ - a_x²
    w + muladd(x², r, ((c₀ - w) - a_x²) - a_x²_lo)
end
```
-/
def cospiKernelSch {T : FTy} (sch : List (FV T)) (x : FV T) : FV T :=
  let x2 := mul x x
  let c0 := nth sch 0
  let c2 := neg (nth sch 1)
  let c2lo := neg (nth sch 2)
  let r := mul (horner x2 (sch.drop 3)) x2
  let ax2 := mul c2 x2
  let ax2lo := add (mul c2lo x2) (add (mul c2 x2) (neg ax2))
  let w := sub c0 ax2
  add w (muladd x2 r (sub (sub (sub c0 w) ax2) ax2lo))

/--
Julia source: base/special/trig.jl:785-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _sinpi_kernel(x::AbstractFloat, sch)
    x² = x * x
    (c₁, c₁_lo) = sch.c₁
    (c₃, rest...) = sch.rest
    if rest === ()
        r = typeof(x)(0)
    else
        r = evalpoly(x², rest)
    end
    muladd(c₁, x, x * muladd(c₃, x², muladd(x² * x², r, c₁_lo)))
end
```
-/
def sinpiKernelSch {T : FTy} (sch : List (FV T)) (x : FV T) : FV T :=
  let x2 := mul x x
  let c1 := nth sch 0
  let c1lo := nth sch 1
  let c3 := nth sch 2
  let rest := sch.drop 3
  let r := if rest.isEmpty then zero T else horner x2 rest
  muladd c1 x (mul x (muladd c3 x2 (muladd (mul x2 x2) r c1lo)))

/-- The widened type of `sinpi_kernel_wide`: `Float32` for `Float16`, else `Float64`. -/
def wideTy : FTy → FTy | .f16 => .f32 | _ => .f64

/--
Julia source: base/special/trig.jl:728-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function sinpi_kernel_wide(x::Float64)
    _sinpi_kernel_f64(x)
end
@inline function sinpi_kernel(x::Float32)
    _sinpi_kernel_f32(x)
end
@inline function sinpi_kernel_wide(x::Float32)
    x = Float64(x)
    return x*evalpoly(x*x, (3.1415926535762266, -5.167712769188119,
                            2.5501626483206374, -0.5992021090314925, 0.08100185277841528))
end

@inline function sinpi_kernel(x::Float16)
    Float16(sinpi_kernel_wide(x))
end
@inline function sinpi_kernel_wide(x::Float16)
    x = Float32(x)
    return x*evalpoly(x*x, (3.1415927f0, -5.1677127f0, 2.5501626f0, -0.5992021f0, 0.081001855f0))
end
```
-/
def sinpiKernelWide : (T : FTy) → FV T → FV (wideTy T)
  | .f64, x => sinpiKernelSch sinpiPoly64 x
  | .f32, x => let w : FV .f64 := conv x; mul w (horner (mul w w) sinpiWide32)
  | .f16, x => let w : FV .f32 := conv x; mul w (horner (mul w w) sinpiWide16)

/--
Julia source: base/special/trig.jl:752-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function cospi_kernel_wide(x::Float64)
    _cospi_kernel_f64(x)
end
@inline function cospi_kernel(x::Float32)
    _cospi_kernel_f32(x)
end
@inline function cospi_kernel_wide(x::Float32)
    x = Float64(x)
    return evalpoly(x*x, (1.0, -4.934802200541122, 4.058712123568637,
                          -1.3352624040152927, 0.23531426791507182, -0.02550710082498761))
end
@inline function cospi_kernel(x::Float16)
    Float16(cospi_kernel_wide(x))
end
@inline function cospi_kernel_wide(x::Float16)
    x = Float32(x)
    return evalpoly(x*x, (1.0f0, -4.934802f0, 4.058712f0, -1.3352624f0, 0.23531426f0, -0.0255071f0))
end
```
-/
def cospiKernelWide : (T : FTy) → FV T → FV (wideTy T)
  | .f64, x => cospiKernelSch cospiPoly64 x
  | .f32, x => let w : FV .f64 := conv x; horner (mul w w) cospiWide32
  | .f16, x => let w : FV .f32 := conv x; horner (mul w w) cospiWide16

/--
Julia source: base/special/trig.jl:725-742 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function sinpi_kernel(x::Float64)
    _sinpi_kernel_f64(x)
end
@inline function sinpi_kernel_wide(x::Float64)
    _sinpi_kernel_f64(x)
end
@inline function sinpi_kernel(x::Float32)
    _sinpi_kernel_f32(x)
end
@inline function sinpi_kernel_wide(x::Float32)
    x = Float64(x)
    return x*evalpoly(x*x, (3.1415926535762266, -5.167712769188119,
                            2.5501626483206374, -0.5992021090314925, 0.08100185277841528))
end

@inline function sinpi_kernel(x::Float16)
    Float16(sinpi_kernel_wide(x))
end
```
-/
def sinpiKernel : (T : FTy) → FV T → FV T
  | .f64, x => sinpiKernelSch sinpiPoly64 x
  | .f32, x => sinpiKernelSch sinpiPoly32 x
  | .f16, x => conv (sinpiKernelWide .f16 x)

/--
Julia source: base/special/trig.jl:749-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function cospi_kernel(x::Float64)
    _cospi_kernel_f64(x)
end
@inline function cospi_kernel_wide(x::Float64)
    _cospi_kernel_f64(x)
end
@inline function cospi_kernel(x::Float32)
    _cospi_kernel_f32(x)
end
@inline function cospi_kernel_wide(x::Float32)
    x = Float64(x)
    return evalpoly(x*x, (1.0, -4.934802200541122, 4.058712123568637,
                          -1.3352624040152927, 0.23531426791507182, -0.02550710082498761))
end
@inline function cospi_kernel(x::Float16)
    Float16(cospi_kernel_wide(x))
end
```
-/
def cospiKernel : (T : FTy) → FV T → FV T
  | .f64, x => cospiKernelSch cospiPoly64 x
  | .f32, x => cospiKernelSch cospiPoly32 x
  | .f16, x => conv (cospiKernelWide .f16 x)

/-- `n = round(2*x)`, `rx = float(muladd(T(-.5), n, x))`, `n = Int64(n) & 3`; the shared
reduction of the four functions. -/
def piReduce {T : FTy} (x : FV T) : FV T × Int :=
  let n := roundI (mul (ofInt T 2) x)
  let rx := muladd (neg (div (one T) (ofInt T 2))) n x
  (rx, ((n.toRat.1 / (n.toRat.2 : Int)) % 4))

/--
Julia source: base/special/trig.jl:934-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sinpi(_x::T) where T<:IEEEFloat
    x = abs(_x)
    if !isfinite(x)
        isnan(x) && return x
        return throw_finite_domainerror(:sinpi, x)
    end
    # For large x, answers are all 1 or zero.
    x >= maxintfloat(T) && return copysign(zero(T), _x)

    # reduce to interval [0, 0.5]
    n = round(2*x)
    rx = float(muladd(T(-.5), n, x))
    n = Int64(n) & 3
    if n==0
        res = sinpi_kernel(rx)
    elseif n==1
        res = cospi_kernel(rx)
    elseif n==2
        res = zero(T)-sinpi_kernel(rx)
    else
        res = zero(T)-cospi_kernel(rx)
    end
    return ifelse(signbit(_x), -res, res)
end
```
-/
def sinpi (T : FTy) (x0 : FV T) : Jl (FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok x else finiteDomainError "sinpi"
  else if le (Bits.maxintfloat T) x then .ok (copysign (zero T) x0)
  else
    let (rx, n) := piReduce x
    let res := if n == 0 then sinpiKernel T rx else if n == 1 then cospiKernel T rx
      else if n == 2 then sub (zero T) (sinpiKernel T rx) else sub (zero T) (cospiKernel T rx)
    .ok (if x0.signbit then neg res else res)

/--
Julia source: base/special/trig.jl:968-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cospi(x::T) where T<:IEEEFloat
    x = abs(x)
    if !isfinite(x)
        isnan(x) && return x
        return throw_finite_domainerror(:cospi, x)
    end
    # For large x, answers are all 1 or zero.
    x >= maxintfloat(T) && return one(T)

    # reduce to interval [0, 0.5]
    n = round(2*x)
    rx = float(muladd(T(-.5), n, x))
    n = Int64(n) & 3
    if n==0
        return cospi_kernel(rx)
    elseif n==1
        return zero(T)-sinpi_kernel(rx)
    elseif n==2
        return zero(T)-cospi_kernel(rx)
    else
        return sinpi_kernel(rx)
    end
end
```
-/
def cospi (T : FTy) (x0 : FV T) : Jl (FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok x else finiteDomainError "cospi"
  else if le (Bits.maxintfloat T) x then .ok (one T)
  else
    let (rx, n) := piReduce x
    .ok (if n == 0 then cospiKernel T rx else if n == 1 then sub (zero T) (sinpiKernel T rx)
      else if n == 2 then sub (zero T) (cospiKernel T rx) else sinpiKernel T rx)

/--
Julia source: base/special/trig.jl:1005-1030 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sincospi(_x::T) where T<:IEEEFloat
    x = abs(_x)
    if !isfinite(x)
        isnan(x) && return x, x
        return throw_finite_domainerror(:sincospi, x)
    end
    # For large x, answers are all 1 or zero.
    x >= maxintfloat(T) && return (copysign(zero(T), _x), one(T))

    # reduce to interval [0, 0.5]
    n = round(2*x)
    rx = float(muladd(T(-.5), n, x))
    n = Int64(n) & 3
    si, co = sinpi_kernel(rx),cospi_kernel(rx)
    if n==0
        si, co = si, co
    elseif n==1
        si, co  = co, zero(T)-si
    elseif n==2
        si, co  = zero(T)-si, zero(T)-co
    else
        si, co  = zero(T)-co, si
    end
    si = ifelse(signbit(_x), -si, si)
    return si, co
end
```
-/
def sincospi (T : FTy) (x0 : FV T) : Jl (FV T × FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok (x, x) else finiteDomainError "sincospi"
  else if le (Bits.maxintfloat T) x then .ok (copysign (zero T) x0, one T)
  else
    let (rx, n) := piReduce x
    let si := sinpiKernel T rx
    let co := cospiKernel T rx
    let (si, co) := if n == 0 then (si, co) else if n == 1 then (co, sub (zero T) si)
      else if n == 2 then (sub (zero T) si, sub (zero T) co) else (sub (zero T) co, si)
    .ok (if x0.signbit then neg si else si, co)

/--
Julia source: base/special/trig.jl:1044-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tanpi(_x::T) where T<:IEEEFloat
    # This is modified from sincospi.
    # Would it be faster or more accurate to make a tanpi_kernel?
    x = abs(_x)
    if !isfinite(x)
        isnan(x) && return x
        return throw_finite_domainerror(:tanpi, x)
    end
    # For large x, answers are all zero.
    # All integer values for floats larger than maxintfloat are even.
    x >= maxintfloat(T) && return copysign(zero(T), _x)

    # reduce to interval [0, 0.5]
    n = round(2*x)
    rx = float(muladd(T(-.5), n, x))
    n = Int64(n) & 3
    si, co = sinpi_kernel_wide(rx), cospi_kernel_wide(rx)
    if n==0
        si, co = si, co
    elseif n==1
        si, co  = co, zero(T)-si
    elseif n==2
        si, co  = zero(T)-si, zero(T)-co
    else
        si, co  = zero(T)-co, si
    end
    si = ifelse(signbit(_x), -si, si)
    return float(T)(si / co)
end
```
-/
def tanpi (T : FTy) (x0 : FV T) : Jl (FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok x else finiteDomainError "tanpi"
  else if le (Bits.maxintfloat T) x then .ok (copysign (zero T) x0)
  else
    let (rx, n) := piReduce x
    let si := sinpiKernelWide T rx
    let co := cospiKernelWide T rx
    let z : FV (wideTy T) := zero (wideTy T)
    let (si, co) := if n == 0 then (si, co) else if n == 1 then (co, sub z si)
      else if n == 2 then (sub z si, sub z co) else (sub z co, si)
    let si := if x0.signbit then neg si else si
    .ok (conv (div si co))

/-! ## Integer and generic methods, `base/special/trig.jl:1074-1082` -/

/-- `sinpi(x::Integer) = x >= 0 ? zero(float(x)) : -zero(float(x))`. -/
def sinpiInt (x : Int) : FV .f64 := if x ≥ 0 then zero .f64 else zero .f64 true
/-- `cospi(x::Integer) = isodd(x) ? -one(float(x)) : one(float(x))`. -/
def cospiInt (x : Int) : FV .f64 := if x % 2 != 0 then neg (one .f64) else one .f64
/-- `tanpi(x::Integer)`: a signed zero, negative for odd positive and even negative `x`. -/
def tanpiInt (x : Int) : FV .f64 :=
  if x ≥ 0 then (if x % 2 != 0 then zero .f64 true else zero .f64)
  else (if x % 2 != 0 then zero .f64 else zero .f64 true)
/-- `sincospi(x::Integer) = (sinpi(x), cospi(x))`. -/
def sincospiInt (x : Int) : FV .f64 × FV .f64 := (sinpiInt x, cospiInt x)

/-- `sinpi(x::AbstractFloat) = sin(pi*x)` and the other three generic methods, for a
float type `α` with its `pi*x` and trigonometric functions. -/
def piGeneric {α β : Type} (piMul : α → α) (f : α → β) (x : α) : β := f (piMul x)

/-! ## Complex methods, `base/special/trig.jl:1084-1207`. `sinh`, `cosh`, `tanh`
(`base/special/hyperbolic.jl`) are parameters. -/

/-- A `Complex{T}` value. -/
structure Cx (T : FTy) where
  re : FV T
  im : FV T

/-- Hyperbolic functions of the component type. -/
structure Hyp (T : FTy) where
  sinh : FV T → FV T
  cosh : FV T → FV T
  tanh : FV T → FV T

/-- `pi * x` for a float `x`: `T(pi) * x`. -/
def piMul {T : FTy} (x : FV T) : FV T := mul (piT T) x

/-- `isinteger(x)` for a float. -/
def isint {T : FTy} (x : FV T) : Bool := x.isinteger

/-- The value of a `Jl` float result, `NaN` on error (unreachable where used). -/
def getF {T : FTy} : Jl (FV T) → FV T | .ok v => v | .error _ => nan T

/--
Julia source: base/special/trig.jl:1084-1091 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tanpi(z::Complex)
    zr, zi = reim(z)
    iszero(zi) && return Complex(tanpi(zr))
    sr, cr = sincospi(zr)
    ti = tanh(zi * pi)
    cz = Complex(cr, ti * sr)
    Complex(sr, ti * cr) * cz / abs2(cz)
end
```
-/
def tanpiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T) := do
  if z.im.iszero then return ⟨← tanpi T z.re, zero T⟩
  let (sr, cr) ← sincospi T z.re
  let ti := h.tanh (mul z.im (piT T))
  let cz : Cx T := ⟨cr, mul ti sr⟩
  let a : Cx T := ⟨sr, mul ti cr⟩
  let prod : Cx T := ⟨sub (mul a.re cz.re) (mul a.im cz.im), add (mul a.re cz.im) (mul a.im cz.re)⟩
  let n := add (mul cz.re cz.re) (mul cz.im cz.im)
  return ⟨div prod.re n, div prod.im n⟩

/--
Julia source: base/special/trig.jl:1093-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sinpi(z::Complex{T}) where T
    F = float(T)
    zr, zi = reim(z)
    if isinteger(zr)
        # zr = ...,-2,-1,0,1,2,...
        # sin(pi*zr) == ±0
        # cos(pi*zr) == ±1
        # cosh(pi*zi) > 0
        s = copysign(zero(F),zr)
        c_pos = isa(zr,Integer) ? iseven(zr) : isinteger(zr/2)
        sh = sinh(pi*zi)
        Complex(s, c_pos ? sh : -sh)
    elseif isinteger(2*zr)
        # zr = ...,-1.5,-0.5,0.5,1.5,2.5,...
        # sin(pi*zr) == ±1
        # cos(pi*zr) == +0
        # sign(sinh(pi*zi)) == sign(zi)
        s_pos = isinteger((2*zr-1)/4)
        ch = cosh(pi*zi)
        Complex(s_pos ? ch : -ch, isnan(zi) ? zero(F) : copysign(zero(F),zi))
    elseif !isfinite(zr)
        if zi == 0 || isinf(zi)
            Complex(F(NaN), F(zi))
        else
            Complex(F(NaN), F(NaN))
        end
    else
        pizi = pi*zi
        sipi, copi = sincospi(zr)
        Complex(sipi*cosh(pizi), copi*sinh(pizi))
    end
end
```
-/
def sinpiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T) := do
  let zr := z.re
  let zi := z.im
  if isint zr then
    let s := copysign (zero T) zr
    let cPos := isint (div zr (ofInt T 2))
    let sh := h.sinh (piMul zi)
    return ⟨s, if cPos then sh else neg sh⟩
  else if isint (mul (ofInt T 2) zr) then
    let sPos := isint (div (sub (mul (ofInt T 2) zr) (one T)) (ofInt T 4))
    let ch := h.cosh (piMul zi)
    return ⟨if sPos then ch else neg ch, if zi.isnan then zero T else copysign (zero T) zi⟩
  else if !zr.isfinite then
    if eq zi (zero T) || zi.isinf then return ⟨nan T, zi⟩ else return ⟨nan T, nan T⟩
  else
    let pizi := piMul zi
    let (sipi, copi) ← sincospi T zr
    return ⟨mul sipi (h.cosh pizi), mul copi (h.sinh pizi)⟩

/--
Julia source: base/special/trig.jl:1126-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cospi(z::Complex{T}) where T
    F = float(T)
    zr, zi = reim(z)
    if isinteger(zr)
        # zr = ...,-2,-1,0,1,2,...
        # sin(pi*zr) == ±0
        # cos(pi*zr) == ±1
        # sign(sinh(pi*zi)) == sign(zi)
        # cosh(pi*zi) > 0
        s = copysign(zero(F),zr)
        c_pos = isa(zr,Integer) ? iseven(zr) : isinteger(zr/2)
        ch = cosh(pi*zi)
        Complex(c_pos ? ch : -ch, isnan(zi) ? s : -flipsign(s,zi))
    elseif isinteger(2*zr)
        # zr = ...,-1.5,-0.5,0.5,1.5,2.5,...
        # sin(pi*zr) == ±1
        # cos(pi*zr) == +0
        # sign(sinh(pi*zi)) == sign(zi)
        s_pos = isinteger((2*zr-1)/4)
        sh = sinh(pi*zi)
        Complex(zero(F), s_pos ? -sh : sh)
    elseif !isfinite(zr)
        if zi == 0
            Complex(F(NaN), isnan(zr) ? zero(F) : -flipsign(F(zi),zr))
        elseif isinf(zi)
            Complex(F(Inf), F(NaN))
        else
            Complex(F(NaN), F(NaN))
        end
    else
        pizi = pi*zi
        sipi, copi = sincospi(zr)
        Complex(copi*cosh(pizi), -sipi*sinh(pizi))
    end
end
```
-/
def cospiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T) := do
  let zr := z.re
  let zi := z.im
  if isint zr then
    let s := copysign (zero T) zr
    let cPos := isint (div zr (ofInt T 2))
    let ch := h.cosh (piMul zi)
    return ⟨if cPos then ch else neg ch, if zi.isnan then s else neg (flipsign s zi)⟩
  else if isint (mul (ofInt T 2) zr) then
    let sPos := isint (div (sub (mul (ofInt T 2) zr) (one T)) (ofInt T 4))
    let sh := h.sinh (piMul zi)
    return ⟨zero T, if sPos then neg sh else sh⟩
  else if !zr.isfinite then
    if eq zi (zero T) then
      return ⟨nan T, if zr.isnan then zero T else neg (flipsign zi zr)⟩
    else if zi.isinf then return ⟨inf T, nan T⟩
    else return ⟨nan T, nan T⟩
  else
    let pizi := piMul zi
    let (sipi, copi) ← sincospi T zr
    return ⟨mul copi (h.cosh pizi), mul (neg sipi) (h.sinh pizi)⟩

/--
Julia source: base/special/trig.jl:1162-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sincospi(z::Complex{T}) where T
    F = float(T)
    zr, zi = reim(z)
    if isinteger(zr)
        # zr = ...,-2,-1,0,1,2,...
        # sin(pi*zr) == ±0
        # cos(pi*zr) == ±1
        # cosh(pi*zi) > 0
        s = copysign(zero(F),zr)
        c_pos = isa(zr,Integer) ? iseven(zr) : isinteger(zr/2)
        pizi = pi*zi
        sh, ch = sinh(pizi), cosh(pizi)
        (
            Complex(s, c_pos ? sh : -sh),
            Complex(c_pos ? ch : -ch, isnan(zi) ? s : -flipsign(s,zi)),
        )
    elseif isinteger(2*zr)
        # zr = ...,-1.5,-0.5,0.5,1.5,2.5,...
        # sin(pi*zr) == ±1
        # cos(pi*zr) == +0
        # sign(sinh(pi*zi)) == sign(zi)
        s_pos = isinteger((2*zr-1)/4)
        pizi = pi*zi
        sh, ch = sinh(pizi), cosh(pizi)
        (
            Complex(s_pos ? ch : -ch, isnan(zi) ? zero(F) : copysign(zero(F),zi)),
            Complex(zero(F), s_pos ? -sh : sh),
        )
    elseif !isfinite(zr)
        if zi == 0
            Complex(F(NaN), F(zi)), Complex(F(NaN), isnan(zr) ? zero(F) : -flipsign(F(zi),zr))
        elseif isinf(zi)
            Complex(F(NaN), F(zi)), Complex(F(Inf), F(NaN))
        else
            Complex(F(NaN), F(NaN)), Complex(F(NaN), F(NaN))
        end
    else
        pizi = pi*zi
        sipi, copi = sincospi(zr)
        sihpi, cohpi = sinh(pizi), cosh(pizi)
        (
            Complex(sipi*cohpi, copi*sihpi),
            Complex(copi*cohpi, -sipi*sihpi),
        )
    end
end
```
-/
def sincospiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T × Cx T) := do
  let zr := z.re
  let zi := z.im
  if isint zr then
    let s := copysign (zero T) zr
    let cPos := isint (div zr (ofInt T 2))
    let pizi := piMul zi
    let sh := h.sinh pizi
    let ch := h.cosh pizi
    return (⟨s, if cPos then sh else neg sh⟩,
      ⟨if cPos then ch else neg ch, if zi.isnan then s else neg (flipsign s zi)⟩)
  else if isint (mul (ofInt T 2) zr) then
    let sPos := isint (div (sub (mul (ofInt T 2) zr) (one T)) (ofInt T 4))
    let pizi := piMul zi
    let sh := h.sinh pizi
    let ch := h.cosh pizi
    return (⟨if sPos then ch else neg ch, if zi.isnan then zero T else copysign (zero T) zi⟩,
      ⟨zero T, if sPos then neg sh else sh⟩)
  else if !zr.isfinite then
    if eq zi (zero T) then
      return (⟨nan T, zi⟩, ⟨nan T, if zr.isnan then zero T else neg (flipsign zi zr)⟩)
    else if zi.isinf then return (⟨nan T, zi⟩, ⟨inf T, nan T⟩)
    else return (⟨nan T, nan T⟩, ⟨nan T, nan T⟩)
  else
    let pizi := piMul zi
    let (sipi, copi) ← sincospi T zr
    let sihpi := h.sinh pizi
    let cohpi := h.cosh pizi
    return (⟨mul sipi cohpi, mul copi sihpi⟩, ⟨mul copi cohpi, mul (neg sipi) sihpi⟩)



open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
/--
Julia source: base/special/trig.jl:1217-1218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fastabs(x::Number) = abs(x)
fastabs(z::Complex) = abs(real(z)) + abs(imag(z))
```
-/
def fastabs {T : FTy} (x : FV T) : FV T := abs x
def fastabsC {T : FTy} (z : Cx T) : FV T := add (abs z.re) (abs z.im)

/--
Julia source: base/special/trig.jl:1221-1223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinf_real(x::Real) = isinf(x)
isinf_real(x::Complex) = isinf(real(x)) && isfinite(imag(x))
isinf_real(x::Number) = false
```
-/
def isinfReal {T : FTy} (x : FV T) : Bool := x.isinf
def isinfRealC {T : FTy} (z : Cx T) : Bool := z.re.isinf && z.im.isfinite
def isinfRealNumber {α : Type} (_x : α) : Bool := false

/--
Julia source: base/special/trig.jl:1237-1238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sinc_threshold(::Type{Float64}) = 0.001
_sinc_threshold(::Type{Float32}) = 0.05f0
```
-/
def sincThreshold : (T : FTy) → FV T | .f32 => sincThr32 | _ => conv sincThr64

/--
Julia source: base/special/trig.jl:1239-1240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _sinc(x::Union{T,Complex{T}}) where {T<:Union{Float32,Float64}} =
    fastabs(x) < _sinc_threshold(T) ? evalpoly(x^2, (T(1), -T(pi)^2/6, T(pi)^4/120)) : isinf_real(x) ? zero(x) : sinpi(x)/(pi*x)
```
-/
def sincF (T : FTy) (x : FV T) : Jl (FV T) := do
  if lt (fastabs x) (sincThreshold T) then
    let p := piT T
    let p2 := mul p p
    let c2 := neg (div p2 (ofInt T 6))
    let c4 := div (mul p2 p2) (ofInt T 120)
    return horner (mul x x) [one T, c2, c4]
  else if isinfReal x then return zero T
  else
    let s ← sinpi T x
    return div s (mul (piT T) x)

/--
Julia source: base/special/trig.jl:1241-1241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sinc(x::Float16) = Float16(_sinc(Float32(x)))
```
-/
def sinc16 (x : FV .f16) : Jl (FV .f16) := do return conv (← sincF .f32 (conv x))

/--
Julia source: base/special/trig.jl:1234-1234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sinc(x::Number) = _sinc(float(x))
```
-/
def sinc (T : FTy) (x : FV T) : Jl (FV T) :=
  match T, x with
  | .f16, x => sinc16 x
  | T, x => sincF T x

/--
Julia source: base/special/trig.jl:1235-1235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sinc(x::Integer) = iszero(x) ? one(x) : zero(x)
```
-/
def sincInt (x : Int) : Int := if x == 0 then 1 else 0

/--
Julia source: base/special/trig.jl:1236-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sinc(x::Number) = iszero(x) ? one(x) : isinf_real(x) ? zero(x) : sinpi(x)/(pi*x)
```
-/
def sincGeneric {α : Type} (iszero isinfR : α → Bool) (one0 zero0 : α → α)
    (sinpi piMul : α → α) (divα : α → α → α) (x : α) : α :=
  if iszero x then one0 x else if isinfR x then zero0 x else divα (sinpi x) (piMul x)

/--
Julia source: base/special/trig.jl:1239-1240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _sinc(x::Union{T,Complex{T}}) where {T<:Union{Float32,Float64}} =
    fastabs(x) < _sinc_threshold(T) ? evalpoly(x^2, (T(1), -T(pi)^2/6, T(pi)^4/120)) : isinf_real(x) ? zero(x) : sinpi(x)/(pi*x)
```
-/
def sincSpecialized {α β : Type} (ltβ : β → β → Bool) (fastabs : α → β) (threshold : β)
    (poly zero quotient : α → α) (isinfReal : α → Bool) (x : α) : α :=
  if ltβ (fastabs x) threshold then poly x else if isinfReal x then zero x else quotient x

/--
Julia source: base/special/trig.jl:1242-1242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sinc(x::ComplexF16) = ComplexF16(_sinc(ComplexF32(x)))
```
-/
def sincComplex16 {α β : Type} (convert32 : α → β) (convert16 : β → α)
    (sinc32 : β → β) (x : α) : α := convert16 (sinc32 (convert32 x))

/--
Julia source: base/special/trig.jl:1255-1258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cosc_generic(x)
    pi_x = pi * x
    (pi_x*cospi(x)-sinpi(x))/(pi_x*x)
end
```
-/
def coscGeneric (T : FTy) (x : FV T) : Jl (FV T) := do
  let piX := mul (piT T) x
  let c ← cospi T x
  let s ← sinpi T x
  return div (sub (mul piX c) s) (mul piX x)

/--
Julia source: base/special/trig.jl:1333-1366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cos_cardinal_eval(x::AbstractFloat, polynomials_close_to_origin::NTuple)
    function choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{2})
        ((b1, p0), (_, p1)) = polynomials_close_to_origin
        if a ≤ b1
            p0
        else
            p1
        end
    end
    function choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{4})
        ((b1, p0), (b2, p1), (b3, p2), (_, p3)) = polynomials_close_to_origin
        if a ≤ b2  # hardcoded binary search
            if a ≤ b1
                p0
            else
                p1
            end
        else
            if a ≤ b3
                p2
            else
                p3
            end
        end
    end
    a = abs(x)
    if (polynomials_close_to_origin !== ()) && (a ≤ polynomials_close_to_origin[end][1])
        x * evalpoly(x * x, choose_poly(a, polynomials_close_to_origin))
    elseif isinf(x)
        typeof(x)(0)
    else
        _cosc_generic(x)
    end
end
```
-/
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

/--
Julia source: base/special/trig.jl:1384-1391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cosc(x::Union{Float32, Float64})
    if x isa Float32
        pols = _cosc_f32
    else
        pols = _cosc_f64
    end
    _cos_cardinal_eval(x, pols)
end
```
-/
def coscF (T : FTy) (x : FV T) : Jl (FV T) :=
  match T with
  | .f32 => cosCardinalEval .f32 x (pairs 4 cosc32)
  | .f64 => cosCardinalEval .f64 x (pairs 6 cosc64)
  | .f16 => do return conv (← cosCardinalEval .f32 (conv x) (pairs 4 cosc32))
/--
Julia source: base/special/trig.jl:1401-1401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cosc(x::Float16) = Float16(_cosc(Float32(x)))
```
-/
def cosc16 (x : FV .f16) : Jl (FV .f16) := do return conv (← coscF .f32 (conv x))

/--
Julia source: base/special/trig.jl:1254-1254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cosc(x::Number) = _cosc(float(x))
```
-/
def cosc (T : FTy) (x : FV T) : Jl (FV T) :=
  match T, x with
  | .f16, x => cosc16 x
  | T, x => coscF T x

/--
Julia source: base/special/trig.jl:1395-1400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cosc(x::ComplexF64) =
    fastabs(x) < 0.14 ? x*evalpoly(x^2, (-3.289868133696453, 3.2469697011334144, -1.1445109447325053, 0.2091827825412384, -0.023460810354558236, 0.001781145516372852)) :
    isinf_real(x) ? zero(x) : _cosc_generic(x)
_cosc(x::ComplexF32) =
    fastabs(x) < 0.26f0 ? x*evalpoly(x^2, (-3.289868f0, 3.2469697f0, -1.144511f0, 0.20918278f0)) :
    isinf_real(x) ? zero(x) : _cosc_generic(x)
```
-/
def coscComplex {α β : Type} (ltβ : β → β → Bool) (fastabs : α → β) (threshold : β)
    (poly generic zero : α → α) (isinfReal : α → Bool) (x : α) : α :=
  if ltβ (fastabs x) threshold then poly x else if isinfReal x then zero x else generic x

/--
Julia source: base/special/trig.jl:1402-1402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cosc(x::ComplexF16) = ComplexF16(_cosc(ComplexF32(x)))
```
-/
def coscComplex16 {α β : Type} (convert32 : α → β) (convert16 : β → α)
    (cosc32 : β → β) (x : α) : α := convert16 (cosc32 (convert32 x))

/--
Julia source: base/special/trig.jl:1259-1281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cosc(x::Number)
    # naive cosc formula is susceptible to catastrophic
    # cancellation error near x=0, so we use the Taylor series
    # for small enough |x|.
    if fastabs(x) < 0.5
        # generic Taylor series: π ∑ (-1)^n (πx)^{2n-1}/a(n) where
        # a(n) = (1+2n)*(2n-1)! (= OEIS A174549)
        s = (term = -(π*x))/3
        iszero(s) && return s  # preserve floating-point signed zero
        π²x² = term^2
        ε = eps(fastabs(term)) # error threshold to stop sum
        n = 1
        while true
            n += 1
            term *= π²x²/((1-2n)*(2n-2))
            s += (δs = term/(1+2n))
            fastabs(δs) ≤ ε && break
        end
        return π*s
    else
        return isinf_real(x) ? zero(x) : _cosc_generic(x)
    end
end
```
-/
def coscSeries {α : Type} (pi : α) (mulα divα addα : α → α → α) (negα : α → α) (ofNat : Int → α)
    (iszero : α → Bool) (leα : α → α → Bool) (fabs eps : α → α) :
    Nat → α → α → α → α → Nat → JuliaLean.base.range.JlX α
  | 0, _, _, _, _, _ => .error (.errorException "fuel")
  | fuel + 1, s, term, pi2x2, e, n =>
    let n := n + 1
    let term := mulα term (divα pi2x2 (mulα (ofNat (1 - 2 * n)) (ofNat (2 * n - 2))))
    let ds := divα term (ofNat (1 + 2 * n))
    let s := addα s ds
    if leα (fabs ds) e then .ok (mulα pi s)
    else coscSeries pi mulα divα addα negα ofNat iszero leα fabs eps fuel s term pi2x2 e n

theorem coscSeries_zero_fuel {α : Type} (pi : α)
    (mul div add : α → α → α) (neg : α → α) (ofInt : Int → α)
    (iszero : α → Bool) (le : α → α → Bool) (abs eps : α → α)
    (s term square threshold : α) (n : Nat) :
    coscSeries pi mul div add neg ofInt iszero le abs eps 0 s term square threshold n =
      .error (.errorException "fuel") := rfl

/--
Julia source: base/special/trig.jl:1404-1433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (finv, f, finvh, fh, finvd, fd, fn) in ((:sec, :cos, :sech, :cosh, :secd, :cosd, "secant"),
                                            (:csc, :sin, :csch, :sinh, :cscd, :sind, "cosecant"),
                                            (:cot, :tan, :coth, :tanh, :cotd, :tand, "cotangent"))
    name = string(finv)
    hname = string(finvh)
    dname = string(finvd)
    @eval begin
        @doc """
            $($name)(x::T) where {T <: Number} -> float(T)

        Compute the $($fn) of `x`, where `x` is in radians.

        Throw a [`DomainError`](@ref) if `isinf(x)`, return a `T(NaN)` if `isnan(x)`.
        """ ($finv)(z::Number) = inv(($f)(z))
        @doc """
            $($hname)(x::T) where {T <: Number} -> float(T)

        Compute the hyperbolic $($fn) of `x`.

        Return a `T(NaN)` if `isnan(x)`.
        """ ($finvh)(z::Number) = inv(($fh)(z))
        @doc """
            $($dname)(x::T) where {T <: Number} -> float(T)

        Compute the $($fn) of `x`, where `x` is in degrees.

        Throw a [`DomainError`](@ref) if `isinf(x)`, return a `T(NaN)` if `isnan(x)`.
        """ ($finvd)(z::Number) = inv(($fd)(z))
    end
end
```
-/
def recipOf {α β γ : Type} (f : α → Jl β) (invβ : β → Jl γ) (z : α) : Jl γ := do
  invβ (← f z)
/--
Julia source: base/special/trig.jl:1435-1452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (tfa, tfainv, hfa, hfainv, fn) in ((:asec, :acos, :asech, :acosh, "secant"),
                                       (:acsc, :asin, :acsch, :asinh, "cosecant"),
                                       (:acot, :atan, :acoth, :atanh, "cotangent"))
    tname = string(tfa)
    hname = string(hfa)
    @eval begin
        @doc """
            $($tname)(x::T) where {T <: Number} -> float(T)

        Compute the inverse $($fn) of `x`, where the output is in radians.
        """ ($tfa)(y::Number) = ($tfainv)(inv(y))
        @doc """
            $($hname)(x::T) where {T <: Number} -> float(T)

        Compute the inverse hyperbolic $($fn) of `x`.
        """ ($hfa)(y::Number) = ($hfainv)(inv(y))
    end
end
```
-/
def invArgOf {α β γ : Type} (f : β → Jl γ) (invα : α → Jl β) (y : α) : Jl γ := do
  f (← invα y)

/--
Julia source: base/special/trig.jl:1456-1469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deg2rad_ext(x::Float64)
    m = 0.017453292519943295
    m_hi = 0.01745329238474369
    m_lo = 1.3519960527851425e-10

    u = 134217729.0*x # 0x1p27 + 1
    x_hi = u-(u-x)
    x_lo = x-x_hi

    y_hi = m*x
    y_lo = x_hi * m_lo + (x_lo* m_hi + ((x_hi*m_hi-y_hi) + x_lo*m_lo))

    DoubleFloat64(y_hi,y_lo)
end
```
-/
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
def oneEightyOverPi (T : FTy) : FV T := div (ofInt T 180) (piT T)
def piOverOneEighty (T : FTy) : FV T := div (piT T) (ofInt T 180)

/--
Julia source: base/special/trig.jl:1456-1470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deg2rad_ext(x::Float64)
    m = 0.017453292519943295
    m_hi = 0.01745329238474369
    m_lo = 1.3519960527851425e-10

    u = 134217729.0*x # 0x1p27 + 1
    x_hi = u-(u-x)
    x_lo = x-x_hi

    y_hi = m*x
    y_lo = x_hi * m_lo + (x_lo* m_hi + ((x_hi*m_hi-y_hi) + x_lo*m_lo))

    DoubleFloat64(y_hi,y_lo)
end
deg2rad_ext(x::Float32) = DoubleFloat32(deg2rad(Float64(x)))
```
-/
def deg2radExt (T : FTy) (x : FV T) : DF64 :=
  match T with
  | .f32 => ⟨deg2rad .f64 (conv x), zero .f64⟩
  | _ => deg2radExt64 (conv x)

/-- `sin_kernel`/`cos_kernel` on a `deg2rad_ext` argument. -/
def sinKd (T : FTy) (y : DF64) : FV T := sinK T y
def cosKd (T : FTy) (y : DF64) : FV T := cosK T y


/--
Julia source: base/special/trig.jl:1473-1502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sind(x::Real)
    if isinf(x)
        return throw_finite_domainerror(:sind, x)
    elseif isnan(x)
        return x
    end

    rx = copysign(float(rem(x,360)),x)
    arx = abs(rx)

    if rx == zero(rx)
        return rx
    elseif arx < oftype(rx,45)
        return sin_kernel(deg2rad_ext(rx))
    elseif arx <= oftype(rx,135)
        y = deg2rad_ext(oftype(rx,90) - arx)
        return copysign(cos_kernel(y),rx)
    elseif arx == oftype(rx,180)
        return copysign(zero(rx),rx)
    elseif arx < oftype(rx,225)
        y = deg2rad_ext((oftype(rx,180) - arx)*sign(rx))
        return sin_kernel(y)
    elseif arx <= oftype(rx,315)
        y = deg2rad_ext(oftype(rx,270) - arx)
        return -copysign(cos_kernel(y),rx)
    else
        y = deg2rad_ext(rx - copysign(oftype(rx,360),rx))
        return sin_kernel(y)
    end
end
```
-/
def sind (T : FTy) (x : FV T) : Jl (FV T) :=
  if x.isinf then finiteDomainError "sind"
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

/--
Julia source: base/special/trig.jl:1504-1528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cosd(x::Real)
    if isinf(x)
        return throw_finite_domainerror(:cosd, x)
    elseif isnan(x)
        return x
    end

    rx = abs(float(rem(x,360)))

    if rx <= oftype(rx,45)
        return cos_kernel(deg2rad_ext(rx))
    elseif rx < oftype(rx,135)
        y = deg2rad_ext(oftype(rx,90) - rx)
        return sin_kernel(y)
    elseif rx <= oftype(rx,225)
        y = deg2rad_ext(oftype(rx,180) - rx)
        return -cos_kernel(y)
    elseif rx < oftype(rx,315)
        y = deg2rad_ext(rx - oftype(rx,270))
        return sin_kernel(y)
    else
        y = deg2rad_ext(oftype(rx,360) - rx)
        return cos_kernel(y)
    end
end
```
-/
def cosd (T : FTy) (x : FV T) : Jl (FV T) :=
  if x.isinf then finiteDomainError "cosd"
  else if x.isnan then .ok x
  else
    let c (n : Int) : FV T := ofInt T n
    let rx := abs (FloatIntCov.Float.rem x (c 360))
    if le rx (c 45) then .ok (cosKd T (deg2radExt T rx))
    else if lt rx (c 135) then .ok (sinKd T (deg2radExt T (sub (c 90) rx)))
    else if le rx (c 225) then .ok (neg (cosKd T (deg2radExt T (sub (c 180) rx))))
    else if lt rx (c 315) then .ok (sinKd T (deg2radExt T (sub rx (c 270))))
    else .ok (cosKd T (deg2radExt T (sub (c 360) rx)))

/--
Julia source: base/special/trig.jl:1530-1530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tand(x::Real) = sind(x) / cosd(x)
```
-/
def tand (T : FTy) (x : FV T) : Jl (FV T) := do return div (← sind T x) (← cosd T x)

/--
Julia source: base/special/trig.jl:1543-1543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincosd(x) = (sind(x), cosd(x))
```
-/
def sincosd (T : FTy) (x : FV T) : Jl (FV T × FV T) := do return (← sind T x, ← cosd T x)

/--
Julia source: base/special/trig.jl:1604-1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:sind, :cosd, :tand)
    @eval $f(x::Float16) = isinf(x) ? throw_finite_domainerror($(QuoteNode(f)), x) : Float16($f(Float32(x)))
end
```
-/
def degF16 (f : FV .f32 → Jl (FV .f32)) (name : String) (x : FV .f16) : Jl (FV .f16) :=
  if x.isinf then finiteDomainError name else do return conv (← f (conv x))

/--
Julia source: base/special/trig.jl:1549-1566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fd, f, fn) in ((:sind, :sin, "sine"), (:cosd, :cos, "cosine"), (:tand, :tan, "tangent"))
    for (fu, un) in ((:deg2rad, "degrees"),)
        name = string(fd)
        @eval begin
            @doc """
                $($name)(x::T) where T -> float(T)

            Compute $($fn) of `x`, where `x` is in $($un).
            If `x` is a matrix, `x` needs to be a square matrix.

            Throw a [`DomainError`](@ref) if `isinf(x)`, return a `T(NaN)` if `isnan(x)`.

            !!! compat "Julia 1.7"
                Matrix arguments require Julia 1.7 or later.
            """ ($fd)(x) = ($f)(($fu).(x))
        end
    end
end
```
-/
def viaDeg2rad {α β γ : Type} (f : β → Jl γ) (d2r : α → Jl β) (x : α) : Jl γ := do
  f (← d2r x)

/--
Julia source: base/special/trig.jl:1568-1601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (fd, f, fn) in ((:asind, :asin, "sine"), (:acosd, :acos, "cosine"),
                    (:asecd, :asec, "secant"), (:acscd, :acsc, "cosecant"), (:acotd, :acot, "cotangent"))

    for (fu, un) in ((:rad2deg, "degrees"),)
        name = string(fd)
        @eval begin
            @doc """
                $($name)(x)

            Compute the inverse $($fn) of `x`, where the output is in $($un).
            If `x` is a matrix, `x` needs to be a square matrix.

            !!! compat "Julia 1.7"
                Matrix arguments require Julia 1.7 or later.
            """ ($fd)(x) = ($fu).(($f)(x))
        end
    end
end

"""
    atand(y::T) where T -> float(T)
    atand(y::T, x::S) where {T,S} -> promote_type(T,S)
    atand(y::AbstractMatrix{T}) where T -> AbstractMatrix{Complex{float(T)}}

Compute the inverse tangent of `y` or `y/x`, respectively, where the output is in degrees.

Return a `NaN` if `isnan(y)` or `isnan(x)`. The returned `NaN` is either a `T` in the single
argument version, or a `promote_type(T,S)` in the two argument version.

!!! compat "Julia 1.7"
    The one-argument method supports square matrix arguments as of Julia 1.7.
"""
atand(y)    = rad2deg.(atan(y))
atand(y, x) = rad2deg.(atan(y,x))
```
-/
def viaRad2deg {α β γ : Type} (f : α → Jl β) (r2d : β → Jl γ) (x : α) : Jl γ := do
  r2d (← f x)
/--
Julia source: base/special/trig.jl:1601-1601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atand(y, x) = rad2deg.(atan(y,x))
```
-/
def viaRad2deg2 {α β γ δ : Type} (atan : α → β → Jl γ) (r2d : γ → Jl δ)
    (y : α) (x : β) : Jl δ := do
  r2d (← atan y x)

/--
Julia source: base/special/trig.jl:1607-1610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for f in (:asind, :acosd, :asecd, :acscd, :acotd, :atand)
    @eval $f(x::Float16) = Float16($f(Float32(x)))
end
atand(y::Float16, x::Float16) = Float16(atand(Float32(y), Float32(x)))
```
-/
def invDegF16 (f : FV .f32 → Jl (FV .f32)) (x : FV .f16) : Jl (FV .f16) := do
  return conv (← f (conv x))
/--
Julia source: base/special/trig.jl:1610-1610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atand(y::Float16, x::Float16) = Float16(atand(Float32(y), Float32(x)))
```
-/
def invDegPairF16 (f : FV .f32 → FV .f32 → Jl (FV .f32))
    (y x : FV .f16) : Jl (FV .f16) := do
  return conv (← f (conv y) (conv x))

/--
Julia source: base/special/trig.jl:1547-1547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincosd(::Missing) = (missing, missing)
```
-/
def sincosdMissing : Option Unit × Option Unit := (none, none)
structure IntegerTrigOps (α β : Type) where
  nonnegative : α → Bool
  isodd : α → Bool
  toFloat : α → β
  zero : β → β
  one : β → β
  neg : β → β
  iszero : β → Bool

/--
Julia source: base/special/trig.jl:1074-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sinpi(x::Integer) = x >= 0 ? zero(float(x)) : -zero(float(x))
```
-/
def sinpiInteger {α β : Type} (o : IntegerTrigOps α β) (x : α) : β :=
  if o.nonnegative x then o.zero (o.toFloat x) else o.neg (o.zero (o.toFloat x))

/--
Julia source: base/special/trig.jl:1075-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cospi(x::Integer) = isodd(x) ? -one(float(x)) : one(float(x))
```
-/
def cospiInteger {α β : Type} (o : IntegerTrigOps α β) (x : α) : β :=
  if o.isodd x then o.neg (o.one (o.toFloat x)) else o.one (o.toFloat x)

/--
Julia source: base/special/trig.jl:1076-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tanpi(x::Integer) = x >= 0 ? (isodd(x) ? -zero(float(x)) : zero(float(x))) :
                             (isodd(x) ? zero(float(x)) : -zero(float(x)))
```
-/
def tanpiInteger {α β : Type} (o : IntegerTrigOps α β) (x : α) : β :=
  if o.nonnegative x then
    if o.isodd x then o.neg (o.zero (o.toFloat x)) else o.zero (o.toFloat x)
  else if o.isodd x then o.zero (o.toFloat x) else o.neg (o.zero (o.toFloat x))

/--
Julia source: base/special/trig.jl:1078-1078 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincospi(x::Integer) = (sinpi(x), cospi(x))
```
-/
def sincospiInteger {α β : Type} (o : IntegerTrigOps α β) (x : α) : β × β :=
  (sinpiInteger o x, cospiInteger o x)

structure IntegerSincOps (α : Type) where
  iszero : α → Bool
  one : α → α
  zero : α → α

/--
Julia source: base/special/trig.jl:1235-1235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sinc(x::Integer) = iszero(x) ? one(x) : zero(x)
```
-/
def sincInteger {α : Type} (o : IntegerSincOps α) (x : α) : α :=
  if o.iszero x then o.one x else o.zero x

/-- Typed callees used by the generic `Real` degree methods. Their types preserve the
argument/result relationship of `float`, `oftype`, `deg2rad_ext` and the trigonometric kernels. -/
structure RealDegreeOps (α β γ : Type) where
  isinf : α → Bool
  isnan : α → Bool
  float : α → β
  rem : α → Int → α
  ofInt : Int → α
  oftype : β → Int → β
  zero : β
  iszero : β → Bool
  abs : β → β
  copysignInput : β → α → β
  copysign : β → β → β
  eq : β → β → Bool
  lt : β → β → Bool
  le : β → β → Bool
  sub : β → β → β
  mul : β → β → β
  neg : β → β
  sign : β → β
  div : β → β → β
  isinfValue : β → Bool
  deg2radExt : β → γ
  sinKernel : γ → β
  cosKernel : γ → β
  domainError : String → Jl β

/--
Julia source: base/special/trig.jl:1473-1502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sind(x::Real)
    if isinf(x)
        return throw_finite_domainerror(:sind, x)
    elseif isnan(x)
        return x
    end

    rx = copysign(float(rem(x,360)),x)
    arx = abs(rx)

    if rx == zero(rx)
        return rx
    elseif arx < oftype(rx,45)
        return sin_kernel(deg2rad_ext(rx))
    elseif arx <= oftype(rx,135)
        y = deg2rad_ext(oftype(rx,90) - arx)
        return copysign(cos_kernel(y),rx)
    elseif arx == oftype(rx,180)
        return copysign(zero(rx),rx)
    elseif arx < oftype(rx,225)
        y = deg2rad_ext((oftype(rx,180) - arx)*sign(rx))
        return sin_kernel(y)
    elseif arx <= oftype(rx,315)
        y = deg2rad_ext(oftype(rx,270) - arx)
        return -copysign(cos_kernel(y),rx)
    else
        y = deg2rad_ext(rx - copysign(oftype(rx,360),rx))
        return sin_kernel(y)
    end
end
```
-/
def sindReal {α β γ : Type} (o : RealDegreeOps α β γ) (x : α) : Jl β :=
  if o.isinf x then o.domainError "sind"
  else if o.isnan x then .ok (o.float x)
  else
    let rx := o.copysignInput (o.float (o.rem x 360)) x
    let arx := o.abs rx
    if o.iszero rx then .ok rx
    else if o.lt arx (o.oftype rx 45) then .ok (o.sinKernel (o.deg2radExt rx))
    else if o.le arx (o.oftype rx 135) then
      let y := o.deg2radExt (o.sub (o.oftype rx 90) arx)
      .ok (o.copysign (o.cosKernel y) rx)
    else if o.eq arx (o.oftype rx 180) then .ok (o.copysign o.zero rx)
    else if o.lt arx (o.oftype rx 225) then
      let y := o.deg2radExt (o.mul (o.sub (o.oftype rx 180) arx) (o.sign rx))
      .ok (o.sinKernel y)
    else if o.le arx (o.oftype rx 315) then
      let y := o.deg2radExt (o.sub (o.oftype rx 270) arx)
      .ok (o.neg (o.copysign (o.cosKernel y) rx))
    else
      let y := o.deg2radExt (o.sub rx (o.copysign (o.oftype rx 360) rx))
      .ok (o.sinKernel y)

/--
Julia source: base/special/trig.jl:1504-1528 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cosd(x::Real)
    if isinf(x)
        return throw_finite_domainerror(:cosd, x)
    elseif isnan(x)
        return x
    end

    rx = abs(float(rem(x,360)))

    if rx <= oftype(rx,45)
        return cos_kernel(deg2rad_ext(rx))
    elseif rx < oftype(rx,135)
        y = deg2rad_ext(oftype(rx,90) - rx)
        return sin_kernel(y)
    elseif rx <= oftype(rx,225)
        y = deg2rad_ext(oftype(rx,180) - rx)
        return -cos_kernel(y)
    elseif rx < oftype(rx,315)
        y = deg2rad_ext(rx - oftype(rx,270))
        return sin_kernel(y)
    else
        y = deg2rad_ext(oftype(rx,360) - rx)
        return cos_kernel(y)
    end
end
```
-/
def cosdReal {α β γ : Type} (o : RealDegreeOps α β γ) (x : α) : Jl β :=
  if o.isinf x then o.domainError "cosd"
  else if o.isnan x then .ok (o.float x)
  else
    let rx := o.abs (o.float (o.rem x 360))
    if o.le rx (o.oftype rx 45) then .ok (o.cosKernel (o.deg2radExt rx))
    else if o.lt rx (o.oftype rx 135) then
      let y := o.deg2radExt (o.sub (o.oftype rx 90) rx)
      .ok (o.sinKernel y)
    else if o.le rx (o.oftype rx 225) then
      let y := o.deg2radExt (o.sub (o.oftype rx 180) rx)
      .ok (o.neg (o.cosKernel y))
    else if o.lt rx (o.oftype rx 315) then
      let y := o.deg2radExt (o.sub rx (o.oftype rx 270))
      .ok (o.sinKernel y)
    else
      let y := o.deg2radExt (o.sub (o.oftype rx 360) rx)
      .ok (o.cosKernel y)

/--
Julia source: base/special/trig.jl:1530-1530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tand(x::Real) = sind(x) / cosd(x)
```
-/
def tandReal {α β γ : Type} (o : RealDegreeOps α β γ) (x : α) : Jl β := do
  let s ← sindReal o x
  let c ← cosdReal o x
  pure (o.div s c)

/--
Julia source: base/special/trig.jl:1543-1543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincosd(x) = (sind(x), cosd(x))
```
-/
def sincosdReal {α β γ : Type} (o : RealDegreeOps α β γ) (x : α) : Jl (β × β) := do
  let s ← sindReal o x
  let c ← cosdReal o x
  pure (s, c)



end JuliaLean.base.special.trig

/-!
`sinpi`, `cospi`, `sincospi`, `tanpi` for `Float64` and `Int64` from `base/special/trig.jl`,
Julia master `bbfa0ce4150`, and the Float64 kernels of Julia 1.13.2 (tag `v1.13.2`).
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `_sinpi_kernel_polynomial_f64.c₁`; `base/special/trig.jl:907-908`. -/
def sinpiC1 : F64 × F64 := (lit 0x400921fb54442d18, lit 0x3ca1adc7bbf1b141)

/-- `_sinpi_kernel_polynomial_f64.rest`; `base/special/trig.jl:909-918`. -/
def sinpiRest : List F64 :=
  [lit 0xc014abbce625be53, lit 0x400466bc6775ab4d, lit 0xbfe32d2cce634924,
   lit 0x3fb50783492dcb22, lit 0xbf7e3075d7cb71a7, lit 0x3f3e8fb7e22504ca,
   lit 0xbef6fdb69126ffe7]

/-- `_cospi_kernel_polynomial_f64.c₀`; `base/special/trig.jl:896`. -/
def cospiC0 : F64 := lit 0x3ff0000000000000

/-- `_cospi_kernel_polynomial_f64.c₂`; `base/special/trig.jl:897`. -/
def cospiC2 : F64 × F64 := (lit 0xc013bd3cc9be45de, lit 0xbcb30f699892a25e)

/-- `_cospi_kernel_polynomial_f64.rest`; `base/special/trig.jl:898-905`. -/
def cospiRest : List F64 :=
  [lit 0x40103c1f081b5aae, lit 0xbff55d3c7e3c9254, lit 0x3fce1f5068363dd1,
   lit 0xbf9a6d1ec7b4d288, lit 0x3f5f9cc3eb9ab614, lit 0xbf1b26337cdaa924]

/-- `_sinpi_kernel(x, sch)` with `sch.c₁ = (c1, c1lo)` and `sch.rest = c3 :: rest`;
`base/special/trig.jl:785-796`. -/
def sinpiKernelWith (c1 c1lo c3 : F64) (rest : List F64) (x : F64) : F64 :=
  let x2 := F64.mul x x
  let r := if rest.isEmpty then F64.zero else horner x2 rest
  F64.muladd c1 x (F64.mul x (F64.muladd c3 x2 (F64.muladd (F64.mul x2 x2) r c1lo)))

/-- `_cospi_kernel(x, sch)` after the negations `c₂ = -c₂`, `c₂_lo = -c₂_lo`, so `c2`, `c2lo`
are the negated stored coefficients; `base/special/trig.jl:771-783`. The compiled code
(x86, `code_llvm`/`code_native` of `Base.Math._cospi_kernel` on master) merges the
multiplication inside `muladd(c₂, x², -a_x²)` with `a_x² = c₂ * x²`, so that `muladd` is not
fused and evaluates `a_x² - a_x²`; the other `muladd`s are fused. -/
def cospiKernelWith (c0 c2 c2lo : F64) (rest : List F64) (x : F64) : F64 :=
  let x2 := F64.mul x x
  let r := F64.mul (horner x2 rest) x2
  let ax2 := F64.mul c2 x2
  let ax2lo := F64.muladd c2lo x2 (F64.sub ax2 ax2)
  let w := F64.sub c0 ax2
  F64.add w (F64.muladd x2 r (F64.sub (F64.sub (F64.sub c0 w) ax2) ax2lo))

/-- `sinpi_kernel(x::Float64) = _sinpi_kernel_f64(x)`, also `sinpi_kernel_wide`;
`base/special/trig.jl:725-730,923`. -/
def sinpiKernel (x : F64) : F64 :=
  sinpiKernelWith sinpiC1.1 sinpiC1.2 (sinpiRest.headD F64.zero) sinpiRest.tail x

/-- `cospi_kernel(x::Float64) = _cospi_kernel_f64(x)`, also `cospi_kernel_wide`;
`base/special/trig.jl:749-754,921`. -/
def cospiKernel (x : F64) : F64 :=
  cospiKernelWith cospiC0 (F64.neg cospiC2.1) (F64.neg cospiC2.2) cospiRest x

/-- `sinpi_kernel_wide(x::Float64)` of Julia 1.13.2; `base/special/trig.jl:732-739` at `v1.13.2`. -/
def sinpiKernelRelease (x : F64) : F64 :=
  sinpiKernelWith (lit 0x400921fb54442d18) (lit 0x3ca1a5f14401a51a) (lit 0xc014abbce625be53)
    [lit 0x400466bc6775aad9, lit 0xbfe32d2cce62ac24, lit 0x3fb50783485cc005,
     lit 0xbf7e3074b502de17, lit 0x3f3e8eed159ae666, lit 0xbef6c5b93983c183] x

/-- `cospi_kernel_wide(x::Float64)` of Julia 1.13.2, with the same unfused
`muladd(4.934802200544679, x², -a_x²)` as `cospiKernelWith`; `base/special/trig.jl:761-770` at
`v1.13.2`. -/
def cospiKernelRelease (x : F64) : F64 :=
  cospiKernelWith (lit 0x3ff0000000000000) (lit 0x4013bd3cc9be45de) (lit 0x3cb6685bec517345)
    [lit 0x40103c1f081b5ac0, lit 0xbff55d3c7e3cb0f5, lit 0x3fce1f506865cf50,
     lit 0xbf9a6d1eeca77196, lit 0x3f5f9cdff3b5e8c1, lit 0xbf1b2e7995b6bda9] x

/-- Integer value of an integral finite float, as `Int64(n)` for `|n| < 2^63`;
`base/special/trig.jl:946`. -/
private def intValue (n : F64) : Int :=
  let q := F64.toRat n
  q.1 / (q.2 : Int)

/-- Shared reduction `n = round(2*x)`, `rx = muladd(-0.5, n, x)`, `n = Int64(n) & 3`;
`base/special/trig.jl:944-946`. -/
def piReduce (x : F64) : F64 × Int :=
  let n := F64.round (F64.mul (F64.ofInt 2) x) .RoundNearest
  let rx := F64.muladd (lit 0xbfe0000000000000) n x
  (rx, intValue n % 4)

/-- `sinpi(_x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:934-956`. -/
def sinpiWith (sk ck : F64 → F64) (x0 : F64) : Jl F64 :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok x else .error (.domainError "sinpi")
  else if F64.le maxintfloat x then .ok (copysign F64.zero x0)
  else
    let p := piReduce x
    let rx := p.1
    let n := p.2
    let res :=
      if n == 0 then sk rx
      else if n == 1 then ck rx
      else if n == 2 then F64.sub F64.zero (sk rx)
      else F64.sub F64.zero (ck rx)
    .ok (if F64.signbit x0 then F64.neg res else res)

/-- `cospi(x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:968-990`. -/
def cospiWith (sk ck : F64 → F64) (x0 : F64) : Jl F64 :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok x else .error (.domainError "cospi")
  else if F64.le maxintfloat x then .ok F64.one
  else
    let p := piReduce x
    let rx := p.1
    let n := p.2
    if n == 0 then .ok (ck rx)
    else if n == 1 then .ok (F64.sub F64.zero (sk rx))
    else if n == 2 then .ok (F64.sub F64.zero (ck rx))
    else .ok (sk rx)

/-- The quadrant selection of `sincospi`/`tanpi`; `base/special/trig.jl:1018-1029`. -/
private def sincosQuadrant (sk ck : F64 → F64) (x0 x : F64) : F64 × F64 :=
  let p := piReduce x
  let rx := p.1
  let n := p.2
  let si := sk rx
  let co := ck rx
  let q :=
    if n == 0 then (si, co)
    else if n == 1 then (co, F64.sub F64.zero si)
    else if n == 2 then (F64.sub F64.zero si, F64.sub F64.zero co)
    else (F64.sub F64.zero co, si)
  (if F64.signbit x0 then F64.neg q.1 else q.1, q.2)

/-- `sincospi(_x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:1005-1030`. -/
def sincospiWith (sk ck : F64 → F64) (x0 : F64) : Jl (F64 × F64) :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok (x, x) else .error (.domainError "sincospi")
  else if F64.le maxintfloat x then .ok (copysign F64.zero x0, F64.one)
  else .ok (sincosQuadrant sk ck x0 x)

/-- `tanpi(_x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:1044-1071`. -/
def tanpiWith (sk ck : F64 → F64) (x0 : F64) : Jl F64 :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok x else .error (.domainError "tanpi")
  else if F64.le maxintfloat x then .ok (copysign F64.zero x0)
  else
    let q := sincosQuadrant sk ck x0 x
    .ok (F64.div q.1 q.2)

/-- `sinpi(::Float64)`; `base/special/trig.jl:934-956`. -/
def sinpi (x : F64) : Jl F64 := sinpiWith sinpiKernel cospiKernel x

/-- `cospi(::Float64)`; `base/special/trig.jl:968-990`. -/
def cospi (x : F64) : Jl F64 := cospiWith sinpiKernel cospiKernel x

/-- `sincospi(::Float64)`; `base/special/trig.jl:1005-1030`. -/
def sincospi (x : F64) : Jl (F64 × F64) := sincospiWith sinpiKernel cospiKernel x

/-- `tanpi(::Float64)`; `base/special/trig.jl:1044-1071`. -/
def tanpi (x : F64) : Jl F64 := tanpiWith sinpiKernel cospiKernel x

/-- `sinpi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:796-817` at `v1.13.2`. -/
def sinpiRelease (x : F64) : Jl F64 := sinpiWith sinpiKernelRelease cospiKernelRelease x

/-- `cospi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:829-850` at `v1.13.2`. -/
def cospiRelease (x : F64) : Jl F64 := cospiWith sinpiKernelRelease cospiKernelRelease x

/-- `sincospi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:865-889` at `v1.13.2`. -/
def sincospiRelease (x : F64) : Jl (F64 × F64) :=
  sincospiWith sinpiKernelRelease cospiKernelRelease x

/-- `tanpi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:904-931` at `v1.13.2`. -/
def tanpiRelease (x : F64) : Jl F64 := tanpiWith sinpiKernelRelease cospiKernelRelease x

/-- `sinpi(x::Integer)` for `Int64`; `base/special/trig.jl:1074`. -/
def sinpiInt (n : Int) : F64 := if n ≥ 0 then F64.zero else F64.neg F64.zero

/-- `cospi(x::Integer)` for `Int64`; `base/special/trig.jl:1075`. -/
def cospiInt (n : Int) : F64 := if n % 2 != 0 then F64.neg F64.one else F64.one

/-- `tanpi(x::Integer)` for `Int64`; `base/special/trig.jl:1076-1077`. -/
def tanpiInt (n : Int) : F64 :=
  if n ≥ 0 then (if n % 2 != 0 then F64.neg F64.zero else F64.zero)
  else (if n % 2 != 0 then F64.zero else F64.neg F64.zero)

end JuliaLean.MathFuncs

/-!
`sin`, `cos`, `sincos`, `tan` and their kernels, `asin`, `acos`, `atan`, two-argument
`atan` and their constants, for `Float32` and `Float64`; `base/special/trig.jl:28-722`
at Julia master `bbfa0ce4150`. Argument reduction is `MathFuncs.remPio2Kernel`
(`Float64`) and `Special.remPio2Kernel32` (`Float32`).
-/

namespace JuliaLean.MathCov.Trig

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- `l[i]` (zero-based) of a constant table. -/
def nth {T : FTy} (l : List (FV T)) (i : Nat) : FV T := l.getD i (nan T)

/-! ## Float64 kernels, `base/special/trig.jl:68-81,134-149,234-334` -/

/-- `sin_kernel(y::DoubleFloat64)`. -/
def sinKernelD (y : DF64) : FV .f64 :=
  let y2 := mul y.hi y.hi
  let y4 := mul y2 y2
  let r := add (horner y2 [nth DS 1, nth DS 2, nth DS 3]) (mul (mul y2 y4) (horner y2 [nth DS 4, nth DS 5]))
  let y3 := mul y2 y.hi
  sub y.hi (sub (sub (mul y2 (sub (mul h64 y.lo) (mul y3 r))) y.lo) (mul y3 (nth DS 0)))

/-- `sin_kernel(y::Float64)`. -/
def sinKernel64 (y : FV .f64) : FV .f64 :=
  let y2 := mul y y
  let y4 := mul y2 y2
  let r := add (horner y2 [nth DS 1, nth DS 2, nth DS 3]) (mul (mul y2 y4) (horner y2 [nth DS 4, nth DS 5]))
  let y3 := mul y2 y
  add y (mul y3 (add (nth DS 0) (mul y2 r)))

/-- `cos_kernel(y::DoubleFloat64)`. -/
def cosKernelD (y : DF64) : FV .f64 :=
  let y2 := mul y.hi y.hi
  let y4 := mul y2 y2
  let r := add (mul y2 (horner y2 [nth DC 0, nth DC 1, nth DC 2])) (mul (mul y4 y4) (horner y2 [nth DC 3, nth DC 4, nth DC 5]))
  let halfY2 := mul h64 y2
  let w := sub one64 halfY2
  add w (add (sub (sub one64 w) halfY2) (sub (mul y2 r) (mul y.hi y.lo)))

/-- `cos_kernel(y::Float64)`. -/
def cosKernel64 (y : FV .f64) : FV .f64 :=
  let y2 := mul y y
  let y4 := mul y2 y2
  let r := add (mul y2 (horner y2 [nth DC 0, nth DC 1, nth DC 2])) (mul (mul y4 y4) (horner y2 [nth DC 3, nth DC 4, nth DC 5]))
  let halfY2 := mul h64 y2
  let w := sub one64 halfY2
  add w (add (sub (sub one64 w) halfY2) (mul y2 r))

/-- Clear the low 32 bits: `reinterpret(Float64, (reinterpret(UInt64, x) >> 32) << 32)`. -/
def clearLow (x : FV .f64) : FV .f64 := Fl.ofBits (x.toBits / 2 ^ 32 * 2 ^ 32)

/-- `tan_kernel(y::DoubleFloat64, k)`. -/
def tanKernelD (y : DF64) (k : Int) : FV .f64 :=
  let big := le (nth tanMisc64 0) (abs y.hi)
  let (yhi, ylo) :=
    if big then
      let (yhi, ylo) := if lt y.hi (zero .f64) then (neg y.hi, neg y.lo) else (y.hi, y.lo)
      (add (sub (nth tanMisc64 1) yhi) (sub (nth tanMisc64 2) ylo), zero .f64)
    else (y.hi, y.lo)
  let y2 := mul yhi yhi
  let y4 := mul y2 y2
  let r := horner y4 (tanT64.take 6)
  let v := mul y2 (horner y4 (tanT64.drop 6))
  let y3 := mul y2 yhi
  let r := add ylo (mul y2 (add (mul y3 (add r v)) ylo))
  let r := add r (mul (nth tanMisc64 3) y3)
  let px := add yhi r
  let kf : FV .f64 := ofInt .f64 k
  if big then
    mul (if y.hi.signbit then neg one64 else one64)
      (sub kf (mul two64 (sub yhi (sub (div (mul px px) (add kf px)) r))))
  else if k == 1 then px
  else
    let px0 := clearLow px
    let v := sub r (sub px0 yhi)
    let a := div (neg one64) px
    let t := clearLow a
    let s := add one64 (mul t px0)
    add t (mul a (add s (mul t v)))

/-- `tan_kernel(y::Float64) = tan_kernel(DoubleFloat64(y, 0.0), 1)`. -/
def tanKernel64 (y : FV .f64) : FV .f64 := tanKernelD ⟨y, zero .f64⟩ 1

/-! ## Float32 kernels, `base/special/trig.jl:84-93,152-160,336-351`. `DoubleFloat32(x)`
holds `Float64(x)`. -/

/-- `sin_kernel(y::DoubleFloat32)`; `sin_kernel(x::Float32)` applies it to `Float64(x)`. -/
def sinKernel32 (hi : FV .f64) : FV .f32 :=
  let z := mul hi hi
  let w := mul z z
  let r := horner z [nth sinK32 2, nth sinK32 3]
  let s := mul z hi
  conv (add (add hi (mul s (horner z [nth sinK32 0, nth sinK32 1]))) (mul (mul s w) r))

/-- `cos_kernel(y::DoubleFloat32)`; `cos_kernel(x::Float32)` applies it to `Float64(x)`. -/
def cosKernel32 (hi : FV .f64) : FV .f32 :=
  let y2 := mul hi hi
  let y4 := mul y2 y2
  let r := horner y2 [nth cosK32 2, nth cosK32 3]
  conv (add (add (add one64 (mul y2 (nth cosK32 0))) (mul y4 (nth cosK32 1))) (mul (mul y4 y2) r))

/-- `tan_kernel(y::DoubleFloat32, k)`; `tan_kernel(y::Float32)` is `k = 1`. -/
def tanKernel32 (hi : FV .f64) (k : Int) : FV .f32 :=
  let y2 := mul hi hi
  let r := horner y2 [nth tanK32 0, nth tanK32 1]
  let t := horner y2 [nth tanK32 2, nth tanK32 3]
  let y4 := mul y2 y2
  let y3 := mul y2 hi
  let u := horner y2 [nth tanK32 4, nth tanK32 5]
  let py := add (add hi (mul y3 u)) (mul (mul y3 y4) (add t (mul y4 r)))
  if k == 1 then conv py else conv (div (neg one64) py)

/-! ## The public functions, generic over `T ∈ {Float32, Float64}` -/

/-- Reduced argument: `n` and the kernel argument (`DoubleFloat64` or `DoubleFloat32`). -/
def reduce : (T : FTy) → FV T → Int × DF64
  | .f32, x => let (n, y) := Special.remPio2Kernel32 x; (n, ⟨y, zero .f64⟩)
  | _, x => let (n, hi, lo) := MathFuncs.remPio2Kernel (toD x); (n, ⟨Fl.ofF64 hi, Fl.ofF64 lo⟩)

/-- `sin_kernel`, `cos_kernel` on a reduced argument. -/
def sinK : (T : FTy) → DF64 → FV T
  | .f32, y => conv (sinKernel32 y.hi)
  | _, y => conv (sinKernelD y)
def cosK : (T : FTy) → DF64 → FV T
  | .f32, y => conv (cosKernel32 y.hi)
  | _, y => conv (cosKernelD y)
/-- `sin_kernel(x)`, `cos_kernel(x)`, `tan_kernel(x)` on an unreduced `x::T`. -/
def sinK1 : (T : FTy) → FV T → FV T
  | .f32, x => conv (sinKernel32 (conv x))
  | _, x => conv (sinKernel64 (conv x))
def cosK1 : (T : FTy) → FV T → FV T
  | .f32, x => conv (cosKernel32 (conv x))
  | _, x => conv (cosKernel64 (conv x))
def tanK : (T : FTy) → DF64 → Int → FV T
  | .f32, y, k => conv (tanKernel32 y.hi k)
  | _, y, k => conv (tanKernelD y k)
def tanK1 : (T : FTy) → FV T → FV T
  | .f32, x => conv (tanKernel32 (conv x) 1)
  | _, x => conv (tanKernel64 (conv x))

/-- `T(pi)/4`, `sqrt(eps(T))`, `sqrt(eps(T)/T(2.0))`, `sqrt(eps(T))/2`. -/
def piO4 : (T : FTy) → FV T | .f32 => conv piOver4_32 | _ => conv piOver4_64
def sqrtEps : (T : FTy) → FV T | .f32 => conv sqrtEps32 | _ => conv sqrtEps64
def sqrtHalfEps : (T : FTy) → FV T | .f32 => conv sqrtHalfEps32 | _ => conv sqrtHalfEps64
def halfSqrtEps : (T : FTy) → FV T | .f32 => conv halfSqrtEps32 | _ => conv halfSqrtEps64


/-- `sin(x::T) where T<:Union{Float32, Float64}`; `base/special/trig.jl:28-51`. -/
def sin (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if lt absx (piO4 T) then
    if lt absx (sqrtEps T) then .ok x else .ok (sinK1 T x)
  else if x.isnan then .ok x
  else if x.isinf then finiteDomainError "sin"
  else
    let (n, y) := reduce T x
    let n := n % 4
    .ok (if n == 0 then sinK T y else if n == 1 then cosK T y
      else if n == 2 then neg (sinK T y) else neg (cosK T y))

/-- `cos(x::T) where T<:Union{Float32, Float64}`; `base/special/trig.jl:96-120`. -/
def cos (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if lt absx (piO4 T) then
    if lt absx (sqrtHalfEps T) then .ok (one T) else .ok (cosK1 T x)
  else if x.isnan then .ok x
  else if x.isinf then finiteDomainError "cos"
  else
    let (n, y) := reduce T x
    let n := n % 4
    .ok (if n == 0 then cosK T y else if n == 1 then neg (sinK T y)
      else if n == 2 then neg (cosK T y) else sinK T y)

/-- `sincos_kernel(y) = (sin_kernel(y), cos_kernel(y))`; `base/special/trig.jl:211`. -/
def sincosK (T : FTy) (y : DF64) : FV T × FV T := (sinK T y, cosK T y)
def sincosK1 (T : FTy) (x : FV T) : FV T × FV T := (sinK1 T x, cosK1 T x)

/-- `sincos(x::T) where T<:Union{Float32, Float64}`; `base/special/trig.jl:174-200`. -/
def sincos (T : FTy) (x : FV T) : Jl (FV T × FV T) :=
  if lt (abs x) (piO4 T) then
    if eq x (zero T) then .ok (x, one T) else .ok (sincosK1 T x)
  else if x.isnan then .ok (x, x)
  else if x.isinf then finiteDomainError "sincos"
  else
    let (n, y) := reduce T x
    let n := n % 4
    let (si, co) := sincosK T y
    .ok (if n == 0 then (si, co) else if n == 1 then (co, neg si)
      else if n == 2 then (neg si, neg co) else (neg co, si))

/-- `_sincos(x::AbstractFloat) = sincos(x)`; `base/special/trig.jl:202`. -/
def sincosAbstract {α β : Type} (sincos : α → β) (x : α) : β := sincos x

/-- `_sincos(x) = (sin(x), cos(x))`; `base/special/trig.jl:203`. -/
def sincosFallback {α β : Type} (sin cos : α → β) (x : α) : β × β := (sin x, cos x)

/-- `sincos(x) = _sincos(float(x))`; `base/special/trig.jl:205`. -/
def sincosGeneric {α β γ : Type} (float : α → β) (sincos : β → γ) (x : α) : γ :=
  sincos (float x)

/-- `tan(x::T) where T<:Union{Float32, Float64}`; `base/special/trig.jl:214-232`. -/
def tan (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if lt absx (piO4 T) then
    if lt absx (halfSqrtEps T) then .ok x else .ok (tanK1 T x)
  else if x.isnan then .ok x
  else if x.isinf then finiteDomainError "tan"
  else
    let (n, y) := reduce T x
    .ok (if n % 2 == 0 then tanK T y 1 else tanK T y (-1))

/-- `sin_kernel(x::Real) = sin(x)` and the other fallbacks; `base/special/trig.jl:354-357`. -/
def sinKernelReal {α β : Type} (sinf : α → β) (x : α) : β := sinf x

/-! ## asin, `base/special/trig.jl:361-450` -/

/-- `arc_p`, `arc_q`, `arc_tRt` for `Float64` and `Float32`. -/
def arcP : (T : FTy) → FV T → FV T
  | .f32, t => mul t (horner t arcP32)
  | .f64, t => mul t (horner t arcP64)
  | .f16, t => t
def arcQ : (T : FTy) → FV T → FV T
  | .f32, t => horner t arcQ32
  | .f64, t => horner t arcQ64
  | .f16, t => t
def arcTRt (T : FTy) (t : FV T) : FV T := div (arcP T t) (arcQ T t)

/-- `asin_kernel(t::Float64, x::Float64)`. -/
def asinKernel64 (t x : FV .f64) : FV .f64 :=
  let pio2Lo := nth asinMisc64 0
  let s := sqrtLlvm t
  let tRt := arcTRt .f64 t
  if le (nth asinMisc64 1) (abs x) then
    flipsign (sub (nth asinMisc64 2) (sub (mul two64 (add s (mul s tRt))) pio2Lo)) x
  else
    let s0 := clearLow s
    let c := div (sub t (mul s0 s0)) (add s s0)
    let p := sub (mul (mul two64 s) tRt) (sub pio2Lo (mul two64 c))
    let q := sub (nth asinMisc64 3) (mul two64 s0)
    flipsign (sub (nth asinMisc64 3) (sub p q)) x

/-- `asin_kernel(t::Float32, x::Float32)`. -/
def asinKernel32 (t x : FV .f32) : FV .f32 :=
  let s := sqrtLlvm (conv t : FV .f64)
  let tRt := arcTRt .f32 t
  flipsign (conv (sub (nth asinMisc64 2) (mul two64 (add s (mul s (conv tRt))))) : FV .f32) x

def asinKernel : (T : FTy) → FV T → FV T → FV T
  | .f32, t, x => asinKernel32 t x
  | _, t, x => conv (asinKernel64 (conv t) (conv x))

/-- `ASIN_X_MIN_THRESHOLD(T)`; `base/special/trig.jl:361-362`. -/
def asinMin : (T : FTy) → FV T | .f32 => conv asinMin32 | _ => conv asinMin64

/-- `asin_domain_error(x)`; `base/special/trig.jl:425`. -/
def asinDomainError {α : Type} : Jl α := .error (.domainError "asin(x) is not defined for |x| > 1.")

/-- `asin(x::T) where T<:Union{Float32, Float64}`. -/
def asin (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if le (one T) absx then
    if eq absx (one T) then .ok (flipsign (div (piT T) (ofInt T 2)) x) else asinDomainError
  else if lt absx (div (one T) (ofInt T 2)) then
    if lt absx (asinMin T) then .ok x
    else .ok (muladd x (arcTRt T (mul x x)) x)
  else
    let t := div (sub (one T) absx) (ofInt T 2)
    .ok (asinKernel T t x)
where
  piT : (T : FTy) → FV T | .f32 => piT32 | .f64 => piT64 | .f16 => conv piT32

/-! ## atan, `base/special/trig.jl:453-554` -/

def atanHi : (T : FTy) → Nat → FV T | .f32, i => nth atanHi32 i | _, i => conv (nth atanHi64 i)
def atanLo : (T : FTy) → Nat → FV T | .f32, i => nth atanLo32 i | _, i => conv (nth atanLo64 i)
def atanLarge : (T : FTy) → FV T | .f32 => atanLarge32 | _ => conv atanLarge64
def atanSmall : (T : FTy) → FV T | .f32 => atanSmall32 | _ => conv atanSmall64
def atanBreak : (T : FTy) → Nat → FV T | .f32, i => nth atanBreaks32 i | _, i => conv (nth atanBreaks64 i)

/-- `atan_p(z, w)`, `atan_q(w)`, `atan_pq(x)`. -/
def atanP : (T : FTy) → FV T → FV T → FV T
  | .f32, z, w => mul z (horner w atanP32)
  | _, z, w => conv (mul (conv z : FV .f64) (horner (conv w) atanP64))
def atanQ : (T : FTy) → FV T → FV T
  | .f32, w => mul w (horner w atanQ32)
  | _, w => conv (mul (conv w : FV .f64) (horner (conv w) atanQ64))
def atanPQ (T : FTy) (x : FV T) : FV T × FV T :=
  let x2 := mul x x
  let x4 := mul x2 x2
  (atanP T x2 x4, atanQ T x4)


/-- `atan(x::T) where T<:Union{Float32, Float64}`. -/
def atan (T : FTy) (x : FV T) : FV T :=
  let absx := abs x
  if le (atanLarge T) absx then copysign (atanBreak T 5) x
  else if lt absx (atanBreak T 0) then
    if lt absx (atanSmall T) then x
    else
      let (p, q) := atanPQ T x
      sub x (mul x (add p q))
  else
    let xsign := signF x
    let two := ofInt T 2
    let (hi, lo, x) :=
      if lt absx (atanBreak T 2) then
        if lt absx (atanBreak T 1) then
          (atanHi T 0, atanLo T 0, div (sub (mul two absx) (one T)) (add two absx))
        else (atanHi T 1, atanLo T 1, div (sub absx (one T)) (add absx (one T)))
      else if lt absx (atanBreak T 3) then
        (atanHi T 2, atanLo T 2, div (sub absx (atanBreak T 4)) (add (one T) (mul (atanBreak T 4) absx)))
      else (atanHi T 3, atanLo T 3, div (neg (one T)) absx)
    let (p, q) := atanPQ T x
    let z := sub hi (sub (sub (mul x (add p q)) lo) x)
    copysign z xsign

/-- `ATAN2_PI_LO(T)`, `ATAN2_RATIO_BIT_SHIFT(T)`, `ATAN2_RATIO_THRESHOLD(T)`;
`base/special/trig.jl:556-562`. -/
def atan2PiLo : (T : FTy) → FV T | .f32 => atan2PiLo32 | _ => conv atan2PiLo64
def atan2Shift : FTy → Nat | .f32 => 23 | _ => 20
def atan2Threshold : FTy → Int | .f32 => 26 | _ => 60

def piO2T : (T : FTy) → FV T | .f32 => piOver2T32 | _ => conv piOver2T64
def piO4T : (T : FTy) → FV T | .f32 => piOver4T32 | _ => conv piOver4T64
def threePiO4T : (T : FTy) → FV T | .f32 => threePiOver4T32 | _ => conv threePiOver4T64

/-- `poshighword` of either format. -/
def poshw {T : FTy} (x : FV T) : Nat :=
  if T = .f32 then x.toBits % 2 ^ 31 else Bits.poshighwordU64 x.toBits

/-- `atan(y::T, x::T) where T<:Union{Float32, Float64}`; `base/special/trig.jl:564-655`. -/
def atan2 (T : FTy) (y x : FV T) : FV T := Id.run do
  if x.isnan || y.isnan then return (if x.isnan then x else y)
  if eq x (one T) then return atan T y
  let mut m : Nat := 2 * (if x.signbit then 1 else 0) + (if y.signbit then 1 else 0)
  if y.iszero then
    if m == 0 || m == 1 then return y
    else if m == 2 then return piT T
    else return neg (piT T)
  else if x.iszero then return flipsign (piO2T T) y
  if x.isinf then
    if y.isinf then
      return (if m == 0 then piO4T T else if m == 1 then neg (piO4T T)
        else if m == 2 then threePiO4T T else neg (threePiO4T T))
    else
      return (if m == 0 then zero T else if m == 1 then zero T true
        else if m == 2 then piT T else neg (piT T))
  if y.isinf then return copysign (piO2T T) y
  let k : Int := (wrapInt .i32 ((poshw y + 2 ^ 32 - poshw x) % 2 ^ 32)).fdiv (2 ^ atan2Shift T)
  let mut z := zero T
  if k > atan2Threshold T then
    z := add (piO2T T) (mul (div (one T) (ofInt T 2)) (atan2PiLo T))
    m := m % 2
  else if lt x (zero T) && k < -atan2Threshold T then z := zero T
  else z := atan T (abs (div y x))
  return (if m == 0 then z else if m == 1 then neg z
    else if m == 2 then sub (piT T) (sub z (atan2PiLo T))
    else sub (sub z (atan2PiLo T)) (piT T))

/-! ## acos, `base/special/trig.jl:657-722` -/

def acosMin : (T : FTy) → FV T | .f32 => acosMin32 | _ => conv acosMin64
def pio2Hi : (T : FTy) → FV T | .f32 => pio2Hi32 | _ => conv pio2Hi64
def pio2Lo : (T : FTy) → FV T | .f32 => pio2Lo32 | _ => conv pio2Lo64
def acosPi : (T : FTy) → FV T | .f32 => acosPi32 | _ => conv acosPi64
/-- `ACOS_CORRECT_LOWWORD(T, x)`. -/
def acosLowword {T : FTy} (x : FV T) : FV T :=
  if T = .f32 then Fl.ofBits (x.toBits / 2 ^ 12 * 2 ^ 12) else Fl.ofBits (x.toBits / 2 ^ 32 * 2 ^ 32)

/-- `acos_domain_error(x)`; `base/special/trig.jl:668`. -/
def acosDomainError {α : Type} : Jl α := .error (.domainError "acos(x) not defined for |x| > 1")

/-- `acos(x::T) where T <: Union{Float32, Float64}`. -/
def acos (T : FTy) (x : FV T) : Jl (FV T) :=
  let absx := abs x
  if le (one T) absx then
    if eq absx (one T) then .ok (if lt (zero T) x then zero T else piT T) else acosDomainError
  else if lt absx (div (one T) (ofInt T 2)) then
    if lt absx (acosMin T) then .ok (piO2T T)
    else .ok (sub (pio2Hi T) (sub x (sub (pio2Lo T) (mul x (arcTRt T (mul x x))))))
  else
    let z := mul (sub (one T) absx) (div (one T) (ofInt T 2))
    let zRz := arcTRt T z
    let s := sqrtLlvm z
    if lt x (zero T) then
      .ok (sub (acosPi T) (mul (ofInt T 2) (add s (sub (mul zRz s) (pio2Lo T)))))
    else
      let df := acosLowword s
      let c := div (sub z (mul df df)) (add s df)
      .ok (mul (ofInt T 2) (add df (add (mul zRz s) c)))

end JuliaLean.MathCov.Trig

/-!
`sinpi`, `cospi`, `sincospi`, `tanpi` and their kernels for the three IEEE formats,
the `Integer` and generic `AbstractFloat` methods, and the `Complex` methods;
`base/special/trig.jl:725-1207` at Julia master `bbfa0ce4150`. Master rewrote the
kernel polynomials (#59031); 1.13.2 uses the older coefficients.
-/

namespace JuliaLean.MathCov.TrigPi

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathCov.Trig (nth horner)

/-- `_cospi_kernel(x, sch)` with `sch = [c₀, c₂, c₂_lo, rest...]`; `base/special/trig.jl:771-783`. -/
def cospiKernelSch {T : FTy} (sch : List (FV T)) (x : FV T) : FV T :=
  let x2 := mul x x
  let c0 := nth sch 0
  let c2 := neg (nth sch 1)
  let c2lo := neg (nth sch 2)
  let r := mul (horner x2 (sch.drop 3)) x2
  let ax2 := mul c2 x2
  let ax2lo := add (mul c2lo x2) (add (mul c2 x2) (neg ax2))
  let w := sub c0 ax2
  add w (muladd x2 r (sub (sub (sub c0 w) ax2) ax2lo))

/-- `_sinpi_kernel(x, sch)` with `sch = [c₁, c₁_lo, c₃, rest...]`; `base/special/trig.jl:785-795`. -/
def sinpiKernelSch {T : FTy} (sch : List (FV T)) (x : FV T) : FV T :=
  let x2 := mul x x
  let c1 := nth sch 0
  let c1lo := nth sch 1
  let c3 := nth sch 2
  let rest := sch.drop 3
  let r := if rest.isEmpty then zero T else horner x2 rest
  muladd c1 x (mul x (muladd c3 x2 (muladd (mul x2 x2) r c1lo)))

/-- The widened type of `sinpi_kernel_wide`: `Float32` for `Float16`, else `Float64`. -/
def wideTy : FTy → FTy | .f16 => .f32 | _ => .f64

/-- `sinpi_kernel_wide(x::T)`; `base/special/trig.jl:728-746`. -/
def sinpiKernelWide : (T : FTy) → FV T → FV (wideTy T)
  | .f64, x => sinpiKernelSch sinpiPoly64 x
  | .f32, x => let w : FV .f64 := conv x; mul w (horner (mul w w) sinpiWide32)
  | .f16, x => let w : FV .f32 := conv x; mul w (horner (mul w w) sinpiWide16)

/-- `cospi_kernel_wide(x::T)`; `base/special/trig.jl:752-769`. -/
def cospiKernelWide : (T : FTy) → FV T → FV (wideTy T)
  | .f64, x => cospiKernelSch cospiPoly64 x
  | .f32, x => let w : FV .f64 := conv x; horner (mul w w) cospiWide32
  | .f16, x => let w : FV .f32 := conv x; horner (mul w w) cospiWide16

/-- `sinpi_kernel(x::T)`; `base/special/trig.jl:725-742`. -/
def sinpiKernel : (T : FTy) → FV T → FV T
  | .f64, x => sinpiKernelSch sinpiPoly64 x
  | .f32, x => sinpiKernelSch sinpiPoly32 x
  | .f16, x => conv (sinpiKernelWide .f16 x)

/-- `cospi_kernel(x::T)`; `base/special/trig.jl:749-765`. -/
def cospiKernel : (T : FTy) → FV T → FV T
  | .f64, x => cospiKernelSch cospiPoly64 x
  | .f32, x => cospiKernelSch cospiPoly32 x
  | .f16, x => conv (cospiKernelWide .f16 x)

/-- `n = round(2*x)`, `rx = float(muladd(T(-.5), n, x))`, `n = Int64(n) & 3`; the shared
reduction of the four functions. -/
def piReduce {T : FTy} (x : FV T) : FV T × Int :=
  let n := roundI (mul (ofInt T 2) x)
  let rx := muladd (neg (div (one T) (ofInt T 2))) n x
  (rx, ((n.toRat.1 / (n.toRat.2 : Int)) % 4))

/-- `sinpi(_x::T) where T<:IEEEFloat`; `base/special/trig.jl:934-957`. -/
def sinpi (T : FTy) (x0 : FV T) : Jl (FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok x else Trig.finiteDomainError "sinpi"
  else if le (Bits.maxintfloat T) x then .ok (copysign (zero T) x0)
  else
    let (rx, n) := piReduce x
    let res := if n == 0 then sinpiKernel T rx else if n == 1 then cospiKernel T rx
      else if n == 2 then sub (zero T) (sinpiKernel T rx) else sub (zero T) (cospiKernel T rx)
    .ok (if x0.signbit then neg res else res)

/-- `cospi(x::T) where T<:IEEEFloat`; `base/special/trig.jl:968-990`. -/
def cospi (T : FTy) (x0 : FV T) : Jl (FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok x else Trig.finiteDomainError "cospi"
  else if le (Bits.maxintfloat T) x then .ok (one T)
  else
    let (rx, n) := piReduce x
    .ok (if n == 0 then cospiKernel T rx else if n == 1 then sub (zero T) (sinpiKernel T rx)
      else if n == 2 then sub (zero T) (cospiKernel T rx) else sinpiKernel T rx)

/-- `sincospi(_x::T) where T<:IEEEFloat`; `base/special/trig.jl:1005-1030`. -/
def sincospi (T : FTy) (x0 : FV T) : Jl (FV T × FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok (x, x) else Trig.finiteDomainError "sincospi"
  else if le (Bits.maxintfloat T) x then .ok (copysign (zero T) x0, one T)
  else
    let (rx, n) := piReduce x
    let si := sinpiKernel T rx
    let co := cospiKernel T rx
    let (si, co) := if n == 0 then (si, co) else if n == 1 then (co, sub (zero T) si)
      else if n == 2 then (sub (zero T) si, sub (zero T) co) else (sub (zero T) co, si)
    .ok (if x0.signbit then neg si else si, co)

/-- `tanpi(_x::T) where T<:IEEEFloat`; `base/special/trig.jl:1044-1072`. -/
def tanpi (T : FTy) (x0 : FV T) : Jl (FV T) :=
  let x := abs x0
  if !x.isfinite then
    if x.isnan then .ok x else Trig.finiteDomainError "tanpi"
  else if le (Bits.maxintfloat T) x then .ok (copysign (zero T) x0)
  else
    let (rx, n) := piReduce x
    let si := sinpiKernelWide T rx
    let co := cospiKernelWide T rx
    let z : FV (wideTy T) := zero (wideTy T)
    let (si, co) := if n == 0 then (si, co) else if n == 1 then (co, sub z si)
      else if n == 2 then (sub z si, sub z co) else (sub z co, si)
    let si := if x0.signbit then neg si else si
    .ok (conv (div si co))

/-! ## Integer and generic methods, `base/special/trig.jl:1074-1082` -/

/-- `sinpi(x::Integer) = x >= 0 ? zero(float(x)) : -zero(float(x))`. -/
def sinpiInt (x : Int) : FV .f64 := if x ≥ 0 then zero .f64 else zero .f64 true
/-- `cospi(x::Integer) = isodd(x) ? -one(float(x)) : one(float(x))`. -/
def cospiInt (x : Int) : FV .f64 := if x % 2 != 0 then neg (one .f64) else one .f64
/-- `tanpi(x::Integer)`: a signed zero, negative for odd positive and even negative `x`. -/
def tanpiInt (x : Int) : FV .f64 :=
  if x ≥ 0 then (if x % 2 != 0 then zero .f64 true else zero .f64)
  else (if x % 2 != 0 then zero .f64 else zero .f64 true)
/-- `sincospi(x::Integer) = (sinpi(x), cospi(x))`. -/
def sincospiInt (x : Int) : FV .f64 × FV .f64 := (sinpiInt x, cospiInt x)

/-- `sinpi(x::AbstractFloat) = sin(pi*x)` and the other three generic methods, for a
float type `α` with its `pi*x` and trigonometric functions. -/
def piGeneric {α β : Type} (piMul : α → α) (f : α → β) (x : α) : β := f (piMul x)

/-! ## Complex methods, `base/special/trig.jl:1084-1207`. `sinh`, `cosh`, `tanh`
(`base/special/hyperbolic.jl`) are parameters. -/

/-- Hyperbolic functions of the component type. -/
structure Hyp (T : FTy) where
  sinh : FV T → FV T
  cosh : FV T → FV T
  tanh : FV T → FV T

/-- `pi * x` for a float `x`: `T(pi) * x`. -/
def piMul {T : FTy} (x : FV T) : FV T := mul (Trig.piT T) x

/-- `isinteger(x)` for a float. -/
def isint {T : FTy} (x : FV T) : Bool := x.isinteger

/-- The value of a `Jl` float result, `NaN` on error (unreachable where used). -/
def getF {T : FTy} : Jl (FV T) → FV T | .ok v => v | .error _ => nan T

/-- `tanpi(z::Complex)`; `base/special/trig.jl:1084-1091`. -/
def tanpiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T) := do
  if z.im.iszero then return ⟨← tanpi T z.re, zero T⟩
  let (sr, cr) ← sincospi T z.re
  let ti := h.tanh (mul z.im (Trig.piT T))
  let cz : Cx T := ⟨cr, mul ti sr⟩
  let a : Cx T := ⟨sr, mul ti cr⟩
  let prod : Cx T := ⟨sub (mul a.re cz.re) (mul a.im cz.im), add (mul a.re cz.im) (mul a.im cz.re)⟩
  let n := add (mul cz.re cz.re) (mul cz.im cz.im)
  return ⟨div prod.re n, div prod.im n⟩

/-- `sinpi(z::Complex{T})` for a float `T`; `base/special/trig.jl:1093-1124`. -/
def sinpiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T) := do
  let zr := z.re
  let zi := z.im
  if isint zr then
    let s := copysign (zero T) zr
    let cPos := isint (div zr (ofInt T 2))
    let sh := h.sinh (piMul zi)
    return ⟨s, if cPos then sh else neg sh⟩
  else if isint (mul (ofInt T 2) zr) then
    let sPos := isint (div (sub (mul (ofInt T 2) zr) (one T)) (ofInt T 4))
    let ch := h.cosh (piMul zi)
    return ⟨if sPos then ch else neg ch, if zi.isnan then zero T else copysign (zero T) zi⟩
  else if !zr.isfinite then
    if eq zi (zero T) || zi.isinf then return ⟨nan T, zi⟩ else return ⟨nan T, nan T⟩
  else
    let pizi := piMul zi
    let (sipi, copi) ← sincospi T zr
    return ⟨mul sipi (h.cosh pizi), mul copi (h.sinh pizi)⟩

/-- `cospi(z::Complex{T})`; `base/special/trig.jl:1126-1160`. -/
def cospiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T) := do
  let zr := z.re
  let zi := z.im
  if isint zr then
    let s := copysign (zero T) zr
    let cPos := isint (div zr (ofInt T 2))
    let ch := h.cosh (piMul zi)
    return ⟨if cPos then ch else neg ch, if zi.isnan then s else neg (flipsign s zi)⟩
  else if isint (mul (ofInt T 2) zr) then
    let sPos := isint (div (sub (mul (ofInt T 2) zr) (one T)) (ofInt T 4))
    let sh := h.sinh (piMul zi)
    return ⟨zero T, if sPos then neg sh else sh⟩
  else if !zr.isfinite then
    if eq zi (zero T) then
      return ⟨nan T, if zr.isnan then zero T else neg (flipsign zi zr)⟩
    else if zi.isinf then return ⟨inf T, nan T⟩
    else return ⟨nan T, nan T⟩
  else
    let pizi := piMul zi
    let (sipi, copi) ← sincospi T zr
    return ⟨mul copi (h.cosh pizi), mul (neg sipi) (h.sinh pizi)⟩

/-- `sincospi(z::Complex{T})`; `base/special/trig.jl:1162-1207`. -/
def sincospiC {T : FTy} (h : Hyp T) (z : Cx T) : Jl (Cx T × Cx T) := do
  let zr := z.re
  let zi := z.im
  if isint zr then
    let s := copysign (zero T) zr
    let cPos := isint (div zr (ofInt T 2))
    let pizi := piMul zi
    let sh := h.sinh pizi
    let ch := h.cosh pizi
    return (⟨s, if cPos then sh else neg sh⟩,
      ⟨if cPos then ch else neg ch, if zi.isnan then s else neg (flipsign s zi)⟩)
  else if isint (mul (ofInt T 2) zr) then
    let sPos := isint (div (sub (mul (ofInt T 2) zr) (one T)) (ofInt T 4))
    let pizi := piMul zi
    let sh := h.sinh pizi
    let ch := h.cosh pizi
    return (⟨if sPos then ch else neg ch, if zi.isnan then zero T else copysign (zero T) zi⟩,
      ⟨zero T, if sPos then neg sh else sh⟩)
  else if !zr.isfinite then
    if eq zi (zero T) then
      return (⟨nan T, zi⟩, ⟨nan T, if zr.isnan then zero T else neg (flipsign zi zr)⟩)
    else if zi.isinf then return (⟨nan T, zi⟩, ⟨inf T, nan T⟩)
    else return (⟨nan T, nan T⟩, ⟨nan T, nan T⟩)
  else
    let pizi := piMul zi
    let (sipi, copi) ← sincospi T zr
    let sihpi := h.sinh pizi
    let cohpi := h.cosh pizi
    return (⟨mul sipi cohpi, mul copi sihpi⟩, ⟨mul copi cohpi, mul (neg sipi) sihpi⟩)

end JuliaLean.MathCov.TrigPi

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
`fuel` bounds evaluation; exhaustion returns an explicit error. -/
def coscSeries {α : Type} (pi : α) (mulα divα addα : α → α → α) (negα : α → α) (ofNat : Int → α)
    (iszero : α → Bool) (leα : α → α → Bool) (fabs eps : α → α) :
    Nat → α → α → α → α → Nat → JuliaLean.base.range.JlX α
  | 0, _, _, _, _, _ => .error (.errorException "fuel")
  | fuel + 1, s, term, pi2x2, e, n =>
    let n := n + 1
    let term := mulα term (divα pi2x2 (mulα (ofNat (1 - 2 * n)) (ofNat (2 * n - 2))))
    let ds := divα term (ofNat (1 + 2 * n))
    let s := addα s ds
    if leα (fabs ds) e then .ok (mulα pi s)
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
