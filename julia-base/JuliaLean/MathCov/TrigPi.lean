import JuliaLean.MathCov.Trig

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
