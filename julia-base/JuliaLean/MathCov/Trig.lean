import JuliaLean.MathCov.Special
import JuliaLean.MathFuncs.RemPio2

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

def h64 : FV .f64 := lit .f64 0x3fe0000000000000
def one64 : FV .f64 := one .f64
def two64 : FV .f64 := ofInt .f64 2

/-- `@horner(x, c...)`, i.e. `evalpoly`; `base/math.jl:157-160`. -/
abbrev horner {T : FTy} := @Exp.horner T

/-- `DoubleFloat64(hi, lo)`; `base/special/trig.jl:4-7`. -/
structure DF64 where
  hi : FV .f64
  lo : FV .f64

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

/-- `ATAN2_PI_LO(T)`, `ATAN2_RATIO_BIT_SHIFT(T)`, `ATAN2_RATIO_THRESHOLD(T)`;
`base/special/trig.jl:556-562`. -/
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
