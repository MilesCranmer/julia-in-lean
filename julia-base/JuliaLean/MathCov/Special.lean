import JuliaLean.MathCov.Log
import JuliaLean.FloatFuncs.Round
import JuliaLean.MathCov.Bits
import JuliaLean.MathFuncs.Pow
import JuliaLean.MathFuncs.Cbrt
import JuliaLean.MathFuncs.Rem2pi

/-!
`Float16`/`Float32` methods of `base/special/pow.jl`, `base/special/cbrt.jl`,
`base/special/rem_pio2.jl` and `base/special/rem2pi.jl` at Julia master `bbfa0ce4150`.
The `Float64` kernels they call are the `JuliaLean.MathFuncs` models.
-/

namespace JuliaLean.MathCov.Special

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-! ## pow.jl -/

/-- `use_power_by_squaring(n) = -2^12 <= n <= 3 * 2^13`; `base/special/pow.jl:1-3`. -/
def usePowerBySquaring (n : Int) : Bool := decide (-2 ^ 12 ≤ n ∧ n ≤ 3 * 2 ^ 13)

/-- Number of trailing zero bits of a positive integer. -/
def trailingZeros (p : Nat) : Nat :=
  if h : p = 0 then 0 else if p % 2 = 0 then trailingZeros (p / 2) + 1 else 0
decreasing_by omega

/-- `x = mul(x, x)` repeated `t` times. -/
def squareN {T : FTy} (x : FV T) : Nat → FV T
  | 0 => x
  | t + 1 => squareN (mul x x) t

/-- The `while p > 0` loop of `power_by_squaring`; `base/intfuncs.jl:434-441`. -/
def pbsLoop {T : FTy} : Nat → FV T → FV T → Nat → FV T
  | 0, _, y, _ => y
  | fuel + 1, x, y, p =>
    if p == 0 then y
    else
      let t := trailingZeros p + 1
      let x := squareN x t
      pbsLoop fuel x (mul y x) (p / 2 ^ t)

/-- `power_by_squaring(x, p)` for a float `x` and `p ≥ 0` with `mul = *`;
`base/intfuncs.jl:399-443`. -/
def powerBySquaring {T : FTy} (x : FV T) (p : Nat) : FV T :=
  let xsq := mul x x
  if p == 1 then x
  else if p == 0 then one T
  else if p == 2 then xsq
  else
    let t := trailingZeros p + 1
    let p := p / 2 ^ t
    let x := if t - 1 > 0 then squareN xsq (t - 2) else x
    pbsLoop (p + 1) x x p

/-- `widen(T)` for the narrow formats. -/
def widenTy : FTy → FTy | .f16 => .f32 | .f32 => .f64 | .f64 => .f64

/-- `pow_body(x::Union{Float16,Float32}, n::Int32)`; `base/special/pow.jl:109-114`. -/
def powBodyI {T : FTy} (x : FV T) (n : Int) : FV T :=
  if n == -2 then let i := div (one T) x; mul i i
  else if n == 3 then mul (mul x x) x
  else if n < 0 then
    conv (powerBySquaring (div (one (widenTy T)) (conv x : FV (widenTy T))) (-n).toNat)
  else conv (powerBySquaring (conv x : FV (widenTy T)) n.toNat)

/-- `pow_body(x::T, y) = T(exp2(log2(abs(widen(x))) * y))` for `T = Float16, Float32`
and a `Float64` (or narrower) `y`; `base/special/pow.jl:105-107`. `log2`/`exp2` are the
`Float64` methods for `Float32` and the `Float32` methods for `Float16`. -/
def powBodyF (T : FTy) (x : FV T) (y : FV .f64) : FV T :=
  match T with
  | .f32 =>
    let l := match MathFuncs.log2 (toD (abs x)) with
      | .ok v => v
      | .error _ => F64.nan
    conv (of64 (MathFuncs.exp2 (F64.mul l (Fl.toF64 y))))
  | .f16 =>
    let w : FV .f32 := abs (conv x)
    let l := match Log.log2F32 w with
      | .ok v => v
      | .error _ => nan .f32
    conv (Exp.expImpl32 (mul l (conv y)) .two)
  | .f64 => x

/-- `Bool * x` for a float: `ifelse(b, x, copysign(zero(x), x))`; `base/bool.jl:182`. -/
def boolMul {T : FTy} (b : Bool) (x : FV T) : FV T := if b then x else copysign (zero T) x

/-- `x == yint` for a float `y` and the `Int32` from `unsafe_trunc`. -/
def eqInt {T : FTy} (y : FV T) (n : Int) : Bool := eq y (ofInt T n)

/-- `^(x::T, y::T) where T <: Union{Float16, Float32}`; `base/special/pow.jl:34-56`. -/
def powFF {T : FTy} (x y : FV T) : Jl (FV T) := do
  if eq x (one T) then return one T
  let maxExp : FV T := if T = .f16 then powMaxExp16Of T else powMaxExp32Of T
  let mut y := y
  if !(lt (abs y) maxExp) then
    if y.isnan then return y
    y := mul (if y.signbit then neg (one T) else one T) maxExp
  let yint := (unsafeTrunc .i32 y).val
  let yisint := eqInt y yint
  if yisint then
    if yint == 0 then return one T
    if usePowerBySquaring yint then return powBodyI x yint
  let mut s : Int := 1
  if lt x (zero T) then
    if !yisint then throw (.domainError "Exponentiation yielding a complex result")
    s := if yint % 2 != 0 then -1 else 1
  if !x.isfinite then
    return boolMul (lt (zero T) y || x.isnan) (copysign x (ofInt T s))
  return copysign (powBodyF T (abs x) (conv y)) (ofInt T s)
where
  powMaxExp16Of (T : FTy) : FV T := conv powMaxExp16
  powMaxExp32Of (T : FTy) : FV T := conv powMaxExp32

/-- `clamp(n, Int32)`. -/
def clamp32 (n : Int) : Int := max (IntTy.min .i32) (min (IntTy.max .i32) n)

/-- `^(x::T, n::Integer) where T <: Union{Float16, Float32}`; `base/special/pow.jl:80-89`. -/
def powFI {T : FTy} (x : FV T) (n : Int) : FV T :=
  let n32 := clamp32 n
  if n32 == 0 then one T
  else if usePowerBySquaring n32 then powBodyI x n32
  else
    let s := if x.signbit && n % 2 != 0 then neg (one T) else one T
    let x := abs x
    copysign (powBodyF T x (ofInt .f64 n32)) s

/-! ## cbrt.jl -/

/-- `cbrt(x::AbstractFloat) = x < 0 ? -(-x)^(1//3) : x^(1//3)` for a float type with an
arbitrary power `pow`; `base/special/cbrt.jl:36`. -/
def cbrtAbstract {α : Type} (lt0 : α → Bool) (negα : α → α) (pow : α → α) (x : α) : α :=
  if lt0 x then negα (pow (negα x)) else pow x

/-- `_approx_cbrt(x::T)` for `T = Float32, Float64`; `base/special/cbrt.jl:63-79`. The
constants `floor(UInt32, adj * exp2(k))` are evaluated in Float64. -/
def approxCbrt {T : FTy} (x : FV T) : FV T :=
  let k : Nat := if T = .f64 then 20 else 23
  let adj0 : FV .f64 := if T = .f64 then cbrtAdj64 else cbrtAdj32
  let hw (z : FV T) : Nat := if T = .f64 then Bits.highwordU64 z.toBits else z.toBits % 2 ^ 32
  let fromhw (v : Nat) : FV T := if T = .f64 then Fl.ofBits (v % 2 ^ 32 * 2 ^ 32) else Fl.ofBits (v % 2 ^ 32)
  let floorU32 (y : FV .f64) : Nat :=
    let q := (Fl.ofF64 (F64.floor (Fl.toF64 y)) : FV .f64).toRat
    (q.1 / (q.2 : Int)).toNat
  let two_k : FV .f64 := Fl.ofBits ((1023 + k) * 2 ^ 52)
  let u := hw x % 2 ^ 31
  if u ≥ hw (floatminT T) then
    let v := u / 3 + floorU32 (mul adj0 two_k)
    copysign (fromhw (v % 2 ^ 32)) x
  else
    let mif := Bits.maxintfloat T
    let x' := mul x mif
    let e : Int := match Bits.exponent mif with | .ok e => e | .error _ => 0
    let adj := sub adj0 (div (ofInt .f64 e) (ofInt .f64 3))
    let u := hw x' % 2 ^ 31
    let v := u / 3 + floorU32 (mul adj two_k)
    copysign (fromhw (v % 2 ^ 32)) x'

/-- `tt^3` for a Float64 (`literal_pow`, i.e. `tt*tt*tt`). -/
def cube (t : FV .f64) : FV .f64 := mul (mul t t) t

/-- `_improve_cbrt(x::Float32, t::Float32)`; `base/special/cbrt.jl:81-101`. -/
def improveCbrt32 (x t : FV .f32) : FV .f32 :=
  let xx : FV .f64 := conv x
  let step (tt : FV .f64) : FV .f64 :=
    let tt3 := cube tt
    mul tt (div (add (mul (ofInt .f64 2) xx) tt3) (add (conv x) (mul (ofInt .f64 2) tt3)))
  conv (step (step (conv t)))

/-- `cbrt(x::Union{Float32,Float64})`; `base/special/cbrt.jl:144-150`. -/
def cbrt {T : FTy} (x : FV T) : FV T :=
  if !x.isfinite || x.iszero then x
  else
    let t := approxCbrt x
    if T = .f64 then conv (of64 (MathFuncs.improveCbrt (toD x) (toD t)))
    else improveCbrt32Of x t
where
  improveCbrt32Of {T : FTy} (x t : FV T) : FV T := conv (improveCbrt32 (conv x) (conv t))

/-- `cbrt(a::Float16)`; `base/special/cbrt.jl:152-167`. -/
def cbrt16 (a : FV .f16) : FV .f16 :=
  if !a.isfinite || a.iszero then a
  else
    let x : FV .f32 := conv a
    let u := x.toBits % 2 ^ 31
    let v := (u / 3 + 0x2a5119f2) % 2 ^ 32
    let t := copysign (Fl.ofBits v : FV .f32) x
    let nt (t : FV .f32) : FV .f32 :=
      mul cbrtThird32 (add (mul (ofInt .f32 2) t) (div x (mul t t)))
    conv (nt (nt t))

/-! ## rem_pio2.jl and rem2pi.jl -/

/-- `rem_pio2_kernel(x::Float32)`: `(n, DoubleFloat32(y))`; `base/special/rem_pio2.jl:284-295`. -/
def remPio2Kernel32 (x : FV .f32) : Int × FV .f64 :=
  let xd : FV .f64 := conv x
  if lt (abs x) remPio2Bound32 then
    let fn := roundI (mul xd twoOverPi64)
    let r := fma fn negPiOver2 xd
    let y := fma fn pio2Tail r
    ((unsafeTrunc .i64 fn).val, y)
  else
    let (n, hi, _) := MathFuncs.paynehanek (Fl.toF64 xd)
    (n, Fl.ofF64 hi)

/-- The four `rem2pi(x::Float64, r)` methods; `base/special/rem2pi.jl:14-131`. -/
def rem2pi64 (x : FV .f64) (r : FloatFuncs.Mode) : FV .f64 :=
  let f := Fl.toF64 x
  Fl.ofF64 (match r with
    | .Nearest => MathFuncs.rem2piNearest f
    | .ToZero => MathFuncs.rem2piToZero f
    | .Down => MathFuncs.rem2piDown f
    | _ => MathFuncs.rem2piUp f)

/-- `rem2pi(x::Float32, r)` and `rem2pi(x::Float16, r)`: round the `Float64` result;
`base/special/rem2pi.jl:133-134`. -/
def rem2piNarrow {T : FTy} (x : FV T) (r : FloatFuncs.Mode) : FV T := conv (rem2pi64 (conv x) r)

/-- `rem2pi(x::Int32, r) = rem2pi(Float64(x), r)`; `base/special/rem2pi.jl:135`. -/
def rem2piInt32 (x : JInt .i32) (r : FloatFuncs.Mode) : FV .f64 := rem2pi64 (ofInt .f64 x.val) r

/-- `rem2pi(x::Integer, r)`: `fx = float(x)`, which must equal `x`;
`base/special/rem2pi.jl:138-142`. -/
def rem2piInteger (x : Int) (r : FloatFuncs.Mode) : Jl (FV .f64) :=
  let fx : FV .f64 := ofInt .f64 x
  if fx.isfinite && fx.toRat.2 == 1 && fx.toRat.1 == x then .ok (rem2pi64 fx r)
  else .error (.argumentError "argument to rem2pi is too large")

end JuliaLean.MathCov.Special
