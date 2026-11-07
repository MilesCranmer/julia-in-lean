import JuliaLean.base.math
import JuliaLean.base.reduce
import JuliaLean.base.intfuncs
import JuliaLean.base.special.rem2pi
import JuliaLean.base.mathconstants
import JuliaLean.base.rational
import JuliaLean.base.floatfuncs
import JuliaLean.base.twiceprecision
import JuliaLean.base.special.trig
import JuliaLean.base.special.log
import JuliaLean.base.complex
import JuliaLean.base.checked
import JuliaLean.base.boot
import JuliaLean.base.irrationals

/-!
# `JuliaLean.Bindings.base.math`: callee bindings for `base/math.jl`

Bindings of the callee records and type-dispatched methods that `base/math.jl` calls, for the
Base types that reach them (Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`). A Base type with
no installed model of its callees, and any user type's own methods, are not bound; each binding
states its domain.

Every record field below is bound to the installed model of the Julia method it stands for.
The only runtime inputs are the machine facts the C runtime reads: the widths for which
`jl_cpu_has_fma` holds (`src/runtime_intrinsics.c:1829-1840`, read by `jlHaveFma`), the
`mpfr_const_pi` primitive of the installed `irrationals.PiPrimitive`, the MPFR library's analytic
kernels (`mpfr.AnalyticOps`: `mpfr_exp`, `mpfr_const_euler`, `mpfr_const_catalan`, ...) and its
exponent limits in the load-time MPFR context. The FMA methods are the installed width-indexed
`base/floatfuncs.lean` models. User-defined types keep their own methods as typed parameters.
-/

namespace JuliaLean.Bindings.base.math

open JuliaLean
open JuliaLean.Promotion (Fl)
open JuliaLean.base.math
open JuliaLean.base.float (FV FTy)

/-! ## 1. Machine facts -/

/-- The runtime facts read by the bound methods. -/
structure Machine where
  /-- The widths for which `jl_cpu_has_fma` returns true (`src/runtime_intrinsics.c:1829-1840`). -/
  fmaWidths : List Nat
  /-- `mpfr_const_pi`, with its correctly rounded result law (`irrationals.PiPrimitive`). -/
  pi : JuliaLean.base.irrationals.PiPrimitive
  /-- The MPFR library functions that `@irrational ℯ`, `γ`, `φ` and `catalan` call at load time
  (`base/mathconstants.jl:14-17`). -/
  analytic : JuliaLean.base.mpfr.AnalyticOps
  /-- `mpfr_get_emin`/`mpfr_get_emax` and their limits in the MPFR library. -/
  mpfrEmin : JuliaLean.base.mpfr.Clong
  mpfrEmax : JuliaLean.base.mpfr.Clong
  mpfrLimits : JuliaLean.base.mpfr.ExponentLimits

/-- `Core.Intrinsics.have_fma(T)`. -/
def haveFma (m : Machine) (T : FTy) : Bool := JuliaLean.C.jlHaveFma T.fmt m.fmaWidths

/-- The MPFR context in effect while `base/mathconstants.jl` evaluates `@irrational π`:
Base's default precision 256 and rounding `RoundNearest` (`base/mpfr.jl`), with the library limits. -/
def loadContext (m : Machine) : JuliaLean.base.mpfr.Context :=
  { emin := m.mpfrEmin, emax := m.mpfrEmax, limits := m.mpfrLimits }

/-- `Float64(π)` and `Float32(π)`: the values `v64 = Float64(v)`, `v32 = Float32(v)` that the
`@irrational` macro function (`base/irrationals.jl:270-298`; `let v = $val, v64 = ..., v32 = ...`
at 290-293) computes from `v = big(π)` at load time. -/
def piValue (m : Machine) : (T : JuliaLean.base.irrationals.IEEE32Or64) → FV T.ty
  | T => JuliaLean.base.mathconstants.piDirectedValue m.pi T (loadContext m) .Nearest

/-- `T(π)` for `T <: IEEEFloat`; `Float16(x::AbstractIrrational) = Float16(Float32(x))`
(`base/irrationals.jl:60`). -/
def piIEEE (m : Machine) : (T : FTy) → FV T
  | .f16 => JuliaLean.base.float.convertFloat .f16 (piValue m .f32)
  | .f32 => piValue m .f32
  | .f64 => piValue m .f64

/-! ## 2. IEEE method bindings -/

/-- `flipsign(x::Float64, y::Float64)` and `flipsign(x::Float32, y::Float32)` (`base/floatfuncs.jl:10-11`);
Float16 uses `flipsign(x::Real, y::Real) = ifelse(signbit(y), -x, +x)` (`base/number.jl:255`). -/
def flipsignIEEE : (T : FTy) → FV T → FV T → FV T
  | .f64 => JuliaLean.base.floatfuncs.flipsign_Float64
  | .f32 => JuliaLean.base.floatfuncs.flipsign_Float32
  | .f16 => fun x y => JuliaLean.base.int.okOf
      (JuliaLean.base.number.flipsign (fun y => .ok (JuliaLean.base.float.signbit_float y))
        (fun x => .ok (JuliaLean.base.float.neg_float x)) (fun x => .ok x)
        (fun c a b => JuliaLean.base.operators.ifelseValue c a b) x y)
      (by intro e h; simp [JuliaLean.base.number.flipsign, bind, Except.bind, pure, Except.pure] at h)

/-- `clamp(x, lo, hi)` (`base/intfuncs.jl:1461-1464`) on the `UInt` bit patterns of `scaleinv`. -/
def clampUnsigned (x lo hi : Nat) : Nat :=
  JuliaLean.base.int.okOf
    (JuliaLean.base.intfuncs.clamp (fun a b => decide (b < a)) (fun a b => decide (a < b))
      (fun a => (.ok a : Jl Nat)) (fun a => .ok a) (fun a => .ok a) x lo hi)
    (by intro e h; simp [JuliaLean.base.intfuncs.clamp] at h; split at h <;> (try split at h) <;> simp at h)

/-- Every method of `IEEEOps` except `fma`/`two_mul`, which the Float64 `fma_emulated`
callee set needs before the record exists. -/
def ieeeOpsWith (m : Machine) (T : FTy) (fma : FV T → FV T → FV T → FV T)
    (twoMul : FV T → FV T → FV T × FV T) : IEEEOps T where
  sqrtLlvm := JuliaLean.C.jlSqrtLlvm
  eps := JuliaLean.base.float.eps_float T
  floatmin := JuliaLean.base.float.floatmin_float T
  floatmax := JuliaLean.base.float.floatmax_float T
  invFloatmin := JuliaLean.base.float.div_float (JuliaLean.base.float.one_float T)
    (JuliaLean.base.float.floatmin_float T)
  pi := piIEEE m T
  fma := fma
  twoMul := twoMul
  trunc := JuliaLean.C.jlTruncLlvm
  rem := JuliaLean.base.float.rem_IEEEFloat
  flipsign := flipsignIEEE T
  minFloat := JuliaLean.C.jlMinFloat
  maxFloat := JuliaLean.C.jlMaxFloat
  clampUnsigned := clampUnsigned
  -- `add_float_fast` is an alias of `add_float` in the runtime (`src/intrinsics.h:26`).
  addFast := JuliaLean.base.float.add_float
  oneunit := fun _ => JuliaLean.base.float.one_float T
  inverse := fun x => JuliaLean.base.float.div_float (JuliaLean.base.float.one_float T) x
  greater := fun x y => JuliaLean.base.float.lt_float y x
  muladd := JuliaLean.base.float.muladd_IEEEFloat
  abs2 := fun x => JuliaLean.base.float.mul_float x x
  haveFma := haveFma m T

/-- `ldexp(x::Float64, e::Integer)` (`base/math.jl:854-897`): it reads only `flipsign`
(`ldexp64_eq` below shows it is the public method of the bound record). -/
def ldexp64 (m : Machine) (x : FV .f64) (e : Int) : FV .f64 :=
  ldexp (ieeeOpsWith m .f64 JuliaLean.C.jlFmaFloat
    (fun x y => (JuliaLean.base.float.mul_float x y,
      JuliaLean.C.jlFmaFloat x y (JuliaLean.base.float.neg_float (JuliaLean.base.float.mul_float x y))))) x e

/-- `cmp(x::Float64, 0)` in `fma_emulated`: `cmp(x, y)` (`base/operators.jl:526`) with
`isless(::AbstractFloat, ::Real)` and `isless(::Real, ::AbstractFloat)` (`base/operators.jl:241-242`). -/
def cmpZero64 (x : FV .f64) : JInt .i64 :=
  let zero : JInt .i64 := JInt.lit .i64 0
  JInt.wrap .i64 (JuliaLean.base.operators.cmp
    (JuliaLean.base.operators.islessFloatReal JuliaLean.base.float.isnan_IEEEFloat
      (fun (_ : JInt .i64) => false) JuliaLean.base.float.signbit_float
      JuliaLean.base.int.signbit_Integer JuliaLean.base.float.lt_FI)
    (JuliaLean.base.operators.islessRealFloat (fun (_ : JInt .i64) => false)
      JuliaLean.base.float.isnan_IEEEFloat JuliaLean.base.int.signbit_Integer
      JuliaLean.base.float.signbit_float JuliaLean.base.float.lt_IF) x zero)

/-- The callees of `fma_emulated(::Float64, ::Float64, ::Float64)` and `two_mul(::Float64, ::Float64)`
(`base/floatfuncs.jl:376-460`). -/
def fma64Ops (m : Machine) : JuliaLean.base.floatfuncs.Float64FmaOps where
  haveFma := haveFma m .f64
  truncbits := fun x nb => JuliaLean.base.twiceprecision.truncbitsF64 x (JInt.wrap .i64 nb)
  isfinite := JuliaLean.base.float.isfinite_IEEEFloat
  isinf := JuliaLean.base.float.isinf_IEEEFloat
  iszero := JuliaLean.base.float.iszero_float
  issubnormal := JuliaLean.base.float.issubnormal
  signbit := JuliaLean.base.float.signbit_float
  isless := JuliaLean.base.float.isless_IEEEFloat
  equal := JuliaLean.base.float.eq_IEEEFloat
  abs := JuliaLean.base.float.abs_IEEEFloat
  add := JuliaLean.base.float.add_IEEEFloat
  sub := JuliaLean.base.float.sub_IEEEFloat
  mul := JuliaLean.base.float.mul_IEEEFloat
  neg := JuliaLean.base.float.neg_IEEEFloat
  nextfloat := JuliaLean.base.float.nextfloat_step
  ldexp := fun x e => ldexp64 m x e.val
  exponent := fun x => JInt.wrap .i64 (exponentFiniteNonzero x)
  cmpZero := cmpZero64
  bits := JuliaLean.base.float.reinterpret_Unsigned_Float64
  fromBits := JuliaLean.base.float.reinterpret_Float_Int .f64
  exponentMask := JuliaLean.base.float.exponent_mask_Float64
  exponentOne := JuliaLean.base.float.exponent_one_Float64
  floatmin := JuliaLean.base.float.floatmin_Float64
  pow2_52 := Fl.ofBits 0x4330000000000000
  pow2_neg969 := Fl.ofBits 0x0360000000000000

/-- `widen(T)`/`T(x)` of `fma_emulated(a::T, b::T, c::T)` for `T = Float16` and `Float32`
(`base/floatfuncs.jl:350-361`): `widen(Float16) = Float32`, `widen(Float32) = Float64`
(`base/float.jl:481-482`), each conversion the installed `convertFloat`. -/
def smallFma16Ops : JuliaLean.base.floatfuncs.SmallFmaOps .f16 where
  widen := JuliaLean.base.float.convertFloat .f32
  narrow := JuliaLean.base.float.convertFloat .f16
def smallFma32Ops : JuliaLean.base.floatfuncs.SmallFmaOps .f32 where
  widen := JuliaLean.base.float.convertFloat .f64
  narrow := JuliaLean.base.float.convertFloat .f32

/-- The three emulated `fma` methods and `have_fma` (`base/floatfuncs.jl:464-466`). -/
def floatFmaOps (m : Machine) : JuliaLean.base.floatfuncs.FloatFmaOps :=
  { haveFma := haveFma m, fma16 := smallFma16Ops, fma32 := smallFma32Ops, fma64 := fma64Ops m }

/-- `fma(x::T, y::T, z::T) where T<:IEEEFloat`. -/
def fmaIEEE (m : Machine) {T : FTy} : FV T → FV T → FV T → FV T :=
  JuliaLean.base.floatfuncs.fma_IEEEFloat (floatFmaOps m)

/-- `two_mul` for each IEEE format (`base/floatfuncs.jl:376-398`): Float64 through its own method,
Float16 and Float32 through the `Union{Float16,Float32}` method, whose fallback computes in
`widen(T)` (Float32 for Float16, Float64 for Float32) and whose hardware branch calls `fma`. -/
def twoMulIEEE (m : Machine) : (T : FTy) → FV T → FV T → FV T × FV T
  | .f64 => JuliaLean.base.floatfuncs.two_mul_Float64 (fma64Ops m)
  | .f32 => JuliaLean.base.floatfuncs.two_mul_Small (Or.inr rfl)
      { haveFma := haveFma m .f32, widen := JuliaLean.base.float.convertFloat .f64,
        narrow := JuliaLean.base.float.convertFloat .f32 } (fmaIEEE m)
  | .f16 => JuliaLean.base.floatfuncs.two_mul_Small (Or.inl rfl)
      { haveFma := haveFma m .f16, widen := JuliaLean.base.float.convertFloat .f32,
        narrow := JuliaLean.base.float.convertFloat .f16 } (fmaIEEE m)

/-- The IEEE methods of `T` called by `base/math.jl`. -/
def ieeeOps (m : Machine) (T : FTy) : IEEEOps T :=
  ieeeOpsWith m T (fmaIEEE m) (twoMulIEEE m T)

theorem ldexp64_eq (m : Machine) (x : FV .f64) (e : Int) :
    ldexp64 m x e = ldexp (ieeeOps m .f64) x e := by
  simp only [ldexp64, ieeeOps, ieeeOpsWith, ldexp, ldexpSource]

/-! ## 3. Reductions in `_hypot(x::NTuple{N,<:IEEEFloat})` (`base/math.jl:816-828`) -/

/-- `mapreduce(==(infT), |, x)`, `maximum(z -> reinterpret(Signed, z), x)` and
`mapreduce(y -> abs2(y * invscale), add_fast, x)` over a tuple (`IteratorEltype` is `HasEltype`). -/
def reduceOps (T : FTy) : HypotFloatReductionOps T where
  iteratorEltype := fun _ => .hasEltype
  booleanOr := JuliaLean.base.reduce.valueReducer JuliaLean.base.bool.orBool id
    JuliaLean.base.reduce.reduce_empty_or_bool
  Signed := JInt T.intTy
  reinterpretSigned := JuliaLean.base.float.reinterpret_Signed
  reinterpretFloat := JuliaLean.base.float.reinterpret_Float_Int T
  -- `max(x, y) = ifelse(isless(y, x), x, y)` with `isless(x::Real, y::Real) = x < y`.
  maximumReducer := JuliaLean.base.reduce.valueReducer
    (JuliaLean.base.operators.max (fun y x => JuliaLean.base.int.slt_int y x)
      (fun c a b => JuliaLean.base.operators.ifelseValue c a b))
    id JuliaLean.base.reduce._empty_reduce_error (isMax := true)
  sumReducer := JuliaLean.base.reduce.valueReducer JuliaLean.base.float.add_float id
    JuliaLean.base.reduce._empty_reduce_error

/-! ## 4. Public `hypot`, `sqrt`, `fourthroot`, `log`, `atan`, `min`/`max`, `rad2deg`, `modf` -/

/-- `promote(x::T, y::T) where {T}` (`base/promotion.jl:441`) as the pair `hypot` destructures. -/
def promotePair {α : Type} (x y : α) : Jl (α × α) :=
  match JuliaLean.base.promotion.promoteSameType x y [] with
  | [a, b] => .ok (a, b)
  | _ => .error (.methodError "promote")

theorem promotePair_eq {α : Type} (x y : α) : promotePair x y = .ok (x, y) := rfl

/-- `float(x::T) = AbstractFloat(x)` for `T <: AbstractFloat`, which is `(::Type{T})(x::T) = x`. -/
def floatSame {α : Type} (x : α) : α :=
  JuliaLean.base.float.float_any JuliaLean.BootCov.IntConv.sameTypeCtor x

/-- `hypot(x::T, y::T)`/`hypot(xs::T...)` dispatch for each IEEE format: `_hypot(x, y)` for
Float64 (`base/math.jl:732-786`), `_hypot(x::Float32, y::Float32)` and `_hypot(x::Float16, y::Float16)`
(`base/math.jl:789-802`), `_hypot(x::NTuple{N,<:IEEEFloat})` (`base/math.jl:816-828`). -/
def hypotDispatch (m : Machine) : (T : FTy) → HypotDispatch (FV T) (FV T)
  | .f16 => hypotDispatchFloat16 JuliaLean.base.reduce.mapreduce JuliaLean.base.reduce.maximum_f (ieeeOps m .f16) (ieeeOps m .f32) (reduceOps .f16)
  | .f32 => hypotDispatchFloat32 JuliaLean.base.reduce.mapreduce JuliaLean.base.reduce.maximum_f (ieeeOps m .f32) (ieeeOps m .f64) (reduceOps .f32)
  | .f64 => hypotDispatchFloat64 JuliaLean.base.reduce.mapreduce JuliaLean.base.reduce.maximum_f (ieeeOps m .f64) (reduceOps .f64)

/-- Public `hypot(x::T, y::T)` for `T <: IEEEFloat`: `hypot(x::Number, y::Number)`
(`base/math.jl:730`). -/
def hypotIEEE (m : Machine) (T : FTy) (x y : FV T) : Jl (FV T) :=
  hypotTwo promotePair floatSame (hypotDispatch m T) x y

/-- Public `hypot(x::T, y::T, xs::T...)`: `hypot(x::Number, y::Number, xs::Number...)`
(`base/math.jl:731`). -/
def hypotManyIEEE (m : Machine) (T : FTy) (xs : List (FV T)) : Jl (FV T) :=
  hypotMany (fun xs => match xs with
      | x :: y :: zs => .ok (JuliaLean.base.promotion.promoteSameType x y zs)
      | _ => .error (.methodError "hypot"))
    floatSame (hypotDispatch m T) xs

/-- Public `hypot(x::BitInteger, y::BitInteger)` of one type: `float(x) = Float64(x)`. -/
def hypotBitInteger (m : Machine) {t : IntTy} (x y : JInt t) : Jl (FV .f64) :=
  hypotTwo promotePair JuliaLean.base.float.float_BitInteger (hypotDispatch m .f64) x y

/-- Public `hypot(x::Number) = abs(float(x))` (`base/math.jl:729`) for `x::T <: IEEEFloat`. -/
def hypotOneIEEE {T : FTy} (x : FV T) : FV T :=
  hypotOne floatSame JuliaLean.base.float.abs_IEEEFloat x

/-- `hypot(z::Complex{T})`: `float(z) = z` (`base/complex.jl:1129`) and
`abs(z::Complex) = hypot(real(z), imag(z))` (`base/complex.jl:281`). -/
def hypotOneComplex (m : Machine) (T : FTy) (z : JuliaLean.base.complex.Complex (FV T)) : Jl (FV T) :=
  hypotOne JuliaLean.base.complex.float_Complex_AbstractFloat
    (JuliaLean.base.complex.abs_Complex (hypotIEEE m T)) z

/-- `sqrt(x::T) where T<:IEEEFloat` (`base/math.jl:629-632`). -/
def sqrtFloat (m : Machine) {T : FTy} (x : FV T) : Jl (FV T) := sqrtIEEE (ieeeOps m T) x

/-- `sqrt(x::Real)` for `x::BitInteger`: the `Real` fallback (`base/math.jl:1326-1330`) with
`float(x) = Float64(x)`; `x === float(x)` is false since the two values have different types. -/
def sqrtBitInteger (m : Machine) {t : IntTy} (x : JInt t) : Jl (FV .f64) :=
  realFallback JuliaLean.base.float.float_BitInteger (fun _ => false) "sqrt" (sqrtFloat m) x

/-- `fourthroot(x::Number) = sqrt(sqrt(x))` (`base/math.jl:685`) on an IEEE value; at the pinned
revision every IEEE type, Float16 included, reaches this method (the Float16 loop at
`base/math.jl:1306-1312` does not list `fourthroot` or `sqrt`). -/
def fourthrootFloat (m : Machine) {T : FTy} (x : FV T) : Jl (FV T) :=
  fourthroot (sqrtFloat m) (sqrtFloat m) x

/-- `log(x::Float64)` and `log(x::Float32)` (`base/special/log.jl`). -/
def logFloat : (T : JuliaLean.base.irrationals.IEEE32Or64) → FV T.ty → Jl (FV T.ty)
  | .f64 => JuliaLean.base.special.log.log_64
  | .f32 => JuliaLean.base.special.log.log_32

/-- `log(b::T, x::T)` (`base/math.jl:259`) with `/(x::T, y::T) = div_float(x, y)`. -/
def logBaseFloat (T : JuliaLean.base.irrationals.IEEE32Or64) (b x : FV T.ty) : Jl (FV T.ty) :=
  logBase (logFloat T) JuliaLean.base.float.div_float b x

/-- `min(x::T, y::T)`, `max(x::T, y::T)` for `T <: IEEEFloat` (`base/math.jl:838-839`) and
`minmax(x::T, y::T)` for `T <: AbstractFloat` (`base/math.jl:836`). -/
def minFloat (m : Machine) {T : FTy} (x y : FV T) : FV T := minIEEE (ieeeOps m T) x y
def maxFloat (m : Machine) {T : FTy} (x y : FV T) : FV T := maxIEEE (ieeeOps m T) x y
def minmaxFloat (m : Machine) {T : FTy} (x y : FV T) : FV T × FV T :=
  minmaxGeneric (minFloat m) (maxFloat m) x y

/-- `rad2deg(z::T)`, `deg2rad(z::T)` for `T <: IEEEFloat` (`base/math.jl:213-223,238,253`). -/
def rad2degIEEE (m : Machine) {T : FTy} (z : FV T) : FV T :=
  rad2degFloat JuliaLean.base.float.mul_float (oneEightyOverPiDispatch T (ieeeOps m T)) z
def deg2radIEEE (m : Machine) {T : FTy} (z : FV T) : FV T :=
  deg2radFloat JuliaLean.base.float.mul_float (piOverOneEightyDispatch T (ieeeOps m T)) z

/-- `modf(x::T) where T<:IEEEFloat` (`base/math.jl:1165-1170`). -/
def modfFloat (m : Machine) {T : FTy} (x : FV T) : FV T × FV T := modfIEEE (ieeeOps m T) x

/-- `rem2pi(x::Float64, r)` for the four implemented modes (`base/special/rem2pi.jl:14-131`); π
enters through `Float64(π, RoundDown)` and `abs(x) < π`. Other modes have no method. Bound
domain: `Float64` only; `rem2pi` of `Float32`, `Float16`, `Int32` (`base/special/rem2pi.jl:133-135`),
other `Integer` types (`rem2pi.jl:138-142`) and `BigFloat` (`base/mpfr.jl:932`) is not bound. -/
def rem2pi64 (m : Machine) (x : FV .f64) : JuliaLean.base.float.RoundingMode → Jl (FV .f64)
  | .Nearest => .ok (JuliaLean.base.special.rem2pi.rem2piNearest
      (JuliaLean.base.mathconstants.ltPi m.pi (loadContext m)) x)
  | .ToZero => .ok (JuliaLean.base.special.rem2pi.rem2piToZero
      (JuliaLean.base.mathconstants.piDirectedValue m.pi .f64 (loadContext m) .Down) x)
  | .Down => .ok (JuliaLean.base.special.rem2pi.rem2piDown x)
  | .Up => .ok (JuliaLean.base.special.rem2pi.rem2piUp x)
  | _ => .error (.methodError "rem2pi")

/-- `mod2pi(x) = rem2pi(x, RoundDown)` (`base/math.jl:1241`) on Float64 (other argument
types are not bound). -/
def mod2pi64 (x : FV .f64) : FV .f64 :=
  mod2pi (fun x _ => JuliaLean.base.special.rem2pi.rem2piDown x) x

theorem mod2pi64_eq (m : Machine) (x : FV .f64) : rem2pi64 m x .Down = .ok (mod2pi64 x) := rfl

/-! ## 5. `evalpoly` (`base/math.jl:75-148`)

Bound domain: `evalpoly(x::T, p)` and `evalpoly(z::Complex{T}, p)` with `T <: IEEEFloat`, every
coefficient of type `T` (a `Tuple`, or a plain `Vector`: `require_one_based_indexing` of an
`Array` never throws). Coefficients of any other type (`Int`, `Rational`, `BigFloat`, a different
IEEE width than `z`, complex values), `z::Complex` with non-IEEE parts, and every `AbstractVector`
that is not a `Vector` (ranges, views, offset arrays, which throw `ArgumentError`) are not bound. -/

/-- `require_one_based_indexing(p)` for a `Vector`: `has_offset_axes(::Array) = false`
(`base/abstractarray.jl:118`), `require_one_based_indexing` (`base/abstractarray.jl:135`). -/
def requireOneBasedVector {C : Type} (p : List C) : Jl Unit :=
  match h : JuliaLean.base.abstractarray.requireOneBased (m := Except JuliaLean.base.abstractarray.ArrayError)
      (fun a => pure (JuliaLean.base.abstractarray.hasOffsetArray a)) p with
  | .ok _ => .ok ()
  | .error _ => absurd h (by simp [JuliaLean.base.abstractarray.requireOneBased,
      JuliaLean.base.abstractarray.hasOffsetArray, bind, Except.bind, pure, Except.pure])

/-- `muladd(x::Real, y::Complex, z::Real)` (`base/complex.jl:348-349`), the `muladd(ai, z, b)` of
`_evalpoly(z::Complex, p)`, for one IEEE type. -/
def complexMuladd {T : FTy} (x : FV T) (z : Cx T) (y : FV T) : Cx T :=
  JuliaLean.base.complex.muladd_Real_Complex_Union
    (JuliaLean.base.complex.muladd_Complex_Real_Real JuliaLean.base.float.muladd_IEEEFloat
      JuliaLean.base.float.mul_float (fun a b => (a, b))) x z y

/-- `evalpoly(x::T, p::Vector{T})` and `evalpoly(x::T, p::Tuple)` for `T <: IEEEFloat`. -/
def evalpolyVectorIEEE {T : FTy} (x : FV T) (p : List (FV T)) : Jl (FV T ⊕ FV T) :=
  evalpolyVector (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
    (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b) requireOneBasedVector x p
def evalpolyTupleIEEE {T : FTy} (x : FV T) (p : List (FV T)) : Jl (FV T ⊕ FV T) :=
  evalpolyTuple (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
    (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b) requireOneBasedVector true x p

/-- `evalpoly(z::Complex{T}, p::Tuple)`/`p::Vector{T}` for `T <: IEEEFloat`. -/
def evalpolyComplexTupleIEEE {T : FTy} (z : Cx T) (p : List (FV T)) : Jl (EvalpolyResult T) :=
  evalpolyComplexTuple complexMuladd requireOneBasedVector true z p
def evalpolyComplexVectorIEEE {T : FTy} (z : Cx T) (p : List (FV T)) : Jl (EvalpolyResult T) :=
  evalpolyComplexVector (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
    (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
    (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
    complexMuladd complexMuladd requireOneBasedVector z p

/-! ## 6. User-defined types -/

/-- `exponent(x::Integer)` (`base/math.jl:980-985`) for a user `Integer` type `X`: `iszero`,
`uabs`, `one`, `+`, `*`, `>=` and `>>` are the user's methods; the shift count and
`n` are `Int`, with `s + s` and `Base.checked_add(n, s)` the installed Int methods. -/
def userIntegerExponentOps {X U : Type} (iszero : X → Bool) (uabs : X → U) (one : U)
    (add mul : U → U → U) (ge : U → U → Bool) (shiftRight : U → Int → U) :
    IntegerExponentOps X U where
  iszero := iszero
  uabs := uabs
  step :=
    { one := one
      add := add
      mul := mul
      ge := ge
      shiftRight := shiftRight
      shiftOne := 1
      addShift := fun a b => (JuliaLean.base.int.add_int (JInt.wrap .i64 a) (JInt.wrap .i64 b)).val
      checkedAdd := fun n s =>
        (JuliaLean.base.checked.checkedAddBits (JInt.wrap .i64 n) (JInt.wrap .i64 s)).map (·.val) }

/-- `atan(y::T, x::T) where T<:AbstractFloat` for a user type `T` with printed name `typeName`. -/
def atanNoOpUser {α : Type} (typeName : String) : Except JuliaLean.base.error.JuliaException α :=
  atanNoOp typeName

/-! ## 7. Further public routes of the generic methods

Each generic `math.jl` method below is bound for every Base type that dispatches to it and has
installed models of its callees: `Bool` and the `BitInteger` types (`float` is `Float64`) and the
IEEE types. A user type's own methods (`float`, `abs`, `log`, `/`, `isnan`, ...) are typed
parameters, since the generic functions are user-extensible. The Base types without installed
callee models (`BigInt`, `BigFloat`, `Rational` of non-`BitInteger` parts, `Complex`, other
`Irrational` types) are not bound. -/

/-- `hypot(x::Number) = abs(float(x))` (`base/math.jl:729`) for `x::Bool`. -/
def hypotOneBool (x : Bool) : FV .f64 :=
  hypotOne (JuliaLean.base.float.float_Bool .f64) JuliaLean.base.float.abs_IEEEFloat x

/-- `hypot(x::Number) = abs(float(x))` for `x::BitInteger`. -/
def hypotOneBitInteger {t : IntTy} (x : JInt t) : FV .f64 :=
  hypotOne JuliaLean.base.float.float_BitInteger JuliaLean.base.float.abs_IEEEFloat x

/-- `hypot(x::Number)` for a user `Number` type with its own `float` and `abs` methods. -/
def hypotOneUser {α β γ : Type} (float : α → β) (abs : β → γ) (x : α) : γ :=
  hypotOne float abs x

/-- `sqrt(x::Real)` for `x::Bool`: the `Real` fallback (`base/math.jl:1326-1330`) with
`float(x) = Float64(x)`. -/
def sqrtBool (m : Machine) (x : Bool) : Jl (FV .f64) :=
  realFallback (JuliaLean.base.float.float_Bool .f64) (fun _ => false) "sqrt" (sqrtFloat m) x

/-- `sqrt(x::Real)` for a user `Real` type without its own `sqrt`: `float(x)` is the user's
method, `sameType` whether its value has the input's type, `sqrtF` the `sqrt` of that type. -/
def sqrtUserReal {α β γ : Type} (float : α → β) (sameType : α → Bool) (sqrtF : β → Jl γ)
    (x : α) : Jl γ :=
  realFallback float sameType "sqrt" sqrtF x

/-- `fourthroot(x::Number) = sqrt(sqrt(x))` for `x::Bool` and `x::BitInteger`: the inner `sqrt`
is the `Real` fallback, the outer one Float64's. -/
def fourthrootBool (m : Machine) (x : Bool) : Jl (FV .f64) :=
  fourthroot (sqrtBool m) (sqrtFloat m) x
def fourthrootBitInteger (m : Machine) {t : IntTy} (x : JInt t) : Jl (FV .f64) :=
  fourthroot (sqrtBitInteger m) (sqrtFloat m) x

/-- `fourthroot(x::Number)` for a user `Number` type: its two `sqrt` calls. -/
def fourthrootUser {α β γ : Type} (sqrt1 : α → Jl β) (sqrt2 : β → Jl γ) (x : α) : Jl γ :=
  fourthroot sqrt1 sqrt2 x

/-- `log(a::Float16) = Float16(log(Float32(a)))` (`base/math.jl:1306-1312`). -/
def logFloat16 (x : FV .f16) : Jl (FV .f16) :=
  float16Via32 JuliaLean.base.special.log.log_32 x

/-- `log(b::T, x::T)` (`base/math.jl:259`) for `T = Float16`, `/` the installed `div_float`. -/
def logBaseFloat16 (b x : FV .f16) : Jl (FV .f16) :=
  logBase logFloat16 JuliaLean.base.float.div_float b x

/-- `log(x::Real)` for `Bool`/`BitInteger`: the `Real` fallback to `log(::Float64)`. -/
def logBool (x : Bool) : Jl (FV .f64) :=
  realFallback (JuliaLean.base.float.float_Bool .f64) (fun _ => false) "log"
    JuliaLean.base.special.log.log_64 x
def logBitInteger {t : IntTy} (x : JInt t) : Jl (FV .f64) :=
  realFallback JuliaLean.base.float.float_BitInteger (fun _ => false) "log"
    JuliaLean.base.special.log.log_64 x

/-- `log(b::T, x::T) = log(x)/log(b)` for `T = Bool` and one `BitInteger` type `T`: each `log` is
the `Real` fallback and `/` is Float64's. -/
def logBaseBool (b x : Bool) : Jl (FV .f64) :=
  logBase logBool JuliaLean.base.float.div_float b x
def logBaseBitInteger {t : IntTy} (b x : JInt t) : Jl (FV .f64) :=
  logBase logBitInteger JuliaLean.base.float.div_float b x

/-- `log(b::T, x::T)` for a user `Number` type `T`: its `log` and `/` methods. -/
def logBaseUser {α γ : Type} (logFn : α → Jl γ) (divFn : γ → γ → γ) (b x : α) : Jl γ :=
  logBase logFn divFn b x

/-- `min`/`max` of `T <: AbstractFloat` for a user type: `isnan`, `signbit` and `<` are the user's
methods in its `AbstractFloatOps` record (`base/math.jl:834-835`). -/
def minUserFloat {α : Type} (o : AbstractFloatOps α) (x y : α) : α := minGeneric o x y
def maxUserFloat {α : Type} (o : AbstractFloatOps α) (x y : α) : α := maxGeneric o x y
def minmaxUserFloat {α : Type} (o : AbstractFloatOps α) (x y : α) : α × α :=
  minmaxGeneric (minGeneric o) (maxGeneric o) x y

/-- The installed `base/special/trig.jl` methods `sinpi`, `cospi`, `sincospi`, `tanpi` of an IEEE
type. -/
def sinpiIEEE : (T : FTy) → FV T → Jl (FV T)
  | .f16, x => JuliaLean.base.special.trig.sinpi .f16 x
  | .f32, x => JuliaLean.base.special.trig.sinpi .f32 x
  | .f64, x => JuliaLean.base.special.trig.sinpi .f64 x
def cospiIEEE : (T : FTy) → FV T → Jl (FV T)
  | .f16, x => JuliaLean.base.special.trig.cospi .f16 x
  | .f32, x => JuliaLean.base.special.trig.cospi .f32 x
  | .f64, x => JuliaLean.base.special.trig.cospi .f64 x
def sincospiIEEE : (T : FTy) → FV T → Jl (FV T × FV T)
  | .f16, x => JuliaLean.base.special.trig.sincospi .f16 x
  | .f32, x => JuliaLean.base.special.trig.sincospi .f32 x
  | .f64, x => JuliaLean.base.special.trig.sincospi .f64 x
def tanpiIEEE : (T : FTy) → FV T → Jl (FV T)
  | .f16, x => JuliaLean.base.special.trig.tanpi .f16 x
  | .f32, x => JuliaLean.base.special.trig.tanpi .f32 x
  | .f64, x => JuliaLean.base.special.trig.tanpi .f64 x

/-- `sinpi`, `cospi`, `sincospi`, `tanpi` of `x::Real` (`base/math.jl:1326-1330`) for a user
`Real` type whose `float` returns an IEEE value of type `T`: the installed
`base/special/trig.jl` methods of `T`. `Bool` and `BitInteger` values do not reach this fallback
(they dispatch to `sinpi(x::Integer)` etc., `base/special/trig.jl`). -/
def sinpiUserReal {α : Type} (T : FTy) (float : α → FV T) (sameType : α → Bool) (x : α) :
    Jl (FV T) := realFallback float sameType "sinpi" (sinpiIEEE T) x
def cospiUserReal {α : Type} (T : FTy) (float : α → FV T) (sameType : α → Bool) (x : α) :
    Jl (FV T) := realFallback float sameType "cospi" (cospiIEEE T) x
def sincospiUserReal {α : Type} (T : FTy) (float : α → FV T) (sameType : α → Bool) (x : α) :
    Jl (FV T × FV T) := realFallback float sameType "sincospi" (sincospiIEEE T) x
def tanpiUserReal {α : Type} (T : FTy) (float : α → FV T) (sameType : α → Bool) (x : α) :
    Jl (FV T) := realFallback float sameType "tanpi" (tanpiIEEE T) x

/-! ### `Rational{T<:BitInteger}`

`float(x::Rational) = AbstractFloat(x) = (float(x.num)/float(x.den))::AbstractFloat`
(`base/float.jl:367`, `base/rational.jl:204`): the installed `abstractFloatRatSource` with
`float(::BitInteger) = Float64` and Float64 `/`. -/

abbrev RationalInt (t : IntTy) := JuliaLean.base.rational.Rational (JInt t)

def floatRational {t : IntTy} (x : RationalInt t) : FV .f64 :=
  JuliaLean.base.float.float_any
    (JuliaLean.base.rational.abstractFloatRatSource JuliaLean.base.float.float_BitInteger
      JuliaLean.base.float.div_float) x

/-- `hypot(x::Number) = abs(float(x))` for `x::Rational{<:BitInteger}`. -/
def hypotOneRational {t : IntTy} (x : RationalInt t) : FV .f64 :=
  hypotOne floatRational JuliaLean.base.float.abs_IEEEFloat x

/-- `sqrt(x::Real)` (the `Real` fallback) for `x::Rational{<:BitInteger}`. -/
def sqrtRational (m : Machine) {t : IntTy} (x : RationalInt t) : Jl (FV .f64) :=
  realFallback floatRational (fun _ => false) "sqrt" (sqrtFloat m) x

/-- `fourthroot(x::Number) = sqrt(sqrt(x))` for `x::Rational{<:BitInteger}`. -/
def fourthrootRational (m : Machine) {t : IntTy} (x : RationalInt t) : Jl (FV .f64) :=
  fourthroot (sqrtRational m) (sqrtFloat m) x

/-- `log(x::Real)` (the `Real` fallback) and `log(b::T, x::T)` for `T = Rational{<:BitInteger}`. -/
def logRational {t : IntTy} (x : RationalInt t) : Jl (FV .f64) :=
  realFallback floatRational (fun _ => false) "log" JuliaLean.base.special.log.log_64 x
def logBaseRational {t : IntTy} (b x : RationalInt t) : Jl (FV .f64) :=
  logBase logRational JuliaLean.base.float.div_float b x

/-- `sinpi`, `cospi`, `sincospi`, `tanpi` of `x::Rational{<:BitInteger}`: the `Real` fallback
(`base/math.jl:1326-1330`) to the Float64 methods. -/
def sinpiRational {t : IntTy} (x : RationalInt t) : Jl (FV .f64) :=
  realFallback floatRational (fun _ => false) "sinpi" (sinpiIEEE .f64) x
def cospiRational {t : IntTy} (x : RationalInt t) : Jl (FV .f64) :=
  realFallback floatRational (fun _ => false) "cospi" (cospiIEEE .f64) x
def sincospiRational {t : IntTy} (x : RationalInt t) : Jl (FV .f64 × FV .f64) :=
  realFallback floatRational (fun _ => false) "sincospi" (sincospiIEEE .f64) x
def tanpiRational {t : IntTy} (x : RationalInt t) : Jl (FV .f64) :=
  realFallback floatRational (fun _ => false) "tanpi" (tanpiIEEE .f64) x

/-! ## 8. `Irrational` arguments (`base/irrationals.jl`, `base/mathconstants.jl`)

The bound `Irrational` types are exactly the five `@irrational` constants of `Base.MathConstants`
(`KnownIrrational`: `π`, `ℯ`, `γ`, `φ`, `catalan`). Every other `Irrational{sym}` type (the macro
creates one wherever it is invoked, `base/irrationals.jl:237-242`) and every other
`AbstractIrrational` subtype (`base/irrationals.jl:5-19`) reaches the same fallbacks with its own
`Float64`/`Float32` methods and is not bound.

The five constants reach the `Real`/`Number` fallbacks of `math.jl`, where
`float(x) = AbstractFloat(x) = Float64(x)`
(`base/float.jl:367`, `base/irrationals.jl:59`). `Float64(x)` and `Float32(x)` are the values
`v64`, `v32` that the `@irrational` function computes at load time from `big(x)`
(`base/irrationals.jl:270-298`, values at 290-293): for `π` the directed value of `mathconstants.piDirectedValue`
(`piValue`), for the other four the installed `irrationals.*FloatValues` evaluated in the
load-time MPFR context. An error of that load-time evaluation is returned as the error of the
call. `log(::Irrational{:ℯ}) = 1` and `log(::Irrational{:ℯ}, x::Number) = log(x)`
(`base/mathconstants.jl:143-144`) are the installed `mathconstants.logE`/`logBaseE`. -/

/-- The five `@irrational` constants of `Base.MathConstants` (`base/mathconstants.jl:13-17`): the
whole bound `Irrational` domain. -/
inductive KnownIrrational where
  | pi | e | gamma | phi | catalan
  deriving DecidableEq, Repr

/-- `Float64(x)` and `Float32(x)` of an `@irrational` constant: the load-time values. -/
def irrationalFloatValues (m : Machine) :
    KnownIrrational → Jl JuliaLean.base.irrationals.IrrationalFloatValues
  | .pi => .ok ⟨piValue m .f64, piValue m .f32⟩
  | .e => ((JuliaLean.base.irrationals.eulerFloatValues m.analytic).run (loadContext m)).1
  | .gamma => ((JuliaLean.base.irrationals.gammaFloatValues m.analytic).run (loadContext m)).1
  | .phi => ((JuliaLean.base.irrationals.phiFloatValues m.analytic).run (loadContext m)).1
  | .catalan => ((JuliaLean.base.irrationals.catalanFloatValues m.analytic).run (loadContext m)).1

/-- `float(x::AbstractIrrational) = AbstractFloat(x) = Float64(x)` (installed
`irrationals.abstractFloat` with the constant's `Float64` method). -/
def floatIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) :=
  JuliaLean.base.irrationals.abstractFloat
    (fun c => (irrationalFloatValues m c).map (·.float64)) c

/-- `hypot(x::Number) = abs(float(x))` (`base/math.jl:729`) for an `@irrational` constant. -/
def hypotOneIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) := do
  let v ← floatIrrational m c
  pure (hypotOne (fun _ => v) JuliaLean.base.float.abs_IEEEFloat c)

/-- `sqrt(x::Real)` (the `Real` fallback, `base/math.jl:1326-1330`) for an `@irrational`
constant: `x === float(x)` is false. -/
def sqrtIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) := do
  let v ← floatIrrational m c
  realFallback (fun _ => v) (fun _ => false) "sqrt" (sqrtFloat m) c

/-- `fourthroot(x::Number) = sqrt(sqrt(x))` (`base/math.jl:685`) for an `@irrational` constant. -/
def fourthrootIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) :=
  fourthroot (sqrtIrrational m) (sqrtFloat m) c

/-- `log(x::Real)` (the `Real` fallback, `base/math.jl:1326-1330`) for `π`, `γ`, `φ`, `catalan`;
`ℯ` has its own method (`logIrrational`). -/
def logRealIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) := do
  let v ← floatIrrational m c
  realFallback (fun _ => v) (fun _ => false) "log" JuliaLean.base.special.log.log_64 c

/-- `log(x)` of an `@irrational` constant: `log(::Irrational{:ℯ}) = 1`, an `Int`
(`base/mathconstants.jl:143`, installed `mathconstants.logE`); `π`, `γ`, `φ` and `catalan` reach
the `Real` fallback (`logRealIrrational`). -/
def logIrrational (m : Machine) : KnownIrrational → Jl (JInt .i64 ⊕ FV .f64)
  | .e => .ok (.inl (JuliaLean.base.mathconstants.logE ⟨⟩))
  | c => .inr <$> logRealIrrational m c

theorem logIrrational_e (m : Machine) : logIrrational m .e = .ok (.inl (JInt.wrap .i64 1)) := rfl

/-- The result of `log(b::T, x::T)` for one `@irrational` type `T`: `log(ℯ, ℯ)` is
`log(::Irrational{:ℯ}, x::Number) = log(x)` with `log(ℯ) = 1` (an `Int`); every other constant
reaches `log(b::T, x::T) = log(x)/log(b)` (`base/math.jl:259`) with the `Real` fallback `log` and
Float64 `/`. -/
def logBaseIrrational (m : Machine) : KnownIrrational → Jl (JInt .i64 ⊕ FV .f64)
  | .e => .inl <$> JuliaLean.base.mathconstants.logBaseE
      (fun e => (.ok (JuliaLean.base.mathconstants.logE e) : Jl (JInt .i64))) ⟨⟩ (⟨⟩ : JuliaLean.base.irrationals.Irrational "ℯ")
  | c => .inr <$> logBase (logRealIrrational m) JuliaLean.base.float.div_float c c

/-- `log(::Irrational{:ℯ}, x::Number) = log(x)` (`base/mathconstants.jl:144`), the installed
`mathconstants.logBaseE`. It is more specific than `log(b::T, x::T)` and `log(b::Number, x::Number)`,
so `log(ℯ, x)` selects it for every `Number` `x`, of the type of `x` or not; the bindings below
instantiate it with the `log` of each bound type of `x` (`Complex`, `BigInt`, `BigFloat` and the
other types without bound callee models are not bound). -/
def eIrrational : JuliaLean.base.irrationals.Irrational "ℯ" := ⟨⟩

def logBaseEFloat (T : JuliaLean.base.irrationals.IEEE32Or64) (x : FV T.ty) : Jl (FV T.ty) :=
  JuliaLean.base.mathconstants.logBaseE (logFloat T) eIrrational x
def logBaseEFloat16 (x : FV .f16) : Jl (FV .f16) :=
  JuliaLean.base.mathconstants.logBaseE logFloat16 eIrrational x
def logBaseEBool (x : Bool) : Jl (FV .f64) :=
  JuliaLean.base.mathconstants.logBaseE logBool eIrrational x
def logBaseEBitInteger {t : IntTy} (x : JInt t) : Jl (FV .f64) :=
  JuliaLean.base.mathconstants.logBaseE logBitInteger eIrrational x
def logBaseERational {t : IntTy} (x : RationalInt t) : Jl (FV .f64) :=
  JuliaLean.base.mathconstants.logBaseE logRational eIrrational x
def logBaseEIrrational (m : Machine) (c : KnownIrrational) : Jl (JInt .i64 ⊕ FV .f64) :=
  JuliaLean.base.mathconstants.logBaseE (logIrrational m) eIrrational c
/-- `log(ℯ, x)` for a user `Number` type with its own `log`. -/
def logBaseEUser {α γ : Type} (logFn : α → Jl γ) (x : α) : Jl γ :=
  JuliaLean.base.mathconstants.logBaseE logFn eIrrational x

theorem logBaseEIrrational_e (m : Machine) : logBaseEIrrational m .e = logBaseIrrational m .e := rfl

/-- `sinpi`, `cospi`, `sincospi`, `tanpi` of an `@irrational` constant: the `Real` fallback
(`base/math.jl:1326-1330`) to the Float64 methods of `base/special/trig.jl`. -/
def sinpiIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) := do
  let v ← floatIrrational m c
  realFallback (fun _ => v) (fun _ => false) "sinpi" (sinpiIEEE .f64) c
def cospiIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) := do
  let v ← floatIrrational m c
  realFallback (fun _ => v) (fun _ => false) "cospi" (cospiIEEE .f64) c
def sincospiIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64 × FV .f64) := do
  let v ← floatIrrational m c
  realFallback (fun _ => v) (fun _ => false) "sincospi" (sincospiIEEE .f64) c
def tanpiIrrational (m : Machine) (c : KnownIrrational) : Jl (FV .f64) := do
  let v ← floatIrrational m c
  realFallback (fun _ => v) (fun _ => false) "tanpi" (tanpiIEEE .f64) c

/-- A `Real` argument of `atan(y::Real, x::Real)` with installed models: `Bool`, a `BitInteger`,
an IEEE value, a `Rational{<:BitInteger}` or an `@irrational` constant. -/
inductive RealArg where
  | bool (x : Bool)
  | int {t : IntTy} (x : JInt t)
  | float {T : FTy} (x : FV T)
  | rational {t : IntTy} (x : JuliaLean.base.rational.Rational (JInt t))
  | irrational (c : KnownIrrational)

/-- `float(x)` of a `RealArg`: `float(x) = AbstractFloat(x)` (`base/float.jl:367`), the identity on
an IEEE value; `floatIrrational` for a constant. -/
def RealArg.toFloat (m : Machine) : RealArg → Jl ((T : FTy) × FV T)
  | .bool x => .ok ⟨.f64, JuliaLean.base.float.float_Bool .f64 x⟩
  | .int x => .ok ⟨.f64, JuliaLean.base.float.float_BitInteger x⟩
  | .float x => .ok ⟨_, x⟩
  | .rational x => .ok ⟨.f64, floatRational x⟩
  | .irrational c => (fun v => ⟨.f64, v⟩) <$> floatIrrational m c

/-- `promote_type` of two IEEE types (`base/float.jl:477-479`): the wider format. -/
def widerFloat : FTy → FTy → FTy
  | .f64, _ => .f64
  | _, .f64 => .f64
  | .f32, _ => .f32
  | _, .f32 => .f32
  | .f16, .f16 => .f16

/-- `atan(y::T, x::T)` of an IEEE type: Float32/Float64 `base/special/trig.jl`, Float16
`atan(a::Float16, b::Float16) = Float16(atan(Float32(a), Float32(b)))` (`base/math.jl:1319`). -/
def atanIEEE : (T : FTy) → FV T → FV T → Jl (FV T)
  | .f16, y, x => atan16 (fun a b => .ok (JuliaLean.base.special.trig.atan2 .f32 a b)) y x
  | .f32, y, x => .ok (JuliaLean.base.special.trig.atan2 .f32 y x)
  | .f64, y, x => .ok (JuliaLean.base.special.trig.atan2 .f64 y x)

/-- `atan(y::Real, x::Real) = atan(promote(float(y), float(x))...)` (`base/math.jl:830`) for
`Bool`, `BitInteger`, IEEE, `Rational{<:BitInteger}` and `@irrational` arguments of any two types: `promote` converts both floats to the
wider type with the installed `convertFloat`. Two values of one IEEE type dispatch to
`atan(y::T, x::T)` directly; the result is the same. -/
def atanRealArgs (m : Machine) (y x : RealArg) : Jl ((T : FTy) × FV T) := do
  let ⟨S, ys⟩ ← y.toFloat m
  let ⟨U, xs⟩ ← x.toFloat m
  let T := widerFloat S U
  pure ⟨T, ← atanIEEE T (JuliaLean.base.float.convertFloat T ys) (JuliaLean.base.float.convertFloat T xs)⟩

/-- `modf(x) = isinf(x) ? (flipsign(zero(x), x), x) : (rem(x, one(x)), trunc(x))`
(`base/math.jl:1163`) for a user type with its own `isinf`, `zero`, `one`, `trunc`, `flipsign`
and `rem`; IEEE values dispatch to `modf(x::IEEEFloat)` (`modfFloat`). -/
def modfUser {α : Type} (isinf : α → Bool) (zero one trunc : α → α) (flip rem : α → α → α)
    (x : α) : α × α :=
  modfGeneric isinf zero one trunc flip rem x

/-- The empty polynomial: `evalpoly(x, ())` and `evalpoly(x, T[])` throw `BoundsError` at the
pinned revision (`p[end]` of an empty collection), so the documented zero sum is not the
result. -/
theorem evalpolyTupleIEEE_empty {T : FTy} (x : FV T) :
    evalpolyTupleIEEE x [] = .error .boundsError := by
  exact evalpolyTuple_generated_empty _ _ _ x
theorem evalpolyVectorIEEE_empty {T : FTy} (x : FV T) :
    evalpolyVectorIEEE x [] = .error .boundsError := by
  simp only [evalpolyVectorIEEE, evalpolyVector, evalpolyVectorSource, evalpolyReal,
    evalpolyRealSource, requireOneBasedVector, JuliaLean.base.abstractarray.requireOneBased,
    JuliaLean.base.abstractarray.hasOffsetArray, bind, Except.bind, pure, Except.pure,
    polynomialListIndex_empty, Bool.not_false, ite_true]
  rfl

end JuliaLean.Bindings.base.math
