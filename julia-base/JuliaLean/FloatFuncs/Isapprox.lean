import JuliaLean.Float
import JuliaLean.MathFuncs.Basic

/-!
`isapprox` for Float64 and Int64 arguments with `norm = abs`
(`base/floatfuncs.jl:230-338`, master `bbfa0ce4150`).

The Int64 method is master's exact-integer rewrite (#63022); Julia 1.13.2 computed
`norm(_y - _x) <= max(atol, rtol*max(norm(_x), norm(_y)))` with wrapping arithmetic.
-/

namespace JuliaLean.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

/-- `rtoldefault(Float64, Float64, atol)`: `sqrt(eps(Float64))` unless `atol > 0`;
`base/floatfuncs.jl:326,335-338`. -/
def rtolDefault (atol : F64) : F64 :=
  if F64.lt (F64.zero false) atol then F64.zero false else F64.ofBits 0x3e50000000000000

/-- `isapprox(x::Float64, y::Float64; atol, rtol, nans, norm=abs)`;
`base/floatfuncs.jl:230-237`. `max` is the `max_float` intrinsic (`MathFuncs.fmax`). -/
def isapproxF (x y atol rtol : F64) (nans : Bool) : Bool :=
  F64.eq x y ||
    (F64.isfinite x && F64.isfinite y &&
      F64.le (F64.abs (F64.sub x y))
        (fmax atol (F64.mul rtol (fmax (F64.abs x) (F64.abs y))))) ||
    (nans && F64.isnan x && F64.isnan y)

/-- `x ≈ y` with default keywords: `atol = zero(real(x))`, `rtol = rtoldefault(x, y, atol)`,
`nans = false`; `base/floatfuncs.jl:231-232,317`. -/
def approxDefault (x y : F64) : Bool :=
  isapproxF x y (F64.zero false) (rtolDefault (F64.zero false)) false

/-- `uabs(x::Int64) = unsigned(abs(x))`, `base/int.jl`: the magnitude as a UInt64 value. -/
def uabs64 (x : JInt .i64) : Nat := x.val.natAbs

/--
`isapprox(x::Int64, y::Int64; atol::Int64, rtol::Int64, norm=abs)` on master,
`base/floatfuncs.jl:289-300`:
`_scaled_rtol(rtol::BitInteger, scale::BitInteger) = mul_with_overflow(promote(rtol, scale)...)`
promotes `rtol` to `UInt64` with `convert` (`base/floatfuncs.jl:287`); `max(atol, b)` with
`b::UInt64` is the mixed BitInteger `max`, `ifelse(x < y, y % R, x % R)` with an exact
mixed comparison (`base/int.jl:591-594`); `_uabsdiff(x, y) = unsigned(hi) - unsigned(lo)`
(`base/floatfuncs.jl:253-257`) and `_uabsdiff_le(x, y, b) = _uabsdiff(x, y) <= b`
(`base/floatfuncs.jl:275`).
-/
def isapproxI64 (x y atol rtol : JInt .i64) : Jl Bool :=
  if atol.val < 1 && rtol.val == 0 then .ok (x.val == y.val)
  else if x.val == y.val then .ok true
  else do
    let scale := max (uabs64 x) (uabs64 y)
    let r ← JInt.convert .u64 rtol.val
    let prod := r.val.toNat * scale
    if prod ≥ 2^64 then pure true
    else do
      let bound : Nat := if atol.val < (prod : Int) then prod
        else (JInt.wrap .u64 atol.val).val.toNat
      let lo := min x.val y.val
      let hi := max x.val y.val
      let d := (JInt.wrap .u64 hi - JInt.wrap .u64 lo).val.toNat
      pure (decide (d ≤ bound))

end JuliaLean.FloatFuncs
